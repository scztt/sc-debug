/*
	SuperCollider real time audio synthesis system
    Copyright (c) 2002 James McCartney. All rights reserved.
	http://www.audiosynth.com

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301  USA
*/


#include "Opcodes.h"
#include "PyrInterpreter.h"
#include "PyrPrimitive.h"
#include "PyrPrimitiveProto.h"
#include "PyrMathPrim.h"
#include "PyrListPrim.h"
#include "PyrKernel.h"
#include "PyrMessage.h"
#include "PyrParseNode.h"
#include "PyrSignal.h"
#include "PyrSched.h"
#include "PyrObject.h"
#include "SC_InlineUnaryOp.h"
#include "SC_InlineBinaryOp.h"
#include "PyrKernelProto.h"
#include "PyrSymbolTable.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>
# include <signal.h>

#ifdef SC_WIN32
# include "SC_Win32Utils.h"
#else
# include <sys/time.h>
#endif

#include <float.h>
#define kBigBigFloat DBL_MAX
#define kSmallSmallFloat DBL_MIN

#define JUMPTABLE 0
#if JUMPTABLE
	#define OP_(op) OP_##op
	#define ENDOP goto end;
#else
	#define OP_(op) case op
	#define ENDOP break;
#endif

#include <new>
#include "InitAlloc.h"
#include "bullet.h"



//void tellPlugInsAboutToRun();
double timeNow();


int32 timeseed();
int32 timeseed()
{
	struct timeval tv;
  gettimeofday(&tv, 0);
  return tv.tv_sec ^ tv.tv_usec;
}

VMGlobals gVMGlobals;
VMGlobals *gMainVMGlobals = &gVMGlobals;

extern PyrObject *gSynth;

void debugf(char *fmt, ...) ;

#define SANITYCHECK 0
#define DEBUGINTERPRETER 0
#define METHODMETER 0
#define BCSTAT 0
#define CHECK_MAX_STACK_USE 0

#if SANITYCHECK
#define SANITYCHECKLITE 1
#else
#define SANITYCHECKLITE 0
#endif

#if CHECK_MAX_STACK_USE
int gMaxStackDepth = 0;
#endif

unsigned char* dumpOneByteCode(PyrBlock *theBlock, PyrClass* theClass, unsigned char *ip);
void dumpSlotOneWord(const char *tagstr, PyrSlot *slot);
//bool checkAllObjChecksum(PyrObject* obj);

//bool gTraceInterpreter = false;
bool gTraceInterpreter = true;


char* byteCodeString(int code);

extern int gNumClasses;
extern PyrClass *gClassList;

// runInterpreter has 7 call sites:
//	compileLibrary (4)
// 	runLibrary
// 	interpretCmdLine

void runInterpreter(VMGlobals *g, PyrSymbol *selector, int numArgsPushed)
{
		//postfl("->runInterpreter\n");
#if SANITYCHECKLITE
	g->gc->SanityCheck();
#endif
		//postfl(" >initInterpreter\n");

	if (initInterpreter(g, selector, numArgsPushed)) {
#if SANITYCHECKLITE
	g->gc->SanityCheck();
#endif
//        if (strcmp(selector->name, "tick") != 0) post("%s %d  execMethod %d\n", selector->name, numArgsPushed, g->execMethod);
	//post("->Interpret thread %08X\n", g->thread);
		if (g->execMethod) Interpret(g);
	//post("<-Interpret thread %08X\n", g->thread);
#if SANITYCHECKLITE
	g->gc->SanityCheck();
#endif

        }
        //postfl(" >endInterpreter\n");
        endInterpreter(g);
#if SANITYCHECKLITE
	g->gc->SanityCheck();
#endif
		//postfl("<-runInterpreter\n");
	//dumpGCStats(g->gc);

}

bool initAwakeMessage(VMGlobals *g);

void runAwakeMessage(VMGlobals *g)
{
	if (initAwakeMessage(g)) {
		if (g->execMethod) Interpret(g);
	}
	endInterpreter(g);
}

void initPyrThread(VMGlobals *g, PyrThread *thread, PyrSlot *func, int stacksize, PyrInt32Array* rgenArray,
	double beats, double seconds, PyrSlot* clock, bool collect);
int32 timeseed();

PyrProcess* newPyrProcess(VMGlobals *g, PyrClass *procclassobj)
{
	PyrProcess *proc;
	PyrInterpreter *interpreter;
	PyrClass *classobj;
	PyrObject *classVars;
	PyrThread *thread;
	//PyrDSP *dsp;
        PyrGC* gc = g->gc;

	int numClassVars;

	proc = (PyrProcess*)instantiateObject(gc, procclassobj, 0, true, false);

	PyrObject *sysSchedulerQueue = newPyrArray(gc, 1024, 0, false);
	SetObject(&proc->sysSchedulerQueue, sysSchedulerQueue);

	classVars = newPyrArray(gc, gNumClassVars, 0, false);
	classVars->size = gNumClassVars;
	nilSlots(classVars->slots, gNumClassVars);
	SetObject(&proc->classVars, classVars);
	g->classvars = classVars;

	// fill class vars from prototypes:
	classobj = gClassList;
	while (classobj) {
		if (classobj->cprototype.uo) {
			numClassVars = classobj->cprototype.uo->size;
			if (numClassVars > 0) {
				memcpy(g->classvars->slots + classobj->classVarIndex.ui, classobj->cprototype.uo->slots, numClassVars * sizeof(PyrSlot));
			}
		}
		classobj = classobj->nextclass.uoc;
	}

	class_thread = getsym("Thread")->u.classobj;
	if (class_thread) {
		SetNil(&proc->curThread);
		thread = (PyrThread*)instantiateObject(gc, class_thread, 0, true, false);
		//SetObject(&threadsArray->slots[0], thread);
		SetObject(&proc->mainThread, thread);
		PyrInt32Array *rgenArray = newPyrInt32Array(gc, 4, 0, false);
		rgenArray->size = 4;
		rgenArray->i[0] = 0;
		rgenArray->i[1] = 0;
		rgenArray->i[2] = 0;
		rgenArray->i[3] = 0;
		((RGen*)(rgenArray->i))->init(timeseed());

		PyrSlot clockSlot;
		SetObject(&clockSlot, s_systemclock->u.classobj);
		initPyrThread(g, thread, &o_nil, EVALSTACKDEPTH, rgenArray, 0., 0., &clockSlot, false);
		//postfl("elapsedTime %.6f\n", elapsedTime());
	} else {
		error("Class Thread not found.\n");
	}

	PyrSymbol *contextsym;
	int index;
	PyrMethod *meth;

	contextsym = getsym("functionCompileContext");
	index = class_interpreter->classIndex.ui + contextsym->u.index;
	meth = gRowTable[index];
	if (!meth || meth->name.us != contextsym) {
		error("compile context method 'functionCompileContext' not found.\n");
		//SetNil(&proc->interpreter);
	} else {
		PyrObject *proto;
		PyrFrame *frame;
		PyrMethodRaw *methraw;

		interpreter = (PyrInterpreter*)instantiateObject(gc, class_interpreter, 0, true, false);
		SetObject(&proc->interpreter, interpreter);
		proto = meth->prototypeFrame.uo;

		methraw = METHRAW(meth);
		frame = (PyrFrame*)gc->New(methraw->frameSize, 0, obj_slot, false);
		frame->classptr = class_frame;
		frame->size = FRAMESIZE + proto->size; /// <- IS THIS WRONG ??
		SetObject(&frame->method, meth);
		SetObject(&frame->homeContext, frame);
		SetInt(&frame->caller, 0);
		SetNil(&frame->context);
		SetPtr(&frame->ip,  0);
		SetObject(&frame->vars[0], interpreter);
		SetInt(&frame->line, 0);
		SetInt(&frame->character, 0);

		SetObject(&interpreter->context, frame);
	}

	return proc;
}


#if BCSTAT
int prevop = 0;
int bcstat[256];
int bcpair[256][256];

void clearbcstat();
void clearbcstat()
{
	int i, j;
	for (i=0; i<256; ++i) {
		bcstat[i] = 0;
		for (j=0; j<256; ++j) {
			bcpair[i][j] = 0;
		}
	}
}

void dumpbcstat();
void dumpbcstat()
{
	FILE *file;
	int i, j, k, total;

	file = fopen("bcstat", "w");
	if (file) {
		fprintf(file, "----------\n");
		total = 0;
		for (i=0; i<256; ++i) {
			total +=  bcstat[i];
			if (bcstat[i]) fprintf(file, "%3d %8d  %-32s\n", i, bcstat[i], byteCodeString(i));
		}
		fprintf(file, "\ntotal %d\n", total);
		fprintf(file, "-----cur,next-----\n");
		for (i=0, k=0; i<256; ++i) {
			for (j=0; j<256; j++) {
				if (bcpair[i][j] > 0) {
					fprintf(file, "%4d %3d %3d %8d %-32s %-32s\n", k++, i, j, bcpair[i][j], byteCodeString(i), byteCodeString(j));
				}
			}
		}
		fprintf(file, "-----cur,prev-----\n");
		for (i=0, k=0; i<256; ++i) {
			for (j=0; j<256; j++) {
				if (bcpair[j][i] > 0) {
					fprintf(file, "%4d %3d %3d %8d %-32s %-32s\n", k++, i, j, bcpair[j][i], byteCodeString(i), byteCodeString(j));
				}
			}
		}
	}
	fclose(file);
}
#endif

void initPatterns();
void initThreads();
void initGUI();

#ifndef SC_WIN32
bool running = true;
void handleSigUsr1(int param)
{
  printf("handleSigUsr1()...\n");
  running = false;
}
#endif

bool initRuntime(VMGlobals *g, int poolSize, AllocPool *inPool)
{
	PyrClass *class_main;
	/*
		create a GC environment
		create a vmachine instance of main
		initialize VMGlobals
	*/

	class_main = s_main->u.classobj;

	if (!class_main) { error("Class 'Main' not defined.\n"); return false; }
	if (!isSubclassOf(class_main, class_process)) {
		error("Class Main is not a subclass of Process.\n");
		return false;
	}

	// create GC environment, process
	g->allocPool = inPool;
	g->gc = (PyrGC*)g->allocPool->Alloc(sizeof(PyrGC));
	new (g->gc) PyrGC(g, g->allocPool, class_main, poolSize);
	g->thread = g->process->mainThread.uot;
	SetObject(&g->receiver, g->process);

	// these will be set up when the run method is called
	g->method = NULL;
	g->block = NULL;
	g->frame = NULL;
	g->ip = NULL;

	// initialize process random number generator
	g->rgen = (RGen*)(g->thread->randData.uo->slots);

	//initUGenFuncs();
	signal_init_globs();
	initThreads();
	initPatterns();
	initUniqueMethods();
	initGUI();
	initCachedFrames(g);
	
#if SANITYCHECKLITE
	g->gc->SanityCheck();
#endif
	//tellPlugInsAboutToRun();

#ifndef SC_WIN32
	signal(SIGUSR1,handleSigUsr1);
#endif

	assert((g->gc->SanityCheck()));
#if SANITYCHECKLITE
	g->gc->SanityCheck();
#endif

	return true;
}

bool initAwakeMessage(VMGlobals *g)
{
	//post("initAwakeMessage %08X %08X\n", g->thread, g->process->mainThread.uot);
	slotCopy(&g->process->curThread, &g->process->mainThread); //??
	g->thread = g->process->mainThread.uot; //??

	// these will be set up when the run method is called
	g->method = NULL;
	g->block = NULL;
	g->frame = NULL;
	g->ip = NULL;
        g->execMethod = 0;

	// set process as the receiver
	PyrSlot *slot = g->sp - 3;
	slotCopy(&g->receiver, slot);

	g->thread->beats.uf = slot[1].uf;
	g->thread->seconds.uf = slot[2].uf;
	slotCopy(&g->thread->clock, &slot[3]);
	g->gc->GCWrite(g->thread, slot+3);

	// start it
	sendMessage(g, s_awake, 4);

	return g->method != NULL;
}

bool initInterpreter(VMGlobals *g, PyrSymbol *selector, int numArgsPushed)
{
	slotCopy(&g->process->curThread, &g->process->mainThread);
	g->thread = g->process->mainThread.uot;

	// these will be set up when the run method is called
#if TAILCALLOPTIMIZE
	g->tailCall = 0;
#endif
	g->method = NULL;
	g->block = NULL;
	g->frame = NULL;
	g->ip = NULL;
        g->execMethod = 0;
	g->thread->beats.uf = g->thread->seconds.uf = elapsedTime();
	SetObject(&g->thread->clock, s_systemclock->u.classobj);
	g->gc->GCWrite(g->thread, s_systemclock->u.classobj);

	// set process as the receiver
	PyrSlot *slot = g->sp - numArgsPushed + 1;
	slotCopy(&g->receiver, slot);

	// start it
	sendMessage(g, selector, numArgsPushed);

	return g->method != NULL;
}


void endInterpreter(VMGlobals *g)
{
	slotCopy(&g->result, g->sp);
//	dumpObjectSlot(&g->result);
	g->gc->Stack()->size = 0;
	g->sp = g->gc->Stack()->slots - 1;
}


void StoreToImmutableA(VMGlobals *g, PyrSlot *& sp, unsigned char *& ip);
void StoreToImmutableA(VMGlobals *g, PyrSlot *& sp, unsigned char *& ip)
{
	// only the value is on the stack
	slotCopy(&sp[1], &sp[0]); // copy value up one
	slotCopy(&sp[0], &g->receiver); // put receiver in place
	sp++;
	g->sp = sp;
	g->ip = ip;
	post("StoreToImmutableA\n");
	dumpObjectSlot(sp-1);
	dumpObjectSlot(sp);
	sendMessage(g, getsym("immutableError"), 2);
	sp = g->sp;
	ip = g->ip;
}

void StoreToImmutableB(VMGlobals *g, PyrSlot *& sp, unsigned char *& ip);
void StoreToImmutableB(VMGlobals *g, PyrSlot *& sp, unsigned char *& ip)
{
	// receiver and value are on the stack.
	sp++;
	g->sp = sp;
	g->ip = ip;
	post("StoreToImmutableB\n");
	dumpObjectSlot(sp-1);
	dumpObjectSlot(sp);
	PyrSymbol *selector = getsym("immutableError");
	sendMessage(g, selector, 2);
	sp = g->sp;
	ip = g->ip;
}


void dumpByteCodes(PyrBlock *theBlock);

void Interpret(VMGlobals *g)
{
	// byte code values
	unsigned char *ip;
	unsigned int op1;
	int op2, op3, index, tag;
	// interpreter globals

	// temporary variables used in the interpreter
	int ival, jmplen, numArgsPushed, numKeyArgsPushed;
	PyrFrame *tframe;
	PyrSymbol *selector;
	PyrClass *classobj;
	PyrSlot *slot, *vars;
	PyrSlot *sp, *pslot;
	PyrObject *obj;
	PyrClosure *closure;
	PyrMethod *meth;
	int m,mmax;
#if JUMPTABLE
	const itype jumpTable[] = { 
		&&OP_0, &&OP_1, &&OP_2, &&OP_3, &&OP_4, &&OP_5, &&OP_6, &&OP_7, &&OP_8, &&OP_9, &&OP_10, &&OP_11, &&OP_12, &&OP_13, &&OP_14, &&OP_15, &&OP_16, &&OP_17, &&OP_18, &&OP_19, &&OP_20, &&OP_21, &&OP_22, &&OP_23, &&OP_24, &&OP_25, &&OP_26, &&OP_27, &&OP_28, &&OP_29, &&OP_30, &&OP_31, &&OP_32, &&OP_33, &&OP_34, &&OP_35, &&OP_36, &&OP_37, &&OP_38, &&OP_39, &&OP_40, &&OP_41, &&OP_42, &&OP_43, &&OP_44, &&OP_45, &&OP_46, &&OP_47, &&OP_48, &&OP_49, &&OP_50, &&OP_51, &&OP_52, &&OP_53, &&OP_54, &&OP_55, &&OP_56, &&OP_57, &&OP_58, &&OP_59, &&OP_60, &&OP_61, &&OP_62, &&OP_63, &&OP_64, &&OP_65, &&OP_66, &&OP_67, &&OP_68, &&OP_69, &&OP_70, &&OP_71, &&OP_72, &&OP_73, &&OP_74, &&OP_75, &&OP_76, &&OP_77, &&OP_78, &&OP_79, &&OP_80, &&OP_81, &&OP_82, &&OP_83, &&OP_84, &&OP_85, &&OP_86, &&OP_87, &&OP_88, &&OP_89, &&OP_90, &&OP_91, &&OP_92, &&OP_93, &&OP_94, &&OP_95, &&OP_96, &&OP_97, &&OP_98, &&OP_99, &&OP_100, &&OP_101, &&OP_102, &&OP_103, &&OP_104, &&OP_105, &&OP_106, &&OP_107, &&OP_108, &&OP_109, &&OP_110, &&OP_111, &&OP_112, &&OP_113, &&OP_114, &&OP_115, &&OP_116, &&OP_117, &&OP_118, &&OP_119, &&OP_120, &&OP_121, &&OP_122, &&OP_123, &&OP_124, &&OP_125, &&OP_126, &&OP_127, &&OP_128, &&OP_129, &&OP_130, &&OP_131, &&OP_132, &&OP_133, &&OP_134, &&OP_135, &&OP_136, &&OP_137, &&OP_138, &&OP_139, &&OP_140, &&OP_141, &&OP_142, &&OP_143, &&OP_144, &&OP_145, &&OP_146, &&OP_147, &&OP_148, &&OP_149, &&OP_150, &&OP_151, &&OP_152, &&OP_153, &&OP_154, &&OP_155, &&OP_156, &&OP_157, &&OP_158, &&OP_159, &&OP_160, &&OP_161, &&OP_162, &&OP_163, &&OP_164, &&OP_165, &&OP_166, &&OP_167, &&OP_168, &&OP_169, &&OP_170, &&OP_171, &&OP_172, &&OP_173, &&OP_174, &&OP_175, &&OP_176, &&OP_177, &&OP_178, &&OP_179, &&OP_180, &&OP_181, &&OP_182, &&OP_183, &&OP_184, &&OP_185, &&OP_186, &&OP_187, &&OP_188, &&OP_189, &&OP_190, &&OP_191, &&OP_192, &&OP_193, &&OP_194, &&OP_195, &&OP_196, &&OP_197, &&OP_198, &&OP_199, &&OP_200, &&OP_201, &&OP_202, &&OP_203, &&OP_204, &&OP_205, &&OP_206, &&OP_207, &&OP_208, &&OP_209, &&OP_210, &&OP_211, &&OP_212, &&OP_213, &&OP_214, &&OP_215, &&OP_216, &&OP_217, &&OP_218, &&OP_219, &&OP_220, &&OP_221, &&OP_222, &&OP_223, &&OP_224, &&OP_225, &&OP_226, &&OP_227, &&OP_228, &&OP_229, &&OP_230, &&OP_231, &&OP_232, &&OP_233, &&OP_234, &&OP_235, &&OP_236, &&OP_237, &&OP_238, &&OP_239, &&OP_240, &&OP_241, &&OP_242, &&OP_243, &&OP_244, &&OP_245, &&OP_246, &&OP_247, &&OP_248, &&OP_249, &&OP_250, &&OP_251, &&OP_252, &&OP_253, &&OP_254, &&OP_255
	};
#endif

#if 0
	unsigned char *bzero;
	PyrSlot *szero;
	char str[80];
#endif


#if BCSTAT
	//clearbcstat();
	op1 = 0;
	prevop = 0;
#endif

#if 0
	bzero = g->ip;
	szero = g->sp;
	//SetSymbol(g->sp, getsym("STACK TOP")); // just for debugging
	//g->sp++; // just for debugging
#endif

	// Codewarrior puts them in registers. take advantage..
	sp = g->sp;
	ip = g->ip;

	numKeyArgsPushed = 0;

	if (setjmp(g->escapeInterpreter) != 0) {
		return;
	}
#ifndef SC_WIN32
	while (running) {  // not going to indent body to save line space
#else
	while (true) {
#endif

#if CHECK_MAX_STACK_USE
	int stackDepth = sp - g->sp + 1;
	if (stackDepth > gMaxStackDepth) {
		gMaxStackDepth = stackDepth;
		printf("gMaxStackDepth %d\n", gMaxStackDepth);
	}
#endif

#if BCSTAT
	prevop = op1;
#endif
	op1 = ip[1];
	++ip;
//	op1 = *(++ip);
#if BCSTAT
	++bcstat[op1];
	++bcpair[prevop][op1];
	prevop = op1;
#endif
	//printf("op1 %d\n", op1);
	//postfl("sp %08X   frame %08X  caller %08X  ip %08X\n", sp, g->frame, g->frame->caller.uof, g->frame->caller.uof->ip.ui);
	//postfl("sp %08X   frame %08X   diff %d    caller %08X\n", sp, g->frame, ((int)sp - (int)g->frame)>>3, g->frame->caller.uof);
	if (false && g->debugFlag && strcmp(g->method->ownerclass.s.u.oc->name.s.u.s->name, "String")==0) {
		//DumpStack(g, sp);
		if (FrameSanity(g->frame, "dbgint")) {
			//Debugger();
		}
		//g->gc->SanityCheck();
		//assert(g->gc->SanityCheck());
//		g->sp = sp; g->ip = ip;
//		g->gc->FullCollection();
//			sp = g->sp; ip = g->ip;
//		postfl("[%3d] %20s-%-16s  ",
//			(sp - g->gc->Stack()->slots) + 1,
//			g->method->ownerclass.uoc->name.us->name, g->method->name.us->name);
//		dumpOneByteCode(g->block, NULL, ip);
//		selector = getsym("tracePoint");
//		classobj = g->method->ownerclass.uoc->superclass.us->u.classobj;
//		goto msg_lookup;		
	}
#if SANITYCHECK
//	gcLinkSanity(g->gc);
	g->gc->SanityCheck();
//	do_check_pool(pyr_pool_runtime);
//	do_check_pool(pyr_pool_compile);
#endif
#if METHODMETER
	if (gTraceInterpreter) {
		g->method->byteMeter.ui++;
	}
#endif

	if( IsTrue(&g->thread->debugging) ) 
	{
		if( g->thread->dContinue )
		{
			g->thread->dContinue = false;
		} else {
			PyrBlock* debugBlock = g->block;
			if( debugBlock->debugTable.uo )
			{
				// Follow structure of methPrimative
				dumpOneByteCode(g->block, NULL, ip);

				uint32 *line = ((PyrInt32Array*)debugBlock->debugTable.uo)->i + (2*(ip - (g->block->code.uob->b)));
				uint32 *character = ((PyrInt32Array*)debugBlock->debugTable.uo)->i + (1+2*(ip - (g->block->code.uob->b)));
				SetInt( &g->thread->line, (int)*line );
				SetInt( &g->thread->character, (int)*character );

				SetInt( &g->frame->line, (int)*line );
				SetInt( &g->frame->character, (int)*character );
				 
				selector = getsym("break");
				classobj = classOfSlot(sp);
				index = classobj->classIndex.ui + selector->u.index;
				meth = gRowTable[index];
				
				PyrThread *oldthread = g->thread;
				g->sp = sp; g->ip = ip;				
				doPrimitive(g, meth, 0 );
				sp = g->sp; ip = g->ip;
				oldthread->state.ui = tDebugging;
				continue; 
			} else {
				sp = sp;
			}
		}
	}
				
#if JUMPTABLE
	goto *jumpTable[op1];
#else
	switch (op1) {
#endif
		OP_(0) : //	push class
			op2 = ip[1]; ++ip; // get literal index
			classobj = g->block->selectors.uo->slots[op2].us->u.classobj;
			if (classobj) {
				++sp; SetObject(sp, classobj);
			} else {
				postfl("Execution warning: Class '%s' not found\n", g->block->selectors.uo->slots[op2].us->name);
				slotCopy(++sp, (PyrSlot*)&gSpecialValues[svNil]);
			}
			ENDOP;
		OP_(1) : // opExtended, opPushInstVar
			op2 = ip[1]; ++ip; // get inst var index
			slotCopy(++sp, &g->receiver.uo->slots[op2]);
			ENDOP;
		OP_(2) : // opExtended, opPushTempVar
			op2 = ip[1]; // get temp var level
			op3 = ip[2]; // get temp var index
			ip += 2;
			for (tframe = g->frame; --op2; tframe = tframe->context.uof) { /* noop */ }
			slotCopy(++sp, &tframe->vars[op3]);
			ENDOP;
		OP_(3) : // opExtended, opPushTempZeroVar
			op2 = ip[1]; ++ip; // get temp var index
			slotCopy(++sp, &g->frame->vars[op2]);
			ENDOP;
		OP_(4) : // opExtended, opPushLiteral
			op2 = ip[1]; ++ip; // get literal index
			// push a block as a closure if it is one
			slot = g->block->selectors.uo->slots + op2;
			if (IsObj(slot) && slot->uo->classptr == gSpecialClasses[op_class_fundef]->u.classobj) {
				// push a closure
				g->sp = sp; // gc may push the stack
				closure = (PyrClosure*)g->gc->New(2*sizeof(PyrSlot), 0, obj_notindexed, true);
				sp = g->sp;
				closure->classptr = gSpecialClasses[op_class_func]->u.classobj;
				closure->size = 2;
				slotCopy(&closure->block, slot);
				if (IsNil(&slot->uoblk->contextDef)) {
					slotCopy(&closure->context, &g->process->interpreter.uoi->context);
				} else {
					SetObject(&closure->context, g->frame);
				}
				++sp; SetObject(sp, closure);
			} else {
				slotCopy(++sp, slot);
			}
			ENDOP;
		OP_(5) : // opExtended, opPushClassVar
			op2 = ip[1]; // get class
			op3 = ip[2]; // get class var index
			ip += 2;
			slotCopy(++sp, &g->classvars->slots[(op2<<8)|op3]);
			ENDOP;
		OP_(6) :  // opExtended, opPushSpecialValue == push a special class
			op2 = ip[1]; ++ip; // get class name index
			classobj = gSpecialClasses[op2]->u.classobj;
			if (classobj) {
				++sp; SetObject(sp, classobj);
			} else {
				slotCopy(++sp, (PyrSlot*)&gSpecialValues[svNil]);
			}
			ENDOP;
		OP_(7) : // opExtended, opStoreInstVar
			op2 = ip[1]; ++ip; // get inst var index
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + op2;
				slotCopy(slot, sp);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(8) : // opExtended, opStoreTempVar
			op2 = ip[1]; // get temp var level
			op3 = ip[2]; // get temp var index
			ip += 2;
			for (tframe = g->frame; op2--; tframe = tframe->context.uof) { /* noop */ }
			slot = tframe->vars + op3;
			slotCopy(slot, sp);
			g->gc->GCWrite(tframe, slot);
			ENDOP;
		OP_(9) : // opExtended, opStoreClassVar
			op2 = ip[1]; // get index of class name literal
			op3 = ip[2]; // get class var index
			ip += 2;
			slotCopy(&g->classvars->slots[(op2<<8)|op3], sp);
			g->gc->GCWrite(g->classvars, sp);
			ENDOP;
		OP_(10) : // opExtended, opSendMsg
			numArgsPushed = ip[1]; // get num args
			numKeyArgsPushed = ip[2]; // get num keyword args
			op3 = ip[3]; // get selector index
			ip += 3;
			selector = g->block->selectors.uo->slots[op3].us;

			slot = sp - numArgsPushed + 1;

			if (numKeyArgsPushed) goto key_class_lookup;
			else goto class_lookup;

		OP_(11) : // opExtended, opSendSuper
			numArgsPushed = ip[1]; // get num args
			numKeyArgsPushed = ip[2]; // get num keyword args
			op3 = ip[3]; // get selector index
			ip += 3;
			selector = g->block->selectors.uo->slots[op3].us;

			slot = g->sp - numArgsPushed + 1;
			classobj = g->method->ownerclass.uoc->superclass.us->u.classobj;

			if (numKeyArgsPushed) goto key_msg_lookup;
			else goto msg_lookup;

		OP_(12) :  // opExtended, opSendSpecialMsg
			numArgsPushed = ip[1]; // get num args
			numKeyArgsPushed = ip[2]; // get num keyword args
			op3 = ip[3]; // get selector index
			ip += 3;

			selector = gSpecialSelectors[op3];
			slot = sp - numArgsPushed + 1;

			if (numKeyArgsPushed) goto key_class_lookup;
			else goto class_lookup;

		OP_(13) :  // opExtended, opSendSpecialUnaryArithMsg
			op2 = ip[1]; ++ip; // get selector index
			g->sp = sp; g->ip = ip;
			g->primitiveIndex = op2;
			doSpecialUnaryArithMsg(g, -1);
#if TAILCALLOPTIMIZE
			g->tailCall = 0;
#endif
			sp = g->sp; ip = g->ip;
			ENDOP;
		OP_(14) :  // opExtended, opSendSpecialBinaryArithMsg
			op2 = ip[1]; ++ip; // get selector index
			g->sp = sp; g->ip = ip;
			g->primitiveIndex = op2;
			doSpecialBinaryArithMsg(g, 2, false);
			sp = g->sp; ip = g->ip;
			ENDOP;
		OP_(15) : // opExtended, opSpecialOpcode (none yet)
			op2 = ip[1]; ++ip; // get extended special opcode
			switch (op2) {
				case opgProcess : // push thisProcess
					++sp; SetObject(sp, g->process); ENDOP;
				case opgThread : // push thisProcess
					++sp; SetObject(sp, g->thread); ENDOP;
				case opgMethod : // push thisMethod
					++sp; SetObject(sp, g->method); ENDOP;
				case opgFunctionDef : // push thisFunctionDef
					++sp; SetObject(sp, g->block); ENDOP;
				case opgFunction : // push thisFunc
					// push a closure
					g->sp = sp; // gc may push the stack
					closure = (PyrClosure*)g->gc->New(2*sizeof(PyrSlot), 0, obj_notindexed, true);
					sp = g->sp;
					closure->classptr = gSpecialClasses[op_class_func]->u.classobj;
					closure->size = 2;
					SetObject(&closure->block, g->block);
					SetObject(&closure->context, g->frame->context.uof);
					++sp; SetObject(sp, closure);
					ENDOP;
				default :
					slotCopy(++sp, (PyrSlot*)&gSpecialValues[svNil]); ENDOP;
			}
			ENDOP;
		// opPushInstVar, 0..15
		OP_(16) : slotCopy(++sp, &g->receiver.uo->slots[ 0]); ENDOP;
		OP_(17) : slotCopy(++sp, &g->receiver.uo->slots[ 1]); ENDOP;
		OP_(18) : slotCopy(++sp, &g->receiver.uo->slots[ 2]); ENDOP;
		OP_(19) : slotCopy(++sp, &g->receiver.uo->slots[ 3]); ENDOP;
		OP_(20) : slotCopy(++sp, &g->receiver.uo->slots[ 4]); ENDOP;
		OP_(21) : slotCopy(++sp, &g->receiver.uo->slots[ 5]); ENDOP;
		OP_(22) : slotCopy(++sp, &g->receiver.uo->slots[ 6]); ENDOP;
		OP_(23) : slotCopy(++sp, &g->receiver.uo->slots[ 7]); ENDOP;
		OP_(24) : slotCopy(++sp, &g->receiver.uo->slots[ 8]); ENDOP;
		OP_(25) : slotCopy(++sp, &g->receiver.uo->slots[ 9]); ENDOP;
		OP_(26) : slotCopy(++sp, &g->receiver.uo->slots[10]); ENDOP;
		OP_(27) : slotCopy(++sp, &g->receiver.uo->slots[11]); ENDOP;
		OP_(28) : slotCopy(++sp, &g->receiver.uo->slots[12]); ENDOP;
		OP_(29) : slotCopy(++sp, &g->receiver.uo->slots[13]); ENDOP;
		OP_(30) : slotCopy(++sp, &g->receiver.uo->slots[14]); ENDOP;
		OP_(31) : slotCopy(++sp, &g->receiver.uo->slots[15]); ENDOP;

		OP_(32) : // JumpIfTrue
			// cannot compare with o_false because it is NaN
			if ( IsTrue(sp) ) {
				jmplen = (ip[1]<<8) | ip[2];
				ip += jmplen + 2;
			} else if ( IsFalse(sp)) {
				ip+=2;
			} else {
				numArgsPushed = 1;
				selector = gSpecialSelectors[opmNonBooleanError];
				slot = sp;

				goto class_lookup;
			}
			--sp;
			ENDOP;

		// opPushTempVar, levels 1..7
		OP_(33) : slotCopy(++sp, &g->frame->context.uof->vars[ip[1]]); ++ip; ENDOP;
		OP_(34) : slotCopy(++sp, &g->frame->context.uof->context.uof->vars[ip[1]]); ++ip; ENDOP;
		OP_(35) : slotCopy(++sp, &g->frame->context.uof->context.uof->context.uof->vars[ip[1]]); ++ip; ENDOP;
		OP_(36) : slotCopy(++sp, &g->frame->context.uof->context.uof->context.uof->
					context.uof->vars[ip[1]]); ++ip; ENDOP;
		OP_(37) : slotCopy(++sp, &g->frame->context.uof->context.uof->context.uof->
					context.uof->context.uof->vars[ip[1]]); ++ip; ENDOP;
		OP_(38) : slotCopy(++sp, &g->frame->context.uof->context.uof->context.uof->
					context.uof->context.uof->context.uof->vars[ip[1]]); ++ip; ENDOP;
		OP_(39) : slotCopy(++sp, &g->frame->context.uof->context.uof->context.uof->
					context.uof->context.uof->context.uof->context.uof->vars[ip[1]]); ++ip; ENDOP;

		// push literal constants.
		OP_(40) :
			ival = ip[1];
			ip+=1;
			slotCopy(++sp, &g->block->constants.uo->slots[ival]);
			ENDOP;
		OP_(41) :
			ival = (ip[1] << 8) | ip[2];
			ip+=2;
			slotCopy(++sp, &g->block->constants.uo->slots[ival]);
			ENDOP;
		OP_(42) :
			ival = (ip[1] << 16) | (ip[2] << 8) | ip[3];
			ip+=3;
			slotCopy(++sp, &g->block->constants.uo->slots[ival]);
			ENDOP;
		OP_(43) :
			ival = (ip[1] << 24) | (ip[2] << 16) | (ip[3] << 8) | ip[4];
			ip+=4;
			slotCopy(++sp, &g->block->constants.uo->slots[ival]);
			ENDOP;

		// push integers.
		OP_(44) :
			ival = (int32)(ip[1] << 24) >> 24;
			ip+=1;
			++sp; SetInt(sp, ival);
			ENDOP;
		OP_(45) :
			ival = (int32)((ip[1] << 24) | (ip[2] << 16)) >> 16;
			ip+=2;
			++sp; SetInt(sp, ival);
			ENDOP;
		OP_(46) :
			ival = (int32)((ip[1] << 24) | (ip[2] << 16) | (ip[3] << 8)) >> 8;
			ip+=3;
			++sp; SetInt(sp, ival);
			ENDOP;
		OP_(47) :
			ival = (int32)((ip[1] << 24) | (ip[2] << 16) | (ip[3] << 8) | ip[4]);
			ip+=4;
			++sp; SetInt(sp, ival);
			ENDOP;


		// opPushTempZeroVar
		OP_(48) : slotCopy(++sp, &g->frame->vars[ 0]); ENDOP;
		OP_(49) : slotCopy(++sp, &g->frame->vars[ 1]); ENDOP;
		OP_(50) : slotCopy(++sp, &g->frame->vars[ 2]); ENDOP;
		OP_(51) : slotCopy(++sp, &g->frame->vars[ 3]); ENDOP;
		OP_(52) : slotCopy(++sp, &g->frame->vars[ 4]); ENDOP;
		OP_(53) : slotCopy(++sp, &g->frame->vars[ 5]); ENDOP;
		OP_(54) : slotCopy(++sp, &g->frame->vars[ 6]); ENDOP;
		OP_(55) : slotCopy(++sp, &g->frame->vars[ 7]); ENDOP;
		OP_(56) : slotCopy(++sp, &g->frame->vars[ 8]); ENDOP;
		OP_(57) : slotCopy(++sp, &g->frame->vars[ 9]); ENDOP;
		OP_(58) : slotCopy(++sp, &g->frame->vars[10]); ENDOP;
		OP_(59) : slotCopy(++sp, &g->frame->vars[11]); ENDOP;
		OP_(60) : slotCopy(++sp, &g->frame->vars[12]); ENDOP;
		OP_(61) : slotCopy(++sp, &g->frame->vars[13]); ENDOP;
		OP_(62) : slotCopy(++sp, &g->frame->vars[14]); ENDOP;
		OP_(63) : slotCopy(++sp, &g->frame->vars[15]); ENDOP;

		// case opPushLiteral
		OP_(64) : slotCopy(++sp, &g->block->constants.uo->slots[ 0]); ENDOP;
		OP_(65) : slotCopy(++sp, &g->block->constants.uo->slots[ 1]); ENDOP;
		OP_(66) : slotCopy(++sp, &g->block->constants.uo->slots[ 2]); ENDOP;
		OP_(67) : slotCopy(++sp, &g->block->constants.uo->slots[ 3]); ENDOP;
		OP_(68) : slotCopy(++sp, &g->block->constants.uo->slots[ 4]); ENDOP;
		OP_(69) : slotCopy(++sp, &g->block->constants.uo->slots[ 5]); ENDOP;
		OP_(70) : slotCopy(++sp, &g->block->constants.uo->slots[ 6]); ENDOP;
		OP_(71) : slotCopy(++sp, &g->block->constants.uo->slots[ 7]); ENDOP;
		OP_(72) : slotCopy(++sp, &g->block->constants.uo->slots[ 8]); ENDOP;
		OP_(73) : slotCopy(++sp, &g->block->constants.uo->slots[ 9]); ENDOP;
		OP_(74) : slotCopy(++sp, &g->block->constants.uo->slots[10]); ENDOP;
		OP_(75) : slotCopy(++sp, &g->block->constants.uo->slots[11]); ENDOP;
		OP_(76) : slotCopy(++sp, &g->block->constants.uo->slots[12]); ENDOP;
		OP_(77) : slotCopy(++sp, &g->block->constants.uo->slots[13]); ENDOP;
		OP_(78) : slotCopy(++sp, &g->block->constants.uo->slots[14]); ENDOP;
		OP_(79) : slotCopy(++sp, &g->block->constants.uo->slots[15]); ENDOP;

		//	opPushClassVar
		OP_(80) :  OP_(81) :  OP_(82) :  OP_(83) :
		OP_(84) :  OP_(85) :  OP_(86) :  OP_(87) :
		OP_(88) :  OP_(89) :  OP_(90) :  OP_(91) :
		OP_(92) :  OP_(93) :  OP_(94) :  OP_(95) :
			op2 = op1 & 15;
			op3 = ip[1]; ++ip; // get class var index
			slotCopy(++sp, &g->classvars->slots[(op2<<8)|op3]);
			ENDOP;

		// opPushSpecialValue
		OP_(96) : slotCopy(++sp, &g->receiver); ENDOP;
		OP_(97) : // push one and subtract
			if (IsInt(sp)) {
				sp->ui--;
#if TAILCALLOPTIMIZE
				g->tailCall = 0;
#endif
			} else {
				slotCopy(++sp, (PyrSlot*)&gSpecialValues[svOne]);
				g->sp = sp; g->ip = ip;
				g->primitiveIndex = opSub;
				prSubNum(g, -1);
				sp = g->sp; ip = g->ip;
			}
			ENDOP;
		OP_(98) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svNegOne]); ENDOP;
		OP_(99) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svZero]); ENDOP;
		OP_(100) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svOne]); ENDOP;
		OP_(101) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svTwo]); ENDOP;
		OP_(102) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svFHalf]); ENDOP;
		OP_(103) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svFNegOne]); ENDOP;
		OP_(104) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svFZero]); ENDOP;
		OP_(105) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svFOne]); ENDOP;
		OP_(106) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svFTwo]); ENDOP;
		OP_(107) : // push one and add
			if (IsInt(sp)) {
				sp->ui++;
#if TAILCALLOPTIMIZE
				g->tailCall = 0;
#endif
			} else {
				slotCopy(++sp, (PyrSlot*)&gSpecialValues[svOne]);
				g->sp = sp; g->ip = ip;
				g->primitiveIndex = opAdd;
				prAddNum(g, -1);
				sp = g->sp; ip = g->ip;
			}
			ENDOP;
		OP_(108) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svTrue]); ENDOP;
		OP_(109) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svFalse]); ENDOP;
		OP_(110) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svNil]); ENDOP;
		OP_(111) : slotCopy(++sp, (PyrSlot*)&gSpecialValues[svInf]); ENDOP;

		// opStoreInstVar, 0..15
#if 1
		OP_(112) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(113) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 1;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(114) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 2;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(115) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 3;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(116) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 4;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(117) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 5;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(118) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 6;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(119) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 7;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(120) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 8;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(121) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 9;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(122) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 10;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(123) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 11;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(124) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 12;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(125) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 13;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(126) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 14;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
		OP_(127) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + 15;
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
#else
		OP_(112) :  OP_(113) :  OP_(114) :  OP_(115) :
		OP_(116) :  OP_(117) :  OP_(118) :  OP_(119) :
		OP_(120) :  OP_(121) :  OP_(122) :  OP_(123) :
		OP_(124) :  OP_(125) :  OP_(126) :  OP_(127) :
			obj = g->receiver.uo;
			if (obj->obj_flags & obj_immutable) { StoreToImmutableA(g, (PyrSlot*&)sp, ip); }
			else {
				slot = obj->slots + (op1 & 15);
				slotCopy(slot, sp--);
				g->gc->GCWrite(obj, slot);
			}
			ENDOP;
#endif

		// opStoreTempVar
		OP_(128) :
			op3 = ip[1]; ++ip;  // get temp var index
			tframe = g->frame; // zero level
			slot = tframe->vars + op3;
			slotCopy(slot, sp--);
			g->gc->GCWrite(tframe, slot);
			ENDOP;

		OP_(129) :
			op3 = ip[1]; ++ip;  // get temp var index
			tframe = g->frame->context.uof; // one level
			slot = tframe->vars + op3;
			slotCopy(slot, sp--);
			g->gc->GCWrite(tframe, slot);
			ENDOP;

		OP_(130) :
			op3 = ip[1]; ++ip;  // get temp var index
			tframe = g->frame->context.uof->context.uof; // two levels
			slot = tframe->vars + op3;
			slotCopy(slot, sp--);
			g->gc->GCWrite(tframe, slot);
			ENDOP;

		OP_(131) :
			op3 = ip[1]; ++ip;  // get temp var index
			tframe = g->frame->context.uof->context.uof->context.uof; // three levels
			slot = tframe->vars + op3;
			slotCopy(slot, sp--);
			g->gc->GCWrite(tframe, slot);
			ENDOP;

		OP_(132) :
			op3 = ip[1]; ++ip;  // get temp var index
			tframe = g->frame->context.uof->context.uof->context.uof->context.uof; // four levels
			slot = tframe->vars + op3;
			slotCopy(slot, sp--);
			g->gc->GCWrite(tframe, slot);
			ENDOP;

		OP_(133) : OP_(134) : OP_(135) :
			op2 = op1 & 15;
			op3 = ip[1]; ++ip; // get temp var index
			for (tframe = g->frame; op2--; tframe = tframe->context.uof) { /* noop */ }
			slot = tframe->vars + op3;
			slotCopy(slot, sp);
			g->gc->GCWrite(tframe, slot);
			ENDOP;

		OP_(136) :  // push inst var, send special selector
			op2 = ip[1]; // get inst var index
			op3 = ip[2]; // get selector
			ip+=2;

			slotCopy(++sp, &g->receiver.uo->slots[op2]);

			numArgsPushed = 1;
			selector = gSpecialSelectors[op3];
			slot = sp;

			goto class_lookup;

		OP_(137) :  // push all args, send msg
			numArgsPushed = METHRAW(g->block)->numargs;
			pslot = g->frame->vars - 1;
			for (m=0,mmax=numArgsPushed; m<mmax; ++m) *++sp = *++pslot;

			op2 = ip[1]; ++ip; // get selector index
			selector = g->block->selectors.uo->slots[op2].us;
			slot = sp - numArgsPushed + 1;

			goto class_lookup;

		OP_(138) :  // push all but first arg, send msg
			numArgsPushed = METHRAW(g->block)->numargs;
			pslot = g->frame->vars;
			for (m=0,mmax=numArgsPushed-1; m<mmax; ++m) *++sp = *++pslot;

			op2 = ip[1]; ++ip; // get selector index
			selector = g->block->selectors.uo->slots[op2].us;
			slot = sp - numArgsPushed + 1;

			goto class_lookup;

		OP_(139) :  // push all args, send special
			numArgsPushed = METHRAW(g->block)->numargs;
			pslot = g->frame->vars - 1;
			for (m=0,mmax=numArgsPushed; m<mmax; ++m) *++sp = *++pslot;

			op2 = ip[1]; ++ip; // get selector
			selector = gSpecialSelectors[op2];
			slot = sp - numArgsPushed + 1;

			goto class_lookup;

		OP_(140) :  // push all but first arg, send special
			numArgsPushed = METHRAW(g->block)->numargs;
			pslot = g->frame->vars;
			for (m=0,mmax=numArgsPushed-1; m<mmax; ++m) *++sp = *++pslot;

			op2 = ip[1]; ++ip; // get selector
			selector = gSpecialSelectors[op2];
			slot = sp - numArgsPushed + 1;

			goto class_lookup;

		OP_(141) :  // one arg pushed, push all but first arg, send msg
			numArgsPushed = METHRAW(g->block)->numargs + 1;
			pslot = g->frame->vars;
			for (m=0,mmax=numArgsPushed-2; m<mmax; ++m) *++sp = *++pslot;

			op2 = ip[1]; ++ip; // get selector index
			selector = g->block->selectors.uo->slots[op2].us;
			slot = sp - numArgsPushed + 1;

			goto class_lookup;

		OP_(142) :  // one arg pushed, push all but first arg, send special
			numArgsPushed = METHRAW(g->block)->numargs + 1;
			pslot = g->frame->vars;
			for (m=0,mmax=numArgsPushed-2; m<mmax; ++m) *++sp = *++pslot;

			op2 = ip[1]; ++ip; // get selector
			selector = gSpecialSelectors[op2];
			slot = sp - numArgsPushed + 1;

			goto class_lookup;

		OP_(143) : // loop byte codes
			// this is major cheating to speed up often used looping methods
			// these byte codes are specific to their method and should only be used there.
			op2 = ip[1]; ++ip; // get which one
			switch (op2) {
				// Integer-do : 143 0, 143 1
				case 0 :
					vars = g->frame->vars;
					if (vars[2].ui < g->receiver.ui) {
						slotCopy(++sp, &vars[1]); // push function
						slotCopy(++sp, &vars[2]); // push i
						slotCopy(++sp, &vars[2]); // push i
						// SendSpecialMsg value
						numArgsPushed = 3;
						selector = gSpecialSelectors[opmValue];
						slot = sp - 2;

						goto class_lookup;
					} else {
						slotCopy(++sp, &g->receiver);
						g->sp = sp; g->ip = ip;
						returnFromMethod(g);
						sp = g->sp; ip = g->ip;
					}
				break;
				case 1 :
					-- sp ; // Drop
					g->frame->vars[2].ui ++; // inc i
					ip -= 4;
					break;

				// Integer-reverseDo : 143 2, 143 3, 143 4
				case 2 :
					g->frame->vars[2].ui = g->receiver.ui - 1;
					break;
				case 3 :
					vars = g->frame->vars;
					if (vars[2].ui >= 0) {
						slotCopy(++sp, &vars[1]); // push function
						slotCopy(++sp, &vars[2]); // push i
						slotCopy(++sp, &vars[3]); // push j
						// SendSpecialMsg value
						numArgsPushed = 3;
						selector = gSpecialSelectors[opmValue];
						slot = sp - 2;

						goto class_lookup;
					} else {
						slotCopy(++sp, &g->receiver);
						g->sp = sp; g->ip = ip;
						returnFromMethod(g);
						sp = g->sp; ip = g->ip;
					}
					break;
				case 4 :
					-- sp ; // Drop
					vars = g->frame->vars;
					vars[2].ui --; // dec i
					vars[3].ui ++; // inc j
					ip -= 4;
					break;

				// Integer-for : 143 5, 143 6, 143 16
				case 5 :
					vars = g->frame->vars;
					tag = vars[1].utag;

					if (tag != tagInt) {
						if (IsFloat(&vars[1])) {
							// coerce to int
							SetInt(&vars[1], (int32)(vars[1].uf));
						} else {
							error("Integer-for : endval not a SimpleNumber.\n");

							slotCopy(++sp, &g->receiver);
							numArgsPushed = 1;
							selector = gSpecialSelectors[opmPrimitiveFailed];
							slot = sp;

							goto class_lookup;
						}
					}

					if (g->receiver.ui <= vars[1].ui) {
						vars[5].ui = 1;
					} else {
						vars[5].ui = -1;
					}
					slotCopy(&vars[3], &g->receiver);

					break;
				case 6 :
					vars = g->frame->vars;
					if ((vars[5].ui > 0 && vars[3].ui <= vars[1].ui)
							|| (vars[5].ui < 0 && vars[3].ui >= vars[1].ui))
					{
						slotCopy(++sp, &vars[2]); // push function
						slotCopy(++sp, &vars[3]); // push i
						slotCopy(++sp, &vars[4]); // push j
						// SendSpecialMsg value
						numArgsPushed = 3;
						selector = gSpecialSelectors[opmValue];
						slot = sp - 2;

						goto class_lookup;
					} else {
						slotCopy(++sp, &g->receiver);
						g->sp = sp; g->ip = ip;
						returnFromMethod(g);
						sp = g->sp; ip = g->ip;
					}
					break;

				// Integer-forBy : 143 7, 143 8, 143 9
				case 7 :
					vars = g->frame->vars;
					if (IsFloat(vars+1)) {
						SetInt(&vars[1], (int32)(vars[1].uf));
					}
					if (IsFloat(vars+2)) {
						SetInt(&vars[2], (int32)(vars[2].uf));
					}
					tag = vars[1].utag;
					if ((tag != tagInt)
							|| NotInt(&vars[2])) {
						error("Integer-forBy : endval or stepval not an Integer.\n");

						slotCopy(++sp, &g->receiver);
						numArgsPushed = 1;
						selector = gSpecialSelectors[opmPrimitiveFailed];
						slot = sp;

						goto class_lookup;
					}
					slotCopy(&vars[4], &g->receiver);
					break;
				case 8 :
					vars = g->frame->vars;
					if ((vars[2].ui >= 0 && vars[4].ui <= vars[1].ui)
							|| (vars[2].ui < 0 && vars[4].ui >= vars[1].ui)) {
						slotCopy(++sp, &vars[3]); // push function
						slotCopy(++sp, &vars[4]); // push i
						slotCopy(++sp, &vars[5]); // push j
						// SendSpecialMsg value
						numArgsPushed = 3;
						selector = gSpecialSelectors[opmValue];
						slot = sp - 2;

						goto class_lookup;
					} else {
						slotCopy(++sp, &g->receiver);
						g->sp = sp; g->ip = ip;
						returnFromMethod(g);
						sp = g->sp; ip = g->ip;
					}
					break;
				case 9 :
					--sp ; // Drop
					vars = g->frame->vars;
					vars[4].ui += vars[2].ui; // inc i
					++ vars[5].ui; // inc j
					ip -= 4;
					break;

				// ArrayedCollection-do : 143 10, 143 1
				case 10 :
					// 0 this, 1 func, 2 i
					vars = g->frame->vars;

					if (vars[2].ui < g->receiver.uo->size) {
						slotCopy(++sp, &vars[1]); // push function
						getIndexedSlot(g->receiver.uo, ++sp, vars[2].ui); // push this.at(i)
						slotCopy(++sp, &vars[2]); // push i
						// SendSpecialMsg value
						numArgsPushed = 3;
						selector = gSpecialSelectors[opmValue];
						slot = sp - 2;

						goto class_lookup;
					} else {
						slotCopy(++sp, &g->receiver);
						g->sp = sp; g->ip = ip;
						returnFromMethod(g);
						sp = g->sp; ip = g->ip;
					}
					break;

				// ArrayedCollection-reverseDo : 143 11, 143 12, 143 4
				case 11 :
					g->frame->vars[2].ui = g->receiver.uo->size - 1;
					break;
				case 12 :
					vars = g->frame->vars;
					if (vars[2].ui >= 0) {
						slotCopy(++sp, &vars[1]); // push function
						getIndexedSlot(g->receiver.uo, ++sp, vars[2].ui); // push this.at(i)
						slotCopy(++sp, &vars[3]); // push j
						// SendSpecialMsg value
						numArgsPushed = 3;
						selector = gSpecialSelectors[opmValue];
						slot = sp - 2;

						goto class_lookup; // class_lookup:
					} else {
						slotCopy(++sp, &g->receiver);
						g->sp = sp; g->ip = ip;
						returnFromMethod(g);
						sp = g->sp; ip = g->ip;
					}
					break;

				// Dictionary-keysValuesArrayDo
				case 13 :
					vars = g->frame->vars;
					m = vars[3].ui;
					obj = vars[1].uo;
					if ( m < obj->size ) {
						slot = obj->slots + m;	// key
						while (IsNil(slot)) {
							m += 2;
							if ( m >= obj->size ) {
								vars[3].ui = m;
								goto keysValuesArrayDo_return;
							}
							slot = obj->slots + m;	// key
						}
						vars[3].ui = m;
						slotCopy(++sp, &vars[2]); // function
						slotCopy(++sp, &slot[0]); // key
						slotCopy(++sp, &slot[1]); // val
						slotCopy(++sp, &vars[4]); // j
						++vars[4].ui;

						// SendSpecialMsg value
						numArgsPushed = 4;
						selector = gSpecialSelectors[opmValue];
						slot = sp - 3;

						goto class_lookup; // class_lookup:
					} else {
						keysValuesArrayDo_return:
						slotCopy(++sp, &g->receiver);
						g->sp = sp; g->ip = ip;
						returnFromMethod(g);
						sp = g->sp; ip = g->ip;
					}
					break;
				case 14 :
					-- sp; // Drop
					g->frame->vars[3].ui += 2; // inc i
					ip -= 4;
					break;
				case 15 :
					// unused opcode.
					break;

				case 16 :
					-- sp ; // Drop
					vars = g->frame->vars;
					vars[3].ui += vars[5].ui; // inc i by stepval
					++ vars[4].ui; // inc j
					ip -= 4;
					break;

				// Float-do : 143 17, 143 18
				case 17 :
					vars = g->frame->vars;
					if (vars[2].uf + 0.5 < g->receiver.uf) {
						slotCopy(++sp, &vars[1]); // push function
						slotCopy(++sp, &vars[2]); // push i
						slotCopy(++sp, &vars[2]); // push i
						// SendSpecialMsg value
						numArgsPushed = 3;
						selector = gSpecialSelectors[opmValue];
						slot = sp - 2;

						goto class_lookup;
					} else {
						slotCopy(++sp, &g->receiver);
						g->sp = sp; g->ip = ip;
						returnFromMethod(g);
						sp = g->sp; ip = g->ip;
					}
					break;
				case 18 :
					-- sp ; // Drop
					g->frame->vars[2].uf += 1.0; // inc i
					ip -= 4;
					break;

				// Float-reverseDo : 143 19, 143 20, 143 21
				case 19 :
					g->frame->vars[2].uf = g->receiver.uf - 1.0;
					break;
				case 20 :
					vars = g->frame->vars;
					if (vars[2].uf + 0.5 >= 0.0) {
						slotCopy(++sp, &vars[1]); // push function
						slotCopy(++sp, &vars[2]); // push i
						slotCopy(++sp, &vars[3]); // push j
						// SendSpecialMsg value
						numArgsPushed = 3;
						selector = gSpecialSelectors[opmValue];
						slot = sp - 2;

						goto class_lookup;
					} else {
						slotCopy(++sp, &g->receiver);
						g->sp = sp; g->ip = ip;
						returnFromMethod(g);
						sp = g->sp; ip = g->ip;
					}
					break;
				case 21 :
					-- sp ; // Drop
					vars = g->frame->vars;
					vars[2].uf -= 1.0; // dec i
					vars[3].uf += 1.0; // inc j
					ip -= 4;
					break;
				case 22 : // ? question mark method
					--sp;
					if (IsNil(sp)) {
						*sp = *(sp+1);
					}
					break;
				case 23 : // if not nil push this and jump. used to implement ??
					if (NotNil(sp)) {
						jmplen = (ip[1]<<8) | ip[2];
						ip += jmplen + 2;
					} else {
						--sp;
						ip+=2;
					}
					break;
				case 24 : // ifNil
					if ( NotNil(sp) ) {
						jmplen = (ip[1]<<8) | ip[2];
						ip += jmplen + 2;
					} else {
						ip+=2;
					}
					--sp;
					break;
				case 25 : // ifNotNil
					if ( IsNil(sp) ) {
						jmplen = (ip[1]<<8) | ip[2];
						ip += jmplen + 2;
					} else {
						ip+=2;
					}
					--sp;
					break;
				case 26 : // ifNotNilPushNil
					if ( NotNil(sp) ) {
						jmplen = (ip[1]<<8) | ip[2];
						ip += jmplen + 2;
						slotCopy(sp, (PyrSlot*)&gSpecialValues[svNil]);
					} else {
						ip+=2;
						--sp;
					}
					break;
				case 27 : // ifNilPushNil
					if ( IsNil(sp) ) {
						jmplen = (ip[1]<<8) | ip[2];
						ip += jmplen + 2;
					} else {
						ip+=2;
						--sp;
					}
					break;
				case 28 : // switch
					obj = sp->uo;
					op2 = 1 + arrayAtIdentityHashInPairs(obj, (sp-1));
					sp-=2;
					ip += obj->slots[op2].ui;
					break;

				// Number-forSeries : 143 29, 143 30, 143 31
				case 29 :
					vars = g->frame->vars;
					// 0 receiver, 1 step, 2 last, 3 function, 4 i, 5 j
					if (IsInt(vars+0) && (IsInt(vars+1) || IsNil(vars+1)) && (IsInt(vars+2) || IsNil(vars+2))) {
						if (IsNil(vars+1)) {
							if (IsNil(vars+2)) SetInt(vars+2, 0x7FFFFFFF);
							if (vars[0].ui < vars[2].ui) SetInt(vars+1, 1);
							else SetInt(vars+1, -1);
						} else {
							if (IsNil(vars+2)) {
								if (vars[1].ui < vars[0].ui) SetInt(vars+2, 0x80000000);
								else SetInt(vars+2, 0x7FFFFFFF);
							}
							SetInt(vars+1, vars[1].ui - vars[0].ui);
						}
						slotCopy(&vars[4], &vars[0]);
					} else {
						if (IsInt(vars+0)) {
							vars[4].uf = vars[0].ui;
						} else if (IsFloat(vars+0)) {
							vars[4].uf = vars[0].uf;
						} else {
							bailFromNumberSeries:
							error("Number-forSeries : first, second or last not an Integer or Float.\n");

							slotCopy(++sp, &g->receiver);
							numArgsPushed = 1;
							selector = gSpecialSelectors[opmPrimitiveFailed];
							slot = sp;

							goto class_lookup;
						}

						if (IsNil(vars+1)) {
							if (IsNil(vars+2)) SetFloat(vars+2, kBigBigFloat);
							else if (IsInt(vars+2)) vars[2].uf = vars[2].ui;
							else if (!IsFloat(vars+2)) goto bailFromNumberSeries;

							if (vars[4].uf < vars[2].uf) SetFloat(vars+1, 1.);
							else SetFloat(vars+1, -1.);
						} else {
							if (IsInt(vars+1)) vars[1].uf = vars[1].ui;
							else if (!IsFloat(vars+1)) goto bailFromNumberSeries;

							if (IsNil(vars+2)) {
								if (vars[1].uf < vars[4].uf) SetFloat(vars+2, kSmallSmallFloat);
								else SetFloat(vars+2, kBigBigFloat);
							}
							else if (IsInt(vars+2)) vars[2].uf = vars[2].ui;
							else if (!IsFloat(vars+2)) goto bailFromNumberSeries;
							SetFloat(vars+1, vars[1].uf - vars[4].uf);
						}
					}
					break;
				case 30 :
					vars = g->frame->vars;
					tag = vars[1].utag;
					if (tag == tagInt) {
						if ((vars[1].ui >= 0 && vars[4].ui <= vars[2].ui)
								|| (vars[1].ui < 0 && vars[4].ui >= vars[2].ui)) {
							slotCopy(++sp, &vars[3]); // push function
							slotCopy(++sp, &vars[4]); // push i
							slotCopy(++sp, &vars[5]); // push j
							// SendSpecialMsg value
							numArgsPushed = 3;
							selector = gSpecialSelectors[opmValue];
							slot = sp - 2;

							goto class_lookup;
						} else {
							slotCopy(++sp, &g->receiver);
							g->sp = sp; g->ip = ip;
							returnFromMethod(g);
							sp = g->sp; ip = g->ip;
						}
					} else {
						if ((vars[1].uf >= 0. && vars[4].uf <= vars[2].uf)
								|| (vars[1].uf < 0. && vars[4].uf >= vars[2].uf)) {
							slotCopy(++sp, &vars[3]); // push function
							slotCopy(++sp, &vars[4]); // push i
							slotCopy(++sp, &vars[5]); // push j
							// SendSpecialMsg value
							numArgsPushed = 3;
							selector = gSpecialSelectors[opmValue];
							slot = sp - 2;

							goto class_lookup;
						} else {
							slotCopy(++sp, &g->receiver);
							g->sp = sp; g->ip = ip;
							returnFromMethod(g);
							sp = g->sp; ip = g->ip;
						}
					}
					break;
				case 31 :
					-- sp ; // Drop
					vars = g->frame->vars;

					tag = vars[1].utag;
					if (tag == tagInt) {
						vars[4].ui += vars[1].ui; // inc i
					} else {
						vars[4].uf += vars[1].uf; // inc i
					}
					vars[5].ui ++; // inc j
					ip -= 4;
					break;

			}
			ENDOP;


		//	opStoreClassVar
		OP_(144) :  OP_(145) :  OP_(146) :  OP_(147) :
		OP_(148) :  OP_(149) :  OP_(150) :  OP_(151) :
		OP_(152) :  OP_(153) :  OP_(154) :  OP_(155) :
		OP_(156) :  OP_(157) :  OP_(158) :  OP_(159) :
			op2 = op1 & 15;
			op3 = ip[1]; ++ip; // get class var index
			slotCopy(&g->classvars->slots[(op2<<8)|op3], sp--);
			g->gc->GCWrite(g->classvars, (sp+1));
			ENDOP;

		// opSendMsg
		OP_(160) :
			// special case for this as only arg
			op2 = ip[1]; ++ip; // get selector index
			slotCopy(++sp, &g->receiver);
			numArgsPushed = 1;
			selector = g->block->selectors.uo->slots[op2].us;
			slot = sp;

			goto class_lookup;
		
		// SendMsg??
		OP_(161) :  OP_(162) :  OP_(163) :  
		OP_(164) :  OP_(165) :  OP_(166) :  OP_(167) :  
		OP_(168) :  OP_(169) :  OP_(170) :  OP_(171) :  
		OP_(172) :  OP_(173) :  OP_(174) :  OP_(175) :

			op2 = ip[1]; ++ip; // get selector index
			numArgsPushed = op1 & 15;
			selector = g->block->selectors.uo->slots[op2].us;
			slot = sp - numArgsPushed + 1;
			goto class_lookup;

		OP_(176) : // opcTailCallReturnFromFunction
#if TAILCALLOPTIMIZE
			g->tailCall = 2;
#endif
			ENDOP;
		// opSuperMsg
		OP_(177) :
			// special case for this as only arg
			op2 = ip[1]; ++ip; // get selector index
			slotCopy(++sp, &g->receiver);
			numArgsPushed = 1;
			selector = g->block->selectors.uo->slots[op2].us;
			slot = sp;
			classobj = g->method->ownerclass.uoc->superclass.us->u.classobj;

			goto msg_lookup;

		OP_(178) :  OP_(179) :
		OP_(180) :  OP_(181) :  OP_(182) :  OP_(183) :
		OP_(184) :  OP_(185) :  OP_(186) :  OP_(187) :
		OP_(188) :  OP_(189) :  OP_(190) :  OP_(191) :

			op2 = ip[1]; ++ip; // get selector index
			numArgsPushed = op1 & 15;
			selector = g->block->selectors.uo->slots[op2].us;
			slot = sp - numArgsPushed + 1;
			classobj = g->method->ownerclass.uoc->superclass.us->u.classobj;

			goto msg_lookup;

		// opSendSpecialMsg
		OP_(192) :

			slotCopy(++sp, &g->receiver);
			op2 = ip[1]; ++ip; // get selector index
			numArgsPushed = 1;
			selector = gSpecialSelectors[op2];
			slot = sp;

			goto class_lookup;

		OP_(193) :  OP_(194) :  OP_(195) :
		OP_(196) :  OP_(197) :  OP_(198) :  OP_(199) :
		OP_(200) :  OP_(201) :  OP_(202) :  OP_(203) :
		OP_(204) :  OP_(205) :  OP_(206) :  OP_(207) :

			op2 = ip[1]; ++ip; // get selector index
			numArgsPushed = op1 & 15;
			selector = gSpecialSelectors[op2];
			slot = sp - numArgsPushed + 1;

			goto class_lookup;

		// opSendSpecialUnaryArithMsg
		OP_(208) :  // opNeg
			if (IsFloat(sp)) {
				SetFloat(sp, -sp->uf);
#if TAILCALLOPTIMIZE
				g->tailCall = 0;
#endif
			} else if (IsInt(&sp[0])) {
				sp[0].ui = -sp[0].ui;
#if TAILCALLOPTIMIZE
				g->tailCall = 0;
#endif
			} else goto unary_send;
			ENDOP;
		OP_(209) : // opNot
			if (IsTrue(&sp[0])) {
				sp[0].utag = tagFalse;
#if TAILCALLOPTIMIZE
				g->tailCall = 0;
#endif
			} else if (IsFalse(&sp[0])) {
				sp[0].utag = tagTrue;
#if TAILCALLOPTIMIZE
				g->tailCall = 0;
#endif
			} else goto unary_send;
			ENDOP;
		OP_(210) : // opIsNil
			if (IsNil(&sp[0])) {
				sp[0].utag = tagTrue;
			} else {
				slotCopy(sp, (PyrSlot*)&gSpecialValues[svFalse]);
			}
#if TAILCALLOPTIMIZE
			g->tailCall = 0;
#endif
			ENDOP;
		OP_(211) : // opNotNil
			if (NotNil(&sp[0])) {
				slotCopy(sp, (PyrSlot*)&gSpecialValues[svTrue]);
			} else {
				sp[0].utag = tagFalse;
			}
#if TAILCALLOPTIMIZE
			g->tailCall = 0;
#endif
			ENDOP;

		OP_(212) :  OP_(213) :  OP_(214) :  OP_(215) :
		OP_(216) :  OP_(217) :  OP_(218) :  OP_(219) :
		OP_(220) :  OP_(221) :  OP_(222) :  OP_(223) :
			unary_send:
			g->sp = sp; g->ip = ip;
			g->primitiveIndex = op1 & 15;
			doSpecialUnaryArithMsg(g, -1);
			sp = g->sp; ip = g->ip;
			ENDOP;

		// opSendSpecialBinaryArithMsg
		OP_(224) : // add
			if (IsInt(&sp[-1])) {
				if (IsInt(&sp[0])) {
					--sp; sp[0].ui += sp[1].ui;
#if TAILCALLOPTIMIZE
					g->tailCall = 0;
#endif
				} else {
					g->sp = sp; g->ip = ip;
					g->primitiveIndex = opAdd;
					prAddInt(g, -1);
					sp = g->sp; ip = g->ip;
				}
			} else {
				g->sp = sp; g->ip = ip;
				g->primitiveIndex = opAdd;
				prAddNum(g, -1);
				sp = g->sp; ip = g->ip;
			}
			ENDOP;
		OP_(225) : // subtract
			if (IsInt(&sp[-1])) {
				if (IsInt(&sp[0])) {
					--sp; sp[0].ui -= sp[1].ui;
#if TAILCALLOPTIMIZE
					g->tailCall = 0;
#endif
				} else {
					g->sp = sp; g->ip = ip;
					g->primitiveIndex = opSub;
					prSubInt(g, -1);
					sp = g->sp; ip = g->ip;
				}
			} else {
				g->sp = sp; g->ip = ip;
				g->primitiveIndex = opSub;
				prSubNum(g, -1);
				sp = g->sp; ip = g->ip;
			}
			ENDOP;
		OP_(226) :  // multiply
			if (IsInt(&sp[-1])) {
				if (IsInt(&sp[0])) {
					--sp; sp[0].ui *= sp[1].ui;
#if TAILCALLOPTIMIZE
					g->tailCall = 0;
#endif
				} else {
					g->sp = sp; g->ip = ip;
					g->primitiveIndex = opMul;
					prMulInt(g, -1);
					sp = g->sp; ip = g->ip;
				}
			} else {
				g->sp = sp; g->ip = ip;
				g->primitiveIndex = opMul;
				prMulNum(g, -1);
				sp = g->sp; ip = g->ip;
			}
			ENDOP;

		OP_(227) :
		OP_(228) :  OP_(229) :  OP_(230) :  OP_(231) :
		OP_(232) :  OP_(233) :  OP_(234) :  OP_(235) :
		OP_(236) :  OP_(237) :  OP_(238) :  OP_(239) :
			g->sp = sp; g->ip = ip;
			g->primitiveIndex = op1 & 15;
			doSpecialBinaryArithMsg(g, 2, false);
			sp = g->sp; ip = g->ip;
			ENDOP;

		// opSpecialOpcodes
		// DROP 
		OP_(240):
			--sp; 
			ENDOP; // opDrop
		OP_(241) : ++sp; *sp = sp[-1]; ENDOP;	// opDup

		OP_(242) : // opcFunctionReturn
			g->sp = sp; g->ip = ip;
			returnFromBlock(g);
			sp = g->sp; ip = g->ip;
			ENDOP;
		OP_(243) : // opcReturn
			g->sp = sp; g->ip = ip;
			returnFromMethod(g);
			sp = g->sp; ip = g->ip;
			ENDOP;
		OP_(244) : // opcReturnSelf
		slotCopy(++sp, &g->receiver);
			g->sp = sp; g->ip = ip;
			returnFromMethod(g);
			sp = g->sp; ip = g->ip;
			ENDOP;
		OP_(245) : // opcReturnTrue
			slotCopy(++sp, (PyrSlot*)&gSpecialValues[svTrue]);
			g->sp = sp; g->ip = ip;
			returnFromMethod(g);
			sp = g->sp; ip = g->ip;
			ENDOP;
		OP_(246) : // opcReturnFalse
			slotCopy(++sp, (PyrSlot*)&gSpecialValues[svFalse]);
			g->sp = sp; g->ip = ip;
			returnFromMethod(g);
			sp = g->sp; ip = g->ip;
			ENDOP;
		OP_(247) : // opcReturnNil
			slotCopy(++sp, (PyrSlot*)&gSpecialValues[svNil]);
			g->sp = sp; g->ip = ip;
			returnFromMethod(g);
			sp = g->sp; ip = g->ip;
			ENDOP;

		OP_(248) : // opcJumpIfFalse
			// cannot compare with o_false because it is NaN
			if ( IsFalse(sp) ) {
				jmplen = (ip[1]<<8) | ip[2];
				ip += jmplen + 2;
			} else if ( IsTrue(sp)) {
				ip+=2;
			} else {
				numArgsPushed = 1;
				selector = gSpecialSelectors[opmNonBooleanError];
				slot = sp;

				goto class_lookup;
			}
			--sp;
			ENDOP;
		OP_(249) : // opcJumpIfFalsePushNil
			if ( IsFalse(sp)) {
				jmplen = (ip[1]<<8) | ip[2];
				ip += jmplen + 2;
				slotCopy(sp, (PyrSlot*)&gSpecialValues[svNil]);
			} else if ( IsTrue(sp)) {
				--sp;
				ip+=2;
			} else {
				numArgsPushed = 1;
				selector = gSpecialSelectors[opmNonBooleanError];
				slot = sp;

				goto class_lookup;
			}
			ENDOP;
		OP_(250) : // opcJumpIfFalsePushFalse
			if (IsFalse(sp)) {
				jmplen = (ip[1]<<8) | ip[2];
				ip += jmplen + 2;
				//*sp = r_false;
			} else if (IsTrue(sp)) {
				--sp;
				ip+=2;
			} else {
				numArgsPushed = 1;
				selector = gSpecialSelectors[opmNonBooleanError];
				slot = sp;

				goto class_lookup;
			}
			ENDOP;
		OP_(251) : // opcJumpIfTruePushTrue
			if (IsFalse(sp)) {
				--sp;
				ip+=2;
			} else if (IsTrue(sp)) {
				jmplen = (ip[1]<<8) | ip[2];
				ip += jmplen + 2;
				slotCopy(sp, (PyrSlot*)&gSpecialValues[svTrue]);
			} else {
				numArgsPushed = 1;
				selector = gSpecialSelectors[opmNonBooleanError];
				slot = sp;

				goto class_lookup;
			}
			ENDOP;
		OP_(252) : // opcJumpFwd
			jmplen = (ip[1]<<8) | ip[2];
			ip += jmplen + 2;
			ENDOP;
		OP_(253) : // opcJumpBak
			--sp; // also drops the stack. This saves an opcode in the while loop
					// which is the only place this opcode is used.
			jmplen = (ip[1]<<8) | ip[2];
			ip -= jmplen;

			//assert(g->gc->SanityCheck());
			ENDOP;
		OP_(254) : // opcSpecialBinaryOpWithAdverb
			op2 = ip[1]; ++ip; // get selector index
			g->sp = sp; g->ip = ip;
			g->primitiveIndex = op2;
			doSpecialBinaryArithMsg(g, 3, false);
			sp = g->sp; ip = g->ip;
			ENDOP;
		OP_(255) : // opcTailCallReturnFromMethod
#if TAILCALLOPTIMIZE
			g->tailCall = 1;
#endif
			ENDOP;

			////////////////////////////////////

			class_lookup:
			// normal class lookup
			classobj = classOfSlot(slot);

			// message sends handled here:
			msg_lookup:
			index = classobj->classIndex.ui + selector->u.index;
			meth = gRowTable[index];

			if (meth->name.us != selector) {
				g->sp = sp; g->ip = ip;
				doesNotUnderstand(g, selector, numArgsPushed);
				sp = g->sp; ip = g->ip;
			} else {
				PyrMethodRaw *methraw;
				methraw = METHRAW(meth);
				switch (methraw->methType) {
					case methNormal : /* normal msg send */
							g->sp = sp; g->ip = ip;
						executeMethod(g, meth, numArgsPushed);
						sp = g->sp; ip = g->ip;
						break;
					case methReturnSelf : /* return self */
						sp -= numArgsPushed - 1;
						break;
					case methReturnLiteral : /* return literal */
						sp -= numArgsPushed - 1;
						slotCopy(sp, &meth->selectors); /* in this case selectors is just a single value */
						break;
					case methReturnArg : /* return an argument */
						sp -= numArgsPushed - 1;
						index = methraw->specialIndex; // zero is index of the first argument
						if (index < numArgsPushed) {
							slotCopy(sp, &sp[index]);
						} else {
							slotCopy(sp, &meth->prototypeFrame.uo->slots[index]);
						}
						break;
					case methReturnInstVar : /* return inst var */
						sp -= numArgsPushed - 1;
						index = methraw->specialIndex;
						slotCopy(sp, &slot->uo->slots[index]);
						break;
					case methAssignInstVar : /* assign inst var */
						sp -= numArgsPushed - 1;
						index = methraw->specialIndex;
						obj = slot->uo;
						if (obj->obj_flags & obj_immutable) { StoreToImmutableB(g, (PyrSlot*&)sp, ip); }
						else {
							if (numArgsPushed >= 2) {
								slotCopy(&obj->slots[index], &sp[1]);
								g->gc->GCWrite(obj, sp + 1);
							} else {
								slotCopy(&obj->slots[index], (PyrSlot*)&gSpecialValues[svNil]);
							}
							slotCopy(sp, slot);
						}
						break;
					case methReturnClassVar : /* return class var */
						sp -= numArgsPushed - 1;
						slotCopy(sp, &g->classvars->slots[methraw->specialIndex]);
						break;
					case methAssignClassVar : /* assign class var */
						sp -= numArgsPushed - 1;
						if (numArgsPushed >= 2) {
							slotCopy(&g->classvars->slots[methraw->specialIndex], &sp[1]);
							g->gc->GCWrite(g->classvars, sp + 1);
						} else {
							g->classvars->slots[methraw->specialIndex].uf = gSpecialValues[svNil];
						}
						slotCopy(sp, slot);
						break;
					case methRedirect : /* send a different selector to self */
						if (numArgsPushed < methraw->numargs) { // not enough args pushed
							/* push default arg values */
							PyrSlot *qslot;
							int m, mmax;
							qslot = meth->prototypeFrame.uo->slots + numArgsPushed - 1;
							for (m=0, mmax=methraw->numargs - numArgsPushed; m<mmax; ++m) slotCopy(++sp, ++qslot);
							numArgsPushed = methraw->numargs;
						}
						selector = meth->selectors.us;
						goto msg_lookup;
					case methRedirectSuper : /* send a different selector to self */
						if (numArgsPushed < methraw->numargs) { // not enough args pushed
							/* push default arg values */
							PyrSlot *qslot;
							int m, mmax;
							qslot = meth->prototypeFrame.uo->slots + numArgsPushed - 1;
							for (m=0, mmax=methraw->numargs - numArgsPushed; m<mmax; ++m) slotCopy(++sp, ++qslot);
							numArgsPushed = methraw->numargs;
						}
						selector = meth->selectors.us;
						classobj = meth->ownerclass.uoc->superclass.us->u.classobj;
						goto msg_lookup;
					case methForwardInstVar : /* forward to an instance variable */
						if (numArgsPushed < methraw->numargs) { // not enough args pushed
							/* push default arg values */
							PyrSlot *qslot;
							int m, mmax;
							qslot = meth->prototypeFrame.uo->slots + numArgsPushed - 1;
							for (m=0, mmax=methraw->numargs - numArgsPushed; m<mmax; ++m) slotCopy(++sp, ++qslot);
							numArgsPushed = methraw->numargs;
						}
						selector = meth->selectors.us;
						index = methraw->specialIndex;
						slotCopy(slot, &slot->uo->slots[index]);

						classobj = classOfSlot(slot);

						goto msg_lookup;
					case methForwardClassVar : /* forward to an instance variable */
						if (numArgsPushed < methraw->numargs) { // not enough args pushed
							/* push default arg values */
							PyrSlot *qslot;
							int m, mmax;
							qslot = meth->prototypeFrame.uo->slots + numArgsPushed - 1;
							for (m=0, mmax=methraw->numargs - numArgsPushed; m<mmax; ++m) slotCopy(++sp, ++qslot);
							numArgsPushed = methraw->numargs;
						}
						selector = meth->selectors.us;
						slotCopy(slot, &g->classvars->slots[methraw->specialIndex]);

						classobj = classOfSlot(slot);

						goto msg_lookup;
					case methPrimitive : /* primitive */
						g->sp = sp; g->ip = ip;
						doPrimitive(g, meth, numArgsPushed);
						sp = g->sp; ip = g->ip;
						break;
				} // switch (meth->methType)
			} // end handle message
#if TAILCALLOPTIMIZE
			g->tailCall = 0;
#endif
			continue;

			////////////////////////////////////

			key_class_lookup:
			// normal class lookup
			classobj = classOfSlot(slot);

			// message sends handled here:
			key_msg_lookup:
			index = classobj->classIndex.ui + selector->u.index;
			meth = gRowTable[index];

			if (meth->name.us != selector) {
				g->sp = sp; g->ip = ip;
				doesNotUnderstandWithKeys(g, selector, numArgsPushed, numKeyArgsPushed);
				sp = g->sp; ip = g->ip;
			} else {
				PyrMethodRaw *methraw;
				methraw = METHRAW(meth);
				switch (methraw->methType) {
					case methNormal : /* normal msg send */
						g->sp = sp; g->ip = ip;
						executeMethodWithKeys(g, meth, numArgsPushed, numKeyArgsPushed);
						sp = g->sp; ip = g->ip;
						break;
					case methReturnSelf : /* return self */
						sp -= numArgsPushed - 1;
						break;
					case methReturnLiteral : /* return literal */
						sp -= numArgsPushed - 1;
						slotCopy(sp, &meth->selectors); /* in this case selectors is just a single value */
						break;
					case methReturnArg : /* return an argument */
						g->sp = sp;
						numArgsPushed = keywordFixStack(g, meth, methraw, numArgsPushed, numKeyArgsPushed);
						numKeyArgsPushed = 0;
						sp = g->sp;
						sp -= numArgsPushed - 1;
						index = methraw->specialIndex; // zero is index of the first argument
						if (index < numArgsPushed) {
							slotCopy(sp, &sp[index]);
						} else {
							slotCopy(sp, &meth->prototypeFrame.uo->slots[index]);
						}
						break;
					case methReturnInstVar : /* return inst var */
						sp -= numArgsPushed - 1;
						index = methraw->specialIndex;
						slotCopy(sp, &slot->uo->slots[index]);
						break;
					case methAssignInstVar : /* assign inst var */
						sp -= numArgsPushed - 1;
						numArgsPushed -= numKeyArgsPushed << 1;
						index = methraw->specialIndex;
						obj = slot->uo;
						if (obj->obj_flags & obj_immutable) { StoreToImmutableB(g, (PyrSlot*&)sp, ip); }
						else {
							if (numArgsPushed >= 2) {
								slotCopy(&obj->slots[index], &sp[1]);
								g->gc->GCWrite(obj, sp + 1);
							} else {
								obj->slots[index].uf = gSpecialValues[svNil];
							}
							slotCopy(sp, slot);
						}
						break;
					case methReturnClassVar : /* return class var */
						sp -= numArgsPushed - 1;
						slotCopy(sp, &g->classvars->slots[methraw->specialIndex]);
						break;
					case methAssignClassVar : /* assign class var */
						sp -= numArgsPushed - 1;
						if (numArgsPushed >= 2) {
							slotCopy(&g->classvars->slots[methraw->specialIndex], &sp[1]);
							g->gc->GCWrite(g->classvars, sp + 1);
						} else {
							g->classvars->slots[methraw->specialIndex].uf = gSpecialValues[svNil];
						}
						slotCopy(sp, slot);
						break;
					case methRedirect : /* send a different selector to self, e.g. this.subclassResponsibility */
						g->sp = sp;
						numArgsPushed = keywordFixStack(g, meth, methraw, numArgsPushed, numKeyArgsPushed);
						numKeyArgsPushed = 0;
						sp = g->sp;
						selector = meth->selectors.us;

						goto msg_lookup;
					case methRedirectSuper : /* send a different selector to super */
						g->sp = sp;
						numArgsPushed = keywordFixStack(g, meth, methraw, numArgsPushed, numKeyArgsPushed);
						numKeyArgsPushed = 0;
						sp = g->sp;
						selector = meth->selectors.us;

						classobj = meth->ownerclass.uoc->superclass.us->u.classobj;

						goto msg_lookup;
					case methForwardInstVar : /* forward to an instance variable */
						g->sp = sp;
						numArgsPushed = keywordFixStack(g, meth, methraw, numArgsPushed, numKeyArgsPushed);
						numKeyArgsPushed = 0;
						sp = g->sp;
						selector = meth->selectors.us;
						index = methraw->specialIndex;
						slotCopy(slot, &slot->uo->slots[index]);

						classobj = classOfSlot(slot);

						goto msg_lookup;
					case methForwardClassVar : /* forward to an instance variable */
						g->sp = sp;
						numArgsPushed = keywordFixStack(g, meth, methraw, numArgsPushed, numKeyArgsPushed);
						numKeyArgsPushed = 0;
						sp = g->sp;
						selector = meth->selectors.us;
						slotCopy(slot, &g->classvars->slots[methraw->specialIndex]);

						classobj = classOfSlot(slot);

						goto msg_lookup;
					case methPrimitive : /* primitive */
						g->sp = sp; g->ip = ip;
						doPrimitiveWithKeys(g, meth, numArgsPushed, numKeyArgsPushed);
						sp = g->sp; ip = g->ip;
						break;
				} // switch (meth->methType)
			} // end handle message
			numKeyArgsPushed = 0;
#if TAILCALLOPTIMIZE
			g->tailCall = 0;
#endif
			
#if JUMPTABLE==0
	} // switch(op1)
#endif

	end:
		continue;
	} // end while(running)
#ifndef SC_WIN32
	running = true; // reset the signal
#endif
	g->sp = sp; g->ip = ip;
}

void DumpSimpleBackTrace(VMGlobals *g);
void DumpSimpleBackTrace(VMGlobals *g)
{
	int i;
	PyrFrame *frame;

	post("CALL STACK:\n");
	// print the variables and arguments for the most recent frames in the
	// call graph
	frame = g->frame;

	for (i=0; i<16; ++i) {
		char str[256];
		slotOneWord(&frame->method, str);
		post("%s ip %d\n", str, (char*)frame->ip.ui - (char*)frame->method.uom->code.uo->slots);
		frame = frame->caller.uof;
		if (!frame) break;
	}
	if (frame) { post("...\n"); }
	//DumpStack(g, g->sp);
}

void DumpBackTrace(VMGlobals *g)
{
	int i;
	PyrFrame *frame;

	post("CALL STACK:\n");
	// print the variables and arguments for the most recent frames in the
	// call graph
	frame = g->frame;

	for (i=0; i<16; ++i) {
		if (FrameSanity(frame, "DumpBackTrace")) {
			post("FRAME CORRUPTED\n");
			return;
		}
		DumpFrame(frame);
		frame = frame->caller.uof;
		if (!frame) break;
	}
	if (frame) { post("...\n"); }
	//DumpStack(g, g->sp);
}

void DumpDetailedFrame(PyrFrame *frame);
void DumpDetailedBackTrace(VMGlobals *g);
void DumpDetailedBackTrace(VMGlobals *g)
{
	int i;
	PyrFrame *frame;

	post("CALL STACK:\n");
	// print the variables and arguments for the most recent frames in the
	// call graph
	frame = g->frame;

	for (i=0; i<16; ++i) {
		if (FrameSanity(frame, "DumpDetailedBackTrace")) {
			post("FRAME CORRUPTED\n");
			return;
		}
		DumpDetailedFrame(frame);
		frame = frame->caller.uof;
		if (!frame) break;
	}
	if (frame) { post("...\n"); }
	//DumpStack(g, g->sp);
}

void DumpStack(VMGlobals *g, PyrSlot *sp)
{
	int i;
	PyrSlot *slot;
	char str[128];
#if BCSTAT
	dumpbcstat();
#endif
	postfl("STACK:\n");
	slot = sp - 64;
	if (slot < g->gc->Stack()->slots) slot = g->gc->Stack()->slots;
	for (i=slot - g->gc->Stack()->slots; slot<=sp; slot++, ++i) {
		slotString(slot, str);
		post("   %2d  %s\n", i, str);
	}
}



