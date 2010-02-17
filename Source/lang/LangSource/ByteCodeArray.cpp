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

#include <stdlib.h>
#include <string.h>
#include "SCBase.h"
#include "InitAlloc.h"
#include "ByteCodeArray.h"
#include "Opcodes.h"

ByteCodes gCompilingByteCodes;
long totalByteCodes = 0;

DebugTable sDebugTable[32];
DebugTable debugTable;
int debugStackPosition=-1;
bool debugging = false;
DebugTable ptable;
DebugPosition *ptableposition;

void initByteCodes()
{
	if (gCompilingByteCodes) {
		freeByteCodes(gCompilingByteCodes);
		gCompilingByteCodes = NULL;
	}
}

int compileOpcode(long opcode, long operand1)
{
	int retc;
	if (operand1 <= 15) {
		compileByte((opcode<<4) | operand1);
		retc = 1;
	} else {
		compileByte(opcode);
		compileByte(operand1);
		if (opcode == opSendMsg || opcode == opSendSpecialMsg || opcode == opSendSuper) {
			// these expect numKeyArgsPushed to be passed.
			compileByte(0);
		}
		retc = 2;
	}
	return retc;
}

void compileJump(long opcode, long jumplen)
{
	compileByte((opSpecialOpcode<<4) | opcode);
	compileByte((jumplen >> 8) & 0xFF);
	compileByte(jumplen & 0xFF);
}

void compileByte(long byte)
{
	if (gCompilingByteCodes == NULL) {
		gCompilingByteCodes = allocByteCodes();
	}

	if ((gCompilingByteCodes->ptr - gCompilingByteCodes->bytes)
		>= gCompilingByteCodes->size) {
		reallocByteCodes(gCompilingByteCodes);
	}
	totalByteCodes++;
	*gCompilingByteCodes->ptr++ = byte;
	if( debugging )
	{
		if( (debugTable->ptr - debugTable->positions)*sizeof(DebugPosition) >= (debugTable->size) )
		{
			reallocDebugTable(debugTable);
		}
		debugSanityCheck();
		*debugTable->ptr++ = debugTable->currentPosition;
		if( abs(debugTableLength( debugTable )) > 200 ) 
		{
			debugSanityCheck();
		}
	}
}

int compileNumber(unsigned long value)
{
	compileByte((value >> 24) & 0xFF);
	compileByte((value >> 16) & 0xFF);
	compileByte((value >> 8) & 0xFF);
	compileByte(value & 0xFF);
	return 4;
}

int compileNumber24(unsigned long value)
{
	compileByte((value >> 16) & 0xFF);
	compileByte((value >> 8) & 0xFF);
	compileByte(value & 0xFF);
	return 4;
}

void compileAndFreeByteCodes(ByteCodes byteCodes)
{
	compileByteCodes(byteCodes);
	freeByteCodes(byteCodes);
}

void compileAndFreeByteCodes(ByteCodes byteCodes, DebugTable tempTable)
{
	compileByteCodes(byteCodes, tempTable);
	freeByteCodes(byteCodes);
	freeDebugTable(tempTable);
}

void copyByteCodes(Byte *dest, ByteCodes byteCodes)
{
  memcpy(dest, byteCodes->bytes, byteCodeLength(byteCodes));
}

ByteCodes getByteCodes()
{
  ByteCodes	curByteCodes;

  curByteCodes = gCompilingByteCodes;
  gCompilingByteCodes = NULL;

  return curByteCodes;
}

ByteCodes saveByteCodeArray()
{
	ByteCodes	curByteCodes;

	curByteCodes = gCompilingByteCodes;
	gCompilingByteCodes = NULL;
	
	return curByteCodes;
}

void restoreByteCodeArray(ByteCodes byteCodes)
{
	gCompilingByteCodes = byteCodes;
}

int byteCodeLength(ByteCodes byteCodes)
{
    if (!byteCodes) return 0;
    return (byteCodes->ptr - byteCodes->bytes);
}

int debugTableLength(DebugTable debugTable)
{
    if (!debugTable) return 0;
    return (debugTable->ptr - debugTable->positions);
}

/***********************************************************************
 *
 *	Internal routines.
 *
 ***********************************************************************/

void compileByteCodes(ByteCodes byteCodes)
{
  Byte		*ptr;
  int i;

  if (byteCodes == NULL) return;

  //postfl("[%d]\n", byteCodes->ptr - byteCodes->bytes);
  for (i=0, ptr = byteCodes->bytes; ptr < byteCodes->ptr; ptr++, ++i) {
    compileByte(*ptr);

	//postfl("%02X ", *ptr);
	//if ((i & 15) == 15) postfl("\n");
  }
  //postfl("\n\n");
}

void compileByteCodes(ByteCodes byteCodes, DebugTable tempTable)
{
	Byte		*ptr;
	int i;
	
	if (byteCodes == NULL) return;
	DebugPosition *position = tempTable->positions;
	//postfl("[%d]\n", byteCodes->ptr - byteCodes->bytes);
	for (i=0, ptr = byteCodes->bytes; ptr < byteCodes->ptr; ptr++, ++i) {
		debugTable->currentPosition = *position++;
		compileByte(*ptr);
		
		//postfl("%02X ", *ptr);
		//if ((i & 15) == 15) postfl("\n");
	}
	//postfl("\n\n");
}


////////////////////////////////////////////////////////////////////////////////////
// ByteCodes allocation
////////////////////////////////////////////////////////////////////////////////////
ByteCodes allocByteCodes()
{
	ByteCodes	newByteCodes;

	// pyrmalloc: I think that all bytecodes are copied to objects
	// lifetime: kill after compile
	newByteCodes = (ByteCodes)pyr_pool_compile->Alloc(sizeof(ByteCodeArray));
	MEMFAIL(newByteCodes);
	newByteCodes->bytes = (Byte *)pyr_pool_compile->Alloc(BYTE_CODE_CHUNK_SIZE);
	MEMFAIL(newByteCodes->bytes);
	newByteCodes->ptr = newByteCodes->bytes;
	newByteCodes->size = BYTE_CODE_CHUNK_SIZE;
	//postfl("allocByteCodes %0X\n", newByteCodes);
	return newByteCodes;
}

void reallocByteCodes(ByteCodes byteCodes)
{
	Byte		*newBytes;
	int		newLen;

	if (byteCodes->size != (byteCodes->ptr - byteCodes->bytes)) {
		error("reallocByteCodes called with size != byteCode len");
	}

	newLen = byteCodes->size << 1;
	// pyrmalloc: I think that all bytecodes are copied to objects
	// lifetime: kill after compile
	newBytes = (Byte *)pyr_pool_compile->Alloc(newLen);
	MEMFAIL(newBytes);
	memcpy(newBytes, byteCodes->bytes, byteCodes->size);
	pyr_pool_compile->Free(byteCodes->bytes);

	byteCodes->bytes = newBytes;
	byteCodes->ptr = newBytes + byteCodes->size;
	byteCodes->size = newLen;
}

void freeByteCodes(ByteCodes byteCodes)
{
	//postfl("freeByteCodes %0X\n", byteCodes);
	if (byteCodes != NULL) {
		pyr_pool_compile->Free(byteCodes->bytes);
		pyr_pool_compile->Free(byteCodes);
	}
}

////////////////////////////////////////////////////////////////////////////////////
// DebugTable allocation
////////////////////////////////////////////////////////////////////////////////////
DebugTable allocDebugTable()
{
	DebugTable newDebugTable = (DebugTable)pyr_pool_compile->Alloc(sizeof(DebugTableArray));
	MEMFAIL(newDebugTable);
	newDebugTable->positions = (DebugPosition *)pyr_pool_compile->Alloc(DEBUG_TABLE_CHUNK_SIZE);
	MEMFAIL(newDebugTable->positions);
	newDebugTable->positions->line = 0;
	newDebugTable->positions->character = 0;
	newDebugTable->currentPosition.line = 0;
	newDebugTable->currentPosition.character = 0;
	newDebugTable->ptr = newDebugTable->positions;
	newDebugTable->size = DEBUG_TABLE_CHUNK_SIZE;
	debugSanityCheck();
	return newDebugTable;
}

void reallocDebugTable(DebugTable debugTable)
{
	DebugPosition		*newPositions;
	int		newLen;
	
	if (debugTable->size != (debugTable->ptr - debugTable->positions)*sizeof(DebugPosition)) {
		error("reallocDebugTable called with size != debugTable len");
	}
	
	newLen = debugTable->size << 1;

	newPositions = (DebugPosition *)pyr_pool_compile->Alloc(newLen);
	MEMFAIL(newPositions);
	memcpy(newPositions, debugTable->positions, debugTable->size);
	pyr_pool_compile->Free(debugTable->positions);
	
	debugTable->positions = newPositions;
	debugTable->ptr = newPositions + (debugTable->size/sizeof(DebugPosition));
	debugTable->size = newLen;

	debugTable->ptr->line = 0;
	debugTable->ptr->character = 0;
	
	debugSanityCheck();
}

void freeDebugTable(DebugTable debugTable)
{
	if (debugTable != NULL) {
		pyr_pool_compile->Free(debugTable->positions);
		pyr_pool_compile->Free(debugTable);
	}
	debugSanityCheck();
}

////////////////////////////////////////////////////////////////////////////////////
// extern debug functions
////////////////////////////////////////////////////////////////////////////////////

void debugTablePush()
{
	if( debugStackPosition==-1 )
	{
		sDebugTable[0] = allocDebugTable();
		debugTable = sDebugTable[0];
		debugTable->currentPosition.line = 0; 
		debugTable->currentPosition.character = 0; 
		debugStackPosition = 0;
		debugging = true;
	} else {
		debugStackPosition++;
		if( debugStackPosition > 31 )
		{
			postfl("Stack too deep. Serious problems.");
		} else {
			sDebugTable[debugStackPosition] = allocDebugTable( );
			debugSanityCheck();
			debugTable = sDebugTable[debugStackPosition];
			debugSanityCheck();
			debugTable->currentPosition = sDebugTable[debugStackPosition-1]->currentPosition;
			debugSanityCheck();
		}
	};	
	debugSanityCheck();
}

DebugTable debugTablePop()
{
	DebugTable poppedTable = debugTable;
	
	sDebugTable[ debugStackPosition-- ] = NULL;
	if( debugStackPosition == -1 )
		debugging = false;
	else
		debugTable = sDebugTable[ debugStackPosition ];
	debugSanityCheck();
	return poppedTable;
}

extern void setDebugCharPosition(uint16_t line, uint16_t character) 
{
	if( debugging )
	{
		debugTable->currentPosition.line = line;
		debugTable->currentPosition.character = character;
		debugSanityCheck();
	}
};

bool debugSanityCheck()
{
	for( int i=0; i<32; i++ )
	{
		if( sDebugTable[i] != NULL )
		{
			// table length suspiciously large
			if( debugTableLength( sDebugTable[i] ) > 4000 )
				return false;

			// table length negative!
			if( debugTableLength( sDebugTable[i] ) < 0 )
				return false;

			// size is unexpected
			if( sDebugTable[i]->size % 128 != 0 )
				return false;
			
			// weird line ##
			if( sDebugTable[i]->currentPosition.line > 1200 )
				return false;

			// weird char ##
			if( sDebugTable[i]->currentPosition.character > 400 )
				return false;
				
			// weird line ##
			if( sDebugTable[i]->ptr->line > 800 )
				return false;
			
			// weird char ##
			if( sDebugTable[i]->ptr->character > 200 )
				return false;
		}
	}
	// unmatched
	//if( debugStackPosition != -1 && sDebugTable[debugStackPosition] != debugTable )
	//return false;
}
