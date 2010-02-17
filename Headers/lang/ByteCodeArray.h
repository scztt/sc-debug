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

typedef unsigned char Byte;

#define BYTE_CODE_CHUNK_SIZE		64
#define DEBUG_TABLE_CHUNK_SIZE		128

typedef struct {
	Byte *bytes;
	Byte *ptr;
	long size;
} ByteCodeArray, *ByteCodes;

typedef struct {
	uint16_t line;
	uint16_t character;
} DebugPosition;

typedef struct {
	DebugPosition *positions;
	DebugPosition *ptr;
	int size;
	DebugPosition currentPosition;
} DebugTableArray, *DebugTable;

extern ByteCodes gCompilingByteCodes;
extern long totalByteCodes;
extern DebugTable ptable;
extern DebugPosition *ptableposition;

extern void setDebugCharPosition(uint16_t line, uint16_t character);

void debugTablePush();
DebugTable debugTablePop();

void initByteCodes();
void compileByte(long byte);

void compileAndFreeByteCodes(ByteCodes byteCodes);
void compileAndFreeByteCodes(ByteCodes byteCodes, DebugTable tempTable);

void copyByteCodes(Byte *dest, ByteCodes byteCodes);
ByteCodes getByteCodes();
ByteCodes saveByteCodeArray();
void restoreByteCodeArray(ByteCodes byteCodes);
int byteCodeLength(ByteCodes byteCodes);

void compileByteCodes(ByteCodes byteCodes);
void compileByteCodes(ByteCodes byteCodes, DebugTable tempTable);

ByteCodes allocByteCodes();
void reallocByteCodes(ByteCodes byteCodes);
void freeByteCodes(ByteCodes byteCodes);


DebugTable allocDebugTable();
void reallocDebugTable(DebugTable debugTable);
void freeDebugTable(DebugTable debugTable);
int debugTableLength(DebugTable debugTable);

int compileOpcode(long opcode, long operand1);
void compileJump(long opcode, long jumplen);
int compileNumber(unsigned long value);
int compileNumber24(unsigned long value);

bool debugSanityCheck();
