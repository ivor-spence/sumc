/*******************

Copyright (C) <2021>  <Ivor Spence>

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.

************************/


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <gmp.h>
#include <math.h>

#include <time.h>
#include <signal.h>
#include <malloc.h>

#include <unistd.h>
#include <sys/times.h>



#define STATUS_SUCCESSFUL 1
#define STATUS_OUT_OF_MEMORY 2
#define STATUS_UNSAT_FOUND 3
#define STATUS_INPUT_NOT_FOUND 4
#define STATUS_SYNTAX_ERROR 5
#define STATUS_OUT_OF_TIME 6
#define STATUS_SIGTERM_RECEIVED 7
#define STATUS_SIGINT_RECEIVED 8
#define false 0
#define true 1

#define uint64_t unsigned long long

#pragma intrinsic (memset, memcpy, memcmp)

//#define uint64_t __m128i

uint64_t bytes=0;
int megaBytes=0, gigaBytes=0;

FILE *inFile, *outFile;
char *filename;
int *optimised;

int traceLevel;
int competitionTrace = 1<<1;
int normalProgressTrace = 1<<2;
int fullClausesTrace = 1<<3;
int eachPosClausesTrace = 1<<4;

time_t startTime;


int ch;
int originalNumVars, originalNumClauses, numFirstVars;
int numVars, numClauses, unusedVariables;
int elapsedLimit, cpuLimit, turnsLimit, memoryLimit, noReduce;
char *memoryReason = "";
int bitSetCount = 0;
uint64_t operations = 0;

typedef struct BlockStruct
{
	void * *items;
	int count;
	struct BlockStruct *next,*previous;
} Block, *BlockPtr;

typedef struct BlockListStruct
{
	BlockPtr first, last, current, scanEnd;
	int readPos, scanEndPos;
	int blockSize;
} BlockList, *BlockListPtr;
BlockListPtr *varToClause;

typedef struct BitSetStruct
{
	mpz_t contribution, previousContribution;
	int posAdded;
	uint64_t *bits;
	unsigned short length, savedSize, capacity;
	unsigned int hashCode;
	struct BitSetStruct *next;
} BitSet, *BitSetPtr;

typedef struct ClauseStruct
{
	int length,redundant,pos,posAdded;
	int *lits;
	double weight;
	BitSetPtr bitSet;
} Clause, *ClausePtr;

static double startCPUTime;
static double ticksPerSecond;
static struct tms tmsBuffer;

double currentCPUTime()
{
	double result;

	times (&tmsBuffer);
	result = (tmsBuffer.tms_utime + tmsBuffer.tms_stime)/((double) ticksPerSecond);

	return result;
}


static double CPUTimeLimit;
static int limitSet = 0, nextDisplay;

void initCPUTime()
{
	ticksPerSecond = (double) sysconf(_SC_CLK_TCK);

	startCPUTime = currentCPUTime();
}

double getCPUTimeSinceStart()
{

	double result;
	result = currentCPUTime() - startCPUTime;
	return result;

}


void fprintProposition (FILE *f, int numVars, int numClauses, ClausePtr *clauses)
{
	int c,i;
	ClausePtr clause;
	
	fprintf (f, "p cnf %d %d\n", numVars, numClauses);
	for (c=0;c<numClauses;c++)
	{
		clause = clauses[c];
		for (i=0; i<clause->length; i++)
			fprintf (f, "%d ", clause->lits[i]);
		fprintf (f, "0\n");
	}
}

typedef struct TreeNodeStruct
{
	int lit, bitPos;
	struct TreeNodeStruct *present, *absent;
} TreeNode, *TreeNodePtr;



int *litsBuffer;
ClausePtr *clauses;
int *mapVariables,*unmapVariables;
int **firstVars, **lastVars;
BlockListPtr clauseSet, nextClauseSet;
int pos=0;


 

typedef struct HashTableStruct
{
	int currentNumOfSlots, nextNumOfSlots;
	BitSetPtr *currentSlots;
	int currentNumOfKeys;
	
} HashTable,*HashTablePtr;

void bitSetcheckFree (BitSetPtr bs);
unsigned int bitSetHashCode (BitSetPtr bs);
int clauseCompare (const void *c1, const void *c2);
void printBitSetTables();


int strEqual (char *s1, char *s2)
{
	return strcmp (s1,s2) == 0;
}

int strPrefix(char *s1, char *s2)
{
	return strncmp (s1,s2, strlen(s1)) == 0;
}

double local_mpz_log10(mpz_t x)
{
    signed long int ex;
    const double di = mpz_get_d_2exp(&ex, x);
    return log10(di) + log10(2) * (double) ex;
}

void printFinal(int status)
{
	time_t endTime;
	time (&endTime);
	mpz_t finalCount;
	
	switch (status)
	{
		case STATUS_SUCCESSFUL:
			mpz_init (finalCount);
			mpz_mul_2exp (finalCount, ((BitSetPtr)clauseSet->first->items[0])->contribution, unusedVariables);
			if (mpz_sgn(finalCount) == 0)
				fprintf (outFile, "s UNSATISFIABLE\n");
			else
				fprintf (outFile, "s SATISFIABLE\n");
			fprintf (outFile, "c s mc\n");
			fprintf (outFile, "c s log10-estimate %.15f\n", local_mpz_log10(finalCount));
			fprintf (outFile, "c s exact arb int ");
			mpz_out_str (outFile, 10, finalCount);
			fprintf (outFile, "\n");
			mpz_clear (finalCount);
			fprintf (outFile, "c o CPU-TIME-SECONDS=%.1f\n", getCPUTimeSinceStart());
			fprintf (outFile, "c o ELAPSED-TIME-SECONDS=%.1f\n", difftime (endTime, startTime));
			fprintf (outFile, "c o STATUS=SUCCESS\n");
			fprintf (outFile, "c o OPERATIONS=%llu\n",operations);
			exit(0);
			break;
			
		case STATUS_UNSAT_FOUND:
			fprintf (outFile, "s UNSATISFIABLE\n");
			fprintf (outFile, "c s mc\n");
			fprintf (outFile, "c o UNSAT found by unit propagation\n");
			fprintf (outFile, "c s log10-estimate -inf");
			fprintf (outFile, "c s exact arb int 0");
			fprintf (outFile, "c o CPU-TIME-SECONDS=%.1f\n", getCPUTimeSinceStart());
			fprintf (outFile, "c o ELAPSED-TIME-SECONDS=%.1f\n", difftime (endTime, startTime));
			fprintf (outFile, "c o STATUS=SUCCESS\n");
			fprintf (outFile, "c o OPERATIONS=%llu\n",operations);
			exit (0);
			break;
			
		case STATUS_SIGINT_RECEIVED:
			fprintf (outFile, "s UNKNOWN\n");
			fprintf (outFile, "c s mc\n");
			fprintf (outFile, "c o SIGINT received\n");
			fprintf (outFile, "c o CPU-TIME-SECONDS=%.1f\n", getCPUTimeSinceStart());
			fprintf (outFile, "c o ELAPSED-TIME-SECONDS=%.1f\n", difftime (endTime, startTime));
			fprintf (outFile, "c o STATUS=UNKNOWN\n");
			fprintf (outFile, "c o OPERATIONS=%llu\n",operations);
			exit(1);
			break;
			
		case STATUS_SIGTERM_RECEIVED:
			fprintf (outFile, "s UNKNOWN\n");
			fprintf (outFile, "c s mc\n");
			fprintf (outFile, "c o SIGTERM received\n");
			fprintf (outFile, "c o CPU-TIME-SECONDS=%.1f\n", getCPUTimeSinceStart());
			fprintf (outFile, "c o ELAPSED-TIME-SECONDS=%.1f\n", difftime (endTime, startTime));
			fprintf (outFile, "c o STATUS=SIGTERM\n");
			fprintf (outFile, "c o OPERATIONS=%llu\n",operations);
			exit(1);
			break;
			
		case STATUS_OUT_OF_MEMORY:
			fprintf (outFile, "s UNKNOWN\n");
			fprintf (outFile, "c s mc\n");
			fprintf (outFile, "c o MEMORY-EXCEEDED=<%s>\n", memoryReason);
			fprintf (outFile, "c o CPU-TIME-SECONDS=%.1f\n", getCPUTimeSinceStart());
			fprintf (outFile, "c o ELAPSED-TIME-SECONDS=%.1f\n", difftime (endTime, startTime));
			fprintf (outFile, "c o STATUS=MEMORY-EXCEEDED\n");
			fprintf (outFile, "c o OPERATIONS=%llu\n",operations);
			exit(1);
			break;

		case STATUS_OUT_OF_TIME:
			fprintf (outFile, "s UNKNOWN\n");
			fprintf (outFile, "c s mc\n");
			fprintf (outFile, "c o TIME-EXCEEDED\n");
			fprintf (outFile, "c o CPU-TIME-SECONDS=%.1f\n", getCPUTimeSinceStart());
			fprintf (outFile, "c o ELAPSED-TIME-SECONDS=%.1f\n", difftime (endTime, startTime));
			fprintf (outFile, "c o STATUS=TIME-EXCEEDED\n");
			fprintf (outFile, "c o OPERATIONS=%llu\n",operations);
			exit(1);
			break;
			
			
		case STATUS_INPUT_NOT_FOUND:
			fprintf (outFile, "s UNKNOWN\n");
			fprintf (outFile, "c s mc\n");
			fprintf (outFile, "c Error - no input\n");
			fprintf (outFile, "ce Error - no input\n");
			exit(1);
			break;
			
		case STATUS_SYNTAX_ERROR:
			fprintf (outFile, "s UNKNOWN\n");
			fprintf (outFile, "c s mc\n");
			fprintf (outFile, "c Error - syntax\n");
			fprintf (outFile, "ce Error - syntax\n");
			exit(1);
			break;
		default:
			break;
	}
	
}


void * checkMalloc (size_t size, char *reason)
{
	void *result;
	
	result = malloc (size);
	if (result == NULL)
	{
		memoryReason = reason;
		printFinal (STATUS_OUT_OF_MEMORY);
	}
	
	if (memoryLimit > 0)
	{
		bytes += malloc_usable_size (result);
		megaBytes = bytes/(1024*1024);
		gigaBytes = megaBytes/1024;
		if (gigaBytes > memoryLimit)
		{
			memoryReason = reason;
			printFinal (STATUS_OUT_OF_MEMORY);
		}
	}

	return result;
}

void * checkRealloc (void *p, size_t size, char *reason)
{
	void *result;
	uint64_t oldSize, newSize;

	oldSize = malloc_usable_size (p);

	result = realloc (p, size);
	if (result == NULL)
	{
		memoryReason = reason;
		printFinal (STATUS_OUT_OF_MEMORY);
	}

	if (memoryLimit > 0)
	{
		newSize = malloc_usable_size (result);
		bytes += newSize-oldSize;
		megaBytes = bytes/(1024*1024);
		gigaBytes = megaBytes/1024;
		if (gigaBytes > memoryLimit)
		{
			memoryReason = reason;
			printFinal (STATUS_OUT_OF_MEMORY);
		}
	}
	
	
	return result;
}

void checkFree (void *p)
{
	if (memoryLimit > 0)
	{
		bytes -= malloc_usable_size (p);
	}
	
	free(p);
}

void *gmpMalloc (size_t size)
{
	return checkMalloc (size, "gmpMalloc");
}

void *gmpRealloc (void *p, size_t oldSize, size_t newSize)
{
	return checkRealloc (p, newSize, "gmpRealloc");
}

void gmpFree (void *p, size_t size)
{
	checkFree(p);
}

HashTablePtr newHashTable ()
{
	HashTablePtr result;
	int i;

	result = (HashTablePtr) checkMalloc (sizeof(HashTable),"hashtable");

	result->currentNumOfSlots = (2<<10);
	result->currentSlots = checkMalloc (result->currentNumOfSlots*sizeof(BitSetPtr),"slots");

	for (i=0;i<result->currentNumOfSlots;i++)
		result->currentSlots[i] = NULL;

	result->currentNumOfKeys = 0;

	return result;
}



void freeHashTable (HashTablePtr hashTable)
{
	BitSetPtr b, next;
	int i;
		
	for (i=0;i<hashTable->currentNumOfSlots;i++)
	{
		b = hashTable->currentSlots[i];
		while (b != NULL)
		{
			next = b->next;
			bitSetcheckFree (b);
			b = next;
		}
	}
	checkFree (hashTable->currentSlots);
	checkFree (hashTable);
}


void hashTableExpand (HashTablePtr hashTable)
{
	int i, slotNum,currentNumOfSlots;
	unsigned long newNumOfSlots;
	unsigned long newPosition;
	BitSetPtr bs,next,previous,*slots;

	//printBitSetTables();
	
	//printf ("expand table %p (num slots %d, slots %p)\n", hashTable, hashTable->currentNumOfSlots, hashTable->currentSlots); fflush(stdout);

	currentNumOfSlots = hashTable->currentNumOfSlots;
	newNumOfSlots = 2*currentNumOfSlots;
	hashTable->currentSlots = checkRealloc (hashTable->currentSlots,newNumOfSlots*sizeof(BitSetPtr),"expand slots");
	//printf ("realloced\n"); fflush(stdout);
	slots = hashTable->currentSlots;
	for (i=currentNumOfSlots; i<newNumOfSlots; i++)
		slots[i] = NULL;
	
	for (i=0; i<currentNumOfSlots; i++)
	{
		bs = slots[i];
		previous = NULL;
		while (bs != NULL)
		{
			next = bs->next;
			if ( (bs->hashCode / currentNumOfSlots) % 2 == 1)
			{
				newPosition = bs->hashCode % newNumOfSlots;
				bs->next = slots[newPosition];
				slots[newPosition] = bs;
				if (previous == NULL)
					slots[i] = next;
				else
					previous->next = next;
			}
			else
				previous = bs;
			bs = next;
		}
	}	
	hashTable->currentNumOfSlots = newNumOfSlots;
}


	

void hashTableInsert (HashTablePtr hashTable, BitSetPtr bs)
{
	unsigned long slotNum;
	
	if (hashTable->currentNumOfKeys >= 0.75*hashTable->currentNumOfSlots)
		hashTableExpand(hashTable);

	slotNum = bs->hashCode % hashTable->currentNumOfSlots;

	bs->next = hashTable->currentSlots[slotNum];
	hashTable->currentSlots[slotNum] = bs;
	hashTable->currentNumOfKeys++;
}

//double chainTotal = 0;
//int chainCount;

BitSetPtr oneSearch (HashTablePtr hashTable, BitSetPtr bs)
{
	BitSetPtr bs2;

	bs2 = hashTable->currentSlots[bs->hashCode % hashTable->currentNumOfSlots];
	while (bs2 != NULL)
	{
		if (bs->length == bs2->length && 
			memcmp(bs->bits, bs2->bits, bs->length*(sizeof(uint64_t))) == 0) break;
			//found = true;
			//for (p=0; found && p<bs->length; p++)
			//	found = bs->bits[p] == bs2->bits[p];
			
			//if (found) break;
		bs2 = bs2->next;
	}

	return bs2;
}

int num=0,den=0;

int compareBits (uint64_t *a, uint64_t *b, int count)
{
	int result = 1;
	int i;
	switch (count)
	{
		case 1:
			return a[0] == b[0];
			break;

		case 2:
			return a[0] == b[0] && a[1] == b[1];
			break;

		case 3:
			return a[0] == b[0] && a[1] == b[1] && a[2] == b[2];
			break;

		case 4:
			return a[0] == b[0] && a[1] == b[1] && a[2] == b[2] && a[3] == b[3];
			break;
			
		default:
			for (i=0; result &&  i<count; i++)
				result = a[i] == b[i];
			return result;
			break;
	}
	return 0;
}

void printChain (BitSetPtr bs)
{
	int i;
	while (bs != NULL)
	{
		printf ("%.10X %.10X ", bitSetHashCode(bs), bs->hashCode);
		for (i=0; i<bs->length; i++) printf ("%.20llX ", bs->bits[i]);
		printf ("\n");
		bs = bs->next;
	}
	printf ("\n");
}

double totallength=0,countcalls=0;

BitSetPtr hashTableSearchInsert (HashTablePtr hashTable, BitSetPtr bs)
{

	BitSetPtr *start,bs2;
	//printf ("search insert %p\n", hashTable); fflush (stdout);
	start = hashTable->currentSlots + (bs->hashCode % hashTable->currentNumOfSlots);
	bs2 = *start;
	int l = 0;
	void *a,*b;
	while (bs2 != NULL)
	{
		l++;
		a = __builtin_assume_aligned (bs->bits, sizeof(uint64_t));
		b = __builtin_assume_aligned (bs2->bits, sizeof(uint64_t));
		if (bs->length == bs2->length && bs->hashCode == bs2->hashCode && 
			(!__builtin_memcmp(a, b, bs->length*(sizeof(uint64_t))) )
//			(compareBits(bs->bits, bs2->bits, bs->length) )
			)
			{
				break;
			}
			//found = true;
			//for (p=0; found && p<bs->length; p++)
			//	found = bs->bits[p] == bs2->bits[p];
			
			//if (found) break;
		bs2 = bs2->next;
	}
//	if (l > 100)
//		printChain (*start);
	countcalls++;
	totallength += l;
//	printf ("%.3 f", totallength/countcalls);
	
	if (bs2 == NULL)
	{
		bs->next = *start;
		*start = bs;
		if (hashTable->currentNumOfKeys >= 0.75*hashTable->currentNumOfSlots)
			hashTableExpand(hashTable);
		hashTable->currentNumOfKeys++;
	}

	return bs2;

}

BitSetPtr hashTableSearchInsert1 (HashTablePtr hashTable, BitSetPtr bs)
{

	BitSetPtr result;
	
	result = oneSearch (hashTable, bs);

	if (result == NULL)
	{
		hashTableInsert (hashTable, bs);
	}

	return result;

}


BlockPtr newBlock(int blockSize)
{
	BlockPtr result;
	result = checkMalloc (sizeof(Block), "block");
	result->items = checkMalloc (blockSize*sizeof(Block),"block items");
	result->count = 0;
	result->next = NULL;
	result->previous = NULL;
	return result;
}

void freeBlock (BlockPtr bp)
{
	checkFree (bp->items);
	checkFree (bp);
}

BlockListPtr stackOfBitSetPtrs;

BlockListPtr newBlockList(int blockSize)
{
	BlockListPtr result;
	result = checkMalloc (sizeof(BlockList), "blocklist");
	result->blockSize = blockSize;
	result->first = newBlock(blockSize);
	result->last = result->first;
	result->current = result->first;
	return result;
}

int blockListSize (BlockListPtr blp)
{
	int result;
	BlockPtr bp;
	result = 0;
	for (bp = blp->first; bp != NULL; bp = bp->next)
		result += bp->count;
	return result;
}

void freeBlockList (BlockListPtr blp)
{
	BlockPtr bp, nbp;
	bp = blp->first;
	while (bp != NULL)
	{
		nbp = bp->next;
		freeBlock (bp);
		bp = nbp;
	}
	checkFree (blp);
}

void clearBlockList (BlockListPtr blp)
{
	BlockPtr bp;
	bp = blp->first;
	while (bp != NULL)
	{
		bp->count = 0;
		bp = bp->next;
	}
	blp->last = blp->first;
}

void fprintBitSet (FILE *f, BitSetPtr bs);

void addToBlockList (BlockListPtr blp, void *item)
{
	BlockPtr bp, next;
//	if (blp == stackOfBitSetPtrs) printf ("adding %p\n", item);
	bp = blp->last;
	if (bp->count == blp->blockSize)
	{
		if (bp->next == NULL)
		{
			next = newBlock(blp->blockSize);
			next->previous = bp;
			bp->next = next;
		}
		bp = bp->next;
		blp->last = bp;
		bp->count = 0;
	}
	bp->items[bp->count++] = item;

}

void initBitSetBlock (BlockPtr bp, int size);

void * getFromBlockList (BlockListPtr blp)
{
	BlockPtr bp, next, newOne;
	void *result;
	bp = blp->last;
	if (bp->count == 0)
	{
		if (bp == blp->first)
		{
			newOne = newBlock(blp->blockSize);
			initBitSetBlock (newOne, blp->blockSize);
			newOne->next = blp->first;
			blp->first->previous = newOne;
			blp->first = newOne;
			bp = newOne;
		}
		else
			bp = bp->previous;
		blp->last = bp;
	}
	result = bp->items[--bp->count];
//	if (blp == stackOfBitSetPtrs) printf ("getting %p\n", result);
	return result;
}


void startScanBlockList (BlockListPtr blp)
{
	blp->readPos = 0;
	blp->current = blp->first;
	blp->scanEnd = blp->last;
	blp->scanEndPos = blp->last->count;
}

int hasNextBlockList (BlockListPtr blp)
{
	return !(blp->current == blp->scanEnd && blp->readPos == blp->scanEndPos);

}

int hasNextBlockList1 (BlockListPtr blp)
{
	BlockPtr bp = blp->current;
	if (blp->readPos == blp->blockSize)
		return (bp->next != NULL) && (bp->next->count > 0);
	else
		return blp->readPos < bp->count;

}

void *getNextBlockList (BlockListPtr blp)
{
	if (blp->readPos == blp->blockSize)
	{
		blp->current = blp->current->next;
		blp->readPos = 0;
	}
	
	return blp->current->items[blp->readPos++];
}

int getIntOption (int argc, char *argv[], char *tag, int defaultValue)
{
	int result,p, found;
	char *value;
	
	result = defaultValue;
	found = false;
	
	for (p=0; p<argc && !found; p++)
	{
		found = strPrefix (tag,argv[p]);
		if (found)
		{
			value = argv[p] + strlen(tag);
			sscanf (value, "%d", &result);
		}
	}
	
	return result;
}

void processArgs (int argc, char *argv[])
{
	int i;
	
	if (argc < 2 || strEqual(argv[1],"") || strEqual(argv[1],"-") || strPrefix("--", argv[1]) )
	{
		inFile = stdin;
		fprintf (outFile, "c o FILENAME=standard input\n"); fflush(stdout);
		filename = "standard input";
	}
	else
	{
		filename = argv[1];
		inFile = fopen (filename, "r");
		if (inFile == NULL)
		{
			fprintf (outFile, "c o CANT-OPEN=<%s>\n", filename); fflush(stdout);
			inFile = stdin;
			fprintf (outFile, "c o FILENAME=standard input\n"); fflush(stdout);
			filename = "standard input";
		}
		else
		{
			fprintf (outFile, "c o FILENAME=<%s>\n", filename); fflush(stdout);
		}
	}
	
	turnsLimit = getIntOption (argc, argv, "--turns=", 400);
	traceLevel = getIntOption (argc, argv, "--trace=", 0);
	elapsedLimit = getIntOption (argc, argv, "--timeout=", -1);
	cpuLimit = getIntOption (argc, argv, "--cpu-timeout=", -1);
	memoryLimit = getIntOption (argc, argv, "--maxrss=", -1);
	if (memoryLimit > 0)
		mp_set_memory_functions (gmpMalloc, gmpRealloc, gmpFree);
	noReduce = getIntOption (argc, argv, "--noreduce=", 0);
	if (elapsedLimit > 0)
		fprintf (outFile, "c o TIMEOUT-SECONDS=%d\n", elapsedLimit);
	if (cpuLimit > 0)
		fprintf (outFile, "c o CPU-TIMEOUT-SECONDS=%d\n", cpuLimit);
	if (memoryLimit > 0)
		fprintf (outFile, "c o MAX-MEMORY=%dGB\n", memoryLimit);
	fflush(stdout);
}



void nextCh()
{
	ch = fgetc(inFile);
}

void accept (char *s)
{
	int i;
	for (i=0; i<strlen(s); i++)
	{
		if (ch == s[i])
			nextCh();
		else
		{
			fprintf (outFile, "c Could not find string <%s>\n", s);  fflush(stdout);
			printFinal (STATUS_SYNTAX_ERROR);
		}
	}
}

void skipComments()
{
	while (ch == 'c')
	{
		do
		{
			nextCh();
		} while (ch != '\n' && ch != '\r' && ch >= 0);
		while ((ch >= 0) && (ch == '\n' || ch == '\r'))
			nextCh();
	}
}

int isDigit (char c)
{
	return '0' <= c && c <= '9';
}

int readInteger()
{
	char s[20]; // int can't be this long
	int i=0;
	int result, count;
	
	while (ch >= 0 && ch != '-' && !isDigit(ch))
	{
		while (ch == ' ')
			nextCh();
		if (ch == '\n' || ch == '\r')
		{
			while (ch == '\n' || ch == '\r')
				nextCh();
			skipComments();
		}
	}
	if (ch == '-')
	{
		s[i++] = ch;
		nextCh();
	}
	while (isDigit(ch) && i<19)
	{
		s[i++] = ch;
		nextCh();
	}
	s[i] = '\0';
	count = sscanf (s, "%d", &result);
	if (count != 1)
	{
		fprintf (outFile, "c Could not parse <%s> as in integer\n", s);
		printFinal (STATUS_SYNTAX_ERROR);
	}
	
	return result;
	
}


ClausePtr newClause()
{
	ClausePtr result = checkMalloc (sizeof(Clause), "clause");
	result->length = 0;
	result->lits = NULL;
	result->redundant = false;
	result->posAdded = -1;
	return result;
}

void freeClause (ClausePtr clause)
{
	if (clause->lits != NULL)
		checkFree (clause->lits);
	checkFree (clause);
}

unsigned long clauseHashFunction(void* p)
{
	ClausePtr c;
	c = (ClausePtr) p;
	int result;
	int l;
	result = 0;
	for (l=0; l<c->length;l++)
		result = result*7 + c->lits[l];
	return result;
}

int abs(int i)
{
	return (i<0)?-i:i;
}

int litCompare (const void * a, const void * b)
{
	int lita,litb,vara,varb;
	lita = *(int*)a;
	vara = abs(lita);
	litb = *(int*)b;
	varb = abs(litb);
	
	if (vara < varb)
		return -1;
	else if (vara > varb)
		return 1;
	else if (lita < litb)
		return -1;
	else if (lita > litb)
		return 1;
	else
		return 0;
}

ClausePtr readClause()
{
	ClausePtr result;
	int p1,p2,lit,length;
	int redundantClause = 0, redundantLit;
	result = newClause();
	p1 = 0;
	do
	{
		lit = readInteger();
		if (lit != 0)
		{
			redundantLit = 0;
			for (p2=0; p2<p1; p2++)
				if (litsBuffer[p2] == -lit)
				{
					/* clause with clashing lits is immediately satisfied */
					redundantClause = 1;
				}
				else if (litsBuffer[p2] == lit)
					redundantLit = 1;
				
			if (!redundantLit)
			{
				litsBuffer[p1++] = lit;
			}
		}
	} while (lit != 0);
	
	if (redundantClause)
	{
		freeClause (result);
		return NULL;
	}
	
	length = p1;
	result->lits = checkMalloc (length*sizeof(int), "lits");
	
	qsort (litsBuffer, length, sizeof(int), litCompare);
	
	result->length = 0;
	for (p1=0; p1<length; p1++)
		if (p1==0 || litsBuffer[p1-1] != litsBuffer[p1]) // check for duplicate lits
			result->lits[result->length++] = litsBuffer[p1];
	
	return result;
	
}

void fprintClause (FILE *f, ClausePtr c)
{
	int i;
	fprintf (f, "[");
	for (i=0; i<c->length; i++)
	{
		if (i!=0) fprintf (f, ",");
		fprintf (f, "%d", c->lits[i]);
	}
	fprintf (f, "]");
}
	

void readProblemLine()
{
	accept ("p cnf");
	originalNumVars = readInteger();
	originalNumClauses = readInteger();
}


void readProposition()
{
	int c,p;
	ClausePtr clause, clause1;
	int newNumClauses;
	
	nextCh();
	skipComments();
	readProblemLine();
	fprintf (outFile, "c o INITIAL-VARIABLES=%d\n", originalNumVars); fflush(stdout);
	fprintf (outFile, "c o INITIAL-CLAUSES=%d\n", originalNumClauses); fflush(stdout);
	if ( (traceLevel & competitionTrace) > 0) { fprintf (outFile, "ce Initially %d variables and %d clauses\n", originalNumVars, originalNumClauses);fflush(outFile);}

	litsBuffer = checkMalloc (originalNumVars*sizeof(int), "litsbuffer");
	clauses = checkMalloc (originalNumClauses*sizeof(ClausePtr), "clauses");
	numClauses = 0;
	numVars = originalNumVars;
	
	for (c=0; c<originalNumClauses; c++)
	{
		clause = readClause();
		if (clause != NULL)
			clauses[numClauses++] = clause;
	}
		

	if ((traceLevel & fullClausesTrace))
	{
		fprintf (outFile, "ce Initially %d variables and %d clauses\n", originalNumVars, originalNumClauses);
		fprintf (outFile, "ce Now %d variables and %d clauses\n", numVars, numClauses);
		for (c=0; c<numClauses; c++)
		{
			fprintClause (outFile, clauses[c]);
			fprintf (outFile, "\n");
		}
	}

	for (c=0;c<numClauses;c++)
	{
		clause = clauses[c];
		qsort (clause->lits, clause->length, sizeof(int), litCompare);
	}

	qsort (clauses, numClauses, sizeof (ClausePtr), clauseCompare);
	
	if (numClauses > 0)
	{
		newNumClauses = 1;

		c = 1;
		while (c < numClauses)
		{
			while (c < numClauses && clauseCompare(&clauses[c],&clauses[newNumClauses-1])==0) c++;
			if (c < numClauses) clauses[newNumClauses++] = clauses[c++];
		}
		
		if (newNumClauses < numClauses)
		{
			fprintf (outFile, "c o DUPLICATE-CLAUSES=%d\n", numClauses-newNumClauses);
			numClauses = newNumClauses;
		}
		
	
	}


	checkFree (litsBuffer);

}

void setUpVarToClause()
{
	int v,c,var;
	ClausePtr clause;
	varToClause = checkMalloc ( (1+numVars)*sizeof(BlockListPtr),"vartoclause");
	for (v=1; v<=numVars; v++)
		varToClause[v] = newBlockList(10);
	
	for (c=0; c<numClauses; c++)
	{
		clause = clauses[c];
		for (v=0;v<clause->length;v++)
		{
			var = abs(clause->lits[v]);
			addToBlockList (varToClause[var], clause);
		}
	}
	
}



void freeVarToClause()
{
	int v;

	for (v=1; v<=numVars; v++)
		freeBlockList (varToClause[v]);
	checkFree (varToClause);

}


void remapClauses()
{
	int c,v;
	ClausePtr clause;
	
	for (c=0; c<numClauses; c++)
	{
		clause = clauses[c];
		for (v=0; v<clause->length; v++)
		{
			if (clause->lits[v] > 0)
				clause->lits[v] = mapVariables[clause->lits[v]];
			else
				clause->lits[v] = -mapVariables[-clause->lits[v]];
		}
	}
}


void propagateUnitClauses()
{
	int *unitLits, numUnitLits;
	int *isUnitLit;
	int *isUsed;
	int v,c,lit,var,clit,v1,var1,lit1,varFound;
	int readPos, writePos;
	int newNumClauses, newNumVars;
	ClausePtr clause;
	
	unitLits = checkMalloc ((numVars+1)*sizeof(int),"unitlits");
	isUnitLit = checkMalloc ((numVars+1)*sizeof(int),"isunitlit");
	readPos = 0;
	writePos = 0;
	newNumVars = numVars;
	numUnitLits = 0;
	
	for (v=1;v<=numVars;v++)
		isUnitLit[v] = false;
	for (c=0; c<numClauses;c++)
	{
		clause = clauses[c];
		if (clause->length == 1)
		{
			lit = clause->lits[0];
			var = abs(lit);
			if (!isUnitLit[var])
			{
				isUnitLit[var] = true;
				unitLits[writePos++] = lit;
				numUnitLits++;
			}
		}
	}
	
	fprintf (outFile, "c o UNIT-CLAUSES=%d\n", writePos); fflush(stdout);
	setUpVarToClause();
	while (readPos < writePos)
	{
		lit = unitLits[readPos++];
		var = abs(lit);
		startScanBlockList (varToClause[var]);
		while (hasNextBlockList(varToClause[var]))
		{
			clause = getNextBlockList(varToClause[var]);
			varFound = false;
			for (v=0; v<clause->length && !varFound;v++)
			{
				clit = clause->lits[v];
				if (abs(clit) == var)
				{
					varFound = true;
					if (lit == clit)
						clause->redundant = true;
					else
					{
						for (v1=v; v1<clause->length-1; v1++)
							clause->lits[v1] = clause->lits[v1+1];
						clause->length--;
						if (clause->length == 1)
						{
							lit1 = clause->lits[0];
							var1 = abs(lit1);
							if (!isUnitLit[var1])
							{
								isUnitLit[var1] = true;
								unitLits[writePos++] = lit1;
								numUnitLits++;
							}
						}
						else if (clause->length == 0)
							printFinal (STATUS_UNSAT_FOUND);
					}
				}
			}
		}
	}
	
	freeVarToClause ();
	
	isUsed = checkMalloc ((1+numVars)*sizeof(int),"isused");
	for (v=1;v<=numVars;v++)
	{
		isUsed[v] = false;
	}
	for (c=0; c<numClauses;c++)
	{
		clause = clauses[c];
		if (!clause->redundant)
		{
			for (v=0; v<clause->length; v++)
			{
				isUsed[abs(clause->lits[v])] = true;
			}
		}
	}
	

	unusedVariables = 0;
	for (v=1;v<=numVars;v++)
		if (!isUsed[v])
			unusedVariables++;		
		
	unusedVariables -= numUnitLits;
	
	mapVariables = checkMalloc ((1+numVars)*sizeof(int),"mapvariables");
	unmapVariables = checkMalloc ((1+numVars)*sizeof(int),"mapvariables");
	
	newNumVars =  numVars - (unusedVariables + numUnitLits);

	fprintf (outFile, "c o UNUSED-VARIABLES=%d\n", unusedVariables); fflush (stdout);
	
	if (newNumVars < numVars)
	{
		newNumClauses = 0;
		for (c=0;c<numClauses;c++)
		{
			ClausePtr clause = clauses[c];
			if (clause->redundant)
				freeClause (clause);
			else
				clauses[newNumClauses++] = clause;
		}
		
		numClauses = newNumClauses;
		
		v1 = 0;
		for (v=1; v<=numVars; v++)
		{
			if(isUsed[v]/* && !isUnitLit[v]*/)
			{
				mapVariables[v] = ++v1;
			}
		}
		numVars = v1;
		
		remapClauses();
	}
	
	checkFree (isUsed);
	checkFree (isUnitLit);
	checkFree (unitLits);
}

typedef struct VariableStruct
{
	int var, count;
	double weight;
} Variable, *VariablePtr;

int variableCompare (const void * a, const void * b)
{
	VariablePtr va, vb;
	va = (VariablePtr) a;
	vb = (VariablePtr) b;
		
	if (va->weight > vb->weight)
		return 1;
	else if (va->weight < vb->weight)
		return -1;
	else
		return 0;
}


int clauseCompare4 (const void * a, const void * b)
{
	ClausePtr ca, cb;
	int l, length,result;
	ca = *(ClausePtr *) a;
	cb = *(ClausePtr *) b;
	
	result = litCompare (& (ca->lits[0]), &(cb->lits[0]));
	
	if (result == 0)
		result = litCompare (& (ca->lits[ca->length-1]), &(cb->lits[cb->length-1]));
	
	if (result == 0)
		result = clauseCompare(a,b);
	
	return result;
	
}

int clauseCompare2 (const void * a, const void * b)
{
	ClausePtr ca, cb;
	int l, length;
	ca = *(ClausePtr *) a;
	cb = *(ClausePtr *) b;
	
	int ap, bp;
	
	
	length = (ca->length > cb->length)?cb->length:ca->length;
	
	ap = ca->length;
	bp = cb->length;
	
	for (l=0; l<length && ca->lits[--ap] == cb->lits[--bp]; l++);
	
	if (l == ca->length && l == cb->length) return 0;
	
	if (l == ca->length && l < cb->length) return 1;
	
	if (l == cb->length && l < ca->length) return -1;
	
	return litCompare (& (ca->lits[ap]), &(cb->lits[bp]));
	
}

int clauseCompare (const void * a, const void * b)
{
	ClausePtr ca, cb;
	int l, length;
	ca = *(ClausePtr *) a;
	cb = *(ClausePtr *) b;
	
	
	
	length = (ca->length > cb->length)?cb->length:ca->length;
	
	for (l=0; l<length && ca->lits[l] == cb->lits[l]; l++);
	
	if (l == ca->length && l == cb->length) return 0;
	
	if (l == ca->length && l < cb->length) return 1;
	
	if (l == cb->length && l < ca->length) return -1;
	
	return litCompare (& (ca->lits[l]), &(cb->lits[l]));
	
}

int clauseCompareLength (const void * a, const void * b)
{
	ClausePtr ca, cb;
	int l, length;
	ca = *(ClausePtr *) a;
	cb = *(ClausePtr *) b;
	
	if (ca->length < cb->length) return 1;
	if (cb->length < ca->length) return -1;
	
	length = (ca->length > cb->length)?cb->length:ca->length;
	
	for (l=0; l<length && ca->lits[l] == cb->lits[l]; l++);
	
	if (l == ca->length && l == cb->length) return 0;
	
	if (l == ca->length && l < cb->length) return 1;
	
	if (l == cb->length && l < ca->length) return -1;
	
	return litCompare (& (ca->lits[l]), &(cb->lits[l]));
	
}


double fabs(double x)
{
	return (x<0)?-x:x;
}

int clauseLength (int originalVar)
{
	ClausePtr clause;
	int minVar, maxVar, l, v, result;
	
	result = 0;
	startScanBlockList(varToClause[originalVar]);
	while (hasNextBlockList(varToClause[originalVar]))
	{
		clause = getNextBlockList(varToClause[originalVar]);
		minVar = numVars;
		maxVar = 0;
		for (l=0; l<clause->length; l++)
		{
			v = mapVariables[abs(clause->lits[l])];
			if (v<minVar) minVar = v;
			if (v >maxVar) maxVar = v;
		}
		result += maxVar-minVar;
	}
	return result;
}

void sortVars (int startv, int finishv, int startc, int finishc)
{
	int turn, v,v1, c, lit, var,i,j,p,localNumVars = finishv+1-startv, localNumClauses = finishc+1-startc;
	int minVar, maxVar;
	Variable *variables;
	ClausePtr clause,clause1;
	
	
	double weight, increment, ratio,maxWeight,*weights;
	int converged=0;
	int *clauseCounts, *clauseCountsPos,*used;
	int **varsToClauses;
	int count,steps;
	
	used = checkMalloc ( localNumVars*sizeof(int),"clauseCounts");
	clauseCounts = checkMalloc ( localNumVars*sizeof(int),"clauseCounts");
	clauseCountsPos= checkMalloc ( localNumVars*sizeof(int),"clauseCountsPos");
	varsToClauses= checkMalloc ( localNumVars*sizeof(int *),"varsToClauses");
	for (v=0;v<localNumVars;v++)
	{
		clauseCounts[v] = 0;
		clauseCountsPos[v]=0;
		used[v] = 0;
	}


	
	weights = checkMalloc ( (1+numVars)*sizeof(double), "weights");

	for (v=startv; v<=finishv; v++)
	{
		weights[v] = 0;
	}

	for (c=startc; c<=finishc; c++)
	{
		clause = clauses[c];

		for (v=0; v<clause->length; v++)
		{
			lit = clause->lits[v];
			var = abs(lit);
			clauseCounts[var-startv]++;
			//weights[var]-=clause->length;
		}
	}
	
	for (v=0;v<localNumVars;v++)
	{
		varsToClauses[v] = checkMalloc (clauseCounts[v]*sizeof(int),"vtc");
	}

	for (c=startc; c<=finishc; c++)
	{
		clause = clauses[c];

		for (v=0; v<clause->length; v++)
		{
			lit = clause->lits[v];
			var = abs(lit);
			varsToClauses[var-startv][clauseCountsPos[var-startv]++] = c;
		}
	}
	

	steps = 0;
	for (v1=startv; v1<=finishv;v1++)
	{
		for (v=startv; used[v-startv] != 0; v++);
		maxVar = v;
		maxWeight = weights[maxVar];
		
		for (v=v+1; v<=finishv;v++)
		{
			if (used[v-startv] == 0 && weights[v] > maxWeight)
			{
				maxVar = v;
				maxWeight = weights[maxVar];
			}
		}
		unmapVariables[v1] = maxVar;
		//printf ("%d\n", maxVar);
		used[maxVar-startv] = 1;
		for (c=0;c<clauseCounts[maxVar-startv];c++)
		{
			if ( steps++ == 1000)
			{
				steps = 0;
			}
			clause = clauses[varsToClauses[maxVar-startv][c]];
			count = 0;
			for (v=0; v<clause->length; v++)
			{
				lit = clause->lits[v];
				var = mapVariables[abs(lit)];
				if (used[var-startv] == 0) count++;
			}
			for (v=0; v<clause->length; v++)
			{
				lit = clause->lits[v];
				var = mapVariables[abs(lit)];
				weights[var]+=1.0/count;
			}
		}
		
	}

	checkFree (weights);
	checkFree (clauseCounts);
	checkFree(clauseCountsPos);
	for (v=0;v<localNumVars;v++)
	{
		checkFree (varsToClauses[v]);
	}
	checkFree (varsToClauses);
	
	for (v=startv;v<=finishv;v++)
		mapVariables[unmapVariables[v]] = v;
	
	//exit(0);
	
}

void checkElapsed()
{
	time_t now;
	if (elapsedLimit > 0)
	{
		time(&now);
		double e = difftime (now,startTime);
		if (e > elapsedLimit)
		{
			printFinal (STATUS_OUT_OF_TIME);
		}
	}
	if (cpuLimit > 0)
	{
		if (getCPUTimeSinceStart() > cpuLimit)
		{
			printFinal (STATUS_OUT_OF_TIME);
		}
	}
}

void sortVars3 (int startv, int finishv, int startc, int finishc)
{
	int turn, v, c, lit, var,i,j,p,turns,v1,v2,v2n,ov1,ov2,oldMin,newMin,oldMax,newMax, limit;
	long localNumVars = finishv+1-startv, localNumClauses = finishc+1-startc;
	int minVar, maxVar,steps;
	Variable *variables;
	ClausePtr clause,clause1;
	BlockListPtr *localVarToClause;
	
	
	double weight, increment, ratio,r,delta,cog,temperature;
	int converged=0, inClauseSwap;;
	double increase,change,total;
	

	localVarToClause = checkMalloc ( (localNumVars)*sizeof(BlockListPtr),"vartoclause");
	for (v=0; v<localNumVars; v++)
		localVarToClause[v] = newBlockList(10);
	
	for (c=startc; c<=finishc; c++)
	{
		clause = clauses[c];
		for (v=0;v<clause->length;v++)
		{
			var = abs(clause->lits[v]);
			addToBlockList (localVarToClause[var-startv], clause);
		}
	}
	
	for (v=startv; v<=finishv; v++)
	{
		mapVariables[v] = v;
		unmapVariables[v] = v;
	}


	total = 0;

	temperature = 1*localNumVars;

	ratio = 0.99999;
	if (localNumClauses > 250) ratio = 0.99995;
	if (localNumClauses > 1000) ratio = 0.9999;
	if (localNumClauses > 5000) ratio = 0.999;
	if (localNumClauses > 20000) ratio = 0.99;
	if (localNumClauses > 100000) ratio = 0.95;
	
	turns = 5*localNumVars;
	limit = turns/40;
	if (limit < 5) limit = 5;
	converged = turns;
	while (converged > 0.1)
	{
/*
		for (c=startc; c<=finishc; c++)
		{
			clause = clauses[c];
			for (v=0;v<clause->length;v++)
			{
				var = abs(clause->lits[v]);
				printf ("%d(orig %d) ", mapVariables[var], var);
			}
			printf ("\n");
		}
		printf ("\n\n");
*/

		converged = 0;
		for (turn=0; turn<turns; turn++)
		{
			v1 = startv + rand() % localNumVars;
			v2 = startv + rand() % localNumVars;
			//printf ("swapping %d <-> %d\n",v1,v2);
			ov1 = unmapVariables[v1];
			ov2 = unmapVariables[v2];
	
			increase = 0;
	
			startScanBlockList (localVarToClause[ov1-startv]);
			while (hasNextBlockList(localVarToClause[ov1-startv]))
			{
				clause = getNextBlockList(localVarToClause[ov1-startv]);
/*
				for (i=0;i<clause->length;i++)
					printf ("%d (%d)", clause->lits[i], mapVariables[abs(clause->lits[i])]);
				printf("\n");
*/
				oldMin = startv+localNumVars;
				newMin = oldMin;
				oldMax = startv;
				newMax = oldMax;
				for (v=0;v<clause->length;v++)
				{
					var = abs(clause->lits[v]);
					var = mapVariables[var];
					if (var < oldMin) oldMin = var;
					if (var > oldMax) oldMax = var;
					if (var == v1)
					{
						if (v2 < newMin) newMin = v2;
						if (v2 > newMax) newMax = v2;
					}
					else if (var == v2)
					{
						if (v1 < newMin) newMin = v1;
						if (v1 > newMax) newMax = v1;
					}
					else
					{
						if (var < newMin) newMin = var;
						if (var > newMax) newMax = var;
					}
				}
				change = (newMax + oldMin - (newMin + oldMax) ) ;
				increase += change;
				//printf ("A %d %d %d %d\n", oldMin, oldMax, newMin, newMax);
			}
	
			startScanBlockList (localVarToClause[ov2-startv]);
			while (hasNextBlockList(localVarToClause[ov2-startv]))
			{
				clause = getNextBlockList(localVarToClause[ov2-startv]);
/*
				for (i=0;i<clause->length;i++)
					printf ("%d (%d)", clause->lits[i], mapVariables[abs(clause->lits[i])]);
				printf("\n");
*/
				oldMin = startv+localNumVars;
				newMin = oldMin;
				oldMax = startv;
				newMax = oldMax;
				for (v=0;v<clause->length;v++)
				{
					var = abs(clause->lits[v]);
					var = mapVariables[var];
					if (var < oldMin) oldMin = var;
					if (var > oldMax) oldMax = var;
					if (var == v1)
					{
						if (v2 < newMin) newMin = v2;
						if (v2 > newMax) newMax = v2;
					}
					else if (var == v2)
					{
						if (v1 < newMin) newMin = v1;
						if (v1 > newMax) newMax = v1;
					}
					else
					{
						if (var < newMin) newMin = var;
						if (var > newMax) newMax = var;
					}
				}
				change = (newMax + oldMin - (newMin + oldMax) ) ;
				increase += change;
				//printf ("B %d %d %d %d\n", oldMin, oldMax, newMin, newMax);
			}
			if (increase < 0 || exp(-increase/temperature) > ( ((double) rand())/RAND_MAX) )
			{
				//printf ("%d %f %f %f \n",increase,temperature,( ((double) rand())/RAND_MAX),exp(-increase/temperature));
				//printf ("swap %d %d %f\n",v1,v2,increase);
				mapVariables[ov1] = v2;
				unmapVariables[v2] = ov1;
				mapVariables[ov2] = v1;
				unmapVariables[v1] = ov2;
				if (increase < 0) converged++;
				total += increase;
				//printf ("C %f %f temp %f\n", increase, total,temperature);
			}
			
		}
		
		temperature *= ratio;
		//printf ("%d %e\n", converged, temperature);
	}

	for (v=0; v<localNumVars; v++)
		freeBlockList (localVarToClause[v]);
	checkFree (localVarToClause);
	
	
}

void sortVars1 (int startv, int finishv, int startc, int finishc)
{
	int turn, v, c, lit, var,i,j,p,v1,v2;
	long localNumVars = finishv+1-startv, localNumClauses = finishc+1-startc;
	int minVar, maxVar,steps,steps1;
	Variable *variables;
	ClausePtr clause,clause1;
	
	
	double weight, increment, ratio,r,delta,cog;
	int converged=0;

	
	variables = checkMalloc ( (1+numVars)*sizeof(Variable), "variables");

	for (v=startv; v<=finishv; v++)
	{
		mapVariables[v] = v;
	}

	for (v=1;v<10*localNumVars;v++)
	{
		v1 = startv + rand()%localNumVars;
		v2 = startv + rand()%localNumVars;
		var = mapVariables[v1];
		mapVariables[v1] = mapVariables[v2];
		mapVariables[v2] = var;
	}
	
	for (v=startv; v<=finishv; v++)
	{
		variables[v].var = mapVariables[v];
		variables[v].count = 0;
		variables[v].weight = mapVariables[v];
	}

	qsort (&variables[startv], localNumVars, sizeof(Variable), variableCompare);

	
	int turns=1;
	increment = localNumVars;
	if (localNumVars > 1000)
		increment = 10000000;
/*
	ratio = 1.0 - (log(10+localNumVars)*log (10 + localNumClauses) )/5000000;
	if (localNumClauses > 10000)
		ratio = 1.0 - (log(10+localNumVars) + log (10 + localNumClauses) )/100000;
	if (localNumClauses > 50000)
		ratio = 1.0 - (log(10+localNumVars) + log (10 + localNumClauses) )/10000;
	if (localNumClauses > 100000)
		ratio = 1.0 - (log(10+localNumVars) + log (10 + localNumClauses) )/1000;
		
*/
	increment = 1E20*localNumVars;
	if (localNumVars*localNumClauses > 10000000)
		ratio = 0.999;
	else
		ratio = 0.9999;
	
	delta = 0.0005;
	ratio = 0.9999;
	
		
	//fprintf (outFile, "c inc = %.2f ratio = %.8f\n", increment, ratio);
	steps = 0;
	steps1 = 0;
	do
	{
		//increment = ((numVars+numClauses)*100)/(100 + turns++);
		//ratio = 1.0 - delta;
		//delta = delta*0.9999;
		
		
		increment *= ratio;

		//fprintf (outFile,"inc = %.8f\n",increment);
		
		for (c=startc; c<=finishc; c++)
		{
			if ( steps++ == 100000000)
			{
				checkElapsed();
				steps = 0;
			}
			clause = clauses[c];
			cog = 0;

			minVar = numVars;
			maxVar = 1;


			for (v=0; v<clause->length; v++)
			{
				lit = clause->lits[v];
				var = mapVariables[abs(lit)];
				if (var < minVar) minVar = var;
				if (var > maxVar) maxVar = var;
				cog += var;
			}
		
			variables[minVar].weight += increment;
			variables[maxVar].weight -= increment;
		}
		
	
		qsort (&variables[startv], localNumVars, sizeof(Variable), variableCompare);
		

		converged = 0;
		for (v=startv; v<=finishv; v++)
		{
			//printf ("%d %.2f %d\n", v, variables[v].weight, variables[v].var);
			//if (abs(mapVariables[variables[v].var] - v) > maxDifference)
			//	maxDifference = abs(mapVariables[variables[v].var] - v);
			if (mapVariables[variables[v].var] != v)
				converged++;
			mapVariables[variables[v].var] = v;
			variables[v].weight = v;
		}
		//printf ("---------------------------\n");
		
		//printf ("x %d\n", maxDifference);
		//printf ("c=%d\n", converged);
		
	} while (converged>0);
	
}

void sortVars4 (int startv, int finishv, int startc, int finishc)
{
	int turn, v, c, lit, var,i,j,p,v1,v2;
	long localNumVars = finishv+1-startv, localNumClauses = finishc+1-startc;
	int minVar, maxVar,steps,steps1, clauseLength;
	Variable *variables;
	ClausePtr clause,clause1;
	time_t localSortStart,localSortFinish;
	
	double weight, increment, ratio,r,delta,cog;
	int converged=0;

	time (&localSortStart);
	
	variables = checkMalloc ( (1+numVars)*sizeof(Variable), "variables");

	for (v=startv; v<=finishv; v++)
	{
		mapVariables[v] = v;
	}

	for (v=1;v<10*localNumVars;v++)
	{
		v1 = startv + rand()%localNumVars;
		v2 = startv + rand()%localNumVars;
		var = mapVariables[v1];
		mapVariables[v1] = mapVariables[v2];
		mapVariables[v2] = var;
	}
	
	for (v=startv; v<=finishv; v++)
	{
		variables[v].var = mapVariables[v];
		variables[v].count = 0;
		variables[v].weight = mapVariables[v];
	}

	qsort (&variables[startv], localNumVars, sizeof(Variable), variableCompare);

	
	int turns=1;
	increment = localNumVars;
	if (localNumVars > 1000)
		increment = 10000000;

	increment = 1E10*localNumVars;
	
/*
	ratio = 0.999999;

	if (localNumClauses > 400)
		ratio = 0.999995;
	
	if (localNumClauses > 1000)
		ratio = 0.999994;
	
	if (localNumClauses > 2000)
		ratio = 0.999993;
	
	if (localNumClauses > 3000)
		ratio = 0.999992;
	
	if (localNumClauses > 5000)
		ratio = 0.99995;

	if (localNumClauses > 10000)
		ratio = 0.99995;
*/
	
	ratio = 1.0 - (log(10+localNumVars)*log (10 + localNumClauses) )/100000000;
	if (localNumClauses > 10000)
		ratio = 1.0 - (log(10+localNumVars) + log (10 + localNumClauses) )/1000000;
	if (localNumClauses > 50000)
		ratio = 1.0 - (log(10+localNumVars) + log (10 + localNumClauses) )/100000;
	if (localNumClauses > 100000)
		ratio = 1.0 - (log(10+localNumVars) + log (10 + localNumClauses) )/10000;


	fprintf (outFile, "c o SORTVARS=%d\n", localNumVars);
	fprintf (outFile, "c o SORTCLAUSES=%d\n", localNumClauses);
	fprintf (outFile, "c o RATIO=%.6f\n", ratio);
	
		
	//fprintf (outFile, "c inc = %.2f ratio = %.8f\n", increment, ratio);
	steps = 0;
	steps1 = 0;
	do
	{
		//increment = ((numVars+numClauses)*100)/(100 + turns++);
		//ratio = 1.0 - delta;
		//delta = delta*0.9999;
		
		
		increment *= ratio;

		//fprintf (outFile,"inc = %.8f\n",increment);
		
		for (c=startc; c<=finishc; c++)
		{
			if ( steps++ == 100000000)
			{
				checkElapsed();
				steps = 0;
			}
			clause = clauses[c];

			minVar = numVars;
			maxVar = 1;


			for (v=0; v<clause->length; v++)
			{
				lit = clause->lits[v];
				var = mapVariables[abs(lit)];
				if (var < minVar) minVar = var;
				if (var > maxVar) maxVar = var;
			}
			clauseLength = maxVar+1-minVar;
			variables[maxVar].weight -= increment*sqrt( 10 + (double) clauseLength);
			variables[minVar].weight += increment*sqrt( 10 + (double) clauseLength);
		}
		
	
		qsort (&variables[startv], localNumVars, sizeof(Variable), variableCompare);
		

		converged = 0;
		for (v=startv; v<=finishv; v++)
		{
			//printf ("%d %.2f %d\n", v, variables[v].weight, variables[v].var);
			//if (abs(mapVariables[variables[v].var] - v) > maxDifference)
			//	maxDifference = abs(mapVariables[variables[v].var] - v);
			if (mapVariables[variables[v].var] != v)
				converged++;
			mapVariables[variables[v].var] = v;
			variables[v].weight = v;
		}
		//printf ("---------------------------\n");
		
		//printf ("x %d\n", maxDifference);
		//printf ("c=%d\n", converged);
		
	} while (converged>0);
	time (&localSortFinish);
	fprintf (outFile, "c o SORTTIME=%.1f\n", difftime (localSortFinish, localSortStart)); fflush (outFile);

}

void sortSubProblems()
{
	int *isUsed, *varsUsed;
	int c,r,readPos, writePos, v, lit, var, thisVar, countVars, regionsCount;
	int startc, finishc;
	ClausePtr clause;
	int *startvs,*finishvs, finished;
	
	if (numVars == 0) return;
		
	
	isUsed = checkMalloc ((1+numVars)*sizeof(int),"isused");
	varsUsed = checkMalloc ((1+numVars)*sizeof(int),"varsused");
	
	startvs = checkMalloc ((1+numVars)*sizeof(int),"isused");
	finishvs = checkMalloc ((1+numVars)*sizeof(int),"isused");
	


	for (v=1;v<=numVars; v++)
		isUsed[v] = false;
	
	isUsed[1] = true;
	varsUsed[0] = 1;
	readPos = 0;
	writePos = 1;
	countVars = 0;
	regionsCount = 0;
	
	setUpVarToClause();
	finished = 0;
	
	while (!finished)
	{
	
		startvs[regionsCount] = writePos;
		while (writePos > readPos)
		{
			thisVar = varsUsed[readPos++];
			countVars++;
			mapVariables[thisVar] = countVars; 						//printf ("%d -> %d\n", thisVar,countVars);

			startScanBlockList (varToClause[thisVar]);
			while (hasNextBlockList(varToClause[thisVar]))
			{
				clause = (ClausePtr) getNextBlockList(varToClause[thisVar]);
				for (v=0; v<clause->length;v++)
				{
					lit = clause->lits[v];
					var = abs(lit);
					if (!isUsed[var])
					{
						isUsed[var] = true;
						varsUsed[writePos++] = var;
					}
				}
			}
		}
		finishvs[regionsCount] = writePos;
		regionsCount++;
		
		if (!finished)
		{
			for (v=1; v <= numVars && (isUsed[v] || optimised[v]); v++);
			if (v > numVars)
				finished = true;
			else
			{
				isUsed[v] = true;
				varsUsed[writePos++] = v;
			}
		}
	}
	
	numVars = writePos;
	
	checkFree (optimised);
	
	if (regionsCount > 1)
	{
		fprintf (outFile, "c o %d independent regions found\n", regionsCount);
	}
	else
	{
		//for (v=1; v<=numVars; v++)
		//	mapVariables[v] = v;
	}


	remapClauses();

	for (c=0;c<numClauses;c++)
	{
		clause = clauses[c];
		qsort (clause->lits, clause->length, sizeof(int), litCompare);
	}


	qsort (clauses, numClauses, sizeof (ClausePtr), clauseCompare);
	

	startc=0;
	for (r=0; r<regionsCount;r++)
	{
		for (c=startc; c<numClauses; c++)
		{
			clause = clauses[c];
			v = abs(clause->lits[0]);
			if (v < startvs[r] || v > finishvs[r]) break;
		}
		finishc = c-1;
		
		//sortVars (startvs[r], finishvs[r], startc, finishc);
		sortVars4(startvs[r], finishvs[r], startc, finishc);
		
		startc = finishc+1;
	}

	remapClauses();

	for (c=0;c<numClauses;c++)
	{
		clause = clauses[c];
		qsort (clause->lits, clause->length, sizeof(int), litCompare);
	}

	qsort (clauses, numClauses, sizeof (ClausePtr), clauseCompare);
	
	
	freeVarToClause();
	checkFree (isUsed);
	checkFree (varsUsed);
	checkFree (startvs);
	checkFree (finishvs);
}

void sortVarsAndClauses()
{
	int turn, v, c, lit, var,i,j,p;
	int minVar, maxVar;
	Variable *variables;
	ClausePtr clause,clause1;
	
	
	double weight, increment, ratio;
	int converged=0;


	
	variables = checkMalloc ( (1+numVars)*sizeof(Variable), "variables");

	for (v=1; v<=numVars; v++)
	{
		variables[v].var = v;
		variables[v].count = 0;
		variables[v].weight = v;
		mapVariables[v] = v;
	}


	
	int turns=1;
	increment = 100*numVars;
	if (numVars > 10000)
		increment = 10000000;
	ratio = 1.0 - (log(10+numVars)*log (10 + numClauses) )/1000000;
	if (numClauses > 10000)
		ratio = 1.0 - (log(10+numVars) + log (10 + numClauses) )/100000;
	if (numClauses > 50000)
		ratio = 1.0 - (log(10+numVars) + log (10 + numClauses) )/10000;
	if (numClauses > 100000)
		ratio = 1.0 - (log(10+numVars) + log (10 + numClauses) )/1000;
		
	do
	{
		//increment = ((numVars+numClauses)*1000)/(20 + turns++);
		increment *= ratio;
		//fprintf (outFile,"inc = %.8f\n",increment);
		
		for (c=0; c<numClauses; c++)
		{
			clause = clauses[c];


			minVar = numVars;
			maxVar = 1;


			for (v=0; v<clause->length; v++)
			{
				lit = clause->lits[v];
				var = mapVariables[abs(lit)];
				if (var < minVar) minVar = var;
				if (var > maxVar) maxVar = var;
			}
			
			variables[minVar].weight += increment/clause->length;
			variables[maxVar].weight -= increment/clause->length;
		}
		
	
		qsort (&variables[1], numVars, sizeof(Variable), variableCompare);
		

		converged = true;
		for (v=1; v<=numVars; v++)
		{
			//printf ("%d %.2f %d\n", v, variables[v].weight, variables[v].var);
			//if (abs(mapVariables[variables[v].var] - v) > maxDifference)
			//	maxDifference = abs(mapVariables[variables[v].var] - v);
			if (mapVariables[variables[v].var] != v)
				converged = false;
			mapVariables[variables[v].var] = v;
			variables[v].weight = v;
		}
		//printf ("---------------------------\n");
		
		//printf ("x %d\n", maxDifference);
		
	} while (!converged);
	


	remapClauses();

	for (c=0;c<numClauses;c++)
	{
		clause = clauses[c];
		qsort (clause->lits, clause->length, sizeof(int), litCompare);
	}


	qsort (clauses, numClauses, sizeof (ClausePtr), clauseCompare);
	
	
	
	if ((traceLevel & competitionTrace) > 0) { fprintf (outFile, "ce turns finished\n"); fflush(outFile);}
	
	checkFree (mapVariables);
}



BitSetPtr emptyBitSet, toRemove, other;
HashTablePtr *bitSetTable;
int wordLength;
int lastUnusedWords=0, unusedWords = 0, wordsToLose = 0;
uint64_t one = 1, zero = 0;

void initOneBitSet (BitSetPtr bs)
{
	mpz_init (bs->contribution);
	mpz_init (bs->previousContribution);
	bs->bits = NULL;
	bs->capacity = 0;
	mpz_set_ui (bs->contribution, 0);
	mpz_set_ui (bs->previousContribution, 0);

	bs->length = 0;
	bs->savedSize = 0;
	bs->posAdded = -1;
}


BitSetPtr newBitSet()
{
	BitSetPtr result;
	
	result = (BitSetPtr) getFromBlockList (stackOfBitSetPtrs);
	if (result == NULL)
	{
		result = checkMalloc (sizeof(BitSet),"newbitset result");
		initOneBitSet (result);
	}
	
	bitSetCount++;
	return result;
}

void initBitSetBlock (BlockPtr bp, int size)
{
	BitSet * bitSets;
	int i;
	
	bitSets = checkMalloc (size*sizeof (BitSet), "bitsets");
	for (i=0;i<size; i++)
	{
		initOneBitSet (bitSets+i);
		bp->items[i] = bitSets+i;
		bp->count = size;
	}
}

int bitSetCardinality (BitSetPtr bs)
{
	int count = 0;
	int i;
	for (i=0;i<bs->length; i++)
	{
		uint64_t l = bs->bits[i];
		count += __builtin_popcountll(l);
	}
	return count;
}

#define BITPOS2LIT(bp)	((bp%2==0)?(-(bp/2)):(bp/2))
#define LIT2BITPOS(l)	((l>0)?(2*l+1):( ((-2)*l ) ) )

void bitSetEnsureLength (BitSetPtr bs, int newLength)
{
	if (newLength > bs->capacity)
	{
		bs->bits = checkRealloc (bs->bits, newLength*sizeof(uint64_t), "ensurelength");
		bs->capacity = newLength;
	}
	if (newLength > bs->length)
	{
		memset (&bs->bits[bs->length], 0, (newLength-bs->length)*sizeof(uint64_t));
		bs->length = newLength;
	}
}

void bitSetEnsureSize (BitSetPtr bs, int newSize)
{
	bitSetEnsureLength (bs, (newSize-1)/wordLength + 1 - unusedWords);
}


void bitSetSet (BitSetPtr bs, int bp)
{
	int l;
	bitSetEnsureSize (bs, bp+1);
	l = bp/wordLength - unusedWords;
	uint64_t p = bp % wordLength;
	bs->bits[l] |= one << p;
}


int bitSetIsSet (BitSetPtr bs, int bp)
{
	if (bp >= (unusedWords + bs->length)*wordLength) return false;
	
	int l = bp/wordLength - unusedWords;
	uint64_t p = bp % wordLength;
	
	return (bs->bits[l] & (one<<p) ) != 0;
}

void bitSetClear(BitSetPtr bs, int bp)
{
	int newLength;
	if (bp >= (unusedWords + bs->length)*wordLength) return;
	
	int l = bp/wordLength - unusedWords;
	int p = bp % wordLength;
	bs->bits[l] &= ~ (one <<p);
	newLength = bs->length;
	while (newLength > 0 && bs->bits[newLength-1] == zero)
		newLength--;
	if (newLength < bs->length)
		bs->length = newLength;
}

void bitSetClearAll (BitSetPtr bs)
{
	memset(bs->bits, 0, bs->capacity*sizeof (uint64_t));
	bs->length = 0;
}

int bitSetSubset (BitSetPtr b1, BitSetPtr b2)
{
	int result = 1;
	int i;
	if (b1->length > b2->length)
		result = 0;
	else
	{
		for (i=0; result && i<b1->length; i++)
			if ( ( b1->bits[i] & (b2->bits[i]) ) != b1->bits[i] )
				result = 0;
	}
	return result;
}

int bitSetLastBitSet (BitSetPtr bs)
{
	int lpos;
	lpos = bs->length-1;
	while (lpos >= 0 && bs->bits[lpos] == zero) lpos--;
	if (lpos < 0)
		return -1;
	else
		return wordLength*(lpos+unusedWords+1) - __builtin_clzll(bs->bits[lpos]) - 1;
}

int bitSetNextSetBit (BitSetPtr bs, int index)
{
	int result, lpos, bpos;
	uint64_t l;
	
	if (index < unusedWords*wordLength)
		index = unusedWords*wordLength;
	lpos = index/wordLength - unusedWords;
	if (lpos >= bs->length) return -1;
	l = bs->bits[lpos];
	bpos = index % wordLength;
	
	l = l >>bpos;
	
	if (l == 0)
		bpos += wordLength;
	else
		bpos += __builtin_ctzll(l);
	
	if (bpos < wordLength)
	{
		result = bpos + (lpos+unusedWords)*wordLength;

		return result;
	}
	lpos++;
	while (lpos < bs->length && bs->bits[lpos] == 0x0) lpos++;
	if (lpos >= bs->length) return -1;
	l = bs->bits[lpos];
	bpos = __builtin_ctzll(l);
	result = bpos + (lpos+unusedWords)*wordLength;

	return result;
}

int bitSetNextClearBit (BitSetPtr bs, int index)
{
	int result, lpos, bpos;
	uint64_t l;
	
	if (index < unusedWords*wordLength)
		index = unusedWords*wordLength;
	lpos = index/wordLength - unusedWords;
	if (lpos >= bs->length) return index;
	l = bs->bits[lpos];
	bpos = index % wordLength;
	
	l = l >>bpos;
	
	if (~l == 0)
		bpos += wordLength;
	else
		bpos += __builtin_ctzll(~l);
	
	if (bpos < wordLength)
	{
		result = bpos + (lpos+unusedWords)*wordLength;
		return result;
	}
	lpos++;
	while (lpos < bs->length && (~bs->bits[lpos]) == 0x0) lpos++;
	if (lpos >= bs->length) return (lpos+unusedWords)*wordLength;
	l = bs->bits[lpos];
	bpos = __builtin_ctzll(~l);
	result = bpos + (lpos+unusedWords)*wordLength;
	return result;
}


void fprintBitSet1 (FILE *f, BitSetPtr bs)
{
	int first,i,p;
	first = true;
	p= -1;
	fprintf (f, "{");
	do
	{
		p = bitSetNextSetBit (bs, p+1);
		if (p != -1)
		{
			if (first)
			{
				first = false;
			}
			else
				fprintf (f, ",");
			fprintf (f, "%d", p);
		}
	} while (p != -1);
	fprintf (f, "}");
	
}
	
void fprintBitSet (FILE *f, BitSetPtr bs)
{
	int first,i,p;
	first = true;
	p= -1;
	fprintf (f, "{");
	do
	{
		p = bitSetNextSetBit (bs, p+1);
		if (p != -1)
		{
			if (first)
			{
				first = false;
			}
			else
				fprintf (f, ",");
			fprintf (f, "%d", BITPOS2LIT(p));
		}
	} while (p != -1);
	fprintf (f, "}");
	fprintf (f, "<");
	mpz_out_str (f, 10, bs->previousContribution);
	fprintf (f, ",");
	mpz_out_str (f, 10, bs->contribution);
	fprintf (f, ">(posa %d)",bs->posAdded);
	
}

uint64_t primes[] = {961748941,941083987,920419823,899809363,879190841,858599509,838041647,
817504253,797003437,776531419,756065179,735632797,694847539,654188429,633910111,982451653,
961748927,941083981,920419813,899809343,879190747,858599501};
#define PRIMES_COUNT 22

BitSetPtr bitSetGetUnique (BitSetPtr bs)
{
	BitSetPtr result;
	int v,b;
	b =  bitSetNextSetBit (bs, 0);
	if (b == -1) return emptyBitSet;
	v = b/2;
	//printf ("b=%d v=%d\n",b,v);fflush(stdout);
	bs->hashCode = bitSetHashCode(bs);
	result = hashTableSearchInsert (bitSetTable[v], bs);
	if (result == NULL)
	{
		result = bs;
		result->savedSize = bitSetCardinality(result);

	}
	
	
	return result;
}

void bitSetFinished (BitSetPtr bs)
{
	BitSetPtr this,previous;
	int v,b,slotNum;
	b =  bitSetNextSetBit (bs, 0);
	if (b == -1) return ;
	v = b/2;
	slotNum = bs->hashCode % bitSetTable[v]->currentNumOfSlots;
	this = bitSetTable[v]->currentSlots[slotNum];
	previous = NULL;
	while (this != bs)
	{
		previous = this;
		this = this->next;
	}
	if (previous == NULL)
		bitSetTable[v]->currentSlots[slotNum] = bs->next;
	else
		previous->next = bs->next;
	bitSetTable[v]->currentNumOfKeys--;
	bitSetcheckFree (bs);
}

#define SHUFFLE(x) ( (x) ^ (x>>16) ^ (x>>32) ^ (x>>48)  )

unsigned int bitSetHashCode (BitSetPtr bs)
{
	int p, start, end;
	uint64_t result;
	unsigned int intResult;
	for (start=0;start<bs->length && bs->bits[start]==0;start++);
	for (end=bs->length-1;end>0&&bs->bits[end] == 0; end--);
	if (start > end){ return 0;}
	//printf ("(%d %d) ", start,end);
	result = SHUFFLE(bs->bits[start])*primes[0];
	for (p=start+1; p<=end && p<PRIMES_COUNT+start-1; p++)
		result ^= SHUFFLE(bs->bits[p])*primes[p-(start)];
	
	
	
	intResult =  (unsigned int) (result ^ (result >> 32) );
	
	
	return intResult;
}

int bitSetEqual (BitSetPtr b1, BitSetPtr b2)
{
	int result,p;
	if (b1->length != b2->length) return 0;
	result = true;
	for (p=0; result && p <b1->length; p++)
		result = b1->bits[p] == b2->bits[p];
	
	return result;
		
}

void bitSetcheckFree (BitSetPtr bs)
{
	//if (bs->bits != NULL)
	//	checkFree (bs->bits);
	if (bs->capacity > 0)
	{
		bs->capacity = 0;
		checkFree (bs->bits);
		bs->bits = NULL;
	}

	mpz_clear (bs->contribution);
	mpz_clear (bs->previousContribution);
	mpz_init (bs->contribution);
	mpz_init (bs->previousContribution);


/*
	mpz_set_ui (bs->contribution, 0);
	mpz_set_ui (bs->previousContribution, 0);
*/

	bs->length = 0;
	bs->savedSize = 0;
	bs->posAdded = -1;
	
	addToBlockList (stackOfBitSetPtrs, bs);
	bitSetCount--;
}

void bitSetPrint (void *key)
{
}

void bitSetCopyOr (BitSetPtr dest, BitSetPtr src1, BitSetPtr src2)
{
	int newLength, smallLength, l;
	
	newLength = (src1->length>src2->length)?src1->length:src2->length;
	smallLength = (src1->length>src2->length)?src2->length:src1->length;
	bitSetEnsureLength (dest, newLength);
	
	for (l=0; l<smallLength; l++)
		dest->bits[l] = src1->bits[l] | src2->bits[l];
	
	for (l=smallLength; l<src1->length; l++)
		dest->bits[l] = src1->bits[l];
	
	for (l=smallLength; l<src2->length; l++)
		dest->bits[l] = src2->bits[l];
	
	dest->length = newLength;
	memset (&dest->bits[newLength], 0, (dest->capacity-newLength)*sizeof(uint64_t));
}

void bitSetCopy(BitSetPtr dest, BitSetPtr src)
{
	bitSetEnsureLength (dest, src->length);
	
	memcpy (dest->bits, src->bits, src->length*sizeof(uint64_t));
	
	dest->length = src->length;
	memset (&dest->bits[dest->length], 0, (dest->capacity-dest->length)*sizeof(uint64_t));
}

void bitSetAndNot (BitSetPtr dest, BitSetPtr src)
{
	int limit, l;
	limit = (dest->length>src->length)?src->length:dest->length;
	for (l=0; l<limit; l++)
		dest->bits[l] &= ~src->bits[l];
	limit = dest->length;
	while (limit > 0 && dest->bits[limit] == 0)
		limit++;
	if (limit < dest->length)
		dest->length = limit;
}

BitSetPtr getReducedBitSet (BitSetPtr bs)
{
	BitSetPtr result;
	bitSetCopy (other, bs);
	bitSetAndNot (other, toRemove);
	if (bitSetEqual (bs, other)) return bs;
	result = bitSetGetUnique (other);
	if (result == other)
	{
		other = newBitSet();
	}
	return result;
}

BitSetPtr newBitSetFromClause(ClausePtr clause)
{
	BitSetPtr result;
	int l;
	result = newBitSet();
	for (l=0; l<clause->length; l++)
		bitSetSet (result, LIT2BITPOS(clause->lits[l]));
	return result;
}

void bitSetNoteVarsToRemove (int *vars)
{
	int p,bp;
	bitSetClearAll (toRemove);
	
	for (p=0; vars[p] != 0; p++)
	{
		//printf ("removing %d\n", vars[p]);
		bp = 2*vars[p];
		bitSetSet (toRemove, bp);
		bitSetSet (toRemove, bp+1);
	}
}

void bitSetRemoveVarSet (BitSetPtr bs)
{
	bitSetAndNot (bs, toRemove);
}

void bitSetFreeBitSetsBeginningWith (int *vars)
{
	int p;

	for (p=0; vars[p] != 0; p++)
	{
		freeHashTable (bitSetTable[vars[p]]);
		bitSetTable[vars[p]] = NULL;
	}
}

mpz_t temp_mpz1;

void initBitSets()
{
	int v;
	uint64_t temp;
	
	temp = 1;
	wordLength = 0;
	while (temp != 0)
	{
		temp <<= 1;
		wordLength++;
	}

	stackOfBitSetPtrs = newBlockList (1000);
	initBitSetBlock (stackOfBitSetPtrs->first, stackOfBitSetPtrs->blockSize);
	
	mpz_init (temp_mpz1);
	emptyBitSet = newBitSet();
	toRemove = newBitSet();
	other = newBitSet();
	bitSetTable = checkMalloc((1+numVars)*sizeof(HashTablePtr),"bitsettable");
	for (v=1; v<= numVars; v++)
		bitSetTable[v] = newHashTable ();
}

void bitSetSetContribution (BitSetPtr bs, mpz_t c)
{
	mpz_set (bs->contribution, c);
}

void bitSetAddContribution (BitSetPtr bs, mpz_t c)
{
	mpz_add (bs->contribution, bs->contribution, c);
}

int bitSetIsBitSet(BitSetPtr bs, int bp);

void bitSetNextContribution (BitSetPtr bp)
{
	mpz_mul_2exp (bp->contribution, bp->contribution, numFirstVars);
	mpz_set (bp->previousContribution, bp->contribution);
	mpz_realloc2 (bp->contribution, mpz_sizeinbase(bp->contribution,2));
	mpz_realloc2 (bp->previousContribution, mpz_sizeinbase(bp->previousContribution,2));
}

void bitSetNextContributionSetPos (BitSetPtr bp)
{
	bp->posAdded = pos;
	mpz_mul_2exp (bp->contribution, bp->contribution, numFirstVars);
	mpz_set (bp->previousContribution, bp->contribution);
	mpz_realloc2 (bp->contribution, mpz_sizeinbase(bp->contribution,2));
	mpz_realloc2 (bp->previousContribution, mpz_sizeinbase(bp->previousContribution,2));
}

void bitSetSetNegativeContribution (BitSetPtr bp, mpz_t c, int size)
{
	
	mpz_clear (bp->contribution);
	mpz_init (bp->contribution);
	mpz_tdiv_q_2exp (bp->contribution, c, size);
	mpz_neg (bp->contribution, bp->contribution);

}

int zerocount = 0;

void bitSetAddNegativeContribution (BitSetPtr bp, mpz_t c, int size)
{
	mpz_tdiv_q_2exp (temp_mpz1, c, size);
	//fprintf (outFile, "subtracting "); mpz_out_str(outFile, 10,temp_mpz1); fprintf(outFile,"\n");
	mpz_sub (bp->contribution, bp->contribution, temp_mpz1);
	//mpz_realloc2 (bp->contribution, mpz_sizeinbase(bp->contribution,2));
}

int bitSetClashesClause (BitSetPtr bs, ClausePtr clause)
{
	int l,lit;
	
	for (l=0; l<clause->length; l++)
		if (bitSetIsBitSet(bs, LIT2BITPOS(-clause->lits[l]))) break;
	
	return l < clause->length;
}

int bitSetIntersects (BitSetPtr bs1, BitSetPtr bs2)
{
	int limitLength = (bs1->length>bs2->length)?bs2->length:bs1->length;
	uint64_t *p1,*p2,*limit;
	p1 = bs1->bits; p2 = bs2->bits;
	limit = p1 + limitLength;
	while ( (p1 != limit) && ( !(*p1 & *p2) ) ){p1++; p2++;}
	return p1 != limit;
}

void bitSetReduce(BitSetPtr bs)
{
	int i;


	
	if (bs->length > wordsToLose)
	{
		bs->length -= wordsToLose;
		memmove (&bs->bits[0], &bs->bits[wordsToLose], (bs->length)*sizeof(uint64_t));
		//for (i=bs->length; i<bs->capacity;i++) printf (".");
		bs->capacity = bs->length;
		bs->bits = checkRealloc (bs->bits, bs->length*sizeof(uint64_t),"bitsetreduce");
		bs->hashCode = bitSetHashCode (bs);
	}
	else
	{
		
		bs->length = 0;
		bs->capacity = 0;
		checkFree (bs->bits);
		bs->bits = NULL;
	}
}

BitSetPtr clauseToBitSet (ClausePtr clause)
{
	int p;
	BitSetPtr result = newBitSet();
	for (p=0; p<clause->length; p++)
		bitSetSet (result, LIT2BITPOS(clause->lits[p]));
	return result;
	
}

void bitSetMakeNegBitSet (BitSetPtr neg, BitSetPtr bs)
{
	int bp;
	bitSetClearAll (neg);
	for (bp = bitSetNextSetBit(bs, 0); bp >= 0; bp = bitSetNextSetBit(bs, bp+1))
	{
		if (bp % 2 == 0)
			bitSetSet (neg, bp+1);
		else
			bitSetSet (neg, bp-1);
	}
}

int bitSetIsBitSet (BitSetPtr bs, int index)
{
	int l, p;
	if (index >= (unusedWords + bs->length)*wordLength) return false;
	
	l = index/wordLength - unusedWords;
	p = index % wordLength;
	
	return (bs->bits[l] & one<<p ) != 0;
}

void processBar (char *label, int value, int max)
{
	int scale=20;
	int i;
	int progress = (int) ( ( ( (double)value*scale) / max) );
	fprintf (outFile, "ce %s ", label);
	for (i=0; i<10-strlen(label); i++) fprintf(outFile, " ");
	for (i=0; i<progress; i++) fprintf (outFile,"*");
	for (i=progress; i<scale; i++) fprintf (outFile,".");
	fprintf (outFile,"\n");
}

void printBitSetTables()
{
	int v;
	HashTablePtr table;
	for (v=1; v<=numVars; v++)
	{
		printf ("%d ",v);
		table = bitSetTable[v];
		
		if (table == NULL)
			printf ("NULL\n");
		else
			printf ("table=%p numslots=%d slots=%p\n", table,table->currentNumOfSlots,table->currentSlots);
	}
	fflush(stdout);
}

void printProgress()
{
	int i;
	time_t timeNow;
	double timeUsed;
	
	if ((traceLevel & competitionTrace) > 0)
	{
		time (&timeNow);
		fprintf(outFile, "ce time %.0f(s) pos %d ", difftime(timeNow,startTime),pos);
		if (pos > 0)
		{
			fprintClause(outFile, clauses[pos]);
			fprintf (outFile, "(c %d) nodes %d (%d)\n", clauses[pos]->bitSet->capacity,blockListSize(clauseSet), bitSetCount);
		}
		else
			fprintf(outFile,"\n");
	}
	else
	{
		time (&timeNow);
		timeUsed = difftime(timeNow, startTime);
		fprintf(outFile, "\nc o FILENAME=<%s>\n", filename); fflush (outFile);
		fprintf(outFile, "ce elapsed time %.0f ", timeUsed); fflush (outFile);
		if (elapsedLimit > 0)
		{
			fprintf (outFile, "(limit %d) ", elapsedLimit);
		}
		fprintf(outFile, "seconds\n");
		fflush (outFile);
		if (traceLevel > 0)
		{
			fprintf (outFile, "ce allocated space %dMB", megaBytes); 
			if (memoryLimit > 0) fprintf (outFile, "(limit %dGB) ", memoryLimit);
			fprintf (outFile,"\n");
			fflush(outFile);
			if (pos > 0)
			{
				fprintf(outFile, "ce %d nodes (%d)\n", blockListSize (clauseSet),bitSetCount);
				fprintf(outFile, "ce clause number %d ", pos);
				fprintClause (outFile,clauses[pos]);
				fprintf (outFile,"\n");
				processBar ("clauses", pos, numClauses);
			}
		}
		if (elapsedLimit > 0)
			processBar ("time", (int) timeUsed, elapsedLimit);
		if (cpuLimit > 0)
			processBar ("cpu", (int) getCPUTimeSinceStart(), cpuLimit);
		if (memoryLimit > 0)
		{
			processBar ("memory", megaBytes, 1024*memoryLimit);
		}
		fflush (outFile);
	}
}

int * blockListToIntArray (BlockListPtr blp)
{
	int *result,p;
	result = checkMalloc ((blockListSize(blp)+1)*sizeof(int),"blocklisttointarray");
	p = 0;
	startScanBlockList (blp);
	while (hasNextBlockList(blp))
	{
		result[p++] = (uint64_t) getNextBlockList(blp);
	}
	result[p] = 0;
	return result;
}

void setupFirstAndLastVars()
{
	BlockListPtr *firstvb, *lastvb;
	int *firstc,*lastc,v,c,p;
	ClausePtr clause;
	
	firstvb = checkMalloc (numClauses*sizeof(BlockListPtr),"firstvb");
	lastvb = checkMalloc (numClauses*sizeof(BlockListPtr),"lastvb");
	for (c=0;c<numClauses;c++)
	{
		firstvb[c] = newBlockList (10);
		lastvb[c] = newBlockList (10);
	}
	firstc = checkMalloc((1+numVars)*sizeof(int),"firstc");
	lastc = checkMalloc((1+numVars)*sizeof(int),"lastc");
	
	for (v=1;v<=numVars;v++)
	{
		firstc[v] = 0;
		lastc[v] = 0;
	}
	
	for (c=0;c<numClauses;c++)
	{
		clause = clauses[c];
		for (p=0;p<clause->length;p++)
		{
			lastc[abs(clause->lits[p])] = c;
		}
	}
	for (c=numClauses-1;c>=0;c--)
	{
		clause = clauses[c];
		for (p=0;p<clause->length;p++)
		{
			firstc[abs(clause->lits[p])] = c;
		}
	}
	
	for (v=1;v<=numVars;v++)
	{
		addToBlockList(firstvb[firstc[v]], (void *)(uint64_t)v);
		addToBlockList(lastvb[lastc[v]], (void *)(uint64_t)v);
	}

	firstVars = checkMalloc (numClauses*sizeof(int *),"firstvars");
	lastVars = checkMalloc (numClauses*sizeof(int *),"lastvars");
	
	for (c=0; c<numClauses; c++)
	{
		firstVars[c] = blockListToIntArray(firstvb[c]);
		lastVars[c] = blockListToIntArray(lastvb[c]);
	}
	
	for (c=0;c<numClauses;c++)
	{
		freeBlockList(firstvb[c]);
		freeBlockList(lastvb[c]);
	}
	checkFree (firstvb);
	checkFree (lastvb);
	checkFree (firstc);
	checkFree (lastc);
	

	
	
}

int intListSize (int *list)
{
	int result;
	for (result = 0; list[result] != 0; result++);
	return result;
}

TreeNodePtr treeSentinel;

TreeNodePtr newTreeNode()
{
	TreeNodePtr result;
	result = checkMalloc (sizeof(TreeNode),"newtreenode");
	result->present = NULL;
	result->absent = NULL;
	result->lit = 0;
	result->bitPos = 0;
	return result;
}

TreeNodePtr newTreeNodeParams(int lit, TreeNodePtr present, TreeNodePtr absent)
{
	TreeNodePtr result;
	result = checkMalloc (sizeof(TreeNode),"newTreeNodeParams");
	result->present = present;
	result->absent = absent;
	result->lit = lit;
	result->bitPos = LIT2BITPOS(lit);
	
	return result;
}

void initTrees()
{
	treeSentinel = newTreeNode();
}

void freeTreeNode(TreeNodePtr tn)
{
	if (tn != NULL && tn != treeSentinel)
	{
		freeTreeNode (tn->present);
		freeTreeNode (tn->absent);
		checkFree (tn);
	}
}

TreeNodePtr addClausetToTreeSub (TreeNodePtr tn, ClausePtr clause, int pos)
{
	TreeNodePtr result, present, absent;
	int lit;
	
	if (pos == clause->length || tn == treeSentinel)
		result = treeSentinel;
	else
	{
		lit = clause->lits[pos];
		if (tn == NULL)
		{
			present = addClausetToTreeSub (NULL, clause, pos+1);
			absent = NULL;
			result = newTreeNodeParams (lit, present, absent);
		}
		else switch (litCompare (&tn->lit, &lit))
		{
			case -1:
				tn->absent = addClausetToTreeSub (tn->absent, clause, pos);
				result = tn;
				break;
				
			case 0:
				tn->present = addClausetToTreeSub (tn->present, clause, pos+1);
				result = tn;
				break;
				
			case 1:
				present = addClausetToTreeSub (NULL, clause, pos+1);
				absent = tn;
				result = newTreeNodeParams (lit, present, absent);
				break;
		}
	}
	
	return result;
}

TreeNodePtr addClauseToTree (TreeNodePtr tn, ClausePtr clause)
{
	return addClausetToTreeSub (tn, clause, 0);
}

ClausePtr clausesToCheck[100];
int countClausesToCheck;

TreeNodePtr getTreeNode (int pos, BitSetPtr thisBitSet, BitSetPtr negBitSet)
{
	TreeNodePtr result;
	ClausePtr clause,other;
	int p,lit;
	BlockListPtr blp;
	
	result = NULL;
	
	clause = clauses[pos];
	int count = 0;
	for (p=0; p<clause->length; p++)
	{
		blp = varToClause[abs(clause->lits[p])];
		startScanBlockList (blp);
		while (hasNextBlockList(blp))
		{
			other = (ClausePtr) getNextBlockList(blp);
			if (other->pos > pos && other->posAdded < pos && !bitSetIntersects (negBitSet, other->bitSet) )
			{
				result = addClauseToTree (result, other);
				other->posAdded = pos;
				count++;
			}
				
		}
	}

	return result;
	
}

int treeContainsSubsetOfSub (TreeNodePtr tn, BitSetPtr bs, int lastSetBit)
{
	int bp;
	
	if (tn == NULL)
		return false;
	else if (tn == treeSentinel)
		return true;
	else
	{
		bp = tn->bitPos;
		if (bp > lastSetBit)
			return false;
		else if (bitSetIsBitSet (bs, bp))
			return treeContainsSubsetOfSub (tn->present, bs, lastSetBit) || treeContainsSubsetOfSub (tn->absent, bs, lastSetBit);
		else
			return treeContainsSubsetOfSub (tn->absent, bs, lastSetBit);
	}
}

int treeContainsSubsetOf (TreeNodePtr tn, BitSetPtr bs)
{
	int result = treeContainsSubsetOfSub (tn, bs, bitSetLastBitSet(bs));

	return result;
}




void checkMemory()
{
	
	if (memoryLimit > 0)
	{
		if (gigaBytes >= memoryLimit)
		{
			memoryReason = "limit reached";
			printFinal (STATUS_OUT_OF_MEMORY);
		}
	}
	

}

void mapBlockList (BlockListPtr blp, void f (BitSetPtr g))
{
	BlockPtr bp = blp->first;
	int i;
	BitSetPtr *p,*limit;
	while (bp != NULL)
	{
		p = (BitSetPtr *) bp->items;
		limit = p + bp->count;
		while (p != limit)
			f (*(p++));
		bp = bp->next;
	}
}

void clearUnusedBitSets()
{
	int v,s,numSlots, count;
	int num=0,dem=0;
	BitSetPtr bs, next, previous, *slots;
	for (v=1;v<=numVars;v++)
	{
		if (bitSetTable[v] != NULL)
		{
			numSlots = bitSetTable[v]->currentNumOfSlots;
			slots = bitSetTable[v]->currentSlots;
			for (s=0; s<numSlots; s++)
			{
				bs = slots[s];
				previous = NULL;
				while (bs != NULL)
				{
					dem++;
					next = bs->next;
					if (bs->posAdded < pos)
					{
						if (previous == NULL)
							slots[s] = next;
						else
							previous->next = next;
						bitSetcheckFree (bs);
						bitSetTable[v]->currentNumOfKeys--;
						num++;
					}
					bs = next;
				}
			}
		}
	}
}

void tracePrintBitSet (BitSetPtr bitSet)
{
	fprintBitSet (outFile, bitSet);
	fprintf (outFile, "\n");
}

void bitSetSetPos (BitSetPtr bitSet)
{
	bitSet->posAdded = pos;
}

BitSetPtr thisBitSet, negBitSet, fullNextClause;
ClausePtr currentClause;
TreeNodePtr thisTree;
int areLastVars;

void bitSetRemoveVars (BitSetPtr bitSet)
{
	BitSetPtr reducedBitSet;;
	
	if (mpz_sgn(bitSet->previousContribution) != 0)
	{
		reducedBitSet = getReducedBitSet (bitSet);
		//fprintf (outFile,"reduced "); fprintBitSet (outFile, thisBitSet); fprintBitSet (outFile, reducedBitSet); fprintf (outFile,"\n");
		if (reducedBitSet != bitSet)
		{
			bitSetAddContribution (reducedBitSet, bitSet->contribution);
		}
		//fprintf (outFile,"reduced "); fprintBitSet (outFile, thisBitSet); fprintBitSet (outFile, reducedBitSet); fprintf (outFile,"\n");
		if (reducedBitSet->posAdded < pos)
		{
			addToBlockList (nextClauseSet, reducedBitSet);
			reducedBitSet->posAdded = pos;
		}
	}
}

int zeros, total;

void countZeros (BitSetPtr otherBitSet)
{
	total++;
	if (mpz_sgn(otherBitSet->contribution) == 0)
		zeros++;
}

double capacity;
void countCapacity (BitSetPtr otherBitSet)
{
	total++;
	capacity += otherBitSet->capacity;
}


void mainBlock (BitSetPtr otherBitSet)
{
	int fullNextClauseLits, extraLits;
	BitSetPtr nextBitSet;
	
	
	//otherBitSet = (BitSetPtr) getNextBlockList(clauseSet);
	if (mpz_sgn(otherBitSet->previousContribution) != 0)
	{
		//fprintf (outFile,"B\n");
		if (!bitSetIntersects(otherBitSet, negBitSet))
		//if (!bitSetClashesClause(otherBitSet, currentClause))
		{
			bitSetCopyOr (fullNextClause, thisBitSet, otherBitSet);
			//fprintf (outFile, "fullnextclause "); fprintBitSet (outFile, fullNextClause); fprintf (outFile,"\n");
			fullNextClauseLits = bitSetCardinality (fullNextClause);
			//fprintf (outFile, "count %d\n", fullNextClauseLits);
			if (areLastVars)
				bitSetRemoveVarSet (fullNextClause);
			//fprintf (outFile,"C\n");
			if (!treeContainsSubsetOf (thisTree, fullNextClause) )
			{
				operations++;
				nextBitSet = bitSetGetUnique(fullNextClause);
				if (nextBitSet == fullNextClause)
					fullNextClause = newBitSet();
				extraLits = fullNextClauseLits - otherBitSet->savedSize;
				if (nextBitSet->posAdded == pos)
				{
					bitSetAddNegativeContribution (nextBitSet, otherBitSet->previousContribution, extraLits);
				}
				else
				{
					bitSetSetNegativeContribution(nextBitSet, otherBitSet->previousContribution, extraLits);
					addToBlockList(nextClauseSet, nextBitSet);
					nextBitSet->posAdded = pos;
				}
			}
		}
	}
}


void buildLists()
{
	BlockListPtr tempClauseSet, blockList1, blockList2;
	int c, v;
	BitSetPtr otherBitSet, reducedBitSet;
	ClausePtr thisClause;
	char * processedVariables;
	int *varp;
	int checkCount=0;
	
	int nextEndOfRange, longSize, localUnusedWords, unusedWordsChanged;
	int lastProcessedRange = 0;
	int longEnd;
	
	
	
	mpz_t bigOne;
	
	setUpVarToClause();
	processedVariables = checkMalloc ((2+numVars)*sizeof(char),"processedvariables");
	for (v=1;v<=numVars+1;v++)
		processedVariables[v] = 0;
	
	for (c=0; c<numClauses; c++)
	{
		clauses[c]->bitSet = clauseToBitSet(clauses[c]);
		clauses[c]->pos = c;
	}
	
	
	negBitSet = newBitSet();

	setupFirstAndLastVars();
	
	mpz_init (bigOne);
	mpz_set_ui (bigOne, 1);
	
	bitSetSetContribution (emptyBitSet, bigOne);
	emptyBitSet->posAdded = -1;
	
	blockList1 = newBlockList(50000);
	blockList2 = newBlockList (50000);
	clauseSet = blockList1;
	nextClauseSet = blockList2;
	
	addToBlockList (clauseSet, emptyBitSet);
	fullNextClause = newBitSet();
	for (pos=0; pos<numClauses; pos++)
	{
		
		if (traceLevel > 0)
			printProgress ();
		
		checkElapsed();
		//checkMemory();
		
		if (traceLevel &eachPosClausesTrace)
		{
			mapBlockList (clauseSet, tracePrintBitSet);
			
		}
		
		numFirstVars = intListSize (firstVars[pos]);
		
		areLastVars = lastVars[pos][0] > 0;
		
		
		if (areLastVars)
		{
			mapBlockList (clauseSet, bitSetNextContribution);
			bitSetNoteVarsToRemove (lastVars[pos]);
			mapBlockList (clauseSet, bitSetRemoveVars);
		}
		else
		{
			mapBlockList (clauseSet, bitSetNextContributionSetPos);
			nextClauseSet = clauseSet;
		}

		if ((traceLevel & fullClausesTrace) > 0)
		{
			fprintf (outFile, "\n--------------------\n");
			startScanBlockList (clauseSet);
			while (hasNextBlockList (clauseSet))
			{
				thisBitSet = (BitSetPtr) getNextBlockList(clauseSet);
				fprintBitSet (outFile, thisBitSet);
				fprintf (outFile, "\n");
			}
			fprintf (outFile, "--------------------\n\n");
		}
		
		thisClause = clauses[pos];
		currentClause = thisClause;
		thisBitSet = thisClause->bitSet;
		bitSetMakeNegBitSet (negBitSet, thisBitSet);
		thisTree = getTreeNode (pos, thisBitSet, negBitSet);
		
		startScanBlockList (clauseSet);

		if (!treeContainsSubsetOf (thisTree, thisBitSet))
		{
			mapBlockList (clauseSet, mainBlock);

		}
		

/*
		total = 0;
		zeros = 0;
		mapBlockList (nextClauseSet, countZeros);
		printf ("%d %d %f\n", total, zeros, ( (double) zeros) /total);
*/

/*
		total = 0;
		capacity = 0;
		mapBlockList (nextClauseSet, countCapacity);
		printf ("%d %f\n", total, capacity/total);
	*/
	
		
		varp = lastVars[pos];
		
		while (*varp != 0)
		{
			processedVariables[*varp] = 1;
			varp++;
		}
		
		v = lastProcessedRange+1;
		while (processedVariables[v] == 1)
			v++;
		
		nextEndOfRange = v-1;
		longSize=wordLength/2;
		localUnusedWords = 0;
		unusedWordsChanged = false;
		for (longEnd=1+(lastProcessedRange+1)/longSize; longEnd<=(nextEndOfRange+1)/longSize; longEnd++)
		{
			localUnusedWords = longEnd;
			unusedWordsChanged = true;
		}
		if (unusedWordsChanged)
		{
			//ClauseBitSet.setUnusedWords (unusedWords);
			//for (ClauseBitSet clause: nextClauseSet)
			//	clause.reduce();
			//ClauseBitSet.noteUnusedWordsProcessed();
			unusedWords = localUnusedWords;
			wordsToLose = unusedWords - lastUnusedWords;
			mapBlockList (nextClauseSet, bitSetReduce);
			bitSetReduce(emptyBitSet);
			//bitSetReduce(negBitSet);
			bitSetReduce(fullNextClause);
			//bitSetReduce(otherBitSet);
			bitSetReduce(other);
			
			for (v=pos+1; v<numClauses; v++)
				bitSetReduce (clauses[v]->bitSet);
			
			lastUnusedWords = unusedWords;
			wordsToLose = 0;
		
		}
		lastProcessedRange = nextEndOfRange;		
		bitSetFreeBitSetsBeginningWith (lastVars[pos]);

		freeTreeNode (thisTree);
		
		clauseSet = nextClauseSet;
		if (clauseSet == blockList1)
			nextClauseSet = blockList2;
		else
			nextClauseSet = blockList1;
		clearBlockList (nextClauseSet);
		
		//clearUnusedBitSets(); // Takes more time than it's worth
		

		
	}
}

void term (int signum)
{
	switch (signum)
	{
		case SIGINT:
			printFinal (STATUS_SIGINT_RECEIVED);
			break;
			
		case SIGTSTP:
			printProgress();
			break;
	
		case SIGTERM:
		default:
			printFinal (STATUS_SIGTERM_RECEIVED);
			break;
	}
}

void checkFor2Clauses()
{
	int count= 0;
	int c;
	ClausePtr clause;
	
	for (c=0;c<numClauses;c++)
	{
		clause = clauses[c];
		if (clause->length == 2) count++;
	}
	
	fprintf (stdout, "2-clauses %d %d\n", count,numClauses);
	exit(0);
}

void optimiseClause (ClausePtr clause)
{
	int v1,v2;
	v2 = 1;
			//fprintf (outFile, "opt "); fprintClause (outFile, clause);
			
	qsort (clause->lits, clause->length, sizeof(int), litCompare);
	for (v1=1;v1<clause->length;v1++)
	{
		if (clause->lits[v1] == -clause->lits[v1-1])
			clause->redundant = 1;
		else if (clause->lits[v1] != clause->lits[v1-1])
			clause->lits[v2++] = clause->lits[v1];
	}
	clause->length = v2;
	
			//fprintf (outFile, " "); fprintClause (outFile, clause); fprintf (outFile,"\n");
			
}

void optimisePairs()
{
	ClausePtr clause1,clause2;
	int c,v1,v2,l1,l2,la1,la2,oldNumClauses,v,temp;
	int pairsFound = 0, found;
	
	optimised = (int *) checkMalloc ( (1+numVars)*sizeof(int), "optimised");
	for (v=1;v<=numVars;v++)
		optimised[v] = 0;
	
	return;

	setUpVarToClause();
	

	for (c=0;c<numClauses;c++)
	{
		clause1 = clauses[c];
		if (!clause1->redundant && clause1->length == 2)
		{
			l1 = clause1->lits[0];
			v1 = abs(l1);
			l2 = clause1->lits[1];
			v2 = abs (l2);
			if (v1 > v2)
			{
				temp = v1;
				v1 = v2;
				v2 = temp;
				temp = l1;
				l1 = l2;
				l2 = temp;
			}
			found = 0;
			startScanBlockList (varToClause[v1]);
			while (!found && hasNextBlockList(varToClause[v1]))
			{
				clause2 = getNextBlockList(varToClause[v1]);
				if (clause2->length == 2)
				{
					la1 = clause2->lits[0];
					la2 = clause2->lits[1];
					if ( ( la1 == -l1 && la2 == -l2) || ( la1 == -l2 && la2 == -l1))
					{
						clause1->redundant = 1;
						clause2->redundant = 1;
						optimised[v2] = 1;
						pairsFound++;
						found = 1;
					}
				}
			}
			if (found)
			{
				startScanBlockList (varToClause[v2]);
				while (hasNextBlockList(varToClause[v2]))
				{
					clause2 = getNextBlockList(varToClause[v2]);
					if (!clause2->redundant)
					{
						for (v=0; v<clause2->length; v++)
						{
							if (abs(clause2->lits[v]) == v2)
								if (clause2->lits[v] == l2)
									clause2->lits[v] = -l1;
								else
									clause2->lits[v] = l1;
						}
						optimiseClause(clause2);
					}
				}
				
			
			}
			
		}
	}
	
	if (pairsFound > 0)
	{
		fprintf (outFile, "c o PAIRSFOUND=%d\n", pairsFound);
		oldNumClauses = numClauses;
		numClauses = 0;
		for (c=0;c<oldNumClauses;c++)
		{
			if (!clauses[c]->redundant)
				clauses[numClauses++] = clauses[c];
		}

	}
	
	freeVarToClause();
}

int main(int argc, char *argv[])
{
	int c;
	int returnValue;
	

	time (&startTime);
	time_t sortTime;
	initCPUTime();

	
	struct sigaction action;

	outFile = stdout;

	memset (&action, 0, sizeof(struct sigaction));
	action.sa_handler = term;
	//sigaction (SIGTERM, &action, NULL);
	sigaction (SIGINT, &action, NULL);
	sigaction (SIGTSTP, &action, NULL);
			
	processArgs (argc, argv);
	
	readProposition();
	
	if (!noReduce)
	{
		propagateUnitClauses();
		optimisePairs();

		sortSubProblems();
	
		fprintf (outFile, "c o FINAL-VARIABLES=%d\n",numVars); fflush (outFile);
		fprintf (outFile, "c o FINAL-CLAUSES=%d\n",numClauses); fflush (outFile);

		time (&sortTime);
		fprintf (outFile, "c o ELAPSED-TIME-SORT-SECONDS=%.1f\n", difftime (sortTime, startTime)); fflush (outFile);
		
		//sortVarsAndClauses();
	}
	

	
	initTrees();
	
	initBitSets();
	
	buildLists();
	
	printFinal (STATUS_SUCCESSFUL);
	
	
/*
	for (c=0; c<numClauses; c++)
	{
		fprintClause (outFile, clauses[c]);
		fprintf (outFile, "\n");
	}
*/
	return 0;
}