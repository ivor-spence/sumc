/*******************

Copyright (C) <2020>  <Ivor Spence>

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

#include <time.h>
#include <signal.h>
#include <malloc.h>


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

FILE *inFile, *outFile;
char *filename;

int traceLevel;
int competitionTrace = 1<<1;
int normalProgressTrace = 1<<2;
int fullClausesTrace = 1<<3;

time_t startTime;


int ch;
int originalNumVars, originalNumClauses, numFirstVars;
int numVars, numClauses, unusedVariables;
int elapsedLimit, turnsLimit, memoryLimit, noReduce;
char *memoryReason = "";

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
	int length, savedSize, capacity;
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
int *mapVariables;
int **firstVars, **lastVars;
BlockListPtr clauseSet, nextClauseSet;
int pos=0;


 

typedef struct HashTableStruct
{
	int currentNumOfSlots, nextNumOfSlots;
	BitSetPtr *currentSlots;
	int currentNumOfKeys;
	
} HashTable,*HashTablePtr;

void bitSetFree (BitSetPtr bs);
unsigned int bitSetHashCode (BitSetPtr bs);
int clauseCompare (const void *c1, const void *c2);


int strEqual (char *s1, char *s2)
{
	return strcmp (s1,s2) == 0;
}



void printFinal(int status)
{
	time_t endTime;
	time (&endTime);
	fprintf (outFile, "c Elapsed time %.1f seconds\n", difftime (endTime, startTime));
	mpz_t finalCount;
	
	switch (status)
	{
		case STATUS_SUCCESSFUL:
			fprintf (outFile, "c Completed normally\n");
			mpz_init (finalCount);
			mpz_mul_2exp (finalCount, ((BitSetPtr)clauseSet->first->items[0])->contribution, unusedVariables);
			fprintf (outFile, "s mc ");
			mpz_out_str (outFile, 10, finalCount);
			fprintf (outFile, "\n");
			fprintf (stderr, "ce printing s mc ");
			mpz_out_str (stderr, 10, finalCount);
			fprintf (stderr, "\n");
			mpz_clear (finalCount);
			break;
			
		case STATUS_UNSAT_FOUND:
			fprintf (outFile, "c UNSAT found by unit propagation\n");
			fprintf (outFile, "s mc 0\n");
			fprintf (stderr, "ce UNSAT found by unit propagation\n");
			fprintf (stderr, "s mc 0\n");
			exit (0);
			
		case STATUS_SIGINT_RECEIVED:
			fprintf (outFile, "c SIGINT received\n");
			fprintf (stderr, "ce SIGINT received\n");
			exit(1);
			break;
			
		case STATUS_SIGTERM_RECEIVED:
			fprintf (outFile, "c SIGTERM received\n");
			fprintf (stderr, "ce SIGTERM received\n");
			exit(1);
			break;
			
		case STATUS_OUT_OF_MEMORY:
			fprintf (outFile, "c Error - out of memory <%s>\n", memoryReason);
			fprintf (stderr, "ce Error - out of memory <%s>\n", memoryReason);
			fprintProposition (stderr, numVars, numClauses, clauses);
			exit(1);
			break;

		case STATUS_OUT_OF_TIME:
			fprintf (outFile, "c Error - out of time\n");
			fprintf (stderr, "ce Error - out of time\n");
			exit(1);
			break;
			
			
		case STATUS_INPUT_NOT_FOUND:
			fprintf (outFile, "c Error - no input\n");
			fprintf (stderr, "c Error - no input\n");
			exit(1);
			break;
			
		case STATUS_SYNTAX_ERROR:
			fprintf (outFile, "c Error - syntax\n");
			fprintf (stderr, "ce Error - syntax\n");
			exit(1);
			break;
		default:
			break;
	}
	
}


void * checkMalloc (size_t size, char *reason)
{
	void *result = malloc (size);
	if (result == NULL)
	{
		memoryReason = reason;
		printFinal (STATUS_OUT_OF_MEMORY);
	}
	return result;
}

void * checkRealloc (void *p, size_t size, char *reason)
{
	void *result = realloc (p, size);
	if (result == NULL)
	{
		memoryReason = reason;
		printFinal (STATUS_OUT_OF_MEMORY);
	}
	return result;
}



HashTablePtr newHashTable ()
{
	HashTablePtr result;
	int i;

	result = (HashTablePtr) checkMalloc (sizeof(HashTable),"hashtable");

	result->currentNumOfSlots = (2<<10)-1;
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
			bitSetFree (b);
			b = next;
		}
	}
	free (hashTable->currentSlots);
	free (hashTable);
}


void hashTableExpand (HashTablePtr hashTable)
{
	int i, slotNum,currentNumOfSlots;
	unsigned long newNumOfSlots;
	unsigned long newPosition;
	BitSetPtr bs,next,previous,*slots;

	currentNumOfSlots = hashTable->currentNumOfSlots;
	newNumOfSlots = 2*currentNumOfSlots;
	hashTable->currentSlots = checkRealloc (hashTable->currentSlots,newNumOfSlots*sizeof(BitSetPtr),"expand slots");
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


BitSetPtr hashTableSearchInsert (HashTablePtr hashTable, BitSetPtr bs)
{

	BitSetPtr *start,bs2;

	start = hashTable->currentSlots + (bs->hashCode % hashTable->currentNumOfSlots);
	bs2 = *start;
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
	free (bp->items);
	free (bp);
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
	free (blp);
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
	
	result = defaultValue;
	found = false;
	
	for (p=0; p<argc-1 && !found; p++)
	{
		found = strEqual (argv[p], tag);
		if (found)
			sscanf (argv[p+1], "%d", &result);
	}
	
	return result;
}

void processArgs (int argc, char *argv[])
{
	int i;
	
	if (argc < 2 || strEqual (argv[1], "") || strEqual (argv[1],"-") )
	{
		inFile = stdin;
		fprintf (outFile, "c Processing standard input\n");
		filename = "standard input";
	}
	else
	{
		filename = argv[1];
		inFile = fopen (filename, "r");
		if (inFile == NULL)
		{
			fprintf (outFile, "c Could not open <%s> for reading\n", filename);
			inFile = stdin;
			fprintf (outFile, "c Processing standard input\n");
			fprintf (stderr, "ce Processing standard input\n");
			filename = "standard input";
		}
		else
		{
			fprintf (outFile, "c Processing file <%s>\n", filename);
		}
	}
	
	turnsLimit = getIntOption (argc, argv, "--turns", 400);
	traceLevel = getIntOption (argc, argv, "--trace", competitionTrace);
	elapsedLimit = getIntOption (argc, argv, "--elapsed", -1);
	memoryLimit = getIntOption (argc, argv, "--memory", -1);
	noReduce = getIntOption (argc, argv, "--noreduce", 0);
	if (elapsedLimit > 0)
		fprintf (outFile, "c Elapsed time limit of %d seconds\n", elapsedLimit);
	if (memoryLimit > 0)
		fprintf (outFile, "c Mmory limit of %dMB\n", memoryLimit);
}



void nextCh()
{
	ch = fgetc(inFile);
}

void accept (char *s)
{
	for (int i=0; i<strlen(s); i++)
	{
		if (ch == s[i])
			nextCh();
		else
		{
			fprintf (outFile, "c Could not find string <%s>\n", s);
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
		free (clause->lits);
	free (clause);
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
	fprintf (outFile, "c Initially %d variables and %d clauses\n", originalNumVars, originalNumClauses);
	if ( (traceLevel & competitionTrace) > 0) { fprintf (stderr, "ce Initially %d variables and %d clauses\n", originalNumVars, originalNumClauses);fflush(stderr);}

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
	

	fprintf (outFile, "c Now %d variables and %d clauses\n", numVars, numClauses);
	

	if ((traceLevel & fullClausesTrace))
	{
		fprintf (stderr, "ce Initially %d variables and %d clauses\n", originalNumVars, originalNumClauses);
		fprintf (stderr, "ce Now %d variables and %d clauses\n", numVars, numClauses);
		for (c=0; c<numClauses; c++)
		{
			fprintClause (stderr, clauses[c]);
			fprintf (stderr, "\n");
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
			fprintf (outFile, "c removed %d duplicate clauses, number now %d\n", numClauses-newNumClauses, newNumClauses);
			numClauses = newNumClauses;
		}
		
	
	}


	free (litsBuffer);

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
	free (varToClause);

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
	
	fprintf (outFile, "c Number of unit clauses = %d\n", writePos);
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
		isUsed[v] = false;
	for (c=0; c<numClauses;c++)
	{
		clause = clauses[c];
		if (!clause->redundant)
		{
			for (v=0; v<clause->length; v++)
				isUsed[abs(clause->lits[v])] = true;
		}
	}
	unusedVariables = 0;
	for (v=1;v<=numVars;v++)
		if (!isUsed[v])
			unusedVariables++;
		
		
	unusedVariables -= numUnitLits;
	
	mapVariables = checkMalloc ((1+numVars)*sizeof(int),"mapvariables");
	
	newNumVars =  numVars - (unusedVariables + numUnitLits);

	if (unusedVariables > 0)
		fprintf (outFile, "c Number of unused variables = %d\n", unusedVariables);
	
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
	
	free (isUsed);
	free (isUnitLit);
	free (unitLits);
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

void sortSubProblems()
{
	int *isUsed, *varsUsed;
	int readPos, writePos, v, lit, var, thisVar, countVars, regionsCount;
	ClausePtr clause;
	
	if (numVars == 0) return;
		
	
	isUsed = checkMalloc ((1+numVars)*sizeof(int),"isused");
	varsUsed = checkMalloc ((1+numVars)*sizeof(int),"varsused");

	for (v=1;v<=numVars; v++)
		isUsed[v] = false;
	
	isUsed[1] = true;
	varsUsed[0] = 1;
	readPos = 0;
	writePos = 1;
	countVars = 0;
	regionsCount = 0;
	
	setUpVarToClause();
	
	while (countVars < numVars)
	{
	
		while (writePos > readPos)
		{
			thisVar = varsUsed[readPos++];
			countVars++;
			mapVariables[thisVar] = countVars;
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
		regionsCount++;
		
		if (countVars < numVars)
		{
			for (v=1; isUsed[v]; v++);
			isUsed[v] = true;
			varsUsed[writePos++] = v;
		}
	}
	
	if (regionsCount > 1)
	{
		fprintf (outFile, "c %d independent regions found\n", regionsCount);
		if (traceLevel > 0)
			fprintf (stderr, "ce %d independent regions found\n", regionsCount);
	}
	
	remapClauses();
	
	freeVarToClause();
	free (isUsed);
	free (varsUsed);
}

double fabs(double x)
{
	return (x<0)?-x:x;
}

void sortVarsAndClauses()
{
	int turn, v, c, lit, var,i,j,p;
	int minVar, maxVar;
	Variable *variables;
	ClausePtr clause,clause1;
	
	
	double weight, increment;
	int maxDifference;
	

	
	variables = checkMalloc ( (1+numVars)*sizeof(Variable), "variables");

	for (v=1; v<=numVars; v++)
	{
		variables[v].var = v;
		variables[v].count = 0;
		variables[v].weight = v;
		mapVariables[v] = v;
	}


	turnsLimit = turnsLimit*numVars;
	if ( ((double)turnsLimit)*(numVars+numClauses) > 1e09)
		turnsLimit =1e09/ (numVars+numClauses);
	fprintf (outFile, "c %d turns\n", turnsLimit);
	if ((traceLevel & competitionTrace)) {fprintf (outFile, "c %d turns\n", turnsLimit); fflush(stderr);}

	increment = 10*numVars*numClauses;
	do
	{
		increment *= 0.999;
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
		
		maxDifference = 0;

		for (v=1; v<=numVars; v++)
		{
			//printf ("%d %.2f %d\n", v, variables[v].weight, variables[v].var);
			//if (abs(mapVariables[variables[v].var] - v) > maxDifference)
			//	maxDifference = abs(mapVariables[variables[v].var] - v);
			mapVariables[variables[v].var] = v;
			variables[v].weight = v;
		}
		//printf ("---------------------------\n");
		
		//printf ("x %d\n", maxDifference);
		
	} while (increment > 0.1);
	

	remapClauses();

	for (c=0;c<numClauses;c++)
	{
		clause = clauses[c];
		qsort (clause->lits, clause->length, sizeof(int), litCompare);
	}


	qsort (clauses, numClauses, sizeof (ClausePtr), clauseCompare);
	
	fprintf (outFile, "c turns finished\n");
	if ((traceLevel & competitionTrace) > 0) { fprintf (stderr, "ce turns finished\n"); fflush(stderr);}

	
	free (mapVariables);
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
	else
	{
		mpz_set_ui (result->contribution, 0);
		mpz_set_ui (result->previousContribution, 0);

		result->length = 0;
		result->savedSize = 0;
		result->posAdded = -1;
	}
	
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
	
	bpos += __builtin_ctzll(l);
	if (bpos < wordLength)
	{
		result = bpos + (lpos+unusedWords)*wordLength;
		if (result == 128)
		{
			lpos = 1;
		}
		return result;
	}
	lpos++;
	while (lpos < bs->length && bs->bits[lpos] == 0x0) lpos++;
	if (lpos >= bs->length) return -1;
	l = bs->bits[lpos];
	bpos = __builtin_ctzll(l);
	result = bpos + (lpos+unusedWords)*wordLength;
		if (result == 128)
		{
			lpos = 1;
		}
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
	fprintf (f, ">");
	
}

uint64_t primes[] = {961748941,941083987,920419823,899809363,879190841,858599509,838041647,817504253,
	797003437,776531419,756065179,735632797,694847539,654188429,633910111};
#define PRIMES_COUNT 15

BitSetPtr bitSetGetUnique (BitSetPtr bs)
{
	BitSetPtr result;
	int v,b;
	b =  bitSetNextSetBit (bs, 0);
	if (b == -1) return emptyBitSet;
	v = b/2;
	bs->hashCode = bitSetHashCode(bs);
	result = hashTableSearchInsert (bitSetTable[v], bs);
	if (result == NULL)
	{
		result = bs;
		result->savedSize = bitSetCardinality(result);
	}
	
	
	return result;
}



unsigned int bitSetHashCode (BitSetPtr bs)
{
	int p, start, end;
	uint64_t result;
	unsigned int intResult;
	for (start=0;start<bs->length && bs->bits[start]==0;start++);
	for (end=bs->length-1;end>0&&bs->bits[end] == 0; end--);
	if (start > end) return 0;
	result = bs->bits[0]>>16;
	for (p=start; p<=end && p<PRIMES_COUNT+start; p++)
		result ^= bs->bits[p]*primes[p-start] ;
	
	
	
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

void bitSetFree (BitSetPtr bs)
{
	//mpz_clear (bs->contribution);
	//mpz_clear (bs->previousContribution);
	//if (bs->bits != NULL)
	//	free (bs->bits);
	addToBlockList (stackOfBitSetPtrs, bs);
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
	
	stackOfBitSetPtrs = newBlockList (100);
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
}

void bitSetSetNegativeContribution (BitSetPtr bp, mpz_t c, int size)
{

	mpz_tdiv_q_2exp (bp->contribution, c, size);
	mpz_neg (bp->contribution, bp->contribution);

}


void bitSetAddNegativeContribution (BitSetPtr bp, mpz_t c, int size)
{
	mpz_tdiv_q_2exp (temp_mpz1, c, size);
	//fprintf (stderr, "subtracting "); mpz_out_str(stderr, 10,temp_mpz1); fprintf(stderr,"\n");
	mpz_sub (bp->contribution, bp->contribution, temp_mpz1);
}

int bitSetIntersects (BitSetPtr bs1, BitSetPtr bs2)
{
	int limit,result,p;
	limit = (bs1->length>bs2->length)?bs2->length:bs1->length;
	result = false;
	for (p=0; p<limit && !result; p++)
		result = (bs1->bits[p] & bs2->bits[p]) != 0;
	return result;
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
	}
	else
	{
		
		bs->length = 0;
		bs->capacity = 0;
		free (bs->bits);
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
	int progress = (int) ( scale * ( (1.0*value) / max) );
	fprintf (stderr, "ce %s ", label);
	for (i=0; i<10-strlen(label); i++) fprintf(stderr, " ");
	for (i=0; i<progress; i++) fprintf (stderr,"*");
	for (i=progress; i<scale; i++) fprintf (stderr,".");
	fprintf (stderr,"\n");
}

void printProgress()
{
	int i;
	time_t timeNow;
	double timeUsed;
	struct mallinfo mi;
	
	if ((traceLevel & competitionTrace) > 0)
	{
		time (&timeNow);
		fprintf(stderr, "ce time %.0f(s) pos %d ", difftime(timeNow,startTime),pos);
		fprintClause(stderr, clauses[pos]);
		fprintf (stderr, " nodes %d\n", blockListSize(clauseSet));
	}
	else
	{
		time (&timeNow);
		timeUsed = difftime(timeNow, startTime);
		fprintf(stderr, "\nc processing <%s>\n", filename);
		fprintf(stderr, "ce elapsed time %.0f ", timeUsed);
		if (elapsedLimit > 0) fprintf (stderr, "(limit %d) ", elapsedLimit);
		fprintf (stderr, "seconds\n");
		if (pos > 0)
		{
			fprintf(stderr, "ce %d nodes\n", blockListSize (clauseSet));
			fprintf(stderr, "ce clause number %d ", pos);
			fprintClause (stderr,clauses[pos]);
			fprintf (stderr,"\n");
			processBar ("clauses", pos, numClauses);
		}
		if (elapsedLimit > 0)
			processBar ("time", (int) timeUsed, elapsedLimit);
		mi = mallinfo();
		fprintf (stderr, "ce allocated space %dMB\n", mi.uordblks/(1024*1024));
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
	free (firstvb);
	free (lastvb);
	free (firstc);
	free (lastc);
	
/*
	for (int c=0; c<numClauses; c++)
	{
		printf ("c %d\n",c);
		for (v=0; firstVars[c][v] != 0; v++) printf ("%d ", firstVars[c][v]);
		printf("\n");
		for (v=0; lastVars[c][v] != 0; v++) printf ("%d ", lastVars[c][v]);
		printf("\n");
	}
	*/
	
	
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
		free (tn);
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
			if (other->pos > pos && bitSetIntersects (thisBitSet, other->bitSet) && !bitSetIntersects (negBitSet, other->bitSet) && other->posAdded < pos)
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
}

void checkMemory()
{
	struct mallinfo mi;
	int megaBytes;
	
	if (memoryLimit > 0)
	{
		mi = mallinfo();
		megaBytes = mi.uordblks/(1024*1024);
		if (megaBytes > memoryLimit)
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
						bitSetFree (bs);
						num++;
					}
					bs = next;
				}
			}
		}
	}
}

void buildLists()
{
	BlockListPtr tempClauseSet, blockList1, blockList2;
	BitSetPtr fullNextClause;
	int areLastVars, c, v,fullNextClauseLits, extraLits;
	BitSetPtr thisBitSet, otherBitSet, reducedBitSet, negBitSet, nextBitSet;
	ClausePtr thisClause;
	TreeNodePtr thisTree;
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
		
		numFirstVars = intListSize (firstVars[pos]);
		
/*
		startScanBlockList (clauseSet);
		while (hasNextBlockList (clauseSet))
		{
			bitSetNextContribution (( BitSetPtr) getNextBlockList(clauseSet), numFirstVars);
		}
*/
		mapBlockList (clauseSet, bitSetNextContribution);
		
		areLastVars = lastVars[pos][0] > 0;
		
		
		if (areLastVars)
		{
			bitSetNoteVarsToRemove (lastVars[pos]);
			startScanBlockList (clauseSet);
			while (hasNextBlockList (clauseSet))
			{
				thisBitSet = (BitSetPtr) getNextBlockList(clauseSet);
				if (mpz_sgn(thisBitSet->previousContribution) != 0)
				{
					reducedBitSet = getReducedBitSet (thisBitSet);
					//fprintf (stderr,"reduced "); fprintBitSet (stderr, thisBitSet); fprintBitSet (stderr, reducedBitSet); fprintf (stderr,"\n");
					if (reducedBitSet != thisBitSet)
					{
						bitSetAddContribution (reducedBitSet, thisBitSet->contribution);
					}
					//fprintf (stderr,"reduced "); fprintBitSet (stderr, thisBitSet); fprintBitSet (stderr, reducedBitSet); fprintf (stderr,"\n");
					if (reducedBitSet->posAdded < pos)
					{
						addToBlockList (nextClauseSet, reducedBitSet);
						reducedBitSet->posAdded = pos;
					}
				}
			}
		}
		else
		{
			if (firstVars[pos][0] == 0)
			{
				nextClauseSet = clauseSet;
			}
			else
			{
				startScanBlockList (clauseSet);
				while (hasNextBlockList (clauseSet))
				{
					thisBitSet = (BitSetPtr) getNextBlockList(clauseSet);
					if (mpz_sgn(thisBitSet->previousContribution) != 0)
					{
						addToBlockList (nextClauseSet, thisBitSet);
						thisBitSet->posAdded = pos;
					}
				}
			}
		}

		if ((traceLevel & fullClausesTrace) > 0)
		{
			fprintf (stderr, "\n--------------------\n");
			startScanBlockList (clauseSet);
			while (hasNextBlockList (clauseSet))
			{
				thisBitSet = (BitSetPtr) getNextBlockList(clauseSet);
				fprintBitSet (outFile, thisBitSet);
				fprintf (outFile, "\n");
			}
			fprintf (stderr, "--------------------\n\n");
		}
		
		thisClause = clauses[pos];
		thisBitSet = thisClause->bitSet;
		bitSetMakeNegBitSet (negBitSet, thisBitSet);
		thisTree = getTreeNode (pos, thisBitSet, negBitSet);
		
		startScanBlockList (clauseSet);
		while (hasNextBlockList (clauseSet))
		{

			if (checkCount++ > 100000)
			{
				checkElapsed();
				checkMemory();
				checkCount = 0;
			}

			otherBitSet = (BitSetPtr) getNextBlockList(clauseSet);
			if (mpz_sgn(otherBitSet->previousContribution) != 0)
			{
				//fprintf (stderr,"B\n");
				if (!bitSetIntersects(otherBitSet, negBitSet))
				{
					bitSetCopyOr (fullNextClause, thisBitSet, otherBitSet);
					//fprintf (stderr, "fullnextclause "); fprintBitSet (stderr, fullNextClause); fprintf (stderr,"\n");
					fullNextClauseLits = bitSetCardinality (fullNextClause);
					//fprintf (stderr, "count %d\n", fullNextClauseLits);
					if (areLastVars)
						bitSetRemoveVarSet (fullNextClause);
					//fprintf (stderr,"C\n");
					if (!treeContainsSubsetOf (thisTree, fullNextClause))
					{
/*
						if (bitSetEqual(otherBitSet, fullNextClause))
							nextBitSet = otherBitSet;
						else
*/
						{
							nextBitSet = bitSetGetUnique(fullNextClause);
							if (nextBitSet == fullNextClause)
								fullNextClause = newBitSet();
						}
						extraLits = fullNextClauseLits - otherBitSet->savedSize;
						if (nextBitSet->posAdded == pos)
						{
							//fprintf (stderr,"D %d %d %d\n", fullNextClauseLits, otherBitSet->savedSize,extraLits);
							//fprintf (stderr,"next "); fprintBitSet (stderr,nextBitSet); fprintBitSet (stderr,otherBitSet); fprintf(stderr,"\n");
							bitSetAddNegativeContribution (nextBitSet, otherBitSet->previousContribution, extraLits);
							//fprintf (stderr,"next1 "); fprintBitSet (stderr,nextBitSet); fprintf(stderr,"\n");
						}
						else
						{
							//fprintf (stderr,"E\n");
							bitSetSetNegativeContribution(nextBitSet, otherBitSet->previousContribution, extraLits);
							addToBlockList(nextClauseSet, nextBitSet);
							nextBitSet->posAdded = pos;
						}
					}
				}
			}
		}


		
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

int main(int argc, char *argv[])
{
	int c;
	

	time (&startTime);
	outFile = stdout;
	
	struct sigaction action;
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

		fprintf (outFile, "c Now %d variables and %d clauses\n", numVars, numClauses);
		
		sortSubProblems();
		
		sortVarsAndClauses();
	}
	
	initTrees();
	
	initBitSets();
	
	buildLists();
	
	printFinal (STATUS_SUCCESSFUL);
	
	
/*
	for (c=0; c<numClauses; c++)
	{
		fprintClause (stderr, clauses[c]);
		fprintf (stderr, "\n");
	}
*/
	return 0;
}