/********************************************************
* csim.c -- program of cache simulator                 *
*                                                      *
* Author:  Shu, Liu                                    *
* AndrewID: shul2                                      *
*                                                      *
* Purpose:  simulate a cache system with LRU policy    *
*                                                      *
* Usage:                                               *
*       takes a memory trace as input, simulates the   *
*       hit/miss behavior of a cache memory on this    *
*       trace, and outputs the total number of hits,   *
*       misses, and evictions.                         *
********************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <getopt.h>
#include <string.h>
#include "cachelab.h"

#define EXIT_SUCCESS 0 /* exit program successfuly*/
#define EXIT_FAILURE 1 /* exit program abnormally*/

#define MISS            0 /* MISS */
#define HIT             1 /* HIT */
#define MISS_EVICTION   2 /* EVICTION */

#define ADDRESS_BIT   64 /*number of physical address bits*/ 

int blockbitsize = 0;  /* b block field bit size*/
int tagbitsize = 0;    /* t tag field bit size*/
int setbitsize = 0;    /* s set field bit size*/
int linesize = 0;      /* e number of lines each set*/
int setsize = 0;       /* S number of set */

typedef enum {false, true} bool;

typedef struct LinkNode{
  bool valid;
  long long tag;
  struct LinkNode * next;
  struct LinkNode * prev;
} node;

typedef struct{
  int capacity;
  int size;
  node *head;
  node *tail;
} LinkPoint;

/*
  search_linked_list: used for traverse all the lines stored in a set
*/
node *search_linked_list(int setval, unsigned long tagval, LinkPoint *point) {

  int count = 0, i = 0;
  LinkPoint *linkhead = point + setval;

  node *cur = linkhead->head->next;
  linkhead->tail->valid = false;
  linkhead->head->valid = false;

  count = linkhead->size;
  while (i != count && cur != NULL) {
    if (cur->valid && cur->tag == tagval) {
      return cur;
    }
    cur = cur->next;
    i++;
  }
  return NULL;
}

/*
  move_to_tail: used to put the current node to the end of the linklist
*/
void move_to_tail(LinkPoint *phead, node *pnode) {
  pnode->prev = phead->tail->prev;
  pnode->next = phead->tail;
  pnode->prev->next = pnode;
  phead->tail->prev = pnode;
}


/*
  load_data: want to read a data
*/
int load_data(LinkPoint *pbuf, unsigned long addr) {
  node *pnode = NULL;
  int sval = 0;
  unsigned long tval = 0;

  // set value
  sval = (addr >> blockbitsize) & (~((~0) << setbitsize));    // range 0 ~ 15
  // tag value
  tval = (addr >> (setbitsize + blockbitsize)) & (~((~0) << tagbitsize));   // range 0 ~ 15

  pnode = search_linked_list(sval, tval, pbuf);
  if (pnode != NULL) {
    // when find the specific node

    // remove the current element
    pnode->prev->next = pnode->next;
    pnode->next->prev = pnode->prev;

    // add the element to the tail, indicating this is the most recent element
    move_to_tail(pbuf+sval, pnode);

    return HIT;

  } else {
    // when not find element

    // create a new node and initialize it
    pnode = (node *)malloc(sizeof(node));
    memset(pnode, 0, sizeof(node));
    pnode->tag = tval;
    pnode->valid = true;

    if ((pbuf+sval)->size < (pbuf+sval)->capacity) {
      // cache amout is not full
      move_to_tail(pbuf+sval, pnode);
      (pbuf+sval)->size += 1;

      return MISS;

    } else {
      // cache amout is full
      // delete the earliest one
      LinkPoint *point = pbuf + sval;

      // remove the lease recent element
      point->head->next = point->head->next->next;
      point->head->next->prev = point->head;

      // put the current node to the tail of list
      move_to_tail(pbuf+sval, pnode);

      return MISS_EVICTION;
    }
  }

  return MISS_EVICTION;
}

/*
  process_info: process the input data

*/
int process_info(char *fname, LinkPoint *pbuf, int *phit, int *pmiss, int *pevic) {
  int r;
  FILE *fptr;
  fptr = fopen(fname, "r");
  char opr;
  unsigned long addr = 0;
  int size = 0;

  if (fptr == NULL) {
    printf("Error! file is empty.");
    goto END;
  }

  while (1) {

    r = fscanf(fptr, " %c %lx,%i\n", &opr, &addr, &size);
    if (r == EOF) {
      break;
    }

    int resulttype = -1;

    if (opr == 'L') {
      resulttype = load_data(pbuf, addr);
    } else if (opr == 'S') {
      resulttype = load_data(pbuf, addr);
    } else {
      printf("operation code wrong!");
      goto END;
    }

    switch (resulttype) {
      case MISS:
        (*pmiss)++;
        break;

      case HIT:
        (*phit)++;
        break;

      case MISS_EVICTION:
        (*pevic)++;
        (*pmiss)++;
        break;

      default:
        printf("program is wrong!\n");
    }
  }

  fclose(fptr);
  return EXIT_SUCCESS;

END:
  if (fptr != NULL) {
    fclose(fptr);
  }
  return EXIT_FAILURE;
}

/*
  free_buffer: used for cleaning buffer
*/
void free_buffer(LinkPoint *pbuf) {
  int i = 0;
  LinkPoint *phead = NULL;
  if (pbuf != NULL) {
    phead = NULL;
    for (i = 0; i < setsize; i++) {
      phead = pbuf + i;
      if (phead->head != NULL) {
        free(phead->head);
      }
      if (phead->tail != NULL) {
        free(phead->tail);
      }
    }
    free(pbuf);
  }
}

/*
  cache_process: including the cache creation & initialization, cache process
                and buffer cleaning.
*/
int cache_process(char *fname, int *pnumhit, int *pnummiss, int *pnumevic) {

  int i = 0, ret = 0;
  LinkPoint *pbuf = NULL;

  // construct cache
  pbuf = (LinkPoint *) malloc(sizeof(LinkPoint) * setsize);
  if (pbuf == NULL) {
    goto END;
  }
  memset(pbuf, 0, sizeof(LinkPoint) * setsize);
  LinkPoint *cur = pbuf;
  for (i = 0; i < setsize; i++) {
    cur->capacity = linesize;
    cur->size = 0;
    cur->head = (node *) malloc(sizeof(node));
    cur->tail = (node *) malloc(sizeof(node));
    if (cur->head == NULL || cur->tail == NULL) {
      goto END;
    }
    memset(cur->head, 0, sizeof(node));
    memset(cur->tail, 0, sizeof(node));

    cur->tail->prev = cur->head;
    cur->head->next = cur->tail;

    cur++;
  }

  /*
    process info
  */
  ret = process_info(fname, pbuf, pnumhit, pnummiss, pnumevic);
  if (ret != EXIT_SUCCESS) {
    goto END;
  }

  // free buffer
  free_buffer(pbuf);
  return EXIT_SUCCESS;

END:
  free_buffer(pbuf);
  return EXIT_FAILURE;
}

int main(int argc, char* argv[]) {

    int sflag = 0, eflag = 0, bflag = 0;

    int setindexbit = 0; /* -s number of set index bits */
    int linesperset = 0; /* -E Associativity: number of lines per set */
    int blockbits = 0;   /* -b number of block bits*/
    char *fname = "default_name";
    char opt;
    int ret;
    int numhit = 0, nummiss = 0, numevic = 0;

    /*
       fetch the parameter
    */
    while ((opt = getopt(argc, argv, "hvs:E:b:t:")) != -1) {
       switch (opt) {
       case 'h':
           //usageinfo_flag = 1;
           break;
       case 'v':
           //verbose_flag = 1;
           break;
       case 's':
           sflag = 1;
           setindexbit = atoi(optarg);
           break;
       case 'E':
           eflag = 1;
           linesperset = atoi(optarg);
           break;
       case 'b':
           bflag = 1;
           blockbits = atoi(optarg);
           break;
       case 't':
           fname = optarg;
           break;
       default: /* '?' */
           fprintf(stderr, "Usage: %s [-t nsecs] [-n] name\n",
                   argv[0]);
           exit(EXIT_FAILURE);
       }
    }

    /*
      check the parameter
    */
    if (optind > argc) {
        fprintf(stderr, "Expected argument after options\n");
        return EXIT_FAILURE;
     }

     if (!sflag) {
       fprintf(stderr, "Need to set number of set index bits options\n");
       return EXIT_FAILURE;
     }

     if (!eflag) {
       fprintf(stderr, "Need to set number of lines per set\n");
       return EXIT_FAILURE;
     }

     if (!bflag) {
       fprintf(stderr, "Need to set number of block bits\n");
       return EXIT_FAILURE;
     }

     if (strcmp(fname, "default_name") == 0) {
       fprintf(stderr, "Need to set the file name\n");
       return EXIT_FAILURE;
     }

    /*
      set some global variables
    */
    setbitsize = setindexbit; /* -s number of set index bits */
    setsize = 1 << setbitsize;    /* -S  number of sets in total */
    tagbitsize = 64 - (setindexbit + blockbits); /* -E Associativity: number of lines per set */
    blockbitsize = blockbits;   /* -b number of block bits*/
    linesize = linesperset;

    /*
       cache process
    */

    ret = cache_process(fname, &numhit, &nummiss, &numevic);
    if (ret != EXIT_SUCCESS) {
      goto END;
    }

    //printf("number of hit is %d, number of miss is %d, number of evic is %d\n",
        //numhit, nummiss, numevic);

    printSummary(numhit, nummiss, numevic);

    return EXIT_SUCCESS;
END:
    // do something before exit
    return EXIT_FAILURE;
}
