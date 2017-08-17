/*                                                                            *
 *  cache.h                                                                   *
 *  this file is head file for cache.c  :)                                    *
 *              Name: Shu Liu   AndrewID: Shul2                               *
 *  this file defines MAX_CACHE_SIZE, MAX_OBJECT_SIZE, cache node structure   *
 *  and extern some global variables from cache.c                             *
 *                                                                            *
 */
#ifndef CACHE_H
#define CACHE_H

#include "csapp.h"

/* Recommended max cache and object sizes */
#define MAX_CACHE_SIZE 1049000
#define MAX_OBJECT_SIZE 102400

/* we key structure */
typedef struct web_key{
    char *host;
    char *path;
    char *port;
}web_key_t;

/* cache node structure */
typedef struct c_node{
    web_key_t cache_key;
    char *web_object;
    struct c_node *next;
    struct c_node *prev;
    size_t size;
}cache_node;

// global variables
extern int readcnt;  // initialized as 0
extern sem_t mutex, w;   // initialized as 1
extern cache_node *head;  // the head of the cache list
extern cache_node *tail;  // the tail of the cache list
extern size_t cache_actual_size;

// cache out functions that users can access
void cache_init();
cache_node *cache_search(char *host, char *path, char *port);
void cache_removefromlist(cache_node *pnode);
void cache_addlast(cache_node *pnode);
void cache_deletefirst();
cache_node *cache_block_create(char *host, char *path, char *port,
                      char *web_content, size_t size);

#endif
