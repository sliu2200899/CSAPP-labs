/*                                                                            *
 *  cache.c                                                                   *
 *  this file is used for providing cache for web proxy  . :)                 *
 *              Name: Shu Liu   AndrewID: Shul2                               *
 *  our cache system is constructured as a double-ended doubly linked list    *
 *  and we can search, remove, addlast and delete node                        *
 *                                                                            *
 */
#include "cache.h"
#include "strings.h"
#include "stdbool.h"

// double-ended doubly linked list
cache_node *tail;
cache_node *head;

size_t cache_actual_size;

// shared control resources
int readcnt;  // initialized as 0
sem_t mutex, w;   // initialized as 1

/*
 * cache_search : search for the matched cache block
 */
cache_node *cache_search(char *host, char *path, char *port)
{
    cache_node *cur = tail;
    while (cur != NULL) {

      if ((strcasecmp(cur->cache_key.host, host) == 0)
          && (strcasecmp(cur->cache_key.path, path) == 0)
          && (strcasecmp(cur->cache_key.port, port) == 0)) {
            printf("found it!\n");
            return cur;
      }

      cur = cur->prev;
    }
    // not found
    printf("no found!\n");
    return NULL;
}

/*
 * cache_init : initialize the cache system
 */

void cache_init()
{
  // initialize the mutex and write
  Sem_init(&mutex, 0 , 1);
  Sem_init(&w, 0, 1);

  tail = NULL;
  head = NULL;

  cache_actual_size = 0;

}

/*
 * cache_removefromlist : remove some node from list temporally,
 * afterward, the node would add to the last of the list
 */
void cache_removefromlist(cache_node *pnode)
{
    cache_node *cur = NULL;
    if (head == tail && head != NULL) {
        head = NULL;
        tail = NULL;
    } else if (pnode->prev == NULL) {
        cur = head->next;
        cur->prev = NULL;
        head = cur;
    } else if (pnode->next == NULL) {
        cur = tail->prev;
        cur->next = NULL;
        tail = cur;
    } else {
        cur = pnode->next;
        cache_node *nprev = pnode->prev;
        nprev->next = cur;
        cur->prev = nprev;
    }
    cache_actual_size -= pnode->size;
}

/*
 * cache_addlast : add the current node to the last of the list
 */
void cache_addlast(cache_node *pnode)
{
    if (tail == head && head == NULL) {
        head = pnode;
        tail = pnode;
        pnode->next = NULL;
        pnode->prev = NULL;
    } else {
        cache_node *curtail = tail;
        curtail->next = pnode;
        pnode->prev = curtail;
        pnode->next = NULL;
        tail = pnode;
    }
    cache_actual_size += pnode->size;
}

// cache_deletefirst : remove node and include freeing the memory
void cache_deletefirst()
{
    cache_node *cur = head;
    cache_node *next = NULL;
    if (tail == NULL) {
      printf("no cache node!");
      return;
    }
    if (head == tail) {
        head = NULL;
        tail = NULL;
    } else {
        next = cur->next;
        next->prev = NULL;
        head = next;
    }
    cache_actual_size -= cur->size;
    if (cur->cache_key.host != NULL) {
      Free(cur->cache_key.host);
    }
    if (cur->cache_key.path != NULL) {
      Free(cur->cache_key.path);
    }
    if (cur->cache_key.port != NULL) {
      Free(cur->cache_key.port);
    }
    if (cur->web_object != NULL) {
      Free(cur->web_object);
    }
    if (cur != NULL) {
      Free(cur);
    }
}

/*
 * cache_block_create : allocate memory for a cache block and
 * store web_content.
 */
 cache_node *cache_block_create(char *host, char *path, char *port,
                       char *web_content, size_t size)
 {
     cache_node *node = (cache_node *)Malloc(sizeof(cache_node));
     // create web cache key part
     node->cache_key.host = (char *)Malloc(sizeof(strlen(host) + 1));
     strncpy(node->cache_key.host, host, strlen(host));
     node->cache_key.path = (char *)Malloc(sizeof(strlen(path) + 1));
     strncpy(node->cache_key.path, path, strlen(path));
     node->cache_key.port = (char *)Malloc(sizeof(strlen(port) + 1));
     strncpy(node->cache_key.port, port, strlen(port));

     // create web content part
     node->web_object = (char *)Malloc(size + 1);
     strncpy(node->web_object, web_content, size);

     node->size = size;

     return node;
 }
