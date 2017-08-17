/*                                                                            *
 *  proxy.c                                                                   *
 *  this file create one simple web proxy  . :)                               *
 *              Name: Shu Liu   AndrewID: Shul2                               *
 *  our web proxy is constructured as a multithreaded and cached-based proxy  *
 *  this proxy can only deal with get request.                                *
 *                                                                            *
 */

#include "csapp.h"
#include <strings.h>
#include <stdbool.h>
#include "cache.h"

#define HOSTLEN 256
#define SERVLEN 8

static const char *header_user_agent = "Mozilla/5.0"
                                    " (X11; Linux x86_64; rv:45.0)"
                                    " Gecko/20100101 Firefox/45.0";

/* Information about a connected client. */
typedef struct {
    struct sockaddr_in addr;    // Socket address
    socklen_t addrlen;          // Socket address length
    int connfd;                 // Client connection file descriptor
    char host[HOSTLEN];         // Client host
    char serv[SERVLEN];         // Client service (port)
} client_info;

/* URI parsing results. */
typedef enum {
    PARSE_ERROR,
    PARSE_SUCCESS
} parse_result;

/* process results. */
typedef enum {
    PROCESS_ERROR,
    SEND_SUCCESS,
    RECEIVE_SUCCESS
} process_result;

void serve(client_info *client, int connfd);
char content_buffer[MAX_OBJECT_SIZE];

/*
 * parse_uri - parse URI into filename and CGI args
 *
 * uri - The buffer containing URI. Must contain a NUL-terminated string.
 * phost - The buffer into which the filename will be placed.
 * ppath - The buffer into which the CGI args will be placed.
 * pport - The buffer into which the port number will be placed.
 * NOTE: All buffers must hold MAXLINE bytes, and will contain
 * NUL-terminated strings after parsing.
 *
 * Returns the appropriate parse result for the type of request.
 */
parse_result parse_uri(char *uri, char *phost, char *ppath, char *pport) {

    // sanity check
    if (uri == NULL || phost == NULL || ppath == NULL || pport == NULL) {
      printf("parse uri error!\n");
      return PARSE_ERROR;
    }

    // fetch the host name from uri
    // bool res = checkstartwith(uri, "http://");
    if (strncasecmp(uri, "http://", 7) != 0) {
      printf("host name error!\n");
      return PARSE_ERROR;
    }

    char *curindex = uri + 7;
    char *endindex;
    if ((endindex = strpbrk(curindex, " :/\r\n\0")) == NULL) {
      printf("host name parse error!\n");
      return PARSE_ERROR;
    }
    printf("in parse uri, the curindex is %s, endindex is %s\n",
              curindex, endindex);
    strncpy(phost, curindex, endindex - curindex);
    phost[endindex - curindex] = '\0';
    printf("int parse uri, phost is %s\n", phost);

    // fetch the port from uri
    // char portStr[MAXLINE];
    if (*endindex == ':') {
        //portStr = strcpy(portStr, endindex + 1);
        char *portCur = endindex + 1;
        while (*portCur >= '0' && *portCur <= '9') {
            *pport = *portCur;
            pport++;
            portCur++;
        }
        printf("port is %s\n", pport);
    } else {
        strcpy(pport, "80");  // default port number
        //*pport = 80;
    }

    // get the path from uri
    char *pathbegin;
    char pathStr[MAXLINE];
    if ((pathbegin = strchr(curindex, '/')) == NULL) {
        // find the empty directory
        pathStr[0] = '\0';
    } else {
        // find the directory
	      pathbegin++;
	      strcpy(pathStr, pathbegin);
        printf("pathStr is %s\n", pathStr);
    }

    ppath[0] = '/';
    strcpy(ppath+1, pathStr);
    printf("ppath is %s\n", ppath);

    return PARSE_SUCCESS;
}


/*
 * clienterror - returns an error message to the client,
 * reference by tiny.c
 */
void clienterror(int fd, char *cause, char *errnum,
        char *shortmsg, char *longmsg) {
    char buf[MAXLINE];
    char body[MAXBUF];
    size_t buflen;
    size_t bodylen;

    /* Build the HTTP response body */
    bodylen = snprintf(body, MAXBUF,
            "<!DOCTYPE html>\r\n" \
            "<html>\r\n" \
            "<head><title>Tiny Error</title></head>\r\n" \
            "<body bgcolor=\"ffffff\">\r\n" \
            "<h1>%s: %s</h1>\r\n" \
            "<p>%s: %s</p>\r\n" \
            "<hr /><em>The Tiny Web server</em>\r\n" \
            "</body></html>\r\n", \
            errnum, shortmsg, longmsg, cause);
    if (bodylen >= MAXBUF) {
        return; // Overflow!
    }

    /* Build the HTTP response headers */
    buflen = snprintf(buf, MAXLINE,
            "HTTP/1.0 %s %s\r\n" \
            "Content-Type: text/html\r\n" \
            "Content-Length: %zu\r\n\r\n", \
            errnum, shortmsg, bodylen);
    if (buflen >= MAXLINE) {
        return; // Overflow!
    }

    /* Write the headers */
    if (rio_writen(fd, buf, buflen) < 0) {
        fprintf(stderr, "Error writing error response headers to client\n");
        return;
    }

    /* Write the body */
    if (rio_writen(fd, body, bodylen) < 0) {
        fprintf(stderr, "Error writing error response body to client\n");
        return;
    }
}


/*
 * send_request: send http request to the web server, should create client file
 * descriptor first, and initialized afterward
 */
process_result send_request(int *pclientfd, rio_t *prioclient, rio_t *prio,
                char *host, char *port, char *method, char *path)
{
  int clientfd = 0;
  // Open socket connection to server
  if ((clientfd = open_clientfd(host, port)) < 0) {
      fprintf(stderr, "Error connecting to %s:%s\n", host, port);
      return PROCESS_ERROR;
  }

  // Initialize RIO read structure for server
  rio_readinitb(prioclient, clientfd);

  // first request line
  char buftemp[MAXLINE];
  sprintf(buftemp, "%s %s HTTP/1.0\r\n", method, path);
  rio_writen(clientfd, buftemp, strlen(buftemp));
  printf("the buf is %s\n", buftemp);

  // read other lines of request
  while(rio_readlineb(prio, buftemp, MAXLINE) > 2) {
      if (strstr(buftemp, "User-Agent")) {
          char userAg[MAXLINE];
          strcpy(userAg, "User-Agent: ");
          strcpy(userAg+12, header_user_agent);
          //strcpy(userAg+12+strlen(header_user_agent), "\r\n");
          strncpy(buftemp, userAg, strlen(userAg));
      }
      else if (strstr(buftemp, "Proxy-Connection")) {
          strcpy(buftemp, "Proxy-Connection: close\r\n");
      }
      else if (strstr(buftemp, "Connection")) {
          strcpy(buftemp, "Connection: close\r\n");
      }
      printf("header within client: %s\n", buftemp);
      rio_writen(clientfd, buftemp, strlen(buftemp));
  }
  rio_writen(clientfd, "\r\n", 2);
  *pclientfd = clientfd;
  return SEND_SUCCESS;
}

/*
 * receive_content: receive http response from the server and send back to
 * client, we try to search the content-length first and then read message
 * respectively
 */
process_result receive_content(int fd, rio_t *prioclient,
                                      char *webbuf, size_t *psize)
{

  size_t length = 0;
  bool flag = false;
  // read the response from server
  char buf[MAXLINE];
  char *cur = webbuf;
  size_t total_size = 0;
  int size = 0;
  while ((size = rio_readlineb(prioclient, buf, MAXLINE)) > 2)
  {
      char *result = NULL;
      if ((result = strstr(buf, "Content-Length")) != NULL)
      {
          flag = true;
          result += 16;
          length = atoi(result);
      }
      // send message to the client
      // total_size += size;
      // if (total_size < MAX_OBJECT_SIZE) {
      //     memcpy(cur, buf, size);
      //     cur += size;
      // }
      Rio_writen(fd, buf, size);
  }

  Rio_writen(fd, "\r\n", 2);

  // send body of the message to the web client
  char bodyMsg[MAXLINE];

  if (!flag)
  {
      printf("no content_length\n");
      size = 0;
      cur = webbuf;
      while ((size = rio_readnb(prioclient, bodyMsg, MAXLINE)) > 0) {
          printf("size is %d\n", size);
          total_size += size;
          if (total_size < MAX_OBJECT_SIZE) {
              printf("copy size is %d\n", size);
              memcpy(cur, bodyMsg, size);
              cur += size;
          }
          Rio_writen(fd, bodyMsg, strlen(bodyMsg));
      }
      printf("no length, size is %zu\n", total_size);
      *psize = total_size;
      return RECEIVE_SUCCESS;
  }

  // have content length
  size = 0;
  cur = webbuf;
  printf("have content_length\n");
  printf("content length : %zu\n", length);
  while (length > 0)
  {
      int readlength = 0;
      if (length > MAXLINE) {
          readlength = MAXLINE;
      } else {
          readlength = length;
      }

      if ((size = rio_readnb(prioclient, bodyMsg, readlength)) == readlength) {
          total_size += size;
          if (total_size < MAX_OBJECT_SIZE) {
              memcpy(cur, bodyMsg, size);
              cur += size;
          }
          rio_writen(fd, bodyMsg, size);
          length -= readlength;
      }
      else {
          fprintf(stderr, "read from server error\n");

          if (prioclient->rio_fd > 0) {
            Close(prioclient->rio_fd);
          }
          if (fd > 0) {
            Close(fd);
          }
          return PROCESS_ERROR;
      }
  }
  printf("total size is %zu\n", total_size);
  *psize = total_size;
  return RECEIVE_SUCCESS;
}

/*
 * closefd : close the file descriptor
 */
void closefd(int fd)
{
  if (fd > 0) {
    Close(fd);
  }
}

/* Thread routine */
void *thread(void *vargp)
{
    pthread_detach(pthread_self());

    client_info *pclient = (client_info *)vargp;
    int connfd = pclient->connfd;
    client_info localclient;
    memcpy(&localclient, pclient, sizeof(client_info));

    // free the client_info
    Free(pclient);

    // serve functions
    serve(&localclient, connfd);

    // important, close file descriptor
    printf("close file descriptor %d\n", connfd);
    Close(connfd);
    return NULL;
}


/*
 * serve - handle one HTTP request/response transaction
 * reference tiny.c
 */
void serve(client_info *client, int connfd) {
    // Get some extra info about the client (hostname/port)
    // This is optional, but it's nice to know who's connected

    Getnameinfo((SA *) &client->addr, client->addrlen,
            client->host, sizeof(client->host),
            client->serv, sizeof(client->serv),
            0);
    printf("Accepted connection from %s:%s\n", client->host, client->serv);

    int fd = connfd;
    printf("the file descriptor is %d\n", fd);
    rio_t rio;
    rio_readinitb(&rio, fd);   // client receive

    /* Read request line */
    char buf[MAXLINE];
    if (rio_readlineb(&rio, buf, MAXLINE) <= 0) {
        return;
    }

    printf("%s", buf);

    /* Parse the request line and check if it's well-formed */
    char method[MAXLINE];
    char uri[MAXLINE];
    char version;

    /* sscanf must parse exactly 3 things for request line to be well-formed */
    /* version must be either HTTP/1.0 or HTTP/1.1 */
    if (sscanf(buf, "%s %s HTTP/1.%c", method, uri, &version) != 3
            || (version != '0' && version != '1')) {
        clienterror(connfd, buf, "400", "Bad Request",
                "Tiny received a malformed request");
        return;
    }

    /* Check that the method is GET */
    if (strncmp(method, "GET", sizeof("GET"))) {
        clienterror(connfd, method, "501", "Not Implemented",
                "Tiny does not implement this method");
        return;
    }

    /* Parse URI from GET request */
    char host[MAXLINE], path[MAXLINE], port[MAXLINE];

    parse_result result = parse_uri(uri, host, path, port);
    if (result == PARSE_ERROR) {
        clienterror(connfd, uri, "400", "Bad Request",
                "Tiny could not parse the request URI");
        return;
    }

    // step 2 :search the cache block
    // 2.1 lock the readcnt, and allow all the reader when first in
    P(&mutex);
    readcnt++;
    if (readcnt == 1) {    // first in
        P(&w);
    }
    V(&mutex);

    /* reading happens here */
    cache_node *pnode = NULL;
    if ((pnode = cache_search(host, path, port)) != NULL) {
        // cache hit
        cache_removefromlist(pnode);   // remove node from the list
        cache_addlast(pnode);    //  add it to the last position

        // send back to the client immediatelly
        printf("web object size is %zu\n", pnode->size);
        rio_writen(fd, pnode->web_object, pnode->size);
        return;
    }


    P(&mutex);
    readcnt--;
    if (readcnt == 0) {  // last out
      V(&w);
    }
    V(&mutex);


    // step 3 : send http requrest
    int clientfd = 0;
    rio_t rioclient;
    process_result res;
    res = send_request(&clientfd, &rioclient, &rio, host, port, method, path);
    if (res == PROCESS_ERROR) {
        printf("malformed requrest");
        closefd(clientfd);
        return;
    }
    printf("client fd is %d\n", clientfd);

    // step 4 : receive message
    size_t content_size = 0;
    res = receive_content(fd, &rioclient, content_buffer, &content_size);
    if (res == PROCESS_ERROR) {
        printf("malformed requrest");
        closefd(clientfd);
        return;
    }

    // step 5: write cache block
    if (content_size <= MAX_OBJECT_SIZE) {

        // block the other writer operation on the cache
        P(&w);
        cache_actual_size += content_size;
        while (cache_actual_size > MAX_CACHE_SIZE) {
            printf("total size is %zu\n", cache_actual_size);
            cache_deletefirst();
        }

        // create new cache block
        cache_node *newnode = cache_block_create(host, path, port,
                                content_buffer, content_size);
        printf("after create new cache!\n");
        cache_addlast(newnode);

        V(&w);
    }

    // step 6: finish
    printf("close server file descriptor %d\n", clientfd);
    closefd(clientfd);

    return;
}

int main(int argc, char **argv) {

  int listenfd;
  pthread_t tid;
  Signal(SIGPIPE, SIG_IGN);

  /* Check command line args */
  if (argc != 2) {
      fprintf(stderr, "usage: %s <port>\n", argv[0]);
      return 0;
  }

  // initialize the cache system
  cache_init();

  if ((listenfd = Open_listenfd(argv[1])) < 0) {
      fprintf(stderr, "Error input!\n");
      return 0;
  }

  while (1) {
      /* Allocate space on the stack for client info */
      // client_info client_data;
      client_info *client = (client_info *)Malloc(sizeof(client_info));

      /* Initialize the length of the address */
      client->addrlen = sizeof(client->addr);

      /* Accept() will block until a client connects to the port */
      client->connfd = Accept(listenfd,
              (SA *) &client->addr, &client->addrlen);

      /* Connection is established; serve client */
      // serve(client);
      pthread_create(&tid, NULL, thread, client);
  }
}
