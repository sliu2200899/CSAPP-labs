/*
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(size_t M, size_t N, double A[N][M], double B[M][N], double *tmp);
 * A is the source matrix, B is the destination
 * tmp points to a region of memory able to hold TMPCOUNT (set to 256) doubles as temporaries
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 2KB direct mapped cache with a block size of 64 bytes.
 *
 *  Full Name: Shu Liu
 *  Andrew ID: shul2
 *
 * Programming restrictions:
 *   No out-of-bounds references are allowed
 *   No alterations may be made to the source array A
 *   Data in tmp can be read or written
 *   This file cannot contain any local or global doubles or arrays of doubles
 *   You may not use unions, casting, global variables, or
 *     other tricks to hide array data in other forms of local or global memory.
 */
#include <stdio.h>
#include <stdbool.h>
#include "cachelab.h"
#include "contracts.h"

#define SIZEFOR32 32   /* regular smaller size for M and N, 32 */
#define SIZEFOR64 64   /* regular larger size for M and N, 64 */
#define IRREGSIZE1 63  /* irregular larger size for M, 63 */
#define IRREGSIZE2 65  /* irregular larger size for N, 65 */
#define IRREGSIZEBLKROW 16  /* irregular size block row 16 */
#define IRREGSIZEBLKCOL 4   /* irregular size block col 4 */
#define REGULARNORMBLK 8   /* regular normal block size for row and col 8 */


/* Forward declarations */
bool is_transpose(size_t M, size_t N, double A[N][M], double B[M][N]);
void trans(size_t M, size_t N, double A[N][M], double B[M][N], double *tmp);
void trans_tmp(size_t M, size_t N, double A[N][M], double B[M][N], double *tmp);

/*
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded.
 */
char transpose_submit_desc[] = "Transpose submission";


void trans_irregular_size(size_t M, size_t N, double A[N][M], double B[M][N]) {
  int blocksizeforRow = 0, blocksizeforCol = 0;
  int blockCol = 0, blockRow = 0;
  int i1 = 0, i2 = 0;

  blocksizeforRow = IRREGSIZEBLKROW;
  blocksizeforCol = IRREGSIZEBLKCOL;
  for (blockCol = 0; blockCol < M; blockCol+=blocksizeforCol) {
    for (blockRow = 0; blockRow < N; blockRow+=blocksizeforRow) {
      for (i1 = blockRow; i1 < N && i1 < blockRow+blocksizeforRow; i1++) {
          for (i2 = blockCol; i2 < M && i2 < blockCol+blocksizeforCol; i2++) {
             B[i2][i1] = A[i1][i2];
          }
      }
    }
  }
}


void trans_regular_small_size(size_t M, size_t N, double A[N][M], double B[M][N], double *tmp) {
  int blockCol = 0, blockRow = 0;
  int i1 = 0, i2 = 0;
  int blocksize = REGULARNORMBLK;
  int l = 0; // indicating this is diagonal block

  for (blockCol = 0; blockCol < M; blockCol+=blocksize) {
    for (blockRow = 0; blockRow < N; blockRow+=blocksize) {
      for (i1 = blockCol; i1 < M && i1 < blockCol+blocksize; i1++) {
          for (i2 = blockRow; i2 < N && i2 < blockRow+blocksize; i2++) {

            if (i1 != i2) {
              B[i2][i1] = A[i1][i2];
            } else {
              tmp[i1 + blocksize] = A[i1][i2];
              l = 1;  // indicating this is diagonal block
            }
          }
          if (l == 1) {
            B[i1][i1] = tmp[i1 + blocksize];
            l = 0;
          }
        }
     }
  }
}

void trans_regular_large_size(size_t M, size_t N, double A[N][M], double B[M][N], double *tmp) {
  int blockCol = 0, blockRow = 0;
  int i1 = 0, i2 = 0;
  int blocksize = REGULARNORMBLK;
  int flagT = 0;  //
  int colplusblock = 0, rowplusblock = 0; // for loop middle variable
  int outer4 = 0, inner4 = 0;  // divide into 4*4 matrix
  int w = 0;   // indicating this is diagonal top right or left or down right or left
  int k = 0, t = 0;  // put tmp data into the B
  int icount = 0;   // store A data into tmp
  int l = 0;  // indicating end of storing 32 elements
  int i1temp = 0, res = 0;; // middle variables

  for (blockCol = 0; blockCol < M; blockCol+=blocksize) {
    for (blockRow = 0; blockRow < N; blockRow+=blocksize) {
      colplusblock = blockCol + blocksize;
      rowplusblock = blockRow + blocksize;
      // divide 8*8 matrix
      for (i1 = blockRow; i1 < N && i1 < rowplusblock; i1+=4) {
          for (i2 = blockCol; i2 < M && i2 < colplusblock; i2+=4) {
            // divide 4*4 matrix
            for (outer4 = i1; outer4 < i1 + 4; outer4++) {
              for (inner4 = i2; inner4 < i2 + 4; inner4++) {

                if (blockCol != blockRow) {
                  // this is non-diagnal block

                  // the top left 4*4 matrix should be put directly
                  if (i2 - blockCol < 4 && i1 - blockRow < 4) {
                     B[inner4][outer4] = A[outer4][inner4];
                  }

                  // the top right 4*4 matrix should be stored in tmp
                  // notice that almost all the data put in tmp in 2 block, otherwise 3
                  if (i2 - blockCol >= 4 && i1 - blockRow < 4) {
                    if (outer4%4 == 0 && inner4 < 16) {
                      flagT = 1;
                    }

                    if (flagT) {
                      tmp[icount + 16] = A[outer4][inner4];
                    } else {
                      tmp[icount] = A[outer4][inner4];
                    }

                    icount++;
                    if (icount == 16) {
                      icount = 0;
                    }
                  }

                  // the down left and down right 4*4 matrix should be put finally
                  if (i1 - blockRow >= 4) {
                      B[inner4][outer4] = A[outer4][inner4];
                      l++;
                  }

                  // when the down left and down right 4*4 matrix has been dealt with properly,
                  // put the elements in tmp array into the B.
                  if (l == 32) {
                    
                    for (k = 0; k < 4; k++) {
                      for (t = 0; t < 4; t++) {
                        if (flagT) {
                          B[inner4 - 3 + k][outer4 - 7 + t] = tmp[16+t*4+k];
                        } else {
                          B[inner4 - 3 + k][outer4 - 7 + t] = tmp[t*4+k];
                        }
                      }
                    }

                    l = 0;
                    flagT = 0;
                    icount = 0;
                  }

                } else {
                  // this is diagonal block, should deal with the diagonal carefully
                  // i1 row , i2 col
                  // outer<-> row, inner<-> col

                  // top left diagonal element are put into the tmp[0~3]
                  if (i2 - blockCol < 4 && i1 - blockRow < 4) {
                    if (outer4 != inner4) {
                      B[inner4][outer4] = A[outer4][inner4];
                    } else {
                      tmp[inner4 - i2] = A[outer4][inner4];
                      w = 1;  // indicating this is diagonal block
                    }
                  }

                  // top right diagonal element are put into the tmp[4~7]
                  if (i2 - blockCol >= 4 && i1 - blockRow < 4) {
                    if (outer4 != (inner4-4)) {
                      B[inner4][outer4] = A[outer4][inner4];
                    } else {
                      tmp[4 + inner4 - i2] = A[outer4][inner4];
                      w = 2;  // indicating this is diagonal block
                    }
                  }

                  // down left diagonal element are put into the tmp[0~3]
                  if (i2 - blockCol < 4 && i1 - blockRow >= 4) {
                    if ((outer4-4) != inner4) {
                      B[inner4][outer4] = A[outer4][inner4];
                    } else {
                      tmp[inner4 - i2] = A[outer4][inner4];
                      w = 3;  // indicating this is diagonal block
                    }
                  }

                  // top right diagonal element are put into the tmp[4~7]
                  if (i2 - blockCol >= 4 && i1 - blockRow >= 4) {
                    if (inner4 != outer4) {
                      B[inner4][outer4] = A[outer4][inner4];
                    } else {
                      tmp[4 + inner4 - i2] = A[outer4][inner4];
                      w = 4;  // indicating this is diagonal block
                    }
                  }
                } // end of blockcol == blockRow
              } // end of inner4
            } // end of outer4
          } // end of i2
          if (w == 2) {
            i1temp = i1;
            for (res = 0; res < 4; res++, i1temp++) {
              B[i1temp][i1temp] = tmp[res];
            }
            i1temp = i1;
            for (res = 4; res < 8; res++, i1temp++) {
              B[i1temp+4][i1temp] = tmp[res];
            }
            w = 0;
          } else if (w == 4) {
            i1temp = i1;
            for (res = 0; res < 4; res++, i1temp++) {
              B[i1temp-4][i1temp] = tmp[res];
            }
            i1temp = i1;
            for (res = 4; res < 8; res++, i1temp++) {
              B[i1temp][i1temp] = tmp[res];
            }
            w = 0;
          }
        } // end of i1
     } // end of blockRow
  }// end of blockCol
}

void transpose_submit(size_t M, size_t N, double A[N][M], double B[M][N], double *tmp)
{

    //int tempcol = 0;
    /*
     * This is a good place to call your favorite transposition functions
     * It's OK to choose different functions based on array size, but
     * your code must be correct for all values of M and N
     */
    if (M == SIZEFOR32 && N == SIZEFOR32) {
      trans_regular_small_size(M, N, A, B, tmp);
    } else if (M == SIZEFOR64 && N == SIZEFOR64) {
      trans_regular_large_size(M, N, A, B, tmp);
    } else if (M == IRREGSIZE1 && N == IRREGSIZE2) {
      trans_irregular_size(M, N, A, B);
    } else {
      trans(M, N, A, B, tmp);
    }
}

/*
 * You can define additional transpose functions below. We've defined
 * some simple ones below to help you get started.
 */

/*
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";

/*
 * The following shows an example of a correct, but cache-inefficient
 *   transpose function.  Note the use of macros (defined in
 *   contracts.h) that add checking code when the file is compiled in
 *   debugging mode.  See the Makefile for instructions on how to do
 *   this.
 *
 *   IMPORTANT: Enabling debugging will significantly reduce your
 *   cache performance.  Be sure to disable this checking when you
 *   want to measure performance.
 */
void trans(size_t M, size_t N, double A[N][M], double B[M][N], double *tmp)
{
    size_t i, j;

    REQUIRES(M > 0);
    REQUIRES(N > 0);

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            B[j][i] = A[i][j];
        }
    }

    ENSURES(is_transpose(M, N, A, B));
}

/*
 * This is a contrived example to illustrate the use of the temporary array
 */

char trans_tmp_desc[] =
    "Simple row-wise scan transpose, using a 2X2 temporary array";

void trans_tmp(size_t M, size_t N, double A[N][M], double B[M][N], double *tmp)
{
    size_t i, j;
    /* Use the first four elements of tmp as a 2x2 array with row-major ordering. */
    REQUIRES(M > 0);
    REQUIRES(N > 0);

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            int di = i%2;
            int dj = j%2;
            tmp[2*di+dj] = A[i][j];
            B[j][i] = tmp[2*di+dj];
        }
    }

    ENSURES(is_transpose(M, N, A, B));
}

void trans_tmp_1(size_t M, size_t N, double A[N][M], double B[M][N], double *tmp) {
  int blocksize = 0;
  int i, j;
  int i1, i2;

  /*
   * This is a good place to call your favorite transposition functions
   * It's OK to choose different functions based on array size, but
   * your code must be correct for all values of M and N
   */
  if (M == 32 && N == 32) {
    blocksize = 8;
    for (i = 0; i < M; i+=blocksize) {
      for (j = 0; j < N; j+=blocksize) {
        for (i1 = i; i1 < M && i1 < i+blocksize; i1++) {
          for (i2 = j; i2 < N && i2 < j+blocksize; i2++) {

            B[i2][i1] = A[i1][i2];
          }
        }
      }
    }
  } else if (M == 64 && N == 64) {
      ;
  }
}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions()
{
    /* Register your solution function */
    registerTransFunction(transpose_submit, transpose_submit_desc);

    /* Register any additional transpose functions */
    registerTransFunction(trans, trans_desc);
    registerTransFunction(trans_tmp, trans_tmp_desc);
    //registerTransFunction(trans_tmp_1, transpose_submit_desc);

}

/*
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
bool is_transpose(size_t M, size_t N, double A[N][M], double B[M][N])
{
    size_t i, j;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; ++j) {
            if (A[i][j] != B[j][i]) {
                return false;
            }
        }
    }
    return true;
}
