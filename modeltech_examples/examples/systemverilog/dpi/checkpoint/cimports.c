/*
 * DPI C functions for checkpoint test.
 *
 * These are examples on how to use interfaces related to checkpoint
 * and restore.
 *
 * The following interfaces are used in this example:
 *
 * extern void     mti_AddDPISaveRestoreCB(mtiVoidFuncPtrT saveFuncPtr, char* restoreFuncName);
 * extern char*    mti_GetCheckpointFilename();
 * extern int      mti_IsRestore();
 * extern int      mti_IsColdRestore();
 * extern void     mti_SaveBlock(char* p, mtiLongT size);
 * extern void     mti_SaveChar(char data);
 * extern void     mti_SaveLong(mtiLongT data);
 * extern void     mti_SaveShort(short data);
 * extern void     mti_SaveString(char* data);
 * extern void     mti_RestoreBlock(char * p);
 * extern char     mti_RestoreChar();
 * extern mtiLongT mti_RestoreLong();
 * extern short    mti_RestoreShort();
 * extern char*    mti_RestoreString();
 * extern void*    mti_Malloc(mtiUlongT size)
 */
#include <stdlib.h>
#include "cimports.h"
#include "mti.h"
#include "vpi_user.h"

DPI_DLLESPEC void myRestoreHandler1();
DPI_DLLESPEC void myRestoreHandler2();
DPI_DLLESPEC void mySharedHandler();

/* 
 * Example 1:
 * 
 * show a matching save/restore callback functions involving stack data manipulation.
 *
 */
static void print_data(mtiLongT long_data, char* str_data, int is_restore)
{
    if (is_restore) {      
        vpi_printf("After restore: \n");
    } else {
        vpi_printf("Before save: \n");
    }

    vpi_printf("\tlong_data = %ld, str_data = %s \n", long_data, str_data);
}

static void mySaveHandler1()
{
    mtiLongT  long_data = 57;
    char*  str_data = "hello";

    print_data(long_data, str_data, 0);

    mti_SaveLong(long_data);
    mti_SaveString(str_data);
}

void myRestoreHandler1()
{
  mtiLongT long_data;
  char* str_data;

  long_data = mti_RestoreLong();
  str_data = mti_RestoreString();

  print_data(long_data, str_data, 1);
}

/* 
 * Example 2:
 * 
 * show a matching save/restore callback functions involving static data and global data.
 *
 */

typedef struct myStructS {
    char    f1;
    short   f2;
} myStructT;

myStructT s1 = { 'x', 11} ;
static myStructT s2 =  { 'd', 77 };

static void printMyStruct (const char* prefix, myStructT* s1, myStructT* s2, int is_restore)
{
    if (is_restore) {
        vpi_printf("After restore '%s': \n", prefix);
    } else {
        vpi_printf("Before save  '%s': \n", prefix);
    }

    vpi_printf("\tf1 = '%c', f2 = %d \n", s1->f1, s1->f2);
    vpi_printf("\tf1 = '%c', f2 = %d \n", s2->f1, s2->f2);
}

static void mySaveHandler2()
{
    printMyStruct("s1 and s2", &s1, &s2, 0);

    mti_SaveBlock((char*) &s1, sizeof(myStructT));

    mti_SaveChar(s2.f1);
    mti_SaveShort(s2.f2);
}

void myRestoreHandler2()
{
    mti_RestoreBlock((char*)&s1);
    
    s2.f1 = mti_RestoreChar();
    s2.f2 = mti_RestoreShort();

    printMyStruct("s1 and s2", &s1, &s2, 1);
}

/* 
 * Example 3:
 * 
 * show a shared save/restore callback function involving heap allocation.
 *
 */

myStructT*  heap_data1;
myStructT*  heap_data2;

/* DPI call to trigger the heap memory allocations */
void run()
{
   vpi_printf("run() is called\n");

    /* use an external heap memory allocator */
    heap_data1 = malloc(sizeof(myStructT));
    heap_data1->f1 = 'a';
    heap_data1->f2 = 10;

    /* use a builtin heap memory allocator */
    heap_data2 = mti_Malloc(sizeof(myStructT));
    heap_data2->f1 = 'b';
    heap_data2->f2 = 5;
}


void mySharedHandler()
{
  int is_restore = mti_IsRestore();

  if (is_restore) {

      if (mti_IsColdRestore()) {
	  vpi_printf("reading checkpoint file %s ...\n", mti_GetCheckpointFilename());
	  heap_data1 = malloc(sizeof(myStructT));
      }

      /* restore heap memory allocation done by external allocator */
      mti_RestoreBlock((char*)heap_data1);

      /* restore heap memory allocation done by builtin allocator */
      heap_data2 = (myStructT* ) mti_RestoreLong();      

      printMyStruct("heap_data1 and heap_data2", heap_data1, heap_data2, 1);
  } else {
      printMyStruct("heap_data1 and heap_data2", heap_data1, heap_data2, 0);

      /* save heap memory allocation done by external allocator */
      mti_SaveBlock((char*)heap_data1, sizeof(myStructT));

      /* save heap memory allocation done by builtin allocator */
      mti_SaveLong((mtiLongT)heap_data2);
  }
}

/* DPI call */
void register_dpi_callback()
{
   vpi_printf("register_dpi_callback() is called\n");

   /* example 1 */
   mti_AddDPISaveRestoreCB(mySaveHandler1, "myRestoreHandler1");

   /* example 2 */
   mti_AddDPISaveRestoreCB(mySaveHandler2, "myRestoreHandler2");

   /* example 3 */
   mti_AddDPISaveRestoreCB(mySharedHandler, "mySharedHandler");
}
