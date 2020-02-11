#include "stdint.h"
#include "stdbool.h"

typedef int8_t int8;
typedef int16_t int16;
typedef int32_t int32;
typedef int64_t int64;
typedef uint8_t uint8;
typedef uint16_t uint16;
typedef uint32_t uint32;
typedef uint64_t uint64;
typedef float float32;
typedef double float64;
typedef char* string;

/* Secret values */

/*
// creates new secret memory
extern secret int8    new_int8    (void);
extern secret int16   new_int16   (void);
extern secret int32   new_int32   (void);
extern secret int64   new_int64   (void);
extern secret uint8   new_uint8   (void);
extern secret uint16  new_uint16  (void);
extern secret uint32  new_uint32  (void);
extern secret uint64  new_uint64  (void);
extern secret float32 new_float32 (void);
extern secret float64 new_float64 (void);
extern secret bool    new_bool    (void);*/

/*
// copy from x to y (secret values are seen as pointers)
extern void copy_int8    (secret int8    x,secret int8    y);
extern void copy_int16   (secret int16   x,secret int16   y);
extern void copy_int32   (secret int32   x,secret int32   y);
extern void copy_int64   (secret int64   x,secret int64   y);
extern void copy_uint8   (secret uint8   x,secret uint8   y);
extern void copy_uint16  (secret uint16  x,secret uint16  y);
extern void copy_uint32  (secret uint32  x,secret uint32  y);
extern void copy_uint64  (secret uint64  x,secret uint64  y);
extern void copy_float32 (secret float32 x,secret float32 y);
extern void copy_float64 (secret float64 x,secret float64 y);
extern void copy_bool    (secret bool    x,secret bool    y);*/

/*// frees secret memory
extern void delete_int8    (secret int8    x);
extern void delete_int16   (secret int16   x);
extern void delete_int32   (secret int32   x);
extern void delete_int64   (secret int64   x);
extern void delete_uint8   (secret uint8   x);
extern void delete_uint16  (secret uint16  x);
extern void delete_uint32  (secret uint32  x);
extern void delete_uint64  (secret uint64  x);
extern void delete_float32 (secret float32 x);
extern void delete_float64 (secret float64 x);
extern void delete_bool    (secret bool    x);*/

/*
// creates secret memory
extern secret int8    classify_int8    (int8    x);
extern secret int16   classify_int16   (int16   x);
extern secret int32   classify_int32   (int32   x);
extern secret int64   classify_int64   (int64   x);
extern secret uint8   classify_uint8   (uint8   x);
extern secret uint16  classify_uint16  (uint16  x);
extern secret uint32  classify_uint32  (uint32  x);
extern secret uint64  classify_uint64  (uint64  x);
extern secret float32 classify_float32 (float32 x);
extern secret float64 classify_float64 (float64 x);
extern secret bool    classify_bool    (bool    x);*/

extern int8    declassify_int8    (secret int8    x);
extern int16   declassify_int16   (secret int16   x);
extern int32   declassify_int32   (secret int32   x);
extern int64   declassify_int64   (secret int64   x);
extern uint8   declassify_uint8   (secret uint8   x);
extern uint16  declassify_uint16  (secret uint16  x);
extern uint32  declassify_uint32  (secret uint32  x);
extern uint64  declassify_uint64  (secret uint64  x);
extern float32 declassify_float32 (secret float32 x);
extern float64 declassify_float64 (secret float64 x);
extern bool    declassify_bool    (secret bool    x);

/*
//creates secret memory
extern secret int8    add_int8    (secret int8    x,secret int8    y);
extern secret int16   add_int16   (secret int16   x,secret int16   y);
extern secret int32   add_int32   (secret int32   x,secret int32   y);
extern secret int64   add_int64   (secret int64   x,secret int64   y);
extern secret uint8   add_uint8   (secret uint8   x,secret uint8   y);
extern secret uint16  add_uint16  (secret uint16  x,secret uint16  y);
extern secret uint32  add_uint32  (secret uint32  x,secret uint32  y);
extern secret uint64  add_uint64  (secret uint64  x,secret uint64  y);
extern secret float32 add_float32 (secret float32 x,secret float32 y);
extern secret float64 add_float64 (secret float64 x,secret float64 y);

//creates secret memory
extern secret int8    sub_int8    (secret int8    x,secret int8    y);
extern secret int16   sub_int16   (secret int16   x,secret int16   y);
extern secret int32   sub_int32   (secret int32   x,secret int32   y);
extern secret int64   sub_int64   (secret int64   x,secret int64   y);
extern secret uint8   sub_uint8   (secret uint8   x,secret uint8   y);
extern secret uint16  sub_uint16  (secret uint16  x,secret uint16  y);
extern secret uint32  sub_uint32  (secret uint32  x,secret uint32  y);
extern secret uint64  sub_uint64  (secret uint64  x,secret uint64  y);
extern secret float32 sub_float32 (secret float32 x,secret float32 y);
extern secret float64 sub_float64 (secret float64 x,secret float64 y);

//creates secret memory
extern secret int8    mul_int8    (secret int8    x,secret int8    y);
extern secret int16   mul_int16   (secret int16   x,secret int16   y);
extern secret int32   mul_int32   (secret int32   x,secret int32   y);
extern secret int64   mul_int64   (secret int64   x,secret int64   y);
extern secret uint8   mul_uint8   (secret uint8   x,secret uint8   y);
extern secret uint16  mul_uint16  (secret uint16  x,secret uint16  y);
extern secret uint32  mul_uint32  (secret uint32  x,secret uint32  y);
extern secret uint64  mul_uint64  (secret uint64  x,secret uint64  y);
extern secret float32 mul_float32 (secret float32 x,secret float32 y);
extern secret float64 mul_float64 (secret float64 x,secret float64 y);

//creates secret memory
extern secret int8    mulc_int8    (secret int8    x,int8    y);
extern secret int16   mulc_int16   (secret int16   x,int16   y);
extern secret int32   mulc_int32   (secret int32   x,int32   y);
extern secret int64   mulc_int64   (secret int64   x,int64   y);
extern secret uint8   mulc_uint8   (secret uint8   x,uint8   y);
extern secret uint16  mulc_uint16  (secret uint16  x,uint16  y);
extern secret uint32  mulc_uint32  (secret uint32  x,uint32  y);
extern secret uint64  mulc_uint64  (secret uint64  x,uint64  y);
extern secret float32 mulc_float32 (secret float32 x,float32 y);
extern secret float64 mulc_float64 (secret float64 x,float64 y);
*/

/* Secret arrays */

extern int8    *secret new_int8_array    (size_t size);
extern int16   *secret new_int16_array   (size_t size);
extern int32   *secret new_int32_array   (size_t size);
extern int64   *secret new_int64_array   (size_t size);
extern uint8   *secret new_uint8_array   (size_t size);
extern uint16  *secret new_uint16_array  (size_t size);
extern uint32  *secret new_uint32_array  (size_t size);
extern uint64  *secret new_uint64_array  (size_t size);
extern float32 *secret new_float32_array (size_t size);
extern float64 *secret new_float64_array (size_t size);
extern bool    *secret new_bool_array    (size_t size);

// copy from x to y
extern void copy_int8_array    (int8    *secret x,int8    *secret y);
extern void copy_int16_array   (int16   *secret x,int16   *secret y);
extern void copy_int32_array   (int32   *secret x,int32   *secret y);
extern void copy_int64_array   (int64   *secret x,int64   *secret y);
extern void copy_uint8_array   (uint8   *secret x,uint8   *secret y);
extern void copy_uint16_array  (uint16  *secret x,uint16  *secret y);
extern void copy_uint32_array  (uint32  *secret x,uint32  *secret y);
extern void copy_uint64_array  (uint64  *secret x,uint64  *secret y);
extern void copy_float32_array (float32 *secret x,float32 *secret y);
extern void copy_float64_array (float64 *secret x,float64 *secret y);
extern void copy_bool_array    (bool    *secret x,bool    *secret y);

extern void delete_int8_array    (int8    *secret x);
extern void delete_int16_array   (int16   *secret x);
extern void delete_int32_array   (int32   *secret x);
extern void delete_int64_array   (int64   *secret x);
extern void delete_uint8_array   (uint8   *secret x);
extern void delete_uint16_array  (uint16  *secret x);
extern void delete_uint32_array  (uint32  *secret x);
extern void delete_uint64_array  (uint64  *secret x);
extern void delete_float32_array (float32 *secret x);
extern void delete_float64_array (float64 *secret x);
extern void delete_bool_array    (bool    *secret x);

extern int8    secret load_int8_array    (int8    *secret x,size_t y);
extern int16   secret load_int16_array   (int16   *secret x,size_t y);
extern int32   secret load_int32_array   (int32   *secret x,size_t y);
extern int64   secret load_int64_array   (int64   *secret x,size_t y);
extern uint8   secret load_uint8_array   (uint8   *secret x,size_t y);
extern uint16  secret load_uint16_array  (uint16  *secret x,size_t y);
extern uint32  secret load_uint32_array  (uint32  *secret x,size_t y);
extern uint64  secret load_uint64_array  (uint64  *secret x,size_t y);
extern float32 secret load_float32_array (float32 *secret x,size_t y);
extern float64 secret load_float64_array (float64 *secret x,size_t y);
extern bool    secret load_bool_array    (bool    *secret x,size_t y);

extern void store_int8_array    (int8    *secret x,size_t y,int8    secret z);
extern void store_int16_array   (int16   *secret x,size_t y,int16   secret z);
extern void store_int32_array   (int32   *secret x,size_t y,int32   secret z);
extern void store_int64_array   (int64   *secret x,size_t y,int64   secret z);
extern void store_uint8_array   (uint8   *secret x,size_t y,uint8   secret z);
extern void store_uint16_array  (uint16  *secret x,size_t y,uint16  secret z);
extern void store_uint32_array  (uint32  *secret x,size_t y,uint32  secret z);
extern void store_uint64_array  (uint64  *secret x,size_t y,uint64  secret z);
extern void store_float32_array (float32 *secret x,size_t y,float32 secret z);
extern void store_float64_array (float64 *secret x,size_t y,float64 secret z);
extern void store_bool_array    (bool    *secret x,size_t y,bool    secret z);

// Size of the array in bytes
extern size_t size_int8_array    (int8    *secret x);
extern size_t size_int16_array   (int16   *secret x);
extern size_t size_int32_array   (int32   *secret x);
extern size_t size_int64_array   (int64   *secret x);
extern size_t size_uint8_array   (uint8   *secret x);
extern size_t size_uint16_array  (uint16  *secret x);
extern size_t size_uint32_array  (uint32  *secret x);
extern size_t size_uint64_array  (uint64  *secret x);
extern size_t size_float32_array (float32 *secret x);
extern size_t size_float64_array (float64 *secret x);
extern size_t size_bool_array    (bool    *secret x);

// Public and secret memory must be already allocated
extern void classify_int8_array    (int8    * x,int8    *secret y);
extern void classify_int16_array   (int16   * x,int16   *secret y);
extern void classify_int32_array   (int32   * x,int32   *secret y);
extern void classify_int64_array   (int64   * x,int64   *secret y);
extern void classify_uint8_array   (uint8   * x,uint8   *secret y);
extern void classify_uint16_array  (uint16  * x,uint16  *secret y);
extern void classify_uint32_array  (uint32  * x,uint32  *secret y);
extern void classify_uint64_array  (uint64  * x,uint64  *secret y);
extern void classify_float32_array (float32 * x,float32 *secret y);
extern void classify_float64_array (float64 * x,float64 *secret y);
extern void classify_bool_array  (bool  * x,bool  *secret y);

// Public and secret memory must be already allocated
extern void declassify_int8_array    (int8    *secret x,int8    * y);
extern void declassify_int16_array   (int16   *secret x,int16   * y);
extern void declassify_int32_array   (int32   *secret x,int32   * y);
extern void declassify_int64_array   (int64   *secret x,int64   * y);
extern void declassify_uint8_array   (uint8   *secret x,uint8   * y);
extern void declassify_uint16_array  (uint16  *secret x,uint16  * y);
extern void declassify_uint32_array  (uint32  *secret x,uint32  * y);
extern void declassify_uint64_array  (uint64  *secret x,uint64  * y);
extern void declassify_float32_array (float32 *secret x,float32 * y);
extern void declassify_float64_array (float64 *secret x,float64 * y);
extern void declassify_bool_array (bool *secret x,bool * y);

extern void add_int8_array    (int8    *secret x,int8    *secret y,int8    *secret res);
extern void add_int16_array   (int16   *secret x,int16   *secret y,int16   *secret res);
extern void add_int32_array   (int32   *secret x,int32   *secret y,int32   *secret res);
extern void add_int64_array   (int64   *secret x,int64   *secret y,int64   *secret res);
extern void add_uint8_array   (uint8   *secret x,uint8   *secret y,uint8   *secret res);
extern void add_uint16_array  (uint16  *secret x,uint16  *secret y,uint16  *secret res);
extern void add_uint32_array  (uint32  *secret x,uint32  *secret y,uint32  *secret res);
extern void add_uint64_array  (uint64  *secret x,uint64  *secret y,uint64  *secret res);
extern void add_float32_array (float32 *secret x,float32 *secret y,float32 *secret res);
extern void add_float64_array (float64 *secret x,float64 *secret y,float64 *secret res);

/* Strings and Printers */

extern string int8_to_string    (int8    x);
extern string int16_to_string   (int16   x);
extern string int32_to_string   (int32   x);
extern string int64_to_string   (int64   x);
extern string uint8_to_string   (uint8   x);
extern string uint16_to_string  (uint16  x);
extern string uint32_to_string  (uint32  x);
extern string uint64_to_string  (uint64  x);
extern string float32_to_string (float32 x);
extern string float64_to_string (float64 x);
extern string bool_to_string    (bool x);

extern void print (string str);

void print_int8    (int8    x) { print (int8_to_string    (x)); }
void print_int16   (int16   x) { print (int16_to_string   (x)); }
void print_int32   (int32   x) { print (int32_to_string   (x)); }
void print_int64   (int64   x) { print (int64_to_string   (x)); }
void print_uint8   (uint8   x) { print (uint8_to_string   (x)); }
void print_uint16  (uint16  x) { print (uint16_to_string  (x)); }
void print_uint32  (uint32  x) { print (uint32_to_string  (x)); }
void print_uint64  (uint64  x) { print (uint64_to_string  (x)); }
void print_float32 (float32 x) { print (float32_to_string (x)); }
void print_float64 (float64 x) { print (float64_to_string (x)); }
void print_bool    (bool    x) { print (bool_to_string    (x)); }

/* Conversions */

extern secret uint16  uint8_to_uint16   (secret uint8 x);
extern secret uint32  uint8_to_uint32   (secret uint8 x);
extern secret uint64  uint8_to_uint64   (secret uint8 x);
extern secret int8    uint8_to_int8     (secret uint8 x);
extern secret int16   uint8_to_int16    (secret uint8 x);
extern secret int32   uint8_to_int32    (secret uint8 x);
extern secret int64   uint8_to_int64    (secret uint8 x);
extern secret float32 uint8_to_float32  (secret uint8 x);
extern secret float64 uint8_to_float64  (secret uint8 x);
extern secret bool    uint8_to_bool     (secret uint8 x);

extern secret uint8   uint16_to_uint8   (secret uint16 x);
extern secret uint32  uint16_to_uint32  (secret uint16 x);
extern secret uint64  uint16_to_uint64  (secret uint16 x);
extern secret int8    uint16_to_int8    (secret uint16 x);
extern secret int16   uint16_to_int16   (secret uint16 x);
extern secret int32   uint16_to_int32   (secret uint16 x);
extern secret int64   uint16_to_int64   (secret uint16 x);
extern secret float32 uint16_to_float32 (secret uint16 x);
extern secret float64 uint16_to_float64 (secret uint16 x);
extern secret bool    uint16_to_bool    (secret uint16 x);

extern secret uint8   uint32_to_uint8   (secret uint32 x);
extern secret uint16  uint32_to_uint16  (secret uint32 x);
extern secret uint64  uint32_to_uint64  (secret uint32 x);
extern secret int8    uint32_to_int8    (secret uint32 x);
extern secret int16   uint32_to_int16   (secret uint32 x);
extern secret int32   uint32_to_int32   (secret uint32 x);
extern secret int64   uint32_to_int64   (secret uint32 x);
extern secret float32 uint32_to_float32 (secret uint32 x);
extern secret float64 uint32_to_float64 (secret uint32 x);
extern secret bool    uint32_to_bool    (secret uint32 x);

extern secret uint8   uint64_to_uint8   (secret uint64 x);
extern secret uint16  uint64_to_uint16  (secret uint64 x);
extern secret uint32  uint64_to_uint32  (secret uint64 x);
extern secret int8    uint64_to_int8    (secret uint64 x);
extern secret int16   uint64_to_int16   (secret uint64 x);
extern secret int32   uint64_to_int32   (secret uint64 x);
extern secret int64   uint64_to_int64   (secret uint64 x);
extern secret float32 uint64_to_float32 (secret uint64 x);
extern secret float64 uint64_to_float64 (secret uint64 x);
extern secret bool    uint64_to_bool    (secret uint64 x);

extern secret uint8   int8_to_uint8     (secret int8 x);
extern secret uint16  int8_to_uint16    (secret int8 x);
extern secret uint32  int8_to_uint32    (secret int8 x);
extern secret uint64  int8_to_uint64    (secret int8 x);
extern secret int16   int8_to_int16     (secret int8 x);
extern secret int32   int8_to_int32     (secret int8 x);
extern secret int64   int8_to_int64     (secret int8 x);
extern secret float32 int8_to_float32   (secret int8 x);
extern secret float64 int8_to_float64   (secret int8 x);
extern secret bool    int8_to_bool      (secret int8 x);

extern secret uint8   int16_to_uint8    (secret int16 x);
extern secret uint16  int16_to_uint16   (secret int16 x);
extern secret uint32  int16_to_uint32   (secret int16 x);
extern secret uint64  int16_to_uint64   (secret int16 x);
extern secret int8    int16_to_int8     (secret int16 x);
extern secret int32   int16_to_int32    (secret int16 x);
extern secret int64   int16_to_int64    (secret int16 x);
extern secret float32 int16_to_float32  (secret int16 x);
extern secret float64 int16_to_float64  (secret int16 x);
extern secret bool    int16_to_bool     (secret int16 x);

extern secret uint8   int32_to_uint8    (secret int32 x);
extern secret uint16  int32_to_uint16   (secret int32 x);
extern secret uint32  int32_to_uint32   (secret int32 x);
extern secret uint64  int32_to_uint64   (secret int32 x);
extern secret int8    int32_to_int8     (secret int32 x);
extern secret int16   int32_to_int16    (secret int32 x);
extern secret int64   int32_to_int64    (secret int32 x);
extern secret float32 int32_to_float32  (secret int32 x);
extern secret float64 int32_to_float64  (secret int32 x);
extern secret bool    int32_to_bool     (secret int32 x);

extern secret uint8   int64_to_uint8    (secret int64 x);
extern secret uint16  int64_to_uint16   (secret int64 x);
extern secret uint32  int64_to_uint32   (secret int64 x);
extern secret uint64  int64_to_uint64   (secret int64 x);
extern secret int8    int64_to_int8     (secret int64 x);
extern secret int16   int64_to_int16    (secret int64 x);
extern secret int32   int64_to_int32    (secret int64 x);
extern secret float32 int64_to_float32  (secret int64 x);
extern secret float64 int64_to_float64  (secret int64 x);
extern secret bool    int64_to_bool     (secret int64 x);

extern secret uint8   float32_to_uint8   (secret float32 x);
extern secret uint16  float32_to_uint16  (secret float32 x);
extern secret uint32  float32_to_uint32  (secret float32 x);
extern secret uint64  float32_to_uint64  (secret float32 x);
extern secret int8    float32_to_int8    (secret float32 x);
extern secret int16   float32_to_int16   (secret float32 x);
extern secret int32   float32_to_int32   (secret float32 x);
extern secret int64   float32_to_int64   (secret float32 x);
extern secret float64 float32_to_float64 (secret float32 x);
extern secret bool    float32_to_bool    (secret float32 x);

extern secret uint8   float64_to_uint8   (secret float64 x);
extern secret uint16  float64_to_uint16  (secret float64 x);
extern secret uint32  float64_to_uint32  (secret float64 x);
extern secret uint64  float64_to_uint64  (secret float64 x);
extern secret int8    float64_to_int8    (secret float64 x);
extern secret int16   float64_to_int16   (secret float64 x);
extern secret int32   float64_to_int32   (secret float64 x);
extern secret int64   float64_to_int64   (secret float64 x);
extern secret float32 float64_to_float32 (secret float64 x);
extern secret bool    float64_to_bool    (secret float64 x);

extern secret uint8   bool_to_uint8      (secret bool x);
extern secret uint16  bool_to_uint16     (secret bool x);
extern secret uint32  bool_to_uint32     (secret bool x);
extern secret uint64  bool_to_uint64     (secret bool x);
extern secret int8    bool_to_int8       (secret bool x);
extern secret int16   bool_to_int16      (secret bool x);
extern secret int32   bool_to_int32      (secret bool x);
extern secret int64   bool_to_int64      (secret bool x);
extern secret float32 bool_to_float32    (secret bool x);
extern secret float64 bool_to_float64    (secret bool x);
