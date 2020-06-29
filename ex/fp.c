#include <stdio.h> 
// A normal function with an int parameter 
// and void return type 

extern void fun(int a);

void fun1(int a) 
{ 
    printf("1Value of a is %d\n", a); 
} 

void fun2(int a) 
{ 
    printf("2Value of a is %d\n", a); 
} 
  
int main() 
{ 
    // fun_ptr is a pointer to function fun()  
    void (*fun_ptr)(int);
    int c;
    if (c)
        { fun_ptr = &fun; }
    else
        { fun_ptr = &fun2; }
  
    /* The above line is equivalent of following two 
       void (*fun_ptr)(int); 
       fun_ptr = &fun;  
    */
  
    // Invoking fun() using fun_ptr 
    (*fun_ptr)(10); 
  
    return 0; 
} 