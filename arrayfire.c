#include <arrayfire.h>
#include <math.h>
#include <stdio.h>

void* deref(void **val){
  return *val;
}

int size_of_dim_t(){
  return sizeof(dim_t);
}

int size_of_void(){
  return sizeof(void*);
}

int size_of_double(){
  return sizeof(double);
}

double deref_double(const double* ptr){
  double d = *ptr;
  return d;
}

int size_of_bits64(){
  return sizeof(unsigned long long);
}

unsigned long long deref_bits64(const unsigned long long* ptr){
  unsigned long long d = *ptr;
  return d;
}

void testo(){
    af_set_backend(1);
    af_array a;
    af_array b;
    af_array c;
    dim_t dims[1] = {1};
    af_randu(&a, 1, dims, 0);
    af_randu(&b, 1, dims, 0);
    int r = af_add(&c, a, b, 0);
    // double* d;
    // double* i;
    // int r2 = af_dot_all(d, i, a, b, 0, 0);
    printf("%d\n", r);
    // printf("%d\n", r2);
    // af::setBackend(AF_BACKEND_OPENCL);
    // af::array B = af::constant(10, 5, 5);
    // af::array C = af::matmul(A, B);     // This will throw an 
}

int int_peek(int *ptr, unsigned int offset) {
  int *buf_c = (int*) ptr;
  return (unsigned int) buf_c[offset];
}

void int_poke(void *ptr, unsigned int offset, int val) {
  int *buf_c = (int*)ptr;
  buf_c[offset] = val;
}

dim_t dim_peek(void *ptr, unsigned int offset) {
  dim_t *buf_c = (dim_t*) ptr;
  return (unsigned int) buf_c[offset];
}

void dim_poke(void *ptr, unsigned int offset, dim_t val) {
  dim_t *buf_c = (dim_t*)ptr;
  buf_c[offset] = val;
}
