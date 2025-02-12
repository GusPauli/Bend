#include <stdio.h>
#include <stdlib.h>
#include <omp.h>
#define SIZE 500000

int dot_product(int *, int *, size_t);

int main(void)
{
    int a[SIZE], b[SIZE];
    size_t i;

    // Paralelizando o preenchimento dos vetores
    #pragma omp parallel for
    for (i = 0; i < SIZE; i++) {
        a[i] = 1;
        b[i] = 1;
    }

    printf("%d\n", dot_product(a, b, sizeof(a) / sizeof(a[0])));
    return EXIT_SUCCESS;
}

int dot_product(int *a, int *b, size_t n)
{
    int sum = 0;
    size_t i;
    
    // Paralelizando o cálculo do produto escalar com redução
    #pragma omp parallel for reduction(+:sum)
    for (i = 0; i < n; i++) {
        sum += a[i] * b[i];
    }
    return sum;
}