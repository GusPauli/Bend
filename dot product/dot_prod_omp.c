#include <stdio.h>
#include <stdlib.h>
#include <omp.h>
#include <time.h>
#define SIZE 2000000
#define MAX_RANDOM 100 

int dot_product(int *, int *, size_t);

int main(void)
{
    int *a = (int *)malloc(SIZE * sizeof(int));
    int *b = (int *)malloc(SIZE * sizeof(int));
    
    if (a == NULL || b == NULL) {
        printf("Erro na alocação de memória\n");
        free(a);
        free(b);
        return EXIT_FAILURE;
    }

    srand(time(NULL));

    size_t i;
    
    #pragma omp parallel for
    for (i = 0; i < SIZE; i++) {
        #pragma omp critical
        {
            a[i] = rand() % MAX_RANDOM;
            b[i] = rand() % MAX_RANDOM;
        }
    }

    int result = dot_product(a, b, SIZE);
    printf("\nProduto escalar: %d\n", result);

    free(a);
    free(b);
    
    return EXIT_SUCCESS;
}

int dot_product(int *a, int *b, size_t n)
{
    int sum = 0;
    size_t i;
    
    #pragma omp parallel for reduction(+:sum)
    for (i = 0; i < n; i++) {
        sum += a[i] * b[i];
    }
    return sum;
}