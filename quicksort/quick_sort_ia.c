#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <omp.h>
#define MAX_SIZE 3000000
#define RAND_MAX_VALUE 100000

void quicksort(int *arr, int low, int high);

int main()
{
    int *arr = (int *)malloc(MAX_SIZE * sizeof(int));
    if (arr == NULL) {
        printf("Erro na alocação de memória!\n");
        return 1;
    }
    
    int n = MAX_SIZE;
    
    //gera numeros aleatórios
    srand(time(NULL));
    
    for(int i = 0; i < n; i++) {
        arr[i] = rand() % RAND_MAX_VALUE;
    }
    
    // Configura o número de threads para OpenMP
    omp_set_num_threads(4);
    
    // Registra o tempo inicial
    double start_time = omp_get_wtime();
    
    // Inicia região paralela
    #pragma omp parallel
    {
        #pragma omp single nowait
        {
            quicksort(arr, 0, n-1);
        }
    }
    
    // Registra o tempo final
    double end_time = omp_get_wtime();
    
    printf("\nTempo de execução: %.2f segundos\n", end_time - start_time);
    
    // Libera a memória alocada
    free(arr);
    
    return 0;
}

void quicksort(int *arr, int low, int high)
{
    if(low < high) {
        int i = low, j = high;
        // Usa diretamente o elemento do meio como pivô
        int pivot_index = low + (high - low) / 2;
        int pivot = arr[pivot_index];
        
        // Particiona o array
        while(i <= j) {
            while(arr[i] < pivot)
                i++;
            while(arr[j] > pivot)
                j--;
            if(i <= j) {
                int temp = arr[i];
                arr[i] = arr[j];
                arr[j] = temp;
                i++;
                j--;
            }
        }
        
        // Chamadas recursivas paralelas
        #pragma omp task
        quicksort(arr, low, j);
        #pragma omp task
        quicksort(arr, i, high);
        #pragma omp taskwait
    }
}
