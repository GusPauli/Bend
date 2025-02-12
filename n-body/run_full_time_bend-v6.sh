#!/bin/bash

# Define programs
pthread_programs=(
    "bend.c"
)
openmp_programs=(
    "n_body_sim.c"
)

iterations=$(seq 1 3)

# Create a directory to store all results
mkdir -p benchmark_results

# Function to monitor and log detailed metrics using perf stat
monitor_metrics() {
    local program_cmd=$1
    local results_dir=$2
    local iteration=$3
    local prefix=$4
    
    mkdir -p "$results_dir"
    /usr/bin/time -v -o "$results_dir/${prefix}_perf_$iteration.txt" $program_cmd >/dev/null 2>&1
}

# Function to run and monitor a program
run_program() {
    local program=$1
    local results_dir=$2
    local prefix=$3
    
    for iteration in $iterations; do
        echo "Running ${program%.c} iteration $iteration..."
        monitor_metrics "../n-body/${program%.c}" "$results_dir" "$iteration" "$prefix"
        echo "Metrics for ${program%.c} iteration $iteration logged to $results_dir"
    done
}

# Compile pthread programs
compile_pthread_programs() {
    for program in "${pthread_programs[@]}"; do
        gcc "../n-body/$program" -o "../n-body/${program%.c}" -pthread -lm
        if [ $? -ne 0 ]; then
            echo "Failed to compile $program"
            exit 1
        fi
        chmod +x "../n-body/${program%.c}"
    done
}

# Compile OpenMP programs
compile_openmp_programs() {
    for program in "${openmp_programs[@]}"; do
        gcc -fopenmp "../n-body/$program" -o "../n-body/${program%.c}" -lm
        if [ $? -ne 0 ]; then
            echo "Failed to compile $program"
            exit 1
        fi
        chmod +x "../n-body/${program%.c}"
    done
}

# Compile all programs before running
compile_pthread_programs
compile_openmp_programs

# Run pthread programs (bend)
for program in "${pthread_programs[@]}"; do
    program_name=$(basename "$program" .c)
    results_dir="benchmark_results/bend/$program_name"
    mkdir -p "$results_dir"
    run_program "$program" "$results_dir" "bend"
done

# Run OpenMP programs
for program in "${openmp_programs[@]}"; do
    program_name=$(basename "$program" .c)
    results_dir="benchmark_results/openmp/$program_name"
    mkdir -p "$results_dir"
    run_program "$program" "$results_dir" "openmp"
done

