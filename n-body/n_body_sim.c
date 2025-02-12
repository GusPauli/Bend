#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <omp.h>

typedef struct {
    double x, y, z;
} Vector3D;

typedef struct {
    Vector3D position;
    Vector3D velocity;
    double mass;
} Particle;

void compute_forces(Particle *particles, Vector3D *forces, int num_particles, double G) {
    for (int i = 0; i < num_particles; i++) {
        forces[i].x = forces[i].y = forces[i].z = 0.0;
    }

    #pragma omp parallel for
    for (int i = 0; i < num_particles; i++) {
        for (int j = 0; j < num_particles; j++) {
            if (i != j) {
                double dx = particles[j].position.x - particles[i].position.x;
                double dy = particles[j].position.y - particles[i].position.y;
                double dz = particles[j].position.z - particles[i].position.z;
                double distance = sqrt(dx * dx + dy * dy + dz * dz);
                double force_magnitude = G * particles[i].mass * particles[j].mass / (distance * distance);
                double fx = force_magnitude * dx / distance;
                double fy = force_magnitude * dy / distance;
                double fz = force_magnitude * dz / distance;

                #pragma omp atomic
                forces[i].x += fx;
                #pragma omp atomic
                forces[i].y += fy;
                #pragma omp atomic
                forces[i].z += fz;
            }
        }
    }
}

void update_particles(Particle *particles, Vector3D *forces, int num_particles, double dt) {
    #pragma omp parallel for
    for (int i = 0; i < num_particles; i++) {
        particles[i].velocity.x += forces[i].x / particles[i].mass * dt;
        particles[i].velocity.y += forces[i].y / particles[i].mass * dt;
        particles[i].velocity.z += forces[i].z / particles[i].mass * dt;
        particles[i].position.x += particles[i].velocity.x * dt;
        particles[i].position.y += particles[i].velocity.y * dt;
        particles[i].position.z += particles[i].velocity.z * dt;
    }
}

void simulate(Particle *particles, int num_particles, int num_steps, double dt) {
    Vector3D *forces = (Vector3D *)calloc(num_particles, sizeof(Vector3D));
    double G = 6.67430e-11;
    for (int step = 0; step < num_steps; step++) {
        compute_forces(particles, forces, num_particles, G);
        update_particles(particles, forces, num_particles, dt);
    }
    free(forces);
}

int main() {
    int num_particles = 12;
    Particle particles[] = {
    {{ 0.49729, 0.966226, 0.428681 }, { 0.198307, 0.361111, 0.689255 }, 0.223625 * powl(10, 10)},
    {{ 0.964621, 0.821291, 0.419606 }, { 0.662684, 0.587032, 0.16395 }, 0.364583 * powl(10, 10)},
    {{ 0.020512, 0.015483, 0.220429 }, { 0.340974, 0.021423, 0.830723 }, 0.152234 * powl(10, 10)},
    {{ 0.967333, 0.542652, 0.476052 }, { 0.267489, 0.542374, 0.945749 }, 0.289386 * powl(10, 10)},
    {{ 0.129828, 0.036068, 0.901068 }, { 0.341789, 0.620712, 0.605176 }, 0.625194 * powl(10, 10)},
    {{ 0.360191, 0.230534, 0.795457 }, { 0.645617, 0.484988, 0.961972 }, 0.848607 * powl(10, 10)},
    {{ 0.966311, 0.59361, 0.141998 }, { 0.677856, 0.129522, 0.422948 }, 0.943829 * powl(10, 10)},
    {{ 0.973433, 0.26352, 0.962326 }, { 0.091437, 0.564834, 0.232784 }, 0.014364 * powl(10, 10)},
    {{ 0.859302, 0.90352, 0.46878 }, { 0.864171, 0.291022, 0.077413 }, 0.869917 * powl(10, 10)},
    {{ 0.913648, 0.644178, 0.668867 }, { 0.971718, 0.82145, 0.852497 }, 0.349954 * powl(10, 10)},
    {{ 0.474571, 0.435113, 0.346686 }, { 0.269302, 0.337521, 0.651064 }, 0.79614 * powl(10, 10)},
    {{ 0.63553, 0.514166, 0.194046 }, { 0.11376, 0.185229, 0.999429 }, 0.91927 * powl(10, 10)},
};

    simulate(particles, num_particles, 50000, 0.001);

    for (int i = 0; i < num_particles; i++) {
        printf("Particle: position=(%f, %f, %f), velocity=(%f, %f, %f), mass=%f\n",
               particles[i].position.x, particles[i].position.y, particles[i].position.z,
               particles[i].velocity.x, particles[i].velocity.y, particles[i].velocity.z,
               particles[i].mass);
    }

    return 0;
}
