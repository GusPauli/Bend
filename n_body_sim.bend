object Vector3D { x, y, z }

object Particle { position, velocity, mass }

def getG():
  return 6.67430 * ( 10.0 ** -11.0 )

# Calculates the gravitational force between two particles
def calculate_force(p1, p2):
  open Particle: p1
  open Particle: p2

  r = distance(p1.position, p2.position)
  if r == 0.0:
    return get_origin()
  else:
    force = (getG() * p1.mass * p2.mass) / (r * r)
    direction = normalize(subtract(p2.position, p1.position))
    return multiply(direction, force)

# Updates the position and velocity of a particle
def update_particle(particle, particles, timestep):
  fold particles:
    case List/Nil:
      total_force = get_origin()
    case List/Cons:
      total_force = add(calculate_force(particle, particles.head), particles.tail)

  open Particle: particle
  acceleration = divide(total_force, particle.mass)
  velocity = add(particle.velocity, multiply(acceleration, timestep))
  position = add(particle.position, multiply(particle.velocity, timestep))
  return Particle {position: position, velocity: velocity, mass: particle.mass}

def update_all_particles(particles, timestep):
  particles_cp = particles
  fold particles:
    case List/Nil:
      return List/Nil
    case List/Cons:
      return List/Cons { head: update_particle(particles.head, particles_cp, timestep), tail: particles.tail }

# Simulates the N-body system
def simulate(particles, steps, timestep):
  if steps == 0:
    return particles
  else:
    final_particles = update_all_particles(particles, timestep)
    return simulate(final_particles, steps - 1, timestep)

# Example setup
def get_particles():
  return [
  Particle {position: Vector3D {x: 0.497290, y: 0.966226, z: 0.428681 }, velocity: Vector3D {x: 0.198307, y: 0.361111, z: 0.689255 }, mass: 0.223625 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.964621, y: 0.821291, z: 0.419606 }, velocity: Vector3D {x: 0.662684, y: 0.587032, z: 0.163950 }, mass: 0.364583 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.020512, y: 0.015483, z: 0.220429 }, velocity: Vector3D {x: 0.340974, y: 0.021423, z: 0.830723 }, mass: 0.152234 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.967333, y: 0.542652, z: 0.476052 }, velocity: Vector3D {x: 0.267489, y: 0.542374, z: 0.945749 }, mass: 0.289386 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.129828, y: 0.036068, z: 0.901068 }, velocity: Vector3D {x: 0.341789, y: 0.620712, z: 0.605176 }, mass: 0.625194 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.360191, y: 0.230534, z: 0.795457 }, velocity: Vector3D {x: 0.645617, y: 0.484988, z: 0.961972 }, mass: 0.848607 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.966311, y: 0.593610, z: 0.141998 }, velocity: Vector3D {x: 0.677856, y: 0.129522, z: 0.422948 }, mass: 0.943829 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.973433, y: 0.263520, z: 0.962326 }, velocity: Vector3D {x: 0.091437, y: 0.564834, z: 0.232784 }, mass: 0.014364 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.859302, y: 0.903520, z: 0.468780 }, velocity: Vector3D {x: 0.864171, y: 0.291022, z: 0.077413 }, mass: 0.869917 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.913648, y: 0.644178, z: 0.668867 }, velocity: Vector3D {x: 0.971718, y: 0.821450, z: 0.852497 }, mass: 0.349954 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.474571, y: 0.435113, z: 0.346686 }, velocity: Vector3D {x: 0.269302, y: 0.337521, z: 0.651064 }, mass: 0.796140 * 10.0 ** 10.0 },
  Particle {position: Vector3D {x: 0.635530, y: 0.514166, z: 0.194046 }, velocity: Vector3D {x: 0.113760, y: 0.185229, z: 0.999429 }, mass: 0.919270 * 10.0 ** 10.0 },
  ]

def main:
  particles = get_particles()
  steps = 500000
  timestep = 0.001
  final_particles = simulate(particles, steps, timestep)
  return final_particles

# Helper functions
def distance(v1, v2):
  open Vector3D: v1
  open Vector3D: v2
  return ((v1.x - v2.x) ** 2.0 + (v1.y - v2.y) ** 2.0 + (v1.z - v2.z) ** 2.0) ** 0.5

def vector(x, y, z):
  return {x: x, y: y, z: z}

def add(v1, v2):
  open Vector3D: v1
  open Vector3D: v2
  return Vector3D { x: v1.x + v2.x, y: v1.y + v2.y, z: v1.z + v2.z }

def subtract(v1, v2):
  open Vector3D: v1
  open Vector3D: v2
  return Vector3D { x: v1.x - v2.x, y: v1.y - v2.y, z: v1.z - v2.z }

def multiply(v, scalar):
  open Vector3D: v
  return Vector3D { x: v.x * scalar, y: v.y * scalar, z: v.z * scalar }

def divide(v, scalar):
  open Vector3D: v
  return Vector3D { x: v.x / scalar, y: v.y / scalar, z: v.z / scalar }

def normalize(v):
  len = distance(get_origin(), v)
  return divide(v, len)

def get_origin():
  return Vector3D {x: 0.0, y: 0.0, z: 0.0}
