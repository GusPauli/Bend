#define IO

#include <inttypes.h>
#include <math.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef DEBUG
  #define debug(...) fprintf(stderr, __VA_ARGS__)
#else
  #define debug(...)
#endif

#define COMPILED
#define WITH_MAIN

// Types
// --------

typedef  uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
typedef  int32_t i32;
typedef    float f32;
typedef   double f64;

typedef  _Atomic(u8)  a8;
typedef _Atomic(u16) a16;
typedef _Atomic(u32) a32;
typedef _Atomic(u64) a64;

// Configuration
// -------------

// Threads per CPU
#ifndef TPC_L2
#define TPC_L2 2 // 4 cores
#endif
#define TPC (1ul << TPC_L2)

// Types
// -----

// Local Types
typedef u8  Tag;  // Tag  ::= 3-bit (rounded up to u8)
typedef u32 Val;  // Val  ::= 29-bit (rounded up to u32)
typedef u32 Port; // Port ::= Tag + Val (fits a u32)
typedef u64 Pair; // Pair ::= Port + Port (fits a u64)

typedef a32 APort; // atomic Port
typedef a64 APair; // atomic Pair

// Rules
typedef u8 Rule; // Rule ::= 3-bit (rounded up to 8)

// Numbs
typedef u32 Numb; // Numb ::= 29-bit (rounded up to u32)

// Tags
#define VAR 0x0 // variable
#define REF 0x1 // reference
#define ERA 0x2 // eraser
#define NUM 0x3 // number
#define CON 0x4 // constructor
#define DUP 0x5 // duplicator
#define OPR 0x6 // operator
#define SWI 0x7 // switch

// Interaction Rule Values
#define LINK 0x0
#define CALL 0x1
#define VOID 0x2
#define ERAS 0x3
#define ANNI 0x4
#define COMM 0x5
#define OPER 0x6
#define SWIT 0x7

// Numbers
static const f32 U24_MAX = (f32) (1 << 24) - 1;
static const f32 U24_MIN = 0.0;
static const f32 I24_MAX = (f32) (1 << 23) - 1;
static const f32 I24_MIN = (f32) (i32) ((-1u) << 23);
#define TY_SYM 0x00
#define TY_U24 0x01
#define TY_I24 0x02
#define TY_F24 0x03
#define OP_ADD 0x04
#define OP_SUB 0x05
#define FP_SUB 0x06
#define OP_MUL 0x07
#define OP_DIV 0x08
#define FP_DIV 0x09
#define OP_REM 0x0A
#define FP_REM 0x0B
#define OP_EQ  0x0C
#define OP_NEQ 0x0D
#define OP_LT  0x0E
#define OP_GT  0x0F
#define OP_AND 0x10
#define OP_OR  0x11
#define OP_XOR 0x12
#define OP_SHL 0x13
#define FP_SHL 0x14
#define OP_SHR 0x15
#define FP_SHR 0x16

// Constants
#define FREE 0x00000000
#define ROOT 0xFFFFFFF8
#define NONE 0xFFFFFFFF

// Cache Padding
#define CACHE_PAD 64

// Global Net
#define HLEN (1ul << 16) // max 16k high-priority redexes
#define RLEN (1ul << 24) // max 16m low-priority redexes
#define G_NODE_LEN (1ul << 29) // max 536m nodes
#define G_VARS_LEN (1ul << 29) // max 536m vars
#define G_RBAG_LEN (TPC * RLEN)

typedef struct Net {
  APair node_buf[G_NODE_LEN]; // global node buffer
  APort vars_buf[G_VARS_LEN]; // global vars buffer
  APair rbag_buf[G_RBAG_LEN]; // global rbag buffer
  a64 itrs; // interaction count
  a32 idle; // idle thread counter
} Net;

#define DEF_RBAG_LEN 0xFFF
#define DEF_NODE_LEN 0xFFF

// Top-Level Definition
typedef struct Def {
  char name[256];
  bool safe;
  u32  rbag_len;
  u32  node_len;
  u32  vars_len;
  Port root;
  Pair node_buf[DEF_NODE_LEN];
  Pair rbag_buf[DEF_RBAG_LEN];
} Def;

typedef struct Book Book;

// A Foreign Function
typedef struct {
  char name[256];
  Port (*func)(Net*, Book*, Port);
} FFn;

// Book of Definitions
typedef struct Book {
  u32 defs_len;
  Def defs_buf[0x4000];
  u32 ffns_len;
  FFn ffns_buf[0x4000];
} Book;

// Local Thread Memory
typedef struct TM {
  u32  tid; // thread id
  u32  itrs; // interaction count
  u32  nput; // next node allocation attempt index
  u32  vput; // next vars allocation attempt index
  u32  hput; // next hbag push index
  u32  rput; // next rbag push index
  u32  sidx; // steal index
  u32  nloc[0xFFF]; // global node allocation indices
  u32  vloc[0xFFF]; // global vars allocation indices
  Pair hbag_buf[HLEN]; // high-priority redexes
} TM;

// Debugger
// --------

typedef struct {
  char x[13];
} Show;

void put_u16(char* B, u16 val);
Show show_port(Port port);
Show show_rule(Rule rule);
void print_net(Net* net);
void pretty_print_numb(Numb word);
void pretty_print_port(Net* net, Book* book, Port port);

// Port: Constructor and Getters
// -----------------------------

static inline Port new_port(Tag tag, Val val) {
  return (val << 3) | tag;
}

static inline Tag get_tag(Port port) {
  return port & 7;
}

static inline Val get_val(Port port) {
  return port >> 3;
}

// Pair: Constructor and Getters
// -----------------------------

static inline const Pair new_pair(Port fst, Port snd) {
  return ((u64)snd << 32) | fst;
}

static inline Port get_fst(Pair pair) {
  return pair & 0xFFFFFFFF;
}

static inline Port get_snd(Pair pair) {
  return pair >> 32;
}

Pair set_par_flag(Pair pair) {
  Port p1 = get_fst(pair);
  Port p2 = get_snd(pair);
  if (get_tag(p1) == REF) {
    return new_pair(new_port(get_tag(p1), get_val(p1) | 0x10000000), p2);
  } else {
    return pair;
  }
}

Pair clr_par_flag(Pair pair) {
  Port p1 = get_fst(pair);
  Port p2 = get_snd(pair);
  if (get_tag(p1) == REF) {
    return new_pair(new_port(get_tag(p1), get_val(p1) & 0xFFFFFFF), p2);
  } else {
    return pair;
  }
}

bool get_par_flag(Pair pair) {
  Port p1 = get_fst(pair);
  if (get_tag(p1) == REF) {
    return (get_val(p1) >> 28) == 1;
  } else {
    return false;
  }
}

// Utils
// -----

// Swaps two ports.
static inline void swap(Port *a, Port *b) {
  Port x = *a; *a = *b; *b = x;
}

static inline u32 min(u32 a, u32 b) {
  return (a < b) ? a : b;
}

static inline f32 clamp(f32 x, f32 min, f32 max) {
  const f32 t = x < min ? min : x;
  return (t > max) ? max : t;
}

// A simple spin-wait barrier using atomic operations
a64 a_reached = 0; // number of threads that reached the current barrier
a64 a_barrier = 0; // number of barriers passed during this program
void sync_threads() {
  u64 barrier_old = atomic_load_explicit(&a_barrier, memory_order_relaxed);
  if (atomic_fetch_add_explicit(&a_reached, 1, memory_order_relaxed) == (TPC - 1)) {
    // Last thread to reach the barrier resets the counter and advances the barrier
    atomic_store_explicit(&a_reached, 0, memory_order_relaxed);
    atomic_store_explicit(&a_barrier, barrier_old + 1, memory_order_release);
  } else {
    u32 tries = 0;
    while (atomic_load_explicit(&a_barrier, memory_order_acquire) == barrier_old) {
      sched_yield();
    }
  }
}

// Global sum function
static a32 GLOBAL_SUM = 0;
u32 global_sum(u32 x) {
  atomic_fetch_add_explicit(&GLOBAL_SUM, x, memory_order_relaxed);
  sync_threads();
  u32 sum = atomic_load_explicit(&GLOBAL_SUM, memory_order_relaxed);
  sync_threads();
  atomic_store_explicit(&GLOBAL_SUM, 0, memory_order_relaxed);
  return sum;
}

// TODO: write a time64() function that returns the time as fast as possible as a u64
static inline u64 time64() {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (u64)ts.tv_sec * 1000000000ULL + (u64)ts.tv_nsec;
}

// Ports / Pairs / Rules
// ---------------------

// True if this port has a pointer to a node.
static inline bool is_nod(Port a) {
  return get_tag(a) >= CON;
}

// True if this port is a variable.
static inline bool is_var(Port a) {
  return get_tag(a) == VAR;
}

// Given two tags, gets their interaction rule.
static inline Rule get_rule(Port a, Port b) {
  const u8 table[8][8] = {
    //VAR  REF  ERA  NUM  CON  DUP  OPR  SWI
    {LINK,LINK,LINK,LINK,LINK,LINK,LINK,LINK}, // VAR
    {LINK,VOID,VOID,VOID,CALL,CALL,CALL,CALL}, // REF
    {LINK,VOID,VOID,VOID,ERAS,ERAS,ERAS,ERAS}, // ERA
    {LINK,VOID,VOID,VOID,ERAS,ERAS,OPER,SWIT}, // NUM
    {LINK,CALL,ERAS,ERAS,ANNI,COMM,COMM,COMM}, // CON
    {LINK,CALL,ERAS,ERAS,COMM,ANNI,COMM,COMM}, // DUP
    {LINK,CALL,ERAS,OPER,COMM,COMM,ANNI,COMM}, // OPR
    {LINK,CALL,ERAS,SWIT,COMM,COMM,COMM,ANNI}, // SWI
  };
  return table[get_tag(a)][get_tag(b)];
}

// Same as above, but receiving a pair.
static inline Rule get_pair_rule(Pair AB) {
  return get_rule(get_fst(AB), get_snd(AB));
}

// Should we swap ports A and B before reducing this rule?
static inline bool should_swap(Port A, Port B) {
  return get_tag(B) < get_tag(A);
}

// Gets a rule's priority
static inline bool is_high_priority(Rule rule) {
  // TODO: this needs to be more readable
  return (bool)((0b00011101 >> rule) & 1);
}

// Adjusts a newly allocated port.
static inline Port adjust_port(Net* net, TM* tm, Port port) {
  Tag tag = get_tag(port);
  Val val = get_val(port);
  if (is_nod(port)) return new_port(tag, tm->nloc[val]);
  if (is_var(port)) return new_port(tag, tm->vloc[val]);
  return new_port(tag, val);
}

// Adjusts a newly allocated pair.
static inline Pair adjust_pair(Net* net, TM* tm, Pair pair) {
  Port p1 = adjust_port(net, tm, get_fst(pair));
  Port p2 = adjust_port(net, tm, get_snd(pair));
  return new_pair(p1, p2);
}

// Numbs
// -----

// Constructor and getters for SYM (operation selector)
static inline Numb new_sym(u32 val) {
  return (val << 5) | TY_SYM;
}

static inline u32 get_sym(Numb word) {
  return (word >> 5);
}

// Constructor and getters for U24 (unsigned 24-bit integer)
static inline Numb new_u24(u32 val) {
  return (val << 5) | TY_U24;
}

static inline u32 get_u24(Numb word) {
  return word >> 5;
}

// Constructor and getters for I24 (signed 24-bit integer)
static inline Numb new_i24(i32 val) {
  return ((u32)val << 5) | TY_I24;
}

static inline i32 get_i24(Numb word) {
  return ((i32)word) << 3 >> 8;
}

// Constructor and getters for F24 (24-bit float)
static inline Numb new_f24(float val) {
  u32 bits = *(u32*)&val;
  u32 shifted_bits = bits >> 8;
  u32 lost_bits = bits & 0xFF;
  // round ties to even
  shifted_bits += (!isnan(val)) & ((lost_bits - ((lost_bits >> 7) & !shifted_bits)) >> 7);
  // ensure NaNs don't become infinities
  shifted_bits |= isnan(val);
  return (shifted_bits << 5) | TY_F24;
}

static inline float get_f24(Numb word) {
  u32 bits = (word << 3) & 0xFFFFFF00;
  return *(float*)&bits;
}

// Flip flag
static inline Tag get_typ(Numb word) {
  return word & 0x1F;
}

static inline bool is_num(Numb word) {
  return get_typ(word) >= TY_U24 && get_typ(word) <= TY_F24;
}

static inline bool is_cast(Numb word) {
  return get_typ(word) == TY_SYM && get_sym(word) >= TY_U24 && get_sym(word) <= TY_F24;
}

// Partial application
static inline Numb partial(Numb a, Numb b) {
  return (b & ~0x1F) | get_sym(a);
}

// Cast a number to another type.
// The semantics are meant to spiritually resemble rust's numeric casts:
// - i24 <-> u24: is just reinterpretation of bits
// - f24  -> i24,
//   f24  -> u24: casts to the "closest" integer representing this float,
//                saturating if out of range and 0 if NaN
// - i24  -> f24,
//   u24  -> f24: casts to the "closest" float representing this integer.
static inline Numb cast(Numb a, Numb b) {
  if (get_sym(a) == TY_U24 && get_typ(b) == TY_U24) return b;
  if (get_sym(a) == TY_U24 && get_typ(b) == TY_I24) {
    // reinterpret bits
    i32 val = get_i24(b);
    return new_u24(*(u32*) &val);
  }
  if (get_sym(a) == TY_U24 && get_typ(b) == TY_F24) {
    f32 val = get_f24(b);
    if (isnan(val)) {
      return new_u24(0);
    }
    return new_u24((u32) clamp(val, U24_MIN, U24_MAX));
  }

  if (get_sym(a) == TY_I24 && get_typ(b) == TY_U24) {
    // reinterpret bits
    u32 val = get_u24(b);
    return new_i24(*(i32*) &val);
  }
  if (get_sym(a) == TY_I24 && get_typ(b) == TY_I24) return b;
  if (get_sym(a) == TY_I24 && get_typ(b) == TY_F24) {
    f32 val = get_f24(b);
    if (isnan(val)) {
      return new_i24(0);
    }
    return new_i24((i32) clamp(val, I24_MIN, I24_MAX));
  }

  if (get_sym(a) == TY_F24 && get_typ(b) == TY_U24) return new_f24((f32) get_u24(b));
  if (get_sym(a) == TY_F24 && get_typ(b) == TY_I24) return new_f24((f32) get_i24(b));
  if (get_sym(a) == TY_F24 && get_typ(b) == TY_F24) return b;

  return new_u24(0);
}

// Operate function
static inline Numb operate(Numb a, Numb b) {
  Tag at = get_typ(a);
  Tag bt = get_typ(b);
  if (at == TY_SYM && bt == TY_SYM) {
    return new_u24(0);
  }
  if (is_cast(a) && is_num(b)) {
    return cast(a, b);
  }
  if (is_cast(b) && is_num(a)) {
    return cast(b, a);
  }
  if (at == TY_SYM && bt != TY_SYM) {
    return partial(a, b);
  }
  if (at != TY_SYM && bt == TY_SYM) {
    return partial(b, a);
  }
  if (at >= OP_ADD && bt >= OP_ADD) {
    return new_u24(0);
  }
  if (at < OP_ADD && bt < OP_ADD) {
    return new_u24(0);
  }
  Tag op, ty;
  Numb swp;
  if (at >= OP_ADD) {
    op = at; ty = bt;
  } else {
    op = bt; ty = at; swp = a; a = b; b = swp;
  }
  switch (ty) {
    case TY_U24: {
      u32 av = get_u24(a);
      u32 bv = get_u24(b);
      switch (op) {
        case OP_ADD: return new_u24(av + bv);
        case OP_SUB: return new_u24(av - bv);
        case FP_SUB: return new_u24(bv - av);
        case OP_MUL: return new_u24(av * bv);
        case OP_DIV: return new_u24(av / bv);
        case FP_DIV: return new_u24(bv / av);
        case OP_REM: return new_u24(av % bv);
        case FP_REM: return new_u24(bv % av);
        case OP_EQ:  return new_u24(av == bv);
        case OP_NEQ: return new_u24(av != bv);
        case OP_LT:  return new_u24(av < bv);
        case OP_GT:  return new_u24(av > bv);
        case OP_AND: return new_u24(av & bv);
        case OP_OR:  return new_u24(av | bv);
        case OP_XOR: return new_u24(av ^ bv);
        case OP_SHL: return new_u24(av << (bv & 31));
        case FP_SHL: return new_u24(bv << (av & 31));
        case OP_SHR: return new_u24(av >> (bv & 31));
        case FP_SHR: return new_u24(bv >> (av & 31));
        default:     return new_u24(0);
      }
    }
    case TY_I24: {
      i32 av = get_i24(a);
      i32 bv = get_i24(b);
      switch (op) {
        case OP_ADD: return new_i24(av + bv);
        case OP_SUB: return new_i24(av - bv);
        case FP_SUB: return new_i24(bv - av);
        case OP_MUL: return new_i24(av * bv);
        case OP_DIV: return new_i24(av / bv);
        case FP_DIV: return new_i24(bv / av);
        case OP_REM: return new_i24(av % bv);
        case FP_REM: return new_i24(bv % av);
        case OP_EQ:  return new_u24(av == bv);
        case OP_NEQ: return new_u24(av != bv);
        case OP_LT:  return new_u24(av < bv);
        case OP_GT:  return new_u24(av > bv);
        case OP_AND: return new_i24(av & bv);
        case OP_OR:  return new_i24(av | bv);
        case OP_XOR: return new_i24(av ^ bv);
        default:     return new_i24(0);
      }
    }
    case TY_F24: {
      float av = get_f24(a);
      float bv = get_f24(b);
      switch (op) {
        case OP_ADD: return new_f24(av + bv);
        case OP_SUB: return new_f24(av - bv);
        case FP_SUB: return new_f24(bv - av);
        case OP_MUL: return new_f24(av * bv);
        case OP_DIV: return new_f24(av / bv);
        case FP_DIV: return new_f24(bv / av);
        case OP_REM: return new_f24(fmodf(av, bv));
        case FP_REM: return new_f24(fmodf(bv, av));
        case OP_EQ:  return new_u24(av == bv);
        case OP_NEQ: return new_u24(av != bv);
        case OP_LT:  return new_u24(av < bv);
        case OP_GT:  return new_u24(av > bv);
        case OP_AND: return new_f24(atan2f(av, bv));
        case OP_OR:  return new_f24(logf(bv) / logf(av));
        case OP_XOR: return new_f24(powf(av, bv));
        case OP_SHL: return new_f24(sin(av + bv));
        case OP_SHR: return new_f24(tan(av + bv));
        default:     return new_f24(0);
      }
    }
    default: return new_u24(0);
  }
}

// RBag
// ----

// FIXME: what about some bound checks?

static inline void push_redex(Net* net, TM* tm, Pair redex) {
  #ifdef DEBUG
  bool free_local = tm->hput < HLEN;
  bool free_global = tm->rput < RLEN;
  if (!free_global || !free_local) {
    debug("push_redex: limited resources, maybe corrupting memory\n");
  }
  #endif

  if (is_high_priority(get_pair_rule(redex))) {
    tm->hbag_buf[tm->hput++] = redex;
  } else {
    atomic_store_explicit(&net->rbag_buf[tm->tid*(G_RBAG_LEN/TPC) + (tm->rput++)], redex, memory_order_relaxed);
  }
}

static inline Pair pop_redex(Net* net, TM* tm) {
  if (tm->hput > 0) {
    return tm->hbag_buf[--tm->hput];
  } else if (tm->rput > 0) {
    return atomic_exchange_explicit(&net->rbag_buf[tm->tid*(G_RBAG_LEN/TPC) + (--tm->rput)], 0, memory_order_relaxed);
  } else {
    return 0;
  }
}

static inline u32 rbag_len(Net* net, TM* tm) {
  return tm->rput + tm->hput;
}

// TM
// --

static TM* tm[TPC];

TM* tm_new(u32 tid) {
  TM* tm   = malloc(sizeof(TM));
  tm->tid  = tid;
  tm->itrs = 0;
  tm->nput = 1;
  tm->vput = 1;
  tm->rput = 0;
  tm->hput = 0;
  tm->sidx = 0;
  return tm;
}

void alloc_static_tms() {
  for (u32 t = 0; t < TPC; ++t) {
    tm[t] = tm_new(t);
  }
}

void free_static_tms() {
  for (u32 t = 0; t < TPC; ++t) {
    free(tm[t]);
  }
}

// Net
// ----

// Stores a new node on global.
static inline void node_create(Net* net, u32 loc, Pair val) {
  atomic_store_explicit(&net->node_buf[loc], val, memory_order_relaxed);
}

// Stores a var on global.
static inline void vars_create(Net* net, u32 var, Port val) {
  atomic_store_explicit(&net->vars_buf[var], val, memory_order_relaxed);
}

// Reads a node from global.
static inline Pair node_load(Net* net, u32 loc) {
  return atomic_load_explicit(&net->node_buf[loc], memory_order_relaxed);
}

// Reads a var from global.
static inline Port vars_load(Net* net, u32 var) {
  return atomic_load_explicit(&net->vars_buf[var], memory_order_relaxed);
}

// Stores a node on global.
static inline void node_store(Net* net, u32 loc, Pair val) {
  atomic_store_explicit(&net->node_buf[loc], val, memory_order_relaxed);
}

// Exchanges a node on global by a value. Returns old.
static inline Pair node_exchange(Net* net, u32 loc, Pair val) {
  return atomic_exchange_explicit(&net->node_buf[loc], val, memory_order_relaxed);
}

// Exchanges a var on global by a value. Returns old.
static inline Port vars_exchange(Net* net, u32 var, Port val) {
  return atomic_exchange_explicit(&net->vars_buf[var], val, memory_order_relaxed);
}

// Takes a node.
static inline Pair node_take(Net* net, u32 loc) {
  return node_exchange(net, loc, 0);
}

// Takes a var.
static inline Port vars_take(Net* net, u32 var) {
  return vars_exchange(net, var, 0);
}


// Net
// ---

// Initializes a net.
static inline Net* net_new() {
  Net* net = calloc(1, sizeof(Net));

  atomic_store(&net->itrs, 0);
  atomic_store(&net->idle, 0);

  return net;
}

// Allocator
// ---------

u32 node_alloc_1(Net* net, TM* tm, u32* lps) {
  while (true) {
    u32 lc = tm->tid*(G_NODE_LEN/TPC) + (tm->nput%(G_NODE_LEN/TPC));
    Pair elem = net->node_buf[lc];
    tm->nput += 1;
    if (lc > 0 && elem == 0) {
      return lc;
    }
    // FIXME: check this decently
    if (++(*lps) >= G_NODE_LEN/TPC) printf("OOM\n");
  }
}

u32 vars_alloc_1(Net* net, TM* tm, u32* lps) {
  while (true) {
    u32 lc = tm->tid*(G_NODE_LEN/TPC) + (tm->vput%(G_NODE_LEN/TPC));
    Port elem = net->vars_buf[lc];
    tm->vput += 1;
    if (lc > 0 && elem == 0) {
      return lc;
    }
    // FIXME: check this decently
    if (++(*lps) >= G_NODE_LEN/TPC) printf("OOM\n");
  }
}

u32 node_alloc(Net* net, TM* tm, u32 num) {
  u32 got = 0;
  u32 lps = 0;
  while (got < num) {
    u32 lc = tm->tid*(G_NODE_LEN/TPC) + (tm->nput%(G_NODE_LEN/TPC));
    Pair elem = net->node_buf[lc];
    tm->nput += 1;
    if (lc > 0 && elem == 0) {
      tm->nloc[got++] = lc;
    }
    // FIXME: check this decently
    if (++lps >= G_NODE_LEN/TPC) printf("OOM\n");
  }
  return got;
}

u32 vars_alloc(Net* net, TM* tm, u32 num) {
  u32 got = 0;
  u32 lps = 0;
  while (got < num) {
    u32 lc = tm->tid*(G_NODE_LEN/TPC) + (tm->vput%(G_NODE_LEN/TPC));
    Port elem = net->vars_buf[lc];
    tm->vput += 1;
    if (lc > 0 && elem == 0) {
      tm->vloc[got++] = lc;
    }
    // FIXME: check this decently
    if (++lps >= G_NODE_LEN/TPC) printf("OOM\n");
  }
  return got;
}

// Gets the necessary resources for an interaction. Returns success.
static inline bool get_resources(Net* net, TM* tm, u32 need_rbag, u32 need_node, u32 need_vars) {
  u32 got_rbag = min(RLEN - tm->rput, HLEN - tm->hput);
  u32 got_node = node_alloc(net, tm, need_node);
  u32 got_vars = vars_alloc(net, tm, need_vars);

  return got_rbag >= need_rbag && got_node >= need_node && got_vars >= need_vars;
}

// Linking
// -------

// Peeks a variable's final target without modifying it.
static inline Port peek(Net* net, Port var) {
  while (get_tag(var) == VAR) {
    Port val = vars_load(net, get_val(var));
    if (val == NONE) break;
    if (val == 0) break;
    var = val;
  }
  return var;
}

// Finds a variable's value.
static inline Port enter(Net* net, Port var) {
  // While `B` is VAR: extend it (as an optimization)
  while (get_tag(var) == VAR) {
    // Takes the current `var` substitution as `val`
    Port val = vars_exchange(net, get_val(var), NONE);
    // If there was no `val`, stop, as there is no extension
    if (val == NONE || val == 0) {
      break;
    }
    // Otherwise, delete `B` (we own both) and continue
    vars_take(net, get_val(var));
    var = val;
  }
  return var;
}

// Atomically Links `A ~ B`.
static inline void link(Net* net, TM* tm, Port A, Port B) {
  // Attempts to directionally point `A ~> B`
  while (true) {
    // If `A` is NODE: swap `A` and `B`, and continue
    if (get_tag(A) != VAR && get_tag(B) == VAR) {
      Port X = A; A = B; B = X;
    }

    // If `A` is NODE: create the `A ~ B` redex
    if (get_tag(A) != VAR) {
      push_redex(net, tm, new_pair(A, B)); // TODO: move global ports to local
      break;
    }

    // Extends B (as an optimization)
    B = enter(net, B);

    // Since `A` is VAR: point `A ~> B`.
    // Stores `A -> B`, taking the current `A` subst as `A'`
    Port A_ = vars_exchange(net, get_val(A), B);
    // If there was no `A'`, stop, as we lost B's ownership
    if (A_ == NONE) {
      break;
    }
    //if (A_ == 0) { ? } // FIXME: must handle on the move-to-global algo
    // Otherwise, delete `A` (we own both) and link `A' ~ B`
    vars_take(net, get_val(A));
    A = A_;
  }
}

// Links `A ~ B` (as a pair).
static inline void link_pair(Net* net, TM* tm, Pair AB) {
  link(net, tm, get_fst(AB), get_snd(AB));
}

// Interactions
// ------------

// The Link Interaction.
static inline bool interact_link(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 1, 0, 0)) {
    debug("interact_link: get_resources failed\n");
    return false;
  }

  // Links.
  link_pair(net, tm, new_pair(a, b));

  return true;
}

// Declared here for use in call interactions.
static inline bool interact_eras(Net* net, TM* tm, Port a, Port b);

// The Call Interaction.
#ifdef COMPILED
bool interact_call_main(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  if (b != NONE) {
    link(net, tm, new_port(VAR,v0), b);
  } else {
    b = new_port(VAR,v0);
  }
  node_create(net, n2, new_pair(new_port(NUM,0x07506243),new_port(VAR,v0)));
  node_create(net, n1, new_pair(new_port(NUM,0x00186a01),new_port(CON,n2)));
  node_create(net, n0, new_pair(new_port(REF,0x0000002f),new_port(CON,n1)));
  link(net, tm, new_port(REF,0x00000036), new_port(CON,n0));
  return true;
}

bool interact_call_List_Cons(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  if (k12 != NONE) {
    link(net, tm, new_port(VAR,v2), k12);
  } else {
    k12 = new_port(VAR,v2);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k11) == CON && node_load(net, get_val(k11)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k11));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  if (k24 != NONE) {
    link(net, tm, new_port(VAR,v2), k24);
  } else {
    k24 = new_port(VAR,v2);
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v1), k23);
  } else {
    k23 = new_port(VAR,v1);
  }
  if (!k21) {
    node_create(net, n5, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n5), k20);
    } else {
      k20 = new_port(CON,n5);
    }
  }
  if (k19 != NONE) {
    link(net, tm, new_port(VAR,v0), k19);
  } else {
    k19 = new_port(VAR,v0);
  }
  if (!k17) {
    node_create(net, n4, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,n4), k16);
    } else {
      k16 = new_port(CON,n4);
    }
  }
  if (k15 != NONE) {
    link(net, tm, new_port(REF,0x00000002), k15);
  } else {
    k15 = new_port(REF,0x00000002);
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k11 != NONE) {
      link(net, tm, new_port(CON,n3), k11);
    } else {
      k11 = new_port(CON,n3);
    }
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_List_Cons_tag(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  if (0) {
    return false;
  }
  // fast void
  if (get_tag(b) == ERA || get_tag(b) == NUM) {
    tm->itrs += 1;
  } else {
    if (b != NONE) {
      link(net, tm, new_port(NUM,0x00000021), b);
    } else {
      b = new_port(NUM,0x00000021);
    }
  }
  return true;
}

bool interact_call_List_Nil(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x00000004), k7);
  } else {
    k7 = new_port(REF,0x00000004);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_List_Nil_tag(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  if (0) {
    return false;
  }
  // fast void
  if (get_tag(b) == ERA || get_tag(b) == NUM) {
    tm->itrs += 1;
  } else {
    if (b != NONE) {
      link(net, tm, new_port(NUM,0x00000001), b);
    } else {
      b = new_port(NUM,0x00000001);
    }
  }
  return true;
}

bool interact_call_Map_Leaf(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x00000006), k7);
  } else {
    k7 = new_port(REF,0x00000006);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_Map_Leaf_tag(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  if (0) {
    return false;
  }
  // fast void
  if (get_tag(b) == ERA || get_tag(b) == NUM) {
    tm->itrs += 1;
  } else {
    if (b != NONE) {
      link(net, tm, new_port(NUM,0x00000021), b);
    } else {
      b = new_port(NUM,0x00000021);
    }
  }
  return true;
}

bool interact_call_Map_Node(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v3), k16);
  } else {
    k16 = new_port(VAR,v3);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k15) == CON && node_load(net, get_val(k15)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k15));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  bool k25 = 0;
  Pair k26 = 0;
  Port k27 = NONE;
  Port k28 = NONE;
  // fast anni
  if (get_tag(k24) == CON && node_load(net, get_val(k24)) != 0) {
    tm->itrs += 1;
    k25 = 1;
    k26 = node_take(net, get_val(k24));
    k27 = get_fst(k26);
    k28 = get_snd(k26);
  }
  bool k29 = 0;
  Pair k30 = 0;
  Port k31 = NONE;
  Port k32 = NONE;
  // fast anni
  if (get_tag(k28) == CON && node_load(net, get_val(k28)) != 0) {
    tm->itrs += 1;
    k29 = 1;
    k30 = node_take(net, get_val(k28));
    k31 = get_fst(k30);
    k32 = get_snd(k30);
  }
  if (k32 != NONE) {
    link(net, tm, new_port(VAR,v3), k32);
  } else {
    k32 = new_port(VAR,v3);
  }
  if (k31 != NONE) {
    link(net, tm, new_port(VAR,v2), k31);
  } else {
    k31 = new_port(VAR,v2);
  }
  if (!k29) {
    node_create(net, n7, new_pair(k31,k32));
    if (k28 != NONE) {
      link(net, tm, new_port(CON,n7), k28);
    } else {
      k28 = new_port(CON,n7);
    }
  }
  if (k27 != NONE) {
    link(net, tm, new_port(VAR,v1), k27);
  } else {
    k27 = new_port(VAR,v1);
  }
  if (!k25) {
    node_create(net, n6, new_pair(k27,k28));
    if (k24 != NONE) {
      link(net, tm, new_port(CON,n6), k24);
    } else {
      k24 = new_port(CON,n6);
    }
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v0), k23);
  } else {
    k23 = new_port(VAR,v0);
  }
  if (!k21) {
    node_create(net, n5, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n5), k20);
    } else {
      k20 = new_port(CON,n5);
    }
  }
  if (k19 != NONE) {
    link(net, tm, new_port(REF,0x00000008), k19);
  } else {
    k19 = new_port(REF,0x00000008);
  }
  if (!k17) {
    node_create(net, n4, new_pair(k19,k20));
    if (k15 != NONE) {
      link(net, tm, new_port(CON,n4), k15);
    } else {
      k15 = new_port(CON,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_Map_Node_tag(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  if (0) {
    return false;
  }
  // fast void
  if (get_tag(b) == ERA || get_tag(b) == NUM) {
    tm->itrs += 1;
  } else {
    if (b != NONE) {
      link(net, tm, new_port(NUM,0x00000001), b);
    } else {
      b = new_port(NUM,0x00000001);
    }
  }
  return true;
}

bool interact_call_Map_empty(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  if (0) {
    return false;
  }
  if (b != NONE) {
    link(net, tm, new_port(REF,0x00000005), b);
  } else {
    b = new_port(REF,0x00000005);
  }
  return true;
}

bool interact_call_Map_set(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x0000000d), k7);
  } else {
    k7 = new_port(REF,0x0000000d);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_Map_set__C0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v4), k16);
  } else {
    k16 = new_port(VAR,v4);
  }
  if (k15 != NONE) {
    link(net, tm, new_port(VAR,v3), k15);
  } else {
    k15 = new_port(VAR,v3);
  }
  if (!k13) {
    node_create(net, n4, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n4), k12);
    } else {
      k12 = new_port(CON,n4);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n3, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n3), k8);
    } else {
      k8 = new_port(CON,n3);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n2, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n2), k4);
    } else {
      k4 = new_port(CON,n2);
    }
  }
  bool k17 = 0;
  Port k18 = NONE;
  // fast oper
  if (get_tag(k3) == NUM && get_tag(new_port(NUM,0x00000049)) == NUM) {
    tm->itrs += 1;
    k17 = 1;
    k18 = new_port(NUM, operate(get_val(k3), get_val(new_port(NUM,0x00000049))));
  }
  if (k18 != NONE) {
    link(net, tm, new_port(VAR,v0), k18);
  } else {
    k18 = new_port(VAR,v0);
  }
  if (!k17) {
    node_create(net, n1, new_pair(new_port(NUM,0x00000049),k18));
    if (k3 != NONE) {
      link(net, tm, new_port(OPR, n1), k3);
    } else {
      k3 = new_port(OPR, n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n6, new_pair(new_port(VAR,v5),new_port(VAR,v4)));
  node_create(net, n5, new_pair(new_port(VAR,v2),new_port(CON,n6)));
  link(net, tm, new_port(REF,0x00000007), new_port(CON,n5));
  node_create(net, n9, new_pair(new_port(VAR,v1),new_port(VAR,v5)));
  node_create(net, n8, new_pair(new_port(VAR,v0),new_port(CON,n9)));
  node_create(net, n7, new_pair(new_port(VAR,v3),new_port(CON,n8)));
  link(net, tm, new_port(REF,0x0000000a), new_port(CON,n7));
  return true;
}

bool interact_call_Map_set__C1(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  if (k24 != NONE) {
    link(net, tm, new_port(VAR,v5), k24);
  } else {
    k24 = new_port(VAR,v5);
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v4), k23);
  } else {
    k23 = new_port(VAR,v4);
  }
  if (!k21) {
    node_create(net, n6, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n6), k20);
    } else {
      k20 = new_port(CON,n6);
    }
  }
  if (k19 != NONE) {
    link(net, tm, new_port(VAR,v3), k19);
  } else {
    k19 = new_port(VAR,v3);
  }
  if (!k17) {
    node_create(net, n5, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,n5), k16);
    } else {
      k16 = new_port(CON,n5);
    }
  }
  if (k15 != NONE) {
    link(net, tm, new_port(VAR,v2), k15);
  } else {
    k15 = new_port(VAR,v2);
  }
  if (!k13) {
    node_create(net, n4, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n4), k12);
    } else {
      k12 = new_port(CON,n4);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v1), k11);
  } else {
    k11 = new_port(VAR,v1);
  }
  if (!k9) {
    node_create(net, n3, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n3), k8);
    } else {
      k8 = new_port(CON,n3);
    }
  }
  bool k25 = 0;
  Port k26 = NONE;
  // fast oper
  if (get_tag(k7) == NUM && get_tag(new_port(NUM,0x00000049)) == NUM) {
    tm->itrs += 1;
    k25 = 1;
    k26 = new_port(NUM, operate(get_val(k7), get_val(new_port(NUM,0x00000049))));
  }
  if (k26 != NONE) {
    link(net, tm, new_port(VAR,v0), k26);
  } else {
    k26 = new_port(VAR,v0);
  }
  if (!k25) {
    node_create(net, n2, new_pair(new_port(NUM,0x00000049),k26));
    if (k7 != NONE) {
      link(net, tm, new_port(OPR, n2), k7);
    } else {
      k7 = new_port(OPR, n2);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  // fast void
  if (get_tag(k3) == ERA || get_tag(k3) == NUM) {
    tm->itrs += 1;
  } else {
    if (k3 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k3);
    } else {
      k3 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n9, new_pair(new_port(VAR,v6),new_port(VAR,v5)));
  node_create(net, n8, new_pair(new_port(VAR,v3),new_port(CON,n9)));
  node_create(net, n7, new_pair(new_port(VAR,v2),new_port(CON,n8)));
  link(net, tm, new_port(REF,0x00000007), new_port(CON,n7));
  node_create(net, nc, new_pair(new_port(VAR,v1),new_port(VAR,v6)));
  node_create(net, nb, new_pair(new_port(VAR,v0),new_port(CON,nc)));
  node_create(net, na, new_pair(new_port(VAR,v4),new_port(CON,nb)));
  link(net, tm, new_port(REF,0x0000000a), new_port(CON,na));
  return true;
}

bool interact_call_Map_set__C10(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x00000014), k3);
  } else {
    k3 = new_port(REF,0x00000014);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(REF,0x00000015), k4);
  } else {
    k4 = new_port(REF,0x00000015);
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_Map_set__C2(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v1), k4);
  } else {
    k4 = new_port(VAR,v1);
  }
  bool k5 = 0;
  Port k6 = NONE;
  Port k7 = NONE;
  // fast copy
  if (get_tag(k3) == NUM) {
    tm->itrs += 1;
    k5 = 1;
    k6 = k3;
    k7 = k3;
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v0), k7);
  } else {
    k7 = new_port(VAR,v0);
  }
  bool k8 = 0;
  Port k9 = NONE;
  // fast oper
  if (get_tag(k6) == NUM && get_tag(new_port(NUM,0x0000004b)) == NUM) {
    tm->itrs += 1;
    k8 = 1;
    k9 = new_port(NUM, operate(get_val(k6), get_val(new_port(NUM,0x0000004b))));
  }
  node_create(net, n4, new_pair(new_port(REF,0x0000000b),new_port(REF,0x0000000c)));
  node_create(net, n5, new_pair(new_port(VAR,v0),new_port(VAR,v1)));
  node_create(net, n3, new_pair(new_port(CON,n4),new_port(CON,n5)));
  if (k9 != NONE) {
    link(net, tm, new_port(SWI,n3), k9);
  } else {
    k9 = new_port(SWI,n3);
  }
  if (!k8) {
    node_create(net, n2, new_pair(new_port(NUM,0x0000004b),k9));
    if (k6 != NONE) {
      link(net, tm, new_port(OPR, n2), k6);
    } else {
      k6 = new_port(OPR, n2);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k6,k7));
    if (k3 != NONE) {
      link(net, tm, new_port(DUP,n1), k3);
    } else {
      k3 = new_port(DUP,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_Map_set__C3(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !n0 || !n1 || !n2 || !n3 || !n4) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v1), k16);
  } else {
    k16 = new_port(VAR,v1);
  }
  // fast void
  if (get_tag(k15) == ERA || get_tag(k15) == NUM) {
    tm->itrs += 1;
  } else {
    if (k15 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k15);
    } else {
      k15 = new_port(ERA,0x00000000);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v0), k11);
  } else {
    k11 = new_port(VAR,v0);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  // fast void
  if (get_tag(k7) == ERA || get_tag(k7) == NUM) {
    tm->itrs += 1;
  } else {
    if (k7 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k7);
    } else {
      k7 = new_port(ERA,0x00000000);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  // fast void
  if (get_tag(k3) == ERA || get_tag(k3) == NUM) {
    tm->itrs += 1;
  } else {
    if (k3 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k3);
    } else {
      k3 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n4, new_pair(new_port(VAR,v0),new_port(VAR,v1)));
  link(net, tm, new_port(REF,0x00000007), new_port(CON,n4));
  return true;
}

bool interact_call_Map_set__C4(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v2), k8);
  } else {
    k8 = new_port(VAR,v2);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n2, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n2), k4);
    } else {
      k4 = new_port(CON,n2);
    }
  }
  bool k9 = 0;
  Port k10 = NONE;
  // fast oper
  if (get_tag(k3) == NUM && get_tag(new_port(NUM,0x00000049)) == NUM) {
    tm->itrs += 1;
    k9 = 1;
    k10 = new_port(NUM, operate(get_val(k3), get_val(new_port(NUM,0x00000049))));
  }
  if (k10 != NONE) {
    link(net, tm, new_port(VAR,v0), k10);
  } else {
    k10 = new_port(VAR,v0);
  }
  if (!k9) {
    node_create(net, n1, new_pair(new_port(NUM,0x00000049),k10));
    if (k3 != NONE) {
      link(net, tm, new_port(OPR, n1), k3);
    } else {
      k3 = new_port(OPR, n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n5, new_pair(new_port(REF,0x00000005),new_port(VAR,v2)));
  node_create(net, n4, new_pair(new_port(VAR,v3),new_port(CON,n5)));
  node_create(net, n3, new_pair(new_port(REF,0x0000003d),new_port(CON,n4)));
  link(net, tm, new_port(REF,0x00000007), new_port(CON,n3));
  node_create(net, n8, new_pair(new_port(VAR,v1),new_port(VAR,v3)));
  node_create(net, n7, new_pair(new_port(VAR,v0),new_port(CON,n8)));
  node_create(net, n6, new_pair(new_port(REF,0x00000005),new_port(CON,n7)));
  link(net, tm, new_port(REF,0x0000000a), new_port(CON,n6));
  return true;
}

bool interact_call_Map_set__C5(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  if (k12 != NONE) {
    link(net, tm, new_port(VAR,v2), k12);
  } else {
    k12 = new_port(VAR,v2);
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v1), k11);
  } else {
    k11 = new_port(VAR,v1);
  }
  if (!k9) {
    node_create(net, n3, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n3), k8);
    } else {
      k8 = new_port(CON,n3);
    }
  }
  bool k13 = 0;
  Port k14 = NONE;
  // fast oper
  if (get_tag(k7) == NUM && get_tag(new_port(NUM,0x00000049)) == NUM) {
    tm->itrs += 1;
    k13 = 1;
    k14 = new_port(NUM, operate(get_val(k7), get_val(new_port(NUM,0x00000049))));
  }
  if (k14 != NONE) {
    link(net, tm, new_port(VAR,v0), k14);
  } else {
    k14 = new_port(VAR,v0);
  }
  if (!k13) {
    node_create(net, n2, new_pair(new_port(NUM,0x00000049),k14));
    if (k7 != NONE) {
      link(net, tm, new_port(OPR, n2), k7);
    } else {
      k7 = new_port(OPR, n2);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  // fast void
  if (get_tag(k3) == ERA || get_tag(k3) == NUM) {
    tm->itrs += 1;
  } else {
    if (k3 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k3);
    } else {
      k3 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n6, new_pair(new_port(VAR,v3),new_port(VAR,v2)));
  node_create(net, n5, new_pair(new_port(REF,0x00000005),new_port(CON,n6)));
  node_create(net, n4, new_pair(new_port(REF,0x0000003d),new_port(CON,n5)));
  link(net, tm, new_port(REF,0x00000007), new_port(CON,n4));
  node_create(net, n9, new_pair(new_port(VAR,v1),new_port(VAR,v3)));
  node_create(net, n8, new_pair(new_port(VAR,v0),new_port(CON,n9)));
  node_create(net, n7, new_pair(new_port(REF,0x00000005),new_port(CON,n8)));
  link(net, tm, new_port(REF,0x0000000a), new_port(CON,n7));
  return true;
}

bool interact_call_Map_set__C6(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v1), k4);
  } else {
    k4 = new_port(VAR,v1);
  }
  bool k5 = 0;
  Port k6 = NONE;
  Port k7 = NONE;
  // fast copy
  if (get_tag(k3) == NUM) {
    tm->itrs += 1;
    k5 = 1;
    k6 = k3;
    k7 = k3;
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v0), k7);
  } else {
    k7 = new_port(VAR,v0);
  }
  bool k8 = 0;
  Port k9 = NONE;
  // fast oper
  if (get_tag(k6) == NUM && get_tag(new_port(NUM,0x0000004b)) == NUM) {
    tm->itrs += 1;
    k8 = 1;
    k9 = new_port(NUM, operate(get_val(k6), get_val(new_port(NUM,0x0000004b))));
  }
  node_create(net, n4, new_pair(new_port(REF,0x00000010),new_port(REF,0x00000011)));
  node_create(net, n5, new_pair(new_port(VAR,v0),new_port(VAR,v1)));
  node_create(net, n3, new_pair(new_port(CON,n4),new_port(CON,n5)));
  if (k9 != NONE) {
    link(net, tm, new_port(SWI,n3), k9);
  } else {
    k9 = new_port(SWI,n3);
  }
  if (!k8) {
    node_create(net, n2, new_pair(new_port(NUM,0x0000004b),k9));
    if (k6 != NONE) {
      link(net, tm, new_port(OPR, n2), k6);
    } else {
      k6 = new_port(OPR, n2);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k6,k7));
    if (k3 != NONE) {
      link(net, tm, new_port(DUP,n1), k3);
    } else {
      k3 = new_port(DUP,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_Map_set__C7(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  if (k12 != NONE) {
    link(net, tm, new_port(VAR,v1), k12);
  } else {
    k12 = new_port(VAR,v1);
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v0), k11);
  } else {
    k11 = new_port(VAR,v0);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  // fast void
  if (get_tag(k7) == ERA || get_tag(k7) == NUM) {
    tm->itrs += 1;
  } else {
    if (k7 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k7);
    } else {
      k7 = new_port(ERA,0x00000000);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  // fast void
  if (get_tag(k3) == ERA || get_tag(k3) == NUM) {
    tm->itrs += 1;
  } else {
    if (k3 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k3);
    } else {
      k3 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n5, new_pair(new_port(REF,0x00000005),new_port(VAR,v1)));
  node_create(net, n4, new_pair(new_port(REF,0x00000005),new_port(CON,n5)));
  node_create(net, n3, new_pair(new_port(VAR,v0),new_port(CON,n4)));
  link(net, tm, new_port(REF,0x00000007), new_port(CON,n3));
  return true;
}

bool interact_call_Map_set__C8(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  if (k20 != NONE) {
    link(net, tm, new_port(VAR,v6), k20);
  } else {
    k20 = new_port(VAR,v6);
  }
  if (k19 != NONE) {
    link(net, tm, new_port(VAR,v5), k19);
  } else {
    k19 = new_port(VAR,v5);
  }
  if (!k17) {
    node_create(net, n5, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,n5), k16);
    } else {
      k16 = new_port(CON,n5);
    }
  }
  bool k21 = 0;
  Port k22 = NONE;
  Port k23 = NONE;
  // fast copy
  if (get_tag(k15) == NUM) {
    tm->itrs += 1;
    k21 = 1;
    k22 = k15;
    k23 = k15;
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v4), k23);
  } else {
    k23 = new_port(VAR,v4);
  }
  if (k22 != NONE) {
    link(net, tm, new_port(VAR,v3), k22);
  } else {
    k22 = new_port(VAR,v3);
  }
  if (!k21) {
    node_create(net, n4, new_pair(k22,k23));
    if (k15 != NONE) {
      link(net, tm, new_port(DUP,n4), k15);
    } else {
      k15 = new_port(DUP,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n8, new_pair(new_port(REF,0x0000000e),new_port(REF,0x0000000f)));
  node_create(net, nd, new_pair(new_port(VAR,v2),new_port(VAR,v6)));
  node_create(net, nc, new_pair(new_port(VAR,v1),new_port(CON,nd)));
  node_create(net, nb, new_pair(new_port(VAR,v0),new_port(CON,nc)));
  node_create(net, na, new_pair(new_port(VAR,v5),new_port(CON,nb)));
  node_create(net, n9, new_pair(new_port(VAR,v4),new_port(CON,na)));
  node_create(net, n7, new_pair(new_port(CON,n8),new_port(CON,n9)));
  node_create(net, n6, new_pair(new_port(VAR,v3),new_port(SWI,n7)));
  link(net, tm, new_port(OPR,n6), new_port(NUM,0x0000000c));
  return true;
}

bool interact_call_Map_set__C9(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v2), k8);
  } else {
    k8 = new_port(VAR,v2);
  }
  bool k9 = 0;
  Port k10 = NONE;
  Port k11 = NONE;
  // fast copy
  if (get_tag(k7) == NUM) {
    tm->itrs += 1;
    k9 = 1;
    k10 = k7;
    k11 = k7;
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v1), k11);
  } else {
    k11 = new_port(VAR,v1);
  }
  if (k10 != NONE) {
    link(net, tm, new_port(VAR,v0), k10);
  } else {
    k10 = new_port(VAR,v0);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k10,k11));
    if (k7 != NONE) {
      link(net, tm, new_port(DUP,n2), k7);
    } else {
      k7 = new_port(DUP,n2);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  // fast void
  if (get_tag(k3) == ERA || get_tag(k3) == NUM) {
    tm->itrs += 1;
  } else {
    if (k3 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k3);
    } else {
      k3 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n5, new_pair(new_port(REF,0x00000012),new_port(REF,0x00000013)));
  node_create(net, n6, new_pair(new_port(VAR,v1),new_port(VAR,v2)));
  node_create(net, n4, new_pair(new_port(CON,n5),new_port(CON,n6)));
  node_create(net, n3, new_pair(new_port(VAR,v0),new_port(SWI,n4)));
  link(net, tm, new_port(OPR,n3), new_port(NUM,0x0000000c));
  return true;
}

bool interact_call_Particle(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v3), k16);
  } else {
    k16 = new_port(VAR,v3);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k15) == CON && node_load(net, get_val(k15)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k15));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  bool k25 = 0;
  Pair k26 = 0;
  Port k27 = NONE;
  Port k28 = NONE;
  // fast anni
  if (get_tag(k24) == CON && node_load(net, get_val(k24)) != 0) {
    tm->itrs += 1;
    k25 = 1;
    k26 = node_take(net, get_val(k24));
    k27 = get_fst(k26);
    k28 = get_snd(k26);
  }
  bool k29 = 0;
  Pair k30 = 0;
  Port k31 = NONE;
  Port k32 = NONE;
  // fast anni
  if (get_tag(k28) == CON && node_load(net, get_val(k28)) != 0) {
    tm->itrs += 1;
    k29 = 1;
    k30 = node_take(net, get_val(k28));
    k31 = get_fst(k30);
    k32 = get_snd(k30);
  }
  if (k32 != NONE) {
    link(net, tm, new_port(VAR,v3), k32);
  } else {
    k32 = new_port(VAR,v3);
  }
  if (k31 != NONE) {
    link(net, tm, new_port(VAR,v2), k31);
  } else {
    k31 = new_port(VAR,v2);
  }
  if (!k29) {
    node_create(net, n7, new_pair(k31,k32));
    if (k28 != NONE) {
      link(net, tm, new_port(CON,n7), k28);
    } else {
      k28 = new_port(CON,n7);
    }
  }
  if (k27 != NONE) {
    link(net, tm, new_port(VAR,v1), k27);
  } else {
    k27 = new_port(VAR,v1);
  }
  if (!k25) {
    node_create(net, n6, new_pair(k27,k28));
    if (k24 != NONE) {
      link(net, tm, new_port(CON,n6), k24);
    } else {
      k24 = new_port(CON,n6);
    }
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v0), k23);
  } else {
    k23 = new_port(VAR,v0);
  }
  if (!k21) {
    node_create(net, n5, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n5), k20);
    } else {
      k20 = new_port(CON,n5);
    }
  }
  if (k19 != NONE) {
    link(net, tm, new_port(REF,0x00000017), k19);
  } else {
    k19 = new_port(REF,0x00000017);
  }
  if (!k17) {
    node_create(net, n4, new_pair(k19,k20));
    if (k15 != NONE) {
      link(net, tm, new_port(CON,n4), k15);
    } else {
      k15 = new_port(CON,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_Particle_tag(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  if (0) {
    return false;
  }
  // fast void
  if (get_tag(b) == ERA || get_tag(b) == NUM) {
    tm->itrs += 1;
  } else {
    if (b != NONE) {
      link(net, tm, new_port(NUM,0x00000001), b);
    } else {
      b = new_port(NUM,0x00000001);
    }
  }
  return true;
}

bool interact_call_Vector3D(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v3), k16);
  } else {
    k16 = new_port(VAR,v3);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k15) == CON && node_load(net, get_val(k15)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k15));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  bool k25 = 0;
  Pair k26 = 0;
  Port k27 = NONE;
  Port k28 = NONE;
  // fast anni
  if (get_tag(k24) == CON && node_load(net, get_val(k24)) != 0) {
    tm->itrs += 1;
    k25 = 1;
    k26 = node_take(net, get_val(k24));
    k27 = get_fst(k26);
    k28 = get_snd(k26);
  }
  bool k29 = 0;
  Pair k30 = 0;
  Port k31 = NONE;
  Port k32 = NONE;
  // fast anni
  if (get_tag(k28) == CON && node_load(net, get_val(k28)) != 0) {
    tm->itrs += 1;
    k29 = 1;
    k30 = node_take(net, get_val(k28));
    k31 = get_fst(k30);
    k32 = get_snd(k30);
  }
  if (k32 != NONE) {
    link(net, tm, new_port(VAR,v3), k32);
  } else {
    k32 = new_port(VAR,v3);
  }
  if (k31 != NONE) {
    link(net, tm, new_port(VAR,v2), k31);
  } else {
    k31 = new_port(VAR,v2);
  }
  if (!k29) {
    node_create(net, n7, new_pair(k31,k32));
    if (k28 != NONE) {
      link(net, tm, new_port(CON,n7), k28);
    } else {
      k28 = new_port(CON,n7);
    }
  }
  if (k27 != NONE) {
    link(net, tm, new_port(VAR,v1), k27);
  } else {
    k27 = new_port(VAR,v1);
  }
  if (!k25) {
    node_create(net, n6, new_pair(k27,k28));
    if (k24 != NONE) {
      link(net, tm, new_port(CON,n6), k24);
    } else {
      k24 = new_port(CON,n6);
    }
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v0), k23);
  } else {
    k23 = new_port(VAR,v0);
  }
  if (!k21) {
    node_create(net, n5, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n5), k20);
    } else {
      k20 = new_port(CON,n5);
    }
  }
  if (k19 != NONE) {
    link(net, tm, new_port(REF,0x00000019), k19);
  } else {
    k19 = new_port(REF,0x00000019);
  }
  if (!k17) {
    node_create(net, n4, new_pair(k19,k20));
    if (k15 != NONE) {
      link(net, tm, new_port(CON,n4), k15);
    } else {
      k15 = new_port(CON,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_Vector3D_tag(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  if (0) {
    return false;
  }
  // fast void
  if (get_tag(b) == ERA || get_tag(b) == NUM) {
    tm->itrs += 1;
  } else {
    if (b != NONE) {
      link(net, tm, new_port(NUM,0x00000001), b);
    } else {
      b = new_port(NUM,0x00000001);
    }
  }
  return true;
}

bool interact_call_add(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x0000001e), k7);
  } else {
    k7 = new_port(REF,0x0000001e);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_add__C0(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  if (k24 != NONE) {
    link(net, tm, new_port(VAR,v6), k24);
  } else {
    k24 = new_port(VAR,v6);
  }
  bool k25 = 0;
  Port k26 = NONE;
  // fast oper
  if (get_tag(k23) == NUM && get_tag(new_port(NUM,0x00000080)) == NUM) {
    tm->itrs += 1;
    k25 = 1;
    k26 = new_port(NUM, operate(get_val(k23), get_val(new_port(NUM,0x00000080))));
  }
  bool k27 = 0;
  Port k28 = NONE;
  // fast oper
  if (get_tag(k26) == NUM && get_tag(new_port(VAR,v2)) == NUM) {
    tm->itrs += 1;
    k27 = 1;
    k28 = new_port(NUM, operate(get_val(k26), get_val(new_port(VAR,v2))));
  }
  if (k28 != NONE) {
    link(net, tm, new_port(VAR,v5), k28);
  } else {
    k28 = new_port(VAR,v5);
  }
  if (!k27) {
    node_create(net, nb, new_pair(new_port(VAR,v2),k28));
    if (k26 != NONE) {
      link(net, tm, new_port(OPR, nb), k26);
    } else {
      k26 = new_port(OPR, nb);
    }
  }
  if (!k25) {
    node_create(net, na, new_pair(new_port(NUM,0x00000080),k26));
    if (k23 != NONE) {
      link(net, tm, new_port(OPR, na), k23);
    } else {
      k23 = new_port(OPR, na);
    }
  }
  if (!k21) {
    node_create(net, n9, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n9), k20);
    } else {
      k20 = new_port(CON,n9);
    }
  }
  bool k29 = 0;
  Port k30 = NONE;
  // fast oper
  if (get_tag(k19) == NUM && get_tag(new_port(NUM,0x00000080)) == NUM) {
    tm->itrs += 1;
    k29 = 1;
    k30 = new_port(NUM, operate(get_val(k19), get_val(new_port(NUM,0x00000080))));
  }
  bool k31 = 0;
  Port k32 = NONE;
  // fast oper
  if (get_tag(k30) == NUM && get_tag(new_port(VAR,v1)) == NUM) {
    tm->itrs += 1;
    k31 = 1;
    k32 = new_port(NUM, operate(get_val(k30), get_val(new_port(VAR,v1))));
  }
  if (k32 != NONE) {
    link(net, tm, new_port(VAR,v4), k32);
  } else {
    k32 = new_port(VAR,v4);
  }
  if (!k31) {
    node_create(net, n8, new_pair(new_port(VAR,v1),k32));
    if (k30 != NONE) {
      link(net, tm, new_port(OPR, n8), k30);
    } else {
      k30 = new_port(OPR, n8);
    }
  }
  if (!k29) {
    node_create(net, n7, new_pair(new_port(NUM,0x00000080),k30));
    if (k19 != NONE) {
      link(net, tm, new_port(OPR, n7), k19);
    } else {
      k19 = new_port(OPR, n7);
    }
  }
  if (!k17) {
    node_create(net, n6, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,n6), k16);
    } else {
      k16 = new_port(CON,n6);
    }
  }
  bool k33 = 0;
  Port k34 = NONE;
  // fast oper
  if (get_tag(k15) == NUM && get_tag(new_port(NUM,0x00000080)) == NUM) {
    tm->itrs += 1;
    k33 = 1;
    k34 = new_port(NUM, operate(get_val(k15), get_val(new_port(NUM,0x00000080))));
  }
  bool k35 = 0;
  Port k36 = NONE;
  // fast oper
  if (get_tag(k34) == NUM && get_tag(new_port(VAR,v0)) == NUM) {
    tm->itrs += 1;
    k35 = 1;
    k36 = new_port(NUM, operate(get_val(k34), get_val(new_port(VAR,v0))));
  }
  if (k36 != NONE) {
    link(net, tm, new_port(VAR,v3), k36);
  } else {
    k36 = new_port(VAR,v3);
  }
  if (!k35) {
    node_create(net, n5, new_pair(new_port(VAR,v0),k36));
    if (k34 != NONE) {
      link(net, tm, new_port(OPR, n5), k34);
    } else {
      k34 = new_port(OPR, n5);
    }
  }
  if (!k33) {
    node_create(net, n4, new_pair(new_port(NUM,0x00000080),k34));
    if (k15 != NONE) {
      link(net, tm, new_port(OPR, n4), k15);
    } else {
      k15 = new_port(OPR, n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, ne, new_pair(new_port(VAR,v5),new_port(VAR,v6)));
  node_create(net, nd, new_pair(new_port(VAR,v4),new_port(CON,ne)));
  node_create(net, nc, new_pair(new_port(VAR,v3),new_port(CON,nd)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,nc));
  return true;
}

bool interact_call_add__C1(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x0000001b), k3);
  } else {
    k3 = new_port(REF,0x0000001b);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_add__C2(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v3), k16);
  } else {
    k16 = new_port(VAR,v3);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k15) == CON && node_load(net, get_val(k15)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k15));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  bool k25 = 0;
  Pair k26 = 0;
  Port k27 = NONE;
  Port k28 = NONE;
  // fast anni
  if (get_tag(k24) == CON && node_load(net, get_val(k24)) != 0) {
    tm->itrs += 1;
    k25 = 1;
    k26 = node_take(net, get_val(k24));
    k27 = get_fst(k26);
    k28 = get_snd(k26);
  }
  bool k29 = 0;
  Pair k30 = 0;
  Port k31 = NONE;
  Port k32 = NONE;
  // fast anni
  if (get_tag(k28) == CON && node_load(net, get_val(k28)) != 0) {
    tm->itrs += 1;
    k29 = 1;
    k30 = node_take(net, get_val(k28));
    k31 = get_fst(k30);
    k32 = get_snd(k30);
  }
  if (k32 != NONE) {
    link(net, tm, new_port(VAR,v3), k32);
  } else {
    k32 = new_port(VAR,v3);
  }
  if (k31 != NONE) {
    link(net, tm, new_port(VAR,v2), k31);
  } else {
    k31 = new_port(VAR,v2);
  }
  if (!k29) {
    node_create(net, n7, new_pair(k31,k32));
    if (k28 != NONE) {
      link(net, tm, new_port(CON,n7), k28);
    } else {
      k28 = new_port(CON,n7);
    }
  }
  if (k27 != NONE) {
    link(net, tm, new_port(VAR,v1), k27);
  } else {
    k27 = new_port(VAR,v1);
  }
  if (!k25) {
    node_create(net, n6, new_pair(k27,k28));
    if (k24 != NONE) {
      link(net, tm, new_port(CON,n6), k24);
    } else {
      k24 = new_port(CON,n6);
    }
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v0), k23);
  } else {
    k23 = new_port(VAR,v0);
  }
  if (!k21) {
    node_create(net, n5, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n5), k20);
    } else {
      k20 = new_port(CON,n5);
    }
  }
  if (k19 != NONE) {
    link(net, tm, new_port(REF,0x0000001c), k19);
  } else {
    k19 = new_port(REF,0x0000001c);
  }
  if (!k17) {
    node_create(net, n4, new_pair(k19,k20));
    if (k15 != NONE) {
      link(net, tm, new_port(CON,n4), k15);
    } else {
      k15 = new_port(CON,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_add__C3(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x0000001d), k3);
  } else {
    k3 = new_port(REF,0x0000001d);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_calculate_force(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x00000024), k7);
  } else {
    k7 = new_port(REF,0x00000024);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_calculate_force__C0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val v7 = vars_alloc_1(net, tm, &vl);
  Val v8 = vars_alloc_1(net, tm, &vl);
  Val v9 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  Val nf = node_alloc_1(net, tm, &nl);
  Val n10 = node_alloc_1(net, tm, &nl);
  Val n11 = node_alloc_1(net, tm, &nl);
  Val n12 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !v7 || !v8 || !v9 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne || !nf || !n10 || !n11 || !n12) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  vars_create(net, v7, NONE);
  vars_create(net, v8, NONE);
  vars_create(net, v9, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  if (k20 != NONE) {
    link(net, tm, new_port(VAR,v6), k20);
  } else {
    k20 = new_port(VAR,v6);
  }
  bool k21 = 0;
  Port k22 = NONE;
  Port k23 = NONE;
  // fast copy
  if (get_tag(k19) == NUM) {
    tm->itrs += 1;
    k21 = 1;
    k22 = k19;
    k23 = k19;
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v4), k23);
  } else {
    k23 = new_port(VAR,v4);
  }
  bool k24 = 0;
  Port k25 = NONE;
  // fast oper
  if (get_tag(k22) == NUM && get_tag(new_port(NUM,0x000000e0)) == NUM) {
    tm->itrs += 1;
    k24 = 1;
    k25 = new_port(NUM, operate(get_val(k22), get_val(new_port(NUM,0x000000e0))));
  }
  bool k26 = 0;
  Port k27 = NONE;
  // fast oper
  if (get_tag(k25) == NUM && get_tag(new_port(VAR,v4)) == NUM) {
    tm->itrs += 1;
    k26 = 1;
    k27 = new_port(NUM, operate(get_val(k25), get_val(new_port(VAR,v4))));
  }
  if (k27 != NONE) {
    link(net, tm, new_port(VAR,v5), k27);
  } else {
    k27 = new_port(VAR,v5);
  }
  if (!k26) {
    node_create(net, n7, new_pair(new_port(VAR,v4),k27));
    if (k25 != NONE) {
      link(net, tm, new_port(OPR, n7), k25);
    } else {
      k25 = new_port(OPR, n7);
    }
  }
  if (!k24) {
    node_create(net, n6, new_pair(new_port(NUM,0x000000e0),k25));
    if (k22 != NONE) {
      link(net, tm, new_port(OPR, n6), k22);
    } else {
      k22 = new_port(OPR, n6);
    }
  }
  if (!k21) {
    node_create(net, n5, new_pair(k22,k23));
    if (k19 != NONE) {
      link(net, tm, new_port(DUP,n5), k19);
    } else {
      k19 = new_port(DUP,n5);
    }
  }
  if (!k17) {
    node_create(net, n4, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,n4), k16);
    } else {
      k16 = new_port(CON,n4);
    }
  }
  if (k15 != NONE) {
    link(net, tm, new_port(VAR,v3), k15);
  } else {
    k15 = new_port(VAR,v3);
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n9, new_pair(new_port(VAR,v8),new_port(VAR,v6)));
  node_create(net, n8, new_pair(new_port(VAR,v7),new_port(CON,n9)));
  link(net, tm, new_port(REF,0x00000032), new_port(CON,n8));
  node_create(net, na, new_pair(new_port(VAR,v9),new_port(VAR,v7)));
  link(net, tm, new_port(REF,0x00000035), new_port(CON,na));
  node_create(net, nc, new_pair(new_port(VAR,v0),new_port(VAR,v9)));
  node_create(net, nb, new_pair(new_port(VAR,v2),new_port(CON,nc)));
  link(net, tm, new_port(REF,0x00000038), new_port(CON,nb));
  node_create(net, n12, new_pair(new_port(VAR,v5),new_port(VAR,v8)));
  node_create(net, n11, new_pair(new_port(NUM,0x00000100),new_port(OPR,n12)));
  node_create(net, n10, new_pair(new_port(VAR,v3),new_port(OPR,n11)));
  node_create(net, nf, new_pair(new_port(NUM,0x000000e0),new_port(OPR,n10)));
  node_create(net, ne, new_pair(new_port(VAR,v1),new_port(OPR,nf)));
  node_create(net, nd, new_pair(new_port(NUM,0x000000e0),new_port(OPR,ne)));
  link(net, tm, new_port(REF,0x0000002d), new_port(OPR,nd));
  return true;
}

bool interact_call_calculate_force__C1(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val v7 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  Val nf = node_alloc_1(net, tm, &nl);
  Val n10 = node_alloc_1(net, tm, &nl);
  Val n11 = node_alloc_1(net, tm, &nl);
  Val n12 = node_alloc_1(net, tm, &nl);
  Val n13 = node_alloc_1(net, tm, &nl);
  Val n14 = node_alloc_1(net, tm, &nl);
  Val n15 = node_alloc_1(net, tm, &nl);
  Val n16 = node_alloc_1(net, tm, &nl);
  Val n17 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !v7 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne || !nf || !n10 || !n11 || !n12 || !n13 || !n14 || !n15 || !n16 || !n17) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  vars_create(net, v7, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  if (k20 != NONE) {
    link(net, tm, new_port(VAR,v6), k20);
  } else {
    k20 = new_port(VAR,v6);
  }
  if (k19 != NONE) {
    link(net, tm, new_port(VAR,v5), k19);
  } else {
    k19 = new_port(VAR,v5);
  }
  if (!k17) {
    node_create(net, n6, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,n6), k16);
    } else {
      k16 = new_port(CON,n6);
    }
  }
  bool k21 = 0;
  Port k22 = NONE;
  Port k23 = NONE;
  // fast copy
  if (get_tag(k15) == NUM) {
    tm->itrs += 1;
    k21 = 1;
    k22 = k15;
    k23 = k15;
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v4), k23);
  } else {
    k23 = new_port(VAR,v4);
  }
  if (k22 != NONE) {
    link(net, tm, new_port(VAR,v3), k22);
  } else {
    k22 = new_port(VAR,v3);
  }
  if (!k21) {
    node_create(net, n5, new_pair(k22,k23));
    if (k15 != NONE) {
      link(net, tm, new_port(DUP,n5), k15);
    } else {
      k15 = new_port(DUP,n5);
    }
  }
  if (!k13) {
    node_create(net, n4, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n4), k12);
    } else {
      k12 = new_port(CON,n4);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n3, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n3), k8);
    } else {
      k8 = new_port(CON,n3);
    }
  }
  // fast void
  if (get_tag(k7) == ERA || get_tag(k7) == NUM) {
    tm->itrs += 1;
  } else {
    if (k7 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k7);
    } else {
      k7 = new_port(ERA,0x00000000);
    }
  }
  if (!k5) {
    node_create(net, n2, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n2), k4);
    } else {
      k4 = new_port(CON,n2);
    }
  }
  bool k24 = 0;
  Port k25 = NONE;
  Port k26 = NONE;
  // fast copy
  if (get_tag(k3) == NUM) {
    tm->itrs += 1;
    k24 = 1;
    k25 = k3;
    k26 = k3;
  }
  if (k26 != NONE) {
    link(net, tm, new_port(VAR,v1), k26);
  } else {
    k26 = new_port(VAR,v1);
  }
  if (k25 != NONE) {
    link(net, tm, new_port(VAR,v0), k25);
  } else {
    k25 = new_port(VAR,v0);
  }
  if (!k24) {
    node_create(net, n1, new_pair(k25,k26));
    if (k3 != NONE) {
      link(net, tm, new_port(DUP,n1), k3);
    } else {
      k3 = new_port(DUP,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n12, new_pair(new_port(ERA,0x00000000),new_port(REF,0x0000002e)));
  node_create(net, n11, new_pair(new_port(ERA,0x00000000),new_port(CON,n12)));
  node_create(net, n10, new_pair(new_port(ERA,0x00000000),new_port(CON,n11)));
  node_create(net, nf, new_pair(new_port(ERA,0x00000000),new_port(CON,n10)));
  node_create(net, ne, new_pair(new_port(ERA,0x00000000),new_port(CON,nf)));
  node_create(net, nd, new_pair(new_port(ERA,0x00000000),new_port(CON,ne)));
  node_create(net, nc, new_pair(new_port(REF,0x00000020),new_port(CON,nd)));
  node_create(net, n17, new_pair(new_port(VAR,v7),new_port(VAR,v6)));
  node_create(net, n16, new_pair(new_port(VAR,v2),new_port(CON,n17)));
  node_create(net, n15, new_pair(new_port(VAR,v0),new_port(CON,n16)));
  node_create(net, n14, new_pair(new_port(VAR,v5),new_port(CON,n15)));
  node_create(net, n13, new_pair(new_port(VAR,v3),new_port(CON,n14)));
  node_create(net, nb, new_pair(new_port(CON,nc),new_port(CON,n13)));
  node_create(net, na, new_pair(new_port(NUM,0x0000000c),new_port(SWI,nb)));
  node_create(net, n9, new_pair(new_port(OPR,na),new_port(VAR,v7)));
  node_create(net, n8, new_pair(new_port(VAR,v1),new_port(DUP,n9)));
  node_create(net, n7, new_pair(new_port(VAR,v4),new_port(CON,n8)));
  link(net, tm, new_port(REF,0x00000025), new_port(CON,n7));
  return true;
}

bool interact_call_calculate_force__C2(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x00000021), k3);
  } else {
    k3 = new_port(REF,0x00000021);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_calculate_force__C3(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v2), k16);
  } else {
    k16 = new_port(VAR,v2);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k15) == CON && node_load(net, get_val(k15)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k15));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  bool k25 = 0;
  Pair k26 = 0;
  Port k27 = NONE;
  Port k28 = NONE;
  // fast anni
  if (get_tag(k24) == CON && node_load(net, get_val(k24)) != 0) {
    tm->itrs += 1;
    k25 = 1;
    k26 = node_take(net, get_val(k24));
    k27 = get_fst(k26);
    k28 = get_snd(k26);
  }
  if (k28 != NONE) {
    link(net, tm, new_port(VAR,v2), k28);
  } else {
    k28 = new_port(VAR,v2);
  }
  if (k27 != NONE) {
    link(net, tm, new_port(VAR,v1), k27);
  } else {
    k27 = new_port(VAR,v1);
  }
  if (!k25) {
    node_create(net, n6, new_pair(k27,k28));
    if (k24 != NONE) {
      link(net, tm, new_port(CON,n6), k24);
    } else {
      k24 = new_port(CON,n6);
    }
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v0), k23);
  } else {
    k23 = new_port(VAR,v0);
  }
  if (!k21) {
    node_create(net, n5, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n5), k20);
    } else {
      k20 = new_port(CON,n5);
    }
  }
  if (k19 != NONE) {
    link(net, tm, new_port(REF,0x00000022), k19);
  } else {
    k19 = new_port(REF,0x00000022);
  }
  if (!k17) {
    node_create(net, n4, new_pair(k19,k20));
    if (k15 != NONE) {
      link(net, tm, new_port(CON,n4), k15);
    } else {
      k15 = new_port(CON,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v1), k11);
  } else {
    k11 = new_port(VAR,v1);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  // fast void
  if (get_tag(k7) == ERA || get_tag(k7) == NUM) {
    tm->itrs += 1;
  } else {
    if (k7 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k7);
    } else {
      k7 = new_port(ERA,0x00000000);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_calculate_force__C4(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x00000023), k3);
  } else {
    k3 = new_port(REF,0x00000023);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_distance(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x00000029), k7);
  } else {
    k7 = new_port(REF,0x00000029);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_distance__C0(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  Val nf = node_alloc_1(net, tm, &nl);
  Val n10 = node_alloc_1(net, tm, &nl);
  Val n11 = node_alloc_1(net, tm, &nl);
  Val n12 = node_alloc_1(net, tm, &nl);
  Val n13 = node_alloc_1(net, tm, &nl);
  Val n14 = node_alloc_1(net, tm, &nl);
  Val n15 = node_alloc_1(net, tm, &nl);
  Val n16 = node_alloc_1(net, tm, &nl);
  Val n17 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne || !nf || !n10 || !n11 || !n12 || !n13 || !n14 || !n15 || !n16 || !n17) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  if (k24 != NONE) {
    link(net, tm, new_port(VAR,v5), k24);
  } else {
    k24 = new_port(VAR,v5);
  }
  bool k25 = 0;
  Port k26 = NONE;
  // fast oper
  if (get_tag(k23) == NUM && get_tag(new_port(NUM,0x000000a0)) == NUM) {
    tm->itrs += 1;
    k25 = 1;
    k26 = new_port(NUM, operate(get_val(k23), get_val(new_port(NUM,0x000000a0))));
  }
  bool k27 = 0;
  Port k28 = NONE;
  // fast oper
  if (get_tag(k26) == NUM && get_tag(new_port(VAR,v2)) == NUM) {
    tm->itrs += 1;
    k27 = 1;
    k28 = new_port(NUM, operate(get_val(k26), get_val(new_port(VAR,v2))));
  }
  bool k29 = 0;
  Port k30 = NONE;
  // fast oper
  if (get_tag(k28) == NUM && get_tag(new_port(NUM,0x00000240)) == NUM) {
    tm->itrs += 1;
    k29 = 1;
    k30 = new_port(NUM, operate(get_val(k28), get_val(new_port(NUM,0x00000240))));
  }
  bool k31 = 0;
  Port k32 = NONE;
  // fast oper
  if (get_tag(k30) == NUM && get_tag(new_port(NUM,0x08000003)) == NUM) {
    tm->itrs += 1;
    k31 = 1;
    k32 = new_port(NUM, operate(get_val(k30), get_val(new_port(NUM,0x08000003))));
  }
  if (k32 != NONE) {
    link(net, tm, new_port(VAR,v4), k32);
  } else {
    k32 = new_port(VAR,v4);
  }
  if (!k31) {
    node_create(net, n17, new_pair(new_port(NUM,0x08000003),k32));
    if (k30 != NONE) {
      link(net, tm, new_port(OPR, n17), k30);
    } else {
      k30 = new_port(OPR, n17);
    }
  }
  if (!k29) {
    node_create(net, n16, new_pair(new_port(NUM,0x00000240),k30));
    if (k28 != NONE) {
      link(net, tm, new_port(OPR, n16), k28);
    } else {
      k28 = new_port(OPR, n16);
    }
  }
  if (!k27) {
    node_create(net, n15, new_pair(new_port(VAR,v2),k28));
    if (k26 != NONE) {
      link(net, tm, new_port(OPR, n15), k26);
    } else {
      k26 = new_port(OPR, n15);
    }
  }
  if (!k25) {
    node_create(net, n14, new_pair(new_port(NUM,0x000000a0),k26));
    if (k23 != NONE) {
      link(net, tm, new_port(OPR, n14), k23);
    } else {
      k23 = new_port(OPR, n14);
    }
  }
  if (!k21) {
    node_create(net, n13, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n13), k20);
    } else {
      k20 = new_port(CON,n13);
    }
  }
  bool k33 = 0;
  Port k34 = NONE;
  // fast oper
  if (get_tag(k19) == NUM && get_tag(new_port(NUM,0x000000a0)) == NUM) {
    tm->itrs += 1;
    k33 = 1;
    k34 = new_port(NUM, operate(get_val(k19), get_val(new_port(NUM,0x000000a0))));
  }
  bool k35 = 0;
  Port k36 = NONE;
  // fast oper
  if (get_tag(k34) == NUM && get_tag(new_port(VAR,v1)) == NUM) {
    tm->itrs += 1;
    k35 = 1;
    k36 = new_port(NUM, operate(get_val(k34), get_val(new_port(VAR,v1))));
  }
  bool k37 = 0;
  Port k38 = NONE;
  // fast oper
  if (get_tag(k36) == NUM && get_tag(new_port(NUM,0x00000240)) == NUM) {
    tm->itrs += 1;
    k37 = 1;
    k38 = new_port(NUM, operate(get_val(k36), get_val(new_port(NUM,0x00000240))));
  }
  bool k39 = 0;
  Port k40 = NONE;
  // fast oper
  if (get_tag(k38) == NUM && get_tag(new_port(NUM,0x08000003)) == NUM) {
    tm->itrs += 1;
    k39 = 1;
    k40 = new_port(NUM, operate(get_val(k38), get_val(new_port(NUM,0x08000003))));
  }
  if (k40 != NONE) {
    link(net, tm, new_port(VAR,v3), k40);
  } else {
    k40 = new_port(VAR,v3);
  }
  if (!k39) {
    node_create(net, n12, new_pair(new_port(NUM,0x08000003),k40));
    if (k38 != NONE) {
      link(net, tm, new_port(OPR, n12), k38);
    } else {
      k38 = new_port(OPR, n12);
    }
  }
  if (!k37) {
    node_create(net, n11, new_pair(new_port(NUM,0x00000240),k38));
    if (k36 != NONE) {
      link(net, tm, new_port(OPR, n11), k36);
    } else {
      k36 = new_port(OPR, n11);
    }
  }
  if (!k35) {
    node_create(net, n10, new_pair(new_port(VAR,v1),k36));
    if (k34 != NONE) {
      link(net, tm, new_port(OPR, n10), k34);
    } else {
      k34 = new_port(OPR, n10);
    }
  }
  if (!k33) {
    node_create(net, nf, new_pair(new_port(NUM,0x000000a0),k34));
    if (k19 != NONE) {
      link(net, tm, new_port(OPR, nf), k19);
    } else {
      k19 = new_port(OPR, nf);
    }
  }
  if (!k17) {
    node_create(net, ne, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,ne), k16);
    } else {
      k16 = new_port(CON,ne);
    }
  }
  bool k41 = 0;
  Port k42 = NONE;
  // fast oper
  if (get_tag(k15) == NUM && get_tag(new_port(NUM,0x000000a0)) == NUM) {
    tm->itrs += 1;
    k41 = 1;
    k42 = new_port(NUM, operate(get_val(k15), get_val(new_port(NUM,0x000000a0))));
  }
  bool k43 = 0;
  Port k44 = NONE;
  // fast oper
  if (get_tag(k42) == NUM && get_tag(new_port(VAR,v0)) == NUM) {
    tm->itrs += 1;
    k43 = 1;
    k44 = new_port(NUM, operate(get_val(k42), get_val(new_port(VAR,v0))));
  }
  bool k45 = 0;
  Port k46 = NONE;
  // fast oper
  if (get_tag(k44) == NUM && get_tag(new_port(NUM,0x00000240)) == NUM) {
    tm->itrs += 1;
    k45 = 1;
    k46 = new_port(NUM, operate(get_val(k44), get_val(new_port(NUM,0x00000240))));
  }
  bool k47 = 0;
  Port k48 = NONE;
  // fast oper
  if (get_tag(k46) == NUM && get_tag(new_port(NUM,0x08000003)) == NUM) {
    tm->itrs += 1;
    k47 = 1;
    k48 = new_port(NUM, operate(get_val(k46), get_val(new_port(NUM,0x08000003))));
  }
  bool k49 = 0;
  Port k50 = NONE;
  // fast oper
  if (get_tag(k48) == NUM && get_tag(new_port(NUM,0x00000080)) == NUM) {
    tm->itrs += 1;
    k49 = 1;
    k50 = new_port(NUM, operate(get_val(k48), get_val(new_port(NUM,0x00000080))));
  }
  bool k51 = 0;
  Port k52 = NONE;
  // fast oper
  if (get_tag(k50) == NUM && get_tag(new_port(VAR,v3)) == NUM) {
    tm->itrs += 1;
    k51 = 1;
    k52 = new_port(NUM, operate(get_val(k50), get_val(new_port(VAR,v3))));
  }
  bool k53 = 0;
  Port k54 = NONE;
  // fast oper
  if (get_tag(k52) == NUM && get_tag(new_port(NUM,0x00000080)) == NUM) {
    tm->itrs += 1;
    k53 = 1;
    k54 = new_port(NUM, operate(get_val(k52), get_val(new_port(NUM,0x00000080))));
  }
  bool k55 = 0;
  Port k56 = NONE;
  // fast oper
  if (get_tag(k54) == NUM && get_tag(new_port(VAR,v4)) == NUM) {
    tm->itrs += 1;
    k55 = 1;
    k56 = new_port(NUM, operate(get_val(k54), get_val(new_port(VAR,v4))));
  }
  bool k57 = 0;
  Port k58 = NONE;
  // fast oper
  if (get_tag(k56) == NUM && get_tag(new_port(NUM,0x00000240)) == NUM) {
    tm->itrs += 1;
    k57 = 1;
    k58 = new_port(NUM, operate(get_val(k56), get_val(new_port(NUM,0x00000240))));
  }
  bool k59 = 0;
  Port k60 = NONE;
  // fast oper
  if (get_tag(k58) == NUM && get_tag(new_port(NUM,0x07e00003)) == NUM) {
    tm->itrs += 1;
    k59 = 1;
    k60 = new_port(NUM, operate(get_val(k58), get_val(new_port(NUM,0x07e00003))));
  }
  if (k60 != NONE) {
    link(net, tm, new_port(VAR,v5), k60);
  } else {
    k60 = new_port(VAR,v5);
  }
  if (!k59) {
    node_create(net, nd, new_pair(new_port(NUM,0x07e00003),k60));
    if (k58 != NONE) {
      link(net, tm, new_port(OPR, nd), k58);
    } else {
      k58 = new_port(OPR, nd);
    }
  }
  if (!k57) {
    node_create(net, nc, new_pair(new_port(NUM,0x00000240),k58));
    if (k56 != NONE) {
      link(net, tm, new_port(OPR, nc), k56);
    } else {
      k56 = new_port(OPR, nc);
    }
  }
  if (!k55) {
    node_create(net, nb, new_pair(new_port(VAR,v4),k56));
    if (k54 != NONE) {
      link(net, tm, new_port(OPR, nb), k54);
    } else {
      k54 = new_port(OPR, nb);
    }
  }
  if (!k53) {
    node_create(net, na, new_pair(new_port(NUM,0x00000080),k54));
    if (k52 != NONE) {
      link(net, tm, new_port(OPR, na), k52);
    } else {
      k52 = new_port(OPR, na);
    }
  }
  if (!k51) {
    node_create(net, n9, new_pair(new_port(VAR,v3),k52));
    if (k50 != NONE) {
      link(net, tm, new_port(OPR, n9), k50);
    } else {
      k50 = new_port(OPR, n9);
    }
  }
  if (!k49) {
    node_create(net, n8, new_pair(new_port(NUM,0x00000080),k50));
    if (k48 != NONE) {
      link(net, tm, new_port(OPR, n8), k48);
    } else {
      k48 = new_port(OPR, n8);
    }
  }
  if (!k47) {
    node_create(net, n7, new_pair(new_port(NUM,0x08000003),k48));
    if (k46 != NONE) {
      link(net, tm, new_port(OPR, n7), k46);
    } else {
      k46 = new_port(OPR, n7);
    }
  }
  if (!k45) {
    node_create(net, n6, new_pair(new_port(NUM,0x00000240),k46));
    if (k44 != NONE) {
      link(net, tm, new_port(OPR, n6), k44);
    } else {
      k44 = new_port(OPR, n6);
    }
  }
  if (!k43) {
    node_create(net, n5, new_pair(new_port(VAR,v0),k44));
    if (k42 != NONE) {
      link(net, tm, new_port(OPR, n5), k42);
    } else {
      k42 = new_port(OPR, n5);
    }
  }
  if (!k41) {
    node_create(net, n4, new_pair(new_port(NUM,0x000000a0),k42));
    if (k15 != NONE) {
      link(net, tm, new_port(OPR, n4), k15);
    } else {
      k15 = new_port(OPR, n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_distance__C1(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x00000026), k3);
  } else {
    k3 = new_port(REF,0x00000026);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_distance__C2(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v3), k16);
  } else {
    k16 = new_port(VAR,v3);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k15) == CON && node_load(net, get_val(k15)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k15));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  bool k25 = 0;
  Pair k26 = 0;
  Port k27 = NONE;
  Port k28 = NONE;
  // fast anni
  if (get_tag(k24) == CON && node_load(net, get_val(k24)) != 0) {
    tm->itrs += 1;
    k25 = 1;
    k26 = node_take(net, get_val(k24));
    k27 = get_fst(k26);
    k28 = get_snd(k26);
  }
  bool k29 = 0;
  Pair k30 = 0;
  Port k31 = NONE;
  Port k32 = NONE;
  // fast anni
  if (get_tag(k28) == CON && node_load(net, get_val(k28)) != 0) {
    tm->itrs += 1;
    k29 = 1;
    k30 = node_take(net, get_val(k28));
    k31 = get_fst(k30);
    k32 = get_snd(k30);
  }
  if (k32 != NONE) {
    link(net, tm, new_port(VAR,v3), k32);
  } else {
    k32 = new_port(VAR,v3);
  }
  if (k31 != NONE) {
    link(net, tm, new_port(VAR,v2), k31);
  } else {
    k31 = new_port(VAR,v2);
  }
  if (!k29) {
    node_create(net, n7, new_pair(k31,k32));
    if (k28 != NONE) {
      link(net, tm, new_port(CON,n7), k28);
    } else {
      k28 = new_port(CON,n7);
    }
  }
  if (k27 != NONE) {
    link(net, tm, new_port(VAR,v1), k27);
  } else {
    k27 = new_port(VAR,v1);
  }
  if (!k25) {
    node_create(net, n6, new_pair(k27,k28));
    if (k24 != NONE) {
      link(net, tm, new_port(CON,n6), k24);
    } else {
      k24 = new_port(CON,n6);
    }
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v0), k23);
  } else {
    k23 = new_port(VAR,v0);
  }
  if (!k21) {
    node_create(net, n5, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n5), k20);
    } else {
      k20 = new_port(CON,n5);
    }
  }
  if (k19 != NONE) {
    link(net, tm, new_port(REF,0x00000027), k19);
  } else {
    k19 = new_port(REF,0x00000027);
  }
  if (!k17) {
    node_create(net, n4, new_pair(k19,k20));
    if (k15 != NONE) {
      link(net, tm, new_port(CON,n4), k15);
    } else {
      k15 = new_port(CON,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_distance__C3(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x00000028), k3);
  } else {
    k3 = new_port(REF,0x00000028);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_divide(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x0000002c), k7);
  } else {
    k7 = new_port(REF,0x0000002c);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_divide__C0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v6), k16);
  } else {
    k16 = new_port(VAR,v6);
  }
  bool k17 = 0;
  Port k18 = NONE;
  Port k19 = NONE;
  // fast copy
  if (get_tag(k15) == NUM) {
    tm->itrs += 1;
    k17 = 1;
    k18 = k15;
    k19 = k15;
  }
  bool k20 = 0;
  Port k21 = NONE;
  Port k22 = NONE;
  // fast copy
  if (get_tag(k19) == NUM) {
    tm->itrs += 1;
    k20 = 1;
    k21 = k19;
    k22 = k19;
  }
  if (k22 != NONE) {
    link(net, tm, new_port(VAR,v4), k22);
  } else {
    k22 = new_port(VAR,v4);
  }
  if (k21 != NONE) {
    link(net, tm, new_port(VAR,v2), k21);
  } else {
    k21 = new_port(VAR,v2);
  }
  if (!k20) {
    node_create(net, nb, new_pair(k21,k22));
    if (k19 != NONE) {
      link(net, tm, new_port(DUP,nb), k19);
    } else {
      k19 = new_port(DUP,nb);
    }
  }
  if (k18 != NONE) {
    link(net, tm, new_port(VAR,v0), k18);
  } else {
    k18 = new_port(VAR,v0);
  }
  if (!k17) {
    node_create(net, na, new_pair(k18,k19));
    if (k15 != NONE) {
      link(net, tm, new_port(DUP,na), k15);
    } else {
      k15 = new_port(DUP,na);
    }
  }
  if (!k13) {
    node_create(net, n9, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n9), k12);
    } else {
      k12 = new_port(CON,n9);
    }
  }
  bool k23 = 0;
  Port k24 = NONE;
  // fast oper
  if (get_tag(k11) == NUM && get_tag(new_port(NUM,0x00000100)) == NUM) {
    tm->itrs += 1;
    k23 = 1;
    k24 = new_port(NUM, operate(get_val(k11), get_val(new_port(NUM,0x00000100))));
  }
  bool k25 = 0;
  Port k26 = NONE;
  // fast oper
  if (get_tag(k24) == NUM && get_tag(new_port(VAR,v4)) == NUM) {
    tm->itrs += 1;
    k25 = 1;
    k26 = new_port(NUM, operate(get_val(k24), get_val(new_port(VAR,v4))));
  }
  if (k26 != NONE) {
    link(net, tm, new_port(VAR,v5), k26);
  } else {
    k26 = new_port(VAR,v5);
  }
  if (!k25) {
    node_create(net, n8, new_pair(new_port(VAR,v4),k26));
    if (k24 != NONE) {
      link(net, tm, new_port(OPR, n8), k24);
    } else {
      k24 = new_port(OPR, n8);
    }
  }
  if (!k23) {
    node_create(net, n7, new_pair(new_port(NUM,0x00000100),k24));
    if (k11 != NONE) {
      link(net, tm, new_port(OPR, n7), k11);
    } else {
      k11 = new_port(OPR, n7);
    }
  }
  if (!k9) {
    node_create(net, n6, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n6), k8);
    } else {
      k8 = new_port(CON,n6);
    }
  }
  bool k27 = 0;
  Port k28 = NONE;
  // fast oper
  if (get_tag(k7) == NUM && get_tag(new_port(NUM,0x00000100)) == NUM) {
    tm->itrs += 1;
    k27 = 1;
    k28 = new_port(NUM, operate(get_val(k7), get_val(new_port(NUM,0x00000100))));
  }
  bool k29 = 0;
  Port k30 = NONE;
  // fast oper
  if (get_tag(k28) == NUM && get_tag(new_port(VAR,v2)) == NUM) {
    tm->itrs += 1;
    k29 = 1;
    k30 = new_port(NUM, operate(get_val(k28), get_val(new_port(VAR,v2))));
  }
  if (k30 != NONE) {
    link(net, tm, new_port(VAR,v3), k30);
  } else {
    k30 = new_port(VAR,v3);
  }
  if (!k29) {
    node_create(net, n5, new_pair(new_port(VAR,v2),k30));
    if (k28 != NONE) {
      link(net, tm, new_port(OPR, n5), k28);
    } else {
      k28 = new_port(OPR, n5);
    }
  }
  if (!k27) {
    node_create(net, n4, new_pair(new_port(NUM,0x00000100),k28));
    if (k7 != NONE) {
      link(net, tm, new_port(OPR, n4), k7);
    } else {
      k7 = new_port(OPR, n4);
    }
  }
  if (!k5) {
    node_create(net, n3, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n3), k4);
    } else {
      k4 = new_port(CON,n3);
    }
  }
  bool k31 = 0;
  Port k32 = NONE;
  // fast oper
  if (get_tag(k3) == NUM && get_tag(new_port(NUM,0x00000100)) == NUM) {
    tm->itrs += 1;
    k31 = 1;
    k32 = new_port(NUM, operate(get_val(k3), get_val(new_port(NUM,0x00000100))));
  }
  bool k33 = 0;
  Port k34 = NONE;
  // fast oper
  if (get_tag(k32) == NUM && get_tag(new_port(VAR,v0)) == NUM) {
    tm->itrs += 1;
    k33 = 1;
    k34 = new_port(NUM, operate(get_val(k32), get_val(new_port(VAR,v0))));
  }
  if (k34 != NONE) {
    link(net, tm, new_port(VAR,v1), k34);
  } else {
    k34 = new_port(VAR,v1);
  }
  if (!k33) {
    node_create(net, n2, new_pair(new_port(VAR,v0),k34));
    if (k32 != NONE) {
      link(net, tm, new_port(OPR, n2), k32);
    } else {
      k32 = new_port(OPR, n2);
    }
  }
  if (!k31) {
    node_create(net, n1, new_pair(new_port(NUM,0x00000100),k32));
    if (k3 != NONE) {
      link(net, tm, new_port(OPR, n1), k3);
    } else {
      k3 = new_port(OPR, n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, ne, new_pair(new_port(VAR,v5),new_port(VAR,v6)));
  node_create(net, nd, new_pair(new_port(VAR,v3),new_port(CON,ne)));
  node_create(net, nc, new_pair(new_port(VAR,v1),new_port(CON,nd)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,nc));
  return true;
}

bool interact_call_divide__C1(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x0000002b), k3);
  } else {
    k3 = new_port(REF,0x0000002b);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_getG(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  if (b != NONE) {
    link(net, tm, new_port(VAR,v0), b);
  } else {
    b = new_port(VAR,v0);
  }
  node_create(net, n0, new_pair(new_port(VAR,v1),new_port(VAR,v0)));
  link(net, tm, new_port(OPR,n0), new_port(NUM,0x081ab287));
  node_create(net, n1, new_pair(new_port(NUM,0x18260003),new_port(VAR,v1)));
  link(net, tm, new_port(OPR,n1), new_port(NUM,0x08240012));
  return true;
}

bool interact_call_get_origin(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  if (b != NONE) {
    link(net, tm, new_port(VAR,v0), b);
  } else {
    b = new_port(VAR,v0);
  }
  node_create(net, n2, new_pair(new_port(NUM,0x00000003),new_port(VAR,v0)));
  node_create(net, n1, new_pair(new_port(NUM,0x00000003),new_port(CON,n2)));
  node_create(net, n0, new_pair(new_port(NUM,0x00000003),new_port(CON,n1)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n0));
  return true;
}

bool interact_call_get_particles(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val v7 = vars_alloc_1(net, tm, &vl);
  Val v8 = vars_alloc_1(net, tm, &vl);
  Val v9 = vars_alloc_1(net, tm, &vl);
  Val va = vars_alloc_1(net, tm, &vl);
  Val vb = vars_alloc_1(net, tm, &vl);
  Val vc = vars_alloc_1(net, tm, &vl);
  Val vd = vars_alloc_1(net, tm, &vl);
  Val ve = vars_alloc_1(net, tm, &vl);
  Val vf = vars_alloc_1(net, tm, &vl);
  Val v10 = vars_alloc_1(net, tm, &vl);
  Val v11 = vars_alloc_1(net, tm, &vl);
  Val v12 = vars_alloc_1(net, tm, &vl);
  Val v13 = vars_alloc_1(net, tm, &vl);
  Val v14 = vars_alloc_1(net, tm, &vl);
  Val v15 = vars_alloc_1(net, tm, &vl);
  Val v16 = vars_alloc_1(net, tm, &vl);
  Val v17 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  Val nf = node_alloc_1(net, tm, &nl);
  Val n10 = node_alloc_1(net, tm, &nl);
  Val n11 = node_alloc_1(net, tm, &nl);
  Val n12 = node_alloc_1(net, tm, &nl);
  Val n13 = node_alloc_1(net, tm, &nl);
  Val n14 = node_alloc_1(net, tm, &nl);
  Val n15 = node_alloc_1(net, tm, &nl);
  Val n16 = node_alloc_1(net, tm, &nl);
  Val n17 = node_alloc_1(net, tm, &nl);
  Val n18 = node_alloc_1(net, tm, &nl);
  Val n19 = node_alloc_1(net, tm, &nl);
  Val n1a = node_alloc_1(net, tm, &nl);
  Val n1b = node_alloc_1(net, tm, &nl);
  Val n1c = node_alloc_1(net, tm, &nl);
  Val n1d = node_alloc_1(net, tm, &nl);
  Val n1e = node_alloc_1(net, tm, &nl);
  Val n1f = node_alloc_1(net, tm, &nl);
  Val n20 = node_alloc_1(net, tm, &nl);
  Val n21 = node_alloc_1(net, tm, &nl);
  Val n22 = node_alloc_1(net, tm, &nl);
  Val n23 = node_alloc_1(net, tm, &nl);
  Val n24 = node_alloc_1(net, tm, &nl);
  Val n25 = node_alloc_1(net, tm, &nl);
  Val n26 = node_alloc_1(net, tm, &nl);
  Val n27 = node_alloc_1(net, tm, &nl);
  Val n28 = node_alloc_1(net, tm, &nl);
  Val n29 = node_alloc_1(net, tm, &nl);
  Val n2a = node_alloc_1(net, tm, &nl);
  Val n2b = node_alloc_1(net, tm, &nl);
  Val n2c = node_alloc_1(net, tm, &nl);
  Val n2d = node_alloc_1(net, tm, &nl);
  Val n2e = node_alloc_1(net, tm, &nl);
  Val n2f = node_alloc_1(net, tm, &nl);
  Val n30 = node_alloc_1(net, tm, &nl);
  Val n31 = node_alloc_1(net, tm, &nl);
  Val n32 = node_alloc_1(net, tm, &nl);
  Val n33 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !v7 || !v8 || !v9 || !va || !vb || !vc || !vd || !ve || !vf || !v10 || !v11 || !v12 || !v13 || !v14 || !v15 || !v16 || !v17 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne || !nf || !n10 || !n11 || !n12 || !n13 || !n14 || !n15 || !n16 || !n17 || !n18 || !n19 || !n1a || !n1b || !n1c || !n1d || !n1e || !n1f || !n20 || !n21 || !n22 || !n23 || !n24 || !n25 || !n26 || !n27 || !n28 || !n29 || !n2a || !n2b || !n2c || !n2d || !n2e || !n2f || !n30 || !n31 || !n32 || !n33) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  vars_create(net, v7, NONE);
  vars_create(net, v8, NONE);
  vars_create(net, v9, NONE);
  vars_create(net, va, NONE);
  vars_create(net, vb, NONE);
  vars_create(net, vc, NONE);
  vars_create(net, vd, NONE);
  vars_create(net, ve, NONE);
  vars_create(net, vf, NONE);
  vars_create(net, v10, NONE);
  vars_create(net, v11, NONE);
  vars_create(net, v12, NONE);
  vars_create(net, v13, NONE);
  vars_create(net, v14, NONE);
  vars_create(net, v15, NONE);
  vars_create(net, v16, NONE);
  vars_create(net, v17, NONE);
  if (b != NONE) {
    link(net, tm, new_port(VAR,v0), b);
  } else {
    b = new_port(VAR,v0);
  }
  node_create(net, n1, new_pair(new_port(VAR,v2),new_port(VAR,v0)));
  node_create(net, n0, new_pair(new_port(VAR,v1),new_port(CON,n1)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n0));
  node_create(net, n4, new_pair(new_port(VAR,v5),new_port(VAR,v1)));
  node_create(net, n3, new_pair(new_port(VAR,v4),new_port(CON,n4)));
  node_create(net, n2, new_pair(new_port(VAR,v3),new_port(CON,n3)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n2));
  node_create(net, n7, new_pair(new_port(NUM,0x07db6f83),new_port(VAR,v3)));
  node_create(net, n6, new_pair(new_port(NUM,0x07eeeb63),new_port(CON,n7)));
  node_create(net, n5, new_pair(new_port(NUM,0x07dfd3a3),new_port(CON,n6)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n5));
  node_create(net, na, new_pair(new_port(NUM,0x07e60e63),new_port(VAR,v4)));
  node_create(net, n9, new_pair(new_port(NUM,0x07d71c83),new_port(CON,na)));
  node_create(net, n8, new_pair(new_port(NUM,0x07c96223),new_port(CON,n9)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n8));
  node_create(net, nb, new_pair(new_port(VAR,v6),new_port(VAR,v5)));
  link(net, tm, new_port(OPR,nb), new_port(NUM,0x07cc9fc7));
  node_create(net, nc, new_pair(new_port(NUM,0x08240003),new_port(VAR,v6)));
  link(net, tm, new_port(OPR,nc), new_port(NUM,0x08240012));
  node_create(net, ne, new_pair(new_port(VAR,v8),new_port(VAR,v2)));
  node_create(net, nd, new_pair(new_port(VAR,v7),new_port(CON,ne)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,nd));
  node_create(net, n11, new_pair(new_port(VAR,vb),new_port(VAR,v7)));
  node_create(net, n10, new_pair(new_port(VAR,va),new_port(CON,n11)));
  node_create(net, nf, new_pair(new_port(VAR,v9),new_port(CON,n10)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,nf));
  node_create(net, n14, new_pair(new_port(NUM,0x07dadae3),new_port(VAR,v9)));
  node_create(net, n13, new_pair(new_port(NUM,0x07ea4803),new_port(CON,n14)));
  node_create(net, n12, new_pair(new_port(NUM,0x07eede23),new_port(CON,n13)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n12));
  node_create(net, n17, new_pair(new_port(NUM,0x07c4fc63),new_port(VAR,va)));
  node_create(net, n16, new_pair(new_port(NUM,0x07e2c903),new_port(CON,n17)));
  node_create(net, n15, new_pair(new_port(NUM,0x07e534c3),new_port(CON,n16)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n15));
  node_create(net, n18, new_pair(new_port(VAR,vc),new_port(VAR,vb)));
  link(net, tm, new_port(OPR,n18), new_port(NUM,0x07d75567));
  node_create(net, n19, new_pair(new_port(NUM,0x08240003),new_port(VAR,vc)));
  link(net, tm, new_port(OPR,n19), new_port(NUM,0x08240012));
  node_create(net, n1b, new_pair(new_port(VAR,ve),new_port(VAR,v8)));
  node_create(net, n1a, new_pair(new_port(VAR,vd),new_port(CON,n1b)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n1a));
  node_create(net, n1e, new_pair(new_port(VAR,v11),new_port(VAR,vd)));
  node_create(net, n1d, new_pair(new_port(VAR,v10),new_port(CON,n1e)));
  node_create(net, n1c, new_pair(new_port(VAR,vf),new_port(CON,n1d)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n1c));
  node_create(net, n21, new_pair(new_port(NUM,0x07cc3703),new_port(VAR,vf)));
  node_create(net, n20, new_pair(new_port(NUM,0x078fb583),new_port(CON,n21)));
  node_create(net, n1f, new_pair(new_port(NUM,0x07950123),new_port(CON,n20)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n1f));
  node_create(net, n24, new_pair(new_port(NUM,0x07ea9543),new_port(VAR,v10)));
  node_create(net, n23, new_pair(new_port(NUM,0x0795efe3),new_port(CON,n24)));
  node_create(net, n22, new_pair(new_port(NUM,0x07d5d283),new_port(CON,n23)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n22));
  node_create(net, n25, new_pair(new_port(VAR,v12),new_port(VAR,v11)));
  link(net, tm, new_port(OPR,n25), new_port(NUM,0x07c37c67));
  node_create(net, n26, new_pair(new_port(NUM,0x08240003),new_port(VAR,v12)));
  link(net, tm, new_port(OPR,n26), new_port(NUM,0x08240012));
  node_create(net, n28, new_pair(new_port(REF,0x00000031),new_port(VAR,ve)));
  node_create(net, n27, new_pair(new_port(VAR,v13),new_port(CON,n28)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n27));
  node_create(net, n2b, new_pair(new_port(VAR,v16),new_port(VAR,v13)));
  node_create(net, n2a, new_pair(new_port(VAR,v15),new_port(CON,n2b)));
  node_create(net, n29, new_pair(new_port(VAR,v14),new_port(CON,n2a)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n29));
  node_create(net, n2e, new_pair(new_port(NUM,0x07de77a3),new_port(VAR,v14)));
  node_create(net, n2d, new_pair(new_port(NUM,0x07e15d63),new_port(CON,n2e)));
  node_create(net, n2c, new_pair(new_port(NUM,0x07eef463),new_port(CON,n2d)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n2c));
  node_create(net, n31, new_pair(new_port(NUM,0x07ee43a3),new_port(VAR,v15)));
  node_create(net, n30, new_pair(new_port(NUM,0x07e15b23),new_port(CON,n31)));
  node_create(net, n2f, new_pair(new_port(NUM,0x07d11e83),new_port(CON,n30)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n2f));
  node_create(net, n32, new_pair(new_port(VAR,v17),new_port(VAR,v16)));
  link(net, tm, new_port(OPR,n32), new_port(NUM,0x07d28547));
  node_create(net, n33, new_pair(new_port(NUM,0x08240003),new_port(VAR,v17)));
  link(net, tm, new_port(OPR,n33), new_port(NUM,0x08240012));
  return true;
}

bool interact_call_get_particles__C0(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val v7 = vars_alloc_1(net, tm, &vl);
  Val v8 = vars_alloc_1(net, tm, &vl);
  Val v9 = vars_alloc_1(net, tm, &vl);
  Val va = vars_alloc_1(net, tm, &vl);
  Val vb = vars_alloc_1(net, tm, &vl);
  Val vc = vars_alloc_1(net, tm, &vl);
  Val vd = vars_alloc_1(net, tm, &vl);
  Val ve = vars_alloc_1(net, tm, &vl);
  Val vf = vars_alloc_1(net, tm, &vl);
  Val v10 = vars_alloc_1(net, tm, &vl);
  Val v11 = vars_alloc_1(net, tm, &vl);
  Val v12 = vars_alloc_1(net, tm, &vl);
  Val v13 = vars_alloc_1(net, tm, &vl);
  Val v14 = vars_alloc_1(net, tm, &vl);
  Val v15 = vars_alloc_1(net, tm, &vl);
  Val v16 = vars_alloc_1(net, tm, &vl);
  Val v17 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  Val nf = node_alloc_1(net, tm, &nl);
  Val n10 = node_alloc_1(net, tm, &nl);
  Val n11 = node_alloc_1(net, tm, &nl);
  Val n12 = node_alloc_1(net, tm, &nl);
  Val n13 = node_alloc_1(net, tm, &nl);
  Val n14 = node_alloc_1(net, tm, &nl);
  Val n15 = node_alloc_1(net, tm, &nl);
  Val n16 = node_alloc_1(net, tm, &nl);
  Val n17 = node_alloc_1(net, tm, &nl);
  Val n18 = node_alloc_1(net, tm, &nl);
  Val n19 = node_alloc_1(net, tm, &nl);
  Val n1a = node_alloc_1(net, tm, &nl);
  Val n1b = node_alloc_1(net, tm, &nl);
  Val n1c = node_alloc_1(net, tm, &nl);
  Val n1d = node_alloc_1(net, tm, &nl);
  Val n1e = node_alloc_1(net, tm, &nl);
  Val n1f = node_alloc_1(net, tm, &nl);
  Val n20 = node_alloc_1(net, tm, &nl);
  Val n21 = node_alloc_1(net, tm, &nl);
  Val n22 = node_alloc_1(net, tm, &nl);
  Val n23 = node_alloc_1(net, tm, &nl);
  Val n24 = node_alloc_1(net, tm, &nl);
  Val n25 = node_alloc_1(net, tm, &nl);
  Val n26 = node_alloc_1(net, tm, &nl);
  Val n27 = node_alloc_1(net, tm, &nl);
  Val n28 = node_alloc_1(net, tm, &nl);
  Val n29 = node_alloc_1(net, tm, &nl);
  Val n2a = node_alloc_1(net, tm, &nl);
  Val n2b = node_alloc_1(net, tm, &nl);
  Val n2c = node_alloc_1(net, tm, &nl);
  Val n2d = node_alloc_1(net, tm, &nl);
  Val n2e = node_alloc_1(net, tm, &nl);
  Val n2f = node_alloc_1(net, tm, &nl);
  Val n30 = node_alloc_1(net, tm, &nl);
  Val n31 = node_alloc_1(net, tm, &nl);
  Val n32 = node_alloc_1(net, tm, &nl);
  Val n33 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !v7 || !v8 || !v9 || !va || !vb || !vc || !vd || !ve || !vf || !v10 || !v11 || !v12 || !v13 || !v14 || !v15 || !v16 || !v17 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne || !nf || !n10 || !n11 || !n12 || !n13 || !n14 || !n15 || !n16 || !n17 || !n18 || !n19 || !n1a || !n1b || !n1c || !n1d || !n1e || !n1f || !n20 || !n21 || !n22 || !n23 || !n24 || !n25 || !n26 || !n27 || !n28 || !n29 || !n2a || !n2b || !n2c || !n2d || !n2e || !n2f || !n30 || !n31 || !n32 || !n33) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  vars_create(net, v7, NONE);
  vars_create(net, v8, NONE);
  vars_create(net, v9, NONE);
  vars_create(net, va, NONE);
  vars_create(net, vb, NONE);
  vars_create(net, vc, NONE);
  vars_create(net, vd, NONE);
  vars_create(net, ve, NONE);
  vars_create(net, vf, NONE);
  vars_create(net, v10, NONE);
  vars_create(net, v11, NONE);
  vars_create(net, v12, NONE);
  vars_create(net, v13, NONE);
  vars_create(net, v14, NONE);
  vars_create(net, v15, NONE);
  vars_create(net, v16, NONE);
  vars_create(net, v17, NONE);
  if (b != NONE) {
    link(net, tm, new_port(VAR,v0), b);
  } else {
    b = new_port(VAR,v0);
  }
  node_create(net, n1, new_pair(new_port(VAR,v2),new_port(VAR,v0)));
  node_create(net, n0, new_pair(new_port(VAR,v1),new_port(CON,n1)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n0));
  node_create(net, n4, new_pair(new_port(VAR,v5),new_port(VAR,v1)));
  node_create(net, n3, new_pair(new_port(VAR,v4),new_port(CON,n4)));
  node_create(net, n2, new_pair(new_port(VAR,v3),new_port(CON,n3)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n2));
  node_create(net, n7, new_pair(new_port(NUM,0x07de0083),new_port(VAR,v3)));
  node_create(net, n6, new_pair(new_port(NUM,0x07ece9a3),new_port(CON,n7)));
  node_create(net, n5, new_pair(new_port(NUM,0x07eb7f63),new_port(CON,n6)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n5));
  node_create(net, na, new_pair(new_port(NUM,0x07b3d163),new_port(VAR,v4)));
  node_create(net, n9, new_pair(new_port(NUM,0x07d2a023),new_port(CON,na)));
  node_create(net, n8, new_pair(new_port(NUM,0x07eba743),new_port(CON,n9)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n8));
  node_create(net, nb, new_pair(new_port(VAR,v6),new_port(VAR,v5)));
  link(net, tm, new_port(OPR,nb), new_port(NUM,0x07ebd667));
  node_create(net, nc, new_pair(new_port(NUM,0x08240003),new_port(VAR,v6)));
  link(net, tm, new_port(OPR,nc), new_port(NUM,0x08240012));
  node_create(net, ne, new_pair(new_port(VAR,v8),new_port(VAR,v2)));
  node_create(net, nd, new_pair(new_port(VAR,v7),new_port(CON,ne)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,nd));
  node_create(net, n11, new_pair(new_port(VAR,vb),new_port(VAR,v7)));
  node_create(net, n10, new_pair(new_port(VAR,va),new_port(CON,n11)));
  node_create(net, nf, new_pair(new_port(VAR,v9),new_port(CON,n10)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,nf));
  node_create(net, n14, new_pair(new_port(NUM,0x07e56763),new_port(VAR,v9)));
  node_create(net, n13, new_pair(new_port(NUM,0x07e49d23),new_port(CON,n14)));
  node_create(net, n12, new_pair(new_port(NUM,0x07ed3ca3),new_port(CON,n13)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n12));
  node_create(net, n17, new_pair(new_port(NUM,0x07eb47a3),new_port(VAR,va)));
  node_create(net, n16, new_pair(new_port(NUM,0x07ea4963),new_port(CON,n17)));
  node_create(net, n15, new_pair(new_port(NUM,0x07ef1863),new_port(CON,n16)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n15));
  node_create(net, n18, new_pair(new_port(VAR,vc),new_port(VAR,vb)));
  link(net, tm, new_port(OPR,n18), new_port(NUM,0x07d665a7));
  node_create(net, n19, new_pair(new_port(NUM,0x08240003),new_port(VAR,vc)));
  link(net, tm, new_port(OPR,n19), new_port(NUM,0x08240012));
  node_create(net, n1b, new_pair(new_port(VAR,ve),new_port(VAR,v8)));
  node_create(net, n1a, new_pair(new_port(VAR,vd),new_port(CON,n1b)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n1a));
  node_create(net, n1e, new_pair(new_port(VAR,v11),new_port(VAR,vd)));
  node_create(net, n1d, new_pair(new_port(VAR,v10),new_port(CON,n1e)));
  node_create(net, n1c, new_pair(new_port(VAR,vf),new_port(CON,n1d)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n1c));
  node_create(net, n21, new_pair(new_port(NUM,0x07d63023),new_port(VAR,vf)));
  node_create(net, n20, new_pair(new_port(NUM,0x07dbd8e3),new_port(CON,n21)));
  node_create(net, n1f, new_pair(new_port(NUM,0x07de5f63),new_port(CON,n20)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n1f));
  node_create(net, n24, new_pair(new_port(NUM,0x07e4d583),new_port(VAR,v10)));
  node_create(net, n23, new_pair(new_port(NUM,0x07d59a03),new_port(CON,n24)));
  node_create(net, n22, new_pair(new_port(NUM,0x07d13c43),new_port(CON,n23)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n22));
  node_create(net, n25, new_pair(new_port(VAR,v12),new_port(VAR,v11)));
  link(net, tm, new_port(OPR,n25), new_port(NUM,0x07e97a07));
  node_create(net, n26, new_pair(new_port(NUM,0x08240003),new_port(VAR,v12)));
  link(net, tm, new_port(OPR,n26), new_port(NUM,0x08240012));
  node_create(net, n28, new_pair(new_port(REF,0x00000003),new_port(VAR,ve)));
  node_create(net, n27, new_pair(new_port(VAR,v13),new_port(CON,n28)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n27));
  node_create(net, n2b, new_pair(new_port(VAR,v16),new_port(VAR,v13)));
  node_create(net, n2a, new_pair(new_port(VAR,v15),new_port(CON,n2b)));
  node_create(net, n29, new_pair(new_port(VAR,v14),new_port(CON,n2a)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n29));
  node_create(net, n2e, new_pair(new_port(NUM,0x07c8d683),new_port(VAR,v14)));
  node_create(net, n2d, new_pair(new_port(NUM,0x07e07403),new_port(CON,n2e)));
  node_create(net, n2c, new_pair(new_port(NUM,0x07e45643),new_port(CON,n2d)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n2c));
  node_create(net, n31, new_pair(new_port(NUM,0x07effb63),new_port(VAR,v15)));
  node_create(net, n30, new_pair(new_port(NUM,0x07c7b5a3),new_port(CON,n31)));
  node_create(net, n2f, new_pair(new_port(NUM,0x07bd1f63),new_port(CON,n30)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n2f));
  node_create(net, n32, new_pair(new_port(VAR,v17),new_port(VAR,v16)));
  link(net, tm, new_port(OPR,n32), new_port(NUM,0x07ed6aa7));
  node_create(net, n33, new_pair(new_port(NUM,0x08240003),new_port(VAR,v17)));
  link(net, tm, new_port(OPR,n33), new_port(NUM,0x08240012));
  return true;
}

bool interact_call_get_particles__C1(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val v7 = vars_alloc_1(net, tm, &vl);
  Val v8 = vars_alloc_1(net, tm, &vl);
  Val v9 = vars_alloc_1(net, tm, &vl);
  Val va = vars_alloc_1(net, tm, &vl);
  Val vb = vars_alloc_1(net, tm, &vl);
  Val vc = vars_alloc_1(net, tm, &vl);
  Val vd = vars_alloc_1(net, tm, &vl);
  Val ve = vars_alloc_1(net, tm, &vl);
  Val vf = vars_alloc_1(net, tm, &vl);
  Val v10 = vars_alloc_1(net, tm, &vl);
  Val v11 = vars_alloc_1(net, tm, &vl);
  Val v12 = vars_alloc_1(net, tm, &vl);
  Val v13 = vars_alloc_1(net, tm, &vl);
  Val v14 = vars_alloc_1(net, tm, &vl);
  Val v15 = vars_alloc_1(net, tm, &vl);
  Val v16 = vars_alloc_1(net, tm, &vl);
  Val v17 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  Val nf = node_alloc_1(net, tm, &nl);
  Val n10 = node_alloc_1(net, tm, &nl);
  Val n11 = node_alloc_1(net, tm, &nl);
  Val n12 = node_alloc_1(net, tm, &nl);
  Val n13 = node_alloc_1(net, tm, &nl);
  Val n14 = node_alloc_1(net, tm, &nl);
  Val n15 = node_alloc_1(net, tm, &nl);
  Val n16 = node_alloc_1(net, tm, &nl);
  Val n17 = node_alloc_1(net, tm, &nl);
  Val n18 = node_alloc_1(net, tm, &nl);
  Val n19 = node_alloc_1(net, tm, &nl);
  Val n1a = node_alloc_1(net, tm, &nl);
  Val n1b = node_alloc_1(net, tm, &nl);
  Val n1c = node_alloc_1(net, tm, &nl);
  Val n1d = node_alloc_1(net, tm, &nl);
  Val n1e = node_alloc_1(net, tm, &nl);
  Val n1f = node_alloc_1(net, tm, &nl);
  Val n20 = node_alloc_1(net, tm, &nl);
  Val n21 = node_alloc_1(net, tm, &nl);
  Val n22 = node_alloc_1(net, tm, &nl);
  Val n23 = node_alloc_1(net, tm, &nl);
  Val n24 = node_alloc_1(net, tm, &nl);
  Val n25 = node_alloc_1(net, tm, &nl);
  Val n26 = node_alloc_1(net, tm, &nl);
  Val n27 = node_alloc_1(net, tm, &nl);
  Val n28 = node_alloc_1(net, tm, &nl);
  Val n29 = node_alloc_1(net, tm, &nl);
  Val n2a = node_alloc_1(net, tm, &nl);
  Val n2b = node_alloc_1(net, tm, &nl);
  Val n2c = node_alloc_1(net, tm, &nl);
  Val n2d = node_alloc_1(net, tm, &nl);
  Val n2e = node_alloc_1(net, tm, &nl);
  Val n2f = node_alloc_1(net, tm, &nl);
  Val n30 = node_alloc_1(net, tm, &nl);
  Val n31 = node_alloc_1(net, tm, &nl);
  Val n32 = node_alloc_1(net, tm, &nl);
  Val n33 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !v7 || !v8 || !v9 || !va || !vb || !vc || !vd || !ve || !vf || !v10 || !v11 || !v12 || !v13 || !v14 || !v15 || !v16 || !v17 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne || !nf || !n10 || !n11 || !n12 || !n13 || !n14 || !n15 || !n16 || !n17 || !n18 || !n19 || !n1a || !n1b || !n1c || !n1d || !n1e || !n1f || !n20 || !n21 || !n22 || !n23 || !n24 || !n25 || !n26 || !n27 || !n28 || !n29 || !n2a || !n2b || !n2c || !n2d || !n2e || !n2f || !n30 || !n31 || !n32 || !n33) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  vars_create(net, v7, NONE);
  vars_create(net, v8, NONE);
  vars_create(net, v9, NONE);
  vars_create(net, va, NONE);
  vars_create(net, vb, NONE);
  vars_create(net, vc, NONE);
  vars_create(net, vd, NONE);
  vars_create(net, ve, NONE);
  vars_create(net, vf, NONE);
  vars_create(net, v10, NONE);
  vars_create(net, v11, NONE);
  vars_create(net, v12, NONE);
  vars_create(net, v13, NONE);
  vars_create(net, v14, NONE);
  vars_create(net, v15, NONE);
  vars_create(net, v16, NONE);
  vars_create(net, v17, NONE);
  if (b != NONE) {
    link(net, tm, new_port(VAR,v0), b);
  } else {
    b = new_port(VAR,v0);
  }
  node_create(net, n1, new_pair(new_port(VAR,v2),new_port(VAR,v0)));
  node_create(net, n0, new_pair(new_port(VAR,v1),new_port(CON,n1)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n0));
  node_create(net, n4, new_pair(new_port(VAR,v5),new_port(VAR,v1)));
  node_create(net, n3, new_pair(new_port(VAR,v4),new_port(CON,n4)));
  node_create(net, n2, new_pair(new_port(VAR,v3),new_port(CON,n3)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n2));
  node_create(net, n7, new_pair(new_port(NUM,0x07ecd583),new_port(VAR,v3)));
  node_create(net, n6, new_pair(new_port(NUM,0x07a27783),new_port(CON,n7)));
  node_create(net, n5, new_pair(new_port(NUM,0x07c09e43),new_port(CON,n6)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n5));
  node_create(net, na, new_pair(new_port(NUM,0x07e35da3),new_port(VAR,v4)));
  node_create(net, n9, new_pair(new_port(NUM,0x07e3dce3),new_port(CON,na)));
  node_create(net, n8, new_pair(new_port(NUM,0x07d5dfe3),new_port(CON,n9)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n8));
  node_create(net, nb, new_pair(new_port(VAR,v6),new_port(VAR,v5)));
  link(net, tm, new_port(OPR,nb), new_port(NUM,0x07e401a7));
  node_create(net, nc, new_pair(new_port(NUM,0x08240003),new_port(VAR,v6)));
  link(net, tm, new_port(OPR,nc), new_port(NUM,0x08240012));
  node_create(net, ne, new_pair(new_port(VAR,v8),new_port(VAR,v2)));
  node_create(net, nd, new_pair(new_port(VAR,v7),new_port(CON,ne)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,nd));
  node_create(net, n11, new_pair(new_port(VAR,vb),new_port(VAR,v7)));
  node_create(net, n10, new_pair(new_port(VAR,va),new_port(CON,n11)));
  node_create(net, nf, new_pair(new_port(VAR,v9),new_port(CON,n10)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,nf));
  node_create(net, n14, new_pair(new_port(NUM,0x07e97463),new_port(VAR,v9)));
  node_create(net, n13, new_pair(new_port(NUM,0x07cd8223),new_port(CON,n14)));
  node_create(net, n12, new_pair(new_port(NUM,0x07d70d63),new_port(CON,n13)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n12));
  node_create(net, n17, new_pair(new_port(NUM,0x07eec883),new_port(VAR,va)));
  node_create(net, n16, new_pair(new_port(NUM,0x07df0a03),new_port(CON,n17)));
  node_create(net, n15, new_pair(new_port(NUM,0x07e4a8e3),new_port(CON,n16)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n15));
  node_create(net, n18, new_pair(new_port(VAR,vc),new_port(VAR,vb)));
  link(net, tm, new_port(OPR,n18), new_port(NUM,0x07eb27c7));
  node_create(net, n19, new_pair(new_port(NUM,0x08240003),new_port(VAR,vc)));
  link(net, tm, new_port(OPR,n19), new_port(NUM,0x08240012));
  node_create(net, n1b, new_pair(new_port(VAR,ve),new_port(VAR,v8)));
  node_create(net, n1a, new_pair(new_port(VAR,vd),new_port(CON,n1b)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n1a));
  node_create(net, n1e, new_pair(new_port(VAR,v11),new_port(VAR,vd)));
  node_create(net, n1d, new_pair(new_port(VAR,v10),new_port(CON,n1e)));
  node_create(net, n1c, new_pair(new_port(VAR,vf),new_port(CON,n1d)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n1c));
  node_create(net, n21, new_pair(new_port(NUM,0x07c22d03),new_port(VAR,vf)));
  node_create(net, n20, new_pair(new_port(NUM,0x07e2fee3),new_port(CON,n21)));
  node_create(net, n1f, new_pair(new_port(NUM,0x07eeec03),new_port(CON,n20)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n1f));
  node_create(net, n24, new_pair(new_port(NUM,0x07db11a3),new_port(VAR,v10)));
  node_create(net, n23, new_pair(new_port(NUM,0x07c09423),new_port(CON,n24)));
  node_create(net, n22, new_pair(new_port(NUM,0x07e5b103),new_port(CON,n23)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n22));
  node_create(net, n25, new_pair(new_port(VAR,v12),new_port(VAR,v11)));
  link(net, tm, new_port(OPR,n25), new_port(NUM,0x07ee33e7));
  node_create(net, n26, new_pair(new_port(NUM,0x08240003),new_port(VAR,v12)));
  link(net, tm, new_port(OPR,n26), new_port(NUM,0x08240012));
  node_create(net, n28, new_pair(new_port(REF,0x00000030),new_port(VAR,ve)));
  node_create(net, n27, new_pair(new_port(VAR,v13),new_port(CON,n28)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n27));
  node_create(net, n2b, new_pair(new_port(VAR,v16),new_port(VAR,v13)));
  node_create(net, n2a, new_pair(new_port(VAR,v15),new_port(CON,n2b)));
  node_create(net, n29, new_pair(new_port(VAR,v14),new_port(CON,n2a)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n29));
  node_create(net, n2e, new_pair(new_port(NUM,0x07eecb63),new_port(VAR,v14)));
  node_create(net, n2d, new_pair(new_port(NUM,0x07d0dd83),new_port(CON,n2e)));
  node_create(net, n2c, new_pair(new_port(NUM,0x07ef2663),new_port(CON,n2d)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n2c));
  node_create(net, n31, new_pair(new_port(NUM,0x07cdcbe3),new_port(VAR,v15)));
  node_create(net, n30, new_pair(new_port(NUM,0x07e21323),new_port(CON,n31)));
  node_create(net, n2f, new_pair(new_port(NUM,0x07b76863),new_port(CON,n30)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,n2f));
  node_create(net, n32, new_pair(new_port(VAR,v17),new_port(VAR,v16)));
  link(net, tm, new_port(OPR,n32), new_port(NUM,0x078d6ae7));
  node_create(net, n33, new_pair(new_port(NUM,0x08240003),new_port(VAR,v17)));
  link(net, tm, new_port(OPR,n33), new_port(NUM,0x08240012));
  return true;
}

bool interact_call_multiply(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x00000034), k7);
  } else {
    k7 = new_port(REF,0x00000034);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_multiply__C0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v6), k16);
  } else {
    k16 = new_port(VAR,v6);
  }
  bool k17 = 0;
  Port k18 = NONE;
  Port k19 = NONE;
  // fast copy
  if (get_tag(k15) == NUM) {
    tm->itrs += 1;
    k17 = 1;
    k18 = k15;
    k19 = k15;
  }
  bool k20 = 0;
  Port k21 = NONE;
  Port k22 = NONE;
  // fast copy
  if (get_tag(k19) == NUM) {
    tm->itrs += 1;
    k20 = 1;
    k21 = k19;
    k22 = k19;
  }
  if (k22 != NONE) {
    link(net, tm, new_port(VAR,v4), k22);
  } else {
    k22 = new_port(VAR,v4);
  }
  if (k21 != NONE) {
    link(net, tm, new_port(VAR,v2), k21);
  } else {
    k21 = new_port(VAR,v2);
  }
  if (!k20) {
    node_create(net, nb, new_pair(k21,k22));
    if (k19 != NONE) {
      link(net, tm, new_port(DUP,nb), k19);
    } else {
      k19 = new_port(DUP,nb);
    }
  }
  if (k18 != NONE) {
    link(net, tm, new_port(VAR,v0), k18);
  } else {
    k18 = new_port(VAR,v0);
  }
  if (!k17) {
    node_create(net, na, new_pair(k18,k19));
    if (k15 != NONE) {
      link(net, tm, new_port(DUP,na), k15);
    } else {
      k15 = new_port(DUP,na);
    }
  }
  if (!k13) {
    node_create(net, n9, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n9), k12);
    } else {
      k12 = new_port(CON,n9);
    }
  }
  bool k23 = 0;
  Port k24 = NONE;
  // fast oper
  if (get_tag(k11) == NUM && get_tag(new_port(NUM,0x000000e0)) == NUM) {
    tm->itrs += 1;
    k23 = 1;
    k24 = new_port(NUM, operate(get_val(k11), get_val(new_port(NUM,0x000000e0))));
  }
  bool k25 = 0;
  Port k26 = NONE;
  // fast oper
  if (get_tag(k24) == NUM && get_tag(new_port(VAR,v4)) == NUM) {
    tm->itrs += 1;
    k25 = 1;
    k26 = new_port(NUM, operate(get_val(k24), get_val(new_port(VAR,v4))));
  }
  if (k26 != NONE) {
    link(net, tm, new_port(VAR,v5), k26);
  } else {
    k26 = new_port(VAR,v5);
  }
  if (!k25) {
    node_create(net, n8, new_pair(new_port(VAR,v4),k26));
    if (k24 != NONE) {
      link(net, tm, new_port(OPR, n8), k24);
    } else {
      k24 = new_port(OPR, n8);
    }
  }
  if (!k23) {
    node_create(net, n7, new_pair(new_port(NUM,0x000000e0),k24));
    if (k11 != NONE) {
      link(net, tm, new_port(OPR, n7), k11);
    } else {
      k11 = new_port(OPR, n7);
    }
  }
  if (!k9) {
    node_create(net, n6, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n6), k8);
    } else {
      k8 = new_port(CON,n6);
    }
  }
  bool k27 = 0;
  Port k28 = NONE;
  // fast oper
  if (get_tag(k7) == NUM && get_tag(new_port(NUM,0x000000e0)) == NUM) {
    tm->itrs += 1;
    k27 = 1;
    k28 = new_port(NUM, operate(get_val(k7), get_val(new_port(NUM,0x000000e0))));
  }
  bool k29 = 0;
  Port k30 = NONE;
  // fast oper
  if (get_tag(k28) == NUM && get_tag(new_port(VAR,v2)) == NUM) {
    tm->itrs += 1;
    k29 = 1;
    k30 = new_port(NUM, operate(get_val(k28), get_val(new_port(VAR,v2))));
  }
  if (k30 != NONE) {
    link(net, tm, new_port(VAR,v3), k30);
  } else {
    k30 = new_port(VAR,v3);
  }
  if (!k29) {
    node_create(net, n5, new_pair(new_port(VAR,v2),k30));
    if (k28 != NONE) {
      link(net, tm, new_port(OPR, n5), k28);
    } else {
      k28 = new_port(OPR, n5);
    }
  }
  if (!k27) {
    node_create(net, n4, new_pair(new_port(NUM,0x000000e0),k28));
    if (k7 != NONE) {
      link(net, tm, new_port(OPR, n4), k7);
    } else {
      k7 = new_port(OPR, n4);
    }
  }
  if (!k5) {
    node_create(net, n3, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n3), k4);
    } else {
      k4 = new_port(CON,n3);
    }
  }
  bool k31 = 0;
  Port k32 = NONE;
  // fast oper
  if (get_tag(k3) == NUM && get_tag(new_port(NUM,0x000000e0)) == NUM) {
    tm->itrs += 1;
    k31 = 1;
    k32 = new_port(NUM, operate(get_val(k3), get_val(new_port(NUM,0x000000e0))));
  }
  bool k33 = 0;
  Port k34 = NONE;
  // fast oper
  if (get_tag(k32) == NUM && get_tag(new_port(VAR,v0)) == NUM) {
    tm->itrs += 1;
    k33 = 1;
    k34 = new_port(NUM, operate(get_val(k32), get_val(new_port(VAR,v0))));
  }
  if (k34 != NONE) {
    link(net, tm, new_port(VAR,v1), k34);
  } else {
    k34 = new_port(VAR,v1);
  }
  if (!k33) {
    node_create(net, n2, new_pair(new_port(VAR,v0),k34));
    if (k32 != NONE) {
      link(net, tm, new_port(OPR, n2), k32);
    } else {
      k32 = new_port(OPR, n2);
    }
  }
  if (!k31) {
    node_create(net, n1, new_pair(new_port(NUM,0x000000e0),k32));
    if (k3 != NONE) {
      link(net, tm, new_port(OPR, n1), k3);
    } else {
      k3 = new_port(OPR, n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, ne, new_pair(new_port(VAR,v5),new_port(VAR,v6)));
  node_create(net, nd, new_pair(new_port(VAR,v3),new_port(CON,ne)));
  node_create(net, nc, new_pair(new_port(VAR,v1),new_port(CON,nd)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,nc));
  return true;
}

bool interact_call_multiply__C1(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x00000033), k3);
  } else {
    k3 = new_port(REF,0x00000033);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_normalize(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v2), k4);
  } else {
    k4 = new_port(VAR,v2);
  }
  bool k5 = 0;
  Port k6 = NONE;
  Port k7 = NONE;
  // fast copy
  if (get_tag(k3) == NUM) {
    tm->itrs += 1;
    k5 = 1;
    k6 = k3;
    k7 = k3;
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (k6 != NONE) {
    link(net, tm, new_port(VAR,v0), k6);
  } else {
    k6 = new_port(VAR,v0);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k6,k7));
    if (k3 != NONE) {
      link(net, tm, new_port(DUP,n1), k3);
    } else {
      k3 = new_port(DUP,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n3, new_pair(new_port(VAR,v3),new_port(VAR,v2)));
  node_create(net, n2, new_pair(new_port(VAR,v0),new_port(CON,n3)));
  link(net, tm, new_port(REF,0x0000002a), new_port(CON,n2));
  node_create(net, n5, new_pair(new_port(VAR,v1),new_port(VAR,v3)));
  node_create(net, n4, new_pair(new_port(REF,0x0000002e),new_port(CON,n5)));
  link(net, tm, new_port(REF,0x00000025), new_port(CON,n4));
  return true;
}

bool interact_call_simulate(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v3), k8);
  } else {
    k8 = new_port(VAR,v3);
  }
  bool k9 = 0;
  Port k10 = NONE;
  Port k11 = NONE;
  // fast copy
  if (get_tag(k7) == NUM) {
    tm->itrs += 1;
    k9 = 1;
    k10 = k7;
    k11 = k7;
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  bool k12 = 0;
  Port k13 = NONE;
  // fast oper
  if (get_tag(k10) == NUM && get_tag(new_port(NUM,0x0000000c)) == NUM) {
    tm->itrs += 1;
    k12 = 1;
    k13 = new_port(NUM, operate(get_val(k10), get_val(new_port(NUM,0x0000000c))));
  }
  node_create(net, n9, new_pair(new_port(ERA,0x00000000),new_port(VAR,v1)));
  node_create(net, n8, new_pair(new_port(ERA,0x00000000),new_port(CON,n9)));
  node_create(net, n7, new_pair(new_port(VAR,v1),new_port(CON,n8)));
  node_create(net, n6, new_pair(new_port(ERA,0x00000000),new_port(CON,n7)));
  node_create(net, n5, new_pair(new_port(REF,0x00000037),new_port(CON,n6)));
  node_create(net, nb, new_pair(new_port(VAR,v2),new_port(VAR,v3)));
  node_create(net, na, new_pair(new_port(VAR,v0),new_port(CON,nb)));
  node_create(net, n4, new_pair(new_port(CON,n5),new_port(CON,na)));
  if (k13 != NONE) {
    link(net, tm, new_port(SWI,n4), k13);
  } else {
    k13 = new_port(SWI,n4);
  }
  if (!k12) {
    node_create(net, n3, new_pair(new_port(NUM,0x0000000c),k13));
    if (k10 != NONE) {
      link(net, tm, new_port(OPR, n3), k10);
    } else {
      k10 = new_port(OPR, n3);
    }
  }
  if (!k9) {
    node_create(net, n2, new_pair(k10,k11));
    if (k7 != NONE) {
      link(net, tm, new_port(DUP,n2), k7);
    } else {
      k7 = new_port(DUP,n2);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_simulate__C0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  if (k12 != NONE) {
    link(net, tm, new_port(VAR,v4), k12);
  } else {
    k12 = new_port(VAR,v4);
  }
  bool k13 = 0;
  Port k14 = NONE;
  Port k15 = NONE;
  // fast copy
  if (get_tag(k11) == NUM) {
    tm->itrs += 1;
    k13 = 1;
    k14 = k11;
    k15 = k11;
  }
  if (k15 != NONE) {
    link(net, tm, new_port(VAR,v3), k15);
  } else {
    k15 = new_port(VAR,v3);
  }
  if (k14 != NONE) {
    link(net, tm, new_port(VAR,v2), k14);
  } else {
    k14 = new_port(VAR,v2);
  }
  if (!k13) {
    node_create(net, n4, new_pair(k14,k15));
    if (k11 != NONE) {
      link(net, tm, new_port(DUP,n4), k11);
    } else {
      k11 = new_port(DUP,n4);
    }
  }
  if (!k9) {
    node_create(net, n3, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n3), k8);
    } else {
      k8 = new_port(CON,n3);
    }
  }
  bool k16 = 0;
  Port k17 = NONE;
  // fast oper
  if (get_tag(k7) == NUM && get_tag(new_port(NUM,0x00000026)) == NUM) {
    tm->itrs += 1;
    k16 = 1;
    k17 = new_port(NUM, operate(get_val(k7), get_val(new_port(NUM,0x00000026))));
  }
  if (k17 != NONE) {
    link(net, tm, new_port(VAR,v1), k17);
  } else {
    k17 = new_port(VAR,v1);
  }
  if (!k16) {
    node_create(net, n2, new_pair(new_port(NUM,0x00000026),k17));
    if (k7 != NONE) {
      link(net, tm, new_port(OPR, n2), k7);
    } else {
      k7 = new_port(OPR, n2);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n7, new_pair(new_port(VAR,v2),new_port(VAR,v4)));
  node_create(net, n6, new_pair(new_port(VAR,v1),new_port(CON,n7)));
  node_create(net, n5, new_pair(new_port(VAR,v5),new_port(CON,n6)));
  link(net, tm, new_port(REF,0x00000036), new_port(CON,n5));
  node_create(net, n9, new_pair(new_port(VAR,v3),new_port(VAR,v5)));
  node_create(net, n8, new_pair(new_port(VAR,v0),new_port(CON,n9)));
  link(net, tm, new_port(REF,0x0000003e), new_port(CON,n8));
  return true;
}

bool interact_call_subtract(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x0000003c), k7);
  } else {
    k7 = new_port(REF,0x0000003c);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_subtract__C0(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  if (k24 != NONE) {
    link(net, tm, new_port(VAR,v6), k24);
  } else {
    k24 = new_port(VAR,v6);
  }
  bool k25 = 0;
  Port k26 = NONE;
  // fast oper
  if (get_tag(k23) == NUM && get_tag(new_port(NUM,0x000000a0)) == NUM) {
    tm->itrs += 1;
    k25 = 1;
    k26 = new_port(NUM, operate(get_val(k23), get_val(new_port(NUM,0x000000a0))));
  }
  bool k27 = 0;
  Port k28 = NONE;
  // fast oper
  if (get_tag(k26) == NUM && get_tag(new_port(VAR,v2)) == NUM) {
    tm->itrs += 1;
    k27 = 1;
    k28 = new_port(NUM, operate(get_val(k26), get_val(new_port(VAR,v2))));
  }
  if (k28 != NONE) {
    link(net, tm, new_port(VAR,v5), k28);
  } else {
    k28 = new_port(VAR,v5);
  }
  if (!k27) {
    node_create(net, nb, new_pair(new_port(VAR,v2),k28));
    if (k26 != NONE) {
      link(net, tm, new_port(OPR, nb), k26);
    } else {
      k26 = new_port(OPR, nb);
    }
  }
  if (!k25) {
    node_create(net, na, new_pair(new_port(NUM,0x000000a0),k26));
    if (k23 != NONE) {
      link(net, tm, new_port(OPR, na), k23);
    } else {
      k23 = new_port(OPR, na);
    }
  }
  if (!k21) {
    node_create(net, n9, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n9), k20);
    } else {
      k20 = new_port(CON,n9);
    }
  }
  bool k29 = 0;
  Port k30 = NONE;
  // fast oper
  if (get_tag(k19) == NUM && get_tag(new_port(NUM,0x000000a0)) == NUM) {
    tm->itrs += 1;
    k29 = 1;
    k30 = new_port(NUM, operate(get_val(k19), get_val(new_port(NUM,0x000000a0))));
  }
  bool k31 = 0;
  Port k32 = NONE;
  // fast oper
  if (get_tag(k30) == NUM && get_tag(new_port(VAR,v1)) == NUM) {
    tm->itrs += 1;
    k31 = 1;
    k32 = new_port(NUM, operate(get_val(k30), get_val(new_port(VAR,v1))));
  }
  if (k32 != NONE) {
    link(net, tm, new_port(VAR,v4), k32);
  } else {
    k32 = new_port(VAR,v4);
  }
  if (!k31) {
    node_create(net, n8, new_pair(new_port(VAR,v1),k32));
    if (k30 != NONE) {
      link(net, tm, new_port(OPR, n8), k30);
    } else {
      k30 = new_port(OPR, n8);
    }
  }
  if (!k29) {
    node_create(net, n7, new_pair(new_port(NUM,0x000000a0),k30));
    if (k19 != NONE) {
      link(net, tm, new_port(OPR, n7), k19);
    } else {
      k19 = new_port(OPR, n7);
    }
  }
  if (!k17) {
    node_create(net, n6, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,n6), k16);
    } else {
      k16 = new_port(CON,n6);
    }
  }
  bool k33 = 0;
  Port k34 = NONE;
  // fast oper
  if (get_tag(k15) == NUM && get_tag(new_port(NUM,0x000000a0)) == NUM) {
    tm->itrs += 1;
    k33 = 1;
    k34 = new_port(NUM, operate(get_val(k15), get_val(new_port(NUM,0x000000a0))));
  }
  bool k35 = 0;
  Port k36 = NONE;
  // fast oper
  if (get_tag(k34) == NUM && get_tag(new_port(VAR,v0)) == NUM) {
    tm->itrs += 1;
    k35 = 1;
    k36 = new_port(NUM, operate(get_val(k34), get_val(new_port(VAR,v0))));
  }
  if (k36 != NONE) {
    link(net, tm, new_port(VAR,v3), k36);
  } else {
    k36 = new_port(VAR,v3);
  }
  if (!k35) {
    node_create(net, n5, new_pair(new_port(VAR,v0),k36));
    if (k34 != NONE) {
      link(net, tm, new_port(OPR, n5), k34);
    } else {
      k34 = new_port(OPR, n5);
    }
  }
  if (!k33) {
    node_create(net, n4, new_pair(new_port(NUM,0x000000a0),k34));
    if (k15 != NONE) {
      link(net, tm, new_port(OPR, n4), k15);
    } else {
      k15 = new_port(OPR, n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, ne, new_pair(new_port(VAR,v5),new_port(VAR,v6)));
  node_create(net, nd, new_pair(new_port(VAR,v4),new_port(CON,ne)));
  node_create(net, nc, new_pair(new_port(VAR,v3),new_port(CON,nd)));
  link(net, tm, new_port(REF,0x00000018), new_port(CON,nc));
  return true;
}

bool interact_call_subtract__C1(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x00000039), k3);
  } else {
    k3 = new_port(REF,0x00000039);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_subtract__C2(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v3), k16);
  } else {
    k16 = new_port(VAR,v3);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k15) == CON && node_load(net, get_val(k15)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k15));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  bool k21 = 0;
  Pair k22 = 0;
  Port k23 = NONE;
  Port k24 = NONE;
  // fast anni
  if (get_tag(k20) == CON && node_load(net, get_val(k20)) != 0) {
    tm->itrs += 1;
    k21 = 1;
    k22 = node_take(net, get_val(k20));
    k23 = get_fst(k22);
    k24 = get_snd(k22);
  }
  bool k25 = 0;
  Pair k26 = 0;
  Port k27 = NONE;
  Port k28 = NONE;
  // fast anni
  if (get_tag(k24) == CON && node_load(net, get_val(k24)) != 0) {
    tm->itrs += 1;
    k25 = 1;
    k26 = node_take(net, get_val(k24));
    k27 = get_fst(k26);
    k28 = get_snd(k26);
  }
  bool k29 = 0;
  Pair k30 = 0;
  Port k31 = NONE;
  Port k32 = NONE;
  // fast anni
  if (get_tag(k28) == CON && node_load(net, get_val(k28)) != 0) {
    tm->itrs += 1;
    k29 = 1;
    k30 = node_take(net, get_val(k28));
    k31 = get_fst(k30);
    k32 = get_snd(k30);
  }
  if (k32 != NONE) {
    link(net, tm, new_port(VAR,v3), k32);
  } else {
    k32 = new_port(VAR,v3);
  }
  if (k31 != NONE) {
    link(net, tm, new_port(VAR,v2), k31);
  } else {
    k31 = new_port(VAR,v2);
  }
  if (!k29) {
    node_create(net, n7, new_pair(k31,k32));
    if (k28 != NONE) {
      link(net, tm, new_port(CON,n7), k28);
    } else {
      k28 = new_port(CON,n7);
    }
  }
  if (k27 != NONE) {
    link(net, tm, new_port(VAR,v1), k27);
  } else {
    k27 = new_port(VAR,v1);
  }
  if (!k25) {
    node_create(net, n6, new_pair(k27,k28));
    if (k24 != NONE) {
      link(net, tm, new_port(CON,n6), k24);
    } else {
      k24 = new_port(CON,n6);
    }
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v0), k23);
  } else {
    k23 = new_port(VAR,v0);
  }
  if (!k21) {
    node_create(net, n5, new_pair(k23,k24));
    if (k20 != NONE) {
      link(net, tm, new_port(CON,n5), k20);
    } else {
      k20 = new_port(CON,n5);
    }
  }
  if (k19 != NONE) {
    link(net, tm, new_port(REF,0x0000003a), k19);
  } else {
    k19 = new_port(REF,0x0000003a);
  }
  if (!k17) {
    node_create(net, n4, new_pair(k19,k20));
    if (k15 != NONE) {
      link(net, tm, new_port(CON,n4), k15);
    } else {
      k15 = new_port(CON,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v2), k11);
  } else {
    k11 = new_port(VAR,v2);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_subtract__C3(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x0000003b), k3);
  } else {
    k3 = new_port(REF,0x0000003b);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_unreachable(Net *net, TM *tm, Port a, Port b) {
  if (get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }
  u32 vl = 0;
  u32 nl = 0;
  if (0) {
    return false;
  }
  // fast void
  if (get_tag(b) == ERA || get_tag(b) == NUM) {
    tm->itrs += 1;
  } else {
    if (b != NONE) {
      link(net, tm, new_port(ERA,0x00000000), b);
    } else {
      b = new_port(ERA,0x00000000);
    }
  }
  return true;
}

bool interact_call_update_all_particles(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !n0 || !n1 || !n2 || !n3) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v2), k4);
  } else {
    k4 = new_port(VAR,v2);
  }
  bool k5 = 0;
  Port k6 = NONE;
  Port k7 = NONE;
  // fast copy
  if (get_tag(k3) == NUM) {
    tm->itrs += 1;
    k5 = 1;
    k6 = k3;
    k7 = k3;
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v1), k7);
  } else {
    k7 = new_port(VAR,v1);
  }
  if (k6 != NONE) {
    link(net, tm, new_port(VAR,v0), k6);
  } else {
    k6 = new_port(VAR,v0);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k6,k7));
    if (k3 != NONE) {
      link(net, tm, new_port(DUP,n1), k3);
    } else {
      k3 = new_port(DUP,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n3, new_pair(new_port(VAR,v1),new_port(VAR,v2)));
  node_create(net, n2, new_pair(new_port(VAR,v0),new_port(CON,n3)));
  link(net, tm, new_port(REF,0x0000003f), new_port(CON,n2));
  return true;
}

bool interact_call_update_all_particles__fold0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x00000041), k7);
  } else {
    k7 = new_port(REF,0x00000041);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_update_all_particles__fold0__C0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val v7 = vars_alloc_1(net, tm, &vl);
  Val v8 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !v7 || !v8 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  vars_create(net, v7, NONE);
  vars_create(net, v8, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  if (k20 != NONE) {
    link(net, tm, new_port(VAR,v6), k20);
  } else {
    k20 = new_port(VAR,v6);
  }
  bool k21 = 0;
  Port k22 = NONE;
  Port k23 = NONE;
  // fast copy
  if (get_tag(k19) == NUM) {
    tm->itrs += 1;
    k21 = 1;
    k22 = k19;
    k23 = k19;
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v5), k23);
  } else {
    k23 = new_port(VAR,v5);
  }
  if (k22 != NONE) {
    link(net, tm, new_port(VAR,v4), k22);
  } else {
    k22 = new_port(VAR,v4);
  }
  if (!k21) {
    node_create(net, n6, new_pair(k22,k23));
    if (k19 != NONE) {
      link(net, tm, new_port(DUP,n6), k19);
    } else {
      k19 = new_port(DUP,n6);
    }
  }
  if (!k17) {
    node_create(net, n5, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,n5), k16);
    } else {
      k16 = new_port(CON,n5);
    }
  }
  bool k24 = 0;
  Port k25 = NONE;
  Port k26 = NONE;
  // fast copy
  if (get_tag(k15) == NUM) {
    tm->itrs += 1;
    k24 = 1;
    k25 = k15;
    k26 = k15;
  }
  if (k26 != NONE) {
    link(net, tm, new_port(VAR,v3), k26);
  } else {
    k26 = new_port(VAR,v3);
  }
  if (k25 != NONE) {
    link(net, tm, new_port(VAR,v2), k25);
  } else {
    k25 = new_port(VAR,v2);
  }
  if (!k24) {
    node_create(net, n4, new_pair(k25,k26));
    if (k15 != NONE) {
      link(net, tm, new_port(DUP,n4), k15);
    } else {
      k15 = new_port(DUP,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v1), k11);
  } else {
    k11 = new_port(VAR,v1);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v0), k7);
  } else {
    k7 = new_port(VAR,v0);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  // fast void
  if (get_tag(k3) == ERA || get_tag(k3) == NUM) {
    tm->itrs += 1;
  } else {
    if (k3 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k3);
    } else {
      k3 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n8, new_pair(new_port(VAR,v8),new_port(VAR,v6)));
  node_create(net, n7, new_pair(new_port(VAR,v7),new_port(CON,n8)));
  link(net, tm, new_port(REF,0x00000001), new_port(CON,n7));
  node_create(net, nb, new_pair(new_port(VAR,v4),new_port(VAR,v7)));
  node_create(net, na, new_pair(new_port(VAR,v2),new_port(CON,nb)));
  node_create(net, n9, new_pair(new_port(VAR,v0),new_port(CON,na)));
  link(net, tm, new_port(REF,0x00000042), new_port(CON,n9));
  node_create(net, ne, new_pair(new_port(VAR,v5),new_port(VAR,v8)));
  node_create(net, nd, new_pair(new_port(VAR,v3),new_port(CON,ne)));
  node_create(net, nc, new_pair(new_port(VAR,v1),new_port(CON,nd)));
  link(net, tm, new_port(REF,0x0000003f), new_port(CON,nc));
  return true;
}

bool interact_call_update_all_particles__fold0__C1(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2 || !n3 || !n4) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  bool k6 = 0;
  Pair k7 = 0;
  Port k8 = NONE;
  Port k9 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k6 = 1;
    k7 = node_take(net, get_val(k3));
    k8 = get_fst(k7);
    k9 = get_snd(k7);
  }
  bool k10 = 0;
  Pair k11 = 0;
  Port k12 = NONE;
  Port k13 = NONE;
  // fast anni
  if (get_tag(k9) == CON && node_load(net, get_val(k9)) != 0) {
    tm->itrs += 1;
    k10 = 1;
    k11 = node_take(net, get_val(k9));
    k12 = get_fst(k11);
    k13 = get_snd(k11);
  }
  if (k13 != NONE) {
    link(net, tm, new_port(REF,0x00000003), k13);
  } else {
    k13 = new_port(REF,0x00000003);
  }
  // fast void
  if (get_tag(k12) == ERA || get_tag(k12) == NUM) {
    tm->itrs += 1;
  } else {
    if (k12 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k12);
    } else {
      k12 = new_port(ERA,0x00000000);
    }
  }
  if (!k10) {
    node_create(net, n4, new_pair(k12,k13));
    if (k9 != NONE) {
      link(net, tm, new_port(CON,n4), k9);
    } else {
      k9 = new_port(CON,n4);
    }
  }
  // fast void
  if (get_tag(k8) == ERA || get_tag(k8) == NUM) {
    tm->itrs += 1;
  } else {
    if (k8 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k8);
    } else {
      k8 = new_port(ERA,0x00000000);
    }
  }
  if (!k6) {
    node_create(net, n3, new_pair(k8,k9));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n3), k3);
    } else {
      k3 = new_port(CON,n3);
    }
  }
  if (k4 != NONE) {
    link(net, tm, new_port(REF,0x00000040), k4);
  } else {
    k4 = new_port(REF,0x00000040);
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_update_particle(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  if (k12 != NONE) {
    link(net, tm, new_port(VAR,v2), k12);
  } else {
    k12 = new_port(VAR,v2);
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v0), k11);
  } else {
    k11 = new_port(VAR,v0);
  }
  if (!k9) {
    node_create(net, n6, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n6), k8);
    } else {
      k8 = new_port(CON,n6);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v4), k7);
  } else {
    k7 = new_port(VAR,v4);
  }
  if (!k5) {
    node_create(net, n5, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n5), k4);
    } else {
      k4 = new_port(CON,n5);
    }
  }
  bool k13 = 0;
  Port k14 = NONE;
  Port k15 = NONE;
  // fast copy
  if (get_tag(k3) == NUM) {
    tm->itrs += 1;
    k13 = 1;
    k14 = k3;
    k15 = k3;
  }
  if (k15 != NONE) {
    link(net, tm, new_port(VAR,v3), k15);
  } else {
    k15 = new_port(VAR,v3);
  }
  bool k16 = 0;
  Pair k17 = 0;
  Port k18 = NONE;
  Port k19 = NONE;
  // fast anni
  if (get_tag(k14) == CON && node_load(net, get_val(k14)) != 0) {
    tm->itrs += 1;
    k16 = 1;
    k17 = node_take(net, get_val(k14));
    k18 = get_fst(k17);
    k19 = get_snd(k17);
  }
  bool k20 = 0;
  Pair k21 = 0;
  Port k22 = NONE;
  Port k23 = NONE;
  // fast anni
  if (get_tag(k19) == CON && node_load(net, get_val(k19)) != 0) {
    tm->itrs += 1;
    k20 = 1;
    k21 = node_take(net, get_val(k19));
    k22 = get_fst(k21);
    k23 = get_snd(k21);
  }
  bool k24 = 0;
  Pair k25 = 0;
  Port k26 = NONE;
  Port k27 = NONE;
  // fast anni
  if (get_tag(k23) == CON && node_load(net, get_val(k23)) != 0) {
    tm->itrs += 1;
    k24 = 1;
    k25 = node_take(net, get_val(k23));
    k26 = get_fst(k25);
    k27 = get_snd(k25);
  }
  if (k27 != NONE) {
    link(net, tm, new_port(VAR,v2), k27);
  } else {
    k27 = new_port(VAR,v2);
  }
  if (k26 != NONE) {
    link(net, tm, new_port(VAR,v1), k26);
  } else {
    k26 = new_port(VAR,v1);
  }
  if (!k24) {
    node_create(net, n4, new_pair(k26,k27));
    if (k23 != NONE) {
      link(net, tm, new_port(CON,n4), k23);
    } else {
      k23 = new_port(CON,n4);
    }
  }
  if (k22 != NONE) {
    link(net, tm, new_port(VAR,v0), k22);
  } else {
    k22 = new_port(VAR,v0);
  }
  if (!k20) {
    node_create(net, n3, new_pair(k22,k23));
    if (k19 != NONE) {
      link(net, tm, new_port(CON,n3), k19);
    } else {
      k19 = new_port(CON,n3);
    }
  }
  if (k18 != NONE) {
    link(net, tm, new_port(REF,0x00000044), k18);
  } else {
    k18 = new_port(REF,0x00000044);
  }
  if (!k16) {
    node_create(net, n2, new_pair(k18,k19));
    if (k14 != NONE) {
      link(net, tm, new_port(CON,n2), k14);
    } else {
      k14 = new_port(CON,n2);
    }
  }
  if (!k13) {
    node_create(net, n1, new_pair(k14,k15));
    if (k3 != NONE) {
      link(net, tm, new_port(DUP,n1), k3);
    } else {
      k3 = new_port(DUP,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n8, new_pair(new_port(VAR,v3),new_port(VAR,v1)));
  node_create(net, n7, new_pair(new_port(VAR,v4),new_port(CON,n8)));
  link(net, tm, new_port(REF,0x00000045), new_port(CON,n7));
  return true;
}

bool interact_call_update_particle__C0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val v7 = vars_alloc_1(net, tm, &vl);
  Val v8 = vars_alloc_1(net, tm, &vl);
  Val v9 = vars_alloc_1(net, tm, &vl);
  Val va = vars_alloc_1(net, tm, &vl);
  Val vb = vars_alloc_1(net, tm, &vl);
  Val vc = vars_alloc_1(net, tm, &vl);
  Val vd = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  Val nf = node_alloc_1(net, tm, &nl);
  Val n10 = node_alloc_1(net, tm, &nl);
  Val n11 = node_alloc_1(net, tm, &nl);
  Val n12 = node_alloc_1(net, tm, &nl);
  Val n13 = node_alloc_1(net, tm, &nl);
  Val n14 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !v7 || !v8 || !v9 || !va || !vb || !vc || !vd || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne || !nf || !n10 || !n11 || !n12 || !n13 || !n14) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  vars_create(net, v7, NONE);
  vars_create(net, v8, NONE);
  vars_create(net, v9, NONE);
  vars_create(net, va, NONE);
  vars_create(net, vb, NONE);
  vars_create(net, vc, NONE);
  vars_create(net, vd, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  bool k17 = 0;
  Pair k18 = 0;
  Port k19 = NONE;
  Port k20 = NONE;
  // fast anni
  if (get_tag(k16) == CON && node_load(net, get_val(k16)) != 0) {
    tm->itrs += 1;
    k17 = 1;
    k18 = node_take(net, get_val(k16));
    k19 = get_fst(k18);
    k20 = get_snd(k18);
  }
  if (k20 != NONE) {
    link(net, tm, new_port(VAR,v8), k20);
  } else {
    k20 = new_port(VAR,v8);
  }
  if (k19 != NONE) {
    link(net, tm, new_port(VAR,v7), k19);
  } else {
    k19 = new_port(VAR,v7);
  }
  if (!k17) {
    node_create(net, n7, new_pair(k19,k20));
    if (k16 != NONE) {
      link(net, tm, new_port(CON,n7), k16);
    } else {
      k16 = new_port(CON,n7);
    }
  }
  bool k21 = 0;
  Port k22 = NONE;
  Port k23 = NONE;
  // fast copy
  if (get_tag(k15) == NUM) {
    tm->itrs += 1;
    k21 = 1;
    k22 = k15;
    k23 = k15;
  }
  if (k23 != NONE) {
    link(net, tm, new_port(VAR,v6), k23);
  } else {
    k23 = new_port(VAR,v6);
  }
  if (k22 != NONE) {
    link(net, tm, new_port(VAR,v5), k22);
  } else {
    k22 = new_port(VAR,v5);
  }
  if (!k21) {
    node_create(net, n6, new_pair(k22,k23));
    if (k15 != NONE) {
      link(net, tm, new_port(DUP,n6), k15);
    } else {
      k15 = new_port(DUP,n6);
    }
  }
  if (!k13) {
    node_create(net, n5, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n5), k12);
    } else {
      k12 = new_port(CON,n5);
    }
  }
  bool k24 = 0;
  Port k25 = NONE;
  Port k26 = NONE;
  // fast copy
  if (get_tag(k11) == NUM) {
    tm->itrs += 1;
    k24 = 1;
    k25 = k11;
    k26 = k11;
  }
  if (k26 != NONE) {
    link(net, tm, new_port(VAR,v4), k26);
  } else {
    k26 = new_port(VAR,v4);
  }
  if (k25 != NONE) {
    link(net, tm, new_port(VAR,v3), k25);
  } else {
    k25 = new_port(VAR,v3);
  }
  if (!k24) {
    node_create(net, n4, new_pair(k25,k26));
    if (k11 != NONE) {
      link(net, tm, new_port(DUP,n4), k11);
    } else {
      k11 = new_port(DUP,n4);
    }
  }
  if (!k9) {
    node_create(net, n3, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n3), k8);
    } else {
      k8 = new_port(CON,n3);
    }
  }
  bool k27 = 0;
  Port k28 = NONE;
  Port k29 = NONE;
  // fast copy
  if (get_tag(k7) == NUM) {
    tm->itrs += 1;
    k27 = 1;
    k28 = k7;
    k29 = k7;
  }
  if (k29 != NONE) {
    link(net, tm, new_port(VAR,v2), k29);
  } else {
    k29 = new_port(VAR,v2);
  }
  if (k28 != NONE) {
    link(net, tm, new_port(VAR,v1), k28);
  } else {
    k28 = new_port(VAR,v1);
  }
  if (!k27) {
    node_create(net, n2, new_pair(k28,k29));
    if (k7 != NONE) {
      link(net, tm, new_port(DUP,n2), k7);
    } else {
      k7 = new_port(DUP,n2);
    }
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(VAR,v0), k3);
  } else {
    k3 = new_port(VAR,v0);
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, na, new_pair(new_port(VAR,v3),new_port(VAR,v8)));
  node_create(net, n9, new_pair(new_port(VAR,va),new_port(CON,na)));
  node_create(net, n8, new_pair(new_port(VAR,v9),new_port(CON,n9)));
  link(net, tm, new_port(REF,0x00000016), new_port(CON,n8));
  node_create(net, nc, new_pair(new_port(VAR,vb),new_port(VAR,v9)));
  node_create(net, nb, new_pair(new_port(VAR,v0),new_port(CON,nc)));
  link(net, tm, new_port(REF,0x0000001a), new_port(CON,nb));
  node_create(net, ne, new_pair(new_port(VAR,v5),new_port(VAR,vb)));
  node_create(net, nd, new_pair(new_port(VAR,v1),new_port(CON,ne)));
  link(net, tm, new_port(REF,0x00000032), new_port(CON,nd));
  node_create(net, n10, new_pair(new_port(VAR,vc),new_port(VAR,va)));
  node_create(net, nf, new_pair(new_port(VAR,v2),new_port(CON,n10)));
  link(net, tm, new_port(REF,0x0000001a), new_port(CON,nf));
  node_create(net, n12, new_pair(new_port(VAR,v6),new_port(VAR,vc)));
  node_create(net, n11, new_pair(new_port(VAR,vd),new_port(CON,n12)));
  link(net, tm, new_port(REF,0x00000032), new_port(CON,n11));
  node_create(net, n14, new_pair(new_port(VAR,v4),new_port(VAR,vd)));
  node_create(net, n13, new_pair(new_port(VAR,v7),new_port(CON,n14)));
  link(net, tm, new_port(REF,0x0000002a), new_port(CON,n13));
  return true;
}

bool interact_call_update_particle__C1(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  if (k3 != NONE) {
    link(net, tm, new_port(REF,0x00000043), k3);
  } else {
    k3 = new_port(REF,0x00000043);
  }
  // fast void
  if (get_tag(k4) == ERA || get_tag(k4) == NUM) {
    tm->itrs += 1;
  } else {
    if (k4 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k4);
    } else {
      k4 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_update_particle__fold0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  if (k4 != NONE) {
    link(net, tm, new_port(VAR,v0), k4);
  } else {
    k4 = new_port(VAR,v0);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k3));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  if (k8 != NONE) {
    link(net, tm, new_port(VAR,v0), k8);
  } else {
    k8 = new_port(VAR,v0);
  }
  if (k7 != NONE) {
    link(net, tm, new_port(REF,0x00000047), k7);
  } else {
    k7 = new_port(REF,0x00000047);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n1), k3);
    } else {
      k3 = new_port(CON,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  return true;
}

bool interact_call_update_particle__fold0__C0(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  bool k13 = 0;
  Pair k14 = 0;
  Port k15 = NONE;
  Port k16 = NONE;
  // fast anni
  if (get_tag(k12) == CON && node_load(net, get_val(k12)) != 0) {
    tm->itrs += 1;
    k13 = 1;
    k14 = node_take(net, get_val(k12));
    k15 = get_fst(k14);
    k16 = get_snd(k14);
  }
  if (k16 != NONE) {
    link(net, tm, new_port(VAR,v4), k16);
  } else {
    k16 = new_port(VAR,v4);
  }
  bool k17 = 0;
  Port k18 = NONE;
  Port k19 = NONE;
  // fast copy
  if (get_tag(k15) == NUM) {
    tm->itrs += 1;
    k17 = 1;
    k18 = k15;
    k19 = k15;
  }
  if (k19 != NONE) {
    link(net, tm, new_port(VAR,v3), k19);
  } else {
    k19 = new_port(VAR,v3);
  }
  if (k18 != NONE) {
    link(net, tm, new_port(VAR,v2), k18);
  } else {
    k18 = new_port(VAR,v2);
  }
  if (!k17) {
    node_create(net, n4, new_pair(k18,k19));
    if (k15 != NONE) {
      link(net, tm, new_port(DUP,n4), k15);
    } else {
      k15 = new_port(DUP,n4);
    }
  }
  if (!k13) {
    node_create(net, n3, new_pair(k15,k16));
    if (k12 != NONE) {
      link(net, tm, new_port(CON,n3), k12);
    } else {
      k12 = new_port(CON,n3);
    }
  }
  if (k11 != NONE) {
    link(net, tm, new_port(VAR,v1), k11);
  } else {
    k11 = new_port(VAR,v1);
  }
  if (!k9) {
    node_create(net, n2, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n2), k8);
    } else {
      k8 = new_port(CON,n2);
    }
  }
  if (k7 != NONE) {
    link(net, tm, new_port(VAR,v0), k7);
  } else {
    k7 = new_port(VAR,v0);
  }
  if (!k5) {
    node_create(net, n1, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n1), k4);
    } else {
      k4 = new_port(CON,n1);
    }
  }
  // fast void
  if (get_tag(k3) == ERA || get_tag(k3) == NUM) {
    tm->itrs += 1;
  } else {
    if (k3 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k3);
    } else {
      k3 = new_port(ERA,0x00000000);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n6, new_pair(new_port(VAR,v6),new_port(VAR,v4)));
  node_create(net, n5, new_pair(new_port(VAR,v5),new_port(CON,n6)));
  link(net, tm, new_port(REF,0x0000001a), new_port(CON,n5));
  node_create(net, n8, new_pair(new_port(VAR,v0),new_port(VAR,v5)));
  node_create(net, n7, new_pair(new_port(VAR,v2),new_port(CON,n8)));
  link(net, tm, new_port(REF,0x0000001f), new_port(CON,n7));
  node_create(net, na, new_pair(new_port(VAR,v3),new_port(VAR,v6)));
  node_create(net, n9, new_pair(new_port(VAR,v1),new_port(CON,na)));
  link(net, tm, new_port(REF,0x00000045), new_port(CON,n9));
  return true;
}

bool interact_call_update_particle__fold0__C1(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !n0 || !n1 || !n2 || !n3) {
    return false;
  }
  vars_create(net, v0, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k5 = NONE;
  Port k3 = NONE;
  Port k4 = NONE;
  //fast switch
  if (get_tag(b) == CON) {
    k2 = node_load(net, get_val(b));
    k5 = enter(net,get_fst(k2));
    if (get_tag(k5) == NUM) {
      tm->itrs += 3;
      vars_take(net, v0);
      k1 = 1;
      if (get_u24(get_val(k5)) == 0) {
        node_take(net, get_val(b));
        k3 = get_snd(k2);
        k4 = new_port(ERA,0);
      } else {
        node_store(net, get_val(b), new_pair(new_port(NUM,new_u24(get_u24(get_val(k5))-1)), get_snd(k2)));
        k3 = new_port(ERA,0);
        k4 = b;
      }
    } else {
      node_store(net, get_val(b), new_pair(k5,get_snd(k2)));
    }
  }
  bool k6 = 0;
  Pair k7 = 0;
  Port k8 = NONE;
  Port k9 = NONE;
  // fast anni
  if (get_tag(k3) == CON && node_load(net, get_val(k3)) != 0) {
    tm->itrs += 1;
    k6 = 1;
    k7 = node_take(net, get_val(k3));
    k8 = get_fst(k7);
    k9 = get_snd(k7);
  }
  if (k9 != NONE) {
    link(net, tm, new_port(REF,0x0000002e), k9);
  } else {
    k9 = new_port(REF,0x0000002e);
  }
  // fast void
  if (get_tag(k8) == ERA || get_tag(k8) == NUM) {
    tm->itrs += 1;
  } else {
    if (k8 != NONE) {
      link(net, tm, new_port(ERA,0x00000000), k8);
    } else {
      k8 = new_port(ERA,0x00000000);
    }
  }
  if (!k6) {
    node_create(net, n3, new_pair(k8,k9));
    if (k3 != NONE) {
      link(net, tm, new_port(CON,n3), k3);
    } else {
      k3 = new_port(CON,n3);
    }
  }
  if (k4 != NONE) {
    link(net, tm, new_port(REF,0x00000046), k4);
  } else {
    k4 = new_port(REF,0x00000046);
  }
  if (!k1) {
    node_create(net, n0, new_pair(new_port(SWI,n1),new_port(VAR,v0)));
    node_create(net, n1, new_pair(new_port(CON,n2),new_port(VAR,v0)));
    node_create(net, n2, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON, n0), b);
    } else {
      b = new_port(CON, n0);
    }
  }
  return true;
}

bool interact_call_vector(Net *net, TM *tm, Port a, Port b) {
  u32 vl = 0;
  u32 nl = 0;
  Val v0 = vars_alloc_1(net, tm, &vl);
  Val v1 = vars_alloc_1(net, tm, &vl);
  Val v2 = vars_alloc_1(net, tm, &vl);
  Val v3 = vars_alloc_1(net, tm, &vl);
  Val v4 = vars_alloc_1(net, tm, &vl);
  Val v5 = vars_alloc_1(net, tm, &vl);
  Val v6 = vars_alloc_1(net, tm, &vl);
  Val v7 = vars_alloc_1(net, tm, &vl);
  Val v8 = vars_alloc_1(net, tm, &vl);
  Val n0 = node_alloc_1(net, tm, &nl);
  Val n1 = node_alloc_1(net, tm, &nl);
  Val n2 = node_alloc_1(net, tm, &nl);
  Val n3 = node_alloc_1(net, tm, &nl);
  Val n4 = node_alloc_1(net, tm, &nl);
  Val n5 = node_alloc_1(net, tm, &nl);
  Val n6 = node_alloc_1(net, tm, &nl);
  Val n7 = node_alloc_1(net, tm, &nl);
  Val n8 = node_alloc_1(net, tm, &nl);
  Val n9 = node_alloc_1(net, tm, &nl);
  Val na = node_alloc_1(net, tm, &nl);
  Val nb = node_alloc_1(net, tm, &nl);
  Val nc = node_alloc_1(net, tm, &nl);
  Val nd = node_alloc_1(net, tm, &nl);
  Val ne = node_alloc_1(net, tm, &nl);
  if (0 || !v0 || !v1 || !v2 || !v3 || !v4 || !v5 || !v6 || !v7 || !v8 || !n0 || !n1 || !n2 || !n3 || !n4 || !n5 || !n6 || !n7 || !n8 || !n9 || !na || !nb || !nc || !nd || !ne) {
    return false;
  }
  vars_create(net, v0, NONE);
  vars_create(net, v1, NONE);
  vars_create(net, v2, NONE);
  vars_create(net, v3, NONE);
  vars_create(net, v4, NONE);
  vars_create(net, v5, NONE);
  vars_create(net, v6, NONE);
  vars_create(net, v7, NONE);
  vars_create(net, v8, NONE);
  bool k1 = 0;
  Pair k2 = 0;
  Port k3 = NONE;
  Port k4 = NONE;
  // fast anni
  if (get_tag(b) == CON && node_load(net, get_val(b)) != 0) {
    tm->itrs += 1;
    k1 = 1;
    k2 = node_take(net, get_val(b));
    k3 = get_fst(k2);
    k4 = get_snd(k2);
  }
  bool k5 = 0;
  Pair k6 = 0;
  Port k7 = NONE;
  Port k8 = NONE;
  // fast anni
  if (get_tag(k4) == CON && node_load(net, get_val(k4)) != 0) {
    tm->itrs += 1;
    k5 = 1;
    k6 = node_take(net, get_val(k4));
    k7 = get_fst(k6);
    k8 = get_snd(k6);
  }
  bool k9 = 0;
  Pair k10 = 0;
  Port k11 = NONE;
  Port k12 = NONE;
  // fast anni
  if (get_tag(k8) == CON && node_load(net, get_val(k8)) != 0) {
    tm->itrs += 1;
    k9 = 1;
    k10 = node_take(net, get_val(k8));
    k11 = get_fst(k10);
    k12 = get_snd(k10);
  }
  if (k12 != NONE) {
    link(net, tm, new_port(VAR,v6), k12);
  } else {
    k12 = new_port(VAR,v6);
  }
  bool k13 = 0;
  Port k14 = NONE;
  Port k15 = NONE;
  // fast copy
  if (get_tag(k11) == NUM) {
    tm->itrs += 1;
    k13 = 1;
    k14 = k11;
    k15 = k11;
  }
  if (k15 != NONE) {
    link(net, tm, new_port(VAR,v5), k15);
  } else {
    k15 = new_port(VAR,v5);
  }
  if (k14 != NONE) {
    link(net, tm, new_port(VAR,v4), k14);
  } else {
    k14 = new_port(VAR,v4);
  }
  if (!k13) {
    node_create(net, n5, new_pair(k14,k15));
    if (k11 != NONE) {
      link(net, tm, new_port(DUP,n5), k11);
    } else {
      k11 = new_port(DUP,n5);
    }
  }
  if (!k9) {
    node_create(net, n4, new_pair(k11,k12));
    if (k8 != NONE) {
      link(net, tm, new_port(CON,n4), k8);
    } else {
      k8 = new_port(CON,n4);
    }
  }
  bool k16 = 0;
  Port k17 = NONE;
  Port k18 = NONE;
  // fast copy
  if (get_tag(k7) == NUM) {
    tm->itrs += 1;
    k16 = 1;
    k17 = k7;
    k18 = k7;
  }
  if (k18 != NONE) {
    link(net, tm, new_port(VAR,v3), k18);
  } else {
    k18 = new_port(VAR,v3);
  }
  if (k17 != NONE) {
    link(net, tm, new_port(VAR,v2), k17);
  } else {
    k17 = new_port(VAR,v2);
  }
  if (!k16) {
    node_create(net, n3, new_pair(k17,k18));
    if (k7 != NONE) {
      link(net, tm, new_port(DUP,n3), k7);
    } else {
      k7 = new_port(DUP,n3);
    }
  }
  if (!k5) {
    node_create(net, n2, new_pair(k7,k8));
    if (k4 != NONE) {
      link(net, tm, new_port(CON,n2), k4);
    } else {
      k4 = new_port(CON,n2);
    }
  }
  bool k19 = 0;
  Port k20 = NONE;
  Port k21 = NONE;
  // fast copy
  if (get_tag(k3) == NUM) {
    tm->itrs += 1;
    k19 = 1;
    k20 = k3;
    k21 = k3;
  }
  if (k21 != NONE) {
    link(net, tm, new_port(VAR,v1), k21);
  } else {
    k21 = new_port(VAR,v1);
  }
  if (k20 != NONE) {
    link(net, tm, new_port(VAR,v0), k20);
  } else {
    k20 = new_port(VAR,v0);
  }
  if (!k19) {
    node_create(net, n1, new_pair(k20,k21));
    if (k3 != NONE) {
      link(net, tm, new_port(DUP,n1), k3);
    } else {
      k3 = new_port(DUP,n1);
    }
  }
  if (!k1) {
    node_create(net, n0, new_pair(k3,k4));
    if (b != NONE) {
      link(net, tm, new_port(CON,n0), b);
    } else {
      b = new_port(CON,n0);
    }
  }
  node_create(net, n8, new_pair(new_port(VAR,v5),new_port(VAR,v6)));
  node_create(net, n7, new_pair(new_port(VAR,v4),new_port(CON,n8)));
  node_create(net, n6, new_pair(new_port(VAR,v7),new_port(CON,n7)));
  link(net, tm, new_port(REF,0x0000000a), new_port(CON,n6));
  node_create(net, nb, new_pair(new_port(VAR,v3),new_port(VAR,v7)));
  node_create(net, na, new_pair(new_port(VAR,v2),new_port(CON,nb)));
  node_create(net, n9, new_pair(new_port(VAR,v8),new_port(CON,na)));
  link(net, tm, new_port(REF,0x0000000a), new_port(CON,n9));
  node_create(net, ne, new_pair(new_port(VAR,v1),new_port(VAR,v8)));
  node_create(net, nd, new_pair(new_port(VAR,v0),new_port(CON,ne)));
  node_create(net, nc, new_pair(new_port(REF,0x00000009),new_port(CON,nd)));
  link(net, tm, new_port(REF,0x0000000a), new_port(CON,nc));
  return true;
}

bool interact_call(Net *net, TM *tm, Port a, Port b) {
  u32 fid = get_val(a) & 0xFFFFFFF;
  switch (fid) {
    case 0: return interact_call_main(net, tm, a, b);
    case 1: return interact_call_List_Cons(net, tm, a, b);
    case 2: return interact_call_List_Cons_tag(net, tm, a, b);
    case 3: return interact_call_List_Nil(net, tm, a, b);
    case 4: return interact_call_List_Nil_tag(net, tm, a, b);
    case 5: return interact_call_Map_Leaf(net, tm, a, b);
    case 6: return interact_call_Map_Leaf_tag(net, tm, a, b);
    case 7: return interact_call_Map_Node(net, tm, a, b);
    case 8: return interact_call_Map_Node_tag(net, tm, a, b);
    case 9: return interact_call_Map_empty(net, tm, a, b);
    case 10: return interact_call_Map_set(net, tm, a, b);
    case 11: return interact_call_Map_set__C0(net, tm, a, b);
    case 12: return interact_call_Map_set__C1(net, tm, a, b);
    case 13: return interact_call_Map_set__C10(net, tm, a, b);
    case 14: return interact_call_Map_set__C2(net, tm, a, b);
    case 15: return interact_call_Map_set__C3(net, tm, a, b);
    case 16: return interact_call_Map_set__C4(net, tm, a, b);
    case 17: return interact_call_Map_set__C5(net, tm, a, b);
    case 18: return interact_call_Map_set__C6(net, tm, a, b);
    case 19: return interact_call_Map_set__C7(net, tm, a, b);
    case 20: return interact_call_Map_set__C8(net, tm, a, b);
    case 21: return interact_call_Map_set__C9(net, tm, a, b);
    case 22: return interact_call_Particle(net, tm, a, b);
    case 23: return interact_call_Particle_tag(net, tm, a, b);
    case 24: return interact_call_Vector3D(net, tm, a, b);
    case 25: return interact_call_Vector3D_tag(net, tm, a, b);
    case 26: return interact_call_add(net, tm, a, b);
    case 27: return interact_call_add__C0(net, tm, a, b);
    case 28: return interact_call_add__C1(net, tm, a, b);
    case 29: return interact_call_add__C2(net, tm, a, b);
    case 30: return interact_call_add__C3(net, tm, a, b);
    case 31: return interact_call_calculate_force(net, tm, a, b);
    case 32: return interact_call_calculate_force__C0(net, tm, a, b);
    case 33: return interact_call_calculate_force__C1(net, tm, a, b);
    case 34: return interact_call_calculate_force__C2(net, tm, a, b);
    case 35: return interact_call_calculate_force__C3(net, tm, a, b);
    case 36: return interact_call_calculate_force__C4(net, tm, a, b);
    case 37: return interact_call_distance(net, tm, a, b);
    case 38: return interact_call_distance__C0(net, tm, a, b);
    case 39: return interact_call_distance__C1(net, tm, a, b);
    case 40: return interact_call_distance__C2(net, tm, a, b);
    case 41: return interact_call_distance__C3(net, tm, a, b);
    case 42: return interact_call_divide(net, tm, a, b);
    case 43: return interact_call_divide__C0(net, tm, a, b);
    case 44: return interact_call_divide__C1(net, tm, a, b);
    case 45: return interact_call_getG(net, tm, a, b);
    case 46: return interact_call_get_origin(net, tm, a, b);
    case 47: return interact_call_get_particles(net, tm, a, b);
    case 48: return interact_call_get_particles__C0(net, tm, a, b);
    case 49: return interact_call_get_particles__C1(net, tm, a, b);
    case 50: return interact_call_multiply(net, tm, a, b);
    case 51: return interact_call_multiply__C0(net, tm, a, b);
    case 52: return interact_call_multiply__C1(net, tm, a, b);
    case 53: return interact_call_normalize(net, tm, a, b);
    case 54: return interact_call_simulate(net, tm, a, b);
    case 55: return interact_call_simulate__C0(net, tm, a, b);
    case 56: return interact_call_subtract(net, tm, a, b);
    case 57: return interact_call_subtract__C0(net, tm, a, b);
    case 58: return interact_call_subtract__C1(net, tm, a, b);
    case 59: return interact_call_subtract__C2(net, tm, a, b);
    case 60: return interact_call_subtract__C3(net, tm, a, b);
    case 61: return interact_call_unreachable(net, tm, a, b);
    case 62: return interact_call_update_all_particles(net, tm, a, b);
    case 63: return interact_call_update_all_particles__fold0(net, tm, a, b);
    case 64: return interact_call_update_all_particles__fold0__C0(net, tm, a, b);
    case 65: return interact_call_update_all_particles__fold0__C1(net, tm, a, b);
    case 66: return interact_call_update_particle(net, tm, a, b);
    case 67: return interact_call_update_particle__C0(net, tm, a, b);
    case 68: return interact_call_update_particle__C1(net, tm, a, b);
    case 69: return interact_call_update_particle__fold0(net, tm, a, b);
    case 70: return interact_call_update_particle__fold0__C0(net, tm, a, b);
    case 71: return interact_call_update_particle__fold0__C1(net, tm, a, b);
    case 72: return interact_call_vector(net, tm, a, b);
    default: return false;
  }
}
#else
static inline bool interact_call(Net* net, TM* tm, Port a, Port b, Book* book) {
  // Loads Definition.
  u32  fid = get_val(a) & 0xFFFFFFF;
  Def* def = &book->defs_buf[fid];

  // Copy Optimization.
  if (def->safe && get_tag(b) == DUP) {
    return interact_eras(net, tm, a, b);
  }

  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, def->rbag_len + 1, def->node_len, def->vars_len)) {
    debug("interact_call: get_resources failed\n");
    return false;
  }

  // Stores new vars.
  for (u32 i = 0; i < def->vars_len; ++i) {
    vars_create(net, tm->vloc[i], NONE);
  }

  // Stores new nodes.
  for (u32 i = 0; i < def->node_len; ++i) {
    node_create(net, tm->nloc[i], adjust_pair(net, tm, def->node_buf[i]));
  }

  // Links.
  for (u32 i = 0; i < def->rbag_len; ++i) {
    link_pair(net, tm, adjust_pair(net, tm, def->rbag_buf[i]));
  }
  link_pair(net, tm, new_pair(adjust_port(net, tm, def->root), b));

  return true;
}
#endif

// The Void Interaction.
static inline bool interact_void(Net* net, TM* tm, Port a, Port b) {
  return true;
}

// The Eras Interaction.
static inline bool interact_eras(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 2, 0, 0)) {
    debug("interact_eras: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports.
  Pair B  = node_exchange(net, get_val(b), 0);
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Links.
  link_pair(net, tm, new_pair(a, B1));
  link_pair(net, tm, new_pair(a, B2));

  return true;
}

// The Anni Interaction.
static inline bool interact_anni(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 2, 0, 0)) {
    debug("interact_anni: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports.
  Pair A  = node_take(net, get_val(a));
  Port A1 = get_fst(A);
  Port A2 = get_snd(A);
  Pair B  = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Links.
  link_pair(net, tm, new_pair(A1, B1));
  link_pair(net, tm, new_pair(A2, B2));

  return true;
}

// The Comm Interaction.
static inline bool interact_comm(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 4, 4, 4)) {
    debug("interact_comm: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(a)) == 0 || node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports.
  Pair A  = node_take(net, get_val(a));
  Port A1 = get_fst(A);
  Port A2 = get_snd(A);
  Pair B  = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Stores new vars.
  vars_create(net, tm->vloc[0], NONE);
  vars_create(net, tm->vloc[1], NONE);
  vars_create(net, tm->vloc[2], NONE);
  vars_create(net, tm->vloc[3], NONE);

  // Stores new nodes.
  node_create(net, tm->nloc[0], new_pair(new_port(VAR, tm->vloc[0]), new_port(VAR, tm->vloc[1])));
  node_create(net, tm->nloc[1], new_pair(new_port(VAR, tm->vloc[2]), new_port(VAR, tm->vloc[3])));
  node_create(net, tm->nloc[2], new_pair(new_port(VAR, tm->vloc[0]), new_port(VAR, tm->vloc[2])));
  node_create(net, tm->nloc[3], new_pair(new_port(VAR, tm->vloc[1]), new_port(VAR, tm->vloc[3])));

  // Links.
  link_pair(net, tm, new_pair(new_port(get_tag(b), tm->nloc[0]), A1));
  link_pair(net, tm, new_pair(new_port(get_tag(b), tm->nloc[1]), A2));
  link_pair(net, tm, new_pair(new_port(get_tag(a), tm->nloc[2]), B1));
  link_pair(net, tm, new_pair(new_port(get_tag(a), tm->nloc[3]), B2));

  return true;
}

// The Oper Interaction.
static inline bool interact_oper(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 1, 1, 0)) {
    debug("interact_oper: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports.
  Val  av = get_val(a);
  Pair B  = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = enter(net, get_snd(B));

  // Performs operation.
  if (get_tag(B1) == NUM) {
    Val  bv = get_val(B1);
    Numb cv = operate(av, bv);
    link_pair(net, tm, new_pair(new_port(NUM, cv), B2));
  } else {
    node_create(net, tm->nloc[0], new_pair(a, B2));
    link_pair(net, tm, new_pair(B1, new_port(OPR, tm->nloc[0])));
  }

  return true;
}

// The Swit Interaction.
static inline bool interact_swit(Net* net, TM* tm, Port a, Port b) {
  // Allocates needed nodes and vars.
  if (!get_resources(net, tm, 1, 2, 0)) {
    debug("interact_swit: get_resources failed\n");
    return false;
  }

  // Checks availability
  if (node_load(net, get_val(b)) == 0) {
    return false;
  }

  // Loads ports.
  u32  av = get_u24(get_val(a));
  Pair B  = node_take(net, get_val(b));
  Port B1 = get_fst(B);
  Port B2 = get_snd(B);

  // Stores new nodes.
  if (av == 0) {
    node_create(net, tm->nloc[0], new_pair(B2, new_port(ERA,0)));
    link_pair(net, tm, new_pair(new_port(CON, tm->nloc[0]), B1));
  } else {
    node_create(net, tm->nloc[0], new_pair(new_port(ERA,0), new_port(CON, tm->nloc[1])));
    node_create(net, tm->nloc[1], new_pair(new_port(NUM, new_u24(av-1)), B2));
    link_pair(net, tm, new_pair(new_port(CON, tm->nloc[0]), B1));
  }

  return true;
}

// Pops a local redex and performs a single interaction.
static inline bool interact(Net* net, TM* tm, Book* book) {
  // Pops a redex.
  Pair redex = pop_redex(net, tm);

  // If there is no redex, stop.
  if (redex != 0) {
    // Gets redex ports A and B.
    Port a = get_fst(redex);
    Port b = get_snd(redex);

    // Gets the rule type.
    Rule rule = get_rule(a, b);

    // Used for root redex.
    if (get_tag(a) == REF && b == ROOT) {
      rule = CALL;
    // Swaps ports if necessary.
    } else if (should_swap(a,b)) {
      swap(&a, &b);
    }

    // Dispatches interaction rule.
    bool success;
    switch (rule) {
      case LINK: success = interact_link(net, tm, a, b); break;
      #ifdef COMPILED
      case CALL: success = interact_call(net, tm, a, b); break;
      #else
      case CALL: success = interact_call(net, tm, a, b, book); break;
      #endif
      case VOID: success = interact_void(net, tm, a, b); break;
      case ERAS: success = interact_eras(net, tm, a, b); break;
      case ANNI: success = interact_anni(net, tm, a, b); break;
      case COMM: success = interact_comm(net, tm, a, b); break;
      case OPER: success = interact_oper(net, tm, a, b); break;
      case SWIT: success = interact_swit(net, tm, a, b); break;
    }

    // If error, pushes redex back.
    if (!success) {
      push_redex(net, tm, redex);
      return false;
    // Else, increments the interaction count.
    } else if (rule != LINK) {
      tm->itrs += 1;
    }
  }

  return true;
}

// Evaluator
// ---------

void evaluator(Net* net, TM* tm, Book* book) {
  // Initializes the global idle counter
  atomic_store_explicit(&net->idle, TPC - 1, memory_order_relaxed);
  sync_threads();

  // Performs some interactions
  u32  tick = 0;
  bool busy = tm->tid == 0;
  while (true) {
    tick += 1;

    // If we have redexes...
    if (rbag_len(net, tm) > 0) {
      // Update global idle counter
      if (!busy) atomic_fetch_sub_explicit(&net->idle, 1, memory_order_relaxed);
      busy = true;

      // Perform an interaction
      #ifdef DEBUG
      if (!interact(net, tm, book)) debug("interaction failed\n");
      #else
      interact(net, tm, book);
      #endif
    // If we have no redexes...
    } else {
      // Update global idle counter
      if (busy) atomic_fetch_add_explicit(&net->idle, 1, memory_order_relaxed);
      busy = false;

      //// Peeks a redex from target
      u32 sid = (tm->tid - 1) % TPC;
      u32 idx = sid*(G_RBAG_LEN/TPC) + (tm->sidx++);

      // Stealing Everything: this will steal all redexes

      Pair got = atomic_exchange_explicit(&net->rbag_buf[idx], 0, memory_order_relaxed);
      if (got != 0) {
        push_redex(net, tm, got);
        continue;
      } else {
        tm->sidx = 0;
      }

      // Chill...
      sched_yield();
      // Halt if all threads are idle
      if (tick % 256 == 0) {
        if (atomic_load_explicit(&net->idle, memory_order_relaxed) == TPC) {
          break;
        }
      }
    }
  }

  sync_threads();

  atomic_fetch_add(&net->itrs, tm->itrs);
  tm->itrs = 0;
}

// Normalizer
// ----------

// Thread data
typedef struct {
  Net*  net;
  TM*   tm;
  Book* book;
} ThreadArg;

void* thread_func(void* arg) {
  ThreadArg* data = (ThreadArg*)arg;
  evaluator(data->net, data->tm, data->book);
  return NULL;
}

// Sets the initial redex.
void boot_redex(Net* net, Pair redex) {
  net->vars_buf[get_val(ROOT)] = NONE;
  net->rbag_buf[0] = redex;
}

// Evaluates all redexes.
// TODO: cache threads to avoid spawning overhead
void normalize(Net* net, Book* book) {
  // Inits thread_arg objects
  ThreadArg thread_arg[TPC];
  for (u32 t = 0; t < TPC; ++t) {
    thread_arg[t].net  = net;
    thread_arg[t].tm   = tm[t];
    thread_arg[t].book = book;
  }

  // Spawns the evaluation threads
  pthread_t threads[TPC];
  for (u32 t = 0; t < TPC; ++t) {
    pthread_create(&threads[t], NULL, thread_func, &thread_arg[t]);
  }

  // Wait for the threads to finish
  for (u32 t = 0; t < TPC; ++t) {
    pthread_join(threads[t], NULL);
  }
}

// Util: expands a REF Port.
Port expand(Net* net, Book* book, Port port) {
  Port old = vars_load(net, get_val(ROOT));
  Port got = peek(net, port);
  while (get_tag(got) == REF) {
    boot_redex(net, new_pair(got, ROOT));
    normalize(net, book);
    got = peek(net, vars_load(net, get_val(ROOT)));
  }
  vars_create(net, get_val(ROOT), old);
  return got;
}

// Reads back an image.
// Encoding: (<tree>,<tree>) | #RRGGBB
void read_img(Net* net, Port port, u32 width, u32 height, u32* buffer) {
  //pretty_print_port(net, port);
  //printf("\n");
  typedef struct {
    Port port; u32 lv;
    u32 x0; u32 x1;
    u32 y0; u32 y1;
  } Rect;
  Rect stk[24];
  u32 pos = 0;
  stk[pos++] = (Rect){port, 0, 0, width, 0, height};
  while (pos > 0) {
    Rect rect = stk[--pos];
    Port port = enter(net, rect.port);
    u32  lv   = rect.lv;
    u32  x0   = rect.x0;
    u32  x1   = rect.x1;
    u32  y0   = rect.y0;
    u32  y1   = rect.y1;
    if (get_tag(port) == CON) {
      Pair nd = node_load(net, get_val(port));
      Port p1 = get_fst(nd);
      Port p2 = get_snd(nd);
      u32  xm = (x0 + x1) / 2;
      u32  ym = (y0 + y1) / 2;
      if (lv % 2 == 0) {
        stk[pos++] = (Rect){p2, lv+1, xm, x1, y0, y1};
        stk[pos++] = (Rect){p1, lv+1, x0, xm, y0, y1};
      } else {
        stk[pos++] = (Rect){p2, lv+1, x0, x1, ym, y1};
        stk[pos++] = (Rect){p1, lv+1, x0, x1, y0, ym};
      }
      continue;
    }
    if (get_tag(port) == NUM) {
      u32 color = get_u24(get_val(port));
      printf("COL=%08x x0=%04u x1=%04u y0=%04u y1=%04u | %s\n", color, x0, x1, y0, y1, show_port(port).x);
      for (u32 y = y0; y < y1; y++) {
        for (u32 x = x0; x < x1; x++) {
          buffer[y*width + x] = 0xFF000000 | color;
        }
      }
      continue;
    }
    break;
  }
}


//#ifdef IO_DRAWIMAGE
//// Global variables for the window and renderer
//static SDL_Window *window = NULL;
//static SDL_Renderer *renderer = NULL;
//static SDL_Texture *texture = NULL;
//// Function to close the SDL window and clean up resources
//void close_sdl(void) {
  //if (texture != NULL) {
    //SDL_DestroyTexture(texture);
    //texture = NULL;
  //}
  //if (renderer != NULL) {
    //SDL_DestroyRenderer(renderer);
    //renderer = NULL;
  //}
  //if (window != NULL) {
    //SDL_DestroyWindow(window);
    //window = NULL;
  //}
  //SDL_Quit();
//}
//// Function to render an image to the SDL window
//void render(uint32_t width, uint32_t height, uint32_t *buffer) {
  //// Initialize SDL if it hasn't been initialized
  //if (SDL_WasInit(SDL_INIT_VIDEO) == 0) {
    //if (SDL_Init(SDL_INIT_VIDEO) < 0) {
      //fprintf(stderr, "SDL could not initialize! SDL Error: %s\n", SDL_GetError());
      //return;
    //}
  //}
  //// Create window and renderer if they don't exist
  //if (window == NULL) {
    //window = SDL_CreateWindow("SDL Window", SDL_WINDOWPOS_UNDEFINED, SDL_WINDOWPOS_UNDEFINED, width, height, SDL_WINDOW_SHOWN);
    //if (window == NULL) {
      //fprintf(stderr, "Window could not be created! SDL Error: %s\n", SDL_GetError());
      //return;
    //}
    //renderer = SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC);
    //if (renderer == NULL) {
      //SDL_DestroyWindow(window);
      //window = NULL;
      //fprintf(stderr, "Renderer could not be created! SDL Error: %s\n", SDL_GetError());
      //return;
    //}
  //}
  //// Create or recreate the texture if necessary
  //if (texture == NULL) {
    //texture = SDL_CreateTexture(renderer, SDL_PIXELFORMAT_ARGB8888, SDL_TEXTUREACCESS_STREAMING, width, height);
    //if (texture == NULL) {
      //fprintf(stderr, "Texture could not be created! SDL Error: %s\n", SDL_GetError());
      //return;
    //}
  //}
  //// Update the texture with the new buffer
  //if (SDL_UpdateTexture(texture, NULL, buffer, width * sizeof(uint32_t)) < 0) {
    //fprintf(stderr, "Texture could not be updated! SDL Error: %s\n", SDL_GetError());
    //return;
  //}
  //// Clear the renderer
  //SDL_RenderClear(renderer);
  //// Copy the texture to the renderer
  //SDL_RenderCopy(renderer, texture, NULL, NULL);
  //// Update the screen
  //SDL_RenderPresent(renderer);
  //// Process events to prevent the OS from thinking the application is unresponsive
  //SDL_Event e;
  //while (SDL_PollEvent(&e)) {
    //if (e.type == SDL_QUIT) {
      //close_sdl();
      //exit(0);
    //}
  //}
//}
//// IO: DrawImage
//Port io_put_image(Net* net, Book* book, u32 argc, Port* argv) {
  //u32 width = 256;
  //u32 height = 256;
  //// Create a buffer
  //uint32_t *buffer = (uint32_t *)malloc(width * height * sizeof(uint32_t));
  //if (buffer == NULL) {
    //fprintf(stderr, "Failed to allocate memory for buffer\n");
    //return 1;
  //}
  //// Initialize buffer to a dark blue background
  //for (int i = 0; i < width * height; ++i) {
    //buffer[i] = 0xFF000030; // Dark blue background
  //}
  //// Converts a HVM2 tuple-encoded quadtree to a color buffer
  //read_img(net, argv[0], width, height, buffer);
  //// Render the buffer to the screen
  //render(width, height, buffer);
  //// Wait some time
  //SDL_Delay(2000);
  //// Free the buffer
  //free(buffer);
  //return new_port(ERA, 0);
//}
//#else
//// IO: DrawImage
//Port io_put_image(Net* net, Book* book, u32 argc, Port* argv) {
  //printf("DRAWIMAGE: disabled.\n");
  //printf("Image rendering is a WIP. For now, to enable it, you must:\n");
  //printf("1. Generate a C file, with `hvm gen-c your_file.hvm`.\n");
  //printf("2. Manually un-comment the '#define IO_DRAWIMAGE' line on it.\n");
  //printf("3. Have SDL installed and compile it with '-lSDL2'.\n");
  //return new_port(ERA, 0);
//}
//#endif

// Book Loader
// -----------

bool book_load(Book* book, u32* buf) {
  // Reads defs_len
  book->defs_len = *buf++;

  // Parses each def
  for (u32 i = 0; i < book->defs_len; ++i) {
    // Reads fid
    u32 fid = *buf++;

    // Gets def
    Def* def = &book->defs_buf[fid];

    // Reads name
    memcpy(def->name, buf, 256);
    buf += 64;

    // Reads safe flag
    def->safe = *buf++;

    // Reads lengths
    def->rbag_len = *buf++;
    def->node_len = *buf++;
    def->vars_len = *buf++;

    if (def->rbag_len > DEF_RBAG_LEN) {
      fprintf(stderr, "def '%s' has too many redexes: %u\n", def->name, def->rbag_len);
      return false;
    }

    if (def->node_len > DEF_NODE_LEN) {
      fprintf(stderr, "def '%s' has too many nodes: %u\n", def->name, def->node_len);
      return false;
    }

    // Reads root
    def->root = *buf++;

    // Reads rbag_buf
    memcpy(def->rbag_buf, buf, 8*def->rbag_len);
    buf += def->rbag_len * 2;

    // Reads node_buf
    memcpy(def->node_buf, buf, 8*def->node_len);
    buf += def->node_len * 2;
  }

  return true;
}

// Debug Printing
// --------------

void put_u32(char* B, u32 val) {
  for (int i = 0; i < 8; i++, val >>= 4) {
    B[8-i-1] = "0123456789ABCDEF"[val & 0xF];
  }
}

Show show_port(Port port) {
  // NOTE: this is done like that because sprintf seems not to be working
  Show s;
  switch (get_tag(port)) {
    case VAR: memcpy(s.x, "VAR:", 4); put_u32(s.x+4, get_val(port)); break;
    case REF: memcpy(s.x, "REF:", 4); put_u32(s.x+4, get_val(port)); break;
    case ERA: memcpy(s.x, "ERA:________", 12); break;
    case NUM: memcpy(s.x, "NUM:", 4); put_u32(s.x+4, get_val(port)); break;
    case CON: memcpy(s.x, "CON:", 4); put_u32(s.x+4, get_val(port)); break;
    case DUP: memcpy(s.x, "DUP:", 4); put_u32(s.x+4, get_val(port)); break;
    case OPR: memcpy(s.x, "OPR:", 4); put_u32(s.x+4, get_val(port)); break;
    case SWI: memcpy(s.x, "SWI:", 4); put_u32(s.x+4, get_val(port)); break;
  }
  s.x[12] = '\0';
  return s;
}

Show show_rule(Rule rule) {
  Show s;
  switch (rule) {
    case LINK: memcpy(s.x, "LINK", 4); break;
    case VOID: memcpy(s.x, "VOID", 4); break;
    case ERAS: memcpy(s.x, "ERAS", 4); break;
    case ANNI: memcpy(s.x, "ANNI", 4); break;
    case COMM: memcpy(s.x, "COMM", 4); break;
    case OPER: memcpy(s.x, "OPER", 4); break;
    case SWIT: memcpy(s.x, "SWIT", 4); break;
    case CALL: memcpy(s.x, "CALL", 4); break;
    default  : memcpy(s.x, "????", 4); break;
  }
  s.x[4] = '\0';
  return s;
}

//void print_rbag(RBag* rbag) {
  //printf("RBAG | FST-TREE     | SND-TREE    \n");
  //printf("---- | ------------ | ------------\n");
  //for (u32 i = rbag->lo_ini; i < rbag->lo_end; ++i) {
    //Pair redex = rbag->lo_buf[i%RLEN];
    //printf("%04X | %s | %s\n", i, show_port(get_fst(redex)).x, show_port(get_snd(redex)).x);
  //}
  //for (u32 i = 0; i > rbag->hi_end; ++i) {
    //Pair redex = rbag->hi_buf[i];
    //printf("%04X | %s | %s\n", i, show_port(get_fst(redex)).x, show_port(get_snd(redex)).x);
  //}
  //printf("==== | ============ | ============\n");
//}

void print_net(Net* net) {
  printf("NODE | PORT-1       | PORT-2      \n");
  printf("---- | ------------ | ------------\n");
  for (u32 i = 0; i < G_NODE_LEN; ++i) {
    Pair node = node_load(net, i);
    if (node != 0) {
      printf("%04X | %s | %s\n", i, show_port(get_fst(node)).x, show_port(get_snd(node)).x);
    }
  }
  printf("==== | ============ |\n");
  printf("VARS | VALUE        |\n");
  printf("---- | ------------ |\n");
  for (u32 i = 0; i < G_VARS_LEN; ++i) {
    Port var = vars_load(net,i);
    if (var != 0) {
      printf("%04X | %s |\n", i, show_port(vars_load(net,i)).x);
    }
  }
  printf("==== | ============ |\n");
}

void pretty_print_numb(Numb word) {
  switch (get_typ(word)) {
    case TY_SYM: {
      switch (get_sym(word)) {
        // types
        case TY_U24: printf("[u24]"); break;
        case TY_I24: printf("[i24]"); break;
        case TY_F24: printf("[f24]"); break;
        // operations
        case OP_ADD: printf("[+]"); break;
        case OP_SUB: printf("[-]"); break;
        case FP_SUB: printf("[:-]"); break;
        case OP_MUL: printf("[*]"); break;
        case OP_DIV: printf("[/]"); break;
        case FP_DIV: printf("[:/]"); break;
        case OP_REM: printf("[%%]"); break;
        case FP_REM: printf("[:%%]"); break;
        case OP_EQ:  printf("[=]"); break;
        case OP_NEQ: printf("[!]"); break;
        case OP_LT:  printf("[<]"); break;
        case OP_GT:  printf("[>]"); break;
        case OP_AND: printf("[&]"); break;
        case OP_OR:  printf("[|]"); break;
        case OP_XOR: printf("[^]"); break;
        case OP_SHL: printf("[<<]"); break;
        case FP_SHL: printf("[:<<]"); break;
        case OP_SHR: printf("[>>]"); break;
        case FP_SHR: printf("[:>>]"); break;
        default:     printf("[?]"); break;
      }
      break;
    }
    case TY_U24: {
      printf("%u", get_u24(word));
      break;
    }
    case TY_I24: {
      printf("%+d", get_i24(word));
      break;
    }
    case TY_F24: {
      if (isinf(get_f24(word))) {
        if (signbit(get_f24(word))) {
          printf("-inf");
        } else {
          printf("+inf");
        }
      } else if (isnan(get_f24(word))) {
        printf("+NaN");
      } else {
        printf("%.7e", get_f24(word));
      }
      break;
    }
    default: {
      switch (get_typ(word)) {
        case OP_ADD: printf("[+0x%07X]", get_u24(word)); break;
        case OP_SUB: printf("[-0x%07X]", get_u24(word)); break;
        case FP_SUB: printf("[:-0x%07X]", get_u24(word)); break;
        case OP_MUL: printf("[*0x%07X]", get_u24(word)); break;
        case OP_DIV: printf("[/0x%07X]", get_u24(word)); break;
        case FP_DIV: printf("[:/0x%07X]", get_u24(word)); break;
        case OP_REM: printf("[%%0x%07X]", get_u24(word)); break;
        case FP_REM: printf("[:%%0x%07X]", get_u24(word)); break;
        case OP_EQ:  printf("[=0x%07X]", get_u24(word)); break;
        case OP_NEQ: printf("[!0x%07X]", get_u24(word)); break;
        case OP_LT:  printf("[<0x%07X]", get_u24(word)); break;
        case OP_GT:  printf("[>0x%07X]", get_u24(word)); break;
        case OP_AND: printf("[&0x%07X]", get_u24(word)); break;
        case OP_OR:  printf("[|0x%07X]", get_u24(word)); break;
        case OP_XOR: printf("[^0x%07X]", get_u24(word)); break;
        case OP_SHL: printf("[<<0x%07X]", get_u24(word)); break;
        case FP_SHL: printf("[:<<0x%07X]", get_u24(word)); break;
        case OP_SHR: printf("[>>0x%07X]", get_u24(word)); break;
        case FP_SHR: printf("[:>>0x%07X]", get_u24(word)); break;
        default:     printf("[?0x%07X]", get_u24(word)); break;
      }
      break;
    }
  }

}

void pretty_print_port(Net* net, Book* book, Port port) {
  Port stack[4096];
  stack[0] = port;
  u32 len = 1;
  u32 num = 0;
  while (len > 0) {
    Port cur = stack[--len];
    switch (get_tag(cur)) {
      case CON: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p2;
        stack[len++] = new_port(ERA, (u32)(' '));
        stack[len++] = p1;
        break;
      }
      case ERA: {
        if (get_val(cur) != 0) {
          printf("%c", (char)get_val(cur));
        } else {
          printf("*");
        }
        break;
      }
      case VAR: {
        Port got = vars_load(net, get_val(cur));
        if (got != NONE) {
          stack[len++] = got;
        } else {
          printf("x%x", get_val(cur));
        }
        break;
      }
      case NUM: {
        pretty_print_numb(get_val(cur));
        break;
      }
      case DUP: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("{");
        stack[len++] = new_port(ERA, (u32)('}'));
        stack[len++] = p2;
        stack[len++] = new_port(ERA, (u32)(' '));
        stack[len++] = p1;
        break;
      }
      case OPR: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("$(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p2;
        stack[len++] = new_port(ERA, (u32)(' '));
        stack[len++] = p1;
        break;
      }
      case SWI: {
        Pair node = node_load(net,get_val(cur));
        Port p2   = get_snd(node);
        Port p1   = get_fst(node);
        printf("?(");
        stack[len++] = new_port(ERA, (u32)(')'));
        stack[len++] = p2;
        stack[len++] = new_port(ERA, (u32)(' '));
        stack[len++] = p1;
        break;
      }
      case REF: {
        u32  fid = get_val(cur) & 0xFFFFFFF;
        Def* def = &book->defs_buf[fid];
        printf("@%s", def->name);
        break;
      }
    }
  }
}

//void pretty_print_rbag(Net* net, RBag* rbag) {
  //for (u32 i = rbag->lo_ini; i < rbag->lo_end; ++i) {
    //Pair redex = rbag->lo_buf[i];
    //if (redex != 0) {
      //pretty_print_port(net, get_fst(redex));
      //printf(" ~ ");
      //pretty_print_port(net, get_snd(redex));
      //printf("\n");
    //}
  //}
  //for (u32 i = 0; i > rbag->hi_end; ++i) {
    //Pair redex = rbag->hi_buf[i];
    //if (redex != 0) {
      //pretty_print_port(net, get_fst(redex));
      //printf(" ~ ");
      //pretty_print_port(net, get_snd(redex));
      //printf("\n");
    //}
  //}
//}

// Demos
// -----

  // stress_test 2^10 x 65536
  //static const u8 BOOK_BUF[] = {6, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 11, 10, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 102, 117, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 25, 0, 0, 0, 2, 0, 0, 0, 102, 117, 110, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 4, 0, 0, 0, 11, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 102, 117, 110, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 128, 20, 0, 0, 0, 9, 0, 0, 128, 44, 0, 0, 0, 13, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 3, 4, 0, 0, 38, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 4, 0, 0, 0, 108, 111, 111, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 41, 0, 0, 0, 5, 0, 0, 0, 108, 111, 111, 112, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0};

  // stress_test 2^18 x 65536
  //static const u8 BOOK_BUF[] = {6, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 11, 18, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 102, 117, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 17, 0, 0, 0, 25, 0, 0, 0, 2, 0, 0, 0, 102, 117, 110, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 4, 0, 0, 0, 11, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 102, 117, 110, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 128, 20, 0, 0, 0, 9, 0, 0, 128, 44, 0, 0, 0, 13, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 3, 4, 0, 0, 38, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 4, 0, 0, 0, 108, 111, 111, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 41, 0, 0, 0, 5, 0, 0, 0, 108, 111, 111, 112, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0};

  // bitonic_sort 2^20
  //static const u8 BOOK_BUF[] = {19, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 89, 0, 0, 0, 4, 0, 0, 0, 11, 18, 0, 0, 12, 0, 0, 0, 65, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 100, 111, 119, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 60, 0, 0, 0, 20, 0, 0, 0, 44, 0, 0, 0, 28, 0, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 68, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 2, 0, 0, 0, 100, 111, 119, 110, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 13, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 25, 0, 0, 128, 60, 0, 0, 0, 25, 0, 0, 128, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 45, 0, 0, 0, 52, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 32, 0, 0, 0, 76, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 40, 0, 0, 0, 100, 0, 0, 0, 24, 0, 0, 0, 56, 0, 0, 0, 3, 0, 0, 0, 102, 108, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 60, 0, 0, 0, 20, 0, 0, 0, 44, 0, 0, 0, 28, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 68, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 4, 0, 0, 0, 102, 108, 111, 119, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 14, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 60, 0, 0, 0, 129, 0, 0, 0, 84, 0, 0, 0, 13, 0, 0, 0, 28, 0, 0, 0, 22, 0, 0, 0, 8, 0, 0, 0, 35, 1, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 53, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 32, 0, 0, 0, 76, 0, 0, 0, 56, 0, 0, 0, 48, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 40, 0, 0, 0, 100, 0, 0, 0, 16, 0, 0, 0, 108, 0, 0, 0, 24, 0, 0, 0, 56, 0, 0, 0, 5, 0, 0, 0, 103, 101, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 103, 101, 110, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 41, 0, 0, 128, 68, 0, 0, 0, 41, 0, 0, 128, 84, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 60, 0, 0, 0, 38, 0, 0, 0, 54, 0, 0, 0, 59, 2, 0, 0, 46, 0, 0, 0, 35, 1, 0, 0, 16, 0, 0, 0, 59, 2, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 7, 0, 0, 0, 109, 97, 105, 110, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 4, 0, 0, 0, 11, 18, 0, 0, 12, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 109, 97, 105, 110, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 73, 0, 0, 0, 4, 0, 0, 0, 11, 18, 0, 0, 12, 0, 0, 0, 11, 0, 0, 0, 20, 0, 0, 0, 57, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 115, 111, 114, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 60, 0, 0, 0, 20, 0, 0, 0, 44, 0, 0, 0, 28, 0, 0, 0, 81, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 68, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 10, 0, 0, 0, 115, 111, 114, 116, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 17, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 25, 0, 0, 0, 60, 0, 0, 0, 73, 0, 0, 128, 92, 0, 0, 0, 73, 0, 0, 128, 116, 0, 0, 0, 13, 0, 0, 0, 36, 0, 0, 0, 22, 0, 0, 0, 29, 0, 0, 0, 35, 1, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 44, 0, 0, 0, 52, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 40, 0, 0, 0, 76, 0, 0, 0, 84, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 64, 0, 0, 0, 8, 0, 0, 0, 100, 0, 0, 0, 11, 0, 0, 0, 108, 0, 0, 0, 24, 0, 0, 0, 56, 0, 0, 0, 16, 0, 0, 0, 124, 0, 0, 0, 11, 1, 0, 0, 132, 0, 0, 0, 32, 0, 0, 0, 64, 0, 0, 0, 11, 0, 0, 0, 115, 117, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 115, 117, 109, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 89, 0, 0, 128, 36, 0, 0, 0, 89, 0, 0, 128, 68, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 54, 0, 0, 0, 3, 4, 0, 0, 62, 0, 0, 0, 40, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 13, 0, 0, 0, 115, 119, 97, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 44, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 113, 0, 0, 0, 121, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 8, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 14, 0, 0, 0, 115, 119, 97, 112, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 115, 119, 97, 112, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 119, 97, 114, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 52, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 137, 0, 0, 0, 145, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 8, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 60, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 17, 0, 0, 0, 119, 97, 114, 112, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 12, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 105, 0, 0, 0, 76, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 52, 0, 0, 0, 38, 0, 0, 0, 24, 0, 0, 0, 3, 15, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 62, 0, 0, 0, 40, 0, 0, 0, 3, 18, 0, 0, 70, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 32, 0, 0, 0, 84, 0, 0, 0, 24, 0, 0, 0, 92, 0, 0, 0, 8, 0, 0, 0, 40, 0, 0, 0, 18, 0, 0, 0, 119, 97, 114, 112, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 21, 0, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 129, 0, 0, 128, 92, 0, 0, 0, 129, 0, 0, 128, 132, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 44, 0, 0, 0, 52, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 61, 0, 0, 0, 68, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 76, 0, 0, 0, 84, 0, 0, 0, 64, 0, 0, 0, 72, 0, 0, 0, 80, 0, 0, 0, 88, 0, 0, 0, 8, 0, 0, 0, 100, 0, 0, 0, 56, 0, 0, 0, 108, 0, 0, 0, 40, 0, 0, 0, 116, 0, 0, 0, 24, 0, 0, 0, 124, 0, 0, 0, 72, 0, 0, 0, 88, 0, 0, 0, 0, 0, 0, 0, 140, 0, 0, 0, 48, 0, 0, 0, 148, 0, 0, 0, 32, 0, 0, 0, 156, 0, 0, 0, 16, 0, 0, 0, 164, 0, 0, 0, 64, 0, 0, 0, 80, 0, 0, 0};

static const u8 BOOK_BUF[] = {73, 0, 0, 0, 0, 0, 0, 0, 109, 97, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 177, 1, 0, 0, 4, 0, 0, 0, 121, 1, 0, 0, 12, 0, 0, 0, 11, 80, 195, 0, 20, 0, 0, 0, 27, 18, 131, 58, 0, 0, 0, 0, 1, 0, 0, 0, 76, 105, 115, 116, 47, 67, 111, 110, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 17, 0, 0, 0, 36, 0, 0, 0, 0, 0, 0, 0, 44, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 2, 0, 0, 0, 76, 105, 115, 116, 47, 67, 111, 110, 115, 47, 116, 97, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 1, 0, 0, 3, 0, 0, 0, 76, 105, 115, 116, 47, 78, 105, 108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 76, 105, 115, 116, 47, 78, 105, 108, 47, 116, 97, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 5, 0, 0, 0, 77, 97, 112, 47, 76, 101, 97, 102, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 49, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 77, 97, 112, 47, 76, 101, 97, 102, 47, 116, 97, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 1, 0, 0, 7, 0, 0, 0, 77, 97, 112, 47, 78, 111, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 24, 0, 0, 0, 65, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 77, 97, 112, 47, 78, 111, 100, 101, 47, 116, 97, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 9, 0, 0, 0, 77, 97, 112, 47, 101, 109, 112, 116, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41, 0, 0, 0, 10, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 105, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 57, 0, 0, 0, 44, 0, 0, 0, 81, 0, 0, 0, 60, 0, 0, 0, 14, 0, 0, 0, 20, 0, 0, 0, 75, 2, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 36, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 52, 0, 0, 0, 40, 0, 0, 0, 32, 0, 0, 0, 24, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 40, 0, 0, 0, 12, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 13, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 57, 0, 0, 0, 60, 0, 0, 0, 81, 0, 0, 0, 84, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 22, 0, 0, 0, 28, 0, 0, 0, 75, 2, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 44, 0, 0, 0, 24, 0, 0, 0, 52, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 16, 0, 0, 0, 68, 0, 0, 0, 24, 0, 0, 0, 76, 0, 0, 0, 48, 0, 0, 0, 40, 0, 0, 0, 32, 0, 0, 0, 92, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 8, 0, 0, 0, 48, 0, 0, 0, 13, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 49, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 161, 0, 0, 0, 169, 0, 0, 0, 14, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 13, 0, 0, 0, 8, 0, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 91, 2, 0, 0, 31, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 89, 0, 0, 0, 97, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 15, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 5, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 57, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 57, 0, 0, 0, 28, 0, 0, 0, 81, 0, 0, 0, 52, 0, 0, 0, 14, 0, 0, 0, 20, 0, 0, 0, 75, 2, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 233, 1, 0, 0, 36, 0, 0, 0, 24, 0, 0, 0, 44, 0, 0, 0, 41, 0, 0, 0, 16, 0, 0, 0, 41, 0, 0, 0, 60, 0, 0, 0, 0, 0, 0, 0, 68, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 17, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 53, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 57, 0, 0, 0, 36, 0, 0, 0, 81, 0, 0, 0, 60, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 22, 0, 0, 0, 28, 0, 0, 0, 75, 2, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 233, 1, 0, 0, 44, 0, 0, 0, 41, 0, 0, 0, 52, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 41, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 18, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 54, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 13, 0, 0, 0, 8, 0, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 91, 2, 0, 0, 31, 0, 0, 0, 36, 0, 0, 0, 44, 0, 0, 0, 129, 0, 0, 0, 137, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 19, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 55, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 57, 0, 0, 0, 28, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 41, 0, 0, 0, 44, 0, 0, 0, 41, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 56, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 14, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 54, 0, 0, 0, 99, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 37, 0, 0, 0, 44, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 24, 0, 0, 0, 63, 0, 0, 0, 68, 0, 0, 0, 76, 0, 0, 0, 113, 0, 0, 0, 121, 0, 0, 0, 32, 0, 0, 0, 84, 0, 0, 0, 40, 0, 0, 0, 92, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 16, 0, 0, 0, 48, 0, 0, 0, 21, 0, 0, 0, 77, 97, 112, 47, 115, 101, 116, 95, 95, 67, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 30, 0, 0, 0, 99, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 21, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 39, 0, 0, 0, 44, 0, 0, 0, 52, 0, 0, 0, 145, 0, 0, 0, 153, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 22, 0, 0, 0, 80, 97, 114, 116, 105, 99, 108, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 24, 0, 0, 0, 185, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 23, 0, 0, 0, 80, 97, 114, 116, 105, 99, 108, 101, 47, 116, 97, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 24, 0, 0, 0, 86, 101, 99, 116, 111, 114, 51, 68, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 24, 0, 0, 0, 201, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 25, 0, 0, 0, 86, 101, 99, 116, 111, 114, 51, 68, 47, 116, 97, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 26, 0, 0, 0, 97, 100, 100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 241, 0, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 97, 100, 100, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 15, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 193, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 38, 0, 0, 0, 52, 0, 0, 0, 3, 4, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 62, 0, 0, 0, 76, 0, 0, 0, 3, 4, 0, 0, 70, 0, 0, 0, 8, 0, 0, 0, 32, 0, 0, 0, 86, 0, 0, 0, 48, 0, 0, 0, 3, 4, 0, 0, 94, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 108, 0, 0, 0, 32, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 28, 0, 0, 0, 97, 100, 100, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 217, 0, 0, 0, 2, 0, 0, 0, 29, 0, 0, 0, 97, 100, 100, 95, 95, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 24, 0, 0, 0, 225, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 30, 0, 0, 0, 97, 100, 100, 95, 95, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 233, 0, 0, 0, 2, 0, 0, 0, 31, 0, 0, 0, 99, 97, 108, 99, 117, 108, 97, 116, 101, 95, 102, 111, 114, 99, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 33, 1, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 99, 97, 108, 99, 117, 108, 97, 116, 101, 95, 102, 111, 114, 99, 101, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 19, 0, 0, 0, 10, 0, 0, 0, 4, 0, 0, 0, 145, 1, 0, 0, 68, 0, 0, 0, 169, 1, 0, 0, 84, 0, 0, 0, 193, 1, 0, 0, 92, 0, 0, 0, 105, 1, 0, 0, 110, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 36, 0, 0, 0, 45, 0, 0, 0, 48, 0, 0, 0, 54, 0, 0, 0, 32, 0, 0, 0, 3, 7, 0, 0, 62, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 76, 0, 0, 0, 64, 0, 0, 0, 48, 0, 0, 0, 72, 0, 0, 0, 56, 0, 0, 0, 16, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 72, 0, 0, 0, 3, 7, 0, 0, 118, 0, 0, 0, 8, 0, 0, 0, 126, 0, 0, 0, 3, 7, 0, 0, 134, 0, 0, 0, 24, 0, 0, 0, 142, 0, 0, 0, 3, 8, 0, 0, 150, 0, 0, 0, 40, 0, 0, 0, 64, 0, 0, 0, 33, 0, 0, 0, 99, 97, 108, 99, 117, 108, 97, 116, 101, 95, 102, 111, 114, 99, 101, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 41, 1, 0, 0, 60, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 2, 0, 0, 0, 28, 0, 0, 0, 16, 0, 0, 0, 36, 0, 0, 0, 45, 0, 0, 0, 52, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 68, 0, 0, 0, 8, 0, 0, 0, 77, 0, 0, 0, 86, 0, 0, 0, 56, 0, 0, 0, 99, 0, 0, 0, 95, 0, 0, 0, 100, 0, 0, 0, 156, 0, 0, 0, 1, 1, 0, 0, 108, 0, 0, 0, 2, 0, 0, 0, 116, 0, 0, 0, 2, 0, 0, 0, 124, 0, 0, 0, 2, 0, 0, 0, 132, 0, 0, 0, 2, 0, 0, 0, 140, 0, 0, 0, 2, 0, 0, 0, 148, 0, 0, 0, 2, 0, 0, 0, 113, 1, 0, 0, 24, 0, 0, 0, 164, 0, 0, 0, 40, 0, 0, 0, 172, 0, 0, 0, 0, 0, 0, 0, 180, 0, 0, 0, 16, 0, 0, 0, 188, 0, 0, 0, 56, 0, 0, 0, 48, 0, 0, 0, 34, 0, 0, 0, 99, 97, 108, 99, 117, 108, 97, 116, 101, 95, 102, 111, 114, 99, 101, 95, 95, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 9, 1, 0, 0, 2, 0, 0, 0, 35, 0, 0, 0, 99, 97, 108, 99, 117, 108, 97, 116, 101, 95, 102, 111, 114, 99, 101, 95, 95, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 17, 1, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 36, 0, 0, 0, 99, 97, 108, 99, 117, 108, 97, 116, 101, 95, 102, 111, 114, 99, 101, 95, 95, 67, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 25, 1, 0, 0, 2, 0, 0, 0, 37, 0, 0, 0, 100, 105, 115, 116, 97, 110, 99, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 73, 1, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 100, 105, 115, 116, 97, 110, 99, 101, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 38, 0, 0, 0, 116, 0, 0, 0, 3, 5, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 3, 18, 0, 0, 62, 0, 0, 0, 27, 0, 0, 64, 70, 0, 0, 0, 3, 4, 0, 0, 78, 0, 0, 0, 24, 0, 0, 0, 86, 0, 0, 0, 3, 4, 0, 0, 94, 0, 0, 0, 32, 0, 0, 0, 102, 0, 0, 0, 3, 18, 0, 0, 110, 0, 0, 0, 27, 0, 0, 63, 40, 0, 0, 0, 126, 0, 0, 0, 156, 0, 0, 0, 3, 5, 0, 0, 134, 0, 0, 0, 8, 0, 0, 0, 142, 0, 0, 0, 3, 18, 0, 0, 150, 0, 0, 0, 27, 0, 0, 64, 24, 0, 0, 0, 166, 0, 0, 0, 40, 0, 0, 0, 3, 5, 0, 0, 174, 0, 0, 0, 16, 0, 0, 0, 182, 0, 0, 0, 3, 18, 0, 0, 190, 0, 0, 0, 27, 0, 0, 64, 32, 0, 0, 0, 39, 0, 0, 0, 100, 105, 115, 116, 97, 110, 99, 101, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 49, 1, 0, 0, 2, 0, 0, 0, 40, 0, 0, 0, 100, 105, 115, 116, 97, 110, 99, 101, 95, 95, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 24, 0, 0, 0, 57, 1, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 41, 0, 0, 0, 100, 105, 115, 116, 97, 110, 99, 101, 95, 95, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 65, 1, 0, 0, 2, 0, 0, 0, 42, 0, 0, 0, 100, 105, 118, 105, 100, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 97, 1, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 100, 105, 118, 105, 100, 101, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 15, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 193, 0, 0, 0, 100, 0, 0, 0, 14, 0, 0, 0, 28, 0, 0, 0, 3, 8, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 38, 0, 0, 0, 52, 0, 0, 0, 3, 8, 0, 0, 46, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 62, 0, 0, 0, 76, 0, 0, 0, 3, 8, 0, 0, 70, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 85, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 93, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 24, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 44, 0, 0, 0, 100, 105, 118, 105, 100, 101, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 89, 1, 0, 0, 2, 0, 0, 0, 45, 0, 0, 0, 103, 101, 116, 71, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 59, 148, 213, 64, 14, 0, 0, 0, 147, 0, 32, 65, 8, 0, 0, 0, 0, 0, 0, 0, 27, 0, 48, 193, 8, 0, 0, 0, 46, 0, 0, 0, 103, 101, 116, 95, 111, 114, 105, 103, 105, 110, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 193, 0, 0, 0, 4, 0, 0, 0, 27, 0, 0, 0, 12, 0, 0, 0, 27, 0, 0, 0, 20, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0, 47, 0, 0, 0, 103, 101, 116, 95, 112, 97, 114, 116, 105, 99, 108, 101, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 24, 0, 0, 0, 52, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 177, 0, 0, 0, 20, 0, 0, 0, 193, 0, 0, 0, 44, 0, 0, 0, 193, 0, 0, 0, 68, 0, 0, 0, 94, 0, 0, 0, 59, 254, 100, 62, 102, 0, 0, 0, 147, 0, 32, 65, 9, 0, 0, 0, 108, 0, 0, 0, 177, 0, 0, 0, 124, 0, 0, 0, 193, 0, 0, 0, 148, 0, 0, 0, 193, 0, 0, 0, 172, 0, 0, 0, 198, 0, 0, 0, 59, 171, 186, 62, 206, 0, 0, 0, 147, 0, 32, 65, 9, 0, 0, 0, 212, 0, 0, 0, 177, 0, 0, 0, 228, 0, 0, 0, 193, 0, 0, 0, 252, 0, 0, 0, 193, 0, 0, 0, 20, 1, 0, 0, 46, 1, 0, 0, 59, 227, 27, 62, 54, 1, 0, 0, 147, 0, 32, 65, 9, 0, 0, 0, 60, 1, 0, 0, 177, 0, 0, 0, 76, 1, 0, 0, 193, 0, 0, 0, 100, 1, 0, 0, 193, 0, 0, 0, 124, 1, 0, 0, 150, 1, 0, 0, 59, 42, 148, 62, 158, 1, 0, 0, 147, 0, 32, 65, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 36, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 27, 157, 254, 62, 52, 0, 0, 0, 27, 91, 119, 63, 60, 0, 0, 0, 27, 124, 219, 62, 24, 0, 0, 0, 27, 17, 75, 62, 76, 0, 0, 0, 27, 228, 184, 62, 84, 0, 0, 0, 27, 115, 48, 63, 32, 0, 0, 0, 48, 0, 0, 0, 40, 0, 0, 0, 27, 0, 32, 65, 48, 0, 0, 0, 56, 0, 0, 0, 116, 0, 0, 0, 64, 0, 0, 0, 16, 0, 0, 0, 72, 0, 0, 0, 132, 0, 0, 0, 80, 0, 0, 0, 140, 0, 0, 0, 88, 0, 0, 0, 56, 0, 0, 0, 27, 241, 118, 63, 156, 0, 0, 0, 27, 64, 82, 63, 164, 0, 0, 0, 27, 215, 214, 62, 72, 0, 0, 0, 27, 166, 41, 63, 180, 0, 0, 0, 27, 72, 22, 63, 188, 0, 0, 0, 27, 227, 39, 62, 80, 0, 0, 0, 96, 0, 0, 0, 88, 0, 0, 0, 27, 0, 32, 65, 96, 0, 0, 0, 104, 0, 0, 0, 220, 0, 0, 0, 112, 0, 0, 0, 64, 0, 0, 0, 120, 0, 0, 0, 236, 0, 0, 0, 128, 0, 0, 0, 244, 0, 0, 0, 136, 0, 0, 0, 104, 0, 0, 0, 27, 9, 168, 60, 4, 1, 0, 0, 27, 172, 125, 60, 12, 1, 0, 0, 27, 184, 97, 62, 120, 0, 0, 0, 27, 148, 174, 62, 28, 1, 0, 0, 27, 127, 175, 60, 36, 1, 0, 0, 27, 170, 84, 63, 128, 0, 0, 0, 144, 0, 0, 0, 136, 0, 0, 0, 27, 0, 32, 65, 144, 0, 0, 0, 152, 0, 0, 0, 68, 1, 0, 0, 137, 1, 0, 0, 112, 0, 0, 0, 160, 0, 0, 0, 84, 1, 0, 0, 168, 0, 0, 0, 92, 1, 0, 0, 176, 0, 0, 0, 152, 0, 0, 0, 27, 163, 119, 63, 108, 1, 0, 0, 27, 235, 10, 63, 116, 1, 0, 0, 27, 189, 243, 62, 160, 0, 0, 0, 27, 244, 136, 62, 132, 1, 0, 0, 27, 217, 10, 63, 140, 1, 0, 0, 27, 29, 114, 63, 168, 0, 0, 0, 184, 0, 0, 0, 176, 0, 0, 0, 27, 0, 32, 65, 184, 0, 0, 0, 48, 0, 0, 0, 103, 101, 116, 95, 112, 97, 114, 116, 105, 99, 108, 101, 115, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 24, 0, 0, 0, 52, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 177, 0, 0, 0, 20, 0, 0, 0, 193, 0, 0, 0, 44, 0, 0, 0, 193, 0, 0, 0, 68, 0, 0, 0, 94, 0, 0, 0, 59, 179, 94, 63, 102, 0, 0, 0, 147, 0, 32, 65, 9, 0, 0, 0, 108, 0, 0, 0, 177, 0, 0, 0, 124, 0, 0, 0, 193, 0, 0, 0, 148, 0, 0, 0, 193, 0, 0, 0, 172, 0, 0, 0, 198, 0, 0, 0, 59, 45, 179, 62, 206, 0, 0, 0, 147, 0, 32, 65, 9, 0, 0, 0, 212, 0, 0, 0, 177, 0, 0, 0, 228, 0, 0, 0, 193, 0, 0, 0, 252, 0, 0, 0, 193, 0, 0, 0, 20, 1, 0, 0, 46, 1, 0, 0, 59, 208, 75, 63, 54, 1, 0, 0, 147, 0, 32, 65, 9, 0, 0, 0, 60, 1, 0, 0, 177, 0, 0, 0, 76, 1, 0, 0, 193, 0, 0, 0, 100, 1, 0, 0, 193, 0, 0, 0, 124, 1, 0, 0, 150, 1, 0, 0, 59, 85, 107, 63, 158, 1, 0, 0, 147, 0, 32, 65, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 36, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 27, 251, 91, 63, 52, 0, 0, 0, 27, 77, 103, 63, 60, 0, 0, 0, 27, 4, 240, 62, 24, 0, 0, 0, 27, 58, 93, 63, 76, 0, 0, 0, 27, 1, 149, 62, 84, 0, 0, 0, 27, 139, 158, 61, 32, 0, 0, 0, 48, 0, 0, 0, 40, 0, 0, 0, 27, 0, 32, 65, 48, 0, 0, 0, 56, 0, 0, 0, 116, 0, 0, 0, 64, 0, 0, 0, 16, 0, 0, 0, 72, 0, 0, 0, 132, 0, 0, 0, 80, 0, 0, 0, 140, 0, 0, 0, 88, 0, 0, 0, 56, 0, 0, 0, 27, 229, 105, 63, 156, 0, 0, 0, 27, 233, 36, 63, 164, 0, 0, 0, 27, 59, 43, 63, 72, 0, 0, 0, 27, 195, 120, 63, 180, 0, 0, 0, 27, 75, 82, 63, 188, 0, 0, 0, 27, 61, 90, 63, 80, 0, 0, 0, 96, 0, 0, 0, 88, 0, 0, 0, 27, 0, 32, 65, 96, 0, 0, 0, 104, 0, 0, 0, 220, 0, 0, 0, 112, 0, 0, 0, 64, 0, 0, 0, 120, 0, 0, 0, 236, 0, 0, 0, 128, 0, 0, 0, 244, 0, 0, 0, 136, 0, 0, 0, 104, 0, 0, 0, 27, 251, 242, 62, 4, 1, 0, 0, 27, 199, 222, 62, 12, 1, 0, 0, 27, 129, 177, 62, 120, 0, 0, 0, 27, 226, 137, 62, 28, 1, 0, 0, 27, 208, 172, 62, 36, 1, 0, 0, 27, 172, 38, 63, 128, 0, 0, 0, 144, 0, 0, 0, 136, 0, 0, 0, 27, 0, 32, 65, 144, 0, 0, 0, 152, 0, 0, 0, 68, 1, 0, 0, 25, 0, 0, 0, 112, 0, 0, 0, 160, 0, 0, 0, 84, 1, 0, 0, 168, 0, 0, 0, 92, 1, 0, 0, 176, 0, 0, 0, 152, 0, 0, 0, 27, 178, 34, 63, 108, 1, 0, 0, 27, 160, 3, 63, 116, 1, 0, 0, 27, 180, 70, 62, 160, 0, 0, 0, 27, 251, 232, 61, 132, 1, 0, 0, 27, 173, 61, 62, 140, 1, 0, 0, 27, 219, 127, 63, 168, 0, 0, 0, 184, 0, 0, 0, 176, 0, 0, 0, 27, 0, 32, 65, 184, 0, 0, 0, 49, 0, 0, 0, 103, 101, 116, 95, 112, 97, 114, 116, 105, 99, 108, 101, 115, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 24, 0, 0, 0, 52, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 177, 0, 0, 0, 20, 0, 0, 0, 193, 0, 0, 0, 44, 0, 0, 0, 193, 0, 0, 0, 68, 0, 0, 0, 94, 0, 0, 0, 59, 13, 32, 63, 102, 0, 0, 0, 147, 0, 32, 65, 9, 0, 0, 0, 108, 0, 0, 0, 177, 0, 0, 0, 124, 0, 0, 0, 193, 0, 0, 0, 148, 0, 0, 0, 193, 0, 0, 0, 172, 0, 0, 0, 198, 0, 0, 0, 59, 62, 89, 63, 206, 0, 0, 0, 147, 0, 32, 65, 9, 0, 0, 0, 212, 0, 0, 0, 177, 0, 0, 0, 228, 0, 0, 0, 193, 0, 0, 0, 252, 0, 0, 0, 193, 0, 0, 0, 20, 1, 0, 0, 46, 1, 0, 0, 59, 159, 113, 63, 54, 1, 0, 0, 147, 0, 32, 65, 9, 0, 0, 0, 60, 1, 0, 0, 177, 0, 0, 0, 76, 1, 0, 0, 193, 0, 0, 0, 100, 1, 0, 0, 193, 0, 0, 0, 124, 1, 0, 0, 150, 1, 0, 0, 59, 87, 107, 60, 158, 1, 0, 0, 147, 0, 32, 65, 8, 0, 0, 0, 12, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 28, 0, 0, 0, 32, 0, 0, 0, 36, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 27, 242, 4, 62, 52, 0, 0, 0, 27, 188, 19, 61, 60, 0, 0, 0, 27, 172, 102, 63, 24, 0, 0, 0, 27, 255, 174, 62, 76, 0, 0, 0, 27, 231, 30, 63, 84, 0, 0, 0, 27, 237, 26, 63, 32, 0, 0, 0, 48, 0, 0, 0, 40, 0, 0, 0, 27, 0, 32, 65, 48, 0, 0, 0, 56, 0, 0, 0, 116, 0, 0, 0, 64, 0, 0, 0, 16, 0, 0, 0, 72, 0, 0, 0, 132, 0, 0, 0, 80, 0, 0, 0, 140, 0, 0, 0, 88, 0, 0, 0, 56, 0, 0, 0, 27, 107, 184, 62, 156, 0, 0, 0, 27, 17, 108, 62, 164, 0, 0, 0, 27, 163, 75, 63, 72, 0, 0, 0, 27, 71, 37, 63, 180, 0, 0, 0, 27, 80, 248, 62, 188, 0, 0, 0, 27, 68, 118, 63, 80, 0, 0, 0, 96, 0, 0, 0, 88, 0, 0, 0, 27, 0, 32, 65, 96, 0, 0, 0, 104, 0, 0, 0, 220, 0, 0, 0, 112, 0, 0, 0, 64, 0, 0, 0, 120, 0, 0, 0, 236, 0, 0, 0, 128, 0, 0, 0, 244, 0, 0, 0, 136, 0, 0, 0, 104, 0, 0, 0, 27, 96, 119, 63, 4, 1, 0, 0, 27, 247, 23, 63, 12, 1, 0, 0, 27, 104, 17, 62, 120, 0, 0, 0, 27, 136, 45, 63, 28, 1, 0, 0, 27, 161, 4, 62, 36, 1, 0, 0, 27, 141, 216, 62, 128, 0, 0, 0, 144, 0, 0, 0, 136, 0, 0, 0, 27, 0, 32, 65, 144, 0, 0, 0, 152, 0, 0, 0, 68, 1, 0, 0, 129, 1, 0, 0, 112, 0, 0, 0, 160, 0, 0, 0, 84, 1, 0, 0, 168, 0, 0, 0, 92, 1, 0, 0, 176, 0, 0, 0, 152, 0, 0, 0, 27, 51, 121, 63, 108, 1, 0, 0, 27, 236, 134, 62, 116, 1, 0, 0, 27, 91, 118, 63, 160, 0, 0, 0, 27, 67, 187, 61, 132, 1, 0, 0, 27, 153, 16, 63, 140, 1, 0, 0, 27, 95, 110, 62, 168, 0, 0, 0, 184, 0, 0, 0, 176, 0, 0, 0, 27, 0, 32, 65, 184, 0, 0, 0, 50, 0, 0, 0, 109, 117, 108, 116, 105, 112, 108, 121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 161, 1, 0, 0, 0, 0, 0, 0, 51, 0, 0, 0, 109, 117, 108, 116, 105, 112, 108, 121, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 15, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 193, 0, 0, 0, 100, 0, 0, 0, 14, 0, 0, 0, 28, 0, 0, 0, 3, 7, 0, 0, 22, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 38, 0, 0, 0, 52, 0, 0, 0, 3, 7, 0, 0, 46, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 62, 0, 0, 0, 76, 0, 0, 0, 3, 7, 0, 0, 70, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 85, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 93, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 24, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 52, 0, 0, 0, 109, 117, 108, 116, 105, 112, 108, 121, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 153, 1, 0, 0, 2, 0, 0, 0, 53, 0, 0, 0, 110, 111, 114, 109, 97, 108, 105, 122, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 81, 1, 0, 0, 20, 0, 0, 0, 41, 1, 0, 0, 36, 0, 0, 0, 13, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 24, 0, 0, 0, 16, 0, 0, 0, 113, 1, 0, 0, 44, 0, 0, 0, 8, 0, 0, 0, 24, 0, 0, 0, 54, 0, 0, 0, 115, 105, 109, 117, 108, 97, 116, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 21, 0, 0, 0, 24, 0, 0, 0, 30, 0, 0, 0, 16, 0, 0, 0, 99, 0, 0, 0, 39, 0, 0, 0, 44, 0, 0, 0, 84, 0, 0, 0, 185, 1, 0, 0, 52, 0, 0, 0, 2, 0, 0, 0, 60, 0, 0, 0, 8, 0, 0, 0, 68, 0, 0, 0, 2, 0, 0, 0, 76, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 55, 0, 0, 0, 115, 105, 109, 117, 108, 97, 116, 101, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 10, 0, 0, 0, 6, 0, 0, 0, 4, 0, 0, 0, 177, 1, 0, 0, 44, 0, 0, 0, 241, 1, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 22, 0, 0, 0, 28, 0, 0, 0, 51, 1, 0, 0, 8, 0, 0, 0, 37, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 76, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 115, 117, 98, 116, 114, 97, 99, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 225, 1, 0, 0, 0, 0, 0, 0, 57, 0, 0, 0, 115, 117, 98, 116, 114, 97, 99, 116, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 15, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 193, 0, 0, 0, 100, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 38, 0, 0, 0, 52, 0, 0, 0, 3, 5, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 62, 0, 0, 0, 76, 0, 0, 0, 3, 5, 0, 0, 70, 0, 0, 0, 8, 0, 0, 0, 32, 0, 0, 0, 86, 0, 0, 0, 48, 0, 0, 0, 3, 5, 0, 0, 94, 0, 0, 0, 16, 0, 0, 0, 40, 0, 0, 0, 24, 0, 0, 0, 108, 0, 0, 0, 32, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 58, 0, 0, 0, 115, 117, 98, 116, 114, 97, 99, 116, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 201, 1, 0, 0, 2, 0, 0, 0, 59, 0, 0, 0, 115, 117, 98, 116, 114, 97, 99, 116, 95, 95, 67, 50, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 8, 0, 0, 0, 20, 0, 0, 0, 16, 0, 0, 0, 28, 0, 0, 0, 36, 0, 0, 0, 24, 0, 0, 0, 209, 1, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 52, 0, 0, 0, 8, 0, 0, 0, 60, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 60, 0, 0, 0, 115, 117, 98, 116, 114, 97, 99, 116, 95, 95, 67, 51, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 217, 1, 0, 0, 2, 0, 0, 0, 61, 0, 0, 0, 117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 62, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 97, 108, 108, 95, 112, 97, 114, 116, 105, 99, 108, 101, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 249, 1, 0, 0, 20, 0, 0, 0, 13, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 63, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 97, 108, 108, 95, 112, 97, 114, 116, 105, 99, 108, 101, 115, 95, 95, 102, 111, 108, 100, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 9, 2, 0, 0, 0, 0, 0, 0, 64, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 97, 108, 108, 95, 112, 97, 114, 116, 105, 99, 108, 101, 115, 95, 95, 102, 111, 108, 100, 48, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 15, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0, 60, 0, 0, 0, 17, 2, 0, 0, 76, 0, 0, 0, 249, 1, 0, 0, 100, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 37, 0, 0, 0, 44, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 53, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 68, 0, 0, 0, 64, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 84, 0, 0, 0, 16, 0, 0, 0, 92, 0, 0, 0, 32, 0, 0, 0, 56, 0, 0, 0, 8, 0, 0, 0, 108, 0, 0, 0, 24, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 64, 0, 0, 0, 65, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 97, 108, 108, 95, 112, 97, 114, 116, 105, 99, 108, 101, 115, 95, 95, 102, 111, 108, 100, 48, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 36, 0, 0, 0, 2, 0, 0, 0, 25, 0, 0, 0, 66, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 112, 97, 114, 116, 105, 99, 108, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 9, 0, 0, 0, 5, 0, 0, 0, 4, 0, 0, 0, 41, 2, 0, 0, 60, 0, 0, 0, 13, 0, 0, 0, 44, 0, 0, 0, 20, 0, 0, 0, 24, 0, 0, 0, 33, 2, 0, 0, 28, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 32, 0, 0, 0, 68, 0, 0, 0, 24, 0, 0, 0, 8, 0, 0, 0, 67, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 112, 97, 114, 116, 105, 99, 108, 101, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 21, 0, 0, 0, 14, 0, 0, 0, 4, 0, 0, 0, 177, 0, 0, 0, 68, 0, 0, 0, 209, 0, 0, 0, 92, 0, 0, 0, 145, 1, 0, 0, 108, 0, 0, 0, 209, 0, 0, 0, 124, 0, 0, 0, 145, 1, 0, 0, 140, 0, 0, 0, 81, 1, 0, 0, 156, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 21, 0, 0, 0, 28, 0, 0, 0, 8, 0, 0, 0, 16, 0, 0, 0, 37, 0, 0, 0, 44, 0, 0, 0, 24, 0, 0, 0, 32, 0, 0, 0, 53, 0, 0, 0, 60, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 56, 0, 0, 0, 64, 0, 0, 0, 72, 0, 0, 0, 76, 0, 0, 0, 80, 0, 0, 0, 84, 0, 0, 0, 24, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 100, 0, 0, 0, 88, 0, 0, 0, 72, 0, 0, 0, 8, 0, 0, 0, 116, 0, 0, 0, 40, 0, 0, 0, 88, 0, 0, 0, 16, 0, 0, 0, 132, 0, 0, 0, 96, 0, 0, 0, 80, 0, 0, 0, 104, 0, 0, 0, 148, 0, 0, 0, 48, 0, 0, 0, 96, 0, 0, 0, 56, 0, 0, 0, 164, 0, 0, 0, 32, 0, 0, 0, 104, 0, 0, 0, 68, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 112, 97, 114, 116, 105, 99, 108, 101, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 25, 2, 0, 0, 2, 0, 0, 0, 69, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 112, 97, 114, 116, 105, 99, 108, 101, 95, 95, 102, 111, 108, 100, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 57, 2, 0, 0, 0, 0, 0, 0, 70, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 112, 97, 114, 116, 105, 99, 108, 101, 95, 95, 102, 111, 108, 100, 48, 95, 95, 67, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 11, 0, 0, 0, 7, 0, 0, 0, 4, 0, 0, 0, 209, 0, 0, 0, 44, 0, 0, 0, 249, 0, 0, 0, 60, 0, 0, 0, 41, 2, 0, 0, 76, 0, 0, 0, 2, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 8, 0, 0, 0, 28, 0, 0, 0, 37, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 40, 0, 0, 0, 52, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 16, 0, 0, 0, 68, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 8, 0, 0, 0, 84, 0, 0, 0, 24, 0, 0, 0, 48, 0, 0, 0, 71, 0, 0, 0, 117, 112, 100, 97, 116, 101, 95, 112, 97, 114, 116, 105, 99, 108, 101, 95, 95, 102, 111, 108, 100, 48, 95, 95, 67, 49, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 28, 0, 0, 0, 49, 2, 0, 0, 2, 0, 0, 0, 113, 1, 0, 0, 72, 0, 0, 0, 118, 101, 99, 116, 111, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 15, 0, 0, 0, 9, 0, 0, 0, 4, 0, 0, 0, 81, 0, 0, 0, 52, 0, 0, 0, 81, 0, 0, 0, 76, 0, 0, 0, 81, 0, 0, 0, 100, 0, 0, 0, 13, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 29, 0, 0, 0, 36, 0, 0, 0, 16, 0, 0, 0, 24, 0, 0, 0, 45, 0, 0, 0, 48, 0, 0, 0, 32, 0, 0, 0, 40, 0, 0, 0, 56, 0, 0, 0, 60, 0, 0, 0, 32, 0, 0, 0, 68, 0, 0, 0, 40, 0, 0, 0, 48, 0, 0, 0, 64, 0, 0, 0, 84, 0, 0, 0, 16, 0, 0, 0, 92, 0, 0, 0, 24, 0, 0, 0, 56, 0, 0, 0, 73, 0, 0, 0, 108, 0, 0, 0, 0, 0, 0, 0, 116, 0, 0, 0, 8, 0, 0, 0, 64, 0, 0, 0};

#ifdef IO
void do_run_io(Net* net, Book* book, Port port);
#endif

// Main
// ----

void hvm_c(u32* book_buffer) {
  // Creates static TMs
  alloc_static_tms();

  // Loads the Book
  Book* book = NULL;
  if (book_buffer) {
    book = (Book*)malloc(sizeof(Book));
    if (!book_load(book, book_buffer)) {
      fprintf(stderr, "failed to load book\n");

      return;
    }
  }

  // GMem
  Net *net = net_new();

  // Starts the timer
  u64 start = time64();

  // Creates an initial redex that calls main
  boot_redex(net, new_pair(new_port(REF, 0), ROOT));

  #ifdef IO
  do_run_io(net, book, ROOT);
  #else
  normalize(net, book);
  #endif

  // Prints the result
  printf("Result: ");
  pretty_print_port(net, book, enter(net, ROOT));
  printf("\n");

  // Stops the timer
  double duration = (time64() - start) / 1000000000.0; // seconds

  // Prints interactions and time
  u64 itrs = atomic_load(&net->itrs);
  printf("- ITRS: %" PRIu64 "\n", itrs);
  printf("- TIME: %.2fs\n", duration);
  printf("- MIPS: %.2f\n", (double)itrs / duration / 1000000.0);

  // Frees everything
  free_static_tms();
  free(net);
  free(book);
}

#ifdef WITH_MAIN
int main() {
  hvm_c((u32*)BOOK_BUF);
  return 0;
}
#endif


#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>


// Readback: λ-Encoded Ctr
typedef struct Ctr {
  u32  tag;
  u32  args_len;
  Port args_buf[16];
} Ctr;

// Readback: Tuples
typedef struct Tup {
  u32  elem_len;
  Port elem_buf[8];
} Tup;

// Readback: λ-Encoded Str (UTF-32), null-terminated
// FIXME: this is actually ASCII :|
typedef struct Str {
  u32  len;
  char *buf;
} Str;

// Readback: λ-Encoded list of bytes
typedef struct Bytes {
  u32  len;
  char *buf;
} Bytes;

// IO Magic Number
#define IO_MAGIC_0 0xD0CA11
#define IO_MAGIC_1 0xFF1FF1

// IO Tags
#define IO_DONE 0
#define IO_CALL 1

// Result Tags = Result<T, E>
#define RESULT_OK  0
#define RESULT_ERR 1

// IOError = {
//   Type,           -- a type error
//   Name,           -- invalid io func name
//   Inner {val: T}, -- an error while calling an io func
// }
#define IO_ERR_TYPE 0
#define IO_ERR_NAME 1
#define IO_ERR_INNER 2

typedef struct IOError {
  u32 tag;
  Port val;
} IOError;

// List Tags
#define LIST_NIL  0
#define LIST_CONS 1

// Readback
// --------

// Reads back a λ-Encoded constructor from device to host.
// Encoding: λt ((((t TAG) arg0) arg1) ...)
Ctr readback_ctr(Net* net, Book* book, Port port) {
  Ctr ctr;
  ctr.tag = -1;
  ctr.args_len = 0;

  // Loads root lambda
  Port lam_port = expand(net, book, port);
  if (get_tag(lam_port) != CON) return ctr;
  Pair lam_node = node_load(net, get_val(lam_port));

  // Loads first application
  Port app_port = expand(net, book, get_fst(lam_node));
  if (get_tag(app_port) != CON) return ctr;
  Pair app_node = node_load(net, get_val(app_port));

  // Loads first argument (as the tag)
  Port arg_port = expand(net, book, get_fst(app_node));
  if (get_tag(arg_port) != NUM) return ctr;
  ctr.tag = get_u24(get_val(arg_port));

  // Loads remaining arguments
  while (true) {
    app_port = expand(net, book, get_snd(app_node));
    if (get_tag(app_port) != CON) break;
    app_node = node_load(net, get_val(app_port));
    arg_port = expand(net, book, get_fst(app_node));
    ctr.args_buf[ctr.args_len++] = arg_port;
  }

  return ctr;
}

// Reads back a tuple of at most `size` elements. Tuples are
// (right-nested con nodes) (CON 1 (CON 2 (CON 3 (...))))
// The provided `port` should be `expanded` before calling.
extern Tup readback_tup(Net* net, Book* book, Port port, u32 size) {
  Tup tup;
  tup.elem_len = 0;

  // Loads remaining arguments
  while (get_tag(port) == CON && (tup.elem_len + 1 < size)) {
    Pair node = node_load(net, get_val(port));
    tup.elem_buf[tup.elem_len++] = expand(net, book, get_fst(node));

    port = expand(net, book, get_snd(node));
  }

  tup.elem_buf[tup.elem_len++] = port;

  return tup;
}

// Converts a Port into a list of bytes.
// Encoding:
// - λt (t NIL)
// - λt (((t CONS) head) tail)
Bytes readback_bytes(Net* net, Book* book, Port port) {
  Bytes bytes;
  u32 capacity = 256;
  bytes.buf = (char*) malloc(sizeof(char) * capacity);
  bytes.len = 0;

  // Readback loop
  while (true) {
    // Normalizes the net
    normalize(net, book);

    // Reads the λ-Encoded Ctr
    Ctr ctr = readback_ctr(net, book, peek(net, port));

    // Reads string layer
    switch (ctr.tag) {
      case LIST_NIL: {
        break;
      }
      case LIST_CONS: {
        if (ctr.args_len != 2) break;
        if (get_tag(ctr.args_buf[0]) != NUM) break;

        if (bytes.len == capacity - 1) {
          capacity *= 2;
          bytes.buf = realloc(bytes.buf, capacity);
        }

        bytes.buf[bytes.len++] = get_u24(get_val(ctr.args_buf[0]));
        boot_redex(net, new_pair(ctr.args_buf[1], ROOT));
        port = ROOT;
        continue;
      }
    }
    break;
  }

  return bytes;
}

// Converts a Port into a UTF-32 (truncated to 24 bits) null-terminated string.
// Since unicode scalars can fit in 21 bits, HVM's u24
// integers can contain any unicode scalar value.
// Encoding:
// - λt (t NIL)
// - λt (((t CONS) head) tail)
Str readback_str(Net* net, Book* book, Port port) {
  // readback_bytes is guaranteed to return a buffer with a capacity of at least one more
  // than the number of bytes read, so we can null-terminate it.
  Bytes bytes = readback_bytes(net, book, port);

  Str str;
  str.len = bytes.len;
  str.buf = bytes.buf;
  str.buf[str.len] = 0;

  return str;
}

/// Returns a λ-Encoded Ctr for a NIL: λt (t NIL)
/// A previous call to `get_resources(tm, 0, 2, 1)` is required.
Port inject_nil(Net* net) {
  u32 v1 = tm[0]->vloc[0];

  u32 n1 = tm[0]->nloc[0];
  u32 n2 = tm[0]->nloc[1];

  vars_create(net, v1, NONE);
  Port var = new_port(VAR, v1);

  node_create(net, n1, new_pair(new_port(NUM, new_u24(LIST_NIL)), var));
  node_create(net, n2, new_pair(new_port(CON, n1), var));

  return new_port(CON, n2);
}

/// Returns a λ-Encoded Ctr for a CONS: λt (((t CONS) head) tail)
/// A previous call to `get_resources(tm, 0, 4, 1)` is required.
Port inject_cons(Net* net, Port head, Port tail) {
  u32 v1 = tm[0]->vloc[0];

  u32 n1 = tm[0]->nloc[0];
  u32 n2 = tm[0]->nloc[1];
  u32 n3 = tm[0]->nloc[2];
  u32 n4 = tm[0]->nloc[3];

  vars_create(net, v1, NONE);
  Port var = new_port(VAR, v1);

  node_create(net, n1, new_pair(tail, var));
  node_create(net, n2, new_pair(head, new_port(CON, n1)));
  node_create(net, n3, new_pair(new_port(NUM, new_u24(LIST_CONS)), new_port(CON, n2)));
  node_create(net, n4, new_pair(new_port(CON, n3), var));

  return new_port(CON, n4);
}

// Converts a list of bytes to a Port.
// Encoding:
// - λt (t NIL)
// - λt (((t CONS) head) tail)
Port inject_bytes(Net* net, Bytes *bytes) {
  // Allocate all resources up front:
  // - NIL needs  2 nodes & 1 var
  // - CONS needs 4 nodes & 1 var
  u32 len = bytes->len;
  if (!get_resources(net, tm[0], 0, 2, 1)) {
    fprintf(stderr, "inject_bytes: failed to get resources\n");
    return new_port(ERA, 0);
  }
  Port port = inject_nil(net);

  // TODO: batch-allocate these (within the limits of TM)
  for (u32 i = 0; i < len; i++) {
    if (!get_resources(net, tm[0], 0, 4, 1)) {
      fprintf(stderr, "inject_bytes: failed to get resources\n");
      return new_port(ERA, 0);
    }
    Port byte = new_port(NUM, new_u24(bytes->buf[len - i - 1]));
    port = inject_cons(net, byte, port);
  }

  return port;
}

/// Returns a λ-Encoded Ctr for a RESULT_OK: λt ((t RESULT_OK) val)
Port inject_ok(Net* net, Port val) {
  if (!get_resources(net, tm[0], 0, 3, 1)) {
    fprintf(stderr, "inject_ok: failed to get resources\n");
    return new_port(ERA, 0);
  }

  u32 v1 = tm[0]->vloc[0];

  u32 n1 = tm[0]->nloc[0];
  u32 n2 = tm[0]->nloc[1];
  u32 n3 = tm[0]->nloc[2];

  vars_create(net, v1, NONE);
  Port var = new_port(VAR, v1);

  node_create(net, n1, new_pair(val, var));
  node_create(net, n2, new_pair(new_port(NUM, new_u24(RESULT_OK)), new_port(CON, n1)));
  node_create(net, n3, new_pair(new_port(CON, n2), var));

  return new_port(CON, n3);
}

/// Returns a λ-Encoded Ctr for a RESULT_ERR: λt ((t RESULT_ERR) err)
Port inject_err(Net* net, Port err) {
  if (!get_resources(net, tm[0], 0, 3, 1)) {
    fprintf(stderr, "inject_err: failed to get resources\n");
    return new_port(ERA, 0);
  }

  u32 v1 = tm[0]->vloc[0];

  u32 n1 = tm[0]->nloc[0];
  u32 n2 = tm[0]->nloc[1];
  u32 n3 = tm[0]->nloc[2];

  vars_create(net, v1, NONE);
  Port var = new_port(VAR, v1);

  node_create(net, n1, new_pair(err, var));
  node_create(net, n2, new_pair(new_port(NUM, new_u24(RESULT_ERR)), new_port(CON, n1)));
  node_create(net, n3, new_pair(new_port(CON, n2), var));

  return new_port(CON, n3);
}

/// Returns a λ-Encoded Ctr for a Result/Err(IOError(..))
Port inject_io_err(Net* net, IOError err) {
  if (err.tag <= IO_ERR_NAME) {
    if (!get_resources(net, tm[0], 0, 2, 1)) {
      fprintf(stderr, "inject_io_err: failed to get resources\n");
      return new_port(ERA, 0);
    }

    u32 v1 = tm[0]->vloc[0];

    u32 n1 = tm[0]->nloc[0];
    u32 n2 = tm[0]->nloc[1];

    vars_create(net, v1, NONE);
    Port var = new_port(VAR, v1);

    node_create(net, n1, new_pair(new_port(NUM, new_u24(err.tag)), var));
    node_create(net, n2, new_pair(new_port(CON, n1), var));

    return inject_err(net, new_port(CON, n2));
  }

  if (!get_resources(net, tm[0], 0, 3, 1)) {
    fprintf(stderr, "inject_io_err: failed to get resources\n");
    return new_port(ERA, 0);
  }

  u32 v1 = tm[0]->vloc[0];

  u32 n1 = tm[0]->nloc[0];
  u32 n2 = tm[0]->nloc[1];
  u32 n3 = tm[0]->nloc[2];

  vars_create(net, v1, NONE);
  Port var = new_port(VAR, v1);

  node_create(net, n1, new_pair(err.val, var));
  node_create(net, n2, new_pair(new_port(NUM, new_u24(IO_ERR_INNER)), new_port(CON, n1)));
  node_create(net, n3, new_pair(new_port(CON, n2), var));

  return inject_err(net, new_port(CON, n3));
}

/// Returns a λ-Encoded Ctr for a Result/Err(IOError/Type)
Port inject_io_err_type(Net* net) {
  IOError io_error = {
    .tag = IO_ERR_TYPE,
  };

  return inject_io_err(net, io_error);
}

/// Returns a λ-Encoded Ctr for a Result/Err(IOError/Name)
Port inject_io_err_name(Net* net) {
  IOError io_error = {
    .tag = IO_ERR_NAME,
  };

  return inject_io_err(net, io_error);
}

/// Returns a λ-Encoded Ctr for a Result/Err(IOError/Inner(val))
Port inject_io_err_inner(Net* net, Port val) {
  IOError io_error = {
    .tag = IO_ERR_INNER,
    .val = val,
  };

  return inject_io_err(net, io_error);
}

/// Returns a λ-Encoded Ctr for an Result<T, IOError<String>>
/// `err` must be `NUL`-terminated.
Port inject_io_err_str(Net* net, char* err) {
  Bytes err_bytes;
  err_bytes.buf = err;
  err_bytes.len = strlen(err_bytes.buf);
  Port err_port = inject_bytes(net, &err_bytes);

  return inject_io_err_inner(net, err_port);
}

// Primitive IO Fns
// -----------------

// Open file pointers. Indices into this array
// are used as "file descriptors".
// Indices 0 1 and 2 are reserved.
// - 0 -> stdin
// - 1 -> stdout
// - 2 -> stderr
static FILE* FILE_POINTERS[256];

// Open dylibs handles. Indices into this array
// are used as opaque loadedd object "handles".
static void* DYLIBS[256];

// Converts a NUM port (file descriptor) to file pointer.
FILE* readback_file(Port port) {
  if (get_tag(port) != NUM) {
    fprintf(stderr, "non-num where file descriptor was expected: %i\n", get_tag(port));
    return NULL;
  }

  u32 idx = get_u24(get_val(port));

  if (idx == 0) return stdin;
  if (idx == 1) return stdout;
  if (idx == 2) return stderr;

  FILE* fp = FILE_POINTERS[idx];
  if (fp == NULL) {
    return NULL;
  }

  return fp;
}

// Converts a NUM port (dylib handle) to an opaque dylib object.
void* readback_dylib(Port port) {
  if (get_tag(port) != NUM) {
    fprintf(stderr, "non-num where dylib handle was expected: %i\n", get_tag(port));
    return NULL;
  }

  u32 idx = get_u24(get_val(port));

  void* dl = DYLIBS[idx];
  if (dl == NULL) {
    fprintf(stderr, "invalid dylib handle\n");
    return NULL;
  }

  return dl;
}

// Reads from a file a specified number of bytes.
// `argm` is a tuple of (file_descriptor, num_bytes).
// Returns: Result<Bytes, IOError<i24>>
Port io_read(Net* net, Book* book, Port argm) {
  Tup tup = readback_tup(net, book, argm, 2);
  if (tup.elem_len != 2) {
    return inject_io_err_type(net);
  }

  FILE* fp = readback_file(tup.elem_buf[0]);
  u32 num_bytes = get_u24(get_val(tup.elem_buf[1]));

  if (fp == NULL) {
    return inject_io_err_inner(net, new_port(NUM, new_i24(EBADF)));
  }

  /// Read a string.
  Bytes bytes;
  bytes.buf = (char*) malloc(sizeof(char) * num_bytes);
  bytes.len = fread(bytes.buf, sizeof(char), num_bytes, fp);

  if ((bytes.len != num_bytes) && ferror(fp)) {
    free(bytes.buf);
    return inject_io_err_inner(net, new_port(NUM, new_i24(ferror(fp))));
  }

  // Convert it to a port.
  Port ret = inject_bytes(net, &bytes);
  free(bytes.buf);

  return inject_ok(net, ret);
}

// Opens a file with the provided mode.
// `argm` is a tuple (CON node) of the
// file name and mode as strings.
// Returns: Result<File, IOError<i24>>
Port io_open(Net* net, Book* book, Port argm) {
  Tup tup = readback_tup(net, book, argm, 2);
  if (tup.elem_len != 2) {
    return inject_io_err_type(net);
  }

  Str name = readback_str(net, book, tup.elem_buf[0]);
  Str mode = readback_str(net, book, tup.elem_buf[1]);

  for (u32 fd = 3; fd < sizeof(FILE_POINTERS); fd++) {
    if (FILE_POINTERS[fd] == NULL) {
      FILE_POINTERS[fd] = fopen(name.buf, mode.buf);

      free(name.buf);
      free(mode.buf);

      if (FILE_POINTERS[fd] == NULL) {
        return inject_io_err_inner(net, new_port(NUM, new_i24(errno)));
      }

      return inject_ok(net, new_port(NUM, new_u24(fd)));
    }
  }

  free(name.buf);
  free(mode.buf);

  // too many open files
  return inject_io_err_inner(net, new_port(NUM, new_i24(EMFILE)));
}

// Closes a file, reclaiming the file descriptor.
// Returns: Result<*, IOError<i24>>
Port io_close(Net* net, Book* book, Port argm) {
  FILE* fp = readback_file(argm);
  if (fp == NULL) {
    return inject_io_err_inner(net, new_port(NUM, new_i24(EBADF)));
  }

  if (fclose(fp) != 0) {
    return inject_io_err_inner(net, new_port(NUM, new_i24(ferror(fp))));
  }

  FILE_POINTERS[get_u24(get_val(argm))] = NULL;

  return inject_ok(net, new_port(ERA, 0));
}

// Writes a list of bytes to a file.
// `argm` is a tuple (CON node) of the
// file descriptor and list of bytes to write.
// Returns: Result<*, IOError<i24>>
Port io_write(Net* net, Book* book, Port argm) {
  Tup tup = readback_tup(net, book, argm, 2);
  if (tup.elem_len != 2) {
    return inject_io_err_type(net);
  }

  FILE* fp = readback_file(tup.elem_buf[0]);
  Bytes bytes = readback_bytes(net, book, tup.elem_buf[1]);

  if (fp == NULL) {
    free(bytes.buf);

    return inject_io_err_inner(net, new_port(NUM, new_i24(EBADF)));
  }

  if (fwrite(bytes.buf, sizeof(char), bytes.len, fp) != bytes.len) {
    free(bytes.buf);

    return inject_io_err_inner(net, new_port(NUM, new_i24(ferror(fp))));
  }

  free(bytes.buf);

  return inject_ok(net, new_port(ERA, 0));
}

// Flushes an output stream.
// Returns: Result<*, IOError<i24>>
Port io_flush(Net* net, Book* book, Port argm) {
  FILE* fp = readback_file(argm);
  if (fp == NULL) {
    return inject_io_err_inner(net, new_port(NUM, new_i24(EBADF)));
  }

  if (fflush(fp) != 0) {
    return inject_io_err_inner(net, new_port(NUM, new_i24(ferror(fp))));
  }

  return inject_ok(net, new_port(ERA, 0));
}

// Seeks to a position in a file.
// `argm` is a 3-tuple (CON fd (CON offset whence)), where
// - fd is a file descriptor
// - offset is a signed byte offset
// - whence is what that offset is relative to:
//    - 0 (SEEK_SET): beginning of file
//    - 1 (SEEK_CUR): current position of the file pointer
//    - 2 (SEEK_END): end of the file
// Returns: Result<*, IOError<i24>>
Port io_seek(Net* net, Book* book, Port argm) {
  Tup tup = readback_tup(net, book, argm, 3);
  if (tup.elem_len != 3) {
    return inject_io_err_type(net);
  }

  FILE* fp = readback_file(tup.elem_buf[0]);
  i32 offset = get_i24(get_val(tup.elem_buf[1]));
  u32 whence = get_i24(get_val(tup.elem_buf[2]));

  if (fp == NULL) {
    return inject_io_err_inner(net, new_port(NUM, new_i24(EBADF)));
  }

  int cwhence;
  switch (whence) {
    case 0: cwhence = SEEK_SET; break;
    case 1: cwhence = SEEK_CUR; break;
    case 2: cwhence = SEEK_END; break;
    default:
      return inject_io_err_type(net);
  }

  if (fseek(fp, offset, cwhence) != 0) {
    return inject_io_err_inner(net, new_port(NUM, new_i24(ferror(fp))));
  }

  return inject_ok(net, new_port(ERA, 0));
}

// Returns the current time as a tuple of the high
// and low 24 bits of a 48-bit nanosecond timestamp.
// Returns: Result<(u24, u24), IOError<*>>
Port io_get_time(Net* net, Book* book, Port argm) {
  // Get the current time in nanoseconds
  u64 time_ns = time64();
  // Encode the time as a 64-bit unsigned integer
  u32 time_hi = (u32)(time_ns >> 24) & 0xFFFFFFF;
  u32 time_lo = (u32)(time_ns & 0xFFFFFFF);
  // Allocate a node to store the time
  u32 lps = 0;
  u32 loc = node_alloc_1(net, tm[0], &lps);
  node_create(net, loc, new_pair(new_port(NUM, new_u24(time_hi)), new_port(NUM, new_u24(time_lo))));

  return inject_ok(net, new_port(CON, loc));
}

// Sleeps.
// `argm` is a tuple (CON node) of the high and low
// 24 bits for a 48-bit duration in nanoseconds.
// Returns: Result<*, IOError<*>>
Port io_sleep(Net* net, Book* book, Port argm) {
  Tup tup = readback_tup(net, book, argm, 2);
  if (tup.elem_len != 2) {
    return inject_io_err_type(net);
  }

  // Get the sleep duration node
  Pair dur_node = node_load(net, get_val(argm));
  // Get the high and low 24-bit parts of the duration
  u32 dur_hi = get_u24(get_val(tup.elem_buf[0]));
  u32 dur_lo = get_u24(get_val(tup.elem_buf[1]));
  // Combine into a 48-bit duration in nanoseconds
  u64 dur_ns = (((u64)dur_hi) << 24) | dur_lo;
  // Sleep for the specified duration
  struct timespec ts;
  ts.tv_sec = dur_ns / 1000000000;
  ts.tv_nsec = dur_ns % 1000000000;
  nanosleep(&ts, NULL);

  return inject_ok(net, new_port(ERA, 0));
}

// Opens a dylib at the provided path.
// `argm` is a tuple of `filename` and `lazy`.
// `filename` is a λ-encoded string.
// `lazy` is a `bool` indicating if functions should be lazily loaded.
// Returns: Result<Dylib, IOError<String>>
Port io_dl_open(Net* net, Book* book, Port argm) {
  Tup tup = readback_tup(net, book, argm, 2);
  Str str = readback_str(net, book, tup.elem_buf[0]);
  u32 lazy = get_u24(get_val(tup.elem_buf[1]));

  int flags = lazy ? RTLD_LAZY : RTLD_NOW;

  for (u32 dl = 0; dl < sizeof(DYLIBS); dl++) {
    if (DYLIBS[dl] == NULL) {
      DYLIBS[dl] = dlopen(str.buf, flags);

      free(str.buf);

      if (DYLIBS[dl] == NULL) {
        return inject_io_err_str(net, dlerror());
      }

      return inject_ok(net, new_port(NUM, new_u24(dl)));
    }
  }

  return inject_io_err_str(net, "too many open dylibs");
}

// Calls a function from a loaded dylib.
// `argm` is a 3-tuple of `dylib_handle`, `symbol`, `args`.
// `dylib_handle` is the numeric node returned from a `DL_OPEN` call.
// `symbol` is a λ-encoded string of the symbol name.
// `args` is the argument to be provided to the dylib symbol.
//
// This function returns a Result with an Ok variant containing an
// arbitrary type.
//
// Returns Result<T, IOError<String>>
Port io_dl_call(Net* net, Book* book, Port argm) {
  Tup tup = readback_tup(net, book, argm, 3);
  if (tup.elem_len != 3) {
    return inject_io_err_type(net);
  }

  void* dl = readback_dylib(tup.elem_buf[0]);
  Str symbol = readback_str(net, book, tup.elem_buf[1]);

  dlerror();
  Port (*func)(Net*, Book*, Port) = dlsym(dl, symbol.buf);
  char* error = dlerror();
  if (error != NULL) {
    return inject_io_err_str(net, error);
  }

  return inject_ok(net, func(net, book, tup.elem_buf[2]));
}

// Closes a loaded dylib, reclaiming the handle.
//
// Returns:  Result<*, IOError<String>>
Port io_dl_close(Net* net, Book* book, Port argm) {
  void* dl = readback_dylib(argm);
  if (dl == NULL) {
    return inject_io_err_type(net);
  }

  int err = dlclose(dl) != 0;
  if (err != 0) {
    return inject_io_err_str(net, dlerror());
  }

  DYLIBS[get_u24(get_val(argm))] = NULL;

  return inject_ok(net, new_port(ERA, 0));
}

// Book Loader
// -----------

void book_init(Book* book) {
  book->ffns_buf[book->ffns_len++] = (FFn){"READ", io_read};
  book->ffns_buf[book->ffns_len++] = (FFn){"OPEN", io_open};
  book->ffns_buf[book->ffns_len++] = (FFn){"CLOSE", io_close};
  book->ffns_buf[book->ffns_len++] = (FFn){"FLUSH", io_flush};
  book->ffns_buf[book->ffns_len++] = (FFn){"WRITE", io_write};
  book->ffns_buf[book->ffns_len++] = (FFn){"SEEK", io_seek};
  book->ffns_buf[book->ffns_len++] = (FFn){"GET_TIME", io_get_time};
  book->ffns_buf[book->ffns_len++] = (FFn){"SLEEP", io_sleep};
  book->ffns_buf[book->ffns_len++] = (FFn){"DL_OPEN", io_dl_open};
  book->ffns_buf[book->ffns_len++] = (FFn){"DL_CALL", io_dl_call};
  book->ffns_buf[book->ffns_len++] = (FFn){"DL_CLOSE", io_dl_open};
}

// Monadic IO Evaluator
// ---------------------

// Runs an IO computation.
void do_run_io(Net* net, Book* book, Port port) {
  book_init(book);

  setlinebuf(stdout);
  setlinebuf(stderr);

  // IO loop
  while (true) {
    // Normalizes the net
    normalize(net, book);

    // Reads the λ-Encoded Ctr
    Ctr ctr = readback_ctr(net, book, peek(net, port));

    // Checks if IO Magic Number is a CON
    if (ctr.args_len < 1 || get_tag(ctr.args_buf[0]) != CON) {
      break;
    }

    // Checks the IO Magic Number
    Pair io_magic = node_load(net, get_val(ctr.args_buf[0]));
    //printf("%08x %08x\n", get_u24(get_val(get_fst(io_magic))), get_u24(get_val(get_snd(io_magic))));
    if (get_val(get_fst(io_magic)) != new_u24(IO_MAGIC_0) || get_val(get_snd(io_magic)) != new_u24(IO_MAGIC_1)) {
      break;
    }

    switch (ctr.tag) {
      case IO_CALL: {
        if (ctr.args_len != 4) {
          fprintf(stderr, "invalid IO_CALL: args_len = %u\n", ctr.args_len);
          break;
        }

        Str  func = readback_str(net, book, ctr.args_buf[1]);
        FFn* ffn  = NULL;
        // FIXME: optimize this linear search
        for (u32 fid = 0; fid < book->ffns_len; ++fid) {
          if (strcmp(func.buf, book->ffns_buf[fid].name) == 0) {
            ffn = &book->ffns_buf[fid];
            break;
          }
        }

        free(func.buf);

        Port argm = ctr.args_buf[2];
        Port cont = ctr.args_buf[3];

        Port ret;
        if (ffn == NULL) {
          ret = inject_io_err_name(net);
        } else {
          ret = ffn->func(net, book, argm);
        };

        u32 lps = 0;
        u32 loc = node_alloc_1(net, tm[0], &lps);
        node_create(net, loc, new_pair(ret, ROOT));
        boot_redex(net, new_pair(new_port(CON, loc), cont));
        port = ROOT;

        continue;
      }

      case IO_DONE: {
        break;
      }
    }
    break;
  }
}



