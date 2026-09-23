#ifndef BUFF_RUNTIME_H
#define BUFF_RUNTIME_H

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct {
    uint8_t* memory;
    size_t offset;
    size_t capacity;
} Arena;

static inline Arena arena_make(size_t capacity) {
    Arena arena = {(uint8_t*)malloc(capacity), 0, capacity};
    return arena;
}

static inline void* arena_alloc(Arena* arena, size_t size) {
    if (!arena->memory) *arena = arena_make(1024 * 1024);
    if (!arena->memory || size > SIZE_MAX - 7u) return NULL;
    size_t aligned = (size + 7u) & ~7u;
    if (arena->offset > arena->capacity || aligned > arena->capacity - arena->offset) return NULL;
    void* result = arena->memory + arena->offset;
    arena->offset += aligned;
    return result;
}

static inline void arena_free(Arena* arena) {
    free(arena->memory);
    arena->memory = NULL;
    arena->offset = 0;
    arena->capacity = 0;
}

static Arena game_arena = {0};

#endif
