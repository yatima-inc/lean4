/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstddef>
#include "runtime/thread.h"
#include "runtime/debug.h"

#define LEAN_SEGMENT_SIZE          8*1024*1024 // 8 Mb
#define LEAN_PAGE_SIZE             8192        // 8 Kb
#define LEAN_OBJECT_SIZE_DELTA     32
#define LEAN_MAX_SMALL_OBJECT_SIZE 512
#define LEAN_NUM_SLOTS             (LEAN_MAX_SMALL_OBJECT_SIZE / LEAN_OBJECT_SIZE_DELTA)
#define LEAN_MAX_TO_EXPORT_OBJS    1024

namespace lean {
namespace allocator {
#ifdef LEAN_RUNTIME_STATS
static atomic<uint64> g_num_alloc(0);
static atomic<uint64> g_num_small_alloc(0);
static atomic<uint64> g_num_dealloc(0);
static atomic<uint64> g_num_small_dealloc(0);
#endif

struct segment;
struct page;
struct heap {
    segment * m_curr_segment{nullptr};
    heap *    m_next_orphan{nullptr};
    page *    m_curr_page[LEAN_NUM_SLOTS];
    page *    m_page_free_list[LEAN_NUM_SLOTS];
    /* Objects that must be sent to other heaps. */
    void *    m_to_export_list{nullptr};
    unsigned  m_to_export_list_size{0};
    mutex     m_mutex; /* for the following fields */
    /* The following list contains object by this heap that were deallocated
       by other heaps. */
    void *    m_to_import_list{nullptr};
    void import_objs();
    void export_objs();
    void alloc_segment();
};

struct page_header {
    atomic<heap *>   m_heap;
    page *           m_next;
    page *           m_prev;
    void *           m_free_list;
    unsigned         m_max_free;
    unsigned         m_num_free;
    unsigned         m_slot_idx;
    bool             m_in_page_free_list;
};

struct page {
    page_header m_header;
    char        m_data[LEAN_PAGE_SIZE - sizeof(page_header)];
    page * get_next() const { return m_header.m_next; }
    page * get_prev() const { return m_header.m_prev; }
    void set_next(page * n) { m_header.m_next = n; }
    void set_prev(page * p) { m_header.m_prev = p; }
    void set_heap(heap * h) { m_header.m_heap = h; }
    heap * get_heap() { return m_header.m_heap; }
    bool has_many_free() const { return m_header.m_num_free > m_header.m_max_free / 4; }
    bool in_page_free_list() const { return m_header.m_in_page_free_list; }
    unsigned get_slot_idx() const { return m_header.m_slot_idx; }
    void push_free_obj(void * o);
};

LEAN_THREAD_EXTERN_PTR(heap, g_heap);

inline size_t align(size_t v, size_t a) {
    return (v / a)*a + a * (v % a != 0);
}

inline char * align_ptr(char * p, size_t a) {
    return reinterpret_cast<char*>(align(reinterpret_cast<size_t>(p), a));
}

inline unsigned get_slot_idx(unsigned obj_size) {
    lean_assert(obj_size > 0);
    lean_assert(align(obj_size, LEAN_OBJECT_SIZE_DELTA) == obj_size);
    return obj_size / LEAN_OBJECT_SIZE_DELTA - 1;
}

inline void set_next_obj(void * obj, void * next) {
    *reinterpret_cast<void**>(obj) = next;
}

inline void * get_next_obj(void * obj) {
    return *reinterpret_cast<void**>(obj);
}
}

void init_thread_heap();
void * alloc(size_t sz);
void dealloc(void * o, size_t sz);
void * small_alloc_slow(size_t sz, unsigned slot_idx);
void * big_alloc(size_t sz);
inline void * small_alloc(size_t sz) {
    sz = allocator::align(sz, LEAN_OBJECT_SIZE_DELTA);
    if (sz <= LEAN_MAX_SMALL_OBJECT_SIZE) {
        lean_assert(allocator::g_heap);
        unsigned slot_idx = allocator::get_slot_idx(sz);
        allocator::page * p = allocator::g_heap->m_curr_page[slot_idx];
        void * r = p->m_header.m_free_list;
        if (r != nullptr) {
            p->m_header.m_free_list = allocator::get_next_obj(r);
            p->m_header.m_num_free--;
            return r;
        }
        return small_alloc_slow(sz, slot_idx);
    } else {
        return big_alloc(sz);
    }
}
void initialize_alloc();
void finalize_alloc();
}
