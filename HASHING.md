# Hashing in `lang`

This document describes the current hashing strategy used by the interpreter, with a focus on dictionaries.

## Terminology / data model

`lang` values are represented by a tagged 64-bit word `Q` (see `l.c`). A `Q` is either:

- **Immediate** (tagged atom): payload lives in the low bits / shifted form.
- **Pointer**: points to a heap object with a 6-word header: `(type;shape;log_elt_sz;refcnt;len;cap)` followed by payload.

“Structural equality” is implemented by the match verb `~` (see `match_struct` / `mt` in `l.c`). Dictionaries use the same structural comparator for key equality.

## Structural hash (`qhash64`)

The dictionary subsystem uses a **structural 64-bit hash** for keys:

- The hash includes **type**, **shape**, **element size**, and **length** metadata.
- Atoms hash their **payload** (immediates and heap-atoms hash the same payload).
- Homogeneous value vectors hash the raw bytes of the payload.
- Pointer lists (type `0`, and type `4` partial-eval chains) hash recursively in order.
- Dictionaries hash structurally but **ignore the internal hash table** (they hash only keys and values).

Cycle handling: `qhash64` has a small pointer stack used for cycle detection; if a cycle is detected, hashing falls back to mixing the pointer value (so hashing terminates even for cyclic graphs).

## Dictionary representation

A dictionary is a shape-2 object (a fixed 3-list) with:

1. `ht`: hash table (type `5`) — a vector of 64-bit entries
2. `keys`: key vector (type `0` pointer list)
3. `vals`: value vector (type `t(vals)`, possibly `0` for boxed values)

Important notes:

- `ht` is type `5` on purpose: the generic vector growth path refuses to auto-grow type `5` objects. Resizing a dictionary requires a full rehash, not a memcpy resize.
- The `ht` header’s `len` field is used as **used-entry count**; the `cap` field is the bucket array length.

## Hash table entries (“fingerprint” packing)

Each `ht` slot stores a single 64-bit entry:

- `0` means **empty**
- otherwise: `entry = (fp32 << 32) | (idx1)`
  - `fp32`: the top 32 bits of the key’s structural hash (`qhash64(key) >> 32`)
  - `idx1`: 1-based index into `keys`/`vals` (so `idx = idx1 - 1`)

This is a “hash fingerprint” optimization: most probes can be rejected by comparing `fp32` without doing an expensive structural compare.

## Lookup / insert algorithm (open addressing)

The table uses:

- **power-of-two** capacity
- **linear probing**

### Find slot (`fk_h`)

Given `(ht, key, hash64, cap, keys)`:

1. Compute `fp32 = hash64 >> 32`
2. Compute initial bucket from the top bits of `hash64`
3. Probe linearly:
   - if slot is empty → return that index
   - if slot’s `fp32` mismatches → continue
   - else compare `match_struct(keys[idx], key)` → if equal, return that index

### Get (`dk` / `dki`)

- Ensures the table is valid via `dict_ensure_ht` (see below).
- Uses `fk_h` to find the slot.
- If non-empty, returns the corresponding value; otherwise returns “not found”.

### Set (`dkv`)

- Ensures the table is valid and large enough (may trigger a rehash/grow).
- Finds the slot:
  - If occupied with the same key → overwrite the value.
  - If empty → append key/value to `keys`/`vals` and write packed `fp32|idx1` into the slot.

## Rehashing / invariants

The interpreter treats the hash table as a **derived cache** from the key list.

`dict_ensure_ht(d, want_keys)` enforces two invariants:

- `used_entries(ht) == n(keys)` (detects stale tables after cloning/loading/transforms)
- `cap(ht)` is large enough to keep load factor ≤ ~0.75 for the desired key count

If either invariant fails, `dict_rehash(d, new_cap)` rebuilds the hash table by scanning `keys` and reinserting indices.

The capacity policy is:

- `cap = pow2_ceil( ceil( (keys+1) / 0.75 ) )`
- with a minimum of 64 buckets

## Why fingerprints help

Without fingerprints, every collision chain step would potentially require:

- deep structural comparisons of keys (recursive walks)

With fingerprints, most mismatched keys are rejected by a single 32-bit compare, and only “likely matches” pay the structural equality cost. Collisions can still cause compares (32-bit fingerprints are not unique), but the expected compare rate is much lower in practice.

## Future considerations

- If/when floats are added, define both `match_struct` and `qhash64` float semantics (NaN, -0.0, etc.) so dictionary key behavior is predictable.
- If symbols move to a symbol table, hashing/equality should use the interned symbol id (fast-path) while preserving structural semantics.
- If you later want faster worst-case probe behavior, consider robin-hood probing, quadratic probing, or storing a 16-bit “group tag” (SwissTable-style). The current scheme intentionally keeps the implementation small.

