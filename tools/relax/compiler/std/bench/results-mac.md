| bench | A ms | B ms | C ms | B/A | C/B | checksums equal |
|---|---:|---:|---:|---:|---:|---|
| hashmap_u64_insert_get | 66.84 | 63.13 | 123.33 | 0.94 | 1.95 | yes |
| hashmap_liveid | 75.22 | 213.23 | 302.42 | 2.83 | 1.42 | yes |
| hashmap_fx | 70.02 | 178.23 | 297.23 | 2.55 | 1.67 | yes |
| hashset_string (B=real) | 86.97 | 85.70 | 231.32 | 0.99 | 2.70 | yes |
| hashmap_remove_churn | 54.62 | 49.03 | 96.07 | 0.90 | 1.96 | yes |
| vec_push | 92.32 | 44.01 | 243.66 | 0.48 | 5.54 | yes |
| vec_extend_from_slice | 90.95 | 93.63 | 655.42 | 1.03 | 7.00 | yes |
| sort_u64_random | 75.40 | 188.06 | 471.60 | 2.49 | 2.51 | yes |
| sort_unstable_u64_random | 77.47 | 317.57 | 549.15 | 4.10 | 1.73 | yes |
| sort_by_key_struct | 76.31 | 202.28 | 572.16 | 2.65 | 2.83 | yes |
| sort_sorted_and_reversed | 78.53 | 308.14 | 715.96 | 3.92 | 2.32 | yes |
| dedup_binary_search | 80.61 | 107.13 | 477.83 | 1.33 | 4.46 | yes |
| string_push_str | 90.74 | 94.01 | 136.88 | 1.04 | 1.46 | yes |
| format_ints | 64.00 | 61.31 | 168.69 | 0.96 | 2.75 | yes |
| format_floats | 105.42 | 229.55 | 924.28 | 2.18 | 4.03 | yes |
| write_to_string | 87.19 | 86.58 | 202.88 | 0.99 | 2.34 | yes |
| str_find | 156.19 | 904.33 | 1282.42 | 5.79 | 1.42 | yes |
| str_split_lines | 107.72 | 70.66 | 123.03 | 0.66 | 1.74 | yes |
| parse_ints | 80.77 | 98.70 | 1114.69 | 1.22 | 11.29 | yes |
| parse_floats | 70.16 | 18966.54 | 33205.30 | 270.33 | 1.75 | yes |
| rc_refcell_churn (B=real) | 78.51 | 78.48 | 426.71 | 1.00 | 5.44 | yes |
| btreemap_insert_range | 138.16 | 444.20 | 890.81 | 3.22 | 2.01 | yes |
| iter_chain | 79.24 | 79.58 | 820.80 | 1.00 | 10.31 | yes |
| mpsc_ping | 86.36 | 2626.62 | 3396.30 | 30.41 | 1.29 | yes |

Milliseconds per fixed batch: one warm-up batch, best of five batches. Includes input construction, allocation, checksumming and destruction. All columns use identical batch counts. B uses host iterator traits and thread spawning with Relax mpsc. Default hashers intentionally differ.

Batch counts: hashmap_u64_insert_get=1, hashmap_liveid=3, hashmap_fx=3, hashset_string=3, hashmap_remove_churn=1, vec_push=6, vec_extend_from_slice=24, sort_u64_random=2, sort_unstable_u64_random=3, sort_by_key_struct=2, sort_sorted_and_reversed=7, dedup_binary_search=5, string_push_str=3, format_ints=1, format_floats=1, write_to_string=3, str_find=1, str_split_lines=1, parse_ints=5, parse_floats=6, rc_refcell_churn=8, btreemap_insert_range=1, iter_chain=16, mpsc_ping=10.

B=real fallbacks: hashset_string: shim String lacks the host Hash implementation; rc_refcell_churn: optimized shim panics: RefCell already borrowed; its UnsafeCell is not the rustc interior-mutability lang item.

Environment: macOS-26.5.2-arm64-arm-64bit-Mach-O; rustc 1.98.0 (88d9e12ae 2026-08-18). Binary/source hashes and batch counts: logs-mac/metadata.json.

Sandbox limitation: nice -n 10 was invoked, but setpriority was denied; the measured processes ran at the inherited priority.

Execution failures: none.

Concurrent checkout activity: another process committed changes during this run, including additive Box/Rc/Arc uninitialized-allocation APIs. The harness sources and Relax release binary remained unchanged (hashes verified). These results are not from an isolated checkout.
