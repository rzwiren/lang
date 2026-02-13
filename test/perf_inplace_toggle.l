// Run with and without `--no-inplace` to isolate in-place impact on the same expression.
// Prints: (ns; ai0_peak_units; ai0_peak_bytes)

b: bench (30;"{[] 1+1+1+1+!1000000 }[]";1)
(b@0; b@2; b@3)
