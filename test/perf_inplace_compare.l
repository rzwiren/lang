// Manual performance/alloc comparison for arena-0 in-place numeric ops.
// Prints: (inplace_ns; inplace_ai0_peak_units; fresh_ns; fresh_ai0_peak_units; fresh_vs_inplace_time_ratio)

b0: bench (30;"{[] 1+1+1+1+!1000000 }[]";1)
b1: bench (30;"{[] 1+a:1+a:1+a:1+a:!1000000 }[]";1)

(b0@0; b0@2; b1@0; b1@2; (b1@0)/(b0@0))
