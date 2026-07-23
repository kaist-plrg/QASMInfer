let unoptimize_nop instruction = instruction

let unoptimize_I_XX instruction =
  Extracted.function_I_XX instruction 1
