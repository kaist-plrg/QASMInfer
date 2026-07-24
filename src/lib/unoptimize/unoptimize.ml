let unoptimize_nop instruction = instruction

let unoptimize instruction =
  let rule = Extracted.transform_spec_list |> List.hd in
  Extracted.transformSpec_apply rule instruction 0
