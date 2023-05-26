%{


> input nesting
outer :
  field : simple field @Km
  inner_1 :
    nlayer : contains the @number of layers (2 or 3) in the sample
    inner_nesting :
      another_field : @number
  another_field : @number
  inner_2 :
     array : @inner_1.nlayer in @mm
%}
