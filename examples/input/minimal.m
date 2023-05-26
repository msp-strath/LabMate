%{
  > input minimal
test :
  field1 : @Int (`field1` has integral type)
  field2 : @Km (`field2` carries unit information)
  array1 : @ms (`array1` is an array with three elements and each is stored in ms)
    - one
    - two
    - three
  array2 : (the first two entries store some lenghts recorded in mm, while the last one - in Km)
    - one in @mm 
    - two in @mm
    - three in @Km
  vec1 : @field1 elements of @mm (`vec1` is an array containing `field1` many entries, each stored in mm)
%}
