%{
  > input readFromDisk
myStruct :
  count : @Int (`count` has integral type)
  totalLen : @Km (`len` carries unit information)
  unitLens : @count elements of @m (`unitLens` is an array containing `count` many entries, each stored in m)
%}
