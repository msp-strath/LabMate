%> A :: [ i <- 9,  j <- 5 ] (if j == 0 then Q T else Q 1)
A = [ t1 1 -1 0 0
      t2 1 -1 0 0
      t3 1 -1 0 0
      t4 1 -1 0 0
      t5 1 -1 0 0
      t6 0 0 1 -1
      t7 0 0 1 -1
      t8 0 0 1 -1
      t9 0 0 1 -1 ]

%> B :: [ Q TODO; Q TODO; Q TODO; Q TODO; Q TODO; Q TODO ]
B = [ m; c; a; cOffset; aOffset ]

C = A * B

%> typeof C
%< C :: [ 5 x 1 ] (Q (ML^2T^(-3)I^(-1)))
