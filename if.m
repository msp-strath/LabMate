if r == c
  A(r,c) = 2;
elseif abs(r-c) == 1
  A(r,c) = -1;
else
  A(r,c) = 0;
end
