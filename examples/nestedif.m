if a==1 % Front layer
  if (b==0)
    c=[];
  else
    1;
  end
  nz = [n1];
else % Back layer
  if (d==0)
    n2 = nz;
  else
   n1 = 2;
  end
  nz = [];
end
