%{
> input readFromFile
ivals :
  nlayer : contains the @number of layers (2 or 3) in the sample
  tflash : duration of laser flash in @ms
  cps : specific heat capacities in @J kg^-1 K^-1
      - of the front face
      - of the rear face
      - of the curved side face
  rs : heat transfer coefficient for losses in  @W m^-2 K^-1
      - from front face
      - from rear face
      - curved side face
  kappas : contains radius of
      - sample (in @cm)
      - laser (in @mm)
      - measuring (in @mm)
  lams   : array of thermal conductivities of layer @nlayer (in @W m^-2 K^-1)
%}
