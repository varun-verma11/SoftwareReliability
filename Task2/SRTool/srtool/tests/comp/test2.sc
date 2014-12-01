void main()
{

  int a;
  int b;
  int c;
  int d;
  int e;
  int f;

  a=0;
  b=0;
  c=0;
  d=0;
  while(c<100)
  {
    a = a+1;
    b = b+1;
    c = 0;
    while(c<100)
    {
      c = c+1;
    }
  }
  assert(b==c);
  
  e=0;
  f=0;
  while(e<100)
  {
    e = e+1;
    while(f<100)
    {
      f = f+1;
    }
  }
}


