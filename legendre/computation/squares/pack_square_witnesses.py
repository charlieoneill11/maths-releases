import gzip,struct,sys

def offset(lower, upper, p):
 f=1<<((upper.bit_length()+2)//3)
 assert (p-1)%f==0
 return (p-1)//f-lower//f

with gzip.GzipFile(sys.argv[1],mode='wb',mtime=0) as out:
 for line in sys.stdin.buffer:
  n,p,q=map(int,line.split())
  m=n*(n+1)
  out.write(struct.pack('<HH',offset(n*n,m,p),offset(m,(n+1)**2,q)))
