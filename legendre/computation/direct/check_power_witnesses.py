import math,sys
lo,hi=map(int,sys.argv[1:])
expected=lo
for line in sys.stdin:
    n,p=map(int,line.split())
    assert n==expected and n**11<p**5<(n+1)**11
    expected+=1
    f=(p-1)&(1-p)
    assert f**3>p and pow(3,(p-1)//2,p)==p-1
    if (f+1)**2<=p:
        product,add=divmod((p-1)//f,f)
        d=add*add-4*product
        assert d<0 or math.isqrt(d)**2!=d
assert expected==hi+1
print('Independently checked',hi-lo+1,'consecutive strict inequalities and prime certificates')
