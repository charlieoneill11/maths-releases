"""Decide the Z7 x F3^2 quotient emitted by klein_seven.cpp."""
import argparse
from pathlib import Path

import numpy as np

from product_join import meet_spectra


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("rows",type=Path)
    parser.add_argument("library",type=Path)
    args=parser.parse_args()
    data=np.fromfile(args.rows,dtype=np.int32).reshape(-1,36)
    dc=data[:,17:20]
    spectrum=np.concatenate([dc,data[:,20:]],axis=1)
    paf=np.zeros((4,4),dtype=np.int32)
    paf[:,0]=4792
    paf[0]-=4*9*19
    target=np.r_[np.full(3,4792),paf.ravel()]
    result=meet_spectra(data[:,:16],spectrum,dc,target,args.library)
    if result is not None:
        print("a surviving quotient has site values",result.tolist())
        raise SystemExit(1)


if __name__=="__main__":
    main()
