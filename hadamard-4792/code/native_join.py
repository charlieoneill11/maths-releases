"""Memory-bounded native counterpart to the NumPy four-list join."""
import ctypes as ct
from pathlib import Path

import numpy as np


class Join:
    def __init__(self, path):
        library=ct.CDLL(str(Path(path).resolve()))
        self.run=library.join4
        self.run.argtypes=[ct.POINTER(ct.c_void_p),ct.c_void_p,ct.c_uint64,ct.c_void_p,ct.c_uint64]
        self.run.restype=ct.c_int64

    def __call__(self, groups, target):
        hashes=[np.ascontiguousarray(g[0],dtype=np.uint64) for g in groups]
        sizes=np.array([len(h) for h in hashes],dtype=np.uint32)
        pointers=(ct.c_void_p*4)(*(h.ctypes.data for h in hashes))
        rows=np.empty((32,4),dtype=np.uint32)
        while True:
            count=self.run(pointers,sizes.ctypes.data,int(target),rows.ctypes.data,len(rows))
            if count<0:
                raise RuntimeError("native pair join failed")
            if count<=len(rows):
                break
            rows=np.empty((count,4),dtype=np.uint32)
        for row in rows[:count]:
            yield [g[1][i] for g,i in zip(groups,row)]
