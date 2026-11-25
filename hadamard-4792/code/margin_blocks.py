"""Recover compact K-block lists directly from the two sets of allowed row types."""
import ctypes as ct
from itertools import product
from pathlib import Path

import numpy as np


class MarginBlocks:
    def __init__(self,path,labels):
        lib=self.lib=ct.CDLL(str(Path(path).resolve()))
        ptr=ct.c_void_p
        lib.build_margin_tables.argtypes=[ptr]
        lib.build_margin_tables.restype=ptr
        lib.free_margin_tables.argtypes=[ptr]
        lib.free_margin_tables.restype=None
        lib.free_block_words.argtypes=[ptr]
        lib.free_block_words.restype=None
        lib.margin_blocks.argtypes=[ptr,ptr,ct.c_int,ptr,ct.c_int,ptr,ct.c_int,ct.POINTER(ptr)]
        lib.margin_blocks.restype=ct.c_int64
        self.handle=lib.build_margin_tables(np.ascontiguousarray(labels,dtype=np.int16).ctypes.data)
        if not self.handle:
            raise RuntimeError("failed to create half-block tables")
        reps=[np.flatnonzero(labels.ravel()==i)[0] for i in range(17)]
        i,j=np.unravel_index(reps,(7,19))
        self.perms=[]
        for units in ([(6,18)],product(range(1,7),range(1,19))):
            images=[labels[(a*i)%7,(b*j)%19].tolist() for a,b in units]
            self.perms.append(np.array(sorted(set(map(tuple,images))),dtype=np.int16))

    def close(self):
        self.lib.free_margin_tables(self.handle)

    def generate(self,allowed,normalize_all):
        tables=[]
        for keys in allowed:
            ordered={o for a,b,c in keys for o in ((a,b,c),(a,c,b))}
            tables.append(np.array(sorted(ordered),dtype=np.int32).reshape(-1,3))
        a,b=tables
        perms=self.perms[int(normalize_all)]
        out=ct.c_void_p()
        count=self.lib.margin_blocks(self.handle,a.ctypes.data,len(a),b.ctypes.data,len(b),
                                     perms.ctypes.data,len(perms),ct.byref(out))
        if count<0:
            raise RuntimeError("failed to enumerate constrained K-blocks")
        try:
            words=np.ctypeslib.as_array(ct.cast(out,ct.POINTER(ct.c_uint64)),shape=(count,))
            shifts=3*np.arange(16,-1,-1,dtype=np.uint64)
            alphabet=np.array([-9,-7,-1,1,7,9],dtype=np.int8)
            decoded=np.empty((count,17),dtype=np.int8)
            for i in range(0,count,100000):
                decoded[i:i+100000]=alphabet[(words[i:i+100000,None]>>shifts)&7]
            return decoded
        finally:
            self.lib.free_block_words(out)
