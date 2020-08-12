# HMRowUnification

[![Stable](https://img.shields.io/badge/docs-stable-blue.svg)](https://thautwarm.github.io/HMRowUnification.jl/stable)
[![Dev](https://img.shields.io/badge/docs-dev-blue.svg)](https://thautwarm.github.io/HMRowUnification.jl/dev)
[![Build Status](https://travis-ci.com/thautwarm/HMRowUnification.jl.svg?branch=master)](https://travis-ci.com/thautwarm/HMRowUnification.jl)
[![Coverage](https://codecov.io/gh/thautwarm/HMRowUnification.jl/branch/master/graph/badge.svg)](https://codecov.io/gh/thautwarm/HMRowUnification.jl)

<p align="center">
<img width="250px" src="https://raw.githubusercontent.com/thautwarm/HMRowUnification.jl/master/fig.png"/>
</p>

# Usage

```julia
using HMRowUnification

tctx = HMT[]

st = mk_tcstate(tctx);

tvar1 = st.new_tvar()
tvar2 = st.new_tvar()
int_t = Nom(:int)


# int -> int ~ 'tvar1 -> 'tvar2
# =>
# 'tvar1 = int
# 'tvar2 = int
st.unify(Arrow(int_t, int_t), Arrow(tvar1, tvar2))
# true

st.prune.([tvar1, tvar1])
# 2-element Array{Nom,1}:
# int
# int

tv3 = st.new_tvar()
tv4 = st.new_tvar()

# rec1 ~ {a : int, b : int | 'tv3}
rec1 = row_of_pairs(
    Dict(:a => int_t, :b => int_t),
    RowPoly(tv3)
)
# rec2 ~ {a : int, c : int | 'tv4}
rec2 = row_of_pairs(
    Dict(:a => int_t, :c => int_t),
    RowPoly(tv4)
)

st.unify(Record(rec1), Record(rec2))
# true
println(st.prune(tv3), "  ", st.prune(tv4))
# {c::int|'5}  {b::int|'5}
```

# Type Representation

```julia
@data TVar begin
    Refvar(i::UInt)
    Genvar(g::UInt, n::Symbol)
end

@data RowT begin
    RowMono
    RowCons(Symbol, HMT, RowT)
    RowPoly(HMT)
end

@data HMT begin
    Var(var::TVar)
    Nom(n::Symbol)
    Fresh(Symbol)
    App(f::HMT, arg::HMT)
    Arrow(from::HMT, to::HMT)
    Tup{N}::(NTuple{N,HMT}) => HMT
    Forall{N}::(NTuple{N,Symbol}, HMT) => HMT
    Record(RowT)
end
```