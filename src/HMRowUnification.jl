module HMRowUnification
export HMT, TVar, RowT, mk_tcstate
export Refvar, Genvar
export RowMono, RowCons, RowPoly
export Var, Nom, Fresh, Var, Arrow, App, Tup, Forall, Record
export row_of_pairs, extract_row

using MLStyle

include("Core.jl")
include("TCState.jl")


end