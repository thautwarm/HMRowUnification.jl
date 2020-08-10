module HMRowUnification
using MLStyle


const Optional{T} = Union{Some{T}, Nothing}

abstract type RowT end
abstract type HMT end

ImDict = Base.ImmutableDict

@data TVar begin
    Refvar(UInt)
    Genvar(Symbol)
end

@data RowT begin
    RowMono
    RowCons(Symbol, HMT, RowT)
    RowPoly(HMT)
end

# Write your package code here.
@data HMT begin
    Var(TVar)
    Nom(Symbol)
    Fresh(Symbol)
    App(f::HMT, arg::HMT)
    Arrow(from::HMT, to::HMT)
    Tup{N}(NTuple{N, HMT})
    Forall{N}(NTuple{N, Symbol}, HMT)
    Record(RowT)
end


function previsit(f::Function, ctx′, root)
    function visit_t(ctx′, root)
        ctx, root = f(ctx′, root)
        eval_t(node::HMT)::HMT = visit_t(ctx, node)
        eval_row(root::RowT)::RowT =
            @match root begin
                RowMono => RowMono
                RowPoly(t) => RowPoly(eval_t(t))
                RowCons(k, t, row) =>
                    RowCons(k, eval_t(t), eval_row(row))
                
            end
        @match root begin
            Var(_) || Nom(_) || Fresh(_) => root
            App(a, b) => App(eval_t(a), eval_t(b))
            Arrow(a, b) => Arrow(eval_t(a), eval_t(b))
            Tup(xs) => Tup(map(eval_t, xs))
            Forall(ns, t) => Forall(ns, eval_t(t))
            Record(rowt) => Record(eval_row(rowt))
        end
    end
    visit_t(ctx′, root)
end

function visit_check(pred::Function, t::HMT)
    function eval_t(root)
        pred(root) && begin
            eval_row(root::RowT)::Bool =
                @match root begin
                    RowMono => true
                    RowPoly(t) => eval_t(t)
                    RowCons(k, t, row) =>
                        val_t(t) && eval_row(row)
                end
            @match root begin
                Var(_) || Nom(_) || Fresh(_) => true
                App(a, b) || Arrow(a, b) => eval_t(a) && eval_t(b)
                Tup(xs) => all(eval_t, xs)
                Forall(ns, t) => eval_t(t)
                Record(rowt) => eval_row(rowt)
            end
        end
    end
    eval_t(t)
end

struct IllFormedType <: Exception
    msg :: String
end

struct UnboundTypeVar <: Exception
    msg :: String
end

struct RowFieldMismatch <: Exception
    field :: Symbol
end

struct RowFieldDuplicate <: Exception
    field :: Symbol
end

function mk_tcstate(tctx :: Vector{HMT})
  function fresh_visit(freshmap::ImDict{Symbol, HMT}, a::HMT)
    @match a begin
      Fresh(s) =>
        (freshmap, get(freshmap, s, a))
      Forall(ns, _) =>
        (ImDict(n=>t for (n, t) in freshmap if !(n in ns)), a)
      _ => freshmap, a
    end
  end
  function fresh(freshmap::ImDict{Symbol, HMT}, a::HMT)
    previsit(fresh_visit, freshmap, a)
  end

  function tvar_of_int(i::Integer)
    Var(Refvar(i))
  end
  function new_tvar()::HMT
    vid = length(tctx)
    tvar = tvar_of_int(vid)
    push!(tctx, tvar)
    tvar
  end

  function int_of_tvar(x::Var) :: Optional{UInt}
    @match x begin
        Var(Refvar(i)) => Some(i)
        _ => Nothing
    end
  end

  function occur_in(i::Refvar, ty::HMT)
    @switch ty begin
    @case Var(Genvar(_))
        return false
    @case Var(i′) && if i′ === i end
        return false
    @case _
        visit_func(x) =
            @match x begin
                Var(i′) && if i′ === i end => false
                _ => true
            end
        return !visit_check(visit_func, ty)
    end  
  end

  function prune(x)
    function vfunc(::Nothing, a::HMT)
        nothing, @match a begin
            Var(Refvar(i)) =>
                @match tctx[i] begin
                    Var(Refvar(i′)) &&
                    if i′ === i end => a
                    
                    a =>
                    let t = prune(a)
                        tctx[i] = t
                        t
                    end
                end
            _ => a
        end
    end
    previsit(vfunc, nothing, a)
  end

  function extract_row(rowt::RowT)
    function extract_row(fields::ImDict{Symbol, HMT}, rowt::RowT)
      @match rowt begin
        RowCons(k, _, _) && if haskey(fields, k) end =>
            throw(RowFieldDuplicate(k))
        RowCons(k, v, rowt) =>
            let fields = ImDict(fields..., k => v)
                extract_row(fields, rowt)
            end
        RowMono => (fields, nothing)
        RowPoly(Record(rowt)) =>
            extract_row(fields, rowt)
        RowPoly(t) => (fields, Some(t))
      end
    end
    function extract(x)
        extract_row(ImDict{Symbol, HMT}(), x)
    end
  end

  function unify(lhs, rhs)
    @match prune(lhs), prune(rhs)
        (Nom(a), Nom(b)) => a::Symbol === b::Symbol
        (Forall(ns1, p1), Forall(ns2, p2)) =>
            begin
                subst1 = ImDict(
                    a => new_tvar()    
                    for a in ns1
                )
                subst2 = ImDict(
                    a => Var(Genvar(a))
                    for a in ns2
                )
                unify(fresh(subst1, p1), fresh(subst2, p2)) &&
                all(subst1) do (k, v)
                    @match v begin
                        
                    end
                end
            end


    end

  end
end