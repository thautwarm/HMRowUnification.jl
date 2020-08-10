const Optional{T} = Union{Some{T},Nothing}

abstract type RowT end
abstract type HMT end

ImDict = Base.ImmutableDict

abstract type TVar end
@data TVar begin
    Refvar(i::UInt)
    Genvar(n::Symbol)
end

function Base.show(io::IO, x::TVar)
    @match x begin
        Genvar(n) => print(io, '%', n)
        Refvar(i) => print(io, '\'', i)
    end
end

@data RowT begin
    RowMono
    RowCons(Symbol, HMT, RowT)
    RowPoly(HMT)
end

# Write your package code here.
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

Base.show(io::IO, rowt::RowT) =
    @switch rowt begin
    @case RowMono
        return
    @case RowCons(k, t, r)
        print(io, k, "::")
        Base.show(io, t)
        print(io, " {")
        Base.show(io, r)
        print(io, '}')
        return
    @case RowPoly(t)
        print(io, '|')
        Base.show(io, t)
        return
    end

need_parens(hmt::HMT) =
    @match hmt begin
        ::App || ::Arrow || ::Forall => true
        _ => false
    end

with_parens(f::Function, io::IO, need_parens::Bool) =
    if need_parens
        print(io, '(')
        f()
        print(io, ')')
    else
        f()
    end


Base.show(io::IO, hmt::HMT) =
    @switch hmt begin
    @case Var(v)
        print(io, v)
        return
    @case Nom(n)
        print(io, n)
        return

    @case Fresh(n)
        print(io, n)
        return

    @case App(f, a)
        Base.show(io, f)
        print(io, " ")
        with_parens(io, need_parens(a)) do
            Base.show(io, a)
        end
        return
    @case Arrow(a, r)
        with_parens(io, need_parens(a)) do
            Base.show(io, a)
        end
        print(io, "->")
        Base.show(io, r)
        return
    @case Tup(xs)
        print(io, "{")
        print(io, join(repr.(xs), ", "))
        print(io, "}")
        return 
    @case Forall(ns, t)
        print(io, "forall ")
        print(io, join(string.(ns), " "), ".")
        Base.show(io, t)
        return
    @case Record(rec)
       m, ex = extract_row(rec)
       print(io, '{')
       print(io, join(String["$k::$(repr(v))" for (k, v) in m], ", "))
       @when Some(ex) = ex begin
         Base.show(io, RowPoly(ex))
       end
       print(io, '}')
       return
    end


TypeScope = ImDict{Symbol,HMT}

function mk_type_scope(xs::AbstractVector{Pair{K, V}}) where {K, V}
    ret = ImDict{K, V}()
    for x in xs
        ret = ImDict(ret, x)
    end
    ret
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
            Record(rowt) =>
                @match eval_row(rowt) begin
                    RowPoly(t) => t
                    a => Record(a)
                end
        end
    end
    visit_t(ctx′, root)
end

function row_of_pairs(pairs, row)
    for (k, v) in pairs
        row = RowCons(k, v, row)
    end
    row
end

function visit_check(pred::Function, t::HMT)
    function eval_t(root)
        pred(root) && begin
            eval_row(root::RowT)::Bool =
                @match root begin
                RowMono => true
                RowPoly(t) => eval_t(t)
                RowCons(k, t, row) =>
                        eval_t(t) && eval_row(row)
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
    msg::String
end

struct UnboundTypeVar <: Exception
    msg::String
end

struct RowFieldMismatch <: Exception
    field::Symbol
end

struct RowFieldDuplicate <: Exception
    field::Symbol
end
