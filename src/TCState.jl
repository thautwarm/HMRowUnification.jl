function extract_row(rowt::RowT)
    function extract_row_(fields::TypeScope, rowt::RowT)
        @match rowt begin
            RowCons(k, _, _) && if haskey(fields, k) end =>
                throw(RowFieldDuplicate(k))
            RowCons(k, v, rowt) =>
                let fields = ImDict(fields, k => v)
                    extract_row_(fields, rowt)
                end
            RowMono => (fields, nothing)
            RowPoly(Record(rowt)) =>
                extract_row_(fields, rowt)
            RowPoly(t) => (fields, Some(t))
        end
    end
    extract_row_(TypeScope(), rowt)
end

function mk_tcstate(tctx::Vector{HMT}, new_tvar_hook::Union{Nothing, Function}=nothing)
    genvars = Genvar[]
    genvar_links = Set{UInt}[]
    
    function new_genvar(s::Symbol)::Var
        genlevel = length(genvars) + 1
        genvar = Genvar(genlevel, s)
        push!(genvars, genvar)
        push!(genvar_links, Set{UInt}())
        Var(genvar)
    end

    function unlink(maxlevel :: Integer)
        while true
            level = length(genvars)
            if level <= maxlevel
                break
            end
            pop!(genvars)
            vars = pop!(genvar_links) :: Set{UInt}
            for typevar_id in vars
                tctx[typevar_id] = Var(Refvar(typevar_id))
            end

        end
    end

    function fresh_visit(freshmap::TypeScope, a::HMT)
        @match a begin
            Fresh(s) => (freshmap, get(freshmap, s, a))
            Forall(ns, _) => (mk_type_scope(Pair{Symbol, HMT}[n => t for (n, t) in freshmap if !(n in ns)]), a)
            _ => (freshmap, a)
        end
    end
    function fresh(freshmap::TypeScope, a::HMT)
        previsit(fresh_visit, freshmap, a)
    end

    function tvar_of_int(i::Integer)
        Var(Refvar(i))
    end
    function new_tvar()::HMT
        vid = UInt(length(tctx) + 1)
        if new_tvar_hook !== nothing
            new_tvar_hook(vid)
        end
        tvar = tvar_of_int(vid)
        push!(tctx, tvar)
        tvar
    end

    function int_of_tvar(x::Var)::Optional{UInt}
        @match x begin
            Var(Refvar(i)) => Some(i)
            _ => Nothing
        end
    end

    function occur_in(i::Refvar, ty::HMT)
        @switch ty begin
            @case Var(Genvar(_, _))
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
        previsit(vfunc, nothing, x)
    end


    function type_less(lhs::HMT, rhs::HMT)
        lhs = prune(lhs)
        rhs = prune(rhs)
        lhs === rhs && return true

        (@match lhs, rhs begin
            (_, Var(_) || Nom(_) || Fresh(_)) => unify(rhs, lhs)
            
            (Forall(ns1, p1), Forall(ns2, p2)) =>
                (begin
                    pt = Pair{Symbol, HMT}
                    subst1 = mk_type_scope(pt[a => new_genvar(a) for a in ns1])
                    subst2 = mk_type_scope(pt[a => new_tvar() for a in ns2])

                    type_less(fresh(subst1, p1), fresh(subst2, p2))
                end)
            (Var(_), _) => unify(lhs, rhs)
            (_, Forall(ns2, p2)) =>
                (begin
                    pt = Pair{Symbol, HMT}
                    subst = mk_type_scope(pt[a => new_tvar() for a in ns2])
                    type_less(lhs, fresh(subst, p2))
                end)
            (Nom(_) || Fresh(_), _) => unify(lhs, rhs)

                
            # A: (forall a. a -> a) -> [int]
            # B: (int -> int) -> [int]
            # A : B
            (Arrow(a1, r1), Arrow(a2, r2)) =>
                type_less(a2, a1) && type_less(r1, r2)

            # A: (forall a. a) int
            # B: list a
            # A : B
            (App(f1, a1), App(f2, a2)) =>
                type_less(f1, f2) && type_less(a1, a2)

            (Tup(xs1), Tup(xs2)) =>
                all(zip(xs1, xs2)) do (lhs, rhs)
                    type_less(lhs, rhs)
                end

            (Record(a), Record(b)) =>
                (begin
                    (m1, ex1) = extract_row(a)
                    (m2, ex2) = extract_row(b)
                    common_keys =
                        intersect(keys(m1), keys(m2))
                    only_by_1 = [k => v for (k, v) in m1 if !(k in common_keys)]
                    only_by_2 = [k => v for (k, v) in m2 if !(k in common_keys)]

                    all(common_keys) do k
                        type_less(m1[k], m2[k])
                    end || return false

                    function row_check(row1, row2, only_by_1, only_by_2)
                        @match row1, row2 begin
                            (nothing, nothing) => isempty(only_by_1) && isempty(only_by_2)
                            (Some(_), nothing) => false
                            (nothing, Some(row2)) => true
                            (Some(row1), Some(row2)) => isempty(only_by_1) && isempty(only_by_2)
                        end
                    end
                    row_check(ex1, ex2, only_by_1, only_by_2)

                end)
            _ => false
        end)
    end

    function unify(lhs::HMT, rhs::HMT)
        lhs = prune(lhs)
        rhs = prune(rhs)
        lhs === rhs && return true

        (@match lhs, rhs begin
            (Forall{N1}(ns1, p1) where N1, Forall{N2}(ns2, p2) where N2) =>
                N1 === N2 &&
                (begin
                    pt = Pair{Symbol, HMT}
                    subst1 = mk_type_scope(pt[a => new_tvar() for a in ns1])
                    subst2 = mk_type_scope(pt[a => new_genvar(a) for a in ns2])
                    unify(fresh(subst1, p1), fresh(subst2, p2)) &&
                    (let check_unique = Set{Genvar}()
                        all(subst1) do kv
                            @switch prune(kv.second) begin
                            @case Var(a::Genvar)
                                push!(check_unique, a)
                                return true
                            @case _
                                return false
                            end
                        end &&
                        length(check_unique) == N1
                    end)
                end)
            (Var(Refvar(i) && ai), b) =>
            if occur_in(ai, b)
                throw(IllFormedType("a = a -> b"))
            else
                @match b begin
                    Genvar(genlevel, _) =>
                        push!(genvar_links[genlevel], i)
                    _ => nothing
                end
                tctx[i] = b
                true
            end
            (Var(Genvar(_, _)), _) => false
            (a, (Var(_) && b)) => unify(b, a)

            (Arrow(a1, r1), Arrow(a2, r2)) =>
                unify(a1, a2) && unify(r1, r2)

            (App(f1, a1), App(f2, a2)) =>
                unify(f1, f2) && unify(a1, a2)

            (Tup(xs1), Tup(xs2)) =>
                all(zip(xs1, xs2)) do (lhs, rhs)
                    unify(lhs, rhs)
                end

            (Record(a), Record(b)) =>
                (begin
                    (m1, ex1) = extract_row(a)
                    (m2, ex2) = extract_row(b)
                    common_keys =
                        intersect(keys(m1), keys(m2))
                    only_by_1 = [k => v for (k, v) in m1 if !(k in common_keys)]
                    only_by_2 = [k => v for (k, v) in m2 if !(k in common_keys)]

                    all(common_keys) do k
                        unify(m1[k], m2[k])
                    end &&
                    (begin
                        function row_check(row1, row2, only_by_1, only_by_2)
                            @match row1, row2 begin
                                (nothing, nothing) => isempty(only_by_1) && isempty(only_by_2)
                                (Some(_), nothing) => row_check(row2, row1, only_by_2, only_by_1)
                                (nothing, Some(row2)) => isempty(only_by_2) &&
                                    unify(row2, Record(row_of_pairs(only_by_1, RowMono)))
                                (Some(row1), Some(row2)) =>
                                    begin
                                        polyrow = RowPoly(new_tvar())
                                        ex2 = Record(row_of_pairs(only_by_1, polyrow))
                                        ex1 = Record(row_of_pairs(only_by_2, polyrow))
                                        unify(row1, ex1) &&
                                            unify(row2, ex2)
                                    end
                            end
                        end
                        row_check(ex1, ex2, only_by_1, only_by_2)
                    end)
                end)
            _ => false
        end)
    end

    function instantiate(hmt::HMT)
        @match hmt begin
            Forall(ns, t) => begin
                pt = Pair{Symbol, HMT}
                subst = mk_type_scope(pt[a => new_tvar() for a in ns])
                fresh(subst, t)
            end
            _ => hmt
        end
    end

    function generalise(genmap::Dict{UInt, Symbol}, hmt::HMT)
        function visitor(@nospecialize(_), hmt::HMT)
            @match hmt begin
                Var(Refvar(i)) =>
                    let x = get(genmap, i, nothing)
                        x === nothing && return hmt
                        nothing, Fresh(x)
                    end
                _ => (nothing, hmt)
            end
        end

        Forall(Tuple(values(genmap)), previsit(visitor, genmap, hmt))
    end



    (unify = unify,
        type_less = type_less,
        tctx = tctx,
        instantiate = instantiate,
        generalise = generalise,
        new_tvar = new_tvar,
        new_genvar = new_genvar,
        genvar_links = genvar_links,
        genvars = genvars,
        unlink = unlink,
        tvar_of_int = tvar_of_int,
        int_of_tvar = int_of_tvar,
        fresh = fresh,
        occur_in = occur_in,
        prune = prune,
        extract_row = extract_row)
end

function subst_tvar_visit(ctx::Function, root::HMT)
    @match root begin
        Var(Refvar(i)) => (ctx, ctx(i))
        Var(Genvar(_, _)) => error("unexpected genvar outside its scope")
        _ => (ctx, root)
    end
end

(lhs::HMT) ⪯ (rhs::HMT)  = begin
   small_tc = mk_tcstate(HMT[])
   subst_table = Dict{UInt, HMT}()
   function subst(i::UInt)
        get!(subst_table, i) do
            small_tc.new_tvar()
        end
   end
   lhs = previsit(subst_tvar_visit, subst, lhs)
   rhs = previsit(subst_tvar_visit, subst, rhs)
   small_tc.type_less(lhs, rhs)
end

