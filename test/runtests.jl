using HMRowUnification
using MLStyle
using Test


@testset "HMRowUnification.jl" begin
    # Write your tests here.

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
    @test st.unify(Arrow(int_t, int_t), Arrow(tvar1, tvar2))

# true

    @test st.prune.([tvar1, tvar1]) == [int_t, int_t]
# 2-element Array{Nom,1}:
# Nom(:int)
# Nom(:int)

    tv3 = st.new_tvar()
    tv4 = st.new_tvar()

    rec1 = row_of_pairs(
    Dict(:a => int_t, :b => int_t),
    RowPoly(tv3)
)
    rec2 = row_of_pairs(
    Dict(:a => int_t, :c => int_t),
    RowPoly(tv4)
)

    @test Set([st.int_of_tvar(tv4).value]) == ftv(Record(rec2))

    @test st.unify(Record(rec1), Record(rec2))
    println(st.prune(tv3), "  ", st.prune(tv4))
    # @test @match st.prune(tv3), st.prune(tv4) begin
    #     (Record(rec1), Record(rec2)) =>
    #         begin
    #             m1, rowt′ = st.extract_row(rec1)
    #             m2, rowt = st.extract_row(rec2)
    #             @test m1 == m2
    #             sort(collect(m1)) == sort([
    #                 :a => int_t,
    #                 :b => int_t,
    #                 :c => int_t
    #             ])
    #         end
    # end

    
    t1 = Forall((:a, :b), App(Fresh(:b), Fresh(:a)))
    t2 = Forall((:b, :a), App(Fresh(:b), Fresh(:a)))

    @test st.unify(t1, t2)

    t3 = Forall((:b, :a), App(Fresh(:a), Fresh(:b)))

    @test st.unify(t1, t3)

    println(t3)
    println(Genvar(0, :a))
    println(rec2)
    @test repr(Record(RowMono)) == "{}"

    tv5 = st.new_tvar()
    arrow_t = Arrow(int_t, Tup((int_t, tv5)))
    tv6 = st.new_tvar()
    @test st.unify(Arrow(tv6, Tup((tv5, tv6))), arrow_t)
    @test st.prune(tv5) == st.prune(tv6) == int_t
    println(st.prune(arrow_t))
    
    t4 = Forall((:b, :a), App(Fresh(:a), Fresh(:a)))
    @test !(st.unify(t1, t4))

    @test isempty(ftv(t4))
    @test st.unify(st.new_tvar(), Fresh(:a))

    @test int_t ⪯ Forall((:a, ), Fresh(:a))
    @test int_t ⪯ int_t
    @test Arrow(int_t, int_t) ⪯ Forall((:a, ), Arrow(Fresh(:a), Fresh(:a)))
    @test Arrow(
            Forall((:a, ), 
                Arrow(Fresh(:a), Fresh(:a))),
            int_t) ⪯ 
            Arrow(Arrow(int_t, int_t), int_t)
    tv = st.new_tvar()
    @test Tup((int_t, int_t)) ⪯ Forall((:a, ), Tup((Fresh(:a), Fresh(:a))))
    @test st.unify(Fresh(:a), Fresh(:a))
    @test Fresh(:a) ⪯ Fresh(:a)
    println(st.instantiate(t4))
    @test isempty(unbound(t4))
    @test collect(unbound(Tup((int_t,  Fresh(:a))))) == [:a]

end
