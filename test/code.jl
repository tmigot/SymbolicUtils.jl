using Test, SymbolicUtils
using SymbolicUtils.Code
using SymbolicUtils.Code: LazyState

test_repr(a, b) = @test repr(Base.remove_linenums!(a)) == repr(Base.remove_linenums!(b))

@testset "toexpr level 1" begin
    @syms a b c d e t x(t) y(t) z(t)
    @test toexpr(Assignment(a, b)) == :(a = b)
    @test toexpr(a ← b) == :(a = b)
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(a+b) == :($(+)(a, b))
    @test toexpr(a^b) == :($(^)(a, b))
    @test toexpr(a^2) == :($(^)(a, 2))
    @test toexpr(a^-2) == :($(^)($(inv)(a), 2))
    @test toexpr(x(t)+y(t)) == :($(+)(x(t), y(t)))
    @test toexpr(x(t)+y(t)+x(t+1)) == :($(+)(x(t), y(t), x($(+)(1, t))))
    s = LazyState()
    push!(s.symbolify, x(t))
    push!(s.symbolify, y(t))
    @test toexpr(x(t)+y(t)+x(t+1), s) == :($(+)(var"x(t)", var"y(t)", x($(+)(1, t))))

    ex = :(let a = 3, b = $(+)(1,a)
               $(+)(a, b)
           end)

    test_repr(toexpr(Let([a ← 3, b ← 1+a], a + b)), ex)

    test_repr(toexpr(Func([],[], a+b)) |>Base.remove_linenums!, :(function (;)
            $(+)(a, b)
        end))

    test_repr(toexpr(Func([x(t), x],[b ← a+2, y(t) ← b], x(t)+x(t+1)+b+y(t))),
              :(function (var"x(t)", x; b = $(+)(2, a), var"y(t)" = b)
                    $(+)(b, var"x(t)", var"y(t)", x($(+)(1, t)))
                end))
end
