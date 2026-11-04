module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge

/-!
# The self-intersection formula on Chow groups

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible `𝒪_X`-module and let `s ∈ Γ(X, L)` be a global section with
zero scheme `i : D = Z(s) ⟶ X`. [Stacks, Tag 0F95](https://stacks.math.columbia.edu/tag/0F95)
states the self-intersection formula as an identity of maps of **Chow groups**: the composite

  `i^* i_* : \CH_k(D) ⟶ \CH_{k-1}(D)`  sends  `α`  to  `c₁(L|_D) ∩ α`.

That is the statement proved here, with no hypothesis. Each of the three maps of the identity is
the genuine descended operation on Chow groups:

* `i_*` is `Stacks.Chow.properChowPushforward` (Tag 0GU8), whose vanishing hypothesis of Tag 02S2
  is discharged because `i` is a closed immersion;
* `i^*` is `Stacks.Chow.gysinChowOfInvertible`, the descended Gysin map of Tag 02TO, which is
  unconditional in this repository;
* `c₁(L|_D) ∩ -` is `Stacks.Chow.firstChernClassCapChow`, the descended cap product of Tag 02TI,
  also unconditional here.

## The proof

Both sides are homomorphisms out of `\CH_{k+1}(D)`, so it suffices to compare them on the class
of a cycle, and on a cycle each of the three descended maps is the corresponding operation on
cycles. What remains is the identity with `i_*` taken on cycles, which is
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι`, the form of the
self-intersection formula the source's own proof produces; see the module documentation of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersectionFormula` for that proof.

## Degrees

The source writes the composite as `\CH_k(D) ⟶ \CH_{k-1}(D)`. Here the input degree is `k + 1`
and the output degree is `k`, so that the degree-lowering operations compose without casts, as in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap`.

## Main results

* `Stacks.Chow.gysinChowOfInvertible_properChowPushforward_zeroSchemeι` — **Stacks 0F95**:
  `i^* i_* α = c₁(L|_D) ∩ α` in `\CH_k(D)`, for every class `α ∈ \CH_{k+1}(D)`.
* `Stacks.Chow.gysinChowOfInvertible_comp_properChowPushforward_zeroSchemeι` — **Stacks 0F95** as
  the equality of homomorphisms `\CH_{k+1}(D) ⟶ \CH_k(D)` the source states.

## References

* [Stacks Project, Tag 0F95](https://stacks.math.columbia.edu/tag/0F95)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **Stacks 0F95.** The composite of the proper pushforward along the zero scheme
`i : D = Z(s) ⟶ X` of a global section of an invertible module with the Gysin map of that zero
scheme is intersection with the first Chern class of the restriction `L|_D`:

  `i^* i_* α = c₁(L|_D) ∩ α`  in  `\CH_k(D)`,  for `α ∈ \CH_{k+1}(D)`.

All three maps are the operations on Chow groups: `i_*` is Tag 0GU8, whose vanishing hypothesis
of Tag 02S2 is discharged by
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`, `i^*` is
the descended Gysin map `Stacks.Chow.gysinChowOfInvertible` of Tag 02TO and the right hand side
is the descended cap product `Stacks.Chow.firstChernClassCapChow` of Tag 02TI, both of which are
unconditional in this repository. No hypothesis is carried.

Every class is the class of a cycle, and on a cycle the identity is
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι`. -/
@[stacks 0F95]
theorem gysinChowOfInvertible_comp_properChowPushforward_zeroSchemeι :
    (gysinChowOfInvertible C p k L s).comp
        (properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
            (Stacks.Divisors.zeroScheme X L s).subschemeι C
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p rfl (k + 1))) =
      firstChernClassCapChow C k ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L) := by
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β ↦ ?_)
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, properChowPushforward_mk,
    gysinChowOfInvertible_mk, firstChernClassCapChow_mk]
  exact gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι C p k L s β

/-- **Stacks 0F95**, read on a class. This is
`Stacks.Chow.gysinChowOfInvertible_comp_properChowPushforward_zeroSchemeι` evaluated at `α`, the
source's "sends `α` to `c₁(L|_D) ∩ α`". -/
@[stacks 0F95]
theorem gysinChowOfInvertible_properChowPushforward_zeroSchemeι
    (α : chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1)) :
    gysinChowOfInvertible C p k L s
        (properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
            (Stacks.Divisors.zeroScheme X L s).subschemeι C
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p rfl (k + 1)) α) =
      firstChernClassCapChow C k ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L) α :=
  DFunLike.congr_fun (gysinChowOfInvertible_comp_properChowPushforward_zeroSchemeι C p k L s) α

end Stacks.Chow

end
