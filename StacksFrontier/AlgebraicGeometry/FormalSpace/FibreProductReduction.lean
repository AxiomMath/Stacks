module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction

/-!
# The reduction of a fibre product of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `X ⟶ Z` and `Y ⟶ Z` be morphisms
of formal algebraic spaces over `S`. Stacks 0CB9 states the identity
`(X ×_Z Y)_red = (X_red ×_{Z_red} Y_red)_red`. The reduction on the outside of the right-hand
side is essential: the fibre product of the three reductions is in general *not* reduced, so the
assertion is about the reduction of that fibre product and not about the fibre product itself.

The proof is the universal property of the reduction and nothing else. Write `P` for a fibre
product of `X` and `Y` over `Z`, and `Q` for a fibre product of `X_red` and `Y_red` over
`Z_red`. A reduced algebraic space mapping to `P` maps to `X` and to `Y` compatibly over `Z`,
hence — being reduced — factors uniquely through `X_red` and through `Y_red`, and the two
resulting maps to `Z_red` agree because they agree after composing with `Z_red ⟶ Z`. So it maps
to `Q`, and therefore to the reduction of `Q`. Conversely the reduction of `Q` is itself a
reduced algebraic space mapping to `P`, hence maps to the reduction of `P`. The two reductions
represent the same functor on reduced algebraic spaces, so they are canonically isomorphic.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_iso_reduction_fibreProduct`: the same identity for any
  models of the two fibre products and any reductions of the five spaces involved; reductions
  being unique up to unique isomorphism, this is the form in which the argument is carried out.
* `AlgebraicGeometry.FormalSpace.IsReduction.eq_of_comp_inclusion_eq`: two morphisms from a
  reduced algebraic space into a reduction agree as soon as they agree after the inclusion.

## Implementation notes

The statement for the fibre products `CategoryTheory.Limits.pullback` and the reductions
`AlgebraicGeometry.FormalSpace.reduction` supplied by Stacks 0AIN is
`AlgebraicGeometry.FormalSpace.exists_iso_reduction_pullback`, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductReductionChosen`, which deduces it from
the form here.

The general form `exists_iso_reduction_fibreProduct` takes the two fibre products as pullback
squares rather than as `CategoryTheory.Limits.pullback`, and the reductions as witnesses of
`AlgebraicGeometry.FormalSpace.IsReduction`, so that it applies to any model of each.

The identity of the source is an equality of spaces, which in this library is a canonical
isomorphism. The conclusion therefore produces an isomorphism of the two reductions over the
comparison morphism `X_red ×_{Z_red} Y_red ⟶ X ×_Z Y` induced by the inclusions of the
reductions. That isomorphism is the unique morphism lying over the comparison morphism, by the
uniqueness clause of the universal property of the reduction of `X ×_Z Y`; uniqueness given the
compatibility is immediate from
`AlgebraicGeometry.FormalSpace.IsReduction.eq_of_comp_inclusion_eq`.

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0CB9](https://stacks.math.columbia.edu/tag/0CB9)
* [Stacks Project, Tag 0GB8](https://stacks.math.columbia.edu/tag/0GB8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace IsReduction

/-- Two morphisms from a reduced algebraic space into a reduction which agree after the inclusion
of that reduction are equal: each is the unique factorisation of their common composite. -/
theorem eq_of_comp_inclusion_eq {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (h : IsReduction B S hS X Xred i) {U : FppfSheaf B S hS}
    (hU : Space.IsAlgebraicSpaceULift.{u + 1} B S hS U.obj)
    (hUred : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS U.obj
      (fun T : Scheme.{u} ↦ IsReduced T))
    {a b : U ⟶ Xred} (hab : a ≫ i = b ≫ i) : a = b := by
  obtain ⟨l, -, hu⟩ := h.universal U hU hUred (a ≫ i)
  rw [hu a rfl, hu b hab.symm]

end IsReduction

variable {X Y Z Xred Yred Zred P Q Pred Qred : FppfSheaf B S hS}
  {f : X ⟶ Z} {g : Y ⟶ Z} {iX : Xred ⟶ X} {iY : Yred ⟶ Y} {iZ : Zred ⟶ Z}
  {fred : Xred ⟶ Zred} {gred : Yred ⟶ Zred}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {q₁ : Q ⟶ Xred} {q₂ : Q ⟶ Yred}
  {iP : Pred ⟶ P} {iQ : Qred ⟶ Q}

/-- The inclusions of the reductions of `X`, `Y` and `Z` induce a morphism from a fibre product
of `Xred` and `Yred` over `Zred` to a fibre product of `X` and `Y` over `Z`. -/
private theorem exists_comparison_of_isPullback
    (hfred : fred ≫ iZ = iX ≫ f) (hgred : gred ≫ iZ = iY ≫ g)
    (hP : IsPullback p₁ p₂ f g) (hQ : IsPullback q₁ q₂ fred gred) :
    ∃ cmp : Q ⟶ P, cmp ≫ p₁ = q₁ ≫ iX ∧ cmp ≫ p₂ = q₂ ≫ iY :=
  hP.exists_lift (q₁ ≫ iX) (q₂ ≫ iY) <| by
    calc (q₁ ≫ iX) ≫ f = (q₁ ≫ fred) ≫ iZ := by
          rw [Category.assoc, Category.assoc, hfred]
      _ = (q₂ ≫ gred) ≫ iZ := by rw [hQ.w]
      _ = (q₂ ≫ iY) ≫ g := by rw [Category.assoc, Category.assoc, hgred]

/-- The reduction of a fibre product of `X` and `Y` over `Z` maps to a fibre product of `Xred`
and `Yred` over `Zred`: its two components are the factorisations through `Xred` and `Yred` of
the two projections, and these agree over `Zred` because they agree after composing with the
inclusion `Zred ⟶ Z`, where they become the two composites of the pullback square for `P`. -/
private theorem exists_descent_of_isPullback
    (hiX : IsReduction B S hS X Xred iX) (hiY : IsReduction B S hS Y Yred iY)
    (hiZ : IsReduction B S hS Z Zred iZ) (hiP : IsReduction B S hS P Pred iP)
    (hfred : fred ≫ iZ = iX ≫ f) (hgred : gred ≫ iZ = iY ≫ g)
    (hP : IsPullback p₁ p₂ f g) (hQ : IsPullback q₁ q₂ fred gred) :
    ∃ c : Pred ⟶ Q, c ≫ q₁ ≫ iX = iP ≫ p₁ ∧ c ≫ q₂ ≫ iY = iP ≫ p₂ := by
  obtain ⟨b₁, hb₁, -⟩ := hiX.universal Pred hiP.algebraic hiP.reduced (iP ≫ p₁)
  obtain ⟨b₂, hb₂, -⟩ := hiY.universal Pred hiP.algebraic hiP.reduced (iP ≫ p₂)
  have hb : b₁ ≫ fred = b₂ ≫ gred := by
    refine hiZ.eq_of_comp_inclusion_eq hiP.algebraic hiP.reduced ?_
    calc (b₁ ≫ fred) ≫ iZ = (b₁ ≫ iX) ≫ f := by rw [Category.assoc, Category.assoc, hfred]
      _ = iP ≫ p₁ ≫ f := by rw [hb₁, Category.assoc]
      _ = iP ≫ p₂ ≫ g := by rw [hP.w]
      _ = (b₂ ≫ iY) ≫ g := by rw [hb₂, Category.assoc]
      _ = (b₂ ≫ gred) ≫ iZ := by rw [Category.assoc, Category.assoc, hgred]
  obtain ⟨c, hc₁, hc₂⟩ := hQ.exists_lift b₁ b₂ hb
  refine ⟨c, ?_, ?_⟩
  · rw [← Category.assoc, hc₁, hb₁]
  · rw [← Category.assoc, hc₂, hb₂]

/-- If `c` lifts `iP ≫ p` to `Q`, `α ≫ iP = iQ ≫ cmp` and `cmp` lies over `q ≫ i`, then
`α ≫ c` and `iQ` agree after composing with `q ≫ i`. -/
private theorem comp_comp_eq_of_comp_eq {A B' C D V W : FppfSheaf B S hS}
    {α : A ⟶ B'} {c : B' ⟶ C} {iP : B' ⟶ D} {iQ : A ⟶ C} {cmp : C ⟶ D} {p : D ⟶ W}
    {q : C ⟶ V} {i : V ⟶ W}
    (hc : c ≫ q ≫ i = iP ≫ p) (hα : α ≫ iP = iQ ≫ cmp) (hcmp : cmp ≫ p = q ≫ i) :
    (α ≫ c) ≫ q ≫ i = iQ ≫ q ≫ i := by
  rw [Category.assoc, hc, ← Category.assoc, hα, Category.assoc, hcmp]

/-- Stacks 0CB9 for arbitrary reductions and arbitrary models of the fibre products. Let
`X ⟶ Z` and `Y ⟶ Z` be morphisms of formal algebraic spaces over `S`,
let `iX : Xred ⟶ X`, `iY : Yred ⟶ Y` and `iZ : Zred ⟶ Z` be reductions and let `Xred ⟶ Zred` and
`Yred ⟶ Zred` be compatible with the two given morphisms. Let `P` be a fibre product of `X` and
`Y` over `Z`, let `Q` be a fibre product of `Xred` and `Yred` over `Zred`, and let
`iP : Pred ⟶ P` and `iQ : Qred ⟶ Q` be reductions of those two fibre products. Then the
inclusions of the reductions induce a morphism `Q ⟶ P` over which `Qred` and `Pred` are
isomorphic: `(X ×_Z Y)_red = (X_red ×_{Z_red} Y_red)_red`. -/
theorem exists_iso_reduction_fibreProduct
    (_hX : IsFormalAlgebraicSpace B S hS X) (_hY : IsFormalAlgebraicSpace B S hS Y)
    (_hZ : IsFormalAlgebraicSpace B S hS Z)
    (hiX : IsReduction B S hS X Xred iX) (hiY : IsReduction B S hS Y Yred iY)
    (hiZ : IsReduction B S hS Z Zred iZ)
    (hfred : fred ≫ iZ = iX ≫ f) (hgred : gred ≫ iZ = iY ≫ g)
    (hP : IsPullback p₁ p₂ f g) (hQ : IsPullback q₁ q₂ fred gred)
    (hiP : IsReduction B S hS P Pred iP) (hiQ : IsReduction B S hS Q Qred iQ) :
    ∃ (cmp : Q ⟶ P) (e : Qred ≅ Pred),
      cmp ≫ p₁ = q₁ ≫ iX ∧ cmp ≫ p₂ = q₂ ≫ iY ∧ e.hom ≫ iP = iQ ≫ cmp := by
  obtain ⟨cmp, hcmp₁, hcmp₂⟩ := exists_comparison_of_isPullback hfred hgred hP hQ
  obtain ⟨c, hc₁, hc₂⟩ := exists_descent_of_isPullback hiX hiY hiZ hiP hfred hgred hP hQ
  obtain ⟨α, hα, -⟩ := hiP.universal Qred hiQ.algebraic hiQ.reduced (iQ ≫ cmp)
  obtain ⟨β, hβ, -⟩ := hiQ.universal Pred hiP.algebraic hiP.reduced c
  have hcP : c ≫ cmp = iP := by
    refine hP.hom_ext ?_ ?_
    · rw [Category.assoc, hcmp₁, hc₁]
    · rw [Category.assoc, hcmp₂, hc₂]
  have haQ : α ≫ c = iQ := by
    refine hQ.hom_ext ?_ ?_
    · exact hiX.eq_of_comp_inclusion_eq hiQ.algebraic hiQ.reduced <| by
        simpa only [Category.assoc] using comp_comp_eq_of_comp_eq hc₁ hα hcmp₁
    · exact hiY.eq_of_comp_inclusion_eq hiQ.algebraic hiQ.reduced <| by
        simpa only [Category.assoc] using comp_comp_eq_of_comp_eq hc₂ hα hcmp₂
  refine ⟨cmp, ⟨α, β, ?_, ?_⟩, hcmp₁, hcmp₂, hα⟩
  · refine hiQ.eq_of_comp_inclusion_eq hiQ.algebraic hiQ.reduced ?_
    rw [Category.assoc, hβ, haQ, Category.id_comp]
  · refine hiP.eq_of_comp_inclusion_eq hiP.algebraic hiP.reduced ?_
    rw [Category.assoc, hα, ← Category.assoc, hβ, hcP, Category.id_comp]

end AlgebraicGeometry.FormalSpace

end
