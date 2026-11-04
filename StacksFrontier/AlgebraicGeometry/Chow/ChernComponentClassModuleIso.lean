module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponentModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence

/-!
# The first Chern class component rule depends on the module only through its isomorphism class

`Stacks.Chow.firstChernComponentClass`, the Chow-class-valued component rule of Stacks 02SO for an
invertible module `ℒ`, assigns to an integral closed subscheme `W ⊆ X` of delta-dimension `k + 1`
the class in `A_k(W)` of the divisor cycle of a meromorphic section of `ℒ|_W` that it chooses.
This rule takes the same value on two isomorphic invertible modules; in particular it agrees on
the pullback of a module in two steps and its pullback along the composite.

## Main results

* `Stacks.Chow.firstChernComponentClass_eq_of_iso` — the component rule of Stacks 02SO is the same
  for two isomorphic invertible modules.
* `Stacks.Chow.firstChernComponentClass_pullbackComp` — the component rules of a module pulled
  back in two steps and pulled back along the composite agree.

## References

* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- **The first Chern class component rule of Stacks 02SO is an isomorphism invariant of the
module.** -/
theorem firstChernComponentClass_eq_of_iso {L N : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (φ : L ≅ N) (W : X.IdealSheafData) [IsIntegral W.subscheme]
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    firstChernComponentClass C p k L W inferInstance hDim =
      firstChernComponentClass C p k N W inferInstance hDim := by
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  have hLW := isInvertible_presheaf_modulePullback L W.subschemeι
  have hNW := isInvertible_presheaf_modulePullback N W.subschemeι
  have hLt : ∀ x : W.subscheme,
      IsTrivializedNear ((Scheme.Modules.pullback W.subschemeι).obj L) x := fun x ↦
    isTrivializedNear_of_isInvertible _ x
  have hNt : ∀ x : W.subscheme,
      IsTrivializedNear ((Scheme.Modules.pullback W.subschemeι).obj N) x := fun x ↦
    isTrivializedNear_of_isInvertible _ x
  set ψ : (Scheme.Modules.pullback W.subschemeι).obj L ⟶
      (Scheme.Modules.pullback W.subschemeι).obj N :=
    (Scheme.Modules.pullback W.subschemeι).map φ.hom with hψ
  have _ : IsIso ψ := by
    rw [hψ]
    exact inferInstanceAs (IsIso ((Scheme.Modules.pullback W.subschemeι).map φ.hom))
  obtain ⟨s, hs⟩ := exists_ne_zero_genericStalk (hLt (genericPoint W.subscheme))
  have hs' : stalkLinearMap ((Scheme.Modules.pullback W.subschemeι).obj L)
      ((Scheme.Modules.pullback W.subschemeι).obj N) ψ (genericPoint W.subscheme) s ≠ 0 := by
    intro h0
    exact hs ((bijective_stalkLinearMap ((Scheme.Modules.pullback W.subschemeι).obj L)
      ((Scheme.Modules.pullback W.subschemeι).obj N) ψ (genericPoint W.subscheme)).injective
        (h0.trans (map_zero _).symm))
  rw [firstChernComponentClass_eq_mk_of_ne_zero C p k L W hDim hs,
    firstChernComponentClass_eq_mk_of_ne_zero C p k N W hDim hs']
  exact congrArg QuotientAddGroup.mk
    (chernComponentCycle_mapStalkLinearMap C (W.subschemeι ≫ p) hDim
      ((Scheme.Modules.pullback W.subschemeι).obj L)
      ((Scheme.Modules.pullback W.subschemeι).obj N) ψ hLt hNt s).symm

/-- **The component rules of a module pulled back in two steps and pulled back along the
composite agree.** The first Chern class component rules on `A` of the pullback of `L` along `q₂`
and then `q₁`, and of its pullback along `q₁ ≫ q₂`, coincide. -/
theorem firstChernComponentClass_pullbackComp {A B T : Scheme.{u}} (q₁ : A ⟶ B) (q₂ : B ⟶ T)
    (pA : A ⟶ C.S) [LocallyOfFiniteType pA] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (W : A.IdealSheafData) [IsIntegral W.subscheme]
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ pA) = ((k + 1 : ℤ) : EInt)) :
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property
        ((Scheme.Modules.pullback q₂).obj L) := isInvertible_presheaf_modulePullback L q₂
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
        ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L)) :=
      isInvertible_presheaf_modulePullback _ q₁
    haveI : AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
        ((Scheme.Modules.pullback (q₁ ≫ q₂)).obj L) :=
      isInvertible_presheaf_modulePullback L (q₁ ≫ q₂)
    firstChernComponentClass C pA k
        ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L))
        W inferInstance hDim =
      firstChernComponentClass C pA k ((Scheme.Modules.pullback (q₁ ≫ q₂)).obj L)
        W inferInstance hDim := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property
      ((Scheme.Modules.pullback q₂).obj L) := isInvertible_presheaf_modulePullback L q₂
  have : AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback (q₁ ≫ q₂)).obj L) :=
    isInvertible_presheaf_modulePullback L (q₁ ≫ q₂)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback q₂ ⋙ Scheme.Modules.pullback q₁).obj L) :=
    isInvertible_presheaf_modulePullback _ q₁
  exact firstChernComponentClass_eq_of_iso C pA k
    ((Scheme.Modules.pullbackComp q₁ q₂).app L :
      (Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L) ≅
        (Scheme.Modules.pullback (q₁ ≫ q₂)).obj L) W hDim

end Stacks.Chow

end
