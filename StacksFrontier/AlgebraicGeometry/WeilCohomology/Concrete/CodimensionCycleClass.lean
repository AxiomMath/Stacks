module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData

/-!
# Codimension-graded cycle classes of closed subschemes, and the fundamental class

Chapter 45 grades Chow groups of a smooth projective scheme `Y` over `k` by codimension,
`CH^c(Y) = ∏_e CH_{e-c}(Y_e)` (`Stacks.Chow.codimensionChowGroup`), where `Y_e` is the open and
closed part of `Y` of dimension `e`. The class `[Z] ∈ CH^c(Y)` of a closed subscheme `Z ⊂ Y` of
codimension `c` has as component on `Y_e` the restriction to `Y_e` of the class of the cycle
`[Z]_{e-c}` associated to `Z` (Stacks 02QU); this is the class `[Z]` of Lemmas 0FHG and 0FHH, e.g.
the class `[Δ] ∈ CH^d(X × X)` of the diagonal of a scheme of dimension `d`. When `Y` and `Z` are
equidimensional of dimensions `e` and `e - c`, its only nonzero component is `[Z]_{e-c}` on
`Y_e = Y`.

## Main definitions

* `Stacks.WeilCohomology.closedSubschemeClass`: the class `[Z] ∈ CH^c(Y)` of a closed subscheme
  `Z ⊂ Y` of codimension `c`.

## Main results

* `Stacks.WeilCohomology.codimensionGysin_fundamentalClass_point`: `p^![Spec k] = [X]` for the
  structure morphism `p : X ⟶ Spec k`, that is, the Gysin map of Stacks 0FF3, graded by
  codimension (`Stacks.Chow.codimensionGysin`), carries the fundamental class of `Spec k` to the
  fundamental class `Stacks.WeilCohomology.fundamentalClass X = ∑_d [X_d]_d`.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FHF](https://stacks.math.columbia.edu/tag/0FHF)
* [Stacks Project, Tag 0FHG](https://stacks.math.columbia.edu/tag/0FHG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- **The class `[Z] ∈ CH^c(Y)` of a closed subscheme `i : Z ⟶ Y` of codimension `c`**, for `Y`
smooth over `k`: on the part `Y_e` of `Y` of dimension `e` it is the restriction to `Y_e` of the
class of the cycle `[Z]_{e-c}` associated to `Z` (Stacks 02QU). -/
def closedSubschemeClass {Y Z : Scheme.{u}} (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]
    (i : Z ⟶ Y) [IsClosedImmersion i] (c : ℤ) : codimensionChowGroup k sY c :=
  fun e ↦ chowGroupRestrict (fieldChowSituation k) sY (partBase sY e) (dimPart sY e).ι rfl
    ((e : ℤ) - c)
    (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY i
      ((e : ℤ) - c)))

/-- The component of `Stacks.WeilCohomology.closedSubschemeClass` on the part of dimension `e`. -/
theorem closedSubschemeClass_apply {Y Z : Scheme.{u}} (sY : Y ⟶ (fieldChowSituation k).S)
    [Smooth sY] (i : Z ⟶ Y) [IsClosedImmersion i] (c : ℤ) (e : ℕ) :
    closedSubschemeClass sY i c e =
      chowGroupRestrict (fieldChowSituation k) sY (partBase sY e) (dimPart sY e).ι rfl
        ((e : ℤ) - c)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY i
          ((e : ℤ) - c))) :=
  rfl

/-- Fundamental classes in two ways of writing the same degree are heterogeneously equal. -/
private theorem fundamentalChowClass_heq {C : ChowSituation.{u}} {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {n n' : ℤ} (h : n = n') :
    fundamentalChowClass C sX n ≍ fundamentalChowClass C sX n' := by
  subst h
  rfl

/-- **`p^![Spec k] = [X]`.** For a smooth projective scheme `X` over `k` and its morphism
`p : X ⟶ Spec k` (whose underlying morphism of schemes is the structure morphism), the Gysin map
`p^! : CH^0(Spec k) ⟶ CH^0(X)` of Stacks 0FF3 carries the fundamental class of `Spec k` to the
fundamental class `[X] = ∑_d [X_d]_d`. -/
theorem codimensionGysin_fundamentalClass_point {X : (SmoothProjectiveScheme k).FullSubcategory}
    (p : X ⟶ SmoothProjectiveScheme.point k) :
    codimensionGysin X.obj.hom (SmoothProjectiveScheme.point k).obj.hom (Over.w p.hom) 0
        (fundamentalClass (SmoothProjectiveScheme.point k)) = fundamentalClass X := by
  funext d
  refine (chowGroupDimPartPieceEquiv X.obj.hom (SmoothProjectiveScheme.point k).obj.hom
    (f := p.hom.left) d ((d : ℤ) - 0)).injective (funext fun e ↦ ?_)
  rw [chowGroupDimPartPieceEquiv_apply, chowGroupDimPartPieceEquiv_apply,
    chowGroupRestrict_codimensionGysin]
  have hL : dimPartPieceGysin X.obj.hom (SmoothProjectiveScheme.point k).obj.hom (Over.w p.hom) d
        e.down 0 (fundamentalClass (SmoothProjectiveScheme.point k) e.down) ≍
      fundamentalChowClass (fieldChowSituation k)
        (dimPartPieceBase X.obj.hom (SmoothProjectiveScheme.point k).obj.hom p.hom.left d e.down)
        ((e.down : ℤ) - ((e.down : ℤ) - d)) := by
    refine (chowGroupDegreeEquiv_heq _ _ _ _).trans ?_
    rw [← dimPartPieceGysinClass_capTargetHom_fundamentalChowClass X.obj.hom
      (SmoothProjectiveScheme.point k).obj.hom (Over.w p.hom) d e.down]
    exact BivariantClass.capTargetHom_heq_of_heq _ (by ring) (chowGroupDegreeEquiv_heq _ _ _ _)
  have hR : chowGroupRestrict (fieldChowSituation k) (partBase X.obj.hom d)
        (dimPartPieceBase X.obj.hom (SmoothProjectiveScheme.point k).obj.hom p.hom.left d e.down)
        (dimPartPiece X.obj.hom (SmoothProjectiveScheme.point k).obj.hom p.hom.left d e.down).ι
        rfl ((d : ℤ) - 0) (fundamentalClass X d) ≍
      fundamentalChowClass (fieldChowSituation k)
        (dimPartPieceBase X.obj.hom (SmoothProjectiveScheme.point k).obj.hom p.hom.left d e.down)
        (d : ℤ) := by
    have hdim := WeilCohomology.schemeDeltaDimension_le_of_relativeDimension
      (partBase X.obj.hom d) (relativeDimension_partBase X.obj.hom d)
    rw [← chowGroupRestrict_fundamentalChowClass (fieldChowSituation k)
        (partBase X.obj.hom d)
      _ (dimPartPiece X.obj.hom (SmoothProjectiveScheme.point k).obj.hom p.hom.left d e.down).ι
      rfl d hdim]
    exact chowGroupRestrict_heq_of_heq _ _ _ _ _ (by ring) _ _ (chowGroupDegreeEquiv_heq _ _ _ _)
  exact eq_of_heq (hL.trans ((fundamentalChowClass_heq _ (by ring)).trans hR.symm))

end Stacks.WeilCohomology

end
