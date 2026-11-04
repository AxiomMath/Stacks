module

public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapSmooth
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapBirationalCurve
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# The Abel maps of a smooth projective curve over a separably closed field

Clauses (4), (5) and (6) of [Stacks, Tag 0BA0] for a smooth projective curve `X` over a separably
closed field `k`, stated for the degree components `Pic^d_{X/k}` of the Picard scheme of `X`
(`Stacks.PicardFunctor.picardSchemeDegreeComponent`, at a rational point `σ` of `X`, which exists
by [Stacks, Tag 056U]).

The Picard scheme exists by [Stacks, Tag 0B9Z]; its proof is the translation property, which is the
conclusion `Stacks.PicardFunctor.TwistToNormalized` of [Stacks, Tag 0B9Y].

## Main definitions

* `Stacks.AbelMap.curveSection`: a rational point of `X`.

## Main results

* `Stacks.AbelMap.existsUnique_abelMap`: clause (4), the unique Abel map
  `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}` sending a degree-`d` family `D` to the class of `𝒪(D)`.
* `Stacks.AbelMap.surjective_smooth_curveAbelMap`: clause (5), `γ_d` is surjective for `d ≥ g` and
  smooth for `d ≥ 2g - 1`.
* `Stacks.AbelMap.isBirational_curveAbelMap`: clause (6), `γ_g` is birational.

All three assume the representability of the Picard functor; clauses (5) and (6) also take the
conclusion of [Stacks, Tag 0B9Y], and clause (5) the vanishing of [Stacks, Tag 0B90].

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.PicardFunctor Stacks.PicardCurve

universe u

namespace Stacks.AbelMap

variable {k : Type u} [Field k] [IsSepClosed k] (B : BigFppfSite.{u}) {X : Scheme.{u}}
  (hX : B.Contains X) (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [Smooth (B.inclusion.map f)]

include hX hk in
omit [Smooth (B.inclusion.map f)] in
/-- A smooth curve over a separably closed field is geometrically irreducible
([Stacks, Tag 020J]). -/
theorem geometricallyIrreducible_of_isSepClosed : GeometricallyIrreducible (B.inclusion.map f) :=
  geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _ _

/-- **A rational point of the curve** ([Stacks, Tag 056U]). -/
def curveSection : Spec (.of k) ⟶ X :=
  Classical.choose (exists_section_of_isSepClosed (B.inclusion.map f))

/-- The rational point `curveSection` is a section of the structure morphism of `X`. -/
theorem curveSection_comp : curveSection B hX hk f ≫ B.inclusion.map f = 𝟙 _ :=
  Classical.choose_spec (exists_section_of_isSepClosed (B.inclusion.map f))

include hX hk in
omit [IsSepClosed k] [Smooth (B.inclusion.map f)] in
/-- A projective curve is a projective variety. -/
theorem isProjectiveVariety_of_isProjective (hproj : IsProjective (B.inclusion.map f)) :
    IsProjectiveVariety k (B.inclusion.map f) :=
  have : IsProper (B.inclusion.map f) := hproj.isProper
  (isProjectiveVariety_iff k _).2 ⟨inferInstance, isProjectiveMorphism_of_isProper_of_isCurve k _⟩

section Clauses

variable [GeometricallyIrreducible (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [(picardFunctor B hX hk f).IsRepresentable]

omit [IsSepClosed k] in
/-- **Clause (4) of [Stacks, Tag 0BA0] at a rational point**: for `d ≥ 0` there is exactly one
morphism `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}` sending the `T`-point of `Hilb^d_{X/k}` given by a
degree-`d` family `D` on `X_T` to the class of `𝒪(D)`. -/
theorem existsUnique_abelMap (d : ℕ) (H : BigFppfOver B (Spec (.of k)) hk)
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map H.hom)) d) :
    ∃! γ : H ⟶ picardSchemeDegreeComponent B hX hk f σ hσ d,
      ∀ {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ H),
        picardHomEquiv B hX hk f (t ≫ γ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d) =
          (toPicardFunctor B hX hk f).app (op T) (hH.family (testMap B hk t)).picardClass := by
  have : IsProper (B.inclusion.map f) := inferInstance
  refine ⟨curveAbelMap B hX hk f σ hσ H hH,
    fun t => picardHomEquiv_comp_curveAbelMap B hX hk f σ hσ H hH t, fun γ hγ => ?_⟩
  refine abelMap_unique B hX hk f (isDegreeComponent_degreeSubfunctor B hX hk f σ hσ d) H hH
    (degreeComponentRepresentableBy B hX hk f σ hσ d) γ (Subtype.ext ?_)
  have h := hγ (𝟙 H)
  rw [Category.id_comp] at h
  refine h.trans ?_
  show _ = (toPicardFunctor B hX hk f).app (op H) (hH.family (𝟙 _)).picardClass
  rfl

include σ hσ in
omit [IsSepClosed k] in
/-- **Clause (5) of [Stacks, Tag 0BA0] at a rational point**: `γ_d` is surjective for `d ≥ g` and
smooth for `d ≥ 2g - 1`. The vanishing of [Stacks, Tag 0B90] on curves over algebraically closed
fields is `hvan1`, and the conclusion of [Stacks, Tag 0B9Y] is `htw`. -/
theorem surjective_smooth_curveAbelMap (htw : TwistToNormalized B hX hk f)
    (hvan1 : ∀ (K : Type u) [Field K] [IsAlgClosed K] {Z : Scheme.{u}} (fZ : Z ⟶ Spec (.of K))
      [IsProper fZ] [IsCurve K fZ] (M : Z.Modules)
      (hM : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M),
      2 * (genus fZ : ℤ) - 1 ≤ @invertibleCurveDegree K _ Z fZ _
        (IsCurve.topologicalKrullDim_eq_one (k := K) (f := fZ)).le M hM →
      IsZero (cohomologyOverField K fZ M 1))
    (d : ℕ) (H : BigFppfOver B (Spec (.of k)) hk)
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map H.hom)) d) :
    (genus (B.inclusion.map f) ≤ d →
      Surjective (B.inclusion.map (curveAbelMap B hX hk f σ hσ H hH).left)) ∧
    (2 * (genus (B.inclusion.map f) : ℤ) - 1 ≤ d →
      AlgebraicGeometry.Smooth (B.inclusion.map (curveAbelMap B hX hk f σ hσ H hH).left)) := by
  have : IsProper (B.inclusion.map f) := inferInstance
  refine ⟨surjective_curveAbelMap B hX hk f σ hσ H hH, fun hd => ?_⟩
  have := locallyOfFiniteType_picardDegreeComponent B hX hk f σ hσ htw d
  exact smooth_abelMap_of_vanishing B hX hk f σ hσ
    (isDegreeComponent_degreeSubfunctor B hX hk f σ hσ d) H hH
    (degreeComponentRepresentableBy B hX hk f σ hσ d) hvan1 hd

include σ hσ in
omit [IsSepClosed k] in
/-- **Clause (6) of [Stacks, Tag 0BA0] at a rational point**: `γ_g` is birational. -/
theorem isBirational_curveAbelMap (htw : TwistToNormalized B hX hk f)
    (H : BigFppfOver B (Spec (.of k)) hk)
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map H.hom)) (genus (B.inclusion.map f))) :
    IsBirational (B.inclusion.map (curveAbelMap B hX hk f σ hσ H hH).left) :=
  isBirational_curveAbelMap_of_twistToNormalized B hX hk f σ hσ H hH htw

end Clauses

end Stacks.AbelMap

end
