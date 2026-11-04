module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilyFibres
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GorensteinDualizingInvertible
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced

/-!
# The dualizing complex of a fibre of an at-worst-nodal family of curves

Let `f : X ⟶ S` be a family of curves which is at-worst-nodal of relative dimension one, and let
`V` be a scheme presenting the fibre of `f` over a field-valued point `Spec k ⟶ S`. Then `V` is
proper over `k` and, when nonempty, equidimensional of dimension one with at-worst-nodal
singularities (Stacks 0C59 read on the fibre over the unique point of `Spec k`). Such a curve is
Gorenstein (Stacks 0E37), hence Cohen–Macaulay, so (Section 0E6N, from Algebraic Curves, Lemmas
0BS3 and 0BS6) its dualizing complex `ω_V^• = f_V^×(𝒪_{Spec k})` has no cohomology outside
degree `-1` and its dualizing sheaf `ω_V = H^{-1}(ω_V^•)` is invertible. An empty fibre has no
nonzero modules at all.

## Main results

* `AlgebraicGeometry.CurveFamily.fibre_nodal_of_isAtWorstNodal`: a nonempty fibre is proper,
  equidimensional of dimension one, with at-worst-nodal singularities.
* `AlgebraicGeometry.CurveFamily.isZero_homology_dualizingComplexOverField_of_isAtWorstNodal`:
  `H^n(ω_V^•) = 0` for `n ≠ -1`.
* `AlgebraicGeometry.CurveFamily.isInvertible_dualizingSheafOverField_of_isAtWorstNodal`:
  `ω_V` is invertible.

## References

* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0E6N](https://stacks.math.columbia.edu/tag/0E6N)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- A nonempty fibre of a morphism of schemes which is at-worst-nodal of relative dimension one
is equidimensional (Stacks 0C59, condition (1)). -/
theorem equidimensional_of_isPullback_fiber_of_isAtWorstNodal {X S V : Scheme.{u}}
    {q : X ⟶ S} (hq : IsAtWorstNodalOfRelativeDimensionOne q) (s : S) {j : V ⟶ X}
    {g : V ⟶ Spec (.of (S.residueField s))} (sq : IsPullback j g q (S.fromSpecResidueField s))
    [Nonempty V] : TopologicalSpace.Equidimensional V := by
  obtain ⟨-, -, hfib⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff q).mpr hq
  let ι : V ≅ q.fiber s := sq.isoPullback
  have : Nonempty (q.fiber s) := ⟨ι.hom (Classical.arbitrary V)⟩
  obtain ⟨hequi, -, -⟩ := hfib s inferInstance
  exact TopologicalSpace.Equidimensional.of_homeomorph (Scheme.homeoOfIso ι) hequi

/-- **The fibres of an at-worst-nodal family of curves.** If `X ⟶ S` is a family of curves which
is at-worst-nodal of relative dimension one and `V` is a nonempty scheme presenting the fibre of
`X` over a field-valued point `p` of `S`, then `V` is proper over the field `k` of `p`,
equidimensional of dimension one and has at-worst-nodal singularities over `k`. -/
theorem fibre_nodal_of_isAtWorstNodal {X : CurveFamily B hZ}
    (hX : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ X.toBase.hom)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ X.total.obj}
    (hsq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    [Nonempty ((𝒯).obj V)] :
    IsProper ((𝒯).map v) ∧ TopologicalSpace.Equidimensional ((𝒯).obj V) ∧
      topologicalKrullDim ((𝒯).obj V) = 1 ∧
      (letI : ((𝒯).obj V).Over (Spec (.of p.carrier)) := ⟨(𝒯).map v⟩;
        Stacks.Curves.HasAtWorstNodalSingularities p.carrier ((𝒯).obj V)) := by
  have hsq' := isPullback_schemeSpace_of_isPullback_yoneda hsq
  have hprop : IsProper ((𝒯).map v) := isProper_of_isPullback_fieldValuedPoint hsq'
  have hnod : AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne ((𝒯).map v) :=
    (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget v).1
      ((Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase
        hZ).of_isPullback hsq' hX)
  set k := p.carrier
  set f : (𝒯).obj V ⟶ Spec (.of k) := (𝒯).map v
  set s : Spec (.of k) := IsLocalRing.closedPoint k
  have : IsIso ((Spec (.of k)).fromSpecResidueField s) := isIso_fromSpecResidueField_of_field k s
  let g : (𝒯).obj V ⟶ Spec (.of ((Spec (.of k)).residueField s)) :=
    f ≫ inv ((Spec (.of k)).fromSpecResidueField s)
  have hfg : g ≫ (Spec (.of k)).fromSpecResidueField s = f := by simp [g]
  have sq : IsPullback (𝟙 _) g f ((Spec (.of k)).fromSpecResidueField s) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hfg]⟩
  obtain ⟨hdim, hnodal⟩ := Stacks.Models.hasAtWorstNodalSingularities_of_isPullback_fiber hnod s sq
  refine ⟨hprop, equidimensional_of_isPullback_fiber_of_isAtWorstNodal hnod s sq, hdim, ?_⟩
  let φ : CommRingCat.of k ⟶ CommRingCat.of ((Spec (.of k)).residueField s) :=
    Spec.preimage ((Spec (.of k)).fromSpecResidueField s)
  have hφ : Spec.map φ = (Spec (.of k)).fromSpecResidueField s := Spec.map_preimage _
  have : IsIso (Spec.map φ) := by rw [hφ]; infer_instance
  have : IsIso (Scheme.Spec.map φ.op) := inferInstanceAs (IsIso (Spec.map φ))
  have : IsIso φ.op := isIso_of_reflects_iso φ.op Scheme.Spec
  have : IsIso φ := isIso_of_op φ
  have : LocallyOfFiniteType g := by
    have : LocallyOfFiniteType f := inferInstance
    dsimp only [g]
    infer_instance
  exact Stacks.Curves.hasAtWorstNodalSingularities_of_isIso g f hdim (𝟙 _) φ
    (by rw [Category.id_comp, hφ, hfg]) hnodal

/-- A nonempty fibre of an at-worst-nodal family of curves is Gorenstein (Stacks 0E37). -/
theorem isGorenstein_fibre_of_isAtWorstNodal {X : CurveFamily B hZ}
    (hX : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ X.toBase.hom)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ X.total.obj}
    (hsq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    [Nonempty ((𝒯).obj V)] : AlgebraicGeometry.IsGorenstein ((𝒯).obj V) := by
  obtain ⟨hprop, hequi, hdim, hnodal⟩ := fibre_nodal_of_isAtWorstNodal hX hsq
  let : ((𝒯).obj V).Over (Spec (.of p.carrier)) := ⟨(𝒯).map v⟩
  have : LocallyOfFiniteType (((𝒯).obj V) ↘ Spec (.of p.carrier)) :=
    inferInstanceAs (LocallyOfFiniteType ((𝒯).map v))
  exact Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities p.carrier _ hequi hdim hnodal

/-- **The dualizing complex of a fibre of an at-worst-nodal family has no cohomology outside
degree `-1`** (Section 0E6N; Algebraic Curves, Lemma 0BS3). If `X ⟶ S` is a family of curves
which is at-worst-nodal of relative dimension one and `V` presents the fibre over a field-valued
point `Spec k ⟶ S`, then `H^n(ω_V^•) = 0` for `n ≠ -1`, where `ω_V^• = f_V^×(𝒪_{Spec k})`. An
empty fibre has no nonzero modules. -/
theorem isZero_homology_dualizingComplexOverField_of_isAtWorstNodal {X : CurveFamily B hZ}
    (hX : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ X.toBase.hom)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ X.total.obj}
    (hsq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    [IsProper ((𝒯).map v)] (n : ℤ) (hn : n ≠ -1) :
    IsZero ((DerivedCategory.homologyFunctor ((𝒯).obj V).Modules n).obj
      (Stacks.Duality.dualizingComplexOverField ((𝒯).map v)).obj) := by
  by_cases hV : Nonempty ((𝒯).obj V)
  · obtain ⟨-, hequi, hdim, -⟩ := fibre_nodal_of_isAtWorstNodal hX hsq
    have : AlgebraicGeometry.IsGorenstein ((𝒯).obj V) :=
      isGorenstein_fibre_of_isAtWorstNodal hX hsq
    exact Stacks.Duality.isZero_homology_dualizingComplexOverField_of_isCohenMacaulay _
      (isCohenMacaulay_of_isGorenstein _) hequi hdim n hn
  · have : IsEmpty ((𝒯).obj V) := not_nonempty_iff.mp hV
    exact (AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj _ _).mpr
      fun x => isEmptyElim x

/-- **The dualizing sheaf of a nonempty fibre of an at-worst-nodal family is invertible**
(Section 0E6N; Algebraic Curves, Lemma 0BS6). -/
theorem isInvertible_dualizingSheafOverField_of_isAtWorstNodal {X : CurveFamily B hZ}
    (hX : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ X.toBase.hom)
    {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj}
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ X.total.obj}
    (hsq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value))
    [IsProper ((𝒯).map v)] [Nonempty ((𝒯).obj V)] :
    AlgebraicGeometry.SheafOfModules.IsInvertible ((𝒯).obj V).presheaf
        ((𝒯).obj V).ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField ((𝒯).map v)) ∧
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Stacks.Duality.dualizingSheafOverField ((𝒯).map v)) 1 := by
  obtain ⟨-, hequi, hdim, -⟩ := fibre_nodal_of_isAtWorstNodal hX hsq
  exact Stacks.Duality.isInvertible_dualizingSheafOverField_of_isGorenstein _
    (isGorenstein_fibre_of_isAtWorstNodal hX hsq) hequi hdim

end CurveFamily

end AlgebraicGeometry

end
