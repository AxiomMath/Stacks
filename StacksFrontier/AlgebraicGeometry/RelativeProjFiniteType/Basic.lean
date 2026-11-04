module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.GradedPieces
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type of the structure morphism of a relative homogeneous spectrum

Let `S` be a scheme carrying a quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra
`A`, and let `p : Proj_S(A) ⟶ S` be its relative homogeneous spectrum. If `A` is of finite type
as a sheaf of `𝒪_S`-algebras then `p` is of finite type, that is, locally of finite type and
quasi-compact.

Both properties are affine-local on the base. Over an affine open `U` on which the graded ring of
sections `A(U)` is a finite type `Γ(S, U)`-algebra, the part of `Proj_S(A)` lying over `U` is the
chart `Proj A(U)`, whose structure morphism to `U` factors as
`Proj A(U) ⟶ Spec A(U)₀ ⟶ Spec Γ(S, U) ≅ U`. The first map is of finite type and quasi-compact
for every graded ring, the second because `Γ(S, U) ⟶ A(U)₀` is of finite type — it is the
composite of a finite type map with the degree-zero projection, which is surjective — and the
third is an isomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType`: the graded algebra is of finite
  type over the structure sheaf, in the affine-local form: every point of the base has an affine
  neighbourhood over which the graded ring of sections is a finite type algebra over the sections
  of the structure sheaf.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjFiniteType.locallyOfFiniteType_toBase` and
  `Stacks.AlgebraicGeometry.RelativeProjFiniteType.quasiCompact_toBase`: the structure morphism
  of the relative homogeneous spectrum of a finite type quasi-coherent graded algebra is locally
  of finite type and quasi-compact. Together these are the first assertion of Stacks tag 07ZY.

## Implementation notes

That `A(U)` is a finite type algebra over its degree-zero part, which is what the chart needs, is
deduced from finite type over `Γ(S, U)` and the scalar tower `Γ(S, U) ⟶ A(U)₀ ⟶ A(U)`; the tower
commutes because the structure map lands in degree zero, which is
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.toGradeZero_eq`.

The graded ring of sections is a direct sum, so besides the `Γ(S, U)`-algebra structure defined
by its structure map it carries a summandwise `Γ(S, U)`-module structure, and the two agree only
propositionally. The algebra structure used is therefore always
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionRingAlgebra`, installed by
`let`, rather than left to instance search.

## References

* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjFiniteType

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- **Finite type of a quasi-coherent graded algebra over the structure sheaf**, in the
affine-local form: every point of the base has an affine neighbourhood over which the graded ring
of sections is a finite type algebra over the sections of the structure sheaf. This is the
hypothesis of the first assertion of Stacks tag 07ZY. -/
public def IsFiniteType : Prop :=
  ∀ x : S, ∃ U : S.Opens, IsAffineOpen U ∧ x ∈ U ∧ (A.strHom U).FiniteType

/-- A composite of morphisms that are locally of finite type and quasi-compact has both
properties, transported along an equality of morphisms. -/
private theorem properties_of_comp_eq {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    (h : f ≫ g = k) : LocallyOfFiniteType k ∧ QuasiCompact k :=
  h ▸ ⟨inferInstance, inferInstance⟩

include A in
/-- The chart of the relative homogeneous spectrum over an affine open on which the graded ring of
sections is a finite type algebra is of finite type and quasi-compact over that open. -/
private theorem projInclusionToOpen_properties (U : S.Opens) (hU : IsAffineOpen U)
    (hft : (A.strHom U).FiniteType) :
    LocallyOfFiniteType (projInclusionToOpen A U hU) ∧
      QuasiCompact (projInclusionToOpen A U hU) := by
  let _ := A.sectionRingAlgebra U
  let φ := (GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)
  let _ : Algebra Γ(S, U) (A.grading U 0) := φ.toAlgebra
  have hcomp : (algebraMap (A.grading U 0) (A.sectionRing U)).comp φ =
      algebraMap Γ(S, U) (A.sectionRing U) := by
    refine RingHom.ext fun r => ?_
    have hr : φ r = GradedRing.toGradeZero (A.grading U) (A.strHom_mem U) r := by
      rw [A.toGradeZero_eq U]
    rw [RingHom.comp_apply, hr]
    rfl
  let _ := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let _ : Algebra.FiniteType Γ(S, U) (A.sectionRing U) := RingHom.finiteType_algebraMap.mp hft
  let _ : Algebra.FiniteType (A.grading U 0) (A.sectionRing U) :=
    Algebra.FiniteType.of_restrictScalars_finiteType Γ(S, U) (A.grading U 0) (A.sectionRing U)
  have _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.FiniteType.comp_surjective hft
        (GradedRing.projZeroRingHom'_surjective (A.grading U)))
  have hdef : projInclusionToOpen A U hU =
      Proj.toSpecZero (A.grading U) ≫ Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv := rfl
  exact properties_of_comp_eq hdef.symm

include A in
/-- Over an affine open on which the graded ring of sections is a finite type algebra, the
restriction of the structure morphism of the relative homogeneous spectrum is of finite type and
quasi-compact: the chart square identifies it with the chart's own structure morphism. -/
private theorem restrict_toBase_properties (U : S.Opens) (hU : IsAffineOpen U)
    (hft : (A.strHom U).FiniteType) :
    LocallyOfFiniteType ((relativeProj A).toBase ∣_ U) ∧
      QuasiCompact ((relativeProj A).toBase ∣_ U) := by
  have hchart := (relativeProj A).chart_isPullback U hU
  have hrestrict := (isPullback_morphismRestrict (relativeProj A).toBase U).flip
  have he : (hchart.isoIsPullback _ _ hrestrict).inv ≫ projInclusionToOpen A U hU =
      (relativeProj A).toBase ∣_ U :=
    hchart.isoIsPullback_inv_snd _ _ hrestrict
  obtain ⟨hft', hqc'⟩ := projInclusionToOpen_properties A U hU hft
  let _ : LocallyOfFiniteType (projInclusionToOpen A U hU) := hft'
  let _ : QuasiCompact (projInclusionToOpen A U hU) := hqc'
  exact properties_of_comp_eq he

/-- The affine opens witnessing finite type cover the base. -/
private theorem iSup_eq_top_of_isFiniteType {U : S → S.Opens}
    (hU : ∀ x, IsAffineOpen (U x)) (hmem : ∀ x, x ∈ U x) :
    (⨆ x, ((⟨U x, hU x⟩ : S.affineOpens) : S.Opens)) = ⊤ :=
  eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hmem x⟩

include A in
/-- **Stacks 07ZY, first assertion.** The structure morphism of the relative homogeneous spectrum
of a finite type quasi-coherent graded algebra is locally of finite type. -/
@[stacks 07ZY "relative_proj_finite_type",
  ega "II 2.7.1" "(ii)",
  ega "II 4.6.18" "f of finite type",
  ega "II 3.4.1" "locally of finite type",
  ega "II 3.1.3" "locally of finite type"]
public theorem locallyOfFiniteType_toBase (hA : IsFiniteType A) :
    LocallyOfFiniteType (relativeProj A).toBase := by
  choose U hU hmem hft using hA
  let _ : HasAffineProperty @LocallyOfFiniteType _ :=
    HasRingHomProperty.HasAffineProperty @LocallyOfFiniteType
  refine (HasAffineProperty.iff_of_iSup_eq_top (P := @LocallyOfFiniteType)
    (fun x => (⟨U x, hU x⟩ : S.affineOpens))
    (iSup_eq_top_of_isFiniteType hU hmem)).2 fun x => ?_
  let _ : IsAffine (U x).toScheme := hU x
  exact (HasAffineProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp
    (restrict_toBase_properties A (U x) (hU x) (hft x)).1

include A in
/-- **Stacks 07ZY, first assertion.** The structure morphism of the relative homogeneous spectrum
of a finite type quasi-coherent graded algebra is quasi-compact. -/
@[stacks 07ZY "relative_proj_finite_type",
  ega "II 2.7.1" "(ii)",
  ega "II 4.6.18" "f quasi-compact",
  ega "II 3.4.1" "quasi-compactness", ega "II 3.1.3" "quasi-compact"]
public theorem quasiCompact_toBase (hA : IsFiniteType A) :
    QuasiCompact (relativeProj A).toBase := by
  choose U hU hmem hft using hA
  let inst :=
    AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  refine (@HasAffineProperty.iff_of_iSup_eq_top @QuasiCompact (fun X _ _ _ => CompactSpace X)
    inst _ _ _ _ (fun x => (⟨U x, hU x⟩ : S.affineOpens))
    (iSup_eq_top_of_isFiniteType hU hmem)).2 fun x => ?_
  let _ : IsAffine (U x).toScheme := hU x
  exact (@HasAffineProperty.iff_of_isAffine @QuasiCompact (fun X _ _ _ => CompactSpace X)
    inst _ _ _ inferInstance).mp
    (restrict_toBase_properties A (U x) (hU x) (hft x)).2

end Stacks.AlgebraicGeometry.RelativeProjFiniteType

end
