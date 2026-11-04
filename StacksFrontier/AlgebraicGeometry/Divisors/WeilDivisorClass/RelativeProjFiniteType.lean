module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type of the relative homogeneous spectrum

Let `S` be a scheme carrying a quasi-coherent, commutative, nonnegatively graded
`𝒪_S`-algebra `𝒜`, and let `p : Proj_S(𝒜) ⟶ S` be its relative homogeneous spectrum. If `𝒜` is
of finite type as a sheaf of `𝒪_S`-algebras then `p` is of finite type, that is, locally of
finite type and quasi-compact.

Both properties are affine-local on the base. Over an affine open `U` on which the graded ring
of sections `A = 𝒜(U)` is a finite type `Γ(S, U)`-algebra, the fibre of `p` is the chart
`Proj A`, whose structure morphism to `U` factors as
`Proj A ⟶ Spec A_0 ⟶ Spec Γ(S, U) ≅ U`. The first map is of finite type and quasi-compact for
every graded ring, the second because `Γ(S, U) ⟶ A_0` is of finite type — it is the composite
of a finite type map with the surjection `A ⟶ A_0` — and the third is an isomorphism.

## Main definitions

* `Stacks.RelativeProj.Situation.IsFiniteType` — the graded algebra is of finite type over the
  structure sheaf: every point of the base has an affine neighbourhood over which the graded
  ring of sections is a finite type algebra over the sections of the structure sheaf.

## Main results

* `Stacks.RelativeProj.Situation.relativeProj_locallyOfFiniteType` and
  `Stacks.RelativeProj.Situation.relativeProj_quasiCompact` — the structure morphism of the
  relative homogeneous spectrum of a finite type graded algebra is of finite type.

## Implementation notes

That `A` is a finite type algebra over its degree-zero part, which is what the chart needs, is
deduced from finite type over `Γ(S, U)` and the scalar tower `Γ(S, U) ⟶ A_0 ⟶ A`; the tower
commutes because the structure-sheaf map lands in degree zero, which is
`Stacks.RelativeProj.Situation.SectionRingStructure.baseMap_apply`.

Stacks 07ZY also asserts that the twists `𝒪_X(d)` of the relative homogeneous spectrum are
finite type `𝒪_X`-modules; no declaration in this file carries the tag.  The twists are
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra` of
`StacksFrontier/AlgebraicGeometry/GluedTwistAlgebra/Assemble.lean` (Tag 01NR), the finite-type
assertion at those twists is
`Stacks.AlgebraicGeometry.RelativeProjFiniteType.isFiniteType_relativeProjTwist` of
`StacksFrontier/AlgebraicGeometry/RelativeProjFiniteType/GluedTwists.lean`, and the morphism half
is registered in `StacksFrontier/AlgebraicGeometry/RelativeProjFiniteType/Basic.lean`.

## References

* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- The chart of the relative homogeneous spectrum over an affine open on which the graded ring
of sections is a finite type algebra is of finite type and quasi-compact over that open. -/
private theorem projInclusionToOpen_properties (U : s.base.Opens) (hU : IsAffineOpen U)
    (hft : (show Γ(s.base, U) →+* s.sectionRing U from s.sectionRingBaseMap U).FiniteType) :
    LocallyOfFiniteType (projInclusionToOpen s U hU) ∧
      QuasiCompact (projInclusionToOpen s U hU) := by
  let R := Γ(s.base, U)
  let A := s.sectionRing U
  let A₀ := s.sectionRingGrading U 0
  let φ := (GradedRing.projZeroRingHom' (s.sectionRingGrading U)).comp
    (show R →+* A from s.sectionRingBaseMap U)
  let _ : Algebra R A := (show R →+* A from s.sectionRingBaseMap U).toAlgebra
  let _ : Algebra R A₀ := φ.toAlgebra
  have hcomp : (algebraMap A₀ A).comp φ = algebraMap R A := by
    ext r i
    have hmem : s.sectionRingBaseMap U r ∈ s.sectionRingGrading U 0 := by
      show s.sectionRingBaseMap U r ∈ (DirectSum.of (s.sectionPieces U) 0).range
      let r' : (forget₂ CommRingCat RingCat).obj R := r
      show (s.sectionRingStructure).baseMap U r' ∈ _
      rw [(s.sectionRingStructure).baseMap_apply U r']
      exact ⟨_, rfl⟩
    have hproj : φ r = ⟨s.sectionRingBaseMap U r, hmem⟩ := by
      refine Subtype.ext ?_
      show GradedRing.projZeroRingHom (s.sectionRingGrading U)
        (s.sectionRingBaseMap U r) = s.sectionRingBaseMap U r
      rw [GradedRing.projZeroRingHom_apply,
        DirectSum.decompose_of_mem_same (s.sectionRingGrading U) hmem]
    show ((φ r : A₀) : A) i = (s.sectionRingBaseMap U r) i
    rw [hproj]
  let _ : IsScalarTower R A₀ A := IsScalarTower.of_algebraMap_eq' hcomp.symm
  let _ : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp hft
  let _ : Algebra.FiniteType A₀ A := Algebra.FiniteType.of_restrictScalars_finiteType R A₀ A
  have _ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.FiniteType.comp_surjective hft
        (GradedRing.projZeroRingHom'_surjective (s.sectionRingGrading U)))
  have h : LocallyOfFiniteType (Proj.toSpecZero (s.sectionRingGrading U) ≫
      Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv) ∧
      QuasiCompact (Proj.toSpecZero (s.sectionRingGrading U) ≫
        Spec.map (CommRingCat.ofHom φ) ≫ hU.isoSpec.inv) :=
    ⟨inferInstance, inferInstance⟩
  simpa [projInclusionToOpen, sectionRingZeroMap, φ] using h

/-- Over an affine open on which the graded ring of sections is a finite type algebra, the
restriction of the structure morphism of the relative homogeneous spectrum is of finite type and
quasi-compact: the chart square identifies it with the chart's structure morphism. -/
private theorem relativeProj_restrict_properties (U : s.base.Opens) (hU : IsAffineOpen U)
    (hft : (show Γ(s.base, U) →+* s.sectionRing U from s.sectionRingBaseMap U).FiniteType) :
    LocallyOfFiniteType (relativeProjToBase s ∣_ U) ∧ QuasiCompact (relativeProjToBase s ∣_ U) := by
  have hchart := relativeProjChart_isPullback s ⟨U, hU⟩
  have hrestrict := (isPullback_morphismRestrict (relativeProjToBase s) U).flip
  have he : (hchart.isoIsPullback _ _ hrestrict).inv ≫ projInclusionToOpen s U hU =
      relativeProjToBase s ∣_ U :=
    hchart.isoIsPullback_inv_snd _ _ hrestrict
  obtain ⟨_, _⟩ := projInclusionToOpen_properties s U hU hft
  rw [← he]
  exact ⟨inferInstance, inferInstance⟩

/-- The graded algebra of a relative `Proj` situation is of finite type as a sheaf of algebras
over the structure sheaf: every point of the base has an affine neighbourhood over which the
graded ring of sections is a finite type algebra over the sections of the structure sheaf. -/
def IsFiniteType : Prop :=
  ∀ x : s.base, ∃ U : s.base.Opens, IsAffineOpen U ∧ x ∈ U ∧
    (show Γ(s.base, U) →+* s.sectionRing U from s.sectionRingBaseMap U).FiniteType

/-- The affine opens witnessing finite type cover the base. -/
private theorem iSup_eq_top_of_isFiniteType {U : s.base → s.base.Opens}
    (hU : ∀ x, IsAffineOpen (U x)) (hmem : ∀ x, x ∈ U x) :
    (⨆ x, ((⟨U x, hU x⟩ : s.base.affineOpens) : s.base.Opens)) = ⊤ :=
  eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hmem x⟩

/-- **Stacks 07ZY.** The structure morphism of the relative homogeneous spectrum of a finite
type quasi-coherent graded algebra is locally of finite type. -/
@[ega "II 2.7.1" "more general", ega "II 3.1.3" "partial", ega "II 4.6.18" "partial"]
theorem relativeProj_locallyOfFiniteType (hs : IsFiniteType s) :
    LocallyOfFiniteType (relativeProjToBase s) := by
  choose U hU hmem hft using hs
  let _ : HasAffineProperty @LocallyOfFiniteType _ :=
    HasRingHomProperty.HasAffineProperty @LocallyOfFiniteType
  refine (HasAffineProperty.iff_of_iSup_eq_top (P := @LocallyOfFiniteType)
    (fun x => (⟨U x, hU x⟩ : s.base.affineOpens))
    (iSup_eq_top_of_isFiniteType s hU hmem)).2 fun x => ?_
  let _ : IsAffine (U x).toScheme := hU x
  exact (HasAffineProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp
    (relativeProj_restrict_properties s (U x) (hU x) (hft x)).1

/-- **Stacks 07ZY.** The structure morphism of the relative homogeneous spectrum of a finite
type quasi-coherent graded algebra is quasi-compact. -/
@[ega "II 4.6.18" "partial"]
theorem relativeProj_quasiCompact (hs : IsFiniteType s) :
    QuasiCompact (relativeProjToBase s) := by
  choose U hU hmem hft using hs
  let inst :=
    AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  refine (@HasAffineProperty.iff_of_iSup_eq_top @QuasiCompact (fun X _ _ _ => CompactSpace X)
    inst _ _ _ _ (fun x => (⟨U x, hU x⟩ : s.base.affineOpens))
    (iSup_eq_top_of_isFiniteType s hU hmem)).2 fun x => ?_
  let _ : IsAffine (U x).toScheme := hU x
  exact (@HasAffineProperty.iff_of_isAffine @QuasiCompact (fun X _ _ _ => CompactSpace X)
    inst _ _ _ inferInstance).mp
    (relativeProj_restrict_properties s (U x) (hU x) (hft x)).2

end Stacks.RelativeProj.Situation

end
