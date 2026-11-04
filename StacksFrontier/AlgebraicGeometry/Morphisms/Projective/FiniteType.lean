module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BundleTwistVanishing
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.Basic
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.StrHomGradeZero

/-!
# A projective morphism is of finite type

A morphism `f : X ⟶ S` which is projective in the sense of `AlgebraicGeometry.IsProjective` — a
closed immersion over `S` into the projective bundle `𝐏(ℰ) = Proj_S(Sym(ℰ))` of a quasi-coherent
`𝒪_S`-module `ℰ` of finite type — is of finite type: locally of finite type and quasi-compact.
This is the finiteness half of [Stacks, Tag 01W6] for the first of the three conditions of
Definition 01W8.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra
  .finiteType_strHom_of_adjoin_eq_top`: the graded ring of sections of a sheaf-level graded
  algebra over an open is a finite type algebra over the functions on that open, as soon as
  finitely many elements generate it over its degree-zero part and the structure map is onto that
  degree-zero part.
* `Stacks.SymGraded.finiteType_strHom_symAlgebra`: the graded ring of sections of `Sym(ℰ)` over
  an affine open is a finite type algebra over the functions on that open.
* `Stacks.SymGraded.isFiniteType_symAlgebra`: `Sym(ℰ)` satisfies the finite type hypothesis of
  [Stacks, Tag 07ZY].
* `Stacks.SymGraded.locallyOfFiniteType_schemeProjectiveBundleToBase` and
  `Stacks.SymGraded.quasiCompact_schemeProjectiveBundleToBase`: the projection of the
  projective bundle of a quasi-coherent module of finite type is of finite type.
* `AlgebraicGeometry.IsProjective.locallyOfFiniteType` and
  `AlgebraicGeometry.IsProjective.quasiCompact`: a projective morphism is of finite type.

## References

* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-- The graded ring of sections of a sheaf of graded algebras over an open is a finite type
algebra over the functions on that open, as soon as finitely many elements generate it over its
degree-zero part and the structure map is onto that degree-zero part. -/
theorem finiteType_strHom_of_adjoin_eq_top
    (hbij : Function.Bijective (fun r : Γ(S, U) => r • A.one U)) {ι : Type*} [Finite ι]
    (x : ι → A.sectionRing U)
    (hadj : Algebra.adjoin ↥(A.grading U 0) (Set.range x) = ⊤) :
    (A.strHom U).FiniteType := by
  classical
  let _ := A.sectionRingAlgebra U
  have hFT0 : Algebra.FiniteType ↥(A.grading U 0) (A.sectionRing U) :=
    ⟨⟨(Set.finite_range x).toFinset, by rwa [Set.Finite.coe_toFinset]⟩⟩
  have hsurj : Function.Surjective
      ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)) := by
    intro c
    obtain ⟨r, hr⟩ := exists_strHom_eq_of_mem_grading_zero A U hbij c.2
    exact ⟨r, by rw [RingHom.comp_apply, hr, GradedRing.projZeroRingHom'_apply_coe]⟩
  have hcomp : (algebraMap ↥(A.grading U 0) (A.sectionRing U)).comp
      ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)) = A.strHom U := by
    refine RingHom.ext fun r => ?_
    have hr : (GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U) r =
        GradedRing.toGradeZero (A.grading U) (A.strHom_mem U) r := by
      rw [A.toGradeZero_eq U]
    rw [RingHom.comp_apply, hr]
    rfl
  exact hcomp ▸ (RingHom.finiteType_algebraMap.mpr hFT0).comp (.of_surjective _ hsurj)

end Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra

namespace Stacks.SymGraded

variable {S : Scheme.{u}} (E : S.Modules)

section FiniteType

variable [E.IsQuasicoherent] [E.IsFiniteType]

/-- The graded ring of sections of `Sym(ℰ)` over an affine open is a finite type algebra over
the functions on that open, for a quasi-coherent `𝒪_S`-module `ℰ` of finite type. -/
theorem finiteType_strHom_symAlgebra (U : S.Opens) (hU : IsAffineOpen U) :
    ((Tag01VMRelativeVeryAmple.symAlgebra E).strHom U).FiniteType := by
  obtain ⟨n, w, hw⟩ :=
    @Module.Finite.exists_fin Γ(S, U) Γ(E, U) _ _ _
      (AlgebraicGeometry.moduleFinite_sections_on_affine E U hU)
  have hrange : Set.range (fun k : ULift.{u} (Fin n) => w k.down) = Set.range w := by
    ext z
    simp only [Set.mem_range]
    exact ⟨fun ⟨k, hk⟩ => ⟨k.down, hk⟩, fun ⟨a, ha⟩ => ⟨ULift.up a, ha⟩⟩
  obtain ⟨y, hy⟩ := Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.exists_span_sectionPieces_one
    E (isQuasicoherentPieces_of_isQuasicoherent E) hU
    (fun k : ULift.{u} (Fin n) => w k.down) (by rwa [hrange])
  obtain ⟨x, -, hadj⟩ :=
    Stacks.AlgebraicGeometry.ProjectiveBundleVanishing.exists_degreeOne_generators_of_span
      (A := Tag01VMRelativeVeryAmple.symAlgebra E)
      (Tag01VMRelativeVeryAmple.adjoin_symAlgebra_eq_top E U hU) y hy
  exact SheafGradedAlgebra.finiteType_strHom_of_adjoin_eq_top _ U
    (bijective_smul_one E (isQuasicoherentPieces_of_isQuasicoherent E) U) x hadj

/-- `Sym(ℰ)` is of finite type over the structure sheaf in the affine-local sense: every point of
the base has an affine neighbourhood over which the graded ring of sections is a finite type
algebra. -/
theorem isFiniteType_symAlgebra :
    Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType
      (Tag01VMRelativeVeryAmple.symAlgebra E) := by
  intro x
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, hU, hxU, finiteType_strHom_symAlgebra E U hU⟩

/-- The projection of the projective bundle of a quasi-coherent module of finite type is
locally of finite type. -/
theorem locallyOfFiniteType_schemeProjectiveBundleToBase (hqc : IsQuasicoherentPieces E) :
    LocallyOfFiniteType (schemeProjectiveBundle E hqc).toBase :=
  Stacks.AlgebraicGeometry.RelativeProjFiniteType.locallyOfFiniteType_toBase
    (Tag01VMRelativeVeryAmple.symAlgebra E) (isFiniteType_symAlgebra E)

/-- The projection of the projective bundle of a quasi-coherent module of finite type is
quasi-compact. -/
theorem quasiCompact_schemeProjectiveBundleToBase (hqc : IsQuasicoherentPieces E) :
    QuasiCompact (schemeProjectiveBundle E hqc).toBase :=
  Stacks.AlgebraicGeometry.RelativeProjFiniteType.quasiCompact_toBase
    (Tag01VMRelativeVeryAmple.symAlgebra E) (isFiniteType_symAlgebra E)

end FiniteType

end Stacks.SymGraded

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A projective morphism is locally of finite type. -/
theorem IsProjective.locallyOfFiniteType {f : X ⟶ S} (hf : IsProjective f) :
    LocallyOfFiniteType f := by
  obtain ⟨E, _, _, hqc, i, _, rfl⟩ := hf
  have := Stacks.SymGraded.locallyOfFiniteType_schemeProjectiveBundleToBase E hqc
  infer_instance

/-- A projective morphism is quasi-compact. -/
theorem IsProjective.quasiCompact {f : X ⟶ S} (hf : IsProjective f) : QuasiCompact f := by
  obtain ⟨E, _, _, hqc, i, _, rfl⟩ := hf
  have := Stacks.SymGraded.quasiCompact_schemeProjectiveBundleToBase E hqc
  infer_instance

end AlgebraicGeometry

end
