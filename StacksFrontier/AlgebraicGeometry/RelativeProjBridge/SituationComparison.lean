module

public import StacksFrontier.Algebra.DirectSum.GradedRingEquiv
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjSectionRings
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Bridge

/-!
# The two relative-`Proj` substrates have the same graded rings of local sections

This repository carries two inputs for the relative homogeneous spectrum of a quasi-coherent
graded `𝒪_S`-algebra. One is
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, whose section ring over an open
is graded by `DirectSum.of_mul_of` read off the multiplication of the algebra. The other is
`Stacks.RelativeProj.Situation`, whose section ring carries the graded structure selected by
`Classical.choice` from `Stacks.RelativeProj.Situation.sectionRingStructure_exists`. **For one and
the same sheaf of graded algebras this file identifies the two section rings as graded rings.**

The underlying additive groups and the gradings are equal by `rfl`: both are
`⨁_{k ≥ 0} Γ(𝒜ₖ, U)` graded by the summands. The one divergence is the `CommRing` instance, and
it closes in a single step, because the chosen structure's defining equation
`mul_homogeneous` says its multiplication of homogeneous sections is the multiplication of the
graded algebra — which is what `SheafGradedAlgebra.gMul_def` says by `rfl`. So the comparison is
carried by the **identity map**, and no transport appears anywhere.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.situationOfGradedAlgebra`: the
  `Stacks.RelativeProj.Situation` on the same data as
  `Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra`.
* `…situationSectionRingEquiv`: **the two graded rings of local sections over an open are the
  same ring.**
* `…situationSectionGradedHom` and `…situationSectionGradedInv`: that isomorphism and its inverse
  as homomorphisms of graded rings.

## Main results

* `…gMul_situationOfGradedAlgebra`: the two multiplications of homogeneous sections agree.
* `…situationSectionRingEquiv_of`: the comparison is the identity on a homogeneous section.
* `…situationSectionRingEquiv_strHom`: it carries the structure map to the canonical map from the
  structure sheaf.
* `…situationSectionRingEquiv_resRingHom`: **it is natural in the open.**

## Implementation notes

The comparison is assembled by `DirectSum.gradedCongrRingEquiv` from the degreewise identity
`AddEquiv.refl`, with the two type families passed explicitly; without that the elaborator spends
the whole heartbeat budget in `whnf` on the section groups of a sheaf of modules.

`Stacks.RelativeProj.Situation.sectionRingGradedRing` is indexed by `U : s.base.Opens`. For
`s = situationOfGradedAlgebra …` that type is `S.Opens` definitionally, but the situation is a
plain `def`, which instance search does not unfold, so `Semiring (s.sectionRing U)` is not
synthesizable for `U : S.Opens`. `…gcommRingSituationOfGradedAlgebra` is that instance with
`U : S.Opens`; its body is the same term.

## Not done here

This settles the algebra of the comparison of the two presentations of a relative `Proj`, in full
generality. **The glueing is settled elsewhere**, and no longer remains: the two presentations are
glued by two different frameworks — `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData` on
the `SheafGradedAlgebra` side and `Stacks.RelativeProj.Data` on the `Situation` side — so that
`AlgebraicGeometry.reesDataIso`, which compares two `Stacks.RelativeProj.Data`, does not apply;
but `Stacks.AlgebraicGeometry.ProjPresentation.exists_iso_relativeProj`
(`StacksFrontier/AlgebraicGeometry/ProjPresentationCompare/Basic.lean`) compares exactly those two
frameworks, from a graded ring isomorphism over each affine open of the base — which is what the
comparison above supplies. `AlgebraicGeometry.ProjectiveBundlePresentationsAgree` is proved that
way, as `AlgebraicGeometry.projectiveBundlePresentationsAgree` in
`StacksFrontier/AlgebraicGeometry/Morphisms/Projective/BaseChange.lean`, and the same route puts the
Rees algebra on the `SheafGradedAlgebra` substrate in
`StacksFrontier/AlgebraicGeometry/Blowup/ReesProjBridge.lean`.

Only the algebra is treated here. The same comparison for a graded module over it is
`StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationModuleComparison`, where it is easier:
a graded module carries no structure chosen by `Classical.choice`, so the two graded scalar
actions are equal as instances rather than degreewise.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SheafSymmetricAlgebra
open scoped DirectSum

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

variable {S : Scheme.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)
  (hcomm : IsCommutative A) (hneg : VanishesInNegativeDegrees A)
  (hqc : ∀ n : ℤ, ((A.piece n : S.Modules)).IsQuasicoherent)

/-! ### The situation on the same data -/

/-- **The relative-`Proj` situation of a sheaf of graded algebras**, on the same data as
`Stacks.AlgebraicGeometry.SheafSymmetricAlgebra.toSheafGradedAlgebra`. The two carry the same
pieces and the same multiplication, so every comparison below is between two gradings of one
additive group. -/
def situationOfGradedAlgebra : Stacks.RelativeProj.Situation.{u} where
  base := S
  algebra := A
  mul_comm := hcomm
  negative_isZero n hn := isZero_piece_of_neg A hneg n hn
  isQuasicoherent := hqc

/-- The base of `situationOfGradedAlgebra A hcomm hneg hqc` is the scheme `S`. -/
theorem situationOfGradedAlgebra_base :
    (situationOfGradedAlgebra A hcomm hneg hqc).base = S := rfl

/-- The sheaf of graded algebras of `situationOfGradedAlgebra A hcomm hneg hqc` is `A`. -/
theorem situationOfGradedAlgebra_algebra :
    (situationOfGradedAlgebra A hcomm hneg hqc).algebra = A := rfl

/-- The graded-ring structure on the homogeneous sections over an open, indexed by `S.Opens`.
This is `Stacks.RelativeProj.Situation.sectionRingGradedRing` verbatim; see the implementation
notes for why the restatement is needed. -/
instance gcommRingSituationOfGradedAlgebra (U : S.Opens) :
    DirectSum.GCommRing ((situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U) :=
  Stacks.RelativeProj.Situation.sectionRingGradedRing
    (situationOfGradedAlgebra A hcomm hneg hqc) U

/-! ### The comparison -/

/-- **The two multiplications of homogeneous sections agree.** On the `SheafGradedAlgebra` side
this is `SheafGradedAlgebra.gMul_def`, true by `rfl`; on the `Situation` side it is the defining
equation `mul_homogeneous` of the chosen section-ring structure. -/
theorem gMul_situationOfGradedAlgebra (U : S.Opens) (i j : ℕ)
    (a : (toSheafGradedAlgebra A hcomm hneg hqc).sectionPieces U i)
    (b : (toSheafGradedAlgebra A hcomm hneg hqc).sectionPieces U j) :
    (GradedMonoid.GMul.mul a b :
        (toSheafGradedAlgebra A hcomm hneg hqc).sectionPieces U (i + j)) =
      (GradedMonoid.GMul.mul
          (a : (situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U i)
          (b : (situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U j) :
        (situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U (i + j)) :=
  ((toSheafGradedAlgebra A hcomm hneg hqc).gMul_def U a b).trans
    (eq_of_heq ((Stacks.RelativeProj.Situation.sectionRingStructure
      (situationOfGradedAlgebra A hcomm hneg hqc)).mul_homogeneous U i j a b)).symm

/-- **The graded rings of local sections of the two substrates over an open are the same ring.**
The map is the identity; only the two `CommRing` instances have to be reconciled, which
`Stacks.AlgebraicGeometry.RelativeProjBridge.gMul_situationOfGradedAlgebra` does degreewise. -/
def situationSectionRingEquiv (U : S.Opens) :
    (toSheafGradedAlgebra A hcomm hneg hqc).sectionRing U ≃+*
      (situationOfGradedAlgebra A hcomm hneg hqc).sectionRing U :=
  DirectSum.gradedCongrRingEquiv
    (A := fun k : ℕ => (toSheafGradedAlgebra A hcomm hneg hqc).sectionPieces U k)
    (B := fun k : ℕ => (situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U k)
    (fun _ => AddEquiv.refl _)
    (fun i j a b => gMul_situationOfGradedAlgebra A hcomm hneg hqc U i j a b)

/-- The comparison leaves a homogeneous section where it is. -/
theorem situationSectionRingEquiv_of (U : S.Opens) (k : ℕ)
    (y : (toSheafGradedAlgebra A hcomm hneg hqc).sectionPieces U k) :
    situationSectionRingEquiv A hcomm hneg hqc U (DirectSum.of _ k y) =
      DirectSum.of ((situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U) k y :=
  DirectSum.gradedCongr_of
    (A := fun k : ℕ => (toSheafGradedAlgebra A hcomm hneg hqc).sectionPieces U k)
    (B := fun k : ℕ => (situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U k)
    (fun _ => AddEquiv.refl _) k y

/-- The inverse comparison leaves a homogeneous section where it is. -/
theorem situationSectionRingEquiv_symm_of (U : S.Opens) (k : ℕ)
    (y : (toSheafGradedAlgebra A hcomm hneg hqc).sectionPieces U k) :
    (situationSectionRingEquiv A hcomm hneg hqc U).symm
        (DirectSum.of ((situationOfGradedAlgebra A hcomm hneg hqc).sectionPieces U) k y) =
      DirectSum.of ((toSheafGradedAlgebra A hcomm hneg hqc).sectionPieces U) k y :=
  (situationSectionRingEquiv A hcomm hneg hqc U).symm_apply_eq.mpr
    (situationSectionRingEquiv_of A hcomm hneg hqc U k y).symm

/-! ### Compatibility with the gradings -/

/-- The comparison preserves degrees. -/
theorem situationSectionRingEquiv_mem_grading (U : S.Opens) (k : ℕ)
    {x : (toSheafGradedAlgebra A hcomm hneg hqc).sectionRing U}
    (hx : x ∈ (toSheafGradedAlgebra A hcomm hneg hqc).grading U k) :
    situationSectionRingEquiv A hcomm hneg hqc U x ∈
      (situationOfGradedAlgebra A hcomm hneg hqc).sectionRingGrading U k := by
  obtain ⟨y, rfl⟩ := hx
  rw [situationSectionRingEquiv_of]
  exact ⟨y, rfl⟩

/-- The inverse comparison preserves degrees. -/
theorem situationSectionRingEquiv_symm_mem (U : S.Opens) (k : ℕ)
    {x : (situationOfGradedAlgebra A hcomm hneg hqc).sectionRing U}
    (hx : x ∈ (situationOfGradedAlgebra A hcomm hneg hqc).sectionRingGrading U k) :
    (situationSectionRingEquiv A hcomm hneg hqc U).symm x ∈
      (toSheafGradedAlgebra A hcomm hneg hqc).grading U k := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, (situationSectionRingEquiv_symm_of A hcomm hneg hqc U k y).symm⟩

/-- **The comparison as a homomorphism of graded rings.** -/
def situationSectionGradedHom (U : S.Opens) :
    (toSheafGradedAlgebra A hcomm hneg hqc).grading U →+*ᵍ
      (situationOfGradedAlgebra A hcomm hneg hqc).sectionRingGrading U where
  toRingHom := (situationSectionRingEquiv A hcomm hneg hqc U).toRingHom
  map_mem hx := situationSectionRingEquiv_mem_grading A hcomm hneg hqc U _ hx

/-- **The inverse comparison as a homomorphism of graded rings.** -/
def situationSectionGradedInv (U : S.Opens) :
    (situationOfGradedAlgebra A hcomm hneg hqc).sectionRingGrading U →+*ᵍ
      (toSheafGradedAlgebra A hcomm hneg hqc).grading U where
  toRingHom := (situationSectionRingEquiv A hcomm hneg hqc U).symm.toRingHom
  map_mem hx := situationSectionRingEquiv_symm_mem A hcomm hneg hqc U _ hx

/-- The composite of `situationSectionGradedInv` followed by `situationSectionGradedHom` is the
identity. -/
theorem situationSectionGradedHom_comp_inv (U : S.Opens) :
    (situationSectionGradedHom A hcomm hneg hqc U).comp
        (situationSectionGradedInv A hcomm hneg hqc U) =
      GradedRingHom.id
        ((situationOfGradedAlgebra A hcomm hneg hqc).sectionRingGrading U) :=
  GradedRingHom.ext fun x =>
    (situationSectionRingEquiv A hcomm hneg hqc U).apply_symm_apply x

/-- The composite of `situationSectionGradedHom` followed by `situationSectionGradedInv` is the
identity. -/
theorem situationSectionGradedInv_comp_hom (U : S.Opens) :
    (situationSectionGradedInv A hcomm hneg hqc U).comp
        (situationSectionGradedHom A hcomm hneg hqc U) =
      GradedRingHom.id ((toSheafGradedAlgebra A hcomm hneg hqc).grading U) :=
  GradedRingHom.ext fun x =>
    (situationSectionRingEquiv A hcomm hneg hqc U).symm_apply_apply x

/-! ### The structure map, and naturality in the open -/

/-- **The comparison carries the structure map to the canonical map from the structure sheaf.**
Both send a function to its multiple of the unit section, placed in degree zero. -/
theorem situationSectionRingEquiv_strHom (U : S.Opens) (r : Γ(S, U)) :
    situationSectionRingEquiv A hcomm hneg hqc U
        ((toSheafGradedAlgebra A hcomm hneg hqc).strHom U r) =
      (situationOfGradedAlgebra A hcomm hneg hqc).sectionRingBaseMap U r :=
  (situationSectionRingEquiv_of A hcomm hneg hqc U 0 _).trans
    ((Stacks.RelativeProj.Situation.sectionRingStructure
      (situationOfGradedAlgebra A hcomm hneg hqc)).baseMap_apply U r).symm

/-- **The comparison is natural in the open.** Both restrictions are, on a homogeneous section,
the restriction map of its homogeneous piece. -/
theorem situationSectionRingEquiv_resRingHom {U V : S.Opens} (h : U ≤ V)
    (x : (toSheafGradedAlgebra A hcomm hneg hqc).sectionRing V) :
    situationSectionRingEquiv A hcomm hneg hqc U
        ((toSheafGradedAlgebra A hcomm hneg hqc).resRingHom h x) =
      (situationOfGradedAlgebra A hcomm hneg hqc).sectionRingRestrict U V h
        (situationSectionRingEquiv A hcomm hneg hqc V x) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | of k y =>
      rw [SheafGradedAlgebra.resRingHom_of, situationSectionRingEquiv_of,
        situationSectionRingEquiv_of]
      exact ((Stacks.RelativeProj.Situation.sectionRingStructure
        (situationOfGradedAlgebra A hcomm hneg hqc)).restrict_of U V h k y).symm
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
