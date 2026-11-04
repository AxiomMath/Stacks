module

public import Mathlib.Algebra.Module.GradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjSectionRings
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps

/-!
# The graded module of local sections of a graded module on a relative `Proj` situation

Let `s` be a relative `Proj` situation: a scheme together with a quasi-coherent, commutative,
nonnegatively graded algebra `𝒜` over its structure sheaf. A graded module over that algebra is
a family of sheaves of modules indexed by `ℤ` with a unital, associative action of the
homogeneous local sections of `𝒜` adding degrees, which is `SheafOfModules.LeftGradedModule`
over `Stacks.RelativeProj.Situation.algebra`.

This file builds, for every open `U` of the base, the graded module of local sections of such a
module over `U`: the external direct sum

`⨁ n : ℤ, Γ(ℳ.piece n, U)`,

its internal grading by additive subgroups, its module structure over the graded ring of sections
`s.sectionRing U`, and the restriction maps along an inclusion of opens, semilinear over the
restriction of the section rings.

## Main definitions

* `Stacks.RelativeProj.Situation.sectionModulePieces`: the homogeneous sections of degree `n`
  over an open.
* `Stacks.RelativeProj.Situation.sectionModule`: their direct sum, `⨁ n : ℤ, Γ(ℳ.piece n, U)`.
* `Stacks.RelativeProj.Situation.sectionModuleGrading`: the internal grading, by the ranges of
  the inclusions of the homogeneous summands.
* `Stacks.RelativeProj.Situation.sectionModuleRestrictPiece`,
  `Stacks.RelativeProj.Situation.sectionModuleRestrict` and
  `Stacks.RelativeProj.Situation.sectionModuleRestrictₛₗ`: restriction of homogeneous sections
  along an inclusion of opens, restriction of the graded modules of sections as an additive map,
  and the same as a semilinear map over `Stacks.RelativeProj.Situation.sectionRingRestrict`.

## Main results

* `Stacks.RelativeProj.Situation.sectionModuleGmodule` and
  `Stacks.RelativeProj.Situation.sectionModuleModule`: the homogeneous sections form a graded
  module over the homogeneous sections of the algebra, hence their direct sum is a module over
  the graded ring of sections.
* `Stacks.RelativeProj.Situation.sectionModule_of_smul_of`: the action on the homogeneous
  summands is the action of the sheaf-level datum.
* `Stacks.RelativeProj.Situation.sectionModuleDecomposition`: the module of sections is the
  direct sum of its homogeneous parts.
* `Stacks.RelativeProj.Situation.sectionModuleGradedSMul`: the action of the section ring
  respects the two internal gradings.
* `Stacks.RelativeProj.Situation.sectionModuleRestrict_smul`: restriction is semilinear over
  `Stacks.RelativeProj.Situation.sectionRingRestrict`.
* `Stacks.RelativeProj.Situation.sectionModuleRestrict_id` and `sectionModuleRestrict_comp`:
  restriction is functorial.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum
open scoped Stacks.GradedLocalization

universe u

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule s.algebra)

section Sections

variable (U : s.base.Opens)

/-- The degree-`n` homogeneous sections of a graded module over an open of the base. -/
public abbrev sectionModulePieces (n : ℤ) : Type u := (ℳ.piece n).val.obj (op U)

/-- The graded module of local sections of a graded module over an open of the base: the direct
sum of the homogeneous pieces, over all integer degrees. -/
public abbrev sectionModule : Type u := ⨁ n : ℤ, sectionModulePieces ℳ U n

/-! ### The action of the graded ring of sections -/

/-- The homogeneous action of the sections of the algebra on the sections of the module: a
degree-`i` section acts from degree `j` to degree `i + j` by the sheaf-level action. -/
public noncomputable instance sectionModuleGSMul :
    GradedMonoid.GSMul (s.sectionPieces U) (sectionModulePieces ℳ U) :=
  ⟨fun {i j} a x => ℳ.smul (i : ℤ) j (op U) a x⟩

/-- The homogeneous action is the action `ℳ.smul` of the sheaf-level datum. -/
public theorem sectionModuleGSMul_def {i : ℕ} {j : ℤ} (a : s.sectionPieces U i)
    (x : sectionModulePieces ℳ U j) :
    (GradedMonoid.GSMul.smul a x : sectionModulePieces ℳ U (i +ᵥ j)) =
      ℳ.smul (i : ℤ) j (op U) a x := rfl

/-- The product of two homogeneous sections of the algebra is their product in the sheaf-level
algebra. -/
public theorem sectionPieces_mul_eq {i j : ℕ} (a : s.sectionPieces U i)
    (b : s.sectionPieces U j) :
    GradedMonoid.GMul.mul a b = (s.algebra.mul (i : ℤ) (j : ℤ)).app (op U) a b :=
  eq_of_heq ((sectionRingStructure s).mul_homogeneous U i j a b)

/-- **The homogeneous local sections of a graded module form a graded module over the homogeneous
local sections of the algebra.** -/
public noncomputable instance sectionModuleGmodule :
    DirectSum.Gmodule (s.sectionPieces U) (sectionModulePieces ℳ U) :=
  { sectionModuleGSMul ℳ U with
    one_smul := fun x => Sigma.ext (Int.zero_add x.1) (by
      change ℳ.smul ((0 : ℕ) : ℤ) x.1 (op U)
          (GradedMonoid.GOne.one : s.sectionPieces U 0) x.2 ≍ x.2
      rw [(sectionRingStructure s).one_homogeneous U]
      exact ℳ.one_smul x.1 (op U) x.2)
    mul_smul := fun a a' x =>
      Sigma.ext (show ((a.1 + a'.1 : ℕ) : ℤ) + x.1 = (a.1 : ℤ) + ((a'.1 : ℤ) + x.1) by
        push_cast; ring) (by
      change ℳ.smul ((a.1 + a'.1 : ℕ) : ℤ) x.1 (op U)
          (GradedMonoid.GMul.mul a.2 a'.2) x.2 ≍
        ℳ.smul (a.1 : ℤ) ((a'.1 : ℤ) + x.1) (op U) a.2
          (ℳ.smul (a'.1 : ℤ) x.1 (op U) a'.2 x.2)
      rw [sectionPieces_mul_eq]
      exact ℳ.mul_smul (a.1 : ℤ) (a'.1 : ℤ) x.1 (op U) a.2 a'.2 x.2)
    smul_add := fun _ _ _ => map_add _ _ _
    smul_zero := fun _ => map_zero _
    add_smul := fun _ _ _ => by rw [sectionModuleGSMul_def, map_add]; rfl
    zero_smul := fun _ => by rw [sectionModuleGSMul_def, map_zero]; rfl }

/-- **The graded module of local sections over an open is a module over the graded ring of
sections over that open.** -/
public noncomputable instance sectionModuleModule :
    Module (s.sectionRing U) (sectionModule ℳ U) :=
  inferInstance

/-- **The action on the homogeneous summands is the homogeneous action of the sheaf-level
datum.** -/
public theorem sectionModule_of_smul_of {i : ℕ} {j : ℤ} (a : s.sectionPieces U i)
    (x : sectionModulePieces ℳ U j) :
    DirectSum.of (s.sectionPieces U) i a • DirectSum.of (sectionModulePieces ℳ U) j x =
      DirectSum.of (sectionModulePieces ℳ U) ((i : ℤ) + j) (ℳ.smul (i : ℤ) j (op U) a x) :=
  DirectSum.Gmodule.of_smul_of _ _ a x

/-! ### The internal grading -/

/-- The degree-`n` part of the module of local sections, as an additive subgroup: the range of
the inclusion of the degree-`n` summand. -/
public noncomputable abbrev sectionModuleGrading (n : ℤ) : AddSubgroup (sectionModule ℳ U) :=
  (DirectSum.of (sectionModulePieces ℳ U) n).range

/-- A homogeneous section of degree `n` lies in the degree-`n` part of the module of sections. -/
public theorem mem_sectionModuleGrading_of {n : ℤ} (x : sectionModulePieces ℳ U n) :
    DirectSum.of (sectionModulePieces ℳ U) n x ∈ sectionModuleGrading ℳ U n := ⟨x, rfl⟩

/-- An element of the module of sections lies in the degree-`n` part exactly when it is the image
of a homogeneous section of degree `n`. -/
public theorem mem_sectionModuleGrading_iff {n : ℤ} (z : sectionModule ℳ U) :
    z ∈ sectionModuleGrading ℳ U n ↔
      ∃ x, DirectSum.of (sectionModulePieces ℳ U) n x = z := Iff.rfl

/-- The module of local sections is the direct sum of its homogeneous parts. -/
@[instance_reducible]
public noncomputable def sectionModuleDecomposition :
    DirectSum.Decomposition (sectionModuleGrading ℳ U) := by
  let d : sectionModule ℳ U →+ ⨁ n : ℤ, sectionModuleGrading ℳ U n :=
    DirectSum.toAddMonoid fun n =>
      (DirectSum.of (fun n => sectionModuleGrading ℳ U n) n).comp
        (DirectSum.of (sectionModulePieces ℳ U) n).rangeRestrict
  refine DirectSum.Decomposition.ofAddHom _ d ?_ ?_
  · exact DirectSum.addHom_ext fun n x => by simp [d]
  · apply DirectSum.addHom_ext
    rintro n ⟨_, a, rfl⟩
    simp [d]
    rfl

/-- **The action of the graded ring of sections respects the two internal gradings**: a
degree-`i` section of the algebra carries the degree-`j` part of the module of sections into its
degree-`i + j` part. -/
public instance sectionModuleGradedSMul :
    SetLike.GradedSMul (s.sectionRingGrading U) (sectionModuleGrading ℳ U) where
  smul_mem := by
    rintro i j a x ⟨a, rfl⟩ ⟨x, rfl⟩
    exact ⟨_, (DirectSum.Gmodule.of_smul_of _ _ a x).symm⟩

end Sections

/-! ### Restriction -/

section Restriction

variable {U V : s.base.Opens}

/-- Restriction of homogeneous sections of degree `n` along an inclusion of opens. -/
public noncomputable def sectionModuleRestrictPiece (h : U ≤ V) (n : ℤ) :
    sectionModulePieces ℳ V n →+ sectionModulePieces ℳ U n where
  toFun := (ℳ.piece n).val.map (homOfLE h).op
  map_zero' := map_zero _
  map_add' := map_add _

/-- Restriction of a homogeneous section is the restriction map of the degree-`n` piece. -/
public theorem sectionModuleRestrictPiece_apply (h : U ≤ V) (n : ℤ)
    (x : sectionModulePieces ℳ V n) :
    sectionModuleRestrictPiece ℳ h n x = (ℳ.piece n).val.map (homOfLE h).op x := rfl

/-- Restriction of the graded modules of local sections along an inclusion of opens, as an
additive map. -/
public noncomputable def sectionModuleRestrict (h : U ≤ V) :
    sectionModule ℳ V →+ sectionModule ℳ U :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (sectionModulePieces ℳ U) n).comp (sectionModuleRestrictPiece ℳ h n)

/-- Restriction of the module of sections on a homogeneous summand is restriction of the
homogeneous section. -/
public theorem sectionModuleRestrict_of (h : U ≤ V) {n : ℤ} (x : sectionModulePieces ℳ V n) :
    sectionModuleRestrict ℳ h (DirectSum.of (sectionModulePieces ℳ V) n x) =
      DirectSum.of (sectionModulePieces ℳ U) n (sectionModuleRestrictPiece ℳ h n x) :=
  DirectSum.toAddMonoid_of _ n x

/-- Restriction preserves the internal grading. -/
public theorem sectionModuleRestrict_mem_grading (h : U ≤ V) {n : ℤ}
    {z : sectionModule ℳ V} (hz : z ∈ sectionModuleGrading ℳ V n) :
    sectionModuleRestrict ℳ h z ∈ sectionModuleGrading ℳ U n := by
  obtain ⟨x, rfl⟩ := hz
  exact ⟨_, (sectionModuleRestrict_of ℳ h x).symm⟩

/-- **Restriction of the graded modules of local sections is semilinear over restriction of the
graded rings of sections.** -/
public theorem sectionModuleRestrict_smul (h : U ≤ V) (w : s.sectionRing V)
    (z : sectionModule ℳ V) :
    sectionModuleRestrict ℳ h (w • z) =
      s.sectionRingRestrict U V h w • sectionModuleRestrict ℳ h z := by
  induction w using DirectSum.induction_on with
  | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
  | of i a =>
    induction z using DirectSum.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | of j x =>
      refine ((congrArg (sectionModuleRestrict ℳ h)
        (sectionModule_of_smul_of ℳ V a x)).trans
        ((sectionModuleRestrict_of ℳ h (ℳ.smul (i : ℤ) j (op V) a x)).trans
          ((congrArg (DirectSum.of (sectionModulePieces ℳ U) ((i : ℤ) + j))
            (ℳ.smul_naturality (i : ℤ) j (homOfLE h).op a x)).trans
            (sectionModule_of_smul_of ℳ U _ _).symm))).trans ?_
      exact congrArg₂ (· • ·) ((sectionRingStructure s).restrict_of U V h i a).symm
        (sectionModuleRestrict_of ℳ h x).symm
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | add w w' hw hw' => rw [add_smul, map_add, hw, hw', map_add, add_smul]

/-- Restriction of the graded modules of local sections, as a semilinear map over the restriction
`Stacks.RelativeProj.Situation.sectionRingRestrict` of the graded rings of sections. -/
public noncomputable def sectionModuleRestrictₛₗ (h : U ≤ V) :
    sectionModule ℳ V →ₛₗ[s.sectionRingRestrict U V h] sectionModule ℳ U where
  toFun := sectionModuleRestrict ℳ h
  map_add' := map_add _
  map_smul' := sectionModuleRestrict_smul ℳ h

/-- The semilinear restriction map is the additive restriction map. -/
public theorem sectionModuleRestrictₛₗ_apply (h : U ≤ V) (z : sectionModule ℳ V) :
    sectionModuleRestrictₛₗ ℳ h z = sectionModuleRestrict ℳ h z := rfl

end Restriction

/-- Restriction along the identity is the identity. -/
public theorem sectionModuleRestrict_id (U : s.base.Opens) :
    sectionModuleRestrict ℳ (le_refl U) = AddMonoidHom.id (sectionModule ℳ U) := by
  refine DirectSum.addHom_ext fun n x => ?_
  rw [sectionModuleRestrict_of ℳ, AddMonoidHom.id_apply, sectionModuleRestrictPiece_apply ℳ,
    show (homOfLE (le_refl U)).op = 𝟙 (op U) from rfl]
  simp

/-- Restriction is functorial. -/
public theorem sectionModuleRestrict_comp {U V W : s.base.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    sectionModuleRestrict ℳ (hUV.trans hVW) =
      (sectionModuleRestrict ℳ hUV).comp (sectionModuleRestrict ℳ hVW) := by
  refine DirectSum.addHom_ext fun n x => ?_
  rw [sectionModuleRestrict_of ℳ, AddMonoidHom.coe_comp, Function.comp_apply,
    sectionModuleRestrict_of ℳ, sectionModuleRestrict_of ℳ]
  congr 1
  rw [sectionModuleRestrictPiece_apply ℳ, sectionModuleRestrictPiece_apply ℳ,
    sectionModuleRestrictPiece_apply ℳ, ← PresheafOfModules.map_comp_apply]
  rfl

end Stacks.RelativeProj.Situation

end
