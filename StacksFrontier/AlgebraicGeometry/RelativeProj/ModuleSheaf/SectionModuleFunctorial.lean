module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.SectionModule

/-!
# Functoriality of the graded module of local sections

A homomorphism of graded modules over the sheaf of graded algebras of a relative `Proj` situation
is a morphism of sheaves of modules in each degree, compatible with the action. Over an open of
the base it therefore induces a map of the graded modules of local sections of
`StacksFrontier/AlgebraicGeometry/RelativeProj/ModuleSheaf/SectionModule.lean`, degreewise and hence
degree-preserving, linear over the graded ring of sections of the algebra — *not* merely
semilinear, because the ring of scalars does not move — and compatible with restriction to a
smaller open.

Everything is proved by the induction on the direct sum that
`Stacks.RelativeProj.Situation.sectionModuleRestrict_smul` uses: a statement about the module of
sections is reduced to the homogeneous summands, where the module structure is the homogeneous
action of the sheaf-level datum and the map is the degree-`n` component of the homomorphism.

## Main definitions

* `Stacks.RelativeProj.Situation.sectionModuleMapPiece`: the degree-`n` component on sections.
* `Stacks.RelativeProj.Situation.sectionModuleMap`: **the induced map of the graded modules of
  local sections**, as an additive map.
* `Stacks.RelativeProj.Situation.sectionModuleMapₗ`: the same, linear over the graded ring of
  sections of the algebra.

## Main results

* `Stacks.RelativeProj.Situation.sectionModuleMap_mem_grading`: **the induced map preserves the
  internal grading.**
* `Stacks.RelativeProj.Situation.sectionModuleMap_smul`: **it is linear over the graded ring of
  sections.**
* `Stacks.RelativeProj.Situation.sectionModuleMap_restrict`: **it commutes with restriction to a
  smaller open of the base.**
* `Stacks.RelativeProj.Situation.sectionModuleMap_id` and
  `Stacks.RelativeProj.Situation.sectionModuleMap_comp`: it is functorial.

## Implementation notes

The degree index of the algebra is a natural number and that of the module an integer, and the
homogeneous action of the sheaf-level datum takes two integer degrees. The induction over the
graded ring of sections therefore produces the degree `((i : ℕ) : ℤ) + j`, which is the degree at
which `SheafOfModules.LeftGradedModule.Hom.map_smul` is stated; no cast lemma is needed, the two
spellings being definitionally equal.

`Stacks.RelativeProj.Situation.sectionModuleDecomposition` is a `def` rather than an instance, so
the statements below are phrased with `sectionModuleGrading` and the plain module structure and do
not need it; a consumer that wants the grading as a `DirectSum.Decomposition` installs it locally,
as the construction of the glued sheaf does.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} {ℳ 𝒩 𝒬 : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}

section Sections

variable (f : ℳ ⟶ 𝒩) (U : s.base.Opens)

/-- The degree-`n` component on sections of a homomorphism of graded modules: the degree-`n`
morphism of sheaves of modules, read on sections over an open of the base. -/
public noncomputable def sectionModuleMapPiece (n : ℤ) :
    sectionModulePieces ℳ U n →+ sectionModulePieces 𝒩 U n where
  toFun x := (f.app n).val.app (op U) x
  map_zero' := map_zero _
  map_add' := map_add _

/-- The degree-`n` component on sections is the degree-`n` morphism read on sections over `U`. -/
public theorem sectionModuleMapPiece_apply (n : ℤ) (x : sectionModulePieces ℳ U n) :
    sectionModuleMapPiece f U n x = (f.app n).val.app (op U) x := rfl

/-- **The map of the graded modules of local sections induced by a homomorphism of graded
modules**, as an additive map: the degree-`n` component on the degree-`n` summand. -/
public noncomputable def sectionModuleMap : sectionModule ℳ U →+ sectionModule 𝒩 U :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (sectionModulePieces 𝒩 U) n).comp (sectionModuleMapPiece f U n)

/-- On the degree-`n` summand the induced map is the degree-`n` component on sections. -/
public theorem sectionModuleMap_of {n : ℤ} (x : sectionModulePieces ℳ U n) :
    sectionModuleMap f U (DirectSum.of (sectionModulePieces ℳ U) n x) =
      DirectSum.of (sectionModulePieces 𝒩 U) n (sectionModuleMapPiece f U n x) :=
  DirectSum.toAddMonoid_of _ n x

/-- **The induced map preserves the internal grading**, being degreewise. -/
public theorem sectionModuleMap_mem_grading {n : ℤ} {z : sectionModule ℳ U}
    (hz : z ∈ sectionModuleGrading ℳ U n) :
    sectionModuleMap f U z ∈ sectionModuleGrading 𝒩 U n := by
  obtain ⟨x, rfl⟩ := hz
  exact ⟨_, (sectionModuleMap_of f U x).symm⟩

/-- On the degree-`n` summand the induced map is the degree-`n` morphism read on sections. -/
private theorem sectionModuleMap_of_apply (f : ℳ ⟶ 𝒩) (U : s.base.Opens) {n : ℤ}
    (x : sectionModulePieces ℳ U n) :
    sectionModuleMap f U (DirectSum.of (sectionModulePieces ℳ U) n x) =
      DirectSum.of (sectionModulePieces 𝒩 U) n ((f.app n).val.app (op U) x) :=
  sectionModuleMap_of f U x

/-- **The induced map is linear over the graded ring of sections of the algebra.** On the
homogeneous summands this is the compatibility of the homomorphism with the homogeneous action. -/
public theorem sectionModuleMap_smul (w : s.sectionRing U) (z : sectionModule ℳ U) :
    sectionModuleMap f U (w • z) = w • sectionModuleMap f U z := by
  induction w using DirectSum.induction_on with
  | zero => rw [zero_smul, map_zero, zero_smul]
  | of i a =>
    induction z using DirectSum.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | of j x =>
      refine ((congrArg (sectionModuleMap f U) (sectionModule_of_smul_of ℳ U a x)).trans
        ((sectionModuleMap_of f U (ℳ.smul (i : ℤ) j (op U) a x)).trans
          ((congrArg (DirectSum.of (sectionModulePieces 𝒩 U) ((i : ℤ) + j))
            (f.map_smul (i : ℤ) j (op U) a x)).trans
            (sectionModule_of_smul_of 𝒩 U a ((f.app j).val.app (op U) x)).symm))).trans ?_
      exact congrArg (fun y => DirectSum.of (s.sectionPieces U) i a • y)
        (sectionModuleMap_of f U x).symm
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | add w w' hw hw' => rw [add_smul, map_add, hw, hw', add_smul]

/-- **The map of the graded modules of local sections induced by a homomorphism of graded
modules**, as a linear map over the graded ring of sections of the algebra. -/
public noncomputable def sectionModuleMapₗ :
    sectionModule ℳ U →ₗ[s.sectionRing U] sectionModule 𝒩 U where
  toFun := sectionModuleMap f U
  map_add' := map_add _
  map_smul' := sectionModuleMap_smul f U

/-- The linear form of the induced map agrees with the additive one. -/
public theorem sectionModuleMapₗ_apply (z : sectionModule ℳ U) :
    sectionModuleMapₗ f U z = sectionModuleMap f U z := rfl

/-- The linear form of the induced map preserves the internal grading. -/
public theorem sectionModuleMapₗ_mem_grading (n : ℤ) (z : sectionModule ℳ U)
    (hz : z ∈ sectionModuleGrading ℳ U n) :
    sectionModuleMapₗ f U z ∈ sectionModuleGrading 𝒩 U n :=
  sectionModuleMap_mem_grading f U hz

end Sections

/-- **The induced map commutes with restriction to a smaller open of the base.** On the
homogeneous summands this is the naturality of the degree-`n` morphism of sheaves of modules. -/
public theorem sectionModuleMap_restrict (f : ℳ ⟶ 𝒩) {U V : s.base.Opens} (h : U ≤ V)
    (z : sectionModule ℳ V) :
    sectionModuleMap f U (sectionModuleRestrict ℳ h z) =
      sectionModuleRestrict 𝒩 h (sectionModuleMap f V z) := by
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | of n x =>
    rw [sectionModuleRestrict_of ℳ h x, sectionModuleMap_of_apply, sectionModuleMap_of_apply,
      sectionModuleRestrict_of 𝒩 h]
    refine congrArg (DirectSum.of (sectionModulePieces 𝒩 U) n) ?_
    rw [sectionModuleRestrictPiece_apply, sectionModuleRestrictPiece_apply]
    exact PresheafOfModules.naturality_apply (f.app n).val (homOfLE h).op x
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]

/-- The identity homomorphism induces the identity on the graded modules of local sections. -/
public theorem sectionModuleMap_id (U : s.base.Opens) :
    sectionModuleMap (𝟙 ℳ) U = AddMonoidHom.id (sectionModule ℳ U) := by
  refine DirectSum.addHom_ext fun n x => ?_
  rw [sectionModuleMap_of_apply, AddMonoidHom.id_apply]
  rfl

/-- The induced maps compose. -/
public theorem sectionModuleMap_comp (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ 𝒬) (U : s.base.Opens) :
    sectionModuleMap (f ≫ g) U =
      (sectionModuleMap g U).comp (sectionModuleMap f U) := by
  refine DirectSum.addHom_ext fun n x => ?_
  rw [sectionModuleMap_of_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    sectionModuleMap_of_apply, sectionModuleMap_of_apply]
  rfl

end Stacks.RelativeProj.Situation

end
