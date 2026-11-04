module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.SectionModule
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeFunctorial

/-!
# The graded modules of sections of a relative `Proj` situation base-change along a morphism

`Stacks.RelativeProj.Situation.sectionRingBaseChange` base-changes the graded *ring* of sections
of the algebra of a relative `Proj` situation along a morphism `g : S' ⟶ S` of base schemes, for
a pair of affine opens `W ⊆ S`, `W' ⊆ g⁻¹W`. This file does the same for the graded *module* of
sections of a graded module `ℳ` over the algebra.

The identification of `ℳ'` with the pullback of `ℳ` is taken as a degreewise family of morphisms
`Ψ n : g^*(ℳ_n) ⟶ ℳ'_n` of sheaves of modules on `S'`, together with the compatibility of that
family with the two module actions. No pullback of a sheaf of graded modules is used, because the
library has none: `Stacks.Conormal.gradedPullback` pulls back a sheaf of graded *algebras* and
there is no module companion, so the datum is supplied degreewise, exactly as `Φ` is supplied as
a unital homomorphism out of the pulled-back algebra rather than produced by an operation on
graded modules.

The result is the semilinear map

  `ℳ(W) ⟶ ℳ'(W')` over `𝒜(W) ⟶ 𝒜'(W')`

of graded modules of sections, which is the datum
`Stacks.ProjModuleComparison.moduleMap` consumes: it is what makes a comparison morphism of the
sheaves attached to `ℳ` and `ℳ'` on the charts of the two relative projective spectra exist at
all.

## Main definitions

* `Stacks.RelativeProj.Situation.pieceSectionModuleHom` is the degree-`n` component: pull a
  homogeneous section of `ℳ` back along `g` and read it through the identification of `ℳ'` with
  the pullback of `ℳ`.
* `Stacks.RelativeProj.Situation.sectionModuleBaseChangeAddHom` is the induced additive map of
  the graded modules of sections, and
  `Stacks.RelativeProj.Situation.sectionModuleBaseChangeₛₗ` is the same as a map semilinear over
  `Stacks.RelativeProj.Situation.sectionRingBaseChange`.

## Main results

* `Stacks.RelativeProj.Situation.sectionModuleBaseChange_smul`: the induced map is semilinear
  over the base change of the section rings. On the homogeneous summands this is the
  compatibility of the degreewise datum with the two actions.
* `Stacks.RelativeProj.Situation.sectionModuleBaseChange_mem_grading`: the induced map preserves
  the internal grading.
* `Stacks.RelativeProj.Situation.pieceSectionModuleHom_target_le` and
  `pieceSectionModuleHom_source_le`: the degreewise components are functorial in each of the two
  opens.
* `Stacks.RelativeProj.Situation.sectionModuleBaseChange_sectionModuleRestrict` and
  `sectionModuleRestrict_sectionModuleBaseChange`: the induced map of the graded modules of
  sections is functorial in each of the two opens.

## Implementation notes

The degree index of the module is `ℤ` and that of the ring is `ℕ`, so the action of a degree-`i`
section of the algebra on a degree-`n` section of the module lands in degree `(i : ℤ) + n`. The
semilinearity proof is a double induction over the two direct sums whose homogeneous case is
`Stacks.RelativeProj.Situation.sectionModule_of_smul_of` on each side with the degreewise datum
in between; no cast between the two index types appears, because the ring index enters only
through the coercion `(i : ℤ)` that `sectionModule_of_smul_of` already produces.

The functoriality in each open is the functoriality of
`AlgebraicGeometry.Scheme.Modules.pullbackSection` in the two opens, exactly as for the algebra:
in the open of `S` the open appears only inside the pulled-back section, and in the open of `S'`
it is the shrinking of a pulled-back section together with naturality of `Ψ n`.

No `@[stacks]` attribute is attached: what is constructed is the semilinear map of graded modules
of sections that a comparison of module sheaves is built from, which is data and not an assertion
of any tag.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum

universe u

namespace Stacks.RelativeProj.Situation

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)
  {ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}
  {ℳ' : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s'.algebra}
  (Ψ : ∀ n : ℤ, (Scheme.Modules.pullback g).obj (ℳ.piece n) ⟶ ℳ'.piece n)

/-! ### The degreewise components -/

/-- **The degree-`n` component of the base change of the graded modules of sections.** A
homogeneous section of `ℳ` over `W` is pulled back along `g` to `W'` and read through the
identification of `ℳ'` with the pullback of `ℳ`. -/
public def pieceSectionModuleHom (n : ℤ) (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) : sectionModulePieces ℳ W n →+ sectionModulePieces ℳ' W' n :=
  ((Ψ n).val.app (op W')).hom.toAddMonoidHom.comp
    ((((Scheme.Modules.pullback g).obj (ℳ.piece n)).val.map
          (homOfLE h).op).hom.toAddMonoidHom.comp
      ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (ℳ.piece n)).val.app (op W)).hom.toAddMonoidHom))

public theorem pieceSectionModuleHom_apply (n : ℤ) (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (x : sectionModulePieces ℳ W n) :
    pieceSectionModuleHom g Ψ n W W' h x =
      (Ψ n).val.app (op W')
        (Scheme.Modules.pullbackSection g (ℳ.piece n) W W' h x) := rfl

/-- **The degreewise components are functorial in the open of `S`.** Restricting a homogeneous
section of `ℳ` from `W₂` to `W₁` and then base-changing to `W'` is base-changing from `W₂`
directly. The open of `S` appears only inside the pulled-back section. -/
public theorem pieceSectionModuleHom_target_le (n : ℤ) {W₁ W₂ : s.base.Opens} (h₁₂ : W₁ ≤ W₂)
    (W' : s'.base.Opens) (h₁ : W' ≤ g ⁻¹ᵁ W₁) (h₂ : W' ≤ g ⁻¹ᵁ W₂)
    (x : sectionModulePieces ℳ W₂ n) :
    pieceSectionModuleHom g Ψ n W₁ W' h₁ ((ℳ.piece n).val.map (homOfLE h₁₂).op x)
      = pieceSectionModuleHom g Ψ n W₂ W' h₂ x :=
  (pieceSectionModuleHom_apply g Ψ n W₁ W' h₁ _).trans
    ((congrArg (fun z => (Ψ n).val.app (op W') z)
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_target_le g
          (ℳ.piece n) h₁₂ W' h₂ h₁ x)).trans
      (pieceSectionModuleHom_apply g Ψ n W₂ W' h₂ x).symm)

/-- **The degreewise components are functorial in the open of `S'`.** Base-changing to `W₂'` and
then restricting to `W₁'` is base-changing to `W₁'` directly: the shrinking of a pulled-back
section, together with naturality of `Ψ n`. -/
public theorem pieceSectionModuleHom_source_le (n : ℤ) (W : s.base.Opens)
    {W₁' W₂' : s'.base.Opens} (h' : W₁' ≤ W₂') (h₂ : W₂' ≤ g ⁻¹ᵁ W) (h₁ : W₁' ≤ g ⁻¹ᵁ W)
    (x : sectionModulePieces ℳ W n) :
    (ℳ'.piece n).val.map (homOfLE h').op (pieceSectionModuleHom g Ψ n W W₂' h₂ x)
      = pieceSectionModuleHom g Ψ n W W₁' h₁ x := by
  refine Eq.trans ?_ (pieceSectionModuleHom_apply g Ψ n W W₁' h₁ x).symm
  refine Eq.trans (congrArg ((ℳ'.piece n).val.map (homOfLE h').op)
    (pieceSectionModuleHom_apply g Ψ n W W₂' h₂ x)) ?_
  refine ((PresheafOfModules.naturality_apply (Ψ n).val (homOfLE h').op
    (Scheme.Modules.pullbackSection g (ℳ.piece n) W W₂' h₂ x)).symm).trans ?_
  exact congrArg (fun z => (Ψ n).val.app (op W₁') z)
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink g
      (ℳ.piece n) W W₂' W₁' h₂ h' h₁ x)

/-! ### The base change of the graded modules of sections -/

/-- The base change of the graded modules of sections, additively. -/
public def sectionModuleBaseChangeAddHom (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) : sectionModule ℳ W →+ sectionModule ℳ' W' :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (sectionModulePieces ℳ' W') n).comp (pieceSectionModuleHom g Ψ n W W' h)

@[simp] public theorem sectionModuleBaseChangeAddHom_of (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (n : ℤ) (x : sectionModulePieces ℳ W n) :
    sectionModuleBaseChangeAddHom g Ψ W W' h (DirectSum.of (sectionModulePieces ℳ W) n x) =
      DirectSum.of (sectionModulePieces ℳ' W') n (pieceSectionModuleHom g Ψ n W W' h x) :=
  DirectSum.toAddMonoid_of _ n x

/-- The base change preserves the internal grading. -/
public theorem sectionModuleBaseChange_mem_grading (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (n : ℤ) {z : sectionModule ℳ W}
    (hz : z ∈ sectionModuleGrading ℳ W n) :
    sectionModuleBaseChangeAddHom g Ψ W W' h z ∈ sectionModuleGrading ℳ' W' n := by
  obtain ⟨x, rfl⟩ := hz
  exact ⟨_, (sectionModuleBaseChangeAddHom_of g Ψ W W' h n x).symm⟩

variable (hΨ : ∀ (i : ℕ) (n : ℤ) (W : s.base.Opens) (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W)
  (a : s.sectionPieces W i) (x : sectionModulePieces ℳ W n),
  pieceSectionModuleHom g Ψ ((i : ℤ) + n) W W' h (ℳ.smul (i : ℤ) n (op W) a x)
    = ℳ'.smul (i : ℤ) n (op W') (pieceSectionHom g Φ i W W' h a)
        (pieceSectionModuleHom g Ψ n W W' h x))

include hΨ in
/-- **The base change of the graded modules of sections is semilinear over the base change of the
graded rings of sections.** On the homogeneous summands this is the compatibility of the
degreewise datum with the two module actions. -/
public theorem sectionModuleBaseChange_smul (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (w : s.sectionRing W) (z : sectionModule ℳ W) :
    sectionModuleBaseChangeAddHom g Ψ W W' h (w • z) =
      sectionRingBaseChange g Φ W W' h w • sectionModuleBaseChangeAddHom g Ψ W W' h z := by
  induction w using DirectSum.induction_on with
  | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
  | of i a =>
    induction z using DirectSum.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | of j x =>
      rw [sectionModule_of_smul_of ℳ W a x, sectionModuleBaseChangeAddHom_of,
        sectionRingBaseChange_of, sectionModuleBaseChangeAddHom_of,
        sectionModule_of_smul_of ℳ' W' _ _]
      exact congrArg (DirectSum.of (sectionModulePieces ℳ' W') ((i : ℤ) + j))
        (hΨ i j W W' h a x)
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | add w w' hw hw' => rw [add_smul, map_add, hw, hw', map_add, add_smul]

include hΨ in
/-- **The base change of the graded modules of sections**, as a map semilinear over
`Stacks.RelativeProj.Situation.sectionRingBaseChange`. This is the datum
`Stacks.ProjModuleComparison.moduleMap` consumes. -/
public def sectionModuleBaseChangeₛₗ (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) :
    sectionModule ℳ W →ₛₗ[sectionRingBaseChange g Φ W W' h] sectionModule ℳ' W' where
  toFun := sectionModuleBaseChangeAddHom g Ψ W W' h
  map_add' := map_add _
  map_smul' := sectionModuleBaseChange_smul g Φ Ψ hΨ W W' h

include hΨ in
public theorem sectionModuleBaseChangeₛₗ_apply (W : s.base.Opens) (W' : s'.base.Opens)
    (h : W' ≤ g ⁻¹ᵁ W) (z : sectionModule ℳ W) :
    sectionModuleBaseChangeₛₗ g Φ Ψ hΨ W W' h z =
      sectionModuleBaseChangeAddHom g Ψ W W' h z := rfl

/-! ### Functoriality in the two opens -/

/-- **Functoriality in the open of `S`.** Restricting the graded module of sections from `W₂` to
`W₁` and then base-changing to `W'` is base-changing from `W₂` directly. -/
public theorem sectionModuleBaseChange_sectionModuleRestrict {W₁ W₂ : s.base.Opens}
    (h₁₂ : W₁ ≤ W₂) (W' : s'.base.Opens) (h₁ : W' ≤ g ⁻¹ᵁ W₁) (h₂ : W' ≤ g ⁻¹ᵁ W₂)
    (z : sectionModule ℳ W₂) :
    sectionModuleBaseChangeAddHom g Ψ W₁ W' h₁ (sectionModuleRestrict ℳ h₁₂ z)
      = sectionModuleBaseChangeAddHom g Ψ W₂ W' h₂ z := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext (f := (sectionModuleBaseChangeAddHom g Ψ W₁ W'
    h₁).comp (sectionModuleRestrict ℳ h₁₂)) fun n x => ?_) z
  rw [AddMonoidHom.comp_apply, sectionModuleRestrict_of ℳ h₁₂, sectionModuleBaseChangeAddHom_of,
    sectionModuleBaseChangeAddHom_of, sectionModuleRestrictPiece_apply]
  exact congrArg (DirectSum.of (sectionModulePieces ℳ' W') n)
    (pieceSectionModuleHom_target_le g Ψ n h₁₂ W' h₁ h₂ x)

/-- **Functoriality in the open of `S'`.** Base-changing to `W₂'` and then restricting the graded
module of sections to `W₁'` is base-changing to `W₁'` directly. -/
public theorem sectionModuleRestrict_sectionModuleBaseChange (W : s.base.Opens)
    {W₁' W₂' : s'.base.Opens} (h' : W₁' ≤ W₂') (h₂ : W₂' ≤ g ⁻¹ᵁ W) (h₁ : W₁' ≤ g ⁻¹ᵁ W)
    (z : sectionModule ℳ W) :
    sectionModuleRestrict ℳ' h' (sectionModuleBaseChangeAddHom g Ψ W W₂' h₂ z)
      = sectionModuleBaseChangeAddHom g Ψ W W₁' h₁ z := by
  refine DFunLike.congr_fun (DirectSum.addHom_ext (f := (sectionModuleRestrict ℳ' h').comp
    (sectionModuleBaseChangeAddHom g Ψ W W₂' h₂)) fun n x => ?_) z
  rw [AddMonoidHom.comp_apply, sectionModuleBaseChangeAddHom_of, sectionModuleRestrict_of ℳ' h',
    sectionModuleBaseChangeAddHom_of, sectionModuleRestrictPiece_apply]
  exact congrArg (DirectSum.of (sectionModulePieces ℳ' W₁') n)
    (pieceSectionModuleHom_source_le g Ψ n W h' h₂ h₁ x)

end Stacks.RelativeProj.Situation

end
