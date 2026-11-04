module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentTransport
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonSections

/-!
# Reading the tensor comparison of [Stacks, Tag 0EX3] (b) on sections

The canonical map of conclusion (b) of [Stacks, Tag 0EX3] is, by the sheafification adjunction of
[Stacks, Tag 01CB], a bilinear family on sections, whose value over an open `U` of the target is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorSection` read at the top
open of `U` by `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topReading`.

`Stacks.AlgebraicGeometry.ModuleLimits.imageSections` is the interface for exactly that
reading: it takes a morphism of restrictions to an open `W`, a presentation `W.ι ''ᵁ P = U` of an
open `U` of the ambient scheme as the image of an open of `W`, and returns the induced map of
sections over `U`.  It is already known to be additive, `Γ(X, U)`-homogeneous, compatible with
shrinking `U`, independent of the presentation, and unchanged by restricting the morphism to a
smaller open.

This file identifies `topReading` with it and reads off the three consequences the bilinear
family needs, and computes `imageSections` of
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorLocalSection` — the morphism `x ↦ x ⊗ s` —
as the pure tensor it is.  The last of these makes tensoring with a local section visibly
compatible with shrinking the open, which is the form the naturality of the bilinear family
consumes.

## Main results

All of the following live in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `topReading_eq_imageSections`: **`topReading` is `imageSections` at the top open.**
* `restrictFunctor_map_app` and `topReading_restrictFunctor_map`: a morphism restricted to an
  open, read on sections, is the morphism itself.
* `topReading_smul`: **the reading at the top open is `Γ(Y, U)`-homogeneous.**  This is linearity
  of the bilinear family in the section of the module of higher direct images.
* `topReading_presheaf_map`: **the reading at the top open commutes with shrinking the open**,
  the morphism being replaced by its restriction.
* `imageSections_tensorLocalSection`: **tensoring with a local section, read on sections, is the
  pure tensor.**
* `tensorLocalSection_restrictHomOfLE` and `tensorLocalSection_restrictLEIso`: **tensoring with a
  local section commutes with shrinking the open**, sectionwise and as the functorial conjugate
  of `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso`.

## Implementation notes

`imageSections` takes the open of the ambient scheme and a *presentation* of it as an image
separately, and `Stacks.AlgebraicGeometry.ModuleLimits.imageSections_congr` says the value does
not depend on the presentation.  That is what lets the two sides of
`tensorLocalSection_restrictHomOfLE` be compared: they are read through presentations over
different opens.

The restriction map of `tensorLocalSection`'s section is written `homOfLE` of a proof of an
inequality of opens, and two such proofs give the same morphism because an inequality is a
proposition; `presheaf_map_homOfLE_comp` composes two of them into one and is the only place
where that is used.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] moduleOfPresheafRing

variable {Z : Scheme.{u}}

/-! ### The reading at the top open is `imageSections` -/

/-- **`topReading` is `imageSections` at the top open.**  Both conjugate the action of the
morphism at the top open of `U` by the two restriction maps along `U.ι ''ᵁ ⊤ = U`; the
comparison `AlgebraicGeometry.Scheme.Modules.restrictAppIso` that `topReading` writes out is the
identity. -/
theorem topReading_eq_imageSections {M N : Z.Modules} (U : Z.Opens)
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N) (a : Γ(M, U)) :
    topReading U φ a = ModuleLimits.imageSections φ U.ι_image_top a := by
  rw [ModuleLimits.imageSections_eq_map_eqToHom]
  rfl

/-- Two restriction maps of the structure sheaf along inverse equalities of opens cancel. -/
theorem presheaf_map_eqToHom_cancel {A B : Z.Opens} (hAB : A = B) (y : Γ(Z, B)) :
    Z.presheaf.map (eqToHom hAB.symm).op (Z.presheaf.map (eqToHom hAB).op y) = y := by
  rw [← CategoryTheory.comp_apply, ← Z.presheaf.map_comp, ← op_comp]
  simp

/-- The restriction maps along the equality `U.ι ''ᵁ ⊤ = U` of opens cancel, in the other
order. -/
theorem presheaf_map_ι_image_top_cancel' {M : Z.Modules} (U : Z.Opens)
    (y : Γ(M, U.ι ''ᵁ ⊤)) :
    M.presheaf.map (eqToHom U.ι_image_top).op
        (M.presheaf.map (eqToHom U.ι_image_top.symm).op y) = y := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp, ← op_comp]
  simp

/-- **The reading at the top open is functorial.**  The two restriction maps along
`U.ι ''ᵁ ⊤ = U` that the inner reading introduces cancel against the ones the outer reading
introduces. -/
theorem topReading_comp {M N P : Z.Modules} (U : Z.Opens)
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N)
    (ψ : (Scheme.Modules.restrictFunctor U.ι).obj N ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj P) (a : Γ(M, U)) :
    topReading U (φ ≫ ψ) a = topReading U ψ (topReading U φ a) := by
  show P.presheaf.map (eqToHom U.ι_image_top.symm).op
      (ψ.app ⊤ (φ.app ⊤ (M.presheaf.map (eqToHom U.ι_image_top).op a))) = _
  show _ = P.presheaf.map (eqToHom U.ι_image_top.symm).op
      (ψ.app ⊤ (N.presheaf.map (eqToHom U.ι_image_top).op
        (N.presheaf.map (eqToHom U.ι_image_top.symm).op
          (φ.app ⊤ (M.presheaf.map (eqToHom U.ι_image_top).op a)))))
  exact congrArg
    (fun y : Γ(N, U.ι ''ᵁ ⊤) =>
      P.presheaf.map (eqToHom U.ι_image_top.symm).op (ψ.app ⊤ y))
    (presheaf_map_ι_image_top_cancel' U
      (φ.app ⊤ (M.presheaf.map (eqToHom U.ι_image_top).op a))).symm

/-- **A morphism restricted to an open, read on the sections over the image of an open of it, is
the morphism itself.** -/
theorem restrictFunctor_map_app {M N : Z.Modules} (V : Z.Opens) (c : M ⟶ N)
    (S : V.toScheme.Opens) (z : Γ(M, V.ι ''ᵁ S)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor V.ι).map c) S z =
      Scheme.Modules.Hom.app c (V.ι ''ᵁ S) z := rfl

/-- **The reading at the top open of a restricted morphism is that morphism on sections.** -/
theorem topReading_restrictFunctor_map {M N : Z.Modules} (U : Z.Opens) (ρ : M ⟶ N)
    (a : Γ(M, U)) :
    topReading U ((Scheme.Modules.restrictFunctor U.ι).map ρ) a = ρ.app U a := by
  have he : (eqToHom U.ι_image_top : U.ι ''ᵁ ⊤ ⟶ U) = homOfLE (U.ι_image_le ⊤) :=
    Subsingleton.elim _ _
  show N.presheaf.map (eqToHom U.ι_image_top.symm).op
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor U.ι).map ρ) ⊤
        (M.presheaf.map (eqToHom U.ι_image_top).op a)) = _
  rw [restrictFunctor_map_app, he, ← ModuleLimits.Hom_app_presheaf_map ρ (U.ι_image_le ⊤) a,
    ← he, presheaf_map_ι_image_top_cancel]

/-- **The reading at the top open sends the zero section to zero.**  It is additive, and in a
group an element equal to its own double is zero. -/
theorem topReading_zero {M N : Z.Modules} (U : Z.Opens)
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N) :
    topReading U φ 0 = 0 := by
  have h : topReading U φ 0 + topReading U φ 0 = topReading U φ 0 + 0 := by
    rw [add_zero, ← topReading_add U φ 0 0, add_zero]
  exact add_left_cancel h

/-- **The reading at the top open is additive in the morphism, given the decomposition.**  The
morphism and its two summands are variables, so that a consumer whose morphism is built from a
derived functor pairs no two spellings of one object inside this declaration; that pairing is
what exhausts the kernel's budget here. -/
theorem topReading_add_hom_of_eq {M N : Z.Modules} (U : Z.Opens)
    (φ φ₁ φ₂ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N)
    (h : φ = φ₁ + φ₂) (a : Γ(M, U)) :
    topReading U φ a = topReading U φ₁ a + topReading U φ₂ a := by
  rw [h]
  exact topReading_add_hom U φ₁ φ₂ a

/-- **The reading at the top open is `Γ(Z, U)`-homogeneous.**  This is the linearity of the
bilinear family of conclusion (b) of [Stacks, Tag 0EX3] in the section of `R^n f_* F`. -/
theorem topReading_smul {M N : Z.Modules} (U : Z.Opens)
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N) (r : Γ(Z, U))
    (a : Γ(M, U)) :
    topReading U φ (r • a) = r • topReading U φ a := by
  rw [topReading_eq_imageSections, topReading_eq_imageSections,
    ModuleLimits.imageSections_smul]

/-- **The reading at the top open commutes with shrinking the open.**  Restricting the resulting
section from `U` to `U'` is reading the restriction of the morphism to `U'` on the restricted
section. -/
theorem topReading_presheaf_map {M N : Z.Modules} {U U' : Z.Opens} (e : U' ≤ U)
    (φ : (Scheme.Modules.restrictFunctor U.ι).obj M ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj N) (a : Γ(M, U)) :
    N.presheaf.map (homOfLE e).op (topReading U φ a) =
      topReading U' (ModuleLimits.restrictHomOfLE e φ) (M.presheaf.map (homOfLE e).op a) := by
  rw [topReading_eq_imageSections, topReading_eq_imageSections,
    ModuleLimits.imageSections_restrictHomOfLE e φ U'.ι_image_top
      (ModuleLimits.image_preimage_of_le e),
    ModuleLimits.imageSections_presheaf_map φ (ModuleLimits.image_preimage_of_le e)
      U.ι_image_top e a]

/-! ### Tensoring with a local section, read on sections -/

/-- Two successive restrictions of a section along inclusions of opens compose into one. -/
theorem presheaf_map_homOfLE_comp (B : Z.Modules) {U V W : Z.Opens} (h₁ : U ≤ V) (h₂ : V ≤ W)
    (t : Γ(B, W)) :
    B.presheaf.map (homOfLE h₁).op (B.presheaf.map (homOfLE h₂).op t) =
      B.presheaf.map (homOfLE (h₁.trans h₂)).op t := by
  rw [← CategoryTheory.comp_apply, ← B.presheaf.map_comp, ← op_comp]
  rfl

/-- A composite of two restriction maps of the structure sheaf is a restriction map. -/
theorem presheaf_map_structure_comp {A B C : Z.Opens} (i : A ⟶ B) (j : B ⟶ C) (k : A ⟶ C)
    (y : Γ(Z, C)) :
    Z.presheaf.map i.op (Z.presheaf.map j.op y) = Z.presheaf.map k.op y := by
  rw [← CategoryTheory.comp_apply, ← Z.presheaf.map_comp, ← op_comp,
    Subsingleton.elim (i ≫ j) k]

/-- **Tensoring with a local section, read on sections, is the pure tensor.**  For `t` a section
of `B` over `Q` and `U ≤ Q` presented as the image of an open of `Q`, the morphism `x ↦ x ⊗ t`
sends a section `m` of `A` over `U` to the image in the tensor sheaf of `m ⊗ t|_U`. -/
theorem imageSections_tensorLocalSection (A B : Z.Modules) {Q : Z.Opens} (t : Γ(B, Q))
    {U : Z.Opens} {S : Q.toScheme.Opens} (hS : Q.ι ''ᵁ S = U) (hU : U ≤ Q) (m : Γ(A, U)) :
    ModuleLimits.imageSections (tensorLocalSection Z A B Q t) hS m =
      toTensorSheafSection Z.toRingedSpace A B (op U)
        (m ⊗ₜ[Z.presheaf.obj (op U)] B.presheaf.map (homOfLE hU).op t) := by
  subst hS
  rfl

/-- **Tensoring with a local section commutes with shrinking the open.**  The restriction to
`P ≤ Q` of the morphism `x ↦ x ⊗ t` is the morphism `x ↦ x ⊗ t|_P`.  On sections both are the
pure tensor with the restriction of `t`, and a restriction of a restriction is a
restriction. -/
theorem tensorLocalSection_restrictHomOfLE (A B : Z.Modules) {P Q : Z.Opens} (e : P ≤ Q)
    (t : Γ(B, Q)) :
    ModuleLimits.restrictHomOfLE e (tensorLocalSection Z A B Q t) =
      tensorLocalSection Z A B P (B.presheaf.map (homOfLE e).op t) := by
  refine Scheme.Modules.hom_ext _ _ fun R => ?_
  ext (m : Γ(A, P.ι ''ᵁ R))
  rw [← ModuleLimits.imageSections_rfl_app
      (ModuleLimits.restrictHomOfLE e (tensorLocalSection Z A B Q t)) R m,
    ModuleLimits.imageSections_restrictHomOfLE e (tensorLocalSection Z A B Q t) rfl
      (ModuleLimits.image_preimage_of_le ((P.ι_image_le R).trans e)),
    imageSections_tensorLocalSection A B t
      (ModuleLimits.image_preimage_of_le ((P.ι_image_le R).trans e))
      ((P.ι_image_le R).trans e) m,
    ← ModuleLimits.imageSections_rfl_app
      (tensorLocalSection Z A B P (B.presheaf.map (homOfLE e).op t)) R m,
    imageSections_tensorLocalSection A B (B.presheaf.map (homOfLE e).op t) rfl
      (P.ι_image_le R) m,
    presheaf_map_homOfLE_comp B (P.ι_image_le R) e t]

/-- **Tensoring with a local section commutes with shrinking the open, functorially.**  The
functorial conjugate of `x ↦ x ⊗ t` by the comparison
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` between restricting to `Q` and then to `P`
and restricting to `P` directly is `x ↦ x ⊗ t|_P`.  This is the shape the naturality of the
bilinear family of conclusion (b) of [Stacks, Tag 0EX3] consumes. -/
theorem tensorLocalSection_restrictLEIso (A B : Z.Modules) {P Q : Z.Opens} (e : P ≤ Q)
    (t : Γ(B, Q)) :
    (ModuleLimits.restrictLEIso e).inv.app A ≫
        (Scheme.Modules.restrictFunctor (Z.homOfLE e)).map (tensorLocalSection Z A B Q t) ≫
          (ModuleLimits.restrictLEIso e).hom.app
            (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj A).obj B) =
      tensorLocalSection Z A B P (B.presheaf.map (homOfLE e).op t) := by
  rw [← ModuleLimits.restrictHomOfLE_eq e (tensorLocalSection Z A B Q t),
    tensorLocalSection_restrictHomOfLE]

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
