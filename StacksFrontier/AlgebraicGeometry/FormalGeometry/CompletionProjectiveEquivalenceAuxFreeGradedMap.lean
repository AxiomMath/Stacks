module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxFreeGraded

/-!
# Functoriality of the free graded module in the sheaf it is free on

`Stacks.Coherent.freeGradedModuleOn F 𝓟 d` is the free graded `𝓟`-module `F ⊗_{𝒪_X} 𝓟(-d)` on
a sheaf of `𝒪_X`-modules `F` placed in degree `d`, and
`Stacks.Coherent.freeGradedModuleOnDesc` is its universal property, the homomorphism *out* of
it attached to a morphism `F ⟶ N_d`. This file supplies the missing half of its functoriality:
the homomorphism of graded `𝓟`-modules

`F ⊗ 𝓟(-d) ⟶ G ⊗ 𝓟(-d)`

induced by a morphism `ψ : F ⟶ G`, its degreewise formula, the fact that it is a degreewise
epimorphism when `ψ` is an epimorphism, and its compatibility with the universal property.

The epimorphism statement is the point. The dévissage of part (2) of [Stacks, Tag 0897] needs a
presentation of a graded module `N` whose middle term is a sum of free graded modules on
*negative twists of an ample invertible module*, while
`Stacks.Coherent.exists_finset_epi_degreePresentationHom` produces the tautological presentation,
on the homogeneous pieces of `N` themselves. The replacement of `N_j` by a twist sum is this
file's `Stacks.Coherent.epi_app_freeGradedModuleOnMap` applied to Serre's epimorphism
`(L ^⊗ (-k_j)) ^{⊕ I_j} ↠ N_j`, and
`Stacks.Coherent.freeGradedModuleOnMap_comp_freeGradedModuleOnDesc` is what identifies the
composite with the tautological presentation.

## Main definitions

* `Stacks.Coherent.freeGradedTmulBil` is the tautological bilinear family
  `(x, a) ↦ x ⊗ a` of `F ⊗ 𝓟(-d)`, read off the sheafification unit by
  `PresheafOfModules.toBilinear`.
* `Stacks.Coherent.freeGradedMapBil` is that family precomposed with `ψ` in the first variable,
  and `Stacks.Coherent.freeGradedModuleOnMap` the homomorphism of graded `𝓟`-modules it
  descends to.

## Main results

* `Stacks.Coherent.freeGradedModuleOnMap_app_tmul` — the induced homomorphism sends `x ⊗ a` to
  `ψ(x) ⊗ a`.
* `Stacks.Coherent.freeGradedModuleOnMap_app_eq` — **its degree-`n` component is the tensor
  product of `ψ` with the identity of `𝓟_{n-d}`**, the component
  `((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map ψ).app 𝓟_{n-d}` of the tensor
  bifunctor.
* `Stacks.Coherent.epi_app_freeGradedModuleOnMap` — **the induced homomorphism is an
  epimorphism in every homogeneous degree as soon as `ψ` is an epimorphism**, by
  `Stacks.SheafOfModules.TensorPresentations.tensorSheafMapOnSite_epi`.
* `Stacks.Coherent.freeGradedModuleOnMap_comp_freeGradedModuleOnDesc` — the induced
  homomorphism followed by the extension of `φ : G ⟶ N_d` is the extension of `ψ ≫ φ`.

## Implementation notes

**Why the bilinear family is not written out.** The scalar laws of the family
`(x, a) ↦ ψ(x) ⊗ a` are `TensorProduct.smul_tmul'` and `TensorProduct.tmul_smul` read through
the sheafification unit, and the ring the tensor product is formed over,
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf`, is a composite
functor rather than `X.ringCatSheaf.obj`: the two are definitionally equal, but `rw` with
either `TensorProduct` lemma does not fire, the scalar actions not being syntactically the
same. `PresheafOfModules.toBilinear` of the sheafification unit and
`Stacks.BilinearMap.compLeft` assemble the family out of two existing constructions and avoid
the question altogether.

**Why the degreewise component is compared with the tensor bifunctor rather than built from
it.** A family of morphisms of the homogeneous pieces is not a homomorphism of graded modules
until it is checked against the two actions, and the check is available for the descended
homomorphism (`SheafOfModules.GradedModule.tensorLeftDesc`) and not for the family of tensor
products. So the homomorphism is descended and the comparison is proved afterwards, on pure
tensors, where both sides are `ψ(x) ⊗ a`; the comparison is what carries the epimorphism
statement across.

**The two spellings of the category of `𝒪_X`-modules.** `X.Modules` and
`SheafOfModules (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf _)` are
definitionally equal but `structureSheaf` is not reducible, so instance search does not
transport an `Epi` between them; the hypothesis is bound again by hand, exactly as
`Stacks.SheafOfModules.TensorEncodings.epi_tensorSheafBifunctor_map` does. For the same reason
`Epi (𝟙 _)` is passed to `tensorSheafMapOnSite_epi` by name, and the identity factor is removed
in the category `SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)` the bifunctor
is stated over.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01CC](https://stacks.math.columbia.edu/tag/01CC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)
open scoped TensorProduct

universe u

namespace Stacks.Coherent

variable {X : Scheme.{u}} {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-! ### The tautological bilinear family of `F ⊗ 𝓟(-d)` -/

/-- **The bilinear family `(x, a) ↦ x ⊗ a` of `F ⊗ 𝓟(-d)`**: the sheafification unit of the
degree-`n` piece, read as a bilinear map on sections. -/
public def freeGradedTmulBil (F : X.Modules) (d n : ℤ) :
    Stacks.BilinearMap F.val ((shiftedAlgebraModule P d).piece n).val
      ((freeGradedModuleOn F P d).piece n).val :=
  PresheafOfModules.toBilinear
    (SheafOfModules.GradedModule.tensorLeftUnit X.presheaf (isSheaf_structureRingPresheaf X) F
      (shiftedAlgebraModule P d) n)

/-- On sections, `Stacks.Coherent.freeGradedTmulBil` sends `(x, a)` to the image of the pure
tensor `x ⊗ a` in the degree-`n` piece of `F ⊗ 𝓟(-d)`. -/
public theorem freeGradedTmulBil_app (F : X.Modules) (d n : ℤ) (U : X.Opensᵒᵖ)
    (x : F.val.obj U) (a : (P.piece (n + -d)).val.obj U) :
    (freeGradedTmulBil F d n).app U x a = freeGradedMk F d n U (x ⊗ₜ a) := rfl

/-! ### The induced homomorphism -/

section Map

variable {F G : X.Modules} (ψ : F ⟶ G) (d : ℤ)

/-- **The bilinear family `(x, a) ↦ ψ(x) ⊗ a`** attached to a morphism `ψ : F ⟶ G`: the
tautological family of `G ⊗ 𝓟(-d)` restricted along `ψ` in the first variable. -/
public def freeGradedMapBil (n : ℤ) :
    Stacks.BilinearMap F.val ((shiftedAlgebraModule P d).piece n).val
      ((freeGradedModuleOn G P d).piece n).val :=
  (freeGradedTmulBil G d n).compLeft ψ.val

/-- On sections, `Stacks.Coherent.freeGradedMapBil` sends `(x, a)` to the image of the pure
tensor `ψ(x) ⊗ a` in the degree-`n` piece of `G ⊗ 𝓟(-d)`. -/
public theorem freeGradedMapBil_app (n : ℤ) (U : X.Opensᵒᵖ) (x : F.val.obj U)
    (a : (P.piece (n + -d)).val.obj U) :
    (freeGradedMapBil ψ d n).app U x a = freeGradedMk G d n U (ψ.val.app U x ⊗ₜ a) := rfl

/-- **The family `Stacks.Coherent.freeGradedMapBil` is compatible with the two actions**: this
is the action of `𝓟` on a pure tensor of `G ⊗ 𝓟(-d)`, nothing more. -/
public theorem freeGradedMapBil_map_smul (n i : ℤ) (U : X.Opensᵒᵖ) (x : F.val.obj U)
    (a : ((shiftedAlgebraModule P d).piece n).val.obj U) (y : (P.piece i).val.obj U) :
    (freeGradedMapBil ψ d (n + i)).app U x ((shiftedAlgebraModule P d).smul n i U a y) =
      (freeGradedModuleOn G P d).smul n i U ((freeGradedMapBil ψ d n).app U x a) y :=
  (SheafOfModules.GradedModule.tensorLeft_smul_tmul X.presheaf
    (isSheaf_structureRingPresheaf X) G (shiftedAlgebraModule P d) n i U
    (ψ.val.app U x) a y).symm

/-- **`Stacks.Coherent.freeGradedModuleOn` is functorial in the sheaf of modules it is free
on**: a morphism `ψ : F ⟶ G` of `𝒪_X`-modules induces a homomorphism of graded `𝓟`-modules
`F ⊗ 𝓟(-d) ⟶ G ⊗ 𝓟(-d)`, by `x ⊗ a ↦ ψ(x) ⊗ a`. -/
public def freeGradedModuleOnMap : freeGradedModuleOn F P d ⟶ freeGradedModuleOn G P d :=
  SheafOfModules.GradedModule.tensorLeftDesc X.presheaf (isSheaf_structureRingPresheaf X) F
    (shiftedAlgebraModule P d) (freeGradedModuleOn G P d) (freeGradedMapBil ψ d)
    (freeGradedMapBil_map_smul ψ d)

/-- The computation rule: the induced homomorphism sends `x ⊗ a` to `ψ(x) ⊗ a`. -/
public theorem freeGradedModuleOnMap_app_tmul (n : ℤ) (U : X.Opensᵒᵖ) (x : F.val.obj U)
    (a : (P.piece (n + -d)).val.obj U) :
    ((freeGradedModuleOnMap ψ d).app n).val.app U (freeGradedMk F d n U (x ⊗ₜ a)) =
      freeGradedMk G d n U (ψ.val.app U x ⊗ₜ a) :=
  SheafOfModules.GradedModule.tensorLeftDesc_app_tmul X.presheaf
    (isSheaf_structureRingPresheaf X) F (shiftedAlgebraModule P d) (freeGradedModuleOn G P d)
    (freeGradedMapBil ψ d) (freeGradedMapBil_map_smul ψ d) n U x a

/-- The degree-`n` piece of `F ⊗ 𝓟(-d)` is the tensor product sheaf `F ⊗ 𝓟_{n-d}`, and the
degree-`n` component of the induced homomorphism is the tensor product of `ψ` with the identity
of that factor. Both sides send `x ⊗ a` to `ψ(x) ⊗ a`. -/
public theorem freeGradedModuleOnMap_app_eq (n : ℤ) :
    (freeGradedModuleOnMap ψ d).app n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map ψ).app
        ((shiftedAlgebraModule P d).piece n) :=
  SheafOfModules.GradedModule.tensorLeft_hom_ext X.presheaf
    (isSheaf_structureRingPresheaf X) F (shiftedAlgebraModule P d) n fun U x a =>
      (freeGradedModuleOnMap_app_tmul ψ d n U x a).trans
        (PresheafOfModules.unit_naturality_apply
          (α := 𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
            (isSheaf_structureRingPresheaf X)).obj)
          (PresheafOfModulesOfCommRing.Monoidal.tensorHom ψ.val
            (𝟙 (((shiftedAlgebraModule P d).piece n).val))) U (x ⊗ₜ a)).symm

/-- **The induced homomorphism is an epimorphism in every homogeneous degree as soon as `ψ`
is.** Tensoring an epimorphism of sheaves of modules by a sheaf of modules is an epimorphism
([Stacks, Tag 01CC]), and the degree-`n` component is such a tensor product. -/
public theorem epi_app_freeGradedModuleOnMap [Epi ψ] (n : ℤ) :
    Epi (C := X.Modules) ((freeGradedModuleOnMap (P := P) ψ d).app n) := by
  have : Epi (C := SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
        (isSheaf_structureRingPresheaf X))) ψ := inferInstanceAs (Epi (C := X.Modules) ψ)
  let T := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf
  let Y : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) :=
    (shiftedAlgebraModule P d).piece n
  have h : Epi ((T.map ψ).app Y ≫ (T.obj G).map (𝟙 Y)) :=
    Stacks.SheafOfModules.TensorPresentations.tensorSheafMapOnSite_epi X.presheaf
      (isSheaf_structureRingPresheaf X) ψ (𝟙 _) (rightEpi := CategoryTheory.instEpiId _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  rwa [freeGradedModuleOnMap_app_eq ψ d n]

/-- **Compatibility with the universal property of the free graded module**: the homomorphism
induced by `ψ : F ⟶ G`, followed by the extension of `φ : G ⟶ N_d` along the universal property
of `G ⊗ 𝓟(-d)`, is the extension of `ψ ≫ φ` along the universal property of `F ⊗ 𝓟(-d)`. Both
send `x ⊗ a` to `φ(ψ(x)) · a`. -/
public theorem freeGradedModuleOnMap_comp_freeGradedModuleOnDesc
    {N : SheafOfModules.GradedModule P} (φ : G ⟶ N.piece d) :
    freeGradedModuleOnMap ψ d ≫ freeGradedModuleOnDesc G φ
      = freeGradedModuleOnDesc F (ψ ≫ φ) := by
  refine SheafOfModules.GradedModule.Hom.ext fun n => ?_
  refine SheafOfModules.GradedModule.tensorLeft_hom_ext X.presheaf
    (isSheaf_structureRingPresheaf X) F (shiftedAlgebraModule P d) n fun U x a => ?_
  have hl : ((freeGradedModuleOnMap ψ d ≫ freeGradedModuleOnDesc G φ).app n).val.app U
      (freeGradedMk F d n U (x ⊗ₜ a))
      = ((freeGradedModuleOnDesc G φ).app n).val.app U
        (((freeGradedModuleOnMap ψ d).app n).val.app U (freeGradedMk F d n U (x ⊗ₜ a))) := rfl
  refine hl.trans ?_
  refine (congrArg (fun t => ((freeGradedModuleOnDesc G φ).app n).val.app U t)
    (freeGradedModuleOnMap_app_tmul ψ d n U x a)).trans ?_
  exact (freeGradedModuleOnDesc_app_tmul G φ n U (ψ.val.app U x) a).trans
    (freeGradedModuleOnDesc_app_tmul F (ψ ≫ φ) n U x a).symm

end Map

end Stacks.Coherent

end
