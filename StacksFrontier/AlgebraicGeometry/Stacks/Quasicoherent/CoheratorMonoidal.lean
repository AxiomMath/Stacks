module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictBifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.CoreflectionStrongMonoidal

/-!
# The monoidal structures of Stacks 0GQM

Let `𝒳` be an algebraic stack over `S`. **Stacks 0GQM** says that the tensor product of two
quasi-coherent `𝒪_𝒳`-modules is quasi-coherent, that the same holds for `LQCoh^fbc(𝒪_𝒳)`, that
the inclusions `QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) → Mod(𝒪_𝒳)` are functors of symmetric monoidal
categories, and that so is the coherator `Q : LQCoh^fbc(𝒪_𝒳) → QCoh(𝒪_𝒳)`; the comparison
`Q(𝓕) ⊗ Q(𝓖) → Q(𝓕 ⊗ 𝓖)` is the adjoint transpose of `Q(𝓕) ⊗ Q(𝓖) → 𝓕 ⊗ 𝓖`, and it is an
isomorphism because all three arrows of the triangle of the source become isomorphisms after
restriction to the flat objects.

This file sets up the monoidal structure on `Mod(𝒪_𝒳)` the statements are made in, proves that
quasi-coherence is a symmetric monoidal subcategory for it, and proves the input the coherator
needs: **a tensor product of two maps with parasitic kernel and cokernel has parasitic kernel and
cokernel** (`AlgebraicGeometry.Stack.AlgebraicStacks.isParasitic_kernel_tensorHom` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isParasitic_cokernel_tensorHom`).

## The monoidal structure

`Mod(𝒪_𝒳)` carries the monoidal structure of Tag 01CA,
`Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf`, whose tensor product is the tensor
product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` on the nose, with its braiding and
symmetry. It is named here, `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal`, and
made a local instance only where used, since sheaves of modules carry a second, localized,
monoidal structure as well.

## Parasitic kernels and cokernels

A map of `𝒪_𝒳`-modules has parasitic kernel and cokernel exactly when its restriction to the
flat-fppf site is an isomorphism: restriction is exact and kills exactly the parasitic modules
(`AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_moduleRestriction`). Restriction is
pullback along the flat-fppf morphism of ringed topoi of **Stacks 0788**
(`AlgebraicGeometry.Stack.FlatFppf.modulePullbackIso`), and pullback of modules along a morphism
of ringed topoi is a monoidal functor for the structure of Tag 01CA
(`Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal`, **Stacks 03EL**). So restriction
carries `a ⊗ b` to `r a ⊗ r b` up to the tensorators, an isomorphism when `r a` and `r b` are.

## References

* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-! ### The monoidal structure on `Mod(𝒪_𝒳)` -/

/-- The monoidal structure on `Mod(𝒪_𝒳)` of Tag 01CA, whose tensor product is the tensor product
sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` on the nose. -/
@[instance_reducible]
def fppfModulesMonoidal : MonoidalCategory (Stack.fppfModules B S hS 𝒳) :=
  Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (FlatFppf.fppfRingedTopos B S hS 𝒳).O

/-- The braiding of `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal`. -/
@[instance_reducible]
def fppfModulesBraided :
    letI := fppfModulesMonoidal B S hS 𝒳
    BraidedCategory (Stack.fppfModules B S hS 𝒳) :=
  Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf (FlatFppf.fppfRingedTopos B S hS 𝒳).O

/-- The symmetry of the braiding of
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal`. -/
@[instance_reducible]
def fppfModulesSymmetric :
    letI := fppfModulesMonoidal B S hS 𝒳
    letI := fppfModulesBraided B S hS 𝒳
    SymmetricCategory (Stack.fppfModules B S hS 𝒳) :=
  Stacks.SheafOfModules.Strict.symmetricCategory (FlatFppf.fppfRingedTopos B S hS 𝒳).O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
      (FlatFppf.fppfRingedTopos B S hS 𝒳).O)

/-- The tensor product of `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal` is the
tensor product sheaf. -/
theorem fppfModulesMonoidal_tensorObj (F G : Stack.fppfModules B S hS 𝒳) :
    @MonoidalCategoryStruct.tensorObj _ _ (fppfModulesMonoidal B S hS 𝒳).toMonoidalCategoryStruct
        F G =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.structureSheaf B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids .fppf)).obj F).obj G :=
  rfl

/-! ### Stacks 0GQM, (i): the tensor product of quasi-coherent modules -/

/-- **Stacks 0GQM, (i).** The tensor product `𝓕 ⊗_{𝒪_𝒳} 𝓖` of two quasi-coherent modules on an
algebraic stack is quasi-coherent (**Stacks 06WV** part (5)). The tensor product is the tensor
product sheaf, the sheafification of the objectwise tensor product, on the fppf site of `𝒳`.

This is `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_tensorSheaf` at the fppf site of the
algebraic stack, which is essentially small. -/
@[stacks 0GQM "(i): the tensor product of two quasi-coherent modules on an algebraic stack is \
  quasi-coherent"]
theorem isQuasicoherentOnSite_sheafTensor (F G : Stack.fppfModules B S hS 𝒳)
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor (FibredSite.structureSheaf B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf)).obj F).obj G).IsQuasicoherentOnSite :=
  FibredSite.isQuasicoherentOnSite_tensorSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    .fppf F G

section Monoidal

attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

/-- Quasi-coherence is a monoidal property of `𝒪_𝒳`-modules for the monoidal structure of
Tag 01CA: it is stable under the tensor product sheaf and holds for `𝒪_𝒳`. -/
instance isMonoidal_isQuasicoherentOnSite :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        .fppf)).IsMonoidal where
  prop_tensor F G hF hG := isQuasicoherentOnSite_sheafTensor B S hS 𝒳 F G hF hG
  prop_unit := SheafOfModules.isQuasicoherentOnSite_unit
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)

/-- **Stacks 0GQM, (iii), the first inclusion into `Mod(𝒪_𝒳)`.** `QCoh(𝒪_𝒳)` is a symmetric
monoidal category for the tensor product of `𝒪_𝒳`-modules, and the inclusion
`QCoh(𝒪_𝒳) → Mod(𝒪_𝒳)` is a functor of symmetric monoidal categories. -/
@[stacks 0GQM "(iii): the inclusion QCoh(𝒪_𝒳) → Mod(𝒪_𝒳) is a functor of symmetric monoidal \
  categories", instance_reducible]
def quasicoherentInclusionBraided : (quasicoherentInclusion B S hS 𝒳).Braided :=
  inferInstance

end Monoidal

/-! ### Parasitic kernels and cokernels of tensor products -/

section Parasitic

/-- A map of `𝒪_𝒳`-modules with parasitic kernel and cokernel restricts to an isomorphism on the
flat-fppf site. -/
theorem isIso_moduleRestriction_map_of_isParasitic {M N : Stack.fppfModules B S hS 𝒳}
    (φ : M ⟶ N) (hker : IsParasitic B S hS 𝒳 .fppf (kernel φ).val)
    (hcoker : IsParasitic B S hS 𝒳 .fppf (cokernel φ).val) :
    IsIso ((FlatFppf.moduleRestriction B S hS 𝒳).map φ) := by
  let R := FlatFppf.moduleRestriction B S hS 𝒳
  have hk : IsZero (kernel (R.map φ)) :=
    ((FlatFppf.isParasitic_iff_isZero_moduleRestriction B S hS 𝒳 _).1 hker).of_iso
      (PreservesKernel.iso R φ).symm
  have hc : IsZero (cokernel (R.map φ)) :=
    ((FlatFppf.isParasitic_iff_isZero_moduleRestriction B S hS 𝒳 _).1 hcoker).of_iso
      (PreservesCokernel.iso R φ).symm
  have : Mono (R.map φ) := Preadditive.mono_of_isZero_kernel' _ (kernelIsKernel _) hk
  have : Epi (R.map φ) := Preadditive.epi_of_isZero_cokernel' _ (cokernelIsCokernel _) hc
  exact isIso_of_mono_of_epi _

set_option synthInstance.maxHeartbeats 400000 in
/-- A map of `𝒪_𝒳`-modules which restricts to an isomorphism on the flat-fppf site has parasitic
kernel. -/
theorem isParasitic_kernel_of_isIso_moduleRestriction_map {M N : Stack.fppfModules B S hS 𝒳}
    (φ : M ⟶ N) (h : IsIso ((FlatFppf.moduleRestriction B S hS 𝒳).map φ)) :
    IsParasitic B S hS 𝒳 .fppf (kernel φ).val :=
  (FlatFppf.isParasitic_iff_isZero_moduleRestriction B S hS 𝒳 _).2
    ((isZero_kernel_of_mono _).of_iso
      (PreservesKernel.iso (FlatFppf.moduleRestriction B S hS 𝒳) φ))

set_option synthInstance.maxHeartbeats 400000 in
/-- A map of `𝒪_𝒳`-modules which restricts to an isomorphism on the flat-fppf site has parasitic
cokernel. -/
theorem isParasitic_cokernel_of_isIso_moduleRestriction_map {M N : Stack.fppfModules B S hS 𝒳}
    (φ : M ⟶ N) (h : IsIso ((FlatFppf.moduleRestriction B S hS 𝒳).map φ)) :
    IsParasitic B S hS 𝒳 .fppf (cokernel φ).val :=
  (FlatFppf.isParasitic_iff_isZero_moduleRestriction B S hS 𝒳 _).2
    ((isZero_cokernel_of_epi _).of_iso
      (PreservesCokernel.iso (FlatFppf.moduleRestriction B S hS 𝒳) φ))

/-- Pullback along the flat-fppf morphism of ringed topoi carries a tensor product of two maps it
inverts to an isomorphism: it is a monoidal functor for the structure of Tag 01CA
(**Stacks 03EL**). -/
theorem isIso_pullbackModules_map_tensorHom
    {M M' N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (FlatFppf.fppfRingedTopos B S hS 𝒳).O)}
    (a : M ⟶ M') (b : N ⟶ N')
    [IsIso ((FlatFppf.ringedToposModulesHom B S hS 𝒳).pullbackModules.map a)]
    [IsIso ((FlatFppf.ringedToposModulesHom B S hS 𝒳).pullbackModules.map b)] :
    IsIso ((FlatFppf.ringedToposModulesHom B S hS 𝒳).pullbackModules.map
      (@MonoidalCategoryStruct.tensorHom _ _
        (Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
          (FlatFppf.fppfRingedTopos B S hS 𝒳).O).toMonoidalCategoryStruct _ _ _ _ a b)) := by
  let := Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
    (FlatFppf.fppfRingedTopos B S hS 𝒳).O
  let := Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
    (FlatFppf.ringedTopos B S hS 𝒳).O
  let := Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal
    (FlatFppf.ringedToposModulesHom B S hS 𝒳)
  rw [Functor.Monoidal.map_tensor]
  infer_instance

/-- **Restriction to the flat-fppf site carries a tensor product of two maps it inverts to an
isomorphism.** Restriction is pullback along the flat-fppf morphism of ringed topoi
(**Stacks 0788**, `AlgebraicGeometry.Stack.FlatFppf.modulePullbackIso`). -/
theorem isIso_moduleRestriction_map_tensorHom {M M' N N' : Stack.fppfModules B S hS 𝒳}
    (a : M ⟶ M') (b : N ⟶ N') (ha : IsIso ((FlatFppf.moduleRestriction B S hS 𝒳).map a))
    (hb : IsIso ((FlatFppf.moduleRestriction B S hS 𝒳).map b)) :
    IsIso ((FlatFppf.moduleRestriction B S hS 𝒳).map
      (@MonoidalCategoryStruct.tensorHom (Stack.fppfModules B S hS 𝒳) _
        (fppfModulesMonoidal B S hS 𝒳).toMonoidalCategoryStruct _ _ _ _ a b)) := by
  let e := FlatFppf.modulePullbackIso B S hS 𝒳
  have : IsIso ((FlatFppf.ringedToposModulesHom B S hS 𝒳).pullbackModules.map a) :=
    (NatIso.isIso_map_iff e a).2 ha
  have : IsIso ((FlatFppf.ringedToposModulesHom B S hS 𝒳).pullbackModules.map b) :=
    (NatIso.isIso_map_iff e b).2 hb
  exact (NatIso.isIso_map_iff e _).1 (isIso_pullbackModules_map_tensorHom B S hS 𝒳 a b)

/-- **A tensor product of two maps of `𝒪_𝒳`-modules with parasitic kernels and cokernels has
parasitic kernel.** -/
theorem isParasitic_kernel_tensorHom {M M' N N' : Stack.fppfModules B S hS 𝒳}
    (a : M ⟶ M') (b : N ⟶ N')
    (ha₁ : IsParasitic B S hS 𝒳 .fppf (kernel a).val)
    (ha₂ : IsParasitic B S hS 𝒳 .fppf (cokernel a).val)
    (hb₁ : IsParasitic B S hS 𝒳 .fppf (kernel b).val)
    (hb₂ : IsParasitic B S hS 𝒳 .fppf (cokernel b).val) :
    IsParasitic B S hS 𝒳 .fppf (kernel
      (@MonoidalCategoryStruct.tensorHom (Stack.fppfModules B S hS 𝒳) _
        (fppfModulesMonoidal B S hS 𝒳).toMonoidalCategoryStruct _ _ _ _ a b)).val :=
  isParasitic_kernel_of_isIso_moduleRestriction_map B S hS 𝒳 _
    (isIso_moduleRestriction_map_tensorHom B S hS 𝒳 a b
      (isIso_moduleRestriction_map_of_isParasitic B S hS 𝒳 a ha₁ ha₂)
      (isIso_moduleRestriction_map_of_isParasitic B S hS 𝒳 b hb₁ hb₂))

/-- **A tensor product of two maps of `𝒪_𝒳`-modules with parasitic kernels and cokernels has
parasitic cokernel.** -/
theorem isParasitic_cokernel_tensorHom {M M' N N' : Stack.fppfModules B S hS 𝒳}
    (a : M ⟶ M') (b : N ⟶ N')
    (ha₁ : IsParasitic B S hS 𝒳 .fppf (kernel a).val)
    (ha₂ : IsParasitic B S hS 𝒳 .fppf (cokernel a).val)
    (hb₁ : IsParasitic B S hS 𝒳 .fppf (kernel b).val)
    (hb₂ : IsParasitic B S hS 𝒳 .fppf (cokernel b).val) :
    IsParasitic B S hS 𝒳 .fppf (cokernel
      (@MonoidalCategoryStruct.tensorHom (Stack.fppfModules B S hS 𝒳) _
        (fppfModulesMonoidal B S hS 𝒳).toMonoidalCategoryStruct _ _ _ _ a b)).val :=
  isParasitic_cokernel_of_isIso_moduleRestriction_map B S hS 𝒳 _
    (isIso_moduleRestriction_map_tensorHom B S hS 𝒳 a b
      (isIso_moduleRestriction_map_of_isParasitic B S hS 𝒳 a ha₁ ha₂)
      (isIso_moduleRestriction_map_of_isParasitic B S hS 𝒳 b hb₁ hb₂))

end Parasitic

end AlgebraicGeometry.Stack.AlgebraicStacks

end
