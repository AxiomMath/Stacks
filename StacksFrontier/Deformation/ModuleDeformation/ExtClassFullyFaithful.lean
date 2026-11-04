module

public import StacksFrontier.Deformation.ModuleDeformation.CopowerExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Extension classes through a fully faithful exact functor

Let `L : 𝒜' ⥤ 𝒜` be a fully faithful exact `k`-linear functor between abelian `k`-linear
categories. A short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `𝒜` whose three terms are images
of objects `X₁', X₂', X₃'` of `𝒜'` is the image of a short exact sequence of `𝒜'`, so its class
in `Ext¹(X₃, X₁)` is the image, under the map induced by `L` and the identifications, of a class
in `Ext¹(X₃', X₁')`. When the latter group is finite-dimensional, the classes of all such
extensions lie in a fixed finite-dimensional subspace.

This is how the extension classes of the deformations of Stacks 08W8, which live on `X₀` but
are annihilated by a power of the ideal of the support, are bounded by an `Ext¹` on a closed
subspace proper over the field, where Stacks 0D0T applies.

## Main definitions

* `Deformation.ModuleDeformation.extTransfer`: the `k`-linear map
  `Ext¹(X₃', X₁') ⟶ Ext¹(X₃, X₁)` induced by `L` and two identifications.

## Main results

* `Deformation.ModuleDeformation.extClass_mem_range_extTransfer`: the class of a short exact
  sequence with terms in the essential image lies in the range of that map.
* `Deformation.ModuleDeformation.extensionClass_mem_range_extTransfer`: the same for the class
  of a copower extension.
-/

@[expose] public noncomputable section

namespace Deformation.ModuleDeformation

open CategoryTheory CategoryTheory.Limits Abelian

attribute [local instance] Abelian.hasFiniteBiproducts

universe v w w₁ w₂ u₁ v₁ u₂ v₂

variable {k : Type w} [Field k]
  {𝒜' : Type u₁} [Category.{v₁} 𝒜'] [Abelian 𝒜'] [Linear k 𝒜'] [HasExt.{w₁} 𝒜']
  {𝒜 : Type u₂} [Category.{v₂} 𝒜] [Abelian 𝒜] [Linear k 𝒜] [HasExt.{w₂} 𝒜]
  (L : 𝒜' ⥤ 𝒜) [L.Additive] [L.Linear k] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The `k`-linear map `Ext^n(X₃', X₁') ⟶ Ext^n(X₃, X₁)` induced by `L` and identifications
`L X₃' ≅ X₃`, `L X₁' ≅ X₁`. -/
def extTransfer {X₁' X₃' : 𝒜'} {X₁ X₃ : 𝒜} (e₁ : L.obj X₁' ≅ X₁) (e₃ : L.obj X₃' ≅ X₃)
    (n : ℕ) : Ext X₃' X₁' n →ₗ[k] Ext X₃ X₁ n where
  toFun t := (Ext.mk₀ e₃.inv).comp ((t.mapExactFunctor L).comp (Ext.mk₀ e₁.hom) (add_zero n))
    (zero_add n)
  map_add' t t' := by
    rw [Ext.mapExactFunctor_add, Ext.add_comp, Ext.comp_add]
  map_smul' c t := by
    rw [Functor.mapExactFunctor_smul, Ext.smul_comp, Ext.comp_smul]
    rfl

/-- `extTransfer L e₁ e₃ n t` is the composite of `Ext.mk₀ e₃.inv`, the image of `t` under `L`,
and `Ext.mk₀ e₁.hom`. -/
theorem extTransfer_apply {X₁' X₃' : 𝒜'} {X₁ X₃ : 𝒜} (e₁ : L.obj X₁' ≅ X₁)
    (e₃ : L.obj X₃' ≅ X₃) (n : ℕ) (t : Ext X₃' X₁' n) :
    extTransfer (k := k) L e₁ e₃ n t =
      (Ext.mk₀ e₃.inv).comp ((t.mapExactFunctor L).comp (Ext.mk₀ e₁.hom) (add_zero n))
        (zero_add n) := rfl

variable [L.Full] [L.Faithful]

/-- **A short exact sequence with terms in the essential image of a fully faithful exact functor
has its class in the range of the induced map of `Ext¹`.** -/
theorem extClass_mem_range_extTransfer {S : ShortComplex 𝒜} (hS : S.ShortExact)
    {X₁' X₂' X₃' : 𝒜'} (e₁ : L.obj X₁' ≅ S.X₁) (e₂ : L.obj X₂' ≅ S.X₂)
    (e₃ : L.obj X₃' ≅ S.X₃) :
    hS.extClass ∈ LinearMap.range (extTransfer (k := k) L e₁ e₃ 1) := by
  let f' : X₁' ⟶ X₂' := L.preimage (e₁.hom ≫ S.f ≫ e₂.inv)
  let g' : X₂' ⟶ X₃' := L.preimage (e₂.hom ≫ S.g ≫ e₃.inv)
  have hzero : f' ≫ g' = 0 := by
    apply L.map_injective
    simp [f', g', S.zero_assoc]
  let S' : ShortComplex 𝒜' := ShortComplex.mk f' g' hzero
  let φ : S'.map L ≅ S := ShortComplex.isoMk e₁ e₂ e₃ (by simp [S', f']) (by simp [S', g'])
  have hSL : (S'.map L).ShortExact := ShortComplex.shortExact_of_iso φ.symm hS
  have hS' : S'.ShortExact :=
    .mk' ((S'.exact_map_iff_of_faithful L).1 hSL.exact) (L.mono_of_mono_map hSL.mono_f)
      (L.epi_of_epi_map hSL.epi_g)
  refine ⟨hS'.extClass, ?_⟩
  rw [extTransfer_apply, Ext.mapExactFunctor_extClass]
  have h1 : ((hS'.map_of_exact L).extClass).comp (Ext.mk₀ e₁.hom) (add_zero 1) =
      (Ext.mk₀ e₃.hom).comp hS.extClass (zero_add 1) :=
    (hS'.map_of_exact L).extClass_naturality hS φ.hom
  rw [h1, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id, Ext.mk₀_id_comp]

/-- **The classes of the copower extensions whose terms are images under `L` lie in one subspace
which is finite-dimensional as soon as `Ext¹` of the preimages is.** -/
theorem extensionClass_mem_range_extTransfer {G : 𝒜} {V : FGModuleCat.{v} k}
    (A : CopowerExtension G V) {G' C' E' : 𝒜'} (eG : L.obj G' ≅ G)
    (eC : L.obj C' ≅ copowerObj G V) (eE : L.obj E' ≅ A.E) :
    A.extensionClass ∈ LinearMap.range (extTransfer (k := k) L eC eG 1) :=
  extClass_mem_range_extTransfer L A.shortExact eC eE eG

end Deformation.ModuleDeformation

end
