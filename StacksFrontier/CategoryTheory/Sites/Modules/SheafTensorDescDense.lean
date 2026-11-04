module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDesc

/-!
# Bilinear maps of sheaves of modules from a dense subsite

Let `G : C ⥤ D` be cover dense and locally full for a topology `K` on `D`, `F₁`, `F₂` presheaves
of `R`-modules on `D` and `H` a sheaf of `R`-modules on `(D, K)`. A family of `R`-bilinear maps
`F₁(G U) × F₂(G U) → H(G U)`, natural in `U ∈ C`, extends uniquely to a natural family of
bilinear maps on all of `D`: it is a morphism `G^*(F₁ ⊗ F₂) ⟶ G^* H` of presheaves on `C`, and
`CategoryTheory.Functor.IsCoverDense.sheafHom` extends it to `F₁ ⊗ F₂ ⟶ H`. With
`CategoryTheory.Sheaf.tensorDesc` this gives a morphism `F₁ ⊗ F₂ ⟶ H` of sheaves on `D` out of a
pairing defined only on the dense subsite.

This is how a pairing of lisse sheaves defined on the small étale category of Stacks 021B (where
Tag 0DV5 lives) becomes a morphism out of the tensor product of sheaves on Mathlib's small étale
site, as the multiplicativity `L_ψ(g₁) ⊗ L_ψ(g₂) ≅ L_ψ(g₁ + g₂)` of Artin–Schreier sheaves in
the Fourier transform of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) requires.

## Main definitions

* `CategoryTheory.Sheaf.denseExtensionTensorHom`: the extended morphism `F₁ ⊗ F₂ ⟶ H`.
* `CategoryTheory.Sheaf.denseExtensionBilinear`: the extended bilinear maps.

## Main results

* `CategoryTheory.Sheaf.denseExtensionBilinear_naturality`: they commute with restriction.
* `CategoryTheory.Sheaf.denseExtensionBilinear_apply`: on the image of `G` they are the given
  bilinear maps.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe w v₁ v₂ u₁ u₂ u

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
  {K : GrothendieckTopology D} [G.IsCoverDense K] [G.IsLocallyFull K]
  {R : Type u} [CommRing R] {F₁ F₂ : Dᵒᵖ ⥤ ModuleCat.{max w u} R}
  {H : Sheaf K (ModuleCat.{max w u} R)}
  (β : ∀ U : Cᵒᵖ, F₁.obj (G.op.obj U) →ₗ[R] F₂.obj (G.op.obj U) →ₗ[R] H.obj.obj (G.op.obj U))
  (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F₁.obj (G.op.obj U)) (b : F₂.obj (G.op.obj U)),
    H.obj.map (G.op.map f) (β U a b) = β V (F₁.map (G.op.map f) a) (F₂.map (G.op.map f) b))

/-- **The morphism `F₁ ⊗ F₂ ⟶ H` extending a natural family of bilinear maps on a dense
subsite**: the family is a morphism `G^*(F₁ ⊗ F₂) ⟶ G^* H`, extended by
`CategoryTheory.Functor.IsCoverDense.sheafHom`. -/
def denseExtensionTensorHom : F₁ ⊗ F₂ ⟶ H.obj :=
  Functor.IsCoverDense.sheafHom (G := G) (K := K) (ℱ := F₁ ⊗ F₂) (ℱ' := H)
    (presheafTensorDesc (F := G.op ⋙ F₁) (G := G.op ⋙ F₂) (H := G.op ⋙ H.obj) β hβ)

/-- **The bilinear maps `F₁(V) × F₂(V) → H(V)` extending a natural family on a dense
subsite.** -/
def denseExtensionBilinear (V : Dᵒᵖ) : F₁.obj V →ₗ[R] F₂.obj V →ₗ[R] H.obj.obj V :=
  (TensorProduct.mk R (F₁.obj V) (F₂.obj V)).compr₂ ((denseExtensionTensorHom G β hβ).app V).hom

/-- `denseExtensionBilinear` at `a` and `b` is `denseExtensionTensorHom` applied to `a ⊗ₜ b`. -/
theorem denseExtensionBilinear_apply' (V : Dᵒᵖ) (a : F₁.obj V) (b : F₂.obj V) :
    denseExtensionBilinear G β hβ V a b = ((denseExtensionTensorHom G β hβ).app V).hom (a ⊗ₜ b) :=
  rfl

/-- **The extended bilinear maps commute with restriction.** -/
theorem denseExtensionBilinear_naturality {V W : Dᵒᵖ} (f : V ⟶ W) (a : F₁.obj V) (b : F₂.obj V) :
    H.obj.map f (denseExtensionBilinear G β hβ V a b) =
      denseExtensionBilinear G β hβ W (F₁.map f a) (F₂.map f b) :=
  (ConcreteCategory.congr_hom ((denseExtensionTensorHom G β hβ).naturality f) (a ⊗ₜ b)).symm

/-- **On the image of the dense subsite the extended bilinear maps are the given ones.** -/
theorem denseExtensionBilinear_apply (U : Cᵒᵖ) (a : F₁.obj (G.op.obj U))
    (b : F₂.obj (G.op.obj U)) :
    denseExtensionBilinear G β hβ (G.op.obj U) a b = β U a b :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (Functor.IsCoverDense.sheafHom_restrict_eq
    (G := G) (K := K) (ℱ := F₁ ⊗ F₂) (ℱ' := H)
      (presheafTensorDesc (F := G.op ⋙ F₁) (G := G.op ⋙ F₂) (H := G.op ⋙ H.obj) β hβ)) U)
    (a ⊗ₜ b)

end CategoryTheory.Sheaf
