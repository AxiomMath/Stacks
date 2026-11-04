module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms out of a tensor product of sheaves of modules

For `R : Type u` and modules in `Type (max w u)`, the tensor product of sheaves of `R`-modules
of `CategoryTheory.Sheaf.monoidalCategory` exists for the large-universe monoidal structure
`ModuleCat.liftedModuleMonoidal`: the morphisms inverted by sheafification form a monoidal class
(`ModuleCat.isMonoidal_W_lifted`). The tensor product is the sheafification of the sectionwise
tensor product, so a natural family of `R`-bilinear maps `F(U) × G(U) → H(U)` defines a morphism
`F ⊗ G ⟶ H`. This is how the pairing of coefficients `ℱ_ρ ⊗ ℱ_{ρ^∨} → ℤ/ℓ^kℤ` of the purity half
of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) becomes a morphism of sheaves; there the
ring `ℤ/ℓ^kℤ` lives in `Type` and the sheaves take values in `ModuleCat.{u + 1} (ZMod (ℓ ^ k))`,
which is why the large-universe structure is needed.

## Main definitions

* `CategoryTheory.Sheaf.presheafTensorDesc`: the morphism of presheaves out of the sectionwise
  tensor product.
* `CategoryTheory.Sheaf.tensorDesc`: the morphism of sheaves out of the tensor product.
* `CategoryTheory.Sheaf.monoidalClosedLifted`: sheaves of modules are monoidal closed.

## Main results

* `ModuleCat.isMonoidal_W_lifted`: the morphisms of presheaves of modules inverted by
  sheafification are stable under tensoring, for the large-universe monoidal structure.
* `CategoryTheory.Sheaf.preservesColimitsOfSize_tensorRight_moduleCat`: tensoring on the right
  preserves colimits.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits

universe w v₁ u₁ u

namespace ModuleCat

open MonoidalClosed Enriched.FunctorCategory in
/-- **The morphisms of presheaves of `R`-modules inverted by sheafification form a monoidal
class**, for modules in a universe `max w u` above the ring's universe `u` and the
large-universe monoidal structure `ModuleCat.liftedModuleMonoidal`. The tensor product of
modules is closed and braided, so this is `CategoryTheory.GrothendieckTopology.W.monoidal`. -/
theorem isMonoidal_W_lifted {C : Type u₁} [Category.{v₁} C] (R : Type u) [CommRing R]
    [UnivLE.{max u₁ v₁, max w u}] (J : GrothendieckTopology C) :
    (J.W (A := ModuleCat.{max w u} R)).IsMonoidal := by
  let _ : HasLimitsOfSize.{max u₁ v₁, max u₁ v₁} (ModuleCat.{max w u} R) :=
    ModuleCat.hasLimitsOfSize
  let _ : EnrichedOrdinaryCategory (ModuleCat.{max w u} R) (ModuleCat.{max w u} R) :=
    inferInstance
  let _ : ∀ F₁ F₂ : Cᵒᵖ ⥤ ModuleCat.{max w u} R,
      HasFunctorEnrichedHom (ModuleCat.{max w u} R) F₁ F₂ := by
    intro F₁ F₂ V
    infer_instance
  let _ : ∀ F₁ F₂ : Cᵒᵖ ⥤ ModuleCat.{max w u} R,
      HasEnrichedHom (ModuleCat.{max w u} R) F₁ F₂ := by
    intro F₁ F₂
    infer_instance
  exact GrothendieckTopology.W.monoidal

end ModuleCat

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Type u} [CommRing R]

/-- The morphism of presheaves `F ⊗ G ⟶ H` given on sections by a natural family of bilinear
maps. -/
def presheafTensorDesc {F G H : Cᵒᵖ ⥤ ModuleCat.{max w u} R}
    (β : ∀ U, F.obj U →ₗ[R] G.obj U →ₗ[R] H.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj U) (b : G.obj U),
      H.map f (β U a b) = β V (F.map f a) (G.map f b)) :
    F ⊗ G ⟶ H where
  app U := ModuleCat.ofHom (TensorProduct.lift (β U))
  naturality U V f := by
    ext : 1
    refine TensorProduct.ext' fun a b => ?_
    change TensorProduct.lift (β V) (F.map f a ⊗ₜ G.map f b) = _
    simp [hβ]

/-- The morphism of presheaves out of the sectionwise tensor product, on a pure tensor. -/
@[simp]
theorem presheafTensorDesc_app_tmul {F G H : Cᵒᵖ ⥤ ModuleCat.{max w u} R}
    (β : ∀ U, F.obj U →ₗ[R] G.obj U →ₗ[R] H.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj U) (b : G.obj U),
      H.map f (β U a b) = β V (F.map f a) (G.map f b)) (U : Cᵒᵖ) (a : F.obj U) (b : G.obj U) :
    ((presheafTensorDesc β hβ).app U).hom (a ⊗ₜ b) = β U a b :=
  rfl

attribute [local instance] monoidalCategory

variable [(J.W (A := ModuleCat.{max w u} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{max w u} R)]

/-- **A morphism out of a tensor product of sheaves of modules** given on sections by a natural
family of bilinear maps: the tensor product is the sheafification of the sectionwise tensor
product, so such a morphism is a morphism of presheaves out of the sectionwise tensor product. -/
def tensorDesc {F G H : Sheaf J (ModuleCat.{max w u} R)}
    (β : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b)) :
    F ⊗ G ⟶ H :=
  (sheafificationIso F ⊗ᵢ sheafificationIso G).hom ≫
    (Functor.Monoidal.μIso (presheafToSheaf J (ModuleCat.{max w u} R)) F.obj G.obj).hom ≫
      ((sheafificationAdjunction J (ModuleCat.{max w u} R)).homEquiv _ _).symm
        (presheafTensorDesc β hβ)

variable (J R) in
open MonoidalClosed Enriched.FunctorCategory MonoidalClosed.FunctorCategory in
/-- **Sheaves of modules are monoidal closed**, for modules in a universe `max w u` above the
ring's universe `u`: the presheaf category is closed (with the enriched functor hom, which
exists because the module category has the limits of the site's size) and symmetric, and
sheafification is a monoidal reflection, so `CategoryTheory.Monoidal.Reflective.monoidalClosed`
applies. The internal hom is what perfectness of a pairing `F ⊗ G ⟶ H` is stated against. -/
@[instance_reducible]
def monoidalClosedLifted [UnivLE.{max u₁ v₁, max w u}] [HasSheafify J (ModuleCat.{max w u} R)] :
    MonoidalClosed (Sheaf J (ModuleCat.{max w u} R)) :=
  let _ : HasLimitsOfSize.{max u₁ v₁, max u₁ v₁} (ModuleCat.{max w u} R) :=
    ModuleCat.hasLimitsOfSize
  let _ : ∀ F₁ F₂ : Cᵒᵖ ⥤ ModuleCat.{max w u} R,
      HasFunctorEnrichedHom (ModuleCat.{max w u} R) F₁ F₂ := fun _ _ _ => inferInstance
  let _ : ∀ F₁ F₂ : Cᵒᵖ ⥤ ModuleCat.{max w u} R,
      HasEnrichedHom (ModuleCat.{max w u} R) F₁ F₂ := fun _ _ => inferInstance
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J (ModuleCat.{max w u} R))

/-- **Tensoring sheaves of modules on the right preserves colimits**: the tensor product of
sheaves is closed (`CategoryTheory.Sheaf.monoidalClosedLifted`) and symmetric, so `- ⊗ G` is
isomorphic, through the braiding, to the left adjoint `G ⊗ -`. Only preservation of finite
limits, a flatness condition on `G`, is needed on top of this for the cup product of
`Stacks.ExtCup.cup`. -/
@[ega "0 4.1.5" "partial, special case",
  sga "4 IV 12.9" "special case",
  sga "4 V 8.2.4" "special case"]
theorem preservesColimitsOfSize_tensorRight_moduleCat [UnivLE.{max u₁ v₁, max w u}]
    [HasSheafify J (ModuleCat.{max w u} R)] (G : Sheaf J (ModuleCat.{max w u} R)) :
    PreservesColimitsOfSize.{v₁, u₁} (tensorRight G) := by
  let := monoidalClosedLifted J R
  let := symmetricCategory J (ModuleCat.{max w u} R)
  have : PreservesColimitsOfSize.{v₁, u₁} (tensorLeft G) :=
    (ihom.adjunction G).leftAdjoint_preservesColimits
  exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight G)

end CategoryTheory.Sheaf
