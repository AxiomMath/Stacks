module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import StacksFrontier.AlgebraicGeometry.RelativeSpecFinish.Restriction

/-!
# Invertibility of a morphism of sheaves of modules is local

A morphism of sheaves of modules over a sheaf of rings `R` on a site is invertible as soon as it
is invertible over each member of a family of objects covering the final object.  On a scheme
`S`, taking the site of opens, this says that invertibility of a morphism of modules over an
**arbitrary** sheaf of rings `A` on `S` may be checked on an open covering.

## Main results

* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app` and
  `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app`: a morphism of sheaves of modules is
  invertible if and only if each of its components is.
* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`: **invertibility is local on
  the site.**  If `X : ι → C` covers the final object and every component of `φ` at an object
  carrying a morphism to some `X i` is invertible, then `φ` is invertible.
* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over`: the same, with the hypothesis
  in the form `IsIso (φ.over (X i))` used by Mathlib's `SheafOfModules.overFunctor`.
* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_over_of_isIso_val_app`: the converse of the
  component reading, so that `IsIso (φ.over V)` *is* invertibility of the components of `φ` at the
  objects lying over `V`.
* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_restrictOver`: **invertibility of a
  morphism of modules over an arbitrary sheaf of rings on a scheme is local on the scheme**, with
  restriction taken in the open-subscheme spelling
  `Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictOver`. For `A = 𝒪_S` it specializes to
  `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`.

## Implementation notes

`Topology.IsOpenEmbedding.functor_isContinuous` is a lemma rather than an instance and is needed
in order to state a restriction to an open subscheme at all, so it is a section-confined local
instance.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe v v₁ v₂ u₁ u₂ u

namespace Stacks.AlgebraicGeometry.QcohRestrictEquiv

/-! ### Components -/

section Components

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A morphism of modules is invertible iff it is so after forgetting to abelian groups. -/
private theorem isIso_forget₂_map_iff {A : Type u} [Ring A] {M N : ModuleCat.{v} A} (f : M ⟶ N) :
    IsIso ((forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}).map f) ↔ IsIso f :=
  isIso_iff_of_reflects_iso f _

/-- Each component of an invertible morphism of sheaves of modules is invertible. -/
theorem isIso_val_app {M N : SheafOfModules.{v} R} (φ : M ⟶ N) [IsIso φ] (W : Cᵒᵖ) :
    IsIso (φ.val.app W) :=
  inferInstanceAs
    (IsIso ((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj W).map φ))

/-- Transport of invertibility of a component along an equality of objects. -/
theorem isIso_val_app_congr {M N : SheafOfModules.{v} R} (φ : M ⟶ N) {W W' : Cᵒᵖ} (h : W = W')
    (hW : IsIso (φ.val.app W)) : IsIso (φ.val.app W') := by
  subst h
  exact hW

/-- If the component at `W` of a morphism of sheaves of modules is invertible, then so is the
component at `W` of the underlying morphism of sheaves of abelian groups. -/
theorem isIso_toSheaf_map_hom_app {M N : SheafOfModules.{v} R} (φ : M ⟶ N) (W : Cᵒᵖ)
    (h : IsIso (φ.val.app W)) : IsIso (((SheafOfModules.toSheaf R).map φ).hom.app W) :=
  (isIso_forget₂_map_iff _).2 h

/-- Invertibility of a component of a morphism of sheaves of modules only depends on the
isomorphism class of the object. -/
theorem isIso_val_app_of_iso_obj {M N : SheafOfModules.{v} R} (φ : M ⟶ N) {Z Z' : C}
    (α : Z ≅ Z')
    (h : IsIso (φ.val.app (op Z))) : IsIso (φ.val.app (op Z')) := by
  have h2 : IsIso (((SheafOfModules.toSheaf R).map φ).hom.app (op Z')) :=
    (NatTrans.isIso_app_iff_of_iso _ α.op).2 (isIso_toSheaf_map_hom_app φ (op Z) h)
  exact (isIso_forget₂_map_iff _).1 h2

/-- A morphism of sheaves of modules all of whose components are invertible is invertible. -/
theorem isIso_of_isIso_val_app {M N : SheafOfModules.{v} R} (φ : M ⟶ N)
    (h : ∀ W : Cᵒᵖ, IsIso (φ.val.app W)) : IsIso φ := by
  have hs : IsIso ((SheafOfModules.toSheaf R).map φ) := by
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    exact fun W ↦ isIso_toSheaf_map_hom_app φ W (h W)
  exact @isIso_of_reflects_iso _ _ _ _ _ _ φ (SheafOfModules.toSheaf R) hs inferInstance

/-- **Invertibility of a morphism of sheaves of modules is local on the site.**  If `X : ι → C`
is a family of objects covering the final object and, for every `i`, every component of `φ` at an
object carrying a morphism to `X i` is invertible, then `φ` is invertible. -/
theorem isIso_of_coversTop {ι : Type*} {X : ι → C} (hX : J.CoversTop X)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N)
    (h : ∀ (i : ι) (W : C), (W ⟶ X i) → IsIso (φ.val.app (op W))) : IsIso φ := by
  have hs : IsIso ((SheafOfModules.toSheaf R).map φ) := by
    refine Sheaf.isIso_of_coversTop hX fun i ↦ ?_
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    exact fun W ↦ isIso_toSheaf_map_hom_app φ (op W.unop.left)
      (h i W.unop.left W.unop.hom)
  exact @isIso_of_reflects_iso _ _ _ _ _ _ φ (SheafOfModules.toSheaf R) hs inferInstance

end Components

/-! ### Components of a pushforward -/

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [Functor.IsContinuous F J K] {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}

/-- If the pushforward of `φ` along a site functor `F` is invertible, then the component of `φ`
at the image under `F` of any object is invertible. -/
theorem isIso_val_app_of_isIso_pushforward
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N)
    (h : IsIso ((SheafOfModules.pushforward.{v} ψ).map φ)) (W : Cᵒᵖ) :
    IsIso (φ.val.app (op (F.obj W.unop))) := by
  have h1 : IsIso (((SheafOfModules.pushforward.{v} ψ).map φ).val.app W) :=
    @isIso_val_app _ _ _ _ _ _ _ h W
  have h2 := (isIso_forget₂_map_iff _).2 h1
  exact (isIso_forget₂_map_iff _).1 h2

/-- **Invertibility is local on the site**, with the covering hypothesis in the form given by
Mathlib's `SheafOfModules.overFunctor`: it suffices that the restriction of `φ` to the slice site
over each member of a covering family be invertible. -/
theorem isIso_of_isIso_over {ι : Type*} {X : ι → D} (hX : K.CoversTop X)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) (h : ∀ i, IsIso (φ.over (X i))) : IsIso φ := by
  refine isIso_of_coversTop hX φ fun i Z g ↦ ?_
  exact isIso_val_app_of_isIso_pushforward (𝟙 (R.over (X i))) φ (h i) (op (Over.mk g))

/-- If the component of `φ` at the image of `W` under `F` is invertible, then so is the component
at `W` of the pushforward of `φ` along `F`: the converse of `isIso_val_app_of_isIso_pushforward` at
one object. -/
theorem isIso_val_app_pushforward_map
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) (W : Cᵒᵖ)
    (h : IsIso (φ.val.app (op (F.obj W.unop)))) :
    IsIso (((SheafOfModules.pushforward.{v} ψ).map φ).val.app W) := by
  have h2 := (isIso_forget₂_map_iff _).2 h
  exact (isIso_forget₂_map_iff _).1 h2

/-- **Invertibility over a slice site is a condition on the components at the objects lying over
its base**: if every component of `φ` at the underlying object of an object of `Over V` is
invertible, then the restriction of `φ` to the slice site at `V` is invertible. -/
theorem isIso_over_of_isIso_val_app {M N : SheafOfModules.{v} R} (φ : M ⟶ N) (V : D)
    (h : ∀ Y : Over V, IsIso (φ.val.app (op Y.left))) :
    IsIso (φ.over V) :=
  isIso_of_isIso_val_app _ fun Y =>
    isIso_val_app_pushforward_map (𝟙 (R.over V)) φ Y (h Y.unop)

end Pushforward

/-! ### The open-subscheme form -/

section Scheme

open Stacks.AlgebraicGeometry.AffineQcohRestriction

attribute [local instance] Topology.IsOpenEmbedding.functor_isContinuous

/-- An open of `S` contained in `V` is the image of its preimage in `V`. -/
theorem image_preimage_of_le {S : Scheme.{u}} {V W : S.Opens} (hW : W ≤ V) :
    V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hW

/-- **Invertibility of a morphism of modules over an arbitrary sheaf of rings on a scheme is
local on the scheme.**  Let `A` be a sheaf of rings on a scheme `S` and `φ` a morphism of
`A`-modules whose restriction to each member of an open covering of `S` is invertible; then `φ`
is invertible.  For `A = 𝒪_S` this is
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`. -/
theorem isIso_of_isIso_restrictOver {S : Scheme.{u}}
    {A : Sheaf (Opens.grothendieckTopology S) RingCat.{u}} {G H : SheafOfModules.{u} A}
    (φ : G ⟶ H) {ι : Type*} (V : ι → S.Opens) (hV : IsOpenCover V)
    (h : ∀ i, IsIso ((restrictOver (V i) A).map φ)) : IsIso φ := by
  refine isIso_of_coversTop ((Opens.coversTop_iff _ V).mpr hV) φ fun i W g ↦ ?_
  refine isIso_val_app_congr φ (congrArg op (image_preimage_of_le (leOfHom g))) ?_
  exact isIso_val_app_of_isIso_pushforward (𝟙 (restrictRing (V i) A)) φ (h i)
    (op ((V i).ι ⁻¹ᵁ W))

end Scheme

end Stacks.AlgebraicGeometry.QcohRestrictEquiv

end
