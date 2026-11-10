module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Logic.Small.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Smallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules

/-!
# Colimits of module sheaves on the big fppf site over a scheme

Sheaves of modules over a sheaf of rings on each of the five big sites over a scheme `S`, and on
each of their localizations at an object, have colimits of every shape whose type of objects is
small relative to the module universe. The same holds on the associated site of an essentially
small category fibred in groupoids over the big fppf category of schemes over `S`. The smallness
restriction on the shape cannot be dropped.

## Main results

* `AlgebraicGeometry.BigFppfOver.hasColimitsOfShape_sheafOfModules` and
  `AlgebraicGeometry.BigFppfOver.hasColimits_sheafOfModules`: module sheaves on each of the five
  big sites over `S` have colimits of any shape whose objects form a `u`-small type, and of all
  shapes of a bounded size.
* `AlgebraicGeometry.BigFppfOver.hasColimitsOfShape_sheafOfModules_structureSheaf` and
  `AlgebraicGeometry.BigFppfOver.hasColimits_sheafOfModules_structureSheaf`: the same for modules
  over the structure sheaf of the big fppf site.
* `AlgebraicGeometry.BigFppfOver.hasColimitsOfShape_sheafOfModules_over` and
  `AlgebraicGeometry.BigFppfOver.hasColimits_sheafOfModules_over`: the same on each
  localization at an object.
* `AlgebraicGeometry.FibredSite.hasColimitsOfShape_sheafOfModules`,
  `AlgebraicGeometry.FibredSite.hasColimits_sheafOfModules` and their specializations
  `AlgebraicGeometry.FibredSite.hasColimitsOfShape_sheafOfModules_ringStructureSheafCore` and
  `AlgebraicGeometry.FibredSite.hasColimits_sheafOfModules_ringStructureSheafCore`: module
  sheaves on the associated site of an essentially small category fibred in groupoids have
  those colimits.
* `AddCommGrpCat.not_hasColimitsOfShape_discrete_type` and
  `AddCommGrpCat.not_hasColimitsOfSize_succ`: abelian groups with sections in `Type u` do not
  have coproducts indexed by `Type u`, nor all colimits of size `u + 1`.

## Implementation notes

These are stated as theorems rather than instances, because the sheafification hypotheses they
consume are theorems in `Descent.Smallness` rather than instances.

Each result comes in two forms: one for a single shape under `Small`, and one for all shapes of
a bounded size under `UnivLE`, matching `CategoryTheory.Limits.AddCommGrpCat.hasColimitsOfSize`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t' t w v u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Sheaves of modules over any sheaf of rings on one of the five big sites over `S` have
colimits of every shape whose objects form a `u`-small type. -/
public theorem hasColimitsOfShape_sheafOfModules (τ : SiteKind)
    (R : Sheaf (baseOverTopology B S hS τ) RingCat.{u})
    (K : Type t) [Category.{t'} K] [Small.{u} K] :
    HasColimitsOfShape K (SheafOfModules.{u} R) := by
  let _ := hasWeakSheafify B S hS τ
  let _ := wEqualsLocallyBijective B S hS τ
  infer_instance

/-- Sheaves of modules over any sheaf of rings on one of the five big sites over `S` have all
colimits indexed by shapes whose objects live at most `u` levels up. -/
public theorem hasColimits_sheafOfModules (τ : SiteKind)
    (R : Sheaf (baseOverTopology B S hS τ) RingCat.{u}) [UnivLE.{t, u}] :
    HasColimitsOfSize.{t', t} (SheafOfModules.{u} R) :=
  ⟨fun _ _ => hasColimitsOfShape_sheafOfModules B S hS τ R _⟩

/-- Sheaves of modules over any sheaf of rings on a localization at an object of one of the
five big sites over `S` have colimits of every shape whose objects form a `u`-small type. -/
public theorem hasColimitsOfShape_sheafOfModules_over (τ : SiteKind) (X : BigFppfOver B S hS)
    (R : Sheaf ((baseOverTopology B S hS τ).over X) RingCat.{u})
    (K : Type t) [Category.{t'} K] [Small.{u} K] :
    HasColimitsOfShape K (SheafOfModules.{u} R) := by
  let _ := hasWeakSheafify_over B S hS τ X
  let _ := wEqualsLocallyBijective_over B S hS τ X
  infer_instance

/-- Sheaves of modules over any sheaf of rings on a localization at an object of one of the
five big sites over `S` have all colimits indexed by shapes whose objects live at most `u`
levels up. -/
public theorem hasColimits_sheafOfModules_over (τ : SiteKind) (X : BigFppfOver B S hS)
    (R : Sheaf ((baseOverTopology B S hS τ).over X) RingCat.{u}) [UnivLE.{t, u}] :
    HasColimitsOfSize.{t', t} (SheafOfModules.{u} R) :=
  ⟨fun _ _ => hasColimitsOfShape_sheafOfModules_over B S hS τ X R _⟩

/-- Module sheaves over the structure sheaf of the big fppf site over `S` have colimits of
every shape whose objects form a `u`-small type. -/
public theorem hasColimitsOfShape_sheafOfModules_structureSheaf
    (K : Type t) [Category.{t'} K] [Small.{u} K] :
    HasColimitsOfShape K (SheafOfModules.{u} (structureSheaf B S hS)) :=
  hasColimitsOfShape_sheafOfModules B S hS .fppf (structureSheaf B S hS) K

/-- Module sheaves over the structure sheaf of the big fppf site over `S` have all colimits
indexed by shapes whose objects live at most `u` levels up. -/
public theorem hasColimits_sheafOfModules_structureSheaf [UnivLE.{t, u}] :
    HasColimitsOfSize.{t', t} (SheafOfModules.{u} (structureSheaf B S hS)) :=
  hasColimits_sheafOfModules B S hS .fppf (structureSheaf B S hS)

end BigFppfOver

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- Sheaves of modules on the associated site of an essentially small category fibred in
groupoids over the big fppf category of schemes over `S` have colimits of every shape whose
objects form a `u`-small type. -/
public theorem hasColimitsOfShape_sheafOfModules (τ : SiteKind)
    (R : Sheaf (BigFppfOver.associatedTopology B S hS p τ) RingCat.{u})
    (K : Type t) [Category.{t'} K] [Small.{u} K] :
    HasColimitsOfShape K (SheafOfModules.{u} R) := by
  let _ : HasSheafify (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let _ : (BigFppfOver.associatedTopology B S hS p τ).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  infer_instance

/-- Sheaves of modules on the associated site of an essentially small category fibred in
groupoids over the big fppf category of schemes over `S` have all colimits indexed by shapes
whose objects live at most `u` levels up. -/
public theorem hasColimits_sheafOfModules (τ : SiteKind)
    (R : Sheaf (BigFppfOver.associatedTopology B S hS p τ) RingCat.{u}) [UnivLE.{t, u}] :
    HasColimitsOfSize.{t', t} (SheafOfModules.{u} R) :=
  ⟨fun _ _ => hasColimitsOfShape_sheafOfModules B S hS p τ R _⟩

/-- Module sheaves over the structure sheaf of the associated fppf site of an essentially
small category fibred in groupoids have colimits of every shape whose objects form a `u`-small
type. -/
public theorem hasColimitsOfShape_sheafOfModules_ringStructureSheafCore
    (hp : p.IsFiberedInGroupoids) (τ : SiteKind)
    (K : Type t) [Category.{t'} K] [Small.{u} K] :
    HasColimitsOfShape K (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :=
  hasColimitsOfShape_sheafOfModules B S hS p τ (ringStructureSheafCore B S hS p hp τ) K

/-- Module sheaves over the structure sheaf of the associated fppf site of an essentially
small category fibred in groupoids have all colimits indexed by shapes whose objects live at
most `u` levels up. -/
public theorem hasColimits_sheafOfModules_ringStructureSheafCore
    (hp : p.IsFiberedInGroupoids) (τ : SiteKind) [UnivLE.{t, u}] :
    HasColimitsOfSize.{t', t}
      (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :=
  hasColimits_sheafOfModules B S hS p τ (ringStructureSheafCore B S hS p hp τ)

end FibredSite

end AlgebraicGeometry

namespace AddCommGrpCat

/-- Abelian groups whose sections lie in `Type u` have no coproducts indexed by `Type u`. -/
public theorem not_hasColimitsOfShape_discrete_type :
    ¬ HasColimitsOfShape (Discrete (Type u)) AddCommGrpCat.{u} := by
  classical
  intro _
  let G : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} ℤ)
  let f : Type u → AddCommGrpCat.{u} := fun _ => G
  have hid : (𝟙 G) ≠ 0 := fun hh => by
    have h1 : ((𝟙 G) (ULift.up (1 : ℤ))).down = ((0 : G ⟶ G) (ULift.up (1 : ℤ))).down := by
      rw [hh]
    simp at h1
  have hdesc : Function.Injective (fun p : ∀ i, f i ⟶ G => Sigma.desc p) := by
    intro p q hpq
    have hpq' : Sigma.desc p = Sigma.desc q := hpq
    funext i
    rw [← Sigma.ι_comp_desc p i, ← Sigma.ι_comp_desc q i, hpq']
  have _ : Small.{u} (∀ i : Type u, f i ⟶ G) := small_of_injective hdesc
  refine not_small_type.{u, u} (small_of_injective
    (f := fun α : Type u => (fun β : Type u => if α = β then (𝟙 G) else 0 :
      ∀ i : Type u, f i ⟶ G)) ?_)
  intro α₁ α₂ hα
  by_contra hne
  exact hid (by simpa [hne, Ne.symm hne] using congrFun hα α₁)

/-- Abelian groups with sections in `Type u` do not have colimits of every shape one universe
up. -/
public theorem not_hasColimitsOfSize_succ :
    ¬ HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u} :=
  fun h => not_hasColimitsOfShape_discrete_type (h.has_colimits_of_shape _)

end AddCommGrpCat

end
