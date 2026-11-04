module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationUnitSections
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.SheafifyRestrict

/-!
# Surjectivity of the sheafification unit on the sections over one object

Sheafification of presheaves of modules is locally bijective but not bijective on sections, so
nothing general identifies `P(Z)` with the sections of `P^#` over `Z`. **This file isolates the
one criterion that does**: if `P` admits a locally bijective morphism into the underlying
presheaf of a *sheaf* of modules `N`, then the sheafification unit is surjective on the sections
over an object exactly when that morphism is. Over an affine scheme such an `N` is an associated
sheaf, which is how the sections of a sheafified presheaf over an affine open become computable.

## Main results

* `Stacks.PresheafOfModules.bijective_hom_app`: an isomorphism of presheaves of modules is
  bijective on the sections over every object.
* `Stacks.PresheafOfModules.bijective_sheafifyUnit_forget`: **the sheafification unit of the
  underlying presheaf of a sheaf of modules is bijective on sections.**
* `Stacks.PresheafOfModules.surjective_sheafifyUnit_app_iff`: **the criterion.** For a locally
  bijective `u : P ⟶ N` with `N` a sheaf of modules, the unit of `P` is surjective on the
  sections over `Z` if and only if `u` is.
The companion statement with no sheaf involved — surjectivity of the unit on sections transfers
along a locally bijective morphism of presheaves of modules — is
`Stacks.PresheafOfModules.surjective_sheafifyUnit_app_of_isLocallyBijective`, re-exported here
from `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationUnitSections`.

## Implementation notes

**Both criteria are the same commuting square.** Naturality of the sheafification unit reads
`unit_P ≫ (sheafification u) = u ≫ unit_N`, and three of its four maps are bijective on the
sections over a fixed object: `sheafification u` because sheafification inverts a locally
bijective morphism
(`Stacks.PresheafOfModules.isIso_sheafification_map_of_isLocallyBijective`), and `unit_N` because
the counit of the sheafification adjunction is an isomorphism at a sheaf, so the right triangle
identity exhibits `unit_N` as a two-sided inverse on sections. Surjectivity of the fourth map is
therefore equivalent to surjectivity of the remaining one.

**Local bijectivity is an ordinary argument, not an instance.** This follows
`Stacks.PresheafOfModules.sheafificationIsoOfIsLocallyBijective`, and for the same
reason: at the shape these lemmas are applied at — a comparison into an associated sheaf on
`Spec R` — instance search does not find `Stacks.AffineBaseChange.isLocallySurjective_toTilde`,
although the declaration is an instance.

## References

* [Stacks Project, Tag 00WY](https://stacks.math.columbia.edu/tag/00WY)

## Not done here

Injectivity of the unit on sections is not recorded, although the same square gives it by the
same argument: no consumer needs it. Nothing here is specific to schemes or to a symmetric
algebra.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.PresheafOfModules

universe v u t a

section IsoApp

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}}

/-- **A morphism of presheaves of modules that is an isomorphism is an isomorphism on the
sections over every object.** The inverse is the inverse morphism's component, and the two round
trips are the components of the two round trips of the morphism. -/
instance isIso_hom_app {M N : _root_.PresheafOfModules.{a} R} (φ : M ⟶ N) [IsIso φ] (Z : Cᵒᵖ) :
    IsIso (_root_.PresheafOfModules.Hom.app φ Z) :=
  ⟨_root_.PresheafOfModules.Hom.app (inv φ) Z, by
    rw [← _root_.PresheafOfModules.comp_app, IsIso.hom_inv_id,
      _root_.PresheafOfModules.id_app], by
    rw [← _root_.PresheafOfModules.comp_app, IsIso.inv_hom_id,
      _root_.PresheafOfModules.id_app]⟩

/-- An isomorphism of presheaves of modules is bijective on the sections over every object. -/
theorem bijective_hom_app {M N : _root_.PresheafOfModules.{a} R} (φ : M ⟶ N) [IsIso φ]
    (Z : Cᵒᵖ) :
    Function.Bijective fun x => _root_.PresheafOfModules.Hom.app φ Z x :=
  ConcreteCategory.bijective_of_isIso _

end IsoApp


section Unit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- **The sheafification unit of the underlying presheaf of a sheaf of modules is bijective on
the sections over every object.** The counit of the sheafification adjunction is an isomorphism
at a sheaf, and the right triangle identity makes its component a two-sided inverse of the
unit. -/
theorem bijective_sheafifyUnit_forget (N : SheafOfModules.{a} R) (Z : Cᵒᵖ) :
    Function.Bijective fun x => _root_.PresheafOfModules.Hom.app
      (_root_.PresheafOfModules.sheafifyUnit α
        ((SheafOfModules.forget R ⋙ _root_.PresheafOfModules.restrictScalars α).obj N)) Z x := by
  set G := SheafOfModules.forget R ⋙ _root_.PresheafOfModules.restrictScalars α with hG
  have hiso : IsIso ((_root_.PresheafOfModules.sheafificationAdjunction.{a} α).counit.app N) :=
    inferInstance
  have hg : Function.Bijective fun x => _root_.PresheafOfModules.Hom.app
      (G.map ((_root_.PresheafOfModules.sheafificationAdjunction.{a} α).counit.app N)) Z x :=
    bijective_hom_app _ Z
  have htri := (_root_.PresheafOfModules.sheafificationAdjunction.{a} α).right_triangle_components N
  have hcomp : (fun x => _root_.PresheafOfModules.Hom.app
      (G.map ((_root_.PresheafOfModules.sheafificationAdjunction.{a} α).counit.app N)) Z x) ∘
      (fun x => _root_.PresheafOfModules.Hom.app
        (_root_.PresheafOfModules.sheafifyUnit α (G.obj N)) Z x) = id :=
    funext fun x => (_root_.PresheafOfModules.hom_congr_apply' htri Z x).trans rfl
  exact (hg.of_comp_iff' _).1 (hcomp ▸ Function.bijective_id)

/-- **Surjectivity of the sheafification unit on the sections over one object, from a locally
bijective comparison with a sheaf.** For `u : P ⟶ N` locally bijective with `N` a sheaf of
modules, the unit of `P` is surjective on the sections over `Z` precisely when `u` is. This is
the criterion that makes the sections of a sheafification over an affine open computable: there
`N` is an associated sheaf and `u` is the base-change comparison. -/
theorem surjective_sheafifyUnit_app_iff {P : _root_.PresheafOfModules.{a} R₀}
    (N : SheafOfModules.{a} R)
    (u : P ⟶ (SheafOfModules.forget R ⋙ _root_.PresheafOfModules.restrictScalars α).obj N)
    (hinj : _root_.PresheafOfModules.IsLocallyInjective J u)
    (hsurj : _root_.PresheafOfModules.IsLocallySurjective J u) (Z : Cᵒᵖ) :
    (Function.Surjective fun x =>
        _root_.PresheafOfModules.Hom.app (_root_.PresheafOfModules.sheafifyUnit α P) Z x) ↔
      (Function.Surjective fun x => _root_.PresheafOfModules.Hom.app u Z x) := by
  have := hinj
  have := hsurj
  have := isIso_sheafification_map_of_isLocallyBijective α u
  have : IsIso ((( _root_.PresheafOfModules.sheafification.{a} α).map u).val) :=
    inferInstanceAs (IsIso ((SheafOfModules.forget R).map
      ((_root_.PresheafOfModules.sheafification.{a} α).map u)))
  have hpsi := bijective_hom_app (((_root_.PresheafOfModules.sheafification.{a} α).map u).val) Z
  have hN := bijective_sheafifyUnit_forget α N Z
  have hnat := fun x => _root_.PresheafOfModules.unit_naturality_apply (α := α) u Z x
  constructor
  · intro hs t
    obtain ⟨w, hw⟩ := hpsi.2 (_root_.PresheafOfModules.Hom.app
      (_root_.PresheafOfModules.sheafifyUnit α
        ((SheafOfModules.forget R ⋙ _root_.PresheafOfModules.restrictScalars α).obj N)) Z t)
    obtain ⟨x, hx⟩ := hs w
    exact ⟨x, hN.1 (((hnat x).symm.trans (congrArg _ hx)).trans hw)⟩
  · intro hu s
    obtain ⟨t, ht⟩ := hN.2 (_root_.PresheafOfModules.Hom.app
      (((_root_.PresheafOfModules.sheafification.{a} α).map u).val) Z s)
    obtain ⟨x, hx⟩ := hu t
    exact ⟨x, hpsi.1 (((hnat x).trans (congrArg _ hx)).trans ht)⟩

end Unit

end Stacks.PresheafOfModules

end
