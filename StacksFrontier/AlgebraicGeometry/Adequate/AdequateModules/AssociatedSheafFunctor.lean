module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedKernel
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSiteAssociatedModule

/-!
# The associated module as a functor on a chosen big site, and `M ↦ (M^~)ᵃ`

`Stacks.Adequate.BigSite.associatedModule` attaches to a quasi-coherent `𝒪_S`-module `𝓖` the
`𝒪`-module `𝓖ᵃ` of [Stacks, Tag 03DU] (3) on a chosen big `τ`-site over `S`, taking the sheaf
condition for the presheaf of pullback sections as a parameter. This module discharges that
parameter once and for all, assembles the construction into the functor `𝓖 ↦ 𝓖ᵃ` of
[Stacks, Tag 03DX], and composes it with `AlgebraicGeometry.tilde` to obtain the functor
`M ↦ (M^~)ᵃ` from `A`-modules to `𝒪`-modules on a chosen big site over `Spec A`.

These are the constructions shared by the two halves of the chapter which handle the affine
case: the converse half of [Stacks, Tag 06VK] and the quasi-inverse of [Stacks, Tag 06ZJ]. They
live here so that both halves name the same constants.

## Main definitions

* `Stacks.Adequate.BigSite.associatedSheafFunctor` — the functor `𝓖 ↦ 𝓖ᵃ` of
  [Stacks, Tag 03DX] on a chosen big site, with no hypotheses.
* `Stacks.Adequate.tildeQuasicoherent` — `M ↦ M^~` as a functor into the quasi-coherent
  `𝒪_{Spec A}`-modules.
* `Stacks.Adequate.associatedTilde` — **the associated `𝒪`-module `M^a` of an `A`-module `M`**,
  as a functor: the composite `M ↦ (M^~)ᵃ`. This is the source's `M ↦ M^a` in the proof of
  [Stacks, Tag 06ZJ].

## Main results

* `Stacks.Adequate.isSheaf_associatedPresheaf` — **the `τ`-sheaf condition of
  [Stacks, Tag 03DU] (3) on a chosen big site, with no hypothesis.** Every chosen big site is
  the localization of an ambient big `τ`-site (`Stacks.Adequate.BigSite.exists_eq_ofAmbient`),
  where the condition is `AlgebraicGeometry.isSheaf_overAssociatedPresheaf`, uniform
  in the five topologies. This is what makes `Stacks.Adequate.BigSite.associatedModule`
  available at an arbitrary quasi-coherent module rather than only where a sheaf condition
  happens to be in hand.
* `Stacks.Adequate.BigSite.associatedSheafFunctor_obj` — the functor agrees on objects with
  `Stacks.Adequate.BigSite.associatedModule`, by definitional unfolding.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace Stacks.Adequate

/-! ### The sheaf condition for an associated module on a chosen big site -/

section AssociatedSheafFunctor

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-- **The sheaf condition of [Stacks, Tag 03DU] (3) on a chosen big site, with no hypothesis.**
The presheaf of sections of the pullbacks of a quasi-coherent `𝒪_S`-module to the schemes of a
chosen big site over `S` is a sheaf for the topology of that site.

Every chosen big site is the localization of an ambient big `τ`-site at its base, by
`Stacks.Adequate.BigSite.exists_eq_ofAmbient`, and there the condition is
[Stacks, Tag 03DU] (3), `AlgebraicGeometry.isSheaf_overAssociatedPresheaf`, which is uniform in
the five topologies. -/
public theorem isSheaf_associatedPresheaf (B : BigSite τ S) (G : S.Modules)
    [G.IsQuasicoherent] :
    Presheaf.IsSheaf B.topology (Stacks.Sites.associatedPresheaf S G B.toOver) := by
  obtain ⟨𝒮, hS, rfl⟩ := B.exists_eq_ofAmbient
  exact AlgebraicGeometry.isSheaf_overAssociatedPresheaf τ 𝒮 S hS G

/-- **The functor `𝓖 ↦ 𝓖ᵃ` of [Stacks, Tag 03DX] on a chosen big site.** It sends a
quasi-coherent `𝒪_S`-module to the `𝒪`-module on the site whose sections over an object are the
global sections of the pullback, and a morphism to the induced map on those sections. -/
public noncomputable def BigSite.associatedSheafFunctor (B : BigSite τ S) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} B.structureSheaf :=
  Stacks.Sites.associatedSheafFunctor S B.toOver B.topology B.isSheaf
    fun M hM => @isSheaf_associatedPresheaf τ S B M hM

/-- The functor `𝓖 ↦ 𝓖ᵃ` of a chosen big site agrees on objects with
`Stacks.Adequate.BigSite.associatedModule`. -/
public theorem BigSite.associatedSheafFunctor_obj (B : BigSite τ S) (G : S.Modules)
    [G.IsQuasicoherent] :
    B.associatedSheafFunctor.obj ⟨G, inferInstance⟩ =
      B.associatedModule G (isSheaf_associatedPresheaf B G) := rfl

end AssociatedSheafFunctor

/-! ### The associated module of an `A`-module -/

section AssociatedTilde

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The quasi-coherent `𝒪_{Spec A}`-module `M^~` of an `A`-module `M`, as a functor into the
quasi-coherent modules. -/
public noncomputable def tildeQuasicoherent :
    ModuleCat.{u} A ⥤ (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (tilde.functor A) fun _ => inferInstance

/-- **The associated `𝒪`-module `M^a` of an `A`-module `M`**, as a functor: the `𝒪`-module on the
chosen big site over `Spec A` associated to the quasi-coherent `𝒪_{Spec A}`-module `M^~`. This
is the source's `M ↦ M^a` in the proof of [Stacks, Tag 06ZJ].

On objects this is `Stacks.Adequate.BigSite.associatedModule` at `M^~`, by
`Stacks.Adequate.BigSite.associatedSheafFunctor_obj`. -/
public noncomputable def associatedTilde :
    ModuleCat.{u} A ⥤ SheafOfModules.{u} B.structureSheaf :=
  tildeQuasicoherent ⋙ B.associatedSheafFunctor

/-- The associated `𝒪`-module of an `A`-module is the associated module of `M^~`, by
definitional unfolding. This is the bridge between the functor and the object-level spelling
`Stacks.Adequate.BigSite.associatedModule`, which is the shape the instances of
`Stacks.Adequate.affineSectionsCompare` are keyed on. -/
public theorem associatedTilde_obj (M : ModuleCat.{u} A) :
    (associatedTilde B).obj M =
      B.associatedModule (tilde M) (isSheaf_associatedPresheaf B (tilde M)) := rfl

end AssociatedTilde

end Stacks.Adequate

end
