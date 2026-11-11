module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleChangeOfRingsSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Localization of a presheaf of modules is extension of scalars

Let `O` be a presheaf of commutative rings on a space `X`, let `S` be a family of multiplicative
subsets `S(U) ⊆ O(U)`, and let `α : O ⟶ Oₛ` exhibit `Oₛ(U)` as the localization of `O(U)` at
`S(U)` for every open `U`. If `ι : F ⟶ Fₛ` likewise localizes a presheaf of `O`-modules
sectionwise, then `Fₛ` is canonically the extension of scalars `F ⊗_O Oₛ`. Sheafifying, and
composing `α` with a locally bijective map `σ : Oₛ ⟶ Oₛ'` to a sheaf of rings, the same holds
for sheaves: the sheafification of `Fₛ` is the tensor product sheaf `F ⊗_O Oₛ'`.

These are the two displayed equalities of Stacks 01D1.

## Main definitions

* `Stacks.Presheaf.Localization.IsSectionwiseLocalization`: a morphism of presheaves of
  commutative rings which is a localization at a prescribed family of multiplicative subsets on
  every open.
* `Stacks.Presheaf.Localization.IsSectionwiseLocalizedModule`: the same condition for a morphism
  of presheaves of modules over such a morphism of ring presheaves.
* `Stacks.Presheaf.Localization.moduleSheafificationAlong`: sheafification of presheaves of
  modules along a specified locally bijective morphism of ring presheaves.

## Main results

* `Stacks.Presheaf.Localization.isoTensorOfIsSectionwiseLocalizedModule`: the presheaf assertion
  of Stacks 01D1 — a sectionwise localization of a presheaf of modules is canonically isomorphic
  to the sectionwise extension of scalars.
* `Stacks.Presheaf.Localization.sheafificationIsoTensorOfIsSectionwiseLocalizedModule`: the sheaf
  assertion — after sheafification this becomes the tensor product of sheaves of modules.

Both hold for a space, rings and modules in an arbitrary universe `u`.
`sectionwiseLocalizedModuleIsoTensor` and `sheafificationSectionwiseLocalizedModuleIsoTensor`
are the same two isomorphisms stated in universe `0`; the primed helpers
(`moduleSheafificationAlong'`, `sheafifyAlongTensorIso'`, ...) are the universe-polymorphic
forms of the unprimed ones, which are stated in universe `0`.

## Implementation notes

Both localizations are characterized by the predicates `IsLocalization` and
`IsLocalizedModule` rather than by choosing quotient models, so the first result states the
first displayed equality of Stacks 01D1 canonically: it produces the comparison isomorphism from
the given maps instead of asserting that some isomorphism exists.

The presheaf comparison is built open by open. Over a fixed `U` the canonical map
`Oₛ(U) ⊗_{O(U)} F(U) ⟶ Fₛ(U)` is the adjunct of `ι` under the universal property
`Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafHomEquiv` of the tensor product presheaf,
  and it is bijective
because both sides are localizations of `F(U)` at `S(U)`: the source by
`IsLocalization.tensorProduct_isLocalizedModule`, the target by hypothesis. Uniqueness of a
localization map (`IsLocalizedModule.ext`) identifies it with
`IsLocalizedModule.linearEquiv`, hence it is an isomorphism; `PresheafOfModules.isoMk` then
assembles the sectionwise isomorphisms.

The sheaf assertion needs one further comparison, `sheafifyAlongTensorIso`: sheafifying
`F ⊗_{p,O} Oₛ` along `σ` gives the tensor product sheaf `F ⊗_O Oₛ'`. It is obtained by Yoneda
from `sheafifyAlongTensorHomEquiv`, the composite of the universal property of module
sheafification along `σ` with the two tensor-product universal properties `008A`, so no model of
either sheafification is used. This is a different statement from Tag 0GMW
(`PresheafOfModules.sheafificationTensorIso`), where sheafification commutes with the tensor
product over a *fixed* ring; here the ring changes along `σ` as well.

The morphism of presheaves of rings underlying `σ` is
  `Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap`, which is
also the map along which `Stacks.Sheafify.ChangeOfRingsAdjunction.restrictPresheaf` restricts
  scalars; it is not
redefined here.

## References

* [Stacks Project, Tag 01D1](https://stacks.math.columbia.edu/tag/01D1)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheafify.ModuleStalkTensor

namespace Stacks.Presheaf.Localization

universe u v

variable {X : TopCat}

/-- A morphism `O ⟶ Oₛ` of presheaves of commutative rings is sectionwise localization at
the family of submonoids `S` when every `O(U) ⟶ Oₛ(U)` exhibits the target as the
localization at `S(U)`. -/
def IsSectionwiseLocalization (O Oₛ : TopCat.Presheaf CommRingCat X) (α : O ⟶ Oₛ)
    (S : (U : (TopologicalSpace.Opens X)ᵒᵖ) → Submonoid (O.obj U)) : Prop :=
  ∀ U,
    letI : Algebra (O.obj U) (Oₛ.obj U) := (α.app U).hom.toAlgebra
    IsLocalization (S U) (Oₛ.obj U)

/-- A morphism `F ⟶ Fₛ` over a sectionwise localization `O ⟶ Oₛ` is a sectionwise
localization of modules when each component is an `IsLocalizedModule` map. -/
def IsSectionwiseLocalizedModule (O Oₛ : TopCat.Presheaf CommRingCat X) (α : O ⟶ Oₛ)
    (S : (U : (TopologicalSpace.Opens X)ᵒᵖ) → Submonoid (O.obj U))
    (F : PresheafOfModules (ringPresheaf O))
    (Fₛ : PresheafOfModules (ringPresheaf Oₛ))
    (ι : F ⟶ Stacks.Sheafify.ChangeOfRingsAdjunction.restrictPresheaf O Oₛ α Fₛ) : Prop :=
  ∀ U, IsLocalizedModule (S U) (ι.app U).hom

/-- Sheafification of modules along a specified locally bijective morphism of ring
presheaves, for a space in a universe `v` and rings in a universe `u`.  The local-bijectivity
witnesses are explicit so this construction can occur in the conclusion of a theorem. -/
noncomputable def moduleSheafificationAlong' {X : TopCat.{v}}
    {R₀ : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (f : R₀ ⟶ R.obj)
    (hf₁ : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f)
    (hf₂ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f) :
    PresheafOfModules R₀ ⥤ SheafOfModules R :=
  letI := hf₁
  letI := hf₂
  PresheafOfModules.sheafification f

/-- Sheafification of modules along a specified locally bijective morphism of ring
presheaves.  The local-bijectivity witnesses are explicit so this construction can occur in
the conclusion of a theorem.  The space lies in universe `0`; `moduleSheafificationAlong'` is
the same construction for a space in any universe. -/
noncomputable def moduleSheafificationAlong
    {R₀ : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat}
    {R : Sheaf (Opens.grothendieckTopology X) RingCat} (f : R₀ ⟶ R.obj)
    (hf₁ : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) f)
    (hf₂ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f) :
    PresheafOfModules R₀ ⥤ SheafOfModules R :=
  letI := hf₁
  letI := hf₂
  PresheafOfModules.sheafification f

private theorem tensorSheafHomEquiv_naturality
    (O Oₛ : TopCat.Sheaf CommRingCat X) (α : O ⟶ Oₛ)
    (F : SheafOfModules (ringSheaf O))
    {M N : SheafOfModules (ringSheaf Oₛ)}
    (f : tensorSheaf O Oₛ α F ⟶ M) (g : M ⟶ N) :
    Stacks.Sheafify.ChangeOfRingsAdjunction.tensorSheafHomEquiv O Oₛ α F N (f ≫ g) =
      Stacks.Sheafify.ChangeOfRingsAdjunction.tensorSheafHomEquiv O Oₛ α F M f ≫
        (SheafOfModules.restrictScalars (Stacks.Sheafify.ChangeOfRingsAdjunction.ringSheafMap O Oₛ
          α)).map g := by
  ext U m
  rfl

private theorem tensorSheafHomEquiv'_naturality {X : TopCat.{u}}
    (O Oₛ : TopCat.Sheaf CommRingCat.{u} X) (α : O ⟶ Oₛ)
    (F : SheafOfModules.{u} (ringSheaf O))
    {M N : SheafOfModules.{u} (ringSheaf Oₛ)}
    (f : tensorSheaf O Oₛ α F ⟶ M) (g : M ⟶ N) :
    Stacks.Sheafify.ChangeOfRingsAdjunction.tensorSheafHomEquiv' O Oₛ α F N (f ≫ g) =
      Stacks.Sheafify.ChangeOfRingsAdjunction.tensorSheafHomEquiv' O Oₛ α F M f ≫
        (SheafOfModules.restrictScalars (Stacks.Sheafify.ChangeOfRingsAdjunction.ringSheafMap' O Oₛ
          α)).map g := by
  ext U m
  rfl

/-- Restricting a sheaf of modules along two successive ring maps agrees with restricting
along their composite, for a space, rings and modules in any universe `u`. -/
noncomputable def restrictPresheafToSheafIso' {X : TopCat.{u}}
    (O : TopCat.Sheaf CommRingCat.{u} X) (Oₛ : TopCat.Presheaf CommRingCat.{u} X)
    (Oₛ' : TopCat.Sheaf CommRingCat.{u} X) (α : O.presheaf ⟶ Oₛ) (σ : Oₛ ⟶ Oₛ'.presheaf)
    (G : SheafOfModules.{u} (ringSheaf Oₛ')) :
    Stacks.Sheafify.ChangeOfRingsAdjunction.restrictPresheaf O.presheaf Oₛ α
      ((PresheafOfModules.restrictScalars
        (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)).obj G.val) ≅
      ((SheafOfModules.restrictScalars (Stacks.Sheafify.ChangeOfRingsAdjunction.ringSheafMap' O Oₛ'
        ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv.symm
          (α ≫ σ)))).obj G).val :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intros; rfl)

/-- Restricting a sheaf of modules along two successive ring maps agrees with restricting
along their composite. The space lies in universe `0`; `restrictPresheafToSheafIso'` is the
same isomorphism for a space in any universe. -/
noncomputable def restrictPresheafToSheafIso
    (O : TopCat.Sheaf CommRingCat X) (Oₛ : TopCat.Presheaf CommRingCat X)
    (Oₛ' : TopCat.Sheaf CommRingCat X) (α : O.presheaf ⟶ Oₛ) (σ : Oₛ ⟶ Oₛ'.presheaf)
    (G : SheafOfModules (ringSheaf Oₛ')) :
    Stacks.Sheafify.ChangeOfRingsAdjunction.restrictPresheaf O.presheaf Oₛ α
      ((PresheafOfModules.restrictScalars
        (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)).obj G.val) ≅
      ((SheafOfModules.restrictScalars (Stacks.Sheafify.ChangeOfRingsAdjunction.ringSheafMap O Oₛ'
        ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat).homEquiv.symm
          (α ≫ σ)))).obj G).val :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intros; rfl)

/-- The Hom equivalence comparing the two sheafifications of the tensor product: it is the
composite of the universal property of module sheafification along `σ` with the two
tensor-product universal properties of Stacks 008A, read through restriction of scalars. The
space, the rings and the modules live in any universe `u`. -/
noncomputable def sheafifyAlongTensorHomEquiv' {X : TopCat.{u}}
    (O : TopCat.Sheaf CommRingCat.{u} X) (Oₛ : TopCat.Presheaf CommRingCat.{u} X)
    (Oₛ' : TopCat.Sheaf CommRingCat.{u} X) (α : O.presheaf ⟶ Oₛ) (σ : Oₛ ⟶ Oₛ'.presheaf)
    (F : SheafOfModules.{u} (ringSheaf O))
    (hσi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ))
    (hσs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ))
    (G : SheafOfModules.{u} (ringSheaf Oₛ')) :
    ((moduleSheafificationAlong' (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ
      Oₛ'.presheaf σ) hσi hσs).obj
        (tensorPresheafOfModules O.presheaf Oₛ α F.val) ⟶ G) ≃
      (tensorSheaf O Oₛ'
        ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv.symm
          (α ≫ σ)) F ⟶ G) :=
  (@PresheafOfModules.sheafificationHomEquiv
    (TopologicalSpace.Opens X) _ (Opens.grothendieckTopology X)
    (ringPresheaf Oₛ) (ringSheaf Oₛ') (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ
      Oₛ'.presheaf σ) hσi hσs
    inferInstance inferInstance (tensorPresheafOfModules O.presheaf Oₛ α F.val) G).trans
    ((Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafHomEquiv O.presheaf Oₛ α F.val
      ((PresheafOfModules.restrictScalars
        (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)).obj
          G.val)).trans
    (((Iso.homCongr (Iso.refl _) (restrictPresheafToSheafIso' O Oₛ Oₛ' α σ G)).trans
      ((SheafOfModules.fullyFaithfulForget (ringSheaf O)).homEquiv
        (X := F) (Y := (SheafOfModules.restrictScalars
          (Stacks.Sheafify.ChangeOfRingsAdjunction.ringSheafMap' O Oₛ'
            ((fullyFaithfulSheafToPresheaf
              (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv.symm
                (α ≫ σ)))).obj G)).symm).trans
        ((Stacks.Sheafify.ChangeOfRingsAdjunction.tensorSheafHomEquiv' O Oₛ'
          ((fullyFaithfulSheafToPresheaf
            (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv.symm (α ≫ σ)) F G).symm)))

/-- The Hom equivalence comparing the two sheafifications of the tensor product: it is the
composite of the universal property of module sheafification along `σ` with the two
tensor-product universal properties of Stacks 008A, read through restriction of scalars.
This is `sheafifyAlongTensorHomEquiv'` for a space in universe `0`. -/
noncomputable def sheafifyAlongTensorHomEquiv
    (O : TopCat.Sheaf CommRingCat X) (Oₛ : TopCat.Presheaf CommRingCat X)
    (Oₛ' : TopCat.Sheaf CommRingCat X) (α : O.presheaf ⟶ Oₛ) (σ : Oₛ ⟶ Oₛ'.presheaf)
    (F : SheafOfModules (ringSheaf O))
    (hσi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ))
    (hσs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ))
    (G : SheafOfModules (ringSheaf Oₛ')) :
    ((moduleSheafificationAlong (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ
      Oₛ'.presheaf σ) hσi hσs).obj
        (tensorPresheafOfModules O.presheaf Oₛ α F.val) ⟶ G) ≃
      (tensorSheaf O Oₛ'
        ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat).homEquiv.symm
          (α ≫ σ)) F ⟶ G) :=
  sheafifyAlongTensorHomEquiv' O Oₛ Oₛ' α σ F hσi hσs G

/-- **Sheafification along `σ` commutes with the change-of-rings tensor product.**  The
isomorphism of sheaves of `Oₛ'`-modules obtained from `sheafifyAlongTensorHomEquiv'` by Yoneda;
its naturality is the naturality of each of the three Hom equivalences in turn. The space, the
rings and the modules live in any universe `u`. -/
noncomputable def sheafifyAlongTensorIso' {X : TopCat.{u}}
    (O : TopCat.Sheaf CommRingCat.{u} X) (Oₛ : TopCat.Presheaf CommRingCat.{u} X)
    (Oₛ' : TopCat.Sheaf CommRingCat.{u} X) (α : O.presheaf ⟶ Oₛ) (σ : Oₛ ⟶ Oₛ'.presheaf)
    (F : SheafOfModules.{u} (ringSheaf O))
    (hσi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ))
    (hσs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)) :
    (moduleSheafificationAlong' (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ
      Oₛ'.presheaf σ) hσi hσs).obj
        (tensorPresheafOfModules O.presheaf Oₛ α F.val) ≅
      tensorSheaf O Oₛ'
        ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv.symm
          (α ≫ σ)) F := by
  haveI := hσi
  haveI := hσs
  exact (Coyoneda.ext _ _
    (fun f => (sheafifyAlongTensorHomEquiv' O Oₛ Oₛ' α σ F hσi hσs _).symm f)
    (fun f => sheafifyAlongTensorHomEquiv' O Oₛ Oₛ' α σ F hσi hσs _ f)
    (fun f => (sheafifyAlongTensorHomEquiv' O Oₛ Oₛ' α σ F hσi hσs _).apply_symm_apply f)
    (fun f => (sheafifyAlongTensorHomEquiv' O Oₛ Oₛ' α σ F hσi hσs _).symm_apply_apply f)
    (by
      intro Z Z' f g
      let A (Z : SheafOfModules.{u} (ringSheaf Oₛ')) :=
        @PresheafOfModules.sheafificationHomEquiv
          (TopologicalSpace.Opens X) _ (Opens.grothendieckTopology X)
          (ringPresheaf Oₛ) (ringSheaf Oₛ') (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap
            Oₛ Oₛ'.presheaf σ)
          hσi hσs inferInstance inferInstance
          (tensorPresheafOfModules O.presheaf Oₛ α F.val) Z
      have hA' : A Z' (f ≫ g) = A Z f ≫
          (PresheafOfModules.restrictScalars
            (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)).map
              g.val :=
        (@PresheafOfModules.sheafificationAdjunction
          (TopologicalSpace.Opens X) _ (Opens.grothendieckTopology X)
          (ringPresheaf Oₛ) (ringSheaf Oₛ')
          (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)
          hσi hσs inferInstance inferInstance).homEquiv_naturality_right f g
      let β : O ⟶ Oₛ' := (fullyFaithfulSheafToPresheaf
        (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv.symm (α ≫ σ)
      let D (Z : SheafOfModules.{u} (ringSheaf Oₛ')) :=
        Stacks.Sheafify.ChangeOfRingsAdjunction.tensorSheafHomEquiv' O Oₛ' β F Z
      let B (Z : SheafOfModules.{u} (ringSheaf Oₛ')) :=
        Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafHomEquiv O.presheaf Oₛ α F.val
          ((PresheafOfModules.restrictScalars
            (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)).obj Z.val)
      let C (Z : SheafOfModules.{u} (ringSheaf Oₛ')) :=
        ((Iso.homCongr (Iso.refl _) (restrictPresheafToSheafIso' O Oₛ Oₛ' α σ Z)).trans
          ((SheafOfModules.fullyFaithfulForget (ringSheaf O)).homEquiv
            (X := F) (Y := (SheafOfModules.restrictScalars
              (Stacks.Sheafify.ChangeOfRingsAdjunction.ringSheafMap' O Oₛ' β)).obj Z)).symm)
      apply (D Z').injective
      change (D Z') ((D Z').symm (C Z' (B Z' (A Z' (f ≫ g))))) =
        (D Z') (((D Z).symm (C Z (B Z (A Z f)))) ≫ g)
      rw [Equiv.apply_symm_apply, tensorSheafHomEquiv'_naturality, Equiv.apply_symm_apply, hA']
      ext U x
      rfl)).symm

/-- **Sheafification along `σ` commutes with the change-of-rings tensor product.**  The
isomorphism of sheaves of `Oₛ'`-modules obtained from `sheafifyAlongTensorHomEquiv` by Yoneda;
its naturality is the naturality of each of the three Hom equivalences in turn.
This is `sheafifyAlongTensorIso'` for a space in universe `0`. -/
noncomputable def sheafifyAlongTensorIso
    (O : TopCat.Sheaf CommRingCat X) (Oₛ : TopCat.Presheaf CommRingCat X)
    (Oₛ' : TopCat.Sheaf CommRingCat X) (α : O.presheaf ⟶ Oₛ) (σ : Oₛ ⟶ Oₛ'.presheaf)
    (F : SheafOfModules (ringSheaf O))
    (hσi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ))
    (hσs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)) :
    (moduleSheafificationAlong (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ
      Oₛ'.presheaf σ) hσi hσs).obj
        (tensorPresheafOfModules O.presheaf Oₛ α F.val) ≅
      tensorSheaf O Oₛ'
        ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat).homEquiv.symm
          (α ≫ σ)) F :=
  sheafifyAlongTensorIso' O Oₛ Oₛ' α σ F hσi hσs

/-- **Stacks Project, Tag 01D1, presheaf assertion.**

Any sectionwise localization of a presheaf of modules is canonically isomorphic to extension
of scalars from the original presheaf of rings to its sectionwise localization. The space, the
rings and the modules live in an arbitrary universe `u`. -/
@[stacks 01D1 "presheaf assertion, in every universe"]
noncomputable def isoTensorOfIsSectionwiseLocalizedModule {X : TopCat.{u}}
    (O Oₛ : TopCat.Presheaf CommRingCat.{u} X) (α : O ⟶ Oₛ)
    (S : (U : (TopologicalSpace.Opens X)ᵒᵖ) → Submonoid (O.obj U))
    (F : PresheafOfModules.{u} (ringPresheaf O))
    (Fₛ : PresheafOfModules.{u} (ringPresheaf Oₛ))
    (ι : F ⟶ Stacks.Sheafify.ChangeOfRingsAdjunction.restrictPresheaf O Oₛ α Fₛ)
    (hO : IsSectionwiseLocalization O Oₛ α S)
    (hF : IsSectionwiseLocalizedModule O Oₛ α S F Fₛ ι) :
    Fₛ ≅ tensorPresheafOfModules O Oₛ α F := by
  let q : tensorPresheafOfModules O Oₛ α F ⟶ Fₛ :=
    (Stacks.Sheafify.ChangeOfRingsAdjunction.tensorPresheafHomEquiv O Oₛ α F Fₛ).symm ι
  let e : (U : (TopologicalSpace.Opens X)ᵒᵖ) →
      Fₛ.obj U ≅ (tensorPresheafOfModules O Oₛ α F).obj U := fun U => by
    letI : Algebra (O.obj U) (Oₛ.obj U) := (α.app U).hom.toAlgebra
    change Fₛ.obj U ≅ ModuleCat.of (Oₛ.obj U)
      (TensorProduct (O.obj U) (Oₛ.obj U) (F.obj U))
    letI : IsLocalization (S U) (Oₛ.obj U) := hO U
    letI : IsLocalizedModule (S U) (ι.app U).hom := hF U
    let j : F.obj U →ₗ[O.obj U]
        TensorProduct (O.obj U) (Oₛ.obj U) (F.obj U) :=
      TensorProduct.mk (O.obj U) (Oₛ.obj U) (F.obj U) 1
    letI : IsLocalizedModule (S U) j :=
      IsLocalization.tensorProduct_isLocalizedModule (S U) (Oₛ.obj U)
    let qr := (ModuleCat.restrictScalars
      ((Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap O Oₛ α).app U).hom).map (q.app U)
    let le := (IsLocalizedModule.linearEquiv (S U) j (ι.app U).hom).toLinearMap
    have hq : qr.hom = le := by
      apply IsLocalizedModule.ext (S U) j (IsLocalizedModule.map_units (ι.app U).hom)
      ext m
      change ((Stacks.Sheafify.ChangeOfRingsAdjunction.sectionEquiv O Oₛ α F Fₛ U).symm
        (ι.app U)).hom (1 ⊗ₜ[O.obj U] m) = le (j m)
      rw [← Stacks.Sheafify.ChangeOfRingsAdjunction.sectionEquiv_apply, Equiv.apply_symm_apply]
      exact (IsLocalizedModule.linearEquiv_apply (S U) j (ι.app U).hom m).symm
    haveI : IsIso (q.app U) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective qr
      rw [show (qr : _ → _) = le from congrArg DFunLike.coe hq]
      exact (IsLocalizedModule.linearEquiv (S U) j (ι.app U).hom).bijective
    exact (asIso (q.app U)).symm
  exact PresheafOfModules.isoMk e (by
    intro U V i
    apply (cancel_mono ((ModuleCat.restrictScalars
      ((ringPresheaf Oₛ).map i).hom).map (e V).inv)).1
    simpa [e, Category.assoc] using (q.naturality i).symm)

/-- **Stacks Project, Tag 01D1, sheaf assertion.**

If `O` and `F` are sheaves, sheafifying a sectionwise localization `Fₛ` along a
sheafification `Oₛ ⟶ Oₛ♯` gives the tensor product of `F` with `Oₛ♯` over `O`. The space, the
rings and the modules live in an arbitrary universe `u`. -/
@[stacks 01D1 "sheaf assertion, in every universe"]
noncomputable def sheafificationIsoTensorOfIsSectionwiseLocalizedModule {X : TopCat.{u}}
    (O : TopCat.Sheaf CommRingCat.{u} X) (Oₛ : TopCat.Presheaf CommRingCat.{u} X)
    (Oₛ' : TopCat.Sheaf CommRingCat.{u} X) (α : O.presheaf ⟶ Oₛ) (σ : Oₛ ⟶ Oₛ'.presheaf)
    (S : (U : (TopologicalSpace.Opens X)ᵒᵖ) → Submonoid (O.presheaf.obj U))
    (F : SheafOfModules.{u} (ringSheaf O))
    (Fₛ : PresheafOfModules.{u} (ringPresheaf Oₛ))
    (ι : F.val ⟶ Stacks.Sheafify.ChangeOfRingsAdjunction.restrictPresheaf O.presheaf Oₛ α Fₛ)
    (hO : IsSectionwiseLocalization O.presheaf Oₛ α S)
    (hF : IsSectionwiseLocalizedModule O.presheaf Oₛ α S F.val Fₛ ι)
    (hσi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ))
    (hσs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)) :
    (moduleSheafificationAlong' (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ
      Oₛ'.presheaf σ) hσi hσs).obj Fₛ ≅
      tensorSheaf O Oₛ'
        ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{u}).homEquiv.symm
          (α ≫ σ)) F :=
  (moduleSheafificationAlong' (R₀ := ringPresheaf Oₛ) (R := ringSheaf Oₛ')
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ) hσi hσs).mapIso
      (isoTensorOfIsSectionwiseLocalizedModule O.presheaf Oₛ α S F.val Fₛ ι hO hF) ≪≫
    sheafifyAlongTensorIso' O Oₛ Oₛ' α σ F hσi hσs

/-- The presheaf assertion of Stacks 01D1 for a space, rings and modules in universe `0`: any
sectionwise localization of a presheaf of modules is canonically isomorphic to extension of
scalars to the sectionwise localization. This is `isoTensorOfIsSectionwiseLocalizedModule`
in universe `0`. -/
noncomputable def sectionwiseLocalizedModuleIsoTensor
    (O Oₛ : TopCat.Presheaf CommRingCat X) (α : O ⟶ Oₛ)
    (S : (U : (TopologicalSpace.Opens X)ᵒᵖ) → Submonoid (O.obj U))
    (F : PresheafOfModules.{0} (ringPresheaf O))
    (Fₛ : PresheafOfModules.{0} (ringPresheaf Oₛ))
    (ι : F ⟶ Stacks.Sheafify.ChangeOfRingsAdjunction.restrictPresheaf O Oₛ α Fₛ)
    (hO : IsSectionwiseLocalization O Oₛ α S)
    (hF : IsSectionwiseLocalizedModule O Oₛ α S F Fₛ ι) :
    Fₛ ≅ tensorPresheafOfModules O Oₛ α F :=
  isoTensorOfIsSectionwiseLocalizedModule O Oₛ α S F Fₛ ι hO hF

/-- The sheaf assertion of Stacks 01D1 for a space, rings and modules in universe `0`: if `O`
and `F` are sheaves, sheafifying a sectionwise localization `Fₛ` along a sheafification
`Oₛ ⟶ Oₛ♯` gives the tensor product of `F` with `Oₛ♯` over `O`. This is
`sheafificationIsoTensorOfIsSectionwiseLocalizedModule` in universe `0`. -/
noncomputable def sheafificationSectionwiseLocalizedModuleIsoTensor
    (O : TopCat.Sheaf CommRingCat X) (Oₛ : TopCat.Presheaf CommRingCat X)
    (Oₛ' : TopCat.Sheaf CommRingCat X) (α : O.presheaf ⟶ Oₛ) (σ : Oₛ ⟶ Oₛ'.presheaf)
    (S : (U : (TopologicalSpace.Opens X)ᵒᵖ) → Submonoid (O.presheaf.obj U))
    (F : SheafOfModules (ringSheaf O))
    (Fₛ : PresheafOfModules (ringPresheaf Oₛ))
    (ι : F.val ⟶ Stacks.Sheafify.ChangeOfRingsAdjunction.restrictPresheaf O.presheaf Oₛ α Fₛ)
    (hO : IsSectionwiseLocalization O.presheaf Oₛ α S)
    (hF : IsSectionwiseLocalizedModule O.presheaf Oₛ α S F.val Fₛ ι)
    (hσi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ))
    (hσs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ Oₛ'.presheaf σ)) :
    (moduleSheafificationAlong (Stacks.Sheafify.ChangeOfRingsAdjunction.ringPresheafMap Oₛ
      Oₛ'.presheaf σ) hσi hσs).obj Fₛ ≅
      tensorSheaf O Oₛ'
        ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) CommRingCat).homEquiv.symm
          (α ≫ σ)) F :=
  sheafificationIsoTensorOfIsSectionwiseLocalizedModule O Oₛ Oₛ' α σ S F Fₛ ι hO hF hσi hσs

end Stacks.Presheaf.Localization

end
