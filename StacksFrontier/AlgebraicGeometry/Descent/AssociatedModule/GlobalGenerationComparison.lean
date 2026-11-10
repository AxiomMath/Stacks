module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.SerreClass
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The five remaining global types of modules under `𝓕 ↦ 𝓕^a`

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison` carries the
comparison of Descent, Proposition 03DX as the associated-module functor itself and lands
clauses (1) and (2) of Modules on Sites, Definition 03DE — free and finite free — at that
functor, on the big site at every `τ` and on the small étale site.  Its implementation note
records why it stops there, and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison` says the same from the
other side: clauses (3)–(7) are proved only for a comparison functor hypothesised to be fully
faithful on the *whole* category of `𝒪_S`-modules, which `𝓕 ↦ 𝓕^a` is not — Stacks 0GN7 gives
full faithfulness only on `QCoh(𝒪_S)`.

**This file lands the remaining five clauses, (3)–(7), at the comparison functor itself**, on
the big site at every `τ` and on the small étale site.

## How the restriction to `QCoh` is got around

Clauses (1) and (2) assert the existence of an *isomorphism* with a free module, and an
isomorphism between two objects of a full subcategory is the same thing in the subcategory and
in the ambient category; that is what
`Stacks.Sheaves.QcohTypeComparison.nonempty_iso_of_mapIso` exploits.  Clauses (3), (4) and (5)
assert the existence of an *epimorphism* from a free module, and clauses (6) and (7) the
existence of a *cokernel* of a map of free modules; neither epimorphy nor a colimit is in
general inherited either way between a full subcategory and its ambient category.  The reverse
implications therefore need three further inputs, and all three are available:

* a **faithful** functor reflects epimorphisms,
  `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`, so `P.ι ⋙ Φ` being fully faithful lets
  an epimorphism in `Mod(S_τ, 𝒪)` be pulled back to an epimorphism *of the full subcategory*
  cut out by `P`;
* the inclusion `P.ι` **preserves epimorphisms**, which carries that conclusion from the
  subcategory to `Mod(𝒪_S)`.  For `P` quasi-coherence on a scheme this is
  `AlgebraicGeometry.DerivedCoherent.preservesEpimorphisms_quasicoherentι`, the quasi-coherent
  modules being a weak Serre subcategory.
* for clauses (6) and (7) the same two steps are taken with a cokernel cofork in place of an
  epimorphism: a fully faithful functor **reflects colimits**, and `P.ι` **preserves finite
  colimits**, which for `P` quasi-coherence on a scheme is
  `AlgebraicGeometry.DerivedCoherent.preservesFiniteColimits_quasicoherentι`.  Crossing the
  boundary in either direction also needs the zero morphism of the cofork to be seen on both
  sides, so `P.ι` and `Φ` must preserve zero morphisms; the quasi-coherent full subcategory is
  `Preadditive` and both functors are additive.

The forward implications need only that `Φ` preserve epimorphisms and cokernels, which it does,
being a left adjoint — `AlgebraicGeometry.BigFppfOver.isLeftAdjoint_baseAssociatedModule` and
`AlgebraicGeometry.SmallEtale.isLeftAdjoint_associatedModule`.

## Main definitions

* `Stacks.Sheaves.QcohTypeComparison.generatingSectionsMap`: a generating family of global
  sections transported forward, indexed by the same type.
* `Stacks.Sheaves.QcohTypeComparison.generatingSectionsOfMap`: a generating family of global
  sections of the image transported back, indexed by the same type.  This is where the first
  two inputs above are used.

## Main results

* `Stacks.Sheaves.QcohTypeComparison.isGeneratedByGlobalSections_iff`,
  `.isGeneratedByGlobalSectionsOfCard_iff`,
  `.exists_isGeneratedByGlobalSectionsOfCard_iff`, `.isPresentedByGlobalSections_iff` and
  `.isFinitelyPresentedByGlobalSections_iff`: clauses 03DE (3)–(7) for a comparison functor
  fully faithful on the full subcategory cut out by `P` only.
* `AlgebraicGeometry.BigFppfOver.isGeneratedByGlobalSections_iff_baseAssociatedModule` and its
  four companions: **Descent, Lemma 05VG for 03DE (3)–(7) on the big site `(Sch/S)_τ`, at
  every `τ`**.
* `AlgebraicGeometry.SmallEtale.isGeneratedByGlobalSections_iff_associatedModule` and its four
  companions: the same **on the small étale site**.

## What this completes, and what it does not

With these, all seven global clauses of 05VG are proved at the comparison functor of 03DX
itself, on the big site at every `τ` and on the small étale site; clauses (1) and (2) are in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison`.  The *local*
clauses of 03DL are untouched here: they quantify over the objects of the site and over
coverings of them, which a functor between categories of modules cannot see, and the
subcategory-boundary argument above says nothing about them.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sheaves.QcohTypeComparison

universe w v₁ u₁ v₂ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {R₁ : Sheaf J₁ RingCat.{w}}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {R₂ : Sheaf J₂ RingCat.{w}}
  [HasWeakSheafify J₁ AddCommGrpCat.{w}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J₂ AddCommGrpCat.{w}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (Φ : SheafOfModules.{w} R₁ ⥤ SheafOfModules.{w} R₂)
  [PreservesColimitsOfSize.{w, w} Φ]
  (u : Φ.obj (SheafOfModules.unit R₁) ≅ SheafOfModules.unit R₂)

/-- Instance search for coproducts of presheaves of modules times out; supply it directly. -/
private instance hasColimitsOfShape_discrete_globalGenerationComparison₁ (J : Type w) :
    HasColimitsOfShape (Discrete J) (PresheafOfModules.{w} R₁.obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

/-- Instance search for coproducts of presheaves of modules times out; supply it directly. -/
private instance hasColimitsOfShape_discrete_globalGenerationComparison₂ (J : Type w) :
    HasColimitsOfShape (Discrete J) (PresheafOfModules.{w} R₂.obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

/-- **A generating family of global sections transported forward.**  The generating map is the
free comparison `Stacks.Sheaves.QcohTypeComparison.mapFreeIso` followed by the image of the
original generating map, an epimorphism because `Φ` preserves epimorphisms.  The index type is
unchanged, so every cardinality clause survives. -/
def generatingSectionsMap [Φ.PreservesEpimorphisms] {F : SheafOfModules.{w} R₁}
    (σ : F.GeneratingSections) : (Φ.obj F).GeneratingSections where
  I := σ.I
  s := (Φ.obj F).freeHomEquiv ((mapFreeIso Φ u σ.I).inv ≫ Φ.map σ.π)
  epi := by
    simp only [Equiv.symm_apply_apply]
    have hσ : Epi σ.π := σ.epi
    exact epi_comp' (IsIso.epi_of_iso _) (Φ.map_epi σ.π)

variable (P : ObjectProperty (SheafOfModules.{w} R₁))

/-- **A generating family of global sections of the image transported back.**  The generating
map is read through the free comparison and then pulled back along `Φ`, which is possible
because both the free module and `F` satisfy `P` and `Φ` is full on the subcategory cut out by
`P`.  That the result is again an epimorphism is the two-step argument described in the module
docstring: `P.ι ⋙ Φ` is faithful, hence reflects epimorphisms, and `P.ι` preserves them.  The
index type is unchanged. -/
def generatingSectionsOfMap (hff : (P.ι ⋙ Φ).FullyFaithful)
    (hfree : ∀ I : Type w, P (SheafOfModules.free (R := R₁) I))
    [P.ι.PreservesEpimorphisms] {F : SheafOfModules.{w} R₁} (hF : P F)
    (σ : (Φ.obj F).GeneratingSections) : F.GeneratingSections where
  I := σ.I
  s := F.freeHomEquiv (P.ι.map (hff.preimage (X := ⟨_, hfree σ.I⟩) (Y := ⟨F, hF⟩)
    ((mapFreeIso Φ u σ.I).hom ≫ σ.π)))
  epi := by
    have := hff.faithful
    have hσ : Epi σ.π := σ.epi
    simp only [Equiv.symm_apply_apply]
    have h : Epi ((P.ι ⋙ Φ).map (hff.preimage (X := ⟨_, hfree σ.I⟩) (Y := ⟨F, hF⟩)
        ((mapFreeIso Φ u σ.I).hom ≫ σ.π))) := by
      rw [hff.map_preimage]
      exact epi_comp' (IsIso.epi_of_iso _) hσ
    have := (P.ι ⋙ Φ).epi_of_epi_map h
    infer_instance

variable (hff : (P.ι ⋙ Φ).FullyFaithful)
  (hfree : ∀ I : Type w, P (SheafOfModules.free (R := R₁) I))
  [Φ.PreservesEpimorphisms] [P.ι.PreservesEpimorphisms]

include hff hfree u in
/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (3), at a comparison functor
fully faithful on `P` alone.**  A module with the property `P` is generated by global sections
if and only if its image under the comparison is. -/
theorem isGeneratedByGlobalSections_iff {F : SheafOfModules.{w} R₁} (hF : P F) :
    F.IsGeneratedByGlobalSections ↔ (Φ.obj F).IsGeneratedByGlobalSections :=
  ⟨fun h ↦ ⟨generatingSectionsMap Φ u h.some⟩,
    fun h ↦ ⟨generatingSectionsOfMap Φ u P hff hfree hF h.some⟩⟩

include hff hfree u in
/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (4), at a comparison functor
fully faithful on `P` alone.**  A module with the property `P` is generated by `r` global
sections if and only if its image under the comparison is: both transports leave the index type
of the generating family alone, so the same `r` works. -/
theorem isGeneratedByGlobalSectionsOfCard_iff {F : SheafOfModules.{w} R₁} (hF : P F) (r : ℕ) :
    F.IsGeneratedByGlobalSectionsOfCard r ↔
      (Φ.obj F).IsGeneratedByGlobalSectionsOfCard r :=
  ⟨fun h ↦ ⟨generatingSectionsMap Φ u h.choose, h.choose_spec⟩,
    fun h ↦ ⟨generatingSectionsOfMap Φ u P hff hfree hF h.choose, h.choose_spec⟩⟩

include hff hfree u in
/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (5), at a comparison functor
fully faithful on `P` alone.**  A module with the property `P` is generated by finitely many
global sections if and only if its image under the comparison is. -/
theorem exists_isGeneratedByGlobalSectionsOfCard_iff {F : SheafOfModules.{w} R₁} (hF : P F) :
    (∃ r : ℕ, F.IsGeneratedByGlobalSectionsOfCard r) ↔
      ∃ r : ℕ, (Φ.obj F).IsGeneratedByGlobalSectionsOfCard r :=
  ⟨fun h ↦ ⟨h.choose,
      (isGeneratedByGlobalSectionsOfCard_iff Φ u P hff hfree hF h.choose).1 h.choose_spec⟩,
    fun h ↦ ⟨h.choose,
      (isGeneratedByGlobalSectionsOfCard_iff Φ u P hff hfree hF h.choose).2 h.choose_spec⟩⟩

section Presentation

variable [Φ.PreservesZeroMorphisms] [P.ι.PreservesZeroMorphisms]
  [PreservesFiniteColimits P.ι]

/-- `Φ` preserves colimits indexed by small categories in the lowest universe. -/
local instance : PreservesColimitsOfSize.{0, 0} Φ := preservesColimitsOfSize_shrink _

omit [HasWeakSheafify J₁ AddCommGrpCat.{w}] [J₁.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J₂ AddCommGrpCat.{w}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [PreservesColimitsOfSize.{w, w} Φ] [Φ.PreservesEpimorphisms] [P.ι.PreservesEpimorphisms] in
include hff in
/-- **A cokernel presentation of `Φ.obj F` by images of objects of `P` pulls back.**  Given
objects `X`, `Y`, `F` with the property `P` and a cokernel cofork of `b : P₀ ⟶ Φ.obj F` with
`P₀ ≅ Φ.obj X` and `Q₀ ≅ Φ.obj Y`, the maps pull back along the fully faithful `P.ι ⋙ Φ` to a
cokernel cofork of modules over `R₁`. -/
theorem exists_isColimit_cokernelCofork_of_isColimit_map
    {X Y F : SheafOfModules.{w} R₁} (hX : P X) (hY : P Y) (hF : P F)
    {P₀ Q₀ : SheafOfModules.{w} R₂} (eP : Φ.obj X ≅ P₀) (eQ : Φ.obj Y ≅ Q₀)
    {a : Q₀ ⟶ P₀} {b : P₀ ⟶ Φ.obj F} {hab : a ≫ b = 0}
    (hc : IsColimit (CokernelCofork.ofπ b hab)) :
    ∃ (a' : Y ⟶ X) (b' : X ⟶ F) (hab' : a' ≫ b' = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ b' hab')) := by
  have := hff.full
  have := hff.faithful
  have hrefl : ReflectsColimitsOfSize.{0, 0} (P.ι ⋙ Φ) := fullyFaithful_reflectsColimits _
  have hab' : (hff.preimage (X := ⟨_, hY⟩) (Y := ⟨_, hX⟩) (eQ.hom ≫ a ≫ eP.inv)) ≫
      (hff.preimage (X := ⟨_, hX⟩) (Y := ⟨F, hF⟩) (eP.hom ≫ b)) = 0 :=
    hff.map_injective (by simp [hab, hff.map_preimage, -Functor.comp_map])
  have l : IsColimit (CokernelCofork.ofπ
      ((P.ι ⋙ Φ).map (hff.preimage (X := ⟨_, hX⟩) (Y := ⟨F, hF⟩) (eP.hom ≫ b)))
      (show (P.ι ⋙ Φ).map (hff.preimage (X := ⟨_, hY⟩) (Y := ⟨_, hX⟩)
          (eQ.hom ≫ a ≫ eP.inv)) ≫
        (P.ι ⋙ Φ).map (hff.preimage (X := ⟨_, hX⟩) (Y := ⟨F, hF⟩) (eP.hom ≫ b)) = 0 by
        rw [← Functor.map_comp, hab', Functor.map_zero])) :=
    Cofork.isColimitOfIsos _ hc _ eQ.symm eP.symm (Iso.refl _)
      (by simp [hff.map_preimage, -Functor.comp_map])
      (by simp [-Functor.comp_map])
      (by simp [hff.map_preimage, -Functor.comp_map])
  exact ⟨_, _, _, ⟨isColimitCoforkMapOfIsColimit' P.ι hab'
    (@isColimitOfReflects _ _ _ _ _ _ _ (P.ι ⋙ Φ) _
      ((isColimitMapCoconeCoforkEquiv' (P.ι ⋙ Φ) hab').symm l)
      hrefl.reflectsColimitsOfShape.reflectsColimit)⟩⟩

omit [Φ.PreservesEpimorphisms] [P.ι.PreservesEpimorphisms] in
include hff hfree u in
/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (6), at a comparison functor
fully faithful on `P` alone.**  A module with the property `P` has a global presentation if and
only if its image under the comparison has one, with the same two index types.

The preservation half maps the two coproducts and the cokernel across.  The reverse half
replaces the two given coproducts by `SheafOfModules.free` on the same index types, compares
them with the given ones through `Stacks.Sheaves.QcohTypeComparison.mapFreeIso`, moves the
cokernel cofork across that comparison with `CategoryTheory.Limits.Cofork.isColimitOfIsos`, and
then crosses the subcategory boundary in two steps: `P.ι ⋙ Φ` is fully faithful, so it reflects
the cofork into the full subcategory cut out by `P`, and `P.ι` preserves finite colimits, so it
carries the cofork from there into the ambient category of modules. -/
theorem isPresentedByGlobalSections_iff {F : SheafOfModules.{w} R₁} (hF : P F) :
    F.IsPresentedByGlobalSections ↔ (Φ.obj F).IsPresentedByGlobalSections := by
  constructor
  · rintro ⟨I, K, P₀, Q₀, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩
    exact ⟨I, K, Φ.obj P₀, Φ.obj Q₀, _, _,
      ⟨GlobalTypeComparison.isColimitCofanMap Φ u ι hP⟩,
      ⟨GlobalTypeComparison.isColimitCofanMap Φ u κ hQ⟩,
      Φ.map a, Φ.map b, _, ⟨isColimitCoforkMapOfIsColimit' Φ hab hc⟩⟩
  · rintro ⟨I, K, P₀, Q₀, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩
    obtain ⟨a', b', hab', hc'⟩ := exists_isColimit_cokernelCofork_of_isColimit_map Φ P hff
      (hfree I) (hfree K) hF
      (mapFreeIso Φ u I ≪≫ (SheafOfModules.isColimitFreeCofan I).coconePointUniqueUpToIso hP)
      (mapFreeIso Φ u K ≪≫ (SheafOfModules.isColimitFreeCofan K).coconePointUniqueUpToIso hQ) hc
    exact ⟨I, K, _, _, _, _, ⟨SheafOfModules.isColimitFreeCofan I⟩,
      ⟨SheafOfModules.isColimitFreeCofan K⟩, a', b', hab', hc'⟩

omit [HasWeakSheafify J₂ AddCommGrpCat.{w}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Φ.PreservesEpimorphisms] [P.ι.PreservesEpimorphisms] in
include hff hfree u in
/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (7), at a comparison functor
fully faithful on `P` alone.**  A module with the property `P` has a finite global presentation
if and only if its image under the comparison has one, with the same two finite index types
`Fin n` and `Fin k`.

Those index types do not live in the universe of sections, so the two coproducts the reverse
half builds are the free modules on `ULift (Fin n)` and `ULift (Fin k)`, with their cofans
reindexed by `Stacks.Sheaves.QcohTypeComparison.isColimitFreeCofanFin`; the presentation
produced is still indexed by `Fin n` and `Fin k`, so no finiteness is lost. -/
theorem isFinitelyPresentedByGlobalSections_iff {F : SheafOfModules.{w} R₁} (hF : P F) :
    F.IsFinitelyPresentedByGlobalSections ↔
      (Φ.obj F).IsFinitelyPresentedByGlobalSections := by
  constructor
  · rintro ⟨n, k, P₀, Q₀, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩
    exact ⟨n, k, Φ.obj P₀, Φ.obj Q₀, _, _,
      ⟨GlobalTypeComparison.isColimitCofanMap Φ u ι hP⟩,
      ⟨GlobalTypeComparison.isColimitCofanMap Φ u κ hQ⟩,
      Φ.map a, Φ.map b, _, ⟨isColimitCoforkMapOfIsColimit' Φ hab hc⟩⟩
  · rintro ⟨n, k, P₀, Q₀, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hc⟩⟩
    obtain ⟨a', b', hab', hc'⟩ := exists_isColimit_cokernelCofork_of_isColimit_map Φ P hff
      (hfree (ULift.{w} (Fin n))) (hfree (ULift.{w} (Fin k))) hF
      ((GlobalTypeComparison.isColimitCofanMap Φ u _
        (isColimitFreeCofanFin n)).coconePointUniqueUpToIso hP)
      ((GlobalTypeComparison.isColimitCofanMap Φ u _
        (isColimitFreeCofanFin k)).coconePointUniqueUpToIso hQ) hc
    exact ⟨n, k, _, _, _, _, ⟨isColimitFreeCofanFin n⟩, ⟨isColimitFreeCofanFin k⟩,
      a', b', hab', hc'⟩

end Presentation

end Stacks.Sheaves.QcohTypeComparison

namespace AlgebraicGeometry

universe u

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated-module functor of the indicated big site preserves epimorphisms, being a
left adjoint; recorded at the retyping
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOfSheaf`. -/
theorem preservesEpimorphisms_baseAssociatedModuleOfSheaf (τ : SiteKind) :
    (baseAssociatedModuleOfSheaf B S hS τ).PreservesEpimorphisms :=
  have h : (baseAssociatedModule B S hS τ).PreservesEpimorphisms := inferInstance
  h

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (3), on the big site.**  A
quasi-coherent `𝒪_S`-module is generated by global sections if and only if `𝓕^a` is generated by
global sections as an `𝒪`-module on `(Sch/S)_τ`. -/
@[stacks 05VG "generated by global sections, big site (Sch/S)_τ at every τ, at the comparison \
functor of 03DX itself"]
theorem isGeneratedByGlobalSections_iff_baseAssociatedModule (τ : SiteKind)
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsGeneratedByGlobalSections ↔
      ((baseAssociatedModuleQcoh B S hS τ).obj F).IsGeneratedByGlobalSections :=
  have := preservesColimitsOfSize_baseAssociatedModuleOfSheaf.{u, u} B S hS τ
  have := preservesEpimorphisms_baseAssociatedModuleOfSheaf B S hS τ
  Stacks.Sheaves.QcohTypeComparison.isGeneratedByGlobalSections_iff _
    (baseAssociatedModuleUnitIso B S hS τ) _
    (fullyFaithfulBaseAssociatedModuleQcoh B S hS τ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (4), on the big site.**  A
quasi-coherent `𝒪_S`-module is generated by `r` global sections if and only if `𝓕^a` is, with
the same `r`. -/
@[stacks 05VG "generated by r global sections, big site (Sch/S)_τ at every τ, at the comparison \
functor of 03DX itself"]
theorem isGeneratedByGlobalSectionsOfCard_iff_baseAssociatedModule (τ : SiteKind)
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) (r : ℕ) :
    F.obj.IsGeneratedByGlobalSectionsOfCard r ↔
      ((baseAssociatedModuleQcoh B S hS τ).obj F).IsGeneratedByGlobalSectionsOfCard r :=
  have := preservesColimitsOfSize_baseAssociatedModuleOfSheaf.{u, u} B S hS τ
  have := preservesEpimorphisms_baseAssociatedModuleOfSheaf B S hS τ
  Stacks.Sheaves.QcohTypeComparison.isGeneratedByGlobalSectionsOfCard_iff _
    (baseAssociatedModuleUnitIso B S hS τ) _
    (fullyFaithfulBaseAssociatedModuleQcoh B S hS τ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property r

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (5), on the big site.**  A
quasi-coherent `𝒪_S`-module is generated by finitely many global sections if and only if `𝓕^a`
is. -/
@[stacks 05VG "generated by finitely many global sections, big site (Sch/S)_τ at every τ, at \
the comparison functor of 03DX itself"]
theorem exists_isGeneratedByGlobalSectionsOfCard_iff_baseAssociatedModule (τ : SiteKind)
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (∃ r : ℕ, F.obj.IsGeneratedByGlobalSectionsOfCard r) ↔
      ∃ r : ℕ, ((baseAssociatedModuleQcoh B S hS τ).obj F).IsGeneratedByGlobalSectionsOfCard r :=
  have := preservesColimitsOfSize_baseAssociatedModuleOfSheaf.{u, u} B S hS τ
  have := preservesEpimorphisms_baseAssociatedModuleOfSheaf B S hS τ
  Stacks.Sheaves.QcohTypeComparison.exists_isGeneratedByGlobalSectionsOfCard_iff _
    (baseAssociatedModuleUnitIso B S hS τ) _
    (fullyFaithfulBaseAssociatedModuleQcoh B S hS τ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- The associated-module functor of the indicated big site preserves zero morphisms, being a
left adjoint; recorded at the retyping
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleOfSheaf`. -/
theorem preservesZeroMorphisms_baseAssociatedModuleOfSheaf (τ : SiteKind) :
    (baseAssociatedModuleOfSheaf B S hS τ).PreservesZeroMorphisms :=
  have h : (baseAssociatedModule B S hS τ).PreservesZeroMorphisms := inferInstance
  h

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (6), on the big site.**  A
quasi-coherent `𝒪_S`-module has a global presentation if and only if `𝓕^a` has one as an
`𝒪`-module on `(Sch/S)_τ`, with the same two index types. -/
@[stacks 05VG "global presentation, big site (Sch/S)_τ at every τ, at the comparison functor \
of 03DX itself"]
theorem isPresentedByGlobalSections_iff_baseAssociatedModule (τ : SiteKind)
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsPresentedByGlobalSections ↔
      ((baseAssociatedModuleQcoh B S hS τ).obj F).IsPresentedByGlobalSections :=
  have := preservesColimitsOfSize_baseAssociatedModuleOfSheaf.{u, u} B S hS τ
  have := preservesEpimorphisms_baseAssociatedModuleOfSheaf B S hS τ
  have := preservesZeroMorphisms_baseAssociatedModuleOfSheaf B S hS τ
  Stacks.Sheaves.QcohTypeComparison.isPresentedByGlobalSections_iff _
    (baseAssociatedModuleUnitIso B S hS τ) _
    (fullyFaithfulBaseAssociatedModuleQcoh B S hS τ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (7), on the big site.**  A
quasi-coherent `𝒪_S`-module has a finite global presentation if and only if `𝓕^a` has one,
with the same two finite index types. -/
@[stacks 05VG "finite global presentation, big site (Sch/S)_τ at every τ, at the comparison \
functor of 03DX itself"]
theorem isFinitelyPresentedByGlobalSections_iff_baseAssociatedModule (τ : SiteKind)
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsFinitelyPresentedByGlobalSections ↔
      ((baseAssociatedModuleQcoh B S hS τ).obj F).IsFinitelyPresentedByGlobalSections :=
  have := preservesColimitsOfSize_baseAssociatedModuleOfSheaf.{u, u} B S hS τ
  have := preservesEpimorphisms_baseAssociatedModuleOfSheaf B S hS τ
  have := preservesZeroMorphisms_baseAssociatedModuleOfSheaf B S hS τ
  Stacks.Sheaves.QcohTypeComparison.isFinitelyPresentedByGlobalSections_iff _
    (baseAssociatedModuleUnitIso B S hS τ) _
    (fullyFaithfulBaseAssociatedModuleQcoh B S hS τ)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

end BigFppfOver

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated-module functor of the small étale site preserves epimorphisms, being a left
adjoint; recorded at the retyping
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`. -/
theorem preservesEpimorphisms_associatedModuleOfSheaf :
    (associatedModuleOfSheaf B S hS).PreservesEpimorphisms :=
  have h : (associatedModule B S hS).PreservesEpimorphisms := inferInstance
  h

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (3), on the small étale
site.**  A quasi-coherent `𝒪_S`-module is generated by global sections if and only if `𝓕^a` is
generated by global sections as an `𝒪`-module on `S_étale`. -/
@[stacks 05VG "generated by global sections, small site at τ = étale, at the comparison functor \
of 03DX itself"]
theorem isGeneratedByGlobalSections_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsGeneratedByGlobalSections ↔
      ((associatedModuleQcoh B S hS).obj F).IsGeneratedByGlobalSections :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS
  Stacks.Sheaves.QcohTypeComparison.isGeneratedByGlobalSections_iff _
    (associatedModuleUnitIso B S hS) _
    (fullyFaithfulAssociatedModuleQcoh' B S hS)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (4), on the small étale
site.**  A quasi-coherent `𝒪_S`-module is generated by `r` global sections if and only if `𝓕^a`
is, with the same `r`. -/
@[stacks 05VG "generated by r global sections, small site at τ = étale, at the comparison \
functor of 03DX itself"]
theorem isGeneratedByGlobalSectionsOfCard_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) (r : ℕ) :
    F.obj.IsGeneratedByGlobalSectionsOfCard r ↔
      ((associatedModuleQcoh B S hS).obj F).IsGeneratedByGlobalSectionsOfCard r :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS
  Stacks.Sheaves.QcohTypeComparison.isGeneratedByGlobalSectionsOfCard_iff _
    (associatedModuleUnitIso B S hS) _
    (fullyFaithfulAssociatedModuleQcoh' B S hS)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property r

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (5), on the small étale
site.**  A quasi-coherent `𝒪_S`-module is generated by finitely many global sections if and
only if `𝓕^a` is. -/
@[stacks 05VG "generated by finitely many global sections, small site at τ = étale, at the \
comparison functor of 03DX itself"]
theorem exists_isGeneratedByGlobalSectionsOfCard_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    (∃ r : ℕ, F.obj.IsGeneratedByGlobalSectionsOfCard r) ↔
      ∃ r : ℕ, ((associatedModuleQcoh B S hS).obj F).IsGeneratedByGlobalSectionsOfCard r :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS
  Stacks.Sheaves.QcohTypeComparison.exists_isGeneratedByGlobalSectionsOfCard_iff _
    (associatedModuleUnitIso B S hS) _
    (fullyFaithfulAssociatedModuleQcoh' B S hS)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- The associated-module functor of the small étale site preserves zero morphisms, being a
left adjoint; recorded at the retyping
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`. -/
theorem preservesZeroMorphisms_associatedModuleOfSheaf :
    (associatedModuleOfSheaf B S hS).PreservesZeroMorphisms :=
  have h : (associatedModule B S hS).PreservesZeroMorphisms := inferInstance
  h

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (6), on the small étale
site.**  A quasi-coherent `𝒪_S`-module has a global presentation if and only if `𝓕^a` has one
as an `𝒪`-module on `S_étale`, with the same two index types. -/
@[stacks 05VG "global presentation, small site at τ = étale, at the comparison functor of 03DX \
itself"]
theorem isPresentedByGlobalSections_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsPresentedByGlobalSections ↔
      ((associatedModuleQcoh B S hS).obj F).IsPresentedByGlobalSections :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS
  have := preservesZeroMorphisms_associatedModuleOfSheaf B S hS
  Stacks.Sheaves.QcohTypeComparison.isPresentedByGlobalSections_iff _
    (associatedModuleUnitIso B S hS) _
    (fullyFaithfulAssociatedModuleQcoh' B S hS)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DE (7), on the small étale
site.**  A quasi-coherent `𝒪_S`-module has a finite global presentation if and only if `𝓕^a`
has one, with the same two finite index types. -/
@[stacks 05VG "finite global presentation, small site at τ = étale, at the comparison functor \
of 03DX itself"]
theorem isFinitelyPresentedByGlobalSections_iff_associatedModule
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    F.obj.IsFinitelyPresentedByGlobalSections ↔
      ((associatedModuleQcoh B S hS).obj F).IsFinitelyPresentedByGlobalSections :=
  have := preservesColimitsOfSize_associatedModuleOfSheaf.{u, u} B S hS
  have := preservesEpimorphisms_associatedModuleOfSheaf B S hS
  have := preservesZeroMorphisms_associatedModuleOfSheaf B S hS
  Stacks.Sheaves.QcohTypeComparison.isFinitelyPresentedByGlobalSections_iff _
    (associatedModuleUnitIso B S hS) _
    (fullyFaithfulAssociatedModuleQcoh' B S hS)
    (fun I ↦ Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I) F.property

end SmallEtale

end AlgebraicGeometry

end
