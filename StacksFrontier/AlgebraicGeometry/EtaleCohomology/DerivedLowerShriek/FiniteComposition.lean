module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Composition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension by zero commutes with a finite direct image, and `R(g ∘ f)_!` for a finite `f`

Let
```
V --j'--> V̄
|f        |f̄
v         v
U --j---> Ū
```
be a cartesian square of schemes with `j` an open immersion and `f̄` integral (for instance
finite), and let `Λ` be a ring, not necessarily commutative. For sheaves of `Λ`-modules on the
small étale sites, `j_! ∘ f_* ≅ f̄_* ∘ j'_!` ([Stacks, Tag 0GJ1]), as a natural isomorphism, and
the same holds for the derived functors on `D⁺`. The components are the isomorphisms
`Stacks.EtaleCohomology.isIso_extensionByZeroDirectImageMap`, proved through integral base change
(`Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_of_isIntegralHom`, [Stacks, Tag 0EYP]); both
hold over a noncommutative ring, which the coefficients of [Stacks, Tag 03V3] need.

As a consequence, for `f : X ⟶ Y` finite and `g : Y ⟶ Z` separated of finite type,
`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` on `D⁺_tors(X_étale, Λ)`, with no proper base change: the proof of
[Stacks, Tag 0F7J] needs base change only for the morphism `X̄ ⟶ Ȳ` of compactifications, and by
Zariski's Main Theorem that morphism may be chosen finite.

## Main results

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroDirectImageIsoOfIsIntegralHom`: **Tag 0GJ1**
  for sheaves of modules over an arbitrary ring.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroDirectImageIso`: its derived form.
* `AlgebraicGeometry.CompactificationOf.exists_isFinite_toBase`: a compactification of
  `X ⟶ Y ⟶ Ȳ` finite over `Ȳ`.
* `Stacks.EtaleCohomology.derivedLowerShriekCompIsoOfIsFinite`: `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` for a
  finite `f`, through any compactification of `g ∘ f`.
* `Stacks.EtaleCohomology.derivedLowerShriekOfProperIso`: `Rf_!` through the trivial
  compactification of a proper `f` is `Rf_*`.
* `Stacks.EtaleCohomology.derivedLowerShriekCompDirectImageIsoOfIsFinite`:
  `R(g ∘ f)_! ≅ Rg_! ∘ Rf_*` for a finite `f`.

## References

* [Stacks Project, Tag 0GJ1](https://stacks.math.columbia.edu/tag/0GJ1)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 05K0](https://stacks.math.columbia.edu/tag/05K0)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section ExtensionByZero

variable (Λ : Type) [Ring Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [IsOpenImmersion j]
  (j' : V ⟶ Vb) [IsOpenImmersion j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb)

/-- The transformation `f_* ⟶ j^{-1} f̄_* j'_!`: the unit of `j'_! ⊣ j'^{-1}` followed by the
isomorphism `f_* j'^{-1} ≅ j^{-1} f̄_*`. -/
def etaleModuleDirectImageToRestrictionDirectImageExtensionByZero :
    etaleModuleDirectImage.{u, 0} Λ f ⟶
      etaleModuleExtensionByZero.{u, 0} Λ j' ⋙ etaleModuleDirectImage.{u, 0} Λ fb ⋙
        etaleModuleRestriction.{u, 0} Λ j :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit
      (etaleModuleDirectImage.{u, 0} Λ f) ≫
    Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ j')
      (restrictionDirectImageIso Λ j j' f fb sq).hom

/-- **The canonical transformation `j_! ∘ f_* ⟶ f̄_* ∘ j'_!`**, adjoint under `j_! ⊣ j^{-1}`
to `etaleModuleDirectImageToRestrictionDirectImageExtensionByZero`. -/
def etaleModuleExtensionByZeroDirectImageMap :
    etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleExtensionByZero.{u, 0} Λ j ⟶
      etaleModuleExtensionByZero.{u, 0} Λ j' ⋙ etaleModuleDirectImage.{u, 0} Λ fb :=
  Functor.whiskerRight (etaleModuleDirectImageToRestrictionDirectImageExtensionByZero Λ j j' f fb sq)
      (etaleModuleExtensionByZero.{u, 0} Λ j) ≫
    Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ j' ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit

/-- The components of `etaleModuleExtensionByZeroDirectImageMap` are the adjoints of those of
`etaleModuleDirectImageToRestrictionDirectImageExtensionByZero`. -/
theorem etaleModuleExtensionByZeroDirectImageMap_app (M : EtaleModules.{u, 0} Λ V) :
    (etaleModuleExtensionByZeroDirectImageMap Λ j j' f fb sq).app M =
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).symm
        ((etaleModuleDirectImageToRestrictionDirectImageExtensionByZero Λ j j' f fb sq).app M) := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- **Extension by zero commutes with an integral direct image**, given closed complements: the
components of `etaleModuleExtensionByZeroDirectImageMap` are the maps
`Stacks.EtaleCohomology.extensionByZeroDirectImageMap`, which are isomorphisms
(`Stacks.EtaleCohomology.isIso_extensionByZeroDirectImageMap`). -/
theorem isIso_etaleModuleExtensionByZeroDirectImageMap_app_of_closed {Z Z' : Scheme.{u}}
    (i : Z ⟶ Ub) [IsClosedImmersion i]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (i' : Z' ⟶ Vb) [IsClosedImmersion i']
    (hij' : Set.range j'.base = (Set.range i'.base)ᶜ) (fZ : Z' ⟶ Z) (sqZ : IsPullback fZ i' i fb)
    (M : EtaleModules.{u, 0} Λ V) :
    IsIso ((etaleModuleExtensionByZeroDirectImageMap Λ j j' f fb sq).app M) := by
  rw [etaleModuleExtensionByZeroDirectImageMap_app]
  have h : (etaleModuleDirectImageToRestrictionDirectImageExtensionByZero Λ j j' f fb sq).app M =
      (etaleModuleDirectImage.{u, 0} Λ f).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app M) ≫
        (restrictionDirectImageIso Λ j j' f fb sq).hom.app _ :=
    Category.id_comp _
  rw [h]
  exact isIso_extensionByZeroDirectImageMap Λ j j' f fb sq i hij i' hij' fZ sqZ M

/-- **Stacks Project, Tag 0GJ1**, for sheaves of modules over an arbitrary ring `Λ`. For a
cartesian square `f ≫ j = j' ≫ f̄` of schemes with `j` an open immersion and `f̄` integral (for
instance finite), `j_! ∘ f_* ≅ f̄_* ∘ j'_!` as functors from sheaves of `Λ`-modules on `V_étale`
to sheaves of `Λ`-modules on `Ū_étale`. -/
@[sga "4 IX 5.2.1" "special case"]
def etaleModuleExtensionByZeroDirectImageIsoOfIsIntegralHom :
    etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleExtensionByZero.{u, 0} Λ j ≅
      etaleModuleExtensionByZero.{u, 0} Λ j' ⋙ etaleModuleDirectImage.{u, 0} Λ fb := by
  let Zc : Ub.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  have hij : Set.range j.base = (Set.range Zc.subschemeι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl _).symm
  have sqZ := (IsPullback.of_hasPullback fb Zc.subschemeι).flip
  have hij' : Set.range j'.base = (Set.range (pullback.fst fb Zc.subschemeι).base)ᶜ := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩ ⟨z, hz⟩
      have h₁ : fb.base ((pullback.fst fb Zc.subschemeι).base z) ∈ Set.range Zc.subschemeι.base :=
        ⟨(pullback.snd fb Zc.subschemeι).base z, by
          rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
      have h₂ : fb.base ((pullback.fst fb Zc.subschemeι).base z) ∈ Set.range j.base :=
        ⟨f.base x, by rw [hz, ← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]⟩
      rw [hij] at h₂
      exact h₂ h₁
    · intro hv
      by_contra hv'
      have hfv : fb.base v ∈ Set.range Zc.subschemeι.base := by
        rw [← Set.notMem_compl_iff, ← hij]
        rintro ⟨u, hu⟩
        obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := fb) u v hu
        refine hv' ⟨sq.isoPullback.inv.base w, ?_⟩
        rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hw]
      obtain ⟨z, hz⟩ := hfv
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback v z hz.symm
      exact hv ⟨w, hw⟩
  haveI : ∀ M, IsIso ((etaleModuleExtensionByZeroDirectImageMap Λ j j' f fb sq).app M) :=
    fun M => isIso_etaleModuleExtensionByZeroDirectImageMap_app_of_closed Λ j j' f fb sq
      Zc.subschemeι hij (pullback.fst fb Zc.subschemeι) hij' (pullback.snd fb Zc.subschemeι)
      sqZ M
  haveI : IsIso (etaleModuleExtensionByZeroDirectImageMap Λ j j' f fb sq) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (etaleModuleExtensionByZeroDirectImageMap Λ j j' f fb sq)

end ExtensionByZero

/-! ### The derived form -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [IsOpenImmersion j]
  (j' : V ⟶ Vb) [IsOpenImmersion j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]

/-- **`Rf̄_* ∘ Rj'_! ≅ Rj_! ∘ Rf_*` on `D⁺(V_étale, Λ)`** for a cartesian square with `j` an open
immersion and `f̄` integral, over an arbitrary ring `Λ`. All four functors are exact (extension
by zero, Tag 03S5; integral direct image, Tag 04C2), so both composites are the derived functors
of the underived composites, which agree by Tag 0GJ1
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroDirectImageIsoOfIsIntegralHom`).

This is stated in the standard model `HasDerivedCategory.standard` of the derived category, the
model in which `Stacks.EtaleCohomology.derivedLowerShriek` is defined. -/
def etaleModuleDerivedExtensionByZeroDirectImageIso (sq : IsPullback f j' j fb) :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ j' ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ fb ≅
      etaleModuleDerivedDirectImage.{u, 0} Λ f ⋙ etaleModuleDerivedExtensionByZero.{u, 0} Λ j :=
  Functor.rightDerivedFunctorPlusCompIsoOfExact (etaleModuleExtensionByZero.{u, 0} Λ j')
      (etaleModuleDirectImage.{u, 0} Λ fb) _
      (etaleModuleExtensionByZeroDirectImageIsoOfIsIntegralHom Λ j j' f fb sq).symm ≪≫
    (Functor.rightDerivedFunctorPlusCompIsoOfExact (etaleModuleDirectImage.{u, 0} Λ f)
      (etaleModuleExtensionByZero.{u, 0} Λ j) _ (Iso.refl _)).symm

end Derived

end Stacks.EtaleCohomology

-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions (`Field ?k`, `QuasiCompact ?f`, ...) match every goal and send instance search
-- through `Submodule ?R ?R`; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

/-! ### A compactification of `X ⟶ Ȳ` finite over `Ȳ` -/

namespace AlgebraicGeometry.CompactificationOf

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))

/-- **A compactification finite over the base.** For `f : X ⟶ Y` finite and a compactification
`Y ⟶ Ȳ` of `Y` over `Z`, with `Z` quasi-compact and quasi-separated and `g` quasi-compact, the
quasi-finite separated morphism `X ⟶ Y ⟶ Ȳ` factors as an open immersion followed by a finite
morphism, by Zariski's Main Theorem ([Stacks, Tag 05K0]). -/
theorem exists_isFinite_toBase [IsFinite f] [QuasiCompact g] [CompactSpace Z]
    [QuasiSeparatedSpace Z] :
    ∃ jX : CompactificationOf (Over.mk (f ≫ jg.immersion)), IsFinite jX.toBase := by
  have : CompactSpace jg.space := QuasiCompact.compactSpace_of_compactSpace jg.toBase
  have hsep : IsSeparated jg.toBase := (inferInstance : IsProper jg.toBase).toIsSeparated
  have hqs : QuasiSeparated jg.toBase := @IsSeparated.instQuasiSeparated _ _ jg.toBase hsep
  have : QuasiSeparatedSpace jg.space :=
    @quasiSeparatedSpace_of_quasiSeparated _ _ jg.toBase ‹QuasiSeparatedSpace Z› hqs
  have : QuasiCompact (jg.immersion ≫ jg.toBase) := by
    rw [CompactificationOf.immersion_toBase]
    infer_instance
  have : QuasiCompact jg.immersion := QuasiCompact.of_comp jg.immersion jg.toBase
  have : IsOpenImmersion jg.immersion := jg.property.1
  have : LocallyQuasiFinite f := ((IsFinite.iff_isProper_and_locallyQuasiFinite f).1 ‹_›).2
  have : LocallyQuasiFinite jg.immersion := inferInstance
  have : LocallyQuasiFinite (f ≫ jg.immersion) :=
    MorphismProperty.comp_mem _ _ _ ‹LocallyQuasiFinite f› ‹LocallyQuasiFinite jg.immersion›
  have : LocallyOfFiniteType f :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).1 ‹_›).2
  have : LocallyOfFiniteType jg.immersion := inferInstance
  have : LocallyOfFiniteType (f ≫ jg.immersion) :=
    MorphismProperty.comp_mem _ _ _ ‹LocallyOfFiniteType f› ‹LocallyOfFiniteType jg.immersion›
  have : QuasiCompact f := inferInstance
  have : QuasiCompact (f ≫ jg.immersion) :=
    MorphismProperty.comp_mem _ _ _ ‹QuasiCompact f› ‹QuasiCompact jg.immersion›
  have : IsSeparated f := inferInstance
  have : IsSeparated jg.immersion := inferInstance
  have : IsSeparated (f ≫ jg.immersion) :=
    MorphismProperty.comp_mem _ _ _ ‹IsSeparated f› ‹IsSeparated jg.immersion›
  obtain ⟨T, i, π, hi, -, hπ, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_factorization (f ≫ jg.immersion)
  have : IsFinite π := hπ
  have : IsProper π := inferInstance
  exact ⟨⟨StructuredArrow.mk (Y := Over.mk π) (Over.homMk i hfac.symm), ⟨hi, this⟩⟩, hπ⟩

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

section FiniteComposition

variable (Λ : Type) [Ring Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (jg : CompactificationOf (Over.mk g))

/-- The compactification `X ⟶ X̄ ×_Ȳ Y` of `f` induced by a compactification of `X` over `Ȳ`
receives the trivial compactification of the finite morphism `f`, through the open immersion
`X ⟶ X̄ ×_Ȳ Y`. -/
def ofProperToRestrictBase [IsFinite f]
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    CompactificationOf.ofProper f ⟶ CompactificationOf.restrictBase jg jX :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk (CompactificationOf.restrictBase jg jX).immersion
      (CompactificationOf.immersion_toBase _)) (by ext; rfl))

/-- **`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` for a finite `f`, through a compactification of `X` finite over
`Ȳ`**, on `D⁺_tors(X_étale, Λ)` for an arbitrary ring `Λ`, with `Rf_!` computed through the
trivial compactification of `f`. This is the assembly of the proof of [Stacks, Tag 0F7J]
(`Stacks.EtaleCohomology.derivedLowerShriekCompOverIsoOfBaseChange`) in the case where the
open-immersion base change it needs is Tag 0GJ1 for the finite morphism `X̄ ⟶ Ȳ`, so that no
proper base change enters. -/
def derivedLowerShriekCompOverIsoOfIsFinite [IsFinite f]
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) [IsFinite jX.toBase] :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙
        derivedLowerShriek.{u, 0} (f ≫ g) (CompactificationOf.compOver jg jX) Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f (CompactificationOf.ofProper f) Λ ⋙
        derivedLowerShriek.{u, 0} g jg Λ :=
  derivedLowerShriekCompOverIsoOfBaseChange Λ jg jX
      (Functor.isoWhiskerLeft _ (etaleModuleDerivedExtensionByZeroDirectImageIso Λ jg.immersion
        (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
        jX.toBase (IsPullback.of_hasPullback jX.toBase jg.immersion).flip))
      (fun K hK => isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ _ K hK) ≪≫
    Functor.isoWhiskerRight (derivedLowerShriekHomIso Λ (ofProperToRestrictBase f g jg jX))
      (derivedLowerShriek.{u, 0} g jg Λ)

/-- **`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` for a finite morphism `f`**, on `D⁺_tors(X_étale, Λ)` for an
arbitrary ring `Λ`. Here `f : X ⟶ Y` is finite, with `Rf_! = Rf_*` computed through its trivial
compactification, `g : Y ⟶ Z` is separated of finite type and quasi-compact over a quasi-compact
quasi-separated `Z`, `Rg_!` is computed through any compactification `jg` and `R(g ∘ f)_!` through
any compactification `j`.

The proof chooses, by Zariski's Main Theorem, a compactification `X ⟶ X̄` of `X` over `Ȳ` with
`X̄ ⟶ Ȳ` finite (`AlgebraicGeometry.CompactificationOf.exists_isFinite_toBase`); through it the
identification of the proof of [Stacks, Tag 0F7J] needs only Tag 0GJ1
(`Stacks.EtaleCohomology.derivedLowerShriekCompOverIsoOfIsFinite`), and [Stacks, Tag 0F7I]
(`Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso`) passes to the compactification
`j`. It covers the composite of a finite étale morphism, or of a closed immersion, with an
arbitrary separated morphism of finite type. -/
def derivedLowerShriekCompIsoOfIsFinite [IsFinite f] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (j : CompactificationOf (Over.mk (f ≫ g))) :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} (f ≫ g) j Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f (CompactificationOf.ofProper f) Λ ⋙
        derivedLowerShriek.{u, 0} g jg Λ :=
  haveI : LocallyOfFiniteType f :=
    ((IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).1 ‹_›).2
  haveI : LocallyOfFiniteType (f ≫ g) :=
    MorphismProperty.comp_mem _ _ _ ‹LocallyOfFiniteType f› ‹LocallyOfFiniteType g›
  haveI : QuasiCompact f := inferInstance
  haveI : QuasiCompact (f ≫ g) :=
    MorphismProperty.comp_mem _ _ _ ‹QuasiCompact f› ‹QuasiCompact g›
  haveI : IsSeparated f := inferInstance
  haveI : IsSeparated (f ≫ g) :=
    MorphismProperty.comp_mem _ _ _ ‹IsSeparated f› ‹IsSeparated g›
  haveI : IsFinite (CompactificationOf.exists_isFinite_toBase (f := f) jg).choose.toBase :=
    (CompactificationOf.exists_isFinite_toBase (f := f) jg).choose_spec
  derivedLowerShriekCompactificationIso (f ≫ g) j
      (CompactificationOf.compOver jg (CompactificationOf.exists_isFinite_toBase (f := f) jg).choose)
      Λ ≪≫
    derivedLowerShriekCompOverIsoOfIsFinite Λ f g jg _

/-- **`Rf_!` through the trivial compactification of a proper `f` is `Rf_*`**: extension by zero
along the identity is the identity (`Stacks.EtaleCohomology.etaleModuleExtensionByZeroIdIso`), so
its derived functor is the identity of `D⁺(X_étale, Λ)`. -/
def derivedLowerShriekOfProperIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    derivedLowerShriek.{u, 0} f (CompactificationOf.ofProper f) Λ ≅
      etaleModuleDerivedDirectImage.{u, 0} Λ f :=
  Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusIdIsoOf _ (etaleModuleExtensionByZeroIdIso.{u, 0} Λ X)) _ ≪≫
    Functor.leftUnitor _

/-- **`R(g ∘ f)_! ≅ Rg_! ∘ Rf_*` for a finite morphism `f`**, on `D⁺_tors(X_étale, Λ)`:
`Stacks.EtaleCohomology.derivedLowerShriekCompIsoOfIsFinite` with `Rf_!` through the trivial
compactification read as `Rf_*` (`Stacks.EtaleCohomology.derivedLowerShriekOfProperIso`). For
`f` finite étale, or a closed immersion, this is the case of [Stacks, Tag 0F7J] needed when one of
the two morphisms is finite. -/
def derivedLowerShriekCompDirectImageIsoOfIsFinite [IsFinite f] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] [CompactSpace Z] [QuasiSeparatedSpace Z]
    (j : CompactificationOf (Over.mk (f ≫ g))) :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} (f ≫ g) j Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ f ⋙
        derivedLowerShriek.{u, 0} g jg Λ :=
  derivedLowerShriekCompIsoOfIsFinite Λ f g jg j ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (derivedLowerShriekOfProperIso Λ f) _)

end FiniteComposition

end Stacks.EtaleCohomology

end
