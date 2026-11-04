module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechGlobalSliceAway
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ExtendedCechFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation

/-!
# The extended alternating Čech complex restricts to the one of the restricted family

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let `U` be an
object of `𝒞`. Then

`Č(f)|_U ≅ Č(f|_U)`

as complexes of sheaves of `𝒪_U`-modules, compatibly with the augmentations out of the structure
sheaf.

On terms, `AlgebraicGeometry.RingedSite.awayModuleProdOverIso` identifies `(𝒪_{f_S})|_U` with
`(𝒪_U)_{(f|_U)_S}` for each subset `S`. This identification is natural in `S`, so it is an
isomorphism of localization *systems*, and the functoriality of the extended alternating Čech
complex turns it into an isomorphism of complexes.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayLocalizationFunctorOverIso`: the system `S ↦ 𝒪_{f_S}`,
  restricted to the slice, **is** the system `S ↦ (𝒪_U)_{(f|_U)_S}` of the slice.
* `AlgebraicGeometry.RingedSite.extendedAlternatingCechOverIso`: **`Č(f)|_U ≅ Č(f|_U)`.**

## Main results

* `AlgebraicGeometry.RingedSite.bijective_smul_awayModule_prodGlobalSection_of_subset`: for
  `S ⊆ T` every power of `f_S` acts bijectively on the sections of `𝒪_{f_T}`.
* `AlgebraicGeometry.RingedSite.overFunctor_map_awayModuleTransition_comp_awayModuleProdOverIso`:
  the identification of the Čech terms is natural in the subset, i.e. it carries the restriction
  of the transition map `𝒪_{f_S} ⟶ 𝒪_{f_T}` to the transition map of the slice.
* `AlgebraicGeometry.RingedSite.overFunctor_map_extendedAlternatingCechAugmentation_comp`: the
  identification carries the restriction of the augmentation `𝒪 ⟶ Č(f)^0` to the augmentation
  `𝒪_U ⟶ Č(f|_U)^0`.

## Implementation notes

Naturality in the subset is proved by the universal property of `(𝒪_U)_{(f|_U)_S}`, not by
unfolding the identification: `AlgebraicGeometry.RingedSite.hom_ext_unitToAwayModule` says that
two maps out of it agree once they agree after the canonical map out of `𝒪_U`, provided every
power of `(f|_U)_S` acts bijectively on the sections of the target. The target here is
`(𝒪_U)_{(f|_U)_T}` with `S ⊆ T`, and the bijectivity is
`AlgebraicGeometry.RingedSite.isUnit_toAwaySheaf_prodGlobalSection_of_subset` read on sections;
after the canonical map both sides become the canonical map `𝒪_U ⟶ (𝒪_U)_{(f|_U)_T}`, by
`AlgebraicGeometry.RingedSite.unitToAwayModule_comp_awayModuleTransition` on the two sites and
`AlgebraicGeometry.RingedSite.overFunctor_map_unitToAwayModule_comp_awayModuleProdOverIso`.

The passage from the system to the complex is the two halves of functoriality of
`CategoryTheory.AlternatingCech.complex`:
`CategoryTheory.AlternatingCech.mapComplexIso` exchanges the complex with the restriction functor,
which is additive and preserves the finite products forming the terms
(`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits`), and
`CategoryTheory.AlternatingCech.complexMapIso` turns the isomorphism of systems into an
isomorphism of complexes.

*Why the two proofs here go through abstract lemmas.* Sheaves of modules on the slice are indexed
by `(X.over U).ringSheaf` when they come from the slice ringed site and by `X.ringSheaf.over U`
when they come from restriction along `CategoryTheory.Over.forget U`. Those two sheaves of rings
are the same object, but only after the restriction of the structure sheaf along `Over.forget U`
is commuted past forgetting commutativity, which is invisible at the transparency `rw` uses: a
composite that crosses from one indexing to the other is ill-typed there, and every rewrite on it
fails. So each of the two statements is reduced, by a single `exact`, to a lemma stated in one
abstract category where the rewriting is unproblematic —
`CategoryTheory.comp_hom_eq_hom_comp_of_hom_ext` below and
`CategoryTheory.AlternatingCech.mapTermIso_hom_comp_mapTerm_comp_lift` of
`ExtendedCechFunctoriality.lean`. The alternative, making the functors involved locally
`implicit_reducible` as
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomRestriction.lean` does, does
not suffice here: it restores the typing of a composite of two morphisms but not of the
compositions with the unit sheaf and with a product projection that these proofs need.

Nothing here carries a `stacks` attribute: the extended alternating Čech complex of a finite
family of global sections of the structure sheaf of a ringed site is not a notion the source
names separately, and neither is its base change along `𝒞/U ⥤ 𝒞`. It is one of the inputs of
[Stacks, Tag 099E], which is `AlgebraicGeometry.RingedSite.exists_isGlobalExtendedCech`.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
* [Stacks Project, Tag 099H](https://stacks.math.columbia.edu/tag/099H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

/-- **A square of isomorphisms commutes as soon as it commutes after a map out of which
morphisms are determined.** Given `e₁ : A₁ ≅ B₁`, `e₂ : A₂ ≅ B₂`, maps `φ : A₁ ⟶ A₂` and
`ψ : B₁ ⟶ B₂`, and maps out of a common source `Z` matching up along the two isomorphisms and
commuting with `φ` and with `ψ`, the square commutes — provided a morphism out of `B₁` is
determined by its composite with `Z ⟶ B₁`.

This is the shape of a naturality check for an identification which is *not* given by a formula,
only by a universal property: `hext` is that universal property, and `hφ`, `hψ` are the two
compatibilities it is applied to. -/
theorem comp_hom_eq_hom_comp_of_hom_ext {𝒞 : Type*} [Category 𝒞] {A₁ A₂ B₁ B₂ Z : 𝒞}
    (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (φ : A₁ ⟶ A₂) (ψ : B₁ ⟶ B₂)
    {uS : Z ⟶ A₁} {uT : Z ⟶ A₂} {vS : Z ⟶ B₁} {vT : Z ⟶ B₂}
    (hS : uS ≫ e₁.hom = vS) (hT : uT ≫ e₂.hom = vT)
    (hφ : uS ≫ φ = uT) (hψ : vS ≫ ψ = vT)
    (hext : ∀ {g₁ g₂ : B₁ ⟶ B₂}, vS ≫ g₁ = vS ≫ g₂ → g₁ = g₂) :
    φ ≫ e₂.hom = e₁.hom ≫ ψ := by
  rw [← Iso.inv_comp_eq]
  refine hext ?_
  rw [hψ, ← hT, ← hφ, ← hS]
  simp

end CategoryTheory

namespace AlgebraicGeometry.RingedSite

section Bijective

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **For `S ⊆ T` every power of `f_S` acts bijectively on the sections of `𝒪_{f_T}`**: it acts
by multiplication by its image, which
`AlgebraicGeometry.RingedSite.isUnit_toAwaySheaf_prodGlobalSection_of_subset` says is a unit. -/
theorem bijective_smul_awayModule_prodGlobalSection_of_subset {S T : Finset (Fin r)}
    (hST : S ⊆ T) (V : X.Cᵒᵖ) (n : ℕ) :
    Function.Bijective fun t : (awayModule X (prodGlobalSection f T)).val.obj V =>
      globalSectionVal (prodGlobalSection f S) V ^ n • t := by
  show Function.Bijective fun t : (awaySheaf (prodGlobalSection f T)).obj.obj V =>
    ((toAwaySheaf (prodGlobalSection f T)).hom.app V).hom
      (globalSectionVal (prodGlobalSection f S) V ^ n) * t
  exact IsUnit.isUnit_iff_mulLeft_bijective.1
    (isUnit_toAwaySheaf_prodGlobalSection_of_subset f hST V n)

end Bijective

section System

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C)
  [HasWeakSheafify (X.over U).J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The identification of the Čech terms is natural in the subset.** For `S ⊆ T` it carries the
restriction of the transition map `𝒪_{f_S} ⟶ 𝒪_{f_T}` to the transition map
`(𝒪_U)_{(f|_U)_S} ⟶ (𝒪_U)_{(f|_U)_T}` of the slice.

Both sides are maps out of `(𝒪_U)_{(f|_U)_S}`, every power of `(f|_U)_S` acts bijectively on the
sections of the target `(𝒪_U)_{(f|_U)_T}`, and after the canonical map `𝒪_U ⟶ (𝒪_U)_{(f|_U)_S}`
both become the canonical map `𝒪_U ⟶ (𝒪_U)_{(f|_U)_T}`. -/
theorem overFunctor_map_awayModuleTransition_comp_awayModuleProdOverIso
    {S T : Finset (Fin r)} (hST : S ⊆ T) :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
          (awayModuleTransition X f hST) ≫
        (awayModuleProdOverIso X U f T).hom =
      (awayModuleProdOverIso X U f S).hom ≫
        awayModuleTransition (X.over U) (fun i ↦ globalSectionOver X U (f i)) hST :=
  comp_hom_eq_hom_comp_of_hom_ext (awayModuleProdOverIso X U f S)
    (awayModuleProdOverIso X U f T)
    ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
      (awayModuleTransition X f hST))
    (awayModuleTransition (X.over U) (fun i ↦ globalSectionOver X U (f i)) hST)
    (overFunctor_map_unitToAwayModule_comp_awayModuleProdOverIso X U f S)
    (overFunctor_map_unitToAwayModule_comp_awayModuleProdOverIso X U f T)
    (by rw [← Functor.map_comp, unitToAwayModule_comp_awayModuleTransition])
    (unitToAwayModule_comp_awayModuleTransition (X.over U)
      (fun i ↦ globalSectionOver X U (f i)) hST)
    fun h ↦ hom_ext_unitToAwayModule (X.over U)
      (prodGlobalSection (fun i ↦ globalSectionOver X U (f i)) S) _
      (bijective_smul_awayModule_prodGlobalSection_of_subset (X.over U)
        (fun i ↦ globalSectionOver X U (f i)) hST) h

/-- **The localization system of the Čech complex restricts to the localization system of the
restricted family:** `S ↦ (𝒪_{f_S})|_U` is `S ↦ (𝒪_U)_{(f|_U)_S}`, with components
`AlgebraicGeometry.RingedSite.awayModuleProdOverIso`. -/
def awayLocalizationFunctorOverIso :
    awayLocalizationFunctor X f ⋙
        SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U ≅
      awayLocalizationFunctor (X.over U) (fun i ↦ globalSectionOver X U (f i)) :=
  NatIso.ofComponents (fun S ↦ awayModuleProdOverIso X U f S) fun {_S _T} g ↦
    overFunctor_map_awayModuleTransition_comp_awayModuleProdOverIso X U f (leOfHom g)

/-- The component of `awayLocalizationFunctorOverIso` at a subset `S` is
`awayModuleProdOverIso X U f S`. -/
@[simp]
theorem awayLocalizationFunctorOverIso_hom_app (S : Finset (Fin r)) :
    (awayLocalizationFunctorOverIso X U f).hom.app S = (awayModuleProdOverIso X U f S).hom :=
  rfl

end System

section Complex

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C)
  [HasWeakSheafify (X.over U).J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- Restriction of sheaves of modules to a slice is additive: it is a sectionwise reindexing, so
addition of morphisms is preserved on the nose. -/
theorem additive_overFunctor :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).Additive :=
  ⟨by intros; ext W; rfl⟩

/-- Restriction of sheaves of modules to a slice preserves the finite products that form the
terms of the extended alternating Čech complex: limits of sheaves of modules are computed
sectionwise, and restriction is a reindexing of sections. -/
theorem preservesFiniteProducts_overFunctor :
    PreservesFiniteProducts
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
  have : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U
  inferInstance

attribute [local instance] additive_overFunctor preservesFiniteProducts_overFunctor

/-- **`Č(f)|_U ≅ Č(f|_U)`**: the extended alternating Čech complex of a finite family of global
sections restricts to the extended alternating Čech complex of the restricted family.

Restriction to the slice is additive and preserves the finite products forming the terms, so by
`CategoryTheory.AlternatingCech.mapComplexIso` it carries `Č(f)` to the Čech complex of the
restricted localization system; and that system is the localization system of the restricted
family by `AlgebraicGeometry.RingedSite.awayLocalizationFunctorOverIso`, so
`CategoryTheory.AlternatingCech.complexMapIso` finishes. -/
def extendedAlternatingCechOverIso :
    ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (extendedAlternatingCech X f) ≅
      extendedAlternatingCech (X.over U) (fun i ↦ globalSectionOver X U (f i)) :=
  AlternatingCech.mapComplexIso
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
      (awayLocalizationFunctor X f) ≪≫
    AlternatingCech.complexMapIso (awayLocalizationFunctorOverIso X U f)

/-- In degree `p`, the isomorphism `Č(f)|_U ≅ Č(f|_U)` is the exchange of restriction with the
degree-`p` term followed by the degree-`p` term of `awayLocalizationFunctorOverIso`. -/
theorem extendedAlternatingCechOverIso_hom_f (p : ℤ) :
    (extendedAlternatingCechOverIso X U f).hom.f p =
      (AlternatingCech.mapTermIso
          (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
          (awayLocalizationFunctor X f) p).hom ≫
        AlternatingCech.mapTerm (awayLocalizationFunctorOverIso X U f).hom p :=
  rfl

/-- **The identification `Č(f)|_U ≅ Č(f|_U)` is compatible with the augmentations:** it carries
the restriction of `𝒪 ⟶ Č(f)^0` to `𝒪_U ⟶ Č(f|_U)^0`.

Both augmentations are assembled from the canonical maps `𝒪 ⟶ 𝒪_{f_S}` out of the structure
sheaf, one for each singleton-cardinality index, so by
`CategoryTheory.AlternatingCech.mapTermIso_hom_comp_mapTerm_comp_lift` the statement reduces to
one factor at a time, where it is
`AlgebraicGeometry.RingedSite.overFunctor_map_unitToAwayModule_comp_awayModuleProdOverIso`. -/
theorem overFunctor_map_extendedAlternatingCechAugmentation_comp :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).map
          (extendedAlternatingCechAugmentation X f) ≫
        (extendedAlternatingCechOverIso X U f).hom.f 0 =
      extendedAlternatingCechAugmentation (X.over U) (fun i ↦ globalSectionOver X U (f i)) :=
  AlternatingCech.mapTermIso_hom_comp_mapTerm_comp_lift
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U)
    (awayLocalizationFunctor X f)
    (awayLocalizationFunctorOverIso X U f)
    (fun S ↦ unitToAwayModule X (prodGlobalSection f S))
    (fun S ↦ unitToAwayModule (X.over U)
      (prodGlobalSection (fun i ↦ globalSectionOver X U (f i)) S))
    (fun S ↦ overFunctor_map_unitToAwayModule_comp_awayModuleProdOverIso X U f S) 0

end Complex

end AlgebraicGeometry.RingedSite

end
