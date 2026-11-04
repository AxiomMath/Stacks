module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineBase
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCechDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleHigherDirectImageRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePushforwardInjectiveAcyclic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleVanishing
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# The étale comparison of higher direct images, once they are quasi-coherent

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site with underlying morphism of schemes
`r`, and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites whose inverse
image is `𝓖 ↦ 𝓖ᵃ` (`AlgebraicGeometry.SmallEtale.associatedModule`) and whose direct image is the
restriction `AlgebraicGeometry.SmallEtale.restrictModule`.  This file constructs the canonical
comparison

`R ⁿ (ε_a)_*(𝓕ᵃ) ≅ (R ⁿ r_* 𝓕)ᵃ`

of [Stacks, Tag 071N] at `τ = étale`, naturally in the quasi-coherent `𝒪_X`-module `𝓕`, out of the
single input that every higher direct image `R ^q (ε_a)_*(𝓕ᵃ)` is quasi-coherent on `Y_étale`.

## The construction

Three canonical isomorphisms, each natural in `𝓕`:

1. the counit `(ε_* M)ᵃ ⟶ M` of `𝓖 ↦ 𝓖ᵃ ⊣ ε_*` at `M = R ⁿ (ε_a)_*(𝓕ᵃ)`, invertible because `M` is
   quasi-coherent on the site (`AlgebraicGeometry.SmallEtale.isIso_counit`);
2. `ε_* (R ⁿ (ε_a)_*(𝓕ᵃ)) ≅ R ⁿ (ε_* ∘ (ε_a)_*)(𝓕ᵃ)`, the collapse of the composite at the *outer*
   functor: `ε_*` preserves the homology of `(ε_a)_*` applied to an injective resolution of `𝓕ᵃ`
   because every term of that complex is the direct image of an injective, hence `ε_*`-acyclic
   (`AlgebraicGeometry.SmallEtale.acyclic_restrictModule_pushforward_of_injective`), and every
   homology object is a higher direct image, quasi-coherent on the site, hence `ε_*`-acyclic
   (`AlgebraicGeometry.SmallEtale.acyclic_restrictModule`, the vanishing of [Stacks, Tag 03DW]).
   This is `CategoryTheory.Functor.rightDerivedCompIsoOfPreservesLeftHomology` fed by
   `CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc`;
3. `R ⁿ (ε_* ∘ (ε_a)_*)(𝓕ᵃ) ≅ R ⁿ r_* 𝓕`, the collapse along the other side of the square
   `ε_* ∘ (ε_a)_* = r_* ∘ ε_*`, which is
   `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardRestrictModuleIso`; here it is assembled
   as a natural isomorphism on the quasi-coherent modules out of the same two pieces,
   `Stacks.RightDerivedComp.natIso` and the unit of `𝓖 ↦ 𝓖ᵃ ⊣ ε_*`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedModuleIsoOfIsQuasicoherentOnSite`:
  the comparison as an isomorphism of functors on the quasi-coherent `𝒪_X`-modules, given that
  every higher direct image of every associated module is quasi-coherent on the site.

No `@[stacks]` attribute is placed here: the quasi-coherence input is proved, for `r`
quasi-compact and quasi-separated, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleHigherDirectImageQcqs.lean`,
which is where the étale clause of [Stacks, Tag 071N] is stated.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] HasDerivedCategory.standard

-- `CategoryTheory.Functor.rightAcyclic` mentions `HasRightDerivedFunctor`; the cheap instance
-- coming from `EnoughInjectives` is given precedence, as in
-- `StacksFrontier/Algebra/Homology/DerivedCategory/AcyclicPreservesHomology.lean`.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The associated modules of the quasi-coherent `𝒪_X`-modules, as a functor on the full
subcategory of quasi-coherent modules: `𝓕 ↦ 𝓕ᵃ`. -/
abbrev associatedModuleOnQuasicoherent :
    (SheafOfModules.isQuasicoherent X.obj.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B X.obj X.property) :=
  Stacks.Cohomology.AffineBase.quasicoherentInclusion X.obj ⋙
    associatedModule B X.obj X.property

/-- The associated module of a quasi-coherent module is acyclic for the restriction `ε_*`. -/
theorem acyclic_restrictModule_associatedModuleOnQuasicoherent
    (𝓕 : (SheafOfModules.isQuasicoherent X.obj.ringCatSheaf).FullSubcategory) :
    Stacks.RightDerivedComp.acyclic (restrictModule B X.obj X.property)
      ((associatedModuleOnQuasicoherent B (X := X)).obj 𝓕) :=
  acyclic_restrictModule B X.obj X.property _
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B X.obj X.property 𝓕.obj
      𝓕.property)

/-- The associated-module functor on the quasi-coherent modules, landing in the `ε_*`-acyclic
objects. -/
def associatedModuleOnQuasicoherentToAcyclic :
    (SheafOfModules.isQuasicoherent X.obj.ringCatSheaf).FullSubcategory ⥤
      (Stacks.RightDerivedComp.acyclic (restrictModule B X.obj X.property)).FullSubcategory :=
  ObjectProperty.lift _ (associatedModuleOnQuasicoherent B (X := X))
    (acyclic_restrictModule_associatedModuleOnQuasicoherent B)

/-- The unit of `𝓖 ↦ 𝓖ᵃ ⊣ ε_*` on the quasi-coherent `𝒪_X`-modules, as an isomorphism of functors
`ε_* (𝓕ᵃ) ≅ 𝓕`, read through the `ε_*`-acyclic objects. -/
def unitQuasicoherentIso :
    (associatedModuleOnQuasicoherentToAcyclic B (X := X) ⋙
        (Stacks.RightDerivedComp.acyclic (restrictModule B X.obj X.property)).ι) ⋙
      restrictModule B X.obj X.property ≅
    Stacks.Cohomology.AffineBase.quasicoherentInclusion X.obj :=
  (NatIso.ofComponents
    (fun 𝓕 ↦ @asIso _ _ _ _ ((associatedModuleAdjunction B X.obj X.property).unit.app 𝓕.obj)
      (unitIsoOnQuasicoherent B X.obj X.property 𝓕))
    (fun g ↦ (associatedModuleAdjunction B X.obj X.property).unit.naturality
      ((SheafOfModules.isQuasicoherent X.obj.ringCatSheaf).ι.map g))).symm

/-- **The collapse along `ε_X`, naturally in the quasi-coherent module.**
`R ⁿ (ε_* ∘ (ε_a)_*)(𝓕ᵃ) ≅ R ⁿ r_* 𝓕`, as an isomorphism of functors on the quasi-coherent
`𝒪_X`-modules.  Objectwise this is
`AlgebraicGeometry.SmallEtale.rightDerivedPushforwardRestrictModuleIso`. -/
def rightDerivedPushforwardRestrictModuleNatIso (n : ℕ) :
    associatedModuleOnQuasicoherent B (X := X) ⋙
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
          restrictModule B Y.obj Y.property).rightDerived n ≅
      Stacks.Cohomology.AffineBase.quasicoherentInclusion X.obj ⋙
        (Scheme.Modules.pushforward (schemeHom B a)).rightDerived n :=
  Functor.isoWhiskerLeft (associatedModuleOnQuasicoherent B (X := X))
      (Stacks.RightDerivedSpelling.rightDerivedIsoOfNatIsoOfAdditive ⟨by intros; rfl⟩
        ⟨by intros; rfl⟩ (restrictModulePushforwardIso B a) n) ≪≫
    Functor.isoWhiskerRight
      (ObjectProperty.liftCompιIso _ (associatedModuleOnQuasicoherent B (X := X))
        (acyclic_restrictModule_associatedModuleOnQuasicoherent B)).symm
      ((restrictModule B X.obj X.property ⋙
        Scheme.Modules.pushforward (schemeHom B a)).rightDerived n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (associatedModuleOnQuasicoherentToAcyclic B (X := X))
      (Stacks.RightDerivedComp.natIso (restrictModule B X.obj X.property)
        (Scheme.Modules.pushforward (schemeHom B a)) n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (unitQuasicoherentIso B (X := X))
      ((Scheme.Modules.pushforward (schemeHom B a)).rightDerived n)

section Comparison

variable (hM : ∀ (𝓕 : (SheafOfModules.isQuasicoherent X.obj.ringCatSheaf).FullSubcategory)
  (q : ℕ), (((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived
    q).obj ((associatedModule B X.obj X.property).obj 𝓕.obj)).IsQuasicoherentOnSite)

include hM

/-- `ε_*` preserves the homology of `(ε_a)_*` applied to the chosen injective resolution of an
associated module, once every higher direct image of it is quasi-coherent on the site: the terms
are injective and the homology objects are `ε_*`-acyclic. -/
theorem restrictModule_preservesLeftHomologyOf_pushforward_injectiveResolution (n : ℕ)
    (𝓕 : (SheafOfModules.isQuasicoherent X.obj.ringCatSheaf).FullSubcategory) :
    (restrictModule B Y.obj Y.property).PreservesLeftHomologyOf
      ((((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (injectiveResolution ((associatedModuleOnQuasicoherent B (X := X)).obj 𝓕)).cocomplex).sc
            n) := by
  refine ((restrictModule B Y.obj Y.property).rightAcyclic_cycles_and_preservesLeftHomologyOf_sc
    _ (fun i ↦ ?_) (fun i ↦ ?_) n).2
  · have := (injectiveResolution ((associatedModuleOnQuasicoherent B (X := X)).obj 𝓕)).injective i
    exact (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic _ _).2
      (acyclic_restrictModule_pushforward_of_injective B a _)
  · exact (restrictModule B Y.obj Y.property).rightAcyclic.prop_of_iso
      ((injectiveResolution ((associatedModuleOnQuasicoherent B (X := X)).obj 𝓕)).isoRightDerivedObj
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) i)
      ((Stacks.RightDerivedComp.rightAcyclic_iff_acyclic _ _).2
        (acyclic_restrictModule B Y.obj Y.property _ (hM 𝓕 i)))

/-- The counit of `𝓖 ↦ 𝓖ᵃ ⊣ ε_*` at the higher direct images of the associated modules, as an
isomorphism of functors on the quasi-coherent `𝒪_X`-modules. -/
def counitHigherDirectImageIso (n : ℕ) :
    associatedModuleOnQuasicoherent B (X := X) ⋙
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived n ⋙
          restrictModule B Y.obj Y.property ⋙ associatedModule B Y.obj Y.property ≅
      associatedModuleOnQuasicoherent B (X := X) ⋙
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived n :=
  NatIso.ofComponents
    (fun 𝓕 ↦
      @asIso _ _ _ _ ((associatedModuleAdjunction B Y.obj Y.property).counit.app
          (((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived n).obj
            ((associatedModule B X.obj X.property).obj 𝓕.obj)))
        (isIso_counit B Y.obj Y.property _ (hM 𝓕 n)
          (isQuasicoherent_restrictModule B Y.obj Y.property _ (hM 𝓕 n))))
    (fun g ↦ (associatedModuleAdjunction B Y.obj Y.property).counit.naturality _)

/-- **The étale comparison of [Stacks, Tag 071N], given quasi-coherence of the higher direct
images.**  If every `R ^q (ε_a)_*(𝓕ᵃ)` is quasi-coherent on `Y_étale`, then

`R ⁿ (ε_a)_*(𝓕ᵃ) ≅ (R ⁿ r_* 𝓕)ᵃ`

naturally in the quasi-coherent `𝒪_X`-module `𝓕`, in every degree `n`.  The isomorphism is the
composite of the inverse counit of `𝓖 ↦ 𝓖ᵃ ⊣ ε_*`, the collapse of `ε_* ∘ (ε_a)_*` at its outer
functor, and the collapse along `ε_* ∘ (ε_a)_* = r_* ∘ ε_*`; nothing is chosen. -/
def higherDirectImageAssociatedModuleIsoOfIsQuasicoherentOnSite (n : ℕ) :
    associatedModuleOnQuasicoherent B (X := X) ⋙
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived n ≅
      Stacks.Cohomology.AffineBase.quasicoherentInclusion X.obj ⋙
        (Scheme.Modules.pushforward (schemeHom B a)).rightDerived n ⋙
          associatedModule B Y.obj Y.property :=
  (counitHigherDirectImageIso B a hM n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.associator _ _ _) ≪≫
        Functor.rightDerivedCompIsoOfPreservesLeftHomology
          (associatedModuleOnQuasicoherent B (X := X))
          (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
          (restrictModule B Y.obj Y.property) n
          (restrictModule_preservesLeftHomologyOf_pushforward_injectiveResolution B a hM n) ≪≫
        rightDerivedPushforwardRestrictModuleNatIso B a n)
      (associatedModule B Y.obj Y.property) ≪≫
    Functor.associator _ _ _

end Comparison

end AlgebraicGeometry.SmallEtale

end
