module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ExtensionByZeroFormula
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ModulePushforwardLocalization
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of modules along a localization of a ringed topos is exact and keeps K-injectives

Let `X` be a ringed topos presented by a site `(C, J)`, let `F` be a sheaf of sets on `C` and let
`j : X_F ⟶ X` be the localization of `X` at `F`. By Stacks 04IE part (2) the pullback `j^*` of
sheaves of modules is restriction to the site of elements of `F`, and by part (4) it has a left
adjoint `j_!`, the lower shriek, whose presheaf-level form has over an object `V` of `C` the
direct sum `⨁_{s ∈ F(V)} G(V, s)`. This file draws the two consequences for derived functors.

* `j^*` is exact: it is a right adjoint, so it preserves limits, and it is a left adjoint.
* `j_!` is exact (Stacks 03DJ for the site of elements of a sheaf): it preserves monomorphisms,
  because a monomorphism of sheaves of modules induces a direct sum of monomorphisms of modules
  on the sections of the direct-sum presheaf, and `ModuleCat` satisfies Grothendieck's axiom
  AB4; and it preserves cokernels, being a left adjoint. Consequently `j^*` carries K-injective
  complexes to K-injective complexes (Stacks 08BJ).

## Main definitions

* `AlgebraicGeometry.RingedTopos.localizationToModulesHomPullbackIso`: Stacks 04IE part (2) for the
  pullback built from `AlgebraicGeometry.RingedToposHom.toModulesHom`, the four-field morphism the
  derived pullback is formed from.

## Main results

* `AlgebraicGeometry.RingedTopos.elementExtensionByZero_preservesMonomorphisms` and
  `.elementExtensionByZero_preservesFiniteLimits`: the lower shriek along the localization
  preserves monomorphisms, and is exact.
* `AlgebraicGeometry.RingedTopos.isKInjective_elementRestriction`: restriction to the site of
  elements keeps K-injectives.
* `AlgebraicGeometry.RingedTopos.preservesFiniteLimits_localization_pullbackModules`: `j^*` is
  left exact.
* `AlgebraicGeometry.RingedTopos.isKInjective_localization_pullbackModules`: `j^*` carries
  K-injective complexes to K-injective complexes.

## References

* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedTopos

universe u

variable (X : RingedTopos.{u, u, u}) (F : X.Topos)

/-- The map of direct sums induced on the sections over `V` of the presheaf-level lower shriek by
a morphism `f : G ⟶ H` of sheaves of modules on the site of elements: on the summand indexed by
`s ∈ F(V)` it is the component of `f` at the element `(V, s)`. -/
noncomputable def extensionByZeroSummandsMap
    {G H : SheafOfModules.{u} (localizedRingSheaf X F)} (f : G ⟶ H) (V : X.C) :
    (∐ extensionByZeroSummands X F G V) ⟶ (∐ extensionByZeroSummands X F H V) :=
  Limits.Sigma.map (fun s => (f.val.app (elementObj X F (Opposite.op V) s) :
    extensionByZeroSummands X F G V s ⟶ extensionByZeroSummands X F H V s))

/-- `extensionByZeroSummandsMap` is a monomorphism as soon as `f` is. -/
lemma extensionByZeroSummandsMap_mono
    {G H : SheafOfModules.{u} (localizedRingSheaf X F)} (f : G ⟶ H) (V : X.C) [Mono f] :
    Mono (extensionByZeroSummandsMap X F f V) := by
  have hval : Mono f.val := by
    change Mono ((SheafOfModules.forget (localizedRingSheaf X F)).map f)
    infer_instance
  exact Stacks.Sites.ExtensionByZero.mono_sigmaMap _ fun s => (ModuleCat.mono_iff_injective _).2
    (PresheafOfModules.injective_of_mono f.val (elementObj X F (Opposite.op V) s))

/-- The direct-sum formula is natural in the sheaf of modules. -/
lemma extensionByZeroSectionMap_naturality
    {G H : SheafOfModules.{u} (localizedRingSheaf X F)} (f : G ⟶ H) (V : X.C) :
    ((PresheafOfModules.pullback.{u} (F := elementProjection X F)
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (S := (localizedRingSheaf X F).obj) (elementModuleRingPresheafHom X F)).map
          f.val).app (Opposite.op V) ≫
      (extensionByZeroPresheafSectionIso X F H V).hom =
      (extensionByZeroPresheafSectionIso X F G V).hom ≫ extensionByZeroSummandsMap X F f V := by
  let eG := extensionByZeroPresheafSectionIso X F G V
  let eH := extensionByZeroPresheafSectionIso X F H V
  let adj := PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (F := elementProjection X F) (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (S := (localizedRingSheaf X F).obj) (elementModuleRingPresheafHom X F)
  apply (Iso.inv_comp_eq eG).1
  refine Sigma.hom_ext _ _ fun s => ?_
  have hG' := eq_of_heq (extensionByZeroPresheafSectionIso_inv_ι X F G V s)
  have hH' := eq_of_heq (extensionByZeroPresheafSectionIso_inv_ι X F H V s)
  have hnat' := (congrArg (fun g => g.app (elementObj X F (Opposite.op V) s))
    (adj.unit.naturality f.val)).symm
  have hUnit : ((adj.unit.app H.val).app (elementObj X F (Opposite.op V) s)) ≫ eH.hom =
      Sigma.ι (extensionByZeroSummands X F H V) s :=
    ((Iso.comp_inv_eq eH).1 hH').symm
  have hι := (Limits.Sigma.ι_map (g := extensionByZeroSummands X F G V)
    (f := extensionByZeroSummands X F H V)
    (fun t => (f.val.app (elementObj X F (Opposite.op V) t) :
      extensionByZeroSummands X F G V t ⟶ extensionByZeroSummands X F H V t)) s).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun x => x ≫ ((PresheafOfModules.pullback.{u} (F := elementProjection X F)
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (S := (localizedRingSheaf X F).obj) (elementModuleRingPresheafHom X F)).map
          f.val).app (Opposite.op V) ≫ eH.hom) hG').trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun x => x ≫ eH.hom) hnat').trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun x => f.val.app (elementObj X F (Opposite.op V) s) ≫ x) hUnit).trans
              hι)))))

/-- The presheaf-level lower shriek along the localization preserves monomorphisms. -/
private lemma elementExtensionByZeroPresheaf_map_mono
    {G H : SheafOfModules.{u} (localizedRingSheaf X F)} (f : G ⟶ H) [Mono f] :
    Mono ((PresheafOfModules.pullback.{u} (F := elementProjection X F)
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      (S := (localizedRingSheaf X F).obj) (elementModuleRingPresheafHom X F)).map f.val) := by
  apply PresheafOfModules.mono_of_injective
  intro V
  rw [← ModuleCat.mono_iff_injective]
  have hcomp :
      ((PresheafOfModules.pullback.{u} (F := elementProjection X F)
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (S := (localizedRingSheaf X F).obj) (elementModuleRingPresheafHom X F)).map
          f.val).app V =
      ((extensionByZeroPresheafSectionIso X F G V.unop).hom ≫
        extensionByZeroSummandsMap X F f V.unop) ≫
          (extensionByZeroPresheafSectionIso X F H V.unop).inv :=
    (Iso.eq_comp_inv _).2 (extensionByZeroSectionMap_naturality X F f V.unop)
  have := extensionByZeroSummandsMap_mono X F f V.unop
  rw [hcomp]
  infer_instance

/-- Restriction of sheaves of modules to the site of elements is additive. -/
private lemma elementPushforward_additive :
    (SheafOfModules.pushforward.{u} (F := elementProjection X F) (J := elementTopology X F)
      (K := X.J) (elementModuleRingHom X F)).Additive :=
  ⟨rfl⟩

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 03DJ for the site of elements of a sheaf, monomorphisms.** The lower shriek of
sheaves of modules along the localization of a ringed topos at a sheaf preserves monomorphisms. -/
lemma elementExtensionByZero_preservesMonomorphisms :
    Functor.PreservesMonomorphisms (SheafOfModules.pullback.{u}
      (F := elementProjection X F) (J := elementTopology X F) (K := X.J)
      (elementModuleRingHom X F)) := by
  constructor
  intro G H f hf
  have : (PresheafOfModules.pushforward.{u} (elementModuleRingHom X F).hom).IsRightAdjoint :=
    elementPresheafModulePushforwardIsRightAdjoint X F
  have : Presheaf.IsLocallyInjective X.J (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
    Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h => by simpa using h
  have : Presheaf.IsLocallySurjective X.J (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
    Presheaf.isLocallySurjective_of_iso _ _
  rw [← NatIso.naturality_2 (SheafOfModules.pullbackIso (F := elementProjection X F)
    (J := elementTopology X F) (K := X.J) (elementModuleRingHom X F)) f]
  have hcomp : Mono ((SheafOfModules.forget (localizedRingSheaf X F) ⋙
      PresheafOfModules.pullback.{u} (elementModuleRingHom X F).hom ⋙
      PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
        f) := by
    change Mono ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      ((PresheafOfModules.pullback.{u} (elementModuleRingHom X F).hom).map f.val))
    have : Mono ((PresheafOfModules.pullback.{u} (elementModuleRingHom X F).hom).map f.val) :=
      elementExtensionByZeroPresheaf_map_mono X F f
    infer_instance
  exact @mono_comp _ _ _ _ _ _ inferInstance _ (@mono_comp _ _ _ _ _ _ hcomp _ inferInstance)

/-- **Stacks 03DJ for the site of elements of a sheaf.** The lower shriek of sheaves of modules
along the localization of a ringed topos at a sheaf is exact. -/
lemma elementExtensionByZero_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.pullback.{u}
      (F := elementProjection X F) (J := elementTopology X F) (K := X.J)
      (elementModuleRingHom X F)) := by
  let L := SheafOfModules.pullback.{u} (F := elementProjection X F) (J := elementTopology X F)
    (K := X.J) (elementModuleRingHom X F)
  let adj := SheafOfModules.pullbackPushforwardAdjunction.{u} (F := elementProjection X F)
    (J := elementTopology X F) (K := X.J) (elementModuleRingHom X F)
  have := elementPushforward_additive X F
  have : L.Additive := adj.left_adjoint_additive
  have : Functor.PreservesMonomorphisms L := elementExtensionByZero_preservesMonomorphisms X F
  have : PreservesColimits L := adj.leftAdjoint_preservesColimits
  have : Functor.PreservesHomology L := Functor.preservesHomology_of_preservesMonos_and_cokernels L
  exact Functor.preservesFiniteLimits_of_preservesHomology L

/-- Restriction of sheaves of modules to the site of elements carries K-injective complexes to
K-injective complexes, its left adjoint the lower shriek being exact (Stacks 08BJ). -/
theorem isKInjective_elementRestriction
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective (((SheafOfModules.pushforward.{u} (F := elementProjection X F)
      (J := elementTopology X F) (K := X.J) (elementModuleRingHom X F)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  have := elementPushforward_additive X F
  let adj := SheafOfModules.pullbackPushforwardAdjunction.{u} (F := elementProjection X F)
    (J := elementTopology X F) (K := X.J) (elementModuleRingHom X F)
  have : (SheafOfModules.pullback.{u} (F := elementProjection X F) (J := elementTopology X F)
      (K := X.J) (elementModuleRingHom X F)).Additive := adj.left_adjoint_additive
  have := elementExtensionByZero_preservesFiniteLimits X F
  have : PreservesFiniteColimits (SheafOfModules.pullback.{u} (F := elementProjection X F)
      (J := elementTopology X F) (K := X.J) (elementModuleRingHom X F)) :=
    have := adj.leftAdjoint_preservesColimits
    inferInstance
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ adj I

/-- Pullback of sheaves of modules along the localization morphism, built from the four-field
morphism `AlgebraicGeometry.RingedToposHom.toModulesHom`, is restriction to the site of elements:
Stacks 04IE part (2) read through the identification of the two four-field morphisms. -/
noncomputable def localizationToModulesHomPullbackIso :
    (localizationMorphism X F).toModulesHom.pullbackModules ≅ elementRestrictionModules X F :=
  eqToIso (congrArg (fun φ ↦ φ.pullbackModules)
    (localizationMorphism X F).toModulesHom_eq_toRingedToposModulesHom) ≪≫
    localizationModulePullbackIso X F

/-- Restriction to the site of elements is additive. -/
instance elementRestrictionModules_additive : (elementRestrictionModules X F).Additive where
  map_add := rfl

/-- Restriction to the site of elements is a right adjoint, of the lower shriek. -/
instance elementRestrictionModules_isRightAdjoint :
    (elementRestrictionModules X F).IsRightAdjoint :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u} (F := elementProjection X F)
    (J := elementTopology X F) (K := X.J) (elementModuleRingHom X F)).isRightAdjoint

/-- **Pullback of sheaves of modules along a localization is left exact.** It is restriction to
the site of elements, which is a right adjoint. -/
instance preservesFiniteLimits_localization_pullbackModules :
    PreservesFiniteLimits (localizationMorphism X F).toModulesHom.pullbackModules :=
  preservesFiniteLimits_of_natIso (localizationToModulesHomPullbackIso X F).symm

/-- **Pullback of sheaves of modules along a localization keeps K-injectives.** It is restriction
to the site of elements, whose left adjoint, the lower shriek, is exact. -/
@[sga "4 V 4.12" "more general"]
theorem isKInjective_localization_pullbackModules
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((localizationMorphism X F).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  have : CochainComplex.IsKInjective
      (((elementRestrictionModules X F).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    isKInjective_elementRestriction X F I
  exact CochainComplex.isKInjective_of_iso
    ((NatIso.mapHomologicalComplex (localizationToModulesHomPullbackIso X F)
      (ComplexShape.up ℤ)).app I).symm

end AlgebraicGeometry.RingedTopos

end
