module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.Opposite
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.GeneralSupports.SupportedInjectives
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn
public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport

/-!
# The bounded-below derived category of modules with support

For a specialization-closed subset `T` of the spectrum of a Noetherian ring, the bounded-below
derived category of modules supported in `T` agrees with the full subcategory of the ambient
derived category whose cohomology is bounded below and supported in `T`.

## Main results

* `Module.exists_supportedModulesDerivedPlusEquivalence` gives the equivalence and identifies its
  underlying functor, after inclusion, with the derived functor of the inclusion of supported
  modules.

## Implementation notes

The target is expressed using `DerivedCategoryB.derivedCategoryBPlus`. The natural isomorphism in
the conclusion pins the equivalence to the canonical functor induced by the inclusion of the
Serre subcategory, rather than merely asserting an abstract equivalence of categories.

Supported modules embed into supported ambient injectives, by
`Module.supportedModule_has_ambientInjective_envelope`. Duality then reduces the comparison to
the bounded-above comparison for a Serre subcategory in the opposite category; the covering
condition that comparison needs follows by extending morphisms into those injectives.

## References

* [Stacks Project, Tag 0EF2](https://stacks.math.columbia.edu/tag/0EF2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.LocalCohomology

universe u v w

namespace Module

attribute [local instance] HasDerivedCategory.standard

/-- The inclusion of the modules supported in `T` preserves finite limits. -/
local instance (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    PreservesFiniteLimits (supportModuleProperty A T :
      ObjectProperty (ModuleCat.{v} A)).ι :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of the modules supported in `T` preserves finite colimits. -/
local instance (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    PreservesFiniteColimits (supportModuleProperty A T :
      ObjectProperty (ModuleCat.{v} A)).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- The opposite of the property of being supported in `T` is a Serre class of the opposite
category of modules. -/
public lemma supportProperty_op_isSerre
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R)) :
    (supportModuleProperty.{u, v} R T).op.IsSerreClass := by
  let P : ObjectProperty (ModuleCat.{v} R) :=
    supportModuleProperty.{u, v} R T
  have : P.op.IsClosedUnderSubobjects := ⟨fun f _ hY => P.prop_of_epi f.unop hY⟩
  have : P.op.IsClosedUnderQuotients := ⟨fun f _ hX => P.prop_of_mono f.unop hX⟩
  have : P.op.IsClosedUnderExtensions :=
    ⟨fun hS h₁ h₃ => P.prop_X₂_of_shortExact hS.unop h₃ h₁⟩
  constructor

/-- `Module.supportProperty_op_isSerre` as a local instance. -/
local instance supportProperty_op_isSerre_instance
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R)) :
    (supportModuleProperty.{u, v} R T).op.IsSerreClass :=
  supportProperty_op_isSerre T

/-- The opposite of the property of being supported in `T` is closed under finite products. -/
public instance supportProperty_op_isClosedUnderFiniteProducts
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R)) :
    (supportModuleProperty.{u, v} R T).op.IsClosedUnderFiniteProducts := by
  let P : ObjectProperty (ModuleCat.{v} R) :=
    supportModuleProperty.{u, v} R T
  exact .of_isClosedUnderLimitsOfShape fun (J : Type) _ =>
    (P.op.isClosedUnderLimitsOfShape_iff_of_equivalence (Discrete.opposite J)).mp
      ((ObjectProperty.isClosedUnderColimitsOfShape_iff_op (P := P) (J := Discrete J)).mp
        inferInstance)

/-- The inclusion of the opposite of the modules supported in `T` preserves finite limits. -/
public instance supportProperty_op_preservesFiniteLimits
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R)) :
    PreservesFiniteLimits
      ((supportModuleProperty.{u, v} R T).op.ι) :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of the opposite of the modules supported in `T` preserves finite
colimits. -/
public instance supportProperty_op_preservesFiniteColimits
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R)) :
    PreservesFiniteColimits
      ((supportModuleProperty.{u, v} R T).op.ι) :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- For `T` stable under specialization over a Noetherian ring, every epimorphism in the
opposite category of modules onto an object supported in `T` is covered by a morphism from an
object supported in `T`. Dually, an injection of a supported module into `M` stays injective
after composing with a suitable map from `M` to a supported module. -/
public lemma supportProperty_op_coversEpis
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (T : Set (PrimeSpectrum R)) (hT : StableUnderSpecialization T) :
    ∀ ⦃X Y : (ModuleCat.{v} R)ᵒᵖ⦄ (f : X ⟶ Y), Epi f →
    (supportModuleProperty.{u, v} R T).op Y →
      ∃ (X' : (ModuleCat.{v} R)ᵒᵖ) (g : X' ⟶ X),
        (supportModuleProperty.{u, v} R T).op X' ∧ Epi (g ≫ f) := by
  intro X Y f hf hY
  let eX : ULift.{u} X.unop ≃ₗ[R] X.unop := ULift.moduleEquiv
  let eY : ULift.{u} Y.unop ≃ₗ[R] Y.unop := ULift.moduleEquiv
  let F : ModuleCat.of R (ULift.{u} Y.unop) ⟶ ModuleCat.of R (ULift.{u} X.unop) :=
    ModuleCat.ofHom (eX.symm.toLinearMap.comp (f.unop.hom.comp eY.toLinearMap))
  have : Mono F := (ModuleCat.mono_iff_injective F).2 <| eX.symm.injective.comp
    (((ModuleCat.mono_iff_injective f.unop).1 inferInstance).comp eY.injective)
  have hY' : Module.support R (ULift.{u} Y.unop) ⊆ T :=
    (Module.support_subset_of_injective eY.toLinearMap eY.injective).trans hY
  obtain ⟨J, hJP, j, hj, hJ⟩ := supportedModule_has_ambientInjective_envelope T hT
    ⟨ModuleCat.of R (ULift.{u} Y.unop), hY'⟩
  have : CategoryTheory.Injective (ModuleCat.of R (↑J)) := hJ
  let g := CategoryTheory.Injective.factorThru j F
  have hgj : F ≫ g = j := CategoryTheory.Injective.comp_factorThru j F
  let q : X.unop →ₗ[R] J := g.hom.comp eX.symm.toLinearMap
  let Q := X.unop ⧸ q.ker
  let i : Q →ₗ[R] J := q.range.subtype.comp q.quotKerEquivRange.toLinearMap
  have hQ : Module.support R Q ⊆ T :=
    (Module.support_subset_of_injective i
      (q.range.subtype_injective.comp q.quotKerEquivRange.injective)).trans hJP
  let k : X.unop ⟶ ModuleCat.of R Q := ModuleCat.ofHom q.ker.mkQ
  have hk : Mono (f.unop ≫ k) := by
    apply (ModuleCat.mono_iff_injective _).2
    intro a b hab
    have hab' : q (f.unop.hom a) = q (f.unop.hom b) := by
      have h := congrArg (fun t => (q.quotKerEquivRange t : J)) hab
      change (q.quotKerEquivRange (Submodule.Quotient.mk (f.unop.hom a)) : J) =
        (q.quotKerEquivRange (Submodule.Quotient.mk (f.unop.hom b)) : J) at h
      simpa only [LinearMap.quotKerEquivRange_apply_mk] using h
    have hq (a : Y.unop) : q (f.unop.hom a) = j.hom (eY.symm a) := by
      simpa [F, q] using congrArg (fun t => t.hom (eY.symm a)) hgj
    rw [hq, hq] at hab'
    exact eY.symm.injective ((ModuleCat.mono_iff_injective j).1 hj hab')
  exact ⟨Opposite.op (ModuleCat.of R Q), k.op, hQ, inferInstanceAs (Epi (f.unop ≫ k).op)⟩

/-- The functor on derived categories induced by an additive equivalence of abelian categories
is an equivalence. -/
public lemma mapDerivedCategory_isEquivalence_of_equivalence
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] : e.functor.mapDerivedCategory.IsEquivalence := by
  let Φ := e.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  have : Φ.functor.IsEquivalence :=
    (e.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  have : Φ.IsInduced := ⟨by
    ext X Y f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f e.functor⟩
  have : Φ.IsLocalizedEquivalence := Φ.isLocalizedEquivalence_of_isInduced
  let : CatCommSq Φ.functor DerivedCategory.Q DerivedCategory.Q e.functor.mapDerivedCategory :=
    ⟨e.functor.mapDerivedCategoryFactors.symm⟩
  exact Φ.isEquivalence DerivedCategory.Q DerivedCategory.Q e.functor.mapDerivedCategory

/-- The opposite of the bounded-below derived category of modules supported in `T` is
equivalent to the bounded-above derived category of the opposite Serre subcategory. -/
public noncomputable def supportedPlusOpEquivalence
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R)) :
    (DerivedCategory.Plus
      ((supportModuleProperty.{u, v} R T).FullSubcategory))ᵒᵖ ≌
      DerivedCategory.Minus
        ((supportModuleProperty.{u, v} R T).op.FullSubcategory) := by
  let P : ObjectProperty (ModuleCat.{v} R) :=
    supportModuleProperty.{u, v} R T
  let Pop : ObjectProperty ((ModuleCat.{v} R)ᵒᵖ) := P.op
  letI : Pop.IsSerreClass := supportProperty_op_isSerre T
  letI : Pop.IsWeakSerreClass := inferInstance
  letI : Pop.IsClosedUnderFiniteProducts :=
    supportProperty_op_isClosedUnderFiniteProducts.{u, v} T
  letI : Abelian Pop.FullSubcategory := inferInstance
  let Ecat : P.FullSubcategoryᵒᵖ ≌ Pop.FullSubcategory :=
    (ObjectProperty.opEquivalence P).symm
  letI : Ecat.functor.Additive := ⟨rfl⟩
  let EderivedOp :
      (DerivedCategory P.FullSubcategory)ᵒᵖ ≌
        DerivedCategory P.FullSubcategoryᵒᵖ :=
    DerivedCategory.derivedOpEquivalence (C := P.FullSubcategory)
  letI : Ecat.functor.mapDerivedCategory.IsEquivalence :=
    mapDerivedCategory_isEquivalence_of_equivalence Ecat
  let E : (DerivedCategory P.FullSubcategory)ᵒᵖ ≌ DerivedCategory Pop.FullSubcategory :=
    EderivedOp.trans Ecat.functor.mapDerivedCategory.asEquivalence
  let PlusP : ObjectProperty
      (DerivedCategory P.FullSubcategory) :=
    DerivedCategory.TStructure.t.plus
  let MinusPop : ObjectProperty
      (DerivedCategory Pop.FullSubcategory) :=
    DerivedCategory.TStructure.t.minus
  have hprop : MinusPop.inverseImage E.functor = PlusP.op := by
    ext X
    change (∃ n : ℤ, (E.functor.obj X).IsLE n) ↔ ∃ n : ℤ, X.unop.IsGE n
    constructor
    · rintro ⟨n, hn⟩
      change (Ecat.functor.mapDerivedCategory.obj (EderivedOp.functor.obj X)).IsLE n at hn
      exact ⟨-n, (DerivedCategory.isLE_derivedOpEquivalence_functor_obj_iff
        (C := P.FullSubcategory) X.unop (-n)).1 (by simpa using
          (Functor.isLE_mapDerivedCategory_obj_iff Ecat (EderivedOp.functor.obj X) n).1 hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨-n, (Functor.isLE_mapDerivedCategory_obj_iff Ecat (EderivedOp.functor.obj X) (-n)).2
        ((DerivedCategory.isLE_derivedOpEquivalence_functor_obj_iff
          (C := P.FullSubcategory) X.unop n).2 (by simpa using hn))⟩
  exact (ObjectProperty.opEquivalence PlusP).symm.trans
    (Equivalence.congrFullSubcategory E hprop)

/-- An object of the derived category is bounded below if and only if it is cohomologically
concentrated in degrees at least some integer `n`. -/
public lemma isBoundedBelow_iff_exists_isGE
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (X : DerivedCategory C) :
    DerivedCategoryB.IsBoundedBelow X ↔ ∃ n : ℤ, X.IsGE n := by
  constructor <;> rintro ⟨n, hn⟩
  · exact ⟨n, (DerivedCategory.isGE_iff X n).2 hn⟩
  · exact ⟨n, (DerivedCategory.isGE_iff X n).1 hn⟩

/-- The opposite of the full subcategory of the derived category of modules with bounded-below
cohomology supported in `T` is equivalent to the full subcategory of the derived category of the
opposite category with bounded-above cohomology in the opposite Serre class. -/
public noncomputable def supportedDerivedPlusOpEquivalence
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R)) :
    (DerivedCategoryB.derivedCategoryBPlus
      (supportModuleProperty.{u, v} R T)).FullSubcategoryᵒᵖ ≌
    (DerivedCategoryB.derivedCategoryBMinus
      (supportModuleProperty.{u, v} R T).op).FullSubcategory := by
  let C := ModuleCat.{v} R
  let P : ObjectProperty C := supportModuleProperty.{u, v} R T
  let PlusP : ObjectProperty (DerivedCategory C) := DerivedCategoryB.derivedCategoryBPlus P
  let MinusPop : ObjectProperty (DerivedCategory Cᵒᵖ) :=
    DerivedCategoryB.derivedCategoryBMinus P.op
  letI : P.IsSerreClass := supportModuleProperty_isSerreClass R T
  letI : P.op.IsSerreClass := supportProperty_op_isSerre T
  letI : P.op.IsWeakSerreClass := inferInstance
  have hWeak : WeakSerre.IsWeakSerre P.op :=
    ⟨inferInstance, P.op.exists_prop_of_isWeakSerreClass, fun E h₀ h₁ h₃ h₄ =>
      ObjectProperty.prop_mid_of_exact₄ P.op.prop_obj₂_of_exact
        E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄⟩
  letI : MinusPop.IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryBMinus_isClosedUnderIsomorphisms P.op hWeak
  let E : (DerivedCategory C)ᵒᵖ ≌ DerivedCategory Cᵒᵖ :=
    DerivedCategory.derivedOpEquivalence (C := C)
  have hprop : MinusPop.inverseImage E.functor = PlusP.op := by
    ext X
    change (DerivedCategoryB.IsBoundedAbove (E.functor.obj X) ∧
      DerivedCategoryB.derivedCategoryB P.op (E.functor.obj X)) ↔
      (DerivedCategoryB.IsBoundedBelow X.unop ∧
        DerivedCategoryB.derivedCategoryB P X.unop)
    rw [DerivedCategoryB.isBoundedAbove_iff_exists_isLE, isBoundedBelow_iff_exists_isGE]
    change ((∃ n : ℤ, (E.functor.obj X).IsLE n) ∧
      ∀ i : ℤ, P.op ((DerivedCategory.homologyFunctor Cᵒᵖ i).obj (E.functor.obj X))) ↔
      ((∃ n : ℤ, X.unop.IsGE n) ∧
      ∀ i : ℤ, P ((DerivedCategory.homologyFunctor C i).obj X.unop))
    refine and_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rintro ⟨n, hn⟩
      exact ⟨-n, (DerivedCategory.isLE_derivedOpEquivalence_functor_obj_iff
        X.unop (-n)).1 (by simpa using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨-n, (DerivedCategory.isLE_derivedOpEquivalence_functor_obj_iff
        X.unop n).2 (by simpa using hn)⟩
    · intro hP i
      simpa using ObjectProperty.prop_of_iso P.op
        (DerivedCategory.derivedHomologyOpObjIso (-i) i (by omega) X.unop) (hP (-i))
    · intro hP i
      exact ObjectProperty.prop_of_iso P.op
        (DerivedCategory.derivedHomologyOpObjIso i (-i) (by omega) X.unop).symm (hP (-i))
  exact (ObjectProperty.opEquivalence PlusP).symm.trans
    (Equivalence.congrFullSubcategory E hprop)

/-- For `T` stable under specialization over a Noetherian ring, the functor from the
bounded-above derived category of the opposite Serre subcategory to the derived category of the
opposite category of modules is fully faithful, with essential image the objects with
bounded-above cohomology in the opposite Serre class. -/
public lemma supportProperty_op_minusComparison
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (T : Set (PrimeSpectrum R)) (hT : StableUnderSpecialization T) :
    (DerivedCategory.Minus.ι (C :=
        (supportModuleProperty.{u, v} R T).op.FullSubcategory) ⋙
        (supportModuleProperty.{u, v} R T).op.ι.mapDerivedCategory).Full ∧
      (DerivedCategory.Minus.ι (C :=
        (supportModuleProperty.{u, v} R T).op.FullSubcategory) ⋙
        (supportModuleProperty.{u, v} R T).op.ι.mapDerivedCategory).Faithful ∧
      ∀ X : DerivedCategory ((ModuleCat.{v} R)ᵒᵖ),
        (DerivedCategory.Minus.ι (C :=
          (supportModuleProperty.{u, v} R T).op.FullSubcategory) ⋙
          (supportModuleProperty.{u, v} R T).op.ι.mapDerivedCategory).essImage X ↔
        ((∃ n : ℤ, X.IsLE n) ∧ ∀ i : ℤ,
          (supportModuleProperty.{u, v} R T).op
            ((DerivedCategory.homologyFunctor ((ModuleCat.{v} R)ᵒᵖ) i).obj X)) :=
  ObjectProperty.full_faithful_essImage_minus_mapDerivedCategory _
    (supportProperty_op_coversEpis T hT)

/-- For `T` stable under specialization over a Noetherian ring, the bounded-above derived
category of the opposite Serre subcategory is equivalent to the full subcategory of the derived
category of the opposite category with bounded-above cohomology in the opposite Serre class. -/
public noncomputable def supportedMinusComparisonEquivalence
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (T : Set (PrimeSpectrum R)) (hT : StableUnderSpecialization T) :
    DerivedCategory.Minus
        (supportModuleProperty.{u, v} R T).op.FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBMinus
        (supportModuleProperty.{u, v} R T).op).FullSubcategory := by
  let P : ObjectProperty (ModuleCat.{v} R) :=
    supportModuleProperty.{u, v} R T
  let Pop : ObjectProperty ((ModuleCat.{v} R)ᵒᵖ) := P.op
  let Bminus : ObjectProperty (DerivedCategory ((ModuleCat.{v} R)ᵒᵖ)) :=
    DerivedCategoryB.derivedCategoryBMinus Pop
  let G := DerivedCategory.Minus.ι (C := Pop.FullSubcategory) ⋙
    Pop.ι.mapDerivedCategory
  have hG := supportProperty_op_minusComparison T hT
  have hprop : ∀ X : DerivedCategory.Minus Pop.FullSubcategory, Bminus (G.obj X) := by
    intro X
    have hX := (hG.2.2 (G.obj X)).1 ⟨X, ⟨Iso.refl _⟩⟩
    exact ⟨(DerivedCategoryB.isBoundedAbove_iff_exists_isLE (G.obj X)).2 hX.1, hX.2⟩
  let L : DerivedCategory.Minus Pop.FullSubcategory ⥤ Bminus.FullSubcategory :=
    Bminus.lift G hprop
  letI : G.Full := hG.1
  letI : G.Faithful := hG.2.1
  letI : L.Full := ⟨fun f => by
    obtain ⟨g, hg⟩ := G.map_surjective f.hom
    exact ⟨g, Bminus.hom_ext hg⟩⟩
  letI : L.Faithful := ⟨fun h => G.map_injective (congrArg (·.hom) h)⟩
  letI : L.EssSurj := ⟨fun X => by
    obtain ⟨Y, ⟨e⟩⟩ := (hG.2.2 X.obj).2
      ⟨(DerivedCategoryB.isBoundedAbove_iff_exists_isLE X.obj).1 X.property.1, X.property.2⟩
    exact ⟨Y, ⟨Bminus.isoMk e⟩⟩⟩
  letI : L.IsEquivalence := {}
  exact L.asEquivalence

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃ w₄
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  preservesFiniteLimits_op preservesFiniteColimits_op

/-- The equivalence `Module.supportedPlusOpEquivalence` followed by the inclusion into the
derived category of the opposite category agrees with the opposite of the inclusion of the
bounded-below derived category of supported modules followed by the duality of derived
categories. -/
public def supportedComparisonOpIso
    {R : Type u} [CommRing R] (T : Set (PrimeSpectrum R)) :
    (supportedPlusOpEquivalence.{u, v} T).functor ⋙
        (DerivedCategory.Minus.ι ⋙
          (supportModuleProperty.{u, v} R T).op.ι.mapDerivedCategory) ≅
      (DerivedCategory.Plus.ι ⋙
        (supportModuleProperty.{u, v} R T).ι.mapDerivedCategory).op ⋙
          (DerivedCategory.derivedOpEquivalence (C := ModuleCat.{v} R)).functor := by
  let P : ObjectProperty (ModuleCat.{v} R) := supportModuleProperty R T
  let Ecat := (ObjectProperty.opEquivalence P).symm
  letI : Ecat.functor.Additive := ⟨rfl⟩
  change (DerivedCategory.Plus.ι (C := P.FullSubcategory)).op ⋙
      (DerivedCategory.derivedOpEquivalence (C := P.FullSubcategory)).functor ⋙
      Ecat.functor.mapDerivedCategory ⋙ P.op.ι.mapDerivedCategory ≅ _
  exact Functor.isoWhiskerLeft
    ((DerivedCategory.Plus.ι (C := P.FullSubcategory)).op ⋙
      (DerivedCategory.derivedOpEquivalence (C := P.FullSubcategory)).functor)
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      Ecat.functor P.op.ι).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.ι (C := P.FullSubcategory)).op
      (CategoryTheory.Functor.mapDerivedCategoryOpIso P.ι).symm

/-- **Stacks Project, Tag 0EF2.** For a specialization-closed subset `T` of the spectrum of a
Noetherian ring `A`, the canonical functor from the bounded-below derived category of modules
supported in `T` to the bounded-below derived category with cohomology supported in `T` is an
equivalence. -/
@[stacks 0EF2]
public theorem exists_supportedModulesDerivedPlusEquivalence
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (_hT : StableUnderSpecialization T) :
    ∃ (e : DerivedCategory.Plus (ModulesSupportedIn A T) ≌
        (DerivedCategoryB.derivedCategoryBPlus
          (supportModuleProperty A T)).FullSubcategory),
      Nonempty
        (e.functor ⋙
            (DerivedCategoryB.derivedCategoryBPlus
              (supportModuleProperty A T)).ι ≅
          DerivedCategory.Plus.ι ⋙
            (supportModuleProperty A T).ι.mapDerivedCategory) := by
  let P := supportModuleProperty A T
  let Bplus := DerivedCategoryB.derivedCategoryBPlus P
  let Bminus := DerivedCategoryB.derivedCategoryBMinus P.op
  let E₁ := supportedPlusOpEquivalence (R := A) T
  let E₂ := supportedMinusComparisonEquivalence (R := A) T _hT
  let E₃ := supportedDerivedPlusOpEquivalence (R := A) T
  let eop := E₁.trans (E₂.trans E₃.symm)
  refine ⟨eop.unop, ⟨?_⟩⟩
  let D := (DerivedCategory.derivedOpEquivalence (C := ModuleCat A)).functor
  have h : (eop.functor ⋙ Bplus.ι.op) ⋙ D ≅
      (DerivedCategory.Plus.ι ⋙ P.ι.mapDerivedCategory).op ⋙ D := by
    change E₁.functor ⋙ E₂.functor ⋙ E₃.inverse ⋙ E₃.functor ⋙ Bminus.ι ≅ _
    exact Functor.isoWhiskerLeft (E₁.functor ⋙ E₂.functor)
      (Functor.isoWhiskerRight E₃.counitIso Bminus.ι) ≪≫
      supportedComparisonOpIso T
  exact NatIso.unop (Functor.fullyFaithfulCancelRight D h).symm

end Module
