module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.RestrictionCoherence
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.KInjectiveRestrictionAlongOverMap
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization

/-!
# Derived objects on a slice of a slice

Let `(C, O_C)` be a ringed site and `X` an object of `C`; write `C/X` for the localized ringed
site. An object `V ⟶ X` of `C/X` has two slices, the slice `C/V` of `C` and the slice
`(C/X)/(V ⟶ X)` of `C/X`, and the two are identified by the iterated slice equivalence. This file
transports derived objects of modules from the first to the second, and shows that the transport
commutes with restriction along arrows of `C/X`, coherently with the comparisons of restriction
along a composite.

On sheaves of modules the transport is the pushforward along
`CategoryTheory.Over.iteratedSliceForward`, and it commutes with restriction on the nose.

## Main definitions

* `AlgebraicGeometry.RingedSite.iteratedSliceTransport`: the transport of sheaves of modules
  from `C/V` to `(C/X)/V`, an equivalence.
* `AlgebraicGeometry.RingedSite.derivedIteratedSliceTransport`: the same on derived categories, an
  equivalence.
* `AlgebraicGeometry.RingedSite.derivedIteratedSliceTransportOverMapIso`: the transport commutes
  with restriction along an arrow `W ⟶ V` of `C/X`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedIteratedSliceTransportOverMapIso_comp`: the commutation is
  compatible with the comparisons of restriction along a composite, on `C` and on `C/X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) (X₀ : X.C)

/-- **Transport of sheaves of modules from the slice `C/V` to the iterated slice `(C/X)/V`**, for
an object `V` of `C/X`: the pushforward along `CategoryTheory.Over.iteratedSliceForward`. -/
abbrev iteratedSliceTransport (V : Over X₀) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V.left) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over X₀).O).over V) :=
  (Stacks.Cohomology.Localization.iteratedSliceModulesEquivalence X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V.hom).functor

/-- The transport of sheaves of modules is additive. -/
instance iteratedSliceTransport_additive (V : Over X₀) : (X.iteratedSliceTransport X₀ V).Additive :=
  ⟨by intros; ext; rfl⟩

/-- The transport of sheaves of modules is an equivalence. -/
instance iteratedSliceTransport_isEquivalence (V : Over X₀) :
    (X.iteratedSliceTransport X₀ V).IsEquivalence :=
  (Stacks.Cohomology.Localization.iteratedSliceModulesEquivalence X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V.hom).isEquivalence_functor

/-- The transport of sheaves of modules preserves finite limits. -/
instance iteratedSliceTransport_preservesFiniteLimits (V : Over X₀) :
    PreservesFiniteLimits (X.iteratedSliceTransport X₀ V) :=
  inferInstance

/-- The transport of sheaves of modules preserves finite colimits. -/
instance iteratedSliceTransport_preservesFiniteColimits (V : Over X₀) :
    PreservesFiniteColimits (X.iteratedSliceTransport X₀ V) :=
  inferInstance

/-- **Transport of derived objects from the slice `C/V` to the iterated slice `(C/X)/V`.** -/
abbrev derivedIteratedSliceTransport (V : Over X₀) :
    LocalDerivedCategory.{0} X V.left ⥤ LocalDerivedCategory.{0} (X.over X₀) V :=
  (X.iteratedSliceTransport X₀ V).mapDerivedCategory

/-- The transport of derived objects is an equivalence. -/
instance derivedIteratedSliceTransport_isEquivalence (V : Over X₀) :
    (X.derivedIteratedSliceTransport X₀ V).IsEquivalence :=
  Stacks.Injectives.mapDerivedCategory_isEquivalence _

/-- The transport of derived objects is induced by the transport of complexes. -/
abbrev derivedIteratedSliceTransportFactors (V : Over X₀) :
    DerivedCategory.Q ⋙ X.derivedIteratedSliceTransport X₀ V ≅
      (X.iteratedSliceTransport X₀ V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  (X.iteratedSliceTransport X₀ V).mapDerivedCategoryFactors

/-- The transport of sheaves of modules commutes with restriction, on the nose. -/
theorem iteratedSliceTransport_comp_overMapModules {V W : Over X₀} (g : W ⟶ V) :
    X.iteratedSliceTransport X₀ V ⋙ (X.over X₀).overMapModules g =
      X.overMapModules g.left ⋙ X.iteratedSliceTransport X₀ W :=
  rfl

/-- The transport of sheaves of modules commutes with restriction: the identity. -/
def iteratedSliceTransportOverMapIso {V W : Over X₀} (g : W ⟶ V) :
    X.iteratedSliceTransport X₀ V ⋙ (X.over X₀).overMapModules g ≅
      X.overMapModules g.left ⋙ X.iteratedSliceTransport X₀ W :=
  Iso.refl _

/-- The transport of complexes commutes with restriction. -/
def iteratedSliceTransportOverMapComplexIso {V W : Over X₀} (g : W ⟶ V) :
    (X.iteratedSliceTransport X₀ V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((X.over X₀).overMapModules g).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (X.overMapModules g.left).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (X.iteratedSliceTransport X₀ W).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (X.iteratedSliceTransportOverMapIso X₀ g)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- Each component of the commutation of the transport of complexes with restriction fixes
sections. -/
theorem iteratedSliceTransportOverMapComplexIso_hom_app_f_fixesSections {V W : Over X₀} (g : W ⟶ V)
    (K : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over
      V.left)) ℤ) (p : ℤ) :
    SheafOfModules.FixesSections
      (((X.iteratedSliceTransportOverMapComplexIso X₀ g).hom.app K).f p) :=
  fun _ _ => HEq.rfl

/-- **The transport of derived objects commutes with restriction** along an arrow `W ⟶ V` of
`C/X`. -/
def derivedIteratedSliceTransportOverMapIso {V W : Over X₀} (g : W ⟶ V) :
    X.derivedIteratedSliceTransport X₀ V ⋙ derivedOverMap.{0} (X.over X₀) g ≅
      derivedOverMap.{0} X g.left ⋙ X.derivedIteratedSliceTransport X₀ W :=
  NatIso.liftAlong (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (Functor.compFactorization (X.derivedIteratedSliceTransportFactors X₀ V)
      ((X.over X₀).derivedOverMapFactors g))
    (Functor.compFactorization (X.derivedOverMapFactors g.left)
      (X.derivedIteratedSliceTransportFactors X₀ W))
    (X.iteratedSliceTransportOverMapComplexIso X₀ g)

/-- The commutation of the transport of derived objects with restriction is induced by the
commutation of the transport of complexes with restriction. -/
theorem derivedIteratedSliceTransportOverMapIso_hom_isInducedBy {V W : Over X₀} (g : W ⟶ V) :
    NatTrans.IsInducedBy
      (Functor.compFactorization (X.derivedIteratedSliceTransportFactors X₀ V)
        ((X.over X₀).derivedOverMapFactors g))
      (Functor.compFactorization (X.derivedOverMapFactors g.left)
        (X.derivedIteratedSliceTransportFactors X₀ W))
      (X.derivedIteratedSliceTransportOverMapIso X₀ g).hom
      (X.iteratedSliceTransportOverMapComplexIso X₀ g).hom :=
  NatTrans.isInducedBy_liftAlong _ _ _ _

/-- If a morphism of sheaves of modules fixes sections, then so does its transport. -/
theorem iteratedSliceTransport_map_fixesSections (V : Over X₀)
    {A B : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V.left)}
    {φ : A ⟶ B} (hφ : SheafOfModules.FixesSections φ) :
    SheafOfModules.FixesSections ((X.iteratedSliceTransport X₀ V).map φ) :=
  fun _ x => hφ _ x

macro_rules
  | `(tactic| fixes_sections_atom) =>
    `(tactic| with_reducible apply
      AlgebraicGeometry.RingedSite.iteratedSliceTransport_map_fixesSections)
macro_rules
  | `(tactic| fixes_sections_atom) =>
    `(tactic| with_reducible apply
      AlgebraicGeometry.RingedSite.iteratedSliceTransportOverMapComplexIso_hom_app_f_fixesSections)

/-- **The commutation of the transport with restriction is compatible with the comparisons of
restriction along a composite**, for arrows `k : Z ⟶ W` and `g : W ⟶ V` of `C/X`. -/
theorem derivedIteratedSliceTransportOverMapIso_comp {V W Z : Over X₀} (g : W ⟶ V) (k : Z ⟶ W)
    (A : LocalDerivedCategory.{0} X V.left) :
    (derivedOverMapComp.{0} (X.over X₀) (rfl : k ≫ g = k ≫ g)).hom.app
          ((X.derivedIteratedSliceTransport X₀ V).obj A) ≫
        (derivedOverMap.{0} (X.over X₀) k).map
          ((X.derivedIteratedSliceTransportOverMapIso X₀ g).hom.app A) ≫
        (X.derivedIteratedSliceTransportOverMapIso X₀ k).hom.app
          ((derivedOverMap.{0} X g.left).obj A) =
      (X.derivedIteratedSliceTransportOverMapIso X₀ (k ≫ g)).hom.app A ≫
        (X.derivedIteratedSliceTransport X₀ Z).map
          ((derivedOverMapComp.{0} X (Over.comp_left _ _ _ k g).symm).hom.app A) := by
  have hL := ((((NatTrans.IsInducedBy.whiskerLeft (X.derivedIteratedSliceTransportFactors X₀ V)
      ((X.over X₀).derivedOverMapComp_hom_isInducedBy (rfl : k ≫ g = k ≫ g))).comp
    (NatTrans.IsInducedBy.associator_inv _ _ _)).comp
    ((X.derivedIteratedSliceTransportOverMapIso_hom_isInducedBy X₀ g).whiskerRight
      ((X.over X₀).derivedOverMapFactors k))).comp
    (NatTrans.IsInducedBy.associator _ _ _)).comp
    ((NatTrans.IsInducedBy.whiskerLeft (X.derivedOverMapFactors g.left)
      (X.derivedIteratedSliceTransportOverMapIso_hom_isInducedBy X₀ k)).comp
      (NatTrans.IsInducedBy.associator_inv _ _ _))
  have hR := (X.derivedIteratedSliceTransportOverMapIso_hom_isInducedBy X₀ (k ≫ g)).comp
    ((X.derivedOverMapComp_hom_isInducedBy (Over.comp_left _ _ _ k g).symm).whiskerRight
      (X.derivedIteratedSliceTransportFactors X₀ Z))
  have := NatTrans.congr_app (isInducedBy_ext_of_fixesSections hL hR ?_ ?_) A
  · simpa using this
  all_goals
    intro K p
    simp_fixesSections
    fixes_sections

end AlgebraicGeometry.RingedSite

end
