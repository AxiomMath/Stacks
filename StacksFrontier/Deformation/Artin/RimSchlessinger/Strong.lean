module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks

/-!
# The Rim–Schlessinger condition (RS*)

A category fibred in groupoids over the big fppf site of a scheme satisfies the
Rim–Schlessinger condition (RS*) when, for every fibre-product square of `S`-algebras in
the big affine fppf site in which one map is a surjection with square-zero kernel,
restriction from the fibre over the pullback algebra to the two-fibre product of the
fibres over the other three corners is an equivalence of categories.

## Main definitions

* `Deformation.Artin.fiberSquareComparison` — the canonical comparison from the fibre over
  the fourth corner of a commutative square to the two-fibre product of the fibres over
  the other three corners.
* `Deformation.Artin.SatisfiesRSStar` — condition (RS*).

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation.Artin

/-- The map on global sections induced by the spectrum of a surjection of rings is again
surjective. -/
public theorem specMap_appTop_surjective {R T : CommRingCat.{u}} (f : R ⟶ T)
    (hf : Function.Surjective f.hom) :
    Function.Surjective (Spec.map f).appTop.hom := by
  have hR := (ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso R).hom).mp inferInstance
  have hT := (ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso T).hom).mp inferInstance
  intro a
  obtain ⟨b, hb⟩ := hf ((Scheme.ΓSpecIso T).hom.hom a)
  obtain ⟨d, hd⟩ := hR.2 b
  refine ⟨d, hT.1 ?_⟩
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality f) d
  change (Scheme.ΓSpecIso T).hom.hom ((Spec.map f).appTop.hom d) =
    f.hom ((Scheme.ΓSpecIso R).hom.hom d) at h
  simpa only [hd, hb] using h

/-- The canonical comparison from the fibre over the fourth corner of a commutative
square to the two-fibre product of the fibres over the other three corners. -/
@[implicit_reducible] public noncomputable def fiberSquareComparison
    {C : Type u} [Category.{v} C] {X : Type w} [Category X]
    (p : X ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) :
    p.Fiber Z ⥤
      CategoricalPullback (c.pullbackFunctor f) (c.pullbackFunctor g) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (c.pullbackFunctor f) (c.pullbackFunctor g) (p.Fiber Z)).obj
      { fst := c.pullbackFunctor i
        snd := c.pullbackFunctor j
        iso := (c.pullbackFunctorCompIso f i).symm ≪≫
          eqToIso (congrArg c.pullbackFunctor h) ≪≫
          c.pullbackFunctorCompIso g j }

/-- Condition (RS*): for every fibre-product square of `S`-algebras in the big affine fppf
site, with one map surjective with square-zero kernel, the canonical functor from the fibre
over the pullback algebra to the two-fibre product of the other three fibres is an
equivalence. -/
@[stacks 07Y8]
public abbrev SatisfiesRSStar
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type w} [Category X]
    (p : X ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) : Prop :=
  letI : p.IsFibered := hp.isFibered
  let C := BigAffineFppf B S hS
  let ι := BigAffineFppf.inclusion B S hS
  let T := BigAffineFppf.toScheme B S hS
  ∀ (U V W Z : C) (f : U ⟶ V) (g : U ⟶ W)
      (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j),
    IsPullback (T.map i).appTop (T.map j).appTop
      (T.map f).appTop (T.map g).appTop →
    Function.Surjective ((T.map g).appTop.hom) →
      (RingHom.ker ((T.map g).appTop.hom)) ^ 2 = ⊥ →
        (fiberSquareComparison p (Functor.chosenPullbacks p)
          (ι.map f) (ι.map g) (ι.map i) (ι.map j)
          (by simpa only [Functor.map_comp] using congrArg ι.map h)).IsEquivalence

end Deformation.Artin
