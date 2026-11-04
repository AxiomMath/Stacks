module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.LowerShriekExact
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallProjection
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction

/-!
# Injectives and K-injectives under pro-étale restriction

An injective abelian sheaf on the big pro-étale site over a scheme stays injective after inverse
image to the small pro-étale site of an object over it, and in particular after restriction to
the small pro-étale site of the scheme itself. The same holds for K-injective complexes of
abelian sheaves.

## Main results

* `injective_smallProetaleInverseImage`, `injective_smallProetaleRestriction`: injectivity is
  preserved by inverse image and by restriction.
* `isKInjective_smallProetaleInverseImage`, `isKInjective_smallProetaleRestriction`: the same for
  K-injective complexes.

## Implementation notes

For abelian sheaves the inverse image `i_f⁻¹` is the continuous pushforward along the small-to-big
site functor; the restriction along the inclusion of the small site is its value at the identity
of the scheme. The coefficient universe is independent of the scheme universe, and the
sheafification and Kan-extension instances supply the categorical constructions at that universe.

## References

* [Stacks Project, Tag 0F67](https://stacks.math.columbia.edu/tag/0F67)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.ProEtale

section InverseImage

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- Pushforward along the small-to-big site functor has an exact additive left adjoint. -/
private theorem exists_exact_additive_adjunction_sheafPushforward
    [HasSheafify (BigProetaleOver.topology B S.obj S.property) Ab.{w}]
    [∀ F : (SmallProetale B T.obj T.property)ᵒᵖ ⥤ Ab.{w},
      (smallProetaleToBigProetaleFunctor B T S f).op.HasPointwiseLeftKanExtension F] :
    ∃ (L : Sheaf (SmallProetale.topology B T.obj T.property) Ab.{w} ⥤
        Sheaf (BigProetaleOver.topology B S.obj S.property) Ab.{w})
      (_ : L ⊣ (smallProetaleToBigProetaleFunctor B T S f).sheafPushforwardContinuous Ab.{w}
        (SmallProetale.topology B T.obj T.property)
        (BigProetaleOver.topology B S.obj S.property)),
      PreservesFiniteLimits L ∧ PreservesFiniteColimits L ∧ L.Additive ∧
      ((smallProetaleToBigProetaleFunctor B T S f).sheafPushforwardContinuous Ab.{w}
        (SmallProetale.topology B T.obj T.property)
        (BigProetaleOver.topology B S.obj S.property)).Additive := by
  let F := smallProetaleToBigProetaleFunctor B T S f
  let J := SmallProetale.topology B T.obj T.property
  let K := BigProetaleOver.topology B S.obj S.property
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F Ab.{w} J K
  have h := (exactFunctor_iff (Functor.sheafPullbackConstruction.sheafPullback F Ab.{w} J K)).mp
    (smallProetaleToBigProetaleLowerShriek_exact B T S f)
  let : (F.sheafPushforwardContinuous Ab.{w} J K).Additive := ⟨fun {_ _ _ _} ↦ by ext; rfl⟩
  exact ⟨_, adj, h.1, h.2, adj.left_adjoint_additive, inferInstance⟩

variable [HasSheafify (SmallProetale.topology B T.obj T.property) Ab.{w}]
  [HasSheafify (BigProetaleOver.topology B S.obj S.property) Ab.{w}]
  [∀ F : (SmallProetale B T.obj T.property)ᵒᵖ ⥤ Ab.{w},
    (smallProetaleToBigProetaleFunctor B T S f).op.HasPointwiseLeftKanExtension F]

/-- Inverse image to the small pro-étale site of `T` preserves injective
abelian sheaves on the big pro-étale site over `S`. -/
@[stacks 0F67 "injective_pullback_t"]
public lemma injective_smallProetaleInverseImage
    (I : Sheaf (BigProetaleOver.topology B S.obj S.property) Ab.{w})
    [Injective I] :
    Injective (((smallProetaleToBigProetaleFunctor B T S f).sheafPushforwardContinuous
      Ab.{w}
      (SmallProetale.topology B T.obj T.property)
      (BigProetaleOver.topology B S.obj S.property)).obj I) := by
  obtain ⟨L, adj, h₁, h₂, _, _⟩ := exists_exact_additive_adjunction_sheafPushforward B T S f
  exact ((preservesInjectiveObjects_of_exact_of_adjunction _ L adj).2 ⟨h₁, h₂⟩).injective_obj
    inferInstance

end InverseImage

section Restriction

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable [HasSheafify (SmallProetale.topology B S hS) Ab.{w}]
  [HasSheafify (BigProetaleOver.topology B S hS) Ab.{w}]
  [∀ F : (SmallProetale B S hS)ᵒᵖ ⥤ Ab.{w},
    (smallProetaleToBigProetaleFunctor B
      (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
      (𝟙 (⟨S, hS⟩ : B.Scheme))).op.HasPointwiseLeftKanExtension F]

/-- Restricting an injective abelian sheaf from the big pro-étale site over `S`
to the small pro-étale site of `S` preserves injectivity. -/
@[stacks 0F67 "injective_restriction_s"]
public lemma injective_smallProetaleRestriction
    (I : Sheaf (BigProetaleOver.topology B S hS) Ab.{w})
    [Injective I] :
    Injective (((SmallProetale.inclusion B S hS).sheafPushforwardContinuous
      Ab.{w}
      (SmallProetale.topology B S hS)
      (BigProetaleOver.topology B S hS)).obj I) := by
  simpa [smallProetaleToBigProetaleFunctor, Over.mapId_eq, Functor.comp_id] using
    injective_smallProetaleInverseImage B (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
      (𝟙 (⟨S, hS⟩ : B.Scheme)) I

end Restriction

section KInjective

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

variable [HasSheafify (SmallProetale.topology B T.obj T.property) AddCommGrpCat.{w}]
  [HasSheafify (BigProetaleOver.topology B S.obj S.property) AddCommGrpCat.{w}]
  [∀ F : (SmallProetale B T.obj T.property)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (smallProetaleToBigProetaleFunctor B T S f).op.HasPointwiseLeftKanExtension F]

/-- The inverse image of a K-injective complex of abelian sheaves from the big
pro-étale site over `S` to the small pro-étale site of `T` is K-injective. -/
@[stacks 0F67 "kinjective_pullback_t"]
public lemma isKInjective_smallProetaleInverseImage
    (I : CochainComplex
      (Sheaf (BigProetaleOver.topology B S.obj S.property) AddCommGrpCat.{w}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((smallProetaleToBigProetaleFunctor B T S f).sheafPushforwardContinuous
        AddCommGrpCat.{w}
        (SmallProetale.topology B T.obj T.property)
        (BigProetaleOver.topology B S.obj S.property)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) := by
  obtain ⟨v, adj, h₁, h₂, _, _⟩ := exists_exact_additive_adjunction_sheafPushforward B T S f
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ v adj I

end KInjective

section KInjectiveRestriction

variable (B : BigProetaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restricting a K-injective complex from the big pro-étale site over `S`
to the small pro-étale site of `S` preserves K-injectivity. -/
@[stacks 0F67 "kinjective_restriction_s"]
public lemma isKInjective_smallProetaleRestriction
    (I : CochainComplex
      (Sheaf (BigProetaleOver.topology B S hS) AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((SmallProetale.inclusion B S hS).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallProetale.topology B S hS)
        (BigProetaleOver.topology B S hS)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) := by
  simpa [smallProetaleToBigProetaleFunctor, Over.mapId_eq, Functor.comp_id] using
    isKInjective_smallProetaleInverseImage B (⟨S, hS⟩ : B.Scheme) (⟨S, hS⟩ : B.Scheme)
      (𝟙 (⟨S, hS⟩ : B.Scheme)) I

end KInjectiveRestriction

end AlgebraicGeometry.ProEtale

end
