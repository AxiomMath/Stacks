module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrict
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.RepresentableSheaves
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalSite

/-!
# The spaces-étale site of a simplicial algebraic space as a simplicial site

Let `X` be a simplicial algebraic space. The strict components `StrictComponent X n` of
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictComponent` are equivalent to the
spaces-étale sites `(X_n)_{spaces,étale}`; they carry the topology induced along the
realization, for which the realization is an equivalence of sites. The transition functors
`u_φ` realize to base change along `X(φ)`, which is a morphism of sites (Stacks 03G2), so the
strict components form a simplicial site in the sense of Stacks 09WC, case (A) of the
simplicial-site situation of Stacks 09WE.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictTopology`: the topology of a strict
  component, induced along the realization.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictSimplicialSite`: the simplicial site
  `[n] ↦ (X_n)_{spaces,étale}` with transitions `u_φ`.

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictRealize_isDenseSubsite`: the
  realization is a dense subsite, hence an equivalence of sites.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictTransition_isMorphismOfSites`: every
  transition functor is a morphism of sites.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- The topology of the strict degree-`n` component: the topology induced along the realization
from the spaces-étale topology of `X_n`. -/
def strictTopology (n : SimplexCategory) : GrothendieckTopology (StrictComponent X n) :=
  (strictRealize X n).inducedTopology (SpacesEtale.topology B S hS (X.obj (op n)))

/-- The inverse of the realization `(X_n)_{spaces,étale} ⥤ StrictComponent X n` is a dense
subsite. -/
instance strictRealize_inverse_isDenseSubsite (n : SimplexCategory) :
    (strictRealize X n).asEquivalence.inverse.IsDenseSubsite
      (SpacesEtale.topology B S hS (X.obj (op n))) (strictTopology X n) :=
  inferInstanceAs ((strictRealize X n).asEquivalence.symm.functor.IsDenseSubsite _
    ((strictRealize X n).asEquivalence.symm.inverse.inducedTopology _))

/-- **The realization of a strict component is a dense subsite**: a sieve covers exactly when
its image in `(X_n)_{spaces,étale}` does, so the realization is an equivalence of sites. -/
instance strictRealize_isDenseSubsite (n : SimplexCategory) :
    (strictRealize X n).IsDenseSubsite (strictTopology X n)
      (SpacesEtale.topology B S hS (X.obj (op n))) :=
  inferInstanceAs ((strictRealize X n).asEquivalence.functor.IsDenseSubsite _ _)

/-- A strict component has pullbacks. -/
instance (n : SimplexCategory) : HasPullbacks (StrictComponent X n) :=
  Adjunction.hasLimitsOfShape_of_equivalence (strictRealize X n)

/-- A strict component has finite limits. -/
instance (n : SimplexCategory) : HasFiniteLimits (StrictComponent X n) := by
  have : HasFiniteLimits (SpacesEtale B S hS (X.obj (op n))) :=
    haveI := (SpacesEtale.isTerminal_idObj B S hS (X.obj (op n))).hasTerminal
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  exact ⟨fun J _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence (strictRealize X n)⟩

/-- The transition functor `u_φ` is base change along `X(φ)` conjugated by the realizations. -/
def strictTransitionIso {m n : SimplexCategory} (φ : m ⟶ n) :
    strictTransition X φ ≅ strictRealize X m ⋙ (spacesBaseChange B S hS (X.map φ.op)).functor ⋙
      (strictRealize X n).asEquivalence.inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (strictRealize X n).asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (strictTransitionRealizeIso X φ) _ ≪≫ Functor.associator _ _ _

/-- A transition functor `u_φ` preserves finite limits. -/
instance strictTransition_preservesFiniteLimits {m n : SimplexCategory} (φ : m ⟶ n) :
    PreservesFiniteLimits (strictTransition X φ) :=
  preservesFiniteLimits_of_natIso (strictTransitionIso X φ).symm

/-- A transition functor `u_φ` is continuous for the strict topologies. -/
instance strictTransition_isContinuous {m n : SimplexCategory} (φ : m ⟶ n) :
    (strictTransition X φ).IsContinuous (strictTopology X m) (strictTopology X n) :=
  haveI := Functor.isContinuous_comp (spacesBaseChange B S hS (X.map φ.op)).functor
    (strictRealize X n).asEquivalence.inverse (SpacesEtale.topology B S hS (X.obj (op m)))
    (SpacesEtale.topology B S hS (X.obj (op n))) (strictTopology X n)
  haveI := Functor.isContinuous_comp (strictRealize X m)
    ((spacesBaseChange B S hS (X.map φ.op)).functor ⋙ (strictRealize X n).asEquivalence.inverse)
    (strictTopology X m) (SpacesEtale.topology B S hS (X.obj (op m))) (strictTopology X n)
  Functor.isContinuous_of_iso (strictTransitionIso X φ).symm _ _

/-- **Every transition functor `u_φ` of the strict components is a morphism of sites**: it is
continuous and left exact, and its source has finite limits. -/
theorem strictTransition_isMorphismOfSites {m n : SimplexCategory} (φ : m ⟶ n) :
    (strictTransition X φ).IsMorphismOfSites (strictTopology X m) (strictTopology X n) :=
  Functor.isMorphismOfSites_of_preservesFiniteLimits _ _ _

/-- A transition functor `u_φ` carries covering presieves to covering presieves. -/
theorem strictTransition_coverPreserving {m n : SimplexCategory} (φ : m ⟶ n) :
    (strictTopology X m).toPrecoverage ≤
      (strictTopology X n).toPrecoverage.comap (strictTransition X φ) := by
  intro U R hR
  rw [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff,
    Sieve.generate_map_eq_functorPushforward]
  exact (CoverPreserving.of_isContinuous (strictTransition X φ) (strictTopology X m)
    (strictTopology X n)).cover_preserve hR

/-- The topology of a strict component is generated by its own covering presieves. -/
theorem strictTopology_toPrecoverage_toGrothendieck (n : SimplexCategory) :
    (strictTopology X n).toPrecoverage.toGrothendieck = strictTopology X n :=
  le_antisymm (GrothendieckTopology.toGrothendieck_toPrecoverage_le _)
    (Stacks.Sites.le_toGrothendieck_toPrecoverage _)

/-- **The spaces-étale site of a simplicial algebraic space, as a simplicial site** (Stacks 09WC,
case (A) of Stacks 09WE): the strict components `[n] ↦ (X_n)_{spaces,étale}` with the covering
presieves of their topologies, and the transition functors `u_φ`, base change along `X(φ)`. -/
def strictSimplicialSite : SimplicialSite.{u + 1} where
  underlying := strictCosimplicial X
  coverage n := (strictTopology X n).toPrecoverage
  coverage_hasIsos n := inferInstanceAs (strictTopology X n).toPrecoverage.HasIsos
  coverage_hasPullbacks n := inferInstanceAs (strictTopology X n).toPrecoverage.HasPullbacks
  coverage_isStableUnderBaseChange n :=
    inferInstanceAs (strictTopology X n).toPrecoverage.IsStableUnderBaseChange
  coverage_isStableUnderComposition n :=
    inferInstanceAs (strictTopology X n).toPrecoverage.IsStableUnderComposition
  isMorphismOfSites φ := by
    change (strictTransition X φ).IsMorphismOfSites
      (strictTopology X _).toPrecoverage.toGrothendieck
      (strictTopology X _).toPrecoverage.toGrothendieck
    rw [strictTopology_toPrecoverage_toGrothendieck, strictTopology_toPrecoverage_toGrothendieck]
    exact strictTransition_isMorphismOfSites X φ
  coverPreserving φ := strictTransition_coverPreserving X φ
  preservesPullbacks φ _ _ _ _ _ _ _ f :=
    PreservesLimitsOfShape.preservesLimit (F := strictTransition X φ)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
