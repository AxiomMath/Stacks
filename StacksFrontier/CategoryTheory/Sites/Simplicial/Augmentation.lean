module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation

/-!
# Augmentations of a simplicial site

In the simplicial-site situation, an augmentation towards a site is a functor involving the
degree-zero site which is compatible with every vertex of every simplicial degree. In the
continuous case it is a morphism of sites, represented by a functor in the opposite direction;
in the cocontinuous case it induces a morphism of topoi directly.

## Main definitions

* `CategoryTheory.SimplicialSite.ContinuousAugmentation`: an augmentation in case (A).
* `CategoryTheory.CocontinuousSimplicialSite.Augmentation`: an augmentation in case (B).
* `CategoryTheory.SimplicialSiteSituation.Augmentation`: an augmentation of either kind
  towards a site.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.morphismOfTopoi`: its degree-zero
  morphism of topoi.

## Implementation notes

The two auxiliary structures record parts (A) and (B) respectively, and the augmentation type
selects the appropriate one from the two cases of the simplicial-site situation. In case (A),
the target site's covering families are recorded explicitly: continuity in the source's sense
requires preservation of these families and of pullbacks along their arrows, which is stronger
than preservation of sheaves by restriction.

Functor composition is written in diagrammatic order, so the equations displayed in the source
as `u_φ ∘ u_0` and `u_0 ∘ u_φ` appear in the reverse textual order below.

## References

* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- An augmentation in case (A): a morphism from the degree-zero site towards `(D, K)`,
represented by a continuous functor in the opposite direction, whose composites with all
vertex functors agree. -/
structure SimplicialSite.ContinuousAugmentation (C : SimplicialSite.{u}) (D : Cat.{u, u})
    (K : GrothendieckTopology D) where
  /-- The covering families of the target site. -/
  targetCoverage : Precoverage D
  /-- The target coverings include singleton isomorphisms. -/
  targetCoverage_hasIsos : targetCoverage.HasIsos
  /-- Pullbacks along target covering arrows exist. -/
  targetCoverage_hasPullbacks : targetCoverage.HasPullbacks
  /-- Target coverings are stable under base change. -/
  targetCoverage_isStableUnderBaseChange : targetCoverage.IsStableUnderBaseChange
  /-- Target coverings are stable under composition. -/
  targetCoverage_isStableUnderComposition : targetCoverage.IsStableUnderComposition
  /-- These covering families present the specified target topology. -/
  targetCoverage_toGrothendieck : targetCoverage.toGrothendieck = K
  /-- The functor in the direction opposite to the morphism of sites. -/
  functor : D ⥤ (C.underlying.obj (SimplexCategory.mk 0))
  /-- The functor represents a morphism of sites from the degree-zero site to `(D, K)`. -/
  isMorphismOfSites :
    functor.IsMorphismOfSites K (C.coverage (SimplexCategory.mk 0)).toGrothendieck
  /-- Covering families of the target site map to covering families of the degree-zero site. -/
  coverPreserving : targetCoverage ≤ (C.coverage (SimplexCategory.mk 0)).comap functor
  /-- Pullbacks along arrows in target covering families are preserved. -/
  preservesPullbacks : ∀ {V : D} {R : Presieve V}, R ∈ targetCoverage V →
    ∀ {W : D} {g : W ⟶ V}, R g → ∀ {T : D} (f : T ⟶ V),
      PreservesLimit (cospan f g) functor
  /-- Composing with the functor attached to a vertex is independent of the vertex. -/
  compatibility (n : SimplexCategory) (φ ψ : SimplexCategory.mk 0 ⟶ n) :
    functor ⋙ (C.underlying.map φ).toFunctor = functor ⋙ (C.underlying.map ψ).toFunctor

/-- An augmentation in case (B): a cocontinuous functor from the degree-zero site towards
`(D, K)` whose composites with all vertex functors agree. -/
structure CocontinuousSimplicialSite.Augmentation (C : CocontinuousSimplicialSite.{u})
    (D : Cat.{u, u}) (K : GrothendieckTopology D) where
  /-- The cocontinuous functor which induces the morphism of topoi. -/
  functor : (C.underlying.obj (Opposite.op (SimplexCategory.mk 0))) ⥤ D
  /-- The functor is cocontinuous for the degree-zero and target topologies. -/
  isCocontinuous : functor.IsCocontinuous
    (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K
  /-- Composing a vertex functor with the augmentation is independent of the vertex. -/
  compatibility (n : SimplexCategory) (φ ψ : SimplexCategory.mk 0 ⟶ n) :
    (C.underlying.map φ.op).toFunctor ⋙ functor =
      (C.underlying.map ψ.op).toFunctor ⋙ functor

namespace SimplicialSiteSituation

/-- **Stacks 0D6Z.** An augmentation of a simplicial site towards `(D, K)`. In case (A) it is
a morphism of sites represented by a continuous functor in the opposite direction; in case (B)
it is represented by a cocontinuous functor. In either case its composite with a vertex functor
is independent of the chosen vertex. -/
@[stacks 0D6Z]
def Augmentation (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u})
    (K : GrothendieckTopology D) : Type u :=
  match S.case with
  | Sum.inl C => C.ContinuousAugmentation D K
  | Sum.inr C => C.Augmentation D K

namespace Augmentation

/-- The morphism of topoi from the sheaves on the degree-zero site to the sheaves on the
augmentation site. -/
noncomputable def morphismOfTopoi (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u})
    (K : GrothendieckTopology D) (a : Augmentation S D K) :
    MorphismOfTopoi (Sheaf (S.componentTopology (SimplexCategory.mk 0)) (Type u))
      (Sheaf K (Type u)) := by
  rcases S with ⟨C | C⟩
  · change C.ContinuousAugmentation D K at a
    exact a.isMorphismOfSites.morphismOfTopoi
  · change C.Augmentation D K at a
    change MorphismOfTopoi
      (Sheaf (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0))))
        (Type u))
      (Sheaf K (Type u))
    letI : a.functor.IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op (SimplexCategory.mk 0)))) K :=
      a.isCocontinuous
    exact
      { pushforward := gStar _ _ _ _ a.functor
        inverseImage := gInv _ _ _ _ a.functor
        adj := gAdjunction _ _ _ _ a.functor
        preservesFiniteLimits := main_left_exact _ _ _ _ a.functor }

end Augmentation

end SimplicialSiteSituation

end CategoryTheory

end
