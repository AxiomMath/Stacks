module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationPushforward
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion

/-!
# The augmentation site functors of a simplicial site in the continuous case

In the continuous form of the simplicial-site situation an augmentation towards a site `(D, K)`
is a morphism of sites from the degree-zero site, represented by a continuous functor into that
site whose composites with the vertex functors of a simplicial degree all agree. Composing the
augmentation with the vertex functor of a degree therefore produces a continuous functor from the
augmentation site into the site of that degree which does not depend on the chosen vertex, and
those functors are strictly compatible with the simplicial diagram: the functor attached to a
degree composed with a transition functor is the functor attached to the target degree, as an
equality of functors. Each of them is again a morphism of sites, which is how the augmentation of
a simplicial degree arises in this case, and composing it with the inclusion of that degree into
the total category gives a continuous functor from the augmentation site into the total site whose
direct image is the direct image of the degree's augmentation applied to the restriction of a
sheaf to that degree.

## Main definitions

* `CategoryTheory.SimplicialSite.situation`: the simplicial-site situation of case (A) attached
  to a simplicial site.
* `CategoryTheory.SimplicialSite.componentInclusion`: the inclusion of the site in a simplicial
  degree into the total category.
* `CategoryTheory.SimplicialSite.ContinuousAugmentation.componentSiteFunctor`: the continuous
  functor from the augmentation site into the site of a simplicial degree, namely the
  augmentation followed by a vertex functor of that degree.
* `CategoryTheory.SimplicialSite.ContinuousAugmentation.componentMorphismOfSites`: the morphism
  of topoi it represents.
* `CategoryTheory.SimplicialSite.ContinuousAugmentation.totalComponentSiteFunctor`: that functor
  followed by the inclusion of the degree into the total category.

## Main results

* `CategoryTheory.SimplicialSite.ContinuousAugmentation.componentSiteFunctor_eq`: the functor
  attached to a degree is the augmentation followed by any vertex functor of that degree.
* `CategoryTheory.SimplicialSite.ContinuousAugmentation.componentSiteFunctor_comp_eq`: the
  functor attached to a degree followed by a transition functor is the functor attached to the
  target degree, as an equality of functors.
* `CategoryTheory.SimplicialSite.ContinuousAugmentation.componentSiteFunctor_isMorphismOfSites`:
  the functor attached to a degree is a morphism of sites.
* `CategoryTheory.SimplicialSite.ContinuousAugmentation.componentAugmentationPushforwardIso`: its
  direct image is the direct image of the augmentation of that simplicial degree.
* `CategoryTheory.SimplicialSite.ContinuousAugmentation.transitionCompPushforwardIso`: the direct
  image of a simplicial transition followed by the direct image of the augmentation of its source
  degree is the direct image of the augmentation of its target degree.
* `CategoryTheory.SimplicialSite.ContinuousAugmentation.componentRestrictionPushforwardIso`:
  restricting a sheaf on the total site to a simplicial degree and then taking its direct image
  along the augmentation of that degree is the direct image along the single continuous functor
  from the augmentation site into the total site attached to that degree.

## Implementation notes

The compatibility condition of a continuous augmentation is an equality of functors, not a
natural isomorphism, so the family of functors attached to the simplicial degrees is strictly
compatible with the simplicial diagram and the comparisons of their direct images are transports
along equalities of site functors rather than coherent isomorphisms. That is what makes the
composition comparisons below instances of Mathlib's
`CategoryTheory.Functor.sheafPushforwardContinuousComp` and `...Comp'` with no coherence of
their own.

The functor attached to a degree is defined using the constant vertex, so that it is syntactically
the site functor underlying the composite morphism of topoi which the situation attaches to that
degree; the comparison of the two direct images is then a composition comparison alone. A
continuous site functor enters the direct image only through a proof of the sheaf condition, so
two continuous structures on one functor give the same direct image and the comparisons do not
depend on which continuity proof is in scope.

The inclusion of a simplicial degree into the total category is the component inclusion of the
simplicial-site situation of case (A), named again here with the degree's site spelled as the
value of the simplicial object of categories rather than as a component of the situation. The
two spellings are definitionally equal, and naming the second one keeps every statement below in
a single spelling, which is what instance synthesis for continuity needs: it does not unfold the
definition of the component of a situation.

Composition of functors is written in diagrammatic order, so the equations displayed in the
source as `u_φ ∘ u_n` appear in the reverse textual order below.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe u

namespace CategoryTheory

namespace SimplicialSite

/-- The simplicial-site situation of case (A) attached to a simplicial site. -/
abbrev situation (C : SimplicialSite.{u}) : SimplicialSiteSituation.{u} :=
  ⟨Sum.inl C⟩

/-- A transition functor of a simplicial site is continuous for the topologies generated by the
covering families of its source and target degrees. -/
instance transitionFunctor_isContinuous {C : SimplicialSite.{u}} {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (C.underlying.map φ).toFunctor.IsContinuous (C.coverage m).toGrothendieck
      (C.coverage n).toGrothendieck :=
  (C.isMorphismOfSites φ).isContinuous

/-- The inclusion of the site in simplicial degree `n` of a simplicial site into its total
category: the inclusion of a fibre of the contravariant Grothendieck construction. -/
def componentInclusion (C : SimplicialSite.{u}) (n : SimplexCategory) :
    C.underlying.obj n ⥤ CoGrothendieck C.totalPseudofunctor :=
  SimplicialSiteSituation.componentFunctor C.situation n

/-- The inclusion of a simplicial degree into the total category is continuous. -/
instance componentInclusion_isContinuous (C : SimplicialSite.{u}) (n : SimplexCategory) :
    (C.componentInclusion n).IsContinuous (C.coverage n).toGrothendieck C.totalTopology :=
  SimplicialSiteSituation.componentFunctor_isContinuous C.situation n

namespace ContinuousAugmentation

variable {C : SimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  (a : C.ContinuousAugmentation D K)

/-- The functor underlying a continuous augmentation is continuous. -/
instance functor_isContinuous :
    a.functor.IsContinuous K (C.coverage (SimplexCategory.mk 0)).toGrothendieck :=
  a.isMorphismOfSites.isContinuous

/-- The functor from the augmentation site into the site in simplicial degree `n` attached to a
continuous augmentation: the augmentation followed by the constant vertex functor of that
degree. -/
def componentSiteFunctor (n : SimplexCategory) : D ⥤ C.underlying.obj n :=
  a.functor ⋙ (C.underlying.map (SimplexCategory.const (SimplexCategory.mk 0) n 0)).toFunctor

/-- The functor attached to a simplicial degree is the augmentation followed by the vertex functor
of any vertex of that degree: this is the compatibility condition of the augmentation. -/
theorem componentSiteFunctor_eq {n : SimplexCategory} (φ : SimplexCategory.mk 0 ⟶ n) :
    a.functor ⋙ (C.underlying.map φ).toFunctor = a.componentSiteFunctor n :=
  a.compatibility n φ (SimplexCategory.const (SimplexCategory.mk 0) n 0)

/-- In simplicial degree zero the functor attached to the degree is the augmentation itself. -/
theorem componentSiteFunctor_zero :
    a.componentSiteFunctor (SimplexCategory.mk 0) = a.functor := by
  rw [← a.componentSiteFunctor_eq (𝟙 (SimplexCategory.mk 0)), C.underlying.map_id]
  rfl

/-- The functors attached to the simplicial degrees are strictly compatible with the simplicial
diagram: the functor attached to the source of a simplex map followed by the corresponding
transition functor is the functor attached to its target. -/
theorem componentSiteFunctor_comp_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    a.componentSiteFunctor m ⋙ (C.underlying.map φ).toFunctor = a.componentSiteFunctor n := by
  dsimp only [componentSiteFunctor]
  rw [Functor.assoc, ← Cat.Hom.comp_toFunctor, ← C.underlying.map_comp]
  exact a.componentSiteFunctor_eq (SimplexCategory.const (SimplexCategory.mk 0) m 0 ≫ φ)

/-- The functor attached to a simplicial degree is a morphism of sites from the site of that
degree to the augmentation site, being a composite of two such. -/
theorem componentSiteFunctor_isMorphismOfSites (n : SimplexCategory) :
    (a.componentSiteFunctor n).IsMorphismOfSites K (C.coverage n).toGrothendieck :=
  a.isMorphismOfSites.comp
    (C.isMorphismOfSites (SimplexCategory.const (SimplexCategory.mk 0) n 0))

/-- The functor attached to a simplicial degree is continuous. -/
instance componentSiteFunctor_isContinuous (n : SimplexCategory) :
    (a.componentSiteFunctor n).IsContinuous K (C.coverage n).toGrothendieck :=
  (a.componentSiteFunctor_isMorphismOfSites n).isContinuous

/-- The morphism of topoi from the sheaves on the site in simplicial degree `n` to the sheaves on
the augmentation site represented by the functor attached to that degree. -/
def componentMorphismOfSites (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf (C.coverage n).toGrothendieck (Type u)) (Sheaf K (Type u)) :=
  (a.componentSiteFunctor_isMorphismOfSites n).morphismOfTopoi

/-- The direct image of the augmentation of a simplicial degree is the direct image along the
functor attached to that degree. -/
def componentAugmentationPushforwardIso (n : SimplexCategory) :
    (SimplicialSiteSituation.Augmentation.componentAugmentation C.situation D K a n).pushforward ≅
      (a.componentSiteFunctor n).sheafPushforwardContinuous (Type u) K
        (C.coverage n).toGrothendieck := by
  change Functor.sheafPushforwardContinuous
        (C.underlying.map (SimplexCategory.const (SimplexCategory.mk 0) n 0)).toFunctor (Type u)
          (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck ⋙
      a.functor.sheafPushforwardContinuous (Type u) K
        (C.coverage (SimplexCategory.mk 0)).toGrothendieck ≅ _
  exact Functor.sheafPushforwardContinuousComp a.functor
    (C.underlying.map (SimplexCategory.const (SimplexCategory.mk 0) n 0)).toFunctor (Type u) K
    (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck

/-- The direct image of a simplicial transition followed by the direct image along the functor
attached to its source degree is the direct image along the functor attached to its target
degree. -/
def transitionCompPushforwardIso {m n : SimplexCategory} (φ : m ⟶ n) :
    (C.underlying.map φ).toFunctor.sheafPushforwardContinuous (Type u)
          (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck ⋙
        (a.componentSiteFunctor m).sheafPushforwardContinuous (Type u) K
          (C.coverage m).toGrothendieck ≅
      (a.componentSiteFunctor n).sheafPushforwardContinuous (Type u) K
        (C.coverage n).toGrothendieck :=
  Functor.sheafPushforwardContinuousComp' (eqToIso (a.componentSiteFunctor_comp_eq φ)) (Type u) K
    (C.coverage m).toGrothendieck (C.coverage n).toGrothendieck

/-- The functor from the augmentation site into the total category attached to a simplicial
degree: the functor attached to that degree followed by the inclusion of the degree. -/
def totalComponentSiteFunctor (n : SimplexCategory) :
    D ⥤ CoGrothendieck C.totalPseudofunctor :=
  a.componentSiteFunctor n ⋙ C.componentInclusion n

/-- The functor from the augmentation site into the total category attached to a simplicial degree
is continuous. -/
instance totalComponentSiteFunctor_isContinuous (n : SimplexCategory) :
    (a.totalComponentSiteFunctor n).IsContinuous K C.totalTopology :=
  Functor.isContinuous_comp (a.componentSiteFunctor n) (C.componentInclusion n) K
    (C.coverage n).toGrothendieck C.totalTopology

/-- Restricting a sheaf on the total site to a simplicial degree and then taking its direct image
along the functor attached to that degree is the direct image along the single functor from the
augmentation site into the total category attached to that degree. -/
def componentRestrictionPushforwardIso (n : SimplexCategory) :
    (C.componentInclusion n).sheafPushforwardContinuous (Type u)
          (C.coverage n).toGrothendieck C.totalTopology ⋙
        (a.componentSiteFunctor n).sheafPushforwardContinuous (Type u) K
          (C.coverage n).toGrothendieck ≅
      (a.totalComponentSiteFunctor n).sheafPushforwardContinuous (Type u) K C.totalTopology :=
  Functor.sheafPushforwardContinuousComp (a.componentSiteFunctor n) (C.componentInclusion n)
    (Type u) K (C.coverage n).toGrothendieck C.totalTopology

end ContinuousAugmentation

end SimplicialSite

end CategoryTheory

end
