module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.FiberedCategory.ProductProjection
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedSite
import StacksCore.Tactic.StacksAttribute

/-!
# The inherited topology satisfies the covering-pullback clause of Stacks continuity

Let `p : 𝒳 ⥤ 𝒮` be a fibred category over a site `(𝒮, J)` whose underlying category has fibre
products, and give `𝒳` the topology it inherits from `J` (Stacks 06NV). Then `p` satisfies
clause (2) of the Stacks definition of a continuous functor of sites, Sites Definition 00WV:
every covering sieve of `𝒳` contains a covering family whose members admit pullbacks along
arbitrary morphisms, and `p` preserves those pullbacks.

This is what the Čech computation behind Stacks 0D6X consumes, through
`Stacks.Sites.PreservesCoveringPullbacks`. Mathlib's `CategoryTheory.Functor.IsContinuous` is
the sheaf-theoretic clause only and does not include it, which is why it has to be supplied.

## Main definitions

* `CategoryTheory.Functor.cartesianArrows`: the strongly cartesian morphisms belonging to a
  sieve.

## Main results

* `CategoryTheory.Functor.generate_cartesianArrows_mem_inheritedTopology`: the sieve generated
  by the strongly cartesian morphisms of a covering sieve is again covering. Equivalently, the
  strongly cartesian morphisms of a covering sieve are cofinal in it.
* `CategoryTheory.Functor.isContinuous_inheritedTopology` and
  `CategoryTheory.Functor.isCocontinuous_inheritedTopology`: **Stacks 06NW**, the structure
  functor is continuous and cocontinuous for the inherited topology.
* `CategoryTheory.Functor.preservesCoveringPullbacks_inheritedTopology`: consequently the
  inherited topology satisfies the covering-pullback clause. Instance search applies it to the
  projection `D × C ⥤ C` of a product category, which is fibred by
  `CategoryTheory.Prod.snd_isFibered`; at `D = Δ` this is the projection `π : Δ × C ⥤ C` of
  Stacks 09D0, the case the simplicial development needs.

## Implementation notes

The cofinality statement is proved by induction over `CategoryTheory.Precoverage.Saturate`,
since the inherited topology is `CategoryTheory.Precoverage.toGrothendieck` of the inherited
collection of covering families and `CategoryTheory.Precoverage.mem_toGrothendieck_iff` lands
there. Taking the refinement to be *all* the strongly cartesian morphisms of the sieve, rather
than a family produced along the way, is what makes the four cases cheap: the refinement is
then a function of the sieve alone, so no presieve has to be transported, and each case is a
containment between two sieves.

* `of`: a covering family of the inherited collection consists of strongly cartesian morphisms,
  so it is contained in the refinement of the sieve it generates.
* `top`: the identity is strongly cartesian and lies in every sieve.
* `pullback`: the base change of a strongly cartesian morphism along an arbitrary morphism
  exists (Stacks 06N5, `CategoryTheory.Functor.IsFibered.hasPullback_of_isStronglyCartesian`)
  and is again strongly cartesian
  (`CategoryTheory.Functor.isStronglyCartesian_of_isPullback`), and a morphism factoring
  through the original factors through the base change.
* `transitive`: a composite of strongly cartesian morphisms is strongly cartesian
  (Stacks 02XL), so the refinement of a pullback sieve pushes forward into the pullback of the
  refinement.

Preservation of the pullbacks is Stacks 06N5 again, in the form
`CategoryTheory.Functor.IsFibered.map_isPullback_of_isStronglyCartesian`: it says that the
comparison morphism `p(x ×_z y) ⟶ p x ×_{p z} p y` is invertible, which is the hypothesis of
`CategoryTheory.Limits.PreservesPullback.of_iso_comparison`.

## References

* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
* [Stacks Project, Tag 06NU](https://stacks.math.columbia.edu/tag/06NU)
* [Stacks Project, Tag 06N5](https://stacks.math.columbia.edu/tag/06N5)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  (p : 𝒳 ⥤ 𝒮) (J : GrothendieckTopology 𝒮)

/-- The strongly cartesian morphisms belonging to a sieve. For the topology `𝒳` inherits from
`(𝒮, J)` these are cofinal in every covering sieve, which is
`CategoryTheory.Functor.generate_cartesianArrows_mem_inheritedTopology`. -/
def cartesianArrows {X : 𝒳} (S : Sieve X) : Presieve X :=
  fun _ f => S.arrows f ∧ p.IsStronglyCartesian (p.map f) f

/-- The strongly cartesian morphisms of a sieve are arrows of that sieve. -/
lemma cartesianArrows_le {X : 𝒳} (S : Sieve X) : p.cartesianArrows S ≤ S.arrows :=
  fun _ _ hf => hf.1

variable [p.IsFibered] [HasPullbacks 𝒮]

/-- **The structure functor of a fibred category is continuous** from the topology `𝒳` inherits
from `(𝒮, J)` to `J`. This is Stacks 06NW, read through
`CategoryTheory.Functor.isFibredOneMorphism_id` — which makes `p` a 1-morphism from `p` to the
identity of `𝒮` — and the identification of the topology a site inherits from itself along the
identity with its own topology.

`HasPullbacks 𝒮` is carried because the route does: it is a hypothesis of
`CategoryTheory.Functor.IsFibredOneMorphism.isContinuous_and_isCocontinuous_inheritedTopology`,
through the cover-preservation argument. It is not needed for *every* `p` — for the projection
of a product category there is an argument with no hypothesis on the base at all,
`Stacks.SimplicialModules.isContinuous_prodSnd_inheritedTopology` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/AugmentationDerivedBaseChange.lean`,
which uses the section `d ↦ (d, U)` instead. That statement is the specialised keeper for
`Prod.snd`; this one is the general statement for an arbitrary fibred category, which nothing
else provides, and the two are at different generality rather than duplicates. -/
instance isContinuous_inheritedTopology : p.IsContinuous (p.inheritedTopology J) J := by
  have : (𝟭 𝒮).IsFibered := (CategoryTheory.Functor.isFiberedInGroupoids_id (𝒞 := 𝒮)).isFibered
  have h := ((CategoryTheory.Functor.isFibredOneMorphism_id
    p).isContinuous_and_isCocontinuous_inheritedTopology J).1
  rwa [CategoryTheory.Functor.inheritedTopology_id] at h

/-- **The structure functor of a fibred category is cocontinuous** from the topology `𝒳`
inherits from `(𝒮, J)` to `J`, the other half of Stacks 06NW. Cocontinuity is what makes
restriction along `p` exact, and so is a standing hypothesis of Stacks 07AC. -/
instance isCocontinuous_inheritedTopology : p.IsCocontinuous (p.inheritedTopology J) J := by
  have : (𝟭 𝒮).IsFibered := (CategoryTheory.Functor.isFiberedInGroupoids_id (𝒞 := 𝒮)).isFibered
  have h := ((CategoryTheory.Functor.isFibredOneMorphism_id
    p).isContinuous_and_isCocontinuous_inheritedTopology J).2
  rwa [CategoryTheory.Functor.inheritedTopology_id] at h

/-- **The strongly cartesian morphisms of a covering sieve are cofinal in it.** The sieve they
generate is again a covering sieve for the topology inherited from `(𝒮, J)`.

The proof is an induction over `CategoryTheory.Precoverage.Saturate`; see the module
docstring. -/
theorem generate_cartesianArrows_mem_inheritedTopology {X : 𝒳} (S : Sieve X)
    (hS : S ∈ p.inheritedTopology J X) :
    Sieve.generate (p.cartesianArrows S) ∈ p.inheritedTopology J X := by
  rw [Functor.inheritedTopology_eq, Precoverage.mem_toGrothendieck_iff] at hS
  induction hS with
  | of X R hR =>
    refine (p.inheritedTopology J).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck hR)
    refine Sieve.giGenerate.gc.monotone_l fun Y f hf => ?_
    exact ⟨⟨Y, 𝟙 Y, f, hf, by simp⟩, hR.1 f hf⟩
  | top X =>
    have hid : Sieve.generate (p.cartesianArrows (⊤ : Sieve X)) = ⊤ :=
      Sieve.id_mem_iff_eq_top.mp ⟨X, 𝟙 X, 𝟙 X, ⟨trivial, inferInstance⟩, by simp⟩
    rw [hid]
    exact (p.inheritedTopology J).top_mem X
  | pullback X S _ Y f ih =>
    refine (p.inheritedTopology J).superset_covering ?_
      ((p.inheritedTopology J).pullback_stable f ih)
    rintro W h ⟨Z, a, g, ⟨hgS, hgc⟩, hfac⟩
    have := hgc
    have : HasPullback g f := IsFibered.hasPullback_of_isStronglyCartesian p g f
    have hcart : p.IsStronglyCartesian (p.map (pullback.snd g f)) (pullback.snd g f) :=
      isStronglyCartesian_of_isPullback p hgc f (IsPullback.of_hasPullback g f).flip
    have hmem : (Sieve.pullback f S).arrows (pullback.snd g f) := by
      show S.arrows (pullback.snd g f ≫ f)
      rw [← pullback.condition]
      exact S.downward_closed hgS _
    exact ⟨pullback g f, pullback.lift a h hfac, pullback.snd g f, ⟨hmem, hcart⟩,
      pullback.lift_snd _ _ _⟩
  | transitive X S R _ hSR ihS ihR =>
    refine (p.inheritedTopology J).transitive ihS _ ?_
    rintro Z g ⟨W, a, g₀, ⟨hg₀S, hg₀c⟩, rfl⟩
    have := hg₀c
    refine (p.inheritedTopology J).superset_covering ?_
      ((p.inheritedTopology J).pullback_stable a (ihR hg₀S))
    rw [Sieve.pullback_comp]
    refine Sieve.pullback_monotone a ?_
    rintro V h ⟨T, b, c, ⟨hcS, hcc⟩, rfl⟩
    have := hcc
    refine ⟨T, b, c ≫ g₀, ⟨hcS, ?_⟩, by simp⟩
    rw [p.map_comp]
    exact IsStronglyCartesian.comp p

/-- **The inherited topology satisfies the covering-pullback clause of Stacks continuity**,
clause (2) of Sites Definition 00WV for the structure functor `p` of a fibred category. The
cofinal covering families are the strongly cartesian morphisms of the covering sieves, by
`generate_cartesianArrows_mem_inheritedTopology`; their pullbacks along arbitrary morphisms
exist and are preserved by `p`, both halves being Stacks 06N5. -/
instance preservesCoveringPullbacks_inheritedTopology :
    Stacks.Sites.PreservesCoveringPullbacks (p.inheritedTopology J) p where
  exists_cover X S hS := by
    refine ⟨p.cartesianArrows S, p.generate_cartesianArrows_mem_inheritedTopology J S hS,
      p.cartesianArrows_le S, ?_⟩
    intro Y f hf W g
    have := hf.2
    have hpb : HasPullback f g := IsFibered.hasPullback_of_isStronglyCartesian p f g
    refine ⟨hpb, ?_⟩
    have hmap := IsFibered.map_isPullback_of_isStronglyCartesian p f g
    have heq : pullbackComparison p f g = hmap.isoPullback.hom := by
      apply pullback.hom_ext <;> simp
    have : IsIso (pullbackComparison p f g) := by rw [heq]; infer_instance
    exact PreservesPullback.of_iso_comparison p

end CategoryTheory.Functor

end
