module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A covering presieve of the final object of the small étale site has a finite covering subfamily

Let `S` be a scheme whose underlying space is quasi-compact and let `P` be a presieve on the
final object of the small étale site of `S` which generates a covering sieve.  Then **finitely
many members of `P` already cover**: there is a finite subfamily of `P` whose sources cover the
final object of the site in the sense of
`CategoryTheory.GrothendieckTopology.CoversTop`.

This is the finite-refinement proviso of the boundedness step of Stacks 08HE (2) ⇒ (1),
`AlgebraicGeometry.RingedSite.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom`, whose hypothesis
is literally the statement below at `X = AlgebraicGeometry.smallEtaleRingedSite B S hS` and `T` the
final object.

## The argument, and what it does *not* use

A covering sieve of the small étale site is jointly surjective on points
(`AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`), and an arrow in the sieve generated
by `P` factors through a member of `P`, so the members of `P` are jointly surjective.  Each of
them is étale on underlying schemes (`AlgebraicGeometry.SmallEtale.etale_toScheme_map`), hence
flat and locally of finite presentation, hence universally open
(`AlgebraicGeometry.UniversallyOpen.of_flat`), so its image is **open**.  A quasi-compact space
covered by open sets is covered by finitely many of them, and a jointly surjective family of the
small étale site generates a covering sieve
(`AlgebraicGeometry.SmallEtale.mem_topology_of_jointlySurjective`); over the final object that is
`CoversTop`, by `CategoryTheory.GrothendieckTopology.coversTop_iff_of_isTerminal`.

Two corrections to the route the obligation file of Stacks 08HE recorded for this proviso, both
machine-checked here.

* The **small affine étale subsite is not needed**, and neither is
  `Stacks.Sites.exists_finite_flat_refinement`.  That route was prescribed because the small étale
  site has no finite *affine* refinement; but the proviso does not ask the members of the
  subfamily to be affine, only to be finitely many and to belong to the given presieve, and for
  that openness of étale images plus quasi-compactness of `S` suffices.  Running it on the small
  étale site itself is also what the chain needs: clause (2) of Stacks 08HE is a statement about
  `AlgebraicGeometry.smallEtaleRingedSite`, not about the affine subsite.
* What the proviso costs is **quasi-compactness of `S`**, not affineness.  Affineness enters only
  as the way the induction's locality reduction supplies it;
  `AlgebraicGeometry.SmallEtale.exists_finite_subfamily_coversTop_of_isAffine` records that
  specialisation.  The final object of the small étale site exists for every `S`
  (`AlgebraicGeometry.SmallEtale.finalIsTerminal`), unlike that of the affine subsite, which needs
  `S` affine; so no hypothesis is spent on having a terminal object at all.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_finite_subfamily_coversTop`: **the finite-refinement
  proviso**, from quasi-compactness of the underlying space of `S`.
* `AlgebraicGeometry.SmallEtale.exists_finite_subfamily_coversTop_of_isAffine`: the same for an
  affine `S`.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 021D](https://stacks.math.columbia.edu/tag/021D)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The image of a morphism of the small étale site is open.**  Every such morphism is étale on
underlying schemes, hence flat and locally of finite presentation, hence universally open. -/
@[sga "3 X 4.7" "special case"]
theorem isOpen_range_toScheme_map {X Y : SmallEtale B S hS} (g : X ⟶ Y) :
    IsOpen (Set.range ((toScheme B S hS).map g)) := by
  have : UniversallyOpen ((toScheme B S hS).map g) := UniversallyOpen.of_flat _
  simpa only [Set.image_univ] using
    Scheme.Hom.isOpenMap ((toScheme B S hS).map g) _ isOpen_univ

/-- **A covering presieve of the final object of the small étale site has a finite covering
subfamily**, when the underlying space of `S` is quasi-compact.

This is the shape of the finite-refinement hypothesis of
`AlgebraicGeometry.RingedSite.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom` at the small étale
ringed site of `S` and its final object. -/
theorem exists_finite_subfamily_coversTop
    (hqc : CompactSpace ((toScheme B S hS).obj (final B S hS)))
    (P : Presieve (final B S hS))
    (hP : Sieve.generate P ∈ topology B S hS (final B S hS)) :
    ∃ (ι : Type (u + 1)) (_ : Finite ι) (V : ι → SmallEtale B S hS)
      (f : ∀ i, V i ⟶ final B S hS),
      (∀ i, P (f i)) ∧ (topology B S hS).CoversTop V := by
  classical
  have hopen : ∀ i : P.uncurry,
      IsOpen (Set.range ((toScheme B S hS).map i.1.2)) := fun i =>
    isOpen_range_toScheme_map B S hS i.1.2
  have hcover : (Set.univ : Set ((toScheme B S hS).obj (final B S hS))) ⊆
      ⋃ i : P.uncurry, Set.range ((toScheme B S hS).map i.1.2) := by
    intro x _
    obtain ⟨W, g, ⟨Z, a, p, hp, rfl⟩, y, rfl⟩ := exists_mem_arrows_mem_range B S hS hP x
    refine Set.mem_iUnion.2 ⟨⟨⟨Z, p⟩, hp⟩, (toScheme B S hS).map a y, ?_⟩
    rw [Functor.map_comp]
    rfl
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨{i : P.uncurry // i ∈ t}, inferInstance, fun j => j.1.1.1, fun j => j.1.1.2,
    fun j => j.1.2, ?_⟩
  refine ((topology B S hS).coversTop_iff_of_isTerminal _ (finalIsTerminal B S hS) _).2 ?_
  refine mem_topology_of_jointlySurjective fun x => ?_
  obtain ⟨i, hit, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨i.1.1, i.1.2, ⟨⟨i, hit⟩, ⟨𝟙 _⟩⟩, hx⟩

/-- **The finite-refinement proviso for an affine `S`**, which is the case the induction of
Stacks 08HE (2) ⇒ (1) reaches through its locality reduction: an affine scheme is quasi-compact. -/
theorem exists_finite_subfamily_coversTop_of_isAffine [_root_.AlgebraicGeometry.IsAffine S]
    (P : Presieve (final B S hS))
    (hP : Sieve.generate P ∈ topology B S hS (final B S hS)) :
    ∃ (ι : Type (u + 1)) (_ : Finite ι) (V : ι → SmallEtale B S hS)
      (f : ∀ i, V i ⟶ final B S hS),
      (∀ i, P (f i)) ∧ (topology B S hS).CoversTop V :=
  exists_finite_subfamily_coversTop B S hS
    (show CompactSpace ((toScheme B S hS).obj (final B S hS)) from
      inferInstanceAs (CompactSpace S)) P hP

end AlgebraicGeometry.SmallEtale

end
