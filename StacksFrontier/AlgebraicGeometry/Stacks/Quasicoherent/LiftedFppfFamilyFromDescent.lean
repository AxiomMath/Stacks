module

public import StacksFrontier.AlgebraicGeometry.Stacks.Localization.InheritedTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilyTransport

/-!
# The step of Stacks 076T carried as a hypothesis

This file discharges the hypothesis `AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily` of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFromFlatBaseChange.lean` over the
one compatibility carried by
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilySheafCondition.lean`.

The transport the source's proof of **Stacks 076T** is — the sheaf condition for `F` along a
family of arrows *is* the sheaf condition for `𝒢^a` downstairs, which is Descent,
**Stacks 03DT** — is run in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilyTransport.lean`. What is
added here is the bookkeeping which puts the hypothesis in the shape that transport consumes:

* the presieve is written as a family of arrows, which costs nothing, the family indexed by the
  arrows of the presieve itself generating it;
* the sheaf condition is moved to the big fppf site of the scheme `U` below `x` by
  `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_overPost`, whose hypothesis is supplied for
  free by `AlgebraicGeometry.Stack.overPostTransportIso`;
* and the covering sieve is moved downstairs by
  `CategoryTheory.Functor.isInheritedTopology_inheritedTopology` — the images of a family of
  strongly cartesian morphisms generate a covering sieve of the localized base topology exactly
  when the family does upstairs, and every morphism of a category fibred in groupoids is
  strongly cartesian. The sieve the two sides of the transport ask about is then the *same*
  sieve on `U` in `B.Schemes`, by `CategoryTheory.GrothendieckTopology.mem_over_iff` and
  `CategoryTheory.Sieve.overEquiv_ofArrows`.

## Main results

* `AlgebraicGeometry.Stack.isSheafForLiftedFppfFamily`: **the step of Stacks 076T carried as
  `AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily`**, over the compatibility
  `AlgebraicGeometry.Stack.LiftedSectionsCocycle` and nothing else.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe t u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

/-! ### The step of Stacks 076T -/

/-- **The step of Stacks 076T carried as
`AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily`.** For a presheaf of modules which is
locally quasi-coherent (**Stacks 06WJ**) and whose comparison map `c_φ` of **Stacks 06WC** is an
isomorphism along every arrow lying over a flat morphism locally of finite presentation, the
sheaf condition holds along every family of arrows of `𝒳` which generates a covering sieve of the
inherited fppf topology and lies over an fppf covering of schemes.

The only hypothesis carried is `AlgebraicGeometry.Stack.LiftedSectionsCocycle`, the compatibility
of the identification of `AlgebraicGeometry.Stack.liftedSectionsIso` with composition of arrows
of `𝒳`.

The presieve is first written as a family of arrows, which costs nothing: the family indexed by
the arrows of the presieve itself generates it. The covering sieve then moves downstairs by
`CategoryTheory.Functor.isInheritedTopology_inheritedTopology`, every arrow of a category fibred
in groupoids being strongly cartesian, and the sieve it lands as on the scheme `U` is the very
sieve the sheaf condition for `𝒢^a` asks about. -/
theorem isSheafForLiftedFppfFamily (hcoc : LiftedSectionsCocycle B E h S hS p hp) :
    IsSheafForLiftedFppfFamily B E h S hS p hp := by
  intro F hlqc hbc x R hR hfl M
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS p hp F hlqc x
  obtain ⟨I, z, φ, hRe⟩ :
      ∃ (I : Type (max v w)) (z : I → 𝒳) (φ : ∀ i, z i ⟶ x), Presieve.ofArrows z φ = R := by
    refine ⟨(y : 𝒳) × {f : y ⟶ x // R f}, fun i ↦ i.1, fun i ↦ i.2.1, ?_⟩
    funext Z g
    refine propext ⟨?_, fun hg ↦ ?_⟩
    · rintro ⟨i⟩
      exact i.2.2
    · exact Presieve.ofArrows.mk (⟨Z, g, hg⟩ : (y : 𝒳) × {f : y ⟶ x // R f})
  have hmem : ∀ i, R (φ i) := fun i ↦ hRe ▸ Presieve.ofArrows.mk i
  have hflat : ∀ i, Flat (B.inclusion.map (p.map (φ i)).left) := fun i ↦ (hfl (φ i) (hmem i)).1
  have hlfp : ∀ i, LocallyOfFinitePresentation (B.inclusion.map (p.map (φ i)).left) := fun i ↦
    (hfl (φ i) (hmem i)).2
  have : p.IsFibered := hp.isFibered
  rw [← hRe] at hR ⊢
  have hbase : Sieve.ofArrows (fun i ↦ p.obj (z i)) (fun i ↦ p.map (φ i)) ∈
      (B.topology.over (B.obj hS)) (p.obj x) :=
    (Functor.isInheritedTopology_inheritedTopology.{max v w} p (B.topology.over (B.obj hS))
      z φ fun i ↦ hp.isStronglyCartesian (φ i)).1 hR
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hbase
  rw [isSheafFor_ofArrows_iff_overPost B S hS p hp x (F.presheaf ⋙ coyoneda.obj (op M))
    (overPostTransportSections B S hS p hp F x M) φ
    (overPostTransportIso B S hS p hp x (F.presheaf ⋙ coyoneda.obj (op M)))]
  refine isSheafFor_overPostTransportSections B E h S hS p hp F hlqc hbc hcoc d _ _ hflat hlfp
    ?_ M
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact hbase

end AlgebraicGeometry.Stack

end
