module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyBaseChangeClass
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FlatBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport

/-!
# Invariance under isomorphism of targets of flatness and of flat adic finite type

`AlgebraicGeometry.FormalSpace.PropertyIsInvariantUnderTargetIsoOn` is the condition the chart
argument of Stacks 0GBD needs of the property it transfers: the presentation of a chart of the
fibre product by a completed tensor product is an isomorphism of chart rings rather than an
equality, so the property must not distinguish a target from an isomorphic one. For a general
property of arrows of `WAdm^{Noeth}` the library carries it as a hypothesis; this file
discharges it for the two properties the base change of a flat morphism is run at, namely
flatness and flatness together with the property of **Stacks 0GBW**.

Both are proved for an arbitrary class of rings, since neither argument looks at the class: the
three conjuncts are each carried along a continuous ring isomorphism with continuous inverse by
a transport that has nothing to do with the topology being adic or the rings being Noetherian.

## Main results

* `RingHom.IsAdic.comp_ringEquiv`: an adic homomorphism stays adic after composition with an
  isomorphism of topological rings.
* `TopologicalRing.IsTopologicallyOfFiniteType.comp_ringEquiv`: a homomorphism topologically of
  finite type stays so after composition with a continuous surjection, in particular with an
  isomorphism of topological rings.
* `AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderTargetIso_isFlatHom`: flatness is
  invariant under isomorphism of targets.
* `AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderTargetIso_isFlatAdicOfFiniteTypeHom`:
  so is flatness together with the property of Stacks 0GBW.

## Implementation notes

The mechanism is not the one the Stacks Project uses. There, invariance under isomorphism of
targets is a consequence of axiom (1) of Situation 0CBA — an isomorphism is étale, and the
completion of a complete ring along the extensions of the ideals of definition is that ring
again — and so holds for every local property. In this library the completed corners of a
`TopologicalRing.LocalizationDiagram` are `TopologicalRing.CompletionOver` types, which are
only *isomorphic* to the rings they complete, and carrying a property of morphisms across such
an isomorphism is exactly the statement being proved; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalSpace/LocalPropertyBaseChange.lean`. So the invariance is
proved here directly from the definitions of the two properties instead.

## References

* [Stacks Project, Tag 0GBW](https://stacks.math.columbia.edu/tag/0GBW)
* [Stacks Project, Tag 0GCA](https://stacks.math.columbia.edu/tag/0GCA)
* [Stacks Project, Tag 0GCE](https://stacks.math.columbia.edu/tag/0GCE)
-/

@[expose] public noncomputable section

universe u

/-- An adic homomorphism of topological rings composed with an isomorphism of topological rings
is adic: the same ideal of definition of the source works, because the isomorphism carries the
ideal it extends to onto its image, which again defines the topology. -/
theorem RingHom.IsAdic.comp_ringEquiv {A R R' : Type u}
    [CommRing A] [TopologicalSpace A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing R'] [TopologicalSpace R'] [IsTopologicalRing R']
    {ψ : A →+* R} (hψ : RingHom.IsAdic ψ) (e : R ≃+* R') (he : Continuous e)
    (he' : Continuous e.symm) : RingHom.IsAdic (e.toRingHom.comp ψ) := by
  obtain ⟨I, hI, hImap⟩ := hψ
  refine ⟨I, hI, ?_⟩
  rw [← Ideal.map_map ψ e.toRingHom]
  exact TopologicalRing.isAdic_map_of_ringEquiv e he he' hImap

/-- A homomorphism topologically of finite type composed with a continuous surjective
homomorphism is topologically of finite type: the polynomial algebra with dense image composes
with the surjection, and the image of a dense set under a continuous surjection is dense. -/
theorem TopologicalRing.IsTopologicallyOfFiniteType.comp_surjective {A R R' : Type u}
    [CommRing A] [CommRing R] [TopologicalSpace R] [CommRing R'] [TopologicalSpace R']
    {ψ : A →+* R} (hψ : TopologicalRing.IsTopologicallyOfFiniteType ψ) (g : R →+* R')
    (hg : Function.Surjective g) (hgc : Continuous g) :
    TopologicalRing.IsTopologicallyOfFiniteType (g.comp ψ) := by
  obtain ⟨n, f, hf, hd⟩ := hψ
  refine ⟨n, g.comp f, ?_, ?_⟩
  · rw [RingHom.comp_assoc, hf]
  · exact hg.denseRange.comp hd hgc

/-- A homomorphism topologically of finite type composed with an isomorphism of topological
rings is topologically of finite type. -/
theorem TopologicalRing.IsTopologicallyOfFiniteType.comp_ringEquiv {A R R' : Type u}
    [CommRing A] [CommRing R] [TopologicalSpace R] [CommRing R'] [TopologicalSpace R']
    {ψ : A →+* R} (hψ : TopologicalRing.IsTopologicallyOfFiniteType ψ) (e : R ≃+* R')
    (he : Continuous e) : TopologicalRing.IsTopologicallyOfFiniteType (e.toRingHom.comp ψ) :=
  hψ.comp_surjective e.toRingHom e.surjective he

namespace AlgebraicGeometry.FormalSpace

/-- **Flatness is invariant under isomorphism of targets**, for every class of topological
rings: an isomorphism of rings is flat, and flatness is stable under composition. This
discharges the hypothesis `hiso` of the Stacks 0GBG transfer at `TopologicalRing.IsFlatHom`,
which is the shape part (1) of Stacks 0GCE consumes it in. -/
theorem propertyIsInvariantUnderTargetIso_isFlatHom
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop) :
    PropertyIsInvariantUnderTargetIsoOn.{u} C TopologicalRing.IsFlatHom := by
  intro A R R' _ _ _ _ _ _ _ _ _ _ _ _ _hA _hR _hR' ψ e _hψc _he _he' hψ
  exact hψ.comp (RingHom.Flat.of_bijective e.bijective)

/-- **Flatness together with the property of Stacks 0GBW is invariant under isomorphism of
targets**, for every class of topological rings: each of the three conjuncts transports along
an isomorphism of topological rings. This discharges the hypothesis `hiso` of the Stacks 0GBF
transfer at `AlgebraicGeometry.FormalSpace.IsFlatAdicOfFiniteTypeHom`, which is the shape part
(2) of Stacks 0GCE consumes it in. -/
theorem propertyIsInvariantUnderTargetIso_isFlatAdicOfFiniteTypeHom
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop) :
    PropertyIsInvariantUnderTargetIsoOn.{u} C IsFlatAdicOfFiniteTypeHom := by
  intro A R R' _ _ _ _ _ _ _ _ _ _ _ _ _hA _hR _hR' ψ e _hψc he he' hψ
  exact ⟨hψ.1.comp (RingHom.Flat.of_bijective e.bijective), hψ.2.1.comp_ringEquiv e he he',
    hψ.2.2.comp_ringEquiv e he⟩

end AlgebraicGeometry.FormalSpace

end
