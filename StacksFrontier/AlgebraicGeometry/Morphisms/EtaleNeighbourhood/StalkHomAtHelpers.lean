module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkHelpers
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reading a local homomorphism off a composite, through `stalkHomAt`

The two helpers of
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkHelpers` which are
stated in terms of `AlgebraicGeometry.Scheme.Hom.stalkHomAt`, the map of local rings that a
morphism induces at a point read through a transport.

They are separate from that module because `stalkHomAt` is defined in
`StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation`, whose
import closure is large; a consumer needing only the `stalkHomAt`-free helpers imports
`CompletedStalkHelpers` and pays nothing for this one.

## Main results

* `StacksDraft.ArtinApproximation.stalkClosedPointTo_comp_stalkHomAt`: the local homomorphism
  attached to a morphism `m : Spec R ⟶ W`, precomposed with the map of stalks of a further
  morphism `k : W ⟶ X`, is read off the composite `m ≫ k`.
* `StacksDraft.ArtinApproximation.stalkHomAt_congr`: the map of local rings depends only on the
  morphism, so an equality of morphisms transports it.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-- **Reading a local homomorphism off a composite.** Let `m : Spec R ⟶ W` be a morphism out of the
spectrum of a local ring and let `k : W ⟶ X` be a further morphism. If the composite `m ≫ k` is
the morphism `Spec.map f ≫ X.fromSpecStalk x` attached to a local homomorphism
`f : 𝒪_{X, x} ⟶ R`, then the local homomorphism attached to `m`, precomposed with the map of
stalks of `k`, is `f`. -/
@[ega "I 3.4.5" "partial"]
public theorem stalkClosedPointTo_comp_stalkHomAt {W X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (m : Spec R ⟶ W) (k : W ⟶ X) {x : X}
    (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom]
    (hmk : m ≫ k = Spec.map f ≫ X.fromSpecStalk x)
    (hk : k (m (closedPoint R)) = x) :
    (Scheme.stalkClosedPointTo m).hom.comp (k.stalkHomAt hk) = f.hom := by
  have hpoint : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) = x :=
    specMap_fromSpecStalk_closedPoint f
  apply CommRingCat.hom_ext_iff.mp
  show (X.presheaf.stalkCongr (.of_eq hk.symm)).hom ≫
    k.stalkMap (m (closedPoint R)) ≫ Scheme.stalkClosedPointTo m = f
  rw [← Scheme.stalkClosedPointTo_comp]
  exact (stalkCongr_comp_stalkClosedPointTo_congr (m ≫ k) (Spec.map f ≫ X.fromSpecStalk x) hmk hk
    hpoint).trans (stalkCongr_comp_stalkClosedPointTo f hpoint)

/-- The induced map of local rings depends only on the morphism, so an equality of morphisms
transports it. -/
public theorem stalkHomAt_congr {W V : Scheme.{u}} {m₁ m₂ : W ⟶ V} (hm : m₁ = m₂) {w : W} {v : V}
    (h₁ : m₁ w = v) (h₂ : m₂ w = v) : m₁.stalkHomAt h₁ = m₂.stalkHomAt h₂ := by
  subst hm
  rfl

end StacksDraft.ArtinApproximation

end
