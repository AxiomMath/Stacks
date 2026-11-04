module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DescentData
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseFaithful

/-!
# The arrow space of a groupoid as the kernel pair of its atlas

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let `φ : U ⟶ X` be a morphism of
algebraic spaces such that `t`, `s` and `φ` form a pullback square of the underlying presheaves.
Then `R` is isomorphic to the fibre product `AlgebraicGeometry.Space.QuasiCoherentDescent.pair` of
the one-element family `{φ : U ⟶ X}`, by an isomorphism carrying `t` to the first projection and
`s` to the second.

## Main definitions

* `AlgebraicGeometry.Space.arrowsKernelPairIso`: the isomorphism of the arrow space of the
  groupoid with the fibre product `U ×_X U`.

## Main results

* `AlgebraicGeometry.Space.arrowsKernelPairIso_hom_comp_pairFst`: the isomorphism carries the
  target projection of the groupoid to the first projection of the fibre product.
* `AlgebraicGeometry.Space.arrowsKernelPairIso_hom_comp_pairSnd`: the isomorphism carries the
  source projection of the groupoid to the second projection of the fibre product.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 03LZ](https://stacks.math.columbia.edu/tag/03LZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)

/-- The isomorphism of the arrow space of a groupoid in algebraic spaces with the fibre product
of the one-element family `{φ : U ⟶ X}`, when the target and source projections and `φ` form a
pullback square of the underlying presheaves. -/
def arrowsKernelPairIso (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    G.arrows ≅ QuasiCoherentDescent.pair B S hS (fun _ : Unit => G.objects) (fun _ => φ) () () :=
  ObjectProperty.isoMk _ hpb.isoPullback

/-- The identification of the arrow space with the kernel pair carries the target projection of
the groupoid to the first projection of the fibre product. -/
theorem arrowsKernelPairIso_hom_comp_pairFst
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    (arrowsKernelPairIso B S hS G φ hpb).hom ≫
        QuasiCoherentDescent.pairFst B S hS (fun _ : Unit => G.objects) (fun _ => φ) () () =
      G.target :=
  ObjectProperty.hom_ext _ hpb.isoPullback_hom_fst

/-- The identification of the arrow space with the kernel pair carries the source projection of
the groupoid to the second projection of the fibre product. -/
theorem arrowsKernelPairIso_hom_comp_pairSnd
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    (arrowsKernelPairIso B S hS G φ hpb).hom ≫
        QuasiCoherentDescent.pairSnd B S hS (fun _ : Unit => G.objects) (fun _ => φ) () () =
      G.source :=
  ObjectProperty.hom_ext _ hpb.isoPullback_hom_snd

end AlgebraicGeometry.Space

end
