module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjectsCanonical

/-!
# Perfect objects are relatively perfect, and tensoring with them preserves relative perfectness

Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite presentation. A
perfect object of `D(𝒪_X)` is `S`-perfect, and if `K` is perfect and `M` is `S`-perfect then
`K ⊗^{L}_{𝒪_X} M` is `S`-perfect. This is [Stacks, Tag 0DI4].

Relative perfectness is `AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`, Stacks 0DI0 itself:
pseudo-coherence together with local finiteness of the Tor dimension over `f⁻¹𝒪_S`, read
against the derived tensor product of Stacks 06YU on each open subspace of `(X, f⁻¹𝒪_S)`. The
derived tensor product `K ⊗^{L}_{𝒪_X} M` is the canonical one of Stacks 06YU on `X`,
`Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct`. No hypothesis beyond the source's
own enters.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_isPerfect`: a perfect object is
  `S`-perfect.
* `AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_derivedTensor`: the derived tensor product
  of a perfect object with an `S`-perfect object is `S`-perfect.
* `AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_isPerfect_and_derivedTensor`: both
  assertions together, which is Stacks 0DI4.

## Implementation notes

The source reduces to the affine case and applies the algebraic statement Stacks 0DHU. The proof
here is stalkwise instead, and is carried out in
`StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjectsCanonical`: Tor amplitude
over `f⁻¹𝒪_S` on an open is a condition on the stalks over the local rings of `S`
(Stacks 09U9), a perfect object has locally bounded Tor amplitude over `𝒪_X` (Stacks 08CS),
flatness of `𝒪_{S, f x} ⟶ 𝒪_{X, x}` carries a bound over `𝒪_{X, x}` down to `𝒪_{S, f x}`, and
on a stalk the derived tensor product is the derived tensor product of the stalks, whose Tor
amplitude over `𝒪_{S, f x}` is bounded by the sum of the two bounds. Pseudo-coherence of the
tensor product is Stacks 09J3, unconditional for the derived tensor product of Stacks 06YU.

That file states the result for `AlgebraicGeometry.Scheme.Hom.IsPerfectRelativeTo` at the
canonical certificate family; at that family the predicate *is* Stacks 0DI0, by
`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_canonicalFamily_iff`, which is `Iff.rfl`.

All derived categories are the standard ones, as in the rest of the Stacks 06YU development.

## References

* [Stacks Project, Lemma 36.35.5 (Tag 0DI4)](https://stacks.math.columbia.edu/tag/0DI4)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]

/-- **Stacks 0DI4, first assertion.** Let `f : X ⟶ S` be a morphism of schemes which is flat and
locally of finite presentation. A perfect object of `D(𝒪_X)` is `S`-perfect. -/
theorem isRelativelyPerfect_of_isPerfect (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : RingedSpace.IsPerfect E) : f.IsRelativelyPerfect E :=
  (isPerfectRelativeTo_canonicalFamily_iff f E).1
    (isPerfectRelativeTo_canonical_of_isPerfect f E hE)

/-- **Stacks 0DI4, second assertion.** Let `f : X ⟶ S` be a morphism of schemes which is flat
and locally of finite presentation, and let `K, M ∈ D(𝒪_X)`. If `K` is perfect and `M` is
`S`-perfect, then `K ⊗^{L}_{𝒪_X} M` is `S`-perfect, the derived tensor product being the one of
Stacks 06YU. -/
theorem isRelativelyPerfect_derivedTensor (K M : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hK : RingedSpace.IsPerfect K) (hM : f.IsRelativelyPerfect M) :
    f.IsRelativelyPerfect
      (((Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct
        X.toRingedSpace).tensor.obj K).obj M) :=
  (isPerfectRelativeTo_canonicalFamily_iff f _).1
    (isPerfectRelativeTo_canonical_derivedTensor f K M hK
      ((isPerfectRelativeTo_canonicalFamily_iff f M).2 hM))

/-- **Stacks 0DI4.** Let `f : X ⟶ S` be a morphism of schemes which is flat and locally of finite
presentation. A perfect object of `D(𝒪_X)` is `S`-perfect. If `K, M ∈ D(𝒪_X)`, then
`K ⊗^{L}_{𝒪_X} M` is `S`-perfect if `K` is perfect and `M` is `S`-perfect.

Here `S`-perfect is Stacks 0DI0, `AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`, and the
derived tensor product is the one of Stacks 06YU. -/
@[stacks 0DI4]
theorem isRelativelyPerfect_of_isPerfect_and_derivedTensor :
    (∀ E : DerivedCategory (OXMod.{u, u} X.toRingedSpace),
        RingedSpace.IsPerfect E → f.IsRelativelyPerfect E) ∧
      ∀ K M : DerivedCategory (OXMod.{u, u} X.toRingedSpace),
        RingedSpace.IsPerfect K → f.IsRelativelyPerfect M →
          f.IsRelativelyPerfect
            (((Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct
              X.toRingedSpace).tensor.obj K).obj M) :=
  ⟨isRelativelyPerfect_of_isPerfect f, isRelativelyPerfect_derivedTensor f⟩

end AlgebraicGeometry.Scheme.Hom

end
