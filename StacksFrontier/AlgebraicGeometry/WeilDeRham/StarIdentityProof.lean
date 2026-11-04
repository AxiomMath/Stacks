module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.SheafCup
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.KunnethRelativeForms
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.TopComponents
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.StarIdentityProof.StarIdentity

/-!
# The identity `(★)` of the diagonal argument from the factorization through the sections

Let `f : X ⟶ Spec A` be proper and smooth of relative dimension `n = e + 1` with a section `σ`,
`W = X ×_A X` with projections `p₁`, `p₂`, `η ∈ Hⁿ(W, Ωⁿ_{W/A})` the Gysin class of the diagonal
and `ξ ∈ Hⁿ(X, Ωⁿ_{X/A})` that of the section. For `θ ∈ Hⁿ(X, Ω^e_{X/A})` the proof of
[Stacks, Tag 0G8J] needs the identity

`(★)  p₁^*θ ∪ η = p₁^*θ ∪ p₂^*ξ + p₂^*θ ∪ p₁^*ξ`   in `H^{2n}(W, Ω^{2n-1}_{W/A})`,

the claim `θ₁ = θ₂ = θ` of the source. This file derives `(★)` from three inputs:
`p₁^*θ ∪ η = p₂^*θ ∪ η`, and the fact that the cup product with `p₁^*θ` (resp. `p₂^*θ`) of a class
of `p₂^*Ωⁿ` (resp. `p₁^*Ωⁿ`) only depends on its restriction along `j = (σ ∘ f, id)` (resp.
`j' = (id, σ ∘ f)`).

The argument is the source's. By the Künneth formula [Stacks, Tag 0FMA] and the vanishing of forms
of degree `> n`, `Ω^{2n-1}_{W/A}` is the direct sum of `p₁^*Ω^e ⊗ p₂^*Ωⁿ` and `p₁^*Ωⁿ ⊗ p₂^*Ω^e`
(`Stacks.WeilDeRham.kunneth_top_split`), so `(★)` may be checked on the two components. On local
sections, by associativity and graded commutativity of the wedge product, the `(e, n)`-component
of `p₁^*ω ∧ ϑ` is `ω ⊗ π(ϑ)`, where `π : Ωⁿ_{W/A} ⟶ p₂^*Ωⁿ` is the projection onto the forms
pulled back along `p₂` (`Stacks.WeilDeRham.fstForms_mul_kunnethProj`), and symmetrically for the
`(n, e)`-component of `p₂^*ω ∧ ϑ` (`Stacks.WeilDeRham.sndForms_mul_kunnethProj`), while the
products `p₂^*ω ∧ p₁^*ϑ'` and `p₁^*ω ∧ p₂^*ϑ'` with `ϑ'` of degree `n` have no `(e, n)`-, resp.
`(n, e)`-component. The cup product being natural in the three sheaves
(`Stacks.WeilDeRham.sheafCup_naturality`), the two components of `(★)` reduce to
`p₁^*θ ∪ π(η) = p₁^*θ ∪ π(p₂^*ξ)` and its mirror
(`Stacks.WeilDeRham.sheafCup_eq_add_of_components`).

The projection `π` is the passage to forms relative to `p₁`, `Ωⁿ_{W/A} ⟶ Ωⁿ_{W/X} ≅ p₂^*Ωⁿ_{X/A}`
(`Stacks.WeilDeRham.relativeProjection`). Its pullback along the section `j` of `p₂` factors
through the pullback of forms along `j` (`Stacks.WeilDeRham.pullback_map_relativeProjection`), so
`j^*π(η)` and `j^*π(p₂^*ξ)` are determined by `j^*η = ξ` and `j^*p₂^*ξ = ξ`, which is what the
factorization through the section asks for.

## Main definitions

* `Stacks.WeilDeRham.sheafCup`: the cup product of Cohomology, Section 0FKU on a scheme along a
  multiplication of sheaves.
* `Stacks.WeilDeRham.kunnethIncl`, `Stacks.WeilDeRham.kunnethProj`: the inclusions and projections
  of the Künneth decomposition of `Ωᵐ_{X ×_S X/S}`.
* `Stacks.WeilDeRham.formsToRelativeOver`: the homomorphism `Ω^•_{W/S} ⟶ Ω^•_{W/X}`.
* `Stacks.WeilDeRham.relativeProjection`: the projection `Ωⁿ_{W/S} ⟶ G^*Ωⁿ_{X/S}` for a cartesian
  square `W = X ×_S X`.
* `Stacks.WeilDeRham.classTransport`: classes of `H^{0+n}(-, Ω^{0+n})`, the degrees in which the
  Gysin classes are stated, read in `Hⁿ(-, Ωⁿ)`.

## Main results

* `Stacks.WeilDeRham.sheafCup_naturality`: the cup product is natural.
* `Stacks.WeilDeRham.kunneth_top_split`: `Ω^{2n-1}_{X ×_S X/S}` is the sum of two Künneth summands.
* `Stacks.WeilDeRham.fstForms_mul_kunnethProj`, `Stacks.WeilDeRham.sndForms_mul_kunnethProj`: the
  top components of products with pulled-back forms.
* `Stacks.WeilDeRham.unitPullback_map_relativeProjection`: the pullback along a section after the
  relative projection factors through the pullback of forms.
* `Stacks.WeilDeRham.starIdentity_of_cupFactorsThroughSection`: **the identity `(★)`**.

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/
