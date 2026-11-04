module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.SpecProductRing
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Defs
public import StacksFrontier.RingTheory.RelativeDimension.Defs
public import StacksFrontier.RingTheory.Smoothing.ProductOfFilteredColimits
public import StacksFrontier.Topology.Dimension.Euclidean

/-!
# A smooth algebra with geometrically irreducible fibres of unequal dimension

The relative dimension `Algebra.relativeDimension R B` is a *single* supremum, taken over all
primes of `B`. The dimension of a fibre of a smooth morphism is only *locally* constant on the
base, so over a disconnected base one supremum cannot record every fibre: there is a smooth
algebra whose spectrum has geometrically irreducible fibres of two different dimensions.

The witness is the disjoint union of a point and the affine line over a two-point base:
`R = ℚ × ℚ`, `B = ℚ × ℚ[X]`, with the componentwise structure map
`(algebraMap ℚ ℚ).prodMap (algebraMap ℚ ℚ[X])`. It is smooth by `Algebra.Smooth.prod`, and its
fibres are geometrically irreducible because `Spec (R₁ × R₂)` is the disjoint union of
`Spec R₁` and `Spec R₂` and geometric irreducibility is Zariski-local at the target
(`AlgebraicGeometry.IsZariskiLocalAtTarget.specMap_prodMap`), so the condition is checked on the
two factors `ℚ/ℚ` and `ℚ[X]/ℚ` separately. `Spec R` has exactly two points, `Ideal.prod ⊥ ⊤`
and `Ideal.prod ⊤ ⊥`; the fibre over the first is the single point `Ideal.prod ⊥ ⊤` of `Spec B`
and has dimension `0`, while the fibre over the second contains `Spec ℚ[X]` as a subspace and
has dimension at least `1`. Both fibres are nonempty, so the discrepancy is genuine and not an
artefact of the value `-∞` on an empty fibre.

## Main results

* `Algebra.PointAndAffineLine.smooth` and
  `Algebra.PointAndAffineLine.geometricallyIrreducible`: the witness is a smooth algebra whose
  spectrum has geometrically irreducible fibres.
* `Algebra.PointAndAffineLine.topologicalKrullDim_fibrePoint` and
  `Algebra.PointAndAffineLine.one_le_topologicalKrullDim_fibreLine`: its two fibres have
  dimensions `0` and at least `1`.
* `Algebra.not_forall_relativeDimension_eq_topologicalKrullDim_fiber`: consequently the relative
  dimension of a smooth algebra with geometrically irreducible fibres does not compute the
  dimension of every fibre.

## Stacks 05I0 (2)

Item (2) of Stacks 05I0 is the dictionary between the scheme-theoretic notion of a one-step
dévissage and the ring-theoretic one, and it is an *equivalence*. This counterexample is what
fixes the condition the ring side has to carry for that: on the scheme side
`AlgebraicGeometry.OneStepDevissage.fiber_dimension` constrains the dimension of **every** fibre
of the smooth morphism `g`, faithfully to Stacks 05H4 (5), which quantifies over all `t ∈ S`,
whereas `Algebra.relativeDimension` is one supremum — and the two are not the same condition,
since the relative dimension of a smooth algebra with geometrically irreducible fibres does not
compute the dimension of every fibre. The relative dimension condition of Stacks 05HZ (4),
which Remark 05I0 describes as the condition of 05H4 (5) "built in" to the notion of a complete
dévissage at `q`, is therefore read fibre by fibre: the ring side of the equivalence is a
complete dévissage at `q`, whose field
`Module.NonemptyCompleteDevissageAt.relativeDimension_eq_support` is the supremum form of
Definition 00QD, together with `Module.CompleteDevissageAt.FibresHaveRelativeDimension`, which
asks every fibre of `Spec Bᵢ → Spec R` to have the relative dimension.

## Implementation notes

The algebra structure on `ℚ × ℚ[X]` over `ℚ × ℚ` is not an instance anywhere, and making it a
global one would put a nonstandard structure on a pair of concrete types; it is therefore a
`def` made available by `attribute [local instance]` for this file only. The refuted statement
quantifies over `R B : Type`, the universe the witness lives in.

The fibre over `Ideal.prod ⊥ ⊤` is a single point because a prime of `B` contracting to it is,
by the classification of primes of a product ring `Ideal.ideal_prod_prime`, either
`Ideal.prod p ⊤` with `p` a prime of `ℚ` — necessarily `⊥`, giving the point itself — or
`Ideal.prod ⊤ p`, which contracts to `Ideal.prod ⊤ (Ideal.comap Polynomial.C p)` and so cannot
contract to `Ideal.prod ⊥ ⊤`. A nonempty subsingleton space is Hausdorff, so
`topologicalKrullDim_eq_zero_of_t2Space` gives the value `0`.

For the other fibre only the lower bound `1` is needed, so no homeomorphism is constructed:
`PrimeSpectrum.comap (RingHom.snd ℚ ℚ[X])` is a closed embedding whose image lies in that
fibre, hence an inducing map `Spec ℚ[X] → ` the fibre, and `topologicalKrullDim` is monotone
along inducing maps. The dimension of `Spec ℚ[X]` is `ringKrullDim ℚ + 1 = 1`.

## References

* [Stacks Project, Tag 00QD](https://stacks.math.columbia.edu/tag/00QD)
* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 05I0](https://stacks.math.columbia.edu/tag/05I0)

## Tags

relative dimension, smooth, geometrically irreducible, counterexample
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat Polynomial PrimeSpectrum

namespace Algebra.PointAndAffineLine

/-- The `ℚ × ℚ`-algebra `ℚ × ℚ[X]`: a point over one factor of the base and the affine line
over the other. Its structure map is the componentwise product of `algebraMap ℚ ℚ` and
`algebraMap ℚ ℚ[X]`. -/
@[instance_reducible]
public noncomputable def algebra : Algebra (ℚ × ℚ) (ℚ × ℚ[X]) :=
  ((algebraMap ℚ ℚ).prodMap (algebraMap ℚ ℚ[X])).toAlgebra

attribute [local instance] algebra

/-- The structure map of the witness sends `(a, b)` to `(a, C b)`. -/
public theorem algebraMap_apply (r : ℚ × ℚ) :
    algebraMap (ℚ × ℚ) (ℚ × ℚ[X]) r = (r.1, C r.2) := rfl

/-- **The witness is smooth.** A componentwise product of smooth algebras is smooth over the
product of the bases. -/
public theorem smooth : Algebra.Smooth (ℚ × ℚ) (ℚ × ℚ[X]) :=
  Algebra.Smooth.prod ℚ ℚ ℚ ℚ[X] ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩

/-- **The fibres of the witness are geometrically irreducible.** `Spec (ℚ × ℚ[X])` is the
disjoint union of `Spec ℚ` and `Spec ℚ[X]` over the disjoint union `Spec (ℚ × ℚ)` of two copies
of `Spec ℚ`, and geometric irreducibility, being Zariski-local at the target, is checked on the
two pieces: `ℚ` and `ℚ[X]` are both geometrically irreducible over `ℚ`. -/
public theorem geometricallyIrreducible :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])))) := by
  have : IsZariskiLocalAtTarget @GeometricallyIrreducible := by
    rw [GeometricallyIrreducible.eq_geometrically]; infer_instance
  rw [show (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])) = (algebraMap ℚ ℚ).prodMap (algebraMap ℚ ℚ[X]) from
    RingHom.algebraMap_toAlgebra _]
  exact IsZariskiLocalAtTarget.specMap_prodMap _ _
    (Algebra.isGeometricallyIrreducible_self ℚ) (Algebra.isGeometricallyIrreducible_polynomial ℚ)

/-- A prime of `ℚ × ℚ[X]` contracting to `Ideal.prod ⊥ ⊤` is `Ideal.prod ⊥ ⊤` itself: by the
classification of primes of a product ring it is `Ideal.prod p ⊤` for a prime `p` of `ℚ`, which
has to be `⊥`, the alternative `Ideal.prod ⊤ p` contracting to an ideal containing `(1, 0)`. -/
public theorem eq_prod_bot_top_of_comap_eq (q : Ideal (ℚ × ℚ[X])) [hq : q.IsPrime]
    (h : Ideal.comap (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])) q = Ideal.prod ⊥ ⊤) :
    q = Ideal.prod ⊥ ⊤ := by
  rcases (Ideal.ideal_prod_prime q).mp hq with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · congr 1
    exact (Ideal.eq_bot_or_top p).resolve_right hp.ne_top
  · exfalso
    have hmem : ((1 : ℚ), (0 : ℚ)) ∈
        Ideal.comap (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])) (Ideal.prod ⊤ p) := by
      simp [Ideal.mem_comap, Ideal.mem_prod, algebraMap_apply]
    rw [h] at hmem
    simp [Ideal.mem_prod] at hmem

/-- The maximal ideal `Ideal.prod ⊥ ⊤` of `ℚ × ℚ[X]` contracts to `Ideal.prod ⊥ ⊤`, so it lies
in the fibre over that point of `Spec (ℚ × ℚ)`. -/
public theorem comap_prod_bot_top :
    Ideal.comap (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])) (Ideal.prod ⊥ ⊤) = Ideal.prod ⊥ ⊤ := by
  ext r; simp [Ideal.mem_comap, Ideal.mem_prod, algebraMap_apply]

/-- Every prime of the form `Ideal.prod ⊤ q` of `ℚ × ℚ[X]` contracts to `Ideal.prod ⊤ ⊥`: a
constant polynomial lies in a prime of `ℚ[X]` only if it is zero, every nonzero constant being
a unit. -/
public theorem comap_comap_snd (q : Ideal ℚ[X]) [hq : q.IsPrime] :
    Ideal.comap (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])) (Ideal.comap (RingHom.snd ℚ ℚ[X]) q)
      = Ideal.prod ⊤ ⊥ := by
  ext r
  simp only [Ideal.mem_comap, Ideal.mem_prod, algebraMap_apply, RingHom.coe_snd, Ideal.mem_bot,
    Submodule.mem_top, true_and]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra hne
  exact hq.ne_top (q.eq_top_of_isUnit_mem h (Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hne)))

/-- **The fibre over `Ideal.prod ⊥ ⊤` is zero-dimensional.** It is the single point
`Ideal.prod ⊥ ⊤` of `Spec (ℚ × ℚ[X])`, and a nonempty subsingleton space has Krull
dimension `0`. -/
public theorem topologicalKrullDim_fibrePoint :
    topologicalKrullDim
      ↥(PrimeSpectrum.comap (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])) ⁻¹'
        {(⟨Ideal.prod ⊥ ⊤, Ideal.isPrime_ideal_prod_top⟩ : PrimeSpectrum (ℚ × ℚ))}) = 0 := by
  set S := PrimeSpectrum.comap (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])) ⁻¹'
    {(⟨Ideal.prod ⊥ ⊤, Ideal.isPrime_ideal_prod_top⟩ : PrimeSpectrum (ℚ × ℚ))}
  have hmem (x : S) : (x : PrimeSpectrum (ℚ × ℚ[X])).asIdeal = Ideal.prod ⊥ ⊤ :=
    eq_prod_bot_top_of_comap_eq _ (congrArg PrimeSpectrum.asIdeal x.2)
  have : Subsingleton S :=
    ⟨fun a b => Subtype.ext (PrimeSpectrum.ext ((hmem a).trans (hmem b).symm))⟩
  have : Nonempty S :=
    ⟨⟨⟨Ideal.prod ⊥ ⊤, Ideal.isPrime_ideal_prod_top⟩, PrimeSpectrum.ext comap_prod_bot_top⟩⟩
  have : T2Space S := ⟨fun x y hxy => absurd (Subsingleton.elim x y) hxy⟩
  exact topologicalKrullDim_eq_zero_of_t2Space _

/-- The affine line inside the fibre over `Ideal.prod ⊤ ⊥`, given by contracting along the
second projection `RingHom.snd ℚ ℚ[X]`. -/
public noncomputable def lineToFibreLine : PrimeSpectrum ℚ[X] →
    ↥(PrimeSpectrum.comap (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])) ⁻¹'
      {(⟨Ideal.prod ⊤ ⊥, Ideal.isPrime_ideal_prod_top'⟩ : PrimeSpectrum (ℚ × ℚ))}) := fun q =>
  ⟨PrimeSpectrum.comap (RingHom.snd ℚ ℚ[X]) q, PrimeSpectrum.ext (comap_comap_snd q.asIdeal)⟩

/-- `Algebra.PointAndAffineLine.lineToFibreLine` is inducing: composed with the inclusion of the
fibre it is `PrimeSpectrum.comap` of the surjection `RingHom.snd ℚ ℚ[X]`, a closed embedding. -/
public theorem isInducing_lineToFibreLine : Topology.IsInducing lineToFibreLine :=
  Topology.IsInducing.of_comp ((PrimeSpectrum.continuous_comap _).subtype_mk _)
    continuous_subtype_val
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ Prod.snd_surjective).isInducing

/-- **The fibre over `Ideal.prod ⊤ ⊥` has dimension at least one.** It contains `Spec ℚ[X]` as a
subspace, and `dim (Spec ℚ[X]) = dim ℚ + 1 = 1`. -/
public theorem one_le_topologicalKrullDim_fibreLine : (1 : WithBot ℕ∞) ≤ topologicalKrullDim
    ↥(PrimeSpectrum.comap (algebraMap (ℚ × ℚ) (ℚ × ℚ[X])) ⁻¹'
      {(⟨Ideal.prod ⊤ ⊥, Ideal.isPrime_ideal_prod_top'⟩ : PrimeSpectrum (ℚ × ℚ))}) := by
  have hline : topologicalKrullDim (PrimeSpectrum ℚ[X]) = 1 := by
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    rfl
  exact hline ▸ isInducing_lineToFibreLine.topologicalKrullDim_le

end Algebra.PointAndAffineLine

namespace Algebra

open Algebra.PointAndAffineLine in
/-- **The relative dimension of a smooth algebra with geometrically irreducible fibres does not
compute the dimension of every fibre.** `Algebra.relativeDimension R B` is one supremum, while
the fibre dimension of a smooth morphism is only locally constant on `Spec R`: for
`R = ℚ × ℚ` and `B = ℚ × ℚ[X]` the two fibres are nonempty of dimensions `0` and at least `1`,
so no single value equals both.

This refutes the algebra ⇒ geometry direction of the dictionary of Stacks 05I0 (2); see the
module docstring. -/
public theorem not_forall_relativeDimension_eq_topologicalKrullDim_fiber :
    ¬ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], Algebra.Smooth R B →
        GeometricallyIrreducible (Spec.map (ofHom (algebraMap R B))) →
        ∀ 𝔭 : PrimeSpectrum R,
          topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R B) ⁻¹' {𝔭}) =
            Algebra.relativeDimension R B := by
  let := Algebra.PointAndAffineLine.algebra
  intro h
  have h' := h (ℚ × ℚ) (ℚ × ℚ[X]) smooth geometricallyIrreducible
  have hpoint := h' ⟨Ideal.prod ⊥ ⊤, Ideal.isPrime_ideal_prod_top⟩
  have hline := h' ⟨Ideal.prod ⊤ ⊥, Ideal.isPrime_ideal_prod_top'⟩
  rw [topologicalKrullDim_fibrePoint] at hpoint
  have hone := one_le_topologicalKrullDim_fibreLine
  rw [hline, ← hpoint] at hone
  exact absurd hone (by simp)

end Algebra

end
