module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantFibrePrimeSpectrum

/-!
# Finiteness of the fibres of the quotient morphism to the invariant spectrum

Let `G` be a groupoid scheme with `U`, `R` affine and `s`, `t` finite locally free, write `C` for
its ring of invariant functions and `q : U ⟶ M = Spec C` for the quotient morphism. Then every
fibre of `q` is a **finite** set of points.

This is the sentence "the fibres `U_p` and `U'_{p'}` are finite sets of points" which opens the
proof of the "Claim" of [Stacks Project, Tag 0DT9], and it is the finiteness hypothesis `hfin`
of `bijective_quotientMapₐ_of_bijective_comapRestrict` and of
`exists_algEquiv_prod_of_etale_of_bijective_comapRestrict`.

The argument is the source text's: `s` is finite locally free, so the fibre `s⁻¹(u)` over a point
`u` of `U` is a finite set; and by Tag 03BL the fibre of `q` through `u` is exactly the set of
targets of the arrows out of `u`, so it is the image of that finite set.

## Main results

* `AlgebraicGeometry.GroupoidScheme.finite_fibre_source`: the fibre of the source map over a
  point of the object scheme is finite.
* `AlgebraicGeometry.GroupoidScheme.finite_fibre_objectsToInvariantSpectrum`: **every fibre of
  `q : U ⟶ Spec C` is finite.**
* `AlgebraicGeometry.GroupoidScheme.finite_primes_invariantFibreIdeal`: the same, read as the
  primes of `Γ(U, ⊤)` above the fibre ideal of a closed point — which is the shape the splitting
  criterion of `StacksFrontier.RingTheory.Henselian.Pair.EtaleSplittingFibre` asks for.

## Implementation notes

Finiteness of `s⁻¹(u)` is read off at the level of rings, through
`AlgebraicGeometry.Scheme.carrierEquivPrimeSpectrum`: `Γ(R, ⊤)` is a finite module over
`Γ(U, ⊤)` along the source map, hence quasi-finite, and
`Algebra.QuasiFinite.finite_comap_preimage_singleton` bounds the fibres of the contraction map.
Going through the carrier equivalence rather than through a scheme-theoretic fibre keeps the
whole argument inside the affine picture the rest of this directory works in.

The surjection onto the fibre of `q` is defined only after a point `u₀` of that fibre has been
chosen, which is possible because `q` is surjective; for the empty fibre there is nothing to
prove, and indeed no fibre is empty.

## References

* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-- **The fibre of the source map over a point of the object scheme is finite.** The source map
is finite locally free, so the ring of global functions on the arrow scheme is a finite module
over the one on the object scheme, hence quasi-finite, and the fibres of a quasi-finite algebra
are finite. -/
theorem finite_fibre_source (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left] (u : G.objects.left) :
    Finite {r : G.arrows.left // G.source.left.base r = u} := by
  let : Algebra Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) :=
    G.source.left.appTop.hom.toAlgebra
  have : IsFinite G.source.left :=
    ((isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      G.source.left).mp inferInstance).1
  have : Module.Finite Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤) :=
    G.source.left.finite_appTop
  have hfin := Algebra.QuasiFinite.finite_comap_preimage_singleton
    (R := Γ(G.objects.left, ⊤)) (S := Γ(G.arrows.left, ⊤))
    (G.objects.left.carrierEquivPrimeSpectrum u)
  have : Finite (PrimeSpectrum.comap
      (algebraMap Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤)) ⁻¹'
      {G.objects.left.carrierEquivPrimeSpectrum u}) := hfin
  refine Finite.of_injective (β := PrimeSpectrum.comap
      (algebraMap Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤)) ⁻¹'
      {G.objects.left.carrierEquivPrimeSpectrum u})
    (fun r => ⟨G.arrows.left.carrierEquivPrimeSpectrum r.1, ?_⟩) ?_
  · show PrimeSpectrum.comap (algebraMap Γ(G.objects.left, ⊤) Γ(G.arrows.left, ⊤))
      (G.arrows.left.carrierEquivPrimeSpectrum r.1) =
        G.objects.left.carrierEquivPrimeSpectrum u
    rw [RingHom.algebraMap_toAlgebra,
      ← Scheme.carrierEquivPrimeSpectrum_naturality G.source.left r.1, r.2]
  · intro a b hab
    exact Subtype.ext (G.arrows.left.carrierEquivPrimeSpectrum.injective
      (congrArg Subtype.val hab))

/-- **Every fibre of the quotient morphism `q : U ⟶ Spec C` is a finite set of points.**

Pick a point `u₀` of the fibre, which exists because `q` is surjective. By Tag 03BL a point of
`U` has the same image as `u₀` exactly when it is the target of an arrow with source `u₀`, so the
fibre is the image of the fibre `s⁻¹(u₀)`, which is finite. -/
theorem finite_fibre_objectsToInvariantSpectrum (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] (p : Spec (.of (invariantRing G))) :
    Finite {u : G.objects.left // (objectsToInvariantSpectrum G).base u = p} := by
  obtain ⟨u₀, hu₀⟩ := surjective_objectsToInvariantSpectrum G p
  have := finite_fibre_source G u₀
  have hwd : ∀ r : G.arrows.left, G.source.left.base r = u₀ →
      (objectsToInvariantSpectrum G).base (G.target.left.base r) = p := by
    intro r hr
    have h : (objectsToInvariantSpectrum G).base (G.target.left.base r) =
        (objectsToInvariantSpectrum G).base (G.source.left.base r) := by
      show (G.target.left ≫ objectsToInvariantSpectrum G).base r =
        (G.source.left ≫ objectsToInvariantSpectrum G).base r
      rw [source_comp_objectsToInvariantSpectrum]
    rw [h, hr, hu₀]
  refine Finite.of_surjective
    (α := {r : G.arrows.left // G.source.left.base r = u₀})
    (fun r => (⟨G.target.left.base r.1, hwd r.1 r.2⟩ :
      {u : G.objects.left // (objectsToInvariantSpectrum G).base u = p})) ?_
  intro v
  obtain ⟨r, hrt, hrs⟩ := (base_objectsToInvariantSpectrum_eq_iff G v.1 u₀).mp
    (by rw [v.2, hu₀])
  exact ⟨⟨r, hrs⟩, Subtype.ext hrt⟩

/-- **The primes of `Γ(U, ⊤)` above the fibre ideal of a closed point of `Spec C` form a finite
set.** This is `finite_fibre_objectsToInvariantSpectrum` in the shape the splitting criterion
`bijective_quotientMapₐ_of_bijective_comapRestrict` asks for: the fibre over a closed point is the
zero locus of the fibre ideal. -/
theorem finite_primes_invariantFibreIdeal (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] (p : Spec (.of (invariantRing G)))
    (hp : p.asIdeal.IsMaximal) :
    Finite {x : PrimeSpectrum Γ(G.objects.left, ⊤) // invariantFibreIdeal G p ≤ x.asIdeal} := by
  have := finite_fibre_objectsToInvariantSpectrum G p
  exact Finite.of_equiv _ ((invariantFibreEquivPrimeSpectrum G p).trans
    (Equiv.subtypeEquivRight fun x => PrimeSpectrum.comap_eq_iff_radical_map_le _ hp x))

end AlgebraicGeometry.GroupoidScheme

end

end
