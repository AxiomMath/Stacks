module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Scheme.Zariski.StandardOpenCover

/-!
# Standard affine open covers and relative pseudo-coherence

Stacks 09VE says that, for a finite-type morphism of affine schemes `f : X ⟶ S`, the condition of
Stacks 09VC holds for `(X ⟶ S, E)` if and only if it holds for `(U ⟶ S, E|_U)` for every member
`U` of a standard affine open cover of `X`. This file collects the part of that statement which
is independent of pseudo-coherence: the dictionary between a standard open cover of
`Spec Γ(X, ⊤)` and a cover of `X` by basic opens, the partition of unity it provides, and the
presentations of `X` and of the members of the cover by closed immersions into affine spaces over
`S`, in the shapes the source's argument uses.

## Main results

* `AlgebraicGeometry.Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top`: for an
  affine scheme `X`, a finite family of global sections is a standard open cover of
  `Spec Γ(X, ⊤)` exactly when the basic opens it defines cover `X`.
* `PrimeSpectrum.IsStandardOpenCoverOfSpectrum.exists_sum_mul_eq_one`: the covering elements of a
  standard open cover of a spectrum admit a dual family summing to one — the relation
  `1 = ∑ fᵢgᵢ` the proof of Stacks 09VE writes down.
* `AlgebraicGeometry.exists_isClosedImmersion_affineSpace_basicOpen_ι_comp`: each member of the
  cover admits a closed immersion into an affine space over `S` factoring its map to `S`, which
  is the shape of clause (1) of Stacks 09VE.
* `AlgebraicGeometry.exists_isClosedImmersion_affineSpace_of_isStandardOpenCoverOfSpectrum`: a
  closed immersion of `X` into an affine space over `S` whose coordinates include both the
  covering elements and their dual family — the surjection
  `R[xᵢ, yᵢ, zᵢ] → A`, `yᵢ ↦ fᵢ`, `zᵢ ↦ gᵢ` with which the proof of Stacks 09VE begins.

## Implementation notes

The dictionary is proved by routing both sides through the unit ideal: a family of standard opens
covers `Spec R` exactly when the family generates the unit ideal
(`PrimeSpectrum.iSup_basicOpen_eq_top_iff`), and the same holds for the basic opens of an affine
scheme (`AlgebraicGeometry.IsAffineOpen.iSup_basicOpen_eq_self_iff` at the top open). No
homeomorphism between `X` and `Spec Γ(X, ⊤)` has to be exhibited.

The basic opens of an affine scheme are affine opens, so the members of the cover are affine and
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_ι_comp` applies to them directly.

What remains for Stacks 09VE itself is the mathematical content of the source's argument: the
intermediate scheme `T = Spec R[xᵢ, yᵢ, zᵢ]/(∑ yᵢzᵢ - 1)` through which the presentation above
factors, pseudo-coherence of that quotient as a module over the polynomial ring, the cover of `T`
by the opens `D(y_{i₀})` — each isomorphic to an affine space over `S` — and the transport of
`m`-pseudo-coherence along the closed immersion `X ⟶ T` (Stacks 09VA). The last of those rests on
the theory of pseudo-coherent complexes on a ringed space (Stacks 08CD, 08DN, 08E7), of which
this library currently has only the definitions, in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/SheafLevel.lean`. The implication (2) ⇒ (1) of
Stacks 09VE is Stacks 09VD, which is blocked on the same lemma.

## References

* [The Stacks Project, Lemma 36.61.5 (09VE)](https://stacks.math.columbia.edu/tag/09VE)
* [The Stacks Project, Lemma 36.61.4 (09VD)](https://stacks.math.columbia.edu/tag/09VD)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 10.17.2 (01HT)](https://stacks.math.columbia.edu/tag/01HT)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial TopologicalSpace

universe u

namespace PrimeSpectrum

/-- The elements of a standard open cover of a prime spectrum admit a dual family summing to one:
covering `Spec R` means generating the unit ideal, so `1` is a combination of the covering
elements. -/
public theorem IsStandardOpenCoverOfSpectrum.exists_sum_mul_eq_one {R : Type u} [CommRing R]
    {n : ℕ} {g : Fin n → R} (hg : IsStandardOpenCoverOfSpectrum g) :
    ∃ h : Fin n → R, ∑ j, g j * h j = 1 := by
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    simpa [IsStandardOpenCoverOfSpectrum, IsStandardOpenCover] using hg
  obtain ⟨c, hc⟩ :=
    Ideal.mem_span_range_iff_exists_fun.mp (hspan ▸ Submodule.mem_top (x := (1 : R)))
  exact ⟨c, by simpa [mul_comm] using hc⟩

end PrimeSpectrum

namespace AlgebraicGeometry

/-- For an affine scheme `X`, a finite family of global sections is a standard open cover of
`Spec Γ(X, ⊤)` exactly when the basic opens it defines cover `X`. Both sides say that the family
generates the unit ideal of `Γ(X, ⊤)`. -/
public theorem Scheme.isStandardOpenCoverOfSpectrum_iff_iSup_basicOpen_eq_top
    {X : Scheme.{u}} [IsAffine X] {n : ℕ} (g : Fin n → Γ(X, ⊤)) :
    PrimeSpectrum.IsStandardOpenCoverOfSpectrum g ↔ (⨆ j, X.basicOpen (g j)) = ⊤ := by
  rw [PrimeSpectrum.IsStandardOpenCoverOfSpectrum, PrimeSpectrum.IsStandardOpenCover,
    PrimeSpectrum.basicOpen_one, PrimeSpectrum.iSup_basicOpen_eq_top_iff,
    ← (isAffineOpen_top X).iSup_basicOpen_eq_self_iff (s := Set.range g), iSup_range']

/-- **The shape of clause (1) of Stacks 09VE.** For a morphism `f : X ⟶ S` of affine schemes
locally of finite type and a global section `a` of `X`, the basic open `X_a` admits a closed
immersion into an affine space over `S` factoring the composite `X_a ⟶ X ⟶ S`.

The basic open of an affine scheme is an affine open, so this is
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_ι_comp` applied to it. -/
public theorem exists_isClosedImmersion_affineSpace_basicOpen_ι_comp {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f] (a : Γ(X, ⊤)) :
    ∃ (k : ℕ) (i : (X.basicOpen a).toScheme ⟶ AffineSpace (ULift.{u} (Fin k)) S),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = (X.basicOpen a).ι ≫ f :=
  exists_isClosedImmersion_affineSpace_ι_comp f ⟨X.basicOpen a, (isAffineOpen_top X).basicOpen a⟩

/-- **The presentation the proof of Stacks 09VE begins with.** Given a standard affine open cover
of an affine scheme `X` by the basic opens of `g : Fin n → Γ(X, ⊤)` and a morphism `f : X ⟶ S`
locally of finite type to an affine scheme, there are a dual family `h` with `∑ gⱼhⱼ = 1` and a
closed immersion of `X` into an affine space over `S` factoring `f` whose coordinates include
both families.

This is the surjection `R[xᵢ, yᵢ, zᵢ] → A` sending `yᵢ` to `fᵢ` and `zᵢ` to `gᵢ`: the `xᵢ` are
the coordinates indexed by the left summand, the `yᵢ` and `zᵢ` those indexed by the two halves of
the right summand. The relation `∑ yᵢzᵢ - 1` lies in the kernel precisely because `∑ gⱼhⱼ = 1`. -/
public theorem exists_isClosedImmersion_affineSpace_of_isStandardOpenCoverOfSpectrum
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    {n : ℕ} (g : Fin n → Γ(X, ⊤)) (hg : PrimeSpectrum.IsStandardOpenCoverOfSpectrum g) :
    ∃ (k : ℕ) (h : Fin n → Γ(X, ⊤))
      (i : X ⟶
        AffineSpace (ULift.{u} (Fin k) ⊕ (ULift.{u} (Fin n) ⊕ ULift.{u} (Fin n))) S),
      (∑ j, g j * h j = 1) ∧ IsClosedImmersion i ∧
        i ≫ (AffineSpace.over
            (ULift.{u} (Fin k) ⊕ (ULift.{u} (Fin n) ⊕ ULift.{u} (Fin n))) S).hom = f ∧
          (∀ j, i.appTop (AffineSpace.coord S (Sum.inr (Sum.inl ⟨j⟩))) = g j) ∧
          (∀ j, i.appTop (AffineSpace.coord S (Sum.inr (Sum.inr ⟨j⟩))) = h j) := by
  obtain ⟨h, hh⟩ := hg.exists_sum_mul_eq_one
  obtain ⟨k, i, hi, hover, hcoord⟩ :=
    AffineSpace.exists_isClosedImmersion_containing f
      (Sum.elim (fun b : ULift.{u} (Fin n) => g b.down) fun b : ULift.{u} (Fin n) => h b.down)
  exact ⟨k, h, i, hh, hi, hover, fun j => hcoord (Sum.inl ⟨j⟩), fun j => hcoord (Sum.inr ⟨j⟩)⟩

end AlgebraicGeometry

end
