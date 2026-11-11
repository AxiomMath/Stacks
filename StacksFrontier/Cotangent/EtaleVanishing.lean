module

public import Mathlib.RingTheory.Etale.Weakly
public import StacksFrontier.Cotangent.DiagonalVanishing
public import StacksFrontier.Homology.Tor.Presentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of the cotangent complex for flat epimorphisms and weakly étale maps

Lemma 92.8.4 of the Stacks Project, [Stacks, Tag 08R2], lists nine situations in which the
cotangent complex `L_{B/A}` vanishes. This file proves item (2), `A → B` a flat epimorphism of
rings, outright, and items (1), `A → B` weakly étale (that is `A → B` and `B ⊗_A B → B` both
flat), and (5), `A → B` étale, for a distinguished triangle on the vertices of the diagonal tower
`B → B ⊗_A B → B` given as a parameter `hT`. This file is upstream of Proposition 08QX; the forms
of items (1) and (5) with that triangle supplied by Proposition 08QX, and so with exactly the
source's hypotheses, are in `StacksFrontier.Cotangent.EtaleVanishingUnconditional`.

The source's proof of item (1) is the one carried out here: the multiplication map
`B ⊗_A B → B` is surjective, and flat by assumption, so item (2) applies to it and gives
`L_{B/(B ⊗_A B)} = 0`; flatness of `A → B` gives `Tor^A_i(B, B) = 0` for `i > 0`; and
[Stacks, Tag 08R1] then gives `L_{B/A} = 0`. Items (3), (4) and (5) are special cases of item
(1) in the source, and item (5) is the one deduced here, along Mathlib's instance
`Algebra.Etale → Algebra.WeaklyEtale`.

Item (2) needs no cotangent triangle at all. For a flat epimorphism the map `b ↦ b ⊗ 1` is
bijective, so `L_{(B ⊗_A B)/B} = 0` because the structure map of that algebra is an isomorphism;
flatness makes `B` Tor independent from itself over `A`; and
`CommAlgCat.cotangentComplexDerived_iso_fundamentalVertex₁_diagonal` already identifies `L_{B/A}`
with `L_{(B ⊗_A B)/B} ⊗^𝐋_{(B ⊗_A B)} B`, which is therefore zero. In the source this is the
appeal to [Stacks, Tag 08R0]; here the identification of Tag 08R1's proof is reused instead, so
that no instance of Proposition 08QX is needed.

## Main results

* `CommAlgCat.isZero_cotangentComplexDerived_of_bijective`: `L_{B/A} = 0` when `A → B` is an
  isomorphism.
* `CommAlgCat.isZero_cotangentComplexDerived_of_flat_of_bijective`: **[Stacks, Tag 08R2] item
  (2)**, a flat epimorphism.
* `CommAlgCat.isZero_cotangentComplexDerived_of_flat_of_surjective`: the surjective case of item
  (2), which is what the multiplication map needs.
* `CommAlgCat.isZero_cotangentComplexDerived_of_weaklyEtale`: [Stacks, Tag 08R2] item (1) for a
  given triangle `hT`.
* `CommAlgCat.isZero_cotangentComplexDerived_of_etale`: [Stacks, Tag 08R2] item (5) for a given
  triangle `hT`.

## Implementation notes

*The epimorphism condition.* Item (2) is stated with the hypothesis
`Function.Bijective (algebraMap B (B ⊗[A] B))`, that is, bijectivity of `b ↦ b ⊗ 1`. By
`CommRingCat.epi_tfae` — [Stacks, Tag 04VN], proved in
`StacksFrontier.Algebra.Category.Ring.Epi.Basic` — this is equivalent to
`CategoryTheory.Epi (CommRingCat.ofHom (algebraMap A B))`, to `Algebra.IsEpi A B`, and to
bijectivity of the multiplication map; so the hypothesis is the source's "epimorphism of rings"
and not something weaker. It is spelled as the bijectivity because that is the form in which the
proof consumes it, through
`CommAlgCat.isZero_cotangentComplexDerived_of_bijective` applied to `B → B ⊗_A B`.

*Where the other items are.* Items (1) and (5) with nothing carried are
`CommAlgCat.isZero_cotangentComplexDerived_of_weaklyEtale_unconditional` and
`CommAlgCat.isZero_cotangentComplexDerived_of_etale_unconditional` in
`StacksFrontier.Cotangent.EtaleVanishingUnconditional`. Item (3), a localization, and item (4),
unramified and flat, are `CommAlgCat.isZero_cotangentComplexDerived_of_isLocalization` and
`CommAlgCat.isZero_cotangentComplexDerived_of_unramified_of_flat` in
`StacksFrontier.Cotangent.EtaleVanishingFurtherCases`. Item (6) is
`CommAlgCat.cotangentComplex_isZero_of_filtered_colimit` in
`StacksFrontier.Cotangent.FilteredColimitVanishing`. Items (7) and (8), the (strict) henselizations,
are `IsLocalRing.IsHenselization.isZero_cotangentComplexDerived_unconditional` in
`StacksFrontier.Cotangent.HenselizationUnconditional` and
`CommAlgCat.isZero_cotangentComplexDerived_of_isHenselization_atPrime` in
`StacksFrontier.Cotangent.EtaleVanishingFurtherCases`.

*Tor independence from flatness.* `CommAlgCat.torIndependent_of_flat` restates
`RingTheory.TorIndependence.torIndependent_of_flat_left` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange`. It is repeated here, in
four lines over `isZero_Tor_succ_of_flat`, rather than imported, because that file sits in the
dualizing-complex development and importing it would attach the whole of that development to the
cotangent-complex files.

## References

* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2), Lemma 92.8.4.
* [Stacks Project, Tag 08R1](https://stacks.math.columbia.edu/tag/08R1), used for item (1).
* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH), through
  `CommAlgCat.cotangentComplex_iso_kaehlerDifferential`.
* [Stacks Project, Tag 04VN](https://stacks.math.columbia.edu/tag/04VN), the epimorphism
  condition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

attribute [local instance] diagonalAlgebra

section Vanishing

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- A flat `A`-algebra `B` is Tor independent over `A` from every `A`-algebra `S`: tensoring with
a flat module preserves the exactness of a projective resolution, so `Tor^A_i(B, S)` vanishes in
positive degrees. -/
@[sga "7 VIII 1.2" "special case"]
theorem torIndependent_of_flat (S : Type u) [CommRing S] [Algebra A S] [Module.Flat A B] :
    RingTheory.TorIndependence.TorIndependent A B S := by
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact isZero_Tor_succ_of_flat (ModuleCat.of A B) (ModuleCat.of A S) k

/-- **The cotangent complex of an isomorphism vanishes.** If `algebraMap A B` is bijective then
`B` is a polynomial algebra over `A` on the empty set of variables, so [Stacks, Tag 08QH]
identifies `L_{B/A}` with `Ω[B⁄A][0]`, and `Ω[B⁄A]` is zero because `algebraMap A B` is
surjective. -/
theorem isZero_cotangentComplexDerived_of_bijective (h : Function.Bijective (algebraMap A B)) :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) := by
  have hpoly : CommAlgCat.IsPolynomialAlgebra A (CommAlgCat.of A B) :=
    ⟨PEmpty.{u + 1}, ⟨(MvPolynomial.isEmptyAlgEquiv A PEmpty.{u + 1}).trans
      (AlgEquiv.ofBijective (Algebra.ofId A B) h)⟩⟩
  refine IsZero.of_iso ?_
    (cotangentComplex_iso_kaehlerDifferential A (CommAlgCat.of A B) hpoly).some
  refine (DerivedCategory.singleFunctor _ 0).map_isZero ?_
  have : Subsingleton (KaehlerDifferential A (CommAlgCat.of A B)) :=
    KaehlerDifferential.subsingleton_of_surjective _ _ h.surjective
  exact ModuleCat.isZero_of_subsingleton _

/-- If `algebraMap A B` is surjective then `b ↦ b ⊗ 1` is bijective, so `A → B` is an
epimorphism. Every `b ⊗ b'` is `(b b') ⊗ 1` because `b'` comes from `A`. -/
theorem bijective_algebraMap_tensorProduct_of_surjective
    (h : Function.Surjective (algebraMap A B)) :
    Function.Bijective (algebraMap B (B ⊗[A] B)) := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · have hmul := congrArg (Algebra.TensorProduct.lmul' (S := B) A) hxy
    simpa using hmul
  · induction z with
    | tmul b b' =>
        obtain ⟨a, rfl⟩ := h b'
        refine ⟨algebraMap A B a * b, ?_⟩
        have hb : algebraMap B (B ⊗[A] B) (algebraMap A B a * b) =
            (algebraMap A B a * b) ⊗ₜ[A] (1 : B) := by simp
        rw [hb, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    | add y z hy hz =>
        obtain ⟨x, hx⟩ := hy
        obtain ⟨x', hx'⟩ := hz
        exact ⟨x + x', by rw [map_add, hx, hx']⟩

/-- **[Stacks, Tag 08R2] item (2).** Let `A → B` be a flat epimorphism of rings. Then
`L_{B/A} = 0` in `D(B)`.

The epimorphism condition is bijectivity of `b ↦ b ⊗ 1 : B → B ⊗_A B`, which is item (3) of
`CommRingCat.epi_tfae`; see the module docstring. Flatness gives `Tor^A_i(B, B) = 0` for `i > 0`,
so `CommAlgCat.cotangentComplexDerived_iso_fundamentalVertex₁_diagonal` identifies `L_{B/A}` with
`L_{(B ⊗_A B)/B} ⊗^𝐋_{(B ⊗_A B)} B`; and `L_{(B ⊗_A B)/B}` vanishes because the structure map
`B → B ⊗_A B` is an isomorphism. No cotangent triangle is used. -/
@[stacks 08R2 "item (2) of the lemma, a flat epimorphism of rings: `Module.Flat A B` together \
with bijectivity of `b ↦ b ⊗ 1 : B → B ⊗_A B`, which is item (3) of `CommRingCat.epi_tfae` \
(Stacks 04VN, proved in this library) and is therefore exactly the source's epimorphism \
condition. NOTHING is carried: no instance of Proposition 08QX is assumed. Both hypotheses are \
load-bearing — flatness gives the Tor independence that \
`CommAlgCat.cotangentComplexDerived_iso_fundamentalVertex₁_diagonal` consumes, and the \
epimorphism condition is what makes `L_{(B ⊗_A B)/B}` vanish"]
theorem isZero_cotangentComplexDerived_of_flat_of_bijective [Module.Flat A B]
    (h : Function.Bijective (algebraMap B (B ⊗[A] B))) :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) := by
  refine IsZero.of_iso ?_
    (cotangentComplexDerived_iso_fundamentalVertex₁_diagonal A B (torIndependent_of_flat A B B))
  exact Functor.map_isZero _ (isZero_cotangentComplexDerived_of_bijective B (B ⊗[A] B) h)

/-- **[Stacks, Tag 08R2] item (2) for a surjection.** A surjective flat ring map has vanishing
relative cotangent complex, a surjection being an epimorphism. This is the case the
multiplication map `B ⊗_A B → B` of item (1) falls under. -/
theorem isZero_cotangentComplexDerived_of_flat_of_surjective [Module.Flat A B]
    (h : Function.Surjective (algebraMap A B)) :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) :=
  isZero_cotangentComplexDerived_of_flat_of_bijective A B
    (bijective_algebraMap_tensorProduct_of_surjective A B h)

/-- The multiplication map `B ⊗_A B → B` is surjective. -/
theorem surjective_algebraMap_diagonalAlgebra :
    Function.Surjective (algebraMap (B ⊗[A] B) B) := fun b =>
  ⟨b ⊗ₜ[A] 1, by rw [algebraMap_diagonalAlgebra]; simp⟩

/-- **[Stacks, Tag 08R2] item (1), for a given triangle.** Let `A → B` be weakly étale, that is,
let `A → B` and the multiplication map `B ⊗_A B → B` both be flat, and let `hT` be a
distinguished triangle on the vertices of the tower `B → B ⊗_A B → B`. Then `L_{B/A} = 0` in
`D(B)`. The form with the triangle supplied by Proposition 08QX is
`CommAlgCat.isZero_cotangentComplexDerived_of_weaklyEtale_unconditional`.

The multiplication map is surjective, so item (2) applies to it and gives
`L_{B/(B ⊗_A B)} = 0`; flatness of `A → B` gives `Tor^A_i(B, B) = 0` for `i > 0`; and
[Stacks, Tag 08R1] concludes. The distinguished triangle of Proposition 08QX for the tower
`B → B ⊗_A B → B` is the parameter `hT` of
`CommAlgCat.isZero_cotangentComplexDerived_of_torIndependent` and is passed through. -/
theorem isZero_cotangentComplexDerived_of_weaklyEtale [Algebra.WeaklyEtale A B]
    {α : fundamentalVertex₁.{u, u} B (B ⊗[A] B) B ⟶ fundamentalVertex₂.{u, u} B B}
    {β : fundamentalVertex₂.{u, u} B B ⟶ fundamentalVertex₃.{u, u} (B ⊗[A] B) B}
    {γ : fundamentalVertex₃.{u, u} (B ⊗[A] B) B ⟶
      (fundamentalVertex₁.{u, u} B (B ⊗[A] B) B)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} B))) :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) :=
  have : Module.Flat (B ⊗[A] B) B := Algebra.WeaklyEtale.flat_lmul' A B
  isZero_cotangentComplexDerived_of_torIndependent A B (torIndependent_of_flat A B B) hT
    (isZero_cotangentComplexDerived_of_flat_of_surjective (B ⊗[A] B) B
      (surjective_algebraMap_diagonalAlgebra A B))

/-- **[Stacks, Tag 08R2] item (5), for a given triangle.** If `A → B` is étale then
`L_{B/A} = 0` in `D(B)`, for a distinguished triangle `hT` on the vertices of the tower
`B → B ⊗_A B → B`.

An étale algebra is weakly étale, so this is the instance of item (1). The form with the
triangle supplied by Proposition 08QX is
`CommAlgCat.isZero_cotangentComplexDerived_of_etale_unconditional`. -/
theorem isZero_cotangentComplexDerived_of_etale [Algebra.Etale A B]
    {α : fundamentalVertex₁.{u, u} B (B ⊗[A] B) B ⟶ fundamentalVertex₂.{u, u} B B}
    {β : fundamentalVertex₂.{u, u} B B ⟶ fundamentalVertex₃.{u, u} (B ⊗[A] B) B}
    {γ : fundamentalVertex₃.{u, u} (B ⊗[A] B) B ⟶
      (fundamentalVertex₁.{u, u} B (B ⊗[A] B) B)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α β γ ∈ distTriang (DerivedCategory (ModuleCat.{u} B))) :
    IsZero (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B)) :=
  isZero_cotangentComplexDerived_of_weaklyEtale A B hT

end Vanishing

end CommAlgCat

end
