module

public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtension
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence

/-!
# The adic dévissage: from the graded pieces to the adic quotients

Let `X` be a scheme, `𝓘` a quasi-coherent ideal sheaf on `X` and `ℱ` a sheaf of modules. The
filtration `ℱ ⊇ 𝓘 ℱ ⊇ 𝓘 ² ℱ ⊇ ⋯` gives the tower of quotients `ℱ / 𝓘 ⁿ ℱ`, whose successive
layers are

`Ker(ℱ / 𝓘 ⁿ⁺¹ ℱ ⟶ ℱ / 𝓘 ⁿ ℱ) = 𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ`,

the homogeneous pieces of the associated graded module. This file climbs the tower: if the
cohomology of every layer vanishes in a degree, then so does the cohomology of every term of the
tower, and if it vanishes in degree `p + 1` then the tower maps are surjective on `H ᵖ`.

Both statements are paragraph three of the proof of [Stacks, Tag 0D2M]:

> Using the long exact cohomology sequence and the vanishing above we conclude (using induction)
> that `H ᵖ(X, ℱ / 𝔪 ⁿ ℱ ⊗ ℒ ^⊗ d) = 0` for all `p > 0`, `d ≥ d₀` and `n ≥ 0`, and
> `H⁰(X, ℱ / 𝔪 ⁿ ℱ ⊗ ℒ ^⊗ d) ⟶ H⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)` is surjective for all `d ≥ d₀` and
> `n ≥ 1`.

Nothing about the ideal, the module or the scheme is used: the input is only the vanishing on the
layers, so a caller supplies that from wherever it comes — in [Stacks, Tag 0D2M] from part (2)
of [Stacks, Tag 0897] for the associated graded algebra, read on the fibre.

## Main results

* `Stacks.Cohomology.FormalFunctions.isZero_rightDerived_idealPowerQuotient_of_isZero_kernel`:
  if `H ᵖ(X, 𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ) = 0` for every `n`, then `H ᵖ(X, ℱ / 𝓘 ⁿ ℱ) = 0` for every `n`.
* `Stacks.Cohomology.FormalFunctions.epi_rightDerived_map_idealPowerQuotientDrop_of_isZero_kernel`:
  if `H ᵖ⁺¹(X, 𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ) = 0` for every `n`, then
  `H ᵖ(X, ℱ / 𝓘 ᵐ ℱ) ⟶ H ᵖ(X, ℱ / 𝓘 ⁿ ℱ)` is an epimorphism for all `n ≤ m`.

## The two inductions

The layer at `n` sits in the short exact sequence

`0 ⟶ Ker(dₙ) ⟶ ℱ / 𝓘 ⁿ⁺¹ ℱ ⟶ ℱ / 𝓘 ⁿ ℱ ⟶ 0`,  `dₙ = idealPowerQuotientDrop`,

which is short exact because `dₙ` is an epimorphism — it is
`Stacks.Algebraization.idealPowerQuotientMap` on the identity of `ℱ`, and that is an
epimorphism for every epimorphism of modules
(`Stacks.Algebraization.epi_idealPowerQuotientMap`) — so
`CategoryTheory.ShortComplex.shortExact_mk_kernel_ι` applies. The long exact sequence of the
right derived functors of global sections is taken from the δ-functor machinery of
`StacksFrontier/Algebra/Homology/RightDerivedDelta.lean`, which needs no hypothesis on `X` beyond
enough injectives on `X.Modules`.

The first induction starts at `n = 0`, where `𝓘 ⁰ ℱ = ℱ` and the quotient is a zero object
(`AlgebraicGeometry.DeligneTriangle.isIso_idealPowerMultiple_zero_ι`), and steps by
`Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂`: the middle term of a short exact
sequence has vanishing `H ᵖ` once the two outer ones do.

The second induction is on `m` above a fixed `n`, by `Nat.le_induction`. Its base case is the
identity, since `dₙₙ = 𝟙`. Its step factors `d` through one layer —
`d_{n ≤ m+1} = d_{m ≤ m+1} ≫ d_{n ≤ m}`, which holds because both sides agree after the
epimorphism `ℱ ⟶ ℱ / 𝓘 ᵐ⁺¹ ℱ` by `Stacks.Algebraization.idealPowerQuotientDrop_π` — and
observes that `H ᵖ` of a single layer map is an epimorphism: the five-term window of the long
exact sequence at `p` is

`H ᵖ(ℱ / 𝓘 ᵐ⁺¹ ℱ) ⟶ H ᵖ(ℱ / 𝓘 ᵐ ℱ) ⟶ H ᵖ⁺¹(Ker dₘ)`,

whose second map lands in a zero object.

## Implementation notes

Cohomology is `(Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p`, valued in
`Γ(X, ⊤)`-modules; this is the functor `Stacks.Cohomology.FormalFunctions.cohomologyOverBase`
restricts scalars along, and restriction of scalars changes neither carriers nor maps, so both
conclusions transport to `A`-modules — the vanishing by
`CategoryTheory.Functor.map_isZero` and the surjectivity because
`Stacks.Cohomology.FormalFunctions.adicCohomologyTowerMap` is the restriction of the map below.

No declaration is introduced for the layer `𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ`, for the short exact sequence, or
for the epimorphism `dₙ`: they are written out, so that nothing here duplicates the graded
module of [Stacks, Tag 087Z]
(`Stacks.Coherent.AssociatedGradedData.modulePieceSucc`, which identifies the homogeneous piece
of the associated graded module with exactly this kernel) or the short exact sequence
`0 → 𝓘 ⁿ ℱ → ℱ → ℱ / 𝓘 ⁿ ℱ → 0` of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/IdealPowerShortExact.lean`, which is a different
sequence.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Algebraization

variable {X : Scheme.{u}} (J : X.IdealSheafData) (M : X.Modules)

/-- The layer sequence `0 ⟶ Ker(dₙ) ⟶ ℱ / 𝓘 ⁿ⁺¹ ℱ ⟶ ℱ / 𝓘 ⁿ ℱ ⟶ 0` is short exact. -/
private theorem shortExact_kernel_idealPowerQuotientDrop (n : ℕ) :
    (ShortComplex.mk (kernel.ι (idealPowerQuotientDrop J (Nat.le_succ n) M))
      (idealPowerQuotientDrop J (Nat.le_succ n) M) (kernel.condition _)).ShortExact := by
  have : Epi (idealPowerQuotientDrop J (Nat.le_succ n) M) := by
    rw [idealPowerQuotientDrop]; infer_instance
  exact ShortComplex.shortExact_mk_kernel_ι _

/-- **The adic dévissage for vanishing.** If the `p`-th cohomology of every layer
`𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ = Ker(ℱ / 𝓘 ⁿ⁺¹ ℱ ⟶ ℱ / 𝓘 ⁿ ℱ)` of the adic filtration vanishes, then so does
the `p`-th cohomology of every quotient `ℱ / 𝓘 ⁿ ℱ`.

The induction starts at the zero object `ℱ / 𝓘 ⁰ ℱ` and steps along the short exact sequence of
the layer. This is the first half of paragraph three of the proof of [Stacks, Tag 0D2M]; there
`𝓘 = 𝔪 𝒪_X` and `ℱ` is a twist `ℱ ⊗ ℒ ^⊗ d`, and the hypothesis is the vanishing on the fibre
supplied by part (2) of [Stacks, Tag 0897]. -/
public theorem isZero_rightDerived_idealPowerQuotient_of_isZero_kernel (p : ℕ)
    (hgr : ∀ n : ℕ, IsZero (((moduleGlobalSections X).rightDerived p).obj
      (kernel (idealPowerQuotientDrop J (Nat.le_succ n) M))))
    (n : ℕ) :
    IsZero (((moduleGlobalSections X).rightDerived p).obj (idealPowerQuotient J n M)) := by
  have : ((moduleGlobalSections X).rightDerived p).Additive :=
    CategoryTheory.DeltaFunctor.additive (cohomologyDeltaFunctor X) p
  induction n with
  | zero =>
      refine CategoryTheory.Functor.map_isZero _ ?_
      have hiso : IsIso (C := X.Modules) (idealPowerMultiple J 0 M).ι :=
        AlgebraicGeometry.DeligneTriangle.isIso_idealPowerMultiple_zero_ι J M
      have : Epi (C := X.Modules) (idealPowerMultiple J 0 M).ι :=
        @CategoryTheory.IsIso.epi_of_iso X.Modules _ _ _ _ hiso
      exact isZero_cokernel_of_epi (C := X.Modules) (idealPowerMultiple J 0 M).ι
  | succ n ih =>
      exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂
        (shortExact_kernel_idealPowerQuotientDrop J M n)
        (moduleGlobalSections X) p (hgr n) ih

/-- **The adic dévissage for surjectivity.** If the `(p+1)`-st cohomology of every layer
`𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ` of the adic filtration vanishes, then the tower map
`H ᵖ(X, ℱ / 𝓘 ᵐ ℱ) ⟶ H ᵖ(X, ℱ / 𝓘 ⁿ ℱ)` is an epimorphism for every `n ≤ m`.

Each single layer contributes an epimorphism because the long exact sequence continues into
`H ᵖ⁺¹` of the layer, which vanishes; the general tower map is a composite of layer maps. At
`p = 0` and `n = 1` this is the second half of paragraph three of the proof of
[Stacks, Tag 0D2M], the surjectivity that lets sections on the fibre be lifted. -/
public theorem epi_rightDerived_map_idealPowerQuotientDrop_of_isZero_kernel (p : ℕ)
    (hgr : ∀ n : ℕ, IsZero (((moduleGlobalSections X).rightDerived (p + 1)).obj
      (kernel (idealPowerQuotientDrop J (Nat.le_succ n) M))))
    {m n : ℕ} (h : n ≤ m) :
    Epi (((moduleGlobalSections X).rightDerived p).map (idealPowerQuotientDrop J h M)) := by
  -- One layer at a time: the long exact sequence runs into `H ᵖ⁺¹` of the layer, which vanishes.
  have layer : ∀ k : ℕ, Epi (((moduleGlobalSections X).rightDerived p).map
      (idealPowerQuotientDrop J (Nat.le_succ k) M)) := by
    intro k
    obtain ⟨δ, -, hex⟩ :=
      Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅
        (shortExact_kernel_idealPowerQuotientDrop J M k)
        (moduleGlobalSections X)
    exact ((hex p).exact 1).epi_f ((hgr k).eq_of_tgt _ _)
  induction m, h using Nat.le_induction with
  | base =>
      rw [show idealPowerQuotientDrop J (le_refl n) M = 𝟙 (idealPowerQuotient J n M) by
        rw [idealPowerQuotientDrop, idealPowerQuotientMap_id],
        CategoryTheory.Functor.map_id]
      infer_instance
  | succ m hm ih =>
      have hfac : idealPowerQuotientDrop J (Nat.le_succ_of_le hm) M =
          idealPowerQuotientDrop J (Nat.le_succ m) M ≫ idealPowerQuotientDrop J hm M := by
        refine (cancel_epi
          (cokernel.π (C := X.Modules) (idealPowerMultiple J (m + 1) M).ι)).1 ?_
        rw [idealPowerQuotientDrop_π, idealPowerQuotientDrop_π_assoc,
          idealPowerQuotientDrop_π]
      rw [hfac, CategoryTheory.Functor.map_comp]
      exact @epi_comp _ _ _ _ _ _ (layer m) _ ih

end Stacks.Cohomology.FormalFunctions

end
