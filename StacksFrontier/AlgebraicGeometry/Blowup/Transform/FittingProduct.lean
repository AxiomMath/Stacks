module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingFlatten
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Summands
import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback

/-!
# Blowing up the product of the Fitting ideals of a module vanishing on an open

Let `ℱ` be a finitely presented `𝒪_X`-module on a scheme `X` which vanishes on an open
`U ⊆ X`. Stacks tag 0ESU produces a `U`-admissible blowup `b : X' ⟶ X` after which `b^*ℱ`
carries two canonical locally finite filtrations whose graded pieces are finite locally free of
rank `i` on a family of effective Cartier divisors `D_i ⊆ X'`. Its proof has two steps: first
blow up the product of the Fitting ideals `Fit_k(ℱ)`, `k ≥ 0`, which makes every Fitting ideal
of the pullback an effective Cartier divisor `E_k`; then build the `D_i` and the two filtrations
locally out of the `E_k`, by induction on the number of generators of a local presentation.

This file carries out the first step, for the product of the Fitting ideals of index at most a
given bound `N`. The blowup and its structure morphism are definitions, so the blowup travels as
data: `X' = blowUp (fittingIdealProd ℱ N)` and `b = blowUpToBase (fittingIdealProd ℱ N)`.

## Main definitions

* `AlgebraicGeometry.fittingIdealProd`: the product `∏_{k ≤ N} Fit_k(ℱ)` of the Fitting ideal
  sheaves of index at most `N`.

## Main results

* `AlgebraicGeometry.isAdmissibleBlowup_blowUpToBase_fittingIdealProd`: the blowup of `X` in
  that product is a `U`-admissible blowup.
* `AlgebraicGeometry.isEffectiveCartierDivisor_fittingIdeal_pullback_fittingIdealProd`: on that
  blowup, each Fitting ideal of index at most `N` of the pulled back module cuts out an
  effective Cartier divisor.
* `AlgebraicGeometry.fittingIdeal_quotient_span_singleton_sq`: for a nonunit nonzerodivisor `g`
  the module `(R ⧸ g)²` has zeroth Fitting ideal `(g²)` and first Fitting ideal `(g)`, so the
  divisors produced above are proper and nonempty rather than empty or everything.

## Implementation notes

**The hypothesis `ℱ|_U = 0`.** It is spelled as finite local freeness of `ℱ|_U` of rank `0`,
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`, which is the form the neighbouring
Fitting material of tags 0ESN and 0EST is stated in; a module is finite locally free of rank `0`
exactly when it vanishes. In that form the Fitting criterion of tag 0C3G applies directly and
gives `Fit_k(ℱ|_U) = 𝒪_U` for every `k ≥ 0`, which is what makes the centre of the blowup avoid
`U`. The bridge from the source's own `CategoryTheory.Limits.IsZero` is
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_zero_of_isZero`, and
`StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingProductAll` states the conclusion in that
form.

**Perfectness is not used.** Tag 0ESU assumes `ℱ` perfect of Tor dimension at most one, which
makes it finitely presented. Only finite presentation enters the statements below, so they are
stated with that hypothesis alone; this generalizes, rather than weakens, the first step of the
source.

**Why a bound `N`.** The source blows up the product of `Fit_k(ℱ)` over all `k ≥ 0`, which makes
sense because locally `Fit_k(ℱ) = 𝒪` once `k` exceeds the number of generators of a local
presentation, so the family is locally finite. The repository has no product of a locally finite
family of quasi-coherent ideal sheaves — only `Finset` products, through
`Stacks.Blowup.isFiniteType_prod` and `Stacks.Blowup.disjoint_support_prod` — and no statement
that the Fitting ideals of a finitely presented module are eventually the unit ideal. The blowup
here therefore depends on a bound `N` and the conclusion is about the Fitting ideals of index at
most `N`.

Both of those are now supplied in
`StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingProductAll`
(`AlgebraicGeometry.exists_forall_fittingIdeal_ideal_eq_top` and
`AlgebraicGeometry.fittingIdealProdAllDiff`), and the blowup good for all `k ≥ 0` at once —
which is the blowup of the source — is
`AlgebraicGeometry.isAdmissibleBlowup_blowUpToBase_fittingIdealProdAll` there. The bounded
statements below are kept because they are what the Fitting material of the neighbouring tags
consumes.

**What of tag 0ESU is not here.** Neither of the two filtrations, and none of the divisors `D_i`.
The `D_i` are determined by the divisors `E_k` of this file through
`E_k = D_{k+1} + 2 D_{k+2} + 3 D_{k+3} + ⋯`, whose solution `D_{k+1} = E_k - 2E_{k+1} + E_{k+2}`
is an effective Cartier divisor only by the local induction of the source; that induction rests
on the local normal form of tag 00MT and on the two canonical short exact sequences
`0 → 𝒪_{D_n}^{⊕n} → ℱ → ℱ' → 0` and `0 → ℱ' → ℱ → 𝒪_{D_n}^{⊕n} → 0` arising from the two
factorizations `A = A'f = fA'` of a local presentation matrix.

Those two sequences are formalized, at the ring level and for a presentation matrix `A = f A'`
over a commutative ring, in `StacksFrontier.RingTheory.Fitting.ScaledPresentation`:
`Stacks.ScaledPresentation.shortExact_ofFree_toBase` and
`Stacks.ScaledPresentation.shortExact_ofBase_toFree`, each with the canonicity statement
identifying the submodule with `Ker(f : ℱ → ℱ)` and the quotient with `Coker(f : ℱ → ℱ)`; the
scaling identity `Fit_k(ℱ) = (f)^{n-k} Fit_k(ℱ')` is
`Stacks.ScaledPresentation.fittingIdeal_cokernel_smul` there, the factorization `A = f A'` itself
is produced by `Stacks.ScaledPresentation.exists_eq_smul_of_fittingIdeal_eq_span_singleton`, and
the whole local step is
`Stacks.ScaledPresentation.exists_eq_smul_and_shortExact`. What is still missing is the
globalization of all of that to a scheme, the step of the induction that drops `n` by one —
Algebra, Lemma 10.102.2 (tag 00MT) applied to a matrix whose entries generate the unit ideal,
which is
`Stacks.ScaledPresentation.fittingIdeal_cokernel_eq_top_of_fittingIdeal_smul_eq_span_singleton`
— the divisors `D_i`, and the filtrations themselves.

**Non-degeneracy of what is proved.** The divisors are not forced to be empty and the blowup is
not forced to be trivial. By tag 0H73 (`fittingIdeal_quotient_and_prod`) the zeroth Fitting ideal
of `R ⧸ I` is `I` for an arbitrary ideal `I`, so `Fit_0(ℱ)` can be any finitely generated ideal,
in particular one that is not locally principal and hence not already an effective Cartier
divisor: the blowup does work. And `fittingIdeal_quotient_span_singleton_sq` exhibits, for a
nonunit nonzerodivisor `g`, a module whose divisors `E_0` and `E_1` are the nonempty effective
Cartier divisors cut out by `g²` and `g`.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 0C3D](https://stacks.math.columbia.edu/tag/0C3D)
* [Stacks Project, Tag 0C3E](https://stacks.math.columbia.edu/tag/0C3E)
* [Stacks Project, Tag 0C3G](https://stacks.math.columbia.edu/tag/0C3G)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 07ZV](https://stacks.math.columbia.edu/tag/07ZV)
* [Stacks Project, Tag 0H73](https://stacks.math.columbia.edu/tag/0H73)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (F : X.Modules)

/-- The product of the Fitting ideal sheaves of `ℱ` of index at most `N`. This is the centre of
the blowup of tag 0ESU, cut off at `N`. -/
abbrev fittingIdealProd (N : ℕ) : X.IdealSheafData :=
  ∏ k ∈ Finset.range (N + 1), fittingIdeal F (k : ℤ)

/-- Every Fitting ideal of nonnegative index restricts to the unit ideal on an open where the
module is finite locally free of rank zero, that is, where it vanishes. -/
theorem fittingIdeal_comap_eq_top_of_rank_zero [F.IsFiniteType] [F.IsQuasicoherent]
    (U : X.Opens)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) 0) (k : ℕ) :
    (fittingIdeal F (k : ℤ)).comap U.ι = ⊤ := by
  have hft : ((Scheme.Modules.pullback U.ι).obj F).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType U.ι.toLRSHom.toShHom F
  have hqc : ((Scheme.Modules.pullback U.ι).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ U.ι.toLRSHom.toShHom F
      (show F.IsQuasicoherent from inferInstance)
  have hcrit : (∀ j : ℕ, j < 0 →
        fittingIdeal ((Scheme.Modules.pullback U.ι).obj F) (j : ℤ) = ⊥) ∧
      ∀ j : ℕ, 0 ≤ j →
        fittingIdeal ((Scheme.Modules.pullback U.ι).obj F) (j : ℤ) = ⊤ :=
    ((finiteLocallyFreeOfRank_tfae_fittingIdeal
      ((Scheme.Modules.pullback U.ι).obj F) 0).out 1 3).mp hrank
  rw [fittingIdeal_comap U.ι F (k : ℤ)]
  exact hcrit.2 k (Nat.zero_le k)

/-- The support of every Fitting ideal of nonnegative index avoids an open on which the module
vanishes. -/
theorem disjoint_support_fittingIdeal_of_rank_zero [F.IsFiniteType] [F.IsQuasicoherent]
    (U : X.Opens)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) 0) (k : ℕ) :
    Disjoint (U : Set X) ((fittingIdeal F (k : ℤ)).support : Set X) := by
  have hsupp : ((fittingIdeal F (k : ℤ)).comap U.ι).support = ⊥ :=
    (Scheme.IdealSheafData.support_eq_bot_iff
      (I := (fittingIdeal F (k : ℤ)).comap U.ι)).mpr
      (fittingIdeal_comap_eq_top_of_rank_zero F U hrank k)
  rw [Set.disjoint_left]
  intro x hxU hxI
  have hx : (⟨x, hxU⟩ : U.toScheme) ∈ ((fittingIdeal F (k : ℤ)).comap U.ι).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hxI
  rw [hsupp] at hx
  exact hx

/-- The centre of the blowup, the product of the Fitting ideals of index at most `N`, is
supported away from an open on which the module vanishes. -/
theorem disjoint_support_fittingIdealProd [F.IsFiniteType] [F.IsQuasicoherent] (U : X.Opens)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) 0) (N : ℕ) :
    Disjoint (U : Set X) ((fittingIdealProd F N).support : Set X) :=
  Stacks.Blowup.disjoint_support_prod U _ _ fun k _ =>
    disjoint_support_fittingIdeal_of_rank_zero F U hrank k

/-- The product of the Fitting ideals of a finitely presented module is of finite type, each
factor being of finite type by tag 0C3E. -/
theorem isFiniteType_fittingIdealProd [F.IsFinitePresentation] (N : ℕ) :
    (fittingIdealProd F N).IsFiniteType :=
  Stacks.Blowup.isFiniteType_prod _ _ fun k => fittingIdeal_isFiniteType F k

/-- **Stacks Project, Tag 0ESU, the blowup.** For a finitely presented `𝒪_X`-module vanishing on
an open `U`, the blowup of `X` in the product of the Fitting ideals of index at most `N` is a
`U`-admissible blowup: that product is of finite type and supported away from `U`. -/
@[stacks 0ESU "the U-admissible blowup, in the product of the Fitting ideals up to N"]
theorem isAdmissibleBlowup_blowUpToBase_fittingIdealProd [F.IsFinitePresentation] (U : X.Opens)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) 0) (N : ℕ) :
    Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase (fittingIdealProd F N)) := by
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  refine (Stacks.Blowup.isAdmissibleBlowup_iff U _).mpr
    ⟨fittingIdealProd F N, ?_, disjoint_support_fittingIdealProd F U hrank N,
      Iso.refl _, Category.id_comp _⟩
  rw [finitePresentation_subschemeι_iff_isFiniteType]
  exact isFiniteType_fittingIdealProd F N

/-- A factor of a finite product of quasi-coherent ideal sheaves whose inverse image along a
morphism is an effective Cartier divisor has itself an effective Cartier inverse image: the
inverse image of the product is the product of the inverse images, and a summand of an effective
Cartier divisor is one by tag 07ZV. -/
theorem isEffectiveCartierDivisor_comap_of_mem_prod {Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type*}
    (s : Finset ι) (I : ι → X.IdealSheafData)
    (h : Stacks.Divisors.IsEffectiveCartierDivisor ((∏ i ∈ s, I i).comap f))
    {i : ι} (hi : i ∈ s) :
    Stacks.Divisors.IsEffectiveCartierDivisor ((I i).comap f) := by
  classical
  rw [← Finset.mul_prod_erase s I hi, comap_mul] at h
  exact isEffectiveCartierDivisor_left_of_mul _ _ h

/-- **Stacks Project, Tag 0ESU, the effective Cartier divisors.** On the blowup of `X` in the
product of the Fitting ideals of index at most `N`, the `k`-th Fitting ideal of the pulled back
module is an effective Cartier divisor for every `k ≤ N`.

The inverse image of the whole product is the exceptional divisor of the blowup, hence an
effective Cartier divisor by tag 02OS, and each factor of it is one by tag 07ZV; the `k`-th
Fitting ideal of the pullback is the inverse image of the `k`-th Fitting ideal by tag 0C3D. -/
@[stacks 0ESU "the Fitting ideals of index at most N become effective Cartier divisors"]
theorem isEffectiveCartierDivisor_fittingIdeal_pullback_fittingIdealProd
    [F.IsFinitePresentation] (N : ℕ) {k : ℕ} (hk : k ≤ N) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (fittingIdeal ((Scheme.Modules.pullback (blowUpToBase (fittingIdealProd F N))).obj F)
        (k : ℤ)) := by
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  rw [← fittingIdeal_comap (blowUpToBase (fittingIdealProd F N)) F (k : ℤ)]
  refine isEffectiveCartierDivisor_comap_of_mem_prod _ (Finset.range (N + 1))
    (fun j : ℕ => fittingIdeal F (j : ℤ)) ?_ (Finset.mem_range.mpr (by omega))
  exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (fittingIdealProd F N)

/-- The module `(R ⧸ g) × (R ⧸ g)` has zeroth Fitting ideal `(g) * (g)` and first Fitting ideal
`(g)`. For `g` a nonunit nonzerodivisor both are proper and nonzero, so the effective Cartier
divisors cut out by the Fitting ideals of a module vanishing on an open are neither empty nor
all of the scheme. -/
theorem fittingIdeal_quotient_span_singleton_sq {R : Type u} [CommRing R] (g : R) :
    _root_.fittingIdeal (M := (R ⧸ Ideal.span {g}) × (R ⧸ Ideal.span {g})) 0 =
        Ideal.span {g} * Ideal.span {g} ∧
      _root_.fittingIdeal (M := (R ⧸ Ideal.span {g}) × (R ⧸ Ideal.span {g})) 1 =
        Ideal.span {g} := by
  obtain ⟨-, h0, h1⟩ := fittingIdeal_quotient_and_prod (Ideal.span {g}) (Ideal.span {g})
  exact ⟨h0, h1.trans (by simp)⟩

end AlgebraicGeometry

end
