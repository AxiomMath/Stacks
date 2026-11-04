module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselizationFlatComparisonBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.NilpotentFlatteningInputs
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties

/-!
# The interlude of the proof of Stacks 05U9

Between Claim 1 of the proof of Stacks 05U9 and the three conclusions the source draws from it
there is a paragraph which turns "every prime of `A` contains a flattening ideal" into "some
finitely generated nilpotent ideal of `A` is a flattening ideal". It runs over the henselization
`A^h`, where Stacks 05PG supplies a smallest flattening ideal `I`, and descends the result to `A`
along Stacks 0ASE. This file is that paragraph.

* `Stacks.ResidueFibre.exists_flat_quotient_le_tensorPrime_of_isPrime` carries the covering
  hypothesis from `A` to `A^h`: a prime of `A^h` contracts to a prime of `A`, a flattening ideal
  inside the contraction extends to one inside the prime, and extensions of ideals of `A` are
  flattening for `N' = B' ⊗_B N` over `A^h` exactly when they are flattening for `N` over `A`
  (`Stacks.ResidueFibre.flat_quotient_tensorPrime_iff_flat_quotient`).

* `Stacks.ResidueFibre.exists_fg_isNilpotent_flat_quotient_of_least_tensorPrime` is the paragraph:
  the smallest flattening ideal `I ⊆ A^h` is nilpotent by
  `Stacks.isNilpotent_of_least_flattening`, hence inside the nilradical of `A^h`, which Stacks
  0ASE identifies with the extension of the nilradical of `A`; so
  `Stacks.exists_fg_isNilpotent_le_map` produces a finitely generated nilpotent `I₀ ⊆ A` whose
  extension contains `I`, and minimality makes that extension flattening over `A^h`, which the
  comparison reads back over `A`.

## Main results

* `Stacks.ResidueFibre.exists_flat_quotient_le_tensorPrime_of_isPrime`: the hypothesis `hcover`
  of `Stacks.isNilpotent_of_least_flattening`, over the henselization.
* `Stacks.ResidueFibre.exists_fg_isNilpotent_flat_quotient_of_least_tensorPrime`: a finitely
  generated nilpotent flattening ideal of `A` from a smallest flattening ideal of `A^h`.

## Implementation notes

The smallest flattening ideal over `A^h` is taken as data rather than produced here:
`Module.FlatAtPointSituation.exists_ideal_flat_quotient_iff_le_of_henselian` produces it from
`Stacks.ResidueFibre.flatAtPointSituation`, but its finite generation asks that `A^h → B'` be
essentially of finite presentation, which is a property of the algebra a caller presents rather
than of the henselization. Both halves of what the source uses — the equivalence and the finite
generation — are therefore hypotheses, and the file is about the descent alone.

Stacks 0ASE is stated for a henselization and a strict henselization together, so a strict
henselization is produced inside the proof by
`IsLocalRing.exists_isHenselization_separableClosure`; only the henselization half of its
conclusion is used.

## References

* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
* [Stacks Project, Tag 0ASE](https://stacks.math.columbia.edu/tag/0ASE)
-/

@[expose] public section

universe u v w

open IsLocalRing TensorProduct

namespace Stacks.ResidueFibre

section Descent

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {B : Type v} [CommRing B] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
variable (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
  [IsLocalRing.IsHenselization A (ResidueField A) Ah]

/-- **The hypothesis `hcover` of the proof of Stacks 05U9, over the henselization.** Suppose
every prime of `A` contains an ideal `K` with `N ⧸ KN` flat over `A ⧸ K`. Then every prime of the
henselization `A^h` contains an ideal `K'` with `N' ⧸ K'N'` flat over `A^h ⧸ K'`, where
`N' = B' ⊗_B N` for `B'` the localization of `A^h ⊗_A B` at
`Stacks.ResidueFibre.tensorPrime`.

A prime `𝔮` of `A^h` contracts to a prime of `A`; a flattening ideal `K` inside that contraction
has `K A^h ⊆ 𝔮`, and `K A^h` is flattening for `N'` over `A^h` by
`Stacks.ResidueFibre.flat_quotient_tensorPrime_iff_flat_quotient`. -/
theorem exists_flat_quotient_le_tensorPrime_of_isPrime
    (hcover : ∀ p : Ideal A, p.IsPrime →
      ∃ K : Ideal A, K ≤ p ∧ Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N))))
    (q : Ideal Ah) (hq : q.IsPrime) :
    ∃ K : Ideal Ah, K ≤ q ∧ Module.Flat (Ah ⧸ K)
      ((Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) ⊗[B] N) ⧸
        (K • (⊤ : Submodule Ah
          (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) ⊗[B] N)))) := by
  obtain ⟨K, hKle, hKflat⟩ := hcover (q.comap (algebraMap A Ah)) (hq.comap _)
  exact ⟨K.map (algebraMap A Ah), Ideal.map_le_iff_le_comap.mpr hKle,
    (flat_quotient_tensorPrime_iff_flat_quotient Ah K).mpr hKflat⟩

/-- **The paragraph after Claim 1 in the proof of Stacks 05U9.** Let `I ⊆ A^h` be a finitely
generated ideal which is the smallest flattening ideal of `N' = B' ⊗_B N` over the henselization
`A^h`, and suppose every prime of `A` contains a flattening ideal of `N` over `A`. Then some
finitely generated *nilpotent* ideal `I₀ ⊆ A` has `N ⧸ I₀N` flat over `A ⧸ I₀`.

The covering hypothesis travels to `A^h` by
`Stacks.ResidueFibre.exists_flat_quotient_le_tensorPrime_of_isPrime`, which makes `I` nilpotent
by `Stacks.isNilpotent_of_least_flattening`. A nilpotent ideal lies in the nilradical, which
Stacks 0ASE identifies with the extension of the nilradical of `A`, so
`Stacks.exists_fg_isNilpotent_le_map` produces a finitely generated nilpotent `I₀ ⊆ A` with
`I ⊆ I₀A^h`. Minimality of `I` makes `I₀A^h` flattening over `A^h`, and
`Stacks.ResidueFibre.flat_quotient_tensorPrime_iff_flat_quotient` reads that back over `A`. -/
theorem exists_fg_isNilpotent_flat_quotient_of_least_tensorPrime
    (I : Ideal Ah) (hIfg : I.FG)
    (hI : ∀ K : Ideal Ah, Module.Flat (Ah ⧸ K)
      ((Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) ⊗[B] N) ⧸
        (K • (⊤ : Submodule Ah
          (Localization.AtPrime (tensorPrime (A := A) (B := B) Ah) ⊗[B] N)))) ↔ I ≤ K)
    (hcover : ∀ p : Ideal A, p.IsPrime →
      ∃ K : Ideal A, K ≤ p ∧ Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N)))) :
    ∃ I₀ : Ideal A, I₀.FG ∧ IsNilpotent I₀ ∧
      Module.Flat (A ⧸ I₀) (N ⧸ (I₀ • (⊤ : Submodule A N))) := by
  have hnil : IsNilpotent I :=
    isNilpotent_of_least_flattening I hIfg (fun K hK => (hI K).mp hK)
      (fun q hq => exists_flat_quotient_le_tensorPrime_of_isPrime Ah hcover q hq)
  have hnilrad : I ≤ nilradical Ah :=
    (Ideal.FG.isNilpotent_iff_le_nilradical hIfg).mp hnil
  obtain ⟨Ash, _, _, _, _⟩ :=
    IsLocalRing.exists_isHenselization_separableClosure A
  have h0ASE := (nilradical_map_eq_henselization_and_strictHenselization A Ah Ash
    (SeparableClosure (ResidueField A))).1
  obtain ⟨I₀, hI₀fg, hI₀nil, hI₀le⟩ :=
    exists_fg_isNilpotent_le_map (algebraMap A Ah) hIfg (by rw [h0ASE]; exact hnilrad)
  exact ⟨I₀, hI₀fg, hI₀nil,
    (flat_quotient_tensorPrime_iff_flat_quotient Ah I₀).mp ((hI _).mpr hI₀le)⟩

end Descent

end Stacks.ResidueFibre

namespace Stacks

/-! ### Claim 1 at a single index of the stratification -/

/-- **Claim 1 of the proof of Stacks 05U9 at an index, from flatness over the stratum itself.**
The closure ideal `J` of a stratum contains the ideal `K` cutting out the closed subscheme the
stratum sits in (`Stacks.le_strataClosureIdeal`), so flatness of `N ⧸ KN` over `A ⧸ K` gives
flatness of `N ⧸ JN` over `A ⧸ J` by base change along `A ⧸ K → A ⧸ J`.

This is how the source's induction supplies Claim 1 at an index `i > 0`: the induction hypothesis
over `A ⧸ K_i` delivers flatness of `N ⧸ K_iN`, and Claim 1 at `i` asks for flatness modulo the
larger `J_i`. -/
theorem flat_quotient_strataClosureIdeal_of_flat_quotient {A : Type u} [CommRing A]
    {N : Type v} [AddCommGroup N] [Module A N] (K : Ideal A) {ι : Type w} (g : ι → A)
    (h : Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N)))) :
    Module.Flat (A ⧸ strataClosureIdeal K g)
      (N ⧸ (strataClosureIdeal K g • (⊤ : Submodule A N))) :=
  let := h
  Module.Flat.quotient_smul_top_of_le (le_strataClosureIdeal K g)

namespace FlatStratification

variable {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N] [Module A N] {t : ℕ}

/-- **Claim 1 of the proof of Stacks 05U9 at the last index.** If the closed subscheme
`S_{i+1}` of a stratification is empty, so that `K_{i+1} = ⊤`, then `N ⧸ K_iN` is flat over
`A ⧸ K_i`.

The stratum `S_i ∖ S_{i+1}` is then all of `S_i`, and the flatness clause of the stratification
covers it on the basic open of `1 ∈ K_{i+1}`, whose localization is `A ⧸ K_i` itself. This is the
case the source calls immediate, and `Stacks.flat_quotient_strataClosureIdeal_of_flat_quotient`
turns it into Claim 1 at that index. -/
theorem flat_quotient_ideal_of_succ_eq_top (S : FlatStratification A N t) (i : Fin t)
    (hi : S.ideal i.succ = ⊤) :
    Module.Flat (A ⧸ S.ideal i.castSucc) (N ⧸ (S.ideal i.castSucc • (⊤ : Submodule A N))) := by
  have : IsLocalization.Away
      (Ideal.Quotient.mk (S.ideal i.castSucc) 1) (A ⧸ S.ideal i.castSucc) := by
    refine IsLocalization.self ?_
    rw [map_one]
    exact Submonoid.powers_le.mpr isUnit_one
  have h := S.flat_away i 1 (by rw [hi]; exact Submodule.mem_top) (A ⧸ S.ideal i.castSucc)
  let := AlgebraicGeometry.flat_tensorQuotient_of_flat_tensor (S.ideal i.castSucc) N h
  exact Module.Flat.of_linearEquiv
    (TensorProduct.lid (A ⧸ S.ideal i.castSucc)
      (N ⧸ (S.ideal i.castSucc • (⊤ : Submodule A N)))).symm

end FlatStratification

end Stacks

end
