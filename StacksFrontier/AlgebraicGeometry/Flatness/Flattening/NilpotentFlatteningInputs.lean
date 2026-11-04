module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatStratificationChain
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.NilpotentFlatteningIdeal

/-!
# Inputs of the nilpotent flattening ideal in the proof of Stacks 05U9

`Stacks.flat_of_least_flattening_of_flat_away` and
`Stacks.exists_fg_isNilpotent_flat_quotient_of_least` are the two ring-theoretic steps of Claim 1
of the proof of Stacks 05U9 and of the paragraph after it. Three of their inputs are supplied
here: two hypotheses read off the generic flatness stratification of
`Stacks.FlatStratification`, and the descent of the resulting ideal from the henselization.

* `hdense`, the scheme theoretic density of the stratum, is produced over `A ⧸ J_i` by
  `Stacks.eq_zero_of_forall_pow_mul_eq_zero_quotient`. The source applies
  `Stacks.flat_of_least_flattening_of_flat_away` not over `A` but over the henselization `A^h`,
  so the density has to travel along `A → A^h`.
  `Stacks.eq_zero_of_forall_pow_mul_eq_zero_of_flat` carries it along any flat algebra: the
  condition says that multiplication by a suitable finite family of elements is injective on
  `A`, and a flat algebra preserves injectivity.

* `hcover`, the statement that every prime of `A` contains a flattening ideal, is
  `Stacks.exists_flat_quotient_le_of_isPrime`: the chain of a stratification runs from inside a
  given prime to `⊤`, so a consecutive pair straddles the prime
  (`Stacks.exists_straddle`), the prime lies in that stratum, and the closure ideal of the
  stratum is therefore inside the prime. Claim 1 at that index makes it a flattening ideal.

## Main results

* `Stacks.eq_zero_of_forall_pow_mul_eq_zero_of_flat`: scheme theoretic density of a finite union
  of basic opens ascends along a flat algebra.
* `Stacks.exists_straddle`: an ascending chain from inside a prime to `⊤` straddles the prime.
* `Stacks.exists_flat_quotient_le_of_isPrime`: **`hcover` from Claim 1 at every index.**
* `Stacks.exists_fg_le_mem_map`, `Stacks.exists_fg_le_le_map` and
  `Stacks.exists_fg_isNilpotent_le_map`: a finitely generated ideal inside the extension of the
  nilradical is inside the extension of a finitely generated nilpotent ideal. With Stacks 0ASE
  this is the descent of the nilpotent flattening ideal from `A^h` to `A`.

## Implementation notes

The density condition is phrased elementwise, as
`Stacks.flat_of_least_flattening_of_flat_away` takes it: `x` is zero as soon as a power of each
`g i` kills it. Its ascent is proved by replacing the family `g` by the family of powers
`g i ^ n i` which actually kill a given element of the flat algebra, and testing the resulting
`A`-linear map `A → (ι → A)` — injective exactly by the density over `A` — against flatness.

The descent of a finitely generated ideal is elementary: each generator lies in the span of
finitely many images, and a choice of preimages generates the finitely generated subideal
wanted.

## References

* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
* [Stacks Project, Tag 0ASY](https://stacks.math.columbia.edu/tag/0ASY)
* [Stacks Project, Tag 0ASE](https://stacks.math.columbia.edu/tag/0ASE)
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Stacks

/-! ### Scheme theoretic density along a flat algebra -/

/-- **Scheme theoretic density of a finite union of basic opens ascends along a flat algebra.**
Suppose the only element of `A` killed by a power of each member of a finite family `g` is zero.
Then for a flat `A`-algebra `R` the only element of `R` killed by a power of each image of a
member of `g` is zero.

This is the hypothesis `hdense` of `Stacks.flat_of_least_flattening_of_flat_away` travelling
from `A` to the henselization `A^h`, over which the source applies that lemma. -/
theorem eq_zero_of_forall_pow_mul_eq_zero_of_flat {A : Type u} [CommRing A] {ι : Type v}
    [Finite ι] (g : ι → A)
    (hdense : ∀ x : A, (∀ i, ∃ n : ℕ, g i ^ n * x = 0) → x = 0)
    (R : Type w) [CommRing R] [Algebra A R] [Module.Flat A R]
    (y : R) (hy : ∀ i, ∃ n : ℕ, algebraMap A R (g i) ^ n * y = 0) : y = 0 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose n hn using hy
  set h : ι → A := fun i => g i ^ n i with hhdef
  have hy' : ∀ i, algebraMap A R (h i) * y = 0 := fun i => by
    rw [hhdef]
    simpa [map_pow] using hn i
  set φ : A →ₗ[A] (ι → A) := LinearMap.pi fun i => LinearMap.lsmul A A (h i) with hφdef
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine hdense x fun i => ⟨n i, ?_⟩
    have hxi := congrFun hx i
    simpa [hφdef, hhdef] using hxi
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := R) φ hφ
  have hz : (LinearMap.lTensor R φ) (y ⊗ₜ[A] (1 : A)) = 0 := by
    apply (TensorProduct.piScalarRight A A R ι).injective
    ext i
    simp [hφdef, TensorProduct.piScalarRight_apply, Algebra.smul_def, hy' i]
  have h0 : (y ⊗ₜ[A] (1 : A)) = 0 := hinj (by simpa using hz)
  simpa using congrArg (TensorProduct.rid A R) h0

/-! ### Every prime of the base contains a flattening ideal -/

/-- **An ascending chain from inside a prime to the unit ideal straddles the prime.** If the
first ideal of the chain is contained in `p` and the last is not, then some consecutive pair
is: the index found is the stratum of the stratification which contains `p`. -/
theorem exists_straddle {A : Type u} [CommRing A] {p : Ideal A} :
    ∀ (t : ℕ) (K : Fin (t + 1) → Ideal A), K 0 ≤ p → ¬ K (Fin.last t) ≤ p →
      ∃ i : Fin t, K i.castSucc ≤ p ∧ ¬ K i.succ ≤ p := by
  intro t
  induction t with
  | zero =>
      intro K h0 hlast
      exact absurd h0 (by simpa using hlast)
  | succ t ih =>
      intro K h0 hlast
      by_cases h : K (Fin.castSucc (Fin.last t)) ≤ p
      · exact ⟨Fin.last t, h, by simpa using hlast⟩
      · obtain ⟨i, hi1, hi2⟩ := ih (K ∘ Fin.castSucc) (by simpa using h0) (by simpa using h)
        refine ⟨i.castSucc, hi1, ?_⟩
        rw [Fin.succ_castSucc]
        exact hi2

/-- **`hcover` for the proof of Stacks 05U9: every prime of `A` contains a flattening ideal.**
Let `S` be a generic flatness stratification of `N` over `A` and suppose Claim 1 of the source's
proof holds at every index: for each `i` and each finite family `g` generating the ideal of
`S_{i+1}`, the reduction of `N` modulo the closure ideal `J_i` of the stratum `S_i ∖ S_{i+1}` is
flat over `A ⧸ J_i`. Then every prime `p` of `A` contains an ideal `K` with `N ⧸ KN` flat over
`A ⧸ K`.

This is the hypothesis `hcover` of `Stacks.isNilpotent_of_least_flattening` and
`Stacks.exists_fg_isNilpotent_flat_quotient_of_least`: it is what makes the smallest flattening
ideal nilpotent. The prime `p` lies in exactly one stratum `S_i ∖ S_{i+1}`, hence on its scheme
theoretic closure, so `J_i ⊆ p`.

Claim 1 is asked for only at *finite* index types, which is all the proof uses: the family it
builds is a finite generating set of `S.ideal i.succ`, which is finitely generated. That is also
all a prover of Claim 1 can give, since the henselization core
`Stacks.flat_of_flat_away_of_flat_quotient_pow` needs the open `⋃ᵢ D(g i)` to be quasi-compact. -/
theorem exists_flat_quotient_le_of_isPrime {A : Type u} [CommRing A] {N : Type v}
    [AddCommGroup N] [Module A N] {t : ℕ} (S : FlatStratification A N t)
    (hclaim1 : ∀ (i : Fin t) (ι : Type u) [Finite ι] (g : ι → A),
      Ideal.span (Set.range g) = S.ideal i.succ →
      Module.Flat (A ⧸ strataClosureIdeal (S.ideal i.castSucc) g)
        (N ⧸ (strataClosureIdeal (S.ideal i.castSucc) g • (⊤ : Submodule A N))))
    (p : Ideal A) [hp : p.IsPrime] :
    ∃ K : Ideal A, K ≤ p ∧ Module.Flat (A ⧸ K) (N ⧸ (K • (⊤ : Submodule A N))) := by
  obtain ⟨i, hi1, hi2⟩ := exists_straddle t S.ideal (S.ideal_zero_le_of_isPrime p)
    (by rw [S.eq_top]; exact fun hle => hp.ne_top (top_le_iff.mp hle))
  obtain ⟨T, hT⟩ := S.fg i.succ
  set g : ((T : Set A)) → A := fun x => (x : A) with hgdef
  have hspan : Ideal.span (Set.range g) = S.ideal i.succ := by
    rw [hgdef, Subtype.range_coe]
    exact hT
  obtain ⟨b, hbT, hbp⟩ : ∃ b : A, b ∈ (T : Set A) ∧ b ∉ p := by
    by_contra hcon
    refine hi2 ?_
    rw [← hspan, hgdef, Subtype.range_coe]
    exact Ideal.span_le.mpr fun b hb => by
      by_contra hbp
      exact hcon ⟨b, hb, hbp⟩
  exact ⟨strataClosureIdeal (S.ideal i.castSucc) g,
    strataClosureIdeal_le_of_isPrime hp hi1 (i := ⟨b, hbT⟩) hbp,
    hclaim1 i _ g hspan⟩

/-! ### Descent of a finitely generated ideal along an extension of ideals -/

/-- An element of the extension of an ideal along a ring map lies in the extension of a finitely
generated subideal. -/
theorem exists_fg_le_mem_map {A R : Type u} [CommRing A] [CommRing R] (f : A →+* R)
    (J : Ideal A) {x : R} (hx : x ∈ Ideal.map f J) :
    ∃ J₀ : Ideal A, J₀.FG ∧ J₀ ≤ J ∧ x ∈ Ideal.map f J₀ := by
  classical
  obtain ⟨G, hG, hxG⟩ :=
    Submodule.mem_span_finite_of_mem_span (show x ∈ Ideal.span (f '' (J : Set A)) from hx)
  set pre : R → A := fun r => if h : ∃ a : A, a ∈ J ∧ f a = r then h.choose else 0 with hpredef
  have hpre : ∀ r ∈ G, pre r ∈ J ∧ f (pre r) = r := by
    intro r hr
    obtain ⟨a, haJ, hfa⟩ := hG (Finset.mem_coe.2 hr)
    have h : ∃ a : A, a ∈ J ∧ f a = r := ⟨a, haJ, hfa⟩
    rw [hpredef]
    simp only [dite_eq_left h]
    exact h.choose_spec
  refine ⟨Ideal.span (G.image pre : Set A), ⟨G.image pre, rfl⟩, ?_, ?_⟩
  · refine Ideal.span_le.mpr ?_
    intro a ha
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (by simpa using ha)
    exact (hpre r hr).1
  · rw [Ideal.map_span]
    refine Ideal.span_mono ?_ hxG
    intro r hr
    have hr' : r ∈ G := Finset.mem_coe.1 hr
    exact ⟨pre r, by simpa using Finset.mem_image_of_mem pre hr', (hpre r hr').2⟩

/-- A finitely generated ideal inside the extension of an ideal lies inside the extension of a
finitely generated subideal. -/
theorem exists_fg_le_le_map {A R : Type u} [CommRing A] [CommRing R] (f : A →+* R)
    (J : Ideal A) {I : Ideal R} (hIfg : I.FG) (hI : I ≤ Ideal.map f J) :
    ∃ J₀ : Ideal A, J₀.FG ∧ J₀ ≤ J ∧ I ≤ Ideal.map f J₀ := by
  classical
  obtain ⟨T, hT⟩ := hIfg
  have hmem : ∀ r ∈ T, ∃ J₀ : Ideal A, J₀.FG ∧ J₀ ≤ J ∧ r ∈ Ideal.map f J₀ :=
    fun r hr => exists_fg_le_mem_map f J (hI (hT ▸ Ideal.subset_span (Finset.mem_coe.2 hr)))
  choose! sub hsubfg hsuble hsubmem using hmem
  refine ⟨T.sup sub, ?_, Finset.sup_le hsuble, ?_⟩
  · refine Finset.sup_induction Submodule.fg_bot (fun a ha b hb => Submodule.FG.sup ha hb) ?_
    exact hsubfg
  · rw [← hT]
    refine Ideal.span_le.mpr fun r hr => ?_
    have hr' : r ∈ T := Finset.mem_coe.1 hr
    exact Ideal.map_mono (Finset.le_sup (f := sub) hr') (hsubmem r hr')

/-- **Descent of the finitely generated nilpotent flattening ideal of the proof of Stacks
05U9.** A finitely generated ideal of `R` contained in the extension of the nilradical of `A` is
contained in the extension of a finitely generated *nilpotent* ideal of `A`.

In the source this is applied with `R = A^h` the henselization, whose nilradical is the
extension of that of `A` by Stacks 0ASE
(`Stacks.nilradical_map_eq_henselization_and_strictHenselization`): the finitely generated
flattening ideal `I ⊆ A^h` of Stacks 05PG is nilpotent, hence inside `nil(A) A^h`, and the ideal
`I₀ ⊆ A` produced here is the finitely generated nilpotent ideal with `N ⧸ I₀N` flat over
`A ⧸ I₀`. -/
theorem exists_fg_isNilpotent_le_map {A R : Type u} [CommRing A] [CommRing R] (f : A →+* R)
    {I : Ideal R} (hIfg : I.FG) (hI : I ≤ Ideal.map f (nilradical A)) :
    ∃ I₀ : Ideal A, I₀.FG ∧ IsNilpotent I₀ ∧ I ≤ Ideal.map f I₀ := by
  obtain ⟨I₀, hfg, hle, hmap⟩ := exists_fg_le_le_map f (nilradical A) hIfg hI
  exact ⟨I₀, hfg, (Ideal.FG.isNilpotent_iff_le_nilradical hfg).mpr hle, hmap⟩

end Stacks

end
