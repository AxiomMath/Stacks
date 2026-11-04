module

public import StacksFrontier.RingTheory.Flat.WeaklyAssociatedFibreConverse
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatFibre

/-!
# Weakly associated primes of a projective tensor product, read on the closed fibre

Let `R` be a local ring with maximal ideal `𝔭`, let `R → S` be essentially of finite presentation
with Noetherian closed fibre ring `S / 𝔭S`, let `N` be an `S`-module finitely presented over `S`
and projective as an `R`-module, and let `M` be an `R`-module.  For a prime `𝔮` of `S` containing
`𝔭S` this file proves

`𝔮 ∈ WeakAss_S(N ⊗_R M) ↔ (𝔭 ∈ WeakAss_R(M) and 𝔮 ∈ Ass_S(N / 𝔭N))`,

under the additional hypothesis that `𝔮` is maximal among the primes associated — in the strict
sense of [Stacks, Tag 00LA] — to the closed fibre `N / 𝔭N`.  Since `R` is local the residue field
`κ(𝔭)` is `R / 𝔭`, so the fibre ring of [Stacks, Tag 05IG] is `S / 𝔭S`, the fibre module is
`N / 𝔭N`, and `𝔮-bar` is the image of `𝔮`;  the equivalence above is therefore that tag in the
situation its own proof reduces to.

The implication `⟹` is
`isWeaklyAssociatedPrime_maximalIdeal_and_isAssociatedPrimeStacks_fibre_of_fg` and uses neither
projectivity nor the maximality of `𝔮`.  What is proved here is `⟸`.  The
converse *step* — a prime of `S` containing `𝔮`, lying over `𝔭` and weakly associated to
`N ⊗[R] M` — is `exists_isWeaklyAssociatedPrime_tensorProduct_of_fibre`, which takes the fibre
condition elementwise;  this file supplies the two things that turn that step into the implication.
First, the elementwise data: a witness `z` for `𝔮 ∈ Ass_S(N / 𝔭N)` is an element of `N` outside
`𝔭N` whose annihilator in `S` is exactly `𝔮`, and `𝔮` is generated over `𝔭S` by finitely many
elements because `S / 𝔭S` is Noetherian, so each of those carries `z` into `𝔭N`.  Second, the
identification of the prime produced with `𝔮` itself: that prime contains `𝔮` and lies over `𝔭`,
so the already-proved implication `⟹` puts it in `Ass_S(N / 𝔭N)`, where the maximality of `𝔮`
forces the two to agree.

The hypotheses added to those of [Stacks, Tag 05IG] — a local base, projectivity of `N` over `R`,
and maximality of `𝔮` in `Ass_S(N / 𝔭N)` — are exactly what the source's étale-local reduction
installs before its last paragraph.  That reduction, which rests on the structure theorem
[Stacks, Tag 05ID], is carried out in
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.EtaleLocalizationReduction`, and the statement
below is the `⟸` half it feeds.  Nothing here therefore carries a `@[stacks 05IG]` attribute;  the
tag is `Stacks.WeaklyAssociatedPrimes.tensorFibreFormula05IG`.

## Main results

* `Stacks.WeaklyAssociatedPrimes.mem_smul_top_iff_mem_map_smul_top`:  for an ideal `J` of `R`, the
  submodule `JN` of an `S`-module `N` is the same whether formed over `R` or over `S`.
* `Stacks.WeaklyAssociatedPrimes.exists_eq_sup_span_range_of_isNoetherianRing_quotient`:  an ideal
  containing `I` is `I` together with finitely many elements when `S / I` is Noetherian.
* `isWeaklyAssociatedPrime_tensorProduct_of_isAssociatedPrimeStacks_closedFibre`, in
  `Stacks.WeaklyAssociatedPrimes`:  the implication `⟸` described above.
* `isWeaklyAssociatedPrime_tensorProduct_iff_isAssociatedPrimeStacks_closedFibre`, in the same
  namespace:  the equivalence.

## References

* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
-/

@[expose] public section

open scoped TensorProduct

open IsLocalRing

universe u v w t

namespace Stacks.WeaklyAssociatedPrimes

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- For an ideal `J` of `R` and an `S`-module `N`, the submodule `JN` of `N` is the same whether
it is formed over `R` from `J` or over `S` from the ideal `JS`. -/
theorem mem_smul_top_iff_mem_map_smul_top (J : Ideal R) (x : N) :
    x ∈ J • (⊤ : Submodule R N) ↔
      x ∈ Ideal.map (algebraMap R S) J • (⊤ : Submodule S N) := by
  rw [← Submodule.restrictScalars_mem R
    (Ideal.map (algebraMap R S) J • (⊤ : Submodule S N)) x,
    Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

/-- An ideal `q` of `S` containing an ideal `I` with `S / I` Noetherian is `I` together with
finitely many elements of `q`. -/
theorem exists_eq_sup_span_range_of_isNoetherianRing_quotient
    {I : Ideal S} {q : Ideal S} (hIq : I ≤ q) [IsNoetherianRing (S ⧸ I)] :
    ∃ (n : ℕ) (g : Fin n → S), q = I ⊔ Ideal.span (Set.range g) := by
  obtain ⟨n, gbar, hgbar⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (IsNoetherian.noetherian (Ideal.map (Ideal.Quotient.mk I) q))
  choose g hg using fun i => Ideal.Quotient.mk_surjective (gbar i)
  refine ⟨n, g, ?_⟩
  have hmapeq : Ideal.map (Ideal.Quotient.mk I) (I ⊔ Ideal.span (Set.range g)) =
      Ideal.map (Ideal.Quotient.mk I) q := by
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_quotient_self, bot_sup_eq, ← hgbar]
    congr 1
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hg)
  have heq := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hmapeq
  rw [Ideal.comap_map_mk le_sup_left, Ideal.comap_map_mk hIq] at heq
  exact heq.symm

variable {M : Type t} [AddCommGroup M] [Module R M]

/-- **The implication `⟸` of [Stacks, Tag 05IG], over a local base and for a projective module.**
Let `R` be local with maximal ideal `𝔭`, let `R → S` be essentially of finite presentation with
`S / 𝔭S` Noetherian, and let `N` be an `S`-module finitely presented over `S` and projective over
`R`.  If `𝔭` is weakly associated to the `R`-module `M` and a prime `𝔮` of `S` is associated — in
the strict sense of [Stacks, Tag 00LA] — to the closed fibre `N / 𝔭N` and is maximal among the
primes so associated, then `𝔮` is weakly associated to `N ⊗[R] M`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_of_isAssociatedPrimeStacks_closedFibre
    [IsLocalRing R] [Module.FinitePresentation S N] [Module.Projective R N]
    [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    (hM : IsWeaklyAssociatedPrime R M (maximalIdeal R)) {q : Ideal S}
    (hq : IsAssociatedPrimeStacks S
      (N ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)) q)
    (hmax : ∀ s : Ideal S, IsAssociatedPrimeStacks S
        (N ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)) s →
      q ≤ s → q = s) :
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q := by
  classical
  set I : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R) with hIdef
  obtain ⟨hqp, w, hw⟩ := hq
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule S N)) w
  have hann : ∀ a : S, a ∈ q ↔ a • z ∈ I • (⊤ : Submodule S N) := by
    intro a
    rw [← hw, Submodule.mem_colon]
    constructor
    · intro h
      have hz := h _ (Submodule.mem_span_singleton_self _)
      rwa [← Submodule.Quotient.mk_smul, Submodule.mem_bot,
        Submodule.Quotient.mk_eq_zero] at hz
    · intro h x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [Submodule.mem_bot, smul_comm, ← Submodule.Quotient.mk_smul,
        (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule S N))).mpr h, smul_zero]
  have hIq : I ≤ q := fun a ha =>
    (hann a).mpr (Submodule.smul_mem_smul ha Submodule.mem_top)
  obtain ⟨n, g, hg⟩ := exists_eq_sup_span_range_of_isNoetherianRing_quotient hIq
  have hz : z ∉ maximalIdeal R • (⊤ : Submodule R N) := by
    rw [mem_smul_top_iff_mem_map_smul_top (S := S), ← hIdef]
    exact fun h => hqp.ne_top
      (Ideal.eq_top_of_isUnit_mem q ((hann 1).mpr (by rwa [one_smul])) isUnit_one)
  have hgz : ∀ i, g i • z ∈ maximalIdeal R • (⊤ : Submodule R N) := by
    intro i
    rw [mem_smul_top_iff_mem_map_smul_top (S := S), ← hIdef, ← hann (g i), hg]
    exact Submodule.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hqs, -, hws⟩ :=
    exists_isWeaklyAssociatedPrime_tensorProduct_of_fibre (M := M) hM q g hg z hz hgz
  have : s.IsPrime := hws.isPrime S (N ⊗[R] M)
  rwa [hmax s (isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct hS
    (hIq.trans hqs) hws) hqs]

/-- **[Stacks, Tag 05IG] over a local base, for a projective module and a maximal fibre prime.**
A prime `𝔮` of `S` containing `𝔭S` is weakly associated to `N ⊗[R] M` if and only if the maximal
ideal `𝔭` of `R` is weakly associated to `M` and `𝔮` is associated to the closed fibre `N / 𝔭N`.
The implication `⟹` needs neither projectivity of `N` over `R` nor maximality of `𝔮` among the
primes associated to `N / 𝔭N`. -/
theorem isWeaklyAssociatedPrime_tensorProduct_iff_isAssociatedPrimeStacks_closedFibre
    [IsLocalRing R] [Module.FinitePresentation S N] [Module.Projective R N]
    [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation) (hfg : (maximalIdeal R).FG)
    {q : Ideal S} [q.IsPrime]
    (hIq : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ q)
    (hmax : ∀ s : Ideal S, IsAssociatedPrimeStacks S
        (N ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)) s →
      q ≤ s → q = s) :
    IsWeaklyAssociatedPrime S (N ⊗[R] M) q ↔
      IsWeaklyAssociatedPrime R M (maximalIdeal R) ∧
        IsAssociatedPrimeStacks S
          (N ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N)) q :=
  ⟨isWeaklyAssociatedPrime_maximalIdeal_and_isAssociatedPrimeStacks_fibre_of_fg hS hfg hIq,
    fun h => isWeaklyAssociatedPrime_tensorProduct_of_isAssociatedPrimeStacks_closedFibre
      hS h.1 h.2 hmax⟩

end Stacks.WeaklyAssociatedPrimes

end
