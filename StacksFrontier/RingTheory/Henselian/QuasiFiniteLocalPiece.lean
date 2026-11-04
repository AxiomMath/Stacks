module

public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The local finite piece at a quasi-finite point over a henselian local ring

Let `(R, 𝔪)` be a henselian local ring, `S` a finite type `R`-algebra and `q` a prime of `S` over
`𝔪` at which `S` is quasi-finite over `R`. Then there is an idempotent `h ∈ S` with `h ∉ q` such
that `S_h` is finite over `R` and `q` is the only prime of `S` over `𝔪` not containing `h`. In
other words `D(h) ⊆ Spec S` is an open and closed neighbourhood of `q`, finite over `Spec R`, whose
closed fibre is the single point `q`. This is the algebraic content of the step of the proof of
Stacks 0CVB which applies Stacks 02LK over a strictly henselian base.

## Main results

* `exists_isIdempotentElem_finite_forall_eq_of_quasiFiniteAt`: the idempotent `h`.

## Implementation notes

The idempotent is assembled from two parts of Stacks 04GG. An isolating idempotent `g`
with `g ∉ q` and `S ⧸ (1 - g)` finite over `R` comes from
`isolating_idempotent_per_point`; the finite algebra `A = S ⧸ (1 - g)` is then a finite product
of local rings, `exists_completeOrthogonalIdempotents_lift`, and `h = g a` for a lift `a` of the
idempotent cutting out the local factor through which `q` passes. The uniqueness clause holds
because a prime of the finite algebra `A` over `𝔪` is maximal, and a local factor has only one
maximal ideal.

## References

* [Stacks Project, Tag 04GG](https://stacks.math.columbia.edu/tag/04GG)
* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
-/

@[expose] public section

universe u

open IsLocalRing

/-- A maximal ideal of a ring containing an ideal `J` with local quotient is determined by `J`:
two such maximal ideals coincide. -/
theorem Ideal.eq_of_isMaximal_of_le_of_isLocalRing_quotient {A : Type*} [CommRing A]
    {J m m' : Ideal A} [IsLocalRing (A ⧸ J)] (hm : m.IsMaximal) (hm' : m'.IsMaximal)
    (hJm : J ≤ m) (hJm' : J ≤ m') : m = m' := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hk : RingHom.ker (Ideal.Quotient.mk J) ≤ m := by rwa [Ideal.mk_ker]
  have hk' : RingHom.ker (Ideal.Quotient.mk J) ≤ m' := by rwa [Ideal.mk_ker]
  have h1 : (m.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj hk
  have h2 : (m'.map (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj hk'
  have heq : m.map (Ideal.Quotient.mk J) = m'.map (Ideal.Quotient.mk J) :=
    (IsLocalRing.eq_maximalIdeal h1).trans (IsLocalRing.eq_maximalIdeal h2).symm
  have e1 := Ideal.comap_map_of_surjective' _ hsurj m
  have e2 := Ideal.comap_map_of_surjective' _ hsurj m'
  rw [sup_eq_left.mpr hk] at e1
  rw [sup_eq_left.mpr hk'] at e2
  rw [← e1, ← e2, heq]

/-- An idempotent outside a prime ideal has its complement `1 - e` inside it. -/
private theorem IsIdempotentElem.one_sub_mem_of_notMem_of_isPrime {A : Type*} [CommRing A] {e : A}
    (he : IsIdempotentElem e) {p : Ideal A} (hp : p.IsPrime) (hep : e ∉ p) : 1 - e ∈ p :=
  (hp.mem_or_mem (show e * (1 - e) ∈ p by
    rw [mul_sub, mul_one, he.eq, sub_self]
    exact p.zero_mem)).resolve_left hep

/-- If `g` is idempotent and `a` is idempotent modulo `1 - g`, then `g * a` is idempotent. -/
private theorem IsIdempotentElem.mul_of_mul_self_sub_mem_span_one_sub {A : Type*} [CommRing A]
    {g a : A} (hg : IsIdempotentElem g) (ha : a * a - a ∈ Ideal.span {1 - g}) :
    IsIdempotentElem (g * a) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
  change g * a * (g * a) = g * a
  linear_combination (a * a - c) * hg.eq - g * hc

/-- For an idempotent `e`, the localization `S_e` is finite over `R` as soon as the quotient
`S ⧸ (1 - e)` is. -/
private theorem Module.Finite.localization_away_of_isIdempotentElem {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {e : S} (he : IsIdempotentElem e)
    (hfin : Module.Finite R (S ⧸ Ideal.span {1 - e})) :
    Module.Finite R (Localization.Away e) := by
  have := IsLocalization.Away.quotient_of_isIdempotentElem he
  exact Module.Finite.equiv ((IsLocalization.algEquiv (Submonoid.powers e)
    (S ⧸ Ideal.span {1 - e}) (Localization.Away e)).restrictScalars R).toLinearEquiv

/-- Over a local ring `R`, a prime of `S` containing `J` and lying over the maximal ideal of `R`
maps to a maximal ideal of `S ⧸ J` whenever `S ⧸ J` is integral over `R`. -/
private theorem Ideal.isMaximal_map_quotientMk_of_liesOver_maximalIdeal {R S : Type*} [CommRing R]
    [IsLocalRing R] [CommRing S] [Algebra R S] {J p : Ideal S} [Algebra.IsIntegral R (S ⧸ J)]
    [p.IsPrime] [p.LiesOver (maximalIdeal R)] (hJp : J ≤ p) :
    (p.map (Ideal.Quotient.mk J)).IsMaximal := by
  have : (p.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) _ ?_
  have hc : (p.map (Ideal.Quotient.mk J)).comap (algebraMap R (S ⧸ J)) = maximalIdeal R := by
    rw [IsScalarTower.algebraMap_eq R S (S ⧸ J), ← Ideal.comap_comap]
    change Ideal.comap (algebraMap R S)
      (Ideal.comap (Ideal.Quotient.mk J) (p.map (Ideal.Quotient.mk J))) = _
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hJp]
    exact (Ideal.LiesOver.over (P := p) (p := maximalIdeal R)).symm
  rw [hc]
  infer_instance

/-- **The local finite piece at a quasi-finite point.** Let `R` be a henselian local ring, `S` a
finite type `R`-algebra and `q` a prime of `S` over the maximal ideal of `R` at which `S` is
quasi-finite. Then there is an idempotent `h ∈ S` outside `q` such that `S_h` is finite over `R`
and `q` is the only prime of `S` over the maximal ideal of `R` not containing `h`. -/
theorem exists_isIdempotentElem_finite_forall_eq_of_quasiFiniteAt (R : Type u) [CommRing R]
    [HenselianLocalRing R] (S : Type u) [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (maximalIdeal R)] [Algebra.QuasiFiniteAt R q] :
    ∃ h : S, IsIdempotentElem h ∧ h ∉ q ∧ Module.Finite R (Localization.Away h) ∧
      ∀ q' : Ideal S, q'.IsPrime → q'.LiesOver (maximalIdeal R) → h ∉ q' → q' = q := by
  classical
  obtain ⟨g, hg, hgfin, hgq⟩ := isolating_idempotent_per_point R S
    (fun R' _ _ _ P _ _ hres => henselian_etale_residue_point_section R R' P hres) q
  set J : Ideal S := Ideal.span {1 - g} with hJ
  set π : S →+* S ⧸ J := Ideal.Quotient.mk J
  have hπsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hJle : ∀ p : Ideal S, p.IsPrime → g ∉ p → J ≤ p := fun p hp hgp =>
    Ideal.span_le.mpr <| Set.singleton_subset_iff.mpr <| hg.one_sub_mem_of_notMem_of_isPrime hp hgp
  have hker : RingHom.ker π = J := Ideal.mk_ker
  have hmapPrime : ∀ p : Ideal S, p.IsPrime → J ≤ p → (p.map π).IsPrime :=
    fun p _ hJp => Ideal.map_isPrime_of_surjective hπsurj (by rwa [hker])
  have hcomapMap : ∀ p : Ideal S, J ≤ p → (p.map π).comap π = p := fun p hJp => by
    rw [Ideal.comap_map_of_surjective' _ hπsurj p, hker, sup_eq_left.mpr hJp]
  have : Algebra.IsIntegral R (S ⧸ J) := Algebra.IsIntegral.of_finite R _
  obtain ⟨n, e, hco, hloc⟩ := exists_completeOrthogonalIdempotents_lift.{u, u} R (S ⧸ J)
  have hJq : J ≤ q := hJle q inferInstance hgq
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ q.map π := by
    by_contra! hall
    refine (hmapPrime q inferInstance hJq).ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    exact hco.complete ▸ Ideal.sum_mem _ fun j _ => hall j
  obtain ⟨a, ha⟩ := hπsurj (e i)
  have hidem : IsIdempotentElem (g * a) := by
    refine hg.mul_of_mul_self_sub_mem_span_one_sub ?_
    change a * a - a ∈ J
    rw [← hker, RingHom.mem_ker]
    change π (a * a - a) = 0
    rw [map_sub, map_mul, ha, (hco.idem i).eq, sub_self]
  have haq : a ∉ q := fun h => hi (ha ▸ Ideal.mem_map_of_mem _ h)
  refine ⟨g * a, hidem, fun hmem => ((inferInstance : q.IsPrime).mem_or_mem hmem).elim hgq haq,
    ?_, ?_⟩
  · have hJle' : J ≤ Ideal.span {1 - g * a} := by
      rw [hJ, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_span_singleton'.mpr ⟨1 - g, by linear_combination a * hg.eq⟩
    exact Module.Finite.localization_away_of_isIdempotentElem hidem
      (Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hJle').toLinearMap
        (Ideal.Quotient.factor_surjective hJle'))
  · intro q' hq' hlo' hq'mem
    have hJq' : J ≤ q' := hJle q' hq' fun h => hq'mem (q'.mul_mem_right a h)
    have hsub : ∀ p : Ideal S, p.IsPrime → a ∉ p → J ≤ p →
        Ideal.span {1 - e i} ≤ p.map π := fun p hp hap hJp =>
      Ideal.span_le.mpr <| Set.singleton_subset_iff.mpr <|
        (hco.idem i).one_sub_mem_of_notMem_of_isPrime (hmapPrime p hp hJp) fun hmem =>
          hap (by rwa [← hcomapMap p hJp, Ideal.mem_comap, ha])
    have : IsLocalRing ((S ⧸ J) ⧸ Ideal.span {1 - e i}) := hloc i
    have heq := Ideal.eq_of_isMaximal_of_le_of_isLocalRing_quotient
      (Ideal.isMaximal_map_quotientMk_of_liesOver_maximalIdeal (R := R) hJq')
      (Ideal.isMaximal_map_quotientMk_of_liesOver_maximalIdeal (R := R) hJq)
      (hsub q' hq' (fun h => hq'mem (q'.mul_mem_left g h)) hJq') (hsub q inferInstance haq hJq)
    rw [← hcomapMap q' hJq', heq, hcomapMap q hJq]

end
