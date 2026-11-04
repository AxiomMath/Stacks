module

public import StacksFrontier.RingTheory.Syntomic.RelativeGlobalCompleteIntersection
public import StacksFrontier.RingTheory.RelativeDimension.Basic
import StacksFrontier.RingTheory.Flat.ShortExact

/-!
# Syntomic neighbourhoods of a prime

Let `R → S` be a ring map and let `𝔮` be a prime of `S` lying over the prime `𝔭` of `R`. The
following are equivalent.

1. There is a `g ∈ S`, `g ∉ 𝔮`, such that `R → S_g` is syntomic.
2. There is a `g ∈ S`, `g ∉ 𝔮`, such that `S_g` is a relative global complete intersection over
   `R`.
3. There is a `g ∈ S`, `g ∉ 𝔮`, such that `R → S_g` is of finite presentation, the local ring map
   `R_𝔭 → S_𝔮` is flat, and `S_𝔮/𝔭S_𝔮` is a complete intersection over `κ(𝔭)`.

## Main results

* `Algebra.Syntomic.flat_localization_and_isCompleteIntersection_fiber`: a syntomic algebra is flat
  with complete intersection fibres at every prime, the local form of (1) ⟹ (3).
* `Algebra.exists_notMem_isRelativeGlobalCompleteIntersection_of_flat`: the local form of
  (3) ⟹ (2).
* `Algebra.exists_notMem_syntomic_tfae`: the equivalence of (1), (2) and (3).

## Implementation notes

*(2) ⟹ (1)* is Lemma 00SW, `Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection`.

*(1) ⟹ (3).* The fibre `κ(𝔭) ⊗_R S_g` is a local complete intersection over `κ(𝔭)`, so all its
local rings are complete intersections (Lemma 00SH), and `κ(𝔭) ⊗_R S_𝔮` is its local ring at the
prime corresponding to `𝔮` (`Ideal.Fiber.isLocalization_atPrime`).

*(3) ⟹ (2)* uses a presentation `S_g = R[x_1, …, x_n]/I` and the prime `𝔮'` of `R[x_i]` below `𝔮`.
By Lemma 00SG the kernel of `κ(𝔭)[x_i] → κ(𝔭) ⊗_R S_g` is generated, near `𝔮`, by a regular
sequence. That local ring is taken to be the closed fibre `R[x_i]_{𝔮'}/𝔭R[x_i]_{𝔮'}`
(`MvPolynomial.FiberAtPrime`, `Algebra.Generators.isLocalization_fiberAtPrime`), whose elements are
fractions of polynomials over `R`, so the regular sequence lifts to `f_1, …, f_c ∈ I` up to a unit
(`MvPolynomial.FiberAtPrime.exists_isRegular_mk`). A Nakayama argument with Lemma 00HL
(`Algebra.Presentation.exists_notMem_mul_relation_mem`) then shows that `I` and `(f_1, …, f_c)`
agree after inverting some `h ∉ 𝔮'`, so `S_{gh}` is presented by `n + 1` variables and `c + 1`
relations (`Algebra.Presentation.localizationAwayCompOfMulMem`); the regular sequence gives
`dim_𝔮(S/R) = n - c` (`Algebra.Generators.relativeDimensionAt_add_length_eq`, through Lemma 00P2),
and Lemma 00ST (3) finishes.

*Principal localizations of principal localizations.* The three conditions are stated for
`Localization.Away g` over `S`, while the arguments produce localizations of `S_g`;
`Algebra.IsRelativeGlobalCompleteIntersection.exists_notMem_of_localizationAway` and
`Localization.AtPrime.algEquivMapAway` move between the two.


## References

* [Stacks, Tag 00SY](https://stacks.math.columbia.edu/tag/00SY)
-/

@[expose] public section

open Algebra.TensorProduct

open scoped TensorProduct

/-! ### Transport along isomorphisms -/

/-- Being a complete intersection over `k` is invariant under `k`-algebra isomorphism. -/
theorem IsCompleteIntersection.of_algEquiv {k : Type*} [Field k] {A B : Type*} [CommRing A]
    [CommRing B] [Algebra k A] [Algebra k B] (h : IsCompleteIntersection k A) (e : A ≃ₐ[k] B) :
    IsCompleteIntersection k B := by
  obtain ⟨R, _, _, hR, hfin, fs, hfs, ⟨e'⟩⟩ := h
  exact ⟨R, _, _, hR, hfin, fs, hfs, ⟨e.symm.trans e'⟩⟩

/-! ### Flatness -/

/-- For the local ring map `R_𝔭 → S_𝔮` of a prime `𝔮` of `S` lying over the prime `𝔭` of `R`,
flatness over `R_𝔭` is flatness over `R` (`Module.flat_iff_of_isLocalization`). -/
theorem Localization.AtPrime.flat_localRingHom_iff {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    (letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).toAlgebra
     Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)) ↔
      Module.Flat R (Localization.AtPrime q) := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).toAlgebra
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R S, RingHom.algebraMap_toAlgebra,
        Localization.localRingHom_to_map]
  exact Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _

/-! ### The fibre of a localization at a prime -/

/-- **The fibre of `S_𝔮` is the localization of the fibre of `S` at the prime corresponding to
`𝔮`.** Let `𝔔` be a prime of the fibre `κ(𝔭) ⊗_R A` and let `B` be the localization of `A` at the
prime `𝔮 = 𝔔 ∩ A`. Then `κ(𝔭) ⊗_R B` is the localization of `κ(𝔭) ⊗_R A` at `𝔔`. -/
theorem Ideal.Fiber.isLocalization_atPrime {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] (Q : Ideal (p.Fiber A)) [Q.IsPrime] (q : Ideal A) [q.IsPrime]
    (hQ : Q.comap (includeRight : A →ₐ[R] p.Fiber A) = q) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalization.AtPrime B q] :
    letI := (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
      (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
    IsLocalization.AtPrime (p.Fiber B) Q := by
  let := (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
    (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
  have : IsScalarTower p.ResidueField (p.Fiber A) (p.Fiber B) :=
    .of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right R p.ResidueField q.primeCompl B
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  refine IsLocalization.of_le (q.primeCompl.map (includeRight : A →ₐ[R] p.Fiber A)) Q.primeCompl
    ?_ fun u hu ↦ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact fun h ↦ hs (hQ ▸ h)
  obtain ⟨r, hr, s, hrs⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p u
  have hrκ : IsUnit (algebraMap R p.ResidueField r) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
    exact hr
  have hsu : r • u = algebraMap p.ResidueField (p.Fiber A) (algebraMap R p.ResidueField r) * u := by
    rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  have hsq : s ∉ q := by
    intro hs
    have hmem : r • u ∈ Q := by
      rw [hrs]
      exact (hQ ▸ hs : s ∈ Q.comap (includeRight : A →ₐ[R] p.Fiber A))
    rw [hsu] at hmem
    exact hu ((Ideal.unit_mul_mem_iff_mem _ (hrκ.map _)).1 hmem)
  have himg : IsUnit (algebraMap (p.Fiber A) (p.Fiber B) (r • u)) := by
    have h1 : algebraMap (p.Fiber A) (p.Fiber B) (1 ⊗ₜ s) = includeRight (algebraMap A B s) := by
      simp [RingHom.algebraMap_toAlgebra]
    rw [hrs, h1]
    exact (IsLocalization.map_units (M := q.primeCompl) B ⟨s, hsq⟩).map _
  rw [hsu, map_mul] at himg
  exact isUnit_of_mul_isUnit_right himg

/-- Being a complete intersection fibre depends on the prime `𝔭` only, not on how it is written. -/
theorem IsCompleteIntersection.fiber_congr {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {p₁ p₂ : Ideal R} [p₁.IsPrime] [p₂.IsPrime] (h : p₁ = p₂)
    (hci : IsCompleteIntersection p₁.ResidueField (p₁.Fiber B)) :
    IsCompleteIntersection p₂.ResidueField (p₂.Fiber B) := by
  subst h
  exact hci

/-! ### (1) ⟹ (3) -/

/-- **A syntomic algebra is flat with complete intersection fibres at every prime.** If `R → S` is
syntomic and `𝔮` is a prime of `S` over `𝔭`, then `S_𝔮` is flat over `R` and
`κ(𝔭) ⊗_R S_𝔮 = S_𝔮/𝔭S_𝔮` is a complete intersection over `κ(𝔭)`. -/
theorem Algebra.Syntomic.flat_localization_and_isCompleteIntersection_fiber {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.Syntomic R S] (q : Ideal S) [q.IsPrime] :
    Module.Flat R (Localization.AtPrime q) ∧
      IsCompleteIntersection (q.under R).ResidueField
        ((q.under R).Fiber (Localization.AtPrime q)) := by
  refine ⟨inferInstance, ?_⟩
  obtain ⟨Q, hQp, hQ⟩ := Ideal.Fiber.exists_comap_includeRight_eq (R := R) q _ rfl
  have hlci := Algebra.Syntomic.isLocalCompleteIntersection_fiber (R := R) (S := S) (q.under R)
  let := (Algebra.TensorProduct.map (AlgHom.id (q.under R).ResidueField (q.under R).ResidueField)
    (IsScalarTower.toAlgHom R S (Localization.AtPrime q))).toRingHom.toAlgebra
  have := Ideal.Fiber.isLocalization_atPrime (q.under R) Q q hQ (Localization.AtPrime q)
  have : IsScalarTower (q.under R).ResidueField ((q.under R).Fiber S)
      ((q.under R).Fiber (Localization.AtPrime q)) :=
    .of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  have h12 := (IsLocalCompleteIntersection.tfae (q.under R).ResidueField
    ((q.under R).Fiber S)).out 1 2
  exact h12.1 hlci Q _

/-! ### Generators after base change -/

/-- The generators of `T ⊗_R S` obtained by base change send the image of `a ∈ R[x_i]` in
`T[x_i]` to `1 ⊗ a(x)`. -/
theorem Algebra.Generators.algebraMap_baseChange_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {ι : Type*} (P : Algebra.Generators R S ι) (T : Type*) [CommRing T]
    [Algebra R T] (a : P.Ring) :
    algebraMap (P.baseChange T).Ring (T ⊗[R] S) (MvPolynomial.map (algebraMap R T) a) =
      includeRight (algebraMap P.Ring S a) := by
  rw [Algebra.Generators.algebraMap_apply, Algebra.Generators.algebraMap_apply,
    MvPolynomial.aeval_map_algebraMap, MvPolynomial.comp_aeval_apply]
  rfl

/-! ### The closed fibre of a localized presentation -/

namespace MvPolynomial.FiberAtPrime

variable {R₀ : Type*} [CommRing R₀] {ι : Type*} (Q : Ideal (MvPolynomial ι R₀)) [Q.IsPrime]

/-- **Lifting a regular sequence from the closed fibre.** Let `g_1, …, g_m ∈ R₀[x_i]` and let `rs`
be a regular sequence in `F = R₀[x_i]_Q/p₀R₀[x_i]_Q` generating the ideal generated by the images
of the `g_i`. Then, up to one unit of `F`, `rs` is the image of a sequence of elements of the ideal
`(g_1, …, g_m)`. -/
theorem exists_isRegular_mk {m : ℕ} (g : Fin m → MvPolynomial ι R₀) {rs : List (FiberAtPrime Q)}
    (hrs : RingTheory.Sequence.IsRegular (FiberAtPrime Q) rs)
    (hspan : Ideal.ofList rs = Ideal.span (Set.range (mk Q ∘ g))) :
    ∃ f : Fin rs.length → MvPolynomial ι R₀, (∀ j, f j ∈ Ideal.span (Set.range g)) ∧
      RingTheory.Sequence.IsRegular (FiberAtPrime Q) (List.ofFn (mk Q ∘ f)) ∧
      Ideal.ofList (List.ofFn (mk Q ∘ f)) = Ideal.span (Set.range (mk Q ∘ g)) := by
  classical
  have hmem : ∀ j : Fin rs.length, rs[j] ∈ Ideal.span (Set.range (mk Q ∘ g)) := fun j ↦
    hspan ▸ Ideal.subset_span (List.getElem_mem _)
  choose c hc using fun j ↦ Ideal.mem_span_range_iff_exists_fun.1 (hmem j)
  choose c' hc' using fun x : Fin rs.length × Fin m ↦ Ideal.Quotient.mk_surjective (c x.1 x.2)
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples Q.primeCompl Finset.univ c'
  choose a ha using fun x ↦ hs x (Finset.mem_univ x)
  have hu : IsUnit (mk Q s) :=
    (IsLocalization.map_units (M := Q.primeCompl) (Localization.AtPrime Q) s).map
      (Ideal.Quotient.mk _)
  have hmk : ∀ j, mk Q (∑ i, a (j, i) * g i) = mk Q s * rs[j] := fun j ↦ by
    rw [← hc j, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, ← mul_assoc, Function.comp_apply]
    congr 1
    rw [mk, RingHom.comp_apply, ha, Algebra.smul_def, map_mul, hc']
    rfl
  have hlist : List.ofFn (mk Q ∘ fun j ↦ ∑ i, a (j, i) * g i) = rs.map (mk Q s * ·) := by
    refine List.ext_getElem (by simp) fun j h₁ h₂ ↦ ?_
    rw [List.getElem_ofFn, List.getElem_map, Function.comp_apply, hmk]
    rfl
  refine ⟨fun j ↦ ∑ i, a (j, i) * g i, fun j ↦ Ideal.sum_mem _ fun i _ ↦
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩), ?_, ?_⟩
  · rw [hlist]
    exact hrs.map_mul_unit hu
  · rw [hlist, Ideal.ofList_map_mul_unit hu, hspan]

end MvPolynomial.FiberAtPrime

namespace Algebra.Generators

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*}
  (P : Algebra.Generators R S ι) (q : Ideal S) [q.IsPrime]
  (Q : Ideal (((q.comap (algebraMap P.Ring S)).under R).Fiber S)) [Q.IsPrime]

omit [Q.IsPrime] in
/-- For a presentation `S = R[x_i]/I`, a prime `𝔮` of `S` with corresponding prime `𝔮'` of
`R[x_i]`, `𝔭 = 𝔮' ∩ R`, and the prime `𝔔` of `κ(𝔭) ⊗_R S` corresponding to `𝔮`, the prime of
`κ(𝔭)[x_i]` below the maximal ideal of the closed fibre of `R[x_i]_{𝔮'}` is the prime below `𝔔`. -/
theorem basePrime_eq_comap
    (hQ : Q.comap (includeRight : S →ₐ[R] ((q.comap (algebraMap P.Ring S)).under R).Fiber S) = q) :
    MvPolynomial.FiberAtPrime.basePrime (q.comap (algebraMap P.Ring S)) =
      Q.comap (algebraMap
        (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
        (((q.comap (algebraMap P.Ring S)).under R).Fiber S)) := by
  ext w
  obtain ⟨d, hd, a, ha⟩ := MvPolynomial.FiberAtPrime.exists_C_mul_eq_residueMap _ w
  have hC : IsUnit (MvPolynomial.C (σ := ι)
      (algebraMap R ((q.comap (algebraMap P.Ring S)).under R).ResidueField d)) := by
    refine (isUnit_iff_ne_zero.2 ?_).map _
    rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
  have h1 : ∀ J : Ideal (MvPolynomial ι ((q.comap (algebraMap P.Ring S)).under R).ResidueField),
      w ∈ J ↔ MvPolynomial.FiberAtPrime.residueMap _ a ∈ J := fun J ↦ by
    rw [← ha, Ideal.unit_mul_mem_iff_mem _ hC]
  rw [h1, h1 (Q.comap _), MvPolynomial.FiberAtPrime.basePrime, Ideal.mem_comap, Ideal.mem_comap,
    MvPolynomial.FiberAtPrime.ofResidueField_residueMap,
    MvPolynomial.FiberAtPrime.mk_mem_maximalIdeal_iff, MvPolynomial.FiberAtPrime.residueMap,
    algebraMap_baseChange_map, ← Ideal.mem_comap, hQ]
  rfl

/-- The closed fibre of `R[x_i]_{𝔮'}` is the localization of `κ(𝔭)[x_i]` at the prime below the
prime `𝔔` of `κ(𝔭) ⊗_R S` corresponding to `𝔮`. -/
theorem isLocalization_fiberAtPrime
    (hQ : Q.comap (includeRight : S →ₐ[R] ((q.comap (algebraMap P.Ring S)).under R).Fiber S) = q) :
    letI := MvPolynomial.FiberAtPrime.algebra (q.comap (algebraMap P.Ring S))
    IsLocalization.AtPrime (MvPolynomial.FiberAtPrime (q.comap (algebraMap P.Ring S)))
      (Q.comap (algebraMap
        (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
        (((q.comap (algebraMap P.Ring S)).under R).Fiber S))) := by
  let := MvPolynomial.FiberAtPrime.algebra (q.comap (algebraMap P.Ring S))
  have hsub : (MvPolynomial.FiberAtPrime.basePrime (q.comap (algebraMap P.Ring S))).primeCompl =
      (Q.comap (algebraMap
        (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
        (((q.comap (algebraMap P.Ring S)).under R).Fiber S))).primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, P.basePrime_eq_comap q Q hQ]
  unfold IsLocalization.AtPrime
  rw [← hsub]
  exact MvPolynomial.FiberAtPrime.isLocalization _

end Algebra.Generators

/-! ### Nakayama: the lifted relations generate the kernel near `𝔮` -/

/-- **Near `𝔮` the kernel is generated by relations lifting generators of its fibre.** Let
`S = R[x_i]/I` be finitely presented, let `𝔮` be a prime of `S` with `S_𝔮` flat over `R`, with
corresponding prime `𝔮'` of `R[x_i]`, and let `f_1, …, f_c ∈ I` be such that the images of the
relations of the presentation lie in the ideal generated by the images of the `f_j` in the closed
fibre `R[x_i]_{𝔮'}/𝔭R[x_i]_{𝔮'}`. Then there is a `g ∉ 𝔮'` with `g I ⊆ (f_1, …, f_c)`. -/
theorem Algebra.Presentation.exists_notMem_mul_relation_mem {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {ι σ : Type*} [Finite σ] (P : Algebra.Presentation R S ι σ)
    (q : Ideal S) [q.IsPrime] [Module.Flat R (Localization.AtPrime q)] {c : ℕ}
    (f : Fin c → P.Ring) (hf : ∀ j, f j ∈ P.ker)
    (hgen : Ideal.span (Set.range
        (MvPolynomial.FiberAtPrime.mk (q.comap (algebraMap P.Ring S)) ∘ P.relation)) ≤
      Ideal.span (Set.range (MvPolynomial.FiberAtPrime.mk (q.comap (algebraMap P.Ring S)) ∘ f))) :
    ∃ g ∉ q.comap (algebraMap P.Ring S), ∀ i, g * P.relation i ∈ Ideal.span (Set.range f) := by
  classical
  have := Fintype.ofFinite σ
  set Q' := q.comap (algebraMap P.Ring S)
  set I := P.ker.map (algebraMap P.Ring (Localization.AtPrime Q'))
  set F := (Ideal.span (Set.range f)).map (algebraMap P.Ring (Localization.AtPrime Q'))
  set pA := (Q'.under R).map (algebraMap R (Localization.AtPrime Q'))
  have : Module.Flat R (Localization.AtPrime Q' ⧸ I) :=
    Module.Flat.of_linearEquiv (P.localizationAtPrimeAlgEquiv q).symm.toLinearEquiv
  have hFI : F ≤ I := Ideal.map_mono (Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hf j))
  have hmap : ∀ s : Set P.Ring, ((Ideal.span s).map
      (algebraMap P.Ring (Localization.AtPrime Q'))).map (Ideal.Quotient.mk pA) =
        Ideal.span (MvPolynomial.FiberAtPrime.mk Q' '' s) := fun s ↦ by
    rw [Ideal.map_map, Ideal.map_span]
    rfl
  have hI : I = (Ideal.span (Set.range P.relation)).map
      (algebraMap P.Ring (Localization.AtPrime Q')) := by
    rw [P.span_range_relation_eq_ker]
  have ha : I ≤ F ⊔ pA := by
    intro x hx
    have hx' : Ideal.Quotient.mk pA x ∈ F.map (Ideal.Quotient.mk pA) := by
      have h1 := Ideal.mem_map_of_mem (Ideal.Quotient.mk pA) (hI ▸ hx : x ∈ _)
      rw [hmap, ← Set.range_comp] at h1
      rw [hmap, ← Set.range_comp]
      exact hgen h1
    obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx'
    rw [show x = y + (x - y) by ring]
    exact Submodule.add_mem_sup hy (Ideal.Quotient.eq.1 hyx.symm)
  have hb := Ideal.map_inf_le_map_mul_of_flat (Q'.under R) I
  have hmax : pA ≤ IsLocalRing.maximalIdeal (Localization.AtPrime Q') :=
    MvPolynomial.FiberAtPrime.map_le_maximalIdeal Q'
  have hc : I ≤ F ⊔ IsLocalRing.maximalIdeal (Localization.AtPrime Q') • I := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (ha hx)
    have hzI : z ∈ I := by simpa using I.sub_mem hx (hFI hy)
    exact Submodule.add_mem_sup hy (Ideal.mul_mono_left hmax (hb ⟨hz, hzI⟩))
  have hfg : I.FG := by
    rw [hI]
    exact Ideal.FG.map (Submodule.fg_span (Set.finite_range _)) _
  have hjac : IsLocalRing.maximalIdeal (Localization.AtPrime Q') ≤ (⊥ : Ideal _).jacobson :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hIF : I ≤ F := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hc
  choose t ht htf using fun i ↦ Localization.AtPrime.exists_notMem_mul_mem_of_algebraMap_mem Q'
    (hIF (Ideal.mem_map_of_mem _ (P.relation_mem_ker i)))
  refine ⟨∏ i, t i, fun h ↦ ?_, fun i ↦ ?_⟩
  · obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (p := Q') (s := Finset.univ)).1 h
    exact ht i hi
  · rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ i), mul_comm (t i), mul_assoc]
    exact Ideal.mul_mem_left _ _ (htf i)

/-! ### The relative dimension at `𝔮` -/

/-- If `L + (d + c) = n + d` in `WithBot ℕ∞` for natural numbers `d`, `c`, `n`, then
`L + c = n`. -/
private theorem add_eq_of_add_add_eq {L : WithBot ℕ∞} {d c n : ℕ}
    (h : L + ((d : WithBot ℕ∞) + (c : WithBot ℕ∞)) = (n : WithBot ℕ∞) + (d : WithBot ℕ∞)) :
    L + (c : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
  have key : L + ((d + c : ℕ) : WithBot ℕ∞) = ((n + d : ℕ) : WithBot ℕ∞) := by
    push_cast
    exact h
  obtain ⟨hle, hL⟩ := WithBot.le_and_eq_tsub_of_add_natCast_eq key
  rw [hL]
  norm_cast
  omega

/-- **The relative dimension at `𝔮` from a regular sequence in the fibre.** Let `S = R[x_i]/I`
with `n` variables, let `𝔮` be a prime of `S` with corresponding prime `𝔮'` of `R[x_i]`,
`𝔭 = 𝔮' ∩ R`, and let `𝔔` be the corresponding prime of the fibre `κ(𝔭) ⊗_R S`. If the kernel of
`κ(𝔭)[x_i] → κ(𝔭) ⊗_R S` is generated, in a localization `A` at the prime below `𝔔`, by a regular
sequence of length `c`, then `dim_𝔮(S/R) + c = n`. -/
theorem Algebra.Generators.relativeDimensionAt_add_length_eq {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {ι : Type*} [Finite ι] (P : Algebra.Generators R S ι)
    (q : Ideal S) [q.IsPrime] (Q : Ideal (((q.comap (algebraMap P.Ring S)).under R).Fiber S))
    [Q.IsPrime]
    (hQ : Q.comap (includeRight : S →ₐ[R] ((q.comap (algebraMap P.Ring S)).under R).Fiber S) = q)
    (A : Type*) [CommRing A]
    [Algebra (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring A]
    [IsLocalization.AtPrime A (Q.comap (algebraMap
      (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
      (((q.comap (algebraMap P.Ring S)).under R).Fiber S)))]
    {rs : List A} (hrs : RingTheory.Sequence.IsRegular A rs)
    (hker : Ideal.ofList rs =
      (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).ker.map
        (algebraMap (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring A)) :
    Algebra.relativeDimensionAt R q + (rs.length : WithBot ℕ∞) =
      ((Nat.card ι : ℕ) : WithBot ℕ∞) := by
  have hp : q.under R = (q.comap (algebraMap P.Ring S)).under R :=
    (Ideal.under_under (B := P.Ring) q).symm
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing (Q.comap (algebraMap
    (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
    (((q.comap (algebraMap P.Ring S)).under R).Fiber S))).primeCompl A inferInstance
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A (Q.comap (algebraMap
    (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
    (((q.comap (algebraMap P.Ring S)).under R).Fiber S)))
  have h00P2 := PrimeSpectrum.localKrullDim_add_height_comap_eq_natCard_add_height _
    (IsScalarTower.toAlgHom ((q.comap (algebraMap P.Ring S)).under R).ResidueField
      (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
      (((q.comap (algebraMap P.Ring S)).under R).Fiber S))
    (P.baseChange _).algebraMap_surjective ⟨Q, ‹_›⟩
  have hA := IsLocalization.AtPrime.ringKrullDim_eq_height (Q.comap (algebraMap
    (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
    (((q.comap (algebraMap P.Ring S)).under R).Fiber S))) A
  have hQh : ringKrullDim (A ⧸ (P.baseChange
      ((q.comap (algebraMap P.Ring S)).under R).ResidueField).ker.map (algebraMap _ A)) =
      (Q.height : WithBot ℕ∞) :=
    ringKrullDim_quotient_map_ker_eq_height _ (P.baseChange _).algebraMap_surjective Q A
  have hreg := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hrs
  rw [hker, hQh, hA] at hreg
  have hQfin : Q.height ≠ ⊤ := by
    intro htop
    have hfin := (ringKrullDim_lt_top (R := A)).ne
    rw [hA, ← hreg, htop] at hfin
    exact hfin rfl
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hQfin
  rw [Algebra.relativeDimensionAt_eq_localKrullDim q _ hp Q hQ]
  refine add_eq_of_add_add_eq (d := d) ?_
  have h1 : ((d : ℕ) : WithBot ℕ∞) = (Q.height : WithBot ℕ∞) := by
    rw [← hd]
    norm_cast
  rw [h1, hreg]
  exact h00P2

/-! ### Principal neighbourhoods of principal neighbourhoods -/

/-- If some localization of `S_g`, `g ∉ 𝔮`, away from an element outside `𝔮S_g` is a relative
global complete intersection over `R`, then so is some localization of `S` away from an element
outside `𝔮`. -/
theorem Algebra.IsRelativeGlobalCompleteIntersection.exists_notMem_of_localizationAway
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime] {g : S}
    (hg : g ∉ q) {f : Localization.Away g}
    (hf : f ∉ Ideal.map (algebraMap S (Localization.Away g)) q)
    [Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away f)] :
    ∃ g' ∉ q, Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g') := by
  have hassoc := IsLocalization.Away.associated_sec_fst (S := Localization.Away g) g f
  have : IsLocalization.Away (g * (IsLocalization.Away.sec g f).1) (Localization.Away f) :=
    .mul_of_associated _ _ f hassoc
  exact ⟨g * (IsLocalization.Away.sec g f).1, ‹q.IsPrime›.mul_notMem hg fun hmem ↦
    hf ((Ideal.mem_iff_of_associated hassoc).mp (Ideal.mem_map_of_mem _ hmem)),
    .of_algEquiv ((Localization.algEquiv (Submonoid.powers (g * (IsLocalization.Away.sec g f).1))
      (Localization.Away f)).restrictScalars R).symm⟩

/-! ### (3) ⟹ (2) -/

/-- The extension of a prime `𝔮` of `S` to `S_g` is prime when `g ∉ 𝔮`. -/
private theorem isPrime_map_away_of_notMem {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime]
    {g : S} (hg : g ∉ q) : (q.map (algebraMap S (Localization.Away g))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) _ q ‹_›
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hg)

/-- The extension of a prime `𝔮` of `S` to `S_g` contracts back to `𝔮` when `g ∉ 𝔮`. -/
private theorem comap_map_away_of_notMem {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime]
    {g : S} (hg : g ∉ q) :
    (q.map (algebraMap S (Localization.Away g))).comap (algebraMap S (Localization.Away g)) = q :=
  IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) _ ‹_›
    ((Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hg)


/-- **Flat with a complete intersection fibre at `𝔮` gives a relative global complete intersection
near `𝔮`.** Let `R → S` be of finite presentation and let `𝔮` be a prime of `S` over `𝔭` such that
`S_𝔮` is flat over `R` and `κ(𝔭) ⊗_R S_𝔮` is a complete intersection over `κ(𝔭)`. Then `S_g` is a
relative global complete intersection over `R` for some `g ∉ 𝔮`. -/
theorem Algebra.exists_notMem_isRelativeGlobalCompleteIntersection_of_flat {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (q : Ideal S)
    [q.IsPrime] [Module.Flat R (Localization.AtPrime q)]
    (hci : IsCompleteIntersection (q.under R).ResidueField
      ((q.under R).Fiber (Localization.AtPrime q))) :
    ∃ g ∉ q, Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := by
  obtain ⟨n, m, ⟨P⟩⟩ := Algebra.Presentation.exists_presentation_fin R S
  have hp : q.under R = (q.comap (algebraMap P.Ring S)).under R :=
    (Ideal.under_under (B := P.Ring) q).symm
  obtain ⟨Q, hQp, hQ⟩ := Ideal.Fiber.exists_comap_includeRight_eq q _ hp
  have hci' := IsCompleteIntersection.fiber_congr hp hci
  let := (Algebra.TensorProduct.map
    (AlgHom.id ((q.comap (algebraMap P.Ring S)).under R).ResidueField
      ((q.comap (algebraMap P.Ring S)).under R).ResidueField)
    (IsScalarTower.toAlgHom R S (Localization.AtPrime q))).toRingHom.toAlgebra
  have := Ideal.Fiber.isLocalization_atPrime _ Q q hQ (Localization.AtPrime q)
  have : IsScalarTower ((q.comap (algebraMap P.Ring S)).under R).ResidueField
      (((q.comap (algebraMap P.Ring S)).under R).Fiber S)
      (((q.comap (algebraMap P.Ring S)).under R).Fiber (Localization.AtPrime q)) :=
    .of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra]
  have h00SG := (IsCompleteIntersection.localization_atPrime_tfae
    ((q.comap (algebraMap P.Ring S)).under R).ResidueField
    (((q.comap (algebraMap P.Ring S)).under R).Fiber S) Q
    (((q.comap (algebraMap P.Ring S)).under R).Fiber (Localization.AtPrime q))).out 1 4
  let := MvPolynomial.FiberAtPrime.algebra (q.comap (algebraMap P.Ring S))
  have : IsLocalization.AtPrime (MvPolynomial.FiberAtPrime (q.comap (algebraMap P.Ring S)))
      (Q.comap (algebraMap
        (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).toGenerators.Ring
        (((q.comap (algebraMap P.Ring S)).under R).Fiber S))) :=
    P.toGenerators.isLocalization_fiberAtPrime q Q hQ
  obtain ⟨rs, hrs, hrsker⟩ := h00SG.1 hci' (Fin n)
    (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).toGenerators
    (MvPolynomial.FiberAtPrime (q.comap (algebraMap P.Ring S)))
  have hkerspan : (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).ker.map
      (algebraMap (P.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
        (MvPolynomial.FiberAtPrime (q.comap (algebraMap P.Ring S)))) =
      Ideal.span (Set.range
        (MvPolynomial.FiberAtPrime.mk (q.comap (algebraMap P.Ring S)) ∘ P.relation)) := by
    rw [← (P.baseChange _).span_range_relation_eq_ker, Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    rw [Function.comp_apply, Function.comp_apply, Algebra.Presentation.baseChange_relation,
      RingHom.algebraMap_toAlgebra]
    exact MvPolynomial.FiberAtPrime.ofResidueField_residueMap _ _
  obtain ⟨f, hf, hfreg, hfspan⟩ :=
    MvPolynomial.FiberAtPrime.exists_isRegular_mk _ P.relation hrs (hrsker.trans hkerspan)
  have hfker : ∀ j, f j ∈ P.ker := fun j ↦ P.span_range_relation_eq_ker ▸ hf j
  obtain ⟨G, hG, hGf⟩ := P.exists_notMem_mul_relation_mem q f hfker (by
    rw [← hfspan, Ideal.ofList_ofFn])
  have : IsLocalization.AtPrime (MvPolynomial.FiberAtPrime (q.comap (algebraMap P.Ring S)))
      (Q.comap (algebraMap
        (P.toGenerators.baseChange ((q.comap (algebraMap P.Ring S)).under R).ResidueField).Ring
        (((q.comap (algebraMap P.Ring S)).under R).Fiber S))) :=
    P.toGenerators.isLocalization_fiberAtPrime q Q hQ
  have hdim := P.toGenerators.relativeDimensionAt_add_length_eq q Q hQ _ hfreg
    (hfspan.trans hkerspan.symm)
  rw [List.length_ofFn] at hdim
  have hGq : algebraMap P.Ring S G ∉ q := hG
  have := isPrime_map_away_of_notMem q hGq
  have hcomap := comap_map_away_of_notMem q hGq
  have hdimG : Algebra.relativeDimensionAt R
      (q.map (algebraMap S (Localization.Away (algebraMap P.Ring S G)))) +
        ((Nat.card (Unit ⊕ Fin rs.length) : ℕ) : WithBot ℕ∞) =
      ((Nat.card (Unit ⊕ Fin n) : ℕ) : WithBot ℕ∞) := by
    rw [← Algebra.relativeDimensionAt_comap_eq (algebraMap P.Ring S G),
      Algebra.relativeDimensionAt_congr hcomap]
    have hc : ∀ k, Nat.card (Unit ⊕ Fin k) = 1 + k := fun k ↦ by simp
    rw [hc, hc]
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hdim
    push_cast
    rw [add_left_comm, hdim, add_comm]
  obtain ⟨h, hh, hrgci⟩ := (P.localizationAwayCompOfMulMem G
    (Localization.Away (algebraMap P.Ring S G)) f hfker
    hGf).exists_notMem_isRelativeGlobalCompleteIntersection _ hdimG
  have := Algebra.IsRelativeGlobalCompleteIntersection.of_presentation _ (hP := hrgci)
  exact Algebra.IsRelativeGlobalCompleteIntersection.exists_notMem_of_localizationAway q hGq hh

/-! ### Syntomic neighbourhoods -/

/-- `S_𝔮` is the local ring of `S_g`, `g ∉ 𝔮`, at the prime `𝔮S_g`, as an `R`-algebra. -/
noncomputable def Localization.AtPrime.algEquivMapAway {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] (g : S)
    [(q.map (algebraMap S (Localization.Away g))).IsPrime]
    (hcomap : (q.map (algebraMap S (Localization.Away g))).comap
      (algebraMap S (Localization.Away g)) = q) :
    Localization.AtPrime q ≃ₐ[R]
      Localization.AtPrime (q.map (algebraMap S (Localization.Away g))) :=
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers g)
    (Localization.AtPrime (q.map (algebraMap S (Localization.Away g))))
    (q.map (algebraMap S (Localization.Away g)))
  have hsub : ((q.map (algebraMap S (Localization.Away g))).comap
      (algebraMap S (Localization.Away g))).primeCompl = q.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  have : IsLocalization q.primeCompl
      (Localization.AtPrime (q.map (algebraMap S (Localization.Away g)))) := hsub ▸ this
  (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) _).restrictScalars R

/-- Let `R → S` be a ring map and let `𝔮` be a prime of `S` lying over the prime `𝔭` of `R`. The
following are equivalent:

1. there is a `g ∈ S`, `g ∉ 𝔮`, such that `R → S_g` is syntomic;
2. there is a `g ∈ S`, `g ∉ 𝔮`, such that `S_g` is a relative global complete intersection over
   `R`;
3. there is a `g ∈ S`, `g ∉ 𝔮`, such that `R → S_g` is of finite presentation, the local ring map
   `R_𝔭 → S_𝔮` is flat, and `S_𝔮/𝔭S_𝔮` is a complete intersection over `κ(𝔭)`. -/
@[stacks 00SY "The principal localization `S_g` is `Localization.Away g`, the local ring map
`R_𝔭 → S_𝔮` is `Localization.localRingHom` for the lying-over relation, and `S_𝔮/𝔭S_𝔮` is the
fibre `𝔭.Fiber S_𝔮 = κ(𝔭) ⊗_R S_𝔮`, canonically a `κ(𝔭)`-algebra, which is `S_𝔮/𝔭S_𝔮` because
`S_𝔮` is an `R_𝔭`-algebra."]
theorem Algebra.exists_notMem_syntomic_tfae {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    List.TFAE
      [∃ g ∉ q, Algebra.Syntomic R (Localization.Away g),
        ∃ g ∉ q, Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g),
        ∃ g ∉ q,
          Algebra.FinitePresentation R (Localization.Away g) ∧
            (letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
              (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).toAlgebra
             Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)) ∧
              IsCompleteIntersection p.ResidueField (p.Fiber (Localization.AtPrime q))] := by
  have hunder : ∀ g ∉ q, (q.map (algebraMap S (Localization.Away g))).under R = p := fun g hg ↦ by
    have := isPrime_map_away_of_notMem q hg
    rw [Ideal.under, IsScalarTower.algebraMap_eq R S (Localization.Away g), ← Ideal.comap_comap,
      comap_map_away_of_notMem q hg, ← Ideal.under, (Ideal.over_def q p).symm]
  have hfib : ∀ g (hg : g ∉ q), have := isPrime_map_away_of_notMem q hg
      (p.Fiber (Localization.AtPrime q) ≃ₐ[p.ResidueField]
        p.Fiber (Localization.AtPrime (q.map (algebraMap S (Localization.Away g))))) :=
    fun g hg ↦
      have := isPrime_map_away_of_notMem q hg
      Algebra.TensorProduct.congr AlgEquiv.refl
        (Localization.AtPrime.algEquivMapAway q g (comap_map_away_of_notMem q hg))
  tfae_have 2 → 1 := by
    rintro ⟨g, hg, h⟩
    exact ⟨g, hg, Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection R _⟩
  tfae_have 1 → 3 := by
    rintro ⟨g, hg, h⟩
    have := isPrime_map_away_of_notMem q hg
    obtain ⟨hflat, hci⟩ := Algebra.Syntomic.flat_localization_and_isCompleteIntersection_fiber
      (R := R) (q.map (algebraMap S (Localization.Away g)))
    refine ⟨g, hg, inferInstance, ?_, ?_⟩
    · rw [Localization.AtPrime.flat_localRingHom_iff]
      exact Module.Flat.of_linearEquiv
        (Localization.AtPrime.algEquivMapAway q g (comap_map_away_of_notMem q hg)).toLinearEquiv
    · exact (IsCompleteIntersection.fiber_congr (hunder g hg) hci).of_algEquiv (hfib g hg).symm
  tfae_have 3 → 2 := by
    rintro ⟨g, hg, hfp, hflat, hci⟩
    have := isPrime_map_away_of_notMem q hg
    rw [Localization.AtPrime.flat_localRingHom_iff] at hflat
    have e := Localization.AtPrime.algEquivMapAway (R := R) q g (comap_map_away_of_notMem q hg)
    have : Module.Flat R (Localization.AtPrime (q.map (algebraMap S (Localization.Away g)))) :=
      Module.Flat.of_linearEquiv e.symm.toLinearEquiv
    obtain ⟨f, hf, hrgci⟩ := Algebra.exists_notMem_isRelativeGlobalCompleteIntersection_of_flat
      (q.map (algebraMap S (Localization.Away g)))
      (IsCompleteIntersection.fiber_congr (hunder g hg).symm (hci.of_algEquiv (hfib g hg)))
    exact Algebra.IsRelativeGlobalCompleteIntersection.exists_notMem_of_localizationAway q hg hf
  tfae_finish

end
