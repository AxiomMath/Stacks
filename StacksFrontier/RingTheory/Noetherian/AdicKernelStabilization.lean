module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Maps
public import StacksFrontier.RingTheory.Noetherian.ArtinRees

/-!
# Stabilization of adic kernels

Let `R` be a Noetherian ring, `J ⊆ R` an ideal and `f : M →ₗ[R] N` a map of `R`-modules with
`N` finite. The Artin–Rees lemma says that the `J`-adic filtration on the image of `f` is
induced by the `J`-adic filtration on `N` up to a shift: there is a constant `c` with
`Jⁿ N ⊓ f(M) = Jⁿ⁻ᶜ • (Jᶜ N ⊓ f(M))` for all `n ≥ c`. The consequence used here is a
*stabilization* statement: the preimage `f⁻¹(Jⁿ N)` is squeezed between `ker f` and
`ker f + Jᵐ M` as soon as `n ≥ m + c`, so its image in the fixed quotient `M ⧸ Jᵐ M` no
longer depends on `n` — it is already the image of `ker f`. In other words the inverse system
`n ↦ f⁻¹(Jⁿ N) / Jᵐ M` is eventually constant with value `ker f / (ker f ⊓ Jᵐ M)`.

Specializing `f` to the inclusion of a submodule `K ⊆ M` gives the comparison between the
*subspace* filtration `Jᵐ M ⊓ K` and the *intrinsic* filtration `Jⁿ K`: the former is
contained in the latter once `m ≥ n + c`. Consequently the two-step quotient
`(K / (Jᵐ M ⊓ K)) / Jⁿ (K / (Jᵐ M ⊓ K))` is canonically the intrinsic adic quotient
`K / Jⁿ K`, by the third isomorphism theorem, and the same holds after replacing `K` by its
image in a quotient of `M` or under a linear map.

Throughout, `Jⁿ M` is written `J ^ n • (⊤ : Submodule R M)`; names abbreviate this as
`pow_smul`, and the equivalences producing a quotient of that shape are prefixed `adic`.

## Main results

* `Stacks.AdicCompletion.map_mkQ_comap_eq_map_mkQ_ker`: the image of `f⁻¹(S)` in `M ⧸ p`
  equals the image of `ker f`, whenever `f⁻¹(S) ≤ ker f + p`.
* `Stacks.AdicCompletion.exists_comap_pow_smul_le_ker_sup`: the Artin–Rees shift, in the form
  `f⁻¹(Jˡ N) ≤ ker f + Jᵐ M` for `l ≥ m + c`.
* `Stacks.AdicCompletion.exists_map_mkQ_comap_pow_smul_eq`: the stabilization statement, that
  the image of `f⁻¹(Jⁿ N)` in `M ⧸ Jᵐ M` is the image of `ker f` for all large `n`.
* `Stacks.AdicCompletion.exists_comap_subtype_pow_smul_le` and
  `Stacks.AdicCompletion.exists_comap_subtype_pow_smul_sup_eq`: the subspace filtration on a
  submodule is finer than its intrinsic adic filtration, up to a shift.
* `Stacks.AdicCompletion.adicQuotientQuotientEquiv` and
  `Stacks.AdicCompletion.exists_adicQuotientQuotientEquiv`: the resulting identification of
  `(M ⧸ L) ⧸ Jⁿ (M ⧸ L)` with `M ⧸ Jⁿ M`.
* `Stacks.AdicCompletion.adicRangeMkQQuotientEquiv` and
  `Stacks.AdicCompletion.adicRangeQuotientEquiv`: the same identification for the image of a
  submodule in a quotient of `M`, respectively under an arbitrary linear map.
* `Stacks.AdicCompletion.exists_map_comap_pow_smul_restrictScalars_eq` and
  `Stacks.AdicCompletion.exists_comap_subtype_pow_smul_restrictScalars_le`: the two
  stabilization statements for a finite module over an `R`-algebra `A`, with the filtration
  taken by powers of an ideal of the base ring `R`.

## Implementation notes

The engine is `comap_smul_top_eq_ker_sup_smul_comap`, the first equality of the map form of
Artin–Rees, which takes the Artin–Rees identity as a hypothesis and so needs no finiteness
assumption of its own; the finiteness of `N` enters only through
`Ideal.exists_pow_inf_eq_pow_smul` applied to `LinearMap.range f`. In particular the source
module `M` is never assumed finite, which matters for the inclusion of a submodule, where the
source is the submodule and the target the ambient module.

For an `A`-module filtered by powers of an ideal `J` of a base ring `R`, the two filtrations
`J ^ n • (⊤ : Submodule R M)` and `(J.map (algebraMap R A)) ^ n • (⊤ : Submodule A M)` have the
same underlying set, by `Submodule.restrictScalars_map_smul_eq`; the `restrictScalars`
statements are obtained from their `A`-linear counterparts through that identification.

## References

* [Stacks Project, Tag 00IN](https://stacks.math.columbia.edu/tag/00IN)
* [Stacks Project, Tag 00IO](https://stacks.math.columbia.edu/tag/00IO)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public section

namespace Stacks.AdicCompletion

/-- If the preimage `f⁻¹(S)` is contained in `ker f + p`, then `f⁻¹(S)` and `ker f` have the
same image in `M ⧸ p`. One inclusion is `ker f ≤ f⁻¹(S)`; for the other, a representative of
`f⁻¹(S)` differs from one of `ker f` by an element of `p`, which dies in the quotient. -/
theorem map_mkQ_comap_eq_map_mkQ_ker
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (S : Submodule R N) (p : Submodule R M)
    (h : S.comap f ≤ LinearMap.ker f ⊔ p) :
    Submodule.map p.mkQ (S.comap f) = Submodule.map p.mkQ (LinearMap.ker f) := by
  refine le_antisymm ?_ (Submodule.map_mono (LinearMap.ker_le_comap f))
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (h hx)
  have hb0 : p.mkQ b = 0 := (Submodule.Quotient.mk_eq_zero _).2 hb
  rw [map_add, hb0, add_zero]
  exact Submodule.mem_map_of_mem ha

/-- **Artin–Rees shift for a preimage.** For a Noetherian ring `R`, an ideal `J` and a linear
map `f : M →ₗ[R] N` with `N` a finite `R`-module, there is a constant `c` such that
`f⁻¹(Jˡ N) ⊆ ker f + Jᵐ M` whenever `l ≥ m + c`. -/
theorem exists_comap_pow_smul_le_ker_sup
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (J : Ideal R) (f : M →ₗ[R] N) :
    ∃ c : ℕ, ∀ m l : ℕ, m + c ≤ l →
      (J ^ l • (⊤ : Submodule R N)).comap f ≤
        LinearMap.ker f ⊔ J ^ m • (⊤ : Submodule R M) := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (I := J) (LinearMap.range f)
  refine ⟨c, fun m l hl => ?_⟩
  rw [comap_smul_top_eq_ker_sup_smul_comap f J c l (by omega) (hc l (by omega)),
    Submodule.add_eq_sup]
  exact sup_le_sup_left (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega)) le_top) _

/-- **Stabilization of adic kernels.** For a Noetherian ring `R`, an ideal `J` and a linear map
`f : M →ₗ[R] N` with `N` a finite `R`-module, the image of `f⁻¹(Jⁿ N)` in the fixed quotient
`M ⧸ Jᵐ M` is independent of `n` once `n` is large, and equals the image of `ker f`. -/
theorem exists_map_mkQ_comap_pow_smul_eq
    {R M N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (J : Ideal R) (f : M →ₗ[R] N) (m : ℕ) :
    ∃ c : ℕ, ∀ n : ℕ, m + c ≤ n →
      Submodule.map (J ^ m • (⊤ : Submodule R M)).mkQ
          ((J ^ n • (⊤ : Submodule R N)).comap f) =
        Submodule.map (J ^ m • (⊤ : Submodule R M)).mkQ (LinearMap.ker f) := by
  obtain ⟨c, hc⟩ := exists_comap_pow_smul_le_ker_sup J f
  exact ⟨c, fun n hn => map_mkQ_comap_eq_map_mkQ_ker f _ _ (hc m n hn)⟩

/-- **Artin–Rees for a submodule.** For a Noetherian ring `R`, an ideal `J` and a submodule `K`
of a finite `R`-module `M`, there is a constant `c` such that the subspace filtration is finer
than the intrinsic one after a shift: `Jᵐ M ⊓ K ⊆ Jⁿ K` whenever `m ≥ n + c`. -/
theorem exists_comap_subtype_pow_smul_le
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (J : Ideal R) (K : Submodule R M) :
    ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m →
      (J ^ m • (⊤ : Submodule R M)).comap K.subtype ≤ J ^ n • (⊤ : Submodule R K) := by
  obtain ⟨c, hc⟩ := exists_comap_pow_smul_le_ker_sup J K.subtype
  exact ⟨c, fun n m hm => by simpa [Submodule.ker_subtype] using hc n m hm⟩

/-- The shifted subspace filtration on a submodule is absorbed by its intrinsic adic
filtration: for `m ≥ n + c` the submodule `Jᵐ M ⊓ K` adds nothing to `Jⁿ K`. -/
theorem exists_comap_subtype_pow_smul_sup_eq
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (J : Ideal R) (K : Submodule R M) :
    ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m →
      (J ^ m • (⊤ : Submodule R M)).comap K.subtype ⊔ J ^ n • (⊤ : Submodule R K) =
        J ^ n • (⊤ : Submodule R K) := by
  obtain ⟨c, hc⟩ := exists_comap_subtype_pow_smul_le J K
  exact ⟨c, fun n m h => sup_eq_right.mpr (hc n m h)⟩

/-- **Third isomorphism theorem for an adic quotient.** If a submodule `L ⊆ M` is contained in
`Jⁿ M`, then quotienting `M ⧸ L` by its own `Jⁿ`-multiple recovers `M ⧸ Jⁿ M`. The point is
that `Jⁿ (M ⧸ L)` is the image of `Jⁿ M` under the projection, because the projection is
surjective. -/
def adicQuotientQuotientEquiv {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (J : Ideal R) (L : Submodule R M)
    (n : ℕ) (h : L ≤ J ^ n • (⊤ : Submodule R M)) :
    ((M ⧸ L) ⧸ J ^ n • (⊤ : Submodule R (M ⧸ L))) ≃ₗ[R] M ⧸ J ^ n • (⊤ : Submodule R M) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ])).trans
      (Submodule.quotientQuotientEquivQuotient L (J ^ n • ⊤) h)

/-- `adicQuotientQuotientEquiv` is the identity on representatives. -/
theorem adicQuotientQuotientEquiv_mk_mk {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (J : Ideal R) (L : Submodule R M)
    (n : ℕ) (h : L ≤ J ^ n • (⊤ : Submodule R M)) (x : M) :
    adicQuotientQuotientEquiv J L n h
        (Submodule.Quotient.mk (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x := by
  simp only [adicQuotientQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  rfl

/-- **Artin–Rees for adic quotients of a submodule.** For a Noetherian ring `R`, an ideal `J`
and a submodule `K` of a finite `R`-module `M`, there is a constant `c` such that for
`m ≥ n + c` the quotient of `K ⧸ (Jᵐ M ⊓ K)` by its `Jⁿ`-multiple is the intrinsic adic
quotient `K ⧸ Jⁿ K`, by an isomorphism which is the identity on representatives. -/
theorem exists_adicQuotientQuotientEquiv
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (J : Ideal R) (K : Submodule R M) :
    ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m →
      ∃ e : ((K ⧸ (J ^ m • (⊤ : Submodule R M)).comap K.subtype) ⧸
          J ^ n • (⊤ : Submodule R
            (K ⧸ (J ^ m • (⊤ : Submodule R M)).comap K.subtype))) ≃ₗ[R]
          K ⧸ J ^ n • (⊤ : Submodule R K),
        ∀ x : K, e (Submodule.Quotient.mk (Submodule.Quotient.mk x)) =
          Submodule.Quotient.mk x := by
  obtain ⟨c, hc⟩ := exists_comap_subtype_pow_smul_le J K
  exact ⟨c, fun n m hm => ⟨adicQuotientQuotientEquiv J _ n (hc n m hm),
    adicQuotientQuotientEquiv_mk_mk J _ n (hc n m hm)⟩⟩

/-- The image of a submodule `K ⊆ M` in the quotient `M ⧸ L` is `K` modulo `L ⊓ K`: the
composite `K → M → M ⧸ L` has kernel `L ⊓ K` and the stated range. -/
noncomputable def quotientComapSubtypeEquivRangeMkQ
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M) :
    (K ⧸ L.comap K.subtype) ≃ₗ[R] LinearMap.range (L.mkQ.comp K.subtype) :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    simp [LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero])).trans
      (L.mkQ.comp K.subtype).quotKerEquivRange

/-- `quotientComapSubtypeEquivRangeMkQ` sends the class of `x : K` to the class of `x` in
`M ⧸ L`. -/
theorem quotientComapSubtypeEquivRangeMkQ_mk
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M) (x : K) :
    ((quotientComapSubtypeEquivRangeMkQ K L (Submodule.Quotient.mk x) :
      LinearMap.range (L.mkQ.comp K.subtype)) : M ⧸ L) = L.mkQ x := by
  simp [quotientComapSubtypeEquivRangeMkQ, LinearMap.quotKerEquivRange_apply_mk]

/-- The adic quotients of the image of `K` in `M ⧸ L` are the intrinsic adic quotients of `K`,
once `L ⊓ K` is contained in `Jⁿ K`. Combine
`quotientComapSubtypeEquivRangeMkQ` with `adicQuotientQuotientEquiv`. -/
noncomputable def adicRangeMkQQuotientEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J : Ideal R) (K L : Submodule R M) (n : ℕ)
    (h : L.comap K.subtype ≤ J ^ n • (⊤ : Submodule R K)) :
    (LinearMap.range (L.mkQ.comp K.subtype) ⧸
      J ^ n • (⊤ : Submodule R (LinearMap.range (L.mkQ.comp K.subtype)))) ≃ₗ[R]
        K ⧸ J ^ n • (⊤ : Submodule R K) :=
  (Submodule.Quotient.equiv _ _ (quotientComapSubtypeEquivRangeMkQ K L) (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).symm.trans
      (adicQuotientQuotientEquiv J _ n h)

/-- The image of a submodule `K ⊆ M` under a linear map `p : M →ₗ[R] N` is `K` modulo
`ker p ⊓ K`: the restriction of `p` to `K` has kernel `ker p ⊓ K` and the stated range. -/
noncomputable def quotientComapSubtypeEquivRange
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : M →ₗ[R] N) (K : Submodule R M) :
    (K ⧸ (LinearMap.ker p).comap K.subtype) ≃ₗ[R] LinearMap.range (p.comp K.subtype) :=
  (Submodule.quotEquivOfEq _ _ (by ext x; rfl)).trans (p.comp K.subtype).quotKerEquivRange

/-- `quotientComapSubtypeEquivRange` sends the class of `x : K` to `p x`. -/
theorem quotientComapSubtypeEquivRange_mk
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : M →ₗ[R] N) (K : Submodule R M) (x : K) :
    ((quotientComapSubtypeEquivRange p K (Submodule.Quotient.mk x) :
      LinearMap.range (p.comp K.subtype)) : N) = p x := by
  simp [quotientComapSubtypeEquivRange, LinearMap.quotKerEquivRange_apply_mk]

/-- The adic quotients of the image of `K` under `p` are the intrinsic adic quotients of `K`,
once `ker p ⊓ K` is contained in `Jⁿ K`. Combine `quotientComapSubtypeEquivRange` with
`adicQuotientQuotientEquiv`. -/
noncomputable def adicRangeQuotientEquiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (p : M →ₗ[R] N) (K : Submodule R M) (n : ℕ)
    (h : (LinearMap.ker p).comap K.subtype ≤ J ^ n • (⊤ : Submodule R K)) :
    (LinearMap.range (p.comp K.subtype) ⧸
      J ^ n • (⊤ : Submodule R (LinearMap.range (p.comp K.subtype)))) ≃ₗ[R]
        K ⧸ J ^ n • (⊤ : Submodule R K) :=
  (Submodule.Quotient.equiv _ _ (quotientComapSubtypeEquivRange p K) (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).symm.trans
      (adicQuotientQuotientEquiv J _ n h)

/-- `adicRangeQuotientEquiv` is the identity on representatives, read through
`quotientComapSubtypeEquivRange`. -/
theorem adicRangeQuotientEquiv_mk
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (p : M →ₗ[R] N) (K : Submodule R M) (n : ℕ)
    (h : (LinearMap.ker p).comap K.subtype ≤ J ^ n • (⊤ : Submodule R K)) (x : K) :
    adicRangeQuotientEquiv J p K n h
        (Submodule.Quotient.mk
          (quotientComapSubtypeEquivRange p K (Submodule.Quotient.mk x))) =
      Submodule.Quotient.mk x := by
  simp [adicRangeQuotientEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    adicQuotientQuotientEquiv_mk_mk]

/-- In a commuting square `a ∘ p = q ∘ f` with `p : M →ₗ[R] P` surjective, the image of
`ker a` under a map `t : P →ₗ[R] T` is the image of `f⁻¹(ker q)` under `t ∘ p`. This transports
a kernel computed downstairs back to one computed upstairs. -/
theorem map_ker_eq_map_comap_ker
    {R M N P Q T : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T]
    (f : M →ₗ[R] N) (p : M →ₗ[R] P) (q : N →ₗ[R] Q)
    (a : P →ₗ[R] Q) (t : P →ₗ[R] T)
    (hp : Function.Surjective p) (h : a.comp p = q.comp f) :
    (LinearMap.ker a).map t = ((LinearMap.ker q).comap f).map (t.comp p) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := hp y
    exact ⟨z, (LinearMap.congr_fun h z).symm.trans hy, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨p z, (LinearMap.congr_fun h z).trans hz, rfl⟩

/-- The `J A`-adic filtration of an `A`-module, viewed over `R`, is the `J`-adic one. -/
private theorem restrictScalars_map_pow_smul_top
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] (J : Ideal R) (n : ℕ) :
    ((J.map (algebraMap R A)) ^ n • (⊤ : Submodule A M)).restrictScalars R =
      J ^ n • (⊤ : Submodule R M) := by
  rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]

/-- **Stabilization of adic kernels over a base ring.** Let `A` be a Noetherian `R`-algebra,
`f : M →ₗ[A] N` a map of `A`-modules with `N` finite over `A`, and `J ⊆ R` an ideal. There is a
constant `c` such that for `l ≥ m + c` and any `R`-linear map `p` out of `M` killing `Jᵐ M`,
the images of `f⁻¹(Jˡ N)` and of `ker f` under `p` agree. The filtration is by powers of `J`
acting through `R`, which is the same as the filtration by powers of `J A`. -/
theorem exists_map_comap_pow_smul_restrictScalars_eq
    {R A M N P : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [Module.Finite A N] [AddCommGroup P] [Module R P]
    (J : Ideal R) (f : M →ₗ[A] N) :
    ∃ c : ℕ, ∀ m l : ℕ, m + c ≤ l →
      ∀ p : M →ₗ[R] P, J ^ m • (⊤ : Submodule R M) ≤ LinearMap.ker p →
      ((J ^ l • (⊤ : Submodule R N)).comap (f.restrictScalars R)).map p =
        ((LinearMap.ker f).restrictScalars R).map p := by
  obtain ⟨c, hc⟩ := exists_comap_pow_smul_le_ker_sup (J.map (algebraMap R A)) f
  refine ⟨c, fun m l hl p hp => ?_⟩
  refine le_antisymm ?_ ?_
  · rintro z ⟨x, hx, rfl⟩
    have hx' : f x ∈ (J.map (algebraMap R A)) ^ l • (⊤ : Submodule A N) := by
      rw [← Submodule.restrictScalars_mem R, restrictScalars_map_pow_smul_top]
      exact hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hc m l hl hx')
    refine ⟨a, ha, ?_⟩
    have hb' : b ∈ J ^ m • (⊤ : Submodule R M) := by
      rw [← restrictScalars_map_pow_smul_top (A := A)]
      exact hb
    rw [← hab, map_add, hp hb', add_zero]
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    have hx0 : f x = 0 := hx
    change f x ∈ J ^ l • (⊤ : Submodule R N)
    rw [hx0]
    exact zero_mem _

/-- **Artin–Rees for a submodule over a base ring.** Let `A` be a Noetherian `R`-algebra, `M` a
finite `A`-module, `K ⊆ M` an `A`-submodule and `J ⊆ R` an ideal. There is a constant `c` such
that `Jᵐ M ⊓ K ⊆ Jⁿ K` whenever `m ≥ n + c`, with both filtrations taken for the action of the
base ring `R`. -/
theorem exists_comap_subtype_pow_smul_restrictScalars_le
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M]
    [Module R M] [IsScalarTower R A M] [Module.Finite A M]
    (J : Ideal R) (K : Submodule A M) :
    ∃ c : ℕ, ∀ n m : ℕ, n + c ≤ m →
      (J ^ m • (⊤ : Submodule R M)).comap (K.restrictScalars R).subtype ≤
        J ^ n • (⊤ : Submodule R (K.restrictScalars R)) := by
  obtain ⟨c, hc⟩ := exists_comap_subtype_pow_smul_le (J.map (algebraMap R A)) K
  refine ⟨c, fun n m hm x hx => ?_⟩
  have hxA : (x : M) ∈ (J.map (algebraMap R A)) ^ m • (⊤ : Submodule A M) := by
    rw [← Submodule.restrictScalars_mem R, restrictScalars_map_pow_smul_top]
    exact hx
  exact (restrictScalars_map_pow_smul_top (A := A) (M := K) J n).le (hc n m hm hxA)

end Stacks.AdicCompletion
