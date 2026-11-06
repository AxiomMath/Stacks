module

import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Smooth.Local
import Mathlib.Tactic.Monotonicity.Lemmas

import StacksFrontier.RingTheory.Kaehler.BaseChange
import StacksFrontier.RingTheory.Smooth.CotangentAtMaximalIdeal
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.Syntomic.Basic
public import StacksFrontier.RingTheory.Smooth.LocusBaseChange
public import StacksFrontier.RingTheory.Kaehler.Separable
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# Regularity at a closed point equals smoothness, over an algebraically closed field

Proof of Stacks 00TS. Let `k` be an algebraically closed field, let `S` be a finite type
`k`-algebra, let `𝔪 ⊆ S` be a maximal ideal with residue field `κ(𝔪) = S/𝔪` and let `S_𝔪` be the
local ring of `S` at `𝔪`. The five conditions of the lemma are that `S_𝔪` is regular, that
`dim_{κ(𝔪)} Ω_{S/k} ⊗_S κ(𝔪)` is at most, respectively equal to, `dim S_𝔪`, that `S_g` is smooth
over `k` for some `g ∉ 𝔪`, and that `S/k` is smooth at `𝔪`.

The first three are equivalent to one another by Lemma 00TR together with the definition of a
regular local ring, in two steps. First, the fibre of the differentials is the Zariski cotangent
space, `Ω_{S/k} ⊗_S κ(𝔪) ≅ 𝔪/𝔪²` (Lemma 00TR, available as
`finrank_kaehler_baseChange_eq_finrank_cotangent`). Second, the cotangent space is unchanged by
passing to the local ring, `𝔪/𝔪² ≅ 𝔪S_𝔪/(𝔪S_𝔪)²`: the canonical map is surjective because for
`s ∉ 𝔪` one may choose `t ∈ S` with `1 - st ∈ 𝔪`, so that `x/s ≡ xt` modulo `(𝔪S_𝔪)²`, and it is
injective because `sx ∈ 𝔪²` for such an `s` forces `x = t(sx) + (1 - st)x ∈ 𝔪²`. Since
`dim S_𝔪 ≤ dim_{κ(𝔪)} 𝔪S_𝔪/(𝔪S_𝔪)²` always holds, the inequality and the equality say the same
thing, and by definition they say that `S_𝔪` is regular.

The last two conditions are equivalent to each other over any base, and this is Mathlib's:
smoothness at `𝔪` is formal smoothness of `S_𝔪`, the smooth locus of a finitely presented algebra
is open (`Algebra.isOpen_smoothLocus`) and a standard open `D(g)` lies in it exactly when `S_g` is
smooth (`Algebra.basicOpen_subset_smoothLocus_iff_smooth`).

The substance of the lemma is that regularity at `𝔪` is equivalent to smoothness near `𝔪`. It is
proved here by the Jacobian criterion for local algebras in a numerical form. Choose a surjection
`k[x_1, …, x_m] → S` and let `A` be the localization of `k[x_1, …, x_m]` at the maximal ideal
corresponding to `𝔪`, so that `A` is a regular local ring, formally smooth over `k`, with `Ω[A⁄k]`
finite free of rank `dim A`, and `S_𝔪 = A/I`. Rank-nullity for the map
`κ ⊗_A I → κ ⊗_A Ω[A⁄k]` whose injectivity is Mathlib's criterion
(`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`) reads

  `S_𝔪` is smooth over `k`  ↔  `μ(I) + dim_κ Ω_{S_𝔪/k} ⊗ κ = dim A`,

the source of the map having dimension the minimal number of generators `μ(I)` by Nakayama, its
target dimension `rank Ω[A⁄k] = dim A`, and its cokernel being the fibre of `Ω[S_𝔪/k]` by
right-exactness of the tensor product on the conormal sequence. By Lemma 00TR that fibre has the
dimension of the cotangent space of `S_𝔪`, so the right-hand side is a relation between `μ(I)`,
`dim_κ 𝔪S_𝔪/(𝔪S_𝔪)²` and `dim A`. Krull's height theorem `dim A ≤ dim S_𝔪 + μ(I)` then turns
smoothness into regularity, and conversely Lemma 00SE, applied to `A → S_𝔪 → S_𝔪`, turns
regularity of `S_𝔪` into the equality `dim S_𝔪 + μ(I) = dim A` the criterion asks for.

This is shorter than the source's route, which builds a second `k`-algebra
`S' = k[x_1, …, x_n]/(f_1, …, f_c)` cut out by `c = n - d` of the equations, shows `S'_{𝔪'} → S_𝔪`
is an isomorphism, and applies the Jacobian criterion 00TE to the resulting global complete
intersection; performing the same count inside the local ring `A` removes `S'` and both principal
localizations. Lemmas 00SC, 00SV, 00TE, 00TA and 00T7, which the source's two arguments use, are
therefore not needed, and Lemma 00SE is used instead.

## Main results

* `Stacks.Smooth.ClosedPointRegularity.solution`: the statement of Stacks 00TS, namely
  `Algebra.isSmoothAt_tfae_of_isAlgClosed`.

## Implementation notes

The statement quantifies over an arbitrary model `Sₘ` of `S_𝔪`; the equivalence of regularity and
smoothness is proved for the concrete model `Localization.AtPrime 𝔪`, which is what
`Algebra.IsSmoothAt` unfolds to, and transported along `IsLocalization.algEquiv`, using that
`IsRegularLocalRing` is invariant under ring isomorphism.

The comparison of the two cotangent spaces is stated as an equality of dimensions over the two
residue fields rather than as an isomorphism of modules, because `κ(𝔪) = S/𝔪` and
`ResidueField S_𝔪` are two different types; `IsLocalization.AtPrime.equivQuotMaximalIdeal` is the
ring isomorphism between them, and `finrank_eq_of_semilinear` is what compares dimensions across
it.

## References

* [StacksProject 00TS](https://stacks.math.columbia.edu/tag/00TS)
-/

@[expose] public section

namespace Stacks.Smooth.ClosedPointRegularity

open TensorProduct IsLocalRing

/-- A `φ`-semilinear additive isomorphism between a `κ`-module and a `κ'`-vector space, along a
bijection `φ : κ → κ'`, matches their dimensions.

Only bijectivity of `φ` and the implication `φ c = 0 → c = 0` are used, so a ring isomorphism may
be passed as its underlying function. The source of the dimension comparison need not be a field:
a ring satisfying the strong rank condition suffices, since the basis is produced on the `κ'` side
and transported back. This matters for `κ = S ⧸ 𝔪`, which is a field but carries no `Field`
instance, and where introducing one by hand puts the scalar action on an instance path that no
longer matches the module structure the goal is about. -/
private theorem finrank_eq_of_semilinear {κ κ' : Type*} [Ring κ] [StrongRankCondition κ]
    [Field κ'] {M N : Type*} [AddCommGroup M] [Module κ M] [AddCommGroup N] [Module κ' N]
    {φ : κ → κ'} (hbij : Function.Bijective φ) (hzero : ∀ c : κ, φ c = 0 → c = 0)
    (e : M ≃+ N) (he : ∀ (c : κ) (m : M), e (c • m) = φ c • e m) :
    Module.finrank κ M = Module.finrank κ' N := by
  classical
  set ψ := Function.surjInv hbij.2 with hψ
  have hψφ : ∀ c' : κ', φ (ψ c') = c' := Function.surjInv_eq hbij.2
  have hsymm : ∀ (c' : κ') (n : N), e.symm (c' • n) = ψ c' • e.symm n := by
    intro c' n
    apply e.injective
    rw [he, hψφ]
    simp
  set b := Module.Basis.ofVectorSpace κ' N with hb
  have hli : LinearIndependent κ (fun i => e.symm (b i)) := by
    rw [linearIndependent_iff']
    intro s c hc i hi
    have h0 : e (∑ j ∈ s, c j • e.symm (b j)) = 0 := by rw [hc]; simp
    rw [map_sum] at h0
    simp only [he, AddEquiv.apply_symm_apply] at h0
    exact hzero _ ((linearIndependent_iff'.mp b.linearIndependent) s (fun j => φ (c j)) h0 i hi)
  have hsp : ⊤ ≤ Submodule.span κ (Set.range fun i => e.symm (b i)) := by
    set P := Submodule.span κ (Set.range fun i => e.symm (b i)) with hP
    let Q : Submodule κ' N :=
      { carrier := {n | e.symm n ∈ P}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, map_add]; exact P.add_mem ha hb
        zero_mem' := by simp
        smul_mem' := fun c n hn => by
          show e.symm (c • n) ∈ P
          rw [hsymm]; exact P.smul_mem _ hn }
    have hQ : (⊤ : Submodule κ' N) ≤ Q := by
      rw [← b.span_eq]
      refine Submodule.span_le.mpr ?_
      rintro x ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    intro m _
    have h2 : e.symm (e m) ∈ P := hQ (Submodule.mem_top (x := e m))
    simpa using h2
  have b' : Module.Basis _ κ M := Module.Basis.mk hli hsp
  rw [Module.finrank_eq_nat_card_basis b', Module.finrank_eq_nat_card_basis b]

/-- The cotangent space of `S` at a maximal ideal `𝔪` is the cotangent space of the local ring
`S_𝔪` at its maximal ideal: the canonical map `𝔪/𝔪² → 𝔪S_𝔪/(𝔪S_𝔪)²` is bijective, and it is
semilinear along the residue field isomorphism `S/𝔪 ≅ κ(S_𝔪)`.

Surjectivity: an element of `𝔪S_𝔪` is `x/s` with `x ∈ 𝔪` and `s ∉ 𝔪`; choosing `t` with
`1 - ts ∈ 𝔪` gives `x/s - xt = (x/s)(1 - ts) ∈ (𝔪S_𝔪)²`. Injectivity: if `x/1 ∈ (𝔪S_𝔪)² =
(𝔪²)S_𝔪` then `sx ∈ 𝔪²` for some `s ∉ 𝔪`, and `x = t(sx) + (1 - ts)x ∈ 𝔪²`. -/
private theorem finrank_cotangent_eq_finrank_cotangentSpace {S : Type*} [CommRing S]
    (𝔪 : Ideal S) [𝔪.IsMaximal] (Sₘ : Type*) [CommRing Sₘ] [Algebra S Sₘ]
    [IsLocalization.AtPrime Sₘ 𝔪] [IsLocalRing Sₘ] :
    Module.finrank (S ⧸ 𝔪) 𝔪.Cotangent =
      Module.finrank (ResidueField Sₘ) (CotangentSpace Sₘ) := by
  have hmax : Ideal.map (algebraMap S Sₘ) 𝔪 = maximalIdeal Sₘ :=
    IsLocalization.AtPrime.map_eq_maximalIdeal 𝔪 Sₘ
  have hmem : ∀ x : S, x ∈ 𝔪 → algebraMap S Sₘ x ∈ maximalIdeal Sₘ := by
    intro x hx
    rw [← hmax]
    exact Ideal.mem_map_of_mem _ hx
  let ι : 𝔪 →ₗ[S] (maximalIdeal Sₘ) :=
    { toFun := fun x => ⟨algebraMap S Sₘ x.1, hmem x.1 x.2⟩
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp [Algebra.smul_def] }
  let f : 𝔪.Cotangent →ₗ[S] CotangentSpace Sₘ :=
    Ideal.Cotangent.lift (((maximalIdeal Sₘ).toCotangent.restrictScalars S).comp ι) (by
      intro x y
      simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, Ideal.toCotangent_eq_zero]
      show algebraMap S Sₘ ((x : S) * y) ∈ (maximalIdeal Sₘ) ^ 2
      rw [map_mul, pow_two]
      exact Ideal.mul_mem_mul (hmem _ x.2) (hmem _ y.2))
  have hfapp : ∀ x : 𝔪, f (𝔪.toCotangent x) =
      (maximalIdeal Sₘ).toCotangent ⟨algebraMap S Sₘ x.1, hmem x.1 x.2⟩ := fun x => rfl
  have hunit : ∀ s : S, s ∉ 𝔪 → ∃ t : S, 1 - t * s ∈ 𝔪 := by
    intro s hs
    obtain ⟨t, i, hi, hti⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) hs
    refine ⟨t, ?_⟩
    have h1 : (1 : S) - t * s = i := by linear_combination -hti
    rw [h1]
    exact hi
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := 𝔪.toCotangent_surjective z
    rw [LinearMap.mem_ker, hfapp] at hz
    rw [Ideal.toCotangent_eq_zero] at hz ⊢
    have hz2 : algebraMap S Sₘ (x : S) ∈ Ideal.map (algebraMap S Sₘ) (𝔪 ^ 2) := by
      rwa [Ideal.map_pow, hmax]
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, key⟩ :=
      (IsLocalization.mem_map_algebraMap_iff 𝔪.primeCompl Sₘ).mp hz2
    simp only at key
    have h0 : algebraMap S Sₘ (s * (x : S) - a) = 0 := by
      rw [map_sub, map_mul, mul_comm, key]; ring
    obtain ⟨⟨u, hu⟩, hu2⟩ := (IsLocalization.map_eq_zero_iff 𝔪.primeCompl Sₘ _).mp h0
    have hmem2 : u * s * (x : S) ∈ 𝔪 ^ 2 := by
      have hz3 : u * (s * (x : S) - a) = 0 := hu2
      have h3 : u * s * (x : S) = u * a := by linear_combination hz3
      rw [h3]
      exact Ideal.mul_mem_left _ _ ha
    obtain ⟨t, ht⟩ := hunit (u * s) (by
      intro hcon
      rcases Ideal.IsPrime.mem_or_mem inferInstance hcon with h | h
      · exact hu h
      · exact hs h)
    have hx : (x : S) = t * (u * s * (x : S)) + (1 - t * (u * s)) * (x : S) := by ring
    rw [hx]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem2) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul ht x.2
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨⟨y, hy⟩, rfl⟩ := (maximalIdeal Sₘ).toCotangent_surjective w
    have hy' : y ∈ Ideal.map (algebraMap S Sₘ) 𝔪 := by rwa [hmax]
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, key⟩ :=
      (IsLocalization.mem_map_algebraMap_iff 𝔪.primeCompl Sₘ).mp hy'
    simp only at key
    obtain ⟨t, ht⟩ := hunit s hs
    refine ⟨𝔪.toCotangent ⟨t * a, Ideal.mul_mem_left _ _ ha⟩, ?_⟩
    rw [hfapp, Ideal.toCotangent_eq]
    have hcalc : algebraMap S Sₘ (t * a) - y = -(y * algebraMap S Sₘ (1 - t * s)) := by
      rw [map_mul, ← key, map_sub, map_one, map_mul]
      ring
    show algebraMap S Sₘ (t * a) - y ∈ (maximalIdeal Sₘ) ^ 2
    rw [hcalc, pow_two]
    exact neg_mem (Ideal.mul_mem_mul hy (hmem _ ht))
  let e : 𝔪.Cotangent ≃ₗ[S] CotangentSpace Sₘ := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine finrank_eq_of_semilinear (κ' := ResidueField Sₘ)
    (φ := fun c => IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 Sₘ c)
    (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 Sₘ).bijective
    (fun c hc => (map_eq_zero_iff _
      (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 Sₘ).injective).mp hc)
    e.toAddEquiv ?_
  intro c m
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := 𝔪) c
  have hact : (Ideal.Quotient.mk 𝔪 x) • m = x • m := rfl
  have hφ : IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 Sₘ (Ideal.Quotient.mk 𝔪 x)
      = Ideal.Quotient.mk (maximalIdeal Sₘ) (algebraMap S Sₘ x) := by
    rfl
  rw [hact, hφ]
  show e (x • m) = Ideal.Quotient.mk (maximalIdeal Sₘ) (algebraMap S Sₘ x) • e m
  rw [map_smul, ← algebraMap_smul (R := S) Sₘ x (e m)]
  exact (algebraMap_smul (ResidueField Sₘ) (algebraMap S Sₘ x) (e m)).symm

/-- A linear map between finite-dimensional vector spaces is injective exactly when the dimension
of its source together with the dimension of its cokernel adds up to the dimension of its target.

This is rank-nullity in the form a Jacobian criterion uses it: for a map whose source, target and
cokernel each have a known dimension, injectivity is a numerical identity between the three. -/
private theorem injective_iff_finrank_add_finrank_quotient_range {κ V W : Type*} [Field κ]
    [AddCommGroup V] [Module κ V] [AddCommGroup W] [Module κ W]
    [FiniteDimensional κ V] [FiniteDimensional κ W] (f : V →ₗ[κ] W) :
    Function.Injective f ↔
      Module.finrank κ V + Module.finrank κ (W ⧸ LinearMap.range f) = Module.finrank κ W := by
  have h1 : Module.finrank κ (W ⧸ LinearMap.range f) + Module.finrank κ (LinearMap.range f)
      = Module.finrank κ W := Submodule.finrank_quotient_add_finrank _
  have h2 : Module.finrank κ (LinearMap.range f) + Module.finrank κ (LinearMap.ker f)
      = Module.finrank κ V := LinearMap.finrank_range_add_finrank_ker f
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero (R := κ) (M := V)]
  omega

/-- Base change of a finite free module along any ring map has the same rank. -/
@[sga "1 IV 4.4" "(i)⇒(vi), dimension form"]
private theorem finrank_baseChange_of_free (A : Type*) [CommRing A] [Nontrivial A]
    (κ : Type*) [CommRing κ] [Nontrivial κ] [Algebra A κ] (M : Type*) [AddCommGroup M]
    [Module A M] [Module.Free A M] [Module.Finite A M] :
    Module.finrank κ (κ ⊗[A] M) = Module.finrank A M := by
  classical
  have hb : Module.Basis (Module.Free.ChooseBasisIndex A M) κ (κ ⊗[A] M) :=
    (Module.Free.chooseBasis A M).baseChange κ
  rw [Module.finrank_eq_card_chooseBasisIndex A M, Module.finrank_eq_nat_card_basis hb,
    Nat.card_eq_fintype_card]

/-- Two base changes of the same module along isomorphic residue algebras have the same
dimension. -/
private theorem finrank_baseChange_eq_of_ringEquiv {A : Type*} [CommRing A] {κ κ' : Type*}
    [CommRing κ] [StrongRankCondition κ] [Field κ'] [Algebra A κ] [Algebra A κ'] (ψ : κ ≃+* κ')
    (hψ : ∀ a : A, ψ (algebraMap A κ a) = algebraMap A κ' a) (M : Type*) [AddCommGroup M]
    [Module A M] :
    Module.finrank κ (κ ⊗[A] M) = Module.finrank κ' (κ' ⊗[A] M) := by
  have hsmul : ∀ (a : A) (x : κ), ψ (a • x) = a • ψ x := by
    intro a x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hψ]
  let ψA : κ ≃ₗ[A] κ' :=
    { ψ.toAddEquiv with map_smul' := fun a x => hsmul a x }
  let e : κ ⊗[A] M ≃ₗ[A] κ' ⊗[A] M := TensorProduct.congr ψA (LinearEquiv.refl A M)
  refine finrank_eq_of_semilinear (φ := ψ) ψ.bijective
    (fun c hc => by simpa using (map_eq_zero_iff _ ψ.injective).mp hc) e.toAddEquiv ?_
  intro c m
  induction m with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul x n =>
    show e (c • (x ⊗ₜ n)) = ψ c • e (x ⊗ₜ n)
    rw [TensorProduct.smul_tmul']
    show ψA (c * x) ⊗ₜ n = ψ c • (ψA x ⊗ₜ n)
    rw [TensorProduct.smul_tmul']
    show ψ (c * x) ⊗ₜ n = (ψ c * ψ x) ⊗ₜ n
    rw [map_mul]

/-- **Stacks 00TR for the local ring.** Over an algebraically closed field `k`, for a finite type
`k`-algebra `S` and a maximal ideal `𝔪`, the fibre of the differentials of the local ring `S_𝔪` at
its closed point has the dimension of the cotangent space `𝔪S_𝔪/(𝔪S_𝔪)²`.

Both sides are computed by transporting Lemma 00TR for `S` itself
(`finrank_kaehler_baseChange_eq_finrank_cotangent`) along the localization isomorphism
`Ω[S_𝔪⁄k] ≅ S_𝔪 ⊗[S] Ω[S⁄k]` (`KaehlerDifferential.isLocalizedModule_map`) and the residue field
isomorphism `S/𝔪 ≅ κ(S_𝔪)`. -/
private theorem finrank_kaehler_baseChange_residueField
    (k S : Type*) [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (𝔪 : Ideal S) [𝔪.IsMaximal] (Sₘ : Type*) [CommRing Sₘ] [Algebra S Sₘ] [Algebra k Sₘ]
    [IsScalarTower k S Sₘ] [IsLocalization.AtPrime Sₘ 𝔪] [IsLocalRing Sₘ] :
    Module.finrank (ResidueField Sₘ) (ResidueField Sₘ ⊗[Sₘ] Ω[Sₘ⁄k])
      = Module.finrank (ResidueField Sₘ) (CotangentSpace Sₘ) := by
  have hbc : IsBaseChange Sₘ (KaehlerDifferential.map k k S Sₘ) :=
    IsLocalizedModule.isBaseChange 𝔪.primeCompl Sₘ _
  let e1 : Sₘ ⊗[S] Ω[S⁄k] ≃ₗ[Sₘ] Ω[Sₘ⁄k] := hbc.equiv
  let e2 : ResidueField Sₘ ⊗[Sₘ] Ω[Sₘ⁄k] ≃ₗ[ResidueField Sₘ]
      ResidueField Sₘ ⊗[Sₘ] (Sₘ ⊗[S] Ω[S⁄k]) :=
    AlgebraTensorModule.congr (LinearEquiv.refl _ _) e1.symm
  let e3 : ResidueField Sₘ ⊗[Sₘ] (Sₘ ⊗[S] Ω[S⁄k]) ≃ₗ[ResidueField Sₘ]
      ResidueField Sₘ ⊗[S] Ω[S⁄k] :=
    AlgebraTensorModule.cancelBaseChange S Sₘ (ResidueField Sₘ) (ResidueField Sₘ) Ω[S⁄k]
  have hψ : ∀ a : S,
      (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 Sₘ).toRingEquiv (algebraMap S (S ⧸ 𝔪) a)
      = algebraMap S (ResidueField Sₘ) a := fun a => rfl
  rw [(e2.trans e3).finrank_eq, ← finrank_baseChange_eq_of_ringEquiv
    (IsLocalization.AtPrime.equivQuotMaximalIdeal 𝔪 Sₘ).toRingEquiv hψ Ω[S⁄k],
    finrank_kaehler_baseChange_eq_finrank_cotangent k S 𝔪]
  exact finrank_cotangent_eq_finrank_cotangentSpace 𝔪 Sₘ

/-- A surjection of local rings induces an isomorphism of residue fields, compatible with the
structure maps: the preimage of the maximal ideal of the target is a maximal ideal, hence the
maximal ideal of the source. -/
private theorem exists_residueFieldEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [Algebra A B] (hsurj : Function.Surjective (algebraMap A B)) :
    ∃ ψ : ResidueField A ≃+* ResidueField B,
      ∀ a : A, ψ (algebraMap A (ResidueField A) a) = algebraMap A (ResidueField B) a := by
  set g : A →+* ResidueField B := (algebraMap B (ResidueField B)).comp (algebraMap A B) with hg
  have hgs : Function.Surjective g := residue_surjective.comp hsurj
  have hker : RingHom.ker g = maximalIdeal A := by
    have h1 : RingHom.ker g = (maximalIdeal B).comap (algebraMap A B) := by
      rw [hg, ← RingHom.comap_ker]
      congr 1
      exact IsLocalRing.ker_residue
    rw [h1]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hsurj)
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hgs),
    fun a => rfl⟩

/-- **Nakayama, in dimensions.** For a finitely generated ideal `I` of a local ring `A` and a
local quotient `B` of `A`, the fibre `κ(B) ⊗_A I` has dimension the minimal number of generators
of `I`. -/
private theorem finrank_baseChange_eq_spanFinrank {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] (hsurj : Function.Surjective (algebraMap A B))
    (I : Ideal A) (hI : I.FG) :
    Module.finrank (ResidueField B) (ResidueField B ⊗[A] I) = I.spanFinrank := by
  obtain ⟨ψ, hψ⟩ := exists_residueFieldEquiv hsurj
  rw [← finrank_baseChange_eq_of_ringEquiv ψ hψ (I : Type _),
    ← TensorProduct.spanFinrank_top_eq_of_residueField I hI]
  exact Module.finrank_eq_spanFinrank_of_free (R := ResidueField A)
    (M := ResidueField A ⊗[A] I)

/-- The cokernel of the base-changed cotangent complex of a presentation `A → B` of a local ring
is the fibre of the differentials of `B`.

This is right-exactness of the tensor product applied to the conormal sequence
`I/I² → B ⊗_A Ω[A⁄k] → Ω[B⁄k] → 0` (`exact_kerCotangentToTensor_mapBaseChange` and
`mapBaseChange_surjective`), together with the identification of the base-changed cotangent
complex (`cotangentComplexBaseChange_eq_lTensor_cotangentComplex`). -/
private theorem finrank_quotient_range_cotangentComplexBaseChange
    (k A B : Type*) [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B] [IsLocalRing B]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Module.finrank (ResidueField B)
        ((ResidueField B ⊗[A] Ω[A⁄k]) ⧸ LinearMap.range
          (KaehlerDifferential.cotangentComplexBaseChange k B A (ResidueField B)))
      = Module.finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄k]) := by
  let P : Algebra.Extension k B :=
    { Ring := A, σ := Function.surjInv hsurj, algebraMap_σ := Function.surjInv_eq hsurj }
  let Φ : ResidueField B ⊗[B] P.CotangentSpace ≃ₗ[ResidueField B] ResidueField B ⊗[A] Ω[A⁄k] :=
    AlgebraTensorModule.cancelBaseChange A B (ResidueField B) (ResidueField B) Ω[A⁄k]
  let G : ResidueField B ⊗[B] P.CotangentSpace →ₗ[ResidueField B]
      ResidueField B ⊗[B] Ω[B⁄k] := LinearMap.baseChange (ResidueField B) P.toKaehler
  have hGsurj : Function.Surjective G := by
    show Function.Surjective (LinearMap.baseChange (ResidueField B) P.toKaehler)
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ Algebra.Extension.toKaehler_surjective
  have hexact : Function.Exact
      (LinearMap.baseChange (ResidueField B) P.cotangentComplex) G := by
    show Function.Exact (LinearMap.baseChange (ResidueField B) P.cotangentComplex)
      (LinearMap.baseChange (ResidueField B) P.toKaehler)
    simp only [LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact _ Algebra.Extension.exact_cotangentComplex_toKaehler
      Algebra.Extension.toKaehler_surjective
  have hker : LinearMap.ker G
      = LinearMap.range (LinearMap.baseChange (ResidueField B) P.cotangentComplex) :=
    hexact.linearMap_ker_eq
  have hrange : LinearMap.range
        (KaehlerDifferential.cotangentComplexBaseChange k B A (ResidueField B))
      = Submodule.map (Φ : _ →ₗ[ResidueField B] _)
        (LinearMap.range (LinearMap.baseChange (ResidueField B) P.cotangentComplex)) := by
    rw [Algebra.Extension.cotangentComplexBaseChange_eq_lTensor_cotangentComplex P
      (ResidueField B), LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
      Submodule.map_top]
  let g : ResidueField B ⊗[A] Ω[A⁄k] →ₗ[ResidueField B] ResidueField B ⊗[B] Ω[B⁄k] :=
    G ∘ₗ (Φ.symm.toLinearMap)
  have hgsurj : Function.Surjective g := hGsurj.comp Φ.symm.surjective
  have hkerg : LinearMap.ker g
      = LinearMap.range
        (KaehlerDifferential.cotangentComplexBaseChange k B A (ResidueField B)) := by
    show LinearMap.ker (G ∘ₗ Φ.symm.toLinearMap) = _
    rw [LinearMap.ker_comp, hker, hrange, Submodule.map_equiv_eq_comap_symm]
  rw [← hkerg]
  exact (LinearMap.quotKerEquivOfSurjective g hgsurj).finrank_eq

/-- **The Jacobian criterion for a local algebra, in numerical form.** Let `A` be a Noetherian
local `k`-algebra which is formally smooth over `k` with finite free module of differentials, and
let `B` be a local quotient of `A` with kernel `I`. Then `B` is formally smooth over `k` if and
only if the minimal number of generators of `I` together with the dimension of the fibre of
`Ω[B⁄k]` at the closed point add up to the rank of `Ω[A⁄k]`.

The criterion of `Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`
says that `B` is formally smooth iff `κ(B) ⊗_A I → κ(B) ⊗_A Ω[A⁄k]` is injective; the three
dimensions occurring in rank-nullity for that map are the minimal number of generators of `I`
(`finrank_baseChange_eq_spanFinrank`), the rank of `Ω[A⁄k]` (`finrank_baseChange_of_free`) and the
dimension of the fibre of `Ω[B⁄k]`
(`finrank_quotient_range_cotangentComplexBaseChange`). -/
@[ega "0 22.6.4" "special case",
  sga "1 II 4.10" "(i)⇔(iii), special case",
  sga "1 II 4.14" "(i)⇔(iii), special case"]
private theorem formallySmooth_iff_spanFinrank_add_finrank_kaehler
    (k A B : Type*) [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    [Algebra.FormallySmooth k A] [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Algebra.FormallySmooth k B ↔
      (RingHom.ker (algebraMap A B)).spanFinrank
        + Module.finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄k])
        = Module.finrank A Ω[A⁄k] := by
  have hFG : (RingHom.ker (algebraMap A B)).FG := IsNoetherian.noetherian _
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField A hsurj hFG,
    injective_iff_finrank_add_finrank_quotient_range,
    finrank_quotient_range_cotangentComplexBaseChange k A B hsurj,
    finrank_baseChange_eq_spanFinrank hsurj _ hFG,
    finrank_baseChange_of_free A (ResidueField B) Ω[A⁄k]]

/-- The Krull dimension of a Noetherian local ring is at most the dimension of its cotangent
space. -/
private theorem ringKrullDim_le_finrank_cotangentSpace (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ringKrullDim R ≤ (Module.finrank (ResidueField R) (CotangentSpace R) : WithBot ℕ∞) := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

/-- **Regularity equals smoothness above a regular formally smooth cover.** Let `A` be a regular
local `k`-algebra, formally smooth over `k`, with `Ω[A⁄k]` finite free of rank `dim A`, and let `B`
be a local quotient of `A` whose fibre of differentials computes its cotangent space. Then `B` is
formally smooth over `k` if and only if `B` is a regular local ring.

Both directions are the numerical criterion
`formallySmooth_iff_spanFinrank_add_finrank_kaehler` read against two general inequalities: Krull's
height theorem `dim A ≤ dim B + μ(I)` and `dim B ≤ dim_{κ(B)} 𝔪_B/𝔪_B²`. For the forward direction
they force the cotangent space of `B` to have dimension `dim B`; for the converse, Lemma 00SE
applied to `A → B → B` turns regularity of `B` into the equality `dim B + μ(I) = dim A` that the
criterion asks for. -/
private theorem formallySmooth_iff_isRegularLocalRing
    (k A B : Type*) [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra A B] [IsScalarTower k A B] [IsRegularLocalRing A] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra.FormallySmooth k A] [Module.Free A Ω[A⁄k]]
    [Module.Finite A Ω[A⁄k]] (hsurj : Function.Surjective (algebraMap A B))
    (hn : (Module.finrank A Ω[A⁄k] : WithBot ℕ∞) = ringKrullDim A)
    (hcot : Module.finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄k])
      = Module.finrank (ResidueField B) (CotangentSpace B)) :
    Algebra.FormallySmooth k B ↔ IsRegularLocalRing B := by
  have hAnoeth : IsNoetherianRing A := IsRegularLocalRing.toIsNoetherian
  have hAloc : IsLocalRing A := IsRegularLocalRing.toIsLocalRing
  set I : Ideal A := RingHom.ker (algebraMap A B) with hI
  set μ : ℕ := I.spanFinrank with hμ
  set e : ℕ := Module.finrank (ResidueField B) (CotangentSpace B) with he
  set n : ℕ := Module.finrank A Ω[A⁄k] with hnn
  obtain ⟨d, hd⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim B
  -- the numerical form of the Jacobian criterion
  have hcrit : Algebra.FormallySmooth k B ↔ μ + e = n := by
    rw [formallySmooth_iff_spanFinrank_add_finrank_kaehler k A B hsurj, hcot]
  -- regularity of `B` is the equality `e = d`
  have hreg : IsRegularLocalRing B ↔ e = d := by
    rw [IsRegularLocalRing.iff_finrank_cotangentSpace, ← he, hd]
    exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
  -- Krull's height theorem: `dim A ≤ dim B + μ`
  have hkrull : n ≤ d + μ := by
    have hne : I ≠ ⊤ := by
      intro h
      have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
      rw [hI, RingHom.mem_ker, map_one] at h1
      exact one_ne_zero h1
    have hq : ringKrullDim (A ⧸ I) = ringKrullDim B :=
      ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)
    have h2 : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + (μ : WithBot ℕ∞) := by
      refine ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I ?_
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal A]
      exact IsLocalRing.le_maximalIdeal hne
    rw [hq, hd, ← hn] at h2
    exact_mod_cast h2
  -- the cotangent space is always at least the dimension
  have hdim : d ≤ e := by
    have h1 := ringKrullDim_le_finrank_cotangentSpace B
    rw [← he, hd] at h1
    exact_mod_cast h1
  rw [hcrit, hreg]
  refine ⟨fun h => by omega, fun h => ?_⟩
  -- the converse: Lemma 00SE for `A → B → B` turns regularity into `dim B + μ = dim A`
  have hregB : IsRegularLocalRing B := hreg.mpr h
  have h00SE := IsRegularLocalRing.exists_isRegular_ker_tfae (A := A) (B := B) (C := B)
    (f := algebraMap A B) (g := RingHom.id B) hsurj Function.surjective_id
  have h4 : ringKrullDim B + ((RingHom.ker (RingHom.id B)).spanFinrank : WithBot ℕ∞)
      = ringKrullDim B := by
    have hk : RingHom.ker (RingHom.id B) = ⊥ := by ext x; simp [RingHom.mem_ker]
    rw [hk, Submodule.spanFinrank_bot]
    simp
  have h2 := (h00SE.out 4 2).mp h4
  rw [RingHom.id_comp, ← hI, ← hμ, ← hn, hd] at h2
  have : d + μ = n := by exact_mod_cast h2
  omega

/-- **Smoothness at a closed point is regularity of the local ring** (the substance of Stacks
00TS). Over an algebraically closed field `k`, a finite type `k`-algebra `S` is formally smooth at
a maximal ideal `𝔪` if and only if `S_𝔪` is a regular local ring.

The cover of `formallySmooth_iff_isRegularLocalRing` is taken to be the localization `A` of a
polynomial ring `k[x_1, …, x_m]` at the maximal ideal `𝔮` corresponding to `𝔪` under a chosen
surjection `k[x_1, …, x_m] → S`: it is a regular local ring because `k[x_1, …, x_m]` is a regular
ring, it is formally smooth over `k` and its differentials are finite free because both properties
pass from `k[x_1, …, x_m]` to a localization, and `A → S_𝔪` is surjective because
`k[x_1, …, x_m] → S` is. That the rank of `Ω[A⁄k]` is `dim A` and that the fibre of `Ω[S_𝔪⁄k]`
computes the cotangent space of `S_𝔪` are both Lemma 00TR, in the form
`finrank_kaehler_baseChange_residueField`. -/
@[ega "0 19.6.4" "a ⇔ c, special case", sga "1 II 5.9" "(ii) ⇒ (i)"]
private theorem formallySmooth_iff_isRegularLocalRing_localizationAtPrime
    (k S : Type*) [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (𝔪 : Ideal S) [𝔪.IsMaximal] :
    Algebra.FormallySmooth k (Localization.AtPrime 𝔪)
      ↔ IsRegularLocalRing (Localization.AtPrime 𝔪) := by
  obtain ⟨m, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k S)
  obtain ⟨𝔮, h𝔮⟩ : ∃ 𝔮 : Ideal (MvPolynomial (Fin m) k),
      𝔮 = 𝔪.comap (π : MvPolynomial (Fin m) k →+* S) := ⟨_, rfl⟩
  have : 𝔮.IsMaximal := h𝔮 ▸ Ideal.comap_isMaximal_of_surjective _ hπ
  let : Algebra (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔪) :=
    (Localization.localAlgHom (R := k) 𝔮 𝔪 π h𝔮).toRingHom.toAlgebra
  have : IsScalarTower k (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔪) :=
    IsScalarTower.of_algebraMap_eq'
      (Localization.localAlgHom (R := k) 𝔮 𝔪 π h𝔮).comp_algebraMap.symm
  have hsurjA : Function.Surjective
      (algebraMap (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔪)) :=
    (RingHom.surjectiveOnStalks_of_surjective
      (f := (π : MvPolynomial (Fin m) k →+* S)) hπ).localRingHom_surjective 𝔮 𝔪 h𝔮
  have hbcA : IsBaseChange (Localization.AtPrime 𝔮)
      (KaehlerDifferential.map k k (MvPolynomial (Fin m) k) (Localization.AtPrime 𝔮)) :=
    IsLocalizedModule.isBaseChange 𝔮.primeCompl (Localization.AtPrime 𝔮) _
  have : Module.Free (Localization.AtPrime 𝔮) Ω[(Localization.AtPrime 𝔮)⁄k] :=
    Module.Free.of_equiv hbcA.equiv
  have : Module.Finite (Localization.AtPrime 𝔮) Ω[(Localization.AtPrime 𝔮)⁄k] :=
    Module.Finite.equiv hbcA.equiv
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsNoetherianRing (Localization.AtPrime 𝔪) :=
    IsLocalization.isNoetherianRing 𝔪.primeCompl _ ‹_›
  have hn : (Module.finrank (Localization.AtPrime 𝔮) Ω[(Localization.AtPrime 𝔮)⁄k] :
      WithBot ℕ∞) = ringKrullDim (Localization.AtPrime 𝔮) := by
    rw [← finrank_baseChange_of_free (Localization.AtPrime 𝔮)
        (ResidueField (Localization.AtPrime 𝔮)) Ω[(Localization.AtPrime 𝔮)⁄k],
      finrank_kaehler_baseChange_residueField k (MvPolynomial (Fin m) k) 𝔮
        (Localization.AtPrime 𝔮)]
    exact (IsRegularLocalRing.iff_finrank_cotangentSpace
      (R := Localization.AtPrime 𝔮)).mp inferInstance
  exact formallySmooth_iff_isRegularLocalRing k (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔪)
    hsurjA hn (finrank_kaehler_baseChange_residueField k S 𝔪 (Localization.AtPrime 𝔪))


/-- **Regularity at a closed point equals smoothness, over an algebraically closed field**
(Stacks 00TS). -/
public theorem solution {k S : Type*} [Field k] [IsAlgClosed k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (𝔪 : Ideal S) [𝔪.IsMaximal]
    (Sₘ : Type*) [CommRing Sₘ] [Algebra S Sₘ] [IsLocalization.AtPrime Sₘ 𝔪] :
    List.TFAE
      [IsRegularLocalRing Sₘ,
       (Module.finrank (S ⧸ 𝔪) ((S ⧸ 𝔪) ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) ≤ ringKrullDim Sₘ,
       (Module.finrank (S ⧸ 𝔪) ((S ⧸ 𝔪) ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) = ringKrullDim Sₘ,
       ∃ g ∉ 𝔪, Algebra.Smooth k (Localization.Away g),
       Algebra.IsSmoothAt k 𝔪] := by
  have hfp : Algebra.FinitePresentation k S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hnoeth : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hloc : IsLocalRing Sₘ := IsLocalization.AtPrime.isLocalRing Sₘ 𝔪
  have hnm : IsNoetherianRing Sₘ := IsLocalization.isNoetherianRing 𝔪.primeCompl Sₘ hnoeth
  have e : Sₘ ≃ₐ[S] Localization.AtPrime 𝔪 :=
    IsLocalization.algEquiv 𝔪.primeCompl Sₘ (Localization.AtPrime 𝔪)
  have key : Module.finrank (S ⧸ 𝔪) ((S ⧸ 𝔪) ⊗[S] Ω[S⁄k])
      = Module.finrank (ResidueField Sₘ) (CotangentSpace Sₘ) := by
    rw [finrank_kaehler_baseChange_eq_finrank_cotangent k S 𝔪]
    exact finrank_cotangent_eq_finrank_cotangentSpace 𝔪 Sₘ
  tfae_have 1 ↔ 3 := by
    rw [IsRegularLocalRing.iff_finrank_cotangentSpace, key]
  tfae_have 3 → 2 := fun h => le_of_eq h
  tfae_have 2 → 3 := fun h =>
    le_antisymm h (key ▸ ringKrullDim_le_finrank_cotangentSpace Sₘ)
  tfae_have 1 ↔ 5 := by
    rw [show IsRegularLocalRing Sₘ ↔ IsRegularLocalRing (Localization.AtPrime 𝔪) from
      ⟨fun _ => IsRegularLocalRing.of_ringEquiv (R := Sₘ) e.toRingEquiv,
        fun _ => IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv⟩]
    exact (formallySmooth_iff_isRegularLocalRing_localizationAtPrime k S 𝔪).symm
  tfae_have 5 → 4 := fun h => Algebra.IsSmoothAt.exists_notMem_smooth k 𝔪
  tfae_have 4 → 5 := fun ⟨g, hg, hs⟩ =>
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hs
      (show (⟨𝔪, inferInstance⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen g by simpa using hg)
  tfae_finish

end Stacks.Smooth.ClosedPointRegularity

end

/-!
# Smoothness at a closed point over an algebraically closed field

Let `k` be an algebraically closed field, let `S` be a finite type `k`-algebra and let `𝔪 ⊆ S` be a
maximal ideal. Because `k` is algebraically closed the composite `k → κ(𝔪) = S/𝔪` is an isomorphism
(Theorem 00FV), so the conormal sequence of Lemma 00RU is exact on the left and the fibre of the
module of differentials at `𝔪` is the cotangent space:
`Ω_{S/k} ⊗_S κ(𝔪) ≅ 𝔪/𝔪²` (Lemma 00TR). Regularity of the local ring `S_𝔪` is by definition the
statement that `dim_{κ(𝔪)} 𝔪/𝔪² = dim S_𝔪`, and the inequality `≥` always holds, so regularity of
`S_𝔪`, the bound `dim_{κ(𝔪)} Ω_{S/k} ⊗_S κ(𝔪) ≤ dim S_𝔪` and the corresponding equality say the
same thing. The substance of 00TS is that these are equivalent to smoothness of `S/k` in a
neighbourhood of `𝔪`: the Jacobian criterion turns a regular closed point into a `c × c` minor of
the Jacobian matrix that is invertible at `𝔪`, hence invertible on a principal open around it.

Over a field that is not algebraically closed the equivalence fails: for `k = 𝔽_p(t)` and
`S = k[x]/(x^p - t)` the ring `S` is a field, so `S_𝔪 = S` is regular of dimension `0`, while
`Ω_{S/k} = S · dx` is one-dimensional and `S` is not smooth over `k`. So `IsAlgClosed k` is
load-bearing, not decoration.

## Main results

* `Algebra.isSmoothAt_tfae_of_isAlgClosed`: the five equivalent conditions, in the source's order.

## Implementation notes

The dimension of the fibre is `Module.finrank (S ⧸ 𝔪) ((S ⧸ 𝔪) ⊗[S] Ω[S⁄k])`. The two tensor
factors are transposed relative to the source's `Ω_{S/k} ⊗_S κ(𝔪)`, because it is the *left* factor
of a tensor product on which Mathlib puts the scalar action of the base-changed ring, and so the
one that makes the base change a `κ(𝔪)`-vector space; `TensorProduct.comm` is the identification,
and it is `κ(𝔪)`-linear. Since `Algebra.FiniteType k S` gives `Module.Finite S Ω[S⁄k]`, the base
change is a finite-dimensional `κ(𝔪)`-vector space and `Module.finrank` is the source's
`dim_{κ(𝔪)}` rather than the junk value `0` it would take on an infinite-dimensional space.

The residue field `κ(𝔪)` is spelled `S ⧸ 𝔪`, which for a maximal ideal is a field, and the local
ring `S_𝔪` is an arbitrary model: `Sₘ` is any `S`-algebra with `IsLocalization.AtPrime Sₘ 𝔪`,
so the statement is the one its consumers apply, and `Localization.AtPrime 𝔪` is a witness.

The source's item (4) is one condition stated twice, "there is `g ∉ 𝔪` with `S_g` smooth over `k`"
and "in other words `S/k` is smooth at `𝔪`"; both readings are items of the list, the second as
Mathlib's `Algebra.IsSmoothAt k 𝔪` (formal smoothness of `S_𝔪` over `k`), which is the name a
reader will want to cite and the entry point to `Algebra.smoothLocus`. The existential is phrased
with `Localization.Away g`, as Mathlib phrases it in `Algebra.IsSmoothAt.exists_notMem_smooth`;
smoothness is invariant under `k`-algebra isomorphism, so the model of `S_g` is immaterial.

Faithfulness to the source, point by point. (1) No hypothesis is idle: `IsAlgClosed k` fails the
equivalence as shown above, `Algebra.FiniteType k S` is the source's "finite type" and is what
makes `Ω[S⁄k]` a finite module and `S` Noetherian, `𝔪.IsMaximal` is needed for `S ⧸ 𝔪` to be the
residue field, and `IsLocalization.AtPrime Sₘ 𝔪` is what makes `Sₘ` the ring `S_𝔪` the source
names. (2) The scalars and base are the source's throughout: differentials are of `S` over `k`
(`Ω[S⁄k]`), the fibre is taken over `S` at `𝔪` and its dimension over `κ(𝔪) = S ⧸ 𝔪`, and both
`ringKrullDim Sₘ` and `IsRegularLocalRing Sₘ` are about the local ring `S_𝔪`, not about `S`.
(3) Where the source names a canonical object the statement pins it rather than asserting
existence: `Sₘ` is pinned as a localization of `S` at `𝔪` along `algebraMap S Sₘ`, the fibre is the
base change along `Ideal.Quotient.mk 𝔪`, and in item 4 the smooth algebra is pinned to be a
localization of `S` away from the element `g` exhibited. (4) The instantiation is not degenerate:
`k = ℂ`, `S = k[x]`, `𝔪 = (x)`, `Sₘ = Localization.AtPrime 𝔪` satisfies all five — `S_𝔪` is a
discrete valuation ring, `Ω_{S/k} = S · dx` has one-dimensional fibre and `dim S_𝔪 = 1` — while
`S = k[x, y]/(xy)` at `𝔪 = (x, y)` satisfies none, its differential fibre being two-dimensional
over a local ring of dimension one, so no item is vacuous and none is automatic.

## References

* [StacksProject 00TS](https://stacks.math.columbia.edu/tag/00TS)

## Tags

smooth, smooth at a point, regular local ring, module of differentials, Jacobian criterion,
algebraically closed field, finite type algebra
-/

@[expose] public section

open TensorProduct in
/-- **Regularity at a closed point equals smoothness, over an algebraically closed field**
(Stacks 00TS). For an algebraically closed field `k`, a finite type `k`-algebra `S`, a maximal
ideal `𝔪 ⊆ S` and a model `Sₘ` of `S_𝔪`, the following are equivalent: (1) `S_𝔪` is a regular
local ring; (2) `dim_{κ(𝔪)} Ω_{S/k} ⊗_S κ(𝔪) ≤ dim S_𝔪`; (3) the same with equality;
(4) there is a `g ∈ S`, `g ∉ 𝔪`, with `S_g` smooth over `k`; (5) in other words, `S/k` is smooth
at `𝔪`. -/
@[stacks 00TS "The residue field `κ(𝔪)` is `S ⧸ 𝔪`, and the fibre `Ω_{S/k} ⊗_S κ(𝔪)` is the
base change `(S ⧸ 𝔪) ⊗[S] Ω[S⁄k]`, whose factors are transposed so that the left one carries the
scalar action making it a `κ(𝔪)`-vector space. `dim S_𝔪` is `ringKrullDim Sₘ` for an arbitrary
model `Sₘ` of the localization, matching Mathlib's `IsRegularLocalRing`. The source's item (4) is
stated twice, as the existential and as Mathlib's `Algebra.IsSmoothAt`; those are items 4 and 5.
See the module docstring.",
  ega "0 22.6.7" "alg. closed k, max ideal",
  ega "IV 17.15.5" "affine, k alg closed",
  ega "IV 17.15.9" "k alg closed, closed pt",
  sga "1 II 5.3" "alg. closed k, max ideal",
  sga "1 II 5.5" "alg closed k, closed pt",
  sga "1 II 5.9" "k alg closed, closed pt"]
public theorem Algebra.isSmoothAt_tfae_of_isAlgClosed {k S : Type*} [Field k] [IsAlgClosed k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (𝔪 : Ideal S) [𝔪.IsMaximal]
    (Sₘ : Type*) [CommRing Sₘ] [Algebra S Sₘ] [IsLocalization.AtPrime Sₘ 𝔪] :
    List.TFAE
      [IsRegularLocalRing Sₘ,
       (Module.finrank (S ⧸ 𝔪) ((S ⧸ 𝔪) ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) ≤ ringKrullDim Sₘ,
       (Module.finrank (S ⧸ 𝔪) ((S ⧸ 𝔪) ⊗[S] Ω[S⁄k]) : WithBot ℕ∞) = ringKrullDim Sₘ,
       ∃ g ∉ 𝔪, Algebra.Smooth k (Localization.Away g),
       Algebra.IsSmoothAt k 𝔪] :=
         by apply Stacks.Smooth.ClosedPointRegularity.solution

end
