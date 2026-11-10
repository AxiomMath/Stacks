module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.Blowup.Defs
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.Defs
public import StacksFrontier.RingTheory.Smooth.NaiveCotangentCriterion
public import StacksFrontier.RingTheory.Smooth.ParameterChart
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smoothing.NeronLocalParameters
public import StacksFrontier.RingTheory.Flat.NonZeroDivisors

/-!
# Smoothness and differentials of the affine Néron blowup

Fix an extension `R → Λ` of discrete valuation rings of ramification index one together with a
factorization `R → A → Λ` in which `A` is flat and of finite type over `R`, let `π` be a
uniformizer of `R`, and let `𝔭 ⊆ A` be the preimage of the maximal ideal of `Λ`. Write
`A' = A[𝔭/π]` for the affine blowup chart. The map `A → Λ` extends uniquely to `A' → Λ`, since
every fraction `g/π` with `g ∈ 𝔭` has a unique image in the discrete valuation ring `Λ`; let
`𝔭'` be the preimage of the maximal ideal of `Λ` along that extension.

If `A` is smooth over `R` at `𝔭` and the residue-field extension `κ(R) → κ(Λ)` is separable, then
`A'` is smooth over `R` at `𝔭'`, and the relative differentials sit in a short exact sequence

`0 → Ω_{A/R} ⊗_A A'_{𝔭'} → Ω_{A'_{𝔭'}/R} → ((A'/πA')_{𝔭'})^c → 0`,

where `c = dim (A/πA)_𝔭`. Both assertions come from the same input: after localizing `A` away
from a suitable element outside `𝔭`, the chart `A'` is a parameter chart
`A_f[y₁, …, y_c]/(π yᵢ - gᵢ)` for local parameters `g₁, …, g_c` whose differentials are part of a
basis of `Ω_{A_f/R}`. The cotangent computation on such a chart is
`formallySmooth_and_exists_differentialBasis_parameterChartAlgebra` and its localized companions.

## Main definitions

* `Stacks.Smoothing.canonicalNeronBlowupMap`: the extension `A' → Λ` of `A → Λ`, packaged with
  the identity that characterizes it.

## Main results

* `Stacks.Smoothing.affineBlowup_smoothAt`: the affine blowup is smooth over `R` at `𝔭'`.
* `Stacks.Smoothing.affineBlowup_differentials_shortExact`: the short exact sequence of relative
  differentials at `𝔭'`.

## Implementation notes

The localization `A'_{𝔭'}` is taken as an arbitrary model `B` with `IsLocalization.AtPrime B 𝔭'`,
so that `Ω_{A'_{𝔭'}/R}` may be read either as `Ω_{B/R}` or as `A' ⊗`-base change; the sequence is
stated on `B ⊗_{A'} Ω_{A'/R}`, which the localization identifies with `Ω_{B/R}`.

The short exact sequence is produced as a `CategoryTheory.ShortComplex` in `ModuleCat B`, whose
`ShortExact` predicate packages exactness together with injectivity of the first and surjectivity
of the second map. The first map is pinned down by its values on `b ⊗ₜ x`, which is what makes the
statement say that it is the base change of `Ω_{A/R} → Ω_{A'/R}` and not merely some injection.

Both assertions rest on `exists_local_parameters_of_smoothAt`; the second one is stated for the
value of `c` given by the Krull dimension of the closed fibre, which that lemma matches.
-/

@[expose] public section

namespace Stacks.Smoothing

open Stacks.Smooth.FlatFibreCriterion

open CategoryTheory
open scoped TensorProduct

universe u v w

/-- A generator of the maximal ideal of a discrete valuation ring is non-zero, since a discrete
valuation ring is not a field. -/
public theorem uniformizer_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R}
    (hπ : IsLocalRing.maximalIdeal R = Ideal.span ({π} : Set R)) : π ≠ 0 := fun h =>
  IsDiscreteValuationRing.not_a_field R (by rw [hπ, h, Ideal.span_singleton_eq_bot])

/-- If a ring map `f : A → Λ` sends `b` to a non-zero-divisor dividing the image of every element
of `I`, the induced map from the affine blowup `A[I/b]` to the fraction ring of `Λ` lands in
`Λ`. -/
theorem localizationMap_affineBlowup_mem_range {A Λ : Type*} [CommRing A] [CommRing Λ]
    (f : A →+* Λ) {b : A} (hb : f b ∈ nonZeroDivisors Λ) (I : Ideal A)
    (hI : ∀ y ∈ I, f b ∣ f y) (x : affineBlowupAlgebra I b (Localization.Away b)) :
    IsLocalization.map (FractionRing Λ) f (M := Submonoid.powers b) (T := nonZeroDivisors Λ)
      (Submonoid.powers_le.mpr hb) x.1 ∈ (algebraMap Λ (FractionRing Λ)).range := by
  let K := FractionRing Λ
  let locMap : Localization.Away b →+* K :=
    IsLocalization.map K f (M := Submonoid.powers b) (T := nonZeroDivisors Λ)
      (Submonoid.powers_le.mpr hb)
  have hx : x.1 ∈ Algebra.adjoin A
      {z : Localization.Away b | ∃ y ∈ I,
        z = IsLocalization.mk' _ y ⟨b, Submonoid.mem_powers b⟩} := x.2
  exact Algebra.adjoin_induction
    (p := fun z _ => locMap z ∈ (algebraMap Λ K).range)
    (mem := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨w, hw⟩ := hI y hy
      refine ⟨w, ?_⟩
      dsimp [locMap]
      rw [IsLocalization.map_mk']
      symm
      apply IsLocalization.mk'_eq_iff_eq_mul.2
      change algebraMap Λ K (f y) = algebraMap Λ K w * algebraMap Λ K (f b)
      rw [hw]
      simp [mul_comm])
    (algebraMap := fun a => ⟨f a, by simp [locMap]⟩)
    (add := by
      rintro x y _ _ ⟨a, ha⟩ ⟨a', ha'⟩
      refine ⟨a + a', ?_⟩
      change algebraMap Λ K (a + a') = locMap (x + y)
      rw [map_add, map_add, ha, ha'])
    (mul := by
      rintro x y _ _ ⟨a, ha⟩ ⟨a', ha'⟩
      refine ⟨a * a', ?_⟩
      change algebraMap Λ K (a * a') = locMap (x * y)
      rw [map_mul, map_mul, ha, ha']) hx

/-- The canonical extension of `A → Λ` to the affine Néron blowup `A' = A[𝔭/π]`, together with
the identity `A' → Λ` restricted to `A` is `A → Λ` that characterizes it. Existence is the content:
a fraction `g/π` with `g ∈ 𝔭` has image in `Λ` the quotient of the images of `g` and of `π`, which
lies in `Λ` because `π` generates the maximal ideal of `Λ` (the ramification index is one). -/
noncomputable def canonicalNeronBlowupMap
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    {φ : affineBlowupAlgebra S.maximalIdealPreimage (algebraMap S.R S.A π)
      (Localization.Away (algebraMap S.R S.A π)) →+* S.Λ //
      φ.comp (algebraMap S.A
        (affineBlowupAlgebra S.maximalIdealPreimage (algebraMap S.R S.A π)
          (Localization.Away (algebraMap S.R S.A π)))) = algebraMap S.A S.Λ} := by
  classical
  let K := FractionRing S.Λ
  let f : S.A →+* S.Λ := algebraMap S.A S.Λ
  let b := algebraMap S.R S.A π
  let I := S.maximalIdealPreimage
  have hb : f b ∈ nonZeroDivisors S.Λ := by
    refine mem_nonZeroDivisors_iff_ne_zero.2 ?_
    change algebraMap S.A S.Λ (algebraMap S.R S.A π) ≠ 0
    rw [← IsScalarTower.algebraMap_apply S.R S.A S.Λ]
    exact fun hz => uniformizer_ne_zero hπ (S.extension.1 (by simpa using hz))
  let locMap : Localization.Away b →+* K :=
    IsLocalization.map K f (M := Submonoid.powers b) (T := nonZeroDivisors S.Λ)
      (Submonoid.powers_le.mpr hb)
  have _ : FaithfulSMul S.R S.Λ := ⟨fun {r s} hrs => by
    apply S.extension.1
    simpa [Algebra.smul_def] using hrs (1 : S.Λ)⟩
  have _ : IsLocalHom (algebraMap S.R S.Λ) := S.extension.2
  have hmax : (IsLocalRing.maximalIdeal S.R).map (algebraMap S.R S.Λ) =
      IsLocalRing.maximalIdeal S.Λ := by
    rw [DiscreteValuationRing.Ramification.map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx
      S.R S.Λ, S.ramificationIndex_one, pow_one]
  have hmaxSpan : IsLocalRing.maximalIdeal S.Λ =
      Ideal.span ({algebraMap S.R S.Λ π} : Set S.Λ) := by
    rw [← hmax, hπ, Ideal.map_span]
    simp [Set.image_singleton]
  have hdvd (y : S.A) (hy : y ∈ I) : f b ∣ f y := by
    have hym : algebraMap S.A S.Λ y ∈ IsLocalRing.maximalIdeal S.Λ := hy
    rwa [hmaxSpan, Ideal.mem_span_singleton,
      IsScalarTower.algebraMap_apply S.R S.A S.Λ] at hym
  let rangeEquiv : S.Λ ≃+* RingHom.range (algebraMap S.Λ K) :=
    RingEquiv.ofBijective (RingHom.rangeRestrict (algebraMap S.Λ K))
      ⟨fun a b hab => IsFractionRing.injective S.Λ K (congrArg Subtype.val hab),
        RingHom.rangeRestrict_surjective _⟩
  let ψ : affineBlowupAlgebra I b (Localization.Away b) →+*
      RingHom.range (algebraMap S.Λ K) :=
    RingHom.codRestrict (locMap.comp (affineBlowupAlgebra I b (Localization.Away b)).subtype)
      _ fun x => localizationMap_affineBlowup_mem_range f hb I hdvd x
  have hkey (a : S.A) :
      ψ (algebraMap S.A (affineBlowupAlgebra I b (Localization.Away b)) a) =
        rangeEquiv (algebraMap S.A S.Λ a) := by
    apply Subtype.ext
    change locMap (algebraMap S.A (Localization.Away b) a) =
      algebraMap S.Λ K (algebraMap S.A S.Λ a)
    rw [IsLocalization.map_eq]
  refine ⟨rangeEquiv.symm.toRingHom.comp ψ, RingHom.ext fun a => ?_⟩
  change rangeEquiv.symm (ψ (algebraMap S.A
    (affineBlowupAlgebra I b (Localization.Away b)) a)) = algebraMap S.A S.Λ a
  rw [hkey a, rangeEquiv.symm_apply_apply]

/-- Smoothness at a prime transports along an algebra equivalence. -/
private theorem isSmoothAt_iff_of_algEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (q : Ideal A) [q.IsPrime] :
    Algebra.IsSmoothAt R q ↔ Algebra.IsSmoothAt R (Ideal.comap e.symm.toRingHom q) := by
  let qB : Ideal B := Ideal.comap e.symm.toRingHom q
  have _ : qB.IsPrime := Ideal.comap_isPrime _ _
  have hqAB : q = Ideal.comap e.toRingHom qB := by
    ext x
    simp [qB]
  let f : Localization.AtPrime q →+* Localization.AtPrime qB :=
    Localization.localRingHom q qB e.toRingHom hqAB
  let g : Localization.AtPrime qB →+* Localization.AtPrime q :=
    Localization.localRingHom qB q e.symm.toRingHom rfl
  have hgf : g.comp f = RingHom.id _ :=
    IsLocalization.ringHom_ext q.primeCompl <| RingHom.ext fun x => by simp [f, g]
  have hfg : f.comp g = RingHom.id _ :=
    IsLocalization.ringHom_ext qB.primeCompl <| RingHom.ext fun x => by simp [f, g]
  let eAt : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime qB :=
    AlgEquiv.ofRingEquiv (R := R) (f := RingEquiv.ofRingHom f g hfg hgf) fun r => by
      change f (algebraMap R (Localization.AtPrime q) r) =
        algebraMap R (Localization.AtPrime qB) r
      rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime q),
        IsScalarTower.algebraMap_apply R B (Localization.AtPrime qB)]
      simp [f]
  exact Algebra.FormallySmooth.iff_of_equiv eAt

/-- Smoothness at a prime is unchanged by a principal localization avoiding that prime. -/
private theorem isSmoothAt_iff_of_away
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime] (a : A) (p : Ideal (Localization.Away a)) [p.IsPrime]
    (hqp : p.comap (algebraMap A (Localization.Away a)) = q) :
    Algebra.IsSmoothAt R q ↔ Algebra.IsSmoothAt R p := by
  let B := Localization.Away a
  subst q
  have _ : IsLocalization.AtPrime (Localization.AtPrime p) (p.comap (algebraMap A B)) :=
    IsLocalization.isLocalization_atPrime_localization_atPrime (Submonoid.powers a) p
  let e : Localization.AtPrime (p.comap (algebraMap A B)) ≃ₐ[A] Localization.AtPrime p :=
    (IsLocalization.algEquiv (p.comap (algebraMap A B)).primeCompl
      (Localization.AtPrime p) (Localization.AtPrime (p.comap (algebraMap A B)))).symm
  change Algebra.FormallySmooth R (Localization.AtPrime (p.comap (algebraMap A B))) ↔
    Algebra.FormallySmooth R (Localization.AtPrime p)
  exact Algebra.FormallySmooth.iff_of_equiv (e.restrictScalars R)

/-- Smoothness at a prime `q` follows from smoothness at every prime of an algebra isomorphic to a
principal localization `A[1/a]` with `a ∉ q`. -/
private theorem isSmoothAt_of_away_algEquiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (q : Ideal A) [hq : q.IsPrime] (a : A) (ha : a ∉ q) (e : Localization.Away a ≃ₐ[R] B)
    (hB : ∀ (p : Ideal B) [p.IsPrime], Algebra.IsSmoothAt R p) :
    Algebra.IsSmoothAt R q := by
  let qL : Ideal (Localization.Away a) := q.map (algebraMap A _)
  have hdisj : Disjoint (Submonoid.powers a : Set A) (q : Set A) := by
    rw [Set.disjoint_left]
    rintro x ⟨k, rfl⟩ hx
    exact ha (hq.mem_of_pow_mem k hx)
  have _ : qL.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) _ q hq hdisj
  have _ : (Ideal.comap e.symm.toRingHom qL).IsPrime := Ideal.comap_isPrime _ _
  exact (isSmoothAt_iff_of_away q a qL
    (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) _ hq hdisj)).mpr
    ((isSmoothAt_iff_of_algEquiv e qL).mpr (hB _))

/-- An affine blowup is of finite type over its base when the centre is finitely generated: the
fractions `s/a` for `s` running through a finite generating set already generate. -/
private theorem affineBlowup_finiteType_of_fg
    {A U : Type*} [CommRing A] [CommRing U] [Algebra A U]
    {a : A} [IsLocalization.Away a U] (I : Ideal A) (hI : I.FG) :
    Algebra.FiniteType A (affineBlowupAlgebra I a U) := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  let frac : A → U := fun x => IsLocalization.mk' U x ⟨a, Submonoid.mem_powers a⟩
  let gens : Set U := Set.image frac (Set.range s)
  let C : Subalgebra A U := Algebra.adjoin A gens
  have hfrac_eq (x : A) : frac x = algebraMap A U x * frac 1 :=
    IsLocalization.mk'_eq_mul_mk'_one (S := U) x ⟨a, Submonoid.mem_powers a⟩
  let Pmod : Submodule A A :=
    { carrier := {x | frac x ∈ C}
      zero_mem' := by
        change frac 0 ∈ C
        rw [hfrac_eq]
        simp
      add_mem' := by
        intro x y hx hy
        change frac (x + y) ∈ C
        rw [hfrac_eq, map_add, add_mul, ← hfrac_eq x, ← hfrac_eq y]
        exact C.add_mem hx hy
      smul_mem' := by
        intro r x hx
        change frac (r • x) ∈ C
        rw [smul_eq_mul, hfrac_eq, map_mul, mul_assoc, ← hfrac_eq x]
        exact C.mul_mem (C.algebraMap_mem r) hx }
  have hP : Submodule.span A (Set.range s) ≤ Pmod :=
    Submodule.span_le.mpr fun x hx => Algebra.subset_adjoin (Set.mem_image_of_mem frac hx)
  have hCT : C ≤ affineBlowupAlgebra I a U := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨s i, ?_, rfl⟩
    rw [← hs]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hTC : affineBlowupAlgebra I a U ≤ C := by
    change Algebra.adjoin A {z : U | ∃ y ∈ I, z = frac y} ≤ C
    apply Algebra.adjoin_le
    rintro z ⟨y, hy, rfl⟩
    exact hP (hs ▸ hy)
  rw [← le_antisymm hCT hTC]
  exact Algebra.FiniteType.adjoin_of_finite ((Set.finite_range s).image frac)

/-- A parameter chart whose `d gᵢ` are part of a basis of `Ω_{B/R}`, with `B` smooth over `R`, is
smooth over `R` at every prime: the first cotangent homology vanishes and the differentials of the
localization are free. -/
private theorem isSmoothAt_parameterChartAlgebra
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    (hsm : Algebra.Smooth R B) (π : R) (c : ℕ) (g : Fin c → B) (ι : Type*)
    (b : Module.Basis (Fin c ⊕ ι) B (KaehlerDifferential R B))
    (hb : ∀ i, b (Sum.inl i) = KaehlerDifferential.D R B (g i))
    (q : Ideal (parameterChartAlgebra B (algebraMap R B π) c g)) [hq : q.IsPrime] :
    Algebra.IsSmoothAt R q := by
  let C := parameterChartAlgebra B (algebraMap R B π) c g
  have hI : (Ideal.span (Set.range fun i : Fin c =>
      MvPolynomial.C (algebraMap R B π) * MvPolynomial.X i - MvPolynomial.C (g i))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have _ : Algebra.FinitePresentation R (MvPolynomial (Fin c) B) :=
    Algebra.FinitePresentation.mvPolynomial (R := R) (A := B) (Fin c)
  have _ : Algebra.FinitePresentation R C := Algebra.FinitePresentation.quotient hI
  have hH1 : Subsingleton (Algebra.H1Cotangent R (Localization.AtPrime q)) :=
    subsingleton_h1Cotangent_parameterChartAlgebra_localization R B hsm π c g ι b hb q hq
  obtain ⟨b', _, _⟩ :=
    exists_differentialBasis_parameterChartAlgebra_localization R B π c g q
      (Localization.AtPrime q) ι b hb
  have _ : Module.Free (Localization.AtPrime q) Ω[Localization.AtPrime q⁄R] :=
    Module.Free.of_basis b'
  have htfae := Algebra.isSmoothAt_tfae_h1Cotangent_and_kaehlerDifferential
    (R := R) (S := C) q (Localization.AtPrime q)
  exact (htfae.out 3 5
    (a := Subsingleton (Algebra.H1Cotangent R (Localization.AtPrime q)) ∧
      Module.Projective (Localization.AtPrime q) Ω[Localization.AtPrime q⁄R])
    (b := Algebra.IsSmoothAt R q)).mp ⟨hH1, Module.Projective.of_free⟩

/-- A family of basis vectors picked out by an injection `Fin c → Fin n` is the left summand of a
reindexing of the basis by a sum type. -/
private theorem exists_basis_sum_inl_eq_of_injective {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {c n : ℕ} (b : Module.Basis (Fin n) R M) (e : Fin c → Fin n)
    (he : Function.Injective e) (v : Fin c → M) (hb : ∀ i, b (e i) = v i) :
    ∃ (ι : Type) (b' : Module.Basis (Fin c ⊕ ι) R M), ∀ i, b' (Sum.inl i) = v i := by
  let ei : Fin c ⊕ {j : Fin n // j ∉ Set.range e} ≃ Fin n :=
    (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range e))
  refine ⟨_, b.reindex ei.symm, fun i => ?_⟩
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, ← hb i]
  change b (Equiv.Set.sumCompl (Set.range e) (Sum.inl ⟨e i, ⟨i, rfl⟩⟩)) = b (e i)
  rw [Equiv.Set.sumCompl_apply_inl]

/-- In a Néron situation, the image in `A` of an element of the maximal ideal of `R` lies in
`𝔭`. -/
private theorem algebraMap_mem_maximalIdealPreimage (S : NeronSituation) {r : S.R}
    (hr : r ∈ IsLocalRing.maximalIdeal S.R) :
    algebraMap S.R S.A r ∈ S.maximalIdealPreimage := by
  have _ : IsLocalHom (algebraMap S.R S.Λ) := S.extension.2
  apply Ideal.mem_comap.mpr
  rw [← IsScalarTower.algebraMap_apply S.R S.A S.Λ, IsLocalRing.mem_maximalIdeal]
  exact fun hu => (IsLocalRing.mem_maximalIdeal r).mp hr
    (IsLocalHom.map_nonunit (f := algebraMap S.R S.Λ) r hu)

/-- In a Néron situation, the affine blowup `A[𝔭/a]` is of finite presentation over `R`. -/
private theorem finitePresentation_affineBlowupAlgebra (S : NeronSituation) (a : S.A) :
    Algebra.FinitePresentation S.R
      (affineBlowupAlgebra S.maximalIdealPreimage a (Localization.Away a)) := by
  have _ : IsNoetherianRing S.A := Algebra.FiniteType.isNoetherianRing S.R S.A
  have _ : Algebra.FiniteType S.R
      (affineBlowupAlgebra S.maximalIdealPreimage a (Localization.Away a)) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType S.R S.A)
      (affineBlowup_finiteType_of_fg _ S.maximalIdealPreimage.fg_of_isNoetherianRing)
  exact (Algebra.FinitePresentation.of_finiteType (R := S.R)).mp inferInstance

/-- The element `f ∉ 𝔭` has image outside the prime `𝔭'` of the affine Néron blowup. -/
private theorem algebraMap_affineBlowup_notMem_comap_canonicalNeronBlowupMap
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) {f : S.A}
    (hf : f ∉ S.maximalIdealPreimage) :
    algebraMap S.A (affineBlowupAlgebra S.maximalIdealPreimage (algebraMap S.R S.A π)
      (Localization.Away (algebraMap S.R S.A π))) f ∉
      Ideal.comap (canonicalNeronBlowupMap S π hπ).1 (IsLocalRing.maximalIdeal S.Λ) := by
  have hfa : (canonicalNeronBlowupMap S π hπ).1 (algebraMap S.A _ f) = algebraMap S.A S.Λ f :=
    congrArg (fun F : S.A →+* S.Λ => F f) (canonicalNeronBlowupMap S π hπ).2
  exact fun h => hf (Ideal.mem_comap.mpr (hfa ▸ h))

/-- **Stacks 0BJ4, smoothness.** In a Néron situation with uniformizer `π`, if `A` is smooth over
`R` at `𝔭` and the residue-field extension `κ(R) → κ(Λ)` is separable, then the affine blowup
`A' = A[𝔭/π]` is smooth over `R` at the prime `𝔭'` induced by the canonical map `A' → Λ`. -/
@[stacks 0BJ4 "blowup_smooth"]
theorem affineBlowup_smoothAt
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hS : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) :
    Algebra.SmoothAt S.R
      (affineBlowupAlgebra S.maximalIdealPreimage (algebraMap S.R S.A π)
        (Localization.Away (algebraMap S.R S.A π)))
      (Ideal.comap (canonicalNeronBlowupMap S π hπ).1
        (IsLocalRing.maximalIdeal S.Λ)) := by
  classical
  let T := affineBlowupAlgebra S.maximalIdealPreimage
    (algebraMap S.R S.A π) (Localization.Away (algebraMap S.R S.A π))
  let φ := (canonicalNeronBlowupMap S π hπ).1
  let qT : Ideal T := Ideal.comap φ (IsLocalRing.maximalIdeal S.Λ)
  have hqT : qT.IsPrime := Ideal.comap_isPrime _ _
  have hπA :=
    algebraMap_mem_maximalIdealPreimage S (r := π) (hπ ▸ Ideal.mem_span_singleton_self π)
  have hirr : Irreducible π :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π
      (uniformizer_ne_zero hπ) hπ
  obtain ⟨f, hf, hfSmooth, c, g, _, _, _, _, ⟨chartAlg, _⟩, n, b, e, he, hb⟩ :=
    exists_local_parameters_of_smoothAt S π hπ hsep hS
  let Aa := Localization.Away f
  let L := Localization.Away (algebraMap S.A T f)
  let Bl := affineBlowupAlgebra (S.maximalIdealPreimage.map (algebraMap S.A Aa))
    (algebraMap S.R Aa π) (Localization.Away (algebraMap S.R Aa π))
  obtain ⟨eLoc, hLocA, _⟩ := neron_affineBlowup_localization S π hirr f hf hπA
  let E : L ≃+* parameterChartAlgebra Aa (algebraMap S.R Aa π) c g :=
    eLoc.trans chartAlg.toRingEquiv
  let Ealg : L ≃ₐ[S.R] parameterChartAlgebra Aa (algebraMap S.R Aa π) c g :=
    AlgEquiv.ofRingEquiv (R := S.R) (f := E) fun r => by
      change chartAlg (eLoc (algebraMap S.R L r)) =
        algebraMap S.R (parameterChartAlgebra Aa (algebraMap S.R Aa π) c g) r
      calc
        chartAlg (eLoc (algebraMap S.R L r)) =
            chartAlg (eLoc (algebraMap T L (algebraMap S.A T (algebraMap S.R S.A r)))) := by
              rw [IsScalarTower.algebraMap_apply S.R T L,
                IsScalarTower.algebraMap_apply S.R S.A T]
        _ = chartAlg (algebraMap Aa Bl (algebraMap S.A Aa (algebraMap S.R S.A r))) :=
          congrArg chartAlg (hLocA (algebraMap S.R S.A r))
        _ = algebraMap S.R (parameterChartAlgebra Aa (algebraMap S.R Aa π) c g) r := by
              rw [← IsScalarTower.algebraMap_apply S.R S.A Aa,
                IsScalarTower.algebraMap_apply S.R Aa
                  (parameterChartAlgebra Aa (algebraMap S.R Aa π) c g)]
              exact chartAlg.commutes (algebraMap S.R Aa r)
  obtain ⟨ι, b', hb'⟩ := exists_basis_sum_inl_eq_of_injective b e he _ hb
  have _ : Algebra.IsSmoothAt S.R qT :=
    isSmoothAt_of_away_algEquiv qT (algebraMap S.A T f)
      (algebraMap_affineBlowup_notMem_comap_canonicalNeronBlowupMap S π hπ hf) Ealg fun p =>
      isSmoothAt_parameterChartAlgebra S.R Aa hfSmooth π c g ι b' hb' p
  have _ := finitePresentation_affineBlowupAlgebra S (algebraMap S.R S.A π)
  exact Algebra.IsSmoothAt.exists_notMem_smooth S.R qT

section Diagonal

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {c : ℕ} {ι : Type*} {π : R}
  (b : Module.Basis (Fin c ⊕ ι) R M) (b' : Module.Basis (Fin c ⊕ ι) R N) (f : M →ₗ[R] N)
  (hf : ∀ i, f (b (Sum.inl i)) = π • b' (Sum.inl i))
  (hg : ∀ j, f (b (Sum.inr j)) = b' (Sum.inr j))
include hf hg

/-- A map which is multiplication by `π` on a common sub-basis multiplies the corresponding
coordinates by `π`. -/
private theorem repr_inl_of_diagonal (x : M) (i : Fin c) :
    (b'.repr (f x)) (Sum.inl i) = π * (b.repr x) (Sum.inl i) := by
  classical
  have hmaps : ((Finsupp.lapply (Sum.inl i)).comp b'.repr.toLinearMap).comp f =
      (LinearMap.mulLeft R π).comp
        ((Finsupp.lapply (Sum.inl i)).comp b.repr.toLinearMap) := by
    apply b.ext
    intro j
    cases j with
    | inl j => simp [hf, Finsupp.single_apply]
    | inr j => simp [hg]
  simpa [LinearMap.comp_apply, Finsupp.lapply_apply, mul_comm] using
    DFunLike.congr_fun hmaps x

/-- A map which is the identity on the complement of a common sub-basis preserves the
corresponding coordinates. -/
private theorem repr_inr_of_diagonal (x : M) (j : ι) :
    (b'.repr (f x)) (Sum.inr j) = (b.repr x) (Sum.inr j) := by
  have hmaps : ((Finsupp.lapply (Sum.inr j)).comp b'.repr.toLinearMap).comp f =
      (Finsupp.lapply (Sum.inr j)).comp b.repr.toLinearMap := by
    apply b.ext
    intro k
    cases k with
    | inl k => simp [hf]
    | inr k => simp [hg]
  simpa [LinearMap.comp_apply, Finsupp.lapply_apply] using DFunLike.congr_fun hmaps x

/-- A map which is multiplication by a non-zero-divisor `π` on a common sub-basis and the
identity on its complement is injective. -/
private theorem injective_of_diagonal (hπ : π ∈ nonZeroDivisors R) : Function.Injective f := by
  intro x y hxy
  apply b.repr.injective
  ext k
  have hfx : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  cases k with
  | inl i =>
      have h := repr_inl_of_diagonal b b' f hf hg (x - y) i
      rw [hfx, map_zero] at h
      have hz : (b.repr (x - y)) (Sum.inl i) = 0 :=
        (mem_nonZeroDivisors_iff.mp hπ).1 _ (by simpa [mul_comm] using h.symm)
      exact sub_eq_zero.mp (by simpa [map_sub] using hz)
  | inr j =>
      have h := repr_inr_of_diagonal b b' f hf hg (x - y) j
      rw [hfx, map_zero] at h
      exact sub_eq_zero.mp (by simpa [map_sub] using h.symm)

/-- For a map which is multiplication by `π` on a common sub-basis and the identity on its
complement, every vector whose sub-basis coordinates are divisible by `π` lies in the range. -/
private theorem mem_range_of_diagonal (y : N) (hy : ∀ i, π ∣ b'.repr y (Sum.inl i)) :
    y ∈ LinearMap.range f := by
  classical
  choose l hl using hy
  let right : Fin c ⊕ ι →₀ R :=
    Finsupp.filter (fun k => match k with | .inl _ => False | .inr _ => True) (b'.repr y)
  refine ⟨b.repr.symm
    (Finsupp.embDomain Function.Embedding.inl (Finsupp.equivFunOnFinite.symm l) + right), ?_⟩
  apply b'.repr.injective
  ext k
  cases k with
  | inl i =>
      rw [repr_inl_of_diagonal b b' f hf hg]
      simp only [right, LinearEquiv.apply_symm_apply, Finsupp.add_apply,
        Finsupp.embDomain_apply, Finsupp.filter_apply]
      simpa [Finsupp.equivFunOnFinite] using (hl i).symm
  | inr j =>
      rw [repr_inr_of_diagonal b b' f hf hg]
      simp only [right, LinearEquiv.apply_symm_apply, Finsupp.add_apply,
        Finsupp.embDomain_apply, Finsupp.filter_apply]
      simp [Function.Embedding.inl]

end Diagonal

/-- A map of free modules which is multiplication by `π` on a common sub-basis and the identity on
its complement is injective with cokernel `(R/πR)^c`, provided `π` is a non-zero-divisor. -/
private theorem diagonal_basis_shortExact
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (c : ℕ) (ι : Type*) (π : R) (hπ : π ∈ nonZeroDivisors R)
    (b : Module.Basis (Fin c ⊕ ι) R M) (b' : Module.Basis (Fin c ⊕ ι) R N) (f : M →ₗ[R] N)
    (hf : ∀ i, f (b (Sum.inl i)) = π • b' (Sum.inl i))
    (hg : ∀ j, f (b (Sum.inr j)) = b' (Sum.inr j)) :
    ∃ g : N →ₗ[R] (Fin c → R ⧸ Ideal.span ({π} : Set R)),
      Function.Exact f g ∧ Function.Injective f ∧ Function.Surjective g := by
  classical
  let I : Ideal R := Ideal.span ({π} : Set R)
  let g : N →ₗ[R] (Fin c → R ⧸ I) :=
    { toFun := fun x i => Ideal.Quotient.mk I ((b'.repr x) (Sum.inl i))
      map_add' := by
        intro x y
        ext i
        change Ideal.Quotient.mk I ((b'.repr (x + y)) (Sum.inl i)) =
          Ideal.Quotient.mk I ((b'.repr x) (Sum.inl i)) +
            Ideal.Quotient.mk I ((b'.repr y) (Sum.inl i))
        simp [map_add]
      map_smul' := by
        intro a x
        ext i
        change Ideal.Quotient.mk I ((b'.repr (a • x)) (Sum.inl i)) =
          a • Ideal.Quotient.mk I ((b'.repr x) (Sum.inl i))
        simp [Algebra.smul_def] }
  have hcomp : g.comp f = 0 := by
    ext x i
    change Ideal.Quotient.mk I ((b'.repr (f x)) (Sum.inl i)) = 0
    rw [repr_inl_of_diagonal b b' f hf hg]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_right _ I (Ideal.subset_span (by simp)))
  have hexact : Function.Exact f g := by
    apply LinearMap.exact_iff.2
    ext y
    refine ⟨fun hy => ?_, ?_⟩
    · have hy0 : g y = 0 := by simpa [LinearMap.mem_ker] using hy
      exact mem_range_of_diagonal b b' f hf hg y fun i =>
        Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp
          (show Ideal.Quotient.mk I (b'.repr y (Sum.inl i)) = 0 by
            simpa [g, I] using congrFun hy0 i))
    · rintro ⟨x, rfl⟩
      exact DFunLike.congr_fun hcomp x
  have hsurj : Function.Surjective g := by
    intro z
    let left : Fin c →₀ R := Finsupp.equivFunOnFinite.symm fun i =>
      Classical.choose (Ideal.Quotient.mk_surjective (z i))
    refine ⟨b'.repr.symm (Finsupp.embDomain Function.Embedding.inl left), ?_⟩
    funext i
    simp [g, left, Finsupp.equivFunOnFinite,
      Classical.choose_spec (Ideal.Quotient.mk_surjective (z i))]
  exact ⟨g, hexact, injective_of_diagonal b b' f hf hg hπ, hsurj⟩

/-- The relative differentials of a localized parameter chart, in a basis adapted to the chart.
Let `A → A'` be a map of `R`-algebras, let `C` be an `A`-algebra formally étale over `A`, let
`Qc = C[y₁, …, y_c]/(π yᵢ - gᵢ)` be a parameter chart whose `d gᵢ` are part of a basis of
`Ω_{C/R}`, and let `B` be a localization of `Qc` at a prime which is also formally étale over
`A'`. Then the base change to `B` of `Ω_{A/R} → Ω_{A'/R}` is, in suitable bases, multiplication by
`π` on the `c` chart directions and the identity on the complementary ones, hence injective with
cokernel `(B/πB)^c`. -/
private theorem exists_diagonal_differentials_parameterChart
    (R A A' C : Type*) [CommRing R] [CommRing A] [CommRing A'] [CommRing C]
    [Algebra R A] [Algebra R A'] [Algebra R C] [Algebra A A'] [Algebra A C]
    [IsScalarTower R A A'] [IsScalarTower R A C]
    (π : R) (c : ℕ) (g : Fin c → C) (ι : Type*)
    (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [Algebra A' B] [Algebra C B]
    [Algebra (parameterChartAlgebra C (algebraMap R C π) c g) B]
    [IsScalarTower R A B] [IsScalarTower A A' B] [IsScalarTower R A' B]
    [IsScalarTower A C B] [IsScalarTower R C B]
    [IsScalarTower C (parameterChartAlgebra C (algebraMap R C π) c g) B]
    [IsScalarTower R (parameterChartAlgebra C (algebraMap R C π) c g) B]
    [Algebra.FormallyEtale A C] [Algebra.FormallyEtale A' B]
    (q : Ideal (parameterChartAlgebra C (algebraMap R C π) c g)) [q.IsPrime]
    [IsLocalization.AtPrime B q]
    (b : Module.Basis (Fin c ⊕ ι) C (KaehlerDifferential R C))
    (hb : ∀ i, b (Sum.inl i) = KaehlerDifferential.D R C (g i))
    (ϖ : B) (hϖ : ϖ = algebraMap R B π) (hϖnzd : ϖ ∈ nonZeroDivisors B) :
    ∃ (φ : B ⊗[A] Ω[A⁄R] →ₗ[B] B ⊗[A'] Ω[A'⁄R])
      (_ : ∀ (x : B) (y : Ω[A⁄R]),
        φ (x ⊗ₜ[A] y) = x ⊗ₜ[A'] KaehlerDifferential.map R R A A' y)
      (ψ : B ⊗[A'] Ω[A'⁄R] →ₗ[B] (Fin c → B ⧸ Ideal.span ({ϖ} : Set B))),
      Function.Exact φ ψ ∧ Function.Injective φ ∧ Function.Surjective ψ := by
  obtain ⟨bQloc, hbQlocLeft, hbQlocRight⟩ :=
    exists_differentialBasis_parameterChartAlgebra_localization R C π c g q B ι b hb
  let φ : B ⊗[A] Ω[A⁄R] →ₗ[B] B ⊗[A'] Ω[A'⁄R] :=
    (TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl B B).toLinearMap
        (KaehlerDifferential.mapBaseChange R A A')) ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A A' B B Ω[A⁄R]).symm.toLinearMap
  have hφ (x : B) (y : Ω[A⁄R]) :
      φ (x ⊗ₜ[A] y) = x ⊗ₜ[A'] KaehlerDifferential.map R R A A' y := by
    change (TensorProduct.AlgebraTensorModule.map (LinearEquiv.refl B B).toLinearMap
        (KaehlerDifferential.mapBaseChange R A A'))
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange A A' B B Ω[A⁄R]).symm
          (x ⊗ₜ[A] y)) = _
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.map_tmul, KaehlerDifferential.mapBaseChange_tmul]
    congr 1
    exact one_smul A' (KaehlerDifferential.map R R A A' y)
  clear_value φ
  let eSource : B ⊗[A] Ω[A⁄R] ≃ₗ[B] B ⊗[C] Ω[C⁄R] :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A C B B Ω[A⁄R]).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A C))
  have heSourceTmul (x : B) (y : Ω[A⁄R]) :
      eSource (x ⊗ₜ[A] y) = x ⊗ₜ[C] KaehlerDifferential.map R R A C y := by
    simp only [eSource, LinearEquiv.trans_apply,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul]
  let eTarget : B ⊗[A'] Ω[A'⁄R] ≃ₗ[B] Ω[B⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A' B
  have heTargetTmul (x : B) (y : Ω[A'⁄R]) :
      eTarget (x ⊗ₜ[A'] y) = x • KaehlerDifferential.map R R A' B y := by
    change KaehlerDifferential.mapBaseChange R A' B (x ⊗ₜ[A'] y) = _
    rw [KaehlerDifferential.mapBaseChange_tmul]
  clear_value eSource eTarget
  have hcommute (z : B ⊗[A] Ω[A⁄R]) :
      eTarget (φ z) = KaehlerDifferential.mapBaseChange R C B (eSource z) := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y =>
        rw [hφ, heTargetTmul, heSourceTmul, KaehlerDifferential.mapBaseChange_tmul]
        congr 1
        calc
          KaehlerDifferential.map R R A' B (KaehlerDifferential.map R R A A' y) =
              KaehlerDifferential.map R R A B y :=
            congrArg (fun F : Ω[A⁄R] →ₗ[A] Ω[B⁄R] => F y)
              (KaehlerDifferential.map_comp_map R A A' B)
          _ = KaehlerDifferential.map R R C B (KaehlerDifferential.map R R A C y) :=
            (congrArg (fun F : Ω[A⁄R] →ₗ[A] Ω[B⁄R] => F y)
              (KaehlerDifferential.map_comp_map R A C B)).symm
  let bSource : Module.Basis (Fin c ⊕ ι) B (B ⊗[A] Ω[A⁄R]) :=
    (b.baseChange B).map eSource.symm
  let bTarget : Module.Basis (Fin c ⊕ ι) B (B ⊗[A'] Ω[A'⁄R]) := bQloc.map eTarget.symm
  have hsourceBasis (k : Fin c ⊕ ι) : eSource (bSource k) = (1 : B) ⊗ₜ[C] b k := by
    change eSource (eSource.symm ((b.baseChange B) k)) = _
    rw [eSource.apply_symm_apply]
    exact Module.Basis.baseChange_apply B b k
  have htargetBasis (k : Fin c ⊕ ι) : eTarget (bTarget k) = bQloc k := by
    change eTarget (eTarget.symm (bQloc k)) = _
    exact eTarget.apply_symm_apply _
  clear_value bSource bTarget
  have htransport (k : Fin c ⊕ ι) :
      eTarget (φ (bSource k)) =
        KaehlerDifferential.mapBaseChange R C B ((1 : B) ⊗ₜ[C] b k) := by
    rw [hcommute (bSource k), hsourceBasis]
  have hdiagLeft (i : Fin c) : φ (bSource (Sum.inl i)) = ϖ • bTarget (Sum.inl i) := by
    rw [hϖ]
    apply eTarget.injective
    rw [htransport, map_smul, htargetBasis, hb i, hbQlocLeft i]
    exact mapBaseChange_D_parameterChartAlgebra_localization R C π c g B i
  have hdiagRight (j : ι) : φ (bSource (Sum.inr j)) = bTarget (Sum.inr j) := by
    apply eTarget.injective
    rw [htransport, htargetBasis, hbQlocRight j]
  exact ⟨φ, hφ, diagonal_basis_shortExact c ι ϖ hϖnzd bSource bTarget φ hdiagLeft hdiagRight⟩

/-- A parameter chart `C[y₁, …, y_c]/(π yᵢ - gᵢ)` over a smooth `R`-algebra `C`, whose `d gᵢ` are
part of a basis of `Ω_{C/R}`, is smooth over `R`. -/
private theorem smooth_parameterChartAlgebra
    (R C : Type*) [CommRing R] [CommRing C] [Algebra R C] (hsm : Algebra.Smooth R C)
    (π : R) (c : ℕ) (g : Fin c → C) (ι : Type*)
    (b : Module.Basis (Fin c ⊕ ι) C (KaehlerDifferential R C))
    (hb : ∀ i, b (Sum.inl i) = KaehlerDifferential.D R C (g i)) :
    Algebra.Smooth R (parameterChartAlgebra C (algebraMap R C π) c g) := by
  have _ : Algebra.FormallySmooth R C := hsm.formallySmooth
  have _ : Algebra.FinitePresentation C (parameterChartAlgebra C (algebraMap R C π) c g) :=
    Algebra.FinitePresentation.quotient
      (Submodule.fg_span (Set.finite_range fun i : Fin c =>
        MvPolynomial.C (algebraMap R C π) * MvPolynomial.X i - MvPolynomial.C (g i)))
  have _ : Algebra.FinitePresentation R C := hsm.finitePresentation
  exact ⟨(formallySmooth_and_exists_differentialBasis_parameterChartAlgebra R C π c g ι b hb).1
    (Algebra.FormallySmooth.comp R C (MvPolynomial (Fin c) C)),
    Algebra.FinitePresentation.trans R C _⟩

/-- The differential sequence of a blowup chart which becomes a parameter chart after inverting
one element. Let `A → A'` be a map of `R`-algebras, let `C = A[1/a]`, and suppose the localization
`L = A'[1/a]` is isomorphic as a ring to a parameter chart `C[y₁, …, y_c]/(π yᵢ - gᵢ)` compatibly
with the maps from `A`, the `d gᵢ` being part of a basis of `Ω_{C/R}` for a smooth `C`. Then for
any localization `B` of `A'` at a prime avoiding `a`, the base change to `B` of
`Ω_{A/R} → Ω_{A'/R}` is injective with cokernel `(B/πB)^c`. -/
private theorem exists_diagonal_differentials_of_awayChart
    (R A A' C L : Type*) [CommRing R] [CommRing A] [CommRing A'] [CommRing C] [CommRing L]
    [Algebra R A] [Algebra R A'] [Algebra R C] [Algebra A A'] [Algebra A C] [Algebra A' L]
    [IsScalarTower R A A'] [IsScalarTower R A C]
    (a : A) [IsLocalization.Away a C] [IsLocalization.Away (algebraMap A A' a) L]
    (π : R) (hπ : π ∈ nonZeroDivisors R) (c : ℕ) (g : Fin c → C) (ι : Type*)
    (e : L ≃+* parameterChartAlgebra C (algebraMap R C π) c g)
    (he : ∀ x : A, e (algebraMap A' L (algebraMap A A' x)) =
      algebraMap C (parameterChartAlgebra C (algebraMap R C π) c g) (algebraMap A C x))
    (b : Module.Basis (Fin c ⊕ ι) C (KaehlerDifferential R C))
    (hb : ∀ i, b (Sum.inl i) = KaehlerDifferential.D R C (g i))
    (hsm : Algebra.Smooth R C)
    (B : Type*) [CommRing B] [Algebra A B] [Algebra A' B] [IsScalarTower A A' B]
    (p : Ideal A') [p.IsPrime] [IsLocalization.AtPrime B p]
    (ha : algebraMap A A' a ∉ p) :
    ∃ (φ : B ⊗[A] Ω[A⁄R] →ₗ[B] B ⊗[A'] Ω[A'⁄R])
      (_ : ∀ (x : B) (y : Ω[A⁄R]),
        φ (x ⊗ₜ[A] y) = x ⊗ₜ[A'] KaehlerDifferential.map R R A A' y)
      (ψ : B ⊗[A'] Ω[A'⁄R] →ₗ[B]
          (Fin c → B ⧸ Ideal.span ({algebraMap A' B (algebraMap R A' π)} : Set B))),
      Function.Exact φ ψ ∧ Function.Injective φ ∧ Function.Surjective ψ := by
  let Qc := parameterChartAlgebra C (algebraMap R C π) c g
  let aA' : A' := algebraMap A A' a
  -- `B` is itself a model of the localization of the parameter chart at the prime corresponding
  -- to `p`: the chart is `A'[1/aA']`, and `aA' ∉ p`.
  let instA'Qc : Algebra A' Qc := RingHom.toAlgebra (e.toRingHom.comp (algebraMap A' L))
  let eA' : L ≃ₐ[A'] Qc := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  have _ : IsLocalization.Away aA' Qc :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers aA') eA'
  let q : Ideal Qc := Ideal.map (algebraMap A' Qc) p
  have _ : q.IsPrime := isPrime_map_algebraMap_of_notMem p ha
  have haUnit : IsUnit (algebraMap A' B aA') :=
    (IsLocalization.AtPrime.isUnit_to_map_iff B p aA').2 ha
  have haUnitA : IsUnit (algebraMap A B a) := by
    rwa [IsScalarTower.algebraMap_apply A A' B a]
  let instRB : Algebra R B := RingHom.toAlgebra ((algebraMap A' B).comp (algebraMap R A'))
  have _ : IsScalarTower R A' B := IsScalarTower.of_algebraMap_eq' rfl
  clear_value instRB
  let instCB : Algebra C B := RingHom.toAlgebra (IsLocalization.Away.lift (S := C) a haUnitA)
  have hAB : (algebraMap C B).comp (algebraMap A C) = algebraMap A B :=
    IsLocalization.Away.lift_comp (S := C) a haUnitA
  have _ : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq' hAB.symm
  let instQcB : Algebra Qc B :=
    RingHom.toAlgebra (IsLocalization.Away.lift (S := Qc) aA' haUnit)
  have hQcB : (algebraMap Qc B).comp (algebraMap A' Qc) = algebraMap A' B :=
    IsLocalization.Away.lift_comp (S := Qc) aA' haUnit
  have _ : IsScalarTower A' Qc B := IsScalarTower.of_algebraMap_eq' hQcB.symm
  have _ : IsLocalization.AtPrime B q :=
    isLocalization_atPrime_map_of_notMem (B := Qc) (C := B) ha
  have hCQcB : (algebraMap Qc B).comp (algebraMap C Qc) = algebraMap C B := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext x
    change algebraMap Qc B (algebraMap C Qc (algebraMap A C x)) =
      algebraMap C B (algebraMap A C x)
    rw [← he x]
    change algebraMap Qc B (algebraMap A' Qc (algebraMap A A' x)) = _
    rw [← IsScalarTower.algebraMap_apply A' Qc B, ← IsScalarTower.algebraMap_apply A A' B]
    exact (congrArg (fun F : A →+* B => F x) hAB).symm
  have _ : IsScalarTower C Qc B := IsScalarTower.of_algebraMap_eq' hCQcB.symm
  have _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A' B, IsScalarTower.algebraMap_apply R A A' r,
      ← IsScalarTower.algebraMap_apply A A' B]
  have _ : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A C r]
    exact (IsScalarTower.algebraMap_apply R A B r).trans (RingHom.congr_fun hAB _).symm
  have _ : IsScalarTower R Qc B := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R C B, IsScalarTower.algebraMap_eq R C Qc,
      ← RingHom.comp_assoc, hCQcB])
  have _ : Algebra.FormallyEtale A' B := Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have _ : Algebra.FormallyEtale A C :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers a)
  have _ : Algebra.Smooth R Qc := smooth_parameterChartAlgebra R C hsm π c g ι b hb
  have _ : Module.Flat R Qc := Algebra.Smooth.flat R Qc
  have _ : Module.Flat Qc B := IsLocalization.flat B q.primeCompl
  have _ : Module.Flat R B := Module.Flat.trans R Qc B
  have hπeq : algebraMap A' B (algebraMap R A' π) = algebraMap R B π :=
    (IsScalarTower.algebraMap_apply R A' B π).symm
  exact exists_diagonal_differentials_parameterChart R A A' C π c g ι B q b hb _ hπeq
    (hπeq ▸ algebraMap_mem_nonZeroDivisors_of_flat hπ)

set_option maxHeartbeats 340000 in
-- Elaborating the statement alone costs 108665 heartbeats -- over half the default budget --
-- because every clause is an `∃` over module maps between tensor products taken over the
-- subalgebra `A'`; the proof shares that budget, and what is left does not cover the single
-- `isDefEq` against the goal. The computation itself has been hoisted into the two abstract
-- lemmas above, where it costs 20160 and 12890 heartbeats.
/-- **Stacks 0BJ4, the differential sequence.** In a Néron situation with uniformizer `π`, if `A`
is smooth over `R` at `𝔭` and the residue-field extension `κ(R) → κ(Λ)` is separable, then for
`c = dim (A/πA)_𝔭` the relative differentials of the affine blowup `A'` at its prime `𝔭'` sit in a
short exact sequence
`0 → Ω_{A/R} ⊗_A A'_{𝔭'} → Ω_{A'/R} ⊗_{A'} A'_{𝔭'} → ((A'/πA')_{𝔭'})^c → 0`,
whose first map is the base change of `Ω_{A/R} → Ω_{A'/R}`. -/
@[stacks 0BJ4 "differentials_sequence"]
theorem affineBlowup_differentials_shortExact
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage)
    (c : ℕ)
    (hc : ringKrullDim
      ((Localization.AtPrime S.maximalIdealPreimage) ⧸
        Ideal.span ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} :
          Set (Localization.AtPrime S.maximalIdealPreimage))) = c) :
    let A' := affineBlowupAlgebra S.maximalIdealPreimage (algebraMap S.R S.A π)
      (Localization.Away (algebraMap S.R S.A π))
    ∀ (p' : Ideal A') [p'.IsPrime],
      p' = Ideal.comap (canonicalNeronBlowupMap S π hπ).1 (IsLocalRing.maximalIdeal S.Λ) →
      ∀ (B : Type w) [CommRing B] [Algebra A' B] [IsLocalization.AtPrime B p']
        [Algebra S.A B] [IsScalarTower S.A A' B],
        let Q := B ⧸ Ideal.span ({algebraMap A' B (algebraMap S.R A' π)} : Set B)
        ∃ (f : B ⊗[S.A] Ω[S.A⁄S.R] →ₗ[B] B ⊗[A'] Ω[A'⁄S.R])
          (_ : ∀ (x : B) (y : Ω[S.A⁄S.R]),
            f (x ⊗ₜ[S.A] y) = x ⊗ₜ[A'] KaehlerDifferential.map S.R S.R S.A A' y)
          (g : B ⊗[A'] Ω[A'⁄S.R] →ₗ[B] (Fin c → Q))
          (hzero : ModuleCat.ofHom f ≫ ModuleCat.ofHom g = 0),
          (ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) hzero).ShortExact := by
  classical
  dsimp only
  intro p' hp' hpB B instComm instAlg instLoc instAlgA instTower
  obtain ⟨f₀, hf₀, hsm₀, c₀, g₀, hc₀, _, _, _, hbasis₀⟩ :=
    exists_local_parameters_of_smoothAt S π hπ hsep hsm
  have hcEq : c₀ = c := by exact_mod_cast hc₀.symm.trans hc
  subst c₀
  have hπirr : Irreducible π :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π
      (uniformizer_ne_zero hπ) hπ
  have hπA : algebraMap S.R S.A π ∈ S.maximalIdealPreimage :=
    algebraMap_mem_maximalIdealPreimage S (hπ ▸ Ideal.mem_span_singleton_self π)
  obtain ⟨eloc, helocA, _⟩ := neron_affineBlowup_localization S π hπirr f₀ hf₀ hπA
  obtain ⟨⟨echart, _⟩, n, braw, e, he, hbraw⟩ := hbasis₀
  let ι := {j : Fin n // j ∉ Set.range e}
  let eIdx : Fin c ⊕ ι ≃ Fin n :=
    (Equiv.sumCongr (Equiv.ofInjective e he) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range e))
  let bC : Module.Basis (Fin c ⊕ ι) (Localization.Away f₀)
      (KaehlerDifferential S.R (Localization.Away f₀)) := braw.reindex eIdx.symm
  have heIdx_inl (i : Fin c) : eIdx (Sum.inl i) = e i := by
    change (Equiv.Set.sumCompl (Set.range e)) (Sum.inl ⟨e i, ⟨i, rfl⟩⟩) = e i
    exact Equiv.Set.sumCompl_apply_inl _ _
  have hbC (i : Fin c) :
      bC (Sum.inl i) = KaehlerDifferential.D S.R (Localization.Away f₀) (g₀ i) := by
    simp only [bC, Module.Basis.reindex_apply, Equiv.symm_symm]
    rw [heIdx_inl]
    exact hbraw i
  -- Everything below uses `bC` only through `hbC`, so the reindexing is discarded: keeping its
  -- body in the context makes every later unifier unfold it.
  clear_value bC
  clear heIdx_inl hbraw eIdx braw
  clear_value ι
  clear he e
  let A' := affineBlowupAlgebra S.maximalIdealPreimage
    (algebraMap S.R S.A π) (Localization.Away (algebraMap S.R S.A π))
  let C := Localization.Away f₀
  let L := Localization.Away (algebraMap S.A A' f₀)
  have hfnot : algebraMap S.A A' f₀ ∉ p' := by
    rw [hpB]
    exact algebraMap_affineBlowup_notMem_comap_canonicalNeronBlowupMap S π hπ hf₀
  have hchart (x : S.A) :
      (eloc.trans echart.toRingEquiv) (algebraMap A' L (algebraMap S.A A' x)) =
        algebraMap C (parameterChartAlgebra C (algebraMap S.R C π) c g₀)
          (algebraMap S.A C x) := by
    change echart (eloc (algebraMap A' L (algebraMap S.A A' x))) = _
    rw [helocA x]
    exact echart.commutes _
  obtain ⟨f, hf, gFinal, hgExact, hgInj, hgSurj⟩ :=
    exists_diagonal_differentials_of_awayChart S.R S.A A' C L f₀ π
      (mem_nonZeroDivisors_iff_ne_zero.mpr hπirr.ne_zero) c g₀ ι
      (eloc.trans echart.toRingEquiv) hchart bC hbC hsm₀ B p' hfnot
  have hzero : ModuleCat.ofHom f ≫ ModuleCat.ofHom gFinal = 0 :=
    ModuleCat.hom_ext (Function.Exact.linearMap_comp_eq_zero hgExact)
  refine ⟨f, hf, gFinal, hzero, ?_⟩
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom gFinal) hzero)).2 hgExact)
    ((ModuleCat.mono_iff_injective _).2 hgInj)
    ((ModuleCat.epi_iff_surjective _).2 hgSurj)

end Stacks.Smoothing

end
