module

public import StacksFrontier.RingTheory.Flat.FlatteningHenselianReductionLocalize
public import StacksFrontier.RingTheory.Flat.FlatteningHenselianReductionTransfer
public import StacksFrontier.RingTheory.Flat.ElementaryEtaleLocalizationHenselian
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraExistence

/-!
# Reduction of the local flattening theorem to a complete dévissage over the base

This is the first paragraph of the source's proof of Stacks Tag 05PG. In the situation of
Stacks Tag 05MK with `A` henselian, `B` essentially of finite type over `A` and `M` finite over
`B`, write `B = (C₀)_{q₀}` and `M = (N₀)_{q₀}` for a finite type `A`-algebra `C₀` and a finite
`C₀`-module `N₀`. Stacks Tag 05I1 gives an elementary étale localization of `A → C₀` at `q₀`
over which the base change of `N₀` has a complete dévissage; since `A` is henselian the base of
that localization is, after localizing at its distinguished prime, `A` itself
(`Algebra.ElementaryEtaleLocalization.exists_isLocalization_primeCompl_of_henselian`), so the
dévissage can be moved to the base `A`. The flatness condition of Stacks Tag 05ML does not
change along the way, by Stacks Tag 05P5 (in the form
`Module.isFlatAtPrimesAbove_iff_of_flat`).

## Main results

* `Algebra.EssFiniteType.exists_finiteType_isLocalization_atPrime`: a local algebra essentially
  of finite type over `A` is the localization at a prime of a finite type `A`-algebra in the
  universe of `A`.
* `Module.exists_finite_isLocalizedModule`: a finite module over a localization of `C` is the
  localization of a finite `C`-module in the universe of `C`.
* `Module.FlatAtPointSituation.exists_devissage_isFlatAtPrimesAbove`: the reduction.

## References

* [Stacks Project, Tag 05I1](https://stacks.math.columbia.edu/tag/05I1)
* [Stacks Project, Tag 05P5](https://stacks.math.columbia.edu/tag/05P5)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w x u₁ u₂

/-- A local algebra `B` essentially of finite type over `A` is the localization, at the
contraction of its maximal ideal, of a finite type `A`-algebra living in the universe of `A`. -/
theorem Algebra.EssFiniteType.exists_finiteType_isLocalization_atPrime (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra.EssFiniteType A B] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FiniteType A C)
      (_ : Algebra C B) (_ : IsScalarTower A C B),
      IsLocalization ((maximalIdeal B).comap (algebraMap C B)).primeCompl B := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A (Algebra.EssFiniteType.subalgebra A B))
  let ψ : MvPolynomial (Fin n) A →ₐ[A] B := (Algebra.EssFiniteType.subalgebra A B).val.comp f
  let ψ' := Ideal.kerLiftAlg ψ
  let : Algebra (MvPolynomial (Fin n) A ⧸ RingHom.ker ψ) B := ψ'.toRingHom.toAlgebra
  have hψ' : ∀ y, algebraMap (MvPolynomial (Fin n) A ⧸ RingHom.ker ψ) B y = ψ' y := fun _ => rfl
  have hmk : ∀ y, ψ' (Ideal.Quotient.mk _ y) = (f y : B) := fun _ => rfl
  refine ⟨MvPolynomial (Fin n) A ⧸ RingHom.ker ψ, inferInstance, inferInstance,
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A _)
      Ideal.Quotient.mk_surjective,
    inferInstance, IsScalarTower.of_algebraMap_eq fun a => (ψ'.commutes a).symm, ?_⟩
  rw [isLocalization_iff]
  refine ⟨fun ⟨c, hc⟩ => ?_, fun b => ?_, fun {y z} h => ?_⟩
  · by_contra h
    exact hc (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr h))
  · obtain ⟨⟨y, t⟩, h⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid A B) b
    obtain ⟨y', hy'⟩ := hf y
    obtain ⟨t', ht'⟩ := hf t.1
    refine ⟨⟨Ideal.Quotient.mk _ y', ⟨Ideal.Quotient.mk _ t', fun hm => ?_⟩⟩, ?_⟩
    · have hm' : algebraMap _ B (Ideal.Quotient.mk (RingHom.ker ψ) t') ∈ maximalIdeal B := hm
      rw [hψ', hmk, ht'] at hm'
      exact (mem_maximalIdeal _).mp hm' t.2
    · show b * ψ' (Ideal.Quotient.mk _ t') = ψ' (Ideal.Quotient.mk _ y')
      rwa [hmk, hmk, ht', hy']
  · exact ⟨1, by rw [Ideal.kerLiftAlg_injective ψ h]⟩

/-- A finite module `M` over a localization `B` of `C` is the localization of a finite
`C`-module living in the universe of `C`: a quotient of a finite free `C`-module mapping onto
generators of `M`. -/
theorem Module.exists_finite_isLocalizedModule {C : Type u} [CommRing C] {B : Type v}
    [CommRing B] [Algebra C B] (P : Submonoid C) [IsLocalization P B] (M : Type w)
    [AddCommGroup M] [Module B M] [Module.Finite B M] [Module C M] [IsScalarTower C B M] :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module C N) (_ : Module.Finite C N)
      (g : N →ₗ[C] M), IsLocalizedModule P g := by
  classical
  obtain ⟨k, m, hm⟩ := Module.Finite.exists_fin (R := B) (M := M)
  let φ : (Fin k →₀ C) →ₗ[C] M := Finsupp.linearCombination C m
  let g := (LinearMap.ker φ).liftQ φ le_rfl
  refine ⟨_ ⧸ LinearMap.ker φ, inferInstance, inferInstance, inferInstance, g, ?_⟩
  refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by
    simpa using LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl) h⟩⟩
  · obtain ⟨u, hu⟩ : IsUnit (algebraMap C B s) := IsLocalization.map_units B s
    rw [Module.End.isUnit_iff]
    refine ⟨fun a b hab => ?_, fun a => ⟨u⁻¹ • a, ?_⟩⟩
    · simp only [Module.algebraMap_end_apply] at hab
      rw [← algebraMap_smul B (s : C) a, ← algebraMap_smul B (s : C) b, ← hu,
        ← Units.smul_def, ← Units.smul_def] at hab
      exact smul_left_cancel u hab
    · simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul B (s : C), ← hu, ← Units.smul_def, smul_inv_smul]
  · have hy : y ∈ Submodule.span B (Set.range m) := hm ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hy
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples P Finset.univ c
    choose d hd using fun i => hb i (Finset.mem_univ i)
    refine ⟨⟨Submodule.Quotient.mk (Finsupp.equivFunOnFinite.symm d), b⟩, ?_⟩
    show (b : C) • y = φ (Finsupp.equivFunOnFinite.symm d)
    rw [← hc, Finset.smul_sum, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _
      (fun i => zero_smul C (m i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.coe_equivFunOnFinite_symm, ← algebraMap_smul B (d i), hd i,
      smul_assoc]

/-- Over a henselian local base, the lower right ring of an elementary étale localization at a
prime lying over the maximal ideal retracts onto the base, which is its localization at the
distinguished prime. This is
`Algebra.ElementaryEtaleLocalization.exists_isLocalization_primeCompl_of_henselian` for a prime
of the base which is equal, rather than identical, to the maximal ideal. -/
theorem Algebra.ElementaryEtaleLocalization.exists_isLocalization_of_henselian_of_eq
    {A : Type u} [CommRing A] [HenselianLocalRing A] {S : Type v} [CommRing S] [Algebra A S]
    {p : Ideal A} [p.IsPrime] {q : Ideal S} [q.IsPrime] [q.LiesOver p]
    (hp : p = maximalIdeal A) (E : ElementaryEtaleLocalization.{u, v, u₁, u₂} A S p q) :
    ∃ σ : E.R' →ₐ[A] A, (maximalIdeal A).comap σ.toRingHom = E.p' ∧
      letI : Algebra E.R' A := σ.toRingHom.toAlgebra
      IsLocalization E.p'.primeCompl A := by
  subst hp
  exact E.exists_isLocalization_primeCompl_of_henselian

/-- **The reduction step of the proof of Stacks Tag 05PG.** In the situation of Stacks Tag 05MK
with `A` henselian, `B` essentially of finite type over `A` and `M` finite over `B`, there are a
finite type `A`-algebra `C`, a finite `C`-module `N` and a prime `q` of `C` over the maximal ideal
of `A`, such that `N` is zero or carries a complete dévissage over `A` at `q`, and such that the
flatness condition of Stacks Tag 05ML for `(B, M)` over a local `A`-algebra `R` is flatness of
the base change of `N` at the primes of `C ⊗[A] R` above `q` and the closed point of `R`.

`B = (C₀)_{q₀}` and `M = (N₀)_{q₀}` for a finite type `C₀` and a finite `N₀`; Stacks Tag 05I1
gives an elementary étale localization `(R', S')` of `A → C₀` with a complete dévissage of the
base change of `N₀`; `A` henselian makes `A` the localization of `R'` at its distinguished prime,
and the dévissage localized there is a dévissage over `A` of `C = S'_{p'}`; finally `C₀ → C` is
flat, so the flatness condition is unchanged (Stacks Tag 05P5). -/
theorem Module.FlatAtPointSituation.exists_devissage_isFlatAtPrimesAbove
    (S : FlatAtPointSituation.{u, v, w}) [HenselianLocalRing S.A]
    [Algebra.EssFiniteType S.A S.B] [Module.Finite S.B S.M] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra S.A C) (_ : Algebra.FiniteType S.A C)
      (N : Type u) (_ : AddCommGroup N) (_ : Module C N) (_ : Module.Finite C N)
      (q : Ideal C) (_ : q.IsPrime),
      q.comap (algebraMap S.A C) = maximalIdeal S.A ∧
      (Subsingleton N ∨ ∃ D : CompleteDevissage S.A C N (maximalIdeal S.A),
        Nonempty (D.Points q)) ∧
      ∀ (R : Type x) [CommRing R] [IsLocalRing R] [Algebra S.A R]
        [IsLocalHom (algebraMap S.A R)], S.ConditionOn R ↔ IsFlatAtPrimesAbove S.A C q N R := by
  obtain ⟨C₀, _, _, _, _, _, _⟩ :=
    Algebra.EssFiniteType.exists_finiteType_isLocalization_atPrime S.A S.B
  set q₀ := (maximalIdeal S.B).comap (algebraMap C₀ S.B) with hq₀def
  let : Module C₀ S.M := Module.compHom S.M (algebraMap C₀ S.B)
  have : IsScalarTower C₀ S.B S.M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨N₀, _, _, _, g₀, _⟩ := Module.exists_finite_isLocalizedModule (B := S.B) q₀.primeCompl S.M
  have hq₀ : q₀.comap (algebraMap S.A C₀) = maximalIdeal S.A := by
    rw [hq₀def, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsLocalRing.maximalIdeal_comap]
  obtain ⟨E, hFT, ⟨D'⟩⟩ :=
    Module.exists_elementaryEtaleLocalization_completeDevissageAt S.A C₀ N₀ q₀
  let := hFT
  obtain ⟨σ, -, hσloc⟩ := E.exists_isLocalization_of_henselian_of_eq hq₀
  set r := E.q'.under E.R'
  have hr : r = E.p' := E.q'_liesOver_p'.symm
  let : Algebra E.R' S.A := σ.toRingHom.toAlgebra
  have hpc : r.primeCompl = E.p'.primeCompl := Submonoid.ext fun y => by
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hr]
  have : IsLocalization r.primeCompl S.A := by rwa [hpc]
  let L := Localization r.primeCompl
  let eRa := IsLocalization.algEquiv r.primeCompl L S.A
  let eR : L ≃+* S.A := eRa.toRingEquiv
  have heR : ∀ y : E.R', eR (algebraMap E.R' L y) = σ y := fun y => eRa.commutes y
  let C := Localization (Algebra.algebraMapSubmonoid E.S' r.primeCompl)
  let N := LocalizedModule (Algebra.algebraMapSubmonoid E.S' r.primeCompl)
    (TensorProduct C₀ E.S' N₀)
  let algAC : Algebra S.A C := ((algebraMap C₀ C).comp (algebraMap S.A C₀)).toAlgebra
  have : IsScalarTower S.A C₀ C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halg : ∀ x : L, algebraMap S.A C (eR x) = algebraMap L C x := by
    have key : (algebraMap S.A C).comp eR.toRingHom = algebraMap L C := by
      refine IsLocalization.ringHom_ext r.primeCompl (RingHom.ext fun y => ?_)
      have hLy : algebraMap E.R' L (algebraMap S.A E.R' (σ y)) = algebraMap E.R' L y :=
        eR.injective (by rw [heR, heR, σ.commutes]; rfl)
      have hcomm := congrArg (fun φ => φ (σ y)) E.commutes
      simp only [RingHom.comp_apply] at hcomm
      calc ((algebraMap S.A C).comp eR.toRingHom).comp (algebraMap E.R' L) y
          = algebraMap C₀ C (algebraMap S.A C₀ (σ y)) := by
            show algebraMap S.A C (eR (algebraMap E.R' L y)) = _
            rw [heR]
            rfl
        _ = algebraMap E.S' C (algebraMap E.R' E.S' (algebraMap S.A E.R' (σ y))) := by
            rw [IsScalarTower.algebraMap_apply C₀ E.S' C, hcomm]
        _ = algebraMap L C (algebraMap E.R' L (algebraMap S.A E.R' (σ y))) := by
            rw [← IsScalarTower.algebraMap_apply E.R' E.S' C,
              IsScalarTower.algebraMap_apply E.R' L C]
        _ = (algebraMap L C).comp (algebraMap E.R' L) y := by
            rw [hLy]
            rfl
    exact RingHom.congr_fun key
  have hFTA : Algebra.FiniteType S.A C := .of_ringEquiv eR (RingEquiv.refl C) halg
  let q : Ideal C := E.q'.map (algebraMap E.S' C)
  have hqd := IsLocalization.disjoint_algebraMapSubmonoid_primeCompl (r := r) (p := E.q') rfl
  have hqprime : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ C _ inferInstance hqd
  have hqS' : q.comap (algebraMap E.S' C) = E.q' :=
    IsLocalization.under_map_of_isPrime_disjoint _ C inferInstance hqd
  have hqC₀ : q.comap (algebraMap C₀ C) = q₀ := by
    rw [IsScalarTower.algebraMap_eq C₀ E.S' C, ← Ideal.comap_comap, hqS']
    exact E.q'_liesOver_q.symm
  have hqA : q.comap (algebraMap S.A C) = maximalIdeal S.A := by
    rw [IsScalarTower.algebraMap_eq S.A C₀ C, ← Ideal.comap_comap, hqC₀, hq₀]
  refine ⟨C, inferInstance, algAC, hFTA, N, inferInstance, inferInstance, inferInstance, q,
    hqprime, hqA, ?_, ?_⟩
  · cases D' with
    | empty hN =>
      exact .inl (inferInstanceAs (Subsingleton (LocalizedModule
        (Algebra.algebraMapSubmonoid E.S' r.primeCompl) (TensorProduct C₀ E.S' N₀))))
    | nonempty E' =>
      right
      have hmax :
          Ideal.map (algebraMap E.R' L) r = Ideal.comap eR.toRingHom (maximalIdeal S.A) := by
        rw [Localization.AtPrime.map_eq_maximalIdeal]
        exact (IsLocalRing.eq_maximalIdeal
          (Ideal.comap_isMaximal_of_surjective _ eR.surjective)).symm
      exact ⟨E'.toCompleteDevissage.localizeAtPrime.ofRingEquiv eR (RingEquiv.refl C)
        (AddEquiv.refl N) halg (fun _ _ => rfl) hmax,
        ⟨E'.points.localizeAtPrime.ofRingEquiv eR (RingEquiv.refl C) (AddEquiv.refl N) halg
          (fun _ _ => rfl) hmax (by ext; exact Iff.rfl)⟩⟩
  · intro R _ _ _ _
    have hQ : IsFlatAtPrimesAbove S.A C₀ q₀ N₀ R ↔
        IsFlatAtPrimesAbove S.A C₀ (q.comap (algebraMap C₀ C)) N₀ R := by
      rw [hqC₀]
    refine (FlatAtPointSituation.conditionOn_iff_isFlatAtPrimesAbove q₀ g₀ R).trans
      (hQ.trans ?_)
    exact isFlatAtPrimesAbove_iff_of_flat q hqA
      (((LocalizedModule.mkLinearMap _ (TensorProduct C₀ E.S' N₀)).restrictScalars C₀).comp
        (TensorProduct.mk C₀ E.S' N₀ 1))
      ((TensorProduct.isBaseChange C₀ N₀ E.S').comp
        (IsLocalizedModule.isBaseChange (Algebra.algebraMapSubmonoid E.S' r.primeCompl) C _)) R

end
