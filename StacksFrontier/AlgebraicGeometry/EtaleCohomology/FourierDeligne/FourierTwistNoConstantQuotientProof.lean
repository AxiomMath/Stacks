module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTwistFieldChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantCurveHalf
public import StacksFrontier.AlgebraicGeometry.Size.AlgebraicExtension

/-!
# The Artin–Schreier half of the generic coinvariant vanishing

This file proves `Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput`: for a sheaf `M` on
a nonempty open `V ⊆ 𝔸¹_k`, locally constant with finite values, there is a nonempty open `U` of
the `t`-line such that at the geometric point `s` of every point of `U` the twisted sheaf
`t⁻¹ M ⊗ L_ψ(x s)` on `C_s` has no constant simple quotient.

Fix `Ω = \overline{k(t)}`, countable, so below every cutoff. A point `y` of an open `U` whose
geometric point `s_y` is bad (the twisted sheaf has a constant simple quotient) makes bad every
`Ω`-point `t ↦ σ` of the `t`-line with the same image prime `𝔭_y`: such a point factors through
`Spec κ(y) ⟶ U`, the embedding `κ(y) ⟶ Ω` extends to the algebraic closure of `κ(y)`, and badness
goes up along `Spec Ω ⟶ Spec \overline{κ(y)}`
(`Stacks.EtaleCohomology.not_hasNoConstantSimpleQuotient_specMap`). Only finitely many `σ ∈ Ω` are
bad (`Stacks.EtaleCohomology.finite_setOf_not_hasNoConstantSimpleQuotient`). Hence:

* the generic point is good: all the `t ↦ x^n`, `n ≥ 1`, `x` transcendental, have image prime
  `0`;
* the bad closed points are among the finitely many primes `ker(t ↦ σ) ≠ 0`, `σ` bad, and
  `U = Spec k[t]_f`, `f` a product of nonzero elements of them, avoids them all.

With the curve half this closes the input (L2) of the single-level argument for the
irreducibility of the Fourier transform in Laumon's proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
(`Stacks.EtaleCohomology.fourierGenericCoinvariantVanishingInput`).

## Main results

* `Stacks.EtaleCohomology.not_hasNoConstantSimpleQuotient_specMap`.
* `Stacks.EtaleCohomology.fourierTwistNoConstantQuotientInput`.
* `Stacks.EtaleCohomology.fourierGenericCoinvariantVanishingInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier
  Polynomial

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal hasSheafify_etaleModules_fourierKernel

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- **A bad point makes bad every point of an algebraically closed field over it**: if `y` is a
point of an open `U` of the `t`-line whose geometric point gives a twisted sheaf with a constant
simple quotient, so does every `ρ : k[t] → Ω`, `Ω` algebraically closed, with kernel the prime of
`y`: `Spec ρ` factors through `Spec κ(y) ⟶ U`, and `κ(y) ⟶ Ω` extends to an algebraic closure of
`κ(y)`. -/
theorem not_hasNoConstantSimpleQuotient_specMap {V : Scheme.{u}} (jV : V ⟶ Spec (.of k[X]))
    (M : EtaleModules.{u, 0} Λ V) {U : Scheme.{u}} (jU : U ⟶ Spec (.of k[X])) [IsOpenImmersion jU]
    (y : U) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (ρ : k[X] →+* Ω)
    (hρ : RingHom.ker ρ = (jU.base y).asIdeal)
    (h : ¬ HasNoConstantSimpleQuotient Λ (fourierTwistSheaf k Λ ψ B p₀ jV M
      ((GeometricPoint.ofPoint U y).hom ≫ jU))) :
    ¬ HasNoConstantSimpleQuotient Λ (fourierTwistSheaf k Λ ψ B p₀ jV M
      (Spec.map (CommRingCat.ofHom ρ))) := by
  let s := Spec.map (CommRingCat.ofHom ρ)
  have hs : ∀ z, s.base z = jU.base y := fun z => by
    refine PrimeSpectrum.ext ?_
    show Ideal.comap ρ z.asIdeal = _
    have := z.isPrime
    rw [Ideal.eq_bot_of_prime z.asIdeal, ← RingHom.ker_eq_comap_bot, hρ]
  let g := IsOpenImmersion.lift jU s (by rintro _ ⟨z, rfl⟩; exact ⟨y, (hs z).symm⟩)
  have hg : g ≫ jU = s := IsOpenImmersion.lift_fac _ _ _
  have hgy : ∀ z, g.base z = y := fun z => jU.isOpenEmbedding.injective
    (show jU.base (g.base z) = jU.base y by rw [← hs z, ← hg]; rfl)
  obtain ⟨⟨y', φ⟩, hφ⟩ : ∃ q, (Scheme.SpecToEquivOfField Ω U).symm q = g :=
    ⟨_, (Scheme.SpecToEquivOfField Ω U).symm_apply_apply g⟩
  have hy' : y' = y := by
    have h1 := hgy (default : Spec (.of Ω))
    rw [← hφ] at h1
    exact (Scheme.fromSpecResidueField_apply y' _).symm.trans h1
  subst hy'
  let : Algebra (U.residueField y') Ω := φ.hom.toAlgebra
  let τ : AlgebraicClosure (U.residueField y') →ₐ[U.residueField y'] Ω := IsAlgClosed.lift
  have : Surjective (Spec.map (CommRingCat.ofHom τ.toRingHom)) :=
    ⟨fun _ => ⟨(default : Spec (.of Ω)), Subsingleton.elim _ _⟩⟩
  have hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (GeometricPoint.ofPoint U y').hom ≫ jU =
      s := by
    rw [← hg, ← hφ]
    show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap (U.residueField y')
      (AlgebraicClosure (U.residueField y')))) ≫ U.fromSpecResidueField y') ≫ jU = _
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp]
    congr 3
    ext a
    exact τ.commutes a
  have h' := not_hasNoConstantSimpleQuotient_comp k Λ ψ B p₀ jV M
    ((GeometricPoint.ofPoint U y').hom ≫ jU) (Spec.map (CommRingCat.ofHom τ.toRingHom)) h
  have key : ∀ t (_ : t = s),
      ¬ HasNoConstantSimpleQuotient Λ (fourierTwistSheaf k Λ ψ B p₀ jV M t) →
      ¬ HasNoConstantSimpleQuotient Λ (fourierTwistSheaf k Λ ψ B p₀ jV M s) := by
    rintro t rfl ht
    exact ht
  exact key _ hτ h'

/-- **`\overline{k(t)}` is below every cutoff**: it is countable. -/
theorem schemeSizeBelow_spec_algebraicClosure_fractionRing :
    schemeSizeBelow B.cutoff (Spec (.of (AlgebraicClosure (FractionRing k[X])))) := by
  refine (schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).2 ?_
  have h1 : Cardinal.mk k[X] ≤ Cardinal.aleph0 :=
    Polynomial.cardinalMk_le_max.trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  have : Countable k[X] := Cardinal.mk_le_aleph0_iff.1 h1
  have : Countable (FractionRing k[X]) :=
    (IsLocalization.mk'_surjective (nonZeroDivisors k[X]) (S := FractionRing k[X])).countable
  exact ((Cardinal.mk_le_max_of_isAlgebraic (FractionRing k[X])
    (AlgebraicClosure (FractionRing k[X]))).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl)).trans_lt B.aleph0_lt_cutoff

/-- Over an algebraically closed field `Ω`, every nonzero prime of `K[X]` is the kernel of an
evaluation `K[X] → Ω`. -/
theorem exists_ker_eval₂RingHom_eq_of_ne_bot {K Ω : Type*} [Field K] [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] (p : Ideal K[X]) (hp : p.IsPrime) (hp0 : p ≠ ⊥) :
    ∃ σ : Ω, RingHom.ker (eval₂RingHom (algebraMap K Ω) σ) = p := by
  obtain ⟨f₀, hf₀⟩ := (IsPrincipalIdealRing.principal p).principal
  have hp' : p = Ideal.span {f₀} := hf₀
  have hf0 : f₀ ≠ 0 := fun h => hp0 (by rw [hp', h, Ideal.span_singleton_eq_bot])
  have hunit : ¬ IsUnit f₀ := fun hu => hp.ne_top (by rwa [hp', Ideal.span_singleton_eq_top])
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_aeval_eq_zero Ω f₀
    (degree_pos_of_ne_zero_of_nonunit hf0 hunit).ne'
  refine ⟨σ, ?_⟩
  have : p.IsMaximal := IsPrime.to_maximal_ideal hp0
  refine (Ideal.IsMaximal.eq_of_le this (RingHom.ker_ne_top _) ?_).symm
  rw [hp', Ideal.span_le, Set.singleton_subset_iff]
  show eval₂ (algebraMap K Ω) σ f₀ = 0
  rwa [← aeval_def]

/-- `K[X]` embeds in the algebraic closure of its fraction field. -/
theorem injective_algebraMap_algebraicClosure_fractionRing (K : Type*) [Field K] :
    Function.Injective (algebraMap K[X] (AlgebraicClosure (FractionRing K[X]))) := by
  rw [IsScalarTower.algebraMap_eq K[X] (FractionRing K[X]) (AlgebraicClosure (FractionRing K[X]))]
  exact (algebraMap (FractionRing K[X]) _).injective.comp
    (IsFractionRing.injective K[X] (FractionRing K[X]))

/-- Evaluation `K[X] → \overline{K(X)}` at `X ^ (n + 1)` is injective. -/
theorem ker_eval₂RingHom_algebraMap_X_pow_eq_bot (K : Type*) [Field K] (n : ℕ) :
    RingHom.ker (eval₂RingHom (algebraMap K (AlgebraicClosure (FractionRing K[X])))
      (algebraMap K[X] (AlgebraicClosure (FractionRing K[X])) (Polynomial.X ^ (n + 1)))) = ⊥ := by
  let Ωs := AlgebraicClosure (FractionRing K[X])
  have heval : ∀ q g : K[X], eval₂ (algebraMap K Ωs) (algebraMap K[X] Ωs q) g =
      algebraMap K[X] Ωs (g.comp q) := by
    intro q g
    show eval₂RingHom (algebraMap K Ωs) (algebraMap K[X] Ωs q) g =
      ((algebraMap K[X] Ωs).comp (compRingHom q)) g
    congr 1
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [coe_eval₂RingHom, eval₂_C, RingHom.coe_comp, Function.comp_apply,
        coe_compRingHom_apply, C_comp]
      rw [IsScalarTower.algebraMap_apply K K[X] Ωs c, Polynomial.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
    · simp
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro g hg
  rw [coe_eval₂RingHom, heval] at hg
  exact (expand_eq_zero (Nat.succ_pos n)).1
    (injective_algebraMap_algebraicClosure_fractionRing K (hg.trans (map_zero _).symm))

/-- **The Artin–Schreier half of the generic coinvariant vanishing**: for a sheaf `M` on a
nonempty open `V ⊆ 𝔸¹_k`, locally constant with finite values, `∑ ψ = 0` and `#k` a unit in the
finite ring `Λ`, there is a nonempty open `U = Spec k[t]_f` of the `t`-line over every point of
which the twisted sheaf `t⁻¹ M ⊗ L_ψ(x s)` on `C_s` has no constant simple quotient. -/
theorem fourierTwistNoConstantQuotientInput : FourierTwistNoConstantQuotientInput.{u} := by
  intro k _ _ Λ _ _ ψ B p₀ hψ hq V jV _ _ M hM
  let Ωs := AlgebraicClosure (FractionRing k[X])
  let F := {σ : Ωs | ¬ HasNoConstantSimpleQuotient Λ (fourierTwistSheaf k Λ ψ B p₀ jV M
    (Spec.map (CommRingCat.ofHom (eval₂RingHom (algebraMap k Ωs) σ))))}
  have hF : F.Finite := finite_setOf_not_hasNoConstantSimpleQuotient k Λ ψ B p₀ hψ hq jV M hM Ωs
    (schemeSizeBelow_spec_algebraicClosure_fractionRing k B)
  classical
  let gσ : Ωs → k[X] := fun σ =>
    if h : RingHom.ker (eval₂RingHom (algebraMap k Ωs) σ) ≠ ⊥ then
      (Submodule.exists_mem_ne_zero_of_ne_bot h).choose else 1
  have hg0 : ∀ σ, gσ σ ≠ 0 := fun σ => by
    simp only [gσ]
    split_ifs with h
    exacts [(Submodule.exists_mem_ne_zero_of_ne_bot h).choose_spec.2, one_ne_zero]
  have hgmem : ∀ σ, RingHom.ker (eval₂RingHom (algebraMap k Ωs) σ) ≠ ⊥ →
      gσ σ ∈ RingHom.ker (eval₂RingHom (algebraMap k Ωs) σ) := fun σ h => by
    simpa only [gσ, dite_eq_left h] using (Submodule.exists_mem_ne_zero_of_ne_bot h).choose_spec.1
  let f := ∏ σ ∈ hF.toFinset, gσ σ
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hg0 σ
  let R := Localization.Away f
  let jU : Spec (.of R) ⟶ Spec (.of k[X]) := Spec.map (CommRingCat.ofHom (algebraMap k[X] R))
  have : Nontrivial R :=
    (IsLocalization.injective R (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)).nontrivial
  refine ⟨Spec (.of R), jU, inferInstance, inferInstance, fun y => ?_⟩
  by_contra hbad
  let p := (jU.base y).asIdeal
  have key : ∀ σ : Ωs, RingHom.ker (eval₂RingHom (algebraMap k Ωs) σ) = p → σ ∈ F :=
    fun σ hσ => not_hasNoConstantSimpleQuotient_specMap k Λ ψ B p₀ jV M jU y _ hσ hbad
  have hfp : f ∉ p := by
    show f ∉ Ideal.comap (algebraMap k[X] R) y.asIdeal
    rw [Ideal.mem_comap]
    exact fun h => y.isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit f))
  by_cases hp : p = ⊥
  · refine Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => algebraMap k[X] Ωs (Polynomial.X ^ (n + 1))) ?_
      (fun n => key _ ((ker_eval₂RingHom_algebraMap_X_pow_eq_bot k n).trans hp.symm)) hF
    intro a b hab
    have h := congrArg natDegree (injective_algebraMap_algebraicClosure_fractionRing k hab)
    simp only [natDegree_X_pow] at h
    omega
  · obtain ⟨σ, hσ⟩ := exists_ker_eval₂RingHom_eq_of_ne_bot (Ω := Ωs) p (jU.base y).isPrime hp
    apply hfp
    rw [← hσ]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem gσ (hF.mem_toFinset.2 (key σ hσ)))
      (hgmem σ (hσ ▸ hp))

/-- **(L2), the generic coinvariant vanishing of the Fourier transform**: the curve half
(`Stacks.EtaleCohomology.isZero_homology_two_derivedLowerShriek_affineLineOpen`) and the
Artin–Schreier half (`Stacks.EtaleCohomology.fourierTwistNoConstantQuotientInput`). -/
theorem fourierGenericCoinvariantVanishingInput : FourierGenericCoinvariantVanishingInput.{u} :=
  fourierGenericCoinvariantVanishingInput_of_twist fourierTwistNoConstantQuotientInput

end Stacks.EtaleCohomology

end
