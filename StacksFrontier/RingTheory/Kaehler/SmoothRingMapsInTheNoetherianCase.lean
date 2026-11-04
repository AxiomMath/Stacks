module

import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Smooth.Locus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smooth ring maps in the Noetherian case

Let `R` be a Noetherian ring, let `S` be an `R`-algebra of finite type and let `q` be a prime of
`S`. Then `R → S` is smooth at `q` if and only if the lifting property of formal smoothness holds
along a very restricted class of surjections: it suffices to test it on *small extensions* of
Artinian local rings, that is on surjections `B' → B` of local Artinian rings whose kernel has
length `1` as a `B'`-module, and even only on those small extensions along which the induced map
of residue fields `κ(q) → κ(𝔪)` is an isomorphism. Concretely, four conditions are equivalent:

1. `R → S` is smooth at `q`;
2. every surjection of local `R`-algebras `B' → B` with square-zero kernel, and every `R`-algebra
   map `S → B` pulling the maximal ideal of `B` back to `q`, admit a lift `S → B'`;
3. the same, with `B' → B` ranging only over small extensions;
4. the same, with `B' → B` ranging over small extensions along which the induced map of residue
   fields `κ(q) → κ(𝔪)` is an isomorphism.

## Main results

* `Algebra.isSmoothAt_tfae`: the equivalence of (1)–(4), as a `List.TFAE`.

## Implementation notes

Smoothness at `q` is `Algebra.IsSmoothAt R q`, that is `Algebra.FormallySmooth R S_q`, rather than
"there is `g ∉ q` with `R → S_g` smooth". The two agree because `R` is Noetherian and
`R → S` of finite type, hence of finite presentation, and Mathlib carries the equivalence for
finitely presented algebras in `Algebra.IsSmoothAt.exists_notMem_smooth`.

A square-zero extension is presented as a surjective `R`-algebra map `f : B' →ₐ[R] B` with
`ker f ^ 2 = ⊥`, rather than as `B' → B' ⧸ I` with `I ^ 2 = ⊥` in the manner of
`Algebra.FormallySmooth.iff_comp_surjective`, so that the target of `S → B` is a ring carrying
`IsLocalRing` as a hypothesis: Mathlib has no instance making `B' ⧸ I` a local ring, and the
maximal ideal `𝔪` of `B` is part of the data. The two forms are interchangeable along
`Ideal.quotientKerAlgEquivOfSurjective`.

"`ker (B' → B)` has length `1` as a `B'`-module" is `IsSimpleModule B' (ker f)`, which is
`Module.length B' (ker f) = 1` by `Module.length_eq_one_iff`. Condition (3) therefore does not
repeat `ker f ^ 2 = ⊥`: a simple `B'`-module is killed by the maximal ideal `𝔪'` of `B'`, and
`ker f ⊆ 𝔪'`, so `(ker f)² ⊆ 𝔪' · ker f = 0`.

The residue field isomorphism of (4) is surjectivity of the canonical map
`Ideal.ResidueField.mapₐ q (maximalIdeal B) g hq.symm : κ(q) →ₐ[R] κ(𝔪)` attached to the equality
`q = g⁻¹(𝔪)` that the condition already carries; surjectivity is the whole of "isomorphism", a
ring map between fields being injective. Here `κ(q)` is the residue field of `S_q` and not of `S`:
surjectivity of the composite `S → B → κ(𝔪)` is strictly stronger, and strong enough to force `q`
maximal, that composite having kernel `g⁻¹(𝔪) = q` and hence image the field `S/q`. What is true
is that the image of `κ(q)` in `κ(𝔪)` is the *fraction field* of the image of `S/q`, and that
image need not be all of it — for `S = ℤ`, `q = (0)`, `B = ℚ` the map `κ(q) = ℚ → ℚ = κ(𝔪)` is an
isomorphism while `ℤ → ℚ` is not onto. Read on `S_q` the class of test objects in (4) is nonempty
at every prime, maximal or not: the small extension `κ(q)[ε]/(ε²) → κ(q)` induces the identity of
`κ(q)`. Read on `S` it would be empty at every non-maximal prime, and the equivalence false there.

The auxiliary rings `B'`, `B` range over `Type max u v` for `R : Type u` and `S : Type v`, the
universe in which `Algebra.FormallySmooth.iff_comp_surjective` states the lifting property of
formal smoothness; as there, this costs no generality, every witness being transportable along a
`ULift` equivalence. No prime `𝔭 ⊂ R` under `q` is a hypothesis: none of (1)–(4) mentions it,
and it is determined by `q` as `q.comap (algebraMap R S)`.

For the implication (4) ⇒ (1), `S_q` is presented as a quotient of the local ring
`P = R[x_1, …, x_n]_{q'}`, formally smooth over `R`, with `q'` the prime of the polynomial ring
under `q`. The Jacobian criterion for local algebras,
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`, reduces smoothness
at `q` to injectivity of the single map of `κ(q)`-vector spaces `κ(q) ⊗_P J → κ(q) ⊗_P Ω[P⁄R]`,
where `J = ker (P → S_q)`. That injectivity is proved by duality: a functional separating a
nonzero element of `κ(q) ⊗_P J` restricts to a `P`-linear `u : J → κ(q)`, functionals on
`κ(q) ⊗_P Ω[P⁄R]` are `R`-derivations `P → κ(q)`, and so it suffices to extend every such `u` to a
derivation, which one small extension built from `u` and Artin–Rees provides.

## References

* [StacksProject 02HT](https://stacks.math.columbia.edu/tag/02HT); small extensions are
  [Tag 02HS](https://stacks.math.columbia.edu/tag/02HS) and smoothness at a prime is
  [Tag 00TB](https://stacks.math.columbia.edu/tag/00TB).
* [StacksProject 00IN](https://stacks.math.columbia.edu/tag/00IN), Artin–Rees, which is
  `Ideal.exists_pow_inf_eq_pow_smul`.
-/

@[expose] public section

universe u v

open IsLocalRing

/-- Over a local ring, a proper ideal that is simple as a module has square zero. -/
public theorem Ideal.sq_eq_bot_of_isSimpleModule {A : Type*} [CommRing A] [IsLocalRing A]
    {I : Ideal A} (hI : I ≠ ⊤) (hs : IsSimpleModule A I) : I ^ 2 = ⊥ := by
  have hle : I ≤ Module.annihilator A I :=
    IsLocalRing.eq_maximalIdeal hs.annihilator_isMaximal ▸ IsLocalRing.le_maximalIdeal hI
  rw [pow_two, ← le_bot_iff]
  refine Ideal.mul_le.2 fun r hr s hs' => ?_
  simpa using congrArg Subtype.val (Module.mem_annihilator.1 (hle hr) ⟨s, hs'⟩)

/-- The maximal ideal of a local ring is the contraction of the maximal ideal of a local ring it
surjects onto. -/
private theorem IsLocalRing.maximalIdeal_comap_of_surjective {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B) (hf : Function.Surjective f) :
    (maximalIdeal B).comap f = maximalIdeal A :=
  have := hf.isLocalHom f
  IsLocalRing.maximalIdeal_comap f

/-- A proper quotient of a local ring is a local ring. -/
theorem isLocalRing_quotient {P : Type*} [CommRing P] [IsLocalRing P] {b : Ideal P}
    (hb : b ≠ ⊤) : IsLocalRing (P ⧸ b) :=
  have : Nontrivial (P ⧸ b) := Submodule.Quotient.nontrivial_iff.mpr hb
  .of_surjective' _ Ideal.Quotient.mk_surjective

/-- A proper quotient of a Noetherian local ring by an ideal containing a power of the maximal
ideal is an Artinian local ring. -/
private theorem isArtinianRing_quotient {P : Type*} [CommRing P] [IsLocalRing P]
    [IsNoetherianRing P] {b : Ideal P} (hbt : b ≠ ⊤) {N : ℕ} (hb : maximalIdeal P ^ N ≤ b) :
    IsArtinianRing (P ⧸ b) := by
  have := isLocalRing_quotient hbt
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨N, le_bot_iff.mp ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← Ideal.map_pow,
    Ideal.map_le_iff_le_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact hb

/-- **Artin–Rees**, in the form that makes reduction injective on a quotient of ideals: if
`a ≤ J` are ideals of a Noetherian ring with `I * J ≤ a`, then `a ⊔ I ^ N` meets `J` in exactly
`a` for some `N > 0`. -/
private theorem Ideal.exists_inf_sup_pow_eq {P : Type*} [CommRing P] [IsNoetherianRing P]
    {I a J : Ideal P} (haJ : a ≤ J) (h : I * J ≤ a) :
    ∃ N : ℕ, 0 < N ∧ J ⊓ (a ⊔ I ^ N) = a := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (J : Submodule P P)
  have key : ∀ I : Ideal P, I • (⊤ : Submodule P P) = I := fun I => by simp
  have h₁ := hc (c + 1) (by omega)
  rw [key, key, Nat.add_sub_cancel_left, pow_one] at h₁
  refine ⟨c + 1, Nat.succ_pos _, ?_⟩
  rw [inf_comm, sup_inf_assoc_of_le _ haJ, sup_eq_left]
  refine le_trans ?_ h
  rw [show (I ^ (c + 1) ⊓ J : Submodule P P) = _ from h₁, ← Ideal.smul_eq_mul]
  exact Submodule.smul_mono le_rfl inf_le_right

/-- Two surjections out of a module with the same kernel differ by an isomorphism. -/
private theorem exists_linearEquiv_of_ker_eq {A M N K : Type*} [Ring A] [AddCommGroup M]
    [AddCommGroup N] [AddCommGroup K] [Module A M] [Module A N] [Module A K] {ψ : M →ₗ[A] N}
    (hψ : Function.Surjective ψ) {u : M →ₗ[A] K} (hu : Function.Surjective u)
    (hker : LinearMap.ker ψ = LinearMap.ker u) : ∃ w : N ≃ₗ[A] K, ∀ x, w (ψ x) = u x := by
  refine ⟨(LinearMap.quotKerEquivOfSurjective ψ hψ).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    LinearMap.quotKerEquivOfSurjective u hu, fun x => ?_⟩
  simp [LinearMap.quotKerEquivOfSurjective_symm_apply]

/-- Let `F : P ⧸ b → P ⧸ c` be a ring map induced by the identity of `P`, and let `J` be an ideal
with `J ≤ c ≤ J ⊔ b`. Then reduction modulo `b` carries `J` `P`-linearly onto `ker F`. -/
private theorem exists_surjective_linearMap_ker {P : Type*} [CommRing P] {b c J : Ideal P}
    (F : (P ⧸ b) →+* (P ⧸ c)) (hF : ∀ p : P, F (Ideal.Quotient.mk b p) = Ideal.Quotient.mk c p)
    (hJc : J ≤ c) (hc : c ≤ J ⊔ b) :
    ∃ ψ : J →ₗ[P] RingHom.ker F, Function.Surjective ψ ∧
      ∀ x : J, (ψ x : P ⧸ b) = Ideal.Quotient.mk b (x : P) := by
  have hmem : ∀ x : J, Ideal.Quotient.mk b (x : P) ∈ RingHom.ker F := fun x => by
    rw [RingHom.mem_ker, hF, Ideal.Quotient.eq_zero_iff_mem]
    exact hJc x.2
  refine ⟨{ toFun := fun x => ⟨_, hmem x⟩
            map_add' := fun x y => by ext; simp
            map_smul' := fun r x => by ext; simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] },
    fun y => ?_, fun _ => rfl⟩
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (y : P ⧸ b)
  have hpc : p ∈ c := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hF, hp]
    exact y.2
  obtain ⟨j, hj, z, hz, hjz⟩ := Submodule.mem_sup.mp (hc hpc)
  refine ⟨⟨j, hj⟩, Subtype.ext ?_⟩
  show Ideal.Quotient.mk b j = (y : P ⧸ b)
  rw [← hp, ← hjz, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simpa using neg_mem hz

/-- A surjection of `R`-algebras `P → A` whose kernel lies in an ideal `c` of `P` induces a
surjection `A → P ⧸ c`. -/
private theorem exists_algHom_quotient_of_ker_le {R P A : Type*} [CommRing R] [CommRing P]
    [CommRing A] [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
    (hsurj : Function.Surjective (algebraMap P A)) {c : Ideal P}
    (hc : RingHom.ker (algebraMap P A) ≤ c) :
    ∃ π : A →ₐ[R] P ⧸ c, Function.Surjective π ∧
      ∀ p : P, π (algebraMap P A p) = Ideal.Quotient.mk c p := by
  have hker : ∀ p ∈ RingHom.ker (IsScalarTower.toAlgHom R P A : P →ₐ[R] A),
      Ideal.Quotient.mkₐ R c p = 0 := fun p hp => Ideal.Quotient.eq_zero_iff_mem.2 (hc hp)
  obtain ⟨π, hπ⟩ : ∃ π : A →ₐ[R] P ⧸ c, ∀ p : P, π (algebraMap P A p) = Ideal.Quotient.mk c p := by
    refine ⟨(Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ R c) hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := (IsScalarTower.toAlgHom R P A : P →ₐ[R] A)) hsurj).symm.toAlgHom, fun p => ?_⟩
    have hsymm : (Ideal.quotientKerAlgEquivOfSurjective
        (f := (IsScalarTower.toAlgHom R P A : P →ₐ[R] A)) hsurj).symm (algebraMap P A p) =
        Ideal.Quotient.mk _ p := (AlgEquiv.symm_apply_eq _).2 rfl
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hsymm]
    rfl
  exact ⟨π, fun y => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨algebraMap P A p, hπ p⟩, hπ⟩

/-- Two `R`-algebra maps from `P` to `C` that differ inside a square-zero ideal `I` of `C` differ
by an `R`-derivation `P → I`, where `I` is a `P`-module through `algebraMap P C`. -/
private def derivationOfSubOfSqZero {R P C : Type*} [CommRing R] [CommRing P] [CommRing C]
    [Algebra R P] [Algebra R C] [Algebra P C] [IsScalarTower R P C] {I : Ideal C}
    (hI : I ^ 2 = ⊥) (β : P →ₐ[R] C) (hβ : ∀ p : P, algebraMap P C p - β p ∈ I) :
    Derivation R P I where
  toFun p := ⟨algebraMap P C p - β p, hβ p⟩
  map_add' x y := by ext; simp only [map_add, AddMemClass.mk_add_mk]; ring
  map_smul' r x := by
    ext
    simp only [Algebra.smul_def, map_mul, AlgHom.commutes, RingHom.id_apply,
      SetLike.val_smul_of_tower, IsScalarTower.algebraMap_apply R P C]
    ring
  map_one_eq_zero' := by ext; simp
  leibniz' x y := by
    ext
    have h₂ : (algebraMap P C x - β x) * (algebraMap P C y - β y) = 0 := by
      have := Ideal.mul_mem_mul (hβ x) (hβ y)
      rwa [← pow_two, hI, Ideal.mem_bot] at this
    simp only [AddMemClass.coe_add, SetLike.val_smul_of_tower, Algebra.smul_def,
      LinearMap.coe_mk, AddHom.coe_mk, map_mul]
    linear_combination -h₂

private lemma derivationOfSubOfSqZero_apply {R P C : Type*} [CommRing R] [CommRing P] [CommRing C]
    [Algebra R P] [Algebra R C] [Algebra P C] [IsScalarTower R P C] {I : Ideal C}
    (hI : I ^ 2 = ⊥) (β : P →ₐ[R] C) (hβ : ∀ p : P, algebraMap P C p - β p ∈ I) (p : P) :
    (derivationOfSubOfSqZero hI β hβ p : C) = algebraMap P C p - β p := rfl

/-- The lifting property for small extensions at `q`: every small extension `f : B' → B` of
Artinian local `R`-algebras — a surjection whose kernel is a simple `B'`-module — along which an
`R`-algebra map `g : S → B` contracting the maximal ideal of `B` to `q` is onto residue fields,
admits a lift `S → B'` of `g`. -/
private def LiftsAlongSmallExtensions (R : Type u) {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] : Prop :=
  ∀ (B' B : Type max u v) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    [IsArtinianRing B'] [IsArtinianRing B] [Algebra R B'] [Algebra R B]
    (f : B' →ₐ[R] B), Function.Surjective f →
    IsSimpleModule B' (RingHom.ker (f : B' →+* B)) →
    ∀ (g : S →ₐ[R] B) (hq : (maximalIdeal B).comap (g : S →+* B) = q),
      Function.Surjective (Ideal.ResidueField.mapₐ q (maximalIdeal B) g hq.symm) →
      ∃ g' : S →ₐ[R] B', f.comp g' = g

/-- Let `A` be a localization of `S` at `q`. If `LiftsAlongSmallExtensions R q` holds, then for
every small extension `f : B' → B` of Artinian local `R`-algebras, every surjection `π : A → B`
lifts to an `R`-algebra map `A → B'`. -/
private theorem exists_algHom_comp_eq_of_lift_smallExtension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {q : Ideal S} [q.IsPrime]
    (h : LiftsAlongSmallExtensions R q)
    {A : Type v} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [IsLocalRing A]
    [IsLocalization.AtPrime A q]
    {B' B : Type max u v} [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    [IsArtinianRing B'] [IsArtinianRing B] [Algebra R B'] [Algebra R B] (f : B' →ₐ[R] B)
    (hf : Function.Surjective f) (hs : IsSimpleModule B' (RingHom.ker (f : B' →+* B)))
    (π : A →ₐ[R] B) (hπ : Function.Surjective π) : ∃ t : A →ₐ[R] B', f.comp t = π := by
  set g : S →ₐ[R] B := π.comp (IsScalarTower.toAlgHom R S A)
  have hgring : (g : S →+* B) = (π : A →+* B).comp (algebraMap S A) := rfl
  have hq : (maximalIdeal B).comap (g : S →+* B) = q := by
    rw [hgring, ← Ideal.comap_comap, maximalIdeal_comap_of_surjective (π : A →+* B) hπ]
    simpa [Ideal.under_def] using IsLocalization.AtPrime.under_maximalIdeal (R := S) A q
  have hres : Function.Surjective (Ideal.ResidueField.mapₐ q (maximalIdeal B) g hq.symm) := by
    have hstalk : (g : S →+* B).SurjectiveOnStalks := by
      rw [hgring]
      exact (RingHom.surjectiveOnStalks_of_surjective hπ).comp
        (RingHom.surjectiveOnStalks_of_isLocalization (M := q.primeCompl) A)
    exact (hstalk.residueFieldMap_bijective q (maximalIdeal B) hq.symm).2
  obtain ⟨g', hg'⟩ := h B' B f hf hs g hq hres
  have := hf.isLocalHom (f : B' →+* B)
  have hunits : ∀ y : q.primeCompl, IsUnit (g' (y : S)) := fun y =>
    isUnit_of_map_unit (f : B' →+* B) _ <| by
      rw [RingHom.coe_coe, ← AlgHom.comp_apply, hg']
      exact notMem_maximalIdeal.1 fun hy => y.2 (hq.le hy)
  refine ⟨IsLocalization.liftAlgHom (M := q.primeCompl) hunits, AlgHom.coe_ringHom_injective ?_⟩
  refine IsLocalization.ringHom_ext q.primeCompl (RingHom.ext fun s => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgHom.comp_apply]
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  exact DFunLike.congr_fun hg' s

/-- Let `A` be a localization of `S` at a prime `q`, presented as a quotient of a Noetherian local
`R`-algebra `P`, and write `k` for the residue field of `A`. If `LiftsAlongSmallExtensions R q`
holds, then every `P`-linear map `u : ker (P → A) → k` is the restriction of an `R`-derivation
`P → k`. -/
private theorem exists_derivation_restrict_eq_of_lift_smallExtension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {q : Ideal S} [q.IsPrime]
    (h : LiftsAlongSmallExtensions R q)
    {A : Type v} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [IsLocalRing A]
    [IsLocalization.AtPrime A q]
    {P : Type max u v} [CommRing P] [Algebra R P] [Algebra P A] [IsScalarTower R P A]
    [IsLocalRing P] [IsNoetherianRing P] (hsurj : Function.Surjective (algebraMap P A))
    (u : RingHom.ker (algebraMap P A) →ₗ[P] ResidueField A) :
    ∃ D : Derivation R P (ResidueField A), ∀ x : RingHom.ker (algebraMap P A), D x.1 = u x := by
  revert u
  set J : Ideal P := RingHom.ker (algebraMap P A)
  intro u
  have hPk : ∀ x : P, algebraMap P (ResidueField A) x = residue A (algebraMap P A x) := fun _ => rfl
  have : IsScalarTower R P (ResidueField A) := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hPk, ← IsScalarTower.algebraMap_apply R P A]; rfl
  have hkPsurj : Function.Surjective (algebraMap P (ResidueField A)) := fun y => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, rfl⟩
  have hksimple : IsSimpleModule P (ResidueField A) :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (S := ResidueField A) (M := ResidueField A) hkPsurj).2 inferInstance
  have hnk : ∀ x ∈ maximalIdeal P, algebraMap P (ResidueField A) x = 0 := fun x hx => by
    rw [hPk, residue_eq_zero_iff]
    exact (maximalIdeal_comap_of_surjective (algebraMap P A) hsurj).ge hx
  have hJn : J ≤ maximalIdeal P := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  by_cases hu : u = 0
  · exact ⟨0, fun x => by simp [hu]⟩
  have husurj : Function.Surjective u := by
    rw [← LinearMap.range_eq_top]
    exact (hksimple.eq_bot_or_eq_top _).resolve_left fun h₁ => hu (LinearMap.range_eq_bot.mp h₁)
  set a : Ideal P := Submodule.map J.subtype (LinearMap.ker u) with hadef
  have haJ : a ≤ J := Submodule.map_subtype_le _ _
  have ha : ∀ x : J, (x : P) ∈ a ↔ u x = 0 := fun x => by
    simp only [hadef, Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype]
    exact ⟨fun ⟨y, hy, hyx⟩ => Subtype.ext hyx ▸ hy, fun h₀ => ⟨x, h₀, rfl⟩⟩
  have hnJ : maximalIdeal P * J ≤ a := by
    refine Ideal.mul_le.2 fun r hr s hs => ?_
    have hmem : r * s ∈ J := Ideal.mul_mem_left _ _ hs
    refine (ha ⟨r * s, hmem⟩).2 ?_
    rw [show (⟨r * s, hmem⟩ : J) = r • (⟨s, hs⟩ : J) from by ext; simp, map_smul, Algebra.smul_def,
      hnk r hr, zero_mul]
  obtain ⟨N, hN₀, hinf⟩ := Ideal.exists_inf_sup_pow_eq haJ hnJ
  set b : Ideal P := a ⊔ maximalIdeal P ^ N with hbdef
  set c : Ideal P := J ⊔ maximalIdeal P ^ N with hcdef
  have hbc : b ≤ c := sup_le_sup_right haJ _
  have hct : c ≠ ⊤ := fun h₁ => (maximalIdeal.isMaximal P).ne_top <| top_le_iff.mp <|
    h₁ ▸ sup_le hJn (Ideal.pow_le_self hN₀.ne')
  have hbt : b ≠ ⊤ := fun h₁ => hct (top_le_iff.mp (h₁ ▸ hbc))
  have hJc : J ≤ c := le_sup_left.trans hcdef.ge
  have := isLocalRing_quotient hbt
  have := isLocalRing_quotient hct
  have := isArtinianRing_quotient hbt (le_sup_right.trans hbdef.ge)
  have := isArtinianRing_quotient hct (le_sup_right.trans hcdef.ge)
  have : IsScalarTower R P (P ⧸ b) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmksurjb : Function.Surjective (algebraMap P (P ⧸ b)) := Ideal.Quotient.mk_surjective
  set f : (P ⧸ b) →ₐ[R] (P ⧸ c) := Ideal.Quotient.factorₐ R hbc
  have hfmk : ∀ p : P,
    (f : (P ⧸ b) →+* (P ⧸ c)) (Ideal.Quotient.mk b p) = Ideal.Quotient.mk c p := fun _ => rfl
  have hfsurj : Function.Surjective f := Ideal.Quotient.factor_surjective hbc
  obtain ⟨ψ, hψsurj, hψcoe⟩ := exists_surjective_linearMap_ker (J := J)
    (f : (P ⧸ b) →+* (P ⧸ c)) hfmk hJc (hcdef.le.trans (sup_le le_sup_left
      (le_sup_of_le_right (le_sup_right.trans hbdef.ge))))
  have hkerψ : LinearMap.ker ψ = LinearMap.ker u := by
    ext x
    have hz : ψ x = 0 ↔ (x : P) ∈ b := by
      rw [← Subtype.coe_inj, ZeroMemClass.coe_zero, hψcoe, Ideal.Quotient.eq_zero_iff_mem]
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← ha x, hz]
    exact ⟨fun hx => hinf.le ⟨x.2, hx⟩, fun hx => le_sup_left.trans hbdef.ge hx⟩
  obtain ⟨w, hw⟩ := exists_linearEquiv_of_ker_eq hψsurj husurj hkerψ
  have hkerfsimple : IsSimpleModule (P ⧸ b) (RingHom.ker (f : (P ⧸ b) →+* (P ⧸ c))) :=
    (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
      (R := P) (S := P ⧸ b) hmksurjb).1 (IsSimpleModule.congr w)
  have hsq : RingHom.ker (f : (P ⧸ b) →+* (P ⧸ c)) ^ 2 = ⊥ :=
    Ideal.sq_eq_bot_of_isSimpleModule (RingHom.ker_ne_top _) hkerfsimple
  obtain ⟨π, hπsurj, hπ⟩ := exists_algHom_quotient_of_ker_le (R := R) hsurj (c := c) hJc
  obtain ⟨t, ht⟩ := exists_algHom_comp_eq_of_lift_smallExtension h f hfsurj hkerfsimple π hπsurj
  set β : P →ₐ[R] (P ⧸ b) := t.comp (IsScalarTower.toAlgHom R P A)
  have hβp : ∀ p : P, β p = t (algebraMap P A p) := fun _ => rfl
  have hβmem : ∀ p : P, algebraMap P (P ⧸ b) p - β p ∈
      RingHom.ker (f : (P ⧸ b) →+* (P ⧸ c)) := fun p => by
    rw [RingHom.mem_ker, RingHom.coe_coe, map_sub, hβp, ← AlgHom.comp_apply, ht, hπ,
      Ideal.Quotient.algebraMap_eq, sub_eq_zero]
    exact hfmk p
  refine ⟨w.compDer (derivationOfSubOfSqZero hsq β hβmem), fun x => ?_⟩
  have hδ : derivationOfSubOfSqZero hsq β hβmem (x : P) = ψ x := by
    ext
    rw [derivationOfSubOfSqZero_apply, hβp, RingHom.mem_ker.mp x.2, map_zero, sub_zero, hψcoe,
      Ideal.Quotient.algebraMap_eq]
  show w (derivationOfSubOfSqZero hsq β hβmem (x : P)) = u x
  rw [hδ, hw]

/-- With `P` a Noetherian local `R`-algebra surjecting onto a localization `A` of `S` at `q`, the
lifting property for small extensions makes the localized naive cotangent complex of the
presentation injective modulo `q`. -/
private theorem injective_cotangentComplexBaseChange_residueField_of_lift_smallExtension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime]
    {A : Type v} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [IsLocalRing A]
    [IsLocalization.AtPrime A q]
    {P : Type max u v} [CommRing P] [Algebra R P] [Algebra P A] [IsScalarTower R P A]
    [IsLocalRing P] [IsNoetherianRing P] (hsurj : Function.Surjective (algebraMap P A))
    (h : LiftsAlongSmallExtensions R q) :
    Function.Injective
      (KaehlerDifferential.cotangentComplexBaseChange R A P (ResidueField A)) := by
  refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx => ?_)
  rw [← Module.forall_dual_apply_eq_zero_iff (ResidueField A) x]
  intro v
  obtain ⟨D, hD⟩ := exists_derivation_restrict_eq_of_lift_smallExtension h hsurj
    ((v.restrictScalars P).comp
      (TensorProduct.mk P (ResidueField A) (RingHom.ker (algebraMap P A)) 1))
  have hv : ∀ z, v z = (LinearMap.liftBaseChange (ResidueField A) D.liftKaehlerDifferential)
      (KaehlerDifferential.cotangentComplexBaseChange R A P (ResidueField A) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
      have hb : D (b : P) = v (1 ⊗ₜ[P] b) := hD b
      rw [KaehlerDifferential.cotangentComplexBaseChange_tmul,
        KaehlerDifferential.kerToTensor_apply, map_smul, LinearMap.liftBaseChange_tmul, one_smul,
        Derivation.liftKaehlerDifferential_comp_D, hb, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']
  rw [hv x, hx, map_zero]

/-- If `LiftsAlongSmallExtensions R q` holds, then `R → S` is smooth at `q`. -/
@[ega "IV 17.14.2" "special case"]
private theorem isSmoothAt_of_lift_smallExtension_residueField
    {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] (h : LiftsAlongSmallExtensions R q) :
    Algebra.IsSmoothAt R q := by
  show Algebra.FormallySmooth R (Localization.AtPrime q)
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨ι, hι, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FiniteType R S)
  let M' := (q.primeCompl).comap f₀
  let P := Localization M'
  let fP : P →ₐ[R] Localization.AtPrime q := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R S (Localization.AtPrime q)).comp f₀) fun x ↦ by
    simpa using IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q)
      ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  have hfP : (RingHom.ker fP).FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective _ hf₀
    convert! this.map (algebraMap _ P)
    refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ by simp_all [fP])
    intro x hx
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M' x
    obtain ⟨a, ha, e⟩ : ∃ a ∈ q.primeCompl, a * f₀ x = 0 := by
      simpa [fP, IsLocalization.lift_mk', IsLocalization.map_eq_zero_iff q.primeCompl] using hx
    obtain ⟨a, rfl⟩ := hf₀ a
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨a, ha, by simpa⟩
  algebraize [fP.toRingHom]
  have : IsScalarTower R P (Localization.AtPrime q) := .of_algebraMap_eq' fP.comp_algebraMap.symm
  have : Algebra.FormallyEtale (MvPolynomial ι R) P := .of_isLocalization M'
  have : Algebra.FormallySmooth R P := .comp _ (MvPolynomial ι R) _
  have : Module.Free P Ω[P⁄R] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial ι R) P)
  have : Module.Finite P Ω[P⁄R] :=
    .of_surjective (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R
      (MvPolynomial ι R) P).toLinearMap (LinearEquiv.surjective _)
  have : (q.comap (f₀ : MvPolynomial ι R →+* S)).IsPrime := Ideal.comap_isPrime _ _
  have hM'eq : M' = (q.comap (f₀ : MvPolynomial ι R →+* S)).primeCompl := by
    ext x
    simp [M', Ideal.primeCompl]
  have : IsLocalization ((q.comap (f₀ : MvPolynomial ι R →+* S)).primeCompl) P := by
    rw [← hM'eq]; infer_instance
  have : IsLocalRing P := IsLocalization.AtPrime.isLocalRing (S := P)
    (P := q.comap (f₀ : MvPolynomial ι R →+* S))
  have : IsNoetherianRing P := IsLocalization.isNoetherianRing M' P inferInstance
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
    (P := P) hf₁ hfP]
  exact injective_cotangentComplexBaseChange_residueField_of_lift_smallExtension q hf₁ h

namespace Algebra

/-- Let `R` be a Noetherian ring, let `S` be an `R`-algebra of finite type and let `q` be a prime
of `S`. The following are equivalent:

1. `R → S` is smooth at `q`;
2. for every surjection `f : B' → B` of local `R`-algebras whose kernel has square zero and every
   `R`-algebra map `g : S → B` with `q` the contraction of the maximal ideal of `B`, there is an
   `R`-algebra map `g' : S → B'` with `f ∘ g' = g`;
3. the same, with `f` ranging over small extensions, that is, surjections of Artinian local rings
   whose kernel is a simple `B'`-module (equivalently, has length `1`);
4. the same, with `f` ranging over small extensions along which `g` additionally induces an
   isomorphism `κ(q) ≅ κ(𝔪)`, that is, along which the canonical map `κ(q) → κ(𝔪)` attached to
   `q = g⁻¹(𝔪)` is surjective. -/
@[stacks 02HT "Smoothness at `q` is `Algebra.IsSmoothAt`, the source's Definition 02HN by the
finite presentation of `S`. A small extension (Definition 02HS) is a surjection `f : B' →ₐ[R] B`
of Artinian local rings with `IsSimpleModule B' (ker f)`, and `κ(q) ≅ κ(𝔪)` is surjectivity of
`Ideal.ResidueField.mapₐ q (maximalIdeal B) g`, the canonical map out of the residue field of
`S_q` — not of `S → κ(𝔪)`, which would force `q` maximal. The source's prime `𝔭` under `q` is not
used. See the module docstring."]
theorem isSmoothAt_tfae {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] :
    List.TFAE
      [ Algebra.IsSmoothAt R q,
        ∀ (B' B : Type max u v) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
          [Algebra R B'] [Algebra R B] (f : B' →ₐ[R] B), Function.Surjective f →
          RingHom.ker (f : B' →+* B) ^ 2 = ⊥ →
          ∀ g : S →ₐ[R] B, (maximalIdeal B).comap (g : S →+* B) = q →
            ∃ g' : S →ₐ[R] B', f.comp g' = g,
        ∀ (B' B : Type max u v) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
          [IsArtinianRing B'] [IsArtinianRing B] [Algebra R B'] [Algebra R B]
          (f : B' →ₐ[R] B), Function.Surjective f →
          IsSimpleModule B' (RingHom.ker (f : B' →+* B)) →
          ∀ g : S →ₐ[R] B, (maximalIdeal B).comap (g : S →+* B) = q →
            ∃ g' : S →ₐ[R] B', f.comp g' = g,
        ∀ (B' B : Type max u v) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
          [IsArtinianRing B'] [IsArtinianRing B] [Algebra R B'] [Algebra R B]
          (f : B' →ₐ[R] B), Function.Surjective f →
          IsSimpleModule B' (RingHom.ker (f : B' →+* B)) →
          ∀ (g : S →ₐ[R] B) (hq : (maximalIdeal B).comap (g : S →+* B) = q),
            Function.Surjective (Ideal.ResidueField.mapₐ q (maximalIdeal B) g hq.symm) →
            ∃ g' : S →ₐ[R] B', f.comp g' = g ] := by
  tfae_have 1 → 2 := by
    intro h B' B _ _ _ _ _ _ f hf hker g hq
    have hunits : ∀ y : q.primeCompl, IsUnit (g (y : S)) :=
      fun y => IsLocalRing.notMem_maximalIdeal.1 fun hy => y.2 (le_of_eq hq hy)
    have hnil : IsNilpotent (RingHom.ker f) := ⟨2, by rwa [RingHom.ker_coe_toRingHom] at hker⟩
    refine ⟨(Algebra.FormallySmooth.liftOfSurjective
        (IsLocalization.liftAlgHom hunits) f hf hnil).comp
      (IsScalarTower.toAlgHom R S (Localization.AtPrime q)), ?_⟩
    ext x
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.FormallySmooth.liftOfSurjective_apply]
    exact IsLocalization.lift_eq _ _
  tfae_have 2 → 3 := fun h B' B _ _ _ _ _ _ _ _ f hf hs g hq =>
    h B' B f hf (Ideal.sq_eq_bot_of_isSimpleModule (RingHom.ker_ne_top _) hs) g hq
  tfae_have 3 → 4 := fun h B' B _ _ _ _ _ _ _ _ f hf hs g hq _ => h B' B f hf hs g hq
  tfae_have 4 → 1 := fun h => isSmoothAt_of_lift_smallExtension_residueField q h
  tfae_finish

end Algebra

end
