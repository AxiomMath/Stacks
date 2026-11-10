module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.StandardOpenBaseChange

/-!
# Finite presentation of the localized twists on a standard open

Let `A` be a graded ring with grading `𝒜` and let `f` be homogeneous of positive degree. The `t`-th
twist of `A`, localized in degree zero away from `f`, is the module of sections of the `t`-th
twisting sheaf over the standard open `D₊(f)`; inside the ordinary localization `A[1/f]` it is the
submodule `Stacks.ProjStandardOpenBaseChange.twistAway 𝒜 f d t`. This file transports *finite
presentation* of that module along a grading preserving ring isomorphism, and along the scalar
extension of a graded algebra.

## Main results

* `Module.FinitePresentation.of_addEquiv`: finite presentation transports along a ring
  isomorphism together with a compatible additive equivalence. This is the semilinear form of
  `Module.FinitePresentation.of_equiv`.
* `Stacks.ProjTwistFinitePresentation.finitePresentation_twistAway_of_ringEquiv`: finite
  presentation of a localized twist transports along a grading preserving ring isomorphism.
* `Stacks.ProjTwistFinitePresentation.finitePresentation_twistAway_baseChange`: finite
  presentation of a localized twist passes to a scalar extension, along the canonical
  isomorphisms of `Stacks.ProjStandardOpenBaseChange.standardOpenBaseChange`.

## References

* [Stacks Project, Tag 0D4D](https://stacks.math.columbia.edu/tag/0D4D)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 07Z2](https://stacks.math.columbia.edu/tag/07Z2)
-/

@[expose] public noncomputable section

open Algebra TensorProduct
open HomogeneousLocalization Stacks.ProjStandardOpenBaseChange

universe u v w x

/-- Finite presentation transports along a ring isomorphism with a compatible additive
equivalence. -/
theorem Module.FinitePresentation.of_addEquiv {R : Type u} {R' : Type v} {M : Type w}
    {M' : Type x} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R' M'] (σ : R ≃+* R') (e : M ≃+ M')
    (he : ∀ (r : R) (x : M), e (r • x) = σ r • e x) (h : Module.FinitePresentation R M) :
    Module.FinitePresentation R' M' := by
  have := h
  obtain ⟨n, m, p, q, hp, hpq⟩ := Module.FinitePresentation.exists_fin' R M
  let Λ : (Fin n → R) →ₛₗ[(σ : R →+* R')] (Fin n → R') :=
    { toFun := fun u i => σ (u i)
      map_add' := fun u v => by funext i; exact map_add σ (u i) (v i)
      map_smul' := fun r u => by funext i; exact map_mul σ r (u i) }
  have hΛsurj : Function.Surjective Λ := fun v => ⟨fun i => σ.symm (v i), by
    funext i; exact σ.apply_symm_apply (v i)⟩
  let ψ : (Fin n → R') →ₗ[R'] M' :=
    { toFun := fun v => e (p fun i => σ.symm (v i))
      map_add' := fun v v' => by
        rw [show (fun i => σ.symm ((v + v') i)) = (fun i => σ.symm (v i)) +
          (fun i => σ.symm (v' i)) from by
            funext i; exact map_add σ.symm (v i) (v' i)]
        simp only [map_add]
      map_smul' := fun r v => by
        simp only [RingHom.id_apply]
        rw [show (fun i => σ.symm ((r • v) i)) = σ.symm r • (fun i => σ.symm (v i)) from by
          funext i; exact map_mul σ.symm r (v i), map_smul, he, σ.apply_symm_apply] }
  have hψ : ∀ u : Fin n → R, ψ (Λ u) = e (p u) := by
    intro u
    change e (p fun i => σ.symm (σ (u i))) = _
    congr 2
    funext i
    exact σ.symm_apply_apply (u i)
  refine Module.finitePresentation_of_surjective ψ ?_ ?_
  · intro y
    obtain ⟨z, hz⟩ := e.surjective y
    obtain ⟨u, hu⟩ := hp z
    exact ⟨Λ u, by rw [hψ, hu, hz]⟩
  · have hker : LinearMap.ker ψ = Submodule.map Λ (LinearMap.range q) := by
      apply le_antisymm
      · intro v hv
        obtain ⟨u, hu⟩ := hΛsurj v
        have h0 : p u = 0 := by
          have : e (p u) = 0 := by rw [← hψ, hu]; exact hv
          simpa using (AddEquiv.map_eq_zero_iff e).mp this
        obtain ⟨c, hc⟩ := (hpq u).mp h0
        exact ⟨u, ⟨c, hc⟩, hu⟩
      · rw [Submodule.map_le_iff_le_comap]
        rintro u ⟨c, hc⟩
        have : p u = 0 := by rw [← hc]; exact hpq.apply_apply_eq_zero c
        simp only [Submodule.mem_comap, LinearMap.mem_ker, hψ, this, map_zero]
    rw [hker]
    exact (Submodule.fg_range q).map Λ

namespace Stacks.ProjTwistFinitePresentation

section RingEquiv

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ]

/-- The inverse of a grading preserving ring isomorphism preserves the grading. -/
private theorem symm_mem (φ : B ≃+* A) (hφ : ∀ (i : ℕ) (x : B), x ∈ ℬ i → φ x ∈ 𝒜 i)
    {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) : φ.symm a ∈ ℬ i := by
  classical
  have ha' : φ (φ.symm a) = a := φ.apply_symm_apply a
  set b : B := φ.symm a with hb
  have key : GradedRing.proj 𝒜 i a = φ ((DirectSum.decompose ℬ b i : B)) := by
    conv_lhs => rw [← ha', ← DirectSum.sum_support_decompose ℬ b]
    simp only [map_sum]
    refine (Finset.sum_eq_single i (fun j _ hj => ?_) (fun hi => ?_)).trans ?_
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne 𝒜 (hφ j _ (DirectSum.decompose ℬ b j).2) hj
    · rw [DFinsupp.notMem_support_iff.mp hi]
      simp
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_same 𝒜 (hφ i _ (DirectSum.decompose ℬ b i).2)
  rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 ha] at key
  have heq : (DirectSum.decompose ℬ b i : B) = b := φ.injective (key.symm.trans ha'.symm)
  exact heq ▸ (DirectSum.decompose ℬ b i).2

/-- The isomorphism of ordinary localizations at `g` and at its image induced by a ring
isomorphism. -/
private def locEquiv (φ : B ≃+* A) (g : B) :
    Localization (Submonoid.powers g) ≃+* Localization (Submonoid.powers (φ g)) :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers g)
    (T := Submonoid.powers (φ g)) (Localization (Submonoid.powers g))
    (Localization (Submonoid.powers (φ g))) φ (by simp)

private lemma locEquiv_mk (φ : B ≃+* A) (g x : B) (k : ℕ) :
    locEquiv φ g (Localization.mk x
        ⟨g ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers g) k⟩) =
      Localization.mk (φ x)
        ⟨φ g ^ k, Submonoid.pow_mem _ (Submonoid.mem_powers (φ g)) k⟩ := by
  rw [Localization.mk_eq_mk'_apply, Localization.mk_eq_mk'_apply]
  change IsLocalization.map (M := Submonoid.powers g) (T := Submonoid.powers (φ g))
      (Localization (Submonoid.powers (φ g))) (φ : B →+* A)
      (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩) _ = _
  rw [IsLocalization.map_mk']
  congr 1
  exact Subtype.ext (map_pow φ g k)


variable (φ : B ≃+* A) (hφ : ∀ (i : ℕ) (x : B), x ∈ ℬ i → φ x ∈ 𝒜 i)

/-- The graded ring homomorphism underlying a grading preserving ring isomorphism. -/
private def gradedHom : ℬ →+*ᵍ 𝒜 where
  __ := (φ : B →+* A)
  map_mem {i x} hx := hφ i x hx

variable {d : ℕ} {g : B} (hg : g ∈ ℬ d)

/-- The induced homomorphism of degree-zero localizations. -/
private def awayHom : Away ℬ g →+* Away 𝒜 (φ g) :=
  Away.map (gradedHom 𝒜 ℬ φ hφ) g

include hg in
private lemma awayHom_mk (n : ℕ) (y : B) (hy : y ∈ ℬ (n • d)) :
    awayHom 𝒜 ℬ φ hφ (Away.mk ℬ hg n y hy) =
      Away.mk 𝒜 (hφ d g hg) n (φ y) (hφ _ y hy) := by
  change Away.map (gradedHom 𝒜 ℬ φ hφ) g (Away.mk ℬ hg n y hy) = _
  rw [Away.map_mk]
  rfl

include hg in
private lemma val_awayHom (a : Away ℬ g) :
    (awayHom 𝒜 ℬ φ hφ a).val = locEquiv φ g a.val := by
  obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective ℬ hg a
  rw [awayHom_mk 𝒜 ℬ φ hφ hg, Away.val_mk, Away.val_mk, locEquiv_mk]

include hg in
private lemma awayHom_bijective : Function.Bijective (awayHom 𝒜 ℬ φ hφ (g := g)) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · refine HomogeneousLocalization.val_injective _ ((locEquiv φ g).injective ?_)
    rw [← val_awayHom 𝒜 ℬ φ hφ hg, ← val_awayHom 𝒜 ℬ φ hφ hg, hab]
  · obtain ⟨n, x, hx, rfl⟩ := Away.mk_surjective 𝒜 (hφ d g hg) a
    refine ⟨Away.mk ℬ hg n (φ.symm x) (symm_mem 𝒜 ℬ φ hφ hx), ?_⟩
    rw [awayHom_mk 𝒜 ℬ φ hφ hg]
    exact HomogeneousLocalization.val_injective _ (by
      rw [Away.val_mk, Away.val_mk, φ.apply_symm_apply])

/-- The isomorphism of degree-zero localizations induced by a grading preserving ring
isomorphism. -/
private def awayEquiv : Away ℬ g ≃+* Away 𝒜 (φ g) :=
  RingEquiv.ofBijective (awayHom 𝒜 ℬ φ hφ) (awayHom_bijective 𝒜 ℬ φ hφ hg)


/-- The semilinear map of ordinary localizations over the induced isomorphism of degree-zero
localizations. -/
private def locMap :
    Localization (Submonoid.powers g) →ₛₗ[(awayEquiv 𝒜 ℬ φ hφ hg : Away ℬ g →+* Away 𝒜 (φ g))]
      Localization (Submonoid.powers (φ g)) where
  toFun := locEquiv φ g
  map_add' := map_add _
  map_smul' a z := by
    change locEquiv φ g (a.val * z) = (awayHom 𝒜 ℬ φ hφ a).val * locEquiv φ g z
    rw [map_mul, val_awayHom 𝒜 ℬ φ hφ hg]

include hg in
private lemma locMap_apply (z : Localization (Submonoid.powers g)) :
    locMap 𝒜 ℬ φ hφ hg z = locEquiv φ g z := rfl

include hg in
/-- A grading preserving ring isomorphism carries the localized twist onto the localized
twist. -/
private lemma map_twistAway (t : ℤ) :
    Submodule.map (locMap 𝒜 ℬ φ hφ hg) (twistAway ℬ g d t) = twistAway 𝒜 (φ g) d t := by
  have : RingHomSurjective
      (awayEquiv 𝒜 ℬ φ hφ hg : Away ℬ g →+* Away 𝒜 (φ g)) :=
    ⟨(awayEquiv 𝒜 ℬ φ hφ hg).surjective⟩
  change Submodule.map (locMap 𝒜 ℬ φ hφ hg) (Submodule.span _ _) = _
  rw [Submodule.map_span]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro z ⟨w, ⟨k, j, y, hj, hy, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨k, j, φ y, hj, hφ j y hy, locEquiv_mk φ g y k⟩
  · rintro z ⟨k, j, x, hj, hx, rfl⟩
    refine Submodule.subset_span ⟨_, ⟨k, j, φ.symm x, hj, symm_mem 𝒜 ℬ φ hφ hx, rfl⟩, ?_⟩
    rw [locMap_apply 𝒜 ℬ φ hφ hg, locEquiv_mk, φ.apply_symm_apply]

include hφ hg in
private lemma mem_twistAway_locEquiv (t : ℤ) (z : Localization (Submonoid.powers g))
    (hz : z ∈ twistAway ℬ g d t) : locEquiv φ g z ∈ twistAway 𝒜 (φ g) d t :=
  (map_twistAway 𝒜 ℬ φ hφ hg t).le (Submodule.mem_map_of_mem hz)

include hφ hg in
private lemma mem_twistAway_locEquiv_symm (t : ℤ)
    (y : Localization (Submonoid.powers (φ g))) (hy : y ∈ twistAway 𝒜 (φ g) d t) :
    (locEquiv φ g).symm y ∈ twistAway ℬ g d t := by
  rw [← map_twistAway 𝒜 ℬ φ hφ hg t] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [locMap_apply 𝒜 ℬ φ hφ hg, (locEquiv φ g).symm_apply_apply]
  exact hz

/-- The additive identification of the two localized twists. -/
private def twistAddEquiv (t : ℤ) : twistAway ℬ g d t ≃+ twistAway 𝒜 (φ g) d t where
  toFun x := ⟨locEquiv φ g x.1, mem_twistAway_locEquiv 𝒜 ℬ φ hφ hg t x.1 x.2⟩
  invFun y := ⟨(locEquiv φ g).symm y.1, mem_twistAway_locEquiv_symm 𝒜 ℬ φ hφ hg t y.1 y.2⟩
  left_inv x := Subtype.ext ((locEquiv φ g).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((locEquiv φ g).apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add (locEquiv φ g) x.1 y.1)

include hg in
private lemma twistAddEquiv_smul (t : ℤ) (a : Away ℬ g) (x : twistAway ℬ g d t) :
    twistAddEquiv 𝒜 ℬ φ hφ hg t (a • x) =
      awayEquiv 𝒜 ℬ φ hφ hg a • twistAddEquiv 𝒜 ℬ φ hφ hg t x := by
  refine Subtype.ext ?_
  change locEquiv φ g (a.val * x.1) = (awayHom 𝒜 ℬ φ hφ a).val * locEquiv φ g x.1
  rw [map_mul, val_awayHom 𝒜 ℬ φ hφ hg]

include hφ hg in
/-- **Finite presentation of a localized twist transports along a grading preserving ring
isomorphism.**

If `φ : B ≃+* A` carries each graded piece of `ℬ` into the corresponding piece of `𝒜` and `g` is
homogeneous, then finite presentation of the localized twist `twistAway ℬ g d t` over `Away ℬ g`
gives finite presentation of `twistAway 𝒜 (φ g) d t` over `Away 𝒜 (φ g)`. -/
public theorem finitePresentation_twistAway_of_ringEquiv (t : ℤ)
    (h : Module.FinitePresentation (Away ℬ g) (twistAway ℬ g d t)) :
    Module.FinitePresentation (Away 𝒜 (φ g)) (twistAway 𝒜 (φ g) d t) :=
  Module.FinitePresentation.of_addEquiv (awayEquiv 𝒜 ℬ φ hφ hg)
    (twistAddEquiv 𝒜 ℬ φ hφ hg t) (twistAddEquiv_smul 𝒜 ℬ φ hφ hg t) h

end RingEquiv

section BaseChange

variable {R₀ R A₀ : Type u} [CommRing R₀] [CommRing R] [CommRing A₀]
  [Algebra R₀ R] [Algebra R₀ A₀]
  (𝒜₀ : ℕ → Submodule R₀ A₀) [GradedAlgebra 𝒜₀] (x₀ : A₀) (d : ℕ)

/-- The degree-zero localization of the base-changed graded ring. -/
private abbrev SBC : Type u :=
  Away (fun i => (𝒜₀ i).baseChange R) (gradedBaseChangeMap (R' := R) 𝒜₀ x₀)

/-- The ring homomorphism from the model's degree-zero localization to its base change. -/
private abbrev awayBC : Away 𝒜₀ x₀ →+* SBC (R := R) 𝒜₀ x₀ :=
  Away.map (gradedBaseChangeMap (R' := R) 𝒜₀) x₀

/-- The base change of a localized twist of the model. -/
private abbrev twistBC (t : ℤ) :
    Submodule (SBC (R := R) 𝒜₀ x₀)
      (Localization (Submonoid.powers (gradedBaseChangeMap (R' := R) 𝒜₀ x₀))) :=
  twistAway (fun i => (𝒜₀ i).baseChange R) (gradedBaseChangeMap (R' := R) 𝒜₀ x₀) d t

variable (bc : StandardOpenBaseChange (R' := R) 𝒜₀ x₀ d)

private lemma ringEquiv_tmul_one (r : R) :
    bc.ringEquiv (r ⊗ₜ[R₀] (1 : Away 𝒜₀ x₀)) = algebraMap R (SBC (R := R) 𝒜₀ x₀) r := by
  rw [bc.ringEquiv_tmul]; simp

private lemma ringEquiv_one_tmul (a : Away 𝒜₀ x₀) :
    bc.ringEquiv ((1 : R) ⊗ₜ[R₀] a) = awayBC (R := R) 𝒜₀ x₀ a := by
  rw [bc.ringEquiv_tmul]; simp

/-- The structure map of the base change on a localized twist. -/
private def iota (t : ℤ) (y : twistAway 𝒜₀ x₀ d t) : twistBC (R := R) 𝒜₀ x₀ d t :=
  bc.twistEquiv t ((1 : R) ⊗ₜ[R₀] y)

private lemma twistEquiv_tmul (t : ℤ) (r : R) (y : twistAway 𝒜₀ x₀ d t) :
    bc.twistEquiv t (r ⊗ₜ[R₀] y) =
      algebraMap R (SBC (R := R) 𝒜₀ x₀) r • iota 𝒜₀ x₀ d bc t y := by
  have h := bc.twistEquiv_smul t r 1 y
  rw [one_smul, ringEquiv_tmul_one] at h
  exact h

private lemma iota_smul (t : ℤ) (a : Away 𝒜₀ x₀) (y : twistAway 𝒜₀ x₀ d t) :
    iota 𝒜₀ x₀ d bc t (a • y) = awayBC (R := R) 𝒜₀ x₀ a • iota 𝒜₀ x₀ d bc t y := by
  have h := bc.twistEquiv_smul t 1 a y
  rw [ringEquiv_one_tmul] at h
  exact h

private lemma iota_add (t : ℤ) (y z : twistAway 𝒜₀ x₀ d t) :
    iota 𝒜₀ x₀ d bc t (y + z) = iota 𝒜₀ x₀ d bc t y + iota 𝒜₀ x₀ d bc t z := by
  change bc.twistEquiv t ((1 : R) ⊗ₜ[R₀] (y + z)) = _
  rw [TensorProduct.tmul_add, map_add]
  rfl

include bc in
private lemma algebraMap_bc (r₀ : R₀) :
    algebraMap R (SBC (R := R) 𝒜₀ x₀) (algebraMap R₀ R r₀) =
      awayBC (R := R) 𝒜₀ x₀ (algebraMap R₀ (Away 𝒜₀ x₀) r₀) := by
  rw [← ringEquiv_tmul_one 𝒜₀ x₀ d bc, ← ringEquiv_one_tmul 𝒜₀ x₀ d bc]
  congr 1
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- The structure map of the base change on a localized twist, as an additive homomorphism. -/
private def iotaHom (t : ℤ) :
    twistAway 𝒜₀ x₀ d t →+ twistBC (R := R) 𝒜₀ x₀ d t where
  toFun := iota 𝒜₀ x₀ d bc t
  map_zero' := by
    change bc.twistEquiv t ((1 : R) ⊗ₜ[R₀] (0 : twistAway 𝒜₀ x₀ d t)) = 0
    rw [TensorProduct.tmul_zero, map_zero]
  map_add' := iota_add 𝒜₀ x₀ d bc t


variable (k : ℕ)

/-- The two-variable additive data of the comparison map out of a base-changed free module. -/
private def alphaAux :
    R →+ ((Fin k → Away 𝒜₀ x₀) →+ (Fin k → SBC (R := R) 𝒜₀ x₀)) where
  toFun r :=
    { toFun := fun u i =>
        algebraMap R (SBC (R := R) 𝒜₀ x₀) r * awayBC (R := R) 𝒜₀ x₀ (u i)
      map_zero' := by funext i; simp
      map_add' := fun u v => by funext i; simp [mul_add] }
  map_zero' := by refine AddMonoidHom.ext fun u => ?_; funext i; simp
  map_add' r r' := by refine AddMonoidHom.ext fun u => ?_; funext i; simp [add_mul]

/-- The comparison map from the base change of a finite free module over the model's degree-zero
localization to the finite free module over its base change. -/
private def alpha :
    R ⊗[R₀] (Fin k → Away 𝒜₀ x₀) →+ (Fin k → SBC (R := R) 𝒜₀ x₀) :=
  TensorProduct.liftAddHom (alphaAux 𝒜₀ x₀ k) fun r₀ r u => by
    refine funext fun i => ?_
    change algebraMap R (SBC (R := R) 𝒜₀ x₀) (r₀ • r) * awayBC (R := R) 𝒜₀ x₀ (u i) =
      algebraMap R (SBC (R := R) 𝒜₀ x₀) r * awayBC (R := R) 𝒜₀ x₀ ((r₀ • u) i)
    have h1 : r₀ • r = algebraMap R₀ R r₀ * r := Algebra.smul_def r₀ r
    have h2 : (r₀ • u) i = algebraMap R₀ (Away 𝒜₀ x₀) r₀ * u i := by
      rw [Pi.smul_apply]; exact Algebra.smul_def r₀ (u i)
    rw [h1, h2, map_mul, map_mul, algebraMap_bc 𝒜₀ x₀ d bc r₀]
    ring

private lemma alpha_tmul (r : R) (u : Fin k → Away 𝒜₀ x₀) :
    alpha 𝒜₀ x₀ d bc k (r ⊗ₜ[R₀] u) =
      fun i => algebraMap R (SBC (R := R) 𝒜₀ x₀) r * awayBC (R := R) 𝒜₀ x₀ (u i) :=
  TensorProduct.liftAddHom_tmul _ _ r u

private lemma alpha_single (i : Fin k) (z : R ⊗[R₀] Away 𝒜₀ x₀) :
    ∃ w, alpha 𝒜₀ x₀ d bc k w = Pi.single i (bc.ringEquiv z) := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul r a =>
      refine ⟨r ⊗ₜ[R₀] Pi.single i a, ?_⟩
      rw [alpha_tmul, bc.ringEquiv_tmul]
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Pi.single_eq_of_ne hj]
  | add z z' hz hz' =>
      obtain ⟨w, hw⟩ := hz
      obtain ⟨w', hw'⟩ := hz'
      exact ⟨w + w', by rw [map_add, hw, hw', map_add, Pi.single_add]⟩

private lemma alpha_surjective : Function.Surjective (alpha 𝒜₀ x₀ d bc k) := by
  classical
  intro v
  choose w hw using fun i => alpha_single 𝒜₀ x₀ d bc k i (bc.ringEquiv.symm (v i))
  refine ⟨∑ i, w i, ?_⟩
  rw [map_sum, ← Finset.univ_sum_single v]
  exact Finset.sum_congr rfl fun i _ => by rw [hw i, bc.ringEquiv.apply_symm_apply]

/-- A linear map out of a finite free module is determined by its values on the standard basis. -/
private lemma map_eq_sum_smul_single {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module S M]
    [Fintype ι] [DecidableEq ι] (f : (ι → S) →ₗ[S] M) (u : ι → S) :
    f u = ∑ i, u i • f (Pi.single i 1) := by
  conv_lhs => rw [show u = ∑ i, u i • Pi.single i (1 : S) from by
    funext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_smul f _ _

variable (t : ℤ) {n : ℕ} (p : (Fin n → Away 𝒜₀ x₀) →ₗ[Away 𝒜₀ x₀] twistAway 𝒜₀ x₀ d t)

/-- The homomorphism from a finite free module onto the base change of a localized twist,
sending the standard basis to the images of a system of generators. -/
private def freeComb : (Fin n → SBC (R := R) 𝒜₀ x₀) →ₗ[SBC (R := R) 𝒜₀ x₀]
    twistBC (R := R) 𝒜₀ x₀ d t :=
  Fintype.linearCombination (SBC (R := R) 𝒜₀ x₀)
    fun i => iota 𝒜₀ x₀ d bc t (p (Pi.single i 1))

private lemma freeComb_awayBC (u : Fin n → Away 𝒜₀ x₀) :
    iota 𝒜₀ x₀ d bc t (p u) =
      freeComb 𝒜₀ x₀ d bc t p fun i => awayBC (R := R) 𝒜₀ x₀ (u i) := by
  rw [map_eq_sum_smul_single p u]
  change iotaHom 𝒜₀ x₀ d bc t (∑ i, u i • p (Pi.single i (1 : Away 𝒜₀ x₀))) = _
  rw [map_sum, freeComb, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change iota 𝒜₀ x₀ d bc t (u i • p (Pi.single i (1 : Away 𝒜₀ x₀))) = _
  rw [iota_smul 𝒜₀ x₀ d bc t]


variable {m : ℕ} (q : (Fin m → Away 𝒜₀ x₀) →ₗ[Away 𝒜₀ x₀] (Fin n → Away 𝒜₀ x₀))

/-- The model's presentation map, read as a map of modules over the small base ring. -/
private def presR : (Fin n → Away 𝒜₀ x₀) →ₗ[R₀] twistAway 𝒜₀ x₀ d t where
  toFun := p
  map_add' := map_add p
  map_smul' r₀ u := by
    rw [show r₀ • u = algebraMap R₀ (Away 𝒜₀ x₀) r₀ • u from
      funext fun i => Algebra.smul_def r₀ (u i), map_smul]
    rfl

/-- The model's relations map, read as a map of modules over the small base ring. -/
private def relR : (Fin m → Away 𝒜₀ x₀) →ₗ[R₀] (Fin n → Away 𝒜₀ x₀) where
  toFun := q
  map_add' := map_add q
  map_smul' r₀ u := by
    rw [show r₀ • u = algebraMap R₀ (Away 𝒜₀ x₀) r₀ • u from
      funext fun i => Algebra.smul_def r₀ (u i), map_smul]
    funext i
    exact (Algebra.smul_def r₀ (q u i)).symm

private lemma freeComb_alpha (z : R ⊗[R₀] (Fin n → Away 𝒜₀ x₀)) :
    bc.twistEquiv t (LinearMap.lTensor R (presR 𝒜₀ x₀ d t p) z) =
      freeComb 𝒜₀ x₀ d bc t p (alpha 𝒜₀ x₀ d bc n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r u =>
      rw [LinearMap.lTensor_tmul]
      change bc.twistEquiv t (r ⊗ₜ[R₀] p u) = _
      rw [twistEquiv_tmul 𝒜₀ x₀ d bc, freeComb_awayBC 𝒜₀ x₀ d bc t p u, alpha_tmul,
        ← map_smul]
      rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- The images in the base change of the standard basis of the module of relations. -/
private def genRel : Fin m → (Fin n → SBC (R := R) 𝒜₀ x₀) :=
  fun j i => awayBC (R := R) 𝒜₀ x₀ (q (Pi.single j 1) i)

private lemma awayBC_comp_rel (u : Fin m → Away 𝒜₀ x₀) :
    (fun i => awayBC (R := R) 𝒜₀ x₀ (q u i)) =
      ∑ j, awayBC (R := R) 𝒜₀ x₀ (u j) • genRel (R := R) 𝒜₀ x₀ q j := by
  funext i
  rw [Finset.sum_apply, map_eq_sum_smul_single q u, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  rfl

private lemma alpha_relR_mem_span (w : R ⊗[R₀] (Fin m → Away 𝒜₀ x₀)) :
    alpha 𝒜₀ x₀ d bc n (LinearMap.lTensor R (relR 𝒜₀ x₀ q) w) ∈
      Submodule.span (SBC (R := R) 𝒜₀ x₀) (Set.range (genRel (R := R) 𝒜₀ x₀ q)) := by
  induction w using TensorProduct.inductionOn with
  | tmul r u =>
      rw [LinearMap.lTensor_tmul]
      change alpha 𝒜₀ x₀ d bc n (r ⊗ₜ[R₀] q u) ∈ _
      rw [alpha_tmul]
      have hrw : (fun i => algebraMap R (SBC (R := R) 𝒜₀ x₀) r *
          awayBC (R := R) 𝒜₀ x₀ (q u i)) =
          algebraMap R (SBC (R := R) 𝒜₀ x₀) r •
            ∑ j, awayBC (R := R) 𝒜₀ x₀ (u j) • genRel (R := R) 𝒜₀ x₀ q j := by
        rw [← awayBC_comp_rel 𝒜₀ x₀ q u]; rfl
      rw [hrw]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  | add w w' hw hw' =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hw hw'

private lemma freeComb_surjective (hp : Function.Surjective p) :
    Function.Surjective (freeComb 𝒜₀ x₀ d bc t p) := by
  intro v
  obtain ⟨z, hz⟩ := (bc.twistEquiv t).surjective v
  obtain ⟨z', rfl⟩ := LinearMap.lTensor_surjective R (g := presR 𝒜₀ x₀ d t p) hp z
  exact ⟨alpha 𝒜₀ x₀ d bc n z', by rw [← freeComb_alpha 𝒜₀ x₀ d bc t p z', hz]⟩

private lemma ker_freeComb (hp : Function.Surjective p) (hpq : Function.Exact q p) :
    LinearMap.ker (freeComb 𝒜₀ x₀ d bc t p) =
      Submodule.span (SBC (R := R) 𝒜₀ x₀) (Set.range (genRel (R := R) 𝒜₀ x₀ q)) := by
  have hex : Function.Exact (LinearMap.lTensor R (relR 𝒜₀ x₀ q))
      (LinearMap.lTensor R (presR 𝒜₀ x₀ d t p)) := lTensor_exact R hpq hp
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · obtain ⟨z, rfl⟩ := alpha_surjective 𝒜₀ x₀ d bc n v
    have h0 : LinearMap.lTensor R (presR 𝒜₀ x₀ d t p) z = 0 := by
      refine (bc.twistEquiv t).map_eq_zero_iff.mp ?_
      rw [freeComb_alpha 𝒜₀ x₀ d bc t p z]
      exact hv
    obtain ⟨w, rfl⟩ := (hex z).mp h0
    exact alpha_relR_mem_span 𝒜₀ x₀ d bc q w
  · rintro v ⟨j, rfl⟩
    have h0 : p (q (Pi.single j (1 : Away 𝒜₀ x₀))) = 0 := hpq.apply_apply_eq_zero _
    have hkey := freeComb_awayBC 𝒜₀ x₀ d bc t p (q (Pi.single j (1 : Away 𝒜₀ x₀)))
    rw [h0] at hkey
    refine LinearMap.mem_ker.mpr ?_
    rw [show (genRel (R := R) 𝒜₀ x₀ q j) =
      fun i => awayBC (R := R) 𝒜₀ x₀ (q (Pi.single j (1 : Away 𝒜₀ x₀)) i) from rfl, ← hkey]
    exact (iotaHom 𝒜₀ x₀ d bc t).map_zero

include bc in
/-- **Finite presentation of a localized twist of the model passes to the base change.** -/
private theorem finitePresentation_twistBC
    (h : Module.FinitePresentation (Away 𝒜₀ x₀) (twistAway 𝒜₀ x₀ d t)) :
    Module.FinitePresentation (SBC (R := R) 𝒜₀ x₀) (twistBC (R := R) 𝒜₀ x₀ d t) := by
  have := h
  obtain ⟨n, m, p, q, hp, hpq⟩ :=
    Module.FinitePresentation.exists_fin' (Away 𝒜₀ x₀) (twistAway 𝒜₀ x₀ d t)
  refine Module.finitePresentation_of_surjective (freeComb 𝒜₀ x₀ d bc t p)
    (freeComb_surjective 𝒜₀ x₀ d bc t p hp) ?_
  rw [ker_freeComb 𝒜₀ x₀ d bc t p q hp hpq]
  exact Submodule.fg_span (Set.finite_range _)

end BaseChange


/-- **Finite presentation of a localized twist passes to a scalar extension.** -/
public theorem finitePresentation_twistAway_baseChange
    {R₀ R A₀ : Type u} [CommRing R₀] [CommRing R] [CommRing A₀]
    [Algebra R₀ R] [Algebra R₀ A₀] (𝒜₀ : ℕ → Submodule R₀ A₀) [GradedAlgebra 𝒜₀]
    (x₀ : A₀) (d : ℕ) (bc : StandardOpenBaseChange (R' := R) 𝒜₀ x₀ d) (t : ℤ)
    (h : Module.FinitePresentation (Away 𝒜₀ x₀) (twistAway 𝒜₀ x₀ d t)) :
    Module.FinitePresentation
      (Away (fun i => (𝒜₀ i).baseChange R) (gradedBaseChangeMap (R' := R) 𝒜₀ x₀))
      (twistAway (fun i => (𝒜₀ i).baseChange R)
        (gradedBaseChangeMap (R' := R) 𝒜₀ x₀) d t) :=
  finitePresentation_twistBC 𝒜₀ x₀ d bc t h

end Stacks.ProjTwistFinitePresentation

end
