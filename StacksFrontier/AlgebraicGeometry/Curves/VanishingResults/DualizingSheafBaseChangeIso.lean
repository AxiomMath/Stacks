module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafBaseChange

/-!
# The dualizing sheaf of a proper curve commutes with extension of the ground field

In Situation [Stacks, Tag 0B5D] let `K/k` be a field extension and `g : X_K ⟶ X` the projection.
Part (2) of [Stacks, Tag 0E32] says that the inverse image of `ω_X` along `g` is the dualizing
sheaf of `X_K`. This file proves it for the canonical `ω_X = H^{-1}(f^×(𝒪_{Spec k}))`:

  `g^*ω_X ≅ ω_{X_K}`  (`pullbackDualizingSheafOverFieldIso`),

with nothing assumed, in particular not the coherence of `ω_X`.

## The argument

Both sides represent `H¹(X_K, -)^∨` on quasi-coherent modules — `ω_{X_K}` by clause (5) of
[Stacks, Tag 0BS2] over `K`, and `g^*ω_X` *nearly*: the pairing `ψ ↦ t_K ∘ H¹(ψ)` of
`DualizingSheafBaseChange.lean` is

* **injective for every quasi-coherent `ℱ` on `X_K`** (`eq_zero_of_basePairing_eq_zero`): for
  each `l : K ⟶ k` the trace of the adjunct, `Tr_l ∘ g_*ψ : g_*ℱ ⟶ ω_X`, pairs to
  `l ∘ t_K ∘ H¹(ψ)` on `X` (`dual_traceAdjunct_apply`), so it vanishes by the duality on `X`; the
  traces detect sections of `g_* g^* ω_X`
  (`Stacks.FlatTrace.eq_zero_of_forall_comp_traceOf_eq_zero`) and `g_*` is faithful on
  quasi-coherent modules, `g` being affine;
* **surjective at `g^*ℱ₀` for coherent `ℱ₀` on `X`** (`exists_basePairing_eq_of_isCoherent`):
  `H¹(X_K, g^*ℱ₀) = K ⊗_k H¹(X, ℱ₀)` is spanned by pulled-back classes, and a dual basis of the
  finite-dimensional `H¹(X, ℱ₀)` is realised by maps `ℱ₀ ⟶ ω_X`.

The map `φ : g^*ω_X ⟶ ω_{X_K}` corresponding to `t_K` is then a monomorphism (its kernel pairs to
zero) and an epimorphism (every `g^*ℱ₀ ⟶ g^*g_*ω_{X_K} ⟶ ω_{X_K}`, `ℱ₀ ⊆ g_*ω_{X_K}` coherent,
lifts through `φ`, and these subobjects cover `g_*ω_{X_K}` by [Stacks, Tag 01PG]); this is
`isIso_symm_dual_baseChangeTraceForm`. Only the quasi-coherent duality on `X` and on `X_K` and
`dim_k H¹(X, ω_X) = 1` are used.

The complex `ω_X^•` half of part (2) of [Stacks, Tag 0E32] is not treated, so no attribute is
attached.

## References

* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable {S : CohenMacaulayCurveSituation.{u}} {K : Type u} [Field K] [Algebra S.k K]

/-- **Every functional on the base is a base functional.** A `Γ(Spec k, ⊤)`-linear functional on
`Γ(Spec K, ⊤)` is the reading through `Γ(Spec R, ⊤) = R` of a `k`-linear functional on `K`. -/
theorem exists_baseFunctional_eq
    (φ : letI := baseAlgebra (S.baseChangeBase K)
      Γ(Spec (.of K), ⊤) →ₗ[Γ(Spec (.of S.k), ⊤)] Γ(Spec (.of S.k), ⊤)) :
    ∃ l : K →ₗ[S.k] S.k, S.baseFunctional K l = φ := by
  let := baseAlgebra (S.baseChangeBase K)
  refine ⟨{ toFun := fun a =>
              (Scheme.ΓSpecIso (.of S.k)).hom.hom (φ ((Scheme.ΓSpecIso (.of K)).inv.hom a))
            map_add' := fun a b => by simp only [map_add]
            map_smul' := fun c a => ?_ }, ?_⟩
  · have e : (Scheme.ΓSpecIso (.of K)).inv.hom (c • a) =
        (Scheme.ΓSpecIso (.of S.k)).inv.hom c • (Scheme.ΓSpecIso (.of K)).inv.hom a := by
      rw [Algebra.smul_def, map_mul, ← S.baseChangeBase_appLE_apply K c]
      rfl
    simp only [RingHom.id_apply]
    rw [e, map_smul, smul_eq_mul, map_mul, Iso.inv_hom_id_apply, smul_eq_mul]
  · refine LinearMap.ext fun b => ?_
    show (Scheme.ΓSpecIso (.of S.k)).inv.hom ((Scheme.ΓSpecIso (.of S.k)).hom.hom
      (φ ((Scheme.ΓSpecIso (.of K)).inv.hom ((Scheme.ΓSpecIso (.of K)).hom.hom b)))) = φ b
    rw [Iso.hom_inv_id_apply, Iso.hom_inv_id_apply]

/-- A map of quasi-coherent modules on `X_K` whose pushforward to `X` is zero is zero. -/
private theorem eq_zero_of_pushforward_baseChangeProj_map_eq_zero
    {F G : (S.baseChange K).X.Modules} [hF : F.IsQuasicoherent] [hG : G.IsQuasicoherent]
    (ψ : F ⟶ G) (hψ : (Scheme.Modules.pushforward (S.baseChangeProj K)).map ψ = 0) : ψ = 0 := by
  have := S.isAffineHom_baseChangeProj K
  exact Stacks.AlgebraicGeometry.ModuleLimits.affinePushforwardFaithful _ hF hG ψ 0
    (hψ.trans (Functor.map_zero _ _ _).symm)

section Duality

variable {ω : S.X.Modules} [hωq : ω.IsQuasicoherent]
  (hone : Module.finrank S.k (cohomologyOverField S.k S.f ω 1) = 1)
  (h : S.FirstCohomologyDuality ω)

variable (K)

/-- The adjunct of `ψ : ℱ ⟶ g^*ω` on `X`, followed by the trace of `l : K ⟶ k`. -/
abbrev traceAdjunct {F : (S.baseChange K).X.Modules}
    (ψ : F ⟶ (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) (l : K →ₗ[S.k] S.k) :
    (Scheme.Modules.pushforward (S.baseChangeProj K)).obj F ⟶ ω :=
  (Scheme.Modules.pushforward (S.baseChangeProj K)).map ψ ≫
    S.baseChangeTrace K ω (S.baseFunctional K l)

include hωq in
/-- **The duality pairing of the trace of the adjunct is `l` of the base-changed pairing.** For
`ψ : ℱ ⟶ g^*ω` on `X_K`, the functional on `H¹(X, g_*ℱ) = H¹(X_K, ℱ)` that the duality on `X`
attaches to `Tr_l ∘ g_*ψ` is `l ∘ t_K ∘ H¹(ψ)`. -/
theorem dual_traceAdjunct_apply {F : (S.baseChange K).X.Modules} [F.IsQuasicoherent]
    (hF : ((Scheme.Modules.pushforward (S.baseChangeProj K)).obj F).IsQuasicoherent)
    (ψ : F ⟶ (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) (l : K →ₗ[S.k] S.k)
    (v : cohomologyOverField K (S.baseChange K).f F 1) :
    haveI := S.isAffineHom_baseChangeProj K
    h.dual _ hF (traceAdjunct K ψ l)
        ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
          (S.baseChangeProj K) F 1).hom.hom v) =
      l (basePairing K hone h ψ v) := by
  have := S.isAffineHom_baseChangeProj K
  have := S.isQuasicoherent_pullback_baseChangeProj K ω
  have h1 : h.dual _ hF (traceAdjunct K ψ l) =
      (traceForm h).comp (cohomologyOverFieldMap S.k S.f (traceAdjunct K ψ l) 1).hom :=
    dual_eq_traceForm_comp h _ hF _
  have h2 : ∀ y, (cohomologyOverFieldMap S.k S.f (traceAdjunct K ψ l) 1).hom y =
      (cohomologyOverFieldMap S.k S.f (S.baseChangeTrace K ω (S.baseFunctional K l)) 1).hom
        ((cohomologyOverFieldMap S.k S.f
          ((Scheme.Modules.pushforward (S.baseChangeProj K)).map ψ) 1).hom y) := fun y => by
    rw [cohomologyOverFieldMap_comp]
    rfl
  have hnat := Stacks.Tag0CKW.cohomologyIsoPushforward_hom_naturality (S.baseChangeProj K) ψ 1
  have e1 : cohomologyOverFieldMap S.k S.f
        ((Scheme.Modules.pushforward (S.baseChangeProj K)).map ψ) 1
      ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
        (S.baseChangeProj K) F 1).hom.hom v) =
      (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward (S.baseChangeProj K) _ 1).hom.hom
        (cohomologyOverFieldMap K (S.baseChange K).f ψ 1 v) := by
    refine (cohomologyOverFieldMap_apply S.k S.f _ 1 _).trans ?_
    refine Eq.trans ?_ (congrArg _
      (cohomologyOverFieldMap_apply (S.baseChange K).k (S.baseChange K).f ψ 1 v).symm)
    exact (congrArg (fun m => m.hom v) hnat).symm
  rw [h1]
  refine (congrArg (traceForm h) ((h2 _).trans (congrArg _ e1))).trans ?_
  exact (congrArg (traceForm h) (cohomologyOverFieldMap_apply S.k S.f _ 1 _)).trans
    (traceForm_traceCohomology K hone h l _)

include hωq in
/-- **The base-changed duality pairing is injective**, for every quasi-coherent `ℱ` on `X_K`:
a map `ψ : ℱ ⟶ g^*ω` with `t_K ∘ H¹(ψ) = 0` is zero. Its traces `Tr_l ∘ g_*ψ` all pair to zero
on `X`, so they vanish by the duality there; the traces detect sections of `g_* g^* ω`, so
`g_*ψ = 0`, and `g_*` is faithful on quasi-coherent modules because `g` is affine. -/
theorem eq_zero_of_basePairing_eq_zero {F : (S.baseChange K).X.Modules} [hFq : F.IsQuasicoherent]
    (ψ : F ⟶ (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω)
    (hψ : basePairing K hone h ψ = 0) : ψ = 0 := by
  have := S.isAffineHom_baseChangeProj K
  have := S.isQuasicoherent_pullback_baseChangeProj K ω
  have hF : ((Scheme.Modules.pushforward (S.baseChangeProj K)).obj F).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom _ F hFq
  have hl : ∀ l : K →ₗ[S.k] S.k, traceAdjunct K ψ l = 0 := by
    intro l
    apply (h.dual _ hF).injective
    rw [map_zero]
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := ((Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward
      (S.baseChangeProj K) F 1).toLinearEquiv.surjective y)
    refine (dual_traceAdjunct_apply K hone h hF ψ l v).trans ?_
    rw [hψ]
    show l ((0 : cohomologyOverField K (S.baseChange K).f F 1 →ₗ[K] K) v) = 0
    exact map_zero l
  have hpush : (Scheme.Modules.pushforward (S.baseChangeProj K)).map ψ = 0 := by
    refine Stacks.FlatTrace.eq_zero_of_forall_comp_traceOf_eq_zero (S.isPullback_baseChange K) ω
      (S.bijective_sectionsBaseChangeMap_baseChange K ω) (S.free_baseChangeBase K) _ fun φ => ?_
    obtain ⟨l, rfl⟩ := exists_baseFunctional_eq (S := S) (K := K) φ
    exact hl l
  exact eq_zero_of_pushforward_baseChangeProj_map_eq_zero ψ hpush

/-- `ψ ↦ t_K ∘ H¹(ψ)` is additive. -/
theorem basePairing_add_apply {F : (S.baseChange K).X.Modules}
    (ψ₁ ψ₂ : F ⟶ (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω)
    (y : cohomologyOverField K (S.baseChange K).f F 1) :
    basePairing K hone h (ψ₁ + ψ₂) y = basePairing K hone h ψ₁ y + basePairing K hone h ψ₂ y := by
  show baseChangeTraceForm K hone h
      ((cohomologyOverFieldMap K (S.baseChange K).f (ψ₁ + ψ₂) 1).hom y) =
    baseChangeTraceForm K hone h ((cohomologyOverFieldMap K (S.baseChange K).f ψ₁ 1).hom y) +
      baseChangeTraceForm K hone h ((cohomologyOverFieldMap K (S.baseChange K).f ψ₂ 1).hom y)
  rw [Stacks.Cohomology.TwistCohomologyAction.cohomologyOverFieldMap_add K (S.baseChange K).f 1
    ψ₁ ψ₂, ModuleCat.hom_add, LinearMap.add_apply, map_add]

/-- `t_K ∘ H¹(0) = 0`. -/
theorem basePairing_zero_apply {F : (S.baseChange K).X.Modules}
    (y : cohomologyOverField K (S.baseChange K).f F 1) :
    basePairing K hone h (0 : F ⟶ (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) y = 0 := by
  have := basePairing_add_apply K hone h
    (0 : F ⟶ (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) 0 y
  rw [add_zero] at this
  exact left_eq_add.mp this

/-- Composing with multiplication by `a ∈ K` multiplies the pairing by `a`. -/
theorem basePairing_comp_smulEnd_apply {F : (S.baseChange K).X.Modules}
    (ψ : F ⟶ (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) (a : K)
    (y : cohomologyOverField K (S.baseChange K).f F 1) :
    basePairing K hone h (ψ ≫ (Scheme.smulEnd (S.baseChange K).X
        (((S.baseChange K).structureRingHom).hom a)).asHom.app _) y = a * basePairing K hone h ψ y := by
  show baseChangeTraceForm K hone h
      ((cohomologyOverFieldMap K (S.baseChange K).f (ψ ≫ _) 1).hom y) =
    a * baseChangeTraceForm K hone h ((cohomologyOverFieldMap K (S.baseChange K).f ψ 1).hom y)
  have h1 := (congrArg (fun m => m.hom y) (cohomologyOverFieldMap_comp K (S.baseChange K).f ψ
    ((Scheme.smulEnd (S.baseChange K).X (((S.baseChange K).structureRingHom).hom a)).asHom.app
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj ω)) 1)).trans
    (cohomologyOverFieldMap_smulEnd _ 1 a ((cohomologyOverFieldMap K (S.baseChange K).f ψ 1).hom y))
  exact (congrArg (baseChangeTraceForm K hone h) h1).trans (by rw [map_smul, smul_eq_mul])

include hωq in
/-- The pairing of a pulled-back map on pulled-back classes is the pairing on `X`. -/
theorem basePairing_pullback_map_pullbackCohomology (F0 : S.X.Modules) [F0.IsQuasicoherent]
    (hF0 : F0.IsQuasicoherent) (φ : F0 ⟶ ω) (x : cohomologyOverField S.k S.f F0 1) :
    basePairing K hone h ((Scheme.Modules.pullback (S.baseChangeProj K)).map φ)
        (S.pullbackCohomology K F0 1 x) = algebraMap S.k K (h.dual F0 hF0 φ x) := by
  show baseChangeTraceForm K hone h ((cohomologyOverFieldMap K (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).map φ) 1) (S.pullbackCohomology K F0 1 x)) = _
  rw [cohomologyOverFieldMap_pullback_pullbackCohomology, baseChangeTraceForm_pullbackCohomology,
    dual_eq_traceForm_comp h F0 hF0 φ]
  rfl

include hωq in
/-- **The base-changed duality pairing is surjective at the inverse image of a coherent module.**
For `ℱ₀` coherent on `X`, every `K`-linear functional `λ` on `H¹(X_K, g^*ℱ₀) = K ⊗_k H¹(X, ℱ₀)` is
`t_K ∘ H¹(ψ)` for some `ψ : g^*ℱ₀ ⟶ g^*ω`: in a basis `(e_i)` of the finite-dimensional
`H¹(X, ℱ₀)` with coordinate functionals `μ_i = t ∘ H¹(φ_i)`, take
`ψ = Σ_i λ(g^* e_i) · g^*φ_i`. -/
theorem exists_basePairing_eq_of_isCoherent (F0 : S.X.Modules) [hF0q : F0.IsQuasicoherent]
    (hF0 : F0.IsCoherent)
    (lam : cohomologyOverField K (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F0) 1 →ₗ[K] K) :
    ∃ ψ : (Scheme.Modules.pullback (S.baseChangeProj K)).obj F0 ⟶
        (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω,
      basePairing K hone h ψ = lam := by
  classical
  have := S.proper
  have : FiniteDimensional S.k (cohomologyOverField S.k S.f F0 1) :=
    forall_finiteDimensional_cohomologyOverField_of_isProper S.k S.f F0 hF0 1
  let b := Module.finBasis S.k (cohomologyOverField S.k S.f F0 1)
  let φ : Fin (Module.finrank S.k (cohomologyOverField S.k S.f F0 1)) → (F0 ⟶ ω) :=
    fun i => (h.dual F0 hF0q).symm (b.coord i)
  let c : Fin (Module.finrank S.k (cohomologyOverField S.k S.f F0 1)) → K :=
    fun i => lam (S.pullbackCohomology K F0 1 (b i))
  let u : Fin (Module.finrank S.k (cohomologyOverField S.k S.f F0 1)) →
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F0 ⟶
        (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) :=
    fun i => (Scheme.Modules.pullback (S.baseChangeProj K)).map (φ i) ≫
      (Scheme.smulEnd (S.baseChange K).X (((S.baseChange K).structureRingHom).hom (c i))).asHom.app _
  have hu : ∀ i x, basePairing K hone h (u i) (S.pullbackCohomology K F0 1 x) =
      c i * algebraMap S.k K (b.coord i x) := by
    intro i x
    rw [basePairing_comp_smulEnd_apply,
      basePairing_pullback_map_pullbackCohomology K hone h F0 hF0q]
    simp only [φ, AddEquiv.apply_symm_apply]
  have hsum : ∀ (s : Finset (Fin (Module.finrank S.k (cohomologyOverField S.k S.f F0 1)))) x,
      basePairing K hone h (∑ i ∈ s, u i) (S.pullbackCohomology K F0 1 x) =
        ∑ i ∈ s, c i * algebraMap S.k K (b.coord i x) := by
    intro s x
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact basePairing_zero_apply K hone h _
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, basePairing_add_apply, ih, hu]
  refine ⟨∑ i, u i, ?_⟩
  have hpb : ∀ x, basePairing K hone h (∑ i, u i) (S.pullbackCohomology K F0 1 x) =
      lam (S.pullbackCohomology K F0 1 x) := by
    intro x
    rw [hsum]
    conv_rhs => rw [← b.sum_repr x]
    rw [map_sum (S.pullbackCohomology K F0 1), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [S.pullbackCohomology_smul K F0 1, map_smul, smul_eq_mul, mul_comm]
    rfl
  refine LinearMap.ext fun w => ?_
  obtain ⟨z, rfl⟩ := (S.cohomologyBaseChange_bijective K F0 hF0 1).2 w
  induction z with
  | tmul a x =>
    rw [cohomologyBaseChange_tmul, map_smul, map_smul, hpb]
  | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]

variable {K} in
include hωq in
/-- The map `φ : g^*ω ⟶ ω'` that a duality on `X_K` attaches to `t_K` pairs every
`ψ : ℱ ⟶ g^*ω` to `t_K ∘ H¹(ψ)`. -/
theorem dual_comp_symm_dual {ω' : (S.baseChange K).X.Modules} (hω' : ω'.IsQuasicoherent)
    (h' : (S.baseChange K).FirstCohomologyDuality ω') {F : (S.baseChange K).X.Modules}
    (hF : F.IsQuasicoherent) (ψ : F ⟶ (Scheme.Modules.pullback (S.baseChangeProj K)).obj ω) :
    h'.dual F hF (ψ ≫ (h'.dual _ (S.isQuasicoherent_pullback_baseChangeProj K ω)).symm
      (baseChangeTraceForm K hone h)) = basePairing K hone h ψ := by
  refine (h'.dual_comp F _ hF (S.isQuasicoherent_pullback_baseChangeProj K ω) ψ _).trans ?_
  exact congrArg (fun m => LinearMap.comp m (cohomologyOverFieldMap K (S.baseChange K).f ψ 1).hom)
    (AddEquiv.apply_symm_apply (h'.dual _ (S.isQuasicoherent_pullback_baseChangeProj K ω))
      (baseChangeTraceForm K hone h))

include hωq in
/-- **Part (2) of [Stacks, Tag 0E32] at the dualizing module, in the form of the uniqueness of
dualizing modules.** Let `ω` on `X` carry the duality of clause (5) of [Stacks, Tag 0BS2] with
`dim_k H¹(X, ω) = 1`, and let `ω'` on `X_K` carry the same duality over `K`. Then `g^*ω ≅ ω'`,
by the map `φ` corresponding to `t_K = K ⊗ t`. It is a monomorphism because the pairing
`ψ ↦ t_K ∘ H¹(ψ)` is injective on all quasi-coherent modules (`eq_zero_of_basePairing_eq_zero`),
and an epimorphism because `ω'` is covered by the images of the `g^*ℱ₀ ⟶ g^*g_*ω' ⟶ ω'` for the
coherent `ℱ₀ ⊆ g_*ω'`, each of which lifts through `φ` by
`exists_basePairing_eq_of_isCoherent`. -/
theorem isIso_symm_dual_baseChangeTraceForm {ω' : (S.baseChange K).X.Modules}
    [hω' : ω'.IsQuasicoherent] (h' : (S.baseChange K).FirstCohomologyDuality ω') :
    IsIso ((h'.dual _ (S.isQuasicoherent_pullback_baseChangeProj K ω)).symm
      (baseChangeTraceForm K hone h)) := by
  have := S.isAffineHom_baseChangeProj K
  have hgq := S.isQuasicoherent_pullback_baseChangeProj K ω
  set φ := (h'.dual _ (S.isQuasicoherent_pullback_baseChangeProj K ω)).symm
    (baseChangeTraceForm K hone h) with hφ
  have hmono : Mono φ := by
    refine Preadditive.mono_of_cancel_zero φ fun {P} t ht => ?_
    have hkq : (kernel φ).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel φ
    have hι : kernel.ι φ = 0 := by
      refine eq_zero_of_basePairing_eq_zero K hone h (hFq := hkq) _ ?_
      rw [← dual_comp_symm_dual hone h hω' h' hkq, kernel.condition, map_zero]
      rfl
    rw [← kernel.lift_ι φ t ht, hι, comp_zero]
  have hepi : Epi φ := by
    refine Preadditive.epi_of_cancel_zero φ fun {R} t ht => ?_
    have hcq : (cokernel φ).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel φ
    suffices hπ : cokernel.π φ = 0 by rw [← cokernel.π_desc φ t ht, hπ, zero_comp]
    have hpq : ((Scheme.Modules.pushforward (S.baseChangeProj K)).obj ω').IsQuasicoherent :=
      Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom _ ω' hω'
    have := S.proper
    have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
    have : IsNoetherian S.X := S.isNoetherian
    let adj := Scheme.Modules.pullbackPushforwardAdjunction (S.baseChangeProj K)
    have hG : ∀ G : FiniteTypeQuasicoherentSubobject
        ((Scheme.Modules.pushforward (S.baseChangeProj K)).obj ω'),
        G.1.arrow ≫ (Scheme.Modules.pushforward (S.baseChangeProj K)).map (cokernel.π φ) = 0 := by
      intro G
      have hGq : (G.1 : S.X.Modules).IsQuasicoherent := G.2.1
      have hGft : (G.1 : S.X.Modules).IsFiniteType := G.2.2
      have hGc : (G.1 : S.X.Modules).IsCoherent :=
        Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
          _
      let u := (Scheme.Modules.pullback (S.baseChangeProj K)).map G.1.arrow ≫ adj.counit.app ω'
      have hpG := S.isQuasicoherent_pullback_baseChangeProj K (G.1 : S.X.Modules)
      obtain ⟨v, hv⟩ := exists_basePairing_eq_of_isCoherent K hone h (G.1 : S.X.Modules) hGc
        (h'.dual _ hpG u)
      have hvu : v ≫ φ = u := by
        apply (h'.dual _ hpG).injective
        rw [dual_comp_symm_dual hone h hω' h' hpG, hv]
      have hu : u ≫ cokernel.π φ = 0 := by rw [← hvu, Category.assoc, cokernel.condition, comp_zero]
      have key : ∀ (a : (G.1 : S.X.Modules) ⟶
            (Scheme.Modules.pushforward (S.baseChangeProj K)).obj ω')
          (Y : (S.baseChange K).X.Modules) (c : ω' ⟶ Y),
          adj.homEquiv _ Y ((Scheme.Modules.pullback (S.baseChangeProj K)).map a ≫
            adj.counit.app ω' ≫ c) =
            a ≫ (Scheme.Modules.pushforward (S.baseChangeProj K)).map c := by
        intro a Y c
        rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, adj.homEquiv_unit,
          adj.right_triangle_components, Category.id_comp]
      have hz : ∀ (Y : (S.baseChange K).X.Modules),
          adj.homEquiv (G.1 : S.X.Modules) Y 0 = 0 := by
        intro Y
        rw [adj.homEquiv_unit, Functor.map_zero, comp_zero]
      have hu' : (Scheme.Modules.pullback (S.baseChangeProj K)).map G.1.arrow ≫
          adj.counit.app ω' ≫ cokernel.π φ = 0 := by
        rw [← Category.assoc]
        exact hu
      exact (key G.1.arrow _ (cokernel.π φ)).symm.trans
        ((congrArg (adj.homEquiv _ _) hu').trans (hz _))
    have hpush : (Scheme.Modules.pushforward (S.baseChangeProj K)).map (cokernel.π φ) = 0 := by
      have htop : (⊤ : Subobject ((Scheme.Modules.pushforward (S.baseChangeProj K)).obj ω')) ≤
          kernelSubobject
            ((Scheme.Modules.pushforward (S.baseChangeProj K)).map (cokernel.π φ)) := by
        rw [← iSup_finiteTypeQuasicoherentSubobject_eq_top]
        exact iSup_le fun G => le_kernelSubobject _ _ (hG G)
      have hk := (Subobject.isIso_arrow_iff_eq_top _).mpr (top_le_iff.mp htop)
      exact (cancel_epi (kernelSubobject ((Scheme.Modules.pushforward
        (S.baseChangeProj K)).map (cokernel.π φ))).arrow).mp
        ((kernelSubobject_arrow_comp _).trans comp_zero.symm)
    exact eq_zero_of_pushforward_baseChangeProj_map_eq_zero _ hpush
  exact isIso_of_mono_of_epi φ

end Duality

variable (S K) in
/-- **The inverse image of the dualizing sheaf of `X` is the dualizing sheaf of `X_K`**: for a
field extension `K/k`, `g^*ω_X ≅ ω_{X_K}` with `g : X_K ⟶ X` the projection, where
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` and `ω_{X_K} = H^{-1}(f_K^×(𝒪_{Spec K}))`. This is the assertion
about `ω_X` in part (2) of [Stacks, Tag 0E32]. It is `isIso_symm_dual_baseChangeTraceForm` at the
canonical dualizing sheaves, whose duality (clause (5) of [Stacks, Tag 0BS2]) and
`dim_k H¹(X, ω_X) = 1` are proved unconditionally. -/
def pullbackDualizingSheafOverFieldIso :
    (Scheme.Modules.pullback (S.baseChangeProj K)).obj
        (Stacks.Duality.dualizingSheafOverField S.f) ≅
      Stacks.Duality.dualizingSheafOverField (S.baseChange K).f :=
  haveI := Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f
  haveI := Stacks.Duality.isQuasicoherent_dualizingSheafOverField (S.baseChange K).f
  @asIso _ _ _ _ _ (isIso_symm_dual_baseChangeTraceForm K
    S.finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one
    S.firstCohomologyDuality_dualizingSheafOverField
    (S.baseChange K).firstCohomologyDuality_dualizingSheafOverField)

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
