module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeTaylorBasis
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysBaseChangeAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemAffine

/-!
# The Taylor coefficients of a crystal at the levels of the system of [Stacks, Tag 07JN]

This module evaluates the Taylor expansion algebra of `Crystalline.TaylorExpansion` on a crystal in
quasi-coherent `𝒪_{X/S}`-modules, at the objects `T(n)_e` of the cosimplicial system of
thickenings `...SmallSite.wholeSpaceSystem` with `n = 0, 1, 2`.

* The section rings `Γ(T(n)_e, 𝒪)` are free over `Γ(T_e, 𝒪)` on the reductions of the divided
  power monomials of `Crystalline.envelopeTaylorMonomial` and
  `Crystalline.envelopeTaylorMonomial₂` (`...SmallSite.bijective_levelTaylorMonomial`,
  `...SmallSite.bijective_levelTaylorMonomial₂`): the freeness of the envelopes `E(n)` over
  `E(0)` passes to the quotients `E(n)/p^{N+e} = Γ(T(n)_e, 𝒪)`.
* With the crystal base change `...SmallSite.bijective_crysBaseChangeAlong` this makes the
  restrictions of `ℱ` along the two projections `T(1)_e → T_e` a
  `Crystalline.TaylorExpansion`, `...SmallSite.levelTaylorExpansion`, whose operators are the
  `θ_K` of the proof of [Stacks, Lemma 60.17.3, Tag 07JG] at the level `e`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.17.5, Tag 07L2](https://stacks.math.columbia.edu/tag/07L2)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline

/-! ### The cosimplicial identities used -/

/-- `σ_0 ∘ δ_1 = id` on `[0]`. -/
theorem δ_one_comp_σ_zero' :
    SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.σ (n := 0) 0 = 𝟙 ⦋0⦌ := by
  ext i; fin_cases i; rfl

/-- `σ_0 ∘ δ_0 = id` on `[0]`. -/
theorem δ_zero_comp_σ_zero' :
    SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.σ (n := 0) 0 = 𝟙 ⦋0⦌ := by
  ext i; fin_cases i; rfl

/-! ### Taylor's formula in the envelope -/

section EnvelopeTaylor

variable (s : AffineCrystallineSituation.{u, u}) {ι : Type u}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- **Taylor's formula in the envelope `E(0)`**: `p₁(y) = ∑_K ξ^{[K]} p₀(δ_K y)`, as a Taylor
expansion datum for `E(0)` and `E(1)` over themselves. -/
def envelopeTaylorExpansion :
    TaylorExpansion (tensorPowerEnvelope s f 1).object (tensorPowerEnvelope s f 0).object
      (tensorPowerEnvelope s f 1).object ι where
  a₀ := (envReindex s f (SimplexCategory.δ (n := 0) 1)).toAddMonoidHom
  a₁ := (envReindex s f (SimplexCategory.δ (n := 0) 0)).toAddMonoidHom
  xi := envelopeTaylorMonomial s f
  bijective := bijective_envelopeTaylorMonomial s f

/-- The coefficients of `Crystalline.envelopeTaylorExpansion` are the Taylor coefficients
`Crystalline.envelopeTaylorCoeff`. -/
theorem envelopeTaylorExpansion_coeffs (y : (tensorPowerEnvelope s f 0).object) :
    (envelopeTaylorExpansion s f).coeffs y = envelopeTaylorCoeff s f y := rfl

/-- **The constant term of Taylor's formula**: `δ_0(y) = y`. -/
theorem envelopeTaylorCoeff_zero (y : (tensorPowerEnvelope s f 0).object) :
    envelopeTaylorCoeff s f y 0 = y := by
  have h := (envelopeTaylorExpansion s f).theta_zero (R₀ := (tensorPowerEnvelope s f 0).object)
    (envReindex s f (SimplexCategory.σ (n := 0) 0))
    (envReindex s f (SimplexCategory.σ (n := 0) 0)).toAddMonoidHom
    (fun r y ↦ map_mul (envReindex s f (SimplexCategory.σ (n := 0) 0)) r y)
    (fun m ↦ by
      show (envelopeReindex s f _).1 ((envelopeReindex s f _).1 m) = m
      rw [← envelopeReindex_comp, δ_one_comp_σ_zero', envelopeReindex_id])
    (fun m ↦ by
      show (envelopeReindex s f _).1 ((envelopeReindex s f _).1 m) = m
      rw [← envelopeReindex_comp, δ_zero_comp_σ_zero', envelopeReindex_id])
    (by
      show envReindex s f _ (envelopeTaylorMonomial s f 0) = 1
      rw [envelopeTaylorMonomial_zero, map_one])
    (fun K hK ↦ envReindex_degeneracy_envelopeTaylorMonomial s f hK) y
  exact h

end EnvelopeTaylor

/-! ### Reduction of the completion modulo `p^k` -/

section Reduction

variable {R : Type*} [CommRing R] (p k : ℕ)

/-- An element of `R` whose image in `R̂ / p^k R̂` vanishes is a multiple of `p^k`. -/
theorem exists_eq_mul_of_mk_algebraMap_eq_zero {x : R}
    (h : Ideal.Quotient.mk (Ideal.span {((p : ℕ) : AdicCompletion (Ideal.span {(p : R)}) R)} ^ k)
      (algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) x) = 0) :
    ∃ z : R, x = ((p ^ k : ℕ) : R) * z := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at h
  obtain ⟨w, hw⟩ := h
  have he := congrArg (AdicCompletion.evalₐ (Ideal.span {(p : R)}) k) hw
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of, map_mul, map_pow, map_natCast] at he
  have hz : Ideal.Quotient.mk (Ideal.span {(p : R)} ^ k) x = 0 := by
    rw [← he, ← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : R)} ^ k)), ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k),
      mul_zero]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at hz
  obtain ⟨z, hz⟩ := hz
  exact ⟨z, by rw [← hz, mul_comm, Nat.cast_pow]⟩

/-- `R → R̂ / p^k R̂` is surjective. -/
theorem surjective_mk_algebraMap :
    Function.Surjective fun x : R ↦
      Ideal.Quotient.mk (Ideal.span {((p : ℕ) : AdicCompletion (Ideal.span {(p : R)}) R)} ^ k)
        (algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) x) := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (Ideal.span {(p : R)}) k r)
  refine ⟨x, Ideal.Quotient.eq.mpr ?_⟩
  have hker : algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) x - r ∈
      (Ideal.span {(p : R)} ^ k • ⊤ :
        Submodule R (AdicCompletion (Ideal.span {(p : R)}) R)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker]
    have h1 : AdicCompletion.evalₐ (Ideal.span {(p : R)}) k
        (algebraMap R (AdicCompletion (Ideal.span {(p : R)}) R) x - r) = 0 := by
      rw [map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        AdicCompletion.evalₐ_of, hx, sub_self]
    rw [← AdicCompletion.factor_evalₐ_eq_eval (Ideal.span {(p : R)}) _
      (by rw [smul_eq_mul, Ideal.mul_top]), h1, map_zero]
  rw [Ideal.span_singleton_pow]
  refine Submodule.smul_induction_on hker (fun a ha z _ ↦ ?_) (fun _ _ h h' ↦ add_mem h h')
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [Algebra.smul_def, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right z _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

end Reduction

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-! ### The section rings of the levels as quotients of the envelopes -/

/-- The divided power envelope `E(n)` of the `(n + 1)`-fold tensor power of the presentation the
system is built from; its `p`-adic completion is the degree `n` of
`...SmallSite.wholeSpaceEnvelopeRing`. -/
abbrev wsEnvelope (n : ℕ) : DividedPowerRing.{u} :=
  (tensorPowerEnvelope (affineSituation S hp)
    (wholeSpacePresentation S hp) n).object

/-- The map from the envelope `E(n)` to its completion, the degree `n` of
`...SmallSite.wholeSpaceEnvelopeRing`. -/
def wsCompletionMap (n : ℕ) :
    (wsEnvelope hp n : Type u) →+* ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u) :=
  algebraMap (wsEnvelope hp n) (AdicCompletion (Ideal.span {((S.p : ℕ) : wsEnvelope hp n)})
    (wsEnvelope hp n))

/-- The cosimplicial structure maps of the completions extend the reindexings of the
envelopes. -/
theorem wholeSpaceEnvelopeRing_map_wsCompletionMap {m n : ℕ}
    (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (x : wsEnvelope hp m) :
    ((wholeSpaceEnvelopeRing hp).map φ).hom (wsCompletionMap hp m x) =
      wsCompletionMap hp n (envReindex (affineSituation S hp)
        (wholeSpacePresentation S hp) φ x) :=
  adicCompletionRingMap_of _ _ x

/-- **The reduction `E(n) → Γ(T(n)_e, 𝒪)`**: the map to the completion followed by
`...SmallSite.levelSectionsScalars`. -/
def envLevelMap (n e : ℕ) :
    (wsEnvelope hp n : Type u) →+* crysSheafRing S (levelObj hp n e).obj :=
  (levelSectionsScalars hp ⦋n⦌ e).comp (wsCompletionMap hp n)

/-- `envLevelMap` is `levelSectionsScalars` applied after `wsCompletionMap`. -/
theorem envLevelMap_apply (n e : ℕ) (x : wsEnvelope hp n) :
    envLevelMap hp n e x = levelSectionsScalars hp ⦋n⦌ e (wsCompletionMap hp n x) := rfl

/-- **The reductions are compatible with the cosimplicial direction.** -/
theorem envLevelMap_restriction {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (e : ℕ)
    (x : wsEnvelope hp m) :
    crysSheafRingMap (wholeSpaceTrans hp φ e).hom (envLevelMap hp m e x) =
      envLevelMap hp n e (envReindex (affineSituation S hp)
        (wholeSpacePresentation S hp) φ x) := by
  rw [envLevelMap_apply, envLevelMap_apply, ← wholeSpaceEnvelopeRing_map_wsCompletionMap]
  exact levelSectionsScalars_restriction hp φ e _

/-- **The reductions are compatible with the levels.** -/
theorem envLevelMap_levelMap (n : ℕ) {e e' : ℕ} (h : e ⟶ e') (x : wsEnvelope hp n) :
    crysSheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map h).hom
        (envLevelMap hp n e' x) = envLevelMap hp n e x := by
  rw [envLevelMap_apply, envLevelMap_apply, levelSectionsScalars_eq_envelopeLevelRingLimitEquiv,
    levelSectionsScalars_eq_envelopeLevelRingLimitEquiv]
  exact (envelopeLevelRingLimitEquiv hp n
    ((wholeSpaceSystemEnvelopeRingEquiv hp n).symm _)).property h

/-- The reduction `E(n) → Γ(T(n)_e, 𝒪)` is surjective. -/
theorem surjective_envLevelMap (n e : ℕ) : Function.Surjective (envLevelMap hp n e) := by
  intro y
  obtain ⟨q, rfl⟩ := (wholeSpaceEnvelopeRingLevelEquiv hp n e).symm.surjective y
  obtain ⟨x, hx⟩ := _root_.Crystalline.surjective_mk_algebraMap (R := wsEnvelope hp n) S.p
    (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) q
  exact ⟨x, congrArg (wholeSpaceEnvelopeRingLevelEquiv hp n e).symm hx⟩

/-- An element of `E(n)` vanishing in `Γ(T(n)_e, 𝒪)` is a multiple of `p^{N+e}`. -/
theorem exists_eq_mul_of_envLevelMap_eq_zero (n e : ℕ) {x : wsEnvelope hp n}
    (h : envLevelMap hp n e x = 0) :
    ∃ z : wsEnvelope hp n,
      x = ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        wsEnvelope hp n) * z := by
  have h' : Ideal.Quotient.mk (DividedPowers.pAdicIdeal
      (A := ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) (affineSituation S hp).p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) (wsCompletionMap hp n x) =
      0 := by
    have := congrArg (wholeSpaceEnvelopeRingLevelEquiv hp n e) h
    rw [envLevelMap_apply, levelSectionsScalars_apply, RingEquiv.apply_symm_apply] at this
    exact this.trans (map_zero _)
  exact _root_.Crystalline.exists_eq_mul_of_mk_algebraMap_eq_zero (R := wsEnvelope hp n) S.p _ h'

/-- `p^{N+e}` vanishes in `Γ(T(n)_e, 𝒪)`. -/
theorem envLevelMap_pow (n e : ℕ) :
    envLevelMap hp n e
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        wsEnvelope hp n) = 0 := by
  have hmem : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) ∈ DividedPowers.pAdicIdeal
        (A := ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) (affineSituation S hp).p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) := by
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
  rw [envLevelMap_apply, levelSectionsScalars_apply, map_natCast (wsCompletionMap hp n),
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
  exact map_zero _

/-! ### The section rings of `T(1)_e` and `T(2)_e` are free over that of `T_e` -/

/-- The restriction of the structure sheaf along a morphism of `Cris(X/S)`, as a ring
homomorphism of section rings. -/
abbrev sheafRingMap {A B : CrystallineThickening S} (k : A ⟶ B) :
    crysSheafRing S B.obj →+* crysSheafRing S A.obj :=
  crysSheafRingMap k.hom

/-- **The monomial `ξ^{[K]}` of `Γ(T(1)_e, 𝒪)`**, the reduction of
`Crystalline.envelopeTaylorMonomial`. -/
def levelTaylorMonomial (e : ℕ) (K : wholeSpaceIndex S hp →₀ ℕ) :
    crysSheafRing S (levelObj hp 1 e).obj :=
  envLevelMap hp 1 e (envelopeTaylorMonomial (affineSituation S hp)
    (wholeSpacePresentation S hp) K)

/-- **The monomial `v^{[K]} u^{[L]}` of `Γ(T(2)_e, 𝒪)`**, the reduction of
`Crystalline.envelopeTaylorMonomial₂`. -/
def levelTaylorMonomial₂ (e : ℕ)
    (KL : (wholeSpaceIndex S hp →₀ ℕ) × (wholeSpaceIndex S hp →₀ ℕ)) :
    crysSheafRing S (levelObj hp 2 e).obj :=
  envLevelMap hp 2 e (envelopeTaylorMonomial₂ (affineSituation S hp)
    (wholeSpacePresentation S hp) KL)

/-- The freeness of `E(n)` over `E(0)` through `ψ` passes to the reductions modulo `p^{N+e}`. -/
private theorem bijective_taylorSum_envLevelMap (n e : ℕ) (ψ : (⦋0⦌ : SimplexCategory) ⟶ ⦋n⦌)
    {X : Type*} (xi : X → wsEnvelope hp n)
    (hxi : Function.Bijective (taylorSum (envReindex (affineSituation S hp)
      (wholeSpacePresentation S hp) ψ).toAddMonoidHom xi)) :
    Function.Bijective (taylorSum (sheafRingMap (wholeSpaceTrans hp ψ e)).toAddMonoidHom
      fun K ↦ envLevelMap hp n e (xi K)) :=
  bijective_taylorSum_quotient _ _ hxi (envLevelMap hp 0 e) (envLevelMap hp n e) _
    (fun r ↦ envLevelMap_restriction hp _ e r) (surjective_envLevelMap hp 0 e)
    (surjective_envLevelMap hp n e) _ (envLevelMap_pow hp 0 e)
    (fun _ h ↦ exists_eq_mul_of_envLevelMap_eq_zero hp n e h)

/-- **`Γ(T(1)_e, 𝒪)` is free over `Γ(T_e, 𝒪)`, through the first projection, on the
`ξ^{[K]}`.** -/
theorem bijective_levelTaylorMonomial (e : ℕ) :
    Function.Bijective (taylorSum
      (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e)).toAddMonoidHom
      (levelTaylorMonomial hp e)) :=
  bijective_taylorSum_envLevelMap hp 1 e _ _ (bijective_envelopeTaylorMonomial _ _)

/-- **`Γ(T(2)_e, 𝒪)` is free over `Γ(T_e, 𝒪)`, through the first coprojection, on the
`v^{[K]} u^{[L]}`.** -/
theorem bijective_levelTaylorMonomial₂ (e : ℕ) :
    Function.Bijective (taylorSum
      (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) e)).toAddMonoidHom
      (levelTaylorMonomial₂ hp e)) :=
  bijective_taylorSum_envLevelMap hp 2 e _ _ (bijective_envelopeTaylorMonomial₂ _ _)

/-! ### Freeness of the sections of a crystal -/

section CrysFree

variable (F : SheafOfModules.{u} (structureSheaf S)) {A A' : CrystallineThickening S}
  (k : A' ⟶ A)

/-- The restriction of sections of `ℱ` along a morphism, as an additive map. -/
def crysRestrictHom : F.val.obj (op A) →+ F.val.obj (op A') :=
  AddMonoidHom.mk' (crysRestrict F k) (map_add _)

/-- `crysRestrictHom F k` is the restriction `crysRestrict F k`. -/
@[simp] theorem crysRestrictHom_apply (x : F.val.obj (op A)) :
    crysRestrictHom F k x = crysRestrict F k x := rfl

/-- **The sections of a crystal over the source of `k` are free over those over its target on a
family of scalars on which the section ring of the source is free.**  This is the crystal base
change `...SmallSite.bijective_crysBaseChangeAlong` combined with the freeness of the ring. -/
theorem bijective_taylorSum_crysRestrictHom [IsAffine A.obj.thickening.target.scheme]
    [IsAffine A'.obj.thickening.target.scheme]
    [(ambientSchemeOf A.obj (moduleRestrictionSheaf F A)).IsQuasicoherent]
    (hF : IsSheafCrystal F) {X : Type*}
    (xi : X → crysSheafRing S A'.obj)
    (hxi : Function.Bijective (taylorSum (sheafRingMap k).toAddMonoidHom xi)) :
    Function.Bijective (taylorSum (crysRestrictHom F k) xi) := by
  classical
  let xi' : X → ringAlong k.hom := fun K ↦ ringAlongSection k.hom (xi K)
  have hlin : ⇑(Finsupp.linearCombination (crysSheafRing S A.obj) xi') =
      ⇑(taylorSum (sheafRingMap k).toAddMonoidHom xi) := by
    funext g
    rw [Finsupp.linearCombination_apply, taylorSum_apply]
    refine Finsupp.sum_congr fun K _ ↦ ?_
    show crysSheafRingMap k.hom (g K) * xi K = xi K * sheafRingMap k (g K)
    exact mul_comm _ _
  have hb : Function.Bijective (Finsupp.linearCombination (crysSheafRing S A.obj) xi') := by
    rw [hlin]
    exact hxi
  have h := bijective_taylorSum_of_basis (crysRestrictHom F k) (siteRingAlong k.hom)
    (basisOfBijective xi' hb) (crysBaseChangeAlong F k) (bijective_crysBaseChangeAlong F k hF)
    (fun t m ↦ crysBaseChangeAlong_tmul F k t m)
  simp only [basisOfBijective_apply] at h
  exact h

end CrysFree

/-! ### The cosimplicial identities used -/

/-- `δ_2 ∘ δ_1 : [0] → [2]` is the constant map at `0`. -/
theorem δ_one_comp_δ_two :
    SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.δ (n := 1) 2 =
      SimplexCategory.const ⦋0⦌ ⦋2⦌ 0 := by
  ext i; fin_cases i; rfl

/-- `δ_1 ∘ δ_1 : [0] → [2]` is the constant map at `0`. -/
theorem δ_one_comp_δ_one :
    SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.δ (n := 1) 1 =
      SimplexCategory.const ⦋0⦌ ⦋2⦌ 0 := by
  ext i; fin_cases i; rfl

/-- `δ_0 ∘ δ_1 = δ_2 ∘ δ_0` as maps `[0] → [2]`. -/
theorem δ_one_comp_δ_zero :
    SimplexCategory.δ (n := 0) 1 ≫ SimplexCategory.δ (n := 1) 0 =
      SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 2 := by
  ext i; fin_cases i; rfl

/-- `δ_0 ∘ δ_0 = δ_1 ∘ δ_0` as maps `[0] → [2]`. -/
theorem δ_zero_comp_δ_zero :
    SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 0 =
      SimplexCategory.δ (n := 0) 0 ≫ SimplexCategory.δ (n := 1) 1 := by
  ext i; fin_cases i; rfl

/-- Alias of `Crystalline.δ_one_comp_σ_zero'`. -/
alias δ_one_comp_σ_zero := Crystalline.δ_one_comp_σ_zero'

/-- `σ_0 ∘ δ_0 = id` on `[0]`. -/
alias δ_zero_comp_σ_zero := Crystalline.δ_zero_comp_σ_zero'

/-! ### The restrictions of a sheaf of modules along the cosimplicial maps -/

section Restrictions

variable (F : SheafOfModules.{u} (structureSheaf S))

/-- The cosimplicial transitions compose. -/
theorem wholeSpaceTrans_comp {l m n : ℕ} (φ : (⦋l⦌ : SimplexCategory) ⟶ ⦋m⦌)
    (ψ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (e : ℕ) :
    wholeSpaceTrans hp ψ e ≫ wholeSpaceTrans hp φ e = wholeSpaceTrans hp (φ ≫ ψ) e := by
  show _ = ((wholeSpaceSystem S hp).map (φ ≫ ψ).op).app e
  rw [op_comp, Functor.map_comp]
  rfl

/-- The cosimplicial transition along an identity is the identity. -/
theorem wholeSpaceTrans_id (n e : ℕ) :
    wholeSpaceTrans hp (𝟙 (⦋n⦌ : SimplexCategory)) e = 𝟙 _ := by
  show ((wholeSpaceSystem S hp).map (𝟙 _).op).app e = _
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restricting along two composable cosimplicial transitions is restricting along the
composite. -/
theorem crysRestrict_wholeSpaceTrans_comp {l m n : ℕ} (φ : (⦋l⦌ : SimplexCategory) ⟶ ⦋m⦌)
    (ψ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (e : ℕ) (x : F.val.obj (op (levelObj hp l e))) :
    crysRestrict F (wholeSpaceTrans hp ψ e) (crysRestrict F (wholeSpaceTrans hp φ e) x) =
      crysRestrict F (wholeSpaceTrans hp (φ ≫ ψ) e) x := by
  rw [crysRestrict_comp, wholeSpaceTrans_comp]

/-- Restricting along the cosimplicial transition of an identity is the identity. -/
theorem crysRestrict_wholeSpaceTrans_id {n : ℕ} (e : ℕ) (x : F.val.obj (op (levelObj hp n e))) :
    crysRestrict F (wholeSpaceTrans hp (𝟙 (⦋n⦌ : SimplexCategory)) e) x = x := by
  rw [wholeSpaceTrans_id, crysRestrict_id]

/-- Two composites of cosimplicial transitions with the same composite restrict alike. -/
theorem crysRestrict_wholeSpaceTrans_comp_eq {l m n : ℕ}
    {φ φ' : (⦋l⦌ : SimplexCategory) ⟶ ⦋m⦌} {ψ ψ' : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌}
    (h : φ ≫ ψ = φ' ≫ ψ') (e : ℕ) (x : F.val.obj (op (levelObj hp l e))) :
    crysRestrict F (wholeSpaceTrans hp ψ e) (crysRestrict F (wholeSpaceTrans hp φ e) x) =
      crysRestrict F (wholeSpaceTrans hp ψ' e) (crysRestrict F (wholeSpaceTrans hp φ' e) x) := by
  rw [crysRestrict_wholeSpaceTrans_comp, crysRestrict_wholeSpaceTrans_comp, h]

/-- Restriction along a cosimplicial transition commutes with restriction along the levels. -/
theorem crysRestrict_wholeSpaceTrans_level {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌)
    {e e' : ℕ} (h : e ⟶ e') (x : F.val.obj (op (levelObj hp m e'))) :
    crysRestrict F (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map h)
        (crysRestrict F (wholeSpaceTrans hp φ e') x) =
      crysRestrict F (wholeSpaceTrans hp φ e)
        (crysRestrict F (((wholeSpaceSystem S hp).obj (op ⦋m⦌)).map h) x) := by
  rw [crysRestrict_comp, crysRestrict_comp, wholeSpaceTrans_naturality]

end Restrictions

/-! ### The Taylor expansion of a crystal at a level -/

section TaylorAtLevel

variable (Fc : QuasiCoherentCrystal S)

/-- The quasi-coherence of `ℱ_T` at the objects of the system, read off a quasi-coherent
crystal. -/
instance isQuasicoherent_ambient_levelObj (n e : ℕ) :
    (ambientSchemeOf (levelObj hp n e).obj
      (moduleRestrictionSheaf Fc.obj (levelObj hp n e))).IsQuasicoherent :=
  isQuasicoherent_ambientSchemeOf Fc.obj
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite Fc.obj Fc.property.1) _

/-- The objects of the system have affine ambient schemes. -/
instance isAffine_levelObj (n e : ℕ) :
    IsAffine (levelObj hp n e).obj.thickening.target.scheme :=
  isAffine_target_wholeSpaceSystem hp n e

/-- **The Taylor expansion datum of a crystal at the level `e`**: the restrictions along the two
projections `p₀, p₁ : T(1)_e → T_e`, and the monomials `ξ^{[K]}` of `Γ(T(1)_e, 𝒪)`, on which the
sections over `T(1)_e` are free over those over `T_e` by the crystal property. -/
def levelTaylorExpansion (e : ℕ) :
    TaylorExpansion (crysSheafRing S (levelObj hp 1 e).obj) (Fc.obj.val.obj (op (levelObj hp 0 e)))
      (Fc.obj.val.obj (op (levelObj hp 1 e))) (wholeSpaceIndex S hp) where
  a₀ := crysRestrictHom Fc.obj (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e)
  a₁ := crysRestrictHom Fc.obj (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e)
  xi := levelTaylorMonomial hp e
  bijective := bijective_taylorSum_crysRestrictHom Fc.obj _ Fc.property.2 _
    (bijective_levelTaylorMonomial hp e)

/-- **The operator `θ_K` of [Stacks, Tag 07JG] at the level `e`.** -/
abbrev levelTheta (e : ℕ) (K : wholeSpaceIndex S hp →₀ ℕ) :
    Fc.obj.val.obj (op (levelObj hp 0 e)) →+ Fc.obj.val.obj (op (levelObj hp 0 e)) :=
  (levelTaylorExpansion hp Fc e).theta K

/-- **The Taylor expansion of a crystal at the level `e`**:
`p₁^* m = ∑_K ξ^{[K]} · p₀^* θ_K(m)`, a finite sum. -/
theorem crysRestrict_δ_zero_eq_sum (e : ℕ) (m : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    crysRestrict Fc.obj (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e) m =
      ((levelTaylorExpansion hp Fc e).coeffs m).sum fun K y ↦
        levelTaylorMonomial hp e K •
          crysRestrict Fc.obj (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e) y :=
  (levelTaylorExpansion hp Fc e).a₁_eq_sum m

/-- `θ_0 = id` at every level, from the diagonal `T_e → T(1)_e`. -/
theorem levelTheta_zero (e : ℕ) (m : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    levelTheta hp Fc e 0 m = m :=
  (levelTaylorExpansion hp Fc e).theta_zero
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.σ (n := 0) 0) e))
    (crysRestrictHom Fc.obj (wholeSpaceTrans hp (SimplexCategory.σ (n := 0) 0) e))
    (fun r y ↦ map_smulₛₗ (crysRestrict Fc.obj _) r y)
    (fun m ↦ by
      show crysRestrict Fc.obj _ (crysRestrict Fc.obj _ m) = m
      rw [crysRestrict_wholeSpaceTrans_comp, δ_one_comp_σ_zero, crysRestrict_wholeSpaceTrans_id])
    (fun m ↦ by
      show crysRestrict Fc.obj _ (crysRestrict Fc.obj _ m) = m
      rw [crysRestrict_wholeSpaceTrans_comp, δ_zero_comp_σ_zero, crysRestrict_wholeSpaceTrans_id])
    (by
      show sheafRingMap _ (envLevelMap hp 1 e (envelopeTaylorMonomial _ _ 0)) = 1
      rw [envelopeTaylorMonomial_zero, map_one, map_one])
    (fun K hK ↦ by
      show sheafRingMap _ (envLevelMap hp 1 e (envelopeTaylorMonomial _ _ K)) = 0
      rw [envLevelMap_restriction, envReindex_degeneracy_envelopeTaylorMonomial _ _ hK, map_zero])
    m

/-- **`θ_L ∘ θ_K = θ_{K + L}` at every level**, from the cocycle condition of the crystal over
`T(2)_e`. -/
theorem levelTheta_levelTheta (e : ℕ) (K L : wholeSpaceIndex S hp →₀ ℕ)
    (m : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    levelTheta hp Fc e L (levelTheta hp Fc e K m) = levelTheta hp Fc e (K + L) m := by
  classical
  refine (levelTaylorExpansion hp Fc e).theta_theta
    (crysRestrictHom Fc.obj (wholeSpaceTrans hp (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0) e))
    (crysRestrictHom Fc.obj (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 2) e))
    (crysRestrictHom Fc.obj (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 0) e))
    (crysRestrictHom Fc.obj (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 1) e))
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 2) e))
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 0) e))
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 1) 1) e))
    (fun r y ↦ map_smulₛₗ (crysRestrict Fc.obj _) r y)
    (fun r y ↦ map_smulₛₗ (crysRestrict Fc.obj _) r y)
    (fun r y ↦ map_smulₛₗ (crysRestrict Fc.obj _) r y)
    (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (levelTaylorMonomial₂ hp e)
    (fun L ↦ ?_) (fun K ↦ ?_) (fun N ↦ ?_) (fun K L ↦ ?_)
    (bijective_taylorSum_crysRestrictHom Fc.obj _ Fc.property.2 _
      (bijective_levelTaylorMonomial₂ hp e)).1 K L m
  · exact (crysRestrict_wholeSpaceTrans_comp hp Fc.obj _ _ e m).trans
      (by rw [δ_one_comp_δ_two]; rfl)
  · exact (crysRestrict_wholeSpaceTrans_comp hp Fc.obj _ _ e m).trans
      (by rw [δ_one_comp_δ_one]; rfl)
  · exact crysRestrict_wholeSpaceTrans_comp_eq hp Fc.obj δ_one_comp_δ_zero e m
  · exact crysRestrict_wholeSpaceTrans_comp_eq hp Fc.obj δ_zero_comp_δ_zero e m
  · show sheafRingMap _ (envLevelMap hp 1 e _) = envLevelMap hp 2 e _
    rw [envLevelMap_restriction, envReindex_delta_two_envelopeTaylorMonomial]
  · show sheafRingMap _ (envLevelMap hp 1 e _) = envLevelMap hp 2 e _
    rw [envLevelMap_restriction, envReindex_delta_zero_envelopeTaylorMonomial]
  · show sheafRingMap _ (envLevelMap hp 1 e _) = ∑ x ∈ _, envLevelMap hp 2 e _
    rw [envLevelMap_restriction, envReindex_delta_one_envelopeTaylorMonomial, map_sum]
  · show envLevelMap hp 2 e _ * envLevelMap hp 2 e _ = envLevelMap hp 2 e _
    rw [← map_mul, envelopeTaylorMonomial₂_mul]

/-- **The operators `θ_K` are compatible with the restrictions between the levels.** -/
theorem levelTheta_levelRestrict {e e' : ℕ} (h : e ⟶ e') (K : wholeSpaceIndex S hp →₀ ℕ)
    (m : Fc.obj.val.obj (op (levelObj hp 0 e'))) :
    levelTheta hp Fc e K (crysRestrict Fc.obj (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h) m) =
      crysRestrict Fc.obj (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h)
        (levelTheta hp Fc e' K m) :=
  (levelTaylorExpansion hp Fc e').theta_naturality (levelTaylorExpansion hp Fc e)
    (crysRestrictHom Fc.obj (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h))
    (crysRestrictHom Fc.obj (((wholeSpaceSystem S hp).obj (op ⦋1⦌)).map h))
    (sheafRingMap (((wholeSpaceSystem S hp).obj (op ⦋1⦌)).map h))
    (fun r y ↦ map_smulₛₗ (crysRestrict Fc.obj _) r y)
    (fun K ↦ envLevelMap_levelMap hp 1 h _)
    (fun m ↦ crysRestrict_wholeSpaceTrans_level hp Fc.obj _ h m)
    (fun m ↦ crysRestrict_wholeSpaceTrans_level hp Fc.obj _ h m) K m

/-- The map of sections over an object induced by a morphism of crystals. -/
def crystalSectionsHom {Fc Gc : QuasiCoherentCrystal S} (psi : Fc ⟶ Gc)
    (A : CrystallineThickening S) : Fc.obj.val.obj (op A) →+ Gc.obj.val.obj (op A) :=
  (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val (op A)).hom.toAddMonoidHom

/-- `crystalSectionsHom psi A` is the component at `A` of the morphism of presheaves of modules
underlying `psi`. -/
theorem crystalSectionsHom_apply {Fc Gc : QuasiCoherentCrystal S} (psi : Fc ⟶ Gc)
    (A : CrystallineThickening S) (x : Fc.obj.val.obj (op A)) :
    crystalSectionsHom psi A x =
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val (op A)).hom x := rfl

/-- A morphism of crystals commutes with the restrictions. -/
theorem crystalSectionsHom_crysRestrict {Fc Gc : QuasiCoherentCrystal S} (psi : Fc ⟶ Gc)
    {A B : CrystallineThickening S} (k : A ⟶ B) (x : Fc.obj.val.obj (op B)) :
    crystalSectionsHom psi A (crysRestrict Fc.obj k x) =
      crysRestrict Gc.obj k (crystalSectionsHom psi B x) :=
  (PresheafOfModules.naturality_apply ((quasiCoherentCrystalι S).map psi).val k.op x)

/-- **The operators `θ_K` are natural in the crystal.** -/
theorem levelTheta_naturality {Fc Gc : QuasiCoherentCrystal S} (psi : Fc ⟶ Gc) (e : ℕ)
    (K : wholeSpaceIndex S hp →₀ ℕ) (m : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    levelTheta hp Gc e K (crystalSectionsHom psi (levelObj hp 0 e) m) =
      crystalSectionsHom psi (levelObj hp 0 e) (levelTheta hp Fc e K m) :=
  (levelTaylorExpansion hp Fc e).theta_naturality (levelTaylorExpansion hp Gc e)
    (crystalSectionsHom psi (levelObj hp 0 e)) (crystalSectionsHom psi (levelObj hp 1 e))
    (RingHom.id _) (fun r y ↦ map_smul (PresheafOfModules.Hom.app
      ((quasiCoherentCrystalι S).map psi).val (op (levelObj hp 1 e))).hom r y)
    (fun K ↦ rfl) (fun m ↦ crystalSectionsHom_crysRestrict psi _ m)
    (fun m ↦ crystalSectionsHom_crysRestrict psi _ m) K m

/-- **The Leibniz rule at a level**: for `f` the reduction of `y ∈ E(0)`,
`θ_i(f m) = f θ_i(m) + δ_i(y) m`, `δ_i(y)` the coefficient of `ξ_i` in Taylor's formula for `y`. -/
theorem levelTheta_single_smul (e : ℕ) (y : wsEnvelope hp 0) (i : wholeSpaceIndex S hp)
    (m : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    levelTheta hp Fc e (Finsupp.single i 1) (envLevelMap hp 0 e y • m) =
      envLevelMap hp 0 e y • levelTheta hp Fc e (Finsupp.single i 1) m +
        envLevelMap hp 0 e (envelopeTaylorCoeff _ _ y (Finsupp.single i 1)) • m := by
  classical
  have h := (levelTaylorExpansion hp Fc e).theta_single_smul
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e))
    (sheafRingMap (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e))
    (fun a m ↦ map_smulₛₗ (crysRestrict Fc.obj _) a m)
    (fun a m ↦ map_smulₛₗ (crysRestrict Fc.obj _) a m)
    (fun K L ↦ by
      show envLevelMap hp 1 e _ * envLevelMap hp 1 e _ = _ * envLevelMap hp 1 e _
      rw [← map_mul, envelopeTaylorMonomial_mul, map_mul, map_natCast])
    (envLevelMap hp 0 e y)
    ((envelopeTaylorCoeff _ _ y).mapRange (envLevelMap hp 0 e) (map_zero _))
    (fun z ↦ by
      congr 1
      have hT := (envelopeTaylorExpansion (affineSituation S hp)
        (wholeSpacePresentation S hp)).taylorSum_coeffs y
      rw [envelopeTaylorExpansion_coeffs, taylorSum_apply] at hT
      rw [envLevelMap_restriction]
      show envLevelMap hp 1 e ((envelopeTaylorExpansion (affineSituation S hp)
        (wholeSpacePresentation S hp)).a₁ y) = _
      rw [← hT, map_finsuppSum, Finsupp.sum_mapRange_index (fun _ ↦ by rw [map_zero, zero_mul])]
      refine Finsupp.sum_congr fun K _ ↦ ?_
      show envLevelMap hp 1 e (envelopeTaylorMonomial _ _ K * envReindex _ _ _ _) = _
      rw [map_mul, ← envLevelMap_restriction, mul_comm]
      rfl)
    i m
  rw [Finsupp.mapRange_apply, Finsupp.mapRange_apply, envelopeTaylorCoeff_zero,
    levelTheta_zero] at h
  exact h

end TaylorAtLevel

/-! ### The operators `θ_K` on `M = lim_e Γ(T_e, ℱ)` -/

section TaylorOnLimit

variable (Fc : QuasiCoherentCrystal S)

/-- Applying `θ_K` level by level to a compatible family of sections gives a compatible family. -/
theorem levelTheta_mem_levelSectionsLimit (K : wholeSpaceIndex S hp →₀ ℕ)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    (fun e ↦ levelTheta hp Fc e K (wholeSpaceSectionsVal hp Fc m e)) ∈
      levelSectionsLimit S ((wholeSpaceSystem S hp).obj (op ⦋0⦌)) Fc := by
  intro e e' h
  have := levelTheta_levelRestrict hp Fc h K (wholeSpaceSectionsVal hp Fc m e')
  have hr : crysRestrict Fc.obj (((wholeSpaceSystem S hp).obj (op ⦋0⦌)).map h)
      (wholeSpaceSectionsVal hp Fc m e') = wholeSpaceSectionsVal hp Fc m e :=
    wholeSpaceSectionsVal_restrict hp Fc m h
  rw [hr] at this
  exact this.symm

/-- **The operator `θ_K` of [Stacks, Tag 07JG] on `M = lim_e Γ(T_e, ℱ)`**, level by level. -/
def crystalTheta (K : wholeSpaceIndex S hp →₀ ℕ) :
    wholeSpaceSections hp Fc ⦋0⦌ →+ wholeSpaceSections hp Fc ⦋0⦌ where
  toFun m := wholeSpaceSectionsMk hp Fc _ (levelTheta_mem_levelSectionsLimit hp Fc K m)
  map_zero' := wholeSpaceSectionsVal_injective hp Fc fun e ↦
    (wholeSpaceSectionsVal_mk hp Fc _ (levelTheta_mem_levelSectionsLimit hp Fc K 0) e).trans
      (map_zero _)
  map_add' m m' := wholeSpaceSectionsVal_injective hp Fc fun e ↦
    (wholeSpaceSectionsVal_mk hp Fc _ (levelTheta_mem_levelSectionsLimit hp Fc K (m + m')) e).trans
      (map_add _ _ _)

/-- The component at the level `e` of `θ_K(m)` is `θ_K` at the level `e` of the component of
`m`. -/
@[simp] theorem wholeSpaceSectionsVal_crystalTheta (K : wholeSpaceIndex S hp →₀ ℕ)
    (m : wholeSpaceSections hp Fc ⦋0⦌) (e : ℕ) :
    wholeSpaceSectionsVal hp Fc (crystalTheta hp Fc K m) e =
      levelTheta hp Fc e K (wholeSpaceSectionsVal hp Fc m e) := rfl

/-- `θ_0 = id`. -/
theorem crystalTheta_zero (m : wholeSpaceSections hp Fc ⦋0⦌) : crystalTheta hp Fc 0 m = m :=
  wholeSpaceSectionsVal_injective hp Fc fun e ↦ by
    rw [wholeSpaceSectionsVal_crystalTheta, levelTheta_zero]

/-- **`θ_L ∘ θ_K = θ_{K + L}`**, which is the identity `θ_K = ∏ θ_i^{k_i}` of the source. -/
theorem crystalTheta_crystalTheta (K L : wholeSpaceIndex S hp →₀ ℕ)
    (m : wholeSpaceSections hp Fc ⦋0⦌) :
    crystalTheta hp Fc L (crystalTheta hp Fc K m) = crystalTheta hp Fc (K + L) m :=
  wholeSpaceSectionsVal_injective hp Fc fun e ↦ by
    rw [wholeSpaceSectionsVal_crystalTheta, wholeSpaceSectionsVal_crystalTheta,
      wholeSpaceSectionsVal_crystalTheta, levelTheta_levelTheta]

/-- **At each level only finitely many `θ_K(m)` are nonzero**: the Taylor expansion over
`T(1)_e` is a finite sum. -/
theorem finite_crystalTheta_ne_zero (m : wholeSpaceSections hp Fc ⦋0⦌) (e : ℕ) :
    {K | wholeSpaceSectionsVal hp Fc (crystalTheta hp Fc K m) e ≠ 0}.Finite :=
  ((levelTaylorExpansion hp Fc e).coeffs (wholeSpaceSectionsVal hp Fc m e)).finite_support

end TaylorOnLimit

end Crystalline.GlobalCrystallineSituation.SmallSite

namespace Crystalline

end Crystalline

end
