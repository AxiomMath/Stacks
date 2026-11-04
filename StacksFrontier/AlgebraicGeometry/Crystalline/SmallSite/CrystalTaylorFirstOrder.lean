module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealAffine
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysFirstOrderAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTaylorLevels
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRingDividedPowers
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceLevelProducts
public import StacksFrontier.RingTheory.DividedPowers.CompletionUniversalProperty

/-!
# The first-order Taylor coefficients of a crystal compute its connection

Let `T_e` be the level `e` of the system of [Stacks, Tag 07JN], `T(1)_e` its first-order
neighbourhood with the two projections `pr₀, pr₁ : T(1)_e ⟶ T_e`, and `T_e'` the first-order
universal thickening of `T_e` of [Stacks, Tag 07J2] with its two projections `p₀, p₁`.  The
level `T(1)_e` is a product of two copies of `T_e` for affine test objects, which gives a morphism
`q : T_e' ⟶ T(1)_e` with `q ≫ pr₀ = p₀` and `q ≫ pr₁ = p₁`.  On sections
`q^♯(ξ_c) = p₀^♯ x̄_c - p₁^♯ x̄_c = -d x̄_c`, and since `q^♯` and the reductions of the envelope
are divided power morphisms, `q^♯(ξ^{[K]})` is `1` for `K = 0`, `-d x̄_c` for `K = e_c` and `0`
otherwise.  Restricting the Taylor expansion `pr₁^* m = ∑_K ξ^{[K]} · pr₀^* θ_K(m)` of a crystal
along `q` computes the canonical connection of [Stacks, Tag 07J6] at `T_e`:
`∇(m) = -∑_c d x̄_c ⊗ θ_c(m)`.

## Main definitions

* `...SmallSite.levelCoordinate` — the image `x̄_c` of the variable `x_c` in `Γ(T_e, 𝒪)`.
* `...SmallSite.firstOrderLevelLift` — the morphism `q : T_e' ⟶ T(1)_e`.

## Main results

* `...SmallSite.sheafRingMap_firstOrderLevelLift_levelTaylorMonomial_zero`,
  `..._single` and `..._eq_zero` — the values `q^♯(ξ^{[K]})`.
* `...SmallSite.connectionDifference_levelObj_eq_sum` — `p₁^* m - p₀^* m` in the Taylor
  coordinates.
* `...SmallSite.connection_levelObj_eq_sum` — **the connection of [Stacks, Tag 07J6] at `T_e` is
  `∇(m) = -∑_c d x̄_c ⊗ θ_c(m)`.**

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Simplicial
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline

section EnvelopeProduct

variable (s : AffineCrystallineSituation.{u, u}) {ι : Type u}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- The image in `E(n)` of `ξ_i(j) = x_i(0) - x_i(j)` is the inverse image of the divided power
variable `ξ_i(j)` under `Crystalline.tensorEnvelopeDPEquiv`. -/
theorem algebraMap_coprojectionDifference_eq (n : ℕ) (q : ι × Fin n) :
    (tensorPowerEnvelope s f n).algebraMap.toRingHom (coprojectionDifference s n q) =
      (tensorEnvelopeDPEquiv s f n).symm
        (DividedPowers.dividedPowerPolynomialVariable (polynomialDividedPowerEnvelope s f).object
          q) :=
  ((RingEquiv.symm_apply_eq _).2 (tensorEnvelopeDPEquiv_coprojectionDifference s f n q).symm).symm

/-- **`ξ^{[K]} = ∏_i γ_{K_i}(ξ_i)` in `E(1)`**, with `ξ_i` the image of `x_i(0) - x_i(1)`. -/
theorem envelopeTaylorMonomial_eq_prod_dpow (K : ι →₀ ℕ) :
    envelopeTaylorMonomial s f K = K.prod fun i m ↦
      (tensorPowerEnvelope s f 1).object.dividedPowers.dpow m
        ((tensorPowerEnvelope s f 1).algebraMap.toRingHom (coprojectionDifference s 1 (i, 0))) := by
  rw [envelopeTaylorMonomial, DividedPowers.dividedPowerPolynomialMonomial, map_finsuppProd,
    Finsupp.prod_mapDomain_index_inj (fun a b h ↦ congrArg Prod.fst h)]
  refine Finsupp.prod_congr fun i _ ↦ ?_
  rw [algebraMap_coprojectionDifference_eq]
  refine Eq.trans ?_ ((tensorEnvelopeDPEquiv_symm_isDPMorphism s f 1).map_dpow
    (DividedPowers.variable_mem_polynomialIdeal _ _))
  rw [DividedPowers.setIndexedDividedPowerPolynomialDividedPowers_dpow_variable]
  rfl

end EnvelopeProduct

section FirstOrderInr

open PresheafOfModules

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)
  (W : (TopologicalSpace.Opens ↑T.scheme)ᵒᵖ)

/-- A differential, read as a section of `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/Y,δ}`, lies in the divided power
ideal `J' = J ⊕ Ω_{T/Y,δ}`. -/
theorem firstOrderThickeningInr_mem (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    firstOrderThickeningInr T Y f W ω ∈ firstOrderThickeningIdeal T Y f W :=
  (mem_firstOrderThickeningIdeal_iff T Y f W _).2 (zero_mem _)

/-- The divided powers of degree at least two of `δ'` vanish on the summand `Ω_{T/Y,δ}` of
`𝒪_{T'}`. -/
theorem firstOrderThickeningDividedPowers_dpow_add_two_inr (k : ℕ)
    (ω : ↑((dpDifferentialsModules T Y f).obj W)) :
    (firstOrderThickeningDividedPowers T Y f W).dpow (k + 2) (firstOrderThickeningInr T Y f W ω) =
      0 := by
  refine (firstOrderThickeningDividedPowers_dpow_succ T Y f W (k + 1)
    (firstOrderThickeningInr_mem T Y f W ω)).trans ?_
  have hfst : sqZeroExtFst (firstOrderThickeningInr T Y f W ω) = 0 := rfl
  refine sqZeroExt_ext ?_ ?_
  · rw [sqZeroExtFst_mk, hfst]
    exact DividedPowers.dpow_eval_zero _ (by omega)
  · rw [sqZeroExtSnd_mk, hfst, DividedPowers.dpow_eval_zero _ (by omega), zero_smul]
    rfl

end FirstOrderInr

/-! ### Two generic identities -/

/-- The coface `δ 1 : ⦋0⦌ ⟶ ⦋1⦌` is the vertex `0`. -/
theorem δ_one_eq_const :
    SimplexCategory.δ (n := 0) 1 = SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 := by
  ext i
  fin_cases i
  rfl

/-- The coface `δ 0 : ⦋0⦌ ⟶ ⦋1⦌` is the vertex `1`. -/
theorem δ_zero_eq_const :
    SimplexCategory.δ (n := 0) 0 = SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 := by
  ext i
  fin_cases i
  rfl

end Crystalline

namespace Crystalline.GlobalCrystallineSituation

/-! ### Divided powers on the first-order thickening -/

section FirstOrderDP

variable {S : GlobalCrystallineSituation.{u}} (A : Thickening S)

/-- A differential, read as a section of `𝒪_{T'}` over the first-order thickening `T'` of an
object, lies in the divided power ideal of `T'`. -/
theorem diffSection_mem_crysDividedPowers (ω : crysDiffSections A) :
    firstOrderThickeningDiffSection A ω ∈
      firstOrderThickeningIdeal A.thickening.target S.S.scheme A.toBase.hom (op ⊤) :=
  firstOrderThickeningInr_mem _ _ _ _ ω

/-- `γ'_0(ω) = 1` on the summand of differentials of `𝒪_{T'}`. -/
theorem dpow_zero_diffSection (ω : crysDiffSections A) :
    (crysDividedPowers S (firstOrderThickeningObject S A)).dpow 0
      (firstOrderThickeningDiffSection A ω) = 1 :=
  DividedPowers.dpow_zero _ (diffSection_mem_crysDividedPowers A ω)

/-- `γ'_1(ω) = ω` on the summand of differentials of `𝒪_{T'}`. -/
theorem dpow_one_diffSection (ω : crysDiffSections A) :
    (crysDividedPowers S (firstOrderThickeningObject S A)).dpow 1
      (firstOrderThickeningDiffSection A ω) = firstOrderThickeningDiffSection A ω :=
  DividedPowers.dpow_one _ (diffSection_mem_crysDividedPowers A ω)

/-- `γ'_k(ω) = 0` for `k ≥ 2` on the summand of differentials of `𝒪_{T'}`. -/
theorem dpow_add_two_diffSection (ω : crysDiffSections A) (k : ℕ) :
    (crysDividedPowers S (firstOrderThickeningObject S A)).dpow (k + 2)
      (firstOrderThickeningDiffSection A ω) = 0 :=
  firstOrderThickeningDividedPowers_dpow_add_two_inr _ _ _ _ k ω

/-- **`∏_i γ'_{K_i}(ω_i) = 0` unless `K = 0` or `K = e_i`**: a factor of degree at least two
vanishes, and two factors of degree one multiply to zero, the summand of differentials being of
square zero. -/
theorem prod_dpow_diffSection_eq_zero {ι : Type*} (ω : ι → crysDiffSections A) {K : ι →₀ ℕ}
    (h0 : K ≠ 0) (h1 : ∀ i, K ≠ Finsupp.single i 1) :
    (K.prod fun i m ↦ (crysDividedPowers S (firstOrderThickeningObject S A)).dpow m
      (firstOrderThickeningDiffSection A (ω i))) = 0 := by
  classical
  rw [Finsupp.prod]
  set g : ι → Γ((firstOrderThickeningObject S A).thickening.target.scheme, ⊤) := fun j ↦
    (crysDividedPowers S (firstOrderThickeningObject S A)).dpow (K j)
      (firstOrderThickeningDiffSection A (ω j))
  show ∏ j ∈ K.support, g j = 0
  have hg : ∀ j ∈ K.support, g j = 0 ∨ g j = firstOrderThickeningDiffSection A (ω j) := by
    intro j hj
    by_cases h : K j = 1
    · right
      simp only [g, h]
      exact dpow_one_diffSection A (ω j)
    · left
      obtain ⟨k, hk⟩ : ∃ k, K j = k + 2 :=
        ⟨K j - 2, by have := Finsupp.mem_support_iff.1 hj; omega⟩
      simp only [g, hk]
      exact dpow_add_two_diffSection A (ω j) k
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 h0
  by_cases hj : ∃ j ∈ K.support, j ≠ i
  · obtain ⟨j, hj, hji⟩ := hj
    rw [← Finset.mul_prod_erase _ _ hi,
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hji, hj⟩), ← mul_assoc]
    have hij : g i * g j = 0 := by
      rcases hg i hi with h | h
      · rw [h, zero_mul]
      rcases hg j hj with h' | h'
      · rw [h', mul_zero]
      rw [h, h']
      exact firstOrderThickeningDiffSection_mul A (ω i) (ω j)
    rw [hij, zero_mul]
  · push Not at hj
    have hKi : K i ≠ 1 := by
      intro h
      refine h1 i (Finsupp.ext fun t ↦ ?_)
      by_cases ht : t = i
      · subst ht
        simp [h]
      · rw [Finsupp.single_eq_of_ne ht]
        exact Finsupp.notMem_support_iff.1 fun h' ↦ ht (hj t h')
    obtain ⟨k, hk⟩ : ∃ k, K i = k + 2 :=
      ⟨K i - 2, by have := Finsupp.mem_support_iff.1 hi; omega⟩
    refine Finset.prod_eq_zero hi ?_
    simp only [g, hk]
    exact dpow_add_two_diffSection A (ω i) k

end FirstOrderDP

end Crystalline.GlobalCrystallineSituation


namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp]

/-- The image of the variable `x_c` in `Γ(T_e, 𝒪)`. -/
abbrev levelCoordinate (e : ℕ) (c : wholeSpaceIndex S hp) :
    crysSheafRing S (levelObj hp 0 e).obj :=
  envLevelMap hp 0 e ((tensorPowerEnvelope (affineSituation S hp)
    (wholeSpacePresentation S hp) 0).algebraMap.toRingHom
      (MvPolynomial.X ((0 : Fin 1), c)))

/-- The first projection `T(1)_e ⟶ T_e` is the vertex `0`. -/
theorem wholeSpaceTrans_δ_one_eq_vertex (e : ℕ) :
    wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e = wholeSpaceVertex S hp 1 e 0 :=
  congrArg (fun φ : (⦋0⦌ : SimplexCategory) ⟶ ⦋1⦌ ↦ ((wholeSpaceSystem S hp).map φ.op).app e)
    δ_one_eq_const

/-- The second projection `T(1)_e ⟶ T_e` is the vertex `1`. -/
theorem wholeSpaceTrans_δ_zero_eq_vertex (e : ℕ) :
    wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e = wholeSpaceVertex S hp 1 e 1 :=
  congrArg (fun φ : (⦋0⦌ : SimplexCategory) ⟶ ⦋1⦌ ↦ ((wholeSpaceSystem S hp).map φ.op).app e)
    δ_zero_eq_const

/-- The first-order thickening `T_e'` of `T_e` has affine ambient scheme. -/
instance isAffine_firstOrderLevel (e : ℕ) :
    IsAffine (firstOrderThickeningCrysObject S (levelObj hp 0 e)).obj.thickening.target.scheme :=
  isAffine_target_firstOrderThickeningObject (A := (levelObj hp 0 e).obj)

/-- A morphism `T_e' ⟶ T(1)_e` whose two vertices are the two projections `p₀, p₁ : T_e' ⟶ T_e`,
by the product property `...SmallSite.bijective_wholeSpaceVertices` of `T(1)_e`. -/
theorem exists_firstOrderLevelLift (e : ℕ) :
    ∃ q : firstOrderThickeningCrysObject S (levelObj hp 0 e) ⟶ levelObj hp 1 e,
      (fun j : Fin 2 ↦ q ≫ wholeSpaceVertex S hp 1 e j) =
        ![firstOrderThickeningCrysP₀ S (levelObj hp 0 e),
          firstOrderThickeningCrysP₁ S (levelObj hp 0 e)] :=
  (bijective_wholeSpaceVertices hp
    (isAffineObject_of_isAffine S (firstOrderThickeningCrysObject S (levelObj hp 0 e))) 1 e).2 _

/-- **The morphism `q : T_e' ⟶ T(1)_e`** with `q ≫ pr₀ = p₀` and `q ≫ pr₁ = p₁`, `T_e'` the
first-order universal thickening of `T_e` of [Stacks, Tag 07J2]. -/
def firstOrderLevelLift (e : ℕ) :
    firstOrderThickeningCrysObject S (levelObj hp 0 e) ⟶ levelObj hp 1 e :=
  (exists_firstOrderLevelLift hp e).choose

/-- `q` followed by the first projection `T(1)_e ⟶ T_e` is `p₀`. -/
theorem firstOrderLevelLift_comp_δ_one (e : ℕ) :
    firstOrderLevelLift hp e ≫ wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 1) e =
      firstOrderThickeningCrysP₀ S (levelObj hp 0 e) := by
  rw [wholeSpaceTrans_δ_one_eq_vertex]
  exact congrFun (exists_firstOrderLevelLift hp e).choose_spec 0

/-- `q` followed by the second projection `T(1)_e ⟶ T_e` is `p₁`. -/
theorem firstOrderLevelLift_comp_δ_zero (e : ℕ) :
    firstOrderLevelLift hp e ≫ wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e =
      firstOrderThickeningCrysP₁ S (levelObj hp 0 e) := by
  rw [wholeSpaceTrans_δ_zero_eq_vertex]
  exact congrFun (exists_firstOrderLevelLift hp e).choose_spec 1

/-- **The base change of sections along `p₀ : T_e' ⟶ T_e` is bijective** for a crystal in
quasi-coherent modules: `...SmallSite.bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite`
at the level `T_e`, whose ambient scheme is affine. -/
theorem bijective_crysExtensionSectionsMap_levelObj (Fc : QuasiCoherentCrystal S) (e : ℕ) :
    Function.Bijective (crysExtensionSectionsMap Fc.obj (levelObj hp 0 e)) :=
  bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite Fc.obj (levelObj hp 0 e)
    Fc.property.1

/-! ### Divided powers -/

/-- The map `E(n) → D(n)` to the `p`-adic completion is a divided power morphism. -/
theorem isDPMorphism_wsCompletionMap (n : ℕ) :
    DividedPowers.IsDPMorphism (wsEnvelope hp n).dividedPowers
      (wholeSpaceEnvelopeDPRing hp n).dividedPowers (wsCompletionMap hp n) := by
  have hmem : ∀ x ∈ (wsEnvelope hp n).ideal,
      wsCompletionMap hp n x ∈ (wholeSpaceEnvelopeDPRing hp n).ideal := fun x hx ↦
    RingHom.mem_ker.2 ((DividedPowers.completionToQuotient_algebraMap _ _ _ x).trans
      (Ideal.Quotient.eq_zero_iff_mem.2 hx))
  refine ⟨Ideal.map_le_iff_le_comap.2 hmem, fun x hx ↦ ?_⟩
  exact (DividedPowers.completedDividedPowers _ _ _ _).2 _ x hx ⟨_, hmem x hx⟩ rfl

/-- **The reduction `E(n) → Γ(T(n)_e, 𝒪)` is a divided power morphism.** -/
theorem isDPMorphism_envLevelMap (n e : ℕ) :
    DividedPowers.IsDPMorphism (wsEnvelope hp n).dividedPowers
      (crysDividedPowers S (levelObj hp n e).obj) (envLevelMap hp n e) :=
  DividedPowers.IsDPMorphism.comp _
    (DividedPowers.IsDPMorphism.comp _ (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv_symm hp n e)
      (DividedPowers.Quotient.isDPMorphism _ _))
    (isDPMorphism_wsCompletionMap hp n)

/-- The restriction of sections of `𝒪_{X/S}` along a morphism of `Cris(X/S)` is a divided power
morphism. -/
theorem isDPMorphism_sheafRingMap {A B : CrystallineThickening S} (k : A ⟶ B) :
    DividedPowers.IsDPMorphism (crysDividedPowers S B.obj) (crysDividedPowers S A.obj)
      (sheafRingMap k) :=
  (globalSectionsDPMorphism k.hom.targetHom).isDPMorphism

/-! ### The lift on the monomials -/

/-- The composite `E(1) → Γ(T(1)_e, 𝒪) → Γ(T_e', 𝒪)` of the reduction with `q^♯`, valued in the
global sections of the ambient scheme of `T_e'`. -/
def firstOrderLevelLiftEnv (e : ℕ) :
    (wsEnvelope hp 1 : Type u) →+*
      Γ((firstOrderThickeningCrysObject S (levelObj hp 0 e)).obj.thickening.target.scheme, ⊤) :=
  (sheafRingMap (firstOrderLevelLift hp e)).comp (envLevelMap hp 1 e)

/-- The composite `E(1) → Γ(T_e', 𝒪)` is a divided power morphism. -/
theorem isDPMorphism_firstOrderLevelLiftEnv (e : ℕ) :
    DividedPowers.IsDPMorphism (wsEnvelope hp 1).dividedPowers
      (crysDividedPowers S (firstOrderThickeningCrysObject S (levelObj hp 0 e)).obj)
      (firstOrderLevelLiftEnv hp e) :=
  DividedPowers.IsDPMorphism.comp _ (isDPMorphism_sheafRingMap (firstOrderLevelLift hp e))
    (isDPMorphism_envLevelMap hp 1 e)

/-- The composite `E(1) → Γ(T_e', 𝒪)` along a coprojection `E(0) → E(1)` is the reduction followed
by the restriction along any morphism `k` with `q ≫ pr = k`. -/
private theorem firstOrderLevelLiftEnv_envReindex_eq (e : ℕ) (φ : (⦋0⦌ : SimplexCategory) ⟶ ⦋1⦌)
    (k : firstOrderThickeningCrysObject S (levelObj hp 0 e) ⟶ levelObj hp 0 e)
    (hk : firstOrderLevelLift hp e ≫ wholeSpaceTrans hp φ e = k) (y : wsEnvelope hp 0) :
    firstOrderLevelLiftEnv hp e (envReindex (affineSituation S hp)
        (wholeSpacePresentation S hp) φ y) =
      crysSheafRingMap (InducedCategory.Hom.hom k) (envLevelMap hp 0 e y) :=
  ((congrArg (sheafRingMap (firstOrderLevelLift hp e))
    (envLevelMap_restriction hp φ e y).symm).trans (crysSheafRingMap_comp _ _ _)).trans
    (congrArg (fun k ↦ crysSheafRingMap (InducedCategory.Hom.hom k) (envLevelMap hp 0 e y)) hk)

/-- On the image of the first coprojection `E(0) → E(1)` the composite `E(1) → Γ(T_e', 𝒪)` is
`p₀` after the reduction. -/
theorem firstOrderLevelLiftEnv_δ_one (e : ℕ) (y : wsEnvelope hp 0) :
    firstOrderLevelLiftEnv hp e (envReindex (affineSituation S hp)
        (wholeSpacePresentation S hp) (SimplexCategory.δ (n := 0) 1) y) =
      crysSheafRingMap (firstOrderThickeningSiteP₀ S (levelObj hp 0 e).obj)
        (envLevelMap hp 0 e y) :=
  firstOrderLevelLiftEnv_envReindex_eq hp e _ _ (firstOrderLevelLift_comp_δ_one hp e) y

/-- On the image of the second coprojection `E(0) → E(1)` the composite `E(1) → Γ(T_e', 𝒪)` is
`p₁` after the reduction. -/
theorem firstOrderLevelLiftEnv_δ_zero (e : ℕ) (y : wsEnvelope hp 0) :
    firstOrderLevelLiftEnv hp e (envReindex (affineSituation S hp)
        (wholeSpacePresentation S hp) (SimplexCategory.δ (n := 0) 0) y) =
      crysSheafRingMap (firstOrderThickeningSiteP₁ S (levelObj hp 0 e).obj)
        (envLevelMap hp 0 e y) :=
  firstOrderLevelLiftEnv_envReindex_eq hp e _ _ (firstOrderLevelLift_comp_δ_zero hp e) y

/-- `ξ_c = p₀(x_c) - p₁(x_c)` in `E(1)`. -/
theorem algebraMap_coprojectionDifference_one_eq_sub (c : wholeSpaceIndex S hp) :
    (tensorPowerEnvelope (affineSituation S hp) (wholeSpacePresentation S hp)
        1).algebraMap.toRingHom (coprojectionDifference (affineSituation S hp) 1 (c, 0)) =
      envReindex (affineSituation S hp) (wholeSpacePresentation S hp)
          (SimplexCategory.δ (n := 0) 1)
          ((tensorPowerEnvelope (affineSituation S hp)
            (wholeSpacePresentation S hp) 0).algebraMap.toRingHom
              (MvPolynomial.X ((0 : Fin 1), c))) -
        envReindex (affineSituation S hp) (wholeSpacePresentation S hp)
          (SimplexCategory.δ (n := 0) 0)
          ((tensorPowerEnvelope (affineSituation S hp)
            (wholeSpacePresentation S hp) 0).algebraMap.toRingHom
              (MvPolynomial.X ((0 : Fin 1), c))) := by
  show _ = (envelopeReindex _ _ _).1 ((tensorPowerEnvelope _ _ (⦋0⦌ : SimplexCategory).len
      ).algebraMap.toRingHom _) - (envelopeReindex _ _ _).1 ((tensorPowerEnvelope _ _
        (⦋0⦌ : SimplexCategory).len).algebraMap.toRingHom _)
  rw [envelopeReindex_polynomial, envelopeReindex_polynomial, ← map_sub]
  congr 1
  simp only [MvPolynomial.rename_X, simplexVariableMap, coprojectionDifference]
  rfl

/-- **`q^♯(ξ_c) = -d x̄_c`**, read in the summand of differentials of `𝒪_{T_e'}`. -/
theorem firstOrderLevelLiftEnv_coprojectionDifference (e : ℕ) (c : wholeSpaceIndex S hp) :
    firstOrderLevelLiftEnv hp e ((tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 1).algebraMap.toRingHom
          (coprojectionDifference (affineSituation S hp) 1 (c, 0))) =
      firstOrderThickeningDiffSection (levelObj hp 0 e).obj
        (-crysDerivation (levelObj hp 0 e).obj (levelCoordinate hp e c)) := by
  rw [algebraMap_coprojectionDifference_one_eq_sub, map_sub, firstOrderLevelLiftEnv_δ_one,
    firstOrderLevelLiftEnv_δ_zero]
  refine (neg_sub _ _).symm.trans ?_
  refine (congrArg Neg.neg (crysSheafRingMap_siteP₁_sub_siteP₀ _ _)).trans ?_
  exact (map_neg (firstOrderThickeningInr _ _ _ (op ⊤)) _).symm

/-- **`q^♯(ξ^{[K]}) = ∏_c γ'_{K_c}(-d x̄_c)`**, since `q^♯` and the reduction are divided power
morphisms. -/
theorem sheafRingMap_firstOrderLevelLift_levelTaylorMonomial (e : ℕ)
    (K : wholeSpaceIndex S hp →₀ ℕ) :
    sheafRingMap (firstOrderLevelLift hp e) (levelTaylorMonomial hp e K) =
      K.prod fun c m ↦
        (crysDividedPowers S (firstOrderThickeningObject S (levelObj hp 0 e).obj)).dpow m
          (firstOrderThickeningDiffSection (levelObj hp 0 e).obj
            (-crysDerivation (levelObj hp 0 e).obj (levelCoordinate hp e c))) := by
  show firstOrderLevelLiftEnv hp e (envelopeTaylorMonomial _ _ K) = _
  rw [envelopeTaylorMonomial_eq_prod_dpow, map_finsuppProd]
  refine Finsupp.prod_congr fun c _ ↦ ?_
  rw [← firstOrderLevelLiftEnv_coprojectionDifference]
  exact ((isDPMorphism_firstOrderLevelLiftEnv hp e).dpow_comp _
    (coprojectionDifference_mem _ _ 1 (c, 0))).symm

/-- `q^♯(ξ^{[0]}) = 1`. -/
theorem sheafRingMap_firstOrderLevelLift_levelTaylorMonomial_zero (e : ℕ) :
    sheafRingMap (firstOrderLevelLift hp e) (levelTaylorMonomial hp e 0) = 1 :=
  (sheafRingMap_firstOrderLevelLift_levelTaylorMonomial hp e 0).trans Finsupp.prod_zero_index

/-- **`q^♯(ξ^{[e_c]}) = -d x̄_c`**, read in the summand of differentials of `𝒪_{T_e'}`. -/
theorem sheafRingMap_firstOrderLevelLift_levelTaylorMonomial_single (e : ℕ)
    (c : wholeSpaceIndex S hp) :
    sheafRingMap (firstOrderLevelLift hp e) (levelTaylorMonomial hp e (Finsupp.single c 1)) =
      firstOrderThickeningDiffSection (levelObj hp 0 e).obj
        (-crysDerivation (levelObj hp 0 e).obj (levelCoordinate hp e c)) := by
  refine (sheafRingMap_firstOrderLevelLift_levelTaylorMonomial hp e _).trans ?_
  refine (Finsupp.prod_single_index ?_).trans ?_
  · exact dpow_zero_diffSection _ _
  · exact dpow_one_diffSection _ _

/-- **`q^♯(ξ^{[K]}) = 0` unless `K = 0` or `K = e_c`.** -/
theorem sheafRingMap_firstOrderLevelLift_levelTaylorMonomial_eq_zero (e : ℕ)
    {K : wholeSpaceIndex S hp →₀ ℕ} (h0 : K ≠ 0) (h1 : ∀ c, K ≠ Finsupp.single c 1) :
    sheafRingMap (firstOrderLevelLift hp e) (levelTaylorMonomial hp e K) = 0 :=
  (sheafRingMap_firstOrderLevelLift_levelTaylorMonomial hp e K).trans
    (prod_dpow_diffSection_eq_zero _ _ h0 h1)

/-! ### The connection at a level -/

section Connection

variable (Fc : QuasiCoherentCrystal S)

/-- **The Taylor expansion restricted to `T_e'`**: `p₁^* m = ∑_K q^♯(ξ^{[K]}) · p₀^* θ_K(m)`. -/
theorem crysSiteRestrict_firstOrderP₁_eq_sum (e : ℕ) (x : Fc.obj.val.obj (op (levelObj hp 0 e))) :
    crysSiteRestrict Fc.obj (firstOrderThickeningCrysP₁ S (levelObj hp 0 e)) x =
      ((levelTaylorExpansion hp Fc e).coeffs x).sum fun K y ↦
        sheafRingMap (firstOrderLevelLift hp e) (levelTaylorMonomial hp e K) •
          crysSiteRestrict Fc.obj (firstOrderThickeningCrysP₀ S (levelObj hp 0 e)) y := by
  have h1 : crysSiteRestrict Fc.obj (firstOrderThickeningCrysP₁ S (levelObj hp 0 e)) x =
      crysRestrictHom Fc.obj (firstOrderLevelLift hp e)
        (crysRestrict Fc.obj (wholeSpaceTrans hp (SimplexCategory.δ (n := 0) 0) e) x) := by
    rw [← firstOrderLevelLift_comp_δ_zero hp e]
    exact (crysSiteRestrict_comp Fc.obj _ _ x).symm
  rw [h1, crysRestrict_δ_zero_eq_sum, map_finsuppSum]
  refine Finsupp.sum_congr fun K _ ↦ ?_
  refine (crysSiteRestrict_smul Fc.obj (firstOrderLevelLift hp e) _ _).trans ?_
  refine congrArg (fun z ↦ sheafRingMap (firstOrderLevelLift hp e)
    (levelTaylorMonomial hp e K) • z) ?_
  rw [← firstOrderLevelLift_comp_δ_one hp e]
  exact crysSiteRestrict_comp Fc.obj _ _ _

/-- **The difference `p₁^* m - p₀^* m` in the Taylor coordinates**: it is the image under the
canonical map `Ω ⊗ ℱ(T_e) ⟶ ℱ(T_e')` of `-∑_c d x̄_c ⊗ θ_c(m)`, for any finite set of indices
outside which the first-order coefficients `θ_c(m)` vanish. -/
theorem connectionDifference_levelObj_eq_sum (e : ℕ)
    (x : Fc.obj.val.obj (op (levelObj hp 0 e))) (T : Finset (wholeSpaceIndex S hp))
    (hT : ∀ c ∉ T, levelTheta hp Fc e (Finsupp.single c 1) x = 0) :
    AffineConnection.connectionDifference Fc.obj (levelObj hp 0 e) x =
      AffineConnection.diffAction Fc.obj (levelObj hp 0 e)
        (-∑ c ∈ T, crysDerivation (levelObj hp 0 e).obj (levelCoordinate hp e c) ⊗ₜ[
          crysSheafRing S (levelObj hp 0 e).obj] levelTheta hp Fc e (Finsupp.single c 1) x) := by
  classical
  set P₀ := firstOrderThickeningCrysP₀ S (levelObj hp 0 e)
  set ω : wholeSpaceIndex S hp → crysDiffSections (levelObj hp 0 e).obj :=
    fun c ↦ -crysDerivation (levelObj hp 0 e).obj (levelCoordinate hp e c) with hω
  set co := (levelTaylorExpansion hp Fc e).coeffs x with hco
  set g : (wholeSpaceIndex S hp →₀ ℕ) → Fc.obj.val.obj
      (op (firstOrderThickeningCrysObject S (levelObj hp 0 e))) := fun K ↦
    sheafRingMap (firstOrderLevelLift hp e) (levelTaylorMonomial hp e K) •
      crysSiteRestrict Fc.obj P₀ (co K) with hg
  set U : Finset (wholeSpaceIndex S hp →₀ ℕ) :=
    insert 0 (T.image fun c ↦ Finsupp.single c 1) with hU
  have hg0 : ∀ K, co K = 0 → g K = 0 := fun K hK ↦ by
    simp only [hg, hK, AffineConnection.restrict_zero, smul_zero]
  have hgU : ∀ K ∉ U, g K = 0 := by
    intro K hK
    by_cases h1 : ∃ c, K = Finsupp.single c 1
    · obtain ⟨c, rfl⟩ := h1
      refine hg0 _ (hT c fun hc ↦ hK ?_)
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hc)
    · push Not at h1
      have h0 : K ≠ 0 := fun h ↦ hK (h ▸ Finset.mem_insert_self _ _)
      simp only [hg, sheafRingMap_firstOrderLevelLift_levelTaylorMonomial_eq_zero hp e h0 h1,
        zero_smul]
  have hsum : (co.sum fun K y ↦ sheafRingMap (firstOrderLevelLift hp e)
      (levelTaylorMonomial hp e K) • crysSiteRestrict Fc.obj P₀ y) = ∑ K ∈ U, g K := by
    rw [Finsupp.sum]
    refine (Finset.sum_subset (Finset.subset_union_left (s₂ := U)) fun K _ hK ↦
      hg0 K (Finsupp.notMem_support_iff.1 hK)).trans ?_
    exact (Finset.sum_subset (Finset.subset_union_right (s₁ := co.support)) fun K _ hK ↦
      hgU K hK).symm
  have h0U : (0 : wholeSpaceIndex S hp →₀ ℕ) ∉ T.image fun c ↦ Finsupp.single c 1 := by
    simp only [Finset.mem_image, not_exists, not_and]
    exact fun c _ h ↦ Finsupp.single_ne_zero.2 one_ne_zero h
  have hgzero : g 0 = crysSiteRestrict Fc.obj P₀ x := by
    simp only [hg, sheafRingMap_firstOrderLevelLift_levelTaylorMonomial_zero, one_smul, hco]
    exact congrArg _ (levelTheta_zero hp Fc e x)
  have hgsingle : ∀ c, g (Finsupp.single c 1) = AffineConnection.diffAction Fc.obj
      (levelObj hp 0 e) (ω c ⊗ₜ[crysSheafRing S (levelObj hp 0 e).obj]
        levelTheta hp Fc e (Finsupp.single c 1) x) := by
    intro c
    rw [AffineConnection.diffAction_tmul]
    simp only [hg, sheafRingMap_firstOrderLevelLift_levelTaylorMonomial_single, hω]
    rfl
  rw [AffineConnection.connectionDifference_apply, crysSiteRestrict_firstOrderP₁_eq_sum, ← hco,
    hsum, hU, Finset.sum_insert h0U, hgzero, add_sub_cancel_left,
    Finset.sum_image fun c _ c' _ h ↦ Finsupp.single_left_injective one_ne_zero h]
  simp only [hgsingle, ← map_sum]
  congr 1
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [hω, TensorProduct.neg_tmul]

/-- **The canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6] at `T_e` in the Taylor
coordinates**: `∇(m) = -∑_c d x̄_c ⊗ θ_c(m)`, the sum over any finite set of indices outside which
the first-order coefficients `θ_c(m)` vanish. -/
theorem connection_levelObj_eq_sum (e : ℕ)
    (x : Fc.obj.val.obj (op (levelObj hp 0 e))) (T : Finset (wholeSpaceIndex S hp))
    (hT : ∀ c ∉ T, levelTheta hp Fc e (Finsupp.single c 1) x = 0) :
    AffineConnection.connection (bijective_crysExtensionSectionsMap_levelObj hp Fc e) x =
      -∑ c ∈ T, crysDerivation (levelObj hp 0 e).obj (levelCoordinate hp e c) ⊗ₜ[
        crysSheafRing S (levelObj hp 0 e).obj] levelTheta hp Fc e (Finsupp.single c 1) x :=
  AffineConnection.injective_diffAction (bijective_crysExtensionSectionsMap_levelObj hp Fc e)
    ((AffineConnection.diffAction_connection _ x).trans
      (connectionDifference_levelObj_eq_sum hp Fc e x T hT))

end Connection

end Crystalline.GlobalCrystallineSituation.SmallSite

end
