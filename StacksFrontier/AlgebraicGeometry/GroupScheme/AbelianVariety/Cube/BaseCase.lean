module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.FibreMaps
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.TrivialCech

/-!
# The theorem of the cube: the base case on a fibre

Let `A` be a scheme over a field `k` with a rational point `e`, with only constant global
functions, and `G` a trivial module on `A × A` with generators `σ_Y`, `σ_X`. On the alternating
Čech complex of `G` for a product cover, restriction to the faces `e × A` and `A × e` followed by
division by the generators maps into the two-term complex of cochains of functions on the faces
glued at `e`. When this is a map of complexes:

* it is onto on `H⁰` (`Stacks.Cube.fib_surjZero`);
* it is one-to-one on `H¹` relative to the target (`Stacks.Cube.fib_injOne`), by the Künneth
  formula in degree one;
* it is one-to-one on `H⁰` (`Stacks.Cube.fib_injZero`), when `A × A` has only constant global
  functions;
* if `G` has no nonzero global sections then `H⁰` vanishes (`Stacks.Cube.fib_kerZero`).

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (U : ι → A.left.Opens) {a₀ : ι}
  (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤) {G : (B A).Modules}
  {σY σX : Γ(G, ⊤)} (hσY : IsGen G σY) (hσX : IsGen G σX)

/-- The face `e × A → A × A` is a morphism over `Spec k`. -/
theorem faceYB_hom : faceYB A ≫ (A ⊗ A).hom = A.hom := by
  change faceYB A ≫ bx A ≫ A.hom = A.hom
  rw [faceY_fst_assoc, show eA (A := A) ≫ A.hom = 𝟙 _ from eA_hom, Category.comp_id]

/-- The face `A × e → A × A` is a morphism over `Spec k`. -/
theorem faceXB_hom : faceXB A ≫ (A ⊗ A).hom = A.hom := by
  change faceXB A ≫ bx A ≫ A.hom = A.hom
  rw [faceX_fst_assoc]

/-- The `k`-module structure on the fibre cochains. -/
noncomputable abbrev fibMod (p : ℕ) := Stacks.Cech.cochainModule (A ⊗ A).hom (coverB U) G p

/-- The fibre cochains. -/
noncomputable abbrev FC (p : ℕ) :=
  letI := fibMod U (G := G) p
  Stacks.Cech.alternatingSubmodule (A ⊗ A).hom (coverB U) G p

/-- The fibre differentials. -/
noncomputable abbrev fd (p : ℕ) := Stacks.Cech.alternatingCechModuleD (A ⊗ A).hom (coverB U) G p

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- The underlying cochain of the fibre differential of `x` is the Čech differential of `x`. -/
theorem fd_val (p : ℕ) (x : FC U (G := G) p) :
    (fd U p x).1 = CechCochains.cechD (coverB U) G.presheaf p x.1 := rfl

/-- Restriction to the face `e × A`, divided by `σ_Y`. -/
noncomputable def fibY (p : ℕ) :
    letI := cochainModule U A.hom p
    letI := fibMod U (G := G) p
    FC U (G := G) p →ₗ[k] RawCochain U p :=
  letI := cochainModule U A.hom p
  letI := fibMod U (G := G) p
  letI := fun O => sectionsAlgebra A.hom O
  { toFun := fun x j => (faceYB A).appLE _ _ (le_faceY U U (isPullback_B A) eA eA_hom a₀ ha₀ j)
      (divGen hσY _ (x.1 (fun l => (a₀, j l))))
    map_add' := fun x y => by
      funext j
      simp only [Submodule.coe_add, CechCochains.Cochain.add_apply, divGen_add, map_add]
      rfl
    map_smul' := fun c x => by
      funext j
      simp only [Submodule.coe_smul, Stacks.Cech.cochain_smul_apply, divGen_smul, map_mul,
        RingHom.id_apply, Pi.smul_apply, Algebra.smul_def]
      congr 1
      exact appLE_algebraMap (A ⊗ A).hom A.hom (faceYB A) faceYB_hom _ c }

/-- Restriction to the face `A × e`, divided by `σ_X`. -/
noncomputable def fibX (p : ℕ) :
    letI := cochainModule U A.hom p
    letI := fibMod U (G := G) p
    FC U (G := G) p →ₗ[k] RawCochain U p :=
  letI := cochainModule U A.hom p
  letI := fibMod U (G := G) p
  letI := fun O => sectionsAlgebra A.hom O
  { toFun := fun x j => (faceXB A).appLE _ _ (le_faceX U U (isPullback_B A) eA eA_hom a₀ ha₀ j)
      (divGen hσX _ (x.1 (fun l => (j l, a₀))))
    map_add' := fun x y => by
      funext j
      simp only [Submodule.coe_add, CechCochains.Cochain.add_apply, divGen_add, map_add]
      rfl
    map_smul' := fun c x => by
      funext j
      simp only [Submodule.coe_smul, Stacks.Cech.cochain_smul_apply, divGen_smul, map_mul,
        RingHom.id_apply, Pi.smul_apply, Algebra.smul_def]
      congr 1
      exact appLE_algebraMap (A ⊗ A).hom A.hom (faceXB A) faceXB_hom _ c }

/-- The fibre map in degree zero. -/
noncomputable def fibφ₀ :
    letI := cochainModule U A.hom 0
    letI := fibMod U (G := G) 0
    FC U (G := G) 0 →ₗ[k] RawCochain U 0 × RawCochain U 0 :=
  letI := cochainModule U A.hom 0
  letI := fibMod U (G := G) 0
  (fibY U ha₀ hσY 0).prod (fibX U ha₀ hσX 0)

/-- The fibre map in degree one. -/
noncomputable def fibφ₁ :
    letI := cochainModule U A.hom 1
    letI := fibMod U (G := G) 1
    FC U (G := G) 1 →ₗ[k] RawCochain U 1 × RawCochain U 1 × k :=
  letI := cochainModule U A.hom 1
  letI := fibMod U (G := G) 1
  (fibY U ha₀ hσY 1).prod ((fibX U ha₀ hσX 1).prod 0)

/-- Evaluation at the identity. -/
noncomputable abbrev evE :=
  evalAt U (eA (A := A)) eA_hom a₀ ha₀

/-- The differential of the fibre target complex. -/
noncomputable def fibδ :
    letI := cochainModule U A.hom 0
    letI := cochainModule U A.hom 1
    RawCochain U 0 × RawCochain U 0 →ₗ[k] RawCochain U 1 × RawCochain U 1 × k :=
  letI := cochainModule U A.hom 0
  letI := cochainModule U A.hom 1
  ((rawDₗ U A.hom 0).comp (LinearMap.fst _ _ _)).prod (((rawDₗ U A.hom 0).comp
    (LinearMap.snd _ _ _)).prod ((evE U ha₀).comp (LinearMap.fst _ _ _) -
      (evE U ha₀).comp (LinearMap.snd _ _ _)))

/-! ### Auxiliary facts -/

omit [Fintype ι] [DecidableEq ι] in
/-- The constant cochain `1` evaluates to `1` at the identity. -/
theorem evE_one : evE U ha₀ (one U) = 1 := by
  change (Scheme.ΓSpecIso (.of k)).hom ((eA (A := A)).appLE _ ⊤ _ 1) = 1
  rw [map_one, map_one]

omit [Fintype ι] [DecidableEq ι] in
/-- The constant cochain `c • 1` evaluates to `c` at the identity. -/
theorem evE_smul_one (c : k) :
    letI := cochainModule U A.hom 0
    evE U ha₀ (c • one U) = c := by
  let := cochainModule U A.hom 0
  rw [map_smul, evE_one, smul_eq_mul, mul_one]

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- If the opens `U a` cover `A`, then the product cover `coverB U` covers `A × A`. -/
theorem hcovB (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a) :
    (⊤ : (B A).Opens) = ⨆ ab, coverB U ab := by
  refine (top_unique fun x _ => ?_).symm
  have h : ∀ y, y ∈ (⨆ a, U a) := fun y => by
    rw [← hUcov]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (h (bx A x))
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 (h (bz A x))
  rw [TopologicalSpace.Opens.mem_iSup]
  exact ⟨(a, b), ha, hb⟩

/-- The constant cochain `1` of `σ_Y`. -/
noncomputable def x₁ : FC U (G := G) 0 :=
  ⟨mulσ (coverB U) (σ := σY) 0 (one (coverB U)),
    isAlternating_zero (coverB U) G.presheaf _⟩

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- The cochain `x₁` is a cocycle. -/
theorem fd_x₁ : fd U 0 (x₁ U (σY := σY)) = 0 := by
  apply Subtype.ext
  change CechCochains.cechD (coverB U) G.presheaf 0 (mulσ (coverB U) (σ := σY) 0 (one _)) = 0
  rw [cechD_mulσ, rawD_one]
  funext i
  exact zero_smul _ _

omit [Fintype ι] [DecidableEq ι] in
/-- Restricting `x₁` to the face `e × A` and dividing by `σ_Y` gives the constant cochain `1`. -/
theorem fibY_x₁ : fibY U ha₀ hσY 0 (x₁ U (σY := σY)) = one U := by
  funext j
  change (faceYB A).appLE _ _ _ (divGen hσY _ ((1 : Γ(B A, _)) • resTop G σY _)) = 1
  rw [one_smul, divGen_resTop, map_one]

variable (σY) in
/-- The ratio of the two generators. -/
noncomputable def ρ : Γ(B A, ⊤) := divGen hσX ⊤ σY

omit [GrpObj A] in
/-- Division by `σ_X` is division by `σ_Y` followed by multiplication by the ratio `ρ σY hσX`. -/
theorem divGen_σX (O : (B A).Opens) (m : Γ(G, O)) :
    divGen hσX O m = res le_top (ρ σY hσX) * divGen hσY O m := by
  rw [divGen_eq_iff]
  conv_rhs => rw [← divGen_smul_resTop hσY O m]
  rw [mul_comm, mul_smul]
  congr 1
  have h' := congrArg (G.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op) (divGen_smul_resTop hσX ⊤ σY)
  rw [Scheme.Modules.map_smul] at h'
  refine Eq.trans ?_ h'
  congr 1
  simp only [resTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

variable (σY) in
/-- The pullback of the ratio of the generators to the face `A × e`. -/
noncomputable def vX : Γ(A.left, ⊤) :=
  (faceXB A).appLE ⊤ ⊤ (by simp) (ρ σY hσX)

omit [Fintype ι] [DecidableEq ι] in
include hσY in
/-- Restricting `x₁` to the face `A × e` and dividing by `σ_X` gives the restriction of
`vX σY hσX`. -/
theorem fibX_x₁ (j : Fin 1 → ι) :
    fibX U ha₀ hσX 0 (x₁ U (σY := σY)) j = res le_top (vX σY hσX) := by
  change (faceXB A).appLE _ _ _ (divGen hσX _ ((1 : Γ(B A, _)) • resTop G σY _)) = _
  rw [one_smul, divGen_σX hσY hσX, divGen_resTop, mul_one, appLE_res, vX, res_appLE]

variable (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop))
include hAc

omit [Fintype ι] [DecidableEq ι] in
/-- **The two generators agree on `A × e`**, when the restriction to the faces is a map of
complexes. -/
theorem vX_eq_one
    (hchain : ∀ x : FC U (G := G) 0, fibδ U ha₀ (fibφ₀ U ha₀ hσY hσX x) =
      fibφ₁ U ha₀ hσY hσX (fd U 0 x)) :
    vX σY hσX = 1 := by
  obtain ⟨c, hc⟩ := hAc (vX σY hσX)
  have h : evE U ha₀ (fibY U ha₀ hσY 0 (x₁ U (σY := σY))) -
      evE U ha₀ (fibX U ha₀ hσX 0 (x₁ U (σY := σY))) = 0 := by
    refine (congrArg (fun y => y.2.2) (hchain (x₁ U (σY := σY)))).trans ?_
    simp only [fd_x₁, map_zero, Prod.snd_zero]
  rw [fibY_x₁, evE_one] at h
  have hX : evE U ha₀ (fibX U ha₀ hσX 0 (x₁ U (σY := σY))) = c := by
    change (Scheme.ΓSpecIso (.of k)).hom ((eA (A := A)).appLE _ ⊤ _
      (fibX U ha₀ hσX 0 (x₁ U (σY := σY)) (fun _ => a₀))) = c
    rw [fibX_x₁ U ha₀ hσY hσX, ← hc, appLE_res, CommRingCat.comp_apply, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    change (Scheme.ΓSpecIso (.of k)).hom ((eA (A := A)).appLE ⊤ ⊤
      (Stacks.AffineProduct.le_preimage_top _ _) (A.hom.appLE ⊤ ⊤
        (Stacks.AffineProduct.le_preimage_top _ _) ((Scheme.ΓSpecIso (.of k)).inv c))) = c
    rw [appLE_comp, appLE_congr eA_hom, id_appLE_self, Iso.inv_hom_id_apply]
  rw [hX, sub_eq_zero] at h
  rw [← hc, ← h, CommRingCat.comp_apply, map_one, map_one]

/-! ### The base case -/

omit [Fintype ι] [DecidableEq ι] in
include hσX in
/-- **Onto on `H⁰`.** -/
theorem fib_surjZero (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
    (hchain : ∀ x : FC U (G := G) 0, fibδ U ha₀ (fibφ₀ U ha₀ hσY hσX x) =
      fibφ₁ U ha₀ hσY hσX (fd U 0 x))
    (y : RawCochain U 0 × RawCochain U 0) (hy : fibδ U ha₀ y = 0) :
    ∃ x : FC U (G := G) 0, fd U 0 x = 0 ∧ fibφ₀ U ha₀ hσY hσX x = y := by
  let := cochainModule U A.hom 0
  obtain ⟨u, w⟩ := y
  have h1 : rawD U 0 u = 0 := congrArg Prod.fst hy
  have h2 : rawD U 0 w = 0 := congrArg (fun y => y.2.1) hy
  have h3 : evE U ha₀ u - evE U ha₀ w = 0 := congrArg (fun y => y.2.2) hy
  obtain ⟨α, rfl⟩ := exists_eq_smul_one_of_rawD_eq_zero A.hom U hUcov hAc u h1
  obtain ⟨β, rfl⟩ := exists_eq_smul_one_of_rawD_eq_zero A.hom U hUcov hAc w h2
  rw [evE_smul_one, evE_smul_one, sub_eq_zero] at h3
  subst h3
  let := fibMod U (G := G) 0
  refine ⟨α • x₁ U (σY := σY), by rw [map_smul, fd_x₁, smul_zero], ?_⟩
  rw [map_smul]
  refine Prod.ext ?_ ?_
  · change α • fibY U ha₀ hσY 0 (x₁ U (σY := σY)) = _
    rw [fibY_x₁]
  · change α • fibX U ha₀ hσX 0 (x₁ U (σY := σY)) = _
    congr 1
    funext j
    rw [fibX_x₁ U ha₀ hσY hσX, vX_eq_one U ha₀ hσY hσX hAc hchain, map_one]
    rfl

omit hAc in
/-- If `vX σY hσX = 1`, then on the face `A × e` division by `σ_X` and division by `σ_Y` agree
after restriction. -/
theorem faceXB_divGen_σX (hv : vX σY hσX = 1) (W : (B A).Opens) (O : A.left.Opens)
    (h : O ≤ faceXB A ⁻¹ᵁ W) (m : Γ(G, W)) :
    (faceXB A).appLE W O h (divGen hσX W m) = (faceXB A).appLE W O h (divGen hσY W m) := by
  rw [divGen_σX hσY hσX, map_mul, appLE_res]
  have h1 : (faceXB A).appLE ⊤ O (h.trans (Scheme.Hom.preimage_mono _ le_top))
      (ρ σY hσX) = 1 := by
    rw [← res_appLE (faceXB A) (le_top : O ≤ ⊤) (Stacks.AffineProduct.le_preimage_top _ _)]
    have hv' : (faceXB A).appLE ⊤ ⊤ (Stacks.AffineProduct.le_preimage_top _ _)
        (ρ σY hσX) = 1 := hv
    rw [hv', map_one]
  rw [h1, one_mul]

omit hAc [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- If `x` is a cocycle, then the cochain of functions obtained by dividing `x` by `σ_Y` is a
cocycle. -/
theorem dg_zero_of_fd (p : ℕ) (x : FC U (G := G) p) (hx : fd U p x = 0) :
    rawD (coverB U) p (dg (coverB U) hσY p x.1) = 0 := by
  refine (rawD_dg (coverB U) hσY p x.1).trans ?_
  have h : CechCochains.cechD (coverB U) G.presheaf p x.1 = 0 := congrArg Subtype.val hx
  funext i
  change divGen hσY _ (CechCochains.cechD (coverB U) G.presheaf p x.1 i) = 0
  rw [show CechCochains.cechD (coverB U) G.presheaf p x.1 i = 0 from
    congrArg (fun c : CechCochains.Cochain (coverB U) G.presheaf (p + 1) => c i) h]
  exact divGen_zero hσY _

omit [Fintype ι] [DecidableEq ι] in
/-- **One-to-one on `H¹`**, by the Künneth formula in degree one. -/
theorem fib_injOne [Finite ι]
    (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i))
    (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
    (hchain : ∀ x : FC U (G := G) 0, fibδ U ha₀ (fibφ₀ U ha₀ hσY hσX x) =
      fibφ₁ U ha₀ hσY hσX (fd U 0 x))
    (x : FC U (G := G) 1) (hx : fd U 1 x = 0)
    (hy : ∃ y, fibφ₁ U ha₀ hσY hσX x = fibδ U ha₀ y) :
    ∃ c : FC U (G := G) 0, fd U 0 c = x := by
  obtain ⟨⟨u, w⟩, hy⟩ := hy
  have hY : fibY U ha₀ hσY 1 x = rawD U 0 u := congrArg Prod.fst hy
  have hX : fibX U ha₀ hσX 1 x = rawD U 0 w := congrArg (fun y => y.2.1) hy
  have hfX : ∀ i : Fin 2 → ι, (faceXB A).appLE _ _
      (le_faceX U U (isPullback_B A) eA eA_hom a₀ ha₀ i)
      (dg (coverB U) hσY 1 x.1 (fun l => (i l, a₀))) = rawD U 0 w i := by
    intro i
    rw [← congrFun hX i]
    exact (faceXB_divGen_σX hσY hσX (vX_eq_one U ha₀ hσY hσX hAc hchain) _ _ _ _).symm
  obtain ⟨F₀, hF₀⟩ := exists_rawD_eq_of_cocycle U U (isPullback_B A) hU hU hUcov hUcov hAc hAc
    eA eA_hom a₀ ha₀ eA eA_hom a₀ ha₀ (dg (coverB U) hσY 1 x.1)
    (dg_zero_of_fd U hσY 1 x hx) ⟨w, hfX⟩
    ⟨u, fun j => congrFun hY j⟩
  refine ⟨⟨mulσ (coverB U) (σ := σY) 0 F₀, isAlternating_zero (coverB U) G.presheaf _⟩,
    Subtype.ext ?_⟩
  change CechCochains.cechD (coverB U) G.presheaf 0 (mulσ (coverB U) (σ := σY) 0 F₀) = x.1
  rw [cechD_mulσ, hF₀]
  exact mulσ_dg (coverB U) hσY 1 x.1

omit hAc [Fintype ι] [DecidableEq ι] in
/-- **One-to-one on `H⁰`**, when `A × A` has only constant global functions. -/
theorem fib_injZero (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
    (hBc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ (A ⊗ A).hom.appTop))
    (x : FC U (G := G) 0) (hx : fd U 0 x = 0) (hφ : fibφ₀ U ha₀ hσY hσX x = 0) : x = 0 := by
  let := cochainModule (coverB U) (A ⊗ A).hom 0
  let := cochainModule U A.hom 0
  obtain ⟨lam, hlam⟩ := exists_eq_smul_one_of_rawD_eq_zero (A ⊗ A).hom (coverB U)
    (hcovB U hUcov) hBc _ (dg_zero_of_fd U hσY 0 x hx)
  have hY : fibY U ha₀ hσY 0 x = lam • one U := by
    funext j
    change (faceYB A).appLE _ _ _ (dg (coverB U) hσY 0 x.1 (fun l => (a₀, j l))) = _
    rw [hlam]
    change (faceYB A).appLE _ _ _ ((Stacks.Cech.baseRingHom (A ⊗ A).hom _).hom lam * 1) =
      (Stacks.Cech.baseRingHom A.hom _).hom lam * 1
    rw [mul_one, mul_one]
    exact appLE_algebraMap (A ⊗ A).hom A.hom (faceYB A) faceYB_hom _ lam
  have h0 : fibY U ha₀ hσY 0 x = 0 := congrArg Prod.fst hφ
  have hlam0 : lam = 0 := by
    have := congrArg (evE U ha₀) (hY.symm.trans h0)
    rwa [evE_smul_one, map_zero] at this
  apply Subtype.ext
  have hm := mulσ_dg (coverB U) hσY 0 x.1
  rw [hlam, hlam0, zero_smul] at hm
  refine hm.symm.trans ?_
  funext i
  exact zero_smul _ _

omit hAc [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- **Vanishing of `H⁰`** when `G` has no nonzero global sections. -/
theorem fib_kerZero (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
    (h0 : ∀ s : Γ(G, ⊤), s = 0) (x : FC U (G := G) 0) (hx : fd U 0 x = 0) : x = 0 := by
  obtain ⟨s, hs⟩ := exists_section_of_cechD_eq_zero (coverB U) G (hcovB U hUcov) x.1
    (congrArg Subtype.val hx)
  apply Subtype.ext
  funext i
  rw [← hs i, h0 s, map_zero]
  rfl

end Stacks.Cube

end
