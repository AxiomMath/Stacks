module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.BaseCase
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# The theorem of the cube: the chart complex at a rational point

For a rational point `z` of an affine chart `V`, the restriction maps to the fibre at `z` identify
the base change of the chart complex along evaluation at `z` with the Čech complex of the fibre,
compatibly with the face maps. The cone conditions and the vanishing of `H⁰` on the fibre, computed
in `StacksFrontier/AlgebraicGeometry/GroupScheme/AbelianVariety/Cube/BaseCase.lean`, therefore transfer
to the base-changed chart complex.

## Main results

* `θC_d`: restriction to the fibre commutes with the differentials of the chart complex.
* `transfer_at`: the cone conditions hold after base change to a rational point.
* `ker_d₀_evz`: the first differential is injective after base change to a rational point whose
  fibre has no nonzero sections.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator Stacks.FlatComplexNakayama

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]
  (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) {V : A.left.Opens}
  (hV : IsAffineOpen V) (hzV : z ⁻¹ᵁ V = ⊤) {ι : Type u} [Fintype ι] [DecidableEq ι]
  (U : ι → A.left.Opens) (N : (P A).Modules)

attribute [local instance] faceModule chartAlgebra secAlg secAlgB

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- The chart complex commutes with restriction to the fibre. -/
theorem θC_d (p : ℕ) (c : CX hV U N p) :
    fd U (G := fibreModule z hzk hzV N) p (θC z hzk hV hzV U N p c) =
      θC z hzk hV hzV U N (p + 1) (((chartComplex hV U N).d p (p + 1)).hom c) := by
  apply Subtype.ext
  rw [fd_val]
  show _ = Stacks.Cech.cochainBaseChange (jzV z hzk hzV) (chartCover U V) (coverB U)
    (Equiv.refl _) (chartModule N V) (coverB_eq_preimage z hzk hzV U) (p + 1)
    (((chartComplex hV U N).d p (p + 1)).hom c).1
  rw [d_apply_val]
  exact Stacks.Cech.cochainBaseChange_cechD _ _ _ _ _ (coverB_eq_preimage z hzk hzV U) p c.1

variable {a₀ : ι} (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤)
  {g₁ : Γ((Scheme.Modules.pullback (face₁ A)).obj N, ⊤)} (hg₁ : IsGen _ g₁)
  {g₂ : Γ((Scheme.Modules.pullback (face₂ A)).obj N, ⊤)} (hg₂ : IsGen _ g₂)
  {σY σX : Γ(fibreModule z hzk hzV N, ⊤)} (hσY : IsGen _ σY) (hσX : IsGen _ σX)

/-- The normalization of a fibre generator along the face `e × A`. -/
def NormY : Prop :=
  pulledGen₁ N (τz z hzk) (face₁ A) (faceYB A) (jzV z hzk hzV ≫ (PV V).ι) (hcommY z hzk hzV)
      (g₁ := g₁) =
    pulledGen₂ N (faceYB A) (jzV z hzk hzV ≫ (PV V).ι)
      (g₂ := Scheme.Modules.Hom.app (restrictPullbackIso (jzV z hzk hzV) (PV V).ι N).hom ⊤ σY)

/-- The normalization of a fibre generator along the face `A × e`. -/
def NormX : Prop :=
  pulledGen₁ N (τz z hzk) (face₂ A) (faceXB A) (jzV z hzk hzV ≫ (PV V).ι) (hcommX z hzk hzV)
      (g₁ := g₂) =
    pulledGen₂ N (faceXB A) (jzV z hzk hzV ≫ (PV V).ι)
      (g₂ := Scheme.Modules.Hom.app (restrictPullbackIso (jzV z hzk hzV) (PV V).ι N).hom ⊤ σX)

/-- Restriction to the fibre intertwines the face map along `e × A` with its fibre analogue. -/
theorem θD_phiY (hnY : NormY z hzk hzV N (g₁ := g₁) (σY := σY)) (p : ℕ) (c : CX hV U N p) :
    θD z hzk hzV U p (phiY hV U ha₀ N hg₁ p c) =
      fibY U ha₀ hσY p (θC z hzk hV hzV U N p c) := by
  funext j
  exact compat_aux z hzk hzV N (face₁ A) (τz z hzk) (faceYB A) (hcommY z hzk hzV) hg₁ hσY hnY
    _ _ _ _ _ _ _ _ (c.1 _)

/-- Restriction to the fibre intertwines the face map along `A × e` with its fibre analogue. -/
theorem θD_phiX (hnX : NormX z hzk hzV N (g₂ := g₂) (σX := σX)) (p : ℕ) (c : CX hV U N p) :
    θD z hzk hzV U p (phiX hV U ha₀ N hg₂ p c) =
      fibX U ha₀ hσX p (θC z hzk hV hzV U N p c) := by
  funext j
  exact compat_aux z hzk hzV N (face₂ A) (τz z hzk) (faceXB A) (hcommX z hzk hzV) hg₂ hσX hnX
    _ _ _ _ _ _ _ _ (c.1 _)

include hg₁ hg₂ hσY hσX in
/-- **The cone conditions after base change to a rational point with trivial fibre.** -/
theorem transfer_at [Finite ι] [IsSeparated (chartMap hV)] [(chartModule N V).IsQuasicoherent]
    (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i))
    (hUaff : ∀ ab, IsAffineOpen (chartCover U V ab))
    (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
    (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop))
    (hBc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ (A ⊗ A).hom.appTop))
    (hnorm : Normalized N (g₁ := g₁) (g₂ := g₂))
    (hnY : NormY z hzk hzV N (g₁ := g₁) (σY := σY))
    (hnX : NormX z hzk hzV N (g₂ := g₂) (σX := σX)) :
    letI : Algebra (chartRing V) k := (evz z hzV).toAlgebra
    (SurjZero (d₀ hV U N) (targetD V U ha₀) (phi₀ hV U ha₀ N hg₁ hg₂) k ∧
      InjOne (d₀ hV U N) (d₁ hV U N) (targetD V U ha₀) (phi₁ hV U ha₀ N hg₁ hg₂) k) ∧
    LinearMap.ker ((coneD₀ (d₀ hV U N) (phi₀ hV U ha₀ N hg₁ hg₂)).baseChange k) = ⊥ := by
  let : Algebra (chartRing V) k := (evz z hzV).toAlgebra
  let := fibMod U (G := fibreModule z hzk hzV N) 0
  let := fibMod U (G := fibreModule z hzk hzV N) 1
  let := fibMod U (G := fibreModule z hzk hzV N) 2
  let := Stacks.Cech.baseAlternatingModule (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 0
  let := Stacks.Cech.baseAlternatingModule (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 1
  let := Stacks.Cech.baseAlternatingModule (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 2
  have := Stacks.Cech.isScalarTowerBaseAlternating (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 0
  have := Stacks.Cech.isScalarTowerBaseAlternating (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 1
  have := Stacks.Cech.isScalarTowerBaseAlternating (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 2
  let := cochainModule U A.hom 0
  let := cochainModule U A.hom 1
  let := rawEvModule z hzV U 0
  let := rawEvModule z hzV U 1
  have := isScalarTower_rawEv' z hzV U 0 (V := V)
  have := isScalarTower_rawEv' z hzV U 1 (V := V)
  have hC0 := isBaseChange_θC z hzk hV hzV U N hUaff 0
  have hC1 := isBaseChange_θC z hzk hV hzV U N hUaff 1
  have hC2 := isBaseChange_θC z hzk hV hzV U N hUaff 2
  have hD0' := isBaseChange_θD z hzk hzV U (hV := hV) hU 0
  have hD1' := isBaseChange_θD z hzk hzV U (hV := hV) hU 1
  have hD0 := hD0'.prodMap _ _ hD0'
  have hD1 := hD1'.prodMap _ _ (hD1'.prodMap _ _ (IsBaseChange.linearMap (chartRing V) k))
  have hd₀ : ((fd U (G := fibreModule z hzk hzV N) 0).restrictScalars (chartRing V)) ∘ₗ
      θC z hzk hV hzV U N 0 = θC z hzk hV hzV U N 1 ∘ₗ d₀ hV U N :=
    LinearMap.ext fun c => θC_d z hzk hV hzV U N 0 c
  have hd₁ : ((fd U (G := fibreModule z hzk hzV N) 1).restrictScalars (chartRing V)) ∘ₗ
      θC z hzk hV hzV U N 1 = θC z hzk hV hzV U N 2 ∘ₗ d₁ hV U N :=
    LinearMap.ext fun c => θC_d z hzk hV hzV U N 1 c
  have hδ₀ : ((fibδ U ha₀).restrictScalars (chartRing V)) ∘ₗ
      ((θD z hzk hzV U 0).prodMap (θD z hzk hzV U 0)) =
      ((θD z hzk hzV U 1).prodMap ((θD z hzk hzV U 1).prodMap
        (Algebra.linearMap (chartRing V) k))) ∘ₗ targetD V U ha₀ := by
    refine LinearMap.ext fun uw => Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact (θD_faceD z hzk hzV U 0 uw.1).symm
    · exact (θD_faceD z hzk hzV U 0 uw.2).symm
    · show evE U ha₀ (θD z hzk hzV U 0 uw.1) - evE U ha₀ (θD z hzk hzV U 0 uw.2) =
        evz z hzV (evalE V U ha₀ uw.1 - evalE V U ha₀ uw.2)
      rw [map_sub, evz_evalE z hzk hzV U ha₀, evz_evalE z hzk hzV U ha₀]
  have hφ₀ : ((fibφ₀ U ha₀ hσY hσX).restrictScalars (chartRing V)) ∘ₗ θC z hzk hV hzV U N 0 =
      ((θD z hzk hzV U 0).prodMap (θD z hzk hzV U 0)) ∘ₗ phi₀ hV U ha₀ N hg₁ hg₂ := by
    refine LinearMap.ext fun c => Prod.ext ?_ ?_
    · exact (θD_phiY z hzk hV hzV U N ha₀ hg₁ hσY hnY 0 c).symm
    · exact (θD_phiX z hzk hV hzV U N ha₀ hg₂ hσX hnX 0 c).symm
  have hφ₁ : ((fibφ₁ U ha₀ hσY hσX).restrictScalars (chartRing V)) ∘ₗ θC z hzk hV hzV U N 1 =
      ((θD z hzk hzV U 1).prodMap ((θD z hzk hzV U 1).prodMap
        (Algebra.linearMap (chartRing V) k))) ∘ₗ phi₁ hV U ha₀ N hg₁ hg₂ := by
    refine LinearMap.ext fun c => Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact (θD_phiY z hzk hV hzV U N ha₀ hg₁ hσY hnY 1 c).symm
    · exact (θD_phiX z hzk hV hzV U N ha₀ hg₂ hσX hnX 1 c).symm
    · show (0 : k) = evz z hzV 0
      rw [map_zero]
  have hR := phi₁_comp_d₀ hV U ha₀ N hg₁ hg₂ hnorm
  have hchain : ∀ x, fibδ U ha₀ (fibφ₀ U ha₀ hσY hσX x) =
      fibφ₁ U ha₀ hσY hσX (fd U (G := fibreModule z hzk hzV N) 0 x) := by
    have := hC0.algHom_ext ((fibδ U ha₀).comp (fibφ₀ U ha₀ hσY hσX))
      ((fibφ₁ U ha₀ hσY hσX).comp (fd U (G := fibreModule z hzk hzV N) 0)) fun c => by
        have e1 := LinearMap.congr_fun hφ₀ c
        have e2 := LinearMap.congr_fun hδ₀ (phi₀ hV U ha₀ N hg₁ hg₂ c)
        have e3 := LinearMap.congr_fun hR c
        have e4 := LinearMap.congr_fun hφ₁ (d₀ hV U N c)
        have e5 := LinearMap.congr_fun hd₀ c
        exact (congrArg (fibδ U ha₀) e1).trans (e2.trans ((congrArg
          ((θD z hzk hzV U 1).prodMap ((θD z hzk hzV U 1).prodMap
            (Algebra.linearMap (chartRing V) k))) e3.symm).trans
          (e4.symm.trans (congrArg (fibφ₁ U ha₀ hσY hσX) e5.symm))))
    exact LinearMap.congr_fun this
  refine ⟨⟨Stacks.ConeTransfer.surjZero_of hC0 hC1 hD0 hD1 hd₀ hδ₀ hφ₀
    (fib_surjZero U ha₀ hσY hσX hAc hUcov hchain),
    Stacks.ConeTransfer.injOne_of hC0 hC1 hC2 hD0 hD1 hd₀ hd₁ hδ₀ hφ₁
    (fib_injOne U ha₀ hσY hσX hAc hU hUcov hchain)⟩,
    Stacks.ConeTransfer.ker_coneD₀_baseChange_eq_bot_of hC0 hC1 hD0 hd₀ hφ₀
    (fib_injZero U ha₀ hσY hσX hAc hUcov hBc)⟩

omit [GrpObj A] [Fintype ι] [DecidableEq ι] in
/-- **Vanishing of `H⁰` after base change to a rational point whose fibre has no sections.** -/
theorem ker_d₀_evz [Finite ι] [IsSeparated (chartMap hV)] [(chartModule N V).IsQuasicoherent]
    (hUaff : ∀ ab, IsAffineOpen (chartCover U V ab))
    (hUcov : (⊤ : A.left.Opens) = ⨆ a, U a)
    (hAc : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop))
    (h0 : ∀ s : Γ(fibreModule z hzk hzV N, ⊤), s = 0) :
    letI : Algebra (chartRing V) k := (evz z hzV).toAlgebra
    LinearMap.ker ((d₀ hV U N).baseChange k) = ⊥ := by
  let : Algebra (chartRing V) k := (evz z hzV).toAlgebra
  let := fibMod U (G := fibreModule z hzk hzV N) 0
  let := fibMod U (G := fibreModule z hzk hzV N) 1
  let := Stacks.Cech.baseAlternatingModule (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 0
  let := Stacks.Cech.baseAlternatingModule (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 1
  have := Stacks.Cech.isScalarTowerBaseAlternating (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 0
  have := Stacks.Cech.isScalarTowerBaseAlternating (jzV z hzk hzV) (coverB U) (chartModule N V)
    (evz z hzV) (A ⊗ A).hom 1
  have hC0 := isBaseChange_θC z hzk hV hzV U N hUaff 0
  have hC1 := isBaseChange_θC z hzk hV hzV U N hUaff 1
  have hd₀ : ((fd U (G := fibreModule z hzk hzV N) 0).restrictScalars (chartRing V)) ∘ₗ
      θC z hzk hV hzV U N 0 = θC z hzk hV hzV U N 1 ∘ₗ d₀ hV U N :=
    LinearMap.ext fun c => θC_d z hzk hV hzV U N 0 c
  exact Stacks.ConeTransfer.ker_baseChange_eq_bot_of hC0 hC1 hd₀
    (fib_kerZero U hAc hUcov h0)

end Stacks.Cube

end
