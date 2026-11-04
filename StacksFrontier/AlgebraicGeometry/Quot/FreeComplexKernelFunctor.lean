module

public import StacksFrontier.AlgebraicGeometry.Quot.MatrixKernelFunctor

/-!
# The degree-zero sections of a split complex of free modules

Let `c` be a scheme of the big fppf site and `P` a complex of `𝒪`-modules on it whose terms in
degrees `-1`, `0`, `1` are free, with differentials `D₁ : 𝒪^{n₁} → 𝒪^{n₀}` and
`D₀ : 𝒪^{n₀} → 𝒪^m` given by matrices of functions.  If the cokernel of `D₁` is split by matrices
`q`, `s`, `t` (`D₁ q = 0`, `s q = 1`, `q s + t D₁ = 1`), the degree-zero cohomology module
`Coker(D₁)` is `𝒪^r`, and the degree-zero sections functor of `P` is the kernel functor of the
matrix `s D₀`.

## Main definitions

* `AlgebraicGeometry.Space.opcyclesFreeIso`: `Coker(D₁) ≅ 𝒪^r`.
* `AlgebraicGeometry.Space.degreeZeroSectionsMatKerIso`: the degree-zero sections functor of `P`
  is the kernel functor of `s D₀`.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {c : BigFppfOver B S hS}

section Opcycles

variable (P : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj c)) ℤ)
  {n₁ n₀ r : ℕ} (e₁ : P.X (-1) ≅ freeObj (unitT c) n₁) (e₀ : P.X 0 ≅ freeObj (unitT c) n₀)
  (D₁ : Matrix (Fin n₁) (Fin n₀) (Gam c)) (hd : P.d (-1) 0 = e₁.hom ≫ matMap c D₁ ≫ e₀.inv)
  (q : Matrix (Fin n₀) (Fin r) (Gam c)) (s : Matrix (Fin r) (Fin n₀) (Gam c))
  (t : Matrix (Fin n₀) (Fin n₁) (Gam c)) (h₁ : D₁ * q = 0) (h₂ : s * q = 1)
  (h₃ : q * s + t * D₁ = 1)

include hd h₁ in
/-- If `D₁ q = 0`, then the differential `P⁻¹ ⟶ P⁰` followed by `q : 𝒪^{n₀} → 𝒪^r` is zero. -/
theorem d_comp_matMap_eq_zero : P.d (-1) 0 ≫ e₀.hom ≫ matMap c q = 0 := by
  rw [hd, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← matMap_mul, h₁, matMap_zero,
    comp_zero]

/-- **The degree-zero cohomology module of a split complex of free modules is free**: the
opcycles in degree `0`, the cokernel of `D₁`, are `𝒪^r`. -/
def opcyclesFreeIso : P.opcycles 0 ≅ freeObj (unitT c) r where
  hom := P.descOpcycles (e₀.hom ≫ matMap c q) (-1) (by simp)
    (d_comp_matMap_eq_zero P e₁ e₀ D₁ hd q h₁)
  inv := matMap c s ≫ e₀.inv ≫ P.pOpcycles 0
  hom_inv_id := by
    rw [← cancel_epi (P.pOpcycles 0), HomologicalComplex.p_descOpcycles_assoc, Category.assoc,
      Category.comp_id, ← Category.assoc (matMap c q), ← matMap_mul]
    have : matMap c (q * s) = 𝟙 _ - matMap c t ≫ matMap c D₁ := by
      rw [← matMap_mul, ← matMap_one, ← h₃, matMap_add, add_sub_cancel_right]
    rw [this, Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, Iso.hom_inv_id_assoc]
    have hz : e₀.hom ≫ (matMap c t ≫ matMap c D₁) ≫ e₀.inv ≫ P.pOpcycles 0 = 0 := by
      have : e₀.hom ≫ (matMap c t ≫ matMap c D₁) ≫ e₀.inv ≫ P.pOpcycles 0 =
          (e₀.hom ≫ matMap c t ≫ e₁.inv) ≫ P.d (-1) 0 ≫ P.pOpcycles 0 := by
        rw [hd]; simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [this, HomologicalComplex.d_pOpcycles, comp_zero]
    rw [hz, sub_zero]
  inv_hom_id := by
    rw [Category.assoc, Category.assoc, HomologicalComplex.p_descOpcycles, Iso.inv_hom_id_assoc,
      ← matMap_mul, h₂, matMap_one]

/-- The projection `P⁰ ⟶ Coker(D₁)` followed by `opcyclesFreeIso` is `q : 𝒪^{n₀} → 𝒪^r`. -/
@[reassoc (attr := simp)]
theorem pOpcycles_opcyclesFreeIso_hom :
    P.pOpcycles 0 ≫ (opcyclesFreeIso P e₁ e₀ D₁ hd q s t h₁ h₂ h₃).hom = e₀.hom ≫ matMap c q :=
  HomologicalComplex.p_descOpcycles _ _ _ (by simp) (d_comp_matMap_eq_zero P e₁ e₀ D₁ hd q h₁)

variable {m : ℕ} (e₁' : P.X 1 ≅ freeObj (unitT c) m) (D₀ : Matrix (Fin n₀) (Fin m) (Gam c))
  (hd₀ : P.d 0 1 = e₀.hom ≫ matMap c D₀ ≫ e₁'.inv)

include hd₀ in
/-- Under `Coker(D₁) ≅ 𝒪^r` and `P¹ ≅ 𝒪^m`, the map `Coker(D₁) ⟶ P¹` induced by `D₀` is the
matrix `s D₀`. -/
theorem fromOpcycles_comp_eq :
    P.fromOpcycles 0 1 ≫ e₁'.hom =
      (opcyclesFreeIso P e₁ e₀ D₁ hd q s t h₁ h₂ h₃).hom ≫ matMap c (s * D₀) := by
  rw [← Iso.cancel_iso_inv_left (opcyclesFreeIso P e₁ e₀ D₁ hd q s t h₁ h₂ h₃),
    Iso.inv_hom_id_assoc]
  show (matMap c s ≫ e₀.inv ≫ P.pOpcycles 0) ≫ P.fromOpcycles 0 1 ≫ e₁'.hom = _
  rw [Category.assoc, Category.assoc, HomologicalComplex.p_fromOpcycles_assoc, hd₀]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, matMap_mul]

/-- **The degree-zero sections functor of a split complex of free modules is the kernel functor
of a matrix**: with `Coker(D₁) ≅ 𝒪^r` read through `q` and `s`, it is the kernel functor of
`s D₀`. -/
def degreeZeroSectionsMatKerIso :
    degreeZeroSectionsFunctor (schemesOverCone ((schemeSpaceFunctor B S hS).obj c)) P ≅
      matKerFunctor c (s * D₀) :=
  (toposModulePullbackData B S hS).relKerIso (toposModulePullbackData_isCoherent B S hS) _
    (Iso.refl _) (P.fromOpcycles 0 1) (matMap c (s * D₀))
    (opcyclesFreeIso P e₁ e₀ D₁ hd q s t h₁ h₂ h₃) e₁'
    (fromOpcycles_comp_eq P e₁ e₀ D₁ hd q s t h₁ h₂ h₃ e₁' D₀ hd₀)

end Opcycles

section Exactness

variable {T : BigFppfOver B S hS}
  (F : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj T)) ℤ)
  {n₂ n₁ n₀ : ℕ} (e₂ : F.X (-2) ≅ freeObj (unitT T) n₂) (e₁ : F.X (-1) ≅ freeObj (unitT T) n₁)
  (e₀ : F.X 0 ≅ freeObj (unitT T) n₀) (D₂ : Matrix (Fin n₂) (Fin n₁) (Gam T))
  (D₁ : Matrix (Fin n₁) (Fin n₀) (Gam T))
  (hd₂ : F.d (-2) (-1) = e₂.hom ≫ matMap T D₂ ≫ e₁.inv)
  (hd₁ : F.d (-1) 0 = e₁.hom ≫ matMap T D₁ ≫ e₀.inv)

/-- A vector `x` is in the kernel of `D` exactly when the morphism `𝒪 ⟶ 𝒪^n` of `x` is killed by
`D`. -/
theorem comp_matMap_eq_zero_iff {n m : ℕ} (x : unitT T ⟶ freeObj (unitT T) n)
    (M : Matrix (Fin n) (Fin m) (Gam T)) :
    x ≫ matMap T M = 0 ↔ freePointEquiv T n x ᵥ* M = 0 := by
  rw [← freePointEquiv_comp_matMap, ← freePointEquiv_zero T m]
  exact (freePointEquiv T m).injective.eq_iff.symm

include hd₂ hd₁ in
/-- **Vanishing of `H⁻¹` of a complex of free modules makes the kernel of `D₁` orthogonal to the
kernel of `D₂`.**  If `H⁻¹` of `𝒪^{n₂} → 𝒪^{n₁} → 𝒪^{n₀}` vanishes, then every row vector `x`
with `x D₁ = 0` and every column vector `l` with `D₂ l = 0` satisfy `x · l = 0`. -/
theorem dotProduct_eq_zero_of_isZero_homology (hz : IsZero (F.homology (-1)))
    (x : Fin n₁ → Gam T) (hx : x ᵥ* D₁ = 0) (l : Fin n₁ → Gam T) (hl : D₂ *ᵥ l = 0) :
    x ⬝ᵥ l = 0 := by
  let X := (freePointEquiv T n₁).symm x
  let L : Matrix (Fin n₁) (Fin 1) (Gam T) := fun i _ => l i
  let lm : freeObj (unitT T) n₁ ⟶ unitT T :=
    matMap T L ≫ biproduct.π (fun _ : Fin 1 => unitT T) 0
  have hX : X ≫ matMap T D₁ = 0 := by
    rw [comp_matMap_eq_zero_iff, Equiv.apply_symm_apply, hx]
  have hL : D₂ * L = 0 := by
    ext i k
    have := congrFun hl i
    rw [Matrix.mul_apply]
    simpa [L, Matrix.mulVec, dotProduct] using this
  have hex : F.ExactAt (-1) := (F.exactAt_iff_isZero_homology (-1)).mpr hz
  have hex' := (F.exactAt_iff' (-2) (-1) 0 (by simp) (by simp)).mp hex
  let S := F.sc' (-2) (-1) 0
  have hgl : S.f ≫ e₁.hom ≫ lm = 0 := by
    show F.d (-2) (-1) ≫ e₁.hom ≫ lm = 0
    rw [hd₂, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc (matMap T D₂),
      ← matMap_mul, hL, matMap_zero, zero_comp, comp_zero]
  have hi : S.iCycles ≫ e₁.hom ≫ lm = 0 := by
    have := hex'.epi_toCycles
    rw [← cancel_epi S.toCycles, ← Category.assoc, S.toCycles_i, hgl, comp_zero]
  have hXg : (X ≫ e₁.inv) ≫ S.g = 0 := by
    show (X ≫ e₁.inv) ≫ F.d (-1) 0 = 0
    rw [hd₁, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hX, zero_comp]
  have hzero : X ≫ lm = 0 := by
    have h1 : X ≫ lm = S.liftCycles (X ≫ e₁.inv) hXg ≫ S.iCycles ≫ e₁.hom ≫ lm := by
      rw [S.liftCycles_i_assoc]
      exact (congrArg (X ≫ ·) (Iso.inv_hom_id_assoc e₁ lm)).symm.trans (Category.assoc _ _ _).symm
    rw [h1, hi, comp_zero]
  have hval : freePointEquiv T 1 (X ≫ matMap T L) 0 = x ⬝ᵥ l := by
    rw [freePointEquiv_comp_matMap, Equiv.apply_symm_apply]
    simp [Matrix.vecMul, dotProduct, L]
  rw [← hval]
  show unitEndValueHom T ((X ≫ matMap T L) ≫ biproduct.π _ 0) = 0
  rw [Category.assoc]
  show unitEndValueHom T (X ≫ lm) = 0
  rw [hzero, map_zero]

end Exactness

end AlgebraicGeometry.Space

end
