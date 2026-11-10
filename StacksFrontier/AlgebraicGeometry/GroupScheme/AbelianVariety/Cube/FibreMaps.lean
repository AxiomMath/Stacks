module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.Cube.Fibre

/-!
# The theorem of the cube: restriction of the chart complexes to a fibre

For a rational point `z` of an affine open `V ⊆ A`, restriction along `τ_z : y ↦ (y, z)` exhibits
functions on `U_j` as the base change along `ev_z` of functions on `U_j × V`
(`Stacks.Cube.isBaseChange_θD`), and pullback along `j_z` exhibits the alternating Čech cochains of
`j_z^* N` on `A × A` as the base change of the chart complex (`Stacks.Cube.isBaseChange_θC`).

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CartesianMonoidalCategory MonoidalCategory
open scoped TensorProduct

universe u

namespace Stacks.Cube

open Stacks.KunnethCech Stacks.TrivialGenerator

variable {k : Type u} [Field k] {A : Over (Spec (.of k))}

attribute [local instance] faceModule chartAlgebra secAlg secAlgB

section ThetaD

variable (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) {V : A.left.Opens}
  (hzV : z ⁻¹ᵁ V = ⊤) {ι : Type u} (U : ι → A.left.Opens)

include hzV in
/-- The intersection `U_j` lies in the preimage of `U_j × V` under `τz`. -/
theorem le_τz {n : ℕ} (j : Fin n → ι) :
    CechCochains.inter U j ≤ τz z hzk ⁻¹ᵁ faceOpen V U j := by
  intro x hx
  refine ⟨?_, ?_⟩
  · change (τz z hzk ≫ bx A) x ∈ CechCochains.inter U j
    rw [τz_bx]; exact hx
  · change (τz z hzk ≫ bz A) x ∈ V
    rw [τz_bz, Scheme.Hom.comp_apply]
    have : A.hom x ∈ z ⁻¹ᵁ V := by rw [hzV]; trivial
    exact this

/-- The ring of the chart acting on `k` through evaluation at `z`. -/
@[instance_reducible]
noncomputable def evAlg : Algebra (chartRing V) k := (evz z hzV).toAlgebra

/-- The ring of the chart acting on raw cochains of `A` through evaluation at `z`. -/
@[instance_reducible]
noncomputable def rawEvModule (p : ℕ) : Module (chartRing V) (RawCochain U p) :=
  letI := cochainModule U A.hom p
  Module.compHom _ (evz z hzV)

/-- Restriction of a face cochain to the fibre over `z`. -/
noncomputable def θDfun (p : ℕ) (F : FaceCochain V U p) : RawCochain U p := fun j =>
  (τz z hzk).appLE _ _ (le_τz z hzk hzV U j) (F j)

/-- Restricting along `τz` the pullback along `bz` of a function `a` on `V` gives the constant
function with value `evz z hzV a`. -/
theorem τz_appLE_bz (W : (B A).Opens) (h1 : W ≤ bz A ⁻¹ᵁ V) (O : A.left.Opens)
    (h2 : O ≤ τz z hzk ⁻¹ᵁ W) (a : chartRing V) :
    (τz z hzk).appLE W O h2 ((bz A).appLE V W h1 a) =
      (Stacks.Cech.baseRingHom A.hom O).hom (evz z hzV a) := by
  rw [appLE_comp, appLE_congr (τz_bz z hzk)]
  have h3 : (A.hom ≫ z).appLE V O (τz_bz z hzk ▸
      (h2.trans (Scheme.Hom.preimage_mono _ h1))) a =
      A.hom.appLE ⊤ O (Stacks.AffineProduct.le_preimage_top _ _)
        (z.appLE V ⊤ (le_top_preimage_z z hzV) a) := by
    rw [appLE_comp]
  refine h3.trans ?_
  rw [Stacks.Cech.baseRingHom_eq_appLE A.hom O (Stacks.AffineProduct.le_preimage_top _ _)]
  change _ = A.hom.appLE ⊤ O _ ((Scheme.ΓSpecIso (.of k)).inv
    ((Scheme.ΓSpecIso (.of k)).hom (z.appLE V ⊤ _ a)))
  rw [Iso.hom_inv_id_apply]

/-- Restriction of face cochains to the fibre over `z`, as a semilinear map. -/
noncomputable def θD (p : ℕ) :
    letI := rawEvModule z hzV U p
    FaceCochain V U p →ₗ[chartRing V] RawCochain U p :=
  letI := cochainModule U A.hom p
  letI := rawEvModule z hzV U p
  { toFun := θDfun z hzk hzV U p
    map_add' := fun F G => by funext j; exact map_add _ _ _
    map_smul' := fun a F => by
      funext j
      change (τz z hzk).appLE _ _ _ (faceAct V U j a * F j) =
        (Stacks.Cech.baseRingHom A.hom _).hom (evz z hzV a) * θDfun z hzk hzV U p F j
      rw [map_mul]
      congr 1
      exact τz_appLE_bz z hzk hzV _ _ _ _ a }

/-- Each component of `θD` is restriction along `τz`. -/
theorem θD_apply (p : ℕ) (F : FaceCochain V U p) (j : Fin (p + 1) → ι) :
    letI := rawEvModule z hzV U p
    θD z hzk hzV U p F j = (τz z hzk).appLE _ _ (le_τz z hzk hzV U j) (F j) := rfl

/-- Restricting `faceψ V U p f` to the fibre over `z` recovers `f`. -/
theorem θD_faceψ (p : ℕ) (f : RawCochain U p) :
    letI := cochainModule U A.hom p
    letI := rawEvModule z hzV U p
    θD z hzk hzV U p (faceψ V U p f) = f := by
  funext j
  rw [θD_apply, faceψ_apply, appLE_comp, appLE_congr (τz_bx z hzk), id_appLE_self]

/-- Restriction to the fibre over `z` commutes with the Čech differentials. -/
theorem θD_faceD (p : ℕ) (F : FaceCochain V U p) :
    letI := cochainModule U A.hom p
    letI := rawEvModule z hzV U p
    θD z hzk hzV U (p + 1) (faceD V U p F) = rawD U p (θD z hzk hzV U p F) := by
  funext j
  rw [θD_apply, faceD_apply, rawD, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, θD_apply, appLE_res, res_appLE]

include hzk in
/-- The scalar tower `k → chartRing V → k`, with `chartRing V` acting on `k` through `evz`. -/
theorem isScalarTower_evAlg :
    letI := evAlg z hzV (V := V)
    IsScalarTower k (chartRing V) k :=
  let := evAlg z hzV (V := V)
  IsScalarTower.of_algebraMap_eq fun c => (evz_algebraMap z hzk hzV c).symm

include hzk in
/-- The scalar tower `k → chartRing V → RawCochain U p`, with `chartRing V` acting through
`evz`. -/
theorem isScalarTower_rawEv (p : ℕ) :
    letI := cochainModule U A.hom p
    letI := rawEvModule z hzV U p
    IsScalarTower k (chartRing V) (RawCochain U p) :=
  let := cochainModule U A.hom p
  let := rawEvModule z hzV U p
  IsScalarTower.of_algebraMap_smul fun c x => by
    change evz z hzV (algebraMap k (chartRing V) c) • x = c • x
    rw [show algebraMap k (chartRing V) c = (Stacks.Cech.baseRingHom A.hom V).hom c from rfl,
      evz_algebraMap z hzk hzV]

/-- The scalar tower `chartRing V → k → RawCochain U p`, with `chartRing V` acting through
`evz`. -/
theorem isScalarTower_rawEv' (p : ℕ) :
    letI := cochainModule U A.hom p
    letI := rawEvModule z hzV U p
    letI := evAlg z hzV (V := V)
    IsScalarTower (chartRing V) k (RawCochain U p) :=
  let := cochainModule U A.hom p
  let := rawEvModule z hzV U p
  let := evAlg z hzV (V := V)
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

variable {hV : IsAffineOpen V}

include hV hzk in
/-- **Functions on the faces restrict to functions on the fibre by base change.** -/
theorem isBaseChange_θD [Finite ι]
    (hU : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsAffineOpen (CechCochains.inter U i)) (p : ℕ) :
    letI := cochainModule U A.hom p
    letI := rawEvModule z hzV U p
    letI := evAlg z hzV (V := V)
    haveI := isScalarTower_rawEv' z hzV U p (V := V)
    IsBaseChange k (θD z hzk hzV U p) := by
  let := cochainModule U A.hom p
  let := rawEvModule z hzV U p
  let := evAlg z hzV (V := V)
  have := isScalarTower_evAlg z hzk hzV (V := V)
  have := isScalarTower_rawEv z hzk hzV U p
  have := isScalarTower_rawEv' z hzV U p (V := V)
  refine IsBaseChange.of_comp (isBaseChange_faceψ U hV hU p) ?_
  have : ((θD z hzk hzV U p).restrictScalars k ∘ₗ faceψ V U p) =
      (LinearEquiv.refl k (RawCochain U p)).toLinearMap := by
    refine LinearMap.ext fun f => ?_
    exact θD_faceψ z hzk hzV U p f
  rw [this]
  exact IsBaseChange.ofEquiv _

end ThetaD

/-! ### Pulling back along a map into an open subscheme -/

section Restrict

/-- The pullback of a restriction to an open subscheme is the pullback along the composite. -/
noncomputable def restrictPullbackIso {Y X' X : Scheme.{u}} (f : Y ⟶ X') (ι : X' ⟶ X)
    [IsOpenImmersion ι] (M : X.Modules) :
    (Scheme.Modules.pullback f).obj (M.restrict ι) ≅ (Scheme.Modules.pullback (f ≫ ι)).obj M :=
  (Scheme.Modules.pullback f).mapIso ((Scheme.Modules.restrictFunctorIsoPullback ι).app M) ≪≫
    (Scheme.Modules.pullbackComp f ι).app M

/-- On sections over `O'`, the isomorphism `restrictFunctorIsoPullback ι` sends a section of `M`
over `ι ''ᵁ O'` to its pullback along `ι`. -/
theorem restrictFunctorIsoPullback_hom_app {X' X : Scheme.{u}} (ι : X' ⟶ X) [IsOpenImmersion ι]
    (M : X.Modules) (O' : X'.Opens) (c : Γ(M.restrict ι, O')) :
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M) O' c =
      pbS ι M (ι ''ᵁ O') O' (ι.preimage_image_eq O').ge c := by
  have h := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection ι M (ι ''ᵁ O') O'
    (ι.preimage_image_eq O').ge le_rfl c
  have h' : M.val.map (homOfLE (le_refl (ι ''ᵁ O'))).op c = c := by
    change M.presheaf.map (𝟙 _) c = c
    rw [CategoryTheory.Functor.map_id]; rfl
  rw [h'] at h
  conv_lhs => rw [← h]
  change (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback ι).inv.app M) O' ≫
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M) O') _ = _
  rw [← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id_app]
  simp only [Scheme.Modules.Hom.id_app]
  rfl

/-- **Pulling back a section of a restriction is pulling back along the composite.** -/
theorem pbS_restrict {Y X' X : Scheme.{u}} (f : Y ⟶ X') (ι : X' ⟶ X) [IsOpenImmersion ι]
    (M : X.Modules) (O' : X'.Opens) (W : Y.Opens) (h : W ≤ f ⁻¹ᵁ O')
    (h' : W ≤ (f ≫ ι) ⁻¹ᵁ (ι ''ᵁ O')) (c : Γ(M.restrict ι, O')) :
    Scheme.Modules.Hom.app (restrictPullbackIso f ι M).hom W (pbS f (M.restrict ι) O' W h c) =
      pbS (f ≫ ι) M (ι ''ᵁ O') W h' c := by
  let c' : Γ(M, ι ''ᵁ O') := c
  have hn : Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map
      ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M)) W
      (pbS f (M.restrict ι) O' W h c) =
      pbS f ((Scheme.Modules.pullback ι).obj M) O' W h
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M) O' c) :=
    Scheme.Modules.pullbackSection_naturality f
      ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M) O' W h c
  have h2 : Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M) O' c =
      pbS ι M (ι ''ᵁ O') O' (ι.preimage_image_eq O').ge c' :=
    restrictFunctorIsoPullback_hom_app ι M O' c
  change Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp f ι).hom.app M) W
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullback f).map
      ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M)) W
      (pbS f (M.restrict ι) O' W h c)) = pbS (f ≫ ι) M (ι ''ᵁ O') W h' c'
  rw [hn, h2]
  exact pbS_comp f ι M (ι ''ᵁ O') O' W _ h h' c'

end Restrict

/-! ### The chart complex restricted to the fibre -/

section ThetaC

variable (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) {V : A.left.Opens}
  (hV : IsAffineOpen V) (hzV : z ⁻¹ᵁ V = ⊤) {ι : Type u} (U : ι → A.left.Opens)
  (N : (P A).Modules)

/-- The member `coverB U ab` of the product cover of `A × A` is the preimage under `jzV` of the
member `chartCover U V ab` of the chart cover. -/
theorem coverB_eq_preimage (ab : ι × ι) :
    coverB U ab = jzV z hzk hzV ⁻¹ᵁ chartCover U V ab := by
  ext x
  change x ∈ coverB U ab ↔ (jzV z hzk hzV ≫ (PV V).ι ≫ q A) x ∈ coverB U ab
  rw [jzV_ι_assoc, jz_q]
  rfl

/-- The pullback of `N` to the fibre over `z`. -/
noncomputable abbrev fibreModule : (B A).Modules :=
  (Scheme.Modules.pullback (jzV z hzk hzV)).obj (chartModule N V)

/-- **Restriction of the chart complex to the fibre over `z`.** -/
noncomputable def θC (p : ℕ) :
    letI := Stacks.Cech.cochainModule (chartMap hV) (chartCover U V) (chartModule N V) p
    letI := Stacks.Cech.cochainModule (A ⊗ A).hom (coverB U) (fibreModule z hzk hzV N) p
    letI := Stacks.Cech.baseAlternatingModule (jzV z hzk hzV) (coverB U) (chartModule N V)
      (evz z hzV) (A ⊗ A).hom p
    Stacks.Cech.alternatingSubmodule (chartMap hV) (chartCover U V) (chartModule N V) p
      →ₗ[chartRing V]
      Stacks.Cech.alternatingSubmodule (A ⊗ A).hom (coverB U) (fibreModule z hzk hzV N) p :=
  Stacks.Cech.alternatingCochainBaseChangeₗ (jzV z hzk hzV) (chartCover U V) (coverB U)
    (Equiv.refl _) (chartModule N V) (coverB_eq_preimage z hzk hzV U) (evz z hzV) (chartMap hV)
    (A ⊗ A).hom (fun W => Stacks.Cech.baseRingHom_comp_app _ _ _ _
      (isPullback_fibre z hzk hV hzV) W) p

/-- Each intersection of the product cover of `A × A` lies in the preimage under `jzV` of the
corresponding intersection of the chart cover. -/
theorem le_inter_coverB {n : ℕ} (i : Fin n → ι × ι) :
    CechCochains.inter (coverB U) i ≤
      jzV z hzk hzV ⁻¹ᵁ CechCochains.inter (chartCover U V) i :=
  (Stacks.Cech.inter_eq_preimage (jzV z hzk hzV) (chartCover U V) (coverB U) (Equiv.refl _)
    (coverB_eq_preimage z hzk hzV U) i).le

/-- Each component of `θC` is pullback of sections along `jzV`. -/
theorem θC_apply (p : ℕ)
    (c : Stacks.Cech.alternatingSubmodule (chartMap hV) (chartCover U V) (chartModule N V) p)
    (i : Fin (p + 1) → ι × ι) :
    (θC z hzk hV hzV U N p c).1 i =
      pbS (jzV z hzk hzV) (chartModule N V) _ _ (le_inter_coverB z hzk hzV U i) (c.1 i) := rfl

/-- The alternating Čech cochains of `fibreModule z hzk hzV N` for the product cover of `A × A`
are the base change along `evz` of the alternating cochains of the chart complex. -/
theorem isBaseChange_θC [Finite ι] [IsSeparated (chartMap hV)] [(chartModule N V).IsQuasicoherent]
    (hUaff : ∀ ab, IsAffineOpen (chartCover U V ab)) (p : ℕ) :
    letI : Algebra (chartRing V) k := (evz z hzV).toAlgebra
    letI := Stacks.Cech.cochainModule (chartMap hV) (chartCover U V) (chartModule N V) p
    letI := Stacks.Cech.cochainModule (A ⊗ A).hom (coverB U) (fibreModule z hzk hzV N) p
    letI := Stacks.Cech.baseAlternatingModule (jzV z hzk hzV) (coverB U) (chartModule N V)
      (evz z hzV) (A ⊗ A).hom p
    letI := Stacks.Cech.isScalarTowerBaseAlternating (jzV z hzk hzV) (coverB U) (chartModule N V)
      (evz z hzV) (A ⊗ A).hom p
    IsBaseChange k (θC z hzk hV hzV U N p) :=
  Stacks.Cech.isBaseChange_alternatingCochainBaseChangeₗ (jzV z hzk hzV) (chartCover U V)
    (coverB U) (Equiv.refl _) (chartModule N V) (coverB_eq_preimage z hzk hzV U) (evz z hzV)
    (chartMap hV) (A ⊗ A).hom (fun W => Stacks.Cech.baseRingHom_comp_app _ _ _ _
      (isPullback_fibre z hzk hV hzV) W) (isPullback_fibre z hzk hV hzV) hUaff p

/-- Two maps `A ⟶ P A` agree if they agree after `q ≫ bx`, `q ≫ bz` and `r`; used for
`τz ≫ g` and `f ≫ jz`. -/
private theorem τz_comp_eq_comp_jz {g : B A ⟶ P A} {f : A.left ⟶ B A}
    (hx : τz z hzk ≫ g ≫ q A ≫ bx A = f ≫ jz z hzk ≫ q A ≫ bx A)
    (hz : τz z hzk ≫ g ≫ q A ≫ bz A = f ≫ jz z hzk ≫ q A ≫ bz A)
    (hr : τz z hzk ≫ g ≫ r A = f ≫ jz z hzk ≫ r A) : τz z hzk ≫ g = f ≫ jz z hzk := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;> simpa

end ThetaC

/-! ### Compatibility of the faces with the fibre -/

section Compat

variable [GrpObj A] (z : Spec (.of k) ⟶ A.left) (hzk : z ≫ A.hom = 𝟙 _) {V : A.left.Opens}
  (hV : IsAffineOpen V) (hzV : z ⁻¹ᵁ V = ⊤) {ι : Type u} (U : ι → A.left.Opens) {a₀ : ι}
  (ha₀ : eA (A := A) ⁻¹ᵁ U a₀ = ⊤) (N : (P A).Modules)

variable (A) in
/-- The face `y ↦ (e, y)` of the fibre `A × A`. -/
noncomputable abbrev faceYB : A.left ⟶ B A := faceY (isPullback_B A) eA eA_hom

variable (A) in
/-- The face `x ↦ (x, e)` of the fibre `A × A`. -/
noncomputable abbrev faceXB : A.left ⟶ B A := faceX (isPullback_B A) eA eA_hom

/-- The maps `τz ≫ face₁` and `faceYB ≫ jzV ≫ (PV V).ι` agree: both send `y` to `(e, y, z)`. -/
theorem hcommY : τz z hzk ≫ face₁ A = faceYB A ≫ jzV z hzk hzV ≫ (PV V).ι := by
  rw [jzV_ι]
  refine τz_comp_eq_comp_jz z hzk ?_ ?_ ?_
  · rw [face₁_q_bx, τz_bx_assoc, jz_q_assoc, faceY_fst]
  · rw [face₁_q_bz, τz_bx, jz_q_assoc, faceY_snd]
  · rw [face₁_r, τz_bz, jz_r]
    change _ = faceYB A ≫ bx A ≫ A.hom ≫ z
    rw [faceY_fst_assoc, ← Category.assoc eA, eA_hom (A := A), Category.id_comp]

/-- The maps `τz ≫ face₂` and `faceXB ≫ jzV ≫ (PV V).ι` agree: both send `y` to `(y, e, z)`. -/
theorem hcommX : τz z hzk ≫ face₂ A = faceXB A ≫ jzV z hzk hzV ≫ (PV V).ι := by
  rw [jzV_ι]
  refine τz_comp_eq_comp_jz z hzk ?_ ?_ ?_
  · rw [face₂_q_bx, τz_bx, jz_q_assoc, faceX_fst]
  · rw [face₂_q_bz, τz_bx_assoc, jz_q_assoc, faceX_snd]
  · rw [face₂_r, τz_bz, jz_r]
    change _ = faceXB A ≫ bx A ≫ A.hom ≫ z
    rw [faceX_fst_assoc]

omit [GrpObj A] in
/-- Given `f₁ ≫ b₁ = f₂ ≫ jzV ≫ (PV V).ι` and generators `g₁` and `σ` with the same pullback to
`A`, the coordinates of a section `x` of the chart module with respect to `g₁` and to `σ`
have the same restriction along `f₁` and `f₂` to `O`. -/
theorem compat_aux {Y₁ : Scheme.{u}} (b₁ : Y₁ ⟶ P A) (f₁ : A.left ⟶ Y₁) (f₂ : A.left ⟶ B A)
    (hcomm : f₁ ≫ b₁ = f₂ ≫ jzV z hzk hzV ≫ (PV V).ι)
    {g₁ : Γ((Scheme.Modules.pullback b₁).obj N, ⊤)} (hg₁ : IsGen _ g₁)
    {σ : Γ(fibreModule z hzk hzV N, ⊤)} (hσ : IsGen _ σ)
    (hnorm : pulledGen₁ N f₁ b₁ f₂ (jzV z hzk hzV ≫ (PV V).ι) hcomm (g₁ := g₁) =
      pulledGen₂ N f₂ (jzV z hzk hzV ≫ (PV V).ι)
        (g₂ := Scheme.Modules.Hom.app (restrictPullbackIso (jzV z hzk hzV) (PV V).ι N).hom ⊤ σ))
    (O' : (PV V).toScheme.Opens) (W₁ : Y₁.Opens) (W₂ : (B A).Opens) (O : A.left.Opens)
    (h₁ : W₁ ≤ b₁ ⁻¹ᵁ ((PV V).ι ''ᵁ O')) (h₂ : W₂ ≤ jzV z hzk hzV ⁻¹ᵁ O')
    (e₁ : O ≤ f₁ ⁻¹ᵁ W₁) (e₂ : O ≤ f₂ ⁻¹ᵁ W₂) (x : Γ(chartModule N V, O')) :
    f₁.appLE W₁ O e₁ (divGen hg₁ W₁ (pbS b₁ N ((PV V).ι ''ᵁ O') W₁ h₁ x)) =
      f₂.appLE W₂ O e₂ (divGen hσ W₂ (pbS (jzV z hzk hzV) (chartModule N V) O' W₂ h₂ x)) := by
  have h₂' : W₂ ≤ (jzV z hzk hzV ≫ (PV V).ι) ⁻¹ᵁ ((PV V).ι ''ᵁ O') := by
    refine h₂.trans ?_
    rw [Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ ((PV V).ι.preimage_image_eq O').ge
  rw [← divGen_app_iso hσ (restrictPullbackIso (jzV z hzk hzV) (PV V).ι N),
    pbS_restrict _ _ N O' W₂ h₂ h₂']
  exact appLE_divGen_eq N f₁ b₁ f₂ (jzV z hzk hzV ≫ (PV V).ι) hcomm hg₁
    (isGen_app_iso hσ _) hnorm _ W₁ W₂ O h₁ h₂' e₁ e₂ x

/-- The points `z ≫ σe` and `eA ≫ τz` of `A × A` agree: both are `(e, z)`. -/
theorem zσe_eq : z ≫ σe = eA ≫ τz z hzk := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, σe_bx, ← Category.assoc, hzk, Category.id_comp, Category.assoc, τz_bx,
      Category.comp_id]
  · rw [Category.assoc, σe_bz, Category.comp_id, Category.assoc, τz_bz, ← Category.assoc,
      eA_hom, Category.id_comp]

attribute [local instance] faceModule

/-- **Evaluation at the identity commutes with restriction to the fibre.** -/
theorem evz_evalE (u : FaceCochain V U 0) :
    letI := cochainModule U A.hom 0
    letI := rawEvModule z hzV U 0
    evz z hzV (evalE V U ha₀ u) =
      evalAt U eA eA_hom a₀ ha₀ (θD z hzk hzV U 0 u) := by
  change (Scheme.ΓSpecIso (.of k)).hom (z.appLE V ⊤ _ (σe.appLE _ V _ (u (fun _ => a₀)))) =
    (Scheme.ΓSpecIso (.of k)).hom (eA.appLE _ ⊤ _ ((τz z hzk).appLE _ _ _ (u (fun _ => a₀))))
  rw [appLE_comp, appLE_comp, appLE_congr (zσe_eq z hzk)]

end Compat

end Stacks.Cube

end
