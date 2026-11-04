module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.Contraction
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProduct

/-!
# The Alexander–Whitney product of Čech cochains on a product of lattices

Let `P` be a presheaf of `k`-modules on a complete lattice `L₁` and `Q` one on `L₂`, with families
`U : ι₁ → L₁` and `V : ι₂ → L₂`. Their external tensor product `P ⊠ Q : (Z₁, Z₂) ↦ P(Z₁) ⊗_k Q(Z₂)`
is a presheaf on `L₁ × L₂`, and `W = U × V : (i, j) ↦ (U_i, V_j)` is a family there. For opens of
two schemes `X`, `Y` over `k` and quasi-coherent `ℱ`, `𝒢`, the sections of `pr₁^*ℱ ⊗ pr₂^*𝒢` over
`U_i × V_j` are `ℱ(U_i) ⊗_k 𝒢(V_j)` on affine opens, so the Čech complex of `W` with values in
`P ⊠ Q` is the Čech complex of the product covering of [Stacks, Tag 0BED].

This file builds the Alexander–Whitney product
`(c ∪ e)_{(s, t)} = c_{s₀ … s_p}| ⊗ e_{t_p … t_{p+q}}|` of a `p`-cochain of `P` and a `q`-cochain
of `Q`, proves the Leibniz rule `d(c ∪ e) = dc ∪ e + (-1)^p c ∪ de`, and deduces the product
`Ȟ^p(U, P) ⊗ Ȟ^q(V, Q) ⟶ Ȟ^{p+q}(U × V, P ⊠ Q)`.

## Main definitions

* `Stacks.CechKunneth.extTensor`: the presheaf `P ⊠ Q` on `L₁ × L₂`.
* `Stacks.CechKunneth.prodCover`: the family `U × V`.
* `Stacks.CechKunneth.cup`: the Alexander–Whitney product of cochains.
* `Stacks.CechKunneth.Hcup`: the induced product on Čech cohomology.

## Main results

* `Stacks.CechKunneth.d_cup`: the Leibniz rule.
* `Stacks.CechKunneth.mapCochain_cup_left`, `mapCochain_cup_right`: naturality.
* `Stacks.CechKunneth.extTensorContraction`: contractions of `P` and `Q` give one of `P ⊠ Q`.

## Implementation notes

The product of the two lattices is the type synonym `Stacks.CechKunneth.LatProd`, so that it is
a category as a preorder; on `L₁ × L₂` itself instance search finds the product of the two
preorder categories first, which is not the category of the preorder `L₁ × L₂`.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct
open Stacks.Cech.LinearCupProduct (frontIdx backIdx frontIdx_val backIdx_val val_succAbove)

universe u

namespace Stacks.CechKunneth

variable {k : Type u} [CommRing k] {L₁ L₂ : Type u} [CompleteLattice L₁] [CompleteLattice L₂]
  {ι₁ ι₂ : Type u}

/-! ### The product of two lattices -/

/-- The product of two lattices. It is a type synonym for `L₁ × L₂`, so that its category
structure is the one of a preorder rather than the product of the two categories. -/
def LatProd (L₁ L₂ : Type u) : Type u := L₁ × L₂

/-- The product lattice structure on `LatProd L₁ L₂`. -/
instance : CompleteLattice (LatProd L₁ L₂) := inferInstanceAs (CompleteLattice (L₁ × L₂))

namespace LatProd

/-- The pair `(Z₁, Z₂)`. -/
def mk (Z₁ : L₁) (Z₂ : L₂) : LatProd L₁ L₂ := (Z₁, Z₂)

/-- The first component. -/
def fst (Z : LatProd L₁ L₂) : L₁ := Prod.fst (α := L₁) (β := L₂) Z

/-- The second component. -/
def snd (Z : LatProd L₁ L₂) : L₂ := Prod.snd (α := L₁) (β := L₂) Z

/-- The first component is monotone. -/
theorem fst_mono {Z Z' : LatProd L₁ L₂} (h : Z ≤ Z') : Z.fst ≤ Z'.fst :=
  (Prod.le_def.1 h).1

/-- The second component is monotone. -/
theorem snd_mono {Z Z' : LatProd L₁ L₂} (h : Z ≤ Z') : Z.snd ≤ Z'.snd :=
  (Prod.le_def.1 h).2

/-- `Z ≤ (Z₁, Z₂)` when `Z.fst ≤ Z₁` and `Z.snd ≤ Z₂`. -/
theorem le_mk {Z : LatProd L₁ L₂} {Z₁ : L₁} {Z₂ : L₂} (h₁ : Z.fst ≤ Z₁) (h₂ : Z.snd ≤ Z₂) :
    Z ≤ mk Z₁ Z₂ :=
  Prod.le_def.2 ⟨h₁, h₂⟩

end LatProd

/-! ### The external tensor product -/

section ExtTensor

variable (P : L₁ᵒᵖ ⥤ ModuleCat.{u} k) (Q : L₂ᵒᵖ ⥤ ModuleCat.{u} k)

/-- **The external tensor product** `P ⊠ Q : (Z₁, Z₂) ↦ P(Z₁) ⊗_k Q(Z₂)`. -/
def extTensor : (LatProd L₁ L₂)ᵒᵖ ⥤ ModuleCat.{u} k where
  obj Z := ModuleCat.of k (P.obj (op Z.unop.fst) ⊗[k] Q.obj (op Z.unop.snd))
  map f := ModuleCat.ofHom (TensorProduct.map (res P (LatProd.fst_mono (leOfHom f.unop)))
    (res Q (LatProd.snd_mono (leOfHom f.unop))))
  map_id Z := ModuleCat.hom_ext (TensorProduct.ext' fun x y => by
    change res P _ x ⊗ₜ res Q _ y = x ⊗ₜ y
    rw [res_self, res_self])
  map_comp f g := ModuleCat.hom_ext <| TensorProduct.ext' fun x y =>
    congrArg₂ (· ⊗ₜ[k] ·) (res_res P _ _ x).symm (res_res Q _ _ y).symm

/-- The restriction of `P ⊠ Q` sends `x ⊗ y` to the tensor product of the restrictions of `x`
and `y`. -/
theorem res_extTensor_tmul {Z Z' : LatProd L₁ L₂} (h : Z ≤ Z') (x : P.obj (op Z'.fst))
    (y : Q.obj (op Z'.snd)) :
    res (extTensor P Q) h (x ⊗ₜ y) =
      res P (LatProd.fst_mono h) x ⊗ₜ res Q (LatProd.snd_mono h) y :=
  rfl

variable {P Q}

/-- `f ⊠ Q` for a morphism `f` of presheaves on `L₁`. -/
def extTensorMapLeft {P' : L₁ᵒᵖ ⥤ ModuleCat.{u} k} (f : P ⟶ P') :
    extTensor P Q ⟶ extTensor P' Q where
  app Z := ModuleCat.ofHom (TensorProduct.map (f.app (op Z.unop.fst)).hom LinearMap.id)
  naturality Z Z' g := ModuleCat.hom_ext (TensorProduct.ext' fun x y => by
    change (f.app _).hom (res P _ x) ⊗ₜ res Q _ y = res P' _ ((f.app _).hom x) ⊗ₜ res Q _ y
    rw [app_res])

/-- `P ⊠ g` for a morphism `g` of presheaves on `L₂`. -/
def extTensorMapRight {Q' : L₂ᵒᵖ ⥤ ModuleCat.{u} k} (g : Q ⟶ Q') :
    extTensor P Q ⟶ extTensor P Q' where
  app Z := ModuleCat.ofHom (TensorProduct.map LinearMap.id (g.app (op Z.unop.snd)).hom)
  naturality Z Z' f := ModuleCat.hom_ext (TensorProduct.ext' fun x y => by
    change res P _ x ⊗ₜ (g.app _).hom (res Q _ y) = res P _ x ⊗ₜ res Q' _ ((g.app _).hom y)
    rw [app_res])

/-- `f ⊠ Q` sends `x ⊗ y` to `f(x) ⊗ y`. -/
theorem extTensorMapLeft_app_tmul {P' : L₁ᵒᵖ ⥤ ModuleCat.{u} k} (f : P ⟶ P')
    (Z : LatProd L₁ L₂) (x : P.obj (op Z.fst)) (y : Q.obj (op Z.snd)) :
    ((extTensorMapLeft (Q := Q) f).app (op Z)).hom (x ⊗ₜ y) = (f.app (op Z.fst)).hom x ⊗ₜ y :=
  rfl

/-- `P ⊠ g` sends `x ⊗ y` to `x ⊗ g(y)`. -/
theorem extTensorMapRight_app_tmul {Q' : L₂ᵒᵖ ⥤ ModuleCat.{u} k} (g : Q ⟶ Q')
    (Z : LatProd L₁ L₂) (x : P.obj (op Z.fst)) (y : Q.obj (op Z.snd)) :
    ((extTensorMapRight (P := P) g).app (op Z)).hom (x ⊗ₜ y) = x ⊗ₜ (g.app (op Z.snd)).hom y :=
  rfl

end ExtTensor

/-! ### The product family -/

section ProdCover

variable (U : ι₁ → L₁) (V : ι₂ → L₂)

/-- **The product family** `U × V : (i, j) ↦ (U_i, V_j)`. -/
def prodCover : ι₁ × ι₂ → LatProd L₁ L₂ := fun ij => LatProd.mk (U ij.1) (V ij.2)

/-- The first component of the intersection of `U × V` along `σ` lies in the intersection of `U`
along the first components of `σ ∘ θ`. -/
theorem fst_inter_prodCover_le {n m : ℕ} (σ : Fin (n + 1) → ι₁ × ι₂)
    (θ : Fin (m + 1) → Fin (n + 1)) :
    (inter (prodCover U V) σ).fst ≤ inter U (Prod.fst ∘ σ ∘ θ) :=
  le_iInf fun j => LatProd.fst_mono (inter_le_apply (prodCover U V) σ (θ j))

/-- The second component of the intersection of `U × V` along `σ` lies in the intersection of `V`
along the second components of `σ ∘ θ`. -/
theorem snd_inter_prodCover_le {n m : ℕ} (σ : Fin (n + 1) → ι₁ × ι₂)
    (θ : Fin (m + 1) → Fin (n + 1)) :
    (inter (prodCover U V) σ).snd ≤ inter V (Prod.snd ∘ σ ∘ θ) :=
  le_iInf fun j => LatProd.snd_mono (inter_le_apply (prodCover U V) σ (θ j))

end ProdCover

/-! ### The Alexander–Whitney product -/

section Cup

variable {P : L₁ᵒᵖ ⥤ ModuleCat.{u} k} {Q : L₂ᵒᵖ ⥤ ModuleCat.{u} k} {U : ι₁ → L₁} {V : ι₂ → L₂}

/-- **The Alexander–Whitney product** of a `p`-cochain of `P` and a `q`-cochain of `Q`, in degree
`n = p + q`: `(c ∪ e)_σ = c_{σ₀ … σ_p}| ⊗ e_{σ_p … σ_n}|`. -/
def cup {p q n : ℕ} (h : p + q = n) :
    Cochain P U p →ₗ[k] Cochain Q V q →ₗ[k] Cochain (extTensor P Q) (prodCover U V) n :=
  LinearMap.mk₂ k
    (fun c e σ => res P (fst_inter_prodCover_le U V σ (frontIdx p n (by omega)))
        (c (Prod.fst ∘ σ ∘ frontIdx p n (by omega))) ⊗ₜ
      res Q (snd_inter_prodCover_le U V σ (backIdx p q n h.le))
        (e (Prod.snd ∘ σ ∘ backIdx p q n h.le)))
    (fun c c' e => funext fun σ => by simp only [Pi.add_apply, map_add, add_tmul]; rfl)
    (fun r c e => funext fun σ => by simp only [Pi.smul_apply, map_smul]; rfl)
    (fun c e e' => funext fun σ => by simp only [Pi.add_apply, map_add, tmul_add]; rfl)
    (fun r c e => funext fun σ => by simp only [Pi.smul_apply, map_smul, tmul_smul]; rfl)

/-- The value of `cup h c e` at `σ`. -/
theorem cup_apply {p q n : ℕ} (h : p + q = n) (c : Cochain P U p) (e : Cochain Q V q)
    (σ : Fin (n + 1) → ι₁ × ι₂) :
    cup h c e σ = res P (fst_inter_prodCover_le U V σ (frontIdx p n (by omega)))
        (c (Prod.fst ∘ σ ∘ frontIdx p n (by omega))) ⊗ₜ
      res Q (snd_inter_prodCover_le U V σ (backIdx p q n h.le))
        (e (Prod.snd ∘ σ ∘ backIdx p q n h.le)) :=
  rfl

/-- The product is natural in the first presheaf: `(f ⊠ Q)(c ∪ e) = f(c) ∪ e`. -/
theorem mapCochain_cup_left {P' : L₁ᵒᵖ ⥤ ModuleCat.{u} k} (f : P ⟶ P') {p q n : ℕ}
    (h : p + q = n) (c : Cochain P U p) (e : Cochain Q V q) :
    mapCochain (prodCover U V) (extTensorMapLeft f) n (cup h c e) =
      cup h (mapCochain U f p c) e := by
  funext σ
  rw [mapCochain_apply, cup_apply, cup_apply, mapCochain_apply, extTensorMapLeft_app_tmul, app_res]

/-- The product is natural in the second presheaf: `(P ⊠ g)(c ∪ e) = c ∪ g(e)`. -/
theorem mapCochain_cup_right {Q' : L₂ᵒᵖ ⥤ ModuleCat.{u} k} (g : Q ⟶ Q') {p q n : ℕ}
    (h : p + q = n) (c : Cochain P U p) (e : Cochain Q V q) :
    mapCochain (prodCover U V) (extTensorMapRight g) n (cup h c e) =
      cup h c (mapCochain V g q e) := by
  funext σ
  rw [mapCochain_apply, cup_apply, cup_apply, mapCochain_apply, extTensorMapRight_app_tmul,
    app_res]

/-- A term of the Leibniz computation: the pure tensor of the restrictions of `c` and `e` along
two tuples, to the member of the nerve of `U × V` selected by `σ`. -/
def leibnizTerm {p q n : ℕ} (c : Cochain P U p) (e : Cochain Q V q) (σ : Fin (n + 1) → ι₁ × ι₂)
    (a : Fin (p + 1) → ι₁) (b : Fin (q + 1) → ι₂) (ha : (inter (prodCover U V) σ).fst ≤ inter U a)
    (hb : (inter (prodCover U V) σ).snd ≤ inter V b) :
    (extTensor P Q).obj (op (inter (prodCover U V) σ)) :=
  res P ha (c a) ⊗ₜ res Q hb (e b)

/-- `leibnizTerm c e σ a b` depends only on the tuples `a` and `b`, not on the inequalities. -/
theorem leibnizTerm_congr {p q n : ℕ} (c : Cochain P U p) (e : Cochain Q V q)
    (σ : Fin (n + 1) → ι₁ × ι₂) {a a' : Fin (p + 1) → ι₁} {b b' : Fin (q + 1) → ι₂}
    (ea : a = a') (eb : b = b') (ha hb ha' hb') :
    leibnizTerm c e σ a b ha hb = leibnizTerm c e σ a' b' ha' hb' := by
  subst ea eb
  rfl

/-- `j.succAbove i` is `i` when `i < j` and `i + 1` when `j ≤ i`. -/
theorem val_succAbove_cases {n : ℕ} (j : Fin (n + 1)) (i : Fin n) :
    ((j.succAbove i).val = i.val ∧ i.val < j.val) ∨
      ((j.succAbove i).val = i.val + 1 ∧ j.val ≤ i.val) := by
  rw [val_succAbove]
  split_ifs with h
  exacts [Or.inl ⟨rfl, h⟩, Or.inr ⟨rfl, by omega⟩]

/-- If `f = s ∘ θ` and `g = s ∘ θ'` where `θ` and `θ'` have the same values, then `f = g`. -/
theorem fin_ext_val {n : ℕ} {f g : Fin (n + 1) → ι₁} {m : ℕ} (s : Fin (m + 1) → ι₁)
    (θ θ' : Fin (n + 1) → Fin (m + 1)) (hθ : ∀ i, (θ i).val = (θ' i).val) (hf : f = s ∘ θ)
    (hg : g = s ∘ θ') : f = g := by
  rw [hf, hg]
  funext i
  simp only [Function.comp_apply]
  rw [Fin.ext (hθ i)]

/-- `leibnizTerm` along `σ ∘ θ` and `σ ∘ η` only depends on the values of `θ` and `η`. -/
private theorem leibnizTerm_eq_of_val_eq {p q n : ℕ} (c : Cochain P U p) (e : Cochain Q V q)
    (σ : Fin (n + 1) → ι₁ × ι₂) {θ θ' : Fin (p + 1) → Fin (n + 1)}
    {η η' : Fin (q + 1) → Fin (n + 1)} (hθ : ∀ i, (θ i).val = (θ' i).val)
    (hη : ∀ i, (η i).val = (η' i).val) (ha hb ha' hb') :
    leibnizTerm c e σ (Prod.fst ∘ σ ∘ θ) (Prod.snd ∘ σ ∘ η) ha hb =
      leibnizTerm c e σ (Prod.fst ∘ σ ∘ θ') (Prod.snd ∘ σ ∘ η') ha' hb' :=
  leibnizTerm_congr c e σ (fin_ext_val (Prod.fst ∘ σ) θ θ' hθ rfl rfl)
    (fin_ext_val (Prod.snd ∘ σ) η η' hη rfl rfl) _ _ _ _

/-- **The Leibniz rule** `d(c ∪ e) = dc ∪ e + (-1)^p c ∪ de`. -/
theorem d_cup {p q n : ℕ} (h : p + q = n) (c : Cochain P U p) (e : Cochain Q V q) :
    d (extTensor P Q) (prodCover U V) n (cup h c e) =
      cup (show p + 1 + q = n + 1 by omega) (d P U p c) e +
        ((-1 : ℤ) ^ p) • cup (show p + (q + 1) = n + 1 by omega) c (d Q V q e) := by
  subst h
  funext σ
  set W := prodCover U V
  have hL : d (extTensor P Q) W (p + q) (cup rfl c e) σ = ∑ j : Fin (p + q + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • leibnizTerm c e σ
        (Prod.fst ∘ σ ∘ j.succAbove ∘ frontIdx p (p + q) (by omega))
        (Prod.snd ∘ σ ∘ j.succAbove ∘ backIdx p q (p + q) le_rfl)
        (fst_inter_prodCover_le U V σ _) (snd_inter_prodCover_le U V σ _) := by
    rw [d_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cup_apply, res_extTensor_tmul, res_res, res_res]
    rfl
  have hR₁ : cup (show p + 1 + q = p + q + 1 by omega) (d P U p c) e σ = ∑ a : Fin (p + 2),
      ((-1 : ℤ) ^ (a : ℕ)) • leibnizTerm c e σ
        (Prod.fst ∘ σ ∘ frontIdx (p + 1) (p + q + 1) (by omega) ∘ a.succAbove)
        (Prod.snd ∘ σ ∘ backIdx (p + 1) q (p + q + 1) (by omega))
        (fst_inter_prodCover_le U V σ _) (snd_inter_prodCover_le U V σ _) := by
    rw [cup_apply, d_apply, map_sum, sum_tmul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_zsmul, res_res, ← smul_tmul']
    rfl
  have hR₂ : cup (show p + (q + 1) = p + q + 1 by omega) c (d Q V q e) σ = ∑ b : Fin (q + 2),
      ((-1 : ℤ) ^ (b : ℕ)) • leibnizTerm c e σ
        (Prod.fst ∘ σ ∘ frontIdx p (p + q + 1) (by omega))
        (Prod.snd ∘ σ ∘ backIdx p (q + 1) (p + q + 1) (by omega) ∘ b.succAbove)
        (fst_inter_prodCover_le U V σ _) (snd_inter_prodCover_le U V σ _) := by
    rw [cup_apply, d_apply, map_sum, tmul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_zsmul, res_res, tmul_smul]
    rfl
  rw [Pi.add_apply, Pi.smul_apply, hL, hR₁, hR₂, Fin.sum_univ_castSucc (n := p + 1),
    Fin.sum_univ_succ (n := q + 1), smul_add, Finset.smul_sum]
  have H : p + 1 + (q + 1) = p + q + 2 := by omega
  rw [← Equiv.sum_comp (finCongr H), Fin.sum_univ_add]
  have e₁ : ∀ a : Fin (p + 1), ((-1 : ℤ) ^ ((finCongr H (Fin.castAdd (q + 1) a) : Fin _) : ℕ)) •
      leibnizTerm c e σ
        (Prod.fst ∘ σ ∘ (finCongr H (Fin.castAdd (q + 1) a)).succAbove ∘
          frontIdx p (p + q) (by omega))
        (Prod.snd ∘ σ ∘ (finCongr H (Fin.castAdd (q + 1) a)).succAbove ∘
          backIdx p q (p + q) le_rfl)
        (fst_inter_prodCover_le U V σ _) (snd_inter_prodCover_le U V σ _) =
      ((-1 : ℤ) ^ ((Fin.castSucc a : Fin (p + 2)) : ℕ)) • leibnizTerm c e σ
        (Prod.fst ∘ σ ∘ frontIdx (p + 1) (p + q + 1) (by omega) ∘ (Fin.castSucc a).succAbove)
        (Prod.snd ∘ σ ∘ backIdx (p + 1) q (p + q + 1) (by omega))
        (fst_inter_prodCover_le U V σ _) (snd_inter_prodCover_le U V σ _) := by
    intro a
    congr 1
    refine leibnizTerm_eq_of_val_eq c e σ (fun i => ?_) (fun i => ?_) _ _ _ _
    · have h₁ := val_succAbove_cases (finCongr H (Fin.castAdd (q + 1) a))
        (frontIdx p (p + q) (by omega) i)
      have h₂ := val_succAbove_cases (Fin.castSucc a) i
      simp only [Function.comp_apply, frontIdx_val, finCongr_apply, Fin.val_cast,
        Fin.val_castAdd, Fin.val_castSucc] at h₁ h₂ ⊢
      omega
    · have h₁ := val_succAbove_cases (finCongr H (Fin.castAdd (q + 1) a))
        (backIdx p q (p + q) le_rfl i)
      simp only [Function.comp_apply, backIdx_val, finCongr_apply, Fin.val_cast,
        Fin.val_castAdd] at h₁ ⊢
      omega
  have e₂ : ∀ b : Fin (q + 1), ((-1 : ℤ) ^ ((finCongr H (Fin.natAdd (p + 1) b) : Fin _) : ℕ)) •
      leibnizTerm c e σ
        (Prod.fst ∘ σ ∘ (finCongr H (Fin.natAdd (p + 1) b)).succAbove ∘
          frontIdx p (p + q) (by omega))
        (Prod.snd ∘ σ ∘ (finCongr H (Fin.natAdd (p + 1) b)).succAbove ∘
          backIdx p q (p + q) le_rfl)
        (fst_inter_prodCover_le U V σ _) (snd_inter_prodCover_le U V σ _) =
      ((-1 : ℤ) ^ p) • (((-1 : ℤ) ^ ((Fin.succ b : Fin (q + 2)) : ℕ)) • leibnizTerm c e σ
        (Prod.fst ∘ σ ∘ frontIdx p (p + q + 1) (by omega))
        (Prod.snd ∘ σ ∘ backIdx p (q + 1) (p + q + 1) (by omega) ∘ (Fin.succ b).succAbove)
        (fst_inter_prodCover_le U V σ _) (snd_inter_prodCover_le U V σ _)) := by
    intro b
    rw [smul_smul, ← pow_add]
    congr 1
    · simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      ring_nf
    refine leibnizTerm_eq_of_val_eq c e σ (fun i => ?_) (fun i => ?_) _ _ _ _
    · have h₁ := val_succAbove_cases (finCongr H (Fin.natAdd (p + 1) b))
        (frontIdx p (p + q) (by omega) i)
      simp only [Function.comp_apply, frontIdx_val, finCongr_apply, Fin.val_cast,
        Fin.val_natAdd] at h₁ ⊢
      omega
    · have h₁ := val_succAbove_cases (finCongr H (Fin.natAdd (p + 1) b))
        (backIdx p q (p + q) le_rfl i)
      have h₂ := val_succAbove_cases (Fin.succ b) i
      simp only [Function.comp_apply, backIdx_val, finCongr_apply, Fin.val_cast,
        Fin.val_natAdd, Fin.val_succ] at h₁ h₂ ⊢
      omega
  rw [Finset.sum_congr rfl fun a _ => e₁ a, Finset.sum_congr rfl fun b _ => e₂ b]
  have e₃ : leibnizTerm c e σ
        (Prod.fst ∘ σ ∘ frontIdx (p + 1) (p + q + 1) (by omega) ∘ (Fin.last (p + 1)).succAbove)
        (Prod.snd ∘ σ ∘ backIdx (p + 1) q (p + q + 1) (by omega))
        (fst_inter_prodCover_le U V σ _) (snd_inter_prodCover_le U V σ _) =
      leibnizTerm c e σ
        (Prod.fst ∘ σ ∘ frontIdx p (p + q + 1) (by omega))
        (Prod.snd ∘ σ ∘ backIdx p (q + 1) (p + q + 1) (by omega) ∘ (0 : Fin (q + 2)).succAbove)
        (fst_inter_prodCover_le U V σ _) (snd_inter_prodCover_le U V σ _) := by
    refine leibnizTerm_eq_of_val_eq c e σ (fun i => ?_) (fun i => ?_) _ _ _ _
    · have h₁ := val_succAbove_cases (Fin.last (p + 1)) i
      simp only [Function.comp_apply, frontIdx_val, Fin.val_last] at h₁ ⊢
      omega
    · have h₁ := val_succAbove_cases (0 : Fin (q + 2)) i
      simp only [Function.comp_apply, backIdx_val, Fin.val_zero] at h₁ ⊢
      omega
  rw [e₃, Fin.val_last, Fin.val_zero, pow_zero, one_smul, pow_succ, mul_neg_one, neg_smul]
  abel

/-- The product of two cocycles is a cocycle. -/
theorem d_cup_eq_zero {p q n : ℕ} (h : p + q = n) {c : Cochain P U p} {e : Cochain Q V q}
    (hc : d P U p c = 0) (he : d Q V q e = 0) :
    d (extTensor P Q) (prodCover U V) n (cup h c e) = 0 := by
  rw [d_cup, hc, he, map_zero, map_zero, LinearMap.zero_apply, smul_zero, add_zero]

/-! ### The product on Čech cohomology -/

/-- The product of a cocycle with a coboundary is a coboundary. -/
theorem Hmk_cup_d_right {p q n : ℕ} (h : p + (q + 1) = n) (c : Cochain P U p)
    (hc : d P U p c = 0) (w : Cochain Q V q) :
    Hmk (extTensor P Q) (prodCover U V) (cup h c (d Q V q w)) (d_cup_eq_zero h hc (d_d Q V q w))
      = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨p + q, by omega⟩
  rw [Hmk_eq_zero_iff_succ]
  refine ⟨((-1 : ℤ) ^ p) • cup (show p + q = m by omega) c w, ?_⟩
  rw [map_zsmul, d_cup, hc, map_zero, LinearMap.zero_apply, zero_add, smul_smul, ← pow_add,
    Even.neg_one_pow ⟨p, rfl⟩, one_smul]

/-- The product of a coboundary with a cocycle is a coboundary. -/
theorem Hmk_cup_d_left {p q n : ℕ} (h : p + 1 + q = n) (w : Cochain P U p) (e : Cochain Q V q)
    (he : d Q V q e = 0) :
    Hmk (extTensor P Q) (prodCover U V) (cup h (d P U p w) e) (d_cup_eq_zero h (d_d P U p w) he)
      = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨p + q, by omega⟩
  rw [Hmk_eq_zero_iff_succ]
  refine ⟨cup (show p + q = m by omega) w e, ?_⟩
  rw [d_cup, he, map_zero, smul_zero, add_zero]

/-- The product of cocycles, as a bilinear map. -/
def cupCocycles {p q n : ℕ} (h : p + q = n) :
    cocycles P U p →ₗ[k] cocycles Q V q →ₗ[k] cocycles (extTensor P Q) (prodCover U V) n :=
  LinearMap.mk₂ k (fun c e => ⟨cup h c.1 e.1, d_cup_eq_zero h c.2 e.2⟩)
    (fun c c' e => Subtype.ext (by simp)) (fun r c e => Subtype.ext (by simp))
    (fun c e e' => Subtype.ext (by simp)) (fun r c e => Subtype.ext (by simp))

/-- The product with a cocycle `c` sends coboundaries of `Q` to coboundaries of `P ⊠ Q`. -/
theorem cupCocycles_le {p q n : ℕ} (h : p + q = n) (c : cocycles P U p) :
    coboundaries Q V q ≤ (coboundaries (extTensor P Q) (prodCover U V) n).comap
      (cupCocycles h c) := by
  cases q with
  | zero => intro e he; simp only [coboundaries, Submodule.mem_bot] at he; subst he; simp
  | succ q =>
    rintro ⟨e, he⟩ ⟨w, rfl⟩
    have := Hmk_cup_d_right h c.1 c.2 w
    rw [Hmk, Submodule.Quotient.mk_eq_zero] at this
    exact this

/-- The product of a cocycle of `P` with classes of `Q`. -/
def cupCocycleH {p q n : ℕ} (h : p + q = n) :
    cocycles P U p →ₗ[k] H Q V q →ₗ[k] H (extTensor P Q) (prodCover U V) n where
  toFun c := Submodule.mapQ _ _ (cupCocycles h c) (cupCocycles_le h c)
  map_add' c c' := Submodule.linearMap_qext _ (LinearMap.ext fun e => by
    simp [Submodule.mapQ_apply])
  map_smul' r c := Submodule.linearMap_qext _ (LinearMap.ext fun e => by
    simp [Submodule.mapQ_apply])

/-- The product of a coboundary of `P` with any class of `Q` is zero. -/
theorem cupCocycleH_le {p q n : ℕ} (h : p + q = n) :
    coboundaries P U p ≤ LinearMap.ker (cupCocycleH (Q := Q) (V := V) h) := by
  cases p with
  | zero => intro c hc; simp only [coboundaries, Submodule.mem_bot] at hc; subst hc; simp
  | succ p =>
    rintro ⟨c, hc⟩ ⟨w, rfl⟩
    refine LinearMap.mem_ker.2 (Submodule.linearMap_qext _ (LinearMap.ext fun e => ?_))
    have := Hmk_cup_d_left h w e.1 e.2
    exact this

/-- **The product on Čech cohomology** `Ȟ^p(U, P) × Ȟ^q(V, Q) ⟶ Ȟ^n(U × V, P ⊠ Q)`. -/
def Hcup {p q n : ℕ} (h : p + q = n) :
    H P U p →ₗ[k] H Q V q →ₗ[k] H (extTensor P Q) (prodCover U V) n :=
  Submodule.liftQ _ (cupCocycleH h) (cupCocycleH_le h)

/-- The product of the classes of two cocycles is the class of their product. -/
theorem Hcup_Hmk {p q n : ℕ} (h : p + q = n) (c : Cochain P U p) (hc : d P U p c = 0)
    (e : Cochain Q V q) (he : d Q V q e = 0) :
    Hcup h (Hmk P U c hc) (Hmk Q V e he) =
      Hmk (extTensor P Q) (prodCover U V) (cup h c e) (d_cup_eq_zero h hc he) :=
  rfl

/-- The product on Čech cohomology out of the tensor product. -/
def HcupT {p q n : ℕ} (h : p + q = n) :
    H P U p ⊗[k] H Q V q →ₗ[k] H (extTensor P Q) (prodCover U V) n :=
  TensorProduct.lift (Hcup h)

/-- `HcupT h (x ⊗ y) = Hcup h x y`. -/
theorem HcupT_tmul {p q n : ℕ} (h : p + q = n) (x : H P U p) (y : H Q V q) :
    HcupT h (x ⊗ₜ y) = Hcup h x y :=
  rfl

end Cup

/-! ### Contractions and exact sequences of external tensor products -/

section Contraction

variable [Fintype ι₁] [Fintype ι₂] {R : L₁ᵒᵖ ⥤ ModuleCat.{u} k} {S : L₂ᵒᵖ ⥤ ModuleCat.{u} k}
  {U : ι₁ → L₁} {V : ι₂ → L₂}

/-- **Contractions of `R` along `U` and of `S` along `V` give a contraction of `R ⊠ S` along
`U × V`.** -/
def extTensorContraction (C₁ : Contraction R U) (C₂ : Contraction S V) :
    Contraction (extTensor R S) (prodCover U V) where
  E ij Z := TensorProduct.map (C₁.E ij.1 Z.fst) (C₂.E ij.2 Z.snd)
  natural ij Z Z' h x := by
    have e : res (extTensor R S) h ∘ₗ TensorProduct.map (C₁.E ij.1 Z.fst) (C₂.E ij.2 Z.snd) =
        TensorProduct.map (C₁.E ij.1 Z'.fst) (C₂.E ij.2 Z'.snd) ∘ₗ
          res (extTensor R S) (inf_le_inf_right (prodCover U V ij) h) :=
      TensorProduct.ext' fun x y => congrArg₂ (· ⊗ₜ[k] ·)
        (C₁.natural ij.1 (LatProd.fst_mono h) x) (C₂.natural ij.2 (LatProd.snd_mono h) y)
    exact LinearMap.congr_fun e x
  sum_eq Z x := by
    have e : ∑ ij : ι₁ × ι₂, TensorProduct.map (C₁.E ij.1 Z.fst) (C₂.E ij.2 Z.snd) ∘ₗ
        TensorProduct.map (res R (inf_le_left : Z.fst ⊓ U ij.1 ≤ Z.fst))
          (res S (inf_le_left : Z.snd ⊓ V ij.2 ≤ Z.snd)) = LinearMap.id := by
      refine TensorProduct.ext' fun x y => ?_
      rw [LinearMap.sum_apply, Fintype.sum_prod_type, LinearMap.id_apply]
      simp only [LinearMap.comp_apply, map_tmul]
      rw [← congrArg₂ (· ⊗ₜ[k] ·) (C₁.sum_eq Z.fst x) (C₂.sum_eq Z.snd y), sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [tmul_sum]
    exact (LinearMap.sum_apply _ _ _).symm.trans (LinearMap.congr_fun e x)

end Contraction

end Stacks.CechKunneth

end
