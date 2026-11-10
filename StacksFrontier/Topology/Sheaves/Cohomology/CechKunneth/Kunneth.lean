module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.Devissage
public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.ExternalProduct
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic

/-!
# The Künneth formula for Čech cohomology over a field

Let `k` be a field, `P` a presheaf of `k`-vector spaces on a complete lattice `L₁` and `Q` one on
`L₂`, and `U : ι₁ → L₁`, `V : ι₂ → L₂` finite families. Then the Alexander–Whitney product
`⨁_{p + q = n} Ȟ^p(U, P) ⊗_k Ȟ^q(V, Q) ⟶ Ȟ^n(U × V, P ⊠ Q)` is an isomorphism.

This is the algebraic core of [Stacks, Tag 0BED], proved as there by dévissage, but entirely on
the level of Čech complexes. Both sides are δ-functors in each variable for sequences of
presheaves short exact on the nerve: the source because `k` is a field, so tensoring with a
vector space is exact, and the target because `P ⊠ Q` is then exact in each variable. Every `P`
embeds into `P' = ∏_i P(- ⊓ U_i)`, which has a contraction
(`Stacks.CechKunneth.piRestrContraction`). For two presheaves with contractions both sides
vanish in positive degrees and are `P(⊤) ⊗ Q(⊤)` in degree zero; the four-lemma induction
`Stacks.CechKunneth.LESMorphism.bijective` then gives the result first for `P'` and every `Q`,
and then for every `P` and every `Q`. This replaces the Leray spectral sequence and the
commutation of cohomology with direct sums used in the source, which are needed there only to
compute the case of `Γ`-acyclic coefficients.

## Main definitions

* `Stacks.CechKunneth.Src`: the source `∏_{p + q = n} Ȟ^p(U, P) ⊗_k Ȟ^q(V, Q)`.
* `Stacks.CechKunneth.kunnethMap`: the Alexander–Whitney product out of it.
* `Stacks.CechKunneth.kunnethEquiv`: the Künneth isomorphism.

## Main results

* `Stacks.CechKunneth.bijective_kunnethMap`: the Künneth formula for Čech cohomology.

## Implementation notes

The sum over `p + q = n` is a finite product indexed by the antidiagonal
`Stacks.CechKunneth.Idx n`, so that its components are plain function values; it is converted to
a direct sum in the final statement.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct

universe u

namespace Stacks.CechKunneth

/-- The pairs `(p, q)` with `p + q = n`. -/
abbrev Idx (n : ℕ) : Type := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

/-- The pairs `(p, q)` with `p + q = n` form a finite type. -/
instance (n : ℕ) : Fintype (Idx n) :=
  Fintype.subtype (Finset.antidiagonal n) fun _ => Finset.mem_antidiagonal

/-- The pair `(p + 1, q)`. -/
def Idx.succFst {n : ℕ} (pq : Idx n) : Idx (n + 1) := ⟨(pq.1.1 + 1, pq.1.2), by omega⟩

/-- The pair `(p, q + 1)`. -/
def Idx.succSnd {n : ℕ} (pq : Idx n) : Idx (n + 1) := ⟨(pq.1.1, pq.1.2 + 1), by omega⟩

/-- The map `(p, q) ↦ (p + 1, q)` is injective. -/
theorem Idx.succFst_injective (n : ℕ) : Function.Injective (Idx.succFst (n := n)) :=
  fun _ _ h => by simpa [succFst, Subtype.ext_iff, Prod.ext_iff] using h

/-- The map `(p, q) ↦ (p, q + 1)` is injective. -/
theorem Idx.succSnd_injective (n : ℕ) : Function.Injective (Idx.succSnd (n := n)) :=
  fun _ _ h => by simpa [succSnd, Subtype.ext_iff, Prod.ext_iff] using h

/-- Acting twice by the sign `(-1) ^ a` is the identity. -/
theorem neg_one_pow_smul_smul {M : Type*} [AddCommGroup M] (a : ℕ) (z : M) :
    ((-1 : ℤ) ^ a) • ((-1 : ℤ) ^ a) • z = z := by
  rw [smul_smul, ← pow_add, Even.neg_one_pow ⟨a, rfl⟩, one_smul]

/-- A product of exact sequences is exact. -/
theorem exact_pi {I : Type*} {k : Type*} [CommRing k] {A B C : I → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
    [∀ i, Module k (A i)] [∀ i, Module k (B i)] [∀ i, Module k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i)
      (LinearMap.pi fun i => g i ∘ₗ LinearMap.proj i) := by
  intro y
  constructor
  · intro hy
    choose x hx using fun i => ((h i) (y i)).1 (congrFun hy i)
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    exact funext fun i => ((h i) _).2 ⟨x i, rfl⟩

variable {k : Type u} [Field k] {L₁ L₂ : Type u} [CompleteLattice L₁] [CompleteLattice L₂]
  {ι₁ ι₂ : Type u} (U : ι₁ → L₁) (V : ι₂ → L₂)

/-- The first component of the intersection of `U × V` along `σ` is the intersection of `U`
along the first coordinates of `σ`. -/
theorem fst_inter_prodCover {n : ℕ} (σ : Fin (n + 1) → ι₁ × ι₂) :
    (inter (prodCover U V) σ).fst = inter U (Prod.fst ∘ σ) := by
  change Prod.fst (⨅ j, ((U (σ j).1, V (σ j).2) : L₁ × L₂)) = _
  rw [Prod.fst_iInf]
  rfl

/-- The second component of the intersection of `U × V` along `σ` is the intersection of `V`
along the second coordinates of `σ`. -/
theorem snd_inter_prodCover {n : ℕ} (σ : Fin (n + 1) → ι₁ × ι₂) :
    (inter (prodCover U V) σ).snd = inter V (Prod.snd ∘ σ) := by
  change Prod.snd (⨅ j, ((U (σ j).1, V (σ j).2) : L₁ × L₂)) = _
  rw [Prod.snd_iInf]
  rfl

/-! ### Exactness of external tensor products of sequences -/

section NerveSES

variable {U V}

/-- If `P ⟶ P' ⟶ P''` is short exact on the nerve of `U`, then `P ⊠ Q ⟶ P' ⊠ Q ⟶ P'' ⊠ Q` is
short exact on the nerve of `U × V`. -/
theorem IsNerveSES.extTensorLeft {P P' P'' : L₁ᵒᵖ ⥤ ModuleCat.{u} k} {f : P ⟶ P'}
    {g : P' ⟶ P''} (h : IsNerveSES U f g) (Q : L₂ᵒᵖ ⥤ ModuleCat.{u} k) :
    IsNerveSES (prodCover U V) (extTensorMapLeft (Q := Q) f) (extTensorMapLeft g) where
  injective σ := by
    have hi := h.injective (Prod.fst ∘ σ)
    rw [← fst_inter_prodCover U V σ] at hi
    exact Module.Flat.rTensor_preserves_injective_linearMap _ hi
  exact σ := by
    have hi := h.exact (Prod.fst ∘ σ)
    rw [← fst_inter_prodCover U V σ] at hi
    exact Module.Flat.rTensor_exact _ hi
  surjective σ := by
    have hi := h.surjective (Prod.fst ∘ σ)
    rw [← fst_inter_prodCover U V σ] at hi
    exact LinearMap.rTensor_surjective _ hi

/-- If `Q ⟶ Q' ⟶ Q''` is short exact on the nerve of `V`, then `P ⊠ Q ⟶ P ⊠ Q' ⟶ P ⊠ Q''` is
short exact on the nerve of `U × V`. -/
theorem IsNerveSES.extTensorRight {Q Q' Q'' : L₂ᵒᵖ ⥤ ModuleCat.{u} k} {f : Q ⟶ Q'}
    {g : Q' ⟶ Q''} (h : IsNerveSES V f g) (P : L₁ᵒᵖ ⥤ ModuleCat.{u} k) :
    IsNerveSES (prodCover U V) (extTensorMapRight (P := P) f) (extTensorMapRight g) where
  injective σ := by
    have hi := h.injective (Prod.snd ∘ σ)
    rw [← snd_inter_prodCover U V σ] at hi
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hi
  exact σ := by
    have hi := h.exact (Prod.snd ∘ σ)
    rw [← snd_inter_prodCover U V σ] at hi
    exact Module.Flat.lTensor_exact _ hi
  surjective σ := by
    have hi := h.surjective (Prod.snd ∘ σ)
    rw [← snd_inter_prodCover U V σ] at hi
    exact LinearMap.lTensor_surjective _ hi

end NerveSES

/-! ### The source and the Künneth map -/

section Src

variable (P : L₁ᵒᵖ ⥤ ModuleCat.{u} k) (Q : L₂ᵒᵖ ⥤ ModuleCat.{u} k)

/-- **The source of the Künneth map**, `∏_{p + q = n} Ȟ^p(U, P) ⊗_k Ȟ^q(V, Q)`. -/
abbrev Src (n : ℕ) : Type u := ∀ pq : Idx n, H P U pq.1.1 ⊗[k] H Q V pq.1.2

/-- **The Künneth map** `∏_{p + q = n} Ȟ^p(U, P) ⊗_k Ȟ^q(V, Q) ⟶ Ȟ^n(U × V, P ⊠ Q)`, the sum of the
Alexander–Whitney products. -/
def kunnethMap (n : ℕ) : Src U V P Q n →ₗ[k] H (extTensor P Q) (prodCover U V) n :=
  ∑ pq : Idx n, HcupT pq.2 ∘ₗ LinearMap.proj pq

/-- The Künneth map sends `x` to the sum over `p + q = n` of the Alexander–Whitney products of
its components. -/
theorem kunnethMap_apply (n : ℕ) (x : Src U V P Q n) :
    kunnethMap U V P Q n x = ∑ pq : Idx n, HcupT pq.2 (x pq) := by
  simp only [kunnethMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

end Src

/-! ### Functoriality and connecting maps in the first variable -/

section Left

variable {U V} {P P' P'' : L₁ᵒᵖ ⥤ ModuleCat.{u} k} (Q : L₂ᵒᵖ ⥤ ModuleCat.{u} k)

/-- The map of sources induced by a morphism in the first variable. -/
def srcMapLeft (f : P ⟶ P') (n : ℕ) : Src U V P Q n →ₗ[k] Src U V P' Q n :=
  LinearMap.pi fun pq => (Hmap U f pq.1.1).rTensor _ ∘ₗ LinearMap.proj pq

variable {f : P ⟶ P'} {g : P' ⟶ P''} (h : IsNerveSES U f g)

/-- The components of the connecting map of sources in the first variable. -/
def srcδLeftComp (n : ℕ) :
    (pq : Idx (n + 1)) → (Src U V P'' Q n →ₗ[k] H P U pq.1.1 ⊗[k] H Q V pq.1.2)
  | ⟨⟨0, _⟩, _⟩ => 0
  | ⟨⟨a + 1, b⟩, hab⟩ =>
    (h.δ a).rTensor (H Q V b) ∘ₗ LinearMap.proj (⟨⟨a, b⟩, by simp only at hab ⊢; omega⟩ : Idx n)

/-- The connecting map of sources in the first variable. -/
def srcδLeft (n : ℕ) : Src U V P'' Q n →ₗ[k] Src U V P Q (n + 1) :=
  LinearMap.pi (srcδLeftComp Q h n)

/-- The component of `srcδLeft` at `(p + 1, q)` is the connecting map in degree `p`, tensored
with `Ȟ^q(V, Q)`, applied to the component at `(p, q)`. -/
theorem srcδLeft_succFst (n : ℕ) (y : Src U V P'' Q n) (pq : Idx n) :
    srcδLeft Q h n y pq.succFst = (h.δ pq.1.1).rTensor _ (y pq) :=
  rfl

/-- The component of `srcδLeft` at `(0, q)` vanishes. -/
theorem srcδLeft_zero (n : ℕ) (y : Src U V P'' Q n) (b : ℕ) (hb : 0 + b = n + 1) :
    srcδLeft Q h n y ⟨⟨0, b⟩, hb⟩ = 0 :=
  rfl

include h in
/-- The maps of sources induced by `f` and `g` form an exact sequence. -/
theorem exact_srcMapLeft (n : ℕ) :
    Function.Exact (srcMapLeft Q f n) (srcMapLeft (U := U) (V := V) Q g n) :=
  exact_pi _ _ fun pq => Module.Flat.rTensor_exact _ (h.exact₁ pq.1.1)

/-- The map of sources induced by `g` and the connecting map `srcδLeft` form an exact
sequence. -/
theorem exact_srcMapLeft_srcδLeft (n : ℕ) :
    Function.Exact (srcMapLeft (U := U) (V := V) Q g n) (srcδLeft Q h n) := by
  intro y
  constructor
  · intro hy
    choose x hx using fun pq : Idx n =>
      ((Module.Flat.rTensor_exact _ (h.exact₂ pq.1.1)) (y pq)).1
        ((srcδLeft_succFst Q h n y pq).symm.trans (congrFun hy pq.succFst))
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    funext ⟨⟨a, b⟩, hab⟩
    cases a with
    | zero => rfl
    | succ a =>
      exact ((Module.Flat.rTensor_exact _ (h.exact₂ a)) _).2 ⟨_, rfl⟩

/-- The connecting map `srcδLeft` and the map of sources induced by `f` in the next degree form
an exact sequence. -/
theorem exact_srcδLeft_srcMapLeft (n : ℕ) :
    Function.Exact (srcδLeft Q h n) (srcMapLeft (U := U) (V := V) Q f (n + 1)) := by
  intro x
  constructor
  · intro hx
    choose y hy using fun pq : Idx n =>
      ((Module.Flat.rTensor_exact _ (h.exact₃ pq.1.1)) _).1 (congrFun hx pq.succFst)
    refine ⟨y, funext fun ⟨⟨a, b⟩, hab⟩ => ?_⟩
    cases a with
    | zero =>
      have hx' : (Hmap U f 0).rTensor (H Q V b) (x ⟨⟨0, b⟩, hab⟩) = 0 := congrFun hx ⟨⟨0, b⟩, hab⟩
      exact (srcδLeft_zero Q h n y b hab).trans
        (Module.Flat.rTensor_preserves_injective_linearMap _ h.injective_Hmap_zero
          (hx'.trans (map_zero ((Hmap U f 0).rTensor (H Q V b))).symm)).symm
    | succ a => exact hy ⟨⟨a, b⟩, by omega⟩
  · rintro ⟨y, rfl⟩
    funext ⟨⟨a, b⟩, hab⟩
    cases a with
    | zero =>
      exact (congrArg ((Hmap U f 0).rTensor (H Q V b)) (srcδLeft_zero Q h n y b hab)).trans
        (map_zero _)
    | succ a => exact ((Module.Flat.rTensor_exact _ (h.exact₃ a)) _).2 ⟨_, rfl⟩

include h in
/-- In degree zero the map of sources induced by `f` is injective. -/
theorem injective_srcMapLeft_zero : Function.Injective (srcMapLeft (U := U) (V := V) Q f 0) := by
  intro x y hxy
  funext ⟨⟨a, b⟩, hab⟩
  obtain rfl : a = 0 := by simp only at hab; omega
  exact Module.Flat.rTensor_preserves_injective_linearMap _ h.injective_Hmap_zero
    (congrFun hxy ⟨⟨0, b⟩, hab⟩)

/-- The Alexander–Whitney product commutes with the maps induced by a morphism `f` in the first
variable. -/
theorem HcupT_rTensor_Hmap {a b n : ℕ} (hn : a + b = n) (z : H P U a ⊗[k] H Q V b) :
    HcupT hn ((Hmap U f a).rTensor _ z) =
      Hmap (prodCover U V) (extTensorMapLeft f) n (HcupT hn z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul x y =>
    obtain ⟨c, hc, rfl⟩ := Hmk_surjective P U x
    obtain ⟨e, he, rfl⟩ := Hmk_surjective Q V y
    rw [LinearMap.rTensor_tmul, HcupT_tmul, HcupT_tmul, Hmap_Hmk, Hcup_Hmk, Hcup_Hmk, Hmap_Hmk]
    exact Hmk_congr _ _ (mapCochain_cup_left f hn c e).symm _ _

/-- The Künneth map commutes with the maps induced by a morphism `f` in the first variable. -/
theorem kunnethMap_srcMapLeft (n : ℕ) (x : Src U V P Q n) :
    kunnethMap U V P' Q n (srcMapLeft Q f n x) =
      Hmap (prodCover U V) (extTensorMapLeft f) n (kunnethMap U V P Q n x) := by
  rw [kunnethMap_apply, kunnethMap_apply, map_sum]
  exact Finset.sum_congr rfl fun pq _ => HcupT_rTensor_Hmap Q pq.2 (x pq)

/-- The Alexander–Whitney product commutes with the connecting maps in the first variable. -/
theorem HcupT_rTensor_δ {a b n : ℕ} (hn : a + b = n) (z : H P'' U a ⊗[k] H Q V b) :
    HcupT (show a + 1 + b = n + 1 by omega) ((h.δ a).rTensor _ z) =
      (h.extTensorLeft Q).δ n (HcupT hn z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul x y =>
    obtain ⟨c, hc, rfl⟩ := Hmk_surjective P'' U x
    obtain ⟨e, he, rfl⟩ := Hmk_surjective Q V y
    obtain ⟨x₀, hx₀⟩ := h.exists_d_lift c hc
    rw [LinearMap.rTensor_tmul, HcupT_tmul, HcupT_tmul, h.δ_Hmk c hc _ (h.mapCochain_lift c) x₀ hx₀,
      Hcup_Hmk, Hcup_Hmk]
    refine ((h.extTensorLeft Q).δ_Hmk _ _ (cup hn (h.lift c) e) ?_ (cup _ x₀ e) ?_).symm
    · rw [mapCochain_cup_left, h.mapCochain_lift]
    · rw [mapCochain_cup_left, hx₀, d_cup hn, he, map_zero, smul_zero, add_zero]

/-- The Künneth map commutes with the connecting maps in the first variable. -/
theorem kunnethMap_srcδLeft (n : ℕ) (y : Src U V P'' Q n) :
    kunnethMap U V P Q (n + 1) (srcδLeft Q h n y) =
      (h.extTensorLeft Q).δ n (kunnethMap U V P'' Q n y) := by
  rw [kunnethMap_apply, kunnethMap_apply, map_sum]
  refine (Fintype.sum_of_injective Idx.succFst (Idx.succFst_injective n) _ _ ?_ ?_).symm
  · rintro ⟨⟨a, b⟩, hab⟩ hpq
    cases a with
    | zero => exact (congrArg (HcupT hab) (srcδLeft_zero Q h n y b hab)).trans (map_zero _)
    | succ a => exact absurd ⟨⟨⟨a, b⟩, by omega⟩, rfl⟩ hpq
  · intro pq
    exact (HcupT_rTensor_δ Q h pq.2 (y pq)).symm

/-- **The morphism of long exact sequences in the first variable.** -/
def lesLeft : LESMorphism (S := fun P n => Src U V P Q n)
    (T := fun P n => H (extTensor P Q) (prodCover U V) n)
    (fun P n => (kunnethMap U V P Q n).toAddMonoidHom) P P' P'' where
  fS n := (srcMapLeft Q f n).toAddMonoidHom
  gS n := (srcMapLeft Q g n).toAddMonoidHom
  δS n := (srcδLeft Q h n).toAddMonoidHom
  fT n := (Hmap (prodCover U V) (extTensorMapLeft f) n).toAddMonoidHom
  gT n := (Hmap (prodCover U V) (extTensorMapLeft g) n).toAddMonoidHom
  δT n := ((h.extTensorLeft Q).δ n).toAddMonoidHom
  exactS₁ n := exact_srcMapLeft Q h n
  exactS₂ n := exact_srcMapLeft_srcδLeft Q h n
  exactS₃ n := exact_srcδLeft_srcMapLeft Q h n
  injS := injective_srcMapLeft_zero Q h
  exactT₁ n := (h.extTensorLeft Q).exact₁ n
  exactT₂ n := (h.extTensorLeft Q).exact₂ n
  exactT₃ n := (h.extTensorLeft Q).exact₃ n
  injT := (h.extTensorLeft Q).injective_Hmap_zero
  comm_f n x := kunnethMap_srcMapLeft Q n x
  comm_g n x := kunnethMap_srcMapLeft Q n x
  comm_δ n x := kunnethMap_srcδLeft Q h n x

end Left

/-! ### Functoriality and connecting maps in the second variable -/

section Right

variable {U V} (P : L₁ᵒᵖ ⥤ ModuleCat.{u} k) {Q Q' Q'' : L₂ᵒᵖ ⥤ ModuleCat.{u} k}

/-- The map of sources induced by a morphism in the second variable. -/
def srcMapRight (f : Q ⟶ Q') (n : ℕ) : Src U V P Q n →ₗ[k] Src U V P Q' n :=
  LinearMap.pi fun pq => (Hmap V f pq.1.2).lTensor _ ∘ₗ LinearMap.proj pq

variable {f : Q ⟶ Q'} {g : Q' ⟶ Q''} (h : IsNerveSES V f g)

/-- The components of the connecting map of sources in the second variable, with the Koszul sign
`(-1)^p`. -/
def srcδRightComp (n : ℕ) :
    (pq : Idx (n + 1)) → (Src U V P Q'' n →ₗ[k] H P U pq.1.1 ⊗[k] H Q V pq.1.2)
  | ⟨⟨_, 0⟩, _⟩ => 0
  | ⟨⟨a, b + 1⟩, hab⟩ => ((-1 : ℤ) ^ a) •
    ((h.δ b).lTensor (H P U a) ∘ₗ LinearMap.proj (⟨⟨a, b⟩, by simp only at hab ⊢; omega⟩ : Idx n))

/-- The connecting map of sources in the second variable. -/
def srcδRight (n : ℕ) : Src U V P Q'' n →ₗ[k] Src U V P Q (n + 1) :=
  LinearMap.pi (srcδRightComp P h n)

/-- The component of `srcδRight` at `(p, q + 1)` is `(-1) ^ p` times `Ȟ^p(U, P)` tensored with
the connecting map in degree `q`, applied to the component at `(p, q)`. -/
theorem srcδRight_succSnd (n : ℕ) (y : Src U V P Q'' n) (pq : Idx n) :
    srcδRight P h n y pq.succSnd = ((-1 : ℤ) ^ pq.1.1) • (h.δ pq.1.2).lTensor _ (y pq) :=
  rfl

/-- The component of `srcδRight` at `(p, 0)` vanishes. -/
theorem srcδRight_zero (n : ℕ) (y : Src U V P Q'' n) (a : ℕ) (ha : a + 0 = n + 1) :
    srcδRight P h n y ⟨⟨a, 0⟩, ha⟩ = 0 :=
  rfl

/-- The component of `srcδRight` at `(a, b + 1)` is `(-1) ^ a` times `Ȟ^a(U, P)` tensored with
the connecting map in degree `b`, applied to the component at `(a, b)`. -/
theorem srcδRight_succ (n : ℕ) (y : Src U V P Q'' n) (a b : ℕ) (hab : a + (b + 1) = n + 1) :
    srcδRight P h n y ⟨⟨a, b + 1⟩, hab⟩ =
      ((-1 : ℤ) ^ a) • (h.δ b).lTensor (H P U a) (y ⟨⟨a, b⟩, by omega⟩) :=
  rfl

include h in
/-- The maps of sources induced by `f` and `g` form an exact sequence. -/
theorem exact_srcMapRight (n : ℕ) :
    Function.Exact (srcMapRight P f n) (srcMapRight (U := U) (V := V) P g n) :=
  exact_pi _ _ fun pq => Module.Flat.lTensor_exact _ (h.exact₁ pq.1.2)

/-- The map of sources induced by `g` and the connecting map `srcδRight` form an exact
sequence. -/
theorem exact_srcMapRight_srcδRight (n : ℕ) :
    Function.Exact (srcMapRight (U := U) (V := V) P g n) (srcδRight P h n) := by
  intro y
  constructor
  · intro hy
    have : ∀ pq : Idx n, ∃ x, (Hmap V g pq.1.2).lTensor (H P U pq.1.1) x = y pq := fun pq => by
      refine ((Module.Flat.lTensor_exact _ (h.exact₂ pq.1.2)) (y pq)).1 ?_
      have h1 : ((-1 : ℤ) ^ pq.1.1) • (h.δ pq.1.2).lTensor (H P U pq.1.1) (y pq) = 0 :=
        (srcδRight_succSnd P h n y pq).symm.trans (congrFun hy pq.succSnd)
      rw [← neg_one_pow_smul_smul pq.1.1 ((h.δ pq.1.2).lTensor _ (y pq)), h1, smul_zero]
    choose x hx using this
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    funext ⟨⟨a, b⟩, hab⟩
    cases b with
    | zero => rfl
    | succ b =>
      refine (srcδRight_succ P h n _ a b hab).trans ?_
      have e := ((Module.Flat.lTensor_exact (H P U a) (h.exact₂ b)) _).2
        ⟨x ⟨⟨a, b⟩, by omega⟩, rfl⟩
      exact (congrArg (((-1 : ℤ) ^ a) • ·) e).trans (smul_zero _)

/-- The connecting map `srcδRight` and the map of sources induced by `f` in the next degree
form an exact sequence. -/
theorem exact_srcδRight_srcMapRight (n : ℕ) :
    Function.Exact (srcδRight P h n) (srcMapRight (U := U) (V := V) P f (n + 1)) := by
  intro x
  constructor
  · intro hx
    have : ∀ pq : Idx n, ∃ y, (h.δ pq.1.2).lTensor (H P U pq.1.1) y =
        ((-1 : ℤ) ^ pq.1.1) • (x pq.succSnd : H P U pq.1.1 ⊗[k] H Q V (pq.1.2 + 1)) := by
      intro pq
      have hx' : (Hmap V f (pq.1.2 + 1)).lTensor (H P U pq.1.1) (x pq.succSnd) = 0 :=
        congrFun hx pq.succSnd
      refine ((Module.Flat.lTensor_exact _ (h.exact₃ pq.1.2)) _).1 ?_
      exact (map_zsmul ((Hmap V f (pq.1.2 + 1)).lTensor (H P U pq.1.1)) ((-1 : ℤ) ^ pq.1.1)
        (x pq.succSnd)).trans ((congrArg _ hx').trans (smul_zero _))
    choose y hy using this
    refine ⟨y, funext fun ⟨⟨a, b⟩, hab⟩ => ?_⟩
    cases b with
    | zero =>
      have hx' : (Hmap V f 0).lTensor (H P U a) (x ⟨⟨a, 0⟩, hab⟩) = 0 := congrFun hx ⟨⟨a, 0⟩, hab⟩
      exact (srcδRight_zero P h n y a hab).trans
        (Module.Flat.lTensor_preserves_injective_linearMap _ h.injective_Hmap_zero
          (hx'.trans (map_zero ((Hmap V f 0).lTensor (H P U a))).symm)).symm
    | succ b =>
      refine (srcδRight_succ P h n y a b hab).trans ?_
      rw [hy ⟨⟨a, b⟩, by omega⟩]
      exact neg_one_pow_smul_smul a _
  · rintro ⟨y, rfl⟩
    funext ⟨⟨a, b⟩, hab⟩
    cases b with
    | zero =>
      exact (congrArg ((Hmap V f 0).lTensor (H P U a)) (srcδRight_zero P h n y a hab)).trans
        (map_zero _)
    | succ b =>
      refine (congrArg ((Hmap V f (b + 1)).lTensor (H P U a))
        (srcδRight_succ P h n y a b hab)).trans ?_
      rw [map_zsmul, ((Module.Flat.lTensor_exact _ (h.exact₃ b)) _).2 ⟨_, rfl⟩, smul_zero]
      rfl

include h in
/-- In degree zero the map of sources induced by `f` is injective. -/
theorem injective_srcMapRight_zero :
    Function.Injective (srcMapRight (U := U) (V := V) P f 0) := by
  intro x y hxy
  funext ⟨⟨a, b⟩, hab⟩
  obtain rfl : b = 0 := by simp only at hab; omega
  exact Module.Flat.lTensor_preserves_injective_linearMap _ h.injective_Hmap_zero
    (congrFun hxy ⟨⟨a, 0⟩, hab⟩)

/-- The Alexander–Whitney product commutes with the maps induced by a morphism `f` in the second
variable. -/
theorem HcupT_lTensor_Hmap {a b n : ℕ} (hn : a + b = n) (z : H P U a ⊗[k] H Q V b) :
    HcupT hn ((Hmap V f b).lTensor _ z) =
      Hmap (prodCover U V) (extTensorMapRight f) n (HcupT hn z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul x y =>
    obtain ⟨c, hc, rfl⟩ := Hmk_surjective P U x
    obtain ⟨e, he, rfl⟩ := Hmk_surjective Q V y
    rw [LinearMap.lTensor_tmul, HcupT_tmul, HcupT_tmul, Hmap_Hmk, Hcup_Hmk, Hcup_Hmk, Hmap_Hmk]
    exact Hmk_congr _ _ (mapCochain_cup_right f hn c e).symm _ _

/-- The Künneth map commutes with the maps induced by a morphism `f` in the second variable. -/
theorem kunnethMap_srcMapRight (n : ℕ) (x : Src U V P Q n) :
    kunnethMap U V P Q' n (srcMapRight P f n x) =
      Hmap (prodCover U V) (extTensorMapRight f) n (kunnethMap U V P Q n x) := by
  rw [kunnethMap_apply, kunnethMap_apply, map_sum]
  exact Finset.sum_congr rfl fun pq _ => HcupT_lTensor_Hmap P pq.2 (x pq)

/-- The Alexander–Whitney product, twisted by the Koszul sign `(-1) ^ a`, commutes with the
connecting maps in the second variable. -/
theorem HcupT_lTensor_δ {a b n : ℕ} (hn : a + b = n) (z : H P U a ⊗[k] H Q'' V b) :
    HcupT (show a + (b + 1) = n + 1 by omega) (((-1 : ℤ) ^ a) • (h.δ b).lTensor _ z) =
      (h.extTensorRight P).δ n (HcupT hn z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, smul_add, hz, hz']
  | tmul x y =>
    obtain ⟨c, hc, rfl⟩ := Hmk_surjective P U x
    obtain ⟨e, he, rfl⟩ := Hmk_surjective Q'' V y
    obtain ⟨x₀, hx₀⟩ := h.exists_d_lift e he
    rw [LinearMap.lTensor_tmul, h.δ_Hmk e he _ (h.mapCochain_lift e) x₀ hx₀, map_zsmul,
      HcupT_tmul, HcupT_tmul, Hcup_Hmk, Hcup_Hmk, ← Hmk_zsmul]
    refine ((h.extTensorRight P).δ_Hmk _ _ (cup hn c (h.lift e)) ?_
      (((-1 : ℤ) ^ a) • cup _ c x₀) ?_).symm
    · rw [mapCochain_cup_right, h.mapCochain_lift]
    · rw [map_zsmul, mapCochain_cup_right, hx₀, d_cup hn, hc, map_zero, LinearMap.zero_apply,
        zero_add]

/-- The Künneth map commutes with the connecting maps in the second variable. -/
theorem kunnethMap_srcδRight (n : ℕ) (y : Src U V P Q'' n) :
    kunnethMap U V P Q (n + 1) (srcδRight P h n y) =
      (h.extTensorRight P).δ n (kunnethMap U V P Q'' n y) := by
  rw [kunnethMap_apply, kunnethMap_apply, map_sum]
  refine (Fintype.sum_of_injective Idx.succSnd (Idx.succSnd_injective n) _ _ ?_ ?_).symm
  · rintro ⟨⟨a, b⟩, hab⟩ hpq
    cases b with
    | zero => exact (congrArg (HcupT hab) (srcδRight_zero P h n y a hab)).trans (map_zero _)
    | succ b => exact absurd ⟨⟨⟨a, b⟩, by omega⟩, rfl⟩ hpq
  · intro pq
    exact (HcupT_lTensor_δ P h pq.2 (y pq)).symm

/-- **The morphism of long exact sequences in the second variable.** -/
def lesRight : LESMorphism (S := fun Q n => Src U V P Q n)
    (T := fun Q n => H (extTensor P Q) (prodCover U V) n)
    (fun Q n => (kunnethMap U V P Q n).toAddMonoidHom) Q Q' Q'' where
  fS n := (srcMapRight P f n).toAddMonoidHom
  gS n := (srcMapRight P g n).toAddMonoidHom
  δS n := (srcδRight P h n).toAddMonoidHom
  fT n := (Hmap (prodCover U V) (extTensorMapRight f) n).toAddMonoidHom
  gT n := (Hmap (prodCover U V) (extTensorMapRight g) n).toAddMonoidHom
  δT n := ((h.extTensorRight P).δ n).toAddMonoidHom
  exactS₁ n := exact_srcMapRight P h n
  exactS₂ n := exact_srcMapRight_srcδRight P h n
  exactS₃ n := exact_srcδRight_srcMapRight P h n
  injS := injective_srcMapRight_zero P h
  exactT₁ n := (h.extTensorRight P).exact₁ n
  exactT₂ n := (h.extTensorRight P).exact₂ n
  exactT₃ n := (h.extTensorRight P).exact₃ n
  injT := (h.extTensorRight P).injective_Hmap_zero
  comm_f n x := kunnethMap_srcMapRight P n x
  comm_g n x := kunnethMap_srcMapRight P n x
  comm_δ n x := kunnethMap_srcδRight P h n x

end Right


/-! ### The Künneth formula -/

/-- The only pair `(p, q)` with `p + q = 0` is `(0, 0)`. -/
instance : Unique (Idx 0) where
  default := ⟨(0, 0), rfl⟩
  uniq := fun ⟨⟨a, b⟩, h⟩ => Subtype.ext (Prod.ext (by simp only at h ⊢; omega)
    (by simp only at h ⊢; omega))

section Kunneth

variable {U V} [Fintype ι₁] [Fintype ι₂]

/-- **The Künneth formula for two presheaves with contractions.** Both sides vanish in positive
degrees, and in degree zero both are `R(⊤) ⊗ S(⊤)`. -/
theorem bijective_kunnethMap_of_contraction {R : L₁ᵒᵖ ⥤ ModuleCat.{u} k}
    {S : L₂ᵒᵖ ⥤ ModuleCat.{u} k} (C₁ : Contraction R U) (C₂ : Contraction S V) (n : ℕ) :
    Function.Bijective (kunnethMap U V R S n) := by
  cases n with
  | succ m =>
    have : Subsingleton (Src U V R S (m + 1)) := ⟨fun x y => funext fun ⟨⟨a, b⟩, hab⟩ => by
      cases a with
      | zero =>
        obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨m, by simp only at hab; omega⟩
        have := C₂.subsingleton_H b
        exact Subsingleton.elim _ _
      | succ a =>
        have := C₁.subsingleton_H a
        exact Subsingleton.elim _ _⟩
    have : Subsingleton (H (extTensor R S) (prodCover U V) (m + 1)) :=
      (extTensorContraction C₁ C₂).subsingleton_H m
    exact ⟨fun x y _ => Subsingleton.elim x y, fun t => ⟨0, Subsingleton.elim _ _⟩⟩
  | zero =>
    have hψ : ∀ x : Src U V R S 0, kunnethMap U V R S 0 x =
        HcupT (rfl : 0 + 0 = 0) (Equiv.piUnique _ x) := fun x => by
      rw [kunnethMap_apply, Fintype.sum_unique]
      rfl
    have key : ∀ z : R.obj (op ⊤) ⊗[k] S.obj (op ⊤),
        HcupT (rfl : 0 + 0 = 0) (TensorProduct.map (Hε R U) (Hε S V) z) =
          Hε (extTensor R S) (prodCover U V) z := by
      intro z
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' =>
        rw [map_add, map_add, hz, hz']
        exact (map_add (Hε (extTensor R S) (prodCover U V)) z z').symm
      | tmul x y =>
        rw [map_tmul, HcupT_tmul, Hε_apply, Hε_apply, Hcup_Hmk]
        refine (Hmk_congr _ _ (funext fun σ => ?_) _ (d_ε _ _ _)).trans
          (Hε_apply (extTensor R S) (prodCover U V) (x ⊗ₜ[k] y :
            (extTensor R S).obj (op ⊤))).symm
        rw [cup_apply, ε_apply, ε_apply, res_res, res_res]
        exact (res_extTensor_tmul R S (Z' := (⊤ : LatProd L₁ L₂)) le_top x y).symm
    have hM : Function.Bijective (TensorProduct.map (Hε R U) (Hε S V)) :=
      (TensorProduct.congr (LinearEquiv.ofBijective _ C₁.bijective_Hε)
        (LinearEquiv.ofBijective _ C₂.bijective_Hε)).bijective
    have hW := (extTensorContraction C₁ C₂).bijective_Hε
    have hcup : Function.Bijective (HcupT (P := R) (Q := S) (U := U) (V := V)
        (rfl : 0 + 0 = 0)) := by
      refine ⟨fun a b hab => ?_, fun t => ?_⟩
      · obtain ⟨a', rfl⟩ := hM.2 a
        obtain ⟨b', rfl⟩ := hM.2 b
        rw [key, key] at hab
        rw [hW.1 hab]
      · obtain ⟨z, rfl⟩ := hW.2 t
        exact ⟨_, key z⟩
    rw [show ⇑(kunnethMap U V R S 0) = HcupT (rfl : 0 + 0 = 0) ∘ Equiv.piUnique _ from funext hψ]
    exact hcup.comp (Equiv.piUnique _).bijective

omit [Fintype ι₂] in
/-- **The Künneth formula when the first presheaf has a contraction**, by dévissage in the second
variable. -/
theorem bijective_kunnethMap_of_contraction_left [Finite ι₂] {R : L₁ᵒᵖ ⥤ ModuleCat.{u} k}
    (C₁ : Contraction R U) (Q : L₂ᵒᵖ ⥤ ModuleCat.{u} k) (n : ℕ) :
    Function.Bijective (kunnethMap U V R Q n) := by
  have := Fintype.ofFinite ι₂
  classical
  exact LESMorphism.bijective (S := fun Q n => Src U V R Q n)
    (T := fun Q n => H (extTensor R Q) (prodCover U V) n)
    (ψ := fun Q n => (kunnethMap U V R Q n).toAddMonoidHom) (fun Q => piRestr Q V)
    (fun Q => coker (toPiRestr Q V)) (fun Q => lesRight R (isNerveSES_toPiRestr Q V))
    (fun Q n => bijective_kunnethMap_of_contraction C₁ (piRestrContraction Q V) n) Q n

variable (U V)

omit [Fintype ι₁] [Fintype ι₂] in
/-- **The Künneth formula for Čech cohomology over a field.** For presheaves `P` on `L₁` and `Q`
on `L₂` of vector spaces over a field `k`, and finite families `U`, `V`, the Alexander–Whitney
product `∏_{p + q = n} Ȟ^p(U, P) ⊗_k Ȟ^q(V, Q) ⟶ Ȟ^n(U × V, P ⊠ Q)` is bijective. -/
theorem bijective_kunnethMap [Finite ι₁] [Finite ι₂] (P : L₁ᵒᵖ ⥤ ModuleCat.{u} k)
    (Q : L₂ᵒᵖ ⥤ ModuleCat.{u} k) (n : ℕ) : Function.Bijective (kunnethMap U V P Q n) := by
  have := Fintype.ofFinite ι₁
  have := Fintype.ofFinite ι₂
  classical
  exact LESMorphism.bijective (S := fun P n => Src U V P Q n)
    (T := fun P n => H (extTensor P Q) (prodCover U V) n)
    (ψ := fun P n => (kunnethMap U V P Q n).toAddMonoidHom) (fun P => piRestr P U)
    (fun P => coker (toPiRestr P U)) (fun P => lesLeft Q (isNerveSES_toPiRestr P U))
    (fun P n => bijective_kunnethMap_of_contraction_left (piRestrContraction P U) Q n) P n

/-- **The Künneth isomorphism for Čech cohomology over a field.** -/
def kunnethEquiv (P : L₁ᵒᵖ ⥤ ModuleCat.{u} k) (Q : L₂ᵒᵖ ⥤ ModuleCat.{u} k) (n : ℕ) :
    Src U V P Q n ≃ₗ[k] H (extTensor P Q) (prodCover U V) n :=
  LinearEquiv.ofBijective _ (bijective_kunnethMap U V P Q n)

end Kunneth

end Stacks.CechKunneth

end
