module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.Complex

/-!
# Contractible Čech complexes and the effacing embedding

Let `P` be a presheaf of `k`-modules on a complete lattice `L` and `U : ι → L` a finite family.
This file supplies the two inputs of the dévissage proving the Künneth formula for Čech
cohomology [Stacks, Tag 0BED].

*Contractions.* A `Stacks.CechKunneth.Contraction` of a presheaf `R` along `U` is a family of
natural maps `E_i : R(Z ⊓ U_i) ⟶ R(Z)` with `∑_i E_i ∘ res = id`. It gives a contracting homotopy
`(h c)_s = ∑_i E_i(c_{i s}|)` of the Čech complex in positive degrees, so `Ȟ^{p+1}(U, R) = 0`, and
identifies `Ȟ^0(U, R)` with `R(⊤)`. This is the familiar fact that the Čech complex of a covering
containing the whole space is acyclic, in the form in which it survives tensor products.

*The effacing embedding.* For any `P`, the presheaf `P' : Z ↦ ∏_i P(Z ⊓ U_i)` has a contraction,
and `P ⟶ P'` is injective on every member of the nerve of `U`. Together with the objectwise
cokernel `P''` this is a sequence `P ⟶ P' ⟶ P''` short exact on the nerve, which is the Čech
shadow of the embedding `ℱ → ∏ j_{i,*}(ℱ|_{U_i})` used in the source.

## Main definitions

* `Stacks.CechKunneth.Contraction`, with the homotopy `Contraction.homotopy`.
* `Stacks.CechKunneth.piRestr`: the presheaf `Z ↦ ∏_i P(Z ⊓ U_i)`, with
  `Stacks.CechKunneth.piRestrContraction` and the embedding `Stacks.CechKunneth.toPiRestr`.
* `Stacks.CechKunneth.coker`: the objectwise cokernel of a morphism of presheaves.

## Main results

* `Stacks.CechKunneth.Contraction.Hmk_eq_zero`: `Ȟ^{p+1}(U, R) = 0`.
* `Stacks.CechKunneth.Contraction.bijective_Hε`: `R(⊤) ⟶ Ȟ^0(U, R)` is bijective.
* `Stacks.CechKunneth.isNerveSES_toPiRestr`: `P ⟶ P' ⟶ P''` is short exact on the nerve.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.CechKunneth

variable {k : Type u} [CommRing k] {L : Type u} [CompleteLattice L] {ι : Type u}

theorem inter_cons_eq {p : ℕ} (U : ι → L) (i : ι) (s : Fin (p + 1) → ι) :
    inter U (Fin.cons i s : Fin (p + 2) → ι) = inter U s ⊓ U i := by
  refine le_antisymm (le_inf ?_ ?_) (le_iInf fun j => ?_)
  · exact le_iInf fun j => (iInf_le _ j.succ).trans (by rw [Fin.cons_succ])
  · exact (iInf_le _ 0).trans (by rw [Fin.cons_zero])
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [Fin.cons_zero]; exact inf_le_right
    · rw [Fin.cons_succ]; exact inf_le_left.trans (inter_le_apply U s j)

theorem le_inter_const (U : ι → L) (i : ι) : U i ≤ inter U (fun _ : Fin 1 => i) :=
  le_iInf fun _ => le_rfl

theorem cons_comp_succAbove_succ {p : ℕ} (i : ι) (s : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    (Fin.cons i s : Fin (p + 3) → ι) ∘ j.succ.succAbove =
      (Fin.cons i (s ∘ j.succAbove) : Fin (p + 2) → ι) := by
  funext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp
  · simp [Fin.succ_succAbove_succ]

theorem cons_comp_succ {p : ℕ} (i : ι) (s : Fin (p + 1) → ι) :
    (Fin.cons i s : Fin (p + 2) → ι) ∘ (0 : Fin (p + 2)).succAbove = s := by
  funext x
  simp

/-! ### Contractions -/

/-- **A contraction of a presheaf along a family `U`**: natural maps `E_i : R(Z ⊓ U_i) ⟶ R(Z)`
with `∑_i E_i ∘ res = id`. -/
structure Contraction [Fintype ι] (R : Lᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L) where
  /-- The maps `E_i : R(Z ⊓ U_i) ⟶ R(Z)`. -/
  E : ∀ (i : ι) (Z : L), R.obj (op (Z ⊓ U i)) →ₗ[k] R.obj (op Z)
  /-- The maps `E_i` commute with restriction. -/
  natural : ∀ (i : ι) {Z Z' : L} (h : Z' ≤ Z) (x : R.obj (op (Z ⊓ U i))),
    res R h (E i Z x) = E i Z' (res R (inf_le_inf_right (U i) h) x)
  /-- The maps `E_i` decompose the identity. -/
  sum_eq : ∀ (Z : L) (x : R.obj (op Z)), ∑ i, E i Z (res R inf_le_left x) = x

namespace Contraction

variable [Fintype ι] {R : Lᵒᵖ ⥤ ModuleCat.{u} k} {U : ι → L} (C : Contraction R U)

/-- The contracting homotopy `(h c)_s = ∑_i E_i(c_{i s}|)`. -/
def homotopy (p : ℕ) : Cochain R U (p + 1) →ₗ[k] Cochain R U p :=
  LinearMap.pi fun s => ∑ i, C.E i (inter U s) ∘ₗ res R (inter_cons_eq U i s).ge ∘ₗ
    LinearMap.proj (R := k) (φ := fun t : Fin (p + 2) → ι => R.obj (op (inter U t)))
      (Fin.cons i s)

theorem homotopy_apply (p : ℕ) (c : Cochain R U (p + 1)) (s : Fin (p + 1) → ι) :
    C.homotopy p c s =
      ∑ i, C.E i (inter U s) (res R (inter_cons_eq U i s).ge (c (Fin.cons i s))) := by
  simp only [homotopy, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

/-- **The homotopy identity** `d h + h d = id` in positive degrees. -/
theorem d_homotopy_add (p : ℕ) (c : Cochain R U (p + 1)) :
    d R U p (C.homotopy p c) + C.homotopy (p + 1) (d R U (p + 1) c) = c := by
  funext s
  rw [Pi.add_apply]
  let T : ι → Fin (p + 2) → R.obj (op (inter U s)) := fun i j =>
    C.E i (inter U s) (res R ((inf_le_inf_right (U i) (inter_le_comp U j.succAbove s)).trans
      (inter_cons_eq U i _).ge) (c (Fin.cons i (s ∘ j.succAbove))))
  have h1 : d R U p (C.homotopy p c) s =
      ∑ j : Fin (p + 2), ∑ i : ι, ((-1 : ℤ) ^ (j : ℕ)) • T i j := by
    rw [d_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [homotopy_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [C.natural, res_res]
  have h2 : C.homotopy (p + 1) (d R U (p + 1) c) s =
      c s + ∑ j : Fin (p + 2), ∑ i : ι, (-((-1 : ℤ) ^ (j : ℕ))) • T i j := by
    rw [homotopy_apply]
    simp only [d_apply, map_sum, map_zsmul, res_res]
    simp only [Fin.sum_univ_succ (n := p + 2), Finset.sum_add_distrib]
    congr 1
    · conv_rhs => rw [← C.sum_eq (inter U s) (c s)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_zero, pow_zero, one_smul]
      exact congrArg (C.E i (inter U s)) (res_congr R (cons_comp_succ i s) c _ _)
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_succ, pow_succ, mul_neg_one]
      exact congrArg (((-((-1 : ℤ) ^ (j : ℕ)))) • ·)
        (congrArg (C.E i (inter U s)) (res_congr R (cons_comp_succAbove_succ i s j) c _ _))
  rw [h1, h2]
  simp only [neg_smul, Finset.sum_neg_distrib]
  abel

include C in
/-- **Positive degree Čech cohomology of a presheaf with a contraction vanishes.** -/
theorem Hmk_eq_zero {p : ℕ} (z : Cochain R U (p + 1)) (hz : d R U (p + 1) z = 0) :
    Hmk R U z hz = 0 := by
  rw [Hmk_eq_zero_iff_succ]
  refine ⟨C.homotopy p z, ?_⟩
  have h := C.d_homotopy_add p z
  rwa [hz, map_zero, add_zero] at h

include C in
theorem subsingleton_H (p : ℕ) : Subsingleton (H R U (p + 1)) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨z, hz, rfl⟩ := Hmk_surjective R U x
  obtain ⟨z', hz', rfl⟩ := Hmk_surjective R U y
  rw [C.Hmk_eq_zero, C.Hmk_eq_zero]

end Contraction

/-- The constant cochain attached to a section over `⊤`. -/
def ε (R : Lᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L) : R.obj (op ⊤) →ₗ[k] Cochain R U 0 :=
  LinearMap.pi fun _ => res R le_top

theorem ε_apply (R : Lᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L) (x : R.obj (op ⊤))
    (s : Fin 1 → ι) : ε R U x s = res R le_top x :=
  rfl

theorem cons_comp_one_succAbove (i : ι) (s : Fin 1 → ι) :
    (Fin.cons i s : Fin 2 → ι) ∘ (1 : Fin 2).succAbove = fun _ => i := by
  funext x
  rw [Subsingleton.elim x 0]
  rfl

/-- The Čech differential in degree zero, as a difference of two restrictions. -/
private theorem d_zero_apply {P : Lᵒᵖ ⥤ ModuleCat.{u} k} {U : ι → L} (c : Cochain P U 0)
    (s : Fin 2 → ι) :
    d P U 0 c s = res P (inter_le_comp U (0 : Fin 2).succAbove s) (c (s ∘ (0 : Fin 2).succAbove)) -
      res P (inter_le_comp U (1 : Fin 2).succAbove s) (c (s ∘ (1 : Fin 2).succAbove)) := by
  rw [d_apply, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_one_smul, sub_eq_add_neg]

theorem d_ε (R : Lᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L) (x : R.obj (op ⊤)) :
    d R U 0 (ε R U x) = 0 := by
  funext s
  rw [d_zero_apply, Pi.zero_apply, ε_apply, ε_apply, res_res, res_res, sub_self]

/-- The class in `Ȟ^0` of the constant cochain attached to a section over `⊤`. -/
def Hε (R : Lᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L) : R.obj (op ⊤) →ₗ[k] H R U 0 :=
  (coboundaries R U 0).mkQ ∘ₗ LinearMap.codRestrict (cocycles R U 0) (ε R U) (d_ε R U)

theorem Hε_apply (R : Lᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L) (x : R.obj (op ⊤)) :
    Hε R U x = Hmk R U (ε R U x) (d_ε R U x) :=
  rfl

namespace Contraction

variable [Fintype ι] {R : Lᵒᵖ ⥤ ModuleCat.{u} k} {U : ι → L} (C : Contraction R U)

/-- The homotopy in degree zero, landing in the sections over `⊤`. -/
def homotopy₀ : Cochain R U 0 →ₗ[k] R.obj (op ⊤) :=
  ∑ i, C.E i ⊤ ∘ₗ res R (inf_le_right.trans (le_inter_const U i)) ∘ₗ
    LinearMap.proj (R := k) (φ := fun t : Fin 1 → ι => R.obj (op (inter U t))) (fun _ => i)

theorem homotopy₀_apply (c : Cochain R U 0) :
    C.homotopy₀ c = ∑ i, C.E i ⊤ (res R (inf_le_right.trans (le_inter_const U i))
      (c fun _ => i)) := by
  simp only [homotopy₀, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

theorem homotopy₀_ε (x : R.obj (op ⊤)) : C.homotopy₀ (ε R U x) = x := by
  rw [homotopy₀_apply]
  simp only [ε_apply, res_res]
  exact C.sum_eq ⊤ x

/-- The homotopy identity in degree zero. -/
theorem ε_homotopy₀_add (c : Cochain R U 0) :
    ε R U (C.homotopy₀ c) + C.homotopy 0 (d R U 0 c) = c := by
  funext s
  rw [Pi.add_apply, homotopy_apply, ε_apply, homotopy₀_apply, map_sum, ← Finset.sum_add_distrib]
  conv_rhs => rw [← C.sum_eq (inter U s) (c s)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C.natural, res_res, ← map_add]
  refine congrArg (C.E i (inter U s)) ?_
  rw [d_zero_apply, map_sub, res_res, res_res,
    res_congr R (cons_comp_succ i s) c _ (inf_le_left : inter U s ⊓ U i ≤ inter U s),
    res_congr R (cons_comp_one_succAbove i s) c _
      (inf_le_right.trans (le_inter_const U i))]
  abel

include C in
/-- **`Ȟ^0(U, R)` is `R(⊤)` for a presheaf with a contraction.** -/
theorem bijective_Hε : Function.Bijective (Hε R U) := by
  refine ⟨fun x y h => ?_, fun z => ?_⟩
  · rw [Hε_apply, Hε_apply, ← sub_eq_zero, ← Hmk_sub, Hmk_eq_zero_iff_zero, ← map_sub] at h
    rw [← C.homotopy₀_ε x, ← C.homotopy₀_ε y, ← sub_eq_zero, ← map_sub, ← map_sub, h, map_zero]
  · obtain ⟨c, hc, rfl⟩ := Hmk_surjective R U z
    refine ⟨C.homotopy₀ c, Hmk_congr R U ?_ _ _⟩
    have h := C.ε_homotopy₀_add c
    rwa [hc, map_zero, add_zero] at h

end Contraction

/-! ### The effacing embedding -/

section PiRestr

variable (P : Lᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L)

/-- The presheaf `Z ↦ ∏_i P(Z ⊓ U_i)`. -/
def piRestr : Lᵒᵖ ⥤ ModuleCat.{u} k where
  obj Z := ModuleCat.of k (∀ i, P.obj (op (Z.unop ⊓ U i)))
  map f := ModuleCat.ofHom (LinearMap.pi fun i =>
    res P (inf_le_inf_right (U i) (leOfHom f.unop)) ∘ₗ LinearMap.proj i)
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun x => funext fun i => res_self P _ (x i))
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => funext fun i =>
    (res_res P _ _ (x i)).symm)

theorem res_piRestr_apply {Z Z' : L} (h : Z ≤ Z') (x : (piRestr P U).obj (op Z')) (i : ι) :
    res (piRestr P U) h x i = res P (inf_le_inf_right (U i) h) (x i) :=
  rfl

/-- The embedding `P ⟶ ∏_i P(- ⊓ U_i)`. -/
def toPiRestr : P ⟶ piRestr P U where
  app _ := ModuleCat.ofHom (LinearMap.pi fun _ => res P inf_le_left)
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun x => funext fun _ =>
    (res_res P _ _ x).trans (res_res P _ _ x).symm)

theorem toPiRestr_app_apply (Z : L) (x : P.obj (op Z)) (i : ι) :
    ((toPiRestr P U).app (op Z)).hom x i = res P inf_le_left x :=
  rfl

theorem injective_toPiRestr {p : ℕ} (s : Fin (p + 1) → ι) :
    Function.Injective ((toPiRestr P U).app (op (inter U s))).hom := by
  intro x y h
  have h' := congrArg (res P (le_inf le_rfl (inter_le_apply U s 0))) (congrFun h (s 0))
  rwa [toPiRestr_app_apply, toPiRestr_app_apply, res_res, res_res, res_self, res_self] at h'

variable [Fintype ι] [DecidableEq ι]

/-- **The presheaf `Z ↦ ∏_i P(Z ⊓ U_i)` has a contraction along `U`.** -/
def piRestrContraction : Contraction (piRestr P U) U where
  E i Z := LinearMap.single k (fun i => P.obj (op (Z ⊓ U i))) i ∘ₗ
    res P (le_inf le_rfl inf_le_right) ∘ₗ LinearMap.proj i
  natural i Z Z' h x := by
    funext j
    change res P _ (Pi.single (M := fun i => P.obj (op (Z ⊓ U i))) i (res P _ (x i)) j) =
      Pi.single (M := fun i => P.obj (op (Z' ⊓ U i))) i (res P _ (res P _ (x i))) j
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, Pi.single_eq_same, res_res, res_res]
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]
  sum_eq Z x := by
    conv_rhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun i _ => ?_
    change Pi.single (M := fun i => P.obj (op (Z ⊓ U i))) i (res P _ (res P _ (x i))) = _
    rw [res_res, res_self]

end PiRestr

/-! ### Cokernels -/

section Coker

variable {P P' : Lᵒᵖ ⥤ ModuleCat.{u} k} (φ : P ⟶ P')

/-- The objectwise cokernel of a morphism of presheaves. -/
def coker : Lᵒᵖ ⥤ ModuleCat.{u} k where
  obj Z := ModuleCat.of k (P'.obj Z ⧸ LinearMap.range (φ.app Z).hom)
  map {Z Z'} f := ModuleCat.ofHom (Submodule.mapQ _ _ (P'.map f).hom (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(P.map f).hom x, by
      change (P.map f ≫ φ.app Z').hom x = (φ.app Z ≫ P'.map f).hom x
      rw [φ.naturality]⟩))
  map_id Z := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    simp [P'.map_id]))
  map_comp f g := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    simp [P'.map_comp]))

/-- The projection onto the objectwise cokernel. -/
def cokerπ : P' ⟶ coker φ where
  app Z := ModuleCat.ofHom (LinearMap.range (φ.app Z).hom).mkQ
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem exact_cokerπ (Z : Lᵒᵖ) : Function.Exact (φ.app Z).hom ((cokerπ φ).app Z).hom :=
  LinearMap.exact_map_mkQ_range _

theorem surjective_cokerπ (Z : Lᵒᵖ) : Function.Surjective ((cokerπ φ).app Z).hom :=
  Submodule.mkQ_surjective _

end Coker

/-- **The effacing sequence** `P ⟶ ∏_i P(- ⊓ U_i) ⟶ coker` is short exact on the nerve of `U`. -/
theorem isNerveSES_toPiRestr (P : Lᵒᵖ ⥤ ModuleCat.{u} k) (U : ι → L) :
    IsNerveSES U (toPiRestr P U) (cokerπ (toPiRestr P U)) where
  injective s := injective_toPiRestr P U s
  exact _ := exact_cokerπ _ _
  surjective _ := surjective_cokerπ _ _

end Stacks.CechKunneth

end
