module

public import StacksFrontier.Algebra.DGA.Abelian.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Products and direct sums of differential graded modules

The product and the direct sum of a family `(f i)` of right differential graded modules over a
differential graded algebra `(A, d)`, computed degreewise: the product has degree-`n` part
`∏ᵢ (f i)^n` and underlying module `⊕ₙ ∏ᵢ (f i)^n`, and the direct sum has degree-`n` part
`⊕ᵢ (f i)^n`. The right action and the differential are the componentwise ones. This file builds
the projections and the lift of the product, and the injections and the descent of the direct sum.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w w' w'' t

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

namespace DifferentialGradedModule

section Product

variable {I : Type w} (f : I → DifferentialGradedModule.{u, v, w} A)

/-- The degree-`n` part of the product, as an `R`-submodule of `∏ᵢ (f i).M`:
`Pⁿ = ∏ᵢ (f i).grading n`. -/
def prodPn (n : ℤ) : Submodule R (∀ i, (f i).M) :=
  Submodule.pi Set.univ (fun i ↦ (f i).grading n)

theorem mem_prodPn {n : ℤ} (x : ∀ i, (f i).M) :
    x ∈ prodPn f n ↔ ∀ i, x i ∈ (f i).grading n := by
  simp [prodPn, Submodule.mem_pi]

theorem map_proj_prodPn (i : I) (m : ℤ) :
    Submodule.map (LinearMap.proj i) (prodPn f m) ≤ (f i).grading m := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_prodPn f x).1 hx i

/-- The degree-`n` pieces `Pⁿ` are independent. -/
theorem prodPn_indep : iSupIndep (prodPn f) := by
  rw [iSupIndep_def]
  intro n
  rw [Submodule.disjoint_def]
  intro x hxn hxsup
  ext i
  have hgi : iSupIndep (f i).grading :=
    (DirectSum.Decomposition.isInternal (f i).grading).submodule_iSupIndep
  rw [iSupIndep_def] at hgi
  have hd := hgi n
  rw [Submodule.disjoint_def] at hd
  have hproj : x i ∈ ⨆ m, ⨆ (_ : m ≠ n), (f i).grading m := by
    have h : x i ∈ Submodule.map (LinearMap.proj i) (⨆ m, ⨆ (_ : m ≠ n), prodPn f m) :=
      ⟨x, hxsup, rfl⟩
    rw [Submodule.map_iSup] at h
    have hle : (⨆ m, Submodule.map (LinearMap.proj i) (⨆ (_ : m ≠ n), prodPn f m))
        ≤ ⨆ m, ⨆ (_ : m ≠ n), (f i).grading m := by
      refine iSup_le (fun m ↦ ?_)
      rw [Submodule.map_iSup]
      exact iSup_le (fun hm ↦ le_trans (map_proj_prodPn f i m)
        (le_iSup₂ (f := fun m _ ↦ (f i).grading m) m hm))
    exact hle h
  simpa using hd (x i) ((mem_prodPn f x).1 hxn i) hproj

/-- A homogeneous element `a ∈ A.grading m` sends `Pⁿ` into `P^(n+m)`. -/
theorem smul_prodPn_hom (n m : ℤ) (a : A.A) (ha : a ∈ A.grading m) (x : ∀ i, (f i).M)
    (hx : x ∈ prodPn f n) : (MulOpposite.op a) • x ∈ prodPn f (n + m) := by
  rw [mem_prodPn] at hx ⊢
  intro i
  have : ((MulOpposite.op a) • x) i = (MulOpposite.op a) • (x i) := rfl
  rw [this]
  exact (f i).smul_mem n m (x i) a (hx i) ha

/-- If `φ` sends each graded piece of `M` into `S`, then it sends all of `M` into `S`. -/
theorem map_mem_of_decompose {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (G : ℤ → Submodule R M) [DirectSum.Decomposition G] (S : Submodule R N)
    (φ : M →+ N) (h : ∀ n y, y ∈ G n → φ y ∈ S) (y : M) : φ y ∈ S := by
  classical
  rw [← DirectSum.sum_support_decompose G y, map_sum]
  exact Submodule.sum_mem _ fun n _ ↦ h n _ (DirectSum.decompose G y n).2

/-- The submodule `⨆ₙ Pⁿ` of `∏ᵢ (f i).M`, for graded pieces `Pⁿ` stable under homogeneous
elements of `A`, as an `Aᵐᵒᵖ`-submodule. -/
def iSupSub (P : ℤ → Submodule R (∀ i, (f i).M))
    (hP : ∀ n m (a : A.A), a ∈ A.grading m → ∀ x, x ∈ P n → (MulOpposite.op a) • x ∈ P (n + m)) :
    Submodule (MulOpposite A.A) (∀ i, (f i).M) where
  carrier := {x | x ∈ ⨆ n, P n}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    exact (⨆ n, P n).add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact (⨆ n, P n).zero_mem
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [show c • x = (MulOpposite.op c.unop) • x from rfl]
    induction hx using Submodule.iSup_induction' with
    | mem n y hy =>
        exact map_mem_of_decompose A.grading _
          (AddMonoidHom.mk' (fun a : A.A ↦ (MulOpposite.op a) • y) fun a b ↦ by
            simp [add_smul]) (fun m a ha ↦ Submodule.mem_iSup_of_mem (n + m) (hP n m a ha y hy))
          c.unop
    | zero => rw [smul_zero]; exact (⨆ n, P n).zero_mem
    | add a b _ _ iha ihb => rw [smul_add]; exact (⨆ n, P n).add_mem iha ihb

/-- The product object as an `Aᵐᵒᵖ`-submodule of `∏ᵢ (f i).M`, with carrier `⨆ₙ Pⁿ`. -/
def prodSub : Submodule (MulOpposite A.A) (∀ i, (f i).M) :=
  iSupSub f (prodPn f) (smul_prodPn_hom f)

theorem mem_prodSub (x : ∀ i, (f i).M) :
    x ∈ prodSub f ↔ x ∈ ⨆ n, prodPn f n := Iff.rfl

theorem prodSub_restrict_eq : (prodSub f).restrictScalars R = ⨆ n, prodPn f n := by
  apply SetLike.coe_injective; rfl

/-- The componentwise differential on `∏ᵢ (f i).M`. -/
noncomputable def prodD0 : (∀ i, (f i).M) →ₗ[R] (∀ i, (f i).M) :=
  LinearMap.pi (fun i ↦ ((f i).d).comp (LinearMap.proj i))

theorem prodD0_apply (x : ∀ i, (f i).M) (i : I) : prodD0 f x i = (f i).d (x i) := by
  simp [prodD0, LinearMap.pi_apply]

/-- `prodD0` sends `Pⁿ` into `P^(n+1)`. -/
theorem prodD0_prodPn (n : ℤ) (x : ∀ i, (f i).M) (hx : x ∈ prodPn f n) :
    prodD0 f x ∈ prodPn f (n + 1) := by
  rw [mem_prodPn] at hx ⊢
  intro i
  rw [prodD0_apply]
  exact (f i).d_mem n (x i) (hx i)

/-- `prodD0` preserves `⨆ₙ Pⁿ` whenever it sends each `Pⁿ` into `P^(n+1)`. -/
theorem prodD0_mem_iSup (P : ℤ → Submodule R (∀ i, (f i).M))
    (hP : ∀ n x, x ∈ P n → prodD0 f x ∈ P (n + 1)) (x : ∀ i, (f i).M) (hx : x ∈ ⨆ n, P n) :
    prodD0 f x ∈ ⨆ n, P n :=
  (iSup_le fun n y hy ↦ Submodule.mem_iSup_of_mem (n + 1) (hP n y hy) :
    ⨆ n, P n ≤ (⨆ n, P n).comap (prodD0 f)) hx

theorem prodD0_prodD0 (x : ∀ i, (f i).M) : prodD0 f (prodD0 f x) = 0 := by
  funext i
  rw [prodD0_apply, prodD0_apply]
  simpa using LinearMap.congr_fun (f i).d_comp_d (x i)

/-- The Leibniz rule for `prodD0`, on homogeneous elements. -/
theorem prodD0_leibniz (n m : ℤ) (x : ∀ i, (f i).M) (hx : x ∈ prodPn f n) (a : A.A)
    (ha : a ∈ A.grading m) : prodD0 f (MulOpposite.op a • x)
      = MulOpposite.op a • prodD0 f x + (n.negOnePow : ℤ) • (MulOpposite.op (A.d a) • x) := by
  funext i
  exact (f i).leibniz n m (x i) a ((mem_prodPn f x).1 hx i) ha

/-- `prodD0` preserves the product submodule `prodSub`. -/
theorem prodD0_mem (x : ∀ i, (f i).M) (hx : x ∈ (prodSub f).restrictScalars R) :
    prodD0 f x ∈ (prodSub f).restrictScalars R := by
  rw [prodSub_restrict_eq] at hx ⊢
  exact prodD0_mem_iSup f _ (prodD0_prodPn f) x hx

/-- The grading on the product object. -/
noncomputable def prodGrading (n : ℤ) : Submodule R ↥(prodSub f) :=
  Submodule.inducedGrading (prodPn f) ((prodSub f).restrictScalars R) n

/-- The differential on the product object. -/
noncomputable def prodD : ↥(prodSub f) →ₗ[R] ↥(prodSub f) :=
  LinearMap.restrict (prodD0 f) (p := (prodSub f).restrictScalars R)
    (q := (prodSub f).restrictScalars R) (prodD0_mem f)

/-- The product object `P = ⊕ₙ ∏ᵢ (f i).grading n`. -/
noncomputable def prodObj : DifferentialGradedModule.{u, v, w} A where
  M := ↥(prodSub f)
  grading := prodGrading f
  decomposition := by
    change DirectSum.Decomposition (prodGrading f)
    unfold prodGrading
    exact Submodule.inducedGrading.decompositionOfEqISup (prodPn f) (prodPn_indep f)
      ((prodSub f).restrictScalars R) (prodSub_restrict_eq f)
  smul_mem := by
    intro n m x a hx ha
    exact smul_prodPn_hom f n m a ha x hx
  d := prodD f
  d_comp_d := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext (prodD0_prodD0 f x)
  d_mem := by
    intro n x hx
    exact prodD0_prodPn f n x hx
  leibniz := by
    intro n m x a hx ha
    exact Subtype.ext (prodD0_leibniz f n m x hx a ha)

@[simp] theorem prodObj_M : (prodObj f).M = ↥(prodSub f) := rfl

@[simp] theorem prodObj_grading : (prodObj f).grading = prodGrading f := rfl

@[simp] theorem prodObj_d : (prodObj f).d = prodD f := rfl

/-- The `i`-th projection `prodObj f ⟶ f i`. -/
noncomputable def prodπ (i : I) : prodObj f ⟶ f i where
  toFun := (LinearMap.proj i).comp ((prodSub f).restrictScalars R).subtype
  map_smul := by intro x a; rfl
  map_grading := by
    intro n x hx
    rw [prodObj_grading, prodGrading, Submodule.inducedGrading, Submodule.mem_comap] at hx
    exact (mem_prodPn f _).1 hx i
  map_d := by
    ext x
    rfl

@[simp] theorem prodπ_toFun_apply (i : I) (x : ↥(prodSub f)) :
    (prodπ f i).toFun x = (x : ∀ i, (f i).M) i := rfl

/-- For `t` in a cone point `T`, the function `i ↦ (g i).toFun t` lies in `prodSub`. -/
theorem prodLift_mem {T : DifferentialGradedModule.{u, v, w} A}
    (g : ∀ i, T ⟶ f i) (t : T.M) :
    (fun i => (g i).toFun t) ∈ (prodSub f).restrictScalars R := by
  rw [prodSub_restrict_eq]
  exact map_mem_of_decompose T.grading _ (LinearMap.pi fun i ↦ (g i).toFun).toAddMonoidHom
    (fun n y hy ↦ Submodule.mem_iSup_of_mem n
      ((mem_prodPn f _).2 fun i ↦ (g i).map_grading n y hy)) t

/-- The lift of a cone `(g i : T ⟶ f i)` to `T ⟶ prodObj f`. -/
noncomputable def prodLift {T : DifferentialGradedModule.{u, v, w} A} (g : ∀ i, T ⟶ f i) :
    T ⟶ prodObj f where
  toFun := LinearMap.codRestrict ((prodSub f).restrictScalars R)
    (LinearMap.pi (fun i ↦ (g i).toFun)) (fun t ↦ prodLift_mem f g t)
  map_smul := by
    intro x a
    apply Subtype.ext
    funext i
    change (g i).toFun (MulOpposite.op a • x) = MulOpposite.op a • (g i).toFun x
    exact (g i).map_smul x a
  map_grading := by
    intro n x hx
    rw [prodObj_grading, prodGrading, Submodule.inducedGrading, Submodule.mem_comap]
    change (fun i ↦ (g i).toFun x) ∈ prodPn f n
    rw [mem_prodPn]
    intro i
    exact (g i).map_grading n x hx
  map_d := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext i
    change (g i).toFun (T.d x) = (f i).d ((g i).toFun x)
    simpa using LinearMap.congr_fun (g i).map_d x

end Product

section Coproduct

variable {I : Type w} (f : I → DifferentialGradedModule.{u, v, w} A)

/-- The finitely-supported functions inside `∏ᵢ (f i).M`, as an `R`-submodule. This is the
underlying module of the direct sum `⊕ᵢ (f i).M`. -/
def finsuppSub : Submodule R (∀ i, (f i).M) where
  carrier := {x | {i | x i ≠ 0}.Finite}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    apply (ha.union hb).subset
    intro i hi
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.add_apply] at *
    by_contra h
    push Not at h
    apply hi
    rw [h.1, h.2, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq] at *
    apply ha.subset
    intro i hi
    simp only [Set.mem_ofPred_eq, Pi.smul_apply] at *
    intro h; apply hi; rw [h]; simp

theorem mem_finsuppSub (x : ∀ i, (f i).M) :
    x ∈ finsuppSub f ↔ {i | x i ≠ 0}.Finite := Iff.rfl

/-- The degree-`n` part of the coproduct, as an `R`-submodule of `∏ᵢ (f i).M`:
finitely-supported functions whose components are homogeneous of degree `n`. -/
def coprodPn (n : ℤ) : Submodule R (∀ i, (f i).M) :=
  finsuppSub f ⊓ prodPn f n

theorem mem_coprodPn {n : ℤ} (x : ∀ i, (f i).M) :
    x ∈ coprodPn f n ↔ {i | x i ≠ 0}.Finite ∧ ∀ i, x i ∈ (f i).grading n := by
  simp [coprodPn, mem_finsuppSub, mem_prodPn]

theorem coprodPn_le_prodPn (n : ℤ) : coprodPn f n ≤ prodPn f n := inf_le_right

/-- The degree-`n` pieces `coprodPn` are independent. -/
theorem coprodPn_indep : iSupIndep (coprodPn f) :=
  (prodPn_indep f).mono (coprodPn_le_prodPn f)

/-- The support of `z` lies in `S` if it lies in the support of `x ⊆ S`. -/
theorem support_subset_of_forall {x z : ∀ i, (f i).M} {S : Set I}
    (hx : {i | x i ≠ 0} ⊆ S) (h : ∀ i, x i = 0 → z i = 0) : {i | z i ≠ 0} ⊆ S :=
  fun i hi ↦ hx fun h0 ↦ hi (h i h0)

/-- Finitely supported, homogeneous `z` whose support lies in that of `x ∈ coprodPn f n`
lies in `coprodPn f m`. -/
theorem mem_coprodPn_of_forall {n m : ℤ} (x z : ∀ i, (f i).M) (hx : x ∈ coprodPn f n)
    (h : ∀ i, x i = 0 → z i = 0) (hz : z ∈ prodPn f m) : z ∈ coprodPn f m :=
  ⟨((mem_coprodPn f x).1 hx).1.subset (support_subset_of_forall f subset_rfl h), hz⟩

/-- A homogeneous element `a ∈ A.grading m` sends `coprodPn n` into `coprodPn (n+m)`. -/
theorem smul_coprodPn_hom (n m : ℤ) (a : A.A) (ha : a ∈ A.grading m) (x : ∀ i, (f i).M)
    (hx : x ∈ coprodPn f n) : (MulOpposite.op a) • x ∈ coprodPn f (n + m) :=
  mem_coprodPn_of_forall f x _ hx (fun i h ↦ by
    change MulOpposite.op a • x i = 0
    rw [h, smul_zero])
    (smul_prodPn_hom f n m a ha x (coprodPn_le_prodPn f n hx))

/-- The coproduct object as an `Aᵐᵒᵖ`-submodule of `∏ᵢ (f i).M`, carrier `⨆ₙ coprodPn n`. -/
def coprodSub : Submodule (MulOpposite A.A) (∀ i, (f i).M) :=
  iSupSub f (coprodPn f) (smul_coprodPn_hom f)

theorem mem_coprodSub (x : ∀ i, (f i).M) :
    x ∈ coprodSub f ↔ x ∈ ⨆ n, coprodPn f n := Iff.rfl

theorem coprodSub_restrict_eq : (coprodSub f).restrictScalars R = ⨆ n, coprodPn f n := by
  apply SetLike.coe_injective; rfl

/-- `prodD0` (componentwise differential) sends `coprodPn n` into `coprodPn (n+1)`. -/
theorem prodD0_coprodPn (n : ℤ) (x : ∀ i, (f i).M) (hx : x ∈ coprodPn f n) :
    prodD0 f x ∈ coprodPn f (n + 1) :=
  mem_coprodPn_of_forall f x _ hx (fun i h ↦ by rw [prodD0_apply, h, map_zero])
    (prodD0_prodPn f n x (coprodPn_le_prodPn f n hx))

/-- `prodD0` preserves the coproduct submodule `coprodSub`. -/
theorem prodD0_coprodMem (x : ∀ i, (f i).M) (hx : x ∈ (coprodSub f).restrictScalars R) :
    prodD0 f x ∈ (coprodSub f).restrictScalars R := by
  rw [coprodSub_restrict_eq] at hx ⊢
  exact prodD0_mem_iSup f _ (prodD0_coprodPn f) x hx

/-- The grading on the coproduct object. -/
noncomputable def coprodGrading (n : ℤ) : Submodule R ↥(coprodSub f) :=
  Submodule.inducedGrading (coprodPn f) ((coprodSub f).restrictScalars R) n

/-- The differential on the coproduct object. -/
noncomputable def coprodD : ↥(coprodSub f) →ₗ[R] ↥(coprodSub f) :=
  LinearMap.restrict (prodD0 f) (p := (coprodSub f).restrictScalars R)
    (q := (coprodSub f).restrictScalars R) (prodD0_coprodMem f)

/-- The coproduct object `S = ⊕ₙ ⊕ᵢ (f i).grading n` (underlying direct sum). -/
noncomputable def coprodObj : DifferentialGradedModule.{u, v, w} A where
  M := ↥(coprodSub f)
  grading := coprodGrading f
  decomposition := by
    change DirectSum.Decomposition (coprodGrading f)
    unfold coprodGrading
    exact Submodule.inducedGrading.decompositionOfEqISup (coprodPn f) (coprodPn_indep f)
      ((coprodSub f).restrictScalars R) (coprodSub_restrict_eq f)
  smul_mem := by
    intro n m x a hx ha
    exact smul_coprodPn_hom f n m a ha x hx
  d := coprodD f
  d_comp_d := by
    apply LinearMap.ext
    intro x
    exact Subtype.ext (prodD0_prodD0 f x)
  d_mem := by
    intro n x hx
    exact prodD0_coprodPn f n x hx
  leibniz := by
    intro n m x a hx ha
    exact Subtype.ext (prodD0_leibniz f n m x (coprodPn_le_prodPn f n hx) a ha)

@[simp] theorem coprodObj_M : (coprodObj f).M = ↥(coprodSub f) := rfl

@[simp] theorem coprodObj_grading : (coprodObj f).grading = coprodGrading f := rfl

@[simp] theorem coprodObj_d : (coprodObj f).d = coprodD f := rfl

/-- Membership in `coprodSub` entails finite support. -/
theorem coprodSub_finite (x : ∀ i, (f i).M) (hx : x ∈ (coprodSub f).restrictScalars R) :
    {i | x i ≠ 0}.Finite := by
  rw [coprodSub_restrict_eq] at hx
  induction hx using Submodule.iSup_induction' with
  | mem n y hy => exact ((mem_coprodPn f y).1 hy).1
  | zero =>
      apply Set.Finite.subset (Set.finite_empty)
      intro i hi; simp only [Set.mem_ofPred_eq, Pi.zero_apply, ne_eq, not_true_eq_false] at hi
  | add a b _ _ iha ihb =>
      apply (iha.union ihb).subset
      intro i hi
      simp only [Set.mem_ofPred_eq, Pi.add_apply, Set.mem_union] at *
      by_contra h
      push Not at h
      exact hi (by rw [h.1, h.2, add_zero])

/-- The canonical inclusion `(f i).M → ∏ⱼ (f j).M` (a single nonzero coordinate). -/
noncomputable def coprodIncl0 (i : I) : (f i).M →ₗ[R] (∀ j, (f j).M) :=
  letI := Classical.decEq I
  LinearMap.single R (fun j ↦ (f j).M) i

theorem coprodIncl0_apply_self (i : I) (y : (f i).M) :
    coprodIncl0 f i y i = y := by
  classical
  change (Pi.single i y : ∀ j, (f j).M) i = y
  simp

theorem coprodIncl0_apply_ne (i : I) (y : (f i).M) (j : I) (h : j ≠ i) :
    coprodIncl0 f i y j = 0 := by
  classical
  change (Pi.single i y : ∀ k, (f k).M) j = 0
  rw [Pi.single_eq_of_ne h]

/-- `coprodIncl0 i y` is in `coprodPn n` when `y` is homogeneous of degree `n`. -/
theorem coprodIncl0_mem_coprodPn (i : I) (n : ℤ) (y : (f i).M) (hy : y ∈ (f i).grading n) :
    coprodIncl0 f i y ∈ coprodPn f n := by
  rw [mem_coprodPn]
  refine ⟨(Set.finite_singleton i).subset fun j hj ↦ ?_, fun j ↦ ?_⟩
  · by_contra h
    exact hj (coprodIncl0_apply_ne f i _ j h)
  · rcases eq_or_ne j i with hji | hji
    · subst hji; rw [coprodIncl0_apply_self]; exact hy
    · rw [coprodIncl0_apply_ne f i _ j hji]; exact Submodule.zero_mem _

/-- `coprodIncl0 i y` lands in `coprodSub`. -/
theorem coprodIncl0_mem (i : I) (y : (f i).M) :
    coprodIncl0 f i y ∈ (coprodSub f).restrictScalars R := by
  rw [coprodSub_restrict_eq]
  exact map_mem_of_decompose (f i).grading _ (coprodIncl0 f i).toAddMonoidHom
    (fun n z hz ↦ Submodule.mem_iSup_of_mem n (coprodIncl0_mem_coprodPn f i n z hz)) y

/-- The `i`-th coproduct injection `f i ⟶ coprodObj f`. -/
noncomputable def coprodι (i : I) : f i ⟶ coprodObj f where
  toFun := LinearMap.codRestrict ((coprodSub f).restrictScalars R) (coprodIncl0 f i)
    (fun y ↦ coprodIncl0_mem f i y)
  map_smul := by
    intro y a
    apply Subtype.ext
    funext j
    change coprodIncl0 f i (MulOpposite.op a • y) j = (MulOpposite.op a • coprodIncl0 f i y) j
    rcases eq_or_ne j i with hji | hji
    · subst hji
      rw [coprodIncl0_apply_self]
      change _ = MulOpposite.op a • (coprodIncl0 f j y j)
      rw [coprodIncl0_apply_self]
    · rw [coprodIncl0_apply_ne f i _ j hji]
      change (0 : (f j).M) = MulOpposite.op a • (coprodIncl0 f i y j)
      rw [coprodIncl0_apply_ne f i _ j hji, smul_zero]
  map_grading := by
    intro n y hy
    exact coprodIncl0_mem_coprodPn f i n y hy
  map_d := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    funext j
    change coprodIncl0 f i ((f i).d y) j = prodD0 f (coprodIncl0 f i y) j
    rw [prodD0_apply]
    rcases eq_or_ne j i with hji | hji
    · subst hji
      rw [coprodIncl0_apply_self, coprodIncl0_apply_self]
    · rw [coprodIncl0_apply_ne f i _ j hji, coprodIncl0_apply_ne f i _ j hji, map_zero]

variable {T : DifferentialGradedModule.{u, v, w} A} (g : ∀ i, f i ⟶ T)

/-- Underlying sum over a finset of the cocone components. -/
noncomputable def coprodGenSum (s : Finset I) (x : ∀ i, (f i).M) : T.M :=
  ∑ j ∈ s, (g j).toFun (x j)

/-- The sum is unchanged when enlarging the finset beyond the support of `x`. -/
theorem coprodGenSum_subset (x : ∀ i, (f i).M) (s t : Finset I)
    (hs : {i | x i ≠ 0} ⊆ ↑s) (hst : s ⊆ t) :
    coprodGenSum f g t x = coprodGenSum f g s x := by
  symm
  apply Finset.sum_subset hst
  intro i _ hi
  have : x i = 0 := by
    by_contra h
    exact hi (hs h)
  rw [this, map_zero]

/-- The descent map's underlying function: `x ↦ ∑ⱼ (g j) (x j)` over the (finite) support. -/
noncomputable def coprodDescent0 : ↥(coprodSub f) →ₗ[R] T.M where
  toFun x := coprodGenSum f g (coprodSub_finite f x x.2).toFinset (x : ∀ i, (f i).M)
  map_add' := by
    intro x y
    classical
    set sx := (coprodSub_finite f x x.2).toFinset
    set sy := (coprodSub_finite f y y.2).toFinset
    set sxy := (coprodSub_finite f (x + y) (x + y).2).toFinset
    have hx : coprodGenSum f g sx (x : ∀ i, (f i).M)
        = coprodGenSum f g (sx ∪ sy ∪ sxy) (x : ∀ i, (f i).M) := by
      apply (coprodGenSum_subset f g _ sx (sx ∪ sy ∪ sxy) _ _).symm
      · intro i hi
        simp only [sx, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]; exact hi
      · exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
    have hy : coprodGenSum f g sy (y : ∀ i, (f i).M)
        = coprodGenSum f g (sx ∪ sy ∪ sxy) (y : ∀ i, (f i).M) := by
      apply (coprodGenSum_subset f g _ sy (sx ∪ sy ∪ sxy) _ _).symm
      · intro i hi
        simp only [sy, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]; exact hi
      · exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
    have hxy : coprodGenSum f g sxy ((x + y : ↥(coprodSub f)) : ∀ i, (f i).M)
        = coprodGenSum f g (sx ∪ sy ∪ sxy) ((x + y : ↥(coprodSub f)) : ∀ i, (f i).M) := by
      apply (coprodGenSum_subset f g _ sxy (sx ∪ sy ∪ sxy) _ _).symm
      · intro i hi
        simp only [sxy, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]; exact hi
      · exact Finset.subset_union_right
    change coprodGenSum f g sxy ((x + y : ↥(coprodSub f)) : ∀ i, (f i).M) = _
    rw [hxy, hx, hy]
    simp only [coprodGenSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have : ((x + y : ↥(coprodSub f)) : ∀ i, (f i).M) j
        = (x : ∀ i, (f i).M) j + (y : ∀ i, (f i).M) j := rfl
    rw [this, map_add]
  map_smul' := by
    intro c x
    classical
    set sx := (coprodSub_finite f x x.2).toFinset
    set scx := (coprodSub_finite f (c • x) (c • x).2).toFinset
    have hx : coprodGenSum f g sx (x : ∀ i, (f i).M)
        = coprodGenSum f g (sx ∪ scx) (x : ∀ i, (f i).M) := by
      apply (coprodGenSum_subset f g _ sx (sx ∪ scx) _ _).symm
      · intro i hi
        simp only [sx, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]; exact hi
      · exact Finset.subset_union_left
    have hcx : coprodGenSum f g scx ((c • x : ↥(coprodSub f)) : ∀ i, (f i).M)
        = coprodGenSum f g (sx ∪ scx) ((c • x : ↥(coprodSub f)) : ∀ i, (f i).M) := by
      apply (coprodGenSum_subset f g _ scx (sx ∪ scx) _ _).symm
      · intro i hi
        simp only [scx, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]; exact hi
      · exact Finset.subset_union_right
    change coprodGenSum f g scx ((c • x : ↥(coprodSub f)) : ∀ i, (f i).M) = c • _
    rw [hcx, hx]
    simp only [coprodGenSum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have : ((c • x : ↥(coprodSub f)) : ∀ i, (f i).M) j
        = c • ((x : ∀ i, (f i).M) j) := rfl
    rw [this, map_smul]

/-- The descent map composed with the `i`-th injection is `g i`. -/
theorem coprodDescent0_incl (i : I) (y : (f i).M) :
    coprodDescent0 f g ((coprodι f i).toFun y) = (g i).toFun y := by
  classical
  let w : ↥(coprodSub f) := (coprodι f i).toFun y
  have hzval : (w : ∀ j, (f j).M) = coprodIncl0 f i y := rfl
  change coprodGenSum f g (coprodSub_finite f (w : ∀ j, (f j).M) w.2).toFinset
      (w : ∀ j, (f j).M) = (g i).toFun y
  have hsub : (coprodSub_finite f (w : ∀ j, (f j).M) w.2).toFinset ⊆ {i} := by
    intro j hj
    rw [Set.Finite.mem_toFinset] at hj
    simp only [Set.mem_ofPred_eq, hzval] at hj
    simp only [Finset.mem_singleton]
    by_contra h
    exact hj (coprodIncl0_apply_ne f i y j h)
  have hsupp : {k | (w : ∀ j, (f j).M) k ≠ 0}
      ⊆ ↑(coprodSub_finite f (w : ∀ j, (f j).M) w.2).toFinset := by
    rw [Set.Finite.coe_toFinset]
  rw [← coprodGenSum_subset f g (w : ∀ j, (f j).M) _ {i} hsupp hsub]
  simp only [coprodGenSum, Finset.sum_singleton]
  rw [hzval, coprodIncl0_apply_self]

/-- `coprodDescent0 x` computed over any finset containing the support of `x`. -/
theorem coprodDescent0_eq_genSum (x : ↥(coprodSub f)) (s : Finset I)
    (hs : {i | (x : ∀ j, (f j).M) i ≠ 0} ⊆ ↑s) :
    coprodDescent0 f g x = coprodGenSum f g s (x : ∀ j, (f j).M) := by
  classical
  change coprodGenSum f g (coprodSub_finite f (x : ∀ j, (f j).M) x.2).toFinset
      (x : ∀ j, (f j).M) = coprodGenSum f g s (x : ∀ j, (f j).M)
  have hsupp : {i | (x : ∀ j, (f j).M) i ≠ 0}
      ⊆ ↑(coprodSub_finite f (x : ∀ j, (f j).M) x.2).toFinset := by
    rw [Set.Finite.coe_toFinset]
  by_cases hle : (coprodSub_finite f (x : ∀ j, (f j).M) x.2).toFinset ⊆ s
  · exact (coprodGenSum_subset f g (x : ∀ j, (f j).M) _ s hsupp hle).symm
  · rw [← coprodGenSum_subset f g (x : ∀ j, (f j).M)
        (coprodSub_finite f (x : ∀ j, (f j).M) x.2).toFinset
        ((coprodSub_finite f (x : ∀ j, (f j).M) x.2).toFinset ∪ s) hsupp Finset.subset_union_left,
      ← coprodGenSum_subset f g (x : ∀ j, (f j).M) s
        ((coprodSub_finite f (x : ∀ j, (f j).M) x.2).toFinset ∪ s) hs Finset.subset_union_right]

/-- The descent homomorphism `coprodObj f ⟶ T` for a cocone `g`. -/
noncomputable def coprodDesc : coprodObj f ⟶ T where
  toFun := coprodDescent0 f g
  map_smul := by
    intro x a
    classical
    let w : ↥(coprodSub f) := x
    obtain ⟨s, hs⟩ := (coprodSub_finite f (w : ∀ j, (f j).M) w.2).exists_finset_coe
    have hsx : {i | (w : ∀ j, (f j).M) i ≠ 0} ⊆ (↑s : Set I) := hs.ge
    have hsax := support_subset_of_forall f (z := ((MulOpposite.op a • w : ↥(coprodSub f)) :
      ∀ j, (f j).M)) hsx fun j h ↦ by
        change MulOpposite.op a • (w : ∀ j, (f j).M) j = 0
        rw [h, smul_zero]
    change coprodDescent0 f g (MulOpposite.op a • w) = MulOpposite.op a • coprodDescent0 f g w
    rw [coprodDescent0_eq_genSum f g (MulOpposite.op a • w) s hsax,
      coprodDescent0_eq_genSum f g w s hsx]
    simp only [coprodGenSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact (g j).map_smul ((w : ∀ k, (f k).M) j) a
  map_grading := by
    intro n x hx
    classical
    let w : ↥(coprodSub f) := x
    have hxn : (w : ∀ j, (f j).M) ∈ coprodPn f n := hx
    obtain ⟨s, hs⟩ := (coprodSub_finite f (w : ∀ j, (f j).M) w.2).exists_finset_coe
    change coprodDescent0 f g w ∈ T.grading n
    rw [coprodDescent0_eq_genSum f g w s hs.ge]
    exact Submodule.sum_mem _ fun j _ ↦ (g j).map_grading n _ (((mem_coprodPn f _).1 hxn).2 j)
  map_d := by
    ext x
    classical
    let w : ↥(coprodSub f) := x
    obtain ⟨s, hs⟩ := (coprodSub_finite f (w : ∀ j, (f j).M) w.2).exists_finset_coe
    have hsx : {i | (w : ∀ j, (f j).M) i ≠ 0} ⊆ (↑s : Set I) := hs.ge
    have hsdx := support_subset_of_forall f (z := ((coprodD f w : ↥(coprodSub f)) :
      ∀ j, (f j).M)) hsx fun j h ↦ by
        change (prodD0 f (w : ∀ j, (f j).M)) j = 0
        rw [prodD0_apply, h, map_zero]
    change coprodDescent0 f g (coprodD f w) = T.d (coprodDescent0 f g w)
    rw [coprodDescent0_eq_genSum f g (coprodD f w) s hsdx,
      coprodDescent0_eq_genSum f g w s hsx]
    simp only [coprodGenSum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    change (g j).toFun (prodD0 f (w : ∀ k, (f k).M) j) = _
    rw [prodD0_apply]
    simpa using LinearMap.congr_fun (g j).map_d ((w : ∀ k, (f k).M) j)

@[simp] theorem coprodDesc_toFun_apply (x : ↥(coprodSub f)) :
    (coprodDesc f g).toFun x = coprodDescent0 f g x := rfl

/-- Every element of the coproduct is the (finite) sum of its single-coordinate parts. -/
theorem coprodSub_repr (x : ↥(coprodSub f)) (s : Finset I)
    (hs : {i | (x : ∀ j, (f j).M) i ≠ 0} ⊆ (↑s : Set I)) :
    x = ∑ i ∈ s, (coprodι f i).toFun ((x : ∀ j, (f j).M) i) := by
  classical
  apply Subtype.ext
  funext k
  change (x : ∀ j, (f j).M) k = ((∑ i ∈ s, (coprodι f i).toFun ((x : ∀ j, (f j).M) i)
      : ↥(coprodSub f)) : ∀ j, (f j).M) k
  rw [AddSubmonoid.coe_finsetSum]
  rw [Finset.sum_apply]
  by_cases hk : k ∈ s
  · rw [Finset.sum_eq_single k]
    · change (x : ∀ j, (f j).M) k = coprodIncl0 f k ((x : ∀ j, (f j).M) k) k
      rw [coprodIncl0_apply_self]
    · intro b _ hbk
      change coprodIncl0 f b ((x : ∀ j, (f j).M) b) k = 0
      rw [coprodIncl0_apply_ne f b _ k (fun h ↦ hbk h.symm)]
    · intro h; exact absurd hk h
  · have hxk : (x : ∀ j, (f j).M) k = 0 := by
      by_contra h
      exact hk (hs h)
    rw [hxk]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    rcases eq_or_ne k b with hkb | hkb
    · subst hkb; exact absurd hb hk
    · change coprodIncl0 f b ((x : ∀ j, (f j).M) b) k = 0
      rw [coprodIncl0_apply_ne f b _ k hkb]

end Coproduct

end DifferentialGradedModule
