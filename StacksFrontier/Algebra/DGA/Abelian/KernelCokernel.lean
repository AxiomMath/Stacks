module

public import StacksFrontier.Algebra.DGA.Abelian.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Kernels and cokernels of differential graded modules

The category `Mod_(A, d)` of right differential graded modules over a differential graded algebra
`(A, d)` has kernels and cokernels, computed on the underlying modules: the kernel of `f : M ⟶ N`
is the kernel of the underlying `R`-linear map with the induced grading and differential, and the
cokernel is the quotient by its image. Every monomorphism is the kernel of its cokernel and every
epimorphism is the cokernel of its kernel.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w w' w'' t

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, v} R}

namespace DifferentialGradedModule

/-- A graded `R`-linear map sends the degree-`i` component of `x` to the degree-`i`
component of `f x`. -/
private theorem comp_of_graded {ι : Type t} [DecidableEq ι]
    {M₀ : Type w} {N₀ : Type w'} [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₀] [Module R N₀]
    (gM : ι → Submodule R M₀) (gN : ι → Submodule R N₀)
    [DirectSum.Decomposition gM] [DirectSum.Decomposition gN]
    (f : M₀ →ₗ[R] N₀)
    (hf : ∀ (i : ι) (x : M₀), x ∈ gM i → f x ∈ gN i) (x : M₀) (i : ι) :
    (DirectSum.decompose gN (f x) i : N₀) = f ((DirectSum.decompose gM x i : M₀)) := by
  have key : ∀ (z : DirectSum ι (fun j ↦ gM j)),
      (DirectSum.decompose gN (f ((DirectSum.decompose gM).symm z)) i : N₀)
        = f ((z i : M₀)) := by
    intro z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of j y =>
        rw [DirectSum.decompose_symm_of,
          show f (y : M₀) = ((⟨f y, hf j y y.2⟩ : gN j) : N₀) from rfl, DirectSum.decompose_coe,
          DirectSum.of_apply, DirectSum.of_apply]
        by_cases h : j = i
        · subst h; simp
        · rw [dite_eq_right h, dite_eq_right h]; simp
    | add a b ha hb =>
        have e1 : (DirectSum.decompose gM).symm (a + b)
            = (DirectSum.decompose gM).symm a + (DirectSum.decompose gM).symm b := by simp
        rw [e1, map_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
          DirectSum.add_apply, Submodule.coe_add, map_add, ha, hb]
  simpa using key (DirectSum.decompose gM x)

/-- A morphism of differential graded modules commutes with the differentials. -/
private theorem toFun_d_apply {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    (x : M.M) : f.toFun (M.d x) = N.d (f.toFun x) :=
  LinearMap.congr_fun f.map_d x

/-- If `g ≫ f = 0`, then `f` kills the image of `g` on underlying elements. -/
private theorem toFun_apply_eq_zero_of_comp_eq_zero
    {M N P : DifferentialGradedModule.{u, v, w} A} {g : M ⟶ N} {f : N ⟶ P} (h : g ≫ f = 0)
    (x : M.M) : f.toFun (g.toFun x) = 0 := by
  simpa using LinearMap.congr_fun (congrArg Hom.toFun h) x

/-- The kernel submodule of a morphism `f`, as a right-`A`-submodule of `M.M`. -/
private def kerSub {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    Submodule (MulOpposite A.A) M.M where
  carrier := {x | f.toFun x = 0}
  add_mem' := by intro a b ha hb; simp only [Set.mem_ofPred_eq] at *; simp [ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [show c • x = (MulOpposite.op c.unop) • x from rfl, f.map_smul, hx, smul_zero]

private theorem mem_kerSub {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) (x : M.M) :
    x ∈ kerSub f ↔ f.toFun x = 0 := Iff.rfl

/-- The grading on the kernel object. -/
private noncomputable def kernelGrading {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    (n : ℤ) : Submodule R ↥(kerSub f) :=
  Submodule.inducedGrading M.grading ((kerSub f).restrictScalars R) n

/-- `M.d` maps the kernel submodule into itself. -/
private theorem kerSub_d_mem {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    (x : M.M) (hx : x ∈ (kerSub f).restrictScalars R) : M.d x ∈ (kerSub f).restrictScalars R := by
  rw [Submodule.restrictScalars_mem, mem_kerSub] at hx ⊢
  rw [toFun_d_apply, hx, map_zero]

/-- The differential on the kernel object. -/
private def kernelD {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    ↥(kerSub f) →ₗ[R] ↥(kerSub f) :=
  LinearMap.restrict M.d (p := (kerSub f).restrictScalars R) (q := (kerSub f).restrictScalars R)
    (kerSub_d_mem f)

/-- The kernel object of a morphism `f`. -/
private noncomputable def kernelObj {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    DifferentialGradedModule.{u, v, w} A where
  M := ↥(kerSub f)
  grading := kernelGrading f
  decomposition := by
    change DirectSum.Decomposition (kernelGrading f)
    unfold kernelGrading
    apply Submodule.inducedGrading.decomposition
    intro n m hm
    rw [Submodule.restrictScalars_mem, mem_kerSub] at hm ⊢
    have := comp_of_graded (R := R) M.grading N.grading f.toFun
      f.map_grading m n
    rw [hm, DirectSum.decompose_zero] at this
    simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero] at this
    exact this.symm
  smul_mem := by
    intro n mdeg x a hx ha
    rw [kernelGrading, Submodule.inducedGrading, Submodule.mem_comap] at hx
    have hxv : (x : M.M) ∈ M.grading n := hx
    rw [kernelGrading, Submodule.inducedGrading, Submodule.mem_comap]
    change (MulOpposite.op a • x : M.M) ∈ M.grading (n + mdeg)
    exact M.smul_mem n mdeg x.val a hxv ha
  d := kernelD f
  d_comp_d := by
    ext x
    have hdd := LinearMap.congr_fun M.d_comp_d (x : M.M)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
    simp only [kernelD, LinearMap.comp_apply, LinearMap.zero_apply,
      ZeroMemClass.coe_zero]
    exact hdd
  d_mem := by
    intro n x hx
    rw [kernelGrading, Submodule.inducedGrading, Submodule.mem_comap] at hx
    have hxv : (x : M.M) ∈ M.grading n := hx
    rw [kernelGrading, Submodule.inducedGrading, Submodule.mem_comap]
    change (M.d (x : M.M)) ∈ M.grading (n + 1)
    exact M.d_mem n x.val hxv
  leibniz := by
    intro n m x a hx ha
    rw [kernelGrading, Submodule.inducedGrading, Submodule.mem_comap] at hx
    have hxv : (x : M.M) ∈ M.grading n := hx
    exact Subtype.ext (M.leibniz n m x.val a hxv ha)

@[simp] private theorem kernelObj_M {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    (kernelObj f).M = ↥(kerSub f) := rfl

@[simp] private theorem kernelObj_grading {M N : DifferentialGradedModule.{u, v, w} A}
    (f : Hom M N) :
    (kernelObj f).grading = kernelGrading f := rfl

@[simp] private theorem kernelObj_d {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    (kernelObj f).d = kernelD f := rfl

/-- The kernel inclusion `kernelObj f ⟶ M`. -/
private def kernelι {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    kernelObj f ⟶ M where
  toFun := ((kerSub f).restrictScalars R).subtype
  map_smul := by intro x a; rfl
  map_grading := by
    intro n x hx
    change ((kerSub f).restrictScalars R).subtype x ∈ M.grading n
    rw [kernelObj_grading, kernelGrading, Submodule.inducedGrading, Submodule.mem_comap] at hx
    exact hx
  map_d := by
    ext x
    rfl

@[simp] private theorem kernelι_toFun_apply {M N : DifferentialGradedModule.{u, v, w} A}
    (f : Hom M N)
    (x : ↥(kerSub f)) : (kernelι f).toFun x = (x : M.M) := rfl

/-- `kernelι f ≫ f = 0`. -/
private theorem kernelι_comp {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    kernelι f ≫ f = 0 := by
  apply Hom.ext
  ext x
  show f.toFun ((kernelι f).toFun x) = (0 : kernelObj f ⟶ N).toFun x
  rw [kernelι_toFun_apply, Hom.hom_zero_toFun]
  exact x.2

/-- The factorization of a morphism `g` with `g ≫ f = 0` through the kernel. -/
private def kernelLift {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    {T : DifferentialGradedModule.{u, v, w} A} (g : T ⟶ M) (hg : g ≫ f = 0) : T ⟶ kernelObj f where
  toFun := LinearMap.codRestrict ((kerSub f).restrictScalars R) g.toFun (by
    intro t
    rw [Submodule.restrictScalars_mem, mem_kerSub]
    exact toFun_apply_eq_zero_of_comp_eq_zero hg t)
  map_smul := by
    intro x a
    apply Subtype.ext
    change g.toFun ((MulOpposite.op a) • x) = (MulOpposite.op a) • g.toFun x
    exact g.map_smul x a
  map_grading := by
    intro n x hx
    rw [kernelObj_grading, kernelGrading, Submodule.inducedGrading, Submodule.mem_comap]
    change g.toFun x ∈ M.grading n
    exact g.map_grading n x hx
  map_d := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact toFun_d_apply g x

/-- The category `Mod_(A, d)` has kernels. -/
instance instHasKernels : HasKernels (DifferentialGradedModule.{u, v, w} A) := by
  constructor
  intro M N f
  apply HasLimit.mk
  refine ⟨KernelFork.ofι (kernelι f) (kernelι_comp f), ?_⟩
  refine KernelFork.IsLimit.ofι _ _
    (fun {T} g hg ↦ kernelLift f g hg) ?_ ?_
  · intro T g hg
    apply Hom.ext
    ext t
    rfl
  · intro T g hg m hm
    apply Hom.ext
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    have hmt := LinearMap.congr_fun (congrArg Hom.toFun hm) t
    change (m.toFun t : ↥(kerSub f)).val = ((kernelLift f g hg).toFun t).val
    have hr : ((kernelLift f g hg).toFun t).val = g.toFun t := rfl
    have hl : ((m ≫ kernelι f).toFun t) = (m.toFun t : ↥(kerSub f)).val := rfl
    rw [hr, ← hl]
    exact hmt

/-- The degree-`i` component of an element of `⨆_{j≠i} gM j` is zero. -/
private theorem decompose_eq_zero_of_mem_iSup_ne {ι : Type t} [DecidableEq ι]
    {M₀ : Type w} [AddCommGroup M₀] [Module R M₀]
    (gM : ι → Submodule R M₀) [DirectSum.Decomposition gM] (i : ι)
    (z : M₀) (hz : z ∈ ⨆ (j : ι) (_ : j ≠ i), gM j) :
    (DirectSum.decompose gM z i : M₀) = 0 := by
  induction hz using Submodule.iSup_induction' with
  | mem j z hzj =>
      by_cases hj : j = i
      · subst hj
        rw [iSup_neg (fun h ↦ h rfl)] at hzj
        rw [Submodule.mem_bot] at hzj
        simp [hzj]
      · rw [iSup_pos hj] at hzj
        rw [DirectSum.decompose_of_mem gM hzj, DirectSum.of_apply]
        rw [dite_eq_right hj]
        rfl
  | zero => simp
  | add a b ha hb iha ihb =>
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, iha, ihb, add_zero]

/-- The grading induced on a quotient `M₀ ⧸ s` by a graded family `gM`: the pushforward
`(gM i).map (mkQ s)`. -/
private def quotGrading {ι : Type t} {M₀ : Type w} [AddCommGroup M₀] [Module R M₀]
    (gM : ι → Submodule R M₀) (s : Submodule R M₀) (i : ι) : Submodule R (M₀ ⧸ s) :=
  (gM i).map s.mkQ

private theorem quotGrading_iSupIndep {ι : Type t} [DecidableEq ι]
    {M₀ : Type w} [AddCommGroup M₀] [Module R M₀]
    (gM : ι → Submodule R M₀) [DirectSum.Decomposition gM] (s : Submodule R M₀)
    (hs : ∀ (i : ι) (m : M₀), m ∈ s → (DirectSum.decompose gM m i : M₀) ∈ s) :
    iSupIndep (quotGrading gM s) := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  rintro ybar hyi hysup
  obtain ⟨y, hy, rfl⟩ := hyi
  have hmapsup : (⨆ (j : ι) (_ : j ≠ i), quotGrading gM s j)
      = Submodule.map s.mkQ (⨆ (j : ι) (_ : j ≠ i), gM j) := by
    simp only [quotGrading, Submodule.map_iSup]
  rw [hmapsup] at hysup
  obtain ⟨z, hz, hzeq⟩ := hysup
  have hdiff : y - z ∈ s := by
    rw [← Submodule.Quotient.eq]
    exact hzeq.symm
  have hcomp := hs i (y - z) hdiff
  have hyc : (DirectSum.decompose gM y i : M₀) = y := by
    rw [DirectSum.decompose_of_mem_same gM hy]
  have hzc : (DirectSum.decompose gM z i : M₀) = 0 :=
    decompose_eq_zero_of_mem_iSup_ne gM i z hz
  rw [DirectSum.decompose_sub, DirectSum.sub_apply, Submodule.coe_sub, hyc, hzc, sub_zero] at hcomp
  show s.mkQ y = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hcomp

private theorem quotGrading_iSup_top {ι : Type t} [DecidableEq ι]
    {M₀ : Type w} [AddCommGroup M₀] [Module R M₀]
    (gM : ι → Submodule R M₀) [DirectSum.Decomposition gM] (s : Submodule R M₀) :
    iSup (quotGrading gM s) = ⊤ := by
  have htop : iSup gM = ⊤ := (DirectSum.Decomposition.isInternal gM).submodule_iSup_eq_top
  rw [eq_top_iff]
  rintro ybar -
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective s ybar
  have hy : y ∈ iSup gM := by rw [htop]; trivial
  induction hy using Submodule.iSup_induction' with
  | mem j z hz =>
      apply Submodule.mem_iSup_of_mem j
      exact ⟨z, hz, rfl⟩
  | zero => simp
  | add a b ha hb iha ihb =>
      rw [map_add]
      exact Submodule.add_mem _ iha ihb

@[instance_reducible]
private noncomputable def quotGrading_decomposition {ι : Type t} [DecidableEq ι]
    {M₀ : Type w} [AddCommGroup M₀] [Module R M₀]
    (gM : ι → Submodule R M₀) [DirectSum.Decomposition gM] (s : Submodule R M₀)
    (hs : ∀ (i : ι) (m : M₀), m ∈ s → (DirectSum.decompose gM m i : M₀) ∈ s) :
    DirectSum.Decomposition (quotGrading gM s) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (quotGrading_iSupIndep gM s hs) (quotGrading_iSup_top gM s)).chooseDecomposition _

/-- The range of `f.toFun`, as a right-`A`-submodule of `N.M`. -/
private def rangeSub {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    Submodule (MulOpposite A.A) N.M where
  carrier := {y | ∃ x, f.toFun x = y}
  add_mem' := by
    rintro a b ⟨x, rfl⟩ ⟨z, rfl⟩
    exact ⟨x + z, by simp⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c y ⟨x, rfl⟩
    refine ⟨(MulOpposite.op c.unop) • x, ?_⟩
    rw [f.map_smul]
    rfl

private theorem mem_rangeSub {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) (y : N.M) :
    y ∈ rangeSub f ↔ ∃ x, f.toFun x = y := Iff.rfl

/-- `rangeSub f` (restricted to `R`) equals `LinearMap.range f.toFun`. -/
private theorem rangeSub_restrictScalars {M N : DifferentialGradedModule.{u, v, w} A}
    (f : Hom M N) :
    (rangeSub f).restrictScalars R = LinearMap.range f.toFun := by
  ext y
  rw [Submodule.restrictScalars_mem, mem_rangeSub, LinearMap.mem_range]

/-- The range submodule is stable under taking graded components: if `y ∈ range f`,
each degree-`i` component of `y` is again in `range f`. -/
private theorem rangeSub_decompose_mem {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    (i : ℤ) (y : N.M) (hy : y ∈ (rangeSub f).restrictScalars R) :
    (DirectSum.decompose N.grading y i : N.M) ∈ (rangeSub f).restrictScalars R := by
  rw [rangeSub_restrictScalars, LinearMap.mem_range] at hy ⊢
  obtain ⟨x, rfl⟩ := hy
  refine ⟨(DirectSum.decompose M.grading x i : M.M), ?_⟩
  exact (comp_of_graded M.grading N.grading f.toFun f.map_grading x i).symm

/-- The grading on the cokernel object: the pushforward of `N.grading`. -/
private def cokernelGrading {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    (n : ℤ) : Submodule R (N.M ⧸ (rangeSub f).restrictScalars R) :=
  quotGrading N.grading ((rangeSub f).restrictScalars R) n

/-- `N.d` maps `range f` into itself, so it descends to the quotient. -/
private theorem rangeSub_d_mem {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    (y : N.M) (hy : y ∈ (rangeSub f).restrictScalars R) :
    N.d y ∈ (rangeSub f).restrictScalars R := by
  rw [rangeSub_restrictScalars, LinearMap.mem_range] at hy ⊢
  obtain ⟨x, rfl⟩ := hy
  exact ⟨M.d x, toFun_d_apply f x⟩

/-- The differential on the cokernel object, induced from `N.d` via `liftQ`. -/
private def cokernelD {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    (N.M ⧸ rangeSub f) →ₗ[R] (N.M ⧸ rangeSub f) :=
  Submodule.mapQ ((rangeSub f).restrictScalars R) ((rangeSub f).restrictScalars R) N.d
    (rangeSub_d_mem f)

@[simp] private theorem cokernelD_mk {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    (y : N.M) :
    cokernelD f (Submodule.Quotient.mk (p := rangeSub f) y)
      = Submodule.Quotient.mk (p := rangeSub f) (N.d y) := rfl

/-- The cokernel object of a morphism `f`: the quotient of `N` by the range of `f`. -/
private noncomputable def cokernelObj {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    DifferentialGradedModule.{u, v, w} A where
  M := N.M ⧸ rangeSub f
  decomposition := by
    change DirectSum.Decomposition (cokernelGrading f)
    unfold cokernelGrading
    apply quotGrading_decomposition
    intro i m hm
    exact rangeSub_decompose_mem f i m hm
  grading := cokernelGrading f
  smul_mem := by
    intro n m ybar a hy ha
    rw [cokernelGrading, quotGrading] at hy ⊢
    obtain ⟨y, hyN, rfl⟩ := hy
    refine ⟨(MulOpposite.op a) • y, N.smul_mem n m y a hyN ha, ?_⟩
    rfl
  d := cokernelD f
  d_comp_d := by
    apply LinearMap.ext
    intro ybar
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (rangeSub f) ybar
    change cokernelD f (cokernelD f (Submodule.Quotient.mk (p := rangeSub f) y)) = 0
    rw [cokernelD_mk, cokernelD_mk]
    have hdd := LinearMap.congr_fun N.d_comp_d y
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdd
    rw [hdd]
    simp
  d_mem := by
    intro n ybar hy
    rw [cokernelGrading, quotGrading] at hy ⊢
    obtain ⟨y, hyN, rfl⟩ := hy
    refine ⟨N.d y, N.d_mem n y hyN, ?_⟩
    rfl
  leibniz := by
    intro n m ybar a hy ha
    rw [cokernelGrading, quotGrading] at hy
    obtain ⟨y, hyN, rfl⟩ := hy
    have hlib := N.leibniz n m y a hyN ha
    change cokernelD f ((MulOpposite.op a) • (Submodule.Quotient.mk (p := rangeSub f) y))
        = (MulOpposite.op a) • cokernelD f (Submodule.Quotient.mk (p := rangeSub f) y)
          + (n.negOnePow : ℤ) • ((MulOpposite.op (A.d a)) •
              (Submodule.Quotient.mk (p := rangeSub f) y))
    rw [← Submodule.Quotient.mk_smul, cokernelD_mk, cokernelD_mk,
        ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
        ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, hlib]

@[simp] private theorem cokernelObj_M {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    (cokernelObj f).M = (N.M ⧸ rangeSub f) := rfl

/-- The cokernel projection `N ⟶ cokernelObj f`. -/
private def cokernelπ {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    N ⟶ cokernelObj f where
  toFun := ((rangeSub f).restrictScalars R).mkQ
  map_smul := by
    intro x a
    change Submodule.Quotient.mk (p := rangeSub f) ((MulOpposite.op a) • x)
        = (MulOpposite.op a) • Submodule.Quotient.mk (p := rangeSub f) x
    rw [Submodule.Quotient.mk_smul]
  map_grading := by
    intro n x hx
    change ((rangeSub f).restrictScalars R).mkQ x ∈ (cokernelObj f).grading n
    change Submodule.Quotient.mk x ∈ cokernelGrading f n
    rw [cokernelGrading, quotGrading]
    exact ⟨x, hx, rfl⟩
  map_d := by
    ext x
    rfl

@[simp] private theorem cokernelπ_toFun_apply {M N : DifferentialGradedModule.{u, v, w} A}
    (f : Hom M N)
    (y : N.M) : (cokernelπ f).toFun y = Submodule.Quotient.mk (p := rangeSub f) y := rfl

/-- `f ≫ cokernelπ f = 0`. -/
private theorem comp_cokernelπ {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N) :
    f ≫ cokernelπ f = 0 := by
  apply Hom.ext
  ext x
  show (cokernelπ f).toFun (f.toFun x) = (0 : M ⟶ cokernelObj f).toFun x
  rw [cokernelπ_toFun_apply]
  show Submodule.Quotient.mk (p := rangeSub f) (f.toFun x) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

/-- The underlying `R`-linear map of the cokernel factorization. -/
private def cokernelDescFun {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    {T : DifferentialGradedModule.{u, v, w} A} (g : N ⟶ T) (hg : f ≫ g = 0) :
    (N.M ⧸ rangeSub f) →ₗ[R] T.M :=
  Submodule.liftQ ((rangeSub f).restrictScalars R) g.toFun (by
    intro y hy
    rw [Submodule.restrictScalars_mem, mem_rangeSub] at hy
    obtain ⟨x, rfl⟩ := hy
    exact toFun_apply_eq_zero_of_comp_eq_zero hg x)

@[simp] private theorem cokernelDescFun_mk {M N : DifferentialGradedModule.{u, v, w} A}
    (f : Hom M N)
    {T : DifferentialGradedModule.{u, v, w} A} (g : N ⟶ T) (hg : f ≫ g = 0) (y : N.M) :
    cokernelDescFun f g hg (Submodule.Quotient.mk (p := rangeSub f) y) = g.toFun y := rfl

/-- The factorization of a morphism `g` with `f ≫ g = 0` through the cokernel. -/
private def cokernelDesc {M N : DifferentialGradedModule.{u, v, w} A} (f : Hom M N)
    {T : DifferentialGradedModule.{u, v, w} A} (g : N ⟶ T) (hg : f ≫ g = 0) :
    cokernelObj f ⟶ T where
  toFun := cokernelDescFun f g hg
  map_smul := by
    intro xbar a
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (rangeSub f) xbar
    rw [← Submodule.Quotient.mk_smul]
    change g.toFun ((MulOpposite.op a) • x) = (MulOpposite.op a) • g.toFun x
    exact g.map_smul x a
  map_grading := by
    intro n xbar hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (rangeSub f) xbar
    have hx' : Submodule.Quotient.mk (p := rangeSub f) x ∈ cokernelGrading f n := hx
    rw [cokernelGrading, quotGrading] at hx'
    obtain ⟨z, hzN, hzeq⟩ := hx'
    change g.toFun x ∈ T.grading n
    have hdiff : x - z ∈ rangeSub f := by
      rw [← Submodule.Quotient.eq]; exact hzeq.symm
    rw [mem_rangeSub] at hdiff
    obtain ⟨w, hw⟩ := hdiff
    have hgw : g.toFun (x - z) = 0 := by
      rw [← hw]
      exact toFun_apply_eq_zero_of_comp_eq_zero hg w
    have hgxz : g.toFun x = g.toFun z := by
      have h0 : g.toFun x - g.toFun z = 0 := by rw [← map_sub]; exact hgw
      exact sub_eq_zero.mp h0
    rw [hgxz]
    exact g.map_grading n z hzN
  map_d := by
    apply LinearMap.ext
    intro xbar
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (rangeSub f) xbar
    change cokernelDescFun f g hg (cokernelD f (Submodule.Quotient.mk (p := rangeSub f) x))
        = T.d (cokernelDescFun f g hg (Submodule.Quotient.mk (p := rangeSub f) x))
    rw [cokernelD_mk]
    exact toFun_d_apply g x

@[simp] private theorem cokernelDesc_toFun_mk {M N : DifferentialGradedModule.{u, v, w} A}
    (f : Hom M N)
    {T : DifferentialGradedModule.{u, v, w} A} (g : N ⟶ T) (hg : f ≫ g = 0) (y : N.M) :
    (cokernelDesc f g hg).toFun (Submodule.Quotient.mk (p := rangeSub f) y) = g.toFun y := rfl

/-- The category `Mod_(A, d)` has cokernels. -/
instance instHasCokernels : HasCokernels (DifferentialGradedModule.{u, v, w} A) := by
  constructor
  intro M N f
  apply HasColimit.mk
  refine ⟨CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f), ?_⟩
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {T} g hg ↦ cokernelDesc f g hg) ?_ ?_
  · intro T g hg
    apply Hom.ext
    ext y
    rfl
  · intro T g hg m hm
    apply Hom.ext
    apply LinearMap.ext
    intro ybar
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (rangeSub f) ybar
    have hmt := LinearMap.congr_fun (congrArg Hom.toFun hm) y
    change m.toFun (Submodule.Quotient.mk (p := rangeSub f) y)
        = (cokernelDesc f g hg).toFun (Submodule.Quotient.mk (p := rangeSub f) y)
    have hr : (cokernelDesc f g hg).toFun (Submodule.Quotient.mk (p := rangeSub f) y) = g.toFun y :=
      rfl
    have hl : (cokernelπ f ≫ m).toFun y = m.toFun (Submodule.Quotient.mk (p := rangeSub f) y) := rfl
    rw [hr, ← hl]
    exact hmt

/-- If every graded component of `y` other than the `n`-th vanishes, then `y` lies in `g n`. -/
private theorem mem_grading_of_decompose_eq_zero {M₀ : Type w} [AddCommGroup M₀] [Module R M₀]
    (g : ℤ → Submodule R M₀) [DirectSum.Decomposition g] (y : M₀) (n : ℤ)
    (h : ∀ i, i ≠ n → (DirectSum.decompose g y i : M₀) = 0) : y ∈ g n := by
  have hdec : (DirectSum.decompose g y)
      = DirectSum.of (fun i ↦ ↥(g i)) n (DirectSum.decompose g y n) := by
    apply DFinsupp.ext
    intro i
    by_cases hi : i = n
    · subst hi; rw [DirectSum.of_apply]; simp
    · rw [DirectSum.of_apply, dite_eq_right (fun hh ↦ hi hh.symm)]
      apply Subtype.ext
      exact h i hi
  have hmem : ((DirectSum.decompose g y n : ↥(g n)) : M₀) ∈ g n := (DirectSum.decompose g y n).2
  have hy : y = ((DirectSum.decompose g y n : ↥(g n)) : M₀) := by
    have h2 := DirectSum.decompose_of_mem g hmem
    have hinj : Function.Injective (DirectSum.decompose g) := (DirectSum.decompose g).injective
    apply hinj
    conv_lhs => rw [hdec]
    rw [h2]
  rw [hy]; exact hmem

/-- A monomorphism of differential graded modules has injective underlying `R`-linear map. -/
private theorem mono_toFun_injective {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N)
    [Mono f] : Function.Injective f.toFun := by
  have hker : kernelι f = 0 := by
    have h0 : (kernelι f) ≫ f = (0 : kernelObj f ⟶ M) ≫ f := by
      rw [kernelι_comp f, zero_comp]
    exact (cancel_mono f).1 h0
  intro a b hab
  rw [← sub_eq_zero]
  have hmem : (a - b) ∈ kerSub f := by
    rw [mem_kerSub, map_sub, hab, sub_self]
  have hz : ((kernelι f).toFun ⟨a - b, hmem⟩) = ((0 : kernelObj f ⟶ M).toFun ⟨a - b, hmem⟩) := by
    rw [hker]
  rw [kernelι_toFun_apply, Hom.hom_zero_toFun] at hz
  simpa using hz

/-- Every monomorphism of differential graded modules is normal. -/
instance instIsNormalMonoCategory :
    IsNormalMonoCategory (DifferentialGradedModule.{u, v, w} A) := by
  refine ⟨fun {M N} f _ ↦ ?_⟩
  have hinj : Function.Injective f.toFun := mono_toFun_injective f
  set eqv : M.M ≃ₗ[R] ↥(LinearMap.range f.toFun) := LinearEquiv.ofInjective f.toFun hinj with heqv
  have hrange : ∀ {T : DifferentialGradedModule.{u, v, w} A} (e : T ⟶ N), e ≫ cokernelπ f = 0 →
      ∀ t, e.toFun t ∈ LinearMap.range f.toFun := by
    intro T e he t
    have h0 : (cokernelπ f).toFun (e.toFun t) = 0 := by
      rw [← Hom.comp_toFun_apply, he]
      rfl
    rw [cokernelπ_toFun_apply, Submodule.Quotient.mk_eq_zero] at h0
    rw [← rangeSub_restrictScalars f]
    exact h0
  let liftFun : ∀ {T : DifferentialGradedModule.{u, v, w} A} (e : T ⟶ N), e ≫ cokernelπ f = 0 →
      T.M →ₗ[R] M.M := fun {T} e he ↦
    eqv.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range f.toFun) e.toFun (hrange e he)
  have hkey : ∀ {T : DifferentialGradedModule.{u, v, w} A}
      (e : T ⟶ N) (he : e ≫ cokernelπ f = 0) (t : T.M),
      f.toFun (liftFun e he t) = e.toFun t := by
    intro T e he t
    change f.toFun (eqv.symm ⟨e.toFun t, hrange e he t⟩) = e.toFun t
    have := LinearEquiv.ofInjective_apply f.toFun (h := hinj) (eqv.symm ⟨e.toFun t, hrange e he t⟩)
    rw [heqv] at this ⊢
    rw [← this, LinearEquiv.apply_symm_apply]
  let lift : ∀ {T : DifferentialGradedModule.{u, v, w} A} (e : T ⟶ N), e ≫ cokernelπ f = 0 →
      (T ⟶ M) := fun {T} e he ↦
    { toFun := liftFun e he
      map_smul := by
        intro x a
        apply hinj
        rw [hkey e he, f.map_smul, hkey e he, e.map_smul]
      map_grading := by
        intro n x hx
        apply mem_grading_of_decompose_eq_zero M.grading _ n
        intro i hi
        apply hinj
        rw [map_zero]
        have hcg := comp_of_graded M.grading N.grading f.toFun
          f.map_grading (liftFun e he x) i
        rw [hkey e he] at hcg
        rw [← hcg]
        have hex : e.toFun x ∈ N.grading n := e.map_grading n x hx
        exact DirectSum.decompose_of_mem_ne N.grading hex (Ne.symm hi)
      map_d := by
        ext x
        apply hinj
        change f.toFun (liftFun e he (T.d x)) = f.toFun (M.d (liftFun e he x))
        rw [hkey e he]
        have hfd := LinearMap.congr_fun f.map_d (liftFun e he x)
        simp only [LinearMap.comp_apply] at hfd
        rw [hfd, hkey e he]
        have hed := LinearMap.congr_fun e.map_d x
        simpa using hed }
  refine ⟨NormalMono.mk (cokernelObj f) (cokernelπ f) (comp_cokernelπ f) ?_⟩
  refine KernelFork.IsLimit.ofι _ _ (fun {T} e he ↦ lift e he) ?_ ?_
  · intro T e he
    apply Hom.ext
    ext t
    change f.toFun (liftFun e he t) = e.toFun t
    exact hkey e he t
  · intro T e he m hm
    apply Hom.ext
    ext t
    apply hinj
    rw [hkey e he]
    simpa using LinearMap.congr_fun (congrArg Hom.toFun hm) t

/-- An epimorphism of differential graded modules has surjective underlying `R`-linear map. -/
private theorem epi_toFun_surjective {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N)
    [Epi f] : Function.Surjective f.toFun := by
  have hcok : cokernelπ f = 0 := by
    have h0 : f ≫ (cokernelπ f) = f ≫ (0 : N ⟶ cokernelObj f) := by
      rw [comp_cokernelπ f, comp_zero]
    exact (cancel_epi f).1 h0
  intro y
  have hz : ((cokernelπ f).toFun y) = ((0 : N ⟶ cokernelObj f).toFun y) := by
    rw [hcok]
  rw [cokernelπ_toFun_apply, Hom.hom_zero_toFun] at hz
  have h0 : Submodule.Quotient.mk (p := rangeSub f) y = 0 := hz
  rwa [Submodule.Quotient.mk_eq_zero, mem_rangeSub] at h0

/-- Every epimorphism of differential graded modules is normal. -/
instance instIsNormalEpiCategory : IsNormalEpiCategory (DifferentialGradedModule.{u, v, w} A) := by
  refine ⟨fun {M N} f _ ↦ ?_⟩
  have hsurj : Function.Surjective f.toFun := epi_toFun_surjective f
  set eqv : (M.M ⧸ LinearMap.ker f.toFun) ≃ₗ[R] N.M :=
    f.toFun.quotKerEquivOfSurjective hsurj with heqv
  have hker : ∀ {T : DifferentialGradedModule.{u, v, w} A} (e : M ⟶ T), kernelι f ≫ e = 0 →
      LinearMap.ker f.toFun ≤ LinearMap.ker e.toFun := by
    intro T e he x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have hxk : x ∈ kerSub f := by rw [mem_kerSub]; exact hx
    have hcomp := LinearMap.congr_fun (congrArg Hom.toFun he) (⟨x, hxk⟩ : ↥(kerSub f))
    have hl : (kernelι f ≫ e).toFun (⟨x, hxk⟩ : ↥(kerSub f))
        = e.toFun ((kernelι f).toFun (⟨x, hxk⟩ : ↥(kerSub f))) := rfl
    rw [hl, kernelι_toFun_apply, Hom.hom_zero_toFun] at hcomp
    simpa using hcomp
  let descFun : ∀ {T : DifferentialGradedModule.{u, v, w} A} (e : M ⟶ T), kernelι f ≫ e = 0 →
      N.M →ₗ[R] T.M := fun {T} e he ↦
    (Submodule.liftQ (LinearMap.ker f.toFun) e.toFun (hker e he)) ∘ₗ eqv.symm.toLinearMap
  have hkey : ∀ {T : DifferentialGradedModule.{u, v, w} A}
      (e : M ⟶ T) (he : kernelι f ≫ e = 0) (x : M.M),
      descFun e he (f.toFun x) = e.toFun x := by
    intro T e he x
    change (Submodule.liftQ (LinearMap.ker f.toFun) e.toFun (hker e he)) (eqv.symm (f.toFun x))
        = e.toFun x
    have hsymm : eqv.symm (f.toFun x) = Submodule.Quotient.mk (p := LinearMap.ker f.toFun) x := by
      apply eqv.injective
      rw [LinearEquiv.apply_symm_apply, heqv]
      rfl
    rw [hsymm, Submodule.liftQ_apply]
  let desc : ∀ {T : DifferentialGradedModule.{u, v, w} A} (e : M ⟶ T), kernelι f ≫ e = 0 →
      (N ⟶ T) := fun {T} e he ↦
    { toFun := descFun e he
      map_smul := by
        intro y a
        obtain ⟨x, rfl⟩ := hsurj y
        rw [← f.map_smul, hkey e he, e.map_smul, hkey e he]
      map_grading := by
        intro n y hy
        obtain ⟨x', rfl⟩ := hsurj y
        set x : M.M := (DirectSum.decompose M.grading x' n : M.M) with hxdef
        have hxmem : x ∈ M.grading n := (DirectSum.decompose M.grading x' n).2
        have hfx : f.toFun x = f.toFun x' := by
          have hcg := comp_of_graded M.grading N.grading f.toFun
            f.map_grading x' n
          rw [← hxdef] at hcg
          rw [← hcg]
          exact (DirectSum.decompose_of_mem_same N.grading hy)
        rw [← hfx, hkey e he]
        exact e.map_grading n x hxmem
      map_d := by
        ext y
        obtain ⟨x, rfl⟩ := hsurj y
        change descFun e he (N.d (f.toFun x)) = T.d (descFun e he (f.toFun x))
        have hfd := LinearMap.congr_fun f.map_d x
        simp only [LinearMap.comp_apply] at hfd
        rw [← hfd, hkey e he, hkey e he]
        have hed := LinearMap.congr_fun e.map_d x
        simpa using hed }
  refine ⟨NormalEpi.mk (kernelObj f) (kernelι f) (kernelι_comp f) ?_⟩
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {T} e he ↦ desc e he) ?_ ?_
  · intro T e he
    apply Hom.ext
    ext x
    change descFun e he (f.toFun x) = e.toFun x
    exact hkey e he x
  · intro T e he m hm
    apply Hom.ext
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    change m.toFun (f.toFun x) = descFun e he (f.toFun x)
    rw [hkey e he]
    simpa using LinearMap.congr_fun (congrArg Hom.toFun hm) x

end DifferentialGradedModule
