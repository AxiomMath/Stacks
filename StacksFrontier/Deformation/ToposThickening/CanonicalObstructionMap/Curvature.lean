module

public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap.FreeDifferentialLift
import all StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap.FreeDifferentialLift

/-!
# The curvature of a lifted differential

The square of a lifted differential vanishes modulo the square-zero kernel, so it factors through
the kernel tensor complex. This file constructs that factorization, the kernel tensor complex
(`kernelComplex`, `kernelTensorInclusion`), the structure `LiftedDifferentialCurvature`, its
existence for every free lift, and the naturality of the curvature up to homotopy. It also
proves that every bounded-above complex of free `R`-modules admits a free differential lift.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Deformation.Obstruction

variable {R' R : Type u} [CommRing R'] [CommRing R]

open CategoryTheory.MonoidalCategory HomologicalComplex CochainComplex.DerivedTensor

private theorem freeDifferentialLift_square_smul_zero
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hzero : (RingHom.ker f) ^ 2 = ⊥) (L : FreeDifferentialLift f P)
    (n : ℤ) (x : L.X n) (a : RingHom.ker f) :
    L.d (n + 1) (n + 2) (L.d n (n + 1) (a • x)) = 0 := by
  show (L.d (n + 1) (n + 2)).hom
      ((L.d n (n + 1)).hom ((a : R') • x)) = 0
  rw [map_smul, map_smul]
  apply squareZeroIdeal_smul_mem (RingHom.ker f) hzero a.2
  rw [← L.reduction_ker]
  exact freeDifferentialLift_square_mem_ker L n x

private theorem freeDifferentialLift_square_eq_of_reduction_eq
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hzero : (RingHom.ker f) ^ 2 = ⊥) (L : FreeDifferentialLift f P)
    (n : ℤ) (x y : L.X n) (hxy : L.reduction n x = L.reduction n y) :
    L.d (n + 1) (n + 2) (L.d n (n + 1) x) =
      L.d (n + 1) (n + 2) (L.d n (n + 1) y) := by
  have hdiff : x - y ∈ RingHom.ker f • (⊤ : Submodule R' (L.X n)) := by
    rw [← L.reduction_ker, LinearMap.mem_ker]
    simp [map_sub, hxy]
  have hsq : L.d (n + 1) (n + 2) (L.d n (n + 1) (x - y)) = 0 := by
    refine Submodule.smul_induction_on hdiff ?_ ?_
    · intro a ha z hz
      exact freeDifferentialLift_square_smul_zero hzero L n z ⟨a, ha⟩
    · intro z w hz hw
      show (L.d (n + 1) (n + 2)).hom
        ((L.d n (n + 1)).hom (z + w)) = 0
      rw [map_add, map_add, hz, hw, add_zero]
  change (L.d (n + 1) (n + 2)).hom
      ((L.d n (n + 1)).hom (x - y)) = 0 at hsq
  rw [map_sub, map_sub] at hsq
  exact sub_eq_zero.mp hsq

private noncomputable def chosenFreeDifferentialLiftPreimage
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : FreeDifferentialLift f P) (n : ℤ) (y : P.X n) : L.X n :=
  Classical.choose (L.reduction_surjective n y)

private theorem chosenFreeDifferentialLiftPreimage_spec
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : FreeDifferentialLift f P) (n : ℤ) (y : P.X n) :
    L.reduction n (chosenFreeDifferentialLiftPreimage L n y) = y :=
  Classical.choose_spec (L.reduction_surjective n y)

private noncomputable def freeDifferentialLift_curvatureKernel
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hzero : (RingHom.ker f) ^ 2 = ⊥) (L : FreeDifferentialLift f P) (n : ℤ)
    : letI : Module R' (P.X n) := Module.compHom _ f
    P.X n →ₗ[R']
      ↥(RingHom.ker f • (⊤ : Submodule R' (L.X (n + 2)))) := by
  letI : Module R' (P.X n) := Module.compHom _ f
  classical
  refine
    { toFun := fun y =>
        ⟨L.d (n + 1) (n + 2)
          (L.d n (n + 1) (chosenFreeDifferentialLiftPreimage L n y)), ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · rw [← L.reduction_ker]
    exact freeDifferentialLift_square_mem_ker L n
      (chosenFreeDifferentialLiftPreimage L n _)
  · intro y z
    apply Subtype.ext
    have hred :
        L.reduction n (chosenFreeDifferentialLiftPreimage L n (y + z)) =
          L.reduction n
            (chosenFreeDifferentialLiftPreimage L n y +
              chosenFreeDifferentialLiftPreimage L n z) := by
      simp [map_add, chosenFreeDifferentialLiftPreimage_spec]
    have heq := freeDifferentialLift_square_eq_of_reduction_eq hzero L n
      (chosenFreeDifferentialLiftPreimage L n (y + z))
      (chosenFreeDifferentialLiftPreimage L n y +
        chosenFreeDifferentialLiftPreimage L n z) hred
    change (L.d (n + 1) (n + 2)).hom
        ((L.d n (n + 1)).hom
          (chosenFreeDifferentialLiftPreimage L n (y + z))) =
      (L.d (n + 1) (n + 2)).hom
        ((L.d n (n + 1)).hom
          (chosenFreeDifferentialLiftPreimage L n y +
            chosenFreeDifferentialLiftPreimage L n z)) at heq
    rw [map_add, map_add] at heq
    exact heq
  · intro r y
    apply Subtype.ext
    have hred :
        L.reduction n (chosenFreeDifferentialLiftPreimage L n (f r • y)) =
          L.reduction n (r • chosenFreeDifferentialLiftPreimage L n y) := by
      calc
        L.reduction n (chosenFreeDifferentialLiftPreimage L n (f r • y)) = f r • y :=
          chosenFreeDifferentialLiftPreimage_spec L n _
        _ = f r • L.reduction n (chosenFreeDifferentialLiftPreimage L n y) := by
          rw [chosenFreeDifferentialLiftPreimage_spec]
        _ = L.reduction n (r • chosenFreeDifferentialLiftPreimage L n y) :=
          (L.reduction n).map_smulₛₗ r _ |>.symm
    have heq := freeDifferentialLift_square_eq_of_reduction_eq hzero L n
      (chosenFreeDifferentialLiftPreimage L n (f r • y))
      (r • chosenFreeDifferentialLiftPreimage L n y) hred
    change (L.d (n + 1) (n + 2)).hom
        ((L.d n (n + 1)).hom
          (chosenFreeDifferentialLiftPreimage L n (f r • y))) =
      (L.d (n + 1) (n + 2)).hom
        ((L.d n (n + 1)).hom
          (r • chosenFreeDifferentialLiftPreimage L n y)) at heq
    rw [map_smul, map_smul] at heq
    have harg : (r : R') • y = f r • y := rfl
    rw [harg]
    exact heq

private theorem freeDifferentialLift_curvatureKernel_d
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hzero : (RingHom.ker f) ^ 2 = ⊥) (L : FreeDifferentialLift f P) (n : ℤ)
    (y : P.X n) :
    (L.d (n + 2) ((n + 1) + 2)).hom
        ((freeDifferentialLift_curvatureKernel hzero L n y).val) =
      (freeDifferentialLift_curvatureKernel hzero L (n + 1)
        (P.d n (n + 1) y)).val := by
  let x := chosenFreeDifferentialLiftPreimage L n y
  let x' := chosenFreeDifferentialLiftPreimage L (n + 1) (P.d n (n + 1) y)
  have hred : L.reduction (n + 1) x' =
      L.reduction (n + 1) (L.d n (n + 1) x) := by
    rw [chosenFreeDifferentialLiftPreimage_spec, L.reduction_d,
      chosenFreeDifferentialLiftPreimage_spec]
  have hsq := freeDifferentialLift_square_eq_of_reduction_eq hzero L (n + 1)
    x' (L.d n (n + 1) x) hred
  have hidx : (n + 1) + 1 = n + 2 := by omega
  rw [hidx] at hsq
  dsimp [freeDifferentialLift_curvatureKernel]
  rw [hidx]
  show (L.d (n + 2) ((n + 1) + 2)).hom
      ((L.d (n + 1) (n + 2)).hom ((L.d n (n + 1)).hom x)) =
    (L.d (n + 2) ((n + 1) + 2)).hom
      ((L.d (n + 1) (n + 2)).hom x')
  exact hsq.symm

/-- The square-zero ideal kills `I • ⊤`. -/
private theorem isTorsionBySet_ker_smul_top {f : R' →+* R}
    (hzero : (RingHom.ker f) ^ 2 = ⊥) (V : Type u) [AddCommGroup V] [Module R' V] :
    Module.IsTorsionBySet R' ↥(RingHom.ker f • (⊤ : Submodule R' V)) (RingHom.ker f) := by
  intro x a
  apply Subtype.ext
  exact squareZeroIdeal_smul_mem (RingHom.ker f) hzero a.2 x.2

@[instance_reducible]
private noncomputable def freeDifferentialLift_curvatureKernelModule
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) :
    Module R ↥(RingHom.ker f • (⊤ : Submodule R' (L.X (n + 2)))) := by
  let K := ↥(RingHom.ker f • (⊤ : Submodule R' (L.X (n + 2))))
  have hkill : Module.IsTorsionBySet R' K (RingHom.ker f) :=
    isTorsionBySet_ker_smul_top hzero _
  letI : Module (R' ⧸ RingHom.ker f) K := hkill.module
  let e : R' ⧸ RingHom.ker f ≃+* R := RingHom.quotientKerEquivOfSurjective hf
  exact Module.compHom K e.symm.toRingHom

private noncomputable def freeDifferentialLift_curvatureMap
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) :
    letI : Module R ↥(RingHom.ker f • (⊤ : Submodule R' (L.X (n + 2)))) :=
      freeDifferentialLift_curvatureKernelModule hf hzero L n
    P.X n →ₗ[R]
      ↥(RingHom.ker f • (⊤ : Submodule R' (L.X (n + 2)))) := by
  letI : Module R ↥(RingHom.ker f • (⊤ : Submodule R' (L.X (n + 2)))) :=
    freeDifferentialLift_curvatureKernelModule hf hzero L n
  letI : Module R' (P.X n) := Module.compHom _ f
  let φ := freeDifferentialLift_curvatureKernel hzero L n
  have hkill := isTorsionBySet_ker_smul_top hzero (L.X (n + 2))
  letI : Module (R' ⧸ RingHom.ker f)
      ↥(RingHom.ker f • (⊤ : Submodule R' (L.X (n + 2)))) := hkill.module
  let e : R' ⧸ RingHom.ker f ≃+* R := RingHom.quotientKerEquivOfSurjective hf
  refine { toFun := φ, map_add' := fun x y => φ.map_add x y, map_smul' := ?_ }
  intro r y
  obtain ⟨s, hs⟩ := hf r
  change φ (r • y) = r • φ y
  rw [← hs]
  change φ (f s • y) = e.symm (f s) • φ y
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply hf s, hkill.mk_smul]
  exact φ.map_smul s y

private theorem exists_freeDifferentialLift (f : R' →+* R) (hf : Function.Surjective f)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) :
    Nonempty (FreeDifferentialLift f P) := by
  classical
  refine ⟨{
    X := fun n => ModuleCat.of R' (freeLiftTerm f P hfree n)
    free := fun n => Module.Free.of_basis Finsupp.basisSingleOne
    d := fun i j => if h : i + 1 = j then
      ModuleCat.ofHom (chosenFreeLiftMap f hf P hfree i j) else 0
    shape := by
      intro i j h
      simp [h]
    reduction := fun n => freeLiftReduction f P hfree n
    reduction_surjective := fun n => freeLiftReduction_surjective f hf P hfree n
    reduction_ker := fun n => freeLiftReduction_ker f P hfree n
    reduction_d := by
      intro i j x
      by_cases h : i + 1 = j
      · simpa [h] using chosenFreeLiftMap_spec f hf P hfree i j x
      · simp [h]
  }⟩

private noncomputable abbrev kernelTensorEmbedding
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) :
    TensorProduct R (P.X n) (squareZeroKernelModule.{u, u} f hf) →+ L.X n :=
  (Submodule.subtype (RingHom.ker f • (⊤ : Submodule R' (L.X n)))).toAddMonoidHom.comp
    (freeDifferentialLift_kernelTensorEquiv hf hzero L n).toAddMonoidHom

private lemma kernelTensorEmbedding_injective
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) :
    Function.Injective (kernelTensorEmbedding hf hzero L n) :=
  Subtype.val_injective.comp (freeDifferentialLift_kernelTensorEquiv hf hzero L n).injective

/-- Induction over `P.X n ⊗ kernel` using pure tensors `L.reduction n x ⊗ₜ toCotangent a`. -/
private lemma tensor_induction_reduction {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift f P) (n : ℤ)
    (motive : TensorProduct R (P.X n) (squareZeroKernelModule.{u, u} f hf) → Prop)
    (hzero : motive 0) (hadd : ∀ z w, motive z → motive w → motive (z + w))
    (htmul : ∀ (x : L.X n) (a : RingHom.ker f),
      motive (L.reduction n x ⊗ₜ[R]
        (show squareZeroKernelModule f hf from (RingHom.ker f).toCotangent a)))
    (z : TensorProduct R (P.X n) (squareZeroKernelModule.{u, u} f hf)) : motive z := by
  induction z using TensorProduct.induction_on with
  | zero => exact hzero
  | add z w hz hw => exact hadd _ _ hz hw
  | tmul x a =>
    obtain ⟨x, rfl⟩ := L.reduction_surjective n x
    obtain ⟨a, rfl⟩ := (RingHom.ker f).toCotangent_surjective a
    exact htmul x a

private lemma kernelTensorEmbedding_natural
    {f : R' →+* R} (hf : Function.Surjective f)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (M : FreeDifferentialLift f Q) (i j : ℤ)
    (a : L.X i ⟶ M.X j) (b : P.X i ⟶ Q.X j)
    (hab : ∀ x, M.reduction j (a x) = b (L.reduction i x))
    (z : TensorProduct R (P.X i) (squareZeroKernelModule.{u, u} f hf)) :
    kernelTensorEmbedding hf hzero M j ((b ⊗ₘ 𝟙 _) z) =
      a (kernelTensorEmbedding hf hzero L i z) := by
  induction z using tensor_induction_reduction L i with
  | hzero => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | htmul x y =>
    show kernelTensorEmbedding hf hzero M j
      (b (L.reduction i x) ⊗ₜ[R] (RingHom.ker f).toCotangent y) = _
    rw [← hab]
    show (freeDifferentialLift_kernelTensorEquiv hf hzero M j _).val =
      a ((freeDifferentialLift_kernelTensorEquiv hf hzero L i _).val)
    rw [kernelTensorEquiv_tmul, kernelTensorEquiv_tmul]
    exact (a.hom.map_smul y.val x).symm

private lemma exists_lift_component
    {f : R' →+* R} (_hf : Function.Surjective f)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : FreeDifferentialLift f P) (M : FreeDifferentialLift f Q) (i j : ℤ)
    (a : P.X i ⟶ Q.X j) :
    ∃ a' : L.X i ⟶ M.X j, ∀ x, M.reduction j (a' x) = a (L.reduction i x) := by
  let : Module R' (Q.X j) := Module.compHom _ f
  let := L.free i
  let π : M.X j →ₗ[R'] Q.X j :=
    { toFun := M.reduction j
      map_add' := (M.reduction j).map_add
      map_smul' := (M.reduction j).map_smulₛₗ }
  let g : L.X i →ₗ[R'] Q.X j :=
    { toFun := fun x => a (L.reduction i x)
      map_add' := by intro x y; simp
      map_smul' := by intro r x; simp; rfl }
  obtain ⟨a', ha'⟩ := Module.projective_lifting_property π g (M.reduction_surjective j)
  exact ⟨ModuleCat.ofHom a', fun x => DFunLike.congr_fun ha' x⟩

private lemma exists_kernel_factor
    {f : R' →+* R} (hf : Function.Surjective f)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (M : FreeDifferentialLift f Q) (i j : ℤ)
    (φ : L.X i ⟶ M.X j) (hφ : ∀ x, M.reduction j (φ x) = 0) :
    ∃ h : P.X i ⟶ Q.X j ⊗ squareZeroKernelModule f hf,
      ∀ x, kernelTensorEmbedding hf hzero M j (h (L.reduction i x)) = φ x := by
  classical
  let := freeDifferentialLift_kernelModule hf hzero M j
  have himage (x) : φ x ∈ RingHom.ker f • (⊤ : Submodule R' (M.X j)) := by
    rw [← M.reduction_ker, LinearMap.mem_ker]
    exact hφ x
  have hsame (x y) (hxy : L.reduction i x = L.reduction i y) : φ x = φ y := by
    have hxy' : x - y ∈ RingHom.ker f • (⊤ : Submodule R' (L.X i)) := by
      rw [← L.reduction_ker, LinearMap.mem_ker]
      simp [hxy]
    have hz : φ (x - y) = 0 := by
      refine Submodule.smul_induction_on hxy' ?_ ?_
      · intro r hr z hz
        rw [map_smul]
        exact squareZeroIdeal_smul_mem (RingHom.ker f) hzero hr (himage z)
      · intro x y hx hy
        simp [hx, hy]
    simpa only [map_sub, sub_eq_zero] using hz
  let g (y : P.X i) := (freeDifferentialLift_kernelTensorEquiv hf hzero M j).symm
    ⟨φ (chosenFreeDifferentialLiftPreimage L i y), himage _⟩
  have hg (y) : kernelTensorEmbedding hf hzero M j (g y) =
      φ (chosenFreeDifferentialLiftPreimage L i y) :=
    congrArg Subtype.val ((freeDifferentialLift_kernelTensorEquiv hf hzero M j).apply_symm_apply _)
  have hs (r : R') (z : TensorProduct R (Q.X j) (squareZeroKernelModule.{u, u} f hf)) :
      kernelTensorEmbedding hf hzero M j (f r • z) =
        r • kernelTensorEmbedding hf hzero M j z := by
    show ((freeDifferentialLift_kernelTensorEquiv hf hzero M j) (f r • z)).val = _
    rw [map_smul, kernelModule_smul]
    rfl
  refine ⟨ModuleCat.ofHom { toFun := g, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro y z
    apply kernelTensorEmbedding_injective hf hzero M j
    rw [map_add, hg, hg, hg, ← map_add]
    apply hsame
    simp [chosenFreeDifferentialLiftPreimage_spec]
  · intro r y
    obtain ⟨r, rfl⟩ := hf r
    apply kernelTensorEmbedding_injective hf hzero M j
    simp only [RingHom.id_apply]
    rw [hs, hg, hg, ← map_smul]
    apply hsame
    simp [chosenFreeDifferentialLiftPreimage_spec]
  · intro x
    show kernelTensorEmbedding hf hzero M j (g (L.reduction i x)) = _
    rw [hg]
    exact hsame _ x (chosenFreeDifferentialLiftPreimage_spec L i _)

private noncomputable abbrev curvatureComponent
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) :
    P.X n ⟶ P.X (n + 2) ⊗ squareZeroKernelModule f hf := by
  letI := freeDifferentialLift_kernelModule hf hzero L (n + 2)
  exact ModuleCat.ofHom
    ((freeDifferentialLift_kernelTensorEquiv hf hzero L (n + 2)).symm.toLinearMap.comp
      (freeDifferentialLift_curvatureMap hf hzero L n))

private lemma curvatureComponent_embedding
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) (y : P.X n) :
    kernelTensorEmbedding hf hzero L (n + 2) (curvatureComponent hf hzero L n y) =
      (freeDifferentialLift_curvatureKernel hzero L n y).val :=
  congrArg Subtype.val
    ((freeDifferentialLift_kernelTensorEquiv hf hzero L (n + 2)).apply_symm_apply _)

private lemma curvatureComponent_square
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) (x : L.X n) :
    kernelTensorEmbedding hf hzero L (n + 2)
        (curvatureComponent hf hzero L n (L.reduction n x)) =
      L.d (n + 1) (n + 2) (L.d n (n + 1) x) := by
  rw [curvatureComponent_embedding hf hzero]
  exact freeDifferentialLift_square_eq_of_reduction_eq hzero L n _ x
    (chosenFreeDifferentialLiftPreimage_spec L n _)

private noncomputable abbrev termwiseKernelTensor
    (f : R' →+* R) (hf : Function.Surjective f)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (((tensoringRight (ModuleCat.{u} R)).obj (squareZeroKernelModule f hf)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P

private noncomputable def curvatureHom
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) : P ⟶ (termwiseKernelTensor f hf P)⟦(2 : ℤ)⟧ where
  f n := curvatureComponent hf hzero L n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [CochainComplex.shiftFunctor_obj_d']
    simp only [show (2 : ℤ).negOnePow = 1 by decide, one_smul]
    ext y
    apply kernelTensorEmbedding_injective hf hzero L ((i + 1) + 2)
    change kernelTensorEmbedding hf hzero L ((i + 1) + 2)
        (((P.d (i + 2) ((i + 1) + 2)) ⊗ₘ 𝟙 _)
          (curvatureComponent hf hzero L i y)) =
      kernelTensorEmbedding hf hzero L ((i + 1) + 2)
        (curvatureComponent hf hzero L (i + 1) (P.d i (i + 1) y))
    rw [kernelTensorEmbedding_natural hf hzero L L _ _
      (L.d _ _) (P.d _ _) (L.reduction_d _ _),
      curvatureComponent_embedding, curvatureComponent_embedding]
    exact freeDifferentialLift_curvatureKernel_d hzero L i y

private noncomputable abbrev termwiseKernelTensorMap
    (f : R' →+* R) (hf : Function.Surjective f)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (a : P ⟶ Q) :
    termwiseKernelTensor f hf P ⟶ termwiseKernelTensor f hf Q :=
  (((tensoringRight (ModuleCat.{u} R)).obj (squareZeroKernelModule f hf)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map a

private theorem curvatureHom_natural_homotopy
    {f : R' →+* R} (hf : Function.Surjective f)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (M : FreeDifferentialLift f Q) (α : P ⟶ Q) :
    Nonempty (Homotopy (α ≫ curvatureHom hf hzero M)
      (curvatureHom hf hzero L ≫
        (shiftFunctor _ (2 : ℤ)).map (termwiseKernelTensorMap f hf α))) := by
  classical
  choose a ha using fun i => exists_lift_component hf L M i i (α.f i)
  let φ (i j : ℤ) := a i ≫ M.d i j - L.d i j ≫ a j
  have hφ (i j : ℤ) (x : L.X i) : M.reduction j (φ i j x) = 0 := by
    show M.reduction j (M.d i j (a i x) - a j (L.d i j x)) = 0
    rw [map_sub, M.reduction_d, ha, ha, L.reduction_d]
    have h := ConcreteCategory.congr_hom (α.comm i j) (L.reduction i x)
    exact sub_eq_zero.mpr h
  choose h hh using fun i j => exists_kernel_factor hf hzero L M i j (φ i j) (hφ i j)
  refine ⟨homotopy_of_component_identity (fun i j => h i (j + 2)) ?_⟩
  intro n
  rw [CochainComplex.shiftFunctor_obj_d']
  simp only [show (2 : ℤ).negOnePow = 1 by decide, one_smul]
  ext y
  obtain ⟨x, rfl⟩ := L.reduction_surjective n y
  apply kernelTensorEmbedding_injective hf hzero M (n + 2)
  show kernelTensorEmbedding hf hzero M (n + 2)
      (curvatureComponent hf hzero M n (α.f n (L.reduction n x))) =
    kernelTensorEmbedding hf hzero M (n + 2)
      (h (n + 1) (n + 2) (P.d n (n + 1) (L.reduction n x)) +
        ((Q.d (n - 1 + 2) (n + 2)) ⊗ₘ 𝟙 _) (h n (n - 1 + 2) (L.reduction n x)) +
        (α.f (n + 2) ⊗ₘ 𝟙 _) (curvatureComponent hf hzero L n (L.reduction n x)))
  rw [show n - 1 + 2 = n + 1 by omega]
  rw [map_add, map_add, ← ha, curvatureComponent_square hf hzero,
    ← L.reduction_d, hh,
    kernelTensorEmbedding_natural hf hzero M M _ _ (M.d _ _) (Q.d _ _)
      (M.reduction_d _ _), hh,
    kernelTensorEmbedding_natural hf hzero L M _ _ (a _) (α.f _) (ha _),
    curvatureComponent_square hf hzero]
  dsimp [φ]
  simp only [map_sub]
  abel

/-- The kernel placed in degree zero, before localization. -/
noncomputable abbrev kernelComplex (f : R' →+* R) (hf : Function.Surjective f) :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (squareZeroKernelModule f hf)

/-- The inclusion of the degree `(n, 0)` tensor summand. -/
noncomputable abbrev kernelTensorInclusion (f : R' →+* R) (hf : Function.Surjective f)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    P.X n ⊗ squareZeroKernelModule f hf ⟶ (P ⊗ kernelComplex f hf).X n :=
  (𝟙 (P.X n) ⊗ₘ
      (singleObjXSelf (ComplexShape.up ℤ) 0 (squareZeroKernelModule f hf)).inv) ≫
    ιMapBifunctor P (kernelComplex f hf) (curriedTensor _) (ComplexShape.up ℤ)
      n 0 n (by simp)

-- `tensorSingleInclusion` and its invertibility come from `TorAmplitude.Comparison`, which
-- exposes the former so that the identifications below can unfold it.
private lemma kernelTensorInclusion_eq (f : R' →+* R) (hf : Function.Surjective f)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    kernelTensorInclusion f hf P n =
      (tensorSingleInclusion (squareZeroKernelModule f hf) P).f n := by
  simp [kernelTensorInclusion, tensorSingleInclusion, HomologicalComplex.ιTensorObj,
    singleObjXSelf, singleObjXIsoOfEq]
  rfl

/-- Every antidiagonal summand other than `(n, 0)` vanishes, so the degree-`(n, 0)` inclusion is
surjective in each degree. -/
lemma kernelTensorInclusion_surjective {f : R' →+* R} {hf : Function.Surjective f}
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Function.Surjective (kernelTensorInclusion f hf P n) := by
  have : IsIso (tensorSingleInclusion (squareZeroKernelModule.{u, u} f hf) P) :=
    tensorSingleInclusion_isIso (squareZeroKernelModule.{u, u} f hf) P
  rw [kernelTensorInclusion_eq]
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- The pure tensors `L.reduction n x ⊗ₜ a` generate `(P ⊗ kernelComplex f hf).X n`: only the
degree-zero kernel summand survives, and both the reduction of a free lift and the cotangent
map of the kernel are surjective. -/
lemma kernelTensor_induction {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : FreeDifferentialLift f P) (n : ℤ)
    (motive : (P ⊗ kernelComplex f hf).X n → Prop)
    (hzero : motive 0)
    (hadd : ∀ z w, motive z → motive w → motive (z + w))
    (htmul : ∀ (x : L.X n) (a : RingHom.ker f),
      motive (kernelTensorInclusion f hf P n
        (L.reduction n x ⊗ₜ[R]
          (show squareZeroKernelModule f hf from (RingHom.ker f).toCotangent a))))
    (z : (P ⊗ kernelComplex f hf).X n) : motive z := by
  obtain ⟨w, rfl⟩ := kernelTensorInclusion_surjective P n z
  induction w using tensor_induction_reduction L n with
  | hzero => simpa only [map_zero] using hzero
  | hadd w w' hw hw' => simpa only [map_add] using hadd _ _ hw hw'
  | htmul x a => exact htmul x a

/-- The differential of the kernel tensor complex acts on the degree-`(n, 0)` summand through the
differential of `P` alone. -/
lemma kernelTensorInclusion_d {f : R' →+* R} {hf : Function.Surjective f}
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : P.X n) (a : squareZeroKernelModule f hf) :
    (P ⊗ kernelComplex f hf).d n (n + 1)
        (kernelTensorInclusion f hf P n (x ⊗ₜ[R] a)) =
      kernelTensorInclusion f hf P (n + 1) (P.d n (n + 1) x ⊗ₜ[R] a) := by
  let K := kernelComplex f hf
  let ι (i : ℤ) := HomologicalComplex.ιMapBifunctor P K (curriedTensor (ModuleCat.{u} R))
    (ComplexShape.up ℤ) i 0 i (by simp)
  have hsum : ι n ≫ (P ⊗ K).d n (n + 1) =
      (P.d n (n + 1) ⊗ₘ 𝟙 (K.X 0)) ≫ ι (n + 1) := by
    show HomologicalComplex.ιMapBifunctor P K (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.up ℤ) n 0 n (by simp) ≫
        (HomologicalComplex.mapBifunctor P K (curriedTensor (ModuleCat.{u} R))
          (ComplexShape.up ℤ)).d n (n + 1) = _
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show n + 1 = n + 1 from rfl) 0 (n + 1) (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ n
        (show (0 : ℤ) + 1 = 1 from rfl) (n + 1) (by simp)]
    simp [K, ι, kernelComplex, CochainComplex.singleFunctor_obj_d,
      ComplexShape.ε₁, ComplexShape.ε₂]
  have h : kernelTensorInclusion f hf P n ≫ (P ⊗ K).d n (n + 1) =
      (P.d n (n + 1) ⊗ₘ 𝟙 (squareZeroKernelModule f hf)) ≫
        kernelTensorInclusion f hf P (n + 1) := by
    show (_ ≫ ι n) ≫ _ = _ ≫ _ ≫ ι (n + 1)
    rw [Category.assoc, hsum, ← Category.assoc, ← Category.assoc,
      tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    simp [K, kernelComplex, CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  exact ConcreteCategory.congr_hom h (x ⊗ₜ[R] a)

/-- The square of a lifted differential, factored through the kernel tensor complex.
The final fields give a K-flat computation of its target in the derived category. -/
structure LiftedDifferentialCurvature (f : R' →+* R) (hf : Function.Surjective f)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (L : FreeDifferentialLift f P) where
  /-- The additive map from the degree `n` term of `P ⊗ kernelComplex f hf` to `L.X n`. -/
  kernelEmbedding (n : ℤ) : (P ⊗ kernelComplex f hf).X n →+ L.X n
  kernelEmbedding_injective (n : ℤ) : Function.Injective (kernelEmbedding n)
  kernelEmbedding_tmul (n : ℤ) (x : L.X n) (a : RingHom.ker f) :
    kernelEmbedding n (kernelTensorInclusion f hf P n
      (L.reduction n x ⊗ₜ[R]
        (show squareZeroKernelModule f hf from (RingHom.ker f).toCotangent a))) =
      (a : R') • x
  /-- The chain map `P ⟶ (P ⊗ kernelComplex f hf)⟦2⟧` whose components give the square of the
  lifted differential. -/
  hom : P ⟶ (P ⊗ kernelComplex f hf)⟦(2 : ℤ)⟧
  hom_eq_square (n : ℤ) (x : L.X n) :
    kernelEmbedding (n + 2) (hom.f n (L.reduction n x)) =
      L.d (n + 1) (n + 2) (L.d n (n + 1) x)
  /-- The complex `P` is K-flat. -/
  isKFlat : P.KFlat
  /-- A complex resolving the kernel complex. -/
  kernelResolution : CochainComplex (ModuleCat.{u} R) ℤ
  /-- The complex `kernelResolution` is K-flat. -/
  kernelResolution_isKFlat : kernelResolution.KFlat
  /-- The map from `kernelResolution` to the kernel complex. -/
  kernelResolutionMap : kernelResolution ⟶ kernelComplex f hf
  /-- The map `kernelResolutionMap` is a quasi-isomorphism. -/
  kernelResolution_quasiIso : QuasiIso kernelResolutionMap
  /-- Tensoring `kernelResolutionMap` with `P` gives an isomorphism in the derived category. -/
  tensorResolution_isIso :
    IsIso (DerivedCategory.Q.map (𝟙 P ⊗ₘ kernelResolutionMap))

/-- The kernel embedding is semilinear over `f`: a scalar `f r` acting on the kernel tensor
complex becomes `r` acting on the lift. -/
lemma kernelEmbedding_smul {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift f P}
    (c : LiftedDifferentialCurvature f hf P L) (n : ℤ) (r : R')
    (z : (P ⊗ kernelComplex f hf).X n) :
    c.kernelEmbedding n (f r • z) = r • c.kernelEmbedding n z := by
  refine kernelTensor_induction L n
    (fun z => c.kernelEmbedding n (f r • z) = r • c.kernelEmbedding n z) ?_ ?_ ?_ z
  · simp
  · intro z w hz hw
    simp only [smul_add, map_add, hz, hw]
  · intro x a
    rw [← (kernelTensorInclusion f hf P n).hom.map_smul,
      TensorProduct.smul_tmul', ← (L.reduction n).map_smulₛₗ,
      c.kernelEmbedding_tmul, c.kernelEmbedding_tmul]
    simp only [smul_smul, mul_comm]

/-- The kernel embedding is a chain map: it carries the differential of the kernel tensor complex
to the lifted differential. -/
lemma kernelEmbedding_d {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift f P}
    (c : LiftedDifferentialCurvature f hf P L)
    (n : ℤ) (z : (P ⊗ kernelComplex f hf).X n) :
    c.kernelEmbedding (n + 1) ((P ⊗ kernelComplex f hf).d n (n + 1) z) =
      L.d n (n + 1) (c.kernelEmbedding n z) := by
  refine kernelTensor_induction L n
    (fun z => c.kernelEmbedding (n + 1) ((P ⊗ kernelComplex f hf).d n (n + 1) z) =
      L.d n (n + 1) (c.kernelEmbedding n z)) ?_ ?_ ?_ z
  · simp
  · intro z w hz hw
    simp only [map_add, hz, hw]
  · intro x a
    rw [kernelTensorInclusion_d, ← L.reduction_d, c.kernelEmbedding_tmul,
      c.kernelEmbedding_tmul, (L.d n (n + 1)).hom.map_smul]

private theorem exists_liftedDifferentialCurvature
    (f : R' →+* R) (hf : Function.Surjective f) (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hbound : P.IsStrictlyLE b) (hfree : ∀ n, Module.Free R (P.X n))
    (L : FreeDifferentialLift f P) : Nonempty (LiftedDifferentialCurvature f hf P L) := by
  classical
  let i := tensorSingleInclusion (squareZeroKernelModule.{u, u} f hf) P
  have : IsIso i := tensorSingleInclusion_isIso _ _
  let E (n : ℤ) : (P ⊗ kernelComplex f hf).X n →+ L.X n :=
    (kernelTensorEmbedding hf hzero L n).comp (inv (i.f n)).hom.toAddMonoidHom
  have hi (n : ℤ) (x : TensorProduct R (P.X n) (squareZeroKernelModule.{u, u} f hf)) :
      inv (i.f n) (i.f n x) = x := by
    show (i.f n ≫ inv (i.f n)) x = x
    rw [IsIso.hom_inv_id]
    rfl
  have hP := free_bounded_complex_isKFlat P b hbound hfree
  obtain ⟨Q, q, hQ, hq, ht⟩ := exists_kernel_resolution_data
    (squareZeroKernelModule.{u, u} f hf) P hP
  refine ⟨{
    kernelEmbedding := E
    kernelEmbedding_injective := fun n =>
      (kernelTensorEmbedding_injective hf hzero L n).comp
        ((ModuleCat.mono_iff_injective (inv (i.f n))).mp inferInstance)
    kernelEmbedding_tmul := ?_
    hom := curvatureHom hf hzero L ≫ (shiftFunctor _ (2 : ℤ)).map i
    hom_eq_square := ?_
    isKFlat := hP
    kernelResolution := Q
    kernelResolution_isKFlat := hQ
    kernelResolutionMap := q
    kernelResolution_quasiIso := hq
    tensorResolution_isIso := ht }⟩
  · intro n x a
    rw [kernelTensorInclusion_eq]
    show kernelTensorEmbedding hf hzero L n (inv (i.f n) (i.f n _)) = _
    rw [hi]
    exact kernelTensorEquiv_tmul hf hzero L n x a
  · intro n x
    show kernelTensorEmbedding hf hzero L (n + 2)
      (inv (i.f (n + 2)) (i.f (n + 2)
        (curvatureComponent hf hzero L n (L.reduction n x)))) = _
    rw [hi]
    exact curvatureComponent_square hf hzero L n x

private lemma LiftedDifferentialCurvature.kernelEmbedding_inclusion
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift f P}
    (c : LiftedDifferentialCurvature f hf P L) (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (n : ℤ) (z : TensorProduct R (P.X n) (squareZeroKernelModule.{u, u} f hf)) :
    c.kernelEmbedding n (kernelTensorInclusion f hf P n z) =
      kernelTensorEmbedding hf hzero L n z := by
  induction z using tensor_induction_reduction L n with
  | hzero => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | htmul x y =>
    rw [c.kernelEmbedding_tmul]
    exact (kernelTensorEquiv_tmul hf hzero L n x y).symm

private lemma LiftedDifferentialCurvature.hom_eq_curvatureHom
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift f P}
    (c : LiftedDifferentialCurvature f hf P L) (hzero : (RingHom.ker f) ^ 2 = ⊥) :
    c.hom = curvatureHom hf hzero L ≫ (shiftFunctor _ (2 : ℤ)).map
      (tensorSingleInclusion (squareZeroKernelModule.{u, u} f hf) P) := by
  ext n y
  obtain ⟨x, rfl⟩ := L.reduction_surjective n y
  apply c.kernelEmbedding_injective (n + 2)
  rw [c.hom_eq_square]
  show _ = c.kernelEmbedding (n + 2)
    ((tensorSingleInclusion (squareZeroKernelModule.{u, u} f hf) P).f (n + 2)
      (curvatureComponent hf hzero L n (L.reduction n x)))
  rw [← kernelTensorInclusion_eq, c.kernelEmbedding_inclusion hzero,
    curvatureComponent_square hf hzero]

private lemma tensorSingleInclusion_natural
    (f : R' →+* R) (hf : Function.Surjective f)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (a : P ⟶ Q) :
    termwiseKernelTensorMap f hf a ≫ tensorSingleInclusion (squareZeroKernelModule.{u, u} f hf) Q =
      tensorSingleInclusion (squareZeroKernelModule.{u, u} f hf) P ≫
        (a ⊗ₘ 𝟙 (kernelComplex f hf)) := by
  ext n : 1
  show (a.f n ▷ squareZeroKernelModule f hf) ≫
      ιMapBifunctor Q (kernelComplex f hf) (curriedTensor _) (ComplexShape.up ℤ) n 0 n _ =
    ιMapBifunctor P (kernelComplex f hf) (curriedTensor _) (ComplexShape.up ℤ) n 0 n _ ≫
      (mapBifunctorMap a (𝟙 (kernelComplex f hf)) (curriedTensor _) (ComplexShape.up ℤ)).f n
  rw [ι_mapBifunctorMap]
  simp
  rfl

private lemma LiftedDifferentialCurvature.hom_natural_homotopy
    {f : R' →+* R} {hf : Function.Surjective f}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : FreeDifferentialLift f P} {M : FreeDifferentialLift f Q}
    (c : LiftedDifferentialCurvature f hf P L) (d : LiftedDifferentialCurvature f hf Q M)
    (hzero : (RingHom.ker f) ^ 2 = ⊥) (a : P ⟶ Q) :
    Nonempty (Homotopy (a ≫ d.hom)
      (c.hom ≫ (shiftFunctor _ (2 : ℤ)).map (a ⊗ₘ 𝟙 (kernelComplex f hf)))) := by
  obtain ⟨h⟩ := curvatureHom_natural_homotopy hf hzero L M a
  have h' := h.compRight ((shiftFunctor _ (2 : ℤ)).map
    (tensorSingleInclusion (squareZeroKernelModule.{u, u} f hf) Q))
  simpa only [c.hom_eq_curvatureHom hzero, d.hom_eq_curvatureHom hzero,
    Category.assoc, ← CategoryTheory.Functor.map_comp, tensorSingleInclusion_natural]
    using Nonempty.intro h'

end Deformation.Obstruction
