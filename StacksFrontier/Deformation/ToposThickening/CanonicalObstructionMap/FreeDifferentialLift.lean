module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Finsupp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.RingTheory.Flat.Nilpotent

/-!
# Free differential lifts and their kernels

Bounded-above free representatives of objects of `D(R)`, lifts of such complexes to free
`R'`-modules with lifted differentials (`FreeDifferentialLift`), the square-zero kernel as an
`R`-module and as an object of `D(R)`, and the identification of the kernel of the reduction of
a free lifted term with the tensor product of the kernel and the original term.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Deformation.Obstruction

variable {R' R : Type u} [CommRing R'] [CommRing R]

private lemma exists_free_bounded_representative
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus K) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ),
      P.IsStrictlyLE b ∧ (∀ n, Module.Free R (P.X n)) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨N, hcoh⟩ := (DerivedCategory.minus_iff K).1 hK
  let b := N - 1
  have hcoh' : ∀ i : ℤ, b < i →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
    intro i hi
    exact hcoh i (by dsimp [b] at hi ⊢; omega)
  obtain ⟨P, hproj, hbound, ⟨ePK⟩⟩ :=
    StacksDraft.TorAmplitude.exists_projective_representative_of_isLE K b hcoh'
  let freeProp : ObjectProperty (ModuleCat.{u} R) := fun M => Module.Free R M
  have hzero : freeProp.ContainsZero :=
    ⟨ModuleCat.of R (Fin 0 → Shrink.{u} R), ModuleCat.isZero_of_subsingleton _, inferInstance⟩
  have hcover : ∀ X : ModuleCat.{u} R, ∃ (Y : ModuleCat.{u} R),
      ∃ (_ : freeProp Y), ∃ p : Y ⟶ X, Epi p := by
    intro X
    let e : Module.Basis X R (X →₀ Shrink.{u} R) :=
      ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
    refine ⟨ModuleCat.of R (X →₀ Shrink.{u} R), ⟨Module.Free.of_basis e,
      ModuleCat.ofHom (e.constr ℕ _root_.id), ?_⟩⟩
    rw [ModuleCat.epi_iff_surjective]
    intro x
    exact ⟨Finsupp.single x 1, by simp [e, Module.Basis.constr_apply]⟩
  have hPLE : P.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact HomologicalComplex.ExactAt.of_isZero (P.isZero_of_isStrictlyLE b i hi)
  obtain ⟨F, g, hg, hfree, hFbound⟩ :=
    (CochainComplex.exists_quasiIso_prop freeProp hcover b).2 P
  have hFfree : ∀ n, Module.Free R (F.X n) := hfree
  let e : DerivedCategory.Q.obj F ≅ K := asIso (DerivedCategory.Q.map g) ≪≫ ePK.symm
  exact ⟨F, b, hFbound, hFfree, ⟨e⟩⟩

private theorem free_bounded_complex_isKFlat
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) (hbound : P.IsStrictlyLE b) (hfree : ∀ n, Module.Free R (P.X n)) :
    P.KFlat := by
  let : P.IsStrictlyLE b := hbound
  let : ∀ n : ℤ, Module.Flat R (P.X n) := fun n => by
    let := hfree n
    infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat P b

private theorem exists_kernel_resolution_data
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) :
    ∃ (Q : CochainComplex (ModuleCat.{u} R) ℤ) (m : Q ⟶
        (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M),
      Q.KFlat ∧ QuasiIso m ∧ IsIso (DerivedCategory.Q.map (𝟙 P ⊗ₘ m)) := by
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  have hS : S.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i (by omega)
  obtain ⟨Q, b, m, hQLE, hQproj, hm⟩ :=
    StacksDraft.TorAmplitude.exists_projective_resolution S 0
  have hQ : Q.KFlat := StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective
    Q b hQproj
  have hqm : QuasiIso ((tensorLeft P).map m) :=
    StacksDraft.TorAmplitude.quasiIso_tensorLeft_map P hP m
  refine ⟨Q, m, hQ, hm, ?_⟩
  show IsIso (DerivedCategory.Q.map ((tensorLeft P).map m))
  infer_instance

private noncomputable abbrev freeLiftTerm (_f : R' →+* R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) (n : ℤ) : Type u := by
  letI := hfree n
  exact Module.Free.ChooseBasisIndex R (P.X n) →₀ R'

private noncomputable abbrev freeLiftBasis (_f : R' →+* R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) (n : ℤ) :
    Module.Basis (Module.Free.ChooseBasisIndex R (P.X n)) R (P.X n) := by
  letI := hfree n
  exact Module.Free.chooseBasis R (P.X n)

private noncomputable abbrev freeLiftReduction (f : R' →+* R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) (n : ℤ) :
    freeLiftTerm f P hfree n →ₛₗ[f] P.X n := by
  let b := freeLiftBasis f P hfree n
  letI : Module R' (Module.Free.ChooseBasisIndex R (P.X n) →₀ R) :=
    Module.compHom _ f
  exact b.repr.symm.toLinearMap.comp
    (Finsupp.mapRange.linearMap (RingHom.toSemilinearMap f))

private theorem freeLiftReduction_surjective (f : R' →+* R)
    (hf : Function.Surjective f) (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) (n : ℤ) :
    Function.Surjective (freeLiftReduction f P hfree n) := by
  classical
  intro y
  let b := freeLiftBasis f P hfree n
  obtain ⟨x, hx⟩ := Finsupp.mapRange_surjective f (RingHom.map_zero f) hf (b.repr y)
  refine ⟨x, ?_⟩
  show b.repr.symm (Finsupp.mapRange f (RingHom.map_zero f) x) = y
  rw [hx]
  exact b.repr.symm_apply_apply y

private theorem freeLiftReduction_ker (f : R' →+* R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) (n : ℤ) :
    LinearMap.ker (freeLiftReduction f P hfree n) =
      RingHom.ker f • (⊤ : Submodule R' (freeLiftTerm f P hfree n)) := by
  classical
  let b := freeLiftBasis f P hfree n
  have hker : LinearMap.ker (freeLiftReduction f P hfree n) =
      Finsupp.submodule (fun _ : Module.Free.ChooseBasisIndex R (P.X n) => RingHom.ker f) := by
    ext x
    show (b.repr.symm (Finsupp.mapRange f (RingHom.map_zero f)
      x) = 0) ↔
      x ∈
        Finsupp.submodule (fun _ : Module.Free.ChooseBasisIndex R (P.X n) => RingHom.ker f)
    rw [LinearEquiv.map_eq_zero_iff]
    rw [Finsupp.ext_iff]
    simp [Finsupp.mapRange_apply, RingHom.mem_ker]
  rw [hker]
  have hs := Finsupp.submodule_smul R' (Module.Free.ChooseBasisIndex R (P.X n))
    (fun _ => (⊤ : Submodule R' R')) (RingHom.ker f)
  show Finsupp.submodule
      (fun _ : Module.Free.ChooseBasisIndex R (P.X n) => RingHom.ker f) =
    RingHom.ker f • (⊤ : Submodule R'
      (Module.Free.ChooseBasisIndex R (P.X n) →₀ R'))
  simpa using hs

private theorem exists_freeLiftMap (f : R' →+* R) (hf : Function.Surjective f)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) (i j : ℤ) :
    ∃ φ : freeLiftTerm f P hfree i →ₗ[R'] freeLiftTerm f P hfree j,
      ∀ x, freeLiftReduction f P hfree j (φ x) =
        P.d i j (freeLiftReduction f P hfree i x) := by
  classical
  let (k : ℤ) : Module R' (P.X k) := Module.compHom (P.X k) f
  let : Module.Free R' (freeLiftTerm f P hfree i) :=
    Module.Free.of_basis (Finsupp.basisSingleOne)
  let : Module.Projective R' (freeLiftTerm f P hfree i) := Module.Projective.of_free
  let ρ (k : ℤ) : freeLiftTerm f P hfree k →ₗ[R'] P.X k := {
    toFun := freeLiftReduction f P hfree k
    map_add' := (freeLiftReduction f P hfree k).map_add
    map_smul' := fun r x => LinearMap.map_smulₛₗ (freeLiftReduction f P hfree k) r x }
  let dR : P.X i →ₗ[R'] P.X j := {
    toFun := P.d i j
    map_add' := (P.d i j).hom.map_add
    map_smul' := by
      intro r x
      show P.d i j (f r • x) = f r • P.d i j x
      exact (P.d i j).hom.map_smul (f r) x }
  let g : freeLiftTerm f P hfree i →ₗ[R'] P.X j := dR.comp (ρ i)
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property (ρ j) g
    (by
      show Function.Surjective (freeLiftReduction f P hfree j)
      exact freeLiftReduction_surjective f hf P hfree j)
  refine ⟨φ, ?_⟩
  intro x
  have h := congrArg (fun q : freeLiftTerm f P hfree i →ₗ[R'] P.X j => q x) hφ
  exact h

private noncomputable def chosenFreeLiftMap (f : R' →+* R) (hf : Function.Surjective f)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) (i j : ℤ) :
    freeLiftTerm f P hfree i →ₗ[R'] freeLiftTerm f P hfree j :=
  Classical.choose (exists_freeLiftMap f hf P hfree i j)

private theorem chosenFreeLiftMap_spec (f : R' →+* R) (hf : Function.Surjective f)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) (i j : ℤ) :
    ∀ x, freeLiftReduction f P hfree j (chosenFreeLiftMap f hf P hfree i j x) =
      P.d i j (freeLiftReduction f P hfree i x) :=
  Classical.choose_spec (exists_freeLiftMap f hf P hfree i j)

/-- The kernel of a surjection `R' → R`, regarded as an `R`-module. For a square-zero kernel,
its conormal module `I / I²` is canonically identified with `I`. -/
@[implicit_reducible]
noncomputable def squareZeroKernelModule {R' : Type (max u v)} {R : Type v}
    [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f) : ModuleCat.{max u v} R := by
  let e : R' ⧸ RingHom.ker f ≃+* R := RingHom.quotientKerEquivOfSurjective hf
  letI : Module R (RingHom.ker f).Cotangent :=
    Module.compHom (RingHom.ker f).Cotangent e.symm.toRingHom
  exact ModuleCat.of R (RingHom.ker f).Cotangent

/-- The kernel module, placed in cohomological degree zero in `D(R)`. -/
noncomputable abbrev squareZeroKernelObject {R' : Type (max u v)} {R : Type v}
    [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f) :
    DerivedCategory (ModuleCat.{max u v} R) :=
  (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj (squareZeroKernelModule f hf)

open CategoryTheory.MonoidalCategory HomologicalComplex CochainComplex.DerivedTensor

/-- Free graded modules lifting a complex, with lifted differentials. Reduction identifies
each term modulo the kernel ideal with the corresponding term of the complex. -/
structure FreeDifferentialLift (f : R' →+* R) (P : CochainComplex (ModuleCat.{u} R) ℤ) where
  /-- The graded module over `R'` lifting the terms of `P`. -/
  X : ℤ → ModuleCat.{u} R'
  /-- Each term `X n` is a free `R'`-module. -/
  free (n : ℤ) : Module.Free R' (X n)
  /-- The lifted differential from `X i` to `X j`. -/
  d (i j : ℤ) : X i ⟶ X j
  shape (i j : ℤ) (h : i + 1 ≠ j) : d i j = 0
  /-- The `f`-semilinear reduction map from `X n` to the term `P.X n`. -/
  reduction (n : ℤ) : X n →ₛₗ[f] P.X n
  reduction_surjective (n : ℤ) : Function.Surjective (reduction n)
  reduction_ker (n : ℤ) :
    LinearMap.ker (reduction n) = RingHom.ker f • (⊤ : Submodule R' (X n))
  reduction_d (i j : ℤ) (x : X i) :
    reduction j (d i j x) = P.d i j (reduction i x)

/-- The coordinates of an element of `I • ⊤` in a basis all lie in `I`. -/
private theorem repr_mem_submodule_of_mem_smul_top {A M ι : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (b : Module.Basis ι A M)
    {x : M} (hx : x ∈ I • (⊤ : Submodule A M)) :
    b.repr x ∈ Finsupp.submodule (fun _ : ι => I) := by
  have h := Submodule.mem_map_of_mem (f := b.repr.toLinearMap) hx
  rw [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr b.repr.surjective] at h
  have hh : b.repr x ∈ Finsupp.submodule (fun _ : ι => I • (⊤ : Submodule A A)) := by
    rw [Finsupp.submodule_smul A ι (fun _ => (⊤ : Submodule A A)) I]
    simpa using h
  rw [Finsupp.mem_submodule_iff] at hh ⊢
  intro i
  simpa using hh i

/-- A basis of a free lifted term reduces to a basis of the original term. The kernel condition
identifies the relations among the lifted basis vectors with coefficientwise membership in the
square-zero ideal. -/
private noncomputable def FreeDifferentialLift.reductionBasis
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : FreeDifferentialLift f P) (hf : Function.Surjective f) (n : ℤ)
    {ι : Type u} (b : Module.Basis ι R' (L.X n)) :
    Module.Basis ι R (P.X n) := by
  classical
  let v : ι → P.X n :=
    fun i => L.reduction n (b i)
  have hsum (l' : ι →₀ R') : L.reduction n (b.repr.symm l') =
      Finsupp.linearCombination R v (Finsupp.mapRange f (RingHom.map_zero f) l') := by
    rw [Module.Basis.repr_symm_apply]
    simp only [Finsupp.linearCombination_apply, map_finsuppSum, map_smulₛₗ]
    exact (Finsupp.sum_mapRange_index (f := f) (hf := RingHom.map_zero f)
      (g := l') (h := fun i r => r • v i) (by intro i; simp)).symm
  refine Module.Basis.mk (v := v) ?_ ?_
  · rw [linearIndependent_iff]
    intro l hl
    obtain ⟨l', hl'⟩ := Finsupp.mapRange_surjective f (RingHom.map_zero f) hf l
    have hred : L.reduction n (b.repr.symm l') = 0 := by rw [hsum, hl', hl]
    have hcoords := repr_mem_submodule_of_mem_smul_top (RingHom.ker f) b
      (by rwa [← L.reduction_ker, LinearMap.mem_ker] : b.repr.symm l' ∈ _)
    rw [LinearEquiv.apply_symm_apply] at hcoords
    apply Finsupp.ext
    intro i
    rw [← hl']
    simp [Finsupp.mapRange_apply, RingHom.mem_ker.mp (hcoords i)]
  · intro y hy
    obtain ⟨x, hx⟩ := L.reduction_surjective n y
    let l' := b.repr x
    have hx' : x = b.repr.symm l' := by simp [l']
    rw [← hx, hx', hsum l', Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Homotopic chain maps induce the same morphism after localization to the derived category.
This is the category-level bridge used to turn a chain-homotopy calculation of lifted squares
into equality of the corresponding derived morphisms. -/
private lemma derived_map_eq_of_homotopy
    {R : Type u} [CommRing R]
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    {f g : P ⟶ Q} (h : Homotopy f g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g :=
  DerivedCategory.Q_map_eq_of_homotopy _ h

/-- Package a degreewise homotopy identity into Mathlib's homotopy structure. Only the component
`H (i + 1) i` occurs in the homotopy, from source degree `i + 1` to target degree `i`. -/
private noncomputable def homotopy_of_component_identity
    {R : Type u} [CommRing R]
    {C D : CochainComplex (ModuleCat.{u} R) ℤ} {f g : C ⟶ D}
    (H : ∀ i j, C.X i ⟶ D.X j)
    (hcomm : ∀ i, f.f i = C.d i (i + 1) ≫ H (i + 1) i +
      H i (i - 1) ≫ D.d (i - 1) i + g.f i) : Homotopy f g := by
  refine Homotopy.mk (fun i j => if hij : i = j + 1 then H i j else 0)
    ?_ ?_
  · intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    by_cases heq : i = j + 1
    · exact (False.elim (hij (by omega)))
    · simp [heq]
  · intro i
    have hnext : (ComplexShape.up ℤ).Rel i (i + 1) := by simp [ComplexShape.up_Rel]
    have hprev : (ComplexShape.up ℤ).Rel (i - 1) i := by simp [ComplexShape.up_Rel]
    rw [dNext_eq _ hnext, prevD_eq _ hprev]
    rw [dite_eq_left rfl, dite_eq_left (show i = (i - 1) + 1 by omega)]
    exact hcomm i

private theorem freeDifferentialLift_square_mem_ker
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : FreeDifferentialLift f P) (n : ℤ) (x : L.X n) :
    L.d (n + 1) (n + 2) (L.d n (n + 1) x) ∈
      LinearMap.ker (L.reduction (n + 2)) := by
  rw [LinearMap.mem_ker]
  rw [L.reduction_d, L.reduction_d]
  show (P.d n (n + 1) ≫ P.d (n + 1) (n + 2)) (L.reduction n x) = 0
  rw [P.d_comp_d]
  rfl

private theorem squareZeroIdeal_mul {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I ^ 2 = ⊥) {a b : A} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have hab : a * b ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [hI] at hab
  simpa using hab

private theorem squareZeroIdeal_smul_mem {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (hI : I ^ 2 = ⊥)
    {a : A} (ha : a ∈ I) {x : M} (hx : x ∈ I • (⊤ : Submodule A M)) : a • x = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro b hb y hy
    rw [smul_smul]
    have hab := squareZeroIdeal_mul I hI ha hb
    simp [hab]
  · intro x y hx hy
    simp [hx, hy]

/-- A square-zero ideal annihilates itself, as a module over the ring. -/
private theorem squareZeroIdeal_isTorsionBySet {A : Type u} [CommRing A] (I : Ideal A)
    (hI : I ^ 2 = ⊥) : Module.IsTorsionBySet A I I := by
  intro x a
  apply Subtype.ext
  exact squareZeroIdeal_mul I hI a.2 x.2

/-- A square-zero ideal annihilates `I • ⊤` inside any module. -/
private theorem squareZeroIdeal_isTorsionBySet_smul_top {A M : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (hI : I ^ 2 = ⊥) :
    Module.IsTorsionBySet A ↥(I • (⊤ : Submodule A M)) I := by
  intro x a
  apply Subtype.ext
  exact squareZeroIdeal_smul_mem I hI a.2 x.2

@[instance_reducible, ega "IV 16.5.14"]
private noncomputable def squareZeroKernelIdealModule
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    (hzero : (RingHom.ker f) ^ 2 = ⊥) : Module R (RingHom.ker f) := by
  let I := RingHom.ker f
  have hkill := squareZeroIdeal_isTorsionBySet I hzero
  letI : Module (R' ⧸ I) I := hkill.module
  let e : R' ⧸ I ≃+* R := RingHom.quotientKerEquivOfSurjective hf
  exact Module.compHom I e.symm.toRingHom

private noncomputable def squareZeroCotangentToIdeal
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    (hzero : (RingHom.ker f) ^ 2 = ⊥) :
    letI : Module R (RingHom.ker f) := squareZeroKernelIdealModule f hf hzero
    letI : Module R (RingHom.ker f).Cotangent :=
      Module.compHom _ (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
    (RingHom.ker f).Cotangent ≃ₗ[R] RingHom.ker f := by
  let I := RingHom.ker f
  letI : Module R I := squareZeroKernelIdealModule f hf hzero
  let e : R' ⧸ I ≃+* R := RingHom.quotientKerEquivOfSurjective hf
  letI : Module R I.Cotangent := Module.compHom _ e.symm.toRingHom
  have hkill := squareZeroIdeal_isTorsionBySet I hzero
  have hkillC : Module.IsTorsionBySet R' I.Cotangent I := I.isTorsionBySet_cotangent
  letI : Module (R' ⧸ I) I := hkill.module
  letI : Module (R' ⧸ I) I.Cotangent := hkillC.module
  let toCotangentR : I →ₗ[R] I.Cotangent := {
    toFun := I.toCotangent
    map_add' := I.toCotangent.map_add
    map_smul' := by
      intro r x
      obtain ⟨s, hs⟩ := hf r
      change I.toCotangent (r • x) = r • I.toCotangent x
      rw [← hs]
      change I.toCotangent (e.symm (f s) • x) =
        e.symm (f s) • I.toCotangent x
      rw [RingHom.quotientKerEquivOfSurjective_symm_apply hf s,
        hkill.mk_smul, hkillC.mk_smul]
      exact I.toCotangent.map_smul s x }
  have hsurj : Function.Surjective toCotangentR := I.toCotangent_surjective
  have hinj : Function.Injective toCotangentR := by
    intro x y h
    change I.toCotangent x = I.toCotangent y at h
    apply Subtype.ext
    have hmem : ((x - y : I) : R') ∈ I ^ 2 :=
      (I.toCotangent_eq_zero (x - y)).mp (by rw [map_sub, h, sub_self])
    rw [hzero, Ideal.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  exact (LinearEquiv.ofBijective toCotangentR ⟨hinj, hsurj⟩).symm

@[instance_reducible]
private noncomputable def freeDifferentialLift_kernelModule
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) :
    Module R ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n))) := by
  let K := ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n)))
  have hkill := squareZeroIdeal_isTorsionBySet_smul_top (M := L.X n) (RingHom.ker f) hzero
  letI : Module (R' ⧸ RingHom.ker f) K := hkill.module
  let e : R' ⧸ RingHom.ker f ≃+* R := RingHom.quotientKerEquivOfSurjective hf
  exact Module.compHom K e.symm.toRingHom

private noncomputable def freeLiftKernelCoordinateEquivData
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    (hzero : (RingHom.ker f) ^ 2 = ⊥)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift f P)
    (n : ℤ) {ι : Type u} (b : Module.Basis ι R' (L.X n)) :
    letI : Module R (RingHom.ker f) := squareZeroKernelIdealModule f hf hzero
    letI : Module R ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n))) :=
      freeDifferentialLift_kernelModule hf hzero L n
    { e : (ι →₀ RingHom.ker f) ≃ₗ[R]
        ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n))) //
      ∀ (i : ι) (a : RingHom.ker f),
        ((e (Finsupp.single i a) : ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n)))) :
          L.X n) = (a : R') • b i } := by
  classical
  let I := RingHom.ker f
  let K := ↥(I • (⊤ : Submodule R' (L.X n)))
  letI : Module R I := squareZeroKernelIdealModule f hf hzero
  have hkillI := squareZeroIdeal_isTorsionBySet I hzero
  letI : Module (R' ⧸ I) I := hkillI.module
  let e : R' ⧸ I ≃+* R := RingHom.quotientKerEquivOfSurjective hf
  letI : Module R K := freeDifferentialLift_kernelModule hf hzero L n
  have hkillK := squareZeroIdeal_isTorsionBySet_smul_top (M := L.X n) I hzero
  letI : Module (R' ⧸ I) K := hkillK.module
  have hmem (i : ι) (a : I) : (a : R') • b i ∈ I • (⊤ : Submodule R' (L.X n)) := by
    rw [← L.reduction_ker, LinearMap.mem_ker]
    change L.reduction n ((a : R') • b i) = 0
    rw [map_smulₛₗ, RingHom.mem_ker.mp a.2, zero_smul]
  let coordMap : ∀ i : ι, I →ₗ[R] K := fun i => {
    toFun := fun a => ⟨(a : R') • b i, hmem i a⟩
    map_add' := by
      intro a a'
      apply Subtype.ext
      change ((a : R') + (a' : R')) • b i = _
      rw [add_smul]
      rfl
    map_smul' := by
      intro r a
      obtain ⟨s, hs⟩ := hf r
      apply Subtype.ext
      change ((r • a : I) : R') • b i =
        ((r • (⟨(a : R') • b i, hmem i a⟩ : K) : K) : L.X n)
      rw [← hs]
      change (e.symm (f s) • a : I) • b i =
        ((e.symm (f s) • (⟨(a : R') • b i, hmem i a⟩ : K) : K) : L.X n)
      rw [RingHom.quotientKerEquivOfSurjective_symm_apply hf s,
        hkillI.mk_smul, hkillK.mk_smul]
      change (s • (a : R')) • b i = s • ((a : R') • b i)
      exact (smul_smul s (a : R') (b i)).symm }
  let m : (ι →₀ I) →ₗ[R] K := Finsupp.lsum R coordMap
  have hm_repr (c : ι →₀ I) :
      b.repr (m c).val = Finsupp.mapRange (fun a : I => (a : R')) (by simp) c := by
    induction c using Finsupp.induction with
    | zero => simp [m]
    | @single_add i a c hi ha ih =>
      rw [m.map_add]
      change b.repr ((m (Finsupp.single i a)).val + (m c).val) = _
      rw [map_add, ih]
      have hs : b.repr (m (Finsupp.single i a)).val = Finsupp.single i (a : R') := by
        simp [m, Finsupp.lsum_single, coordMap]
      rw [hs]
      ext j
      simp [Finsupp.mapRange_apply, Finsupp.single_apply]
      split_ifs <;> rfl
  have hinj : Function.Injective m := by
    intro c d h
    have h' := congrArg (fun z : K => b.repr z.val) h
    rw [hm_repr c, hm_repr d] at h'
    apply Finsupp.ext
    intro i
    have hi := congrArg (fun z : ι →₀ R' => z i) h'
    exact Subtype.ext hi
  have hsurj : Function.Surjective m := by
    intro z
    let q := b.repr z.val
    have hcoords : q ∈ Finsupp.submodule (fun _ : ι => I) :=
      repr_mem_submodule_of_mem_smul_top I b z.2
    let c : ι →₀ I := Finsupp.onFinset q.support
      (fun i => ⟨q i, (Finsupp.mem_submodule_iff _ _).mp hcoords i⟩)
      (fun i hi => Finsupp.mem_support_iff.mpr fun hz => hi (Subtype.ext hz))
    have hmapc : Finsupp.mapRange (fun a : I => (a : R')) (by simp) c = q := by
      ext i
      simp [c]
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact b.repr.injective ((hm_repr c).trans hmapc)
  refine ⟨LinearEquiv.ofBijective m ⟨hinj, hsurj⟩, ?_⟩
  intro i a
  change ((m (Finsupp.single i a) : K) : L.X n) = _
  simp [m, Finsupp.lsum_single, coordMap]

/-- The coordinate identification of the kernel submodule of a free lifted term with the
finitely supported families of kernel elements indexed by a basis. -/
private noncomputable def freeLiftKernelCoordinateEquiv
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    (hzero : (RingHom.ker f) ^ 2 = ⊥)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (L : FreeDifferentialLift f P)
    (n : ℤ) {ι : Type u} (b : Module.Basis ι R' (L.X n)) :
    letI : Module R (RingHom.ker f) := squareZeroKernelIdealModule f hf hzero
    letI : Module R ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n))) :=
      freeDifferentialLift_kernelModule hf hzero L n
    (ι →₀ RingHom.ker f) ≃ₗ[R]
      ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n))) :=
  (freeLiftKernelCoordinateEquivData f hf hzero L n b).val

private noncomputable def freeDifferentialLift_kernelTensorEquiv
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) :
    letI : Module R ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n))) :=
      freeDifferentialLift_kernelModule hf hzero L n
    TensorProduct R (P.X n) (squareZeroKernelModule.{u, u} f hf) ≃ₗ[R]
      ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n))) := by
  classical
  letI : Module R (RingHom.ker f) := squareZeroKernelIdealModule f hf hzero
  letI : Module R (RingHom.ker f).Cotangent :=
    Module.compHom _ (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  letI : Module.Free R' (L.X n) := L.free n
  let b := Module.Free.chooseBasis R' (L.X n)
  let bR := L.reductionBasis hf n b
  letI : Module R ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n))) :=
    freeDifferentialLift_kernelModule hf hzero L n
  exact (TensorProduct.congr bR.repr (squareZeroCotangentToIdeal f hf hzero)) ≪≫ₗ
    TensorProduct.finsuppScalarLeft R (RingHom.ker f)
      (Module.Free.ChooseBasisIndex R' (L.X n)) ≪≫ₗ
    freeLiftKernelCoordinateEquiv f hf hzero L n b

private lemma kernelModule_smul
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) (r : R')
    (x : ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n)))) :
    letI := freeDifferentialLift_kernelModule hf hzero L n
    ((f r • x : ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n)))) : L.X n) = r • x.val := by
  let K := ↥(RingHom.ker f • (⊤ : Submodule R' (L.X n)))
  have hkill := squareZeroIdeal_isTorsionBySet_smul_top (M := L.X n) (RingHom.ker f) hzero
  let : Module (R' ⧸ RingHom.ker f) K := hkill.module
  show (((RingHom.quotientKerEquivOfSurjective hf).symm (f r)) • x : K).val = _
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply hf r, hkill.mk_smul]
  rfl

private lemma kernelTensorEquiv_tmul
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (L : FreeDifferentialLift f P) (n : ℤ) (x : L.X n) (a : RingHom.ker f) :
    (freeDifferentialLift_kernelTensorEquiv hf hzero L n
      (L.reduction n x ⊗ₜ[R]
        (show squareZeroKernelModule f hf from (RingHom.ker f).toCotangent a))).val =
      (a : R') • x := by
  classical
  let := freeDifferentialLift_kernelModule hf hzero L n
  let : Module R (RingHom.ker f) := squareZeroKernelIdealModule f hf hzero
  let : Module R (RingHom.ker f).Cotangent :=
    Module.compHom _ (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  let := L.free n
  let b := Module.Free.chooseBasis R' (L.X n)
  let e := freeDifferentialLift_kernelTensorEquiv hf hzero L n
  have hb (i) : (e (L.reduction n (b i) ⊗ₜ[R]
      (show squareZeroKernelModule f hf from (RingHom.ker f).toCotangent a))).val =
      (a : R') • b i := by
    have hr : (L.reductionBasis hf n b).repr (L.reduction n (b i)) =
        Finsupp.single i 1 := by
      have hi : (L.reductionBasis hf n b) i = L.reduction n (b i) := by
        simp [FreeDifferentialLift.reductionBasis]
      rw [← hi, Module.Basis.repr_self]
    have ha : squareZeroCotangentToIdeal f hf hzero ((RingHom.ker f).toCotangent a) = a :=
      (squareZeroCotangentToIdeal f hf hzero).apply_symm_apply a
    show (freeLiftKernelCoordinateEquiv f hf hzero L n b
      (TensorProduct.finsuppScalarLeft R (RingHom.ker f) _
        (TensorProduct.congr (L.reductionBasis hf n b).repr
          (squareZeroCotangentToIdeal f hf hzero) _))).val = _
    rw [TensorProduct.congr_tmul, hr, ha,
      TensorProduct.finsuppScalarLeft_apply_tmul]
    simp only [Finsupp.sum_single_index, zero_smul, Finsupp.single_zero, one_smul]
    exact (freeLiftKernelCoordinateEquivData f hf hzero L n b).property i a
  show (e _).val = _
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smulₛₗ, TensorProduct.sum_tmul, ← TensorProduct.smul_tmul',
    RingHom.id_apply, AddSubmonoidClass.coe_finsetSum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [kernelModule_smul hf hzero, hb, smul_comm]

end Deformation.Obstruction
