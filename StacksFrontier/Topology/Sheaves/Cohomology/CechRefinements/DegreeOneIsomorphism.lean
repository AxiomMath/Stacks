module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.CategoryTheory.Sites.CechComplexExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.ColimitOverRefinements
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology computes first sheaf cohomology

Let `X` be a topological space and `F` an abelian sheaf on `X`. There is a canonical comparison

`Ȟ^p(X, F) = colim_𝒰 Ȟ^p(𝒰, F) ⟶ H^p(X, F)`

from the Čech cohomology of `X`, the colimit over all open coverings of the Čech cohomology of
the covering, to sheaf cohomology. In degree one this comparison is an isomorphism.

## Main results

* `Stacks.Cohomology.CechRefinement.isIso_colimitToCohomology_one`: the degree-one
  Čech-to-sheaf-cohomology comparison of a topological space is an isomorphism.
* `Stacks.Cohomology.CechRefinement.isIso_colimit_desc_of_injective_of_jointly_surjective`: a
  cocone of abelian groups whose legs are injective and jointly surjective, indexed by a
  category in which any two objects have a common target, exhibits its vertex as the colimit.
* `Stacks.Cohomology.CechRefinement.mono_cechCohomologyToCohomology_one`: for a single covering,
  the degree-one Čech-to-sheaf-cohomology comparison is a monomorphism.
* `Stacks.Cohomology.CechRefinement.exists_cechCohomologyToCohomology_preimage`: every
  degree-one sheaf cohomology class comes from the Čech cohomology of some covering.

## References

* [Stacks Project, Tag 09V1](https://stacks.math.columbia.edu/tag/09V1)
* [Stacks Project, Tag 09UZ](https://stacks.math.columbia.edu/tag/09UZ)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe s t w v u

namespace Stacks.Cohomology.CechRefinement

/-! ### A criterion for a cocone of abelian groups to be a colimit -/

section ColimitCriterion

variable {I : Type s} [Category.{t} I] (D : I ⥤ AddCommGrpCat.{w}) [HasColimit D]

/-- A cocone of abelian groups whose legs are injective and jointly surjective, over an index
category in which any two objects have a common target, has an invertible canonical map out of
the colimit. -/
theorem isIso_colimit_desc_of_injective_of_jointly_surjective (c : Cocone D)
    (hconn : ∀ i j : I, ∃ k, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hinj : ∀ i, Function.Injective (c.ι.app i))
    (hsurj : ∀ y : c.pt, ∃ i, ∃ x : D.obj i, c.ι.app i x = y) :
    IsIso (colimit.desc D c) := by
  classical
  choose i x hx using hsurj
  let g : c.pt → ↥(colimit D) := fun y ↦ colimit.ι D (i y) (x y)
  have hg (j : I) (z : D.obj j) : g (c.ι.app j z) = colimit.ι D j z := by
    obtain ⟨k, ⟨f⟩, ⟨h⟩⟩ := hconn (i (c.ι.app j z)) j
    have heq : D.map f (x (c.ι.app j z)) = D.map h z := by
      apply hinj k
      have hf := congrArg (fun T ↦ T (x (c.ι.app j z))) (c.w f)
      have hh := congrArg (fun T ↦ T z) (c.w h)
      simp only [ConcreteCategory.comp_apply] at hf hh
      exact hf.trans ((hx _).trans hh.symm)
    dsimp only [g]
    have hf := congrArg (fun T ↦ T (x (c.ι.app j z))) (colimit.w D f)
    have hh := congrArg (fun T ↦ T z) (colimit.w D h)
    simp only [ConcreteCategory.comp_apply] at hf hh
    exact hf.symm.trans ((congrArg (colimit.ι D k) heq).trans hh)
  let G : c.pt ⟶ colimit D := AddCommGrpCat.ofHom
    { toFun := g
      map_zero' := by simpa only [map_zero] using hg (i 0) 0
      map_add' := by
        intro a b
        obtain ⟨k, ⟨f⟩, ⟨h⟩⟩ := hconn (i a) (i b)
        have ha : c.ι.app k (D.map f (x a)) = a := by
          simpa using (congrArg (fun T ↦ T (x a)) (c.w f)).trans (hx a)
        have hb : c.ι.app k (D.map h (x b)) = b := by
          simpa using (congrArg (fun T ↦ T (x b)) (c.w h)).trans (hx b)
        rw [← ha, ← hb, ← map_add, hg, hg, hg, map_add] }
  refine ⟨⟨G, ?_, ?_⟩⟩
  · refine colimit.hom_ext fun j ↦ ?_
    ext z
    change G ((colimit.ι D j ≫ colimit.desc D c) z) = colimit.ι D j z
    rw [colimit.ι_desc]
    exact hg j z
  · ext y
    change (colimit.ι D (i y) ≫ colimit.desc D c) (x y) = y
    rw [colimit.ι_desc]
    exact hx y

end ColimitCriterion

/-! ### The inclusion of an object into the zeroth term of an injective resolution -/

section Resolution

variable {A : Type w} [Category.{t} A] [Abelian A] {Y : A} (J : InjectiveResolution Y)

/-- The inclusion of an object into the degree-zero term of an injective resolution exhibits
the object as the kernel of the first differential of the resolution. -/
def inclusionZero_isKernel :
    IsLimit (KernelFork.ofι J.inclusionZero
      (CategoryTheory.InjectiveResolution.inclusionZero_comp_d J)) := by
  have hzS : ∀ i j : ℤ, ((CochainComplex.singleFunctor A 0).obj Y).d i j = 0 :=
    fun i j ↦ CochainComplex.singleFunctor_obj_d Y 0 i j
  have hiS : IsIso (((CochainComplex.singleFunctor A 0).obj Y).iCycles 0) :=
    HomologicalComplex.isIso_iCycles _ 0 1 (by simp) (hzS 0 1)
  have hpS : IsIso (((CochainComplex.singleFunctor A 0).obj Y).homologyπ 0) :=
    HomologicalComplex.isIso_homologyπ _ (-1) 0 (by simp) (hzS (-1) 0)
  have hdL : J.cochainComplex.d (-1) 0 = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE J.cochainComplex 0 (-1) (by omega)).eq_of_src _ _
  have hpL : IsIso (J.cochainComplex.homologyπ 0) :=
    HomologicalComplex.isIso_homologyπ _ (-1) 0 (by simp) hdL
  have hhm : IsIso (HomologicalComplex.homologyMap J.ι' 0) :=
    (quasiIsoAt_iff_isIso_homologyMap J.ι' 0).mp inferInstance
  have hcm : IsIso (HomologicalComplex.cyclesMap J.ι' 0) := by
    have h : HomologicalComplex.cyclesMap J.ι' 0 =
        ((CochainComplex.singleFunctor A 0).obj Y).homologyπ 0 ≫
          HomologicalComplex.homologyMap J.ι' 0 ≫ inv (J.cochainComplex.homologyπ 0) := by
      rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    rw [h]
    infer_instance
  let wv : Y ⟶ J.cochainComplex.cycles 0 :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).inv ≫
      inv (((CochainComplex.singleFunctor A 0).obj Y).iCycles 0) ≫
      HomologicalComplex.cyclesMap J.ι' 0
  have hwv : IsIso wv := by
    dsimp only [wv]
    infer_instance
  have hfac : wv ≫ J.cochainComplex.iCycles 0 = J.inclusionZero := by
    dsimp only [wv, CategoryTheory.InjectiveResolution.inclusionZero]
    simp
  exact IsLimit.ofIsoLimit (J.cochainComplex.cyclesIsKernel 0 1 (by simp))
    (Fork.ext (asIso wv) (by simpa only [Fork.ι_ofι, asIso_hom] using hfac)).symm

/-- The inclusion of an object into the degree-zero term of an injective resolution is a
monomorphism. -/
theorem mono_inclusionZero : Mono J.inclusionZero :=
  mono_of_isLimit_fork (inclusionZero_isKernel J)

/-- An object is the kernel of the first differential of an injective resolution: the sequence
`Y ⟶ J⁰ ⟶ J¹` is exact. -/
theorem inclusionZero_exact :
    (ShortComplex.mk J.inclusionZero (J.cochainComplex.d 0 1)
      (CategoryTheory.InjectiveResolution.inclusionZero_comp_d J)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (inclusionZero_isKernel J)

/-- A functor preserving zero morphisms sends the inclusion into an injective resolution and the
first differential to a pair of composable morphisms with zero composite. -/
private theorem map_inclusionZero_comp_map_d {B : Type*} [Category B] [Preadditive B]
    (C : A ⥤ B) [C.PreservesZeroMorphisms] :
    C.map J.inclusionZero ≫ C.map (J.cochainComplex.d 0 1) = 0 := by
  rw [← C.map_comp, CategoryTheory.InjectiveResolution.inclusionZero_comp_d, Functor.map_zero]

end Resolution

/-! ### Reading off a column of a total complex -/

section Total

variable {A : Type w} [Category.{t} A] [Preadditive A]
  (K : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- The projection of the total complex of a double complex onto one of its constituent
objects, zero on every other summand of the given total degree. -/
def totalProjection (p q n : ℤ) : (K.total (ComplexShape.up ℤ)).X n ⟶ (K.X p).X q :=
  K.totalDesc (fun i j _ ↦ if hi : i = p then if hj : j = q then
    eqToHom (by subst i j; rfl) else 0 else 0)

/-- The projection is a retraction of the inclusion of the summand it names. -/
theorem ι_totalProjection (p q n : ℤ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℤ) p q n h ≫ totalProjection K p q n = 𝟙 _ := by
  simp [totalProjection]

/-- The projection kills every summand other than the one it names. -/
private theorem ι_totalProjection_of_ne (p q i j n : ℤ) (h : i + j = n)
    (hne : i ≠ p ∨ j ≠ q) :
    K.ιTotal (ComplexShape.up ℤ) i j n h ≫ totalProjection K p q n = 0 := by
  rcases hne with hne | hne <;> simp [totalProjection, hne]

/-- For a first-quadrant double complex, the projection of the total complex in degree zero onto
the summand in bidegree `(0, 0)`, followed by the inclusion of that summand, is the identity. -/
private theorem total_zero_decomposition
    (hz : ∀ i j, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) :
    totalProjection K 0 0 0 ≫ K.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp) = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i + j = 0 at hij
  by_cases hi : i = 0
  · subst i
    obtain rfl : j = 0 := by omega
    simp [← Category.assoc, ι_totalProjection]
  · exact (hz i j (by omega)).eq_of_src _ _

/-- The differential of a total complex, read on the summand in bidegree `(0, q)`. -/
private theorem total_zero_row_d (q : ℤ) :
    K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ (K.total (ComplexShape.up ℤ)).d q (q + 1) =
      (K.d 0 1).f q ≫ K.ιTotal (ComplexShape.up ℤ) 1 q (q + 1) (by simp; omega) +
      (K.X 0).d q (q + 1) ≫ K.ιTotal (ComplexShape.up ℤ) 0 (q + 1) (q + 1) (by simp) := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    K.d₁_eq (ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel 0 1) q (q + 1)
      (by simp; omega),
    K.d₂_eq (ComplexShape.up ℤ) 0 (by simp : (ComplexShape.up ℤ).Rel q (q + 1)) (q + 1)
      (by simp)]
  simp [ComplexShape.ε₁, ComplexShape.ε₂]

/-- The differential of a total complex out of total degree zero. -/
private theorem total_zero_d :
    K.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp) ≫ (K.total (ComplexShape.up ℤ)).d 0 1 =
      (K.d 0 1).f 0 ≫ K.ιTotal (ComplexShape.up ℤ) 1 0 1 (by simp) +
      (K.X 0).d 0 1 ≫ K.ιTotal (ComplexShape.up ℤ) 0 1 1 (by simp) := by
  simpa using total_zero_row_d K 0

end Total

section TotalAbelian

variable {A : Type w} [Category.{t} A] [Abelian A]
  (K : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [K.HasTotal (ComplexShape.up ℤ)]

/-- First homology of a map into a total complex is a monomorphism as soon as the map factors
through the zeroth column and that column begins with a kernel. -/
private theorem mono_homologyMap_total_of_kernel
    (hz : ∀ i j, i < 0 ∨ j < 0 → IsZero ((K.X i).X j))
    {B : CochainComplex A ℤ} (f : B ⟶ K.X 0) (hf : f ≫ K.d 0 1 = 0)
    (hker : IsLimit (KernelFork.ofι (f.f 0)
      (show f.f 0 ≫ (K.d 0 1).f 0 = 0 from congrArg (fun g ↦ g.f 0) hf)))
    [Mono (f.f 1)] (β : B ⟶ K.total (ComplexShape.up ℤ))
    (hβ : ∀ p, β.f p = f.f p ≫ K.ιTotal (ComplexShape.up ℤ) 0 p p (by simp)) :
    Mono (HomologicalComplex.homologyMap β 1) := by
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements β 0 1 2 (by simp) (by simp)]
  intro T x hx y hxy
  let b := y ≫ totalProjection K 0 0 0
  have hy : y = b ≫ K.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp) := by
    dsimp only [b]
    rw [Category.assoc, total_zero_decomposition K hz, Category.comp_id]
  rw [hβ 1, hy, Category.assoc, total_zero_d, Preadditive.comp_add,
    ← Category.assoc, ← Category.assoc] at hxy
  have hb : b ≫ (K.d 0 1).f 0 = 0 := by
    simpa [Category.assoc, Preadditive.add_comp, ι_totalProjection,
      ι_totalProjection_of_ne K 1 0 0 1 1 (by simp) (Or.inl (by decide))] using
      (congrArg (fun z ↦ z ≫ totalProjection K 1 0 1) hxy).symm
  let a := hker.lift (KernelFork.ofι b hb)
  have ha : a ≫ f.f 0 = b := hker.fac _ WalkingParallelPair.zero
  refine ⟨T, 𝟙 T, inferInstance, a, ?_⟩
  rw [Category.id_comp, ← cancel_mono (f.f 1), Category.assoc, ← f.comm 0 1,
    ← Category.assoc, ha]
  simpa [Category.assoc, Preadditive.add_comp, ι_totalProjection,
    ι_totalProjection_of_ne K 0 1 1 0 1 (by simp) (Or.inl (by decide))] using
    congrArg (fun z ↦ z ≫ totalProjection K 0 1 1) hxy

end TotalAbelian

/-! ### Lifting a homology class along a map into a total complex -/

section Preimage

/-- Two cycles differing by a boundary have the same homology class. -/
theorem homologyπ_eq_of_boundary (K : CochainComplex AddCommGrpCat.{w} ℤ) (n m : ℤ)
    (x y : K.cycles n) (b : K.X m) (h : K.iCycles n x = K.iCycles n y + K.d m n b) :
    K.homologyπ n x = K.homologyπ n y := by
  have hxy : x = y + K.toCycles m n b := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    simpa only [map_add, ← ConcreteCategory.comp_apply, K.toCycles_i] using h
  rw [hxy, map_add]
  have hz := ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ m n) b
  change K.homologyπ n (K.toCycles m n b) = 0 at hz
  rw [hz, add_zero]

/-- The image of a cycle under a map of complexes is again killed by the differential. -/
theorem differential_map_cycle {R T : CochainComplex AddCommGrpCat.{w} ℤ} (α : R ⟶ T)
    (n : ℤ) (t : R.cycles n) : T.d n (n + 1) (α.f n (R.iCycles n t)) = 0 := by
  have h : R.iCycles n ≫ α.f n ≫ T.d n (n + 1) = 0 := by
    rw [α.comm n (n + 1), ← Category.assoc, R.iCycles_d n (n + 1), zero_comp]
  exact ConcreteCategory.congr_hom h t

/-- A homology class in the target of two maps of complexes is in the image of the first as
soon as, on representatives, the two differ by a boundary. -/
theorem exists_homologyMap_preimage_of_boundary
    {B R T : CochainComplex AddCommGrpCat.{w} ℤ} (α : R ⟶ T) (β : B ⟶ T) (n m : ℤ)
    [Mono (β.f (n + 1))] (t : R.cycles n) (z : B.X n) (b : T.X m)
    (h : α.f n (R.iCycles n t) = β.f n z + T.d m n b) :
    ∃ x, HomologicalComplex.homologyMap β n x =
      HomologicalComplex.homologyMap α n (R.homologyπ n t) := by
  have hz : B.d n (n + 1) z = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (β.f (n + 1))).mp inferInstance
    have h' := congrArg (T.d n (n + 1)) h
    have hdd : T.d n (n + 1) (T.d m n b) = 0 :=
      ConcreteCategory.congr_hom (T.d_comp_d m n (n + 1)) b
    rw [differential_map_cycle, map_add, hdd, add_zero] at h'
    rw [map_zero]
    change (B.d n (n + 1) ≫ β.f (n + 1)) z = 0
    rw [← β.comm n (n + 1)]
    exact h'.symm
  have hz' : z ∈ (B.sc n).g.hom.ker := by
    change B.d n ((ComplexShape.up ℤ).next n) z = 0
    rw [ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)]
    exact hz
  let zc : B.cycles n := (B.sc n).abCyclesIso.inv ⟨z, hz'⟩
  have hzc : B.iCycles n zc = z := (B.sc n).abCyclesIso_inv_apply_iCycles ⟨z, hz'⟩
  refine ⟨B.homologyπ n zc, ?_⟩
  simp only [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality]
  simp only [ConcreteCategory.comp_apply]
  refine (homologyπ_eq_of_boundary T n m _ _ b ?_).symm
  change (HomologicalComplex.cyclesMap α n ≫ T.iCycles n) t =
    (HomologicalComplex.cyclesMap β n ≫ T.iCycles n) zc + _
  rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i]
  simpa only [ConcreteCategory.comp_apply, hzc] using h

/-- A homology class of the total complex lifts along a map factoring through the zeroth
column, as soon as a representative, read on the summand in bidegree `(1, 0)`, is the image of
a section of the summand in bidegree `(0, 0)`. -/
private theorem exists_homologyMap_preimage_of_vertical_lift
    (K : HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    {B R : CochainComplex AddCommGrpCat.{w} ℤ} (f : B ⟶ K.X 0) (hf : f ≫ K.d 0 1 = 0)
    (he : (ShortComplex.mk (f.f 1) ((K.d 0 1).f 1) (congrArg (fun g ↦ g.f 1) hf)).Exact)
    [Mono (f.f 2)]
    (α : R ⟶ K.total (ComplexShape.up ℤ)) (β : B ⟶ K.total (ComplexShape.up ℤ))
    (hβ : ∀ p, β.f p = f.f p ≫ K.ιTotal (ComplexShape.up ℤ) 0 p p (by simp))
    (a : R.X 1 ⟶ (K.X 1).X 0)
    (hα : α.f 1 = a ≫ K.ιTotal (ComplexShape.up ℤ) 1 0 1 (by simp))
    (t : R.cycles 1) (b : (K.X 0).X 0) (hb : (K.d 0 1).f 0 b = a (R.iCycles 1 t)) :
    ∃ x, HomologicalComplex.homologyMap β 1 x =
      HomologicalComplex.homologyMap α 1 (R.homologyπ 1 t) := by
  let T := K.total (ComplexShape.up ℤ)
  let wz := -((K.X 0).d 0 1 b)
  let bt := K.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp) b
  have h : α.f 1 (R.iCycles 1 t) =
      K.ιTotal (ComplexShape.up ℤ) 0 1 1 (by simp) wz + T.d 0 1 bt := by
    have hd := ConcreteCategory.congr_hom (total_zero_d K) b
    change T.d 0 1 bt =
      K.ιTotal (ComplexShape.up ℤ) 1 0 1 (by simp) ((K.d 0 1).f 0 b) +
      K.ιTotal (ComplexShape.up ℤ) 0 1 1 (by simp) ((K.X 0).d 0 1 b) at hd
    rw [hd, hα]
    simp only [ConcreteCategory.comp_apply, hb, wz, map_neg]
    abel
  have hw : (K.d 0 1).f 1 wz = 0 := by
    have hd := congrArg (T.d 1 2) h
    have hd' := ConcreteCategory.congr_hom (total_zero_row_d K 1) wz
    change T.d 1 2 (K.ιTotal (ComplexShape.up ℤ) 0 1 1 (by simp) wz) =
      K.ιTotal (ComplexShape.up ℤ) 1 1 2 (by simp) ((K.d 0 1).f 1 wz) +
      K.ιTotal (ComplexShape.up ℤ) 0 2 2 (by simp) ((K.X 0).d 1 2 wz) at hd'
    have hdd : T.d 1 2 (T.d 0 1 bt) = 0 := ConcreteCategory.congr_hom (T.d_comp_d 0 1 2) bt
    have hc : T.d 1 2 (α.f 1 (R.iCycles 1 t)) = 0 := by
      simpa using differential_map_cycle α 1 t
    rw [hc, map_add, hdd, add_zero] at hd
    rw [hd'] at hd
    have hp := congrArg (totalProjection K 1 1 2) hd
    rw [map_zero, map_add] at hp
    change 0 = (K.ιTotal (ComplexShape.up ℤ) 1 1 2 (by simp) ≫ totalProjection K 1 1 2)
      ((K.d 0 1).f 1 wz) + (K.ιTotal (ComplexShape.up ℤ) 0 2 2 (by simp) ≫
        totalProjection K 1 1 2) ((K.X 0).d 1 2 wz) at hp
    rw [ι_totalProjection, ι_totalProjection_of_ne K 1 1 0 2 2 (by simp)
      (Or.inl (by decide))] at hp
    change 0 = (K.d 0 1).f 1 wz + 0 at hp
    exact (hp.trans (add_zero _)).symm
  obtain ⟨z, hz⟩ := (ShortComplex.ab_exact_iff _).mp he wz hw
  have hmi : Mono (K.ιTotal (ComplexShape.up ℤ) 0 2 2 (by simp)) :=
    mono_of_mono_fac (ι_totalProjection K 0 2 2 (by simp))
  have hβ2 : Mono (β.f (1 + 1)) := by
    rw [show (1 : ℤ) + 1 = 2 by norm_num, hβ 2]
    infer_instance
  refine exists_homologyMap_preimage_of_boundary α β 1 0 t z bt ?_
  simpa only [hβ 1, ConcreteCategory.comp_apply, hz] using h

end Preimage

/-! ### Exactness of the Čech complex functor in a fixed degree -/

section Exactness

variable {X : Type u} [TopologicalSpace X]

open OpenCoverSet

/-- Evaluating the integer-graded Čech complex of an open covering in a fixed degree is a left
exact functor of the abelian sheaf. -/
theorem preservesFiniteLimits_cechIntEval (U : OpenCoverSet X) (p : ℤ) :
    PreservesFiniteLimits (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
      (hypercover U) ⋙
        HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) p) := by
  have hext : PreservesFiniteLimits
      (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max u v}) :=
    ⟨fun _ _ _ ↦ HomologicalComplex.preservesLimitsOfShape_of_eval _ fun i' ↦ by
      by_cases h : ∃ i, ComplexShape.embeddingUpNat.f i = i'
      · obtain ⟨i, hi⟩ := h
        exact preservesLimitsOfShape_of_natIso
          (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso _ hi).symm
      · refine Functor.preservesLimitsOfShape_of_isZero _ ?_ _
        rw [Functor.isZero_iff]
        exact fun L ↦ L.isZero_extend_X _ i' (by tauto)⟩
  have hcech : PreservesFiniteLimits
      (CechSite.cechComplexFunctor (hypercover U) (A := AddCommGrpCat.{max u v})) := by
    unfold CechSite.cechComplexFunctor FormalCoproduct.cochainComplexFunctor
      FormalCoproduct.cosimplicialObjectFunctor
    infer_instance
  dsimp only [CechSite.cechComplexIntFunctor, CechSite.cechComplexIntFunctorPre]
  infer_instance

end Exactness

/-! ### The comparison for a single covering is a monomorphism -/

section Mono

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})]

open OpenCoverSet

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})] in
/-- The Čech bicomplex of a bounded-below resolution vanishes outside the first quadrant. -/
private theorem cechBicomplex_isZero_of_neg (U : OpenCoverSet X)
    {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}}
    (J : InjectiveResolution G) (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero (((CechSite.cechBicomplex.{v} (Opens.grothendieckTopology X) (hypercover U)
      J.cochainComplex).X i).X j) := by
  rcases h with hi | hj
  · exact (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U) ⋙
      HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) j).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE J.cochainComplex 0 i hi)
  · exact CechSite.isZero_cechComplexIntFunctorPre_X.{v} (hypercover U)
      (J.cochainComplex.X i).obj j hj

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- First homology of the map induced by the inclusion of a sheaf into the zeroth term of an
injective resolution is a monomorphism. -/
private theorem mono_homologyMap_cechResolutionComparison_beta (U : OpenCoverSet X)
    {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}}
    (J : InjectiveResolution G)
    (r : CechSite.CechResolutionComparison.{v} (Opens.grothendieckTopology X) (hypercover U)
      (hypercover_mem_grothendieckTopology U) G J) :
    Mono (HomologicalComplex.homologyMap r.β 1) := by
  set C := CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U)
  have hC0 := preservesFiniteLimits_cechIntEval.{v} U 0
  have hC1 := preservesFiniteLimits_cechIntEval.{v} U 1
  have hmono := mono_inclusionZero J
  have hf1 : Mono ((C.map J.inclusionZero).f 1) :=
    (C ⋙ HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) 1).map_mono _
  exact mono_homologyMap_total_of_kernel _ (cechBicomplex_isZero_of_neg.{v} U J)
    (C.map J.inclusionZero) (map_inclusionZero_comp_map_d J _)
    (KernelFork.mapIsLimit _ (inclusionZero_isKernel J)
      (C ⋙ HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) 0)) r.β r.β_f

omit [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- For a single open covering, the degree-one comparison from Čech cohomology to sheaf
cohomology is a monomorphism. -/
theorem mono_cechCohomologyToCohomology_one (U : OpenCoverSet X)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    Mono ((CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X)
      (hypercover U) (hypercover_mem_grothendieckTopology U) 1).app G) := by
  obtain ⟨r⟩ := CechSite.nonempty_cechResolutionComparison.{v}
    (Opens.grothendieckTopology X) (hypercover U)
    (hypercover_mem_grothendieckTopology U) G (InjectiveResolution.of G)
  have hβ : Mono (HomologicalComplex.homologyMap r.β 1) :=
    mono_homologyMap_cechResolutionComparison_beta.{v} U _ r
  have hiso : IsIso ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u v} 1).hom.app
      ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover U)).obj G)) :=
    Iso.isIso_hom ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u v} 1).app
      ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover U)).obj G))
  have hQ : Mono ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 1).map
      (DerivedCategory.Q.map r.β)) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro p p' hpp'
    have hn := DerivedCategory.homologyFunctorFactors_hom_naturality r.β 1
    have h1 := ConcreteCategory.congr_hom hn p
    have h2 := ConcreteCategory.congr_hom hn p'
    simp only [ConcreteCategory.comp_apply] at h1 h2
    rw [hpp', h2] at h1
    have h3 := (AddCommGrpCat.mono_iff_injective _).mp hβ h1
    exact ((AddCommGrpCat.mono_iff_injective _).mp inferInstance h3).symm
  have hcc : ((CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X)
        (hypercover U) (hypercover_mem_grothendieckTopology U) 1).app G) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 1).map
          (DerivedCategory.Q.map r.β) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 1).map
          (r.αIso.inv ≫ (InjectiveResolution.of G).toRightDerived
            ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
              (op (⊤ : Opens X)))) :=
    (congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 1).map
        r.comparison).trans
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 1).map_comp _ _)
  have hm2 : Mono ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 1).map
      (r.αIso.inv ≫ (InjectiveResolution.of G).toRightDerived
        ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
          (op (⊤ : Opens X))))) := inferInstance
  rw [hcc]
  exact mono_comp' hQ hm2

end Mono

/-! ### Local lifting along a surjection of abelian sheaves -/

section Surjective

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

open OpenCoverSet

/-- A global section of the middle term of an exact sequence of abelian sheaves which dies in
the right-hand term is locally in the image of the left-hand term, so there is an open covering
of the space on each member of which it lifts. -/
private theorem exists_openCoverSet_local_preimage
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}))
    (hS : S.Exact) (s : S.X₂.obj.obj (op (⊤ : Opens X)))
    (hs : S.g.hom.app (op (⊤ : Opens X)) s = 0) :
    ∃ U : OpenCoverSet X, ∀ i : U.members, ∃ t, S.f.hom.app (op i.1) t =
      S.X₂.obj.map (homOfLE (show i.1 ≤ (⊤ : Opens X) from le_top)).op s := by
  classical
  have hR : (ShortComplex.mk S.iCycles S.g S.iCycles_g).Exact :=
    ShortComplex.exact_of_f_is_kernel _ S.cyclesIsKernel
  have he : PreservesFiniteLimits ((sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v}).obj (op (⊤ : Opens X))) := by
    change PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v} ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{max u v}).obj (op (⊤ : Opens X)))
    infer_instance
  have hRe := hR.map_of_mono_of_preservesKernel
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
      (op (⊤ : Opens X))) inferInstance inferInstance
  obtain ⟨t, ht⟩ : ∃ t : S.cycles.obj.obj (op (⊤ : Opens X)),
      S.iCycles.hom.app (op (⊤ : Opens X)) t = s :=
    (ShortComplex.ab_exact_iff _).mp hRe s hs
  have hepi : Epi S.toCycles := hS.epi_toCycles
  have hls : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) S.toCycles.hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u v} S.toCycles).mpr inferInstance
  let P : Set (Opens X) := fun V ↦ ∃ t, S.f.hom.app (op V) t =
    S.X₂.obj.map (homOfLE (show V ≤ (⊤ : Opens X) from le_top)).op s
  suffices hP : (⨆ i : P, i.1) = (⊤ : Opens X) from ⟨⟨P, hP⟩, fun i ↦ i.2⟩
  refine le_antisymm le_top fun x hx ↦ ?_
  obtain ⟨V, i, ⟨wit, hwit⟩, hxV⟩ := hls.imageSieve_mem t x hx
  have hV : V ∈ P := by
    refine ⟨wit, ?_⟩
    have h := congrArg (fun z ↦ S.iCycles.hom.app (op V) z) hwit
    change (S.toCycles.hom.app (op V) ≫ S.iCycles.hom.app (op V)) wit =
      (S.cycles.obj.map i.op ≫ S.iCycles.hom.app (op V)) t at h
    rw [S.iCycles.hom.naturality] at h
    have hcomp : S.toCycles.hom.app (op V) ≫ S.iCycles.hom.app (op V) =
        S.f.hom.app (op V) := congrArg (fun g ↦ g.hom.app (op V)) S.toCycles_i
    rw [hcomp] at h
    change S.f.hom.app (op V) wit =
      S.X₂.obj.map i.op (S.iCycles.hom.app (op (⊤ : Opens X)) t) at h
    rwa [ht, Subsingleton.elim i (homOfLE (show V ≤ (⊤ : Opens X) from le_top))] at h
  exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- A family of local lifts along a morphism of abelian sheaves, one over each member of an
open covering, assembles into a degree-zero Čech cochain lifting the augmentation of the global
section being lifted. -/
private theorem exists_cechAugmentation_preimage (U : OpenCoverSet X)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}} (f : F ⟶ G)
    (s : G.obj.obj (op (⊤ : Opens X)))
    (hs : ∀ i : U.members, ∃ t, f.hom.app (op i.1) t =
      G.obj.map (homOfLE (show i.1 ≤ (⊤ : Opens X) from le_top)).op s) :
    ∃ b, ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
      (hypercover U)).map f).f 0 b =
      CechSite.cechAugmentationInt.{v} (Opens.grothendieckTopology X) (hypercover U) G s := by
  classical
  choose t ht using hs
  refine ⟨(CechSite.cechIntXZeroIsoPre.{v} (hypercover U) F.obj).inv
    (CechSite.familyToCochain (hypercover U) F.obj t), ?_⟩
  have hb : ((CechSite.cechComplexFunctor (hypercover U)).map f.hom).f 0
      (CechSite.familyToCochain (hypercover U) F.obj t) =
      CechSite.cechAugmentationPre.{v} (hypercover U) G.obj s := by
    apply (CechSite.productAddEquiv (CechSite.cochainFactor (hypercover U) G.obj 0)).injective
    ext k
    change Pi.π (CechSite.cochainFactor (hypercover U) G.obj 0) k
        (((CechSite.cechComplexFunctor (hypercover U)).map f.hom).f 0
          (CechSite.familyToCochain (hypercover U) F.obj t)) =
      Pi.π (CechSite.cochainFactor (hypercover U) G.obj 0) k
        (CechSite.cechAugmentationPre.{v} (hypercover U) G.obj s)
    refine (CechSite.cechComplexFunctor_map_f_π_apply.{max u v} (hypercover U) f.hom 0 k _).trans ?_
    refine (congrArg (fun z ↦ f.hom.app
      (op ((∏ᶜ fun j ↦ Over.mk ((hypercover U).f (k j)) : Over (⊤ : Opens X)).left)) z)
        (CechSite.familyToCochain_π (hypercover U) F.obj t k)).trans ?_
    refine (app_map_op f.hom _ (t (k 0))).symm.trans ?_
    refine (congrArg (fun z ↦ G.obj.map (Pi.π (fun j : Fin 1 ↦
      Over.mk ((hypercover U).f (k j))) 0).left.op z) (ht (k 0))).trans ?_
    exact (map_op_comp_apply_eq G.obj _ _ _ s).trans
      (CechSite.cechAugmentationPre_π_apply.{v} (hypercover U) G.obj k s).symm
  have hmap : ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover U)).map f).f 0 =
      (CechSite.cechIntXZeroIsoPre.{v} (hypercover U) F.obj).hom ≫
        ((CechSite.cechComplexFunctor (hypercover U)).map f.hom).f 0 ≫
        (CechSite.cechIntXZeroIsoPre.{v} (hypercover U) G.obj).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := 0) rfl
  have key : (CechSite.cechIntXZeroIsoPre.{v} (hypercover U) F.obj).inv ≫
      ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover U)).map f).f 0 =
      ((CechSite.cechComplexFunctor (hypercover U)).map f.hom).f 0 ≫
        (CechSite.cechIntXZeroIsoPre.{v} (hypercover U) G.obj).inv := by
    rw [hmap, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ((ConcreteCategory.comp_apply _ _ _).symm.trans
    (ConcreteCategory.congr_hom key _)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  exact (congrArg (fun z ↦ (CechSite.cechIntXZeroIsoPre.{v} (hypercover U) G.obj).inv z)
    hb).trans (ConcreteCategory.comp_apply _ _ s).symm

end Surjective

/-! ### Joint surjectivity of the comparisons -/

section JointSurjectivity

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})]

open OpenCoverSet

/-- Every first sheaf cohomology class of an abelian sheaf on a topological space comes from the
first Čech cohomology of some open covering. -/
theorem exists_cechCohomologyToCohomology_preimage
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})
    (y : (CechSite.derivedSectionsFunctor.{max u v} (Opens.grothendieckTopology X)
      (⊤ : Opens X) ⋙ DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v} 1).obj G) :
    ∃ U : OpenCoverSet X, ∃ x, ((CechSite.cechCohomologyToCohomology.{v}
      (Opens.grothendieckTopology X) (hypercover U)
        (hypercover_mem_grothendieckTopology U) 1).app G) x = y := by
  classical
  set H := DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} 1
  set q := DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u v} 1
  set Γ := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}).obj
    (op (⊤ : Opens X))
  let J := InjectiveResolution.of G
  let R := (Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex
  let ρ := J.toRightDerived Γ
  have hΦ : IsIso (q.inv.app R ≫ H.map ρ) := inferInstance
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective (R.homologyπ 1)).mp inferInstance
    (inv (q.inv.app R ≫ H.map ρ) y)
  have hS : (ShortComplex.mk _ _ (J.cochainComplex.d_comp_d 0 1 2)).Exact :=
    (J.cochainComplex.exactAt_iff' 0 1 2 (by simp) (by simp)).mp
      (CochainComplex.exactAt_of_isLE J.cochainComplex 0 1 (by decide))
  have hcyc : (J.cochainComplex.d 1 2).hom.app (op (⊤ : Opens X)) (R.iCycles 1 t) = 0 := by
    have h : (R.iCycles 1 ≫ R.d 1 2) t = 0 := by rw [R.iCycles_d 1 2]; simp
    exact (ConcreteCategory.comp_apply (R.iCycles 1) (R.d 1 2) t).symm.trans h
  obtain ⟨U, hlocal⟩ :=
    exists_openCoverSet_local_preimage.{v} _ hS (R.iCycles 1 t) hcyc
  obtain ⟨b, hb⟩ := exists_cechAugmentation_preimage.{v} U (J.cochainComplex.d 0 1)
    (R.iCycles 1 t) hlocal
  obtain ⟨r⟩ := CechSite.nonempty_cechResolutionComparison.{v}
    (Opens.grothendieckTopology X) (hypercover U)
    (hypercover_mem_grothendieckTopology U) G J
  have hC1 := preservesFiniteLimits_cechIntEval.{v} U 1
  have hC2 := preservesFiniteLimits_cechIntEval.{v} U 2
  have hmono := mono_inclusionZero J
  have hf2 : Mono (((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
      (hypercover U)).map J.inclusionZero).f 2) :=
    (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U) ⋙
      HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) 2).map_mono _
  obtain ⟨x, hx⟩ := exists_homologyMap_preimage_of_vertical_lift _
    ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
      (hypercover U)).map J.inclusionZero)
    (map_inclusionZero_comp_map_d J _)
    ((inclusionZero_exact J).map_of_mono_of_preservesKernel
      (CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X) (hypercover U) ⋙
        HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) 1)
      inferInstance inferInstance)
    r.α r.β r.β_f
    (CechSite.cechAugmentationInt.{v} (Opens.grothendieckTopology X) (hypercover U)
      (J.cochainComplex.X 1)) (r.α_f 1) t b hb
  let k := q.inv.app ((CechSite.cechBicomplex.{v} (Opens.grothendieckTopology X)
      (hypercover U) J.cochainComplex).total (ComplexShape.up ℤ)) ≫
    H.map r.αIso.inv ≫ H.map ρ
  have hcc : ((CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X)
        (hypercover U) (hypercover_mem_grothendieckTopology U) 1).app G) =
      H.map (DerivedCategory.Q.map r.β) ≫ H.map r.αIso.inv ≫ H.map ρ :=
    (congrArg H.map r.comparison).trans ((H.map_comp _ _).trans
      (congrArg (fun z ↦ H.map (DerivedCategory.Q.map r.β) ≫ z) (H.map_comp _ _)))
  have hα : HomologicalComplex.homologyMap r.α 1 ≫ k = q.inv.app R ≫ H.map ρ := by
    have hid : H.map (DerivedCategory.Q.map r.α) ≫ H.map r.αIso.inv = 𝟙 _ := by
      rw [← H.map_comp, ← r.αIso_hom, Iso.hom_inv_id, H.map_id]
    have h1 : HomologicalComplex.homologyMap r.α 1 ≫ k =
        q.inv.app R ≫ H.map (DerivedCategory.Q.map r.α) ≫ H.map r.αIso.inv ≫ H.map ρ :=
      q.inv.naturality_assoc r.α _
    rw [h1, ← Category.assoc (H.map (DerivedCategory.Q.map r.α)), hid, Category.id_comp]
  have hβeq : HomologicalComplex.homologyMap r.β 1 ≫ k =
      q.inv.app ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
          (hypercover U)).obj G) ≫
        ((CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X) (hypercover U)
          (hypercover_mem_grothendieckTopology U) 1).app G) := by
    rw [hcc]
    exact q.inv.naturality_assoc r.β _
  have e1 : ((CechSite.cechCohomologyToCohomology.{v} (Opens.grothendieckTopology X)
        (hypercover U) (hypercover_mem_grothendieckTopology U) 1).app G)
      (q.inv.app ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
        (hypercover U)).obj G) x) = (HomologicalComplex.homologyMap r.β 1 ≫ k) x := by
    rw [hβeq]
    exact (ConcreteCategory.comp_apply _ _ x).symm
  have e2 : (HomologicalComplex.homologyMap r.β 1 ≫ k) x = y := by
    have s1 : (HomologicalComplex.homologyMap r.β 1 ≫ k) x =
        k (HomologicalComplex.homologyMap r.β 1 x) := ConcreteCategory.comp_apply _ _ x
    have s2 : k (HomologicalComplex.homologyMap r.β 1 x) =
        (HomologicalComplex.homologyMap r.α 1 ≫ k) (R.homologyπ 1 t) :=
      (congrArg (fun z ↦ k z) hx).trans (ConcreteCategory.comp_apply _ _ _).symm
    have s3 : (HomologicalComplex.homologyMap r.α 1 ≫ k) (R.homologyπ 1 t) =
        (inv (q.inv.app R ≫ H.map ρ) ≫ (q.inv.app R ≫ H.map ρ)) y := by
      rw [hα]
      refine (congrArg (fun z ↦ (q.inv.app R ≫ H.map ρ) z) ht).trans ?_
      exact (ConcreteCategory.comp_apply _ _ y).symm
    have s4 : (inv (q.inv.app R ≫ H.map ρ) ≫ (q.inv.app R ≫ H.map ρ)) y = y := by
      rw [IsIso.inv_hom_id]
      exact CategoryTheory.id_apply y
    exact s1.trans (s2.trans (s3.trans s4))
  exact ⟨U, q.inv.app ((CechSite.cechComplexIntFunctor.{v} (Opens.grothendieckTopology X)
    (hypercover U)).obj G) x, e1.trans e2⟩

end JointSurjectivity

/-! ### Stacks 09V1 -/

section Main

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v})]

open OpenCoverSet

/-- The canonical comparison from the first Čech cohomology of a topological space — the
colimit, over all open coverings, of the first Čech cohomology of the covering — to the first
sheaf cohomology of an abelian sheaf is an isomorphism. -/
@[stacks 09V1]
theorem isIso_colimitToCohomology_one
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u v}) :
    IsIso (colimitToCohomology G 1) := by
  rw [show colimitToCohomology G 1 =
    colimit.desc (cechDiagram G 1) (cechCohomologyCocone G 1) from rfl]
  refine isIso_colimit_desc_of_injective_of_jointly_surjective _ _
    exists_common_refinement (fun U ↦ ?_) (fun y ↦ ?_)
  · exact (AddCommGrpCat.mono_iff_injective _).mp (mono_cechCohomologyToCohomology_one.{v} U G)
  · exact exists_cechCohomologyToCohomology_preimage.{v} G y

end Main

end Stacks.Cohomology.CechRefinement

end
