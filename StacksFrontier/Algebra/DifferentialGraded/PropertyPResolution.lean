module

public import StacksFrontier.Algebra.DifferentialGraded.Basic
public import StacksCore.Tactic.StacksAttribute
import Mathlib.Algebra.Ring.NegOnePow
import StacksFrontier.Algebra.DifferentialGraded.NativeCover

@[expose] public section

/-!
# Resolutions of differential graded modules with property (P)

Let `R` be a commutative ring and let `(A, d)` be a differential graded `R`-algebra. A right
differential graded `A`-module `P` has *property (P)* when it carries an exhaustive increasing
filtration `0 = F_{-1} P ⊆ F_0 P ⊆ F_1 P ⊆ ⋯` by differential graded submodules whose inclusions
are admissible monomorphisms and whose graded pieces `F_{i+1} P / F_i P` are direct sums of shifts
`A[k]` of the algebra. This file shows that every differential graded module is the target of a
quasi-isomorphism from a differential graded module with property (P); such a `P` is the
differential graded analogue of a complex of projectives, and property-(P) resolutions are what
make the derived category of `(A, d)` computable.

## Main definitions

* `Stacks.DifferentialGraded.DGModule.IsQuasiIsomorphism`: a homomorphism of differential graded
  modules is a quasi-isomorphism when it is bijective on cohomology in every degree.

## Main results

* `Stacks.DifferentialGraded.DGModule.exists_propertyP_resolution`: every lawful differential
  graded module `M` over a lawful differential graded algebra `A` admits a lawful differential
  graded module `P` with property (P) together with a quasi-isomorphism `P ⟶ M`.

## Implementation notes

Being a quasi-isomorphism is expressed by the cycle-and-boundary criterion rather than by
inverting a map between cohomology objects: every cocycle of the target is congruent modulo a
boundary to the image of a cocycle of the source, and a cocycle of the source whose image is a
boundary is itself a boundary. This is equivalent to bijectivity on cohomology and avoids
constructing the cohomology modules.

The resolution is assembled from the covers of a differential graded module by a module sitting in
an admissible short exact sequence whose two ends are direct sums of shifts of `A`: iterating such
a cover on its own kernel of cocycles yields a tower `⋯ ⟶ P_1 ⟶ P_0 ⟶ M`, and `P` is the total
object `⨁_i P_i[i]` of that tower, carrying the differentials of the `P_i` together with the
telescoping horizontal map. The filtration exhibiting property (P) admits the summands of this
direct sum one at a time, and each in two steps: first the sub-object of the admissible short
exact sequence of that summand, then its quotient. Every graded piece is therefore one of the two
ends of such a sequence, hence a direct sum of shifts of `A`.

The module carrier of the resolution lives in the universe `max v w` of the algebra and the
module, because its index sets are built from the homogeneous elements of both; the cell indices
and the graded quotients of the property-(P) filtration live there for the same reason.

## References

* [The Stacks Project, Tag 09KP](https://stacks.math.columbia.edu/tag/09KP)
-/

set_option backward.isDefEq.respectTransparency false

open scoped DirectSum

namespace Stacks.DifferentialGraded.DGModule

universe u v w w'

variable {R : Type u} [CommRing R]

/-- A homomorphism of differential graded modules is a quasi-isomorphism if it induces a
bijection on cohomology in every degree. The two clauses are respectively surjectivity and
injectivity on cohomology, written directly in terms of cocycles and coboundaries. -/
def IsQuasiIsomorphism {A : DGAlgebra.{u, v} R} {M : DGModule.{u, w, v} A}
    {N : DGModule.{u, w', v} A}
    (f : DGModule.Hom M N) : Prop :=
  ∀ n : ℤ,
    (∀ y : N.carrier, y ∈ N.grading n → N.d y = 0 →
      ∃ x : M.carrier, x ∈ M.grading n ∧ M.d x = 0 ∧
        ∃ z : N.carrier, z ∈ N.grading (n - 1) ∧ N.d z = y - f.toFun x) ∧
    (∀ x : M.carrier, x ∈ M.grading n → M.d x = 0 →
      (∃ z : N.carrier, z ∈ N.grading (n - 1) ∧ N.d z = f.toFun x) →
        ∃ z : M.carrier, z ∈ M.grading (n - 1) ∧ M.d z = x)

private lemma decompose_map_addHom
    {ι κ X Y : Type*} [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup X] [AddCommGroup Y]
    (G : ι → AddSubgroup X) (H : κ → AddSubgroup Y)
    [DirectSum.Decomposition G] [DirectSum.Decomposition H]
    (e : ι ≃ κ) (f : X →+ Y)
    (hf : ∀ i x, x ∈ G i → f x ∈ H (e i)) (x : X) (i : ι) :
    (DirectSum.decompose H (f x) (e i) : Y) =
      f (DirectSum.decompose G x i) := by
  induction x using DirectSum.Decomposition.inductionOn G with
  | zero => simp
  | @homogeneous j x =>
    by_cases h : j = i
    · subst j
      rw [DirectSum.decompose_of_mem_same H (hf i x x.property),
        DirectSum.decompose_of_mem_same G x.property]
    · rw [DirectSum.decompose_of_mem_ne H (hf j x x.property) (e.injective.ne h),
        DirectSum.decompose_of_mem_ne G x.property h]
      simp
  | add x y hx hy => simp [map_add, DirectSum.decompose_add, hx, hy]

/-- A homogeneous-degree-preserving additive map killing `x` also kills each homogeneous
component of `x`. -/
private lemma map_decompose_eq_zero
    {ι X Y : Type*} [DecidableEq ι] [AddCommGroup X] [AddCommGroup Y]
    (G : ι → AddSubgroup X) (H : ι → AddSubgroup Y)
    [DirectSum.Decomposition G] [DirectSum.Decomposition H]
    (f : X →+ Y) (hf : ∀ i x, x ∈ G i → f x ∈ H i) (x : X) (hx : f x = 0) (i : ι) :
    f (DirectSum.decompose G x i) = 0 := by
  simpa [hx] using (decompose_map_addHom G H (Equiv.refl ι) f hf x i).symm

private lemma isInternal_comap_of_homogeneous
    {ι X : Type*} [DecidableEq ι] [AddCommGroup X]
    (G : ι → AddSubgroup X) [DirectSum.Decomposition G]
    (K : AddSubgroup X)
    (hK : ∀ x ∈ K, ∀ i, (DirectSum.decompose G x i : X) ∈ K) :
    DirectSum.IsInternal (fun i => (G i).comap K.subtype) := by
  classical
  let H := fun i => (G i).comap K.subtype
  let inc : ∀ i, H i →+ G i := fun i =>
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let incl := DirectSum.map inc
  have incl_apply (z : DirectSum ι (fun i => H i)) (i : ι) :
      (incl z) i = inc i (z i) := DirectSum.map_apply inc i z
  have comm (z : DirectSum ι (fun i => H i)) :
      DirectSum.coeAddMonoidHom G (incl z) =
        K.subtype (DirectSum.coeAddMonoidHom H z) := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      rw [show incl (DirectSum.of _ i x) = DirectSum.of _ i (inc i x) from
        DirectSum.map_of inc i x]
      simp only [DirectSum.coeAddMonoidHom_of]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  constructor
  · intro x y hxy
    have h : incl x = incl y := DirectSum.Decomposition.isInternal G |>.injective
      (by rw [comm, comm, hxy])
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    show (inc i (x i) : X) = (inc i (y i) : X)
    rw [← incl_apply x i, ← incl_apply y i, h]
  · intro x
    let z := DirectSum.decompose G (x : X)
    let c : ∀ i, H i := fun i => ⟨⟨z i, hK x x.property i⟩, (z i).property⟩
    refine ⟨∑ i ∈ z.support, DirectSum.of (fun i => H i) i (c i), ?_⟩
    apply Subtype.ext
    show K.subtype (DirectSum.coeAddMonoidHom H _) = (x : X)
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    exact DirectSum.sum_support_decompose G (x : X)

private lemma submodule_isLawful {A : DGAlgebra.{u, v} R}
    {M : DGModule.{u, w, v} A} (hM : M.IsLawful)
    (K : DGModule.DGSubmodule M) (hK : K.IsLawful) : K.toDGModule.IsLawful :=
  ⟨hK, fun n m x a hx ha => hM.grading_smul n m (x : K.toSubmodule).val a hx ha,
    fun n x hx => hM.d_mem n (x : K.toSubmodule).val hx,
    fun x => Subtype.ext (hM.d_comp_d (x : K.toSubmodule).val),
    fun n m x a hx ha => Subtype.ext (hM.leibniz n m (x : K.toSubmodule).val a hx ha)⟩

private def homKernel {A : DGAlgebra.{u, v} R}
    {M : DGModule.{u, w, v} A} {N : DGModule.{u, w', v} A}
    (f : DGModule.Hom M N) : DGModule.DGSubmodule M where
  toSubmodule := LinearMap.ker f.toFun
  d_stable := by
    intro x hx
    change f.toFun (M.d x) = 0
    rw [f.commute_d, show f.toFun x = 0 from hx, map_zero]

private lemma homKernel_isLawful {A : DGAlgebra.{u, v} R}
    {M : DGModule.{u, w, v} A} {N : DGModule.{u, w', v} A}
    (hM : M.IsLawful) (hN : N.IsLawful) (f : DGModule.Hom M N) :
    (homKernel f).IsLawful := by
  let := hM.isInternal.chooseDecomposition
  let := hN.isInternal.chooseDecomposition
  apply isInternal_comap_of_homogeneous M.grading (LinearMap.ker f.toFun).toAddSubgroup
  intro x hx i
  exact map_decompose_eq_zero M.grading N.grading f.toFun.toAddMonoidHom f.map_grading x hx i


private lemma homogeneous_preimage_of_surjective {A : DGAlgebra.{u, v} R}
    {M : DGModule.{u, w, v} A} {N : DGModule.{u, w', v} A}
    (hM : M.IsLawful) (hN : N.IsLawful) (f : DGModule.GradedHom M N)
    (hf : Function.Surjective f.toFun) (n : ℤ) (y : N.carrier)
    (hy : y ∈ N.grading n) :
    ∃ x : M.carrier, x ∈ M.grading n ∧ f.toFun x = y := by
  let := hM.isInternal.chooseDecomposition
  let := hN.isInternal.chooseDecomposition
  obtain ⟨x, rfl⟩ := hf y
  refine ⟨DirectSum.decompose M.grading x n,
    (DirectSum.decompose M.grading x n).property, ?_⟩
  have h := decompose_map_addHom M.grading N.grading (Equiv.refl ℤ)
    f.toFun.toAddMonoidHom f.map_grading x n
  change (DirectSum.decompose N.grading (f.toFun x) n : N.carrier) =
    f.toFun (DirectSum.decompose M.grading x n) at h
  rw [DirectSum.decompose_of_mem_same N.grading hy] at h
  exact h.symm

private lemma isQuasiIsomorphism_of_acyclic_kernel {A : DGAlgebra.{u, v} R}
    {P : DGModule.{u, w, v} A} {M : DGModule.{u, w', v} A}
    (hP : P.IsLawful) (f : DGModule.Hom P M)
    (hs : ∀ n y, y ∈ M.grading n →
      ∃ x, x ∈ P.grading n ∧ f.toFun x = y)
    (hc : ∀ n y, y ∈ M.grading n → M.d y = 0 →
      ∃ x, x ∈ P.grading n ∧ P.d x = 0 ∧ f.toFun x = y)
    (hk : ∀ n x, x ∈ P.grading n → P.d x = 0 → f.toFun x = 0 →
      ∃ z, z ∈ P.grading (n - 1) ∧ P.d z = x) : IsQuasiIsomorphism f := by
  intro n
  constructor
  · intro y hy hdy
    obtain ⟨x, hx, hdx, hfx⟩ := hc n y hy hdy
    exact ⟨x, hx, hdx, 0, (M.grading (n - 1)).zero_mem,
      by simp [hfx]⟩
  · intro x hx hdx ⟨y, hy, hdy⟩
    obtain ⟨t, ht, hft⟩ := hs (n - 1) y hy
    have hdt : P.d t ∈ P.grading n := by
      simpa using hP.d_mem (n - 1) t ht
    have hd : P.d (x - P.d t) = 0 := by
      rw [map_sub, hdx, hP.d_comp_d, sub_self]
    have hf : f.toFun (x - P.d t) = 0 := by
      rw [map_sub, f.commute_d, hft, hdy, sub_self]
    obtain ⟨z, hz, hdz⟩ := hk n (x - P.d t) ((P.grading n).sub_mem hx hdt) hd hf
    exact ⟨z + t, (P.grading (n - 1)).add_mem hz ht,
      by rw [map_add, hdz, sub_add_cancel]⟩

private lemma isInternal_comap_addEquiv {ι X Y : Type*} [DecidableEq ι]
    [AddCommGroup X] [AddCommGroup Y] (G : ι → AddSubgroup Y)
    (hG : DirectSum.IsInternal G) (e : X ≃+ Y) :
    DirectSum.IsInternal (fun i => (G i).comap e.toAddMonoidHom) := by
  let g := fun i => (G i).toIntSubmodule
  let f := e.toIntLinearEquiv.symm.toLinearMap
  have he : (fun i => ((G i).comap e.toAddMonoidHom).toIntSubmodule) =
      fun i => (g i).map f := by
    funext i
    ext x
    show e x ∈ G i ↔ ∃ y, y ∈ G i ∧ e.symm y = x
    constructor
    · intro hx; exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  show DirectSum.IsInternal
    (fun i => ((G i).comap e.toAddMonoidHom).toIntSubmodule)
  rw [he, DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  have hg : DirectSum.IsInternal g := hG
  refine ⟨f.iSupIndep_map e.symm.injective hg.submodule_iSupIndep, ?_⟩
  rw [← Submodule.map_iSup, hg.submodule_iSup_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.symm.surjective

private def uliftModule {A : DGAlgebra.{u, v} R} (M : DGModule.{u, w, v} A) :
    DGModule.{u, max v w, v} A where
  carrier := ULift.{v} M.carrier
  smul_def r x := ULift.ext (M.smul_def r x.down)
  grading n := (M.grading n).comap AddEquiv.ulift.toAddMonoidHom
  d := ULift.moduleEquiv.symm.toLinearMap.comp (M.d.comp ULift.moduleEquiv.toLinearMap)

private lemma uliftModule_isLawful {A : DGAlgebra.{u, v} R}
    {M : DGModule.{u, w, v} A} (hM : M.IsLawful) : (uliftModule M).IsLawful where
  isInternal := isInternal_comap_addEquiv M.grading hM.isInternal AddEquiv.ulift
  grading_smul n m x a hx ha := hM.grading_smul n m x.down a hx ha
  d_mem n x hx := hM.d_mem n x.down hx
  d_comp_d x := ULift.ext (hM.d_comp_d x.down)
  leibniz n m x a hx ha := ULift.ext (hM.leibniz n m x.down a hx ha)

private def uliftHom {A : DGAlgebra.{u, v} R} (M : DGModule.{u, w, v} A) :
    DGModule.Hom (uliftModule M) M where
  toFun := ULift.moduleEquiv.toLinearMap
  map_grading _ _ hx := hx
  commute_d _ := rfl


private lemma directSumGrading_isInternal {A : DGAlgebra.{u, v} R}
    {ι : Type*} (N : ι → DGModule.{u, w, v} A)
    (hN : ∀ i, DirectSum.IsInternal (N i).grading) :
    DirectSum.IsInternal (DGModule.directSumGrading N) := by
  classical
  show Function.Bijective (DirectSum.coeAddMonoidHom (DGModule.directSumGrading N))
  have hbij : ∀ i, Function.Bijective (DirectSum.coeAddMonoidHom (N i).grading) :=
    fun i => hN i
  let pdeg : ∀ (i : ι) (n : ℤ), ↥(DGModule.directSumGrading N n) →+ ↥((N i).grading n) := fun i n =>
    { toFun := fun w => ⟨(w : ⨁ j, (N j).carrier) i, w.2 i⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by intro a b; apply Subtype.ext; simp }
  let proj : ∀ i, (⨁ n, ↥(DGModule.directSumGrading N n)) →+ (⨁ n, ↥((N i).grading n)) := fun i =>
    DirectSum.map (fun n => pdeg i n)
  have proj_of : ∀ i n (w : ↥(DGModule.directSumGrading N n)),
      proj i ((DirectSum.of (fun n => ↥(DGModule.directSumGrading N n)) n) w)
        = (DirectSum.of (fun n => ↥((N i).grading n)) n) (pdeg i n w) :=
    fun i n w => DirectSum.map_of (fun n => pdeg i n) n w
  have bridge : ∀ (i : ι) (z : ⨁ n, ↥(DGModule.directSumGrading N n)),
      (DirectSum.coeAddMonoidHom (DGModule.directSumGrading N) z : ⨁ j, (N j).carrier) i
        = DirectSum.coeAddMonoidHom (N i).grading (proj i z) := by
    intro i z
    induction z using DirectSum.induction_on with
    | zero => simp
    | of n w =>
        rw [DirectSum.coeAddMonoidHom_of, proj_of, DirectSum.coeAddMonoidHom_of]
        rfl
    | add a b ha hb =>
        simp only [map_add, DirectSum.add_apply, ha, hb]
  have proj_apply : ∀ i (z : ⨁ n, ↥(DGModule.directSumGrading N n)) (n : ℤ),
      (proj i z) n = pdeg i n (z n) := by
    intro i z n
    exact DirectSum.map_apply (fun n => pdeg i n) n z
  constructor
  · -- injective
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hpz : ∀ i, proj i z = 0 := by
      intro i
      apply (hbij i).injective
      rw [← bridge i z, hz]
      simp
    apply DirectSum.ext (fun n => ?_)
    apply Subtype.ext
    apply DirectSum.ext (fun i => ?_)
    have hcomp : (pdeg i n (z n) : ↥((N i).grading n)) = (0 : ↥((N i).grading n)) := by
      rw [← proj_apply i z n, hpz i]; simp
    have hval : ((z n : ↥(DGModule.directSumGrading N n)) : ⨁ j, (N j).carrier) i = 0 := by
      show ((pdeg i n (z n) : ↥((N i).grading n)) : (N i).carrier) = 0
      rw [hcomp]; simp
    rw [hval]; simp
  · -- surjective
    intro m
    induction m using DirectSum.induction_on with
    | zero => exact ⟨0, by simp⟩
    | of j a =>
        obtain ⟨u, hu⟩ := (hbij j).surjective a
        let embj : ∀ (n : ℤ), ↥((N j).grading n) →+ ↥(DGModule.directSumGrading N n) := fun n =>
          { toFun := fun c => ⟨(DirectSum.of (fun k => (N k).carrier) j (c : (N j).carrier)),
              by
                intro k
                by_cases hjk : j = k
                · subst hjk; rw [DirectSum.of_eq_same]; exact c.2
                · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk)]; exact AddSubgroup.zero_mem _⟩
            map_zero' := by apply Subtype.ext; simp
            map_add' := by
              intro c d; apply Subtype.ext
              show (DirectSum.of (fun k => (N k).carrier) j) ((c : (N j).carrier) + d) = _
              rw [map_add]; rfl }
        let Z : (⨁ n, ↥((N j).grading n)) →+ (⨁ n, ↥(DGModule.directSumGrading N n)) :=
          DirectSum.map embj
        refine ⟨Z u, ?_⟩
        have key : ∀ v : ⨁ n, ↥((N j).grading n),
            DirectSum.coeAddMonoidHom (DGModule.directSumGrading N) (Z v)
            = (DirectSum.of (fun k => (N k).carrier) j)
                (DirectSum.coeAddMonoidHom (N j).grading v) := by
          intro v
          induction v using DirectSum.induction_on with
          | zero => simp
          | of n c =>
              rw [show Z ((DirectSum.of (fun n => ↥((N j).grading n)) n) c)
                    = (DirectSum.of (fun n => ↥(DGModule.directSumGrading N n)) n) (embj n c) from
                  DirectSum.map_of embj n c,
                DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
              rfl
          | add a b ha hb =>
              rw [map_add, map_add, ha, hb, map_add, ← map_add]
        rw [key u, hu]
    | add a b ha hb =>
        obtain ⟨za, hza⟩ := ha
        obtain ⟨zb, hzb⟩ := hb
        exact ⟨za + zb, by rw [map_add, hza, hzb]⟩

private structure FreeExtension {A : DGAlgebra.{u, v} R}
    (P : DGModule.{u, w, v} A) where
  left : DGModule.{u, w, v} A
  right : DGModule.{u, w, v} A
  left_lawful : left.IsLawful
  right_lawful : right.IsLawful
  incl : DGModule.Hom left P
  proj : DGModule.Hom P right
  exact : DGModule.AdmissibleSES incl proj
  leftIndex : Type w
  rightIndex : Type w
  leftDec : DecidableEq leftIndex
  rightDec : DecidableEq rightIndex
  leftShift : leftIndex → ℤ
  rightShift : rightIndex → ℤ
  leftIso : DGModule.Iso left (@DGModule.directSum _ _ _ leftIndex leftDec
    (fun j => DGModule.shiftFree A (leftShift j)))
  rightIso : DGModule.Iso right (@DGModule.directSum _ _ _ rightIndex rightDec
    (fun j => DGModule.shiftFree A (rightShift j)))

private structure Cover {A : DGAlgebra.{u, v} R} (M : DGModule.{u, w, v} A) where
  obj : DGModule.{u, max v w, v} A
  lawful : obj.IsLawful
  map : DGModule.Hom obj M
  surjective : Function.Surjective map.toFun
  degreewise : ∀ n y, y ∈ M.grading n → ∃ x, x ∈ obj.grading n ∧ map.toFun x = y
  cocycles : ∀ n y, y ∈ M.grading n → M.d y = 0 →
    ∃ x, x ∈ obj.grading n ∧ obj.d x = 0 ∧ map.toFun x = y
  pieces : FreeExtension obj

private lemma nonempty_cover {A : DGAlgebra.{u, v} R} (hA : A.IsLawful)
    {M : DGModule.{u, w, v} A} (hM : M.IsLawful) : Nonempty (Cover M) := by
  obtain ⟨P, hP, f, hs, hg, hc, L, Q, hL, hQ, i, p, I, J, dI, dJ, kI, kJ,
    eI, eJ, he⟩ := DifferentialGraded.NativeCover.exists_native_cover A hA M hM
  exact ⟨⟨P, hP, f, hs, hg, hc,
    ⟨L, Q, hL, hQ, i, p, he, I, J, dI, dJ, kI, kJ, eI, eJ⟩⟩⟩

private noncomputable def cover {A : DGAlgebra.{u, v} R} (hA : A.IsLawful)
    {M : DGModule.{u, w, v} A} (hM : M.IsLawful) : Cover M :=
  (nonempty_cover hA hM).some

private noncomputable def syzygy {A : DGAlgebra.{u, v} R} (hA : A.IsLawful)
    {M : DGModule.{u, w, v} A} (hM : M.IsLawful) :
    ℕ → {N : DGModule.{u, max v w, v} A // N.IsLawful}
  | 0 => ⟨uliftModule M, uliftModule_isLawful hM⟩
  | n + 1 =>
    let K := syzygy hA hM n
    let C := cover hA K.property
    ⟨(homKernel C.map).toDGModule,
      submodule_isLawful C.lawful _ (homKernel_isLawful C.lawful K.property C.map)⟩

private noncomputable abbrev resolutionCover {A : DGAlgebra.{u, v} R}
    (hA : A.IsLawful) {M : DGModule.{u, w, v} A} (hM : M.IsLawful) (n : ℕ) :=
  cover hA (syzygy hA hM n).property

private noncomputable def resolutionMap {A : DGAlgebra.{u, v} R}
    (hA : A.IsLawful) {M : DGModule.{u, w, v} A} (hM : M.IsLawful) (n : ℕ) :
    DGModule.Hom (resolutionCover hA hM (n + 1)).obj (resolutionCover hA hM n).obj :=
  (homKernel (resolutionCover hA hM n).map).incl.comp
    (resolutionCover hA hM (n + 1)).map

private lemma resolutionMap_comp {A : DGAlgebra.{u, v} R}
    (hA : A.IsLawful) {M : DGModule.{u, w, v} A} (hM : M.IsLawful)
    (n : ℕ) (x : (resolutionCover hA hM (n + 2)).obj.carrier) :
    (resolutionMap hA hM n).toFun ((resolutionMap hA hM (n + 1)).toFun x) = 0 := by
  show (((resolutionCover hA hM (n + 1)).map.toFun
    ((resolutionCover hA hM (n + 2)).map.toFun x).val).val) = 0
  have h := ((resolutionCover hA hM (n + 2)).map.toFun x).property
  exact congrArg Subtype.val h

private lemma resolutionMap_exact {A : DGAlgebra.{u, v} R}
    (hA : A.IsLawful) {M : DGModule.{u, w, v} A} (hM : M.IsLawful)
    (i : ℕ) (n : ℤ) (x : (resolutionCover hA hM (i + 1)).obj.carrier)
    (hx : x ∈ (resolutionCover hA hM (i + 1)).obj.grading n)
    (hf : (resolutionMap hA hM i).toFun x = 0) :
    ∃ y, y ∈ (resolutionCover hA hM (i + 2)).obj.grading n ∧
      (resolutionMap hA hM (i + 1)).toFun y = x := by
  have hxk : x ∈ (homKernel (resolutionCover hA hM (i + 1)).map).toSubmodule := Subtype.ext hf
  obtain ⟨y, hy, he⟩ := (resolutionCover hA hM (i + 2)).degreewise n ⟨x, hxk⟩ hx
  exact ⟨y, hy, congrArg Subtype.val he⟩

private lemma resolutionMap_exact_cocycles {A : DGAlgebra.{u, v} R}
    (hA : A.IsLawful) {M : DGModule.{u, w, v} A} (hM : M.IsLawful)
    (i : ℕ) (n : ℤ) (x : (resolutionCover hA hM (i + 1)).obj.carrier)
    (hx : x ∈ (resolutionCover hA hM (i + 1)).obj.grading n)
    (hd : (resolutionCover hA hM (i + 1)).obj.d x = 0)
    (hf : (resolutionMap hA hM i).toFun x = 0) :
    ∃ y, y ∈ (resolutionCover hA hM (i + 2)).obj.grading n ∧
      (resolutionCover hA hM (i + 2)).obj.d y = 0 ∧
      (resolutionMap hA hM (i + 1)).toFun y = x := by
  have hxk : x ∈ (homKernel (resolutionCover hA hM (i + 1)).map).toSubmodule := Subtype.ext hf
  obtain ⟨y, hy, hdy, he⟩ :=
    (resolutionCover hA hM (i + 2)).cocycles n ⟨x, hxk⟩ hx (Subtype.ext hd)
  exact ⟨y, hy, hdy, congrArg Subtype.val he⟩

private lemma shift_isLawful {A : DGAlgebra.{u, v} R} (hA : A.IsLawful)
    {M : DGModule.{u, w, v} A} (hM : M.IsLawful) (k : ℤ) :
    (M.shift k).IsLawful := by
  rw [← DifferentialGraded.NativeCover.Native.ofModule_module M hA hM,
    ← DifferentialGraded.NativeCover.Native.ofModule_shift]
  exact DifferentialGraded.NativeCover.Native.ofModule_isLawful _

private def linearMapRestrictR {A : DGAlgebra.{u, v} R}
    {M : DGModule.{u, w, v} A} {N : DGModule.{u, w', v} A}
    (f : M.carrier →ₗ[A.carrierᵐᵒᵖ] N.carrier) : M.carrier →ₗ[R] N.carrier where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    rw [M.smul_def, N.smul_def, map_smul]
    rfl

private noncomputable abbrev shiftedSum {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) :=
  DGModule.directSum (fun i => (P i).shift (i : ℤ))

private noncomputable def horizontal {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i)) :
    (⨁ i, (P i).carrier) →ₗ[A.carrierᵐᵒᵖ] (⨁ i, (P i).carrier) :=
  DirectSum.toModule _ ℕ _ (fun i => match i with
    | 0 => 0
    | n + 1 => (DirectSum.lof _ ℕ (fun j => (P j).carrier) n).comp (f n).toFun)

private lemma horizontal_apply {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (x : ⨁ i, (P i).carrier) (i : ℕ) :
    (horizontal P f x) i = (f i).toFun (x (i + 1)) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    cases j with
    | zero =>
      have h : horizontal P f (DirectSum.of _ 0 x) = 0 :=
        DirectSum.toModule_lof (R := A.carrierᵐᵒᵖ) (M := fun j => (P j).carrier) 0 x
      rw [h, DirectSum.of_eq_of_ne _ _ _ (by omega)]
      simp
    | succ j =>
      have h : horizontal P f (DirectSum.of _ (j + 1) x) =
          DirectSum.of _ j ((f j).toFun x) :=
        DirectSum.toModule_lof (R := A.carrierᵐᵒᵖ) (M := fun j => (P j).carrier) (j + 1) x
      rw [h]
      by_cases h : j = i
      · subst j; simp
      · simp [DirectSum.of_eq_of_ne, Ne.symm h]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]

private noncomputable def totalDifferential {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i)) :
    (⨁ i, (P i).carrier) →ₗ[R] (⨁ i, (P i).carrier) :=
  let v : (⨁ i, (P i).carrier) →ₗ[R] (⨁ i, (P i).carrier) :=
    DGModule.directSumD (fun i => (P i).shift (i : ℤ))
  let h : (⨁ i, (P i).carrier) →ₗ[R] (⨁ i, (P i).carrier) :=
    linearMapRestrictR (M := shiftedSum P) (N := shiftedSum P) (horizontal P f)
  v + h

private noncomputable def totalModule {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i)) :
    DGModule.{u, w, v} A :=
  { shiftedSum P with d := totalDifferential P f }

private lemma totalModule_d_apply {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (x : ⨁ i, (P i).carrier) (i : ℕ) :
    (totalDifferential P f x) i = (-1 : ℤ) ^ i • (P i).d (x i) +
      (f i).toFun (x (i + 1)) := by
  let y : ⨁ i, (P i).carrier := DGModule.directSumD (fun i => (P i).shift (i : ℤ)) x
  show (y + horizontal P f x) i = _
  rw [DirectSum.add_apply, horizontal_apply]
  have hy : y i = ((P i).shift (i : ℤ)).d (x i) :=
    DifferentialGraded.NativeCover.Native.directSum_d_apply (fun i => (P i).shift (i : ℤ)) x i
  rw [hy]
  simp only [DGModule.shift, LinearMap.smul_apply, Int.natAbs_natCast]

private lemma totalModule_isLawful {A : DGAlgebra.{u, v} R} (hA : A.IsLawful)
    (P : ℕ → DGModule.{u, w, v} A) (hP : ∀ i, (P i).IsLawful)
    (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (hf : ∀ i x, (f i).toFun ((f (i + 1)).toFun x) = 0) :
    (totalModule P f).IsLawful := by
  refine ⟨directSumGrading_isInternal _ (fun i => (shift_isLawful hA (hP i) i).isInternal),
    ?_, ?_, ?_, ?_⟩
  · intro n m x a hx ha i
    let x : ⨁ i, (P i).carrier := x
    show (MulOpposite.op a • x) i ∈ (P i).grading (n + m + (i : ℤ))
    rw [DirectSum.smul_apply]
    simpa [add_right_comm] using (hP i).grading_smul (n + i) m (x i) a (hx i) ha
  · intro n x hx i
    let x : ⨁ i, (P i).carrier := x
    change ∀ j, x j ∈ (P j).grading (n + j) at hx
    show (totalDifferential P f x) i ∈ (P i).grading (n + 1 + (i : ℤ))
    rw [totalModule_d_apply]
    apply add_mem
    · simpa [add_right_comm] using
        (P i).grading (n + (i : ℤ) + 1) |>.zsmul_mem ((hP i).d_mem _ _ (hx i)) ((-1 : ℤ) ^ i)
    · simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (f i).map_grading _ _ (hx (i + 1))
  · intro x
    show totalDifferential P f (totalDifferential P f x) = 0
    apply DirectSum.ext
    intro i
    rw [totalModule_d_apply, totalModule_d_apply, totalModule_d_apply]
    simp only [map_add, map_zsmul, (hP i).d_comp_d, smul_zero, zero_add,
      hf, add_zero, pow_succ, mul_neg_one, neg_smul]
    simp only [map_neg, map_zsmul, (f i).commute_d, add_neg_cancel]
    rfl
  · intro n m x a hx ha
    let x : ⨁ i, (P i).carrier := x
    show totalDifferential P f (MulOpposite.op a • x) =
      MulOpposite.op a • totalDifferential P f x +
        (-1 : ℤ) ^ n.natAbs • (MulOpposite.op (A.d a) • x)
    apply DirectSum.ext
    intro i
    simp only [DirectSum.add_apply, DirectSum.smul_apply, totalModule_d_apply,
      map_smul]
    have hl := (shift_isLawful hA (hP i) (i : ℤ)).leibniz n m (x i) a (hx i) ha
    change (-1 : ℤ) ^ (i : ℤ).natAbs • (P i).d (MulOpposite.op a • x i) =
      MulOpposite.op a • ((-1 : ℤ) ^ (i : ℤ).natAbs • (P i).d (x i)) +
        (-1 : ℤ) ^ n.natAbs • (MulOpposite.op (A.d a) • x i) at hl
    simp only [Int.natAbs_natCast] at hl
    rw [hl]
    simp only [smul_add]
    abel

private lemma total_of_mem {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (i : ℕ) (n : ℤ) (x : (P i).carrier) (hx : x ∈ (P i).grading (n + i)) :
    DirectSum.of (fun i => (P i).carrier) i x ∈ (totalModule P f).grading n := by
  intro j
  by_cases h : j = i
  · subst j
    show (DirectSum.of (fun i => (P i).carrier) i x) i ∈ (P i).grading (n + i)
    rw [DirectSum.of_eq_same]
    exact hx
  · show (DirectSum.of (fun i => (P i).carrier) i x) j ∈ (P j).grading (n + j)
    rw [DirectSum.of_eq_of_ne _ _ _ h]
    exact zero_mem _

private lemma totalDifferential_of_zero {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (x : (P 0).carrier) :
    totalDifferential P f (DirectSum.of _ 0 x) = DirectSum.of _ 0 ((P 0).d x) := by
  apply DirectSum.ext
  intro i
  rw [totalModule_d_apply]
  cases i with
  | zero => simp [DirectSum.of_eq_of_ne]
  | succ i => simp [DirectSum.of_eq_of_ne]

private lemma totalDifferential_of_succ {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (i : ℕ) (x : (P (i + 1)).carrier) :
    totalDifferential P f (DirectSum.of _ (i + 1) x) =
      DirectSum.of _ (i + 1) ((-1 : ℤ) ^ (i + 1) • (P (i + 1)).d x) +
        DirectSum.of _ i ((f i).toFun x) := by
  apply DirectSum.ext
  intro j
  rw [totalModule_d_apply, DirectSum.add_apply]
  by_cases h : j = i
  · subst j
    simp (disch := omega) only [DirectSum.of_eq_same, DirectSum.of_eq_of_ne,
      map_zero, smul_zero, zero_add]
  · by_cases h' : j = i + 1
    · subst j
      simp (disch := omega) only [DirectSum.of_eq_same, DirectSum.of_eq_of_ne,
        map_zero, add_zero]
    · simp (disch := omega) only [DirectSum.of_eq_of_ne, map_zero, smul_zero, add_zero]

private noncomputable def totalAugmentation {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    {M : DGModule.{u, w', v} A} (e : DGModule.Hom (P 0) M)
    (he : ∀ x, e.toFun ((f 0).toFun x) = 0) : DGModule.Hom (totalModule P f) M where
  toFun := e.toFun.comp (DirectSum.component A.carrierᵐᵒᵖ ℕ (fun i => (P i).carrier) 0)
  map_grading n x hx := by
    let x : ⨁ i, (P i).carrier := x
    apply e.map_grading n
    change x 0 ∈ (P 0).grading n
    have h := hx 0
    change x 0 ∈ (P 0).grading (n + (0 : ℤ)) at h
    simpa only [add_zero] using h
  commute_d x := by
    let x : ⨁ i, (P i).carrier := x
    change e.toFun ((totalDifferential P f x) 0) = M.d (e.toFun (x 0))
    rw [totalModule_d_apply]
    simp only [pow_zero, one_smul, map_add, he, add_zero, e.commute_d]

private lemma totalAugmentation_surjective_degreewise {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    {M : DGModule.{u, w', v} A} (e : DGModule.Hom (P 0) M)
    (he : ∀ x, e.toFun ((f 0).toFun x) = 0)
    (hs : ∀ n y, y ∈ M.grading n → ∃ x, x ∈ (P 0).grading n ∧ e.toFun x = y)
    (n : ℤ) (y : M.carrier) (hy : y ∈ M.grading n) :
    ∃ x, x ∈ (totalModule P f).grading n ∧
      (totalAugmentation P f e he).toFun x = y := by
  obtain ⟨x, hx, hxy⟩ := hs n y hy
  refine ⟨DirectSum.of _ 0 x, total_of_mem P f 0 n x (by simpa using hx), ?_⟩
  exact hxy

private lemma totalAugmentation_surjective_cocycles {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    {M : DGModule.{u, w', v} A} (e : DGModule.Hom (P 0) M)
    (he : ∀ x, e.toFun ((f 0).toFun x) = 0)
    (hs : ∀ n y, y ∈ M.grading n → M.d y = 0 →
      ∃ x, x ∈ (P 0).grading n ∧ (P 0).d x = 0 ∧ e.toFun x = y)
    (n : ℤ) (y : M.carrier) (hy : y ∈ M.grading n) (hd : M.d y = 0) :
    ∃ x, x ∈ (totalModule P f).grading n ∧ (totalModule P f).d x = 0 ∧
      (totalAugmentation P f e he).toFun x = y := by
  obtain ⟨x, hx, hdx, hxy⟩ := hs n y hy hd
  refine ⟨DirectSum.of _ 0 x, total_of_mem P f 0 n x (by simpa using hx), ?_, ?_⟩
  · show totalDifferential P f (DirectSum.of _ 0 x) = 0
    rw [totalDifferential_of_zero, hdx, map_zero]
  · exact hxy

private lemma neg_one_pow_smul_eq_zero {X : Type*} [AddCommGroup X] (k : ℕ) (x : X) :
    ((-1 : ℤ) ^ k • x = 0) ↔ x = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simpa only [pow_succ, mul_neg_one, neg_smul, neg_eq_zero] using ih

/-- A finitely supported family vanishes in every index above the supremum of its support. -/
private lemma apply_eq_zero_of_support_sup_lt {X : ℕ → Type*} [∀ i, AddCommMonoid (X i)]
    [∀ (i : ℕ) (a : X i), Decidable (a ≠ 0)] (x : ⨁ i, X i) (j : ℕ)
    (hj : x.support.sup id < j) : x j = 0 := by
  apply DFinsupp.notMem_support_iff.mp
  intro h
  exact absurd (Finset.le_sup (f := id) h) (not_le.mpr hj)

private lemma total_cycle_boundary_of_bounds {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (hT : (totalModule P f).IsLawful)
    (hr : ∀ i n x, x ∈ (P (i + 1)).grading n → (f i).toFun x = 0 →
      ∃ y, y ∈ (P (i + 2)).grading n ∧ (f (i + 1)).toFun y = x)
    (hc : ∀ i n x, x ∈ (P i).grading n → (P i).d x = 0 →
      (∃ y, (f i).toFun y = x) →
      ∃ y, y ∈ (P (i + 1)).grading n ∧ (P (i + 1)).d y = 0 ∧ (f i).toFun y = x)
    (k : ℕ) :
    ∀ (b : ℕ) (n : ℤ) (x : ⨁ i, (P i).carrier),
      x ∈ (totalModule P f).grading n → totalDifferential P f x = 0 →
      (∀ j, j < b ∨ b + k < j → x j = 0) →
      (∃ y, y ∈ (P (b + 1)).grading (n + b) ∧ (f b).toFun y = x b) →
      ∃ z : ⨁ i, (P i).carrier,
        z ∈ (totalModule P f).grading (n - 1) ∧ totalDifferential P f z = x := by
  induction k with
  | zero =>
    intro b n x hx hd hs ⟨y, _, hy⟩
    have hb : (P b).d (x b) = 0 := by
      have h := congrArg (fun z : ⨁ i, (P i).carrier => z b) hd
      rw [totalModule_d_apply, hs (b + 1) (Or.inr (by omega)), map_zero, add_zero] at h
      exact (neg_one_pow_smul_eq_zero b _).mp h
    obtain ⟨y, hyg, hyd, hy⟩ := hc b (n + b) (x b) (hx b) hb ⟨y, hy⟩
    refine ⟨DirectSum.of (fun i => (P i).carrier) (b + 1) y,
      total_of_mem P f (b + 1) (n - 1) y (by
        rw [show n - 1 + ((b + 1 : ℕ) : ℤ) = n + b by omega]
        exact hyg), ?_⟩
    rw [totalDifferential_of_succ, hyd, smul_zero, map_zero, zero_add, hy]
    apply DirectSum.ext
    intro j
    by_cases h : j = b
    · subst j; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ h, hs j (by omega)]
  | succ k ih =>
    intro b n x hx hd hs ⟨y, hyg, hy⟩
    let t : ⨁ i, (P i).carrier := DirectSum.of (fun i => (P i).carrier) (b + 1) y
    have ht : t ∈ (totalModule P f).grading (n - 1) :=
      total_of_mem P f (b + 1) (n - 1) y (by
        rw [show n - 1 + ((b + 1 : ℕ) : ℤ) = n + b by omega]
        exact hyg)
    have hdt : totalDifferential P f t =
        DirectSum.of (fun i => (P i).carrier) (b + 1) ((-1 : ℤ) ^ (b + 1) • (P (b + 1)).d y) +
          DirectSum.of (fun i => (P i).carrier) b (x b) := by
      rw [totalDifferential_of_succ, hy]
    let z := x - totalDifferential P f t
    have hz : z ∈ (totalModule P f).grading n := by
      apply sub_mem hx
      have h : totalDifferential P f t ∈ (totalModule P f).grading (n - 1 + 1) :=
        hT.d_mem (n - 1) t ht
      simpa only [sub_add_cancel] using h
    have hzd : totalDifferential P f z = 0 := by
      show totalDifferential P f (x - totalDifferential P f t) = 0
      rw [map_sub, hd, show totalDifferential P f (totalDifferential P f t) = 0 from
        hT.d_comp_d t, sub_self]
    have hzs : ∀ j, j < b + 1 ∨ b + 1 + k < j → z j = 0 := by
      intro j hj
      show (x - totalDifferential P f t) j = 0
      rw [hdt, DirectSum.sub_apply, DirectSum.add_apply]
      by_cases h : j = b
      · subst j
        simp (disch := omega) only [DirectSum.of_eq_of_ne, DirectSum.of_eq_same,
          zero_add, sub_self]
      · have h' : j ≠ b + 1 := by omega
        rw [DirectSum.of_eq_of_ne _ _ _ h', DirectSum.of_eq_of_ne _ _ _ h,
          hs j (by omega)]
        simp
    have hker : (f b).toFun (z (b + 1)) = 0 := by
      have h := congrArg (fun z : ⨁ i, (P i).carrier => z b) hzd
      rw [totalModule_d_apply, hzs b (Or.inl (by omega)), map_zero, smul_zero,
        zero_add] at h
      exact h
    obtain ⟨q, hq, hqz⟩ := hr b (n + (b + 1)) (z (b + 1)) (hz (b + 1)) hker
    obtain ⟨v, hv, hvz⟩ := ih (b + 1) n z hz hzd hzs ⟨q, hq, hqz⟩
    exact ⟨v + t, add_mem hv ht, by rw [map_add, hvz]; exact sub_add_cancel _ _⟩

private lemma totalAugmentation_isQuasiIsomorphism {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (hT : (totalModule P f).IsLawful)
    {M : DGModule.{u, w', v} A} (e : DGModule.Hom (P 0) M)
    (he : ∀ x, e.toFun ((f 0).toFun x) = 0)
    (hs : ∀ n y, y ∈ M.grading n → ∃ x, x ∈ (P 0).grading n ∧ e.toFun x = y)
    (hsc : ∀ n y, y ∈ M.grading n → M.d y = 0 →
      ∃ x, x ∈ (P 0).grading n ∧ (P 0).d x = 0 ∧ e.toFun x = y)
    (hz : ∀ n x, x ∈ (P 0).grading n → e.toFun x = 0 →
      ∃ y, y ∈ (P 1).grading n ∧ (f 0).toFun y = x)
    (hr : ∀ i n x, x ∈ (P (i + 1)).grading n → (f i).toFun x = 0 →
      ∃ y, y ∈ (P (i + 2)).grading n ∧ (f (i + 1)).toFun y = x)
    (hc : ∀ i n x, x ∈ (P i).grading n → (P i).d x = 0 →
      (∃ y, (f i).toFun y = x) →
      ∃ y, y ∈ (P (i + 1)).grading n ∧ (P (i + 1)).d y = 0 ∧ (f i).toFun y = x) :
    IsQuasiIsomorphism (totalAugmentation P f e he) := by
  classical
  apply isQuasiIsomorphism_of_acyclic_kernel hT _
    (totalAugmentation_surjective_degreewise P f e he hs)
    (totalAugmentation_surjective_cocycles P f e he hsc)
  show ∀ n (x : ⨁ i, (P i).carrier), x ∈ (totalModule P f).grading n →
    totalDifferential P f x = 0 → e.toFun (x 0) = 0 →
      ∃ z : ⨁ i, (P i).carrier, z ∈ (totalModule P f).grading (n - 1) ∧
        totalDifferential P f z = x
  intro n x hx hd he
  apply total_cycle_boundary_of_bounds P f hT hr hc (x.support.sup id) 0 n x hx hd
  · exact fun j hj => apply_eq_zero_of_support_sup_lt x j (by omega)
  · obtain ⟨y, hy, hyx⟩ := hz n (x 0)
      (by simpa only [DGModule.shift, Nat.cast_zero, add_zero] using hx 0) he
    exact ⟨y, by simpa only [Nat.cast_zero, add_zero] using hy, hyx⟩

private lemma resolutionMap_lift_cocycles {A : DGAlgebra.{u, v} R}
    (hA : A.IsLawful) {M : DGModule.{u, w, v} A} (hM : M.IsLawful)
    (i : ℕ) (n : ℤ) (x : (resolutionCover hA hM i).obj.carrier)
    (hx : x ∈ (resolutionCover hA hM i).obj.grading n)
    (hd : (resolutionCover hA hM i).obj.d x = 0)
    (hi : ∃ y, (resolutionMap hA hM i).toFun y = x) :
    ∃ y, y ∈ (resolutionCover hA hM (i + 1)).obj.grading n ∧
      (resolutionCover hA hM (i + 1)).obj.d y = 0 ∧
      (resolutionMap hA hM i).toFun y = x := by
  obtain ⟨y, rfl⟩ := hi
  obtain ⟨z, hz, hdz, he⟩ := (resolutionCover hA hM (i + 1)).cocycles n
    ((resolutionCover hA hM (i + 1)).map.toFun y) hx (Subtype.ext hd)
  exact ⟨z, hz, hdz, congrArg Subtype.val he⟩

private lemma resolution_total_isQuasiIsomorphism {A : DGAlgebra.{u, v} R}
    (hA : A.IsLawful) {M : DGModule.{u, w, v} A} (hM : M.IsLawful) :
    ∃ e : DGModule.Hom
      (totalModule (fun i => (resolutionCover hA hM i).obj) (resolutionMap hA hM)) M,
      IsQuasiIsomorphism e := by
  let P := fun i => (resolutionCover hA hM i).obj
  let f := resolutionMap hA hM
  let e : DGModule.Hom (P 0) M := (uliftHom M).comp (resolutionCover hA hM 0).map
  have he : ∀ x, e.toFun ((f 0).toFun x) = 0 := fun x =>
    congrArg ULift.down ((resolutionCover hA hM 1).map.toFun x).property
  refine ⟨totalAugmentation P f e he, ?_⟩
  apply totalAugmentation_isQuasiIsomorphism P f
    (totalModule_isLawful hA P (fun i => (resolutionCover hA hM i).lawful)
      f (resolutionMap_comp hA hM)) e he
  · intro n y hy
    obtain ⟨x, hx, hxy⟩ := (resolutionCover hA hM 0).degreewise n (ULift.up y) hy
    exact ⟨x, hx, congrArg ULift.down hxy⟩
  · intro n y hy hd
    obtain ⟨x, hx, hdx, hxy⟩ := (resolutionCover hA hM 0).cocycles n
      (ULift.up y) hy (ULift.ext hd)
    exact ⟨x, hx, hdx, congrArg ULift.down hxy⟩
  · intro n x hx hfx
    have hk : x ∈ (homKernel (resolutionCover hA hM 0).map).toSubmodule :=
      ULift.ext hfx
    obtain ⟨y, hy, hyx⟩ := (resolutionCover hA hM 1).degreewise n ⟨x, hk⟩ hx
    exact ⟨y, hy, congrArg Subtype.val hyx⟩
  · exact resolutionMap_exact hA hM
  · exact resolutionMap_lift_cocycles hA hM

private def filtrationSubmodule {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (E : ∀ i, FreeExtension (P i)) (t : ℕ) :
    Submodule A.carrierᵐᵒᵖ (⨁ i, (P i).carrier) where
  carrier := {x | (∀ j, t < 2 * j → x j = 0) ∧
    ∀ j, t = 2 * j → (E j).proj.toFun (x j) = 0}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    constructor
    · intro j hj; simp only [DirectSum.add_apply, hx j hj, hy j hj, add_zero]
    · intro j hj; simp only [DirectSum.add_apply, map_add, hx' j hj, hy' j hj, add_zero]
  smul_mem' := by
    rintro a x ⟨hx, hx'⟩
    constructor
    · intro j hj; simp only [DirectSum.smul_apply, hx j hj, smul_zero]
    · intro j hj; simp only [DirectSum.smul_apply, map_smul, hx' j hj, smul_zero]

private noncomputable def totalFiltrationStep {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t : ℕ) : DGModule.DGSubmodule (totalModule P f) where
  toSubmodule := filtrationSubmodule P E t
  d_stable := by
    rintro x ⟨hx, hx'⟩
    constructor
    · intro j hj
      change (totalDifferential P f x) j = 0
      rw [totalModule_d_apply, hx j hj, hx (j + 1) (by omega), map_zero, map_zero,
        smul_zero, add_zero]
    · intro j hj
      change (E j).proj.toFun ((totalDifferential P f x) j) = 0
      rw [totalModule_d_apply, map_add, map_zsmul, (E j).proj.commute_d, hx' j hj,
        hx (j + 1) (by omega), map_zero, map_zero, map_zero, smul_zero, add_zero]

private lemma totalFiltrationStep_mono {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t : ℕ) :
    (totalFiltrationStep P f E t).toSubmodule ≤
      (totalFiltrationStep P f E (t + 1)).toSubmodule := by
  rintro x ⟨hx, hx'⟩
  refine ⟨fun j hj => hx j (by omega), ?_⟩
  intro j hj
  rw [hx j (by omega), map_zero]

private lemma totalFiltrationStep_exhaustive {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (x : ⨁ i, (P i).carrier) :
    ∃ t, x ∈ (totalFiltrationStep P f E t).toSubmodule := by
  classical
  refine ⟨2 * x.support.sup id + 1, ?_, ?_⟩
  · exact fun j hj => apply_eq_zero_of_support_sup_lt x j (by omega)
  · intro j hj
    omega

private lemma totalFiltrationStep_isLawful {A : DGAlgebra.{u, v} R}
    (hA : A.IsLawful) (P : ℕ → DGModule.{u, w, v} A)
    (hP : ∀ i, (P i).IsLawful) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (hT : (totalModule P f).IsLawful) (E : ∀ i, FreeExtension (P i)) (t : ℕ) :
    (totalFiltrationStep P f E t).IsLawful := by
  let := hT.isInternal.chooseDecomposition
  apply isInternal_comap_of_homogeneous (totalModule P f).grading
    (filtrationSubmodule P E t).toAddSubgroup
  rintro x ⟨hx, hx'⟩ n
  let x : ⨁ i, (P i).carrier := x
  constructor
  · intro j hj
    let G := fun n => (P j).grading (n + j)
    let : DirectSum.Decomposition G := (shift_isLawful hA (hP j) j).isInternal.chooseDecomposition
    let q : (⨁ i, (P i).carrier) →+ (P j).carrier :=
      (DirectSum.component ℤ ℕ (fun i => (P i).carrier) j).toAddMonoidHom
    exact map_decompose_eq_zero (totalModule P f).grading G q (fun n x hx => hx j) x
      (hx j hj) n
  · intro j hj
    let G := fun n => (E j).right.grading (n + j)
    let : DirectSum.Decomposition G :=
      (shift_isLawful hA (E j).right_lawful j).isInternal.chooseDecomposition
    let q : (⨁ i, (P i).carrier) →+ (E j).right.carrier :=
      (E j).proj.toFun.toAddMonoidHom.comp
        (DirectSum.component ℤ ℕ (fun i => (P i).carrier) j).toAddMonoidHom
    exact map_decompose_eq_zero (totalModule P f).grading G q
      (fun n x hx => (E j).proj.map_grading (n + j) _ (hx j)) x (hx' j hj) n

private noncomputable def FreeExtension.retraction {A : DGAlgebra.{u, v} R}
    {P : DGModule.{u, w, v} A} (E : FreeExtension P) : DGModule.GradedHom P E.left :=
  E.exact.admissibleMono.2.choose

private lemma FreeExtension.retraction_incl {A : DGAlgebra.{u, v} R}
    {P : DGModule.{u, w, v} A} (E : FreeExtension P) (x : E.left.carrier) :
    E.retraction.toFun (E.incl.toFun x) = x :=
  E.exact.admissibleMono.2.choose_spec x

private lemma FreeExtension.proj_incl {A : DGAlgebra.{u, v} R}
    {P : DGModule.{u, w, v} A} (E : FreeExtension P) (x : E.left.carrier) :
    E.proj.toFun (E.incl.toFun x) = 0 := by
  have h : E.incl.toFun x ∈ LinearMap.range E.incl.toFun := ⟨x, rfl⟩
  rw [E.exact.exact] at h
  exact h

private lemma FreeExtension.incl_retraction {A : DGAlgebra.{u, v} R}
    {P : DGModule.{u, w, v} A} (E : FreeExtension P) (x : P.carrier)
    (hx : E.proj.toFun x = 0) : E.incl.toFun (E.retraction.toFun x) = x := by
  have h : x ∈ LinearMap.ker E.proj.toFun := hx
  rw [← E.exact.exact] at h
  obtain ⟨y, rfl⟩ := h
  rw [E.retraction_incl]

private lemma FreeExtension.retraction_d {A : DGAlgebra.{u, v} R}
    {P : DGModule.{u, w, v} A} (E : FreeExtension P) (x : P.carrier)
    (hx : E.proj.toFun x = 0) :
    E.retraction.toFun (P.d x) = E.left.d (E.retraction.toFun x) := by
  apply E.exact.injective
  rw [E.incl_retraction _ (by rw [E.proj.commute_d, hx, map_zero]),
    E.incl.commute_d, E.incl_retraction _ hx]

private noncomputable def filtrationProjection {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (E : ∀ i, FreeExtension (P i)) (t : ℕ) :
    (⨁ i, (P i).carrier) →ₗ[A.carrierᵐᵒᵖ] (⨁ i, (P i).carrier) :=
  DirectSum.lmap fun j =>
    if 2 * j < t then LinearMap.id else
    if 2 * j = t then (E j).incl.toFun.comp (E j).retraction.toFun else 0

private lemma filtrationProjection_apply {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (E : ∀ i, FreeExtension (P i)) (t : ℕ)
    (x : ⨁ i, (P i).carrier) (j : ℕ) :
    filtrationProjection P E t x j =
      if 2 * j < t then x j else
      if 2 * j = t then (E j).incl.toFun ((E j).retraction.toFun (x j)) else 0 := by
  simp only [filtrationProjection, DirectSum.lmap_eq_map, DirectSum.map_apply]
  split_ifs <;> rfl

private lemma filtrationProjection_mem {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (E : ∀ i, FreeExtension (P i)) (t : ℕ)
    (x : ⨁ i, (P i).carrier) :
    filtrationProjection P E t x ∈ filtrationSubmodule P E t := by
  constructor
  · intro j hj
    rw [filtrationProjection_apply, ite_eq_right (by omega), ite_eq_right (by omega)]
  · intro j hj
    rw [filtrationProjection_apply, ite_eq_right (by omega), ite_eq_left hj.symm,
      FreeExtension.proj_incl]

private lemma filtrationProjection_eq_self {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (E : ∀ i, FreeExtension (P i)) (t : ℕ)
    (x : ⨁ i, (P i).carrier) (hx : x ∈ filtrationSubmodule P E t) :
    filtrationProjection P E t x = x := by
  apply DirectSum.ext
  intro j
  rw [filtrationProjection_apply]
  split_ifs with h h'
  · rfl
  · exact (E j).incl_retraction _ (hx.2 j h'.symm)
  · exact (hx.1 j (by omega)).symm

private noncomputable def filtrationRetraction {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t : ℕ) :
    DGModule.GradedHom (totalModule P f) (totalFiltrationStep P f E t).toDGModule where
  toFun := (filtrationProjection P E t).codRestrict _ (filtrationProjection_mem P E t)
  map_grading n x hx := by
    intro j
    change filtrationProjection P E t x j ∈ (P j).grading (n + j)
    rw [filtrationProjection_apply]
    split_ifs
    · exact hx j
    · exact (E j).incl.map_grading _ _ ((E j).retraction.map_grading _ _ (hx j))
    · exact zero_mem _

private noncomputable def filtrationInclusion {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t : ℕ) :
    DGModule.Hom (totalFiltrationStep P f E t).toDGModule
      (totalFiltrationStep P f E (t + 1)).toDGModule where
  toFun := Submodule.inclusion (totalFiltrationStep_mono P f E t)
  map_grading _ _ hx := hx
  commute_d _ := rfl

private lemma filtrationInclusion_admissible {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t : ℕ) :
    DGModule.IsAdmissibleMono (filtrationInclusion P f E t) := by
  refine ⟨?_, (filtrationRetraction P f E t).comp
    (totalFiltrationStep P f E (t + 1)).incl.toGradedHom, ?_⟩
  · exact fun _ _ h => Subtype.ext
      (congrArg (fun z : (totalFiltrationStep P f E (t + 1)).toDGModule.carrier => z.val) h)
  · exact fun x => Subtype.ext (filtrationProjection_eq_self P E t x.val x.property)

private lemma neg_one_pow_natAbs_add (a b : ℤ) :
    (-1 : ℤ) ^ (a + b).natAbs = (-1 : ℤ) ^ a.natAbs * (-1 : ℤ) ^ b.natAbs := by
  have hn (n : ℤ) : (n.negOnePow : ℤ) = (-1 : ℤ) ^ n.natAbs := by
    simpa only [Int.cast_id] using Int.coe_negOnePow ℤ n
  rw [← hn, ← hn, ← hn, Int.negOnePow_add, Units.val_mul]

private noncomputable def shiftDirectSumIso {A : DGAlgebra.{u, v} R}
    {ι : Type*} [DecidableEq ι] (k : ι → ℤ)
    {N : DGModule.{u, w, v} A}
    (e : DGModule.Iso N (DGModule.directSum (fun j => DGModule.shiftFree A (k j))))
    (s : ℤ) :
    DGModule.Iso (N.shift s)
      (DGModule.directSum (fun j => DGModule.shiftFree A (k j + s))) where
  toFun := e.toFun
  map_grading n x hx j := by
    let y : ⨁ j : ι, A.carrier := e.toFun x
    have h := e.map_grading (n + s) x hx j
    change y j ∈ (A.grading (n + (k j + s))).toAddSubgroup
    change y j ∈ (A.grading (n + s + k j)).toAddSubgroup at h
    simpa only [add_assoc, add_comm, add_left_comm] using h
  commute_d x := by
    change e.toFun ((-1 : ℤ) ^ s.natAbs • N.d x) = _
    rw [map_zsmul, e.commute_d]
    apply DirectSum.ext
    intro j
    let y : ⨁ j : ι, A.carrier := e.toFun x
    change ((-1 : ℤ) ^ s.natAbs •
      DGModule.directSumD (fun j => DGModule.shiftFree A (k j)) y) j =
      (DGModule.directSumD (fun j => DGModule.shiftFree A (k j + s)) y) j
    rw [DirectSum.smul_apply, DifferentialGraded.NativeCover.Native.directSum_d_apply,
      DifferentialGraded.NativeCover.Native.directSum_d_apply]
    change (-1 : ℤ) ^ s.natAbs • ((-1 : ℤ) ^ (k j).natAbs • A.d (y j)) =
      (-1 : ℤ) ^ (k j + s).natAbs • A.d (y j)
    rw [smul_smul, neg_one_pow_natAbs_add, mul_comm]
  invFun := e.invFun
  left_inv := e.left_inv
  right_inv := e.right_inv

private lemma single_mem_filtrationSubmodule {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (E : ∀ i, FreeExtension (P i))
    (t i : ℕ) (x : (P i).carrier)
    (hi : 2 * i ≤ t) (hx : t = 2 * i → (E i).proj.toFun x = 0) :
    DirectSum.of (fun i => (P i).carrier) i x ∈ filtrationSubmodule P E t := by
  constructor
  · intro j hj
    exact DirectSum.of_eq_of_ne _ _ _ (by omega)
  · intro j hj
    by_cases h : j = i
    · subst j
      rw [DirectSum.of_eq_same]
      exact hx hj
    · rw [DirectSum.of_eq_of_ne _ _ _ h, map_zero]

private noncomputable def leftEvaluation {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t i : ℕ) (ht : t = 2 * i) :
    DGModule.Hom (totalFiltrationStep P f E t).toDGModule ((E i).left.shift (i : ℤ)) where
  toFun := (E i).retraction.toFun.comp
    ((DirectSum.component A.carrierᵐᵒᵖ ℕ (fun i => (P i).carrier) i).comp
      (filtrationSubmodule P E t).subtype)
  map_grading n x hx := (E i).retraction.map_grading (n + i) _ (hx i)
  commute_d x := by
    let z : ⨁ j, (P j).carrier := x.val
    change (E i).retraction.toFun ((totalDifferential P f z) i) =
      (-1 : ℤ) ^ (i : ℤ).natAbs • (E i).left.d ((E i).retraction.toFun (z i))
    rw [totalModule_d_apply, x.property.1 (i + 1) (by omega), map_zero, add_zero,
      map_zsmul, (E i).retraction_d _ (x.property.2 i ht), Int.natAbs_natCast]

private lemma leftEvaluation_surjective {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t i : ℕ) (ht : t = 2 * i) :
    Function.Surjective (leftEvaluation P f E t i ht).toFun := by
  intro y
  refine ⟨⟨DirectSum.of (fun i => (P i).carrier) i ((E i).incl.toFun y),
    single_mem_filtrationSubmodule P E t i _ (by omega)
      (fun _ => (E i).proj_incl y)⟩, ?_⟩
  show (E i).retraction.toFun
    ((DirectSum.of (fun i => (P i).carrier) i ((E i).incl.toFun y)) i) = y
  rw [DirectSum.of_eq_same, FreeExtension.retraction_incl]

private lemma leftEvaluation_eq_zero_iff {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t i : ℕ) (ht : t = 2 * i)
    (x : (totalFiltrationStep P f E t).toDGModule.carrier) :
    (leftEvaluation P f E t i ht).toFun x = 0 ↔
      (DirectSum.component A.carrierᵐᵒᵖ ℕ (fun j => (P j).carrier) i) x.val = 0 := by
  let z : ⨁ j, (P j).carrier := x.val
  show (E i).retraction.toFun (z i) = 0 ↔ z i = 0
  have hz : (E i).proj.toFun (z i) = 0 := x.property.2 i ht
  constructor
  · intro h
    rw [← (E i).incl_retraction (z i) hz, h, map_zero]
  · intro h
    rw [h, map_zero]

private noncomputable def rightEvaluation {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t i : ℕ) (ht : t = 2 * i + 1) :
    DGModule.Hom (totalFiltrationStep P f E t).toDGModule ((E i).right.shift (i : ℤ)) where
  toFun := (E i).proj.toFun.comp
    ((DirectSum.component A.carrierᵐᵒᵖ ℕ (fun i => (P i).carrier) i).comp
      (filtrationSubmodule P E t).subtype)
  map_grading n x hx := (E i).proj.map_grading (n + i) _ (hx i)
  commute_d x := by
    let z : ⨁ j, (P j).carrier := x.val
    change (E i).proj.toFun ((totalDifferential P f z) i) =
      (-1 : ℤ) ^ (i : ℤ).natAbs • (E i).right.d ((E i).proj.toFun (z i))
    rw [totalModule_d_apply, x.property.1 (i + 1) (by omega), map_zero, add_zero,
      map_zsmul, (E i).proj.commute_d, Int.natAbs_natCast]

private lemma rightEvaluation_surjective {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t i : ℕ) (ht : t = 2 * i + 1) :
    Function.Surjective (rightEvaluation P f E t i ht).toFun := by
  intro y
  obtain ⟨x, hx⟩ := (E i).exact.surjective y
  refine ⟨⟨DirectSum.of (fun i => (P i).carrier) i x,
    single_mem_filtrationSubmodule P E t i x (by omega) (by omega)⟩, ?_⟩
  show (E i).proj.toFun ((DirectSum.of (fun i => (P i).carrier) i x) i) = y
  rw [DirectSum.of_eq_same, hx]

private lemma filtrationInclusion_range {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t : ℕ)
    (x : (totalFiltrationStep P f E (t + 1)).toDGModule.carrier) :
    x ∈ LinearMap.range (filtrationInclusion P f E t).toFun ↔
      x.val ∈ filtrationSubmodule P E t := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x.val, hx⟩, rfl⟩

private lemma rightEvaluation_ker {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (i : ℕ) :
    LinearMap.ker (rightEvaluation P f E (2 * i + 1) i rfl).toFun =
      LinearMap.range (filtrationInclusion P f E (2 * i)).toFun := by
  ext x
  rw [filtrationInclusion_range]
  show (E i).proj.toFun
    ((DirectSum.component A.carrierᵐᵒᵖ ℕ (fun j => (P j).carrier) i) x.val) = 0 ↔ _
  constructor
  · intro hx
    constructor
    · intro j hj
      exact x.property.1 j (by omega)
    · intro j hj
      have h : j = i := by omega
      subst j
      exact hx
  · intro hx
    exact hx.2 i rfl

private lemma leftEvaluation_ker {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (i : ℕ) :
    LinearMap.ker (leftEvaluation P f E (2 * i + 1 + 1) (i + 1) (by omega)).toFun =
      LinearMap.range (filtrationInclusion P f E (2 * i + 1)).toFun := by
  ext x
  rw [LinearMap.mem_ker, leftEvaluation_eq_zero_iff, filtrationInclusion_range]
  constructor
  · intro hx
    constructor
    · intro j hj
      by_cases h : j = i + 1
      · subst j; exact hx
      · exact x.property.1 j (by omega)
    · intro j hj
      omega
  · intro hx
    exact hx.1 (i + 1) (by omega)

private noncomputable def isoOfBijective {A : DGAlgebra.{u, v} R}
    {M : DGModule.{u, w, v} A} {N : DGModule.{u, w', v} A}
    (f : DGModule.Hom M N) (hf : Function.Bijective f.toFun) : DGModule.Iso M N where
  toHom := f
  invFun := (LinearEquiv.ofBijective f.toFun hf).symm.toLinearMap
  left_inv := (LinearEquiv.ofBijective f.toFun hf).left_inv
  right_inv := (LinearEquiv.ofBijective f.toFun hf).right_inv

private lemma iso_bijective {A : DGAlgebra.{u, v} R}
    {M : DGModule.{u, w, v} A} {N : DGModule.{u, w', v} A}
    (e : DGModule.Iso M N) : Function.Bijective e.toFun :=
  ⟨Function.LeftInverse.injective e.left_inv, Function.RightInverse.surjective e.right_inv⟩

private lemma leftEvaluation_zero_injective {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) :
    Function.Injective (leftEvaluation P f E 0 0 rfl).toFun := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h0 := (leftEvaluation_eq_zero_iff P f E 0 0 rfl x).mp hx
  apply Subtype.ext
  apply DirectSum.ext
  intro j
  show (DirectSum.component A.carrierᵐᵒᵖ ℕ (fun j => (P j).carrier) j) x.val = 0
  by_cases h : j = 0
  · subst j
    exact h0
  · exact x.property.1 j (by omega)

private noncomputable def filtrationBottomIso {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) :
    DGModule.Iso (totalFiltrationStep P f E 0).toDGModule
      (@DGModule.directSum _ _ _ (E 0).leftIndex (E 0).leftDec
        (fun j => DGModule.shiftFree A ((E 0).leftShift j + (0 : ℕ)))) := by
  letI := (E 0).leftDec
  let e := shiftDirectSumIso (E 0).leftShift (E 0).leftIso 0
  exact isoOfBijective (e.toHom.comp (leftEvaluation P f E 0 0 rfl))
    ((iso_bijective e).comp
      ⟨leftEvaluation_zero_injective P f E, leftEvaluation_surjective P f E 0 0 rfl⟩)

private lemma exists_filtration_quotient {A : DGAlgebra.{u, v} R}
    (P : ℕ → DGModule.{u, w, v} A) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (E : ∀ i, FreeExtension (P i)) (t : ℕ) :
    ∃ (I : Type w) (dec : DecidableEq I) (k : I → ℤ) (Q : DGModule.{u, w, v} A)
      (_e : DGModule.Iso Q (@DGModule.directSum _ _ _ I dec
        (fun j => DGModule.shiftFree A (k j))))
      (q : DGModule.Hom (totalFiltrationStep P f E (t + 1)).toDGModule Q),
      Function.Surjective q.toFun ∧
        LinearMap.ker q.toFun = LinearMap.range (filtrationInclusion P f E t).toFun := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' t
  · let := (E i).rightDec
    exact ⟨(E i).rightIndex, (E i).rightDec, fun j => (E i).rightShift j + i,
      (E i).right.shift i, shiftDirectSumIso (E i).rightShift (E i).rightIso i,
      rightEvaluation P f E (2 * i + 1) i rfl,
      rightEvaluation_surjective P f E (2 * i + 1) i rfl, rightEvaluation_ker P f E i⟩
  · let := (E (i + 1)).leftDec
    exact ⟨(E (i + 1)).leftIndex, (E (i + 1)).leftDec,
      fun j => (E (i + 1)).leftShift j + (i + 1 : ℕ),
      (E (i + 1)).left.shift (i + 1 : ℕ),
      shiftDirectSumIso (E (i + 1)).leftShift (E (i + 1)).leftIso (i + 1 : ℕ),
      leftEvaluation P f E (2 * i + 1 + 1) (i + 1) (by omega),
      leftEvaluation_surjective P f E (2 * i + 1 + 1) (i + 1) (by omega),
      leftEvaluation_ker P f E i⟩

private lemma totalModule_has_propertyP {A : DGAlgebra.{u, v} R}
    (hA : A.IsLawful) (P : ℕ → DGModule.{u, w, v} A)
    (hP : ∀ i, (P i).IsLawful) (f : ∀ i, DGModule.Hom (P (i + 1)) (P i))
    (hT : (totalModule P f).IsLawful) (E : ∀ i, FreeExtension (P i)) :
    Nonempty (DGModule.PropertyPFiltration.{u, v, w, w, w, w} (totalModule P f)) := by
  classical
  choose I dec k Q e q hs hk using exists_filtration_quotient P f E
  exact ⟨{
    F := totalFiltrationStep P f E
    F_lawful := totalFiltrationStep_isLawful hA P hP f hT E
    mono := totalFiltrationStep_mono P f E
    exhaustive := totalFiltrationStep_exhaustive P f E
    inclHom := filtrationInclusion P f E
    inclHom_apply := fun _ _ => rfl
    admissible := filtrationInclusion_admissible P f E
    bottomShiftIndex := (E 0).leftIndex
    bottomShiftIndexDec := (E 0).leftDec
    bottomShiftAmount := fun j => (E 0).leftShift j + (0 : ℕ)
    bottomIso := filtrationBottomIso P f E
    shiftIndex := I
    shiftIndexDec := dec
    shiftAmount := k
    quotient := Q
    quotientIso := e
    isQuotient := fun t => ⟨q t, hs t, hk t⟩ }⟩

/-- **Property-(P) resolutions exist.** Every lawful differential graded module `M` over a lawful
differential graded algebra `A` receives a quasi-isomorphism from a lawful differential graded
`A`-module `P` carrying a property-(P) filtration: an exhaustive increasing filtration by
differential graded submodules with admissible inclusions whose graded pieces are direct sums of
shifts of `A`. -/
@[stacks 09KP]
public theorem exists_propertyP_resolution (A : DGAlgebra.{u, v} R) (hA : A.IsLawful)
    (M : DGModule.{u, w, v} A) (hM : M.IsLawful) :
    ∃ (P : DGModule.{u, max v w, v} A) (_hP : P.IsLawful) (f : DGModule.Hom P M),
      IsQuasiIsomorphism f ∧
        Nonempty (DGModule.PropertyPFiltration.{u, v, max v w, max v w, max v w, max v w} P) := by
  let P := fun i => (resolutionCover hA hM i).obj
  let f := resolutionMap hA hM
  have hT := totalModule_isLawful hA P (fun i => (resolutionCover hA hM i).lawful)
    f (resolutionMap_comp hA hM)
  obtain ⟨e, he⟩ := resolution_total_isQuasiIsomorphism hA hM
  exact ⟨totalModule P f, hT, e, he, totalModule_has_propertyP hA P
    (fun i => (resolutionCover hA hM i).lawful) f hT (fun i => (resolutionCover hA hM i).pieces)⟩

end Stacks.DifferentialGraded.DGModule

end
