module

public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP
public import StacksFrontier.Algebra.DifferentialGraded.Telescope
public import StacksFrontier.Algebra.DirectSum.GradedSubmodule

/-! # The telescope of a property-(P) filtration, in the bundled encoding

Let `(A, d)` be a differential graded algebra over a commutative ring `R` and let `P` be a right
differential graded `A`-module carrying a property-(P) filtration `F_•`. The *telescope* of the
filtration is the differential graded `A`-module `⨁_{i ≥ 0} F_iP` together with the two
homomorphisms

`α : ⨁ F_iP ⟶ ⨁ F_iP`,  `α|_{F_iP} = incl_i - (F_iP ↪ F_{i+1}P)`,
`β : ⨁ F_iP ⟶ P`,  `β|_{F_iP} = (F_iP ↪ P)`,

and `0 → ⨁ F_iP → ⨁ F_iP → P → 0` is an admissible short exact sequence (Stacks Tag 09KL). This
file transports that statement from the unbundled encoding `Stacks.DifferentialGraded.DGAlgebra` /
`Stacks.DifferentialGraded.DGModule` to the bundled encoding, in which a property-(P) filtration
is `DifferentialGradedModule.PropertyPFiltration`.

## Main results

* `DifferentialGradedModule.exists_telescope_of_propertyPFiltration`: the telescoping admissible
  short exact sequence attached to a property-(P) filtration of a bundled differential graded
  module, with its direct sum pinned by the universal property and its two maps pinned by their
  values on each stage.

## References

* [Stacks Project, Tag 09KL](https://stacks.math.columbia.edu/tag/09KL)
* [Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK), property (P)
* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT), admissible short exact
  sequences
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.DifferentialGraded
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### From the bundled encoding to the unbundled one -/

/-- A homomorphism of *graded* bundled differential graded modules, read in the unbundled
encoding. -/
private def unbundledGradedHom {M N : DifferentialGradedModule.{u, u, u} A} (f : GradedHom M N) :
    DGModule.GradedHom (Unbundled.module M) (Unbundled.module N) where
  toFun := { __ := f.toFun.toAddHom, map_smul' := fun a x => f.map_smul x a.unop }
  map_grading := f.map_grading

/-- A homomorphism of bundled differential graded modules, read in the unbundled encoding. -/
private def unbundledHom {M N : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ N) :
    DGModule.Hom (Unbundled.module M) (Unbundled.module N) where
  __ := unbundledGradedHom f.toGradedHom
  commute_d x := LinearMap.congr_fun f.map_d x

/-- The range of a homomorphism of bundled differential graded modules, as an unbundled
differential graded submodule of its target. -/
private def unbundledRange {Q P : DifferentialGradedModule.{u, u, u} A} (f : Q ⟶ P) :
    DGModule.DGSubmodule (Unbundled.module P) where
  toSubmodule := LinearMap.range (unbundledHom f).toFun
  d_stable := by rintro _ ⟨x, rfl⟩; exact ⟨Q.d x, LinearMap.congr_fun f.map_d x⟩

/-- A graded component of an element of the range of a grading-preserving homomorphism is again
in that range. -/
private theorem decompose_mem_range {Q P : DifferentialGradedModule.{u, u, u} A} (f : Q ⟶ P)
    (n : ℤ) (x : P.M) (hx : x ∈ LinearMap.range f.toFun) :
    (DirectSum.decompose P.grading x n : P.M) ∈ LinearMap.range f.toFun := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨DirectSum.decompose Q.grading y n,
    (DirectSum.coe_decompose_apply_map Q.grading P.grading f.toFun
      (fun i z hz => f.map_grading i z hz) y n).symm⟩

/-- The range of a homomorphism is a graded submodule, so it is a lawful unbundled differential
graded submodule. -/
private theorem unbundledRange_isLawful {Q P : DifferentialGradedModule.{u, u, u} A} (f : Q ⟶ P) :
    (unbundledRange f).IsLawful := by
  have hdec := Submodule.inducedGrading.decomposition P.grading
    ((LinearMap.range (unbundledHom f).toFun).restrictScalars R)
    (fun n m hm => decompose_mem_range f n m hm)
  exact DirectSum.Decomposition.isInternal
    (ℳ := Submodule.inducedGrading P.grading
      ((LinearMap.range (unbundledHom f).toFun).restrictScalars R))

/-- An injective homomorphism of differential graded modules is a linear equivalence onto its
range. -/
private def rangeEquiv {Q P : DifferentialGradedModule.{u, u, u} A} (f : Q ⟶ P)
    (hf : Function.Injective f.toFun) : Q.M ≃ₗ[A.Aᵐᵒᵖ] (unbundledRange f).toSubmodule :=
  LinearEquiv.ofInjective (unbundledHom f).toFun hf

/-- The embedding of an injective homomorphism undoes the inverse of `rangeEquiv`. -/
private theorem map_rangeEquiv_symm {Q P : DifferentialGradedModule.{u, u, u} A} (f : Q ⟶ P)
    (hf : Function.Injective f.toFun) (x : (unbundledRange f).toSubmodule) :
    f.toFun ((rangeEquiv f hf).symm x) = (x : P.M) :=
  congrArg Subtype.val ((rangeEquiv f hf).apply_symm_apply x)

/-- An injective homomorphism of differential graded modules reflects homogeneity: a homogeneous
element of its range comes from a homogeneous element. -/
private theorem rangeEquiv_symm_mem_grading {Q P : DifferentialGradedModule.{u, u, u} A}
    (f : Q ⟶ P) (hf : Function.Injective f.toFun) (n : ℤ)
    (x : (unbundledRange f).toSubmodule) (hx : (x : P.M) ∈ P.grading n) :
    (rangeEquiv f hf).symm x ∈ Q.grading n := by
  have he := map_rangeEquiv_symm f hf x
  have h := DirectSum.coe_decompose_apply_map Q.grading P.grading f.toFun
    (fun i z hz => f.map_grading i z hz) ((rangeEquiv f hf).symm x) n
  rw [he, DirectSum.decompose_of_mem_same P.grading hx] at h
  have hy : (DirectSum.decompose Q.grading ((rangeEquiv f hf).symm x) n : Q.M) =
      (rangeEquiv f hf).symm x := hf (h.symm.trans he.symm)
  exact hy ▸ (DirectSum.decompose Q.grading ((rangeEquiv f hf).symm x) n).property

/-- An injective homomorphism of differential graded modules is an isomorphism onto its range, in
the unbundled encoding. -/
private def rangeIso {Q P : DifferentialGradedModule.{u, u, u} A} (f : Q ⟶ P)
    (hf : Function.Injective f.toFun) :
    DGModule.Iso (Unbundled.module Q) (unbundledRange f).toDGModule where
  toFun := (rangeEquiv f hf).toLinearMap
  map_grading := f.map_grading
  commute_d x := Subtype.ext (LinearMap.congr_fun f.map_d x)
  invFun := (rangeEquiv f hf).symm.toLinearMap
  left_inv := (rangeEquiv f hf).symm_apply_apply
  right_inv := (rangeEquiv f hf).apply_symm_apply

/-- The inverse of `DifferentialGradedModule.rangeIso`, as a homomorphism of unbundled
differential graded modules. -/
private def rangeIsoInv {Q P : DifferentialGradedModule.{u, u, u} A} (f : Q ⟶ P)
    (hf : Function.Injective f.toFun) :
    DGModule.Hom (unbundledRange f).toDGModule (Unbundled.module Q) where
  toFun := (rangeEquiv f hf).symm.toLinearMap
  map_grading := rangeEquiv_symm_mem_grading f hf
  commute_d x := by
    refine hf ?_
    exact (map_rangeEquiv_symm f hf _).trans ((congrArg P.d (map_rangeEquiv_symm f hf x).symm).trans
      (LinearMap.congr_fun f.map_d _).symm)

/-- A bijective homomorphism of unbundled differential graded modules is an isomorphism. -/
private def isoOfBijectiveUnbundled {M N : DGModule.{u, u, u} (Unbundled.algebra A)}
    (f : DGModule.Hom M N) (hf : Function.Bijective f.toFun) : DGModule.Iso M N := by
  letI := M.moduleA
  letI := N.moduleA
  exact
    { __ := f
      invFun := (LinearEquiv.ofBijective f.toFun hf).symm.toLinearMap
      left_inv := (LinearEquiv.ofBijective f.toFun hf).symm_apply_apply
      right_inv := (LinearEquiv.ofBijective f.toFun hf).apply_symm_apply }

/-- A homomorphism into a bundled direct sum of shifts of the algebra, read in the unbundled
encoding. -/
private def unbundledShiftSumHom {ι : Type u} [DecidableEq ι] (k : ι → ℤ)
    {M : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ directSumShifts A k) :
    DGModule.Hom (Unbundled.module M)
      (DGModule.directSum (fun i => DGModule.shiftFree (Unbundled.algebra A) (k i))) where
  toFun := (unbundledHom f).toFun
  map_grading := f.map_grading
  commute_d := (unbundledHom f).commute_d

/-- A property-(P) filtration of a bundled differential graded module, read in the unbundled
encoding: each stage is replaced by the range of its embedding into the filtered module. -/
private def unbundledFiltration {P : DifferentialGradedModule.{u, u, u} A}
    (F : PropertyPFiltration P) :
    DGModule.PropertyPFiltration.{u, u, u, u, u, u} (Unbundled.module P) := by
  letI := F.bottomDecidableEq
  letI := F.quotientDecidableEq
  let e : ∀ i, DGModule.Iso (Unbundled.module (F.F i)) (unbundledRange (F.ι i)).toDGModule :=
    fun i => rangeIso (F.ι i) (F.injective i)
  let e' : ∀ i, DGModule.Hom (unbundledRange (F.ι i)).toDGModule (Unbundled.module (F.F i)) :=
    fun i => rangeIsoInv (F.ι i) (F.injective i)
  let inc : ∀ i, DGModule.Hom (unbundledRange (F.ι i)).toDGModule
      (unbundledRange (F.ι (i + 1))).toDGModule :=
    fun i => (e (i + 1)).toHom.comp ((unbundledHom (F.incl i)).comp (e' i))
  refine
    { F := fun i => unbundledRange (F.ι i)
      F_lawful := fun i => unbundledRange_isLawful (F.ι i)
      mono := ?_
      exhaustive := ?_
      inclHom := inc
      inclHom_apply := ?_
      admissible := ?_
      bottomShiftIndex := F.bottomIndex
      bottomShiftIndexDec := F.bottomDecidableEq
      bottomShiftAmount := F.bottomShift
      bottomIso := isoOfBijectiveUnbundled
        ((unbundledShiftSumHom F.bottomShift F.bottomMap).comp (e' 0))
        (F.bottom_bijective.comp (rangeEquiv (F.ι 0) (F.injective 0)).symm.bijective)
      shiftIndex := F.quotientIndex
      shiftIndexDec := F.quotientDecidableEq
      shiftAmount := F.quotientShift
      quotient := fun i => DGModule.directSum
        (fun j => DGModule.shiftFree (Unbundled.algebra A) (F.quotientShift i j))
      quotientIso := fun _ =>
        isoOfBijectiveUnbundled (DGModule.Hom.id _) Function.bijective_id
      isQuotient := ?_ }
  · rintro i _ ⟨x, rfl⟩
    exact ⟨(F.incl i).toFun x, F.incl_comp i x⟩
  · exact F.exhaustive
  · intro i x
    change (F.ι (i + 1)).toFun ((F.incl i).toFun ((e i).invFun x)) = _
    rw [F.incl_comp]
    exact congrArg Subtype.val ((e i).right_inv x)
  · intro i
    obtain ⟨r, hr⟩ := F.admissible i
    let r' := (e i).toGradedHom.comp ((unbundledGradedHom r).comp (e' (i + 1)).toGradedHom)
    have h : ∀ x, r'.toFun ((inc i).toFun x) = x := by
      intro x
      change (e i).toFun (r.toFun ((e (i + 1)).invFun
        ((e (i + 1)).toFun ((F.incl i).toFun ((e i).invFun x))))) = x
      rw [(e (i + 1)).left_inv, hr, (e i).right_inv]
    exact ⟨Function.LeftInverse.injective h, r', h⟩
  · intro i
    let _ := ((unbundledRange (F.ι (i + 1))).toDGModule).moduleA
    refine ⟨(unbundledShiftSumHom (F.quotientShift i) (F.quotientMap i)).comp (e' (i + 1)),
      (F.quotient_surjective i).comp
        (rangeEquiv (F.ι (i + 1)) (F.injective (i + 1))).symm.surjective, ?_⟩
    refine Submodule.ext fun x => ?_
    change (F.quotientMap i).toFun ((e (i + 1)).invFun x) = 0 ↔
      ∃ y, (e (i + 1)).toFun ((F.incl i).toFun ((e i).invFun y)) = x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ : (e (i + 1)).invFun x ∈ LinearMap.range (F.incl i).toFun := by
        rwa [← F.quotient_ker i]
      refine ⟨(e i).toFun y, ?_⟩
      rw [(e i).left_inv, hy, (e (i + 1)).right_inv]
    · rintro ⟨y, rfl⟩
      rw [(e (i + 1)).left_inv]
      have hm : (F.incl i).toFun ((e i).invFun y) ∈ LinearMap.range (F.incl i).toFun := ⟨_, rfl⟩
      rwa [← F.quotient_ker i] at hm

/-! ### The telescope -/

/-- A bundled differential graded module is the bundling of the unbundled module underlying
it. -/
private def rebundleIso (M : DifferentialGradedModule.{u, u, u} A) :
    Unbundled.bundle (Unbundled.module_isLawful M) ≅ M where
  hom :=
    { toFun := LinearMap.id
      map_smul := by intros; rfl
      map_grading := by intros; assumption
      map_d := rfl }
  inv :=
    { toFun := LinearMap.id
      map_smul := by intros; rfl
      map_grading := by intros; assumption
      map_d := rfl }
  hom_inv_id := Hom.ext rfl
  inv_hom_id := Hom.ext rfl

/-- **The telescope of a property-(P) filtration.** Let `P` be a right differential graded
`A`-module with a property-(P) filtration `F_•`. Then there are a differential graded `A`-module
`S` with homomorphisms `ι_i : F_iP ⟶ S` exhibiting it as the direct sum `⨁_{i ≥ 0} F_iP`, and
homomorphisms `α : S ⟶ S`, `β : S ⟶ P` with

`β ∘ ι_i = (F_iP ↪ P)`  and  `α ∘ ι_i = ι_i - ι_{i+1} ∘ (F_iP ↪ F_{i+1}P)`,

such that `0 → S → S → P → 0` is an admissible short exact sequence. The direct sum is recorded
by the universal property of a coproduct. -/
theorem exists_telescope_of_propertyPFiltration {P : DifferentialGradedModule.{u, u, u} A}
    (F : PropertyPFiltration P) :
    ∃ (S : DifferentialGradedModule.{u, u, u} A) (ι : ∀ i : ℕ, F.F i ⟶ S) (α : S ⟶ S) (β : S ⟶ P),
      (∀ (T : DifferentialGradedModule.{u, u, u} A) (g : ∀ i : ℕ, F.F i ⟶ T),
          ∃! h : S ⟶ T, ∀ i : ℕ, ι i ≫ h = g i) ∧
        (∀ (i : ℕ) (x : (F.F i).M), β.toFun ((ι i).toFun x) = (F.ι i).toFun x) ∧
        (∀ (i : ℕ) (x : (F.F i).M), α.toFun ((ι i).toFun x) =
          (ι i).toFun x - (ι (i + 1)).toFun ((F.incl i).toFun x)) ∧
        IsAdmissibleShortExact α β := by
  classical
  let UF := unbundledFiltration F
  have hP := Unbundled.module_isLawful P
  obtain ⟨hS, a, b, ha, hb, hab⟩ := DGModule.admissible_ses_of_propertyP hP UF
  let S := Unbundled.bundle hS
  let a' : S ⟶ S := Unbundled.bundleHom hS hS a
  let b' : S ⟶ P := Unbundled.bundleHom hS hP b ≫ (rebundleIso P).hom
  let K : ℕ → Type u := fun i => (UF.F i).toDGModule.carrier
  let _ : ∀ i, Module R (K i) := fun i => (UF.F i).toDGModule.moduleR
  let _ : ∀ i, Module A.Aᵐᵒᵖ (K i) := fun i => (UF.F i).toDGModule.moduleA
  let _ : Module A.Aᵐᵒᵖ S.M := S.rmodule
  let e : ∀ i, (F.F i).M ≃ₗ[A.Aᵐᵒᵖ] K i := fun i => rangeEquiv (F.ι i) (F.injective i)
  have hdir : ∀ (i : ℕ) (y : K i),
      DGModule.directSumD (fun k => (UF.F k).toDGModule) (DirectSum.of K i y) =
        DirectSum.of K i ((UF.F i).toDGModule.d y) := by
    intro i y
    rw [← DirectSum.lof_eq_of R, ← DirectSum.lof_eq_of R]
    exact DirectSum.toModule_lof R i y
  let jN : ∀ i, DGModule.Hom (Unbundled.module (F.F i)) (DGModule.telescopeObj UF) := fun i =>
    { toFun := (DirectSum.lof A.Aᵐᵒᵖ ℕ K i).comp (e i).toLinearMap
      map_grading := by
        intro n x hx k
        change (DirectSum.of K i (e i x)) k ∈ (UF.F k).grading n
        by_cases h : i = k
        · subst k
          rw [DirectSum.of_eq_same]
          exact (F.ι i).map_grading n x hx
        · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
          exact ((UF.F k).grading n).zero_mem
      commute_d := by
        intro x
        change DirectSum.of K i (e i ((F.F i).d x)) =
          DGModule.directSumD (fun k => (UF.F k).toDGModule) (DirectSum.of K i (e i x))
        rw [hdir]
        exact congrArg (DirectSum.of K i) (Subtype.ext (LinearMap.congr_fun (F.ι i).map_d x)) }
  let j : ∀ i, F.F i ⟶ S := fun i =>
    (rebundleIso (F.F i)).inv ≫ Unbundled.bundleHom (Unbundled.module_isLawful (F.F i)) hS (jN i)
  have hbeta : ∀ (i : ℕ) (y : ↥(UF.F i).toSubmodule),
      DGModule.telescopeBetaFun UF
          (DirectSum.lof A.Aᵐᵒᵖ ℕ (fun k => ↥(UF.F k).toSubmodule) i y) = (y : P.M) :=
    fun i y => DirectSum.toModule_lof A.Aᵐᵒᵖ (M := fun k => ↥(UF.F k).toSubmodule)
      (N := (Unbundled.module P).carrier) (φ := fun k => (UF.F k).toSubmodule.subtype) i y
  have halpha : ∀ (i : ℕ) (y : K i),
      DGModule.telescopeAlphaFun UF (DirectSum.lof A.Aᵐᵒᵖ ℕ K i y) =
        DirectSum.lof A.Aᵐᵒᵖ ℕ K i y -
          DirectSum.lof A.Aᵐᵒᵖ ℕ K (i + 1) ((UF.inclHom i).toFun y) :=
    fun i y => DirectSum.toModule_lof A.Aᵐᵒᵖ (M := K) (N := ⨁ k, K k)
      (φ := fun k => DirectSum.lof A.Aᵐᵒᵖ ℕ K k -
        (DirectSum.lof A.Aᵐᵒᵖ ℕ K (k + 1)).comp (UF.inclHom k).toFun) i y
  refine ⟨S, j, a', b', ?_, ?_, ?_, ?_⟩
  · intro T g
    let q : ∀ i, K i →ₗ[R] T.M := fun i =>
      { toFun := fun x => (g i).toFun ((e i).symm x)
        map_add' := by intros; simp
        map_smul' := by
          intro r x
          change (g i).toFun ((e i).symm ((algebraMap R A.Aᵐᵒᵖ r) • x)) = _
          rw [(e i).symm.map_smul, IsScalarTower.algebraMap_smul A.Aᵐᵒᵖ r]
          exact (g i).toFun.map_smul r _ }
    have hq : ∀ (i : ℕ) (x : K i),
        DirectSum.toModule R ℕ T.M q (DirectSum.of K i x) = (g i).toFun ((e i).symm x) := by
      intro i x
      rw [← DirectSum.lof_eq_of R]
      exact DirectSum.toModule_lof R (φ := q) i x
    have hofsmul : ∀ (i : ℕ) (c : A.A) (y : K i),
        (MulOpposite.op c : A.Aᵐᵒᵖ) • DirectSum.of K i y =
          DirectSum.of K i ((MulOpposite.op c : A.Aᵐᵒᵖ) • y) := by
      intro i c y
      rw [← DirectSum.lof_eq_of A.Aᵐᵒᵖ, ← DirectSum.lof_eq_of A.Aᵐᵒᵖ, map_smul]
    have hsmul : ∀ (c : A.A) (x : ⨁ i, K i),
        DirectSum.toModule R ℕ T.M q ((MulOpposite.op c : A.Aᵐᵒᵖ) • x) =
          (MulOpposite.op c : A.Aᵐᵒᵖ) • DirectSum.toModule R ℕ T.M q x := by
      intro c x
      induction x using DirectSum.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | of i y =>
        rw [hofsmul, hq, hq]
        exact (congrArg (g i).toFun ((e i).symm.map_smul (MulOpposite.op c) y)).trans
          ((g i).map_smul ((e i).symm y) c)
      | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]
    have hgr : ∀ (n : ℤ) (x : ⨁ i, K i), (∀ i, x i ∈ (UF.F i).grading n) →
        DirectSum.toModule R ℕ T.M q x ∈ T.grading n := by
      intro n x hx
      rw [← DirectSum.sum_support_of x, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hq]
      exact (g i).map_grading n _
        (rangeEquiv_symm_mem_grading (F.ι i) (F.injective i) n (x i) (hx i))
    have hdd : ∀ x : ⨁ i, K i,
        DirectSum.toModule R ℕ T.M q
            (DGModule.directSumD (fun k => (UF.F k).toDGModule) x) =
          T.d (DirectSum.toModule R ℕ T.M q x) := by
      intro x
      induction x using DirectSum.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | of i y =>
        rw [hdir, hq, hq]
        have hi : (e i).symm ((UF.F i).toDGModule.d y) = (F.F i).d ((e i).symm y) :=
          (rangeIsoInv (F.ι i) (F.injective i)).commute_d y
        exact (congrArg (g i).toFun hi).trans (LinearMap.congr_fun (g i).map_d _)
      | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add]
    let h : S ⟶ T :=
      { toFun := DirectSum.toModule R ℕ T.M q
        map_smul := fun x c => hsmul c x
        map_grading := hgr
        map_d := LinearMap.ext hdd }
    have hh : ∀ i, j i ≫ h = g i := by
      intro i
      refine Hom.ext (LinearMap.ext fun x => ?_)
      change DirectSum.toModule R ℕ T.M q (DirectSum.of K i (e i x)) = _
      rw [hq]
      exact congrArg (g i).toFun ((e i).symm_apply_apply x)
    refine ⟨h, hh, fun h' hh' => ?_⟩
    refine Hom.ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => exact h'.toFun.map_zero.trans h.toFun.map_zero.symm
    | of i y =>
      obtain ⟨z, rfl⟩ := (e i).surjective y
      exact congrArg (fun f : F.F i ⟶ T => f.toFun z) ((hh' i).trans (hh i).symm)
    | add y z hy hz =>
      exact (h'.toFun.map_add y z).trans
        ((congrArg₂ (· + ·) hy hz).trans (h.toFun.map_add y z).symm)
  · intro i x
    exact (LinearMap.congr_fun hb ((j i).toFun x)).trans (hbeta i (e i x))
  · intro i x
    refine (LinearMap.congr_fun ha ((j i).toFun x)).trans ((halpha i (e i x)).trans ?_)
    refine congrArg₂ (· - ·) rfl (congrArg (DirectSum.lof A.Aᵐᵒᵖ ℕ K (i + 1)) ?_)
    change (e (i + 1)) ((F.incl i).toFun ((e i).symm (e i x))) = _
    rw [(e i).symm_apply_apply]
    rfl
  · refine
      { injective := hab.injective
        surjective := hab.surjective
        exact := Submodule.ext fun x => SetLike.ext_iff.mp hab.exact x
        admissibleMono := ?_
        admissibleEpi := ?_ }
    · obtain ⟨r, hr⟩ := hab.admissibleMono.2
      exact ⟨Unbundled.bundleGradedHom hS hS r, hr⟩
    · obtain ⟨s, hs⟩ := hab.admissibleEpi.2
      exact ⟨{ toFun := (Unbundled.bundleGradedHom hP hS s).toFun
               map_smul := (Unbundled.bundleGradedHom hP hS s).map_smul
               map_grading := (Unbundled.bundleGradedHom hP hS s).map_grading }, hs⟩

end DifferentialGradedModule

end
