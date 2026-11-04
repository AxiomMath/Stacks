module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryComp
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryHomotopyCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHom

/-!
# The internal hom functor of a differential graded bimodule

Let `A` and `B` be differential graded algebras over a commutative ring `R` and let `N` be a
right differential graded `B`-module carrying a compatible left differential graded `A`-action.
Sending a right differential graded `B`-module `P` to the internal hom `Hom^•_B(N, P)` is a
functor of differential graded categories from right differential graded `B`-modules to right
differential graded `A`-modules: a homogeneous right-`B`-linear map `X → Y` acts by
postcomposition. It therefore also induces a functor on the ordinary categories of differential
graded modules and a functor on their homotopy categories.

## Main definitions

* `DifferentialGradedModule.homModulePresentation`: a presentation of the internal hom
  `Hom^•_B(N, P)`, for each `P`.
* `DifferentialGradedModule.HomDGFunctorData`: data presenting the internal hom functor — the
  presentations of its values together with the differential graded functor and the
  postcomposition formula for its action on homogeneous maps.
* `DifferentialGradedModule.homDGFunctorData`: the construction of that data.
* `DifferentialGradedModule.homModuleFunctor` and
  `DifferentialGradedModule.homHomotopyCategoryFunctor`: the induced functors on the category of
  differential graded modules and on its homotopy category.

## Implementation notes

*The values are only characterized up to a presentation.* The internal hom has no canonical
underlying module, so the functor is described by a `HomDGFunctorData`: it carries, for each `P`,
a `HomModuleData` presenting `Hom^•_B(N, P)`, an equality identifying the functor's value with
that presentation's module, and the formula saying that the functor's action on a homogeneous map
is postcomposition read through the presentations. That last formula is a `HEq` because its two
sides live in the two modules identified by `obj_eq`.

*Postcomposition is defined on the whole module by its homogeneous pieces.* `homPostcomp` is
assembled from the degree-wise postcompositions along the direct-sum decomposition of the source
presentation; the proofs that it is additive, `R`-linear and compatible with the right `A`-action
all reduce by `DirectSum.Decomposition.inductionOn` to the degree-wise statement, where the
compatibility with the `A`-action is exactly the `map_smul` field of the two presentations.

*The ordinary functors are transported, not rebuilt.* The category of complexes and the homotopy
category of the differential graded category of differential graded `B`-modules are canonically
equivalent to the category of differential graded `B`-modules and to its homotopy category
(`dgCategoryCompEquivalence`, `homotopyCategoryEquivalence`); the induced functors are the
differential graded functor's `onComp` and `onK` conjugated by those equivalences. Compatibility
with the internal hom is therefore up to natural isomorphism rather than on the nose.

## References

* [Stacks Project, Tag 0FQQ](https://stacks.math.columbia.edu/tag/0FQQ)
-/

@[expose] public section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R]
variable (A B : DifferentialGradedAlgebra R)
variable (N : DifferentialGradedModule B)
variable (L : BimoduleStructure A B N)

/-- A presentation of the internal hom `Hom^•_B(N, P)` as a right differential graded
`A`-module. -/
noncomputable def homModulePresentation (P : DifferentialGradedModule B) :
    HomModuleData A B N P L :=
  (shiftHomModuleIso A B N P L 0).choose

/-- Postcomposition with a degree-`n` homogeneous map `X → Y`, as an `R`-linear map from
degree-`p` to degree-`n + p` homogeneous maps out of `N`. -/
def homogeneousMapPostcompₗ {X Y : DifferentialGradedModule B} {n : ℤ} (p : ℤ)
    (f : HomogeneousMap B X Y n) :
    HomogeneousMap B N X p →ₗ[R] HomogeneousMap B N Y (n + p) where
  toFun g := homogeneousMapComp B (rfl : n + p = n + p) f g
  map_add' g h := by
    apply Subtype.ext
    ext x
    simp [homogeneousMapComp]
  map_smul' r g := by
    apply Subtype.ext
    ext x
    simp [homogeneousMapComp]

/-- Postcomposition with a degree-`n` homogeneous map, on the degree-`p` piece of a presentation
of the internal hom. -/
noncomputable def homPostcompComponent {X Y : DifferentialGradedModule B}
    (HX : HomModuleData A B N X L) (HY : HomModuleData A B N Y L)
    (n p : ℤ) (f : HomogeneousMap B X Y n) : HX.module.grading p →ₗ[R] HY.module.M :=
  (HY.module.grading (n + p)).subtype.comp
    ((HY.homogeneousEquiv (n + p)).symm.toLinearMap.comp
      ((homogeneousMapPostcompₗ B N p f).comp (HX.homogeneousEquiv p).toLinearMap))

/-- Postcomposition with a degree-`n` homogeneous map `X → Y`, as an `R`-linear map between
presentations of the internal homs out of `N`. -/
noncomputable def homPostcomp {X Y : DifferentialGradedModule B}
    (HX : HomModuleData A B N X L) (HY : HomModuleData A B N Y L)
    (n : ℤ) (f : HomogeneousMap B X Y n) : HX.module.M →ₗ[R] HY.module.M :=
  (DirectSum.toModule R ℤ HY.module.M fun p =>
    homPostcompComponent A B N L HX HY n p f).comp
    (DirectSum.decomposeLinearEquiv HX.module.grading).toLinearMap

private theorem homPostcomp_apply {X Y : DifferentialGradedModule B}
    (HX : HomModuleData A B N X L) (HY : HomModuleData A B N Y L)
    (n p : ℤ) (f : HomogeneousMap B X Y n) (g : HX.module.grading p) :
    homPostcomp A B N L HX HY n f (g : HX.module.M) =
      ((HY.homogeneousEquiv (n + p)).symm
        (homogeneousMapComp B (rfl : n + p = n + p) f (HX.homogeneousEquiv p g)) :
          HY.module.M) := by
  show (DirectSum.toModule R ℤ HY.module.M
    (fun i => homPostcompComponent A B N L HX HY n i f))
    ((DirectSum.decomposeLinearEquiv HX.module.grading) (g : HX.module.M)) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
  rfl

/-- Postcomposition with a degree-`n` homogeneous map raises degrees by `n`. -/
theorem homPostcomp_mem {X Y : DifferentialGradedModule B}
    (HX : HomModuleData A B N X L) (HY : HomModuleData A B N Y L)
    (n p : ℤ) (f : HomogeneousMap B X Y n) {x : HX.module.M}
    (hx : x ∈ HX.module.grading p) :
    homPostcomp A B N L HX HY n f x ∈ HY.module.grading (p + n) := by
  rw [homPostcomp_apply A B N L HX HY n p f ⟨x, hx⟩]
  simpa only [add_comm p n] using
    ((HY.homogeneousEquiv (n + p)).symm
      (homogeneousMapComp B rfl f (HX.homogeneousEquiv p ⟨x, hx⟩))).property

private theorem homogeneousEquiv_cast_apply {X : DifferentialGradedModule B}
    (H : HomModuleData A B N X L) {i j : ℤ} (h : i = j) (g : H.module.grading i) (x : N.M) :
    (H.homogeneousEquiv i g).1 x = (H.homogeneousEquiv j (h ▸ g)).1 x := by cases h; rfl

private theorem grading_cast_coe {P : DifferentialGradedModule A} {i j : ℤ} (h : i = j)
    (x : P.grading i) : ((h ▸ x : P.grading j) : P.M) = x := by cases h; rfl

private theorem homogeneousEquiv_symm_cast {X : DifferentialGradedModule B}
    (H : HomModuleData A B N X L) {i j : ℤ} (h : i = j) (f : HomogeneousMap B N X i) :
    ((H.homogeneousEquiv i).symm f : H.module.M) =
      ((H.homogeneousEquiv j).symm (h ▸ f) : H.module.M) := by cases h; rfl

private theorem homogeneousMap_cast_apply {X Y : DifferentialGradedModule B} {i j : ℤ}
    (h : i = j) (f : HomogeneousMap B X Y i) (x : X.M) :
    (h ▸ f : HomogeneousMap B X Y j).1 x = f.1 x := by cases h; rfl

/-- Postcomposition commutes with the right action of a homogeneous element of `A`. -/
theorem homPostcomp_op_smul {X Y : DifferentialGradedModule B}
    (HX : HomModuleData A B N X L) (HY : HomModuleData A B N Y L)
    (n p m : ℤ) (f : HomogeneousMap B X Y n)
    (g : HX.module.grading p) (a : A.grading m) :
    homPostcomp A B N L HX HY n f (MulOpposite.op (a : A.A) • (g : HX.module.M)) =
      MulOpposite.op (a : A.A) • homPostcomp A B N L HX HY n f (g : HX.module.M) := by
  let ga : HX.module.grading (p + m) :=
    ⟨MulOpposite.op (a : A.A) • (g : HX.module.M),
      HX.module.smul_mem p m (g : HX.module.M) (a : A.A) g.property a.property⟩
  let z : HY.module.grading (n + p) :=
    ⟨homPostcomp A B N L HX HY n f (g : HX.module.M),
      by simpa [add_comm] using homPostcomp_mem A B N L HX HY n p f g.property⟩
  let left : HY.module.grading (n + (p + m)) :=
    ⟨homPostcomp A B N L HX HY n f (ga : HX.module.M),
      by simpa [add_assoc, add_comm, add_left_comm] using
        homPostcomp_mem A B N L HX HY n (p + m) f ga.property⟩
  let right : HY.module.grading (n + (p + m)) :=
    ⟨MulOpposite.op (a : A.A) • (z : HY.module.M), by
      simpa [add_assoc] using
        HY.module.smul_mem (n + p) m (z : HY.module.M) (a : A.A) z.property a.property⟩
  have hsub : left = right := by
    apply (HY.homogeneousEquiv (n + (p + m))).injective
    apply Subtype.ext
    ext x
    induction x using DirectSum.Decomposition.inductionOn N.grading with
    | zero => simp
    | @homogeneous q x =>
      let ax : N.grading (q + m) := (L.1.action m a).v q (q + m) (by omega) x
      have hright :
          ((HY.homogeneousEquiv (n + (p + m))) right).1 x =
            ((HY.homogeneousEquiv (n + p) z).1 ax) := by
        have idx : n + (p + m) = n + p + m := by omega
        calc
          ((HY.homogeneousEquiv (n + (p + m))) right).1 x =
              ((HY.homogeneousEquiv (n + p + m)) (idx ▸ right)).1 x :=
            homogeneousEquiv_cast_apply A B N L HY idx right x
          _ = ((HY.homogeneousEquiv (n + p) z).1 ax) := by
            rw [show (idx ▸ right : HY.module.grading (n + p + m)) =
                ⟨MulOpposite.op (a : A.A) • (z : HY.module.M),
                  HY.module.smul_mem (n + p) m (z : HY.module.M) (a : A.A)
                    z.property a.property⟩ from Subtype.ext (grading_cast_coe A idx right)]
            simpa [ax] using HY.map_smul (n + p) m q z a x
      calc
        ((HY.homogeneousEquiv (n + (p + m))) left).1 x =
            (homogeneousMapComp B (rfl : n + (p + m) = n + (p + m)) f
              (HX.homogeneousEquiv (p + m) ga)).1 x := by
          simp [left, homPostcomp_apply]
        _ = f.1 ((HX.homogeneousEquiv p g).1 ax) := by
          simpa [homogeneousMapComp, ga, ax] using congrArg f.1 (HX.map_smul p m q g a x)
        _ = (HY.homogeneousEquiv (n + p) z).1 ax := by
          simp [z, homPostcomp_apply, homogeneousMapComp]
        _ = ((HY.homogeneousEquiv (n + (p + m))) right).1 x := hright.symm
    | add x y hx hy => simp only [map_add, hx, hy]
  exact congrArg Subtype.val hsub

/-- Postcomposition with a degree-`n` homogeneous map `X → Y`, as a degree-`n` homogeneous map
between presentations of the internal homs out of `N`. -/
noncomputable def homPostcompHomogeneousMap {X Y : DifferentialGradedModule B}
    (HX : HomModuleData A B N X L) (HY : HomModuleData A B N Y L)
    (n : ℤ) (f : HomogeneousMap B X Y n) :
    HomogeneousMap A HX.module HY.module n := by
  refine ⟨homPostcomp A B N L HX HY n f,
    fun p x hx => homPostcomp_mem A B N L HX HY n p f hx, fun a x => ?_⟩
  induction x using DirectSum.Decomposition.inductionOn HX.module.grading with
  | zero => simp [homPostcomp]
  | @homogeneous p g =>
    induction a using DirectSum.Decomposition.inductionOn A.grading with
    | zero => simp
    | @homogeneous m a => exact homPostcomp_op_smul A B N L HX HY n p m f g a
    | add a b ha hb =>
      simpa only [map_add, add_smul, MulOpposite.op_add] using congrArg₂ (· + ·) ha hb
  | add x y hx hy =>
    simpa only [map_add, smul_add] using congrArg₂ (· + ·) hx hy

/-- On a homogeneous element `g` of degree `p`, `homPostcompHomogeneousMap` composes the
homogeneous map corresponding to `g` with `f`. -/
theorem homPostcompHomogeneousMap_apply {X Y : DifferentialGradedModule B}
    (HX : HomModuleData A B N X L) (HY : HomModuleData A B N Y L)
    (n p : ℤ) (f : HomogeneousMap B X Y n) (g : HX.module.grading p) :
    (homPostcompHomogeneousMap A B N L HX HY n f).1 (g : HX.module.M) =
      ((HY.homogeneousEquiv (n + p)).symm
        (homogeneousMapComp B (rfl : n + p = n + p) f (HX.homogeneousEquiv p g)) :
          HY.module.M) :=
  homPostcomp_apply A B N L HX HY n p f g

/-- Postcomposition `homPostcomp` is additive in the homogeneous map `f`. -/
theorem homPostcomp_add {X Y : DifferentialGradedModule B}
    (HX : HomModuleData A B N X L) (HY : HomModuleData A B N Y L)
    (n : ℤ) (f g : HomogeneousMap B X Y n) :
    homPostcomp A B N L HX HY n (f + g) =
      homPostcomp A B N L HX HY n f + homPostcomp A B N L HX HY n g := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn HX.module.grading with
  | zero => simp
  | @homogeneous p x =>
    let left : HY.module.grading (n + p) :=
      ⟨homPostcomp A B N L HX HY n (f + g) x,
        by simpa [add_comm] using homPostcomp_mem A B N L HX HY n p (f + g) x.property⟩
    let right₁ : HY.module.grading (n + p) :=
      ⟨homPostcomp A B N L HX HY n f x,
        by simpa [add_comm] using homPostcomp_mem A B N L HX HY n p f x.property⟩
    let right₂ : HY.module.grading (n + p) :=
      ⟨homPostcomp A B N L HX HY n g x,
        by simpa [add_comm] using homPostcomp_mem A B N L HX HY n p g x.property⟩
    have h : left = right₁ + right₂ := by
      apply (HY.homogeneousEquiv (n + p)).injective
      apply Subtype.ext
      ext y
      simp only [left, right₁, right₂]
      rw [map_add]
      simp [homPostcomp_apply, homogeneousMapComp]
    exact congrArg (fun z : HY.module.grading (n + p) => (z : HY.module.M)) h
  | add x y hx hy => rw [map_add, hx, hy, map_add]

/-- Postcomposition `homPostcomp` commutes with scalar multiplication by `r : R` on the
homogeneous map `f`. -/
theorem homPostcomp_smul {X Y : DifferentialGradedModule B}
    (HX : HomModuleData A B N X L) (HY : HomModuleData A B N Y L)
    (n : ℤ) (r : R) (f : HomogeneousMap B X Y n) :
    homPostcomp A B N L HX HY n (r • f) = r • homPostcomp A B N L HX HY n f := by
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn HX.module.grading with
  | zero => simp
  | @homogeneous p x =>
    let left : HY.module.grading (n + p) :=
      ⟨homPostcomp A B N L HX HY n (r • f) x,
        by simpa [add_comm] using homPostcomp_mem A B N L HX HY n p (r • f) x.property⟩
    let right₁ : HY.module.grading (n + p) :=
      ⟨homPostcomp A B N L HX HY n f x,
        by simpa [add_comm] using homPostcomp_mem A B N L HX HY n p f x.property⟩
    have h : left = r • right₁ := by
      apply (HY.homogeneousEquiv (n + p)).injective
      apply Subtype.ext
      ext y
      simp only [left, right₁]
      rw [map_smul]
      simp [homPostcomp_apply, homogeneousMapComp]
    exact congrArg (fun z : HY.module.grading (n + p) => (z : HY.module.M)) h
  | add x y hx hy => rw [map_add, hx, hy, map_add, LinearMap.smul_apply]

/-- Data presenting the internal hom functor of a differential graded bimodule: a presentation of
`Hom^•_B(N, P)` for each `P`, a differential graded functor whose values are those presentations'
modules, and the formula identifying its action on a homogeneous map with postcomposition. -/
structure HomDGFunctorData (A B : DifferentialGradedAlgebra R)
    (N : DifferentialGradedModule B) (L : BimoduleStructure A B N) where
  /-- A presentation of the internal hom out of `N` with values in `P`. -/
  presentation (P : DifferentialGradedModule B) : HomModuleData A B N P L
  /-- The differential graded functor. -/
  functor : DGCategory.DGFunctor (dgCategory B) (dgCategory A)
  /-- Its value at `P` is the module of the chosen presentation. -/
  obj_eq (P : DifferentialGradedModule B) : functor.obj P = (presentation P).module
  /-- Its action on a homogeneous map is postcomposition, read through the presentations. -/
  map_apply {X Y : DifferentialGradedModule B} {n : ℤ} (f : HomogeneousMap B X Y n) (p : ℤ)
      (g : (presentation X).module.grading p) :
    HEq ((functor.map f).1 ((obj_eq X).symm ▸ (g : (presentation X).module.M)))
      (((presentation Y).homogeneousEquiv (n + p)).symm
        (homogeneousMapComp B (rfl : n + p = n + p) f
          ((presentation X).homogeneousEquiv p g))).1

/-- **Stacks 0FQQ.** The internal hom functor of a differential graded bimodule, as a functor of
differential graded categories. -/
@[stacks 0FQQ "the DG functor"]
noncomputable def homDGFunctorData : HomDGFunctorData A B N L := by
  classical
  let pres := fun P => homModulePresentation A B N L P
  let F : DGCategory.DGFunctor (dgCategory B) (dgCategory A) :=
    { obj := fun P => (pres P).module
      map := fun {X Y n} f => homPostcompHomogeneousMap A B N L (pres X) (pres Y) n f
      map_add := fun {X Y n} f g =>
        Subtype.ext (homPostcomp_add A B N L (pres X) (pres Y) n f g)
      map_smul := fun {X Y n} r f =>
        Subtype.ext (homPostcomp_smul A B N L (pres X) (pres Y) n r f)
      map_d := by
        intro X Y n f
        apply Subtype.ext
        ext x
        induction x using DirectSum.Decomposition.inductionOn (pres X).module.grading with
        | zero => simp
        | @homogeneous p x =>
          simp only [dgCategory_d_val, LinearMap.sub_apply, LinearMap.coe_comp,
            Function.comp_apply, LinearMap.smul_apply]
          let g := (pres X).homogeneousEquiv p x
          let z : (pres Y).module.grading (n + p) :=
            ⟨homPostcomp A B N L (pres X) (pres Y) n f x,
              by simpa [add_comm] using
                homPostcomp_mem A B N L (pres X) (pres Y) n p f x.property⟩
          let xdiff : (pres X).module.grading (p + 1) :=
            (pres X).module.gradedDifferential p x
          have hX := (pres X).map_d p x
          have hY := (pres Y).map_d (n + p) z
          have hYval : (pres Y).module.d (z : (pres Y).module.M) =
              (((pres Y).homogeneousEquiv (n + p + 1)).symm
                (homogeneousMapDifferential B
                  (homogeneousMapComp B (rfl : n + p = n + p) f g)) :
                    (pres Y).module.M) := by
            have h := congrArg ((pres Y).homogeneousEquiv (n + p + 1)).symm hY
            have hv := congrArg (fun t : (pres Y).module.grading (n + p + 1) =>
              (t : (pres Y).module.M)) h
            simpa [z, g, homPostcomp_apply] using hv
          rw [homPostcompHomogeneousMap_apply,
            show (homPostcompHomogeneousMap A B N L (pres X) (pres Y) n f).1
              (x : (pres X).module.M) = (z : (pres Y).module.M) from rfl, hYval,
            show (pres X).module.d (x : (pres X).module.M) = (xdiff : (pres X).module.M) by
              simp [xdiff],
            homPostcompHomogeneousMap_apply]
          have idxL : n + 1 + p = n + p + 1 := by omega
          have idxR : n + (p + 1) = n + p + 1 := by omega
          let c : HomogeneousMap B N Y (n + p) := homogeneousMapComp B rfl f g
          let cL : HomogeneousMap B N Y (n + 1 + p) :=
            homogeneousMapComp B (by omega) ((dgCategory B).d f) g
          let cR : HomogeneousMap B N Y (n + (p + 1)) :=
            homogeneousMapComp B (by omega) f ((dgCategory B).d g)
          have hleib : homogeneousMapDifferential B c =
              (dgCategory B).comp (by omega) ((dgCategory B).d f) g +
                ((-1 : R) ^ n.natAbs) •
                  (dgCategory B).comp (by omega) f ((dgCategory B).d g) := by
            change (dgCategory B).d ((dgCategory B).comp rfl f g) = _
            exact (dgCategory B).leibniz (rfl : n + p = n + p) f g
          have hcL : (idxL ▸ cL : HomogeneousMap B N Y (n + p + 1)) =
              (dgCategory B).comp (by omega) ((dgCategory B).d f) g := by
            apply Subtype.ext
            ext y
            rw [homogeneousMap_cast_apply B idxL cL]
            simp [cL, homogeneousMapComp, dgCategory_comp_val]
          have hcR : (idxR ▸ cR : HomogeneousMap B N Y (n + p + 1)) =
              (dgCategory B).comp (by omega) f ((dgCategory B).d g) := by
            apply Subtype.ext
            ext y
            rw [homogeneousMap_cast_apply B idxR cR]
            simp [cR, homogeneousMapComp, dgCategory_comp_val]
          have hvals :
              (((pres Y).homogeneousEquiv (n + p + 1)).symm
                (homogeneousMapDifferential B c) : (pres Y).module.M) =
              (((pres Y).homogeneousEquiv (n + p + 1)).symm
                ((dgCategory B).comp (by omega) ((dgCategory B).d f) g) :
                  (pres Y).module.M) +
                ((-1 : R) ^ n.natAbs) •
                  (((pres Y).homogeneousEquiv (n + p + 1)).symm
                    ((dgCategory B).comp (by omega) f ((dgCategory B).d g)) :
                      (pres Y).module.M) := by
            simpa using congrArg
              (fun q : HomogeneousMap B N Y (n + p + 1) =>
                (((pres Y).homogeneousEquiv (n + p + 1)).symm q : (pres Y).module.M)) hleib
          rw [homogeneousEquiv_symm_cast A B N L (pres Y) idxL cL, hcL, hX]
          let cRin : HomogeneousMap B N Y (n + (p + 1)) :=
            homogeneousMapComp B rfl f (homogeneousMapDifferential B g)
          have hRin : (idxR ▸ cRin : HomogeneousMap B N Y (n + p + 1)) =
              (idxR ▸ cR : HomogeneousMap B N Y (n + p + 1)) := Subtype.ext rfl
          rw [homogeneousEquiv_symm_cast A B N L (pres Y) idxR cRin, hRin, hcR, hvals,
            show (-1 : R) ^ n.natAbs = DifferentialGraded.gradedSign R n from rfl]
          abel
        | add x y hx hy => rw [map_add, hx, hy, map_add]
      map_comp := by
        intro X Y Z m n k h g f
        subst k
        apply Subtype.ext
        ext x
        induction x using DirectSum.Decomposition.inductionOn (pres X).module.grading with
        | zero => simp
        | @homogeneous p x =>
          have idx : m + n + p = m + (n + p) := by omega
          let c₁ : HomogeneousMap B N Z (m + n + p) :=
            homogeneousMapComp B rfl (homogeneousMapComp B rfl g f)
              ((pres X).homogeneousEquiv p x)
          let c₂ : HomogeneousMap B N Z (m + (n + p)) :=
            homogeneousMapComp B rfl g
              (homogeneousMapComp B rfl f ((pres X).homogeneousEquiv p x))
          have hc : (idx ▸ c₁ : HomogeneousMap B N Z (m + (n + p))) = c₂ := by
            apply Subtype.ext
            ext y
            rw [homogeneousMap_cast_apply B idx c₁]
            simp [c₁, c₂, homogeneousMapComp, LinearMap.comp_assoc]
          have hcomp : (dgCategory B).comp (rfl : m + n = m + n) g f =
              homogeneousMapComp B (rfl : m + n = m + n) g f :=
            Subtype.ext (by simp [dgCategory_comp_val, homogeneousMapComp_val])
          rw [hcomp]
          simp only [homPostcompHomogeneousMap_apply, dgCategory_comp_val]
          rw [homogeneousEquiv_symm_cast A B N L (pres Z) idx c₁, hc]
          let fx : (pres Y).module.grading (n + p) :=
            ⟨(homPostcompHomogeneousMap A B N L (pres X) (pres Y) n f).1 x,
              by simpa [add_comm] using
                (homPostcompHomogeneousMap A B N L (pres X) (pres Y) n f).property.1 p _
                  x.property⟩
          have houter :
              (homPostcompHomogeneousMap A B N L (pres Y) (pres Z) m g).1
                  (fx : (pres Y).module.M) =
                ((pres Z).homogeneousEquiv (m + (n + p))).symm c₂ := by
            rw [homPostcompHomogeneousMap_apply]
            simp [fx, homPostcompHomogeneousMap_apply, c₂, homogeneousMapComp]
          exact houter.symm
        | add x y hx hy => simp [hx, hy]
      map_id := by
        intro X
        apply Subtype.ext
        ext x
        induction x using DirectSum.Decomposition.inductionOn (pres X).module.grading with
        | zero => simp
        | @homogeneous p x =>
          simp only [dgCategory_id_val]
          rw [homPostcompHomogeneousMap_apply]
          have idx : (0 : ℤ) + p = p := by omega
          let c : HomogeneousMap B N X (0 + p) :=
            homogeneousMapComp B rfl ((dgCategory B).id X) ((pres X).homogeneousEquiv p x)
          have hc : (idx ▸ c : HomogeneousMap B N X p) = (pres X).homogeneousEquiv p x := by
            apply Subtype.ext
            ext y
            rw [homogeneousMap_cast_apply B idx c]
            simp [c, homogeneousMapComp, dgCategory_id_val]
          let x₀ : (pres X).module.grading (0 + p) := idx.symm ▸ x
          have hxval : x₀.1 = x.1 := by simpa [x₀] using grading_cast_coe A idx.symm x
          have hcval : (((pres X).homogeneousEquiv (0 + p)).symm c : (pres X).module.M) =
              x₀.1 := by
            rw [homogeneousEquiv_symm_cast A B N L (pres X) idx c, hc]
            simp only [LinearEquiv.symm_apply_apply]
            exact hxval.symm
          simpa [c, homogeneousMapComp, x₀, hxval] using hcval
        | add x y hx hy => simp [hx, hy] }
  exact ⟨pres, F, fun _ => rfl, fun f p g =>
    heq_of_eq (homPostcompHomogeneousMap_apply A B N L (pres _) (pres _) _ p f g)⟩

/-- **Stacks 0FQQ.** The internal hom functor on the categories of differential graded
modules. -/
@[stacks 0FQQ "the functor on DG modules",
  stacks 09LG "the induced functor `Mod_(B,d) → Mod_(A,d)`"]
noncomputable def homModuleFunctor :
    DifferentialGradedModule B ⥤ DifferentialGradedModule A :=
  (dgCategoryCompEquivalence B).1.inverse ⋙
    (homDGFunctorData A B N L).functor.onComp ⋙ (dgCategoryCompEquivalence A).1.functor

/-- **Stacks 0FQQ.** The internal hom functor on the homotopy categories of differential graded
modules. -/
@[stacks 0FQQ "the functor on homotopy categories"]
noncomputable def homHomotopyCategoryFunctor :
    HomotopyCategory B ⥤ HomotopyCategory A :=
  (homotopyCategoryEquivalence B).functor ⋙
    (homDGFunctorData A B N L).functor.onK ⋙ (homotopyCategoryEquivalence A).inverse

end DifferentialGradedModule
