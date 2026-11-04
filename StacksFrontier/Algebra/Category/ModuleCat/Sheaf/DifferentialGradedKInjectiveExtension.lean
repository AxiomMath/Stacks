module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedForgetLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeLimits

/-!
# Extension from acyclic differential graded modules into injectives

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. A right differential graded `A`-module that is both K-injective and graded
injective has the extension property for morphisms out of an acyclic right differential graded
module across a monomorphism.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_extension_of_acyclic_of_mono` extends a
  morphism out of an acyclic right differential graded module across a monomorphism.

## Implementation notes

The injective map of the source is a categorical monomorphism, and the extension is a morphism
of right differential graded modules whose composite with it is the given morphism.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring and the algebra pieces are independent;
a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FSW](https://stacks.math.columbia.edu/tag/0FSW)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

private theorem gradedCast_map {ι κ : Type*} (T : ι → Type*) (S : ι → κ → Type*)
    (f : ∀ i, ∀ k, T i → S i k) {i j : ι} (h : i = j) (k : κ) (x : T i) :
    f j k (gradedCast T h x) =
      gradedCast (fun q => S q k) h (f i k x) := by
  cases h
  rfl

private theorem gradedCast_mul {A : DifferentialGradedAlgebra.{t, a} R}
    (N : DifferentialGradedModule.{t, a, m} A) {i j m : ℤ} (h : i = j)
    (U : Cᵒᵖ) (x : (N.complex.X i).val.obj U)
    (a : (A.complex.X m).val.obj U) :
    ((N.mul j m).app U
      (gradedCast (fun q => (N.complex.X q).val.obj U) h x)) a =
      gradedCast (fun q => (N.complex.X q).val.obj U)
        (congrArg (fun q : ℤ => q + m) h) (((N.mul i m).app U x) a) := by
  cases h
  rfl

private theorem gradedCast_d (K : CochainComplex (SheafOfModules.{m} R) ℤ)
    {i j : ℤ} (h : i = j) (U : Cᵒᵖ) (x : (K.X i).val.obj U) :
    (K.d j (j + 1)).val.app U
        (gradedCast (fun q => (K.X q).val.obj U) h x) =
      gradedCast (fun q => (K.X q).val.obj U)
        (congrArg (fun q : ℤ => q + 1) h)
        ((K.d i (i + 1)).val.app U x) := by
  cases h
  rfl

private theorem gradedModule_smul_cast_heq
    {B : GradedAlgebra.{t, a} R}
    (N : GradedModule.{t, a, m} B) {n n' m : ℤ}
    (h : n = n') (U : Cᵒᵖ) (x : (N.piece n).val.obj U)
    (a : (B.piece m).val.obj U) :
    HEq (N.smul n' m U (gradedCast (fun q => (N.piece q).val.obj U) h x) a)
      ((N.smul n m U x) a) := by
  cases h
  rfl

private theorem gradedCast_section_map (F : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : (F i).val.obj U) :
    (F j).val.map f (gradedCast (fun q => (F q).val.obj U) h x) =
      gradedCast (fun q => (F q).val.obj V) h ((F i).val.map f x) := by
  cases h
  rfl

/-- The graded module `N` with its degrees shifted by `k`: its piece in degree `n` is the piece of
`N` in degree `n + k`. -/
private def gradedShift {B : GradedAlgebra.{t, a} R}
    (N : GradedModule.{t, a, m} B) (k : ℤ) :
    GradedModule.{t, a, m} B where
  piece n := N.piece (n + k)
  smul n m U := {
    toFun := fun x => {
      toFun := fun a =>
        gradedCast (fun q => (N.piece q).val.obj U)
          (show (n + k) + m = (n + m) + k by lia)
          ((N.smul (n + k) m U x) a)
      map_zero' := by
        rw [map_zero]
        exact gradedCast_zero _ _
      map_add' := by
        intro a b
        rw [map_add]
        exact gradedCast_add (fun q => (N.piece q).val.obj U)
          (show (n + k) + m = (n + m) + k by lia)
          ((N.smul (n + k) m U x) a) ((N.smul (n + k) m U x) b) }
    map_zero' := by
      ext a
      rw [map_zero]
      exact gradedCast_zero (fun q => (N.piece q).val.obj U)
        (show (n + k) + m = (n + m) + k by lia)
    map_add' := by
      intro x y
      ext a
      rw [map_add]
      exact gradedCast_add (fun q => (N.piece q).val.obj U)
        (show (n + k) + m = (n + m) + k by lia)
        ((N.smul (n + k) m U x) a) ((N.smul (n + k) m U y) a) }
  smul_smul_left := by
    intro n m U r x a
    dsimp only [DFunLike.coe, AddMonoidHom.coe_mk, AddHom.coe_mk, Function.comp_apply]
    change gradedCast (fun q => (N.piece q).val.obj U)
      (show (n + k) + m = (n + m) + k by lia)
      ((N.smul (n + k) m U (r • x)) a) = _
    rw [N.smul_smul_left]
    exact (gradedCast_smul (fun q => (N.piece q).val.obj U)
      (show (n + k) + m = (n + m) + k by lia) r ((N.smul (n + k) m U x) a))
  smul_smul_right := by
    intro n m U r x a
    dsimp only [DFunLike.coe, AddMonoidHom.coe_mk, AddHom.coe_mk, Function.comp_apply]
    change gradedCast (fun q => (N.piece q).val.obj U)
      (show (n + k) + m = (n + m) + k by lia)
      ((N.smul (n + k) m U x) (r • a)) = _
    rw [N.smul_smul_right]
    exact (gradedCast_smul (fun q => (N.piece q).val.obj U)
      (show (n + k) + m = (n + m) + k by lia) r ((N.smul (n + k) m U x) a))
  smul_naturality := by
    intro n m U V f x a
    change (N.piece ((n + m) + k)).val.map f
        (gradedCast (fun q => (N.piece q).val.obj U)
          (show (n + k) + m = (n + m) + k by lia)
          ((N.smul (n + k) m U x) a)) =
      gradedCast (fun q => (N.piece q).val.obj V)
        (show (n + k) + m = (n + m) + k by lia)
        ((N.smul (n + k) m V ((N.piece (n + k)).val.map f x)
          ((B.piece m).val.map f a)))
    calc
      _ = gradedCast (fun q => (N.piece q).val.obj V)
          (show (n + k) + m = (n + m) + k by lia)
          ((N.piece ((n + k) + m)).val.map f ((N.smul (n + k) m U x) a)) :=
        (gradedCast_section_map N.piece
          (show (n + k) + m = (n + m) + k by lia) f _)
      _ = _ := congrArg (gradedCast (fun q => (N.piece q).val.obj V)
        (show (n + k) + m = (n + m) + k by lia))
        (N.smul_naturality (n + k) m f x a)
  smul_mul := by
    intro n i j U x a b
    dsimp only [DFunLike.coe, AddMonoidHom.coe_mk, AddHom.coe_mk, Function.comp_apply]
    change HEq (gradedCast (fun q => (N.piece q).val.obj U)
      (show ((n + i) + k) + j = ((n + i) + j) + k by lia)
      ((N.smul ((n + i) + k) j U
        (gradedCast (fun q => (N.piece q).val.obj U)
          (show (n + k) + i = (n + i) + k by lia)
          ((N.smul (n + k) i U x) a)) b)))
      (gradedCast (fun q => (N.piece q).val.obj U)
        (show (n + k) + (i + j) = (n + (i + j)) + k by lia)
        ((N.smul (n + k) (i + j) U x) ((B.mul i j).app U a b)))
    refine HEq.trans (gradedCast_heq (fun q => (N.piece q).val.obj U)
      (show ((n + i) + k) + j = ((n + i) + j) + k by lia) _) ?_
    refine HEq.trans (gradedModule_smul_cast_heq N
      (show (n + k) + i = (n + i) + k by lia) U _ b) ?_
    refine HEq.trans (N.smul_mul (n + k) i j U x a b) ?_
    exact (gradedCast_heq (fun q => (N.piece q).val.obj U)
      (show (n + k) + (i + j) = (n + (i + j)) + k by lia)
      ((N.smul (n + k) (i + j) U x) ((B.mul i j).app U a b))).symm
  smul_one := by
    intro n U x
    dsimp only [DFunLike.coe, AddMonoidHom.coe_mk, AddHom.coe_mk, Function.comp_apply]
    let y := (((N.smul (n + k) 0 U).toFun x).toFun (B.one.eval U))
    have hcast : HEq
        (gradedCast (fun q => (N.piece q).val.obj U)
          (show (n + k) + 0 = (n + 0) + k by lia) y) y :=
      gradedCast_heq (fun q => (N.piece q).val.obj U)
        (show (n + k) + 0 = (n + 0) + k by lia) y
    have hone : HEq y x := by
      dsimp [y]
      exact N.smul_one (n + k) U x
    dsimp [y] at hcast hone ⊢
    have hfinal : HEq
        (gradedCast (fun q => (N.piece q).val.obj U)
          (show (n + k) + 0 = (n + 0) + k by lia)
          (((N.smul (n + k) 0 U).toFun x).toFun (B.one.eval U))) x :=
      HEq.trans hcast hone
    simpa only [DFunLike.coe, AddMonoidHom.coe_mk, AddHom.coe_mk,
      Function.comp_apply] using hfinal

private theorem gradedShift_smul_cast
    {B : GradedAlgebra.{t, a} R}
    (N : GradedModule.{t, a, m} B) (n m : ℤ) (U : Cᵒᵖ)
    (x : (N.piece n).val.obj U) (a : (B.piece m).val.obj U) :
    (gradedShift N 1).smul (n - 1) m U
        (gradedCast (fun q => (N.piece q).val.obj U)
          (show n = (n - 1) + 1 by lia) x) a =
      gradedCast (fun q => (N.piece q).val.obj U)
        (show n + m = ((n - 1) + m) + 1 by lia) (N.smul n m U x a) := by
  let h : n = (n - 1) + 1 := by lia
  let hleft : ((n - 1) + 1) + m = ((n - 1) + m) + 1 := by lia
  let hright : n + m = ((n - 1) + m) + 1 := by lia
  have hcastL := gradedCast_heq (fun q => (N.piece q).val.obj U) hleft
    (N.smul ((n - 1) + 1) m U
      (gradedCast (fun q => (N.piece q).val.obj U) h x) a)
  have hmul := gradedModule_smul_cast_heq N h U x a
  have hcastR := gradedCast_heq (fun q => (N.piece q).val.obj U) hright
    (N.smul n m U x a)
  dsimp [gradedShift]
  exact eq_of_heq (hcastL.trans (hmul.trans hcastR.symm))

private theorem gradedCast_hom_app {F G : ℤ → SheafOfModules.{m} R} (f : ∀ n, F n ⟶ G n)
    {i j : ℤ} (h : i = j) (U : Cᵒᵖ) (x : (F i).val.obj U) :
    ((f j).val.app U) (gradedCast (fun q => (F q).val.obj U) h x) =
      gradedCast (fun q => (G q).val.obj U) h (((f i).val.app U) x) := by
  cases h
  rfl

private theorem gradedCast_eqToHom (F : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j)
    (U : Cᵒᵖ) (x : (F i).val.obj U) :
    gradedCast (fun q => (F q).val.obj U) h x =
      ((eqToHom (congrArg F h)).val.app U) x := by
  cases h
  rfl

/-- Applying two sections-level `eqToHom`s in succession is applying the `eqToHom` of the
composite equality. -/
private theorem eqToHom_app_eqToHom_app {X Y Z : SheafOfModules.{m} R} (p : X = Y) (q : Y = Z)
    (U : Cᵒᵖ) (x : X.val.obj U) :
    (eqToHom q).val.app U ((eqToHom p).val.app U x) = (eqToHom (p.trans q)).val.app U x := by
  cases p
  cases q
  rfl

private theorem eqToHom_comp_app_comp_eqToHom
    {C : Type*} [Category C] {ι : Type*} {F G : ι → C}
    (f : ∀ index, F index ⟶ G index) {source target : ι}
    (h : source = target) :
    eqToHom (congrArg F h) ≫ f target ≫ eqToHom (congrArg G h.symm) =
      f source := by
  cases h
  simp

private theorem gradedCast_reindex_succ {T : ℤ → Type*} {i j : ℤ}
    (h : i = j) (x : T (i + 1)) :
    gradedCast (fun q => T (q + 1)) h x =
      gradedCast T (congrArg (fun q : ℤ => q + 1) h) x := by
  cases h
  rfl

private theorem gradedCast_reindex_add {T : ℤ → Type*} {i j : ℤ} (m : ℤ)
    (h : i = j) (x : T (i + m)) :
    gradedCast (fun q => T (q + m)) h x =
      gradedCast T (congrArg (fun q : ℤ => q + m) h) x := by
  cases h
  rfl

private theorem heq_after_transport (F : ℤ → SheafOfModules.{m} R) {i j k : ℤ}
    (hi : i = k) (hj : j = k) (U : Cᵒᵖ)
    {x : (F i).val.obj U} {y : (F j).val.obj U} (h : x ≍ y) :
    ((eqToHom (congrArg F hi)).val.app U) x =
      ((eqToHom (congrArg F hj)).val.app U) y := by
  cases hi
  cases hj
  exact eq_of_heq h

private def gradedShiftHom {B : GradedAlgebra.{t, a} R}
    {M N : GradedModule.{t, a, m} B}
    (f : M ⟶ N) (k : ℤ) : gradedShift M k ⟶ gradedShift N k where
  app n := f.app (n + k)
  map_smul := by
    intro n m U x a
    dsimp only [DFunLike.coe, AddMonoidHom.coe_mk, AddHom.coe_mk, Function.comp_apply]
    change ((f.app ((n + m) + k)).val.app U)
        (gradedCast (fun q => (M.piece q).val.obj U)
          (show (n + k) + m = (n + m) + k by lia)
          ((M.smul (n + k) m U x) a)) =
      gradedCast (fun q => (N.piece q).val.obj U)
        (show (n + k) + m = (n + m) + k by lia)
        ((N.smul (n + k) m U (((f.app (n + k)).val.app U) x) a))
    rw [gradedCast_hom_app]
    exact congrArg (gradedCast (fun q => (N.piece q).val.obj U)
      (show (n + k) + m = (n + m) + k by lia)) (f.map_smul (n + k) m U x a)

private theorem gradedShiftHom_mono {B : GradedAlgebra.{t, a} R}
    {M N : GradedModule.{t, a, m} B}
    (f : M ⟶ N) [Mono f] (k : ℤ) : Mono (gradedShiftHom f k) := by
  refine ⟨?_⟩
  intro P g h hgh
  apply GradedModule.Hom.ext
  intro n
  have heq := congrArg (fun q : P ⟶ gradedShift N k => q.app n) hgh
  change g.app n ≫ f.app (n + k) = h.app n ≫ f.app (n + k) at heq
  have hmono : Mono (f.app (n + k)) := GradedModule.mono_app_of_mono f (n + k)
  exact (cancel_mono (f.app (n + k))).1 heq

private theorem forgetMap_mono {A : DifferentialGradedAlgebra.{t, a} R}
    {M N : DifferentialGradedModule.{t, a, m} A} (b : M ⟶ N) [Mono b] :
    Mono ((forgetToGradedModule A).map b) := by
  let F := forgetToGradedModule A
  let _ : PreservesLimits F :=
    forgetToGradedModule_preservesLimits A
  exact Functor.map_mono F b

private theorem gradedShift_piece_eq {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) {i j : ℤ} (h : i = j + 1) :
    M.complex.X i = (gradedShift ((forgetToGradedModule A).obj M) 1).piece j := by
  subst i
  show M.complex.X (j + 1) = M.complex.X (j + 1)
  rfl

private def homotopyShiftHom {A : DifferentialGradedAlgebra.{t, a} R}
    {M I : DifferentialGradedModule.{t, a, m} A}
    {a z : M ⟶ I} (H : Homotopy a z) :
    gradedShift ((forgetToGradedModule A).obj M) 1 ⟶
      (forgetToGradedModule A).obj I where
  app n := H.app (n + 1) ≫
    eqToHom (congrArg I.complex.X (show (n + 1) - 1 = n by lia))
  map_smul := by
    intro n m U x a
    let x₀ : (M.complex.X (n + 1)).val.obj U := x
    let i := ((n + 1) + m) - 1
    let j := ((n + 1) - 1) + m
    let k := n + m
    have hnm : (n + 1) + m = (n + m) + 1 := by lia
    have hn : (n + 1) - 1 = n := by lia
    have hi : i = k := by dsimp [i, k]; lia
    have hj : j = k := by dsimp [j, k]; lia
    have houter : ((n + m) + 1) - 1 = k := by dsimp [k]; lia
    have h : HEq (((H.app ((n + 1) + m)).val.app U)
        (((M.mul (n + 1) m).app U) x₀ a))
        (((I.mul ((n + 1) - 1) m).app U) (((H.app (n + 1)).val.app U) x₀) a) :=
      H.map_mul (n + 1) m U x₀ a
    have hcast := heq_after_transport I.complex.X hi hj U h
    have hact := gradedModule_smul_cast_heq ((forgetToGradedModule A).obj I) hn U
      (((H.app (n + 1)).val.app U) x₀) a
    change
      ((eqToHom (congrArg I.complex.X houter)).val.app U)
        (((H.app ((n + m) + 1)).val.app U)
          (gradedCast (fun q => (M.complex.X q).val.obj U) hnm
            (((M.mul (n + 1) m).app U) x₀ a))) =
      ((I.mul n m).app U)
        (((eqToHom (congrArg I.complex.X hn)).val.app U)
          (((H.app (n + 1)).val.app U) x₀)) a
    calc
      _ = ((eqToHom (congrArg I.complex.X hi)).val.app U)
          (((H.app ((n + 1) + m)).val.app U)
            (((M.mul (n + 1) m).app U) x₀ a)) := by
          rw [gradedCast_hom_app H.app hnm U (((M.mul (n + 1) m).app U) x₀ a)]
          rw [gradedCast_eqToHom (fun q => I.complex.X (q - 1)) hnm U,
            eqToHom_app_eqToHom_app]
      _ = ((eqToHom (congrArg I.complex.X hj)).val.app U)
          (((I.mul ((n + 1) - 1) m).app U)
            (((H.app (n + 1)).val.app U) x₀) a) := hcast
      _ = ((I.mul n m).app U)
          (((eqToHom (congrArg I.complex.X hn)).val.app U)
            (((H.app (n + 1)).val.app U) x₀)) a := by
          have hiAct : n + m = k := by rfl
          have hjAct : j = k := by dsimp [j, k]; lia
          have hact' := heq_after_transport I.complex.X hiAct hjAct U hact
          have hcastInput :
              gradedCast
                  (fun q => (((forgetToGradedModule A).obj I).piece q).val.obj U)
                  hn (((H.app (n + 1)).val.app U) x₀) =
                ((eqToHom (congrArg I.complex.X hn)).val.app U)
                  (((H.app (n + 1)).val.app U) x₀) :=
            gradedCast_eqToHom I.complex.X hn U _
          rw [hcastInput] at hact'
          have hrev := hact'.symm
          change
            ((eqToHom (congrArg I.complex.X hjAct)).val.app U)
                (((I.mul ((n + 1) - 1) m).app U
                  (((H.app (n + 1)).val.app U) x₀)) a) =
              ((eqToHom (congrArg I.complex.X hiAct)).val.app U)
                (((I.mul n m).app U
                  (((eqToHom (congrArg I.complex.X hn)).val.app U)
                    (((H.app (n + 1)).val.app U) x₀))) a) at hrev
          simpa [k] using hrev

private noncomputable def homotopyBoundary {A : DifferentialGradedAlgebra.{t, a} R}
    {M I : DifferentialGradedModule.{t, a, m} A}
    (h : gradedShift ((forgetToGradedModule A).obj M) 1 ⟶
      (forgetToGradedModule A).obj I) : M ⟶ I where
  toHomologicalComplex := Homotopy.nullHomotopicMap (fun i j =>
    if hij : i = j + 1 then
      eqToHom (gradedShift_piece_eq M hij) ≫ h.app j ≫
        eqToHom (forgetToGradedModule_obj_piece
          A I j) else 0)
  map_mul := by
    intro n m U x a
    let GM := (forgetToGradedModule A).obj M
    let GI := (forgetToGradedModule A).obj I
    let a' : (A.toGradedAlgebra.piece m).val.obj U := by
      simpa only [DifferentialGradedAlgebra.toGradedAlgebra_piece] using a
    let hx : ((gradedShift GM 1).piece (n - 1)).val.obj U :=
      gradedCast (fun q => (GM.piece q).val.obj U)
        (show n = (n - 1) + 1 by omega) x
    let i := (n - 1) + m
    let j := n + m - 1
    have hij : i = j := by dsimp [i, j]; omega
    have hinput :
        gradedCast (fun q => ((gradedShift GM 1).piece q).val.obj U) hij
          (((gradedShift GM 1).smul (n - 1) m U hx a')) =
        gradedCast (fun q => (GM.piece q).val.obj U)
          (show n + m = j + 1 by dsimp [j]; omega)
          (((GM.smul n m U x) a')) := by
      let hbase : n + m = ((n - 1) + m) + 1 := by omega
      let hplus : i + 1 = j + 1 := congrArg (fun q : ℤ => q + 1) hij
      let htarget : n + m = j + 1 := by dsimp [j]; omega
      have hshift' := gradedShift_smul_cast GM n m U x a'
      have houter : HEq
          (gradedCast (fun q => ((gradedShift GM 1).piece q).val.obj U)
            hij (((gradedShift GM 1).smul (n - 1) m U hx) a'))
          (gradedCast (fun q => (GM.piece q).val.obj U) hplus
            (((gradedShift GM 1).smul (n - 1) m U hx) a')) :=
        (gradedCast_heq (fun q => ((gradedShift GM 1).piece q).val.obj U)
          hij (((gradedShift GM 1).smul (n - 1) m U hx) a')).trans
          (gradedCast_heq (fun q => (GM.piece q).val.obj U) hplus
            (((gradedShift GM 1).smul (n - 1) m U hx) a')).symm
      apply eq_of_heq
      refine HEq.trans houter ?_
      rw [hshift', gradedCast_trans]
      exact HEq.rfl
    have hsmul₀ :
        ((h.app j).val.app U)
            (gradedCast (fun q => ((gradedShift GM 1).piece q).val.obj U) hij
              (((gradedShift GM 1).smul (n - 1) m U hx a))) =
          gradedCast (fun q => (GI.piece q).val.obj U) hij
            ((GI.smul (n - 1) m U ((h.app (n - 1)).val.app U hx) a')) := by
      have hmove := gradedCast_hom_app h.app hij U
        (((gradedShift GM 1).smul (n - 1) m U hx a'))
      calc
        _ = gradedCast (fun q => (GI.piece q).val.obj U) hij
            (((h.app i).val.app U) (((gradedShift GM 1).smul (n - 1) m U hx a'))) := hmove
        _ = gradedCast (fun q => (GI.piece q).val.obj U) hij
              ((GI.smul (n - 1) m U ((h.app (n - 1)).val.app U hx) a')) := by
              rw [h.map_smul (n - 1) m U hx a']
    simp only []
    rw [Homotopy.nullHomotopicMap_f
      (show (ComplexShape.up ℤ).Rel (n + m - 1) (n + m) by simp)
      (show (ComplexShape.up ℤ).Rel (n + m) (n + m + 1) by simp),
      Homotopy.nullHomotopicMap_f
      (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)
      (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)]
    have h1 : n + m + 1 = n + m + 1 := rfl
    have h2 : n + m = n + m - 1 + 1 := by omega
    have h3 : n + 1 = n + 1 := rfl
    have h4 : n = n - 1 + 1 := by omega
    with_reducible split_ifs ; try omega
    all_goals try with_reducible simp only [SheafOfModules.add_val,
      PresheafOfModules.add_app, ModuleCat.hom_add, LinearMap.add_apply]
    all_goals try simp only [M.leibniz, LinearMap.comp_apply,
      SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
      map_add]
    have hmap1 := h.map_smul n m U ((M.complex.d n (n + 1)).val.app U x) a'
    have hinput1 :
        (gradedShift GM 1).smul n m U ((M.complex.d n (n + 1)).val.app U x) a' =
          gradedCast (fun q => (GM.piece q).val.obj U)
            (show n + 1 + m = (n + m) + 1 by omega)
            (((GM.smul (n + 1) m U)
              ((M.complex.d n (n + 1)).val.app U x)) a') := by
      rfl
    have hmap1' :
        (h.app (n + m)).val.app U
            (gradedCast (fun q => (GM.piece q).val.obj U)
              (show n + 1 + m = (n + m) + 1 by omega)
              (((GM.smul (n + 1) m U)
                ((M.complex.d n (n + 1)).val.app U x)) a')) =
          ((GI.smul n m U)
            (((h.app n).val.app U) ((M.complex.d n (n + 1)).val.app U x)) a') := by
      rw [← hinput1]
      exact hmap1
    let q := (n - 1) + (m + 1)
    have hq : q = n + m := by dsimp [q]; omega
    have hmap2q := h.map_smul (n - 1) (m + 1) U hx
      ((A.complex.d m (m + 1)).val.app U a)
    have hmap2' :
        (h.app (n + m)).val.app U
            (gradedCast (fun q => ((gradedShift GM 1).piece q).val.obj U)
              hq
              (((gradedShift GM 1).smul (n - 1) (m + 1) U) hx
                ((A.complex.d m (m + 1)).val.app U a))) =
          gradedCast (fun q => (GI.piece q).val.obj U) hq
            (((GI.smul (n - 1) (m + 1) U) ((h.app (n - 1)).val.app U hx))
              ((A.complex.d m (m + 1)).val.app U a)) := by
      calc
        _ = gradedCast (fun q => (GI.piece q).val.obj U) hq
            (((h.app q).val.app U)
              (((gradedShift GM 1).smul (n - 1) (m + 1) U) hx
                ((A.complex.d m (m + 1)).val.app U a))) :=
              gradedCast_hom_app h.app hq U _
        _ = _ := congrArg (gradedCast (fun q => (GI.piece q).val.obj U) hq)
          hmap2q
    have hinput2 :
        gradedCast (fun q => ((gradedShift GM 1).piece q).val.obj U)
            hq
            (((gradedShift GM 1).smul (n - 1) (m + 1) U) hx
              ((A.complex.d m (m + 1)).val.app U a)) =
          gradedCast (fun q => (GM.piece q).val.obj U)
            (show n + (m + 1) = (n + m) + 1 by omega)
            (((GM.smul n (m + 1) U) x)
              ((A.complex.d m (m + 1)).val.app U a)) := by
      let i := (n - 1) + (m + 1)
      have hij : i = n + m := by dsimp [i]; omega
      let hbase : n + (m + 1) = i + 1 := by dsimp [i]; omega
      let hplus : i + 1 = (n + m) + 1 := congrArg (fun t : ℤ => t + 1) hij
      let htarget : n + (m + 1) = (n + m) + 1 := by omega
      let x₀ : (GM.piece n).val.obj U := x
      let a₁ : (A.toGradedAlgebra.piece (m + 1)).val.obj U := by
        simpa only [DifferentialGradedAlgebra.toGradedAlgebra_piece] using
          ((A.complex.d m (m + 1)).val.app U a)
      with_reducible
        have hshift' := gradedShift_smul_cast GM n (m + 1) U x₀ a₁
      have hshift'' :
          ((gradedShift GM 1).smul (n - 1) (m + 1) U) hx
              ((A.complex.d m (m + 1)).val.app U a) =
            gradedCast (fun q => (GM.piece q).val.obj U) hbase
              (((GM.smul n (m + 1) U) x₀) a₁) := by
        convert hshift' using 1 ; try rfl
      have houter : HEq
          (gradedCast (fun q => ((gradedShift GM 1).piece q).val.obj U)
            hij
            ((((gradedShift GM 1).smul (n - 1) (m + 1) U) hx)
              ((A.complex.d m (m + 1)).val.app U a)))
          (gradedCast (fun q => (GM.piece q).val.obj U) hplus
            ((((gradedShift GM 1).smul (n - 1) (m + 1) U) hx)
              ((A.complex.d m (m + 1)).val.app U a))) :=
        HEq.trans
          (gradedCast_heq (fun q => ((gradedShift GM 1).piece q).val.obj U) hij _)
          (gradedCast_heq (fun q => (GM.piece q).val.obj U) hplus _).symm
      apply eq_of_heq
      refine HEq.trans houter ?_
      rw [hshift'', gradedCast_trans]
      exact HEq.rfl
    have hproduct :
        (h.app j).val.app U
            (gradedCast (fun q => (GM.piece q).val.obj U)
              (show n + m = j + 1 by dsimp [j]; omega)
              ((GM.smul n m U x) a')) =
          gradedCast (fun q => (GI.piece q).val.obj U) hij
            (((GI.smul (n - 1) m U) ((h.app (n - 1)).val.app U hx)) a') := by
      rw [← hinput]
      exact hsmul₀
    have hmap1'' := congrArg
      ((eqToHom (forgetToGradedModule_obj_piece A I
        (n + m))).val.app U) hmap1'
    have hcastM :
        ((eqToHom (gradedShift_piece_eq M h1)).val.app U)
          (gradedCast (fun q => (M.complex.X q).val.obj U)
            (add_right_comm n 1 m)
            (((M.mul (n + 1) m).app U)
              ((M.complex.d n (n + 1)).val.app U x) a)) =
        gradedCast (fun q => (GM.piece q).val.obj U)
          (show n + 1 + m = (n + m) + 1 by omega)
          (((GM.smul (n + 1) m U)
            ((M.complex.d n (n + 1)).val.app U x)) a') := by
      rw [gradedCast_eqToHom, gradedCast_eqToHom, eqToHom_app_eqToHom_app]
      rfl
    have hinput1' :
        ((eqToHom (gradedShift_piece_eq M h1)).val.app U)
          (gradedCast (fun q => (M.complex.X q).val.obj U)
            (add_right_comm n 1 m)
            (((M.mul (n + 1) m).app U)
              ((M.complex.d n (n + 1)).val.app U x) a)) =
        ((gradedShift GM 1).smul n m U
          ((M.complex.d n (n + 1)).val.app U x)) a' := by
      rw [hcastM]
      exact hinput1.symm
    have hdx (hidx : n + 1 = n + 1) :
        ((eqToHom (gradedShift_piece_eq M hidx)).val.app U)
          ((M.complex.d n (n + 1)).val.app U x) =
        ((M.complex.d n (n + 1)).val.app U x) := by
      simp only []
      cases gradedShift_piece_eq M hidx
      rfl
    have hpieceId (k : ℤ) :
        eqToHom (forgetToGradedModule_obj_piece A I k) = 𝟙 _ := by
      congr 1
    have hterm1 :
        (ModuleCat.Hom.hom ((h.app (n + m) ≫
          eqToHom (forgetToGradedModule_obj_piece A I
            (n + m))).val.app U))
          ((ModuleCat.Hom.hom ((eqToHom (gradedShift_piece_eq M h1)).val.app U))
            (gradedCast (fun q => (M.complex.X q).val.obj U)
              (add_right_comm n 1 m)
              (((M.mul (n + 1) m).app U)
                ((M.complex.d n (n + 1)).val.app U x) a))) =
        ((I.mul n m).app U)
          ((ModuleCat.Hom.hom ((h.app n ≫
            eqToHom (forgetToGradedModule_obj_piece A I n)).val.app U))
            ((ModuleCat.Hom.hom ((eqToHom (gradedShift_piece_eq M h3)).val.app U))
              ((M.complex.d n (n + 1)).val.app U x))) a := by
      let dx' := ((eqToHom (gradedShift_piece_eq M h3)).val.app U)
        ((M.complex.d n (n + 1)).val.app U x)
      have hmap1shift := h.map_smul n m U dx' a'
      have hshiftmove := congrArg (fun y => ((gradedShift GM 1).smul n m U y) a')
        (hdx h3)
      have hmapmove := congrArg ((h.app (n + m)).val.app U) hshiftmove
      have hmapmove' := congrArg
        ((eqToHom (forgetToGradedModule_obj_piece A I
          (n + m))).val.app U) hmapmove
      have hmap1raw := congrArg
        ((eqToHom (forgetToGradedModule_obj_piece A I
          (n + m))).val.app U) hmap1shift
      have hmap1comp := hmapmove'.symm.trans hmap1raw
      rw [hpieceId (n + m)] at hmap1comp
      simp only [] at hmap1comp
      simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
      rw [hinput1', hpieceId n, hdx h3, hpieceId (n + m)]
      dsimp only [dx'] at hmap1comp
      rw [hdx h3] at hmap1comp
      change _ = _
      exact hmap1comp
    have hcastM2 :
        ((eqToHom (gradedShift_piece_eq M h1)).val.app U)
          (gradedCast (fun q => (M.complex.X q).val.obj U)
            (add_assoc n m 1).symm
            (((M.mul n (m + 1)).app U) x
              ((A.complex.d m (m + 1)).val.app U a))) =
        gradedCast (fun q => (GM.piece q).val.obj U)
          (show n + (m + 1) = (n + m) + 1 by omega)
          (((GM.smul n (m + 1) U) x)
            ((A.complex.d m (m + 1)).val.app U a)) := by
      rw [gradedCast_eqToHom, gradedCast_eqToHom, eqToHom_app_eqToHom_app]
      rfl
    have hsource2 :
        ((eqToHom (gradedShift_piece_eq M h1)).val.app U)
          (gradedCast (fun q => (M.complex.X q).val.obj U)
            (add_assoc n m 1).symm
            (((M.mul n (m + 1)).app U) x
              ((A.complex.d m (m + 1)).val.app U a))) =
        gradedCast
          (fun q => ((gradedShift GM 1).piece q).val.obj U) hq
          (((gradedShift GM 1).smul (n - 1) (m + 1) U) hx
            ((A.complex.d m (m + 1)).val.app U a)) :=
      hcastM2.trans hinput2.symm
    have hterm2core := congrArg ((h.app (n + m)).val.app U) hsource2
    have hterm2' :
        ((h.app (n + m)).val.app U)
          ((eqToHom (gradedShift_piece_eq M h1)).val.app U
            (gradedCast (fun q => (M.complex.X q).val.obj U)
              (add_assoc n m 1).symm
              (((M.mul n (m + 1)).app U) x
                ((A.complex.d m (m + 1)).val.app U a)))) =
        gradedCast (fun q => (GI.piece q).val.obj U) hq
          (((GI.smul (n - 1) (m + 1) U)
            ((h.app (n - 1)).val.app U hx))
            ((A.complex.d m (m + 1)).val.app U a)) :=
      hterm2core.trans hmap2'
    have hxEq : hx = ((eqToHom (gradedShift_piece_eq M h4)).val.app U) x := by
      have hc := gradedCast_eqToHom GM.piece h4 U x
      have hp : congrArg GM.piece h4 = gradedShift_piece_eq M h4 :=
        Subsingleton.elim _ _
      rw [hp] at hc
      exact hc
    have hterm2full :
        ((eqToHom (forgetToGradedModule_obj_piece
          A I (n + m))).val.app U)
          (((h.app (n + m)).val.app U)
            ((eqToHom (gradedShift_piece_eq M h1)).val.app U
              (gradedCast (fun q => (M.complex.X q).val.obj U)
                (add_assoc n m 1).symm
                (((M.mul n (m + 1)).app U) x
                  ((A.complex.d m (m + 1)).val.app U a))))) =
        gradedCast (fun q => (I.complex.X q).val.obj U) hq
          (((I.mul (n - 1) (m + 1)).app U)
            (((eqToHom (forgetToGradedModule_obj_piece
              A I (n - 1))).val.app U)
              (((h.app (n - 1)).val.app U)
                (((eqToHom (gradedShift_piece_eq M h4)).val.app U) x)))
            ((A.complex.d m (m + 1)).val.app U a)) := by
      calc
        _ = gradedCast (fun q => (GI.piece q).val.obj U) hq
            (((GI.smul (n - 1) (m + 1) U)
              (((h.app (n - 1)).val.app U) hx))
              ((A.complex.d m (m + 1)).val.app U a)) :=
              congrArg ((eqToHom (forgetToGradedModule_obj_piece
                A I (n + m))).val.app U) hterm2'
        _ = _ := by
              rw [gradedCast_eqToHom]
              change ((eqToHom (congrArg I.complex.X hq)).val.app U)
                  (((I.mul (n - 1) (m + 1)).app U)
                    (((h.app (n - 1)).val.app U) hx)
                    ((A.complex.d m (m + 1)).val.app U a)) = _
              rw [hxEq]
              simp only [gradedCast_eqToHom]
              congr 1
    have hterm1' := hterm1
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hterm1'
    rw [hterm1']
    have hterm2scaled :
        ((eqToHom (forgetToGradedModule_obj_piece
          A I (n + m))).val.app U)
          (((h.app (n + m)).val.app U)
            (((eqToHom (gradedShift_piece_eq M h1)).val.app U)
              ((Int.negOnePow n : ℤ) •
                gradedCast (fun q => (M.complex.X q).val.obj U)
                  (add_assoc n m 1).symm
                  (((M.mul n (m + 1)).app U) x
                    ((A.complex.d m (m + 1)).val.app U a))))) =
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q => (I.complex.X q).val.obj U) hq
            (((I.mul (n - 1) (m + 1)).app U)
              (((eqToHom (forgetToGradedModule_obj_piece
                A I (n - 1))).val.app U)
                (((h.app (n - 1)).val.app U)
                  (((eqToHom (gradedShift_piece_eq M h4)).val.app U) x)))
              ((A.complex.d m (m + 1)).val.app U a)) := by
      let f := ((eqToHom (forgetToGradedModule_obj_piece
        A I (n + m))).val.app U).hom ∘ₗ ((h.app (n + m)).val.app U).hom ∘ₗ
          ((eqToHom (gradedShift_piece_eq M h1)).val.app U).hom
      change f ((Int.negOnePow n : ℤ) •
        gradedCast (fun q => (M.complex.X q).val.obj U)
          (add_assoc n m 1).symm
          (((M.mul n (m + 1)).app U) x
            ((A.complex.d m (m + 1)).val.app U a))) = _
      calc
        _ = (Int.negOnePow n : ℤ) • f
              (gradedCast (fun q => (M.complex.X q).val.obj U)
                (add_assoc n m 1).symm
                (((M.mul n (m + 1)).app U) x
                  ((A.complex.d m (m + 1)).val.app U a))) :=
                map_zsmul f (Int.negOnePow n)
                  (gradedCast (fun q => (M.complex.X q).val.obj U)
                    (add_assoc n m 1).symm
                    (((M.mul n (m + 1)).app U) x
                      ((A.complex.d m (m + 1)).val.app U a)))
        _ = _ := congrArg (fun y => (Int.negOnePow n : ℤ) • y) hterm2full
    rw [hterm2scaled]
    let yI : (I.complex.X (n - 1)).val.obj U :=
      ((h.app (n - 1)).val.app U)
        (((eqToHom (gradedShift_piece_eq M h4)).val.app U) x)
    have hIleib := I.leibniz (n - 1) m U yI a
    have hcastProd :
        ((eqToHom (gradedShift_piece_eq M h2)).val.app U)
            (((M.mul n m).app U) x a) =
          gradedCast (fun q => (GM.piece q).val.obj U)
            (show n + m = (n + m - 1) + 1 by omega)
            (((GM.smul n m U) x) a') := by
      rw [gradedCast_eqToHom]
      congr 1
    have hMapProd :
        ((h.app (n + m - 1)).val.app U)
            (((eqToHom (gradedShift_piece_eq M h2)).val.app U)
              (((M.mul n m).app U) x a)) =
          gradedCast (fun q => (GI.piece q).val.obj U) hij
            (((GI.smul (n - 1) m U) yI) a) := by
      calc
        _ = ((h.app j).val.app U)
              (gradedCast (fun q => (GM.piece q).val.obj U)
                (show n + m = j + 1 by dsimp [j]; omega)
                (((GM.smul n m U) x) a')) :=
              congrArg ((h.app j).val.app U) hcastProd
        _ = gradedCast (fun q => (GI.piece q).val.obj U) hij
              (((GI.smul (n - 1) m U) yI) a) := by
              simpa [yI, a', hxEq] using hproduct
    rw [hMapProd]
    let r1 : (ComplexShape.up ℤ).Rel j (n + m) := by
      change j + 1 = n + m
      dsimp [j]
      omega
    let r2 : (ComplexShape.up ℤ).Rel j (j + 1) := by simp
    have hdEq := I.complex.d_comp_eqToHom r1 r2
    have hidx : (ComplexShape.up ℤ).next_eq r2 r1 = h2.symm :=
      Subsingleton.elim _ _
    rw [hidx] at hdEq
    let zI := gradedCast (fun q => (GI.piece q).val.obj U) hij
      (((GI.smul (n - 1) m U yI) a))
    have hpoint := congrArg (fun f => (f.val.app U) zI) hdEq
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.hom_comp, LinearMap.coe_comp] at hpoint
    have hDbase :
        (I.complex.d j (n + m)).val.app U
            zI =
          gradedCast (fun q => (I.complex.X q).val.obj U)
            (show j + 1 = n + m by dsimp [j]; omega)
            (gradedCast (fun q => (I.complex.X q).val.obj U)
              (congrArg (fun q : ℤ => q + 1) hij)
              ((I.complex.d ((n - 1) + m) (((n - 1) + m) + 1)).val.app U
                (((GI.smul (n - 1) m U yI) a)))) := by
      have hcast := gradedCast_d I.complex hij U (((GI.smul (n - 1) m U yI) a))
      have hz : zI =
          gradedCast (fun q => (I.complex.X q).val.obj U) hij
            (((GI.smul (n - 1) m U yI) a)) := by
        dsimp [zI, GI]
      have hcast' : (I.complex.d j (j + 1)).val.app U zI =
          gradedCast (fun q => (I.complex.X q).val.obj U)
            (congrArg (fun q : ℤ => q + 1) hij)
            ((I.complex.d ((n - 1) + m) (((n - 1) + m) + 1)).val.app U
              (((GI.smul (n - 1) m U yI) a))) := by
        rw [hz]
        exact hcast
      calc
        _ = ((eqToHom (congrArg I.complex.X h2.symm)).val.app U)
              ((I.complex.d j (j + 1)).val.app U zI) := hpoint.symm
        _ = _ := by
          rw [hcast']
          simp only [gradedCast_eqToHom]
    have hD := hDbase
    have hIleibGI :
        (I.complex.d ((n - 1) + m) (((n - 1) + m) + 1)).val.app U
            (((GI.smul (n - 1) m U yI) a)) =
          gradedCast (fun q => (I.complex.X q).val.obj U)
              (add_right_comm (n - 1) 1 m)
              ((((I.mul ((n - 1) + 1) m).app U)
                ((I.complex.d (n - 1) ((n - 1) + 1)).val.app U yI)) a) +
            (Int.negOnePow (n - 1) : ℤ) •
              gradedCast (fun q => (I.complex.X q).val.obj U)
                (add_assoc (n - 1) m 1).symm
                ((((I.mul (n - 1) (m + 1)).app U) yI)
                  ((A.complex.d m (m + 1)).val.app U a)) :=
      hIleib
    have hInput :
        (ModuleCat.Hom.hom ((eqToHom
          (forgetToGradedModule_obj_piece
            A I (n + m - 1))).val.app U))
          (gradedCast (fun q => (GI.piece q).val.obj U) hij
            (((GI.smul (n - 1) m U yI) a))) = zI := by
      rw [hpieceId (n + m - 1)]
      rfl
    rw [hInput]
    rw [hIleibGI] at hD
    rw [hD]
    simp only [gradedCast_add, gradedCast_smul, gradedCast_trans]
    let hRpath : q = n + m :=
      (add_assoc (n - 1) m 1).symm.trans
        ((congrArg (fun q : ℤ => q + 1) hij).trans
          (show j + 1 = n + m by dsimp [j]; omega))
    have hR :
        gradedCast (fun q => (I.complex.X q).val.obj U) hq
            ((((I.mul (n - 1) (m + 1)).app U)
              (((eqToHom (forgetToGradedModule_obj_piece
                A I (n - 1))).val.app U)
                ((h.app (n - 1)).val.app U
                  (((eqToHom (gradedShift_piece_eq M h4)).val.app U) x)))
              ((A.complex.d m (m + 1)).val.app U a))) =
          gradedCast (fun q => (I.complex.X q).val.obj U)
            (show j + 1 = n + m by dsimp [j]; omega)
            (gradedCast (fun q => (I.complex.X q).val.obj U)
              (congrArg (fun q : ℤ => q + 1) hij)
              (gradedCast (fun q => (I.complex.X q).val.obj U)
                (add_assoc (n - 1) m 1).symm
                ((((I.mul (n - 1) (m + 1)).app U) yI)
                  ((A.complex.d m (m + 1)).val.app U a)))) := by
      rw [hpieceId (n - 1)]
      dsimp [yI]
      rw [gradedCast_trans, gradedCast_trans]
      exact gradedCast_proof_irrel (fun q => (I.complex.X q).val.obj U)
        hq hRpath _
    let i₀ := (n - 1) + 1
    let r₀ : (ComplexShape.up ℤ).Rel (n - 1) i₀ := by
      dsimp [i₀]
      simp
    let r₁ : (ComplexShape.up ℤ).Rel (n - 1) n := by
      change (n - 1) + 1 = n
      omega
    have hdEq := I.complex.d_comp_eqToHom r₀ r₁
    have hdi : (ComplexShape.up ℤ).next_eq r₁ r₀ = h4 :=
      Subsingleton.elim _ _
    rw [hdi] at hdEq
    have hdPoint := congrArg (fun f => (f.val.app U) yI) hdEq
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hdPoint
    have hd :
        (I.complex.d (n - 1) i₀).val.app U yI =
          ((eqToHom (congrArg I.complex.X h4)).val.app U)
            ((I.complex.d (n - 1) n).val.app U yI) := hdPoint.symm
    have hdc :
        gradedCast (fun q => (I.complex.X q).val.obj U) h4.symm
            ((I.complex.d (n - 1) i₀).val.app U yI) =
          (I.complex.d (n - 1) n).val.app U yI := by
      rw [hd, gradedCast_eqToHom, eqToHom_app_eqToHom_app]
      simp
    let hPpath : i₀ + m = n + m := congrArg (fun q : ℤ => q + m) h4.symm
    have hMul' :
        (((I.mul n m).app U)
          (gradedCast (fun q => (I.complex.X q).val.obj U) h4.symm
            ((I.complex.d (n - 1) i₀).val.app U yI))) a =
          gradedCast (fun q => (I.complex.X q).val.obj U) hPpath
            ((((I.mul i₀ m).app U) ((I.complex.d (n - 1) i₀).val.app U yI)) a) :=
      gradedCast_mul I h4.symm U ((I.complex.d (n - 1) i₀).val.app U yI) a
    let hPcomp := (add_right_comm (n - 1) 1 m).trans
      ((congrArg (fun q : ℤ => q + 1) hij).trans
        (show j + 1 = n + m by dsimp [j]; omega))
    have hP :
        gradedCast (fun q => (I.complex.X q).val.obj U)
            (show j + 1 = n + m by dsimp [j]; omega)
            (gradedCast (fun q => (I.complex.X q).val.obj U)
              (congrArg (fun q : ℤ => q + 1) hij)
              (gradedCast (fun q => (I.complex.X q).val.obj U)
                (add_right_comm (n - 1) 1 m)
                ((((I.mul i₀ m).app U)
                  ((I.complex.d (n - 1) i₀).val.app U yI)) a))) =
          (((I.mul n m).app U) ((I.complex.d (n - 1) n).val.app U yI)) a := by
      calc
        _ = gradedCast (fun q => (I.complex.X q).val.obj U) hPcomp
              ((((I.mul i₀ m).app U)
                ((I.complex.d (n - 1) i₀).val.app U yI)) a) := by
              rw [gradedCast_trans, gradedCast_trans]
        _ = gradedCast (fun q => (I.complex.X q).val.obj U) hPpath
              ((((I.mul i₀ m).app U)
                ((I.complex.d (n - 1) i₀).val.app U yI)) a) :=
              gradedCast_proof_irrel (fun q => (I.complex.X q).val.obj U)
                hPcomp hPpath _
        _ = (((I.mul n m).app U)
              (gradedCast (fun q => (I.complex.X q).val.obj U) h4.symm
                ((I.complex.d (n - 1) i₀).val.app U yI))) a := hMul'.symm
        _ = _ := by rw [hdc]
    have hPdirect (p : i₀ + m = n + m) :
        gradedCast (fun q => (I.complex.X q).val.obj U) p
            ((((I.mul i₀ m).app U)
              ((I.complex.d (n - 1) i₀).val.app U yI)) a) =
          (((I.mul n m).app U) ((I.complex.d (n - 1) n).val.app U yI)) a := by
      have hpcast := gradedCast_proof_irrel (fun q => (I.complex.X q).val.obj U)
        p hPpath ((((I.mul i₀ m).app U)
          ((I.complex.d (n - 1) i₀).val.app U yI)) a)
      exact hpcast.trans (hMul'.symm.trans
        (congrArg (fun y => (((I.mul n m).app U) y) a) hdc))
    have hT (p : q = n + m) (z : (I.complex.X q).val.obj U) :
        gradedCast (fun q => (I.complex.X q).val.obj U)
          (show j + 1 = n + m by dsimp [j]; omega)
          (gradedCast (fun q => (I.complex.X q).val.obj U)
            (congrArg (fun q : ℤ => q + 1) hij)
            (gradedCast (fun q => (I.complex.X q).val.obj U)
              (add_assoc (n - 1) m 1).symm z)) =
          gradedCast (fun q => (I.complex.X q).val.obj U) p z := by
      rw [gradedCast_trans, gradedCast_trans]
    have hsign : (n - 1).negOnePow = -n.negOnePow := by
      have hs := Int.negOnePow_succ (n - 1)
      have hn : (n - 1) + 1 = n := by omega
      rw [hn] at hs
      calc
        (n - 1).negOnePow = -(-(n - 1).negOnePow) := by simp
        _ = -n.negOnePow := congrArg Neg.neg hs.symm
    rw [hR, hT hRpath]
    have hcastAll (p : q = n + m) (z : (I.complex.X q).val.obj U) :
        gradedCast (fun q => (I.complex.X q).val.obj U) p z =
          gradedCast (fun q => (I.complex.X q).val.obj U) hRpath z :=
      gradedCast_proof_irrel (fun q => (I.complex.X q).val.obj U) p hRpath z
    simp_rw [hcastAll]
    rw [hPdirect, hsign]
    have hidapp (F : SheafOfModules.{m} R) (y : F.val.obj U) :
        (ModuleCat.Hom.hom (((𝟙 F : F ⟶ F).val.app U))) y = y := rfl
    have hB :
        (((I.mul n m).app U) (((I.complex.d (n - 1) n).val.app U).hom' yI)) a =
        (((I.mul n m).app U)
          ((ModuleCat.Hom.hom ((I.complex.d (n - 1) n).val.app U))
            ((ModuleCat.Hom.hom ((eqToHom
              (forgetToGradedModule_obj_piece
                A I (n - 1))).val.app U))
              ((ModuleCat.Hom.hom ((h.app (n - 1)).val.app U))
                  ((ModuleCat.Hom.hom ((eqToHom (gradedShift_piece_eq M h4)).val.app U))
                  x))))) a := by
      rw [hpieceId (n - 1)]
      try simp only [hidapp]
      dsimp [yI]
      rfl
    have hdxM :
        (((M.complex.d n (n + 1)).val.app U).hom' x) =
          (ModuleCat.Hom.hom ((M.complex.d n (n + 1)).val.app U)) x := rfl
    have hprevVal (e : M.complex.X n = (gradedShift GM 1).piece (n - 1)) :
        (ConcreteCategory.hom ((h.app (n - 1)).val.app U))
            ((ConcreteCategory.hom ((eqToHom e).val.app U)) x) =
          (ModuleCat.Hom.hom ((h.app (n - 1)).val.app U))
            ((ModuleCat.Hom.hom ((eqToHom e).val.app U)) x) := by
      rfl
    rw [hprevVal (gradedShift_piece_eq M h4)]
    dsimp only [ConcreteCategory.hom]
    rw [hB, hdxM]
    dsimp only [ConcreteCategory.hom, ModuleCat.Hom.hom]
    simp [neg_smul]
    abel_nf!

/-- A map from an acyclic differential graded module to a K-injective, graded
injective module extends across any monomorphism. -/
@[stacks 0FSW]
theorem exists_extension_of_acyclic_of_mono
    {A : DifferentialGradedAlgebra.{t, a} R}
    {M M' I : DifferentialGradedModule.{t, a, m} A}
    (hI : IsKInjective I) (hI' : GradedInjective I)
    (b : M ⟶ M') [Mono b] (hM : M.complex.Acyclic) (a : M ⟶ I) :
    ∃ a' : M' ⟶ I, b ≫ a' = a := by
  let Q := HomotopyCategory.quotient A
  have hsub : Subsingleton (Q.obj M ⟶ Q.obj I) := hI M hM
  let z : M ⟶ I :=
    { toHomologicalComplex := 0
      map_mul := by
        intro n m U x a
        show 0 = ((I.mul n m).app U) 0 a
        simp }
  have hzero : (Q.map a) = Q.map z := Subsingleton.elim _ _
  have hnull : Homotopic a z :=
    (HomotopyCategory.quotient_map_eq_iff a z).mp hzero
  rcases hnull with ⟨H⟩
  let G := forgetToGradedModule A
  have hbG : Mono (G.map b) := forgetMap_mono b
  let sb := gradedShiftHom (G.map b) 1
  have hsb : Mono sb := by
    let _ : Mono (G.map b) := hbG
    exact gradedShiftHom_mono (G.map b) 1
  let _ : Injective (G.obj I) := hI'
  obtain ⟨Hext, hfactor⟩ := Injective.factors (homotopyShiftHom H) sb
  let a' := homotopyBoundary Hext
  refine ⟨a', ?_⟩
  apply DifferentialGradedModule.Hom.ext
  intro n
  ext U y
  have hprev := congrArg (fun q => q.app (n - 1)) hfactor
  have hnow := congrArg (fun q => q.app n) hfactor
  dsimp [sb, gradedShiftHom, homotopyShiftHom] at hprev hnow
  show (ModuleCat.Hom.hom ((b.toHomologicalComplex.f n ≫
      (homotopyBoundary Hext).toHomologicalComplex.f n).val.app U)) y =
    (ModuleCat.Hom.hom ((a.toHomologicalComplex.f n).val.app U)) y
  dsimp only [homotopyBoundary]
  have hr2 : (ComplexShape.up ℤ).Rel (n - 1) n := by simp
  have hr1 : (ComplexShape.up ℤ).Rel n (n + 1) := by simp
  rw [Homotopy.nullHomotopicMap_f hr2 hr1]
  simp only []
  simp only [dite_eq_left (show n = n - 1 + 1 by lia)]
  simp only [Category.assoc, Preadditive.comp_add]
  split_ifs <;> try lia
  all_goals simp_all only [MorphismProperty.monomorphisms.iff, ComplexShape.up_Rel,
    sub_add_cancel, forgetToGradedModule_obj_piece, HomologicalComplex.Hom.comm_assoc,
    HomologicalComplex.eqToHom_comp_d, add_val, comp_val, PresheafOfModules.add_app,
    PresheafOfModules.comp_app, ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.coe_comp, Function.comp_apply]
  all_goals
    change (GradedModule.Hom.comp _ _).app n = _ at hnow
    change (GradedModule.Hom.comp _ _).app (n - 1) = _ at hprev
    have hnowEval := congrArg
      (fun f => (f.val.app U) ((M.complex.d n (n + 1)).val.app U y)) hnow
    let yshift := (eqToHom (gradedShift_piece_eq M (show n = (n - 1) + 1 by lia))).val.app U y
    have hprevEval := congrArg (fun f => (f.val.app U) yshift) hprev
    change ((Hext.app n).val.app U
      (((G.map b).app (n + 1)).val.app U ((M.complex.d n (n + 1)).val.app U y))) = _
      at hnowEval
    change ((Hext.app (n - 1)).val.app U
      (((G.map b).app ((n - 1) + 1)).val.app U yshift)) = _
      at hprevEval
    simp only [forgetToGradedModule_obj_piece, forgetToGradedModule_map_app, G]
      at hnowEval hprevEval
    have hcommEval := congrArg (fun f => (f.val.app U) y) (H.comm n)
    simp [z, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.hom_comp] at hcommEval
    simp_all only [forgetToGradedModule_obj_piece, GradedModule.Hom.comp_app]
    let t₁ : (I.complex.X n).val.obj U :=
      (ModuleCat.Hom.hom ((Hext.app n ≫ eqToHom
        (forgetToGradedModule_obj_piece A I n)).val.app U))
        ((ModuleCat.Hom.hom ((eqToHom (gradedShift_piece_eq M'
          (show n + 1 = n + 1 by rfl))).val.app U))
          ((ModuleCat.Hom.hom ((b.toHomologicalComplex.f (n + 1)).val.app U))
            ((ModuleCat.Hom.hom ((M.complex.d n (n + 1)).val.app U)) y)))
    let t₂ : (I.complex.X n).val.obj U :=
      (ModuleCat.Hom.hom ((Hext.app (n - 1) ≫ I.complex.d (n - 1) n).val.app U))
        ((ModuleCat.Hom.hom ((eqToHom (gradedShift_piece_eq M'
          (show n = (n - 1) + 1 by lia))).val.app U))
          ((ModuleCat.Hom.hom ((b.toHomologicalComplex.f n).val.app U)) y))
    let r₁ : (I.complex.X n).val.obj U :=
      (ModuleCat.Hom.hom ((I.complex.d (n - 1) n).val.app U))
        ((ModuleCat.Hom.hom ((H.app n).val.app U)) y)
    let r₂ : (I.complex.X n).val.obj U :=
      (ModuleCat.Hom.hom ((eqToHom (congrArg I.complex.X
        (show n + 1 - 1 = n by lia))).val.app U))
        ((ModuleCat.Hom.hom ((H.app (n + 1)).val.app U))
          ((ModuleCat.Hom.hom ((M.complex.d n (n + 1)).val.app U)) y))
    show t₁ + t₂ = r₁ + r₂
    have ht₁ : t₁ = r₂ := by
      dsimp [t₁, r₂]
      convert hnowEval using 1 <;> try rfl
    have hprevD := congrArg
      (fun x => (ModuleCat.Hom.hom ((I.complex.d (n - 1) n).val.app U)) x) hprevEval
    have hindex : n = (n - 1) + 1 := by lia
    have hbc :
        (ConcreteCategory.hom ((b.toHomologicalComplex.f ((n - 1) + 1)).val.app U)) yshift =
          (ConcreteCategory.hom ((eqToHom (gradedShift_piece_eq M' hindex)).val.app U)
            ((ConcreteCategory.hom ((b.toHomologicalComplex.f n).val.app U)) y) :
              ((gradedShift ((forgetToGradedModule A).obj M') 1).piece (n - 1)).val.obj U) := by
      have hMpath : congrArg M.complex.X hindex = gradedShift_piece_eq M hindex :=
        Subsingleton.elim _ _
      have hM'path :
          congrArg M'.complex.X hindex = gradedShift_piece_eq M' hindex :=
        Subsingleton.elim _ _
      have hmap := gradedCast_hom_app b.toHomologicalComplex.f hindex U y
      convert hmap using 1 ;
        simp only [gradedShift, forgetToGradedModule_obj_piece,
          DifferentialGradedAlgebra.toGradedAlgebra_piece, gradedCast_eqToHom, yshift] ;
        first | exact Subsingleton.elim _ _ | exact Iff. | rfl
    have hbcD := congrArg
      (fun x => (ModuleCat.Hom.hom ((I.complex.d (n - 1) n).val.app U))
        ((ModuleCat.Hom.hom ((Hext.app (n - 1)).val.app U)) x)) hbc
    have ht₂ : t₂ = r₁ := by
      calc
        t₂ = (ModuleCat.Hom.hom ((I.complex.d (n - 1) n).val.app U))
            ((ModuleCat.Hom.hom ((Hext.app (n - 1)).val.app U))
                ((ModuleCat.Hom.hom ((b.toHomologicalComplex.f ((n - 1) + 1)).val.app U))
                  yshift)) := by
                dsimp [t₂]
                exact hbcD.symm
        _ = _ := hprevD
        _ = r₁ := by
              have htransport := eqToHom_comp_app_comp_eqToHom H.app hindex
              have htransportEval := congrArg
                (fun morphism => (morphism.val.app U) y) htransport
              apply congrArg
                (fun element => (ModuleCat.Hom.hom
                  ((I.complex.d (n - 1) n).val.app U)) element)
              exact htransportEval
    rw [ht₁, ht₂]
    simp [add_comm]

end DifferentialGradedModule

end SheafOfModules
