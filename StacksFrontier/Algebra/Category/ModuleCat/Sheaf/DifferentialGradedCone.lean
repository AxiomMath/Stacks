module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Cones of morphisms of differential graded modules

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras and
let `f : K ⟶ L` be a morphism of right differential graded `A`-modules. The cone of `f` has the
usual mapping-cone complex and the componentwise action of the graded algebra, and it comes with
the canonical inclusion of `L` and the canonical projection to the degree-one shift of `K`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ShiftPackage` records the degree-one shift of a right
  differential graded module, with its underlying shifted complex and its unchanged right action;
  `SheafOfModules.DifferentialGradedModule.shiftPackage` chooses this data and
  `SheafOfModules.DifferentialGradedModule.shift` is the shifted module itself. The shift is
  attached to the module, independently of any map out of it.
* `SheafOfModules.DifferentialGradedModule.ConePackage` records the cone of a morphism, its two
  canonical maps, and their defining degreewise properties;
  `SheafOfModules.DifferentialGradedModule.conePackage` chooses this data and
  `SheafOfModules.DifferentialGradedModule.cone` is the cone itself.

## Main results

* `SheafOfModules.DifferentialGradedModule.shiftPackage_nonempty`: the degree-one shift of a right
  differential graded module exists, with the right action unchanged.
* `SheafOfModules.DifferentialGradedModule.conePackage_nonempty`: the mapping-cone construction
  exists with its componentwise action and its canonical inclusion and projection.

## Implementation notes

The base is an arbitrary sheaf of rings `R` on an arbitrary site rather than the structure sheaf of
a ringed site; for a ringed site `X` the statements below are the case `R := X.ringSheaf`. The
universes of the site, the ring, the algebra components and the module components are independent.

`shiftPackage_nonempty` constructs the shift with its unchanged right action, and
`conePackage_nonempty` constructs the cone with its full specification. The underlying complex of
the cone is Mathlib's mapping cone `CochainComplex.mappingCone`, and the degreewise splitting
`cone.complex.X n ≅ K.complex.X (n + 1) ⊞ L.complex.X n` is Mathlib's
`HomologicalComplex.homotopyCofiber.XIsoBiprod`; the differential is therefore the mapping-cone
differential rather than one imposed here. The two projection equations of `ConePackage`
characterize the direct-sum action: in the first coordinate the cone acts as the shift of `K` does,
and in the second as `L` does. The defining equalities for the inclusion and the projection
identify their underlying complex maps with Mathlib's canonical maps. Crucially, the projection
targets the fixed `shift K`, not a shift chosen separately for each morphism; this is what makes
the projections of different morphisms out of `K` comparable.

Only *finite* biproducts of sheaves of modules are needed, and those exist with no hypotheses on
the site: `SheafOfModules.hasBinBiprod`. Nothing here needs sheafification or an abelian structure
on `SheafOfModules.{m} R`.

The degrees appearing on the two sides of the module laws are propositionally but not
definitionally equal, so those laws are stated with `HEq` and proved by transporting along
`SheafOfModules.gradedCast`, exactly as for the laws of a differential graded module itself.

## References

* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m m₂ v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Transport and biproducts of bilinear maps -/

/-- Transport of a bilinear map along an equality of its target. -/
def castBilinearMap {M : SheafOfModules.{m₂} R} {P P' : SheafOfModules.{m} R}
    {N : SheafOfModules.{a} R}
    (h : P = P') (f : BilinearMap M N P) : BilinearMap M N P' := by
  subst P'
  exact f

/-- A transported bilinear map has the same local behaviour as the map it came from. -/
theorem castBilinearMap_app_heq {M : SheafOfModules.{m₂} R} {P P' : SheafOfModules.{m} R}
    {N : SheafOfModules.{a} R} (h : P = P') (f : BilinearMap M N P) (U : Cᵒᵖ) :
    HEq ((castBilinearMap h f).app U) (f.app U) := by
  cases h
  rfl

/-- A transported bilinear map agrees with the original on a pair of local sections. -/
theorem castBilinearMap_eval_heq {M : SheafOfModules.{m₂} R} {P P' : SheafOfModules.{m} R}
    {N : SheafOfModules.{a} R} (h : P = P') (f : BilinearMap M N P) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    HEq ((castBilinearMap h f).app U x y) (f.app U x y) := by
  cases h
  rfl

private theorem heq_dependent_add {ι : Type*} {B : ι → Type*} [∀ i, Add (B i)]
    {i j : ι} (h : i = j) {x₁ y₁ : B i} {x₂ y₂ : B j}
    (hx : HEq x₁ x₂) (hy : HEq y₁ y₂) : HEq (x₁ + y₁) (x₂ + y₂) := by
  subst j
  rw [eq_of_heq hx, eq_of_heq hy]

private theorem gradedCast_dependent_apply {ι : Type*} {B D : ι → Type*} (f : ∀ i, B i → D i)
    {i j : ι} (h : i = j) (x : B i) :
    f j (gradedCast B h x) = gradedCast D h (f i x) := by
  subst j
  rfl

private theorem heq_gradedCast (X : ℤ → SheafOfModules.{m} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (x : (X i).val.obj U) : HEq (gradedCast (fun q ↦ (X q).val.obj U) h x) x := by
  rw [← castHom_apply]
  exact heq_castHom X h U x

/-- The zero morphism of sheaves of modules sends every local section to zero. -/
theorem zero_val_app {M N : SheafOfModules.{m} R} (U : Cᵒᵖ) (x : M.val.obj U) :
    (0 : M ⟶ N).val.app U x = 0 := homSections_zero U x

private theorem neg_val_app {M N : SheafOfModules.{m} R} (g : M ⟶ N) (U : Cᵒᵖ)
    (x : M.val.obj U) : (-g).val.app U x = -(g.val.app U x) := rfl

/-- A section of a binary biproduct of sheaves of modules, from its two coordinates. -/
noncomputable def biprodMk {P Q : SheafOfModules.{m} R} (U : Cᵒᵖ)
    (p : P.val.obj U) (q : Q.val.obj U) : (P ⊞ Q).val.obj U :=
  ((biprod.inl : P ⟶ P ⊞ Q).val.app U) p + ((biprod.inr : Q ⟶ P ⊞ Q).val.app U) q

/-- The first coordinate of a section assembled from two coordinates. -/
theorem biprodFst_biprodMk {P Q : SheafOfModules.{m} R} (U : Cᵒᵖ)
    (p : P.val.obj U) (q : Q.val.obj U) :
    (biprod.fst : P ⊞ Q ⟶ P).val.app U (biprodMk U p q) = p :=
  show biprodFst P Q U (biprodInl P Q U p + biprodInr P Q U q) = p by
    rw [map_add, biprodFst_inl, biprodFst_inr, add_zero]

/-- The second coordinate of a section assembled from two coordinates. -/
theorem biprodSnd_biprodMk {P Q : SheafOfModules.{m} R} (U : Cᵒᵖ)
    (p : P.val.obj U) (q : Q.val.obj U) :
    (biprod.snd : P ⊞ Q ⟶ Q).val.app U (biprodMk U p q) = q :=
  show biprodSnd P Q U (biprodInl P Q U p + biprodInr P Q U q) = q by
    rw [map_add, biprodSnd_inl, biprodSnd_inr, zero_add]

/-- The direct sum of two bilinear maps with a common second argument. -/
noncomputable def biprodBilinearMap {M N P Q : SheafOfModules.{m} R}
    {E : SheafOfModules.{a} R} (f : BilinearMap M E P) (g : BilinearMap N E Q) :
    BilinearMap (M ⊞ N) E (P ⊞ Q) where
  app U := {
    toFun := fun x => {
      toFun := fun y => biprodMk U
        ((f.app U) (((biprod.fst : M ⊞ N ⟶ M).val.app U) x) y)
        ((g.app U) (((biprod.snd : M ⊞ N ⟶ N).val.app U) x) y)
      map_zero' := by simp [biprodMk]
      map_add' := by intro y z; simp [biprodMk]; abel
    }
    map_zero' := by ext y; simp [biprodMk]
    map_add' := by intro x y; ext z; simp [biprodMk]; abel
  }
  map_smul_left U r x y := by
    simp [biprodMk, f.map_smul_left, g.map_smul_left]
  map_smul_right U r x y := by
    simp [biprodMk, f.map_smul_right, g.map_smul_right]
  naturality {U V} h x y := by
    change (P ⊞ Q).val.map h (biprodMk U
        ((f.app U) (((biprod.fst : M ⊞ N ⟶ M).val.app U) x) y)
        ((g.app U) (((biprod.snd : M ⊞ N ⟶ N).val.app U) x) y)) =
      biprodMk V
        ((f.app V) (((biprod.fst : M ⊞ N ⟶ M).val.app V)
          ((M ⊞ N).val.map h x)) ((E.val.map h) y))
        ((g.app V) (((biprod.snd : M ⊞ N ⟶ N).val.app V)
          ((M ⊞ N).val.map h x)) ((E.val.map h) y))
    simp only [biprodMk, map_add]
    rw [← PresheafOfModules.naturality_apply (biprod.inl : P ⟶ P ⊞ Q).val h,
      ← PresheafOfModules.naturality_apply (biprod.inr : Q ⟶ P ⊞ Q).val h]
    have hf := f.naturality h (((biprod.fst : M ⊞ N ⟶ M).val.app U) x) y
    have hg := g.naturality h (((biprod.snd : M ⊞ N ⟶ N).val.app U) x) y
    have hfst := PresheafOfModules.naturality_apply
      ((biprod.fst : M ⊞ N ⟶ M).val) h x
    have hsnd := PresheafOfModules.naturality_apply
      ((biprod.snd : M ⊞ N ⟶ N).val) h x
    have h₁ : ((biprod.inl : P ⟶ P ⊞ Q).val.app V)
        ((P.val.map h) ((f.app U) (((biprod.fst : M ⊞ N ⟶ M).val.app U) x) y)) =
      ((biprod.inl : P ⟶ P ⊞ Q).val.app V)
        ((f.app V) (((biprod.fst : M ⊞ N ⟶ M).val.app V) ((M ⊞ N).val.map h x))
          ((E.val.map h) y)) := by
      simpa only [← hfst] using congrArg ((biprod.inl : P ⟶ P ⊞ Q).val.app V) hf
    have h₂ : ((biprod.inr : Q ⟶ P ⊞ Q).val.app V)
        ((Q.val.map h) ((g.app U) (((biprod.snd : M ⊞ N ⟶ N).val.app U) x) y)) =
      ((biprod.inr : Q ⟶ P ⊞ Q).val.app V)
        ((g.app V) (((biprod.snd : M ⊞ N ⟶ N).val.app V) ((M ⊞ N).val.map h x))
          ((E.val.map h) y)) := by
      simpa only [← hsnd] using congrArg ((biprod.inr : Q ⟶ P ⊞ Q).val.app V) hg
    exact congrArg₂ (fun p q => p + q) h₁ h₂

/-- Precomposing the first argument of a bilinear map and postcomposing its value. -/
private def transportBilinearMap {M M' P P' : SheafOfModules.{m} R} {E : SheafOfModules.{a} R}
    (α : M' ⟶ M) (β : P ⟶ P') (f : BilinearMap M E P) : BilinearMap M' E P' where
  app U := {
    toFun := fun x => {
      toFun := fun y => (β.val.app U) ((f.app U) ((α.val.app U) x) y)
      map_zero' := by simp
      map_add' := by intro y z; simp
    }
    map_zero' := by ext y; simp
    map_add' := by intro x y; ext z; simp
  }
  map_smul_left U r x y := by simp [f.map_smul_left]
  map_smul_right U r x y := by simp [f.map_smul_right]
  naturality {U V} h x y := by
    change (P'.val.map h) ((β.val.app U) ((f.app U) ((α.val.app U) x) y)) =
      (β.val.app V) ((f.app V) ((α.val.app V) ((M'.val.map h) x)) ((E.val.map h) y))
    have hα := PresheafOfModules.naturality_apply α.val h x
    have hβ := PresheafOfModules.naturality_apply β.val h ((f.app U) ((α.val.app U) x) y)
    have hf := congrArg (β.val.app V) (f.naturality h ((α.val.app U) x) y)
    rw [hα]
    exact hβ.symm.trans hf

attribute [local simp] biprodFst_biprodMk biprodSnd_biprodMk

private theorem biprodBilinearMap_fst {M N P Q : SheafOfModules.{m} R}
    {E : SheafOfModules.{a} R} (f : BilinearMap M E P) (g : BilinearMap N E Q)
    (U : Cᵒᵖ) (x : (M ⊞ N).val.obj U) (y : E.val.obj U) :
    (biprod.fst : P ⊞ Q ⟶ P).val.app U ((biprodBilinearMap f g).app U x y) =
      (f.app U) ((biprod.fst : M ⊞ N ⟶ M).val.app U x) y := by
  simp [biprodBilinearMap]

private theorem biprodBilinearMap_snd {M N P Q : SheafOfModules.{m} R}
    {E : SheafOfModules.{a} R} (f : BilinearMap M E P) (g : BilinearMap N E Q)
    (U : Cᵒᵖ) (x : (M ⊞ N).val.obj U) (y : E.val.obj U) :
    (biprod.snd : P ⊞ Q ⟶ Q).val.app U ((biprodBilinearMap f g).app U x y) =
      (g.app U) ((biprod.snd : M ⊞ N ⟶ N).val.app U x) y := by
  simp [biprodBilinearMap]

/-! ### The degree-one shift -/

/-- The shift of a differential graded module, with its underlying shifted
complex and unchanged right action. -/
structure ShiftPackage {A : DifferentialGradedAlgebra.{t, a} R}
    (K : DifferentialGradedModule.{t, a, m} A) where
  /-- The shifted differential graded module. -/
  shifted : DifferentialGradedModule.{t, a, m} A
  /-- Its underlying complex is the degree-one shift of the complex of `K`. -/
  shifted_complex : shifted.complex =
    (CochainComplex.shiftFunctor (SheafOfModules.{m} R) 1).obj K.complex
  /-- Its right action is the right action of `K`, unchanged. -/
  shifted_action (n i : ℤ) (U : Cᵒᵖ) :
    HEq ((shifted.mul n i).app U) ((K.mul (n + 1) i).app U)

/-- A dependent function applied to a transported section agrees with its value before transport. -/
private theorem heq_dependent_gradedCast (X : ℤ → SheafOfModules.{m} R) (U : Cᵒᵖ)
    (F : ∀ d, (X d).val.obj U → (X d).val.obj U) {i j : ℤ} (h : i = j) (x : (X i).val.obj U) :
    HEq (F j (gradedCast (fun q ↦ (X q).val.obj U) h x)) (F i x) := by
  subst h
  rfl

private noncomputable abbrev shiftModel {A : DifferentialGradedAlgebra.{t, a} R}
    (K : DifferentialGradedModule.{t, a, m} A) : ShiftPackage K := by
  let sh := (CochainComplex.shiftFunctor (SheafOfModules.{m} R) (1 : ℤ)).obj K.complex
  let shMul (n i : ℤ) : BilinearMap (sh.X n) (A.complex.X i) (sh.X (n + i)) := by
    exact castBilinearMap
      (congrArg K.complex.X (show (n + 1) + i = (n + i) + 1 by omega))
      (K.mul (n + 1) i)
  have hsh (n i : ℤ) (U : Cᵒᵖ) (x : (sh.X n).val.obj U) (a : (A.complex.X i).val.obj U) :
      HEq ((shMul n i).app U x a) ((K.mul (n + 1) i).app U x a) :=
    castBilinearMap_eval_heq
      (congrArg K.complex.X (show (n + 1) + i = (n + i) + 1 by omega)) (K.mul (n + 1) i) U x a
  have hneg {X Y : SheafOfModules.{m} R} (g : X ⟶ Y) (V : Cᵒᵖ) (y : X.val.obj V) :
      ((-1 : ℤ) • g).val.app V y = -(g.val.app V y) := by
    rw [neg_one_zsmul]
    rfl
  refine {
    shifted := {
      complex := sh
      mul := shMul
      mul_assoc := ?_
      mul_one := ?_
      leibniz := ?_
    }
    shifted_complex := rfl
    shifted_action := ?_
  }
  · intro n i j U x a b
    have hpq : (n + i) + 1 = (n + 1) + i := by omega
    exact (hsh _ j U _ b).trans ((heq_dependent_apply
      (fun d y => ((K.mul d j).app U y) b) hpq (hsh n i U x a)).trans
      ((K.mul_assoc (n + 1) i j U x a b).trans (hsh n (i + j) U x _).symm))
  · intro n U x
    exact (hsh n 0 U x _).trans (K.mul_one (n + 1) U x)
  · intro n i U x a
    have h := congrArg (fun z => -z) (K.leibniz (n + 1) i U x a)
    simp only [neg_add] at h
    rw [← neg_smul, Int.negOnePow_succ] at h
    simp only [Units.val_neg, neg_neg] at h
    have hni : (n + i) + 1 = (n + 1) + i := by omega
    have hL : HEq ((sh.d (n + i) (n + i + 1)).val.app U ((shMul n i).app U x a))
        (-((K.complex.d ((n + 1) + i) (((n + 1) + i) + 1)).val.app U
          ((K.mul (n + 1) i).app U x a))) :=
      (heq_of_eq (hneg (K.complex.d ((n + i) + 1) ((n + i) + 1 + 1)) U _)).trans
        (heq_dependent_apply (fun d y => -(K.complex.d d (d + 1)).val.app U y) hni
          (hsh n i U x a))
    have hAct1 : HEq (((shMul (n + 1) i).app U) ((sh.d n (n + 1)).val.app U x) a)
        (-(((K.mul (n + 1 + 1) i).app U) ((K.complex.d (n + 1) (n + 1 + 1)).val.app U x) a)) :=
      (hsh (n + 1) i U _ a).trans (heq_of_eq
        ((congrArg (fun y => ((K.mul (n + 1 + 1) i).app U y) a)
          (hneg (K.complex.d (n + 1) (n + 1 + 1)) U x)).trans
          (congrArg (fun g => g a) (map_neg ((K.mul (n + 1 + 1) i).app U) _))))
    refine eq_of_heq (hL.trans ((heq_of_eq h).trans
      (heq_dependent_add (B := fun q => (K.complex.X q).val.obj U) (by omega) ?_ ?_)))
    · exact (heq_dependent_gradedCast K.complex.X U (fun _ y => -y)
        (add_right_comm (n + 1) 1 i) _).trans
        (hAct1.symm.trans (heq_gradedCast sh.X (add_right_comm n 1 i) U _).symm)
    · exact (heq_dependent_gradedCast K.complex.X U (fun _ y => (Int.negOnePow n : ℤ) • y)
        (add_assoc (n + 1) i 1).symm _).trans
        ((heq_dependent_apply (fun d (y : (K.complex.X d).val.obj U) => (Int.negOnePow n : ℤ) • y)
          (show (n + (i + 1)) + 1 = (n + 1) + (i + 1) by omega)
          (hsh n (i + 1) U x _)).symm.trans
          (heq_dependent_gradedCast sh.X U (fun _ y => (Int.negOnePow n : ℤ) • y)
            (add_assoc n i 1).symm _).symm)
  · intro n i U
    exact castBilinearMap_app_heq
      (congrArg K.complex.X (show (n + 1) + i = (n + i) + 1 by omega)) (K.mul (n + 1) i) U

/-- The degree-one shift of a right differential graded module exists with
the unchanged right action. -/
@[stacks 0FS5 "fixed shifted module for the canonical cone projection"]
theorem shiftPackage_nonempty {A : DifferentialGradedAlgebra.{t, a} R}
    (K : DifferentialGradedModule.{t, a, m} A) : Nonempty (ShiftPackage K) := ⟨shiftModel K⟩

/-- A choice of degree-one shift of a right differential graded module. -/
noncomputable def shiftPackage {A : DifferentialGradedAlgebra.{t, a} R}
    (K : DifferentialGradedModule.{t, a, m} A) : ShiftPackage K :=
  Classical.choice (shiftPackage_nonempty K)

/-- The degree-one shift of a differential graded module, with unchanged right action. -/
noncomputable abbrev shift {A : DifferentialGradedAlgebra.{t, a} R}
    (K : DifferentialGradedModule.{t, a, m} A) : DifferentialGradedModule.{t, a, m} A :=
  (shiftPackage K).shifted

/-! ### The cone of a morphism -/

/-- The full specification of the cone of a morphism of differential graded
modules, including its canonical maps and componentwise action. -/
structure ConePackage {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) where
  /-- The cone itself. -/
  cone : DifferentialGradedModule.{t, a, m} A
  /-- The canonical inclusion of the target. -/
  inclusion : L ⟶ cone
  /-- The canonical projection to the fixed degree-one shift of the source. -/
  projection : cone ⟶ shift K
  /-- The underlying complex is the mapping cone. -/
  cone_complex : cone.complex = CochainComplex.mappingCone f.toHomologicalComplex
  /-- The degreewise splitting of the cone into the shifted source and the target. -/
  componentIso (n : ℤ) :
    cone.complex.X n ≅ K.complex.X (n + 1) ⊞ L.complex.X n
  /-- The splitting is the canonical one of the mapping cone.

  The relation argument is written `(by simp)` rather than `rfl` on purpose. A bare `rfl` here
  elaborates against `(ComplexShape.up ℤ).Rel n (n + 1)` but stores `@rfl ℤ (n + 1)`, and the two
  agree only after unfolding the semireducible `ComplexShape.up`; a consumer that destructures
  this `HEq` then gets a goal which is not type-correct at the transparency `rw` and `simp` use
  to build a motive, and every subsequent rewrite fails. Elaborating at the `.Rel` type avoids
  that. The proposition is unchanged — it is a `Prop`, so this is proof irrelevance. -/
  componentIso_eq (n : ℤ) :
    HEq (componentIso n)
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        f.toHomologicalComplex n (n + 1) (by simp))
  /-- In the first coordinate the cone acts as the shifted source does. -/
  action_first (n i : ℤ) (U : Cᵒᵖ)
      (x : (cone.complex.X n).val.obj U)
      (a : (A.complex.X i).val.obj U) :
    HEq (((componentIso (n + i)).hom ≫ biprod.fst).val.app U
      ((cone.mul n i).app U x a))
      ((K.mul (n + 1) i).app U
        (((componentIso n).hom ≫ biprod.fst).val.app U x) a)
  /-- In the second coordinate the cone acts as the target does. -/
  action_second (n i : ℤ) (U : Cᵒᵖ)
      (x : (cone.complex.X n).val.obj U)
      (a : (A.complex.X i).val.obj U) :
    ((componentIso (n + i)).hom ≫ biprod.snd).val.app U
      ((cone.mul n i).app U x a) =
      (L.mul n i).app U
        (((componentIso n).hom ≫ biprod.snd).val.app U x) a
  /-- The inclusion is the canonical map of the mapping cone. -/
  inclusion_complex :
    HEq inclusion.toHomologicalComplex
      (CochainComplex.mappingCone.inr f.toHomologicalComplex)
  /-- The projection is the canonical map of the mapping cone. -/
  projection_complex :
    HEq projection.toHomologicalComplex
      (CochainComplex.HomComplex.Cocycle.homOf
      ((CochainComplex.mappingCone.fst f.toHomologicalComplex).rightShift
          1 0 (zero_add 1)))

/-- The isomorphism between the degree-`n` component of the mapping cone of `f` and the biproduct
`K.complex.X (n + 1) ⊞ L.complex.X n`. -/
noncomputable def coneComponentIso {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ) :
    (CochainComplex.mappingCone f.toHomologicalComplex).X n ≅
      K.complex.X (n + 1) ⊞ L.complex.X n :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod f.toHomologicalComplex n (n + 1) (by simp)

private noncomputable def coneBilinearMap {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n i : ℤ) :
    BilinearMap
      ((CochainComplex.mappingCone f.toHomologicalComplex).X n)
      (A.complex.X i)
      ((CochainComplex.mappingCone f.toHomologicalComplex).X (n + i)) := by
  let castK := castBilinearMap
    (congrArg K.complex.X (show (n + 1) + i = (n + i) + 1 by omega))
    (K.mul (n + 1) i)
  let sumMul := biprodBilinearMap castK (L.mul n i)
  exact transportBilinearMap
    (coneComponentIso f n).hom (coneComponentIso f (n + i)).inv sumMul

/-- An isomorphism of sheaves of modules is inverse to its inverse on local sections. -/
private theorem iso_hom_inv_val_app {X Y : SheafOfModules.{m} R} (e : X ≅ Y) (U : Cᵒᵖ)
    (y : Y.val.obj U) : e.hom.val.app U (e.inv.val.app U y) = y := by
  simp only [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, Iso.inv_hom_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply]

private theorem coneComponentIso_hom_inv_app {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ) (U : Cᵒᵖ)
    (x : (K.complex.X (n + 1) ⊞ L.complex.X n).val.obj U) :
    ((coneComponentIso f n).hom.val.app U) (((coneComponentIso f n).inv.val.app U) x) = x :=
  iso_hom_inv_val_app _ U x

private theorem coneComponentIso_inv_hom_app {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ) (U : Cᵒᵖ)
    (x : ((CochainComplex.mappingCone f.toHomologicalComplex).X n).val.obj U) :
    ((coneComponentIso f n).inv.val.app U) (((coneComponentIso f n).hom.val.app U) x) = x :=
  iso_hom_inv_val_app (coneComponentIso f n).symm U x

/-- The projection of the degree-`n` component of the mapping cone of `f` onto
`K.complex.X (n + 1)`. -/
noncomputable abbrev coneFirst {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ) :=
  (coneComponentIso f n).hom ≫ biprod.fst

/-- The projection of the degree-`n` component of the mapping cone of `f` onto `L.complex.X n`. -/
noncomputable abbrev coneSecond {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ) :=
  (coneComponentIso f n).hom ≫ biprod.snd

/-- `coneSecond f n` is Mathlib's second projection `HomologicalComplex.homotopyCofiber.sndX` of
the homotopy cofiber. -/
theorem coneSecond_eq {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ) :
    coneSecond f n = HomologicalComplex.homotopyCofiber.sndX f.toHomologicalComplex n := by
  show (HomologicalComplex.homotopyCofiber.XIsoBiprod
    f.toHomologicalComplex n (n + 1) rfl).hom ≫ biprod.snd = _
  have hn : (ComplexShape.up ℤ).next n = n + 1 :=
    (ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)
  unfold HomologicalComplex.homotopyCofiber.sndX
  split_ifs with hi
  · exact congrArg (fun j =>
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f.toHomologicalComplex n j.1 j.2).hom ≫
        (biprod.snd : K.complex.X j.1 ⊞ L.complex.X n ⟶ L.complex.X n))
      (show (⟨n + 1, rfl⟩ : {j // (ComplexShape.up ℤ).Rel n j}) = ⟨_, hi⟩ from
        Subtype.ext hn.symm)
  · rw [hn] at hi
    exact (hi rfl).elim

private theorem cone_ext {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ) (U : Cᵒᵖ)
    {x y : ((CochainComplex.mappingCone f.toHomologicalComplex).X n).val.obj U}
    (h₁ : (coneFirst f n).val.app U x = (coneFirst f n).val.app U y)
    (h₂ : (coneSecond f n).val.app U x = (coneSecond f n).val.app U y) : x = y := by
  have h : (coneComponentIso f n).hom.val.app U x = (coneComponentIso f n).hom.val.app U y :=
    biprodSections_ext _ _ U h₁ h₂
  have := congrArg (fun z => (coneComponentIso f n).inv.val.app U z) h
  simpa only [coneComponentIso_inv_hom_app] using this

private theorem cone_hext {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L)
    {n n' : ℤ} (h : n = n') (U : Cᵒᵖ)
    {x : ((CochainComplex.mappingCone f.toHomologicalComplex).X n).val.obj U}
    {y : ((CochainComplex.mappingCone f.toHomologicalComplex).X n').val.obj U}
    (h₁ : HEq ((coneFirst f n).val.app U x) ((coneFirst f n').val.app U y))
    (h₂ : HEq ((coneSecond f n).val.app U x) ((coneSecond f n').val.app U y)) :
    HEq x y := by
  subst n'
  exact heq_of_eq (cone_ext f n U (eq_of_heq h₁) (eq_of_heq h₂))

private theorem coneFirst_mul {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n i : ℤ)
    (U : Cᵒᵖ) (x : ((CochainComplex.mappingCone f.toHomologicalComplex).X n).val.obj U)
    (a : (A.complex.X i).val.obj U) :
    (coneFirst f (n + i)).val.app U ((coneBilinearMap f n i).app U x a) =
      (((shiftModel K).shifted.mul n i).app U) ((coneFirst f n).val.app U x) a := by
  show ((biprod.fst : K.complex.X (n + i + 1) ⊞ L.complex.X (n + i) ⟶ _).val.app U)
    ((coneComponentIso f (n + i)).hom.val.app U
      ((coneComponentIso f (n + i)).inv.val.app U _)) = _
  rw [coneComponentIso_hom_inv_app]
  exact biprodBilinearMap_fst _ _ U _ a

private theorem coneSecond_mul {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n i : ℤ)
    (U : Cᵒᵖ) (x : ((CochainComplex.mappingCone f.toHomologicalComplex).X n).val.obj U)
    (a : (A.complex.X i).val.obj U) :
    (coneSecond f (n + i)).val.app U ((coneBilinearMap f n i).app U x a) =
      (L.mul n i).app U ((coneSecond f n).val.app U x) a := by
  show ((biprod.snd : K.complex.X (n + i + 1) ⊞ L.complex.X (n + i) ⟶ _).val.app U)
    ((coneComponentIso f (n + i)).hom.val.app U
      ((coneComponentIso f (n + i)).inv.val.app U _)) = _
  rw [coneComponentIso_hom_inv_app]
  exact biprodBilinearMap_snd _ _ U _ a

private theorem coneFirst_d {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ)
    (U : Cᵒᵖ) (x : ((CochainComplex.mappingCone f.toHomologicalComplex).X n).val.obj U) :
    (coneFirst f (n + 1)).val.app U
      (((CochainComplex.mappingCone f.toHomologicalComplex).d n (n + 1)).val.app U x) =
    (((shiftModel K).shifted.complex.d n (n + 1)).val.app U)
      ((coneFirst f n).val.app U x) := by
  have h := congrArg (fun g => g.val.app U x)
    (HomologicalComplex.homotopyCofiber.d_fstX f.toHomologicalComplex
      n (n + 1) (n + 1 + 1) rfl rfl)
  show _ = ((-1 : ℤ) • K.complex.d (n + 1) (n + 1 + 1)).val.app U _
  simpa only [neg_one_zsmul, neg_val_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, Preadditive.neg_comp,
    HomologicalComplex.homotopyCofiber.fstX, coneComponentIso] using! h

private theorem coneSecond_d {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ)
    (U : Cᵒᵖ) (x : ((CochainComplex.mappingCone f.toHomologicalComplex).X n).val.obj U) :
    (coneSecond f (n + 1)).val.app U
      (((CochainComplex.mappingCone f.toHomologicalComplex).d n (n + 1)).val.app U x) =
    (f.toHomologicalComplex.f (n + 1)).val.app U ((coneFirst f n).val.app U x) +
      (L.complex.d n (n + 1)).val.app U ((coneSecond f n).val.app U x) := by
  have h := congrArg (fun g => g.val.app U x)
    (HomologicalComplex.homotopyCofiber.d_sndX f.toHomologicalComplex n (n + 1) rfl)
  simpa only [coneSecond_eq, SheafOfModules.add_val, PresheafOfModules.add_app, ModuleCat.hom_add,
    LinearMap.add_apply, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, Preadditive.neg_comp,
    HomologicalComplex.homotopyCofiber.fstX, coneComponentIso] using! h

private theorem shifted_map_mul {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n i : ℤ)
    (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
    (a : (A.complex.X i).val.obj U) :
    (f.toHomologicalComplex.f (n + i + 1)).val.app U
      (((shiftModel K).shifted.mul n i).app U x a) =
    gradedCast (fun q => (L.complex.X q).val.obj U) (add_right_comm n 1 i)
      ((L.mul (n + 1) i).app U ((f.toHomologicalComplex.f (n + 1)).val.app U x) a) := by
  have ha := castBilinearMap_eval_heq
    (congrArg K.complex.X (add_right_comm n 1 i)) (K.mul (n + 1) i) U x a
  have hf := heq_dependent_apply
    (fun q => fun z : (K.complex.X q).val.obj U =>
      (f.toHomologicalComplex.f q).val.app U z)
    (add_right_comm n 1 i).symm ha
  exact eq_of_heq (hf.trans ((heq_of_eq (f.map_mul (n + 1) i U x a)).trans
    (heq_gradedCast L.complex.X (add_right_comm n 1 i) U _).symm))

/-- The first coordinate of the image of a local section of `L.complex.X n` under the canonical
inclusion into the mapping cone is zero. -/
theorem coneFirst_inr {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ)
    (U : Cᵒᵖ) (x : (L.complex.X n).val.obj U) :
    (coneFirst f n).val.app U
      (((CochainComplex.mappingCone.inr f.toHomologicalComplex).f n).val.app U x) = 0 := by
  have h := congrArg (fun g => g.val.app U x)
    (HomologicalComplex.homotopyCofiber.inrX_fstX f.toHomologicalComplex n (n + 1) rfl)
  simpa only [zero_val_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply,
    HomologicalComplex.homotopyCofiber.fstX, coneComponentIso] using! h

/-- The second coordinate of the image of a local section `x` of `L.complex.X n` under the
canonical inclusion into the mapping cone is `x`. -/
theorem coneSecond_inr {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ)
    (U : Cᵒᵖ) (x : (L.complex.X n).val.obj U) :
    (coneSecond f n).val.app U
      (((CochainComplex.mappingCone.inr f.toHomologicalComplex).f n).val.app U x) = x := by
  have h := congrArg (fun g => g.val.app U x)
    (HomologicalComplex.homotopyCofiber.inrX_sndX f.toHomologicalComplex n)
  simpa only [coneSecond_eq, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using! h

/-- In degree `n`, the canonical projection from the mapping cone of `f` to the degree-one shift
of `K` is `coneFirst f n`. -/
theorem coneProjection_f {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) (n : ℤ) :
    (CochainComplex.HomComplex.Cocycle.homOf
      ((CochainComplex.mappingCone.fst f.toHomologicalComplex).rightShift
        1 0 (zero_add 1))).f n = coneFirst f n := by
  rw [CochainComplex.HomComplex.Cocycle.homOf_f,
    CochainComplex.HomComplex.Cocycle.rightShift_coe,
    CochainComplex.HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ (n + 1) rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, CochainComplex.mappingCone.fst,
    coneFirst, coneComponentIso, HomologicalComplex.homotopyCofiber.fstX]
  show (HomologicalComplex.homotopyCofiber.XIsoBiprod
    f.toHomologicalComplex n (n + 1) rfl).hom ≫ biprod.fst = _
  rfl

private theorem shiftPackage_transport_mul {A : DifferentialGradedAlgebra.{t, a} R}
    {K : DifferentialGradedModule.{t, a, m} A} (s : ShiftPackage K) (n i : ℤ)
    (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
    (a : (A.complex.X i).val.obj U) :
    ((eqToHom s.shifted_complex.symm).f (n + i)).val.app U
      (((shiftModel K).shifted.mul n i).app U x a) =
    (s.shifted.mul n i).app U (((eqToHom s.shifted_complex.symm).f n).val.app U x) a := by
  rcases s with ⟨⟨c, μ, h_assoc, h_one, h_leib⟩, hc, ha⟩
  dsimp only at hc ha ⊢
  subst c
  have hm := eq_of_heq ((ha n i U).trans ((shiftModel K).shifted_action n i U).symm)
  show (((shiftModel K).shifted.mul n i).app U x a) = (μ n i).app U x a
  exact congrArg (fun g => g x a) hm.symm

/-- The mapping-cone construction exists with its componentwise action and
canonical inclusion and projection. -/
@[stacks 0FS5 "existence of the cone with its canonical maps"]
theorem conePackage_nonempty {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) : Nonempty (ConePackage f) := by
  let mc := CochainComplex.mappingCone f.toHomologicalComplex
  let hshift := (shiftPackage K).shifted_complex
  let coneObj : DifferentialGradedModule.{t, a, m} A := {
    complex := mc
    mul := coneBilinearMap f
    mul_assoc := by
      intro n i j U x a b
      apply cone_hext f (add_assoc n i j) U
      · rw [coneFirst_mul f, coneFirst_mul f, coneFirst_mul f]
        exact (shiftModel K).shifted.mul_assoc n i j U _ a b
      · rw [coneSecond_mul f, coneSecond_mul f, coneSecond_mul f]
        exact L.mul_assoc n i j U _ a b
    mul_one := by
      intro n U x
      apply cone_hext f (add_zero n) U
      · rw [coneFirst_mul]
        exact (shiftModel K).shifted.mul_one n U _
      · rw [coneSecond_mul]
        exact L.mul_one n U _
    leibniz := by
      intro n i U x a
      dsimp only [mc]
      apply cone_ext f (n + i + 1) U
      · simp only [map_add, map_zsmul,
          gradedCast_dependent_apply (fun q => (coneFirst f q).val.app U),
          coneFirst_d, coneFirst_mul]
        exact (shiftModel K).shifted.leibniz n i U _ a
      · simp only [map_add, map_zsmul,
          gradedCast_dependent_apply (fun q => (coneSecond f q).val.app U),
          coneSecond_d, coneSecond_mul]
        rw [coneFirst_mul f, shifted_map_mul f, L.leibniz]
        simp only [AddMonoidHom.add_apply, gradedCast_add]
        abel
  }
  let inc : L ⟶ coneObj := {
    toHomologicalComplex := CochainComplex.mappingCone.inr f.toHomologicalComplex
    map_mul := by
      intro n i U x a
      dsimp only [coneObj]
      apply cone_ext f (n + i) U
      · rw [coneFirst_inr f, coneFirst_mul f, coneFirst_inr f]
        simp only [map_zero, AddMonoidHom.zero_apply]
      · rw [coneSecond_inr f, coneSecond_mul f, coneSecond_inr f]
  }
  let rawProjection := CochainComplex.HomComplex.Cocycle.homOf
    ((CochainComplex.mappingCone.fst f.toHomologicalComplex).rightShift 1 0 (zero_add 1))
  let proj : coneObj ⟶ shift K := {
    toHomologicalComplex := rawProjection ≫ eqToHom hshift.symm
    map_mul := by
      intro n i U x a
      show ((eqToHom hshift.symm).f (n + i)).val.app U
        ((rawProjection.f (n + i)).val.app U ((coneBilinearMap f n i).app U x a)) =
        ((shift K).mul n i).app U
          (((eqToHom hshift.symm).f n).val.app U ((rawProjection.f n).val.app U x)) a
      dsimp only [rawProjection]
      rw [coneProjection_f, coneProjection_f]
      exact (congrArg (fun z => ((eqToHom hshift.symm).f (n + i)).val.app U z)
        (coneFirst_mul f n i U x a)).trans
          (shiftPackage_transport_mul (shiftPackage K) n i U _ a)
  }
  refine ⟨{
    cone := coneObj
    inclusion := inc
    projection := proj
    cone_complex := rfl
    componentIso := coneComponentIso f
    componentIso_eq := by intro n; rfl
    action_first := by
      intro n i U x a
      exact (heq_of_eq (coneFirst_mul f n i U x a)).trans
        (castBilinearMap_eval_heq
          (congrArg K.complex.X (add_right_comm n 1 i)) (K.mul (n + 1) i) U _ a)
    action_second := coneSecond_mul f
    inclusion_complex := by rfl
    projection_complex := comp_eqToHom_heq rawProjection hshift.symm
  }⟩

/-- The cone and its canonical maps, characterized by the
mapping-cone complex and the direct-sum action. -/
@[stacks 0FS5 "the cone construction"]
noncomputable def conePackage {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) : ConePackage f :=
  Classical.choice (conePackage_nonempty f)

/-- The cone of a morphism of differential graded modules. -/
noncomputable abbrev cone {A : DifferentialGradedAlgebra.{t, a} R}
    {K L : DifferentialGradedModule.{t, a, m} A} (f : K ⟶ L) :
    DifferentialGradedModule.{t, a, m} A :=
  (conePackage f).cone

end SheafOfModules.DifferentialGradedModule
