module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Serre functors on linear categories

A Serre functor on a `k`-linear category is a linear self-equivalence `S` together with a
bifunctorial family of `k`-linear isomorphisms `(X ⟶ Y) ≃ₗ[k] (Y ⟶ S X)^∨`. For a Hom-finite
linear category the existence of such a structure is equivalent to representability of the
presheaf `Y ↦ (X ⟶ Y)^∨` and corepresentability of the copresheaf `Y ↦ (Y ⟶ X)^∨`, for every
object `X`.

## Main definitions

* `CategoryTheory.homDualPresheaf` is the presheaf `Y ↦ (X ⟶ Y)^∨`.
* `CategoryTheory.homDualCopresheaf` is the copresheaf `Y ↦ (Y ⟶ X)^∨`.
* `CategoryTheory.SerreEquivalence` packages a linear self-equivalence together with its
  bifunctorial Serre pairing.

## Main results

* `CategoryTheory.nonempty_serreEquivalence_iff` is the representability criterion for the
  existence of a Serre equivalence.

## Implementation notes

Functoriality of the Serre isomorphisms in both variables is recorded explicitly as the two
fields `pairing_naturality_left` and `pairing_naturality_right`. The representability
conditions are stated for the underlying type-valued functors, matching Mathlib's
`CategoryTheory.Functor.IsRepresentable` and `CategoryTheory.Functor.IsCorepresentable`. No
triangulated structure is assumed, because the representability argument does not use one.
The field, the objects and the morphisms have independent universes; the dual Hom functors
take values in modules in the maximum of the field and morphism universes.

## References

* [Stacks Project, Tag 0FY4](https://stacks.math.columbia.edu/tag/0FY4)
* [Stacks Project, Tag 0FY5](https://stacks.math.columbia.edu/tag/0FY5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory

variable (k : Type u) [Field k]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]

/-- The presheaf sending `Y` to the linear dual of `Hom(X, Y)`. -/
def homDualPresheaf (X : C) : Cᵒᵖ ⥤ ModuleCat.{max u w} k where
  obj Y := ModuleCat.of k (Module.Dual k (X ⟶ Y.unop))
  map f := ModuleCat.ofHom (Linear.rightComp k X f.unop).dualMap
  map_id Y := by
    ext φ g
    simp
  map_comp f g := by
    ext φ h
    simp

private theorem homDualPresheaf_map_eval {X Y Z : C} (f : Y ⟶ Z)
    (φ : Module.Dual k (X ⟶ Z)) (g : X ⟶ Y) :
    (show Module.Dual k (X ⟶ Y) from
      (ConcreteCategory.hom
        ((homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).map f.op)) φ) g =
      φ (g ≫ f) := by
  show ((Linear.rightComp k X f).dualMap φ) g = φ (g ≫ f)
  simp [LinearMap.dualMap_apply]

/-- The copresheaf sending `Y` to the linear dual of `Hom(Y, X)`. -/
def homDualCopresheaf (X : C) : C ⥤ ModuleCat.{max u w} k where
  obj Y := ModuleCat.of k (Module.Dual k (Y ⟶ X))
  map f := ModuleCat.ofHom (Linear.leftComp k X f).dualMap
  map_id Y := by
    ext φ g
    simp
  map_comp f g := by
    ext φ h
    simp

private theorem homDualCopresheaf_map_eval {X Y Z : C} (f : Y ⟶ Z)
    (φ : Module.Dual k (Y ⟶ X)) (g : Z ⟶ X) :
    (show Module.Dual k (Z ⟶ X) from
      (ConcreteCategory.hom
        ((homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).map f)) φ) g =
      φ (f ≫ g) := by
  show ((Linear.leftComp k X f).dualMap φ) g = φ (f ≫ g)
  simp [LinearMap.dualMap_apply]

/-- **Stacks Project, Tag 0FY5.** A linear self-equivalence together with a bifunctorial family
of Serre duality isomorphisms. -/
structure SerreEquivalence where
  /-- The self-equivalence underlying the Serre equivalence. -/
  equivalence : C ≌ C
  /-- The self-equivalence is linear over the ground field. -/
  linear : Functor.Linear k equivalence.functor
  /-- The Serre duality isomorphism. -/
  pairing : ∀ X Y : C,
    (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ equivalence.functor.obj X)
  /-- Naturality of the pairing in its first variable. -/
  pairing_naturality_left : ∀ {X X' Y : C} (f : X' ⟶ X) (g : X ⟶ Y),
    pairing X' Y (f ≫ g) =
      (Linear.rightComp k Y (equivalence.functor.map f)).dualMap (pairing X Y g)
  /-- Naturality of the pairing in its second variable. -/
  pairing_naturality_right : ∀ {X Y Y' : C} (f : X ⟶ Y) (g : Y ⟶ Y'),
    pairing X Y' (f ≫ g) =
      (Linear.leftComp k (equivalence.functor.obj X) g).dualMap (pairing X Y f)

add_to_stacks 0FY5 CategoryTheory.SerreEquivalence

private noncomputable def chosenRep
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (X : C) : C := by
  letI := h X
  exact (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).reprX

private noncomputable def chosenRepBy
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (X : C) : (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).RepresentableBy
      (chosenRep k h X) := by
  letI := h X
  exact (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).representableBy

private noncomputable def chosenCorep
    (h : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    (X : C) : C := by
  letI := h X
  exact (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).coreprX

private noncomputable def chosenCorepBy
    (h : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    (X : C) : (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).CorepresentableBy
      (chosenCorep k h X) := by
  letI := h X
  exact (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).corepresentableBy

private noncomputable def chosenRepLinearEquiv
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (X Y : C) : (Y ⟶ chosenRep k h X) ≃ₗ[k] Module.Dual k (X ⟶ Y) := by
  let R := chosenRepBy k h X
  refine
    { toFun := R.homEquiv
      invFun := R.homEquiv.symm
      left_inv := R.homEquiv.left_inv
      right_inv := R.homEquiv.right_inv
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    ext z
    rw [R.homEquiv_eq (f + g), R.homEquiv_eq f, R.homEquiv_eq g]
    change (R.homEquiv (𝟙 _)).toFun (z ≫ (f + g)) =
      (R.homEquiv (𝟙 _)).toFun (z ≫ f) + (R.homEquiv (𝟙 _)).toFun (z ≫ g)
    simp
  · intro a f
    ext z
    rw [R.homEquiv_eq (a • f), R.homEquiv_eq f]
    change (R.homEquiv (𝟙 _)).toFun (z ≫ (a • f)) =
      a * (R.homEquiv (𝟙 _)).toFun (z ≫ f)
    rw [Linear.comp_smul]
    change (R.homEquiv (𝟙 _)).toFun (a • (z ≫ f)) =
      a * (R.homEquiv (𝟙 _)).toFun (z ≫ f)
    exact (R.homEquiv (𝟙 _)).map_smul a (z ≫ f)

private theorem chosenRepLinearEquiv_apply
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (X Y : C) (f : Y ⟶ chosenRep k h X) :
    chosenRepLinearEquiv k h X Y f = (chosenRepBy k h X).homEquiv f := rfl

private theorem chosenRepLinearEquiv_naturality
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    {X Y Y' : C} (f : Y ⟶ Y') (g : Y' ⟶ chosenRep k h X) :
    chosenRepLinearEquiv k h X Y (f ≫ g) =
      ((homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).map f.op)
        (chosenRepLinearEquiv k h X Y' g) := by
  rw [chosenRepLinearEquiv_apply, chosenRepLinearEquiv_apply]
  exact (chosenRepBy k h X).homEquiv_comp f g

private theorem chosenRepLinearEquiv_apply_comp
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    {X Y : C} (a : Y ⟶ chosenRep k h X) (g : X ⟶ Y) :
    chosenRepLinearEquiv k h X Y a g =
      chosenRepLinearEquiv k h X (chosenRep k h X) (𝟙 _) (g ≫ a) := by
  have hn := congrArg (fun φ => φ g)
    (chosenRepLinearEquiv_naturality k h a (𝟙 _))
  rw [Category.comp_id, homDualPresheaf_map_eval] at hn
  simpa [Category.assoc] using hn

private noncomputable def serreFunctorMap
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    {X X' : C} (f : X ⟶ X') : chosenRep k h X ⟶ chosenRep k h X' :=
  (chosenRepLinearEquiv k h X' (chosenRep k h X)).symm
    ((Linear.leftComp k (chosenRep k h X) f).dualMap
      (chosenRepLinearEquiv k h X (chosenRep k h X) (𝟙 _)))

private theorem serreFunctorMap_spec
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    {X X' : C} (f : X ⟶ X') :
    chosenRepLinearEquiv k h X' (chosenRep k h X) (serreFunctorMap k h f) =
      (Linear.leftComp k (chosenRep k h X) f).dualMap
        (chosenRepLinearEquiv k h X (chosenRep k h X) (𝟙 _)) := by
  simp [serreFunctorMap]

private theorem serreFunctorMap_naturality_eval
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    {X X' : C} (f : X' ⟶ X) (w : X ⟶ chosenRep k h X') :
    chosenRepLinearEquiv k h X' (chosenRep k h X') (𝟙 _) (f ≫ w) =
      chosenRepLinearEquiv k h X (chosenRep k h X) (𝟙 _) (w ≫ serreFunctorMap k h f) := by
  have hs := congrArg (fun φ => φ w) (serreFunctorMap_spec k h f)
  rw [chosenRepLinearEquiv_apply_comp] at hs
  simpa [LinearMap.dualMap_apply, Linear.leftComp_apply, Category.assoc] using hs.symm

private noncomputable def serreFunctor
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable) :
    C ⥤ C where
  obj X := chosenRep k h X
  map := serreFunctorMap k h
  map_id X := by
    apply (chosenRepLinearEquiv k h X (chosenRep k h X)).injective
    ext z
    simp [serreFunctorMap]
  map_comp {X Y Z} f g := by
    apply (chosenRepLinearEquiv k h Z (chosenRep k h X)).injective
    rw [chosenRepLinearEquiv_naturality k h (serreFunctorMap k h f) (serreFunctorMap k h g)]
    rw [serreFunctorMap_spec k h (f ≫ g), serreFunctorMap_spec k h g]
    ext z
    rw [homDualPresheaf_map_eval]
    simp only [LinearMap.dualMap_apply, Linear.leftComp_apply]
    simpa [Category.assoc] using serreFunctorMap_naturality_eval k h f (g ≫ z)

private theorem serreFunctorLinear
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable) :
    Functor.Linear k (serreFunctor k h) := by
  refine ⟨?_⟩
  intro X X' f a
  show serreFunctorMap k h (a • f) = a • serreFunctorMap k h f
  apply (chosenRepLinearEquiv k h X' (chosenRep k h X)).injective
  ext z
  simp only [serreFunctorMap, LinearEquiv.apply_symm_apply]
  rw [(chosenRepLinearEquiv k h X' (chosenRep k h X)).map_smul]
  simp only [LinearMap.dualMap_apply]
  simp [Linear.smul_comp]

private noncomputable def chosenCorepLinearEquiv
    (h : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    (X Y : C) : (chosenCorep k h X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ X) := by
  let R := chosenCorepBy k h X
  refine
    { toFun := R.homEquiv
      invFun := R.homEquiv.symm
      left_inv := R.homEquiv.left_inv
      right_inv := R.homEquiv.right_inv
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    ext z
    rw [R.homEquiv_eq (f + g), R.homEquiv_eq f, R.homEquiv_eq g]
    change (R.homEquiv (𝟙 _)).toFun ((f + g) ≫ z) =
      (R.homEquiv (𝟙 _)).toFun (f ≫ z) + (R.homEquiv (𝟙 _)).toFun (g ≫ z)
    simp
  · intro a f
    ext z
    rw [R.homEquiv_eq (a • f), R.homEquiv_eq f]
    change (R.homEquiv (𝟙 _)).toFun ((a • f) ≫ z) =
      a * (R.homEquiv (𝟙 _)).toFun (f ≫ z)
    rw [Linear.smul_comp]
    exact (R.homEquiv (𝟙 _)).map_smul a (f ≫ z)

private theorem chosenCorepLinearEquiv_apply
    (h : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    (X Y : C) (f : chosenCorep k h X ⟶ Y) :
    chosenCorepLinearEquiv k h X Y f = (chosenCorepBy k h X).homEquiv f := rfl

private theorem chosenCorepLinearEquiv_naturality
    (h : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    {X Y Y' : C} (f : Y ⟶ Y') (g : chosenCorep k h X ⟶ Y) :
    chosenCorepLinearEquiv k h X Y' (g ≫ f) =
      ConcreteCategory.hom ((homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).map f)
        (chosenCorepLinearEquiv k h X Y g) := by
  rw [chosenCorepLinearEquiv_apply, chosenCorepLinearEquiv_apply]
  exact (chosenCorepBy k h X).homEquiv_comp f g

private noncomputable def serrePairingOfRepresentable
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (X Y : C) :
    (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ chosenRep k h X) := by
  letI : Module.IsReflexive k (X ⟶ Y) := inferInstance
  exact (Module.evalEquiv k (X ⟶ Y)).trans (chosenRepLinearEquiv k h X Y).dualMap

private noncomputable def inverseSerrePairingOfCorepresentable
    (h : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (X Y : C) :
    (Y ⟶ X) ≃ₗ[k] Module.Dual k (chosenCorep k h X ⟶ Y) := by
  letI : Module.IsReflexive k (Y ⟶ X) := inferInstance
  exact (Module.evalEquiv k (Y ⟶ X)).trans (chosenCorepLinearEquiv k h X Y).dualMap

private theorem inverseSerrePairingOfCorepresentable_apply
    (h : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (X Y : C) (a : Y ⟶ X)
    (z : chosenCorep k h X ⟶ Y) :
    inverseSerrePairingOfCorepresentable k h X Y a z =
      chosenCorepLinearEquiv k h X Y z a := by
  simp [inverseSerrePairingOfCorepresentable, Module.evalEquiv,
    LinearEquiv.dualMap_apply]

private theorem inverseSerrePairingOfCorepresentable_naturality
    (h : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    {X Y Y' : C} (f : Y ⟶ Y') (g : Y' ⟶ X) :
    inverseSerrePairingOfCorepresentable k h X Y (f ≫ g) =
      (Linear.rightComp k (chosenCorep k h X) f).dualMap
        (inverseSerrePairingOfCorepresentable k h X Y' g) := by
  ext z
  rw [inverseSerrePairingOfCorepresentable_apply]
  simp only [LinearMap.dualMap_apply, Linear.rightComp_apply,
    inverseSerrePairingOfCorepresentable_apply]
  have hn := congrArg (fun φ => φ g)
    (chosenCorepLinearEquiv_naturality k h f z)
  rw [homDualCopresheaf_map_eval] at hn
  simpa [LinearMap.dualMap_apply, Linear.rightComp_apply] using hn.symm

private theorem serrePairingOfRepresentable_apply
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] (X Y : C) (g : X ⟶ Y)
    (φ : Y ⟶ chosenRep k h X) :
    serrePairingOfRepresentable k h X Y g φ = chosenRepLinearEquiv k h X Y φ g := by
  simp [serrePairingOfRepresentable, Module.evalEquiv, LinearEquiv.dualMap_apply]

private theorem serrePairingOfRepresentable_naturality_left
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    {X X' Y : C} (f : X' ⟶ X) (g : X ⟶ Y) :
    serrePairingOfRepresentable k h X' Y (f ≫ g) =
      (Linear.rightComp k Y (serreFunctorMap k h f)).dualMap
        (serrePairingOfRepresentable k h X Y g) := by
  ext φ
  simp only [LinearMap.dualMap_apply, Linear.rightComp_apply,
    serrePairingOfRepresentable_apply]
  rw [chosenRepLinearEquiv_apply_comp k h φ (f ≫ g)]
  rw [chosenRepLinearEquiv_apply_comp k h (φ ≫ serreFunctorMap k h f) g]
  simpa [Category.assoc] using serreFunctorMap_naturality_eval k h f (g ≫ φ)

private theorem serrePairingOfRepresentable_naturality_right
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    {X Y Y' : C} (g : X ⟶ Y) (f : Y ⟶ Y') :
    serrePairingOfRepresentable k h X Y' (g ≫ f) =
      (Linear.leftComp k (chosenRep k h X) f).dualMap
        (serrePairingOfRepresentable k h X Y g) := by
  ext φ
  simp only [LinearMap.dualMap_apply, Linear.leftComp_apply,
    serrePairingOfRepresentable_apply]
  rw [chosenRepLinearEquiv_apply_comp k h φ (g ≫ f)]
  rw [chosenRepLinearEquiv_apply_comp k h (f ≫ φ) g]
  simp [Category.assoc]

private noncomputable def serreFunctorTargetPairing
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (X Y : C) :
    ((serreFunctor k h).obj X ⟶ (serreFunctor k h).obj Y) ≃ₗ[k]
      Module.Dual k (Y ⟶ chosenRep k h X) :=
  (Module.evalEquiv k ((serreFunctor k h).obj X ⟶ (serreFunctor k h).obj Y)).trans
    (serrePairingOfRepresentable k h Y (chosenRep k h X)).dualMap

private theorem serreFunctorTargetPairing_apply
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (X Y : C) (a : (serreFunctor k h).obj X ⟶ (serreFunctor k h).obj Y)
    (z : Y ⟶ chosenRep k h X) :
    serreFunctorTargetPairing k h X Y a z =
      serrePairingOfRepresentable k h Y (chosenRep k h X) z a := by
  show ((serrePairingOfRepresentable k h Y (chosenRep k h X)).dualMap
    (Module.evalEquiv k ((serreFunctor k h).obj X ⟶ (serreFunctor k h).obj Y) a)) z = _
  show (Module.Dual.eval k ((serreFunctor k h).obj X ⟶ (serreFunctor k h).obj Y) a)
      (serrePairingOfRepresentable k h Y (chosenRep k h X) z) = _
  rfl

private noncomputable def serreFunctorHomLinearEquiv
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (X Y : C) : (X ⟶ Y) ≃ₗ[k]
      ((serreFunctor k h).obj X ⟶ (serreFunctor k h).obj Y) :=
  (serrePairingOfRepresentable k h X Y).trans
    (serreFunctorTargetPairing k h X Y).symm

private theorem serreFunctorHomLinearEquiv_map
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    {X Y : C} (f : X ⟶ Y) :
    serreFunctorHomLinearEquiv k h X Y f = (serreFunctor k h).map f := by
  apply (serreFunctorTargetPairing k h X Y).injective
  show (serreFunctorTargetPairing k h X Y)
      ((serrePairingOfRepresentable k h X Y).trans
        (serreFunctorTargetPairing k h X Y).symm f) =
    (serreFunctorTargetPairing k h X Y) ((serreFunctor k h).map f)
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext z
  have hleft := congrArg (fun q => q (𝟙 _))
    (serrePairingOfRepresentable_naturality_left k h f z)
  have hright := congrArg (fun q => q (𝟙 _))
    (serrePairingOfRepresentable_naturality_right k h f z)
  rw [serreFunctorTargetPairing_apply]
  simpa [serreFunctor, LinearMap.dualMap_apply, Linear.rightComp_apply,
    Linear.leftComp_apply, Category.assoc] using hright.symm.trans hleft

private noncomputable def serreCounitRepresentableBy
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (hr : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (hc : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    (X : C) : (yoneda.obj X).RepresentableBy
      (chosenRep k hr (chosenCorep k hc X)) := by
  refine { homEquiv := ?_, homEquiv_comp := ?_ }
  · intro Y
    exact ((chosenRepLinearEquiv k hr (chosenCorep k hc X) Y).trans
      (inverseSerrePairingOfCorepresentable k hc X Y).symm).toEquiv
  · intro Y Y' f g
    apply (inverseSerrePairingOfCorepresentable k hc X Y).injective
    simp only [LinearEquiv.coe_toEquiv, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
    change chosenRepLinearEquiv k hr (chosenCorep k hc X) Y (f ≫ g) =
      inverseSerrePairingOfCorepresentable k hc X Y
        (f ≫ (inverseSerrePairingOfCorepresentable k hc X Y').symm
          (chosenRepLinearEquiv k hr (chosenCorep k hc X) Y' g))
    rw [inverseSerrePairingOfCorepresentable_naturality k hc]
    simp only [LinearEquiv.apply_symm_apply]
    rw [chosenRepLinearEquiv_naturality k hr]
    rfl

private noncomputable def serreCounitIsoApp
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (hr : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (hc : ∀ X : C, (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable)
    (X : C) : chosenRep k hr (chosenCorep k hc X) ≅ X :=
  (Yoneda.fullyFaithful.preimageIso (serreCounitRepresentableBy k hr hc X).toIso)

private noncomputable def serreRepByOfEquivalence
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (s : SerreEquivalence k (C := C)) (X : C) :
    (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).RepresentableBy
      (s.equivalence.functor.obj X) := by
  refine { homEquiv := ?_, homEquiv_comp := ?_ }
  · intro Y
    letI : Module.IsReflexive k (Y ⟶ s.equivalence.functor.obj X) := inferInstance
    exact ((Module.evalEquiv k (Y ⟶ s.equivalence.functor.obj X)).trans
      (s.pairing X Y).dualMap).toEquiv
  · intro Y Y' f g
    let : Module.IsReflexive k (Y ⟶ s.equivalence.functor.obj X) := inferInstance
    let : Module.IsReflexive k (Y' ⟶ s.equivalence.functor.obj X) := inferInstance
    change ((Module.evalEquiv k (Y ⟶ s.equivalence.functor.obj X)).trans
      (s.pairing X Y).dualMap).toEquiv (f ≫ g) =
      ConcreteCategory.hom ((homDualPresheaf k X).map f.op)
        (((Module.evalEquiv k (Y' ⟶ s.equivalence.functor.obj X)).trans
          (s.pairing X Y').dualMap).toEquiv g)
    ext φ
    change s.pairing X Y φ (f ≫ g) = s.pairing X Y' (φ ≫ f) g
    have hn := congrArg (fun q => q g) (s.pairing_naturality_right φ f)
    simpa only [LinearMap.dualMap_apply, Linear.leftComp_apply] using hn.symm

private noncomputable def serreIsoRightComp
    {A B Y : C} (e : A ≅ B) : (Y ⟶ A) ≃ₗ[k] (Y ⟶ B) where
  toFun := Linear.rightComp k Y e.hom
  invFun := Linear.rightComp k Y e.inv
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp
  map_smul' a f := by simp

private noncomputable def serreCorepByOfEquivalence
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (s : SerreEquivalence k (C := C)) (X : C) :
    (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).CorepresentableBy
      (s.equivalence.inverse.obj X) := by
  let A := s.equivalence.inverse.obj X
  let e := s.equivalence.counitIso.app X
  refine { homEquiv := ?_, homEquiv_comp := ?_ }
  · intro Y
    change (A ⟶ Y) ≃ Module.Dual k (Y ⟶ X)
    simpa using ((s.pairing A Y).trans (serreIsoRightComp k e).symm.dualMap).toEquiv
  · intro Y Y' f g
    change ((s.pairing A Y').trans (serreIsoRightComp k e).symm.dualMap).toEquiv
        (g ≫ f) =
      ConcreteCategory.hom ((homDualCopresheaf k X).map f)
        (((s.pairing A Y).trans (serreIsoRightComp k e).symm.dualMap).toEquiv g)
    ext φ
    simp only [LinearEquiv.coe_toEquiv, LinearEquiv.trans_apply,
      LinearEquiv.dualMap_apply]
    change s.pairing A Y' (g ≫ f) ((serreIsoRightComp k e).symm φ) =
      (Linear.leftComp k X f).dualMap
        ((serreIsoRightComp k e).symm.dualMap (s.pairing A Y g)) φ
    simp only [LinearMap.dualMap_apply, LinearEquiv.dualMap_apply,
      Linear.leftComp_apply, serreIsoRightComp]
    have hn := congrArg (fun q => q (φ ≫ e.inv))
      (s.pairing_naturality_right g f)
    simpa [serreIsoRightComp, Category.assoc] using hn

private theorem serreFunctorFull
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable) :
    Functor.Full (serreFunctor k h) where
  map_surjective {X Y} g := by
    refine ⟨(serreFunctorHomLinearEquiv k h X Y).symm g, ?_⟩
    rw [← serreFunctorHomLinearEquiv_map k h]
    exact (serreFunctorHomLinearEquiv k h X Y).apply_symm_apply g

private theorem serreFunctorFaithful
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (h : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable) :
    Functor.Faithful (serreFunctor k h) where
  map_injective := by
    intro X Y f g hfg
    apply (serreFunctorHomLinearEquiv k h X Y).injective
    simpa only [serreFunctorHomLinearEquiv_map] using hfg

private theorem serreFunctorEssSurj
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
    (hr : ∀ X : C, (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable)
    (hc : ∀ X : C,
      (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable) :
    (serreFunctor k hr).EssSurj where
  mem_essImage X := ⟨chosenCorep k hc X, ⟨serreCounitIsoApp k hr hc X⟩⟩

/-- **Stacks Project, Tag 0FY4.** A Hom-finite linear category admits a Serre equivalence
exactly when both dual Hom functors are representable in the appropriate variance. -/
@[stacks 0FY4]
lemma nonempty_serreEquivalence_iff
    [∀ X Y : C, FiniteDimensional k (X ⟶ Y)] :
    Nonempty (SerreEquivalence k (C := C)) ↔
      (∀ X : C,
        (homDualPresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsRepresentable) ∧
        (∀ X : C,
          (homDualCopresheaf k X ⋙ forget (ModuleCat.{max u w} k)).IsCorepresentable) := by
  refine ⟨fun ⟨s⟩ => ⟨fun X => (serreRepByOfEquivalence k s X).isRepresentable,
    fun X => (serreCorepByOfEquivalence k s X).isCorepresentable⟩, fun ⟨hr, hc⟩ => ?_⟩
  have := serreFunctorFull k hr
  have := serreFunctorFaithful k hr
  have := serreFunctorEssSurj k hr hc
  have : (serreFunctor k hr).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨{
    equivalence := (serreFunctor k hr).asEquivalence
    linear := serreFunctorLinear k hr
    pairing := serrePairingOfRepresentable k hr
    pairing_naturality_left := fun f g => serrePairingOfRepresentable_naturality_left k hr f g
    pairing_naturality_right := fun f g => serrePairingOfRepresentable_naturality_right k hr f g }⟩

end CategoryTheory
