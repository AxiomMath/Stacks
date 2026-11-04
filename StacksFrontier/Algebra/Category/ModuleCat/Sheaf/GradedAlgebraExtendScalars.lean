module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearChangeOfRings

/-!
# Extension of scalars of a sheaf of graded algebras

Let `θ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a site whose underlying
presheaves of rings are sheaves. Extension of scalars along `θ` carries a sheaf of graded
`O₁`-algebras to a sheaf of graded `O₂`-algebras, degree by degree: the homogeneous pieces of
the result are the extensions of scalars of the homogeneous pieces, and the multiplication and
unit are induced by `(a ⊗ x) · (c ⊗ y) = ac ⊗ xy` and `1 ⊗ 1`.

## Main definitions

* `changeOfRingsGradedAlgebra`: the base change of a graded algebra of presheaves of modules
  along `θ`, with homogeneous pieces the sectionwise tensor products.
* `forgetSheaf`: a sheaf of graded algebras, read as a graded algebra of presheaves of modules.
* `extendScalarsGradedAlgebra`: the extension of scalars of a sheaf of graded algebras.
* `extendScalarsGradedAlgebraHom`: the extension of scalars of a homomorphism of sheaves of
  graded algebras.
* `extendScalarsGradedAlgebraFunctor`: extension of scalars as a functor.

## Main results

* `extendScalarsGradedAlgebra_piece`: the homogeneous pieces are the extensions of scalars of
  the original homogeneous pieces.
* `extendScalarsGradedAlgebra_mul_unit`: the multiplication on the images of pure tensors under
  the sheafification unit is the one induced by the original multiplication.
* `extendScalarsGradedAlgebra_one_eval`: the unit is the image of `1 ⊗ 1`.
* `extendScalarsGradedAlgebraFunctor_map_app`: the degreewise components of the extension of
  scalars of a homomorphism are the extensions of scalars of its degreewise components.

## Implementation notes

The construction is the sectionwise base change `changeOfRingsGradedAlgebra` followed by
`Stacks.GradedAlgebra.sheafify` along the identity of the presheaf of rings underlying `O₂`.
These are the two factors of `Stacks.Sheaves.RingedToposModules.extendScalars`, so the
homogeneous pieces are equal to the extensions of scalars of the original pieces, by `rfl`.

The associativity and unit laws of a graded algebra are heterogeneous equalities, because the
two sides live in homogeneous pieces whose degrees agree only propositionally; `heq_cof_add`,
`heq_cof_zero` and `heq_cof_tmul` transport them through sums, zeros and pure tensors.

The algebra structure on the sections of `O₂` over those of `O₁` is the one induced by `θ` at
each object of the site, introduced by `letI` at each use.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory TensorProduct Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.BilinearChangeOfRings Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.GradedAlgebraExtendScalars

universe v u w

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)

/-- Heterogeneous congruence for pure tensors along an equality of degrees. -/
public lemma heq_cof_tmul {Q : ℤ → PMod O₁} {d₁ d₂ : ℤ} (hd : d₁ = d₂) {X : Cᵒᵖ}
    (a : O₂.obj X) {x : (Q d₁).obj X} {y : (Q d₂).obj X} (hxy : HEq x y) :
    letI := (θ.app X).hom.toAlgebra
    HEq (a ⊗ₜ[O₁.obj X] x) (a ⊗ₜ[O₁.obj X] y) := by
  let := (θ.app X).hom.toAlgebra
  subst hd
  exact heq_of_eq (congrArg (fun t => a ⊗ₜ[O₁.obj X] t) (eq_of_heq hxy))

/-- The zero sections of two change-of-rings presheaves of equal degree agree. -/
public lemma heq_cof_zero {Q : ℤ → PMod O₁} {d₁ d₂ : ℤ} (hd : d₁ = d₂) (X : Cᵒᵖ) :
    HEq (0 : cofObj θ (Q d₁) X) (0 : cofObj θ (Q d₂) X) := by
  subst hd; rfl

/-- Heterogeneous congruence for sums along an equality of degrees. -/
public lemma heq_cof_add {Q : ℤ → PMod O₁} {d₁ d₂ : ℤ} (hd : d₁ = d₂) {X : Cᵒᵖ}
    {u₁ u₂ : cofObj θ (Q d₁) X} {v₁ v₂ : cofObj θ (Q d₂) X}
    (h₁ : HEq u₁ v₁) (h₂ : HEq u₂ v₂) : HEq (u₁ + u₂) (v₁ + v₂) := by
  subst hd
  exact heq_of_eq (congrArg₂ (· + ·) (eq_of_heq h₁) (eq_of_heq h₂))

variable {P : ℤ → PMod O₁}

/-- The unit of the base-changed graded algebra: the pure tensor `1 ⊗ 1`. -/
public noncomputable def cofOne (A : Stacks.GradedAlgebra P) :
    ((changeOfRings θ).obj (P 0)).sections :=
  PresheafOfModules.sectionsMk
    (fun X => letI := (θ.app X).hom.toAlgebra; (1 : O₂.obj X) ⊗ₜ[O₁.obj X] A.one.eval X)
    (fun {X Y} f => by
      let := (θ.app X).hom.toAlgebra
      let := (θ.app Y).hom.toAlgebra
      exact (cofMap_tmul θ (P 0) f 1 (A.one.eval X)).trans
        (congrArg₂ (fun (b : O₂.obj Y) t => b ⊗ₜ[O₁.obj Y] t) (map_one _)
          (PresheafOfModules.sections_property A.one f)))

/-- The sections of the base-changed unit. -/
public lemma cofOne_eval (A : Stacks.GradedAlgebra P) (X : Cᵒᵖ) :
    letI := (θ.app X).hom.toAlgebra
    (cofOne θ A).eval X = (1 : O₂.obj X) ⊗ₜ[O₁.obj X] A.one.eval X := rfl

/-- Two additive maps from a change-of-rings presheaf into equal-degree ones are
heterogeneously equal as soon as they are on pure tensors. -/
private lemma heq_cof_app_of_tmul {Q : ℤ → PMod O₁} {d₁ d₂ : ℤ} (hd : d₁ = d₂) {X : Cᵒᵖ}
    {M : PMod O₁} (f : cofObj θ M X →+ cofObj θ (Q d₁) X) (g : cofObj θ M X →+ cofObj θ (Q d₂) X)
    (x : cofObj θ M X)
    (h : letI := (θ.app X).hom.toAlgebra
      ∀ (a : O₂.obj X) (m : M.obj X), HEq (f (a ⊗ₜ[O₁.obj X] m)) (g (a ⊗ₜ[O₁.obj X] m))) :
    HEq (f x) (g x) := by
  let := (θ.app X).hom.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero =>
    exact (heq_of_eq (map_zero f)).trans
      ((heq_cof_zero θ hd X).trans (heq_of_eq (map_zero g)).symm)
  | add x₁ x₂ h₁ h₂ =>
    exact (heq_of_eq (map_add f x₁ x₂)).trans
      ((heq_cof_add θ hd h₁ h₂).trans (heq_of_eq (map_add g x₁ x₂)).symm)
  | tmul a m => exact h a m

/-- Associativity of the base-changed multiplication. -/
public lemma cofApp_assoc (A : Stacks.GradedAlgebra P) (i j k : ℤ) (X : Cᵒᵖ)
    (x : cofObj θ (P i) X) (y : cofObj θ (P j) X) (z : cofObj θ (P k) X) :
    HEq (cofApp θ (A.mul (i + j) k) X (cofApp θ (A.mul i j) X x y) z)
      (cofApp θ (A.mul i (j + k)) X x (cofApp θ (A.mul j k) X y z)) := by
  let := (θ.app X).hom.toAlgebra
  refine heq_cof_app_of_tmul θ (add_assoc i j k)
    (((cofApp θ (A.mul (i + j) k) X).flip z).comp ((cofApp θ (A.mul i j) X).flip y))
    ((cofApp θ (A.mul i (j + k)) X).flip (cofApp θ (A.mul j k) X y z)) x fun a m => ?_
  refine heq_cof_app_of_tmul θ (add_assoc i j k)
    (((cofApp θ (A.mul (i + j) k) X).flip z).comp (cofApp θ (A.mul i j) X (a ⊗ₜ[O₁.obj X] m)))
    ((cofApp θ (A.mul i (j + k)) X (a ⊗ₜ[O₁.obj X] m)).comp
      ((cofApp θ (A.mul j k) X).flip z)) y fun c n => ?_
  refine heq_cof_app_of_tmul θ (add_assoc i j k)
    (cofApp θ (A.mul (i + j) k) X
      (cofApp θ (A.mul i j) X (a ⊗ₜ[O₁.obj X] m) (c ⊗ₜ[O₁.obj X] n)))
    ((cofApp θ (A.mul i (j + k)) X (a ⊗ₜ[O₁.obj X] m)).comp
      (cofApp θ (A.mul j k) X (c ⊗ₜ[O₁.obj X] n))) z fun b p => ?_
  change HEq (cofApp θ (A.mul (i + j) k) X
      (cofApp θ (A.mul i j) X (a ⊗ₜ[O₁.obj X] m) (c ⊗ₜ[O₁.obj X] n)) (b ⊗ₜ[O₁.obj X] p))
    (cofApp θ (A.mul i (j + k)) X (a ⊗ₜ[O₁.obj X] m)
      (cofApp θ (A.mul j k) X (c ⊗ₜ[O₁.obj X] n) (b ⊗ₜ[O₁.obj X] p)))
  rw [cofApp_tmul, cofApp_tmul, cofApp_tmul, cofApp_tmul, mul_assoc a c b]
  exact heq_cof_tmul θ (Q := P) (add_assoc i j k) (a * (c * b)) (A.mul_assoc i j k X m n p)

/-- The base-changed unit is a left identity. -/
public lemma cofApp_one_mul (A : Stacks.GradedAlgebra P) (i : ℤ) (X : Cᵒᵖ)
    (x : cofObj θ (P i) X) :
    HEq (cofApp θ (A.mul 0 i) X ((cofOne θ A).eval X) x) x := by
  let := (θ.app X).hom.toAlgebra
  refine heq_cof_app_of_tmul θ (zero_add i) (cofApp θ (A.mul 0 i) X ((cofOne θ A).eval X))
    (AddMonoidHom.id _) x fun a m => ?_
  refine (heq_of_eq (cofApp_tmul θ (A.mul 0 i) X 1 a (A.one.eval X) m)).trans ?_
  rw [one_mul a]
  exact heq_cof_tmul θ (Q := P) (zero_add i) a (A.one_mul i X m)

/-- The base-changed unit is a right identity. -/
public lemma cofApp_mul_one (A : Stacks.GradedAlgebra P) (i : ℤ) (X : Cᵒᵖ)
    (x : cofObj θ (P i) X) :
    HEq (cofApp θ (A.mul i 0) X x ((cofOne θ A).eval X)) x := by
  let := (θ.app X).hom.toAlgebra
  refine heq_cof_app_of_tmul θ (add_zero i) ((cofApp θ (A.mul i 0) X).flip ((cofOne θ A).eval X))
    (AddMonoidHom.id _) x fun a m => ?_
  refine (heq_of_eq (cofApp_tmul θ (A.mul i 0) X a 1 m (A.one.eval X))).trans ?_
  rw [mul_one a]
  exact heq_cof_tmul θ (Q := P) (add_zero i) a (A.mul_one i X m)

/-- Base change of a graded algebra of presheaves of modules. -/
public noncomputable def changeOfRingsGradedAlgebra (A : Stacks.GradedAlgebra P) :
    Stacks.GradedAlgebra (fun n => (changeOfRings θ).obj (P n)) where
  mul i j := cofBil θ (A.mul i j)
  one := cofOne θ A
  mul_assoc i j k X x y z := cofApp_assoc θ A i j k X x y z
  one_mul i X x := cofApp_one_mul θ A i X x
  mul_one i X x := cofApp_mul_one θ A i X x

section Sheaf

variable (J : GrothendieckTopology C)
  (h₁ : Presheaf.IsSheaf J (ringPresheaf O₁)) (h₂ : Presheaf.IsSheaf J (ringPresheaf O₂))
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A sheaf of graded algebras, read as a graded algebra of presheaves of modules by forgetting
the sheaf conditions on the homogeneous pieces. -/
public noncomputable def forgetSheaf
    (B : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁)) :
    Stacks.GradedAlgebra (fun n : ℤ => (B.piece n).val) where
  mul i j := B.mul i j
  one := PresheafOfModules.sectionsMk (fun X => B.one.eval X) fun {_ _} f =>
    PresheafOfModules.sections_property B.one f
  mul_assoc i j k X x y z := B.mul_assoc i j k X x y z
  one_mul i X x := B.one_mul i X x
  mul_one i X x := B.mul_one i X x

/-- Extension of scalars of a sheaf of graded algebras. The homogeneous pieces are the
extensions of scalars of the original ones, and the multiplication and unit are induced by
`(a ⊗ x) · (c ⊗ y) = ac ⊗ xy` and `1 ⊗ 1`. -/
public noncomputable def extendScalarsGradedAlgebra
    (B : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁)) :
    SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₂ h₂) :=
  (changeOfRingsGradedAlgebra θ (forgetSheaf J h₁ B)).sheafify
    (𝟙 (commRingSheaf J O₂ h₂).obj)

/-- The homogeneous pieces of the extended graded algebra are the extensions of scalars of the
original homogeneous pieces. -/
public theorem extendScalarsGradedAlgebra_piece
    (B : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁)) (n : ℤ) :
    (extendScalarsGradedAlgebra θ J h₁ h₂ B).piece n =
      (extendScalars J θ h₁ h₂).obj (B.piece n) := rfl

/-- The extension-of-scalars multiplication on the images of pure tensors under the
sheafification unit. -/
public theorem extendScalarsGradedAlgebra_mul_unit
    (B : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁)) (i j : ℤ) (X : Cᵒᵖ) :
    letI := (θ.app X).hom.toAlgebra
    ∀ (a c : O₂.obj X) (x : (B.piece i).val.obj X) (y : (B.piece j).val.obj X),
      ((extendScalarsGradedAlgebra θ J h₁ h₂ B).mul i j).app X
          (PresheafOfModules.Hom.app
            (PresheafOfModules.sheafifyUnit (𝟙 (commRingSheaf J O₂ h₂).obj)
              ((changeOfRings θ).obj (B.piece i).val)) X (a ⊗ₜ[O₁.obj X] x))
          (PresheafOfModules.Hom.app
            (PresheafOfModules.sheafifyUnit (𝟙 (commRingSheaf J O₂ h₂).obj)
              ((changeOfRings θ).obj (B.piece j).val)) X (c ⊗ₜ[O₁.obj X] y)) =
        PresheafOfModules.Hom.app
          (PresheafOfModules.sheafifyUnit (𝟙 (commRingSheaf J O₂ h₂).obj)
            ((changeOfRings θ).obj (B.piece (i + j)).val)) X
          ((a * c) ⊗ₜ[O₁.obj X] ((B.mul i j).app X x y)) := by
  let := (θ.app X).hom.toAlgebra
  intro a c x y
  refine Eq.trans (Stacks.GradedAlgebra.sheafify_mul_unit
    (A := changeOfRingsGradedAlgebra θ (forgetSheaf J h₁ B))
    (𝟙 (commRingSheaf J O₂ h₂).obj) i j X _ _) ?_
  exact congrArg _ (cofBil_app_tmul θ (B.mul i j) X a c x y)

/-- The extension-of-scalars unit is the image of `1 ⊗ 1` under the sheafification unit. -/
public theorem extendScalarsGradedAlgebra_one_eval
    (B : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁)) (X : Cᵒᵖ) :
    letI := (θ.app X).hom.toAlgebra
    (extendScalarsGradedAlgebra θ J h₁ h₂ B).one.eval X =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit (𝟙 (commRingSheaf J O₂ h₂).obj)
          ((changeOfRings θ).obj (B.piece 0).val)) X
        ((1 : O₂.obj X) ⊗ₜ[O₁.obj X] B.one.eval X) := rfl

/-! ### Extension of scalars as a functor of sheaves of graded algebras -/

section Map

variable {A B : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁)}

/-- Extension of scalars of a homomorphism of sheaves of graded algebras. Degreewise it is the
extension of scalars of the degreewise morphism. -/
public noncomputable def extendScalarsGradedAlgebraHom (g : A ⟶ B) :
    extendScalarsGradedAlgebra θ J h₁ h₂ A ⟶ extendScalarsGradedAlgebra θ J h₁ h₂ B :=
  (changeOfRingsGradedAlgebra θ (forgetSheaf J h₁ A)).sheafifyGradedHom
    (𝟙 (commRingSheaf J O₂ h₂).obj)
    (changeOfRingsGradedAlgebra θ (forgetSheaf J h₁ B))
    (fun n => (changeOfRings θ).map (g.app n).val)
    (fun i j X x y => cofApp_map θ (A.mul i j) (B.mul i j) (g.app i).val (g.app j).val
      (g.app (i + j)).val (fun X x y => g.map_mul i j X x y) X x y)

/-- The degreewise components of the extension of scalars of a homomorphism of sheaves of
graded algebras are the extensions of scalars of its degreewise components. -/
public theorem extendScalarsGradedAlgebraHom_app (g : A ⟶ B) (n : ℤ) :
    (extendScalarsGradedAlgebraHom θ J h₁ h₂ g).app n =
      (extendScalars J θ h₁ h₂).map (g.app n) := rfl

/-- Extension of scalars of sheaves of graded algebras, as a functor. -/
public noncomputable def extendScalarsGradedAlgebraFunctor :
    SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁) ⥤
      SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₂ h₂) where
  obj A := extendScalarsGradedAlgebra θ J h₁ h₂ A
  map g := extendScalarsGradedAlgebraHom θ J h₁ h₂ g
  map_id A := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    (extendScalars J θ h₁ h₂).map_id (A.piece n)
  map_comp g h := SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    (extendScalars J θ h₁ h₂).map_comp (g.app n) (h.app n)

/-- The extension-of-scalars functor of sheaves of graded algebras acts on objects by
`extendScalarsGradedAlgebra`. -/
public theorem extendScalarsGradedAlgebraFunctor_obj
    (A : SheafOfModules.GradedAlgebra.{w, w} (commRingSheaf J O₁ h₁)) :
    (extendScalarsGradedAlgebraFunctor θ J h₁ h₂).obj A =
      extendScalarsGradedAlgebra θ J h₁ h₂ A := rfl

/-- The degreewise components of the extension-of-scalars functor on morphisms are the
extensions of scalars of the degreewise components. -/
public theorem extendScalarsGradedAlgebraFunctor_map_app (g : A ⟶ B) (n : ℤ) :
    ((extendScalarsGradedAlgebraFunctor θ J h₁ h₂).map g).app n =
      (extendScalars J θ h₁ h₂).map (g.app n) := rfl

end Map

end Sheaf

end Stacks.Sheaves.GradedAlgebraExtendScalars
