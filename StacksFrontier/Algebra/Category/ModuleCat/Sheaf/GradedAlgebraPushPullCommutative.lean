module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictTensorator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided

/-!
# Pullback and pushforward of a sheaf of graded algebras preserve commutativity

Let `f : X ⟶ Y` be a morphism of ringed spaces. The ungraded realization of a sheaf of graded
algebras as a sheaf of **commutative** rings — `Stacks.RelativeSpec.ungradedAlgebraSheaf`, and
the morphisms of algebra sheaves `Stacks.RelativeSpec.ungradedAlgebraSheafMap` between two of
them — takes as a hypothesis that homogeneous multiplication commutes in every pair of degrees,
in the heterogeneous form

`HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x)`,

the heterogeneity being that the two products live in the pieces of degree `i + j` and `j + i`.
This file proves that both transports of a sheaf of graded algebras along `f` inherit that
hypothesis, so that the graded unit `A ⟶ f_* f^* A` of
`Stacks.PushforwardGradedAlgebra.gradedUnit` has an ungraded realization at all.

The two halves are proved by completely different arguments.

* **The pushforward is sectionwise.** A section of `(f_*A)_n` over `U` *is* a section of `A_n`
  over `f⁻¹U` and the multiplication of `f_*A` is the multiplication of `A` read there,
  `Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra_mul_app`; so commutativity is the
  hypothesis over `f⁻¹U` and nothing has to be transported.
* **The pullback is not**: its sections are a sheafification of a tensor product and no formula
  for them exists. Commutativity is therefore carried at *morphism* level, where it says that
  `A_i ⊗ A_j ⟶ A_{i+j}` is the symmetry constraint of [Stacks, Tag 01CA] followed by
  `A_j ⊗ A_i ⟶ A_{j+i}`, and the pullback carries that because it is a **braided** monoidal
  functor: `Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding`. The identification
  of the two monoidal structures on `f^*` that this needs — the braided statement is available
  for the comparison of [Stacks, Tag 01CD] and the multiplication of `f^*A` is built from the
  localization bridge — is `Stacks.PullbackStrictTensorator.mu_pullbackStrictMonoidal_eq`.

## Main results

* `Stacks.TensorSheafWorld.mulSheaf_eq_braiding_comp` and
  `Stacks.TensorSheafWorld.mul_heq_of_mulSheaf_eq_braiding_comp`: **the two readings of
  commutativity of a sheaf of graded algebras on a ringed space are equivalent** — the
  heterogeneous equality on local sections, and the morphism-level factorization of `mulSheaf`
  through the symmetry constraint.
* `Stacks.PullbackGradedAlgebra.mulSheaf_pullbackGradedAlgebra_eq_braiding_comp`: the
  morphism-level commutativity of `f^*A`.
* `Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra_mul_comm`: **homogeneous multiplication in
  `f^*A` commutes in every pair of degrees** whenever it does in `A`.
* `Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra_mul_comm`: **the same for `f_*A`.**
* `Stacks.PushforwardGradedAlgebra.pushforwardPullback_mul_comm`: **the same for `f_* f^* A`**,
  which is the target of `Stacks.PushforwardGradedAlgebra.gradedUnit`, stated at the spelling
  that definition's type uses.

## Implementation notes

The morphism-level form of commutativity is stated as
`A.mulSheaf i j = (β_ A_i A_j).hom ≫ A.mulSheaf j i ≫ eqToHom (congrArg A.piece (add_comm j i))`
rather than as an equality in degree `(i, i)` only, which is the degree
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackCommutative` treats: there
the two sides lie in the same homogeneous piece so no transport is needed, and that is all the
universal property of a symmetric algebra constrains. The arbitrary-degree form needs the
`eqToHom` of `j + i = i + j`, and converting it to and from the section form is what
`Stacks.TensorSheafWorld.heq_eqToHom_val_app` is for. That file also treats a different
pullback, the one for a morphism of ringed *topoi*.

The braiding is `Stacks.PullbackTensorCoherence.braidedCategory`, the symmetry constraint of
[Stacks, Tag 01CA] named at the `Stacks.RingedSpace.structureRingSheaf` spelling of the ring
sheaf, and the monoidal structure is `Stacks.PullbackGradedAlgebra.monoidalCategory`, which is
`Stacks.TensorSheafWorld.monoidalCategory` of the structure sheaf by definition; both are local
instances here, as in the files they come from.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules, with its symmetry constraint.
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — the comparison
  `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`.
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX) — functoriality of
  sheaves of graded algebras.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace TopologicalSpace
open SheafOfModules.GradedAlgebra
open Stacks.PullbackTensorCoherence

open scoped TensorProduct

universe u

namespace Stacks.TensorSheafWorld

/-! ### Commutativity on sections and commutativity at morphism level -/

section Braiding

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackTensorCoherence.braidedCategory

variable (Z : RingedSpace.{u, u})
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z)) (i j : ℤ)

/-- **The braided composite on a local pure tensor**: the symmetry constraint exchanges the two
factors, the multiplication in degrees `j` and `i` multiplies them in the other order, and the
transport along `j + i = i + j` is left standing. -/
theorem braidingMulSheaf_val_app (U : (Opens Z.carrier)ᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) :
    ((β_ (A.piece i) (A.piece j)).hom ≫ A.mulSheaf j i ≫
          eqToHom (congrArg A.piece (add_comm j i))).val.app U
        ((PresheafOfModules.tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y)) =
      (eqToHom (congrArg A.piece (add_comm j i))).val.app U ((A.mul j i).app U y x) := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply (β_ (A.piece i) (A.piece j)).hom
    (A.mulSheaf j i ≫ eqToHom (congrArg A.piece (add_comm j i))) U _) ?_
  refine Eq.trans (congrArg
    (fun z => (A.mulSheaf j i ≫ eqToHom (congrArg A.piece (add_comm j i))).val.app U z)
    (Stacks.PullbackTensorCoherence.braiding_tmul Z (A.piece i) (A.piece j) U x y)) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply (A.mulSheaf j i)
    (eqToHom (congrArg A.piece (add_comm j i))) U _) ?_
  exact congrArg (fun z => (eqToHom (congrArg A.piece (add_comm j i))).val.app U z)
    (mulSheaf_unit A j i U y x)

/-- **Sectionwise commutativity of a sheaf of graded algebras implies the morphism-level
factorization of its multiplication through the symmetry constraint.** -/
theorem mulSheaf_eq_braiding_comp
    (hA : ∀ (p q : ℤ) (U : (Opens Z.carrier)ᵒᵖ) (x : (A.piece p).val.obj U)
      (y : (A.piece q).val.obj U), HEq ((A.mul p q).app U x y) ((A.mul q p).app U y x)) :
    A.mulSheaf i j = (β_ (A.piece i) (A.piece j)).hom ≫ A.mulSheaf j i ≫
      eqToHom (congrArg A.piece (add_comm j i)) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Z.sheaf) fun U x y ↦ ?_
  refine (mulSheaf_unit A i j U x y).trans ?_
  refine Eq.trans ?_ (braidingMulSheaf_val_app Z A i j U x y).symm
  exact eq_of_heq ((hA i j U x y).trans
    (heq_eqToHom_val_app A.piece (add_comm j i) U ((A.mul j i).app U y x)).symm)

/-- **The morphism-level factorization of the multiplication through the symmetry constraint
implies sectionwise commutativity.** The converse of `mulSheaf_eq_braiding_comp`. -/
theorem mul_heq_of_mulSheaf_eq_braiding_comp
    (h : ∀ p q : ℤ, A.mulSheaf p q = (β_ (A.piece p) (A.piece q)).hom ≫ A.mulSheaf q p ≫
      eqToHom (congrArg A.piece (add_comm q p)))
    (U : (Opens Z.carrier)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    HEq ((A.mul i j).app U x y) ((A.mul j i).app U y x) := by
  refine HEq.trans (heq_of_eq ?_)
    (heq_eqToHom_val_app A.piece (add_comm j i) U ((A.mul j i).app U y x))
  refine (mulSheaf_unit A i j U x y).symm.trans ?_
  rw [h i j]
  exact braidingMulSheaf_val_app Z A i j U x y

end Braiding

end Stacks.TensorSheafWorld

namespace Stacks.PullbackGradedAlgebra

/-! ### The pullback of a commutative sheaf of graded algebras -/

section Pullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal
  Stacks.PullbackTensorCoherence.braidedCategory

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))

/-- The multiplication of `f^*A` in closed form: the inverse of the comparison of
[Stacks, Tag 01CD] followed by the pullback of the multiplication of `A`. This is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.mulSheaf_pullbackGradedAlgebra` with the morphism of
ringed spaces left arbitrary rather than coming from a morphism of schemes. -/
theorem mulSheaf_pullbackGradedAlgebra_eq (i j : ℤ) :
    (pullbackGradedAlgebra f A (structureSheafRing Y).property).mulSheaf i j =
      inv (pullbackTensorComparison f (A.piece i) (A.piece j)) ≫
        (pullbackFunctor f).map (A.mulSheaf i j) :=
  (mulSheaf_transport (pullbackFunctor f) A (structureSheafRing Y).property
      (structureSheafRing X).property i j).trans
    (congrArg (fun z => z ≫ (pullbackFunctor f).map (A.mulSheaf i j))
      (Stacks.PullbackStrictTensorator.mu_pullbackStrictMonoidal_eq f (A.piece i) (A.piece j)))

/-- The inverse of the comparison of [Stacks, Tag 01CD] commutes with the symmetry constraint,
which is `Stacks.PullbackTensorCoherence.pullbackTensorComparison_braiding` solved for the
inverse. -/
theorem inv_pullbackTensorComparison_braiding (i j : ℤ) :
    inv (pullbackTensorComparison f (A.piece i) (A.piece j)) ≫
        (pullbackFunctor f).map (β_ (A.piece i) (A.piece j)).hom =
      (β_ ((pullbackFunctor f).obj (A.piece i)) ((pullbackFunctor f).obj (A.piece j))).hom ≫
        inv (pullbackTensorComparison f (A.piece j) (A.piece i)) := by
  rw [IsIso.eq_comp_inv, Category.assoc, pullbackTensorComparison_braiding,
    IsIso.inv_hom_id_assoc]

/-- **The multiplication of `f^*A` factors through the symmetry constraint** whenever that of `A`
does. This is the morphism-level form of commutativity, which is the form the pullback carries:
it is a braided monoidal functor. -/
theorem mulSheaf_pullbackGradedAlgebra_eq_braiding_comp
    (hA : ∀ (p q : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (x : (A.piece p).val.obj U)
      (y : (A.piece q).val.obj U), HEq ((A.mul p q).app U x y) ((A.mul q p).app U y x))
    (i j : ℤ) :
    (pullbackGradedAlgebra f A (structureSheafRing Y).property).mulSheaf i j =
      (β_ ((pullbackFunctor f).obj (A.piece i)) ((pullbackFunctor f).obj (A.piece j))).hom ≫
        (pullbackGradedAlgebra f A (structureSheafRing Y).property).mulSheaf j i ≫
          eqToHom (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm j i)) := by
  rw [mulSheaf_pullbackGradedAlgebra_eq, mulSheaf_pullbackGradedAlgebra_eq f A j i,
    Stacks.TensorSheafWorld.mulSheaf_eq_braiding_comp Y A i j hA]
  have hmap := Functor.map_comp (pullbackFunctor f) (A.mulSheaf j i)
    (eqToHom (congrArg A.piece (add_comm j i)))
  rw [eqToHom_map] at hmap
  erw [Functor.map_comp, hmap, ← Category.assoc, inv_pullbackTensorComparison_braiding,
    Category.assoc, Category.assoc]

/-- **Homogeneous multiplication in `f^*A` commutes in every pair of degrees** whenever it does
in `A`, which is the hypothesis the ungraded realization of a sheaf of graded algebras as a sheaf
of commutative rings takes. -/
theorem pullbackGradedAlgebra_mul_comm
    (hA : ∀ (p q : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (x : (A.piece p).val.obj U)
      (y : (A.piece q).val.obj U), HEq ((A.mul p q).app U x y) ((A.mul q p).app U y x))
    (i j : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((pullbackGradedAlgebra f A (structureSheafRing Y).property).piece i).val.obj U)
    (y : ((pullbackGradedAlgebra f A (structureSheafRing Y).property).piece j).val.obj U) :
    HEq (((pullbackGradedAlgebra f A (structureSheafRing Y).property).mul i j).app U x y)
      (((pullbackGradedAlgebra f A (structureSheafRing Y).property).mul j i).app U y x) :=
  Stacks.TensorSheafWorld.mul_heq_of_mulSheaf_eq_braiding_comp X
    (pullbackGradedAlgebra f A (structureSheafRing Y).property) i j
    (fun p q => mulSheaf_pullbackGradedAlgebra_eq_braiding_comp f A hA p q) U x y

end Pullback

end Stacks.PullbackGradedAlgebra

namespace Stacks.PushforwardGradedAlgebra

/-! ### The pushforward of a commutative sheaf of graded algebras -/

section Pushforward

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal pushforwardFunctorLaxMonoidal

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Homogeneous multiplication in `f_*A` commutes in every pair of degrees** whenever it does
in `A`. Unlike for the pullback this is sectionwise: a local section of `(f_*A)_n` over `U` is a
local section of `A_n` over `f⁻¹U` and the two multiplications agree there, by
`Stacks.PushforwardGradedAlgebra.pushforwardGradedAlgebra_mul_app`. -/
theorem pushforwardGradedAlgebra_mul_comm
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X))
    (hA : ∀ (p q : ℤ) (U : (Opens X.carrier)ᵒᵖ) (x : (A.piece p).val.obj U)
      (y : (A.piece q).val.obj U), HEq ((A.mul p q).app U x y) ((A.mul q p).app U y x))
    (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (x : ((pushforwardGradedAlgebra f A).piece i).val.obj U)
    (y : ((pushforwardGradedAlgebra f A).piece j).val.obj U) :
    HEq (((pushforwardGradedAlgebra f A).mul i j).app U x y)
      (((pushforwardGradedAlgebra f A).mul j i).app U y x) := by
  rw [pushforwardGradedAlgebra_mul_app f A i j U x y,
    pushforwardGradedAlgebra_mul_app f A j i U y x]
  exact hA i j ((opensMap f).op.obj U) x y

/-- **Homogeneous multiplication in `f_* f^* A` commutes in every pair of degrees** whenever it
does in `A`, stated at the spelling the type of `Stacks.PushforwardGradedAlgebra.gradedUnit`
uses, so that it is the hypothesis `Stacks.RelativeSpec.ungradedAlgebraSheafMap` asks of the
target of the graded unit. -/
theorem pushforwardPullback_mul_comm
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))
    (hA : ∀ (p q : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (x : (A.piece p).val.obj U)
      (y : (A.piece q).val.obj U), HEq ((A.mul p q).app U x y) ((A.mul q p).app U y x))
    (i j : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (x : (((SheafOfModules.GradedAlgebra.transportFunctor (pushforwardFunctor f)
        (structureSheafRing X).property (structureSheafRing Y).property).obj
      ((SheafOfModules.GradedAlgebra.transportFunctor (pullbackFunctor f)
        (structureSheafRing Y).property (structureSheafRing X).property).obj A)).piece i).val.obj U)
    (y : (((SheafOfModules.GradedAlgebra.transportFunctor (pushforwardFunctor f)
        (structureSheafRing X).property (structureSheafRing Y).property).obj
      ((SheafOfModules.GradedAlgebra.transportFunctor (pullbackFunctor f)
        (structureSheafRing Y).property (structureSheafRing X).property).obj A)).piece j).val.obj
          U) :
    HEq ((((SheafOfModules.GradedAlgebra.transportFunctor (pushforwardFunctor f)
          (structureSheafRing X).property (structureSheafRing Y).property).obj
        ((SheafOfModules.GradedAlgebra.transportFunctor (pullbackFunctor f)
          (structureSheafRing Y).property (structureSheafRing X).property).obj A)).mul i j).app U
        x y)
      ((((SheafOfModules.GradedAlgebra.transportFunctor (pushforwardFunctor f)
          (structureSheafRing X).property (structureSheafRing Y).property).obj
        ((SheafOfModules.GradedAlgebra.transportFunctor (pullbackFunctor f)
          (structureSheafRing Y).property (structureSheafRing X).property).obj A)).mul j i).app U
        y x) :=
  pushforwardGradedAlgebra_mul_comm f
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra f A (structureSheafRing Y).property)
    (Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra_mul_comm f A hA) i j U x y

end Pushforward

end Stacks.PushforwardGradedAlgebra

end
