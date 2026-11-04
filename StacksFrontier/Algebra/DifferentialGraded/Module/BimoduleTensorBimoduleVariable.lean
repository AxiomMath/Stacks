module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorAdmissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBimoduleMap

/-! # The ordinary tensor product as a functor of the bimodule variable

Let `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`. A
differential graded `(B, C)`-bimodule is the same thing as a right differential graded module
over `Bᵒᵖ ⊗_R C` (Tag 0FQJ), and for a *fixed* right differential graded `B`-module `W` the
ordinary tensor product `W ⊗_B -` of Tag 09LM is therefore a functor
`Mod_{(Bᵒᵖ ⊗_R C, d)} ⥤ Mod_{(C, d)}`. A homomorphism `ρ : W ⟶ W'` induces a morphism of these
functors. This file records both, together with the elementary transfers along Tag 0FQJ that
they need: a homomorphism, a graded homomorphism, an isomorphism and an admissible short exact
sequence of modules over `Bᵒᵖ ⊗_R C` all read as the same for bimodules.

This is the frame in which the dévissage of Stacks 0BZ5 in its second variable runs: the
property-(P) filtration of a bimodule lives over `Bᵒᵖ ⊗_R C`, while the statement being
filtered is about the ordinary tensor product, so the induction needs the ordinary tensor
product as a functor on modules over `Bᵒᵖ ⊗_R C`.

## Main definitions

* `DifferentialGraded.Bimodule.ofTensorHom`, `DifferentialGraded.Bimodule.ofTensorGradedHom`:
  a homomorphism, resp. a graded homomorphism, of right differential graded `Bᵒᵖ ⊗_R C`-modules,
  read as one of bimodules.
* `DifferentialGraded.Bimodule.ofTensorFunctor`: the resulting functor to bimodules, and
  `DifferentialGraded.Bimodule.ofTensorModuleIso` its action on isomorphisms.
* `DifferentialGraded.Bimodule.tensorBimoduleFunctor`: `W ⊗_B -` as a functor of the module over
  `Bᵒᵖ ⊗_R C`.
* `DifferentialGraded.Bimodule.tensorBimoduleNatTrans`: the morphism of those functors induced by
  a homomorphism `ρ : W ⟶ W'`.

## Main results

* `DifferentialGraded.Bimodule.ofTensorModuleToTensorModuleIso`: the bimodule attached to the
  module over `Bᵒᵖ ⊗_R C` attached to a bimodule is that bimodule.
* `DifferentialGraded.Bimodule.ofTensorIsAdmissibleShortExact`: an admissible short exact
  sequence of modules over `Bᵒᵖ ⊗_R C` is an admissible short exact sequence of bimodules.
* `DifferentialGraded.Bimodule.isAdmissibleShortExact_tensorBimoduleFunctor_map`: the functor
  `W ⊗_B -` carries an admissible short exact sequence to an admissible short exact sequence.
* `DifferentialGraded.Bimodule.tensorBimoduleNatTrans_app_pure`: the component of the morphism of
  functors on a pure tensor.

## Implementation notes

*Nothing is rebuilt.* The passage from a map of modules over `Bᵒᵖ ⊗_R C` to a map of bimodules is
the preimage under the fully faithful functor of Tag 0FQJ, conjugated by
`DifferentialGraded.Bimodule.toTensorModuleOfTensorModuleIso`; since both that isomorphism and
the preimage are the identity on underlying modules, every identity among the resulting maps is
an equality of underlying maps and is proved by `rfl` after extensionality.

*Universes are collapsed to one, inherited and not chosen here.*
`DifferentialGraded.Bimodule.TensorDGFunctorData` is stated for
`DifferentialGradedAlgebra.{u, u} R` and `DifferentialGradedModule.{u, u, u}`, so this file is
too.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the relative tensor
  product.
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ), bimodules as modules
  over the graded tensor product.
* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT), admissible short exact
  sequences.
* [Stacks Project, Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5), where the dévissage
  this frame serves is carried out.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] (B C : DifferentialGradedAlgebra.{u, u} R)

/-! ### The left action through the totalized action -/

/-- **The homogeneous left action of a bimodule, read through the totalized left action.** The
cochain component in which the field `DifferentialGraded.Bimodule.Hom.map_left` is phrased is the
value of `DifferentialGradedModule.leftActionTotal`. -/
theorem leftAction_val (N : Bimodule B C) (n q : ℤ) (b : B.grading n)
    (y : N.rightModule.grading q) :
    ((show N.rightModule.grading (q + n) from
      (N.leftAction.1.action n b).v q (q + n) (by omega) y) : N.rightModule.M) =
      leftActionTotal B C N.rightModule N.leftAction.1 (b : B.A) (y : N.rightModule.M) := by
  rw [leftActionTotal_apply B C N.rightModule N.leftAction.1 n b]
  exact (totalizeCochain_apply_of_eq C N.rightModule n q (q + n) rfl
    (N.leftAction.1.action n b) y).symm

/-- **A homomorphism of the underlying right modules commuting with the totalized left action is
a homomorphism of bimodules.** This is the differential graded counterpart of
`DifferentialGraded.Bimodule.gradedHomOfLeftActionTotal`. -/
def homOfLeftActionTotal {N N' : Bimodule B C}
    (u : DifferentialGradedModule.Hom N.rightModule N'.rightModule)
    (hu : ∀ (b : B.A) (y : N.rightModule.M),
      u.toFun (leftActionTotal B C N.rightModule N.leftAction.1 b y) =
        leftActionTotal B C N'.rightModule N'.leftAction.1 b (u.toFun y)) :
    N ⟶ N' where
  rightHom := u
  map_left n q b y := by
    rw [leftAction_val B C N n q b y, leftAction_val B C N' n q b (u.gradedMap q y)]
    exact hu (b : B.A) (y : N.rightModule.M)

/-- **An isomorphism of the underlying right modules commuting with the totalized left action is
an isomorphism of bimodules.** The inverse commutes with the action because the isomorphism
does. -/
def isoOfRightIso {N N' : Bimodule B C} (e : N.rightModule ≅ N'.rightModule)
    (he : ∀ (b : B.A) (y : N.rightModule.M),
      e.hom.toFun (leftActionTotal B C N.rightModule N.leftAction.1 b y) =
        leftActionTotal B C N'.rightModule N'.leftAction.1 b (e.hom.toFun y)) :
    N ≅ N' where
  hom := homOfLeftActionTotal B C e.hom he
  inv := homOfLeftActionTotal B C e.inv (fun b y' => by
    have hhi (z : N'.rightModule.M) : e.hom.toFun (e.inv.toFun z) = z :=
      congrArg (fun f : N'.rightModule ⟶ N'.rightModule => f.toFun z) e.inv_hom_id
    have hih (z : N.rightModule.M) : e.inv.toFun (e.hom.toFun z) = z :=
      congrArg (fun f : N.rightModule ⟶ N.rightModule => f.toFun z) e.hom_inv_id
    have h := he b (e.inv.toFun y')
    rw [hhi] at h
    rw [← h, hih])
  hom_inv_id := Bimodule.Hom.ext e.hom_inv_id
  inv_hom_id := Bimodule.Hom.ext e.inv_hom_id

/-! ### Maps of modules over the graded tensor product, read as maps of bimodules -/

/-- A homomorphism of right differential graded `Bᵒᵖ ⊗_R C`-modules, read as a homomorphism of
the attached differential graded `(B, C)`-bimodules: the preimage under the fully faithful
functor of Tag 0FQJ of the given map, conjugated by
`DifferentialGraded.Bimodule.toTensorModuleOfTensorModuleIso`. -/
def ofTensorHom {Y Y' : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)} (g : Y ⟶ Y') :
    ofTensorModule B C Y ⟶ ofTensorModule B C Y' :=
  tensorMapPreimage B C ((toTensorModuleOfTensorModuleIso B C Y).hom ≫ g ≫
    (toTensorModuleOfTensorModuleIso B C Y').inv)

/-- The underlying map of `DifferentialGraded.Bimodule.ofTensorHom` is the given map. -/
theorem ofTensorHom_rightHom_toFun
    {Y Y' : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)} (g : Y ⟶ Y') :
    (ofTensorHom B C g).rightHom.toFun = g.toFun := rfl

/-- Reading the identity as a map of bimodules gives the identity. -/
theorem ofTensorHom_id (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) :
    ofTensorHom B C (𝟙 Y) = 𝟙 (ofTensorModule B C Y) := rfl

/-- Reading a composite as a map of bimodules gives the composite. -/
theorem ofTensorHom_comp {Y Y' Y'' : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)}
    (g : Y ⟶ Y') (h : Y' ⟶ Y'') :
    ofTensorHom B C (g ≫ h) = ofTensorHom B C g ≫ ofTensorHom B C h := rfl

/-- **The functor of Tag 0FQJ from right differential graded `Bᵒᵖ ⊗_R C`-modules to differential
graded `(B, C)`-bimodules.** -/
def ofTensorFunctor :
    DifferentialGradedModule.{u, u, u} (tensorAlgebra B C) ⥤ Bimodule B C where
  obj Y := ofTensorModule B C Y
  map g := ofTensorHom B C g
  map_id := ofTensorHom_id B C
  map_comp := ofTensorHom_comp B C

/-- An isomorphism of right differential graded `Bᵒᵖ ⊗_R C`-modules, read as an isomorphism of
the attached differential graded `(B, C)`-bimodules. -/
def ofTensorModuleIso {Y Y' : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)}
    (e : Y ≅ Y') : ofTensorModule B C Y ≅ ofTensorModule B C Y' :=
  (ofTensorFunctor B C).mapIso e

/-- **The bimodule attached to the right differential graded `Bᵒᵖ ⊗_R C`-module attached to a
bimodule is that bimodule.** -/
def ofTensorModuleToTensorModuleIso (P : Bimodule B C) :
    ofTensorModule B C (toTensorModule B C P) ≅ P :=
  (tensorFunctorFullyFaithful B C).preimageIso
    (toTensorModuleOfTensorModuleIso B C (toTensorModule B C P))

/-- A graded homomorphism of right differential graded `Bᵒᵖ ⊗_R C`-modules, read as a graded
homomorphism of the attached differential graded `(B, C)`-bimodules. -/
def ofTensorGradedHom {Y Y' : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)}
    (u : DifferentialGradedModule.GradedHom Y Y') :
    Bimodule.GradedHom B C (ofTensorModule B C Y) (ofTensorModule B C Y') :=
  tensorGradedPreimage B C
    { toFun := u.toFun
      map_smul := fun x t => by
        change u.toFun (tensorActionApply B C (ofTensorModule B C Y) t x) =
          tensorActionApply B C (ofTensorModule B C Y') t (u.toFun x)
        rw [tensorActionApply_ofTensorModule, tensorActionApply_ofTensorModule]
        exact u.map_smul x t
      map_grading := u.map_grading }

/-- The underlying map of `DifferentialGraded.Bimodule.ofTensorGradedHom` is the given map. -/
theorem ofTensorGradedHom_rightHom_toFun
    {Y Y' : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)}
    (u : DifferentialGradedModule.GradedHom Y Y') :
    (ofTensorGradedHom B C u).rightHom.toFun = u.toFun := rfl

/-- **An admissible short exact sequence of right differential graded `Bᵒᵖ ⊗_R C`-modules is an
admissible short exact sequence of differential graded `(B, C)`-bimodules.** The three maps and
the two graded splittings are unchanged. -/
theorem ofTensorIsAdmissibleShortExact
    {X Y Z : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)} (i : X ⟶ Y) (p : Y ⟶ Z)
    (h : DifferentialGradedModule.IsAdmissibleShortExact i p) :
    Bimodule.IsAdmissibleShortExact B C (ofTensorHom B C i) (ofTensorHom B C p) where
  injective := h.injective
  surjective := h.surjective
  exact := h.exact
  splitMono := ⟨ofTensorGradedHom B C h.admissibleMono.choose, h.admissibleMono.choose_spec⟩
  splitEpi := ⟨ofTensorGradedHom B C h.admissibleEpi.choose, h.admissibleEpi.choose_spec⟩

/-! ### The ordinary tensor product as a functor of the bimodule variable -/

/-- **The ordinary tensor product `W ⊗_B -` of Tag 09LM as a functor of the differential graded
bimodule**, read through Tag 0FQJ as a functor on right differential graded
`Bᵒᵖ ⊗_R C`-modules. -/
def tensorBimoduleFunctor (W : DifferentialGradedModule.{u, u, u} B) :
    DifferentialGradedModule.{u, u, u} (tensorAlgebra B C) ⥤
      DifferentialGradedModule.{u, u, u} C where
  obj Y := tensorObj (ofTensorModule B C Y) W
  map g := tensorHomOfBimoduleHom (ofTensorHom B C g) W
  map_id Y := by
    rw [ofTensorHom_id]
    exact tensorHomOfBimoduleHom_id (ofTensorModule B C Y) W
  map_comp g h := by
    rw [ofTensorHom_comp]
    exact tensorHomOfBimoduleHom_comp (ofTensorHom B C g) (ofTensorHom B C h) W

/-- The functor `W ⊗_B -` on objects. -/
@[simp] theorem tensorBimoduleFunctor_obj (W : DifferentialGradedModule.{u, u, u} B)
    (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) :
    (tensorBimoduleFunctor B C W).obj Y = tensorObj (ofTensorModule B C Y) W := rfl

/-- The functor `W ⊗_B -` on morphisms. -/
@[simp] theorem tensorBimoduleFunctor_map (W : DifferentialGradedModule.{u, u, u} B)
    {Y Y' : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)} (g : Y ⟶ Y') :
    (tensorBimoduleFunctor B C W).map g = tensorHomOfBimoduleHom (ofTensorHom B C g) W := rfl

/-- The functor `W ⊗_B -` on a pure tensor. -/
theorem tensorBimoduleFunctor_map_pure (W : DifferentialGradedModule.{u, u, u} B)
    {Y Y' : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)} (g : Y ⟶ Y')
    (x : W.M) (y : Y.M) :
    ((tensorBimoduleFunctor B C W).map g).toFun
        ((tensorPure (ofTensorModule B C Y) W).toLinearMap x y) =
      (tensorPure (ofTensorModule B C Y') W).toLinearMap x (g.toFun y) :=
  tensorHomOfBimoduleHom_pure (ofTensorHom B C g) W x y

/-- **The functor `W ⊗_B -` carries an admissible short exact sequence of right differential
graded `Bᵒᵖ ⊗_R C`-modules to an admissible short exact sequence.** -/
theorem isAdmissibleShortExact_tensorBimoduleFunctor_map
    (W : DifferentialGradedModule.{u, u, u} B)
    {X Y Z : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)} (i : X ⟶ Y) (p : Y ⟶ Z)
    (h : DifferentialGradedModule.IsAdmissibleShortExact i p) :
    DifferentialGradedModule.IsAdmissibleShortExact
      ((tensorBimoduleFunctor B C W).map i) ((tensorBimoduleFunctor B C W).map p) :=
  tensorIsAdmissibleShortExact (ofTensorIsAdmissibleShortExact B C i p h) W

/-- **The morphism of functors `W ⊗_B - ⟶ W' ⊗_B -` induced by a homomorphism
`ρ : W ⟶ W'`.** -/
def tensorBimoduleNatTrans {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W') :
    tensorBimoduleFunctor B C W ⟶ tensorBimoduleFunctor B C W' where
  app Y := (tensorCompFunctor (ofTensorModule B C Y)).map ρ
  naturality _ _ g := ((tensorModuleNatTrans (ofTensorHom B C g)).naturality ρ).symm

/-- The component of `W ⊗_B - ⟶ W' ⊗_B -` at `Y` is `ρ` tensored with `Y`. -/
@[simp] theorem tensorBimoduleNatTrans_app
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W')
    (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) :
    (tensorBimoduleNatTrans B C ρ).app Y =
      (tensorCompFunctor (ofTensorModule B C Y)).map ρ := rfl

/-- The component of `W ⊗_B - ⟶ W' ⊗_B -` on a pure tensor. -/
theorem tensorBimoduleNatTrans_app_pure
    {W W' : DifferentialGradedModule.{u, u, u} B} (ρ : W ⟶ W')
    (Y : DifferentialGradedModule.{u, u, u} (tensorAlgebra B C)) (x : W.M) (y : Y.M) :
    ((tensorBimoduleNatTrans B C ρ).app Y).toFun
        ((tensorPure (ofTensorModule B C Y) W).toLinearMap x y) =
      (tensorPure (ofTensorModule B C Y) W').toLinearMap (ρ.toFun x) y :=
  tensorCompFunctor_map_pure (ofTensorModule B C Y) ρ x y

end DifferentialGraded.Bimodule

end
