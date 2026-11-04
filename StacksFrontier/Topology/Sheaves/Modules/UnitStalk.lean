module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkwiseIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The stalk of the structure sheaf as a module over itself

Let `𝒪` be a sheaf of rings on a topological space `X` and let `x : X`. The unit object
`SheafOfModules.unit 𝒪` of the category of sheaves of `𝒪`-modules is `𝒪` viewed as a module
over itself, and its stalk at `x` is the stalk ring `𝒪_x` viewed as a module over itself.

This is the content of `unitStalkIso` below. Both sides are the same filtered colimit over the
open neighbourhoods of `x`, computed in `AddCommGrpCat` on the left and in `RingCat` on the
right, so the isomorphism is the comparison map of
`CategoryTheory.Limits.preservesColimitIso` for `forget₂ RingCat AddCommGrpCat`; the scalar
action matches multiplication because both are computed on germs.

`derivedUnitStalkIso` is the same statement one level up: the derived stalk of the unit object
of the derived tensor product on the ringed site of opens of `X` is `𝒪_x` placed in degree
zero. It is `unitStalkIso` together with the fact that the stalk functor, being exact, carries
a module placed in degree zero to its stalk placed in degree zero.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.unitStalkAddEquiv`: the additive isomorphism from the stalk
  of the unit module to the stalk ring.
* `AlgebraicGeometry.SheafOfModules.unitStalkLinearEquiv`: the same map, as a linear
  isomorphism over the stalk ring.
* `AlgebraicGeometry.SheafOfModules.unitStalkIso`: the same map, as an isomorphism in
  `ModuleCat 𝒪_x`, identifying `(stalkFunctor 𝒪 x).obj (SheafOfModules.unit 𝒪)` with
  `ModuleCat.of 𝒪_x 𝒪_x`.
* `AlgebraicGeometry.SheafOfModules.derivedUnitStalkIso`: the derived form, identifying the
  derived stalk of `Stacks.DerivedTensor.RingedSite.unitObject` with `𝒪_x` in degree zero.

## Main results

* `AlgebraicGeometry.SheafOfModules.unitStalkAddEquiv_germ`: the germ formula pinning the
  isomorphism down — it carries the germ of a section of the unit module to the germ of the
  same section of `𝒪`.
* `AlgebraicGeometry.SheafOfModules.unitStalkAddEquiv_smul`: the isomorphism turns the scalar
  action of the stalk ring into multiplication, which is what makes it linear.

## Implementation notes

**The sheaf of rings is bare.** `unitStalkIso` is stated for an arbitrary
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat`, with no commutativity: the
module `ModuleCat.of 𝒪_x 𝒪_x` needs only a `Ring` structure on the stalk, and the
`RingCat`-valued stalk carries one. So none of
`StacksDraft.StalkTensor.commRing_stalk_ringSheaf` or the `CommRingCat`-versus-`RingCat` stalk
comparison of `StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk` is needed here.
Commutativity enters only in `derivedUnitStalkIso`, and there only because the ringed site of
[Stacks, Tag 06YU] is built from a sheaf of *commutative* rings.

**Relation to the ringed-space statement.** The same mathematics is already proved for a
`RingedSpace` with a `CommRingCat`-valued structure sheaf, as
`Stacks.SheafOfModules.TensorStalkRingedSpace.unitStalkLinearEquiv`. That statement is over the
`CommRingCat`-valued stalk of the structure sheaf, whereas
`AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its modules over the `RingCat`-valued
stalk, and the two rings are isomorphic but not equal. Rather than transport along that
comparison, the one-line `preservesColimitIso` argument is redone with
`forget₂ RingCat AddCommGrpCat` alone, which lands on the `RingCat` stalk directly; the germ
chase for linearity is then the same chase, in the vocabulary of
`AlgebraicGeometry.SheafOfModules.germ_hom_smul`.

**Spelling of the ring sheaf in the derived statement.** `derivedUnitStalkIso` is stated at
`Stacks.SheafOfModules.Tensor.ringSheaf Rc`, which is the spelling in which the ambient category
of `Stacks.DerivedTensor.RingedSite.unitObject` is written, so that the derived stalk functor
applies to the unit object with nothing in between. That sheaf of rings, `structureSheaf Rc`,
`(Stacks.SheafOfModules.ringedSite Rc).ringSheaf` and — for a ringed space `Y` —
`structureSheafRing Y` against `Rc := Y.sheaf`, all unfold to
`(sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).obj Rc` and so are
equal by `rfl`: the `HasSheafCompose` instance each of them seats is a `Prop`, hence irrelevant,
and `TopCat.Sheaf`, `SheafedSpace.sheaf` and `sheafCompose` are all transparent at the default
transparency the elaborator checks these against. In particular the statement is usable at
`Rc := Y.sheaf` for `Y : AlgebraicGeometry.Scheme`.

**Why the derived statement is a composite and not a new theorem.**
`AlgebraicGeometry.SheafOfModules.derivedStalkFunctor 𝒪 x` is by definition
`(stalkFunctor 𝒪 x).mapDerivedCategory`, so
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` applies to it verbatim and moves the
degree-zero placement past the stalk; what is left is `unitStalkIso`, mapped into the derived
category by `DerivedCategory.singleFunctor`.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SheafOfModules

section Stalk

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- **The stalk at `x` of the structure sheaf viewed as a module over itself is the stalk ring**,
as an isomorphism of additive groups: both are the same filtered colimit over the open
neighbourhoods of `x`, computed in `AddCommGrpCat` on the left and in `RingCat` on the right,
and `forget₂ RingCat AddCommGrpCat` preserves that colimit. -/
def unitStalkAddEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
        (_root_.SheafOfModules.unit O).val.presheaf x) ≃+
      ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x) :=
  (preservesColimitIso (forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ O.obj)).symm.addCommGroupIsoToAddEquiv

/-- `unitStalkAddEquiv` carries the germ of a section of the unit module to the germ of the
corresponding section of the sheaf of rings. -/
theorem unitStalkAddEquiv_germ (U : Opens X) (hx : x ∈ U) (r : O.obj.obj (op U)) :
    unitStalkAddEquiv O x
        ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
          (_root_.SheafOfModules.unit O).val.presheaf U x hx).hom r) =
      (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U x hx).hom r := by
  have h := ι_preservesColimitIso_inv (forget₂ RingCat.{u} AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ O.obj) (op ⟨U, hx⟩)
  exact congrArg (fun q => q.hom r) h

/-- **`unitStalkAddEquiv` turns the scalar action of the stalk ring into multiplication.** Both
sides are computed on germs: a scalar and an element of the stalk are germs of sections over a
common open, the action on germs is the germ of the action
(`AlgebraicGeometry.SheafOfModules.germ_hom_smul`), and the action of a section of `𝒪` on a
section of the unit module is multiplication in `𝒪`. -/
theorem unitStalkAddEquiv_smul
    (r : ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
    (m : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
      (_root_.SheafOfModules.unit O).val.presheaf x)) :
    unitStalkAddEquiv O x (r • m) = r * unitStalkAddEquiv O x m := by
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u})
    (_root_.SheafOfModules.unit O).val.presheaf m
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := RingCat.{u}) O.obj r
  have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← TopCat.Presheaf.germ_res_apply O.obj (homOfLE (inf_le_right : U ⊓ V ≤ V)) x hxW t,
    ← TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u})
      (_root_.SheafOfModules.unit O).val.presheaf (homOfLE (inf_le_left : U ⊓ V ≤ U)) x hxW s]
  refine (congrArg _
    (germ_hom_smul O x (_root_.SheafOfModules.unit O).val (U ⊓ V) hxW _ _).symm).trans ?_
  exact ((unitStalkAddEquiv_germ O x (U ⊓ V) hxW _).trans (map_mul _ _ _)).trans
    (congrArg _ (unitStalkAddEquiv_germ O x (U ⊓ V) hxW _).symm)

/-- **The stalk at `x` of the structure sheaf viewed as a module over itself is the stalk ring**,
as a linear isomorphism over the stalk ring: `unitStalkAddEquiv` with the linearity supplied by
`unitStalkAddEquiv_smul`. -/
def unitStalkLinearEquiv :
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X)
        (_root_.SheafOfModules.unit O).val.presheaf x) ≃ₗ[
      ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)]
      ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x) where
  __ := unitStalkAddEquiv O x
  map_smul' := unitStalkAddEquiv_smul O x

/-- **The stalk of the unit module is the stalk ring as a module over itself**, as an
isomorphism in `ModuleCat 𝒪_x`: this is `unitStalkLinearEquiv` read in the category of modules
over the `RingCat`-valued stalk that `AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its
values in. -/
def unitStalkIso :
    (stalkFunctor O x).obj (_root_.SheafOfModules.unit O) ≅
      ModuleCat.of (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))
        (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)) :=
  (unitStalkLinearEquiv O x).toModuleIso

end Stalk

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (x : X)

/-- **The derived stalk of the unit of the derived tensor product is the stalk ring in degree
zero.** The unit object of [Stacks, Tag 06YU] on the ringed site of opens of `X` is the
structure sheaf, viewed as a module over itself, placed in degree zero; its derived stalk at
`x` is `𝒪_x`, viewed as a module over itself, placed in degree zero.

The derived stalk functor is the derived functor of the stalk functor, which is exact, so the
degree-zero placement passes through it
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`); what remains is `unitStalkIso`,
carried into the derived category by `DerivedCategory.singleFunctor`. -/
def derivedUnitStalkIso :
    (derivedStalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Rc) x).obj
        (Stacks.DerivedTensor.RingedSite.unitObject (Stacks.SheafOfModules.ringedSite Rc)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (ToType (TopCat.Presheaf.stalk
        (C := RingCat.{u}) (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf Rc).obj x))) 0).obj
        (ModuleCat.of
          (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X)
            (Stacks.SheafOfModules.Tensor.ringSheaf Rc).obj x))
          (ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X)
            (Stacks.SheafOfModules.Tensor.ringSheaf Rc).obj x))) :=
  ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Rc) x).mapDerivedCategorySingleFunctor
      0).app (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc)) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (ToType (TopCat.Presheaf.stalk
      (C := RingCat.{u}) (X := X) (Stacks.SheafOfModules.Tensor.ringSheaf Rc).obj x))) 0).mapIso
      (unitStalkIso (Stacks.SheafOfModules.Tensor.ringSheaf Rc) x)

end Derived

end AlgebraicGeometry.SheafOfModules

end
