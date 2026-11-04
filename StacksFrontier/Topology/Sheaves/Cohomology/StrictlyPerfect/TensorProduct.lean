module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.TensorOfFiniteFreeSummands
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules

/-!
# The total tensor complex of two strictly perfect complexes on a ringed space

Strict perfection of a complex of `𝒪_X`-modules on a ringed space is
`StrictlyPerfect.IsStrictlyPerfect`: finitely many nonzero terms, each a direct summand of a
finite free `𝒪_X`-module.  This file shows that the total tensor complex
`Tot(E ⊗_{𝒪_X} F)` of two strictly perfect complexes is strictly perfect.

## Main results

* `StrictlyPerfect.isStrictlyPerfect_tensorComplex`: the total tensor complex of two strictly
  perfect complexes of `𝒪_X`-modules is strictly perfect.

## Implementation notes

The mathematics is already in the trees, for an arbitrary monoidal category with finite
biproducts: `strictlyPerfect_tensorObj`, which carries the `09J2` attribute.  What is missing,
and what this file supplies, is the instantiation at `𝒪_X`-modules on a ringed space, where
three identifications have to be made before that theorem can be applied.

* The monoidal structure.  Instance search does not find one on `StrictlyPerfect.OXMod X`:
  `SheafOfModules.monoidalCategorySheafTensor` is stated for a sheaf of rings in
  `CommRingCat.{max u v}` over a site `C : Type u` with `Category.{v} C`, so matching it
  against `X.sheaf` leaves the constraint `max u v = u` with both unknown.  It is seated here
  at `C := Opens X.carrier`, where the constraint is written out, exactly as
  `StacksFrontier/Topology/Sheaves/Cohomology/KFlat/OnARingedSpace.lean` seats the additivity of
  `⊗_{𝒪_X}`.  Seated that way the structure is the *re-seated* one, whose tensor product is
  `Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf` and whose unit is
  `SheafOfModules.unit`, both definitionally; so `MonoidalCategory.curriedTensor` is the
  bifunctor the Stacks tag files use, `finFree` is `StrictlyPerfect.finiteFree`, and
  `HomologicalComplex.tensorObj` is `Stacks.SheafOfModules.Tensor.tensorComplex`, each by
  `rfl`.  All four instances are `private`: `Mod(𝒪_X)` carries a second monoidal structure, the
  localized one of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean`, and leaving a
  visible instance behind would make which of the two is meant depend on import order.  The
  bridge theorem between the two spellings of strict perfection is private for the same reason:
  a public signature may not mention a private instance.  Only
  `StrictlyPerfect.isStrictlyPerfect_tensorComplex`, whose statement names neither the monoidal
  structure nor the generic predicate, is exported.

* The two spellings of boundedness.  `StrictlyPerfect.IsStrictlyPerfect` asks for the set of
  degrees with a nonzero term to be finite, and `StrictlyPerfect` asks for two bounds outside
  which the terms vanish; over `ℤ` a finite set of degrees is contained in an interval and an
  interval is finite.

* The two spellings of "direct summand of a finite free module".
  `StrictlyPerfect.IsDirectSummandOfFiniteFree` is stated after lifting the module and the
  finite free module into a common section universe, since their universes are independent
  there; here they coincide, and `StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract`
  removes the lift.

The universes of the space, its structure sheaf and its module sections coincide, as they must
for `Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf` to be stated at all.

Nothing here carries the `09J2` attribute: `strictlyPerfect_tensorObj` already does, and it is
the general statement of which this is an instance.  Repeating the attribute here would
record two independent claims on one clause of the tag.

## References

* [Stacks Project, Lemma 20.46.3 (Tag 09J2)](https://stacks.math.columbia.edu/tag/09J2)
* [Stacks Project, Definition 20.46.1 (Tag 08C4)](https://stacks.math.columbia.edu/tag/08C4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry TopologicalSpace

namespace StrictlyPerfect

universe u

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-! ### The monoidal structure on `𝒪_X`-modules whose tensor product is `⊗_{𝒪_X}` -/

/-- The symmetric monoidal structure on `𝒪_X`-modules whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf` and whose unit is the structure sheaf,
seated at the site `Opens X.carrier` so that its universe constraint is written out. -/
private instance monoidalOXMod : MonoidalCategory (OXMod.{u, u} X) :=
  SheafOfModules.monoidalCategorySheafTensor.{u, u} (C := Opens X.carrier) X.sheaf

/-- `⊗_{𝒪_X}` is additive in its first variable, at the `MonoidalCategory.curriedTensor`
spelling. -/
private instance curriedTensorAdditive : (curriedTensor (OXMod.{u, u} X)).Additive :=
  inferInstanceAs (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).Additive

/-- `M ⊗_{𝒪_X} -` is additive, at the `MonoidalCategory.curriedTensor` spelling. -/
private instance curriedTensorObjAdditive (M : OXMod.{u, u} X) :
    ((curriedTensor (OXMod.{u, u} X)).obj M).Additive :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.sheafTensor_obj_additive X M

/-- The total complex of the tensor double complex of two complexes of `𝒪_X`-modules exists,
at the `HomologicalComplex.HasTensor` spelling. -/
private instance hasTensorOXMod (E F : CochainComplex (OXMod.{u, u} X) ℤ) :
    HomologicalComplex.HasTensor E F :=
  AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.hasMapBifunctor_sheafTensor X E F

/-! ### The two spellings of strict perfection -/

/-- **Strict perfection of a complex of `𝒪_X`-modules is the monoidal-category notion.**  The
bridge is private, as is the monoidal structure its statement mentions.  The two notions differ
only in how they record boundedness — a finite set of nonzero degrees against a pair
of bounds outside which the terms vanish — and in whether the termwise condition is read before
or after lifting into a common section universe. -/
private theorem isStrictlyPerfect_iff_strictlyPerfect
    (E : CochainComplex (OXMod.{u, u} X) ℤ) :
    IsStrictlyPerfect E ↔ _root_.StrictlyPerfect E := by
  constructor
  · intro hE
    refine ⟨?_, fun i => ?_⟩
    · obtain ⟨a, ha⟩ := hE.bounded.bddBelow
      obtain ⟨b, hb⟩ := hE.bounded.bddAbove
      refine ⟨a, b, fun i hi => ?_⟩
      by_contra hz
      rcases hi with h | h
      · exact absurd (ha hz) (by omega)
      · exact absurd (hb hz) (by omega)
    · obtain ⟨n, ⟨r⟩⟩ :=
        (isDirectSummandOfFiniteFree_iff_retract (E.X i)).mp (hE.directSummand i)
      exact ⟨n, ⟨r⟩⟩
  · intro hE
    obtain ⟨a, b, hab⟩ := hE.bounded
    refine ⟨?_, fun i => ?_⟩
    · refine Set.Finite.subset (Set.finite_Icc a b) fun i hi => ?_
      simp only [Set.mem_Icc]
      by_contra hc
      exact hi (hab i (by omega))
    · exact (isDirectSummandOfFiniteFree_iff_retract (E.X i)).mpr (hE.summand i)

/-! ### The tensor product -/

/-- **The total tensor complex of two strictly perfect complexes of `𝒪_X`-modules is strictly
perfect.**  This is Tag 09J2 read on a ringed space: `strictlyPerfect_tensorObj` proves it for
an arbitrary monoidal category with finite biproducts, and `𝒪_X`-modules are one, with
`Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf` as the tensor product and
`Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf` as the induced total complex. -/
theorem isStrictlyPerfect_tensorComplex (E F : CochainComplex (OXMod.{u, u} X) ℤ)
    (hE : IsStrictlyPerfect E) (hF : IsStrictlyPerfect F) :
    IsStrictlyPerfect
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj E).obj F) :=
  (isStrictlyPerfect_iff_strictlyPerfect X _).mpr
    (strictlyPerfect_tensorObj E F ((isStrictlyPerfect_iff_strictlyPerfect X E).mp hE)
      ((isStrictlyPerfect_iff_strictlyPerfect X F).mp hF))

end StrictlyPerfect

end
