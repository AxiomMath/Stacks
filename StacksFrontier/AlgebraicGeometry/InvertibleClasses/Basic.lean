module

public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Sheaf
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFree

/-!
# The two invertibility predicates of Tag 01CS agree

The repository carries two classes for "the sheaf of modules `L` is invertible", both of them
Tag 01CS and both of them saying that tensoring on the left by `L` is represented by an
equivalence: `AlgebraicGeometry.SheafOfModules.IsInvertible` of
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean` and
`Stacks.SheafOfModules.IsInvertible` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`. Their definitions are
field-for-field identical, but they are distinct constants with distinct `TensorLeftUniversal`
structures, so neither discharges the other by instance search. The identification itself is
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleCompare.lean`, which is imported here;
this file draws the consequences for an invertible module on a scheme that were previously
reachable only from the second class.

## Main results

* `Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry`: the same for the two
  copies of finite local freeness, Tag 01C6 (2), which the chain below has to cross.
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible`: on a scheme,
  an invertible module in the first spelling is finite locally free of rank one — clause 2 of
  Tag 0B8M, transported. In instance form, so that
  `AlgebraicGeometry.curveDegree` and quasi-coherence become available for an invertible module
  with no further hypothesis.
* `AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible`: an invertible module
  on a scheme is of finite presentation — the hypothesis Tag 01CE puts on the factor it tensors
  a coherent module by.
* `AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree_one`: the degree of an invertible
  sheaf on a proper scheme of dimension at most one is the rank-one degree, unconditionally.
* `AlgebraicGeometry.invertibleCurveDegree_eq_zero_of_iso_unit`: an invertible sheaf isomorphic
  to the structure sheaf has degree zero.

## Implementation notes

**Why the identification is two lines and not a construction.** Both classes have the single
field `exists_tensorFunctor : ∃ F, F.IsEquivalence ∧ Nonempty (TensorLeftUniversal O hO L F)`,
and the two `TensorLeftUniversal` structures have the same two fields `ι` and `bijective` at the
same types — the monoidal structure on presheaves of modules through which `ι`'s type is written
is obtained in both files by the same `change`-then-`infer_instance`, so the two field types are
the same term. Destructuring one witness and rebuilding it is therefore the whole proof, which
is why `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleCompare.lean` can state it outright. That identification makes the results
stated for either class usable for the other.
The special case of a tensor power is already done, by the same two lines, as the instance
`AlgebraicGeometry.Scheme.Modules.isInvertible_tensorPower` of
`StacksFrontier/AlgebraicGeometry/Ample/Defs.lean`.

**Direction of the instance.** Only the forward implication from the first class is an instance.
`Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one` is the converse of
`isFiniteLocallyFreeOfRank_one_of_isInvertible` and is deliberately a plain theorem, there and
here, so that instance search cannot cycle between invertibility and rank-one local freeness.

**Spellings of the structure sheaf.** `Stacks.SheafOfModules.TensorSheafification.structureSheaf`
  is a plain `def` and
`structureSheafRing` is `@[reducible]`, so an
  invertibility hypothesis written with
`X.ringCatSheaf.2` — the spelling of `AlgebraicGeometry.invertibleCurveDegree` and of the
chapter-33 statements — does not discharge one written with
`(structureSheafRing X.toRingedSpace).property` by instance search, although the two are
interchangeable by `exact`. The statements here use the first spelling and convert once.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Stacks.FiniteLocallyFree

/-- **The two finite-local-freeness predicates of Tag 01C6 (2) agree.** `IsFiniteLocallyFree` of
`StacksFrontier/AlgebraicGeometry/Modules/FiniteLocallyFree.lean` and
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` of
`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean` have the same single field at the same
type, so each is the other's witness. The first is where finite presentation is derived
(`Stacks.FiniteLocallyFree.isFinitePresentation`), the second is what
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` produces. -/
theorem isFiniteLocallyFree_iff_algebraicGeometry {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [∀ Y, HasWeakSheafify (J.over Y) AddCommGrpCat.{w}]
    [∀ Y, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} R) :
    IsFiniteLocallyFree.{w, v, u} M ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{w, v, u} M :=
  ⟨fun h => ⟨h.exists_isFiniteLocallyFreeData⟩, fun h => ⟨h.exists_isFiniteLocallyFreeData⟩⟩

end Stacks.FiniteLocallyFree

namespace AlgebraicGeometry.SheafOfModules

/-- **An invertible module on a scheme is finite locally free of rank one.** This is clause 2 of
Tag 0B8M, which `Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one`
proves for `Stacks.SheafOfModules.IsInvertible`, transported along
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
instance (priority := 100) isFiniteLocallyFreeOfRank_one_of_isInvertible (X : Scheme.{u})
    (L : X.Modules) [hL : IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
  (Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one X L).1
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L).2 hL)

/-- **An invertible module on a scheme is of finite presentation.** It is finite locally free of
rank one, hence finite locally free, hence of finite presentation by
`Stacks.FiniteLocallyFree.isFinitePresentation`, which is the finite-presentation half of
(4) ⟹ (1) of Tag 05P2. This is the hypothesis Tag 01CE places on the factor it tensors a
coherent module by. -/
instance (priority := 100) isFinitePresentation_of_isInvertible (X : Scheme.{u}) (L : X.Modules)
    [IsInvertible X.presheaf X.ringCatSheaf.2 L] : L.IsFinitePresentation :=
  have h := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have := (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry L).2 h
  Stacks.FiniteLocallyFree.isFinitePresentation L

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry

/-- **The degree of an invertible sheaf is the rank-one degree**, with no local-freeness
hypothesis. Tag 0AYR defines the two separately; since invertibility implies rank-one local
freeness, the comparison
`AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree` applies to every invertible sheaf. -/
theorem invertibleCurveDegree_eq_curveDegree_one (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    invertibleCurveDegree k f hdim L = curveDegree k f hdim L 1 :=
  invertibleCurveDegree_eq_curveDegree k f hdim L

/-- **An invertible sheaf isomorphic to the structure sheaf has degree zero.** The degree is an
isomorphism invariant (`AlgebraicGeometry.invertibleCurveDegree_eq_of_iso`) and the structure
sheaf has degree zero (`AlgebraicGeometry.invertibleCurveDegree_unit_eq_zero`, whose proof is
`sub_self`). This is the trivial case of the degree computations that Tags 0AYX and 0B40
require. -/
theorem invertibleCurveDegree_eq_zero_of_iso_unit (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    invertibleCurveDegree k f hdim L = 0 :=
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  (invertibleCurveDegree_eq_of_iso k f hdim e).trans (sub_self _)

end AlgebraicGeometry

end
