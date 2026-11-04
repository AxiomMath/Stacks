module

public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.Topology.Sheaves.Modules.Invertible
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Degree of a locally free sheaf on a proper curve

On a proper scheme of dimension at most one over a field, the degree of a finite locally free
sheaf of constant rank is its Euler characteristic minus its rank times the Euler
characteristic of the structure sheaf. For an invertible sheaf the rank is one.

## Main definitions

* `AlgebraicGeometry.curveDegree` is the degree of a finite locally free sheaf of constant
  rank.
* `AlgebraicGeometry.invertibleCurveDegree` is the degree of an invertible sheaf.

## Main results

* `AlgebraicGeometry.curveDegree_eq_eulerCharacteristic_sub` identifies the degree with the
  difference of Euler characteristics when coherence instances are available.
* `AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree` identifies the invertible
  specialization with the degree at rank one whenever the locally free rank-one instance is
  available.
* `AlgebraicGeometry.invertibleCurveDegree_eq_eulerCharacteristic_sub` gives the
  Euler-characteristic formula for an invertible sheaf.

## Implementation notes

The alternating sum is written directly in the definition, rather than requiring a coherence
instance in its signature. Properness over a field makes the structure sheaf and finite locally
free sheaves coherent; the comparison with `AlgebraicGeometry.eulerCharacteristic` is
definitionally true once these instances are supplied. This keeps the degree available to
statements about locally free sheaves without adding a coherence hypothesis.

The rank is an explicit argument so that later additivity and pullback statements can use the
same degree function at their respective ranks. The invertible case fixes that rank to one, but
takes invertibility rather than local freeness of rank one as its hypothesis, so the two degrees
are separate definitions and `invertibleCurveDegree_eq_curveDegree` compares them where both
hypotheses hold.

The implication from an invertible sheaf on a scheme to a locally free sheaf of rank one is
clause (2) of Tag 0B8M, not Tag 01CS — Tag 01CS is the
*definition* of invertibility — and it is available, as the instance
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible` of
`StacksFrontier/AlgebraicGeometry/InvertibleClasses/Basic.lean`, at exactly the spelling of
invertibility used below. Consequently `invertibleCurveDegree_eq_curveDegree` applies to every
invertible sheaf with no further hypothesis, which is
`AlgebraicGeometry.invertibleCurveDegree_eq_curveDegree_one` of that same file.

Neither comparison is needed to pass between the two degrees in a statement about Euler
characteristics: `curveDegree_eq_eulerCharacteristic_sub` and
`invertibleCurveDegree_eq_eulerCharacteristic_sub` below both hold by `rfl`, so a computation
that writes every term as an Euler characteristic never has to match the rank index. That is how
`AlgebraicGeometry.invertibleCurveDegree_tensorSheaf_eq_add_of_devissage` of
`StacksFrontier/AlgebraicGeometry/CurveDegreeTensor/Basic.lean` derives the invertible case of
Tag 0AYX from the rank-one case of Tag 0AYV.

Invertibility is `AlgebraicGeometry.SheafOfModules.IsInvertible`, the predicate that the
left-tensor functor of the sheaf is an equivalence, which is also what
`AlgebraicGeometry.Scheme.Modules.IsAmple` takes.

## References

* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The degree of a finite locally free sheaf of constant rank on a proper scheme of
dimension at most one over a field. -/
@[stacks 0AYR "finite locally free case", stacks 0BRX "the degree formula"]
public noncomputable def curveDegree (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (_hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank] : ℤ :=
  (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    (Module.finrank k (cohomologyOverField k f E n) : ℤ)) -
    (rank : ℤ) * (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank k
        (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) : ℤ))

/-- The defining Euler-characteristic formula for degree when the coherence needed for
`eulerCharacteristic` is available. -/
public theorem curveDegree_eq_eulerCharacteristic_sub (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules) (rank : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E rank]
    [E.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent] :
    curveDegree k f hdim E rank =
      eulerCharacteristic k f E -
        (rank : ℤ) * eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) := rfl

/-- The degree of an invertible sheaf on a proper scheme of dimension at most one over a
field: its Euler characteristic minus the Euler characteristic of the structure sheaf. -/
@[stacks 0AYR "invertible case"]
public noncomputable def invertibleCurveDegree (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (_hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] : ℤ :=
  (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    (Module.finrank k (cohomologyOverField k f L n) : ℤ)) -
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank k
        (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) : ℤ))

/-- The degree of an invertible sheaf agrees with the rank-one specialization of the degree
of a finite locally free sheaf. -/
@[simp] public theorem invertibleCurveDegree_eq_curveDegree (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] :
    invertibleCurveDegree k f hdim L = curveDegree k f hdim L 1 := by
  simp [invertibleCurveDegree, curveDegree]

/-- The defining Euler-characteristic formula for the degree of an invertible sheaf when the
coherence needed for `eulerCharacteristic` is available. -/
public theorem invertibleCurveDegree_eq_eulerCharacteristic_sub (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [L.IsCoherent] [(SheafOfModules.unit X.ringCatSheaf).IsCoherent] :
    invertibleCurveDegree k f hdim L =
      eulerCharacteristic k f L -
        eulerCharacteristic k f (SheafOfModules.unit X.ringCatSheaf) := rfl

end AlgebraicGeometry
