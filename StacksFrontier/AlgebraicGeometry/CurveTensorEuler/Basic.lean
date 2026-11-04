module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.EulerCharacteristic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre rank of a sheaf of modules at a point

The fibre of a sheaf of modules at a point of a scheme is the tensor product of its stalk with
the residue field, over the local ring. Its dimension over the residue field is the *fibre
rank*. At the generic point of an integral scheme this is the generic rank.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.fiberRank`: the dimension over the residue field of the
  fibre of a sheaf of modules at a point.

## Main results

* `Stacks.AlgebraicGeometry.CurveTensorEuler.eulerCharacteristic_irrelevant`: the Euler
  characteristic of a module on a proper scheme over a field does not depend on which proof of
  coherence is supplied to it.

## Implementation notes

The stalk of the module is taken in the category of presheaves of modules, and carries its
module structure over the stalk of the structure sheaf; the residue field is an algebra over
that stalk through `Scheme.residue`. Both instances have to be supplied explicitly, since
neither is found by instance search at the spelling used here.

The second result is proof irrelevance, and it is recorded because the statement of Tag 0AYV
is an existential over a coherence proof: it says that the equation holds *for some* proof of
coherence of the tensor product. Since `SheafOfModules.IsCoherent` is `Prop`-valued, the value
of `AlgebraicGeometry.eulerCharacteristic` is unchanged by the choice, so that existential is
no weaker than the equation for an arbitrary coherence proof, and a consumer need not track
which proof was used.

## Relation to Tag 0AYV

Tag 0AYV asserts, for a proper curve `X` over a field `k`, a finite locally free `E` of rank
`n` and a coherent `F`, that the tensor product `E ⊗ F` is coherent and that

`χ(E ⊗ F) = r · deg(E) + n · χ(F)`,

where `r` is the fibre rank of `F` at the generic point. That equation is **not** proved here,
and no Stacks attribute is attached by this file.

What this file adds is the only piece of the vocabulary of the statement that this repository
did not already have. The rest is already present:

* `AlgebraicGeometry.eulerCharacteristic`
  (`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/EulerCharacteristic.lean:48`);
* `AlgebraicGeometry.curveDegree`
  (`StacksFrontier/AlgebraicGeometry/Variety/Curve/Degree.lean:51`), which carries the Tag 0AYR
  attribute for the finite locally free case and is the `deg` of the statement;
* `AlgebraicGeometry.IsCurve` (`StacksFrontier/AlgebraicGeometry/Variety/Curve/Defs.lean:46`);
* `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`
  (`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean:62`), which must be written at
  `.{u, u, u}`;
* `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, the sheaf tensor product of
  Stacks Tag 01CB;
* coherence of `E` and of the structure sheaf over a proper base, in
  `StacksFrontier/AlgebraicGeometry/CurveEulerBridge/Basic.lean`.

With `fiberRank` the equation of the statement is a well-formed statement of this repository, with no
extra hypothesis. What it still owes is the theory, not the vocabulary:

* coherence of a tensor product. No statement combining coherence with a tensor product is
  available, so even the existential witness of the statement is unavailable.
* additivity of the Euler characteristic in a short exact sequence, Tag 08AA, for which this
  repository has no declaration. Note that the long exact sequence itself *is* available, as
  `CategoryTheory.DeltaFunctor` instantiated at a right derived functor over a category with
  enough injectives; what is missing is finite dimensionality of each cohomology group and
  finiteness of the set of degrees where it is nonzero, without which the alternating sum
  defining the Euler characteristic — a `finsum`, which is zero on an infinite support — is
  not pinned down. Those finiteness statements are absent: no declaration in this repository
  mentions `AlgebraicGeometry.cohomologyOverField` in its statement.
* the dévissage induction for coherent modules on a Noetherian scheme, Tags 01YF and 01YG,
  which is present in `StacksFrontier/AlgebraicGeometry/DevissageNoetherian/Basic.lean` but
  conditional on two hypotheses, `HasSupportSplitting` and `HasIrreducibleDevissage`, that
  nothing in this repository discharges.

## References

* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The dimension over the residue field at `x` of the fibre at `x` of a sheaf of modules:
the residue field tensored with the stalk, over the local ring at `x`. -/
@[sga "1 I 7.5" "more general"]
public noncomputable def fiberRank {X : Scheme.{u}} (F : X.Modules) (x : X) : ℕ :=
  letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  Module.finrank (X.residueField x)
    (X.residueField x ⊗[X.presheaf.stalk x] F.presheaf.stalk x)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.AlgebraicGeometry.CurveTensorEuler

/-- The Euler characteristic of a module on a proper scheme over a field does not depend on
which proof of coherence is supplied: coherence is `Prop`-valued. -/
public theorem eulerCharacteristic_irrelevant (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (G : X.Modules) (h h' : G.IsCoherent) :
    @eulerCharacteristic k _ X f _ G h = @eulerCharacteristic k _ X f _ G h' :=
  rfl

end Stacks.AlgebraicGeometry.CurveTensorEuler

end
