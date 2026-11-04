module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.Basic

/-!
# Dehomogenization of an invertible degree-one quotient

The residue of the label `01O4 "represents_f1"` is a single bijection, and
`Stacks.AlgebraicGeometry.ProjF1Normalisation` reduced both of its directions to one
construction: a morphism into relative `Proj` out of an invertible degree-one quotient of the
graded algebra. `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart` supplied the *target* half of
that construction — a ring homomorphism out of the graded ring of sections over an affine open
of the base, inverting one positive-degree homogeneous section, classifies a morphism into
relative `Proj` lying over that open. This file supplies the *source* half: the passage from a
quotient pair to such a ring homomorphism.

The passage is purely algebraic once the invertible sheaf has been trivialized. A pair
`(ℒ, ψ)` over `f : T ⟶ S` consists of maps `ψ n : 𝒜 n ⟶ f_* T(ℒ) n` which are multiplicative
and unital on homogeneous local sections. If the homogeneous sections of `T(ℒ)` over an open of
`T` are carried to a commutative ring `B` by an additive family that is itself multiplicative
and unital — `GradedSectionAlgebraHom` below, the *trivialization datum* — then composing with
`ψ` gives a multiplicative, unital additive family out of the homogeneous sections of `𝒜`, and
`DirectSum.toSemiring` turns it into a ring homomorphism out of the whole graded ring of
sections.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.GradedSectionAlgebraHom`: a multiplicative,
  unital additive family out of the homogeneous sections of a sheaf of graded algebras over one
  open of the site, into a commutative ring.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pairPieceHom`: the composite family attached
  to a quotient pair and a trivialization datum, in the `ℕ`-indexed spelling the graded ring of
  sections uses.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.dehomogenize`: **the dehomogenization.** The
  ring homomorphism `𝒜(U) → B` determined by a quotient pair and a trivialization datum.

## Main results

* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pairPieceHom_one` and `pairPieceHom_mul`:
  the unit and product laws of the composite family, which are exactly the pair's own
  `map_one` and `map_mul` read through the trivialization datum.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.dehomogenize_of`: the dehomogenization on a
  homogeneous section is the trivialization datum applied to that section's image under `ψ`.
* `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.dehomogenize_strHom`: its value on a
  degree-`0` multiple of the unit, which is what makes the classified morphism lie over the
  base.

## Implementation notes

**Why the trivialization is a datum here and not a construction.** The tensor algebra of a sheaf
of modules is *stated* and nowhere *constructed* in this library — see the implementation notes
of `StacksDraft.AlgebraicGeometry.F3.ProjRepresentsF1.Basic` — so `F1Pair` carries it as the
hypothesis `TensorAlgebras`, and nothing is known about the multiplication of
`(TA T L).tensor` beyond the fields of `SheafOfModules.TensorExteriorSymmetricAlgebras`. Taking
the datum as input is what lets this file be about the pair's own multiplicativity and nothing
else.

One route to such a map is genuinely blocked, and it is worth naming because it is the obvious
one: the field `tensorPieceIso_mul_left` relates `tensor.mul` to tensor concatenation only when
the left factor has degree one, so a trivializing section of `ℒ` gives no multiplicative family
in all degrees by that road. This does not mean that no such map can be built, as
`StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Universal` shows: another field of the
same hypothesis is the universal property `tensor_isTensorAlgebra`, which maps the tensor algebra
to *every* sheaf of graded algebras carrying a degree-one generator, and a datum pulls back along
such a map. So a datum for any concrete graded algebra with a map out of `ℒ` into its degree-one
piece gives one here, with the multiplicativity coming from the descended homomorphism rather
than from the tensor powers.

**Degree casts are definitional.** The graded ring of sections is `ℕ`-indexed while the
homogeneous pieces and the maps `ψ` are `ℤ`-indexed, so every statement below crosses the cast
`((i + j : ℕ) : ℤ) = (i : ℤ) + (j : ℤ)`. That equation is `rfl` — `Int.add` on two `Int.ofNat`
arguments reduces to `Int.ofNat` of the sum — which is what lets `pairPieceHom_mul` be a
composite of `congrArg` and the pair's `map_mul` with no transport. The same fact is already
relied on by the `GradedMonoid.GMul` instance of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionPieces`.

**No name is added to another file's namespace.** `pairPieceHom` and `dehomogenize` take the
pair as an explicit argument rather than being declared in the
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair` namespace, following the convention of
`StacksDraft.AlgebraicGeometry.F3.ProjF1Normalisation.Basic`.

## What is not done here

No project tag is attached. The label `01O4 "represents_f1"` covers four assertions and the
fourth — the representation itself — needs, beyond this file, a trivialization datum for the
pair's tensor algebra, the glueing of the resulting local morphisms over a cover of the test
scheme, and the bijectivity of the assembled map on strict-equivalence classes.
`StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Universal` reduces the first of those to a
concrete graded algebra on the test scheme carrying a degree-one map out of `ℒ`; naming such an
algebra is what remains of it.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ProjF1Dehomogenization

universe w t a v u

/-! ### The trivialization datum -/

section Datum

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- **A trivialization datum for a sheaf of graded algebras at one open.** An additive map out
of the homogeneous sections of each degree over a fixed open of the site, into a commutative
ring, carrying the graded multiplication to the product and the algebra unit to `1`.

For the tensor algebra of an invertible sheaf this is the data of a trivializing section: over
an open where a section `t` of `ℒ` is a basis, `t ^ n` is a basis of `ℒ ^ ⊗ n`, and the
coefficient of a homogeneous section against it is such a family. -/
public structure GradedSectionAlgebraHom (G : SheafOfModules.GradedAlgebra.{t, a} R) (W : Cᵒᵖ)
    (B : Type w) [CommRing B] where
  /-- The coefficient map in each degree. -/
  toFun (n : ℤ) : (G.piece n).val.obj W →+ B
  /-- It carries the graded multiplication to the product of `B`. -/
  map_gmul (i j : ℤ) (x : (G.piece i).val.obj W) (y : (G.piece j).val.obj W) :
    toFun (i + j) ((G.mul i j).app W x y) = toFun i x * toFun j y
  /-- It carries the algebra unit to `1`. -/
  map_gone : toFun 0 (G.one.eval W) = 1

end Datum

/-! ### The dehomogenization -/

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  {T : Scheme.{u}} {f : T ⟶ S} (P : F1Pair A TA f) (U : S.Opens) {B : Type w} [CommRing B]
  (Θ : GradedSectionAlgebraHom (TA T P.L).tensor (op (f ⁻¹ᵁ U)) B)

/-- **The composite family.** The degree-`n` homogeneous sections of the graded algebra over `U`
are sent into `B` by the pair's graded map followed by the trivialization datum. The index is
`ℕ`, as in the graded ring of sections. -/
public def pairPieceHom (n : ℕ) : A.sectionPieces U n →+ B :=
  (Θ.toFun (n : ℤ)).comp
    { toFun := (P.ψ (n : ℤ)).val.app (op U)
      map_zero' := map_zero _
      map_add' := map_add _ }

public theorem pairPieceHom_apply (n : ℕ) (x : A.sectionPieces U n) :
    pairPieceHom A TA P U Θ n x = Θ.toFun (n : ℤ) ((P.ψ (n : ℤ)).val.app (op U) x) :=
  rfl

/-- **The unit law**, which is the pair's `map_one` followed by the datum's `map_gone`. -/
public theorem pairPieceHom_one : pairPieceHom A TA P U Θ 0 (A.one U) = 1 :=
  Eq.trans (congrArg (Θ.toFun 0) (P.map_one U)) Θ.map_gone

/-- **The product law**, which is the pair's `map_mul` followed by the datum's `map_gmul`.

Both sides read the degree `((i + j : ℕ) : ℤ)` as `(i : ℤ) + (j : ℤ)`, which is definitional. -/
public theorem pairPieceHom_mul (i j : ℕ) (x : A.sectionPieces U i) (y : A.sectionPieces U j) :
    pairPieceHom A TA P U Θ (i + j) ((A.mul (i : ℤ) (j : ℤ)).app U x y) =
      pairPieceHom A TA P U Θ i x * pairPieceHom A TA P U Θ j y :=
  Eq.trans (congrArg (Θ.toFun ((i : ℤ) + (j : ℤ))) (P.map_mul (i : ℤ) (j : ℤ) U x y))
    (Θ.map_gmul (i : ℤ) (j : ℤ) _ _)

/-- **The dehomogenization of a quotient pair at a trivialization datum.** The ring
homomorphism out of the graded ring of homogeneous sections of `𝒜` over `U` whose restriction
to each degree is the pair's graded map followed by the datum.

This is the shape `AlgebraicGeometry.Proj.fromOfGlobalSections` and
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit` consume, so it is the
missing source half of Tag 01O4's classifying morphism. -/
public def dehomogenize : A.sectionRing U →+* B :=
  DirectSum.toSemiring (pairPieceHom A TA P U Θ) (pairPieceHom_one A TA P U Θ)
    (fun {i j} x y => pairPieceHom_mul A TA P U Θ i j x y)

/-- The dehomogenization on a homogeneous section. -/
@[simp]
public theorem dehomogenize_of {n : ℕ} (x : A.sectionPieces U n) :
    dehomogenize A TA P U Θ (DirectSum.of (A.sectionPieces U) n x) =
      Θ.toFun (n : ℤ) ((P.ψ (n : ℤ)).val.app (op U) x) :=
  DirectSum.toSemiring_of _ _ _ n x

/-- **The dehomogenization on the structure map.** The degree-`0` multiple of the unit attached
to a function on the base is sent to the datum's degree-`0` coefficient of its image under
`ψ 0`. Together with
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.toRelativeProjOfIsUnit_comp_toBase` this is what
places the classified morphism over the affine open it was built on. -/
public theorem dehomogenize_strHom (r : Γ(S, U)) :
    dehomogenize A TA P U Θ (A.strHom U r) =
      Θ.toFun 0 ((P.ψ 0).val.app (op U) (r • A.one U)) :=
  dehomogenize_of A TA P U Θ (r • A.one U)

end Stacks.AlgebraicGeometry.ProjF1Dehomogenization

end
