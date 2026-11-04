module

public import StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Basic

/-!
# A trivialization datum for the tensor algebra reduces to one for any concrete target

`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.GradedSectionAlgebraHom` is the trivialization
datum that Tag 01O4's classifying morphism consumes, and the companion file
`StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Basic` takes it as a hypothesis because
the tensor algebra of a sheaf of modules is itself a hypothesis at this pin, nothing being known
about its multiplication beyond the fields of
`SheafOfModules.TensorExteriorSymmetricAlgebras`.

**One of those fields is the universal property.** `tensor_isTensorAlgebra` says the tensor
algebra maps uniquely to *every* sheaf of graded algebras carrying a degree-one generator, by a
unital homomorphism — `SheafOfModules.GradedAlgebra.IsTensorAlgebra.descAny`. A trivialization
datum pulls back along a unital homomorphism, so a datum for any concrete graded algebra with a
degree-one generator of `ℒ` yields one for the abstract tensor algebra. That is the content of
this file.

So the datum is not inaccessible at this pin: what it needs is a concrete graded algebra to
descend into, together with a map out of `ℒ` into its degree-one piece. The earlier note in
`Basic.lean` reasoned only from `tensorPieceIso_mul_left`, which relates `tensor.mul` to tensor
concatenation when the left factor has degree one, and concluded that no multiplicative family
in all degrees is reachable. That route is indeed blocked; this one is not, and it does not pass
through the tensor powers at all — the multiplicativity comes from `descAny`'s own, and the
note has been corrected.

## Main definitions

* `…GradedSectionAlgebraHom.precomp`: a trivialization datum pulls back along a unital
  homomorphism of sheaves of graded algebras.
* `…GradedSectionAlgebraHom.ofTensorAlgebra`: **the reduction.** A datum for a tensor algebra,
  from a datum for any sheaf of graded algebras together with a degree-one generator.
* `…datumOfGenerator`: the reduction in the shape Tag 01O4 consumes — a trivialization datum for
  `(TA T P.L).tensor` over an open of the test scheme, from a graded algebra on that scheme and a
  map out of the pair's invertible sheaf.

## Implementation notes

**Both laws are one `congrArg` and one field.** `precomp`'s product law is the homomorphism's
`map_mul` at the open `W`, followed by the datum's `map_gmul`; its unit law is `map_one` followed
by `map_gone`. No transport appears, the degree index of `map_gmul` being literally `i + j`.

**The additive structure is read off the module morphism.** `(φ.app n).val.app W` is a morphism
of modules over the ring of sections at `W`, so it is additive and unit-preserving for addition;
it is packaged as an `AddMonoidHom` exactly as
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pairPieceHom` packages the pair's own `ψ`.

**Nothing here produces a concrete target.** The reduction moves the obligation from the
abstract tensor algebra to a graded algebra of the caller's choosing; which graded algebra makes
it dischargeable is not settled here. See the `Not done here` section.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)

## Not done here

**No trivialization datum is constructed in this file, and no project tag is attached.** What
the reduction leaves is a sheaf of graded algebras on the test scheme whose degree-`n` sections
over the chosen open carry a multiplicative, unital family of maps into a commutative ring,
together with a map out of `ℒ` into its degree-one piece. The natural candidate — the structure
sheaf in every degree with its own multiplication, pushed forward from a scheme over the test
scheme — is constructed: `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.pushforwardUnitGradedAlgebra` of
`StacksFrontier.AlgebraicGeometry.ProjF1Dehomogenization.Trivialization` is `g_*𝒪_X` in every degree
for an arbitrary morphism `g : X ⟶ T` into the test scheme, and `datumOfGenerator` descends a
datum from it there, in `datumOfTrivialization`; the map out of `ℒ` is a trivialization of `g^*ℒ`
read through the pullback–pushforward adjunction. The remaining two inputs of the label — the
cover of the test scheme by opens on which some degree-one image is a basis, and bijectivity on
strict-equivalence classes — are untouched here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.ProjF1Dehomogenization

universe w t a v u

section Datum

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {G G' : SheafOfModules.GradedAlgebra.{t, a} R} {W : Cᵒᵖ} {B : Type w} [CommRing B]

/-- **A trivialization datum pulls back along a unital homomorphism.** Composing each
coefficient map with the homomorphism's component at that degree preserves both laws: the
product law is the homomorphism's `map_mul` at `W` followed by the datum's `map_gmul`, and the
unit law is its `map_one` followed by `map_gone`. -/
public def GradedSectionAlgebraHom.precomp (φ : SheafOfModules.GradedAlgebra.UnitalHom G G')
    (Θ : GradedSectionAlgebraHom G' W B) : GradedSectionAlgebraHom G W B where
  toFun n := (Θ.toFun n).comp
    { toFun := (φ.app n).val.app W
      map_zero' := map_zero _
      map_add' := map_add _ }
  map_gmul i j x y :=
    Eq.trans (congrArg (Θ.toFun (i + j)) (φ.map_mul i j W x y)) (Θ.map_gmul i j _ _)
  map_gone := Eq.trans (congrArg (Θ.toFun 0) (φ.map_one W)) Θ.map_gone

/-- The degree-`n` coefficient map of `Θ.precomp φ` sends a section `x` of `G.piece n` over `W` to
`Θ.toFun n` applied to the component of `φ` at `n`, evaluated at `x`. -/
@[simp]
public theorem GradedSectionAlgebraHom.precomp_toFun
    (φ : SheafOfModules.GradedAlgebra.UnitalHom G G') (Θ : GradedSectionAlgebraHom G' W B)
    (n : ℤ) (x : (G.piece n).val.obj W) :
    (Θ.precomp φ).toFun n x = Θ.toFun n ((φ.app n).val.app W x) :=
  rfl

/-- **The reduction.** For a tensor algebra the trivialization datum needs no knowledge of its
multiplication: its universal property maps it to any sheaf of graded algebras carrying a
degree-one generator, and the datum pulls back along that map.

So a datum for `G` — a concrete graded algebra of the caller's choosing — together with a map
`κ` out of the generating sheaf, is a datum for the tensor algebra. -/
public def GradedSectionAlgebraHom.ofTensorAlgebra {M : SheafOfModules.{a} R}
    {Gt : SheafOfModules.GradedAlgebra.{t, a} R} {gen : M ⟶ Gt.piece 1}
    (hGt : SheafOfModules.GradedAlgebra.IsTensorAlgebra Gt gen)
    (G : SheafOfModules.GradedAlgebra.{t, a} R) (κ : M ⟶ G.piece 1)
    (Θ : GradedSectionAlgebraHom G W B) : GradedSectionAlgebraHom Gt W B :=
  Θ.precomp (hGt.descAny G κ)

end Datum

/-! ### In the shape Tag 01O4 consumes -/

section Pair

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
  {T : Scheme.{u}} {f : T ⟶ S} (P : F1Pair A TA f) (U : S.Opens) {B : Type u} [CommRing B]

/-- **The trivialization datum that Tag 01O4's classifying morphism consumes, from a concrete
graded algebra on the test scheme.** The pair's tensor algebra is a tensor algebra by the field
`tensor_isTensorAlgebra` of the hypothesis, so
`Stacks.AlgebraicGeometry.ProjF1Dehomogenization.GradedSectionAlgebraHom.ofTensorAlgebra`
applies with the pair's invertible sheaf as the generating sheaf.

Composed with `Stacks.AlgebraicGeometry.ProjF1Dehomogenization.toRelativeProjOfPair`, this turns
a graded algebra on `T` with a degree-one map out of `ℒ` and a sectionwise multiplicative family
into a morphism into relative `Proj`. -/
public def datumOfGenerator (G : SheafOfModules.GradedAlgebra.{u, u}
      (Sheaf.toRingCat (Opens.grothendieckTopology ↥T) T.sheaf))
    (κ : P.L ⟶ G.piece 1) (Θ : GradedSectionAlgebraHom G (op (f ⁻¹ᵁ U)) B) :
    GradedSectionAlgebraHom (TA T P.L).tensor (op (f ⁻¹ᵁ U)) B :=
  GradedSectionAlgebraHom.ofTensorAlgebra (TA T P.L).tensor_isTensorAlgebra G κ Θ

end Pair

end Stacks.AlgebraicGeometry.ProjF1Dehomogenization

end
