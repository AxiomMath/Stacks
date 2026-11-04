module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.RingTheory.GeometricallyReduced.Basic
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Multiplicities of irreducible components along a smooth morphism

Let `f : U ⟶ X` be a smooth morphism of locally Noetherian schemes, let `T'` be an irreducible
component of `U` and let `T` be the irreducible component of `X` obtained as the closure of the
image of `T'`. Then `T'` and `T` carry the same multiplicity: `m_{T', U} = m_{T, X}`.

Write `ξ'` for the generic point of `T'` and `ξ` for that of `T`, and put `A = 𝒪_{X, ξ}`,
`B = 𝒪_{U, ξ'}`. The stalk map `A → B` is a flat local homomorphism, so the length identity for
such a homomorphism gives `length_A(A) * length_B(B / 𝔪_A B) = length_B(B)`. The fibre of `f`
over `ξ` is smooth over the residue field `κ(ξ)`, hence reduced, and `B / 𝔪_A B` is the local
ring of that fibre at `ξ'`; being reduced, artinian and local it is a field, so the middle
factor is `1`.

## Main results

* `Stacks.Chow.componentMultiplicity_id_eq_of_smooth` — the two component multiplicities agree.

## Implementation notes

The multiplicity of a component of a scheme is its multiplicity as a component of the identity
closed immersion, in the sense of `Stacks.Chow.componentMultiplicity`; by
`Stacks.Chow.componentMultiplicity_eq_length_stalk` this is the length of the local ring at the
generic point over itself, so the statement reduces to the equality of the two lengths, which is
isolated as `Stacks.Chow.length_stalk_eq_length_stalk_of_smooth`.

The quotient `B / 𝔪_A B` is identified with the local ring of the scheme-theoretic fibre by
`AlgebraicGeometry.quotientStalkEquivFiberStalk`, and the base change `B ⊗_A A` with `B` by
`TensorProduct.AlgebraTensorModule.rid`.

## References

* [Stacks Project, Tag 0DR6](https://stacks.math.columbia.edu/tag/0DR6)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- A morphism of schemes carries the generic point of an irreducible component of its source to
the generic point of the irreducible component of its target cut out by the closure of the
image. -/
public theorem genericPoint_ofComponent_image_eq {X U : Scheme.{u}} (f : U ⟶ X)
    (T' : irreducibleComponents U) (T : irreducibleComponents X)
    (hT : closure (f.base '' (T' : Set U)) = (T : Set X)) :
    f.base (genericPoints.ofComponent T').1 = (genericPoints.ofComponent T).1 :=
  IsGenericPoint.eq
    (((genericPoints.isGenericPoint_ofComponent T').image f.continuous).trans hT)
    (genericPoints.isGenericPoint_ofComponent T)

/-- **Stacks 0DR6**, in terms of lengths. For a smooth morphism `f : U ⟶ X` of locally
Noetherian schemes and a generic point `ξ` of an irreducible component of `U`, the local ring of
`X` at `f ξ` and the local ring of `U` at `ξ` have the same length over themselves. -/
public theorem length_stalk_eq_length_stalk_of_smooth {X U : Scheme.{u}} (f : U ⟶ X) [Smooth f]
    [IsLocallyNoetherian X] (ξ : genericPoints U) :
    Module.length (X.presheaf.stalk (f.base ξ.1)) (X.presheaf.stalk (f.base ξ.1)) =
      Module.length (U.presheaf.stalk ξ.1) (U.presheaf.stalk ξ.1) := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian f
  let A : Type u := X.presheaf.stalk (f.base ξ.1)
  let B : Type u := U.presheaf.stalk ξ.1
  let φ : A →+* B := (f.stalkMap ξ.1).hom
  let : Algebra A B := φ.toAlgebra
  have : IsLocalHom (algebraMap A B) := (inferInstance : IsLocalHom φ)
  have : Module.Flat A B := AlgebraicGeometry.Flat.stalkMap f ξ.1
  have : IsArtinianRing B := generic_stalk_artinian ξ
  -- The fibre of `f` over `f ξ` is smooth over a field, hence reduced.
  have : Smooth (f.fiberToSpecResidueField (f.base ξ.1)) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback _ _) inferInstance
  have : GeometricallyReduced (f.fiberToSpecResidueField (f.base ξ.1)) :=
    geometricallyReduced_of_smooth _
  have : IsReduced (f.fiber (f.base ξ.1)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      (f.fiberToSpecResidueField (f.base ξ.1))
  -- Hence `B / 𝔪_A B`, the local ring of that fibre at `ξ`, is a reduced artinian local ring.
  have : Nontrivial (B ⧸ extendedMaximalIdeal A B) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top φ).ne
  have : IsLocalRing (B ⧸ extendedMaximalIdeal A B) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : _root_.IsReduced (B ⧸ extendedMaximalIdeal A B) :=
    isReduced_of_ringEquiv (quotientStalkEquivFiberStalk f ξ.1) inferInstance
  let : Field (B ⧸ extendedMaximalIdeal A B) :=
    (IsArtinianRing.isField_of_isReduced_of_isLocalRing _).toField
  have hfactor : Module.length B (B ⧸ extendedMaximalIdeal A B) = 1 := by
    have hsurj : Function.Surjective (algebraMap B (B ⧸ extendedMaximalIdeal A B)) := by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective
    have : IsSimpleModule B (B ⧸ extendedMaximalIdeal A B) :=
      (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective hsurj).2 inferInstance
    exact Module.length_eq_one B _
  have h := length_baseChange_eq_length_mul_length_quotient A B A
  rwa [(TensorProduct.AlgebraTensorModule.rid A B B).length_eq, hfactor, mul_one] at h

/-- **Stacks 0DR6.** Let `f : U ⟶ X` be a smooth morphism of locally Noetherian schemes, let
`T'` be an irreducible component of `U` and let `T` be the irreducible component of `X` obtained
as the closure of the image of `T'`. Then `T'` and `T` have the same multiplicity. -/
@[stacks 0DR6]
public theorem componentMultiplicity_id_eq_of_smooth
    {X U : Scheme.{u}} (f : U ⟶ X) [Smooth f] [IsLocallyNoetherian X]
    (T' : irreducibleComponents U) (T : irreducibleComponents X)
    (hT : closure (f.base '' (T' : Set U)) = (T : Set X)) :
    Stacks.Chow.componentMultiplicity (𝟙 U) (genericPoints.ofComponent T') =
      Stacks.Chow.componentMultiplicity (𝟙 X) (genericPoints.ofComponent T) := by
  rw [componentMultiplicity_eq_length_stalk, componentMultiplicity_eq_length_stalk,
    ← genericPoint_ofComponent_image_eq f T' T hT,
    length_stalk_eq_length_stalk_of_smooth f (genericPoints.ofComponent T')]

end Stacks.Chow

end
