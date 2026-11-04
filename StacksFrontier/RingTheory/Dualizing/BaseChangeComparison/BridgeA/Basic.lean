module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction

/-!
# Derived coextension after restriction is internal Hom out of the algebra

Let `f : R → A` be a homomorphism of commutative rings. Restriction of scalars along `f`
carries the derived coextension `RHom_R(A, -) : D(R) ⥤ D(A)` of Stacks 0A70 to a functor
`D(R) ⥤ D(R)`, and the resulting functor is the derived internal Hom `RHom_R(A, -)` out of the
algebra `A`, viewed as a degree-zero complex of `R`-modules. This is the identification the
proof of Stacks 0E2A needs in order to recognize the restriction of the base-change morphism of
Stacks 0E29 as the derived-Hom base-change morphism of Stacks 0E1X: both sides of Stacks 0E2A
are written in the internal-Hom vocabulary of Stacks 0E1W, while the morphism of Stacks 0E29 is
built from derived coextension.

The identification is a statement about right adjoints. Derived restriction of scalars is left
adjoint to derived coextension (Stacks 0A70) and right adjoint to derived extension of scalars
(Stacks 0GMT), so the composite `RHom_R(A, -) ∘ Res` is right adjoint to the composite
`Res ∘ (- ⊗ᴸ_R A)`. The derived internal Hom out of a fixed object is right adjoint to the
derived tensor product with that object, by the tensor--Hom adjunction of Stacks 0A63. Hence the
two functors are isomorphic as soon as their left adjoints are, and the isomorphism of the left
adjoints is exactly the statement that restricting derived extension of scalars is tensoring
with the algebra. The two statements are therefore *equivalent*, not merely related: both
implications are recorded below, and the tensor-side statement is proved at the same universes in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Tensor`, which discharges the
hypothesis of `Dualizing.derivedHomRestrictScalarsInternalHomIso`.

## Main definitions

* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorAt`, `.homAt` — the two partial applications
  of the tensor and internal-Hom bifunctors of a derived tensor--Hom adjunction at a fixed
  object.
* `Dualizing.derivedAlgebraSingle` — the algebra `A`, viewed as a degree-zero complex of
  `R`-modules in the module universe used by Stacks 0E2A.
* `Dualizing.derivedExtendRestrictScalarsTensorFunctor` — the derived tensor product with
  `Dualizing.derivedAlgebraSingle`, as an endofunctor of `D(R)`.
* `Dualizing.derivedCoextendRestrictScalarsFunctor`,
  `Dualizing.derivedInternalHomAlgebraFunctor` — the two endofunctors of `D(R)` that
  `Dualizing.derivedHomRestrictScalarsInternalHomIso` identifies.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomAdjunctionAt` — the tensor--Hom
  adjunction of Stacks 0A63 as an honest adjunction of endofunctors at a fixed object.
* `Dualizing.derivedCoextendRestrictScalars_adj` — `Res ∘ (- ⊗ᴸ_R A)` is left adjoint to
  `Res ∘ RHom_R(A, -)`, for any model of derived extension of scalars.
* `Dualizing.derivedHomRestrictScalarsInternalHomIso` — restriction of derived coextension is
  internal Hom out of the algebra, given the identification of the left adjoints.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_of_internalHomIso` — the converse: the
  identification of the left adjoints follows from the identification of the right adjoints.

## Implementation notes

The three universes of the two rings and of the module size are independent, as they are in
`Dualizing.derivedHomBaseChange` and in `Dualizing.derivedBaseChangeAlgebraIso`; the algebra
enters as `ULift A`, restricted along `f`, which is the spelling
`Dualizing.derivedBaseChangeAlgebraIso` and `MateReduction` use, so the object produced here is
literally the first argument of the morphism of Stacks 0E1X there.

Derived extension of scalars is taken as an argument together with the comparison morphism
exhibiting its universal property, exactly as in `Dualizing.derivedHomBaseChange`, so nothing
here depends on a choice of model. The internal-Hom bifunctor is named through
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, whose `hom` field is
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom` on the nose by
`Dualizing.derivedHomAdjunctionOverRing_hom_eq`, so the statements below are statements about
the bifunctor of Stacks 0E1W.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings

universe uR uA v w

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

variable {R : Type uR} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)

/-- The derived tensor product with a fixed object, as an endofunctor of `D(R)`. -/
noncomputable def tensorAt (L : DerivedCategory (ModuleCat.{v} R)) :
    DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R) :=
  (Functor.curry.obj d.tensor).flip.obj L

/-- The derived internal Hom out of a fixed object, as an endofunctor of `D(R)`. -/
noncomputable def homAt (L : DerivedCategory (ModuleCat.{v} R)) :
    DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R) :=
  (Functor.curry.obj d.hom).obj (Opposite.op L)

/-- **Stacks 0A63** as an adjunction. The derived tensor product with a fixed object is left
adjoint to the derived internal Hom out of that object; the unit and counit are those produced
by the Hom equivalence of the tensor--Hom adjunction, so no choice intervenes. -/
noncomputable def tensorHomAdjunctionAt (L : DerivedCategory (ModuleCat.{v} R)) :
    d.tensorAt L ⊣ d.homAt L := by
  refine Adjunction.mkOfHomEquiv
    { homEquiv := fun K M ↦ (d.homEquiv K L M).symm.toEquiv
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro X' X Y g a
    exact d.homEquiv_naturality_left g a
  · intro X Y Y' a g
    refine (Equiv.symm_apply_eq _).2 ?_
    have ha : d.homEquiv X L Y ((d.homEquiv X L Y).symm a) = a :=
      (d.homEquiv X L Y).apply_symm_apply _
    have h := d.homEquiv_naturality_right g ((d.homEquiv X L Y).symm a)
    rw [ha] at h
    exact h.symm

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

/-- Extension of scalars along a bare ring homomorphism is additive. Mathlib derives additivity
from an algebra structure, which a ring homomorphism does not carry, so the algebra structure is
installed locally. -/
local instance extendScalarsAdditiveOfRingHom {S : Type uR} {T : Type uA} [CommRing S]
    [CommRing T] (f : S →+* T) : (ModuleCat.extendScalars.{uR, uA, v} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  ext x
  change (1 : T) ⊗ₜ[S,f] ((a + b) x) =
    (1 : T) ⊗ₜ[S,f] a x + (1 : T) ⊗ₜ[S,f] b x
  rw [show (a + b : X ⟶ Y) x = a x + b x by rfl, TensorProduct.tmul_add]

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- The algebra `A`, viewed as a degree-zero complex of `R`-modules. The carrier is the universe
lift of `A`, so that the module universe may be chosen independently of the two ring
universes. -/
noncomputable def derivedAlgebraSingle : DerivedCategory (ModuleCat.{max v uR uA} R) :=
  (DerivedCategory.singleFunctor (ModuleCat.{max v uR uA} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max v uR uA} A)))

/-- Restriction of scalars along `f`, applied to derived coextension of scalars: the functor
`K ↦ RHom_R(A, K)` of Stacks 0A70, read in `D(R)`. -/
noncomputable def derivedCoextendRestrictScalarsFunctor :
    DerivedCategory (ModuleCat.{max v uR uA} R) ⥤ DerivedCategory (ModuleCat.{max v uR uA} R) :=
  derivedHom.{uR, v, uA} f ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory

/-- The derived internal Hom out of the algebra, in the vocabulary of Stacks 0E1W. -/
noncomputable def derivedInternalHomAlgebraFunctor :
    DerivedCategory (ModuleCat.{max v uR uA} R) ⥤ DerivedCategory (ModuleCat.{max v uR uA} R) :=
  (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1}
      R).homAt
    (derivedAlgebraSingle.{uR, uA, v} f)

/-- The derived tensor product with the algebra, in the vocabulary of Stacks 0A63. -/
noncomputable def derivedExtendRestrictScalarsTensorFunctor :
    DerivedCategory (ModuleCat.{max v uR uA} R) ⥤ DerivedCategory (ModuleCat.{max v uR uA} R) :=
  (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1}
      R).tensorAt
    (derivedAlgebraSingle.{uR, uA, v} f)

/-- The internal-Hom endofunctor of `Dualizing.derivedInternalHomAlgebraFunctor` is the partial
application of the bifunctor `Stacks.DerivedHom.ScalarTransportedInternalHom.hom` with which Stacks
  0E1W and
Stacks 0E1X are stated. -/
theorem derivedInternalHomAlgebraFunctor_obj
    (K : DerivedCategory (ModuleCat.{max v uR uA} R)) :
    (derivedInternalHomAlgebraFunctor.{uR, uA, v} f).obj K =
      (Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max v uR uA} R).obj
        (Opposite.op (derivedAlgebraSingle.{uR, uA, v} f), K) :=
  rfl

/-- **Stacks 0GMT and Stacks 0A70, composed.** Restricting derived extension of scalars is left
adjoint to restricting derived coextension of scalars: derived restriction of scalars is right
adjoint to the former and left adjoint to the latter, and composing the two adjunctions cancels
it. -/
noncomputable def derivedCoextendRestrictScalars_adj
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))] :
    F ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory ⊣
      derivedCoextendRestrictScalarsFunctor.{uR, uA, v} f :=
  (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, v}
      f F comparison).comp
    (derivedHomAdjunction.{uR, uA, v} f)

/-- **The bridge of Stacks 0E2A.** Restriction of scalars along `f : R → A`, applied to the
derived coextension `RHom_R(A, -)` of Stacks 0A70, is the derived internal Hom out of the
algebra `A` viewed as a degree-zero complex of `R`-modules.

The hypothesis is the corresponding statement for the left adjoints: restricting derived
extension of scalars is tensoring with the algebra. Given it, the identification is uniqueness
of right adjoints, with no further input. -/
noncomputable def derivedHomRestrictScalarsInternalHomIso
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (tensorIso : F ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory ≅
      derivedExtendRestrictScalarsTensorFunctor.{uR, uA, v} f) :
    derivedCoextendRestrictScalarsFunctor.{uR, uA, v} f ≅
      derivedInternalHomAlgebraFunctor.{uR, uA, v} f :=
  Adjunction.rightAdjointUniq
    (derivedCoextendRestrictScalars_adj.{uR, uA, v} f F comparison)
    (((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1}
        R).tensorHomAdjunctionAt
      (derivedAlgebraSingle.{uR, uA, v} f)).ofNatIsoLeft tensorIso.symm)

/-- The converse of `Dualizing.derivedHomRestrictScalarsInternalHomIso`: identifying
restriction of derived coextension with internal Hom out of the algebra identifies the left
adjoints, that is, identifies restriction of derived extension of scalars with tensoring by the
algebra. Together with `Dualizing.derivedHomRestrictScalarsInternalHomIso` this records that the
Hom-side and the tensor-side identifications are equivalent, so either may be taken as the
primitive one. -/
noncomputable def derivedExtendRestrictScalarsTensorIso_of_internalHomIso
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (homIso : derivedCoextendRestrictScalarsFunctor.{uR, uA, v} f ≅
      derivedInternalHomAlgebraFunctor.{uR, uA, v} f) :
    F ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory ≅
      derivedExtendRestrictScalarsTensorFunctor.{uR, uA, v} f :=
  Adjunction.leftAdjointUniq
    ((derivedCoextendRestrictScalars_adj.{uR, uA, v} f F comparison).ofNatIsoRight homIso)
    (((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1}
        R).tensorHomAdjunctionAt
      (derivedAlgebraSingle.{uR, uA, v} f)).ofNatIsoRight
        (Iso.refl (derivedInternalHomAlgebraFunctor.{uR, uA, v} f)))

end Dualizing

end
