module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensor

/-!
# The two stalk rings of a scheme at a point, and their comparison

A scheme `X` has two stalk rings at a point `x`, and they are not the same type.  One is
`X.presheaf.stalk x`, the filtered colimit of `𝒪_X` over the neighbourhoods of `x` taken in
`CommRingCat`; this is the ring Mathlib's `AlgebraicGeometry.Scheme.residueField` and the whole
local-ring API are stated over.  The other is the colimit taken in `RingCat`, after composing
`𝒪_X` with `forget₂ CommRingCat RingCat`; this is the ring the sheaf-of-modules stalk functor
`AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x` takes its modules over, and the
one the derived tensor product of `Stacks.SheafOfModules.DerivedTensorStalk` is formed relative
to.  Write `Λ x` for the second ring.

This file makes `Λ x` usable: it carries a commutative ring structure, it is a local ring, it is
Noetherian when `X` is locally Noetherian, and it is canonically isomorphic as a ring to
`X.presheaf.stalk x`, compatibly with residue fields.

## Main results

* `StacksDraft.StalkRingComparison.stalkRing`: the `RingCat`-valued stalk of the structure sheaf
  of a scheme, in the spelling the sheaf-of-modules machinery uses.
* `StacksDraft.StalkRingComparison.commRing_stalkRing`: `Λ x` is a commutative ring.
* `StacksDraft.StalkRingComparison.stalkRingEquiv`: the canonical ring isomorphism
  `Λ x ≃+* 𝒪_{X,x}`, with `stalkRingCatIso` and `stalkCommRingCatIso` its categorical forms.
* `StacksDraft.StalkRingComparison.isLocalRing_stalkRing` and
  `StacksDraft.StalkRingComparison.isNoetherianRing_stalkRing`: `Λ x` is a local ring, and is
  Noetherian as soon as `X` is locally Noetherian.
* `StacksDraft.StalkRingComparison.residueFieldStalkRingEquiv`: the residue field of the maximal
  ideal of `Λ x` is the residue field `κ(x)` of the scheme at `x`.
* `StacksDraft.StalkRingComparison.residueFieldMaximalIdealEquiv`: for any local ring `R`, the
  residue field of the maximal ideal of `R` regarded as a prime is the residue field of `R`.
* `StacksDraft.StalkRingComparison.stalkRing_eq_ringCatSheaf`: the two scheme-level spellings of
  the sheaf of rings give the same stalk, so the instances above serve both.

## Implementation notes

The commutativity of the `RingCat`-valued stalk is not new here: it is
`StacksDraft.StalkTensor.commRing_stalk`, transported from the `CommRingCat`-valued stalk along
`SemilinearStalk.commStalkRingEquiv`; here it is found by instance synthesis for a scheme.
`StacksDraft.StalkTensor.commRing_stalk_ringSheaf` is keyed on a sheaf of rings written
as `CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat`, whereas a scheme offers
`X.sheaf : TopCat.Sheaf CommRingCat X`; since `TopCat.Sheaf` is a plain `def`, unification at
reducible transparency will not cross between the two, and the instance does not fire.  The
instances below are therefore stated with a `Scheme` binder, so that the sheaf argument is already
in the scheme's own spelling and no unfolding is asked of instance search.  Where a bare instance
still cannot be keyed, `commRingStalkRing` repeats the same term as an `@[instance_reducible] def`,
the idiom of `StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafSpelling`, so that it can be
supplied by hand with `letI` at a crossing point.

`Λ x` is spelled out in full in every instance rather than through the `stalkRing` abbreviation,
so that the discrimination keys are exactly those of the spelling the sheaf-of-modules and
derived tensor machinery produces. The scheme's other spelling of the same sheaf of rings,
`X.ringCatSheaf`, needs no separate instance: it gives the same stalk by
`stalkRing_eq_ringCatSheaf`, and both spellings are reducible abbreviations of it, so the
instances fire through either — as `mul_comm_stalkRing_ringCatSheaf` and
`fg_maximalIdeal_stalkRing` record.

Noetherianness is stated under `AlgebraicGeometry.IsLocallyNoetherian`, which is what Mathlib's
instance on `X.presheaf.stalk x` needs; `AlgebraicGeometry.IsNoetherian` extends it, so a
Noetherian scheme is covered.

## References

* `StacksFrontier.Topology.Sheaves.Modules.StalkTensor`, for the commutativity of the
  `RingCat`-valued stalk and for why the two spellings of the sheaf of rings do not unify.
* `Mathlib.AlgebraicGeometry.ResidueField`, for `AlgebraicGeometry.Scheme.residueField`.
* `Mathlib.AlgebraicGeometry.Noetherian`, for the Noetherianness of the stalks of a locally
  Noetherian scheme.
* [The Stacks Project, Lemma 17.16.1 (01CB)](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace StacksDraft.StalkRingComparison

/-- For a local ring `R`, the residue field of `R` at its maximal ideal regarded as a prime —
that is, the residue field of the localization of `R` at that prime — is the residue field of `R`
itself, the localization being redundant. -/
public def residueFieldMaximalIdealEquiv (R : Type u) [CommRing R] [IsLocalRing R] :
    (IsLocalRing.maximalIdeal R).ResidueField ≃+* IsLocalRing.ResidueField R :=
  IsLocalRing.ResidueField.mapEquiv
    (IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
        (S := Localization.AtPrime (IsLocalRing.maximalIdeal R))
        fun _ ha => IsLocalRing.notMem_maximalIdeal.mp ha).toRingEquiv.symm

variable (X : Scheme.{u}) (x : X)

/-- The stalk at `x` of the structure sheaf of a scheme `X`, as a colimit in `RingCat`: this is
the ring over which `AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x` and the
derived tensor product of stalks are formed, and it is a different type from the `CommRingCat`
colimit `X.presheaf.stalk x`. -/
public abbrev stalkRing : RingCat.{u} :=
  TopCat.Presheaf.stalk (C := RingCat.{u})
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x

/-- The `RingCat`-valued stalk of the structure sheaf of a scheme is a commutative ring. -/
public instance commRing_stalkRing :
    CommRing ((TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x : RingCat.{u}) : Type u) :=
  StacksDraft.StalkTensor.commRing_stalk X.presheaf x

/-- The commutative ring structure of `commRing_stalkRing` as a term, usable with `letI` where the
sheaf of rings is written in a spelling instance search cannot key on. -/
@[instance_reducible]
public def commRingStalkRing :
    CommRing ((TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x : RingCat.{u}) : Type u) :=
  StacksDraft.StalkTensor.commRing_stalk X.presheaf x

/-- The two scheme-level spellings of the sheaf of rings, `X.ringCatSheaf` and
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, give the same `RingCat`-valued stalk. -/
public theorem stalkRing_eq_ringCatSheaf :
    stalkRing X x =
      TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x :=
  rfl

/-- Multiplication on the `RingCat`-valued stalk of the structure sheaf of a scheme is
commutative, in the `stalkRing` spelling of that stalk. -/
public theorem mul_comm_stalkRing (a b : (stalkRing X x : Type u)) : a * b = b * a :=
  mul_comm a b

/-- Multiplication on the `RingCat`-valued stalk of the structure sheaf of a scheme is
commutative, in the `X.ringCatSheaf` spelling of the underlying sheaf of rings. -/
public theorem mul_comm_stalkRing_ringCatSheaf
    (a b : ((TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x
      : RingCat.{u}) : Type u)) : a * b = b * a :=
  mul_comm_stalkRing X x a b

/-- The `RingCat`-valued stalk of the structure sheaf of a scheme, packaged as an object of
`CommRingCat` through `commRing_stalkRing`. -/
public abbrev stalkCommRingCat : CommRingCat.{u} :=
  CommRingCat.of ((TopCat.Presheaf.stalk (C := RingCat.{u})
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x : RingCat.{u}) : Type u)

/-- **The comparison of the two stalk rings.**  The `RingCat`-valued stalk of the structure sheaf
at `x` is isomorphic as a ring to the `CommRingCat`-valued stalk `𝒪_{X,x}`, the isomorphism being
the canonical comparison of colimits across `forget₂ CommRingCat RingCat`. -/
public def stalkRingEquiv :
    ((TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x : RingCat.{u}) : Type u)
      ≃+* (X.presheaf.stalk x : Type u) :=
  SemilinearStalk.commStalkRingEquiv X.presheaf x

/-- `stalkRingEquiv` on germs: the comparison isomorphism sends the germ of a section computed in
`RingCat` to its germ computed in `CommRingCat`. -/
public theorem stalkRingEquiv_germ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    stalkRingEquiv X x (TopCat.Presheaf.germ (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj U x hx r)
      = X.presheaf.germ U x hx r :=
  SemilinearStalk.commStalkRingEquiv_germ X.presheaf x U hx r

/-- `stalkRingEquiv` as an isomorphism in `RingCat`. -/
public def stalkRingCatIso :
    TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x ≅
      (forget₂ CommRingCat.{u} RingCat.{u}).obj (X.presheaf.stalk x) :=
  SemilinearStalk.commStalkIso X.presheaf x

/-- `stalkRingEquiv` as an isomorphism in `CommRingCat`, using the commutative ring structure of
`commRing_stalkRing` on the `RingCat`-valued stalk. -/
public def stalkCommRingCatIso : stalkCommRingCat X x ≅ X.presheaf.stalk x :=
  (stalkRingEquiv X x).toCommRingCatIso

/-- The `RingCat`-valued stalk of the structure sheaf of a scheme at `x` is a local ring. -/
public instance isLocalRing_stalkRing :
    IsLocalRing ((TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x : RingCat.{u}) : Type u) :=
  (stalkRingEquiv X x).symm.isLocalRing

/-- On a locally Noetherian scheme the `RingCat`-valued stalk of the structure sheaf at `x` is a
Noetherian ring. -/
public instance isNoetherianRing_stalkRing [IsLocallyNoetherian X] :
    IsNoetherianRing ((TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x : RingCat.{u}) : Type u) :=
  isNoetherianRing_of_ringEquiv _ (stalkRingEquiv X x).symm

/-- On a locally Noetherian scheme the maximal ideal of the `RingCat`-valued stalk of the
structure sheaf at `x` is finitely generated, in the `X.ringCatSheaf` spelling of the underlying
sheaf of rings. -/
public theorem fg_maximalIdeal_stalkRing [IsLocallyNoetherian X] :
    letI : CommRing ((TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x
      : RingCat.{u}) : Type u) := commRingStalkRing X x
    letI : IsLocalRing ((TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x
      : RingCat.{u}) : Type u) := isLocalRing_stalkRing X x
    (IsLocalRing.maximalIdeal ((TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x
      : RingCat.{u}) : Type u)).FG := by
  let : CommRing ((TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x
      : RingCat.{u}) : Type u) := commRingStalkRing X x
  let : IsLocalRing ((TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x
      : RingCat.{u}) : Type u) := isLocalRing_stalkRing X x
  let : IsNoetherianRing ((TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x
      : RingCat.{u}) : Type u) := isNoetherianRing_stalkRing X x
  exact IsNoetherian.noetherian _

/-- **The residue fields agree.**  The residue field of the maximal ideal of the `RingCat`-valued
stalk at `x` is the residue field `κ(x)` of the scheme at `x`, through `stalkRingEquiv`. -/
public def residueFieldStalkRingEquiv :
    (IsLocalRing.maximalIdeal
        ((TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj x
            : RingCat.{u}) : Type u)).ResidueField ≃+* (X.residueField x : Type u) :=
  (residueFieldMaximalIdealEquiv _).trans
    (IsLocalRing.ResidueField.mapEquiv (stalkRingEquiv X x))

end StacksDraft.StalkRingComparison

end
