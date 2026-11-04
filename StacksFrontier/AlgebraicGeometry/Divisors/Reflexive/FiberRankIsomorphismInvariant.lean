module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic

/-!
# The fibre rank of a module is an isomorphism invariant

The fibre rank of an `𝒪_X`-module at a point `x` is the dimension over the residue field at `x`
of the fibre `κ(x) ⊗_{𝒪_{X,x}} ℱ_x`.  Isomorphic modules have isomorphic stalks, so they have
isomorphic fibres and the same fibre rank.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfIso`: the stalk at `x` of an isomorphism
  of `𝒪_X`-modules, as a linear equivalence over the local ring at `x`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.fiberRank_eq_of_iso`: **the fibre rank is an isomorphism
  invariant**, at every point and with no finiteness hypothesis on the modules.

## Implementation notes

The stalk of a morphism of `𝒪_X`-modules, as a map linear over the local ring, is
`Stacks.SheafOfModules.FlatShortExact.stalkLinearMap`; its underlying map of abelian groups is
the image of the morphism under the additive stalk functor
`Stacks.SheafOfModules.FlatShortExact.stalkF`, so for an isomorphism it is bijective and the
linear map is a linear equivalence.  Base change along the residue map
(`LinearEquiv.baseChange`) turns that into a linear equivalence of fibres over the residue
field, whose source and target are by definition the modules whose dimensions the two fibre
ranks are.

No finiteness is needed: `AlgebraicGeometry.Scheme.Modules.fiberRank` is a `Module.finrank`,
which is defined for an arbitrary module, and a linear equivalence equates `Module.finrank`
unconditionally.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules.FlatShortExact (abStalk stalkModule stalkLinearMap stalkF)

variable {X : Scheme.{u}} {F G : X.Modules}

/-- **The stalk at `x` of an isomorphism of `𝒪_X`-modules, as a linear equivalence** over the
local ring at `x`.  The underlying map of abelian groups is the image of the isomorphism under
the additive stalk functor, hence bijective. -/
public def stalkLinearEquivOfIso (e : F ≅ G) (x : X) :
    letI := stalkModule (X := X.toRingedSpace) F x
    letI := stalkModule (X := X.toRingedSpace) G x
    ToType (F.presheaf.stalk x) ≃ₗ[ToType (X.presheaf.stalk x)] ToType (G.presheaf.stalk x) :=
  letI := stalkModule (X := X.toRingedSpace) F x
  letI := stalkModule (X := X.toRingedSpace) G x
  LinearEquiv.ofBijective (stalkLinearMap (X := X.toRingedSpace) e.hom x) <| by
    have h : (stalkLinearMap (X := X.toRingedSpace) e.hom x :
          abStalk (X := X.toRingedSpace) F x → abStalk (X := X.toRingedSpace) G x) =
        ((stalkF (X := X.toRingedSpace) x).mapIso e).addCommGroupIsoToAddEquiv := rfl
    rw [h]
    exact ((stalkF (X := X.toRingedSpace) x).mapIso e).addCommGroupIsoToAddEquiv.bijective

/-- **The fibre rank is an isomorphism invariant.**  The stalks of isomorphic modules are
linearly equivalent over the local ring, so their base changes to the residue field are linearly
equivalent over it, and the fibre rank is the dimension of that base change. -/
public theorem fiberRank_eq_of_iso (e : F ≅ G) (x : X) : fiberRank F x = fiberRank G x := by
  let := stalkModule (X := X.toRingedSpace) F x
  let := stalkModule (X := X.toRingedSpace) G x
  let : Algebra (ToType (X.presheaf.stalk x)) (X.residueField x) := (X.residue x).hom.toAlgebra
  exact (LinearEquiv.baseChange (ToType (X.presheaf.stalk x)) (X.residueField x)
    (ToType (F.presheaf.stalk x)) (ToType (G.presheaf.stalk x))
    (stalkLinearEquivOfIso e x)).finrank_eq

end AlgebraicGeometry.Scheme.Modules

end
