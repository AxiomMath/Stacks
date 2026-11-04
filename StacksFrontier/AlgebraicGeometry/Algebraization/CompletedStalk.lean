module

public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits

/-!
# The adic completion of a stalk and the formal stalk of a coherent adic system

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals on `X` and let `x` be a point
of `X`. Write `I_x ⊆ 𝒪_{X,x}` for the stalk of `I`. This file defines the `I`-adic completion

  `𝒪_{X,x}^∧ = lim 𝒪_{X,x}/Iⁿ𝒪_{X,x}`

of the local ring, the ideal `I𝒪_{X,x}^∧` it generates and, for a coherent `I`-adic system
`(ℱ_n)`, the inverse limit `ℱ_x^∧ = lim ℱ_{n,x}` of the stalks, regarded as a module over
`𝒪_{X,x}^∧`.

## Main definitions

* `Stacks.Algebraization.stalkModuleFunctor` — the stalk at `x`, as a functor from sheaves of
  modules on `X` to modules over `𝒪_{X,x}`.
* `Stacks.Algebraization.completedLocalRing` — the `I`-adic completion `𝒪_{X,x}^∧` of the local
  ring at `x`.
* `Stacks.Algebraization.completedLocalIdeal` — the ideal `I𝒪_{X,x}^∧` of `𝒪_{X,x}^∧`.
* `Stacks.Algebraization.formalStalk` — the inverse limit `ℱ_x^∧ = lim ℱ_{n,x}` of the stalks of
  a coherent adic system.
* `Stacks.Algebraization.completedStalk` — the `I`-adic completion of `formalStalk`, a module
  over `𝒪_{X,x}^∧`.

## Implementation notes

`AlgebraicGeometry.SheafOfModules.stalkFunctor` takes values in modules over the `RingCat`-valued
stalk of the structure sheaf; `stalkModuleFunctor` restricts scalars along
`SemilinearStalk.commStalkIso` to the `CommRingCat`-valued stalk `𝒪_{X,x}`.

Each `ℱ_{n,x}` is a module over `𝒪_{X,x}`, hence so is `formalStalk`; `completedStalk` is its
`I`-adic completion, a module over `𝒪_{X,x}^∧`. Since `ℱ_{n,x}` is annihilated by `I^{n+1}`, the
completion map `formalStalk ⟶ completedStalk` is an isomorphism (Stacks 0EJE).

The ideal `I𝒪_{X,x}^∧` is the image of `I_x` under the structure map to the completion.

## References

* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the paragraph
  introducing `𝒪_{X,y}^∧` and `ℱ_y^∧`.
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE), where the formal stalk
  is identified with its completion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Algebraization

/-- The stalk at `x` of a sheaf of modules on a scheme, as a functor to modules over the local
ring `𝒪_{X,x}`. -/
public def stalkModuleFunctor {X : Scheme.{u}} (x : X) :
    X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  SheafOfModules.stalkFunctor X.ringCatSheaf x ⋙
    ModuleCat.restrictScalars (SemilinearStalk.commStalkIso X.presheaf x).inv.hom

/-- The `I`-adic completion `𝒪_{X,x}^∧ = lim 𝒪_{X,x}/Iⁿ𝒪_{X,x}` of the local ring of `X`
at `x`. -/
public abbrev completedLocalRing {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :=
  AdicCompletion (IdealSheafData.stalk I x) (X.presheaf.stalk x)

/-- The ideal `I𝒪_{X,x}^∧` of the completed local ring, the image of the stalk `I_x` under the
structure map to the completion. -/
public abbrev completedLocalIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    Ideal (completedLocalRing I x) :=
  (IdealSheafData.stalk I x).map
    (algebraMap (X.presheaf.stalk x) (completedLocalRing I x))

/-- The inverse limit `ℱ_x^∧ = lim ℱ_{n,x}` of the stalks of a coherent adic system, as a
module over the local ring `𝒪_{X,x}`. -/
public abbrev formalStalk {X : Scheme.{u}} {I : X.IdealSheafData}
    (F : Stacks.Coherent.CoherentAdicSystems I) (x : X) :=
  (limit (F.obj ⋙ stalkModuleFunctor x) : ModuleCat.{u} (X.presheaf.stalk x))

/-- The formal stalk of a coherent adic system with its `𝒪_{X,x}^∧`-module structure, obtained
by `I`-adically completing `Stacks.Algebraization.formalStalk`. -/
public abbrev completedStalk {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : Stacks.Coherent.CoherentAdicSystems I) (x : X) :=
  AdicCompletion (IdealSheafData.stalk I x) (formalStalk F x)

end Stacks.Algebraization

end
