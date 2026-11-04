module

public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Sheafify
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative

/-!
# The stalk of the sheaf of relative differentials of a morphism of schemes

**For a morphism of schemes `f : X ⟶ S` and a point `x` of `X`, the stalk at `x` of the sheaf of
relative differentials of `f` is the module of Kähler differentials of the stalk of the structural
map of `f` at `x`,** compatibly with universal differentials.

This is Stacks Tag 01V0 read at a point, for the relative differentials of a morphism of schemes:
the sheaf of relative differentials commutes with taking stalks.

## Main definitions

* `Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv`: the identification.

## Main results

* `Stacks.RelativeDifferentialStalk.relativeDifferentialsStalkLinearEquiv_germ_d`: the
  identification carries the germ of the universal relative differential of a local section of the
  structure sheaf to the universal differential of the germ of that section.

## Implementation notes

The base ring of the Kähler differentials is the stalk at `x` of the *inverse image*
`f⁻¹𝒪_S`, which is where the structural map
`AlgebraicGeometry.inverseImageStructureMap` of `f` lives.  The same identification over the
stalk `𝒪_{S,f x}` of the structure sheaf of `S`, that is with `Ω[𝒪_{X,x}⁄𝒪_{S,f x}]`, is
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.SheafOfModules PresheafOfModules

universe u

namespace Stacks.RelativeDifferentialStalk

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
  [DecidableEq (OrderDual (TopologicalSpace.OpenNhds x))]

/-- The stalk of the sheaf of relative differentials of a morphism of schemes is a module over the
stalk of the structure sheaf of the source.  This is the module structure of
`Mathlib.Algebra.Category.ModuleCat.Stalk`, recorded at the `relativeDifferentials` spelling:
instance search does not unfold `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and so does
not see it. -/
public noncomputable instance moduleStalkRelativeDifferentials :
    Module (ToType (X.sheaf.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf x)) :=
  inferInstanceAs (Module (ToType (X.sheaf.presheaf.stalk x))
    (ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (moduleOfDifferentials.{u, u, u} (inverseImageStructureMap f)).val.presheaf x)))

/-- **The stalk of the sheaf of relative differentials of a morphism of schemes is the module of
Kähler differentials of the stalk of its structural map.** -/
public noncomputable def relativeDifferentialsStalkLinearEquiv :
    letI := algebraStalk (inverseImageStructureMap f).hom x
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (Scheme.Hom.relativeDifferentials f).val.presheaf x)
      ≃ₗ[ToType (X.sheaf.presheaf.stalk x)]
      KaehlerDifferential
        (ToType (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.stalk x))
        (ToType (X.sheaf.presheaf.stalk x)) := by
  letI := algebraStalk (inverseImageStructureMap f).hom x
  exact stalkModuleOfDifferentialsKaehlerLinearEquiv (inverseImageStructureMap f) x

/-- **The identification carries universal differentials to universal differentials.** -/
public theorem relativeDifferentialsStalkLinearEquiv_germ_d
    (i : OrderDual (TopologicalSpace.OpenNhds x)) (a : nhdRing X.sheaf.presheaf i) :
    letI := algebraStalk (inverseImageStructureMap f).hom x
    relativeDifferentialsStalkLinearEquiv f x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (Scheme.Hom.relativeDifferentials f).val.presheaf (nhdOpen i) x (mem_nhdOpen i)
          ((Scheme.Hom.universalRelativeDerivation f).d a)) =
      KaehlerDifferential.D
        (ToType (((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.stalk x))
        (ToType (X.sheaf.presheaf.stalk x))
        (X.sheaf.presheaf.germ (nhdOpen i) x (mem_nhdOpen i) a) :=
  stalkModuleOfDifferentialsKaehlerLinearEquiv_germ_d (inverseImageStructureMap f) x i a

end Stacks.RelativeDifferentialStalk

end
