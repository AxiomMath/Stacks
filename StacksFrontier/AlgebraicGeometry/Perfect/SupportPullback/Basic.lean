module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.LocalTensor
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Support of the pullback of a module of finite type

The support of the pullback of a module of finite type along a morphism of schemes is the
inverse image of its support.

## Main results

* `SheafOfModules.supp_pullback` computes the support of a pullback.

## Implementation notes

Support is `SheafOfModules.supp`, read off the stalks of the underlying sheaf of abelian
groups, so the statement is checked one point at a time. The stalk of the pullback at `y` is
the base change of the stalk of the module at `f y` along the local homomorphism
`𝒪_{X, f y} → 𝒪_{Y, y}`, by
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` (Tag 0098), and that
base change is nonzero exactly when the original stalk is, by
`IsLocalRing.nontrivial_tensorProduct_of_isLocalHom`. Finiteness of the stalk over the stalk
of the structure sheaf, which that criterion needs, is `SheafOfModules.finite_stalk`.

Quasi-coherence is not used: finite type alone gives both the finiteness of the stalk and the
stalk formula for the pullback.

The stalk comparison is produced for the morphism of ringed spaces underlying `f`, whose base
map is a different spelling of `f.base`. The equivalence is therefore retyped at the spelling
of this statement by `let e : N ≃ₗ[S] _ := e₀`, so that the local-ring structures and the
module structure on the stalk are the ones instance search finds here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open scoped TensorProduct

universe u

namespace SheafOfModules

/-- **Stacks Project, Tag 056J.** The support of the pullback of a module of finite type
along a morphism of schemes is the inverse image of its support. -/
@[stacks 056J "pullback_support"]
theorem supp_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsFiniteType] :
    supp ((Scheme.Modules.pullback f).obj F) = f ⁻¹' supp F := by
  ext y
  rw [Set.mem_preimage, mem_supp_iff_nontrivial_stalk ((Scheme.Modules.pullback f).obj F) y,
    mem_supp_iff_nontrivial_stalk F (f y)]
  let R := X.presheaf.stalk (f.base y)
  let S := Y.presheaf.stalk y
  let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf (f.base y)
  let N := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    ((Scheme.Modules.pullback f).obj F).val.presheaf y
  let : Algebra R S := (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap R S) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  let : Module R M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      F.val (f.base y)
  have : Module.Finite R M := finite_stalk X.sheaf F (f.base y)
  let : Module S N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      ((Scheme.Modules.pullback f).obj F).val y
  obtain ⟨e₀, -⟩ := exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom F y
  let e : N ≃ₗ[S] TensorProduct R S M := e₀
  exact e.toEquiv.nontrivial_congr.trans IsLocalRing.nontrivial_tensorProduct_of_isLocalHom

end SheafOfModules

end
