module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.FlatPullback
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksCore.Tactic.StacksAttribute

import all StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.FlatPullback

/-!
# Cohen–Macaulay pullback of a depth-two extension

A map of modules on a scheme is a *depth-two extension along `T`* when its target is coherent,
it is an isomorphism on stalks away from `T`, and the stalks of its target have depth at least
two at every point of `T`.  That property is preserved by pullback along a Cohen–Macaulay
morphism of Noetherian schemes, along the inverse image of the subset.

## Main results

* `AlgebraicGeometry.depthTwoExtension_pullback`: the pullback of a depth-two extension along a
  Cohen–Macaulay morphism of Noetherian schemes is a depth-two extension along the preimage of
  the subset.

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- The pullback of a depth-two extension along a Cohen–Macaulay morphism of Noetherian schemes
is a depth-two extension along the inverse image of the subset.

The hypothesis `hfib`, that the fibres of `f` are locally Noetherian, is the one under which
`AlgebraicGeometry.Scheme.Hom.IsCohenMacaulay` is stated; it follows from `[IsNoetherian Y]` by
`AlgebraicGeometry.isLocallyNoetherian_fiber`. -/
public theorem depthTwoExtension_pullback
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (T : Set X) (F G : X.Modules) (φ : F ⟶ G)
    (hφ : IsDepthTwoExtension T φ)
    (f : Y ⟶ X) (hfib : ∀ x : X, IsLocallyNoetherian (f.fiber x))
    (hcm : f.IsCohenMacaulay hfib) :
    IsDepthTwoExtension (f ⁻¹' T) ((Scheme.Modules.pullback f).map φ) := by
  have hGc : G.IsCoherent := hφ.1
  refine ⟨isCoherent_pullback f G, ?_, ?_⟩
  · intro y hy
    have hyT : f.base y ∉ T := by simpa using hy
    have hbij : Function.Bijective
        (stalkMapLinear (R := X.presheaf) F.val G.val φ.val (f.base y)) :=
      (ConcreteCategory.isIso_iff_bijective
        (SheafOfModules.stalkMap X.ringCatSheaf (f.base y) φ)).mp (hφ.2.1 (f.base y) hyT)
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (modulePullback_stalkMap_bijective f.toLRSHom.toShHom F G φ y hbij)
  · intro y hy
    let R := X.presheaf.stalk (f.base y)
    let S := Y.presheaf.stalk y
    let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base y)
    let N := TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pullback f).obj G).val.presheaf y
    let :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val (f.base y)
    let :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pullback f).obj G).val y
    let : Algebra R S := (f.stalkMap y).hom.toAlgebra
    have hyT : f.base y ∈ T := by simpa using hy
    have hdepth : 2 ≤ Module.depth R (IsLocalRing.maximalIdeal R) M := hφ.2.2 (f.base y) hyT
    have : G.IsFiniteType := IsCoherent.toIsFiniteType G
    have : Module.Finite R M := SheafOfModules.finite_stalk X.sheaf G (f.base y)
    have : IsLocalHom (algebraMap R S) := by
      rw [RingHom.algebraMap_toAlgebra]
      infer_instance
    have : Module.Flat R S := (hcm y).1
    obtain ⟨E, -⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      f.toLRSHom.toShHom G y
    have hdepthEq : Module.depth S (IsLocalRing.maximalIdeal S) N =
        Module.depth S (IsLocalRing.maximalIdeal S) (TensorProduct R S M) :=
      Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal S) E
    change 2 ≤ Module.depth S (IsLocalRing.maximalIdeal S) N
    rw [hdepthEq, Module.depth_tensorProduct_of_flat (R := R) (S := S) (M := M) (N := S)]
    exact le_trans hdepth (le_add_of_nonneg_right (by positivity))

end AlgebraicGeometry

end
