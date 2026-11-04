module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericBaseChange
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# The stalk-detection hypothesis of Tag 09N8

`Stacks.AlgebraicGeometry.OneDimensionalLocal.isZero_rightDerived_pushforward_of_isRetrocompact`
is [Stacks, Tag 09N8] stated from three hypotheses, one for each result the source cites that
was absent when it was proved. The third of the three,
`Stacks.AlgebraicGeometry.OneDimensionalLocal.PullbackFromSpecStalkDetectsStalk`, is
[Stacks, Tag 0098] specialized to `g = X.fromSpecStalk x`; this file discharges it from
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`.

The specialization is where the tensor product disappears. Tag 0098 gives
`(g^* M)_c ≅ 𝒪_{S, c} ⊗_{𝒪_{X, x}} M_x` for `c` the closed point of `S = Spec 𝒪_{X, x}`, and
`g.stalkMap c : 𝒪_{X, x} ⟶ 𝒪_{S, c}` is an isomorphism, so the tensor product is
`𝒪_{X, x} ⊗_{𝒪_{X, x}} M_x ≅ M_x`. Vanishing of `g^* M` therefore forces `M_x` to vanish,
which is the implication Tag 09N8 consumes.

## Main results

* `AlgebraicGeometry.isIso_stalkMap_fromSpecStalk_closedPoint` (in
  `StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericBaseChange`, imported): the map on
  stalks induced by `Spec 𝒪_{X, x} ⟶ X` at the closed point is an isomorphism.
* `Stacks.AlgebraicGeometry.OneDimensionalLocal.pullbackFromSpecStalkDetectsStalk`: the third
  hypothesis of `isZero_rightDerived_pushforward_of_isRetrocompact`, proved.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 09N8](https://stacks.math.columbia.edu/tag/09N8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AlgebraicGeometry.OneDimensionalLocal

/-- **The third hypothesis of [Stacks, Tag 09N8] holds.** If the pullback of `M` along
`X.fromSpecStalk x` vanishes then the stalk of `M` at `x` vanishes.

By [Stacks, Tag 0098] the stalk of the pullback at the closed point `c` of `Spec 𝒪_{X, x}` is
`𝒪_{Spec 𝒪_{X, x}, c} ⊗_{𝒪_{X, x}} M_x`; the stalk map at `c` is an isomorphism, so that
tensor product is `M_x` and the hypothesis of vanishing transports. -/
theorem pullbackFromSpecStalkDetectsStalk : PullbackFromSpecStalkDetectsStalk.{u} := by
  intro X x M hM
  classical
  set S := Spec (.of (X.presheaf.stalk x))
  set g := X.fromSpecStalk x
  let z : S := ⟨IsLocalRing.closedPoint (X.presheaf.stalk x),
    (IsLocalRing.closedPoint (X.presheaf.stalk x)).2⟩
  -- The underlying abelian sheaf of `g^* M` has vanishing stalk at `z`, for trivial reasons.
  have hNz : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} z).obj
      ((Scheme.Modules.toPresheaf S).obj ((Scheme.Modules.pullback g).obj M))) :=
    (TopCat.Presheaf.stalkFunctor Ab.{u} z).map_isZero
      ((Scheme.Modules.toPresheaf S).map_isZero hM)
  have hiso : IsIso (g.stalkMap z) := isIso_stalkMap_fromSpecStalk_closedPoint X x
  -- Tag 0098 for `g`, with the tensor product collapsed along the iso `g.stalkMap z`.
  let A := X.presheaf.stalk (g z)
  let B := S.presheaf.stalk z
  let : Algebra A B := (g.stalkMap z).hom.toAlgebra
  let Mpb := (RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom).obj M
  let Pstalk := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) Mpb.val.presheaf z
  let Mstalk := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf (g z)
  let : Module A Mstalk :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) M.val (g z)
  let : Module B Pstalk :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.presheaf) Mpb.val z
  let ePull := Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      g.toLRSHom.toShHom M z)
  let e : A ≃+* B := (asIso (g.stalkMap z)).commRingCatIsoToRingEquiv
  let eLin : B ≃ₗ[A] A := (AlgEquiv.ofRingEquiv (f := e) fun _ => rfl).symm.toLinearEquiv
  let eAll := ePull.toEquiv.trans
    ((TensorProduct.congr eLin (LinearEquiv.refl A Mstalk)).trans
      (TensorProduct.lid A Mstalk)).toEquiv
  have : Subsingleton Mstalk :=
    eAll.subsingleton_congr.mp (AddCommGrpCat.isZero_iff_subsingleton.mp hNz)
  exact (AddCommGrpCat.isZero_of_subsingleton Mstalk).of_iso
    (M.presheaf.stalkCongr (.of_eq (Scheme.fromSpecStalk_closedPoint (x := x)).symm))

end Stacks.AlgebraicGeometry.OneDimensionalLocal

end
