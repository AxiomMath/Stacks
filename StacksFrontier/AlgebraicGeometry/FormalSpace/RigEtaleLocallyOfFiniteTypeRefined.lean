module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.TypeImplicationsRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterizationRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types

/-!
# Rig-étale morphisms of locally Noetherian formal algebraic spaces: refined forms

A rig-étale morphism of locally Noetherian formal algebraic spaces is locally of finite type.
This module states strengthened forms, under primed names, of declarations of
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocallyOfFiniteType`, together with further
results on the same subject.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inputs this library does not carry -/

/-- **A Noetherian affine formal algebraic space is countably indexed.** This is items (1),
(2), (3) and (5) of **Stacks 0AIK** composed, in
`AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_isNoetherian`.

Untagged: Stacks 0AKY is a list of definitions, whose covering set is the five predicates of
`StacksFrontier/AlgebraicGeometry/FormalSpace/Types.lean`; this is the implication between two of
them that the source records in passing. -/
theorem isCountablyIndexedOfIsNoetherian : IsCountablyIndexedOfIsNoetherian B S hS :=
  fun _ hU ↦ isCountablyIndexed_of_isNoetherian B S hS hU

/-! ### Stacks 0AQN -/

variable {B S hS}

/-- A locally Noetherian formal algebraic space over `S` is locally countably indexed: the
atlas of Noetherian affine formal algebraic spaces of Stacks 0AKY is an atlas of countably
indexed ones. -/
theorem isLocallyCountablyIndexed_of_isLocallyNoetherian' {X : FppfSheaf B S hS}
    (hX : IsLocallyNoetherian B S hS X) :
    IsLocallyCountablyIndexed B S hS X := by
  obtain ⟨hform, I, Xi, a, haff, hetale, hsurj, hnoeth⟩ := hX
  exact ⟨hform, I, Xi, a, haff, hetale, hsurj,
    fun i ↦ isCountablyIndexedOfIsNoetherian B S hS (Xi i) (hnoeth i)⟩

/-- **Stacks 0AQN.** A rig-étale morphism of locally Noetherian formal algebraic spaces over
`S` is locally of finite type.

Rig-étaleness of `f` is tested on the same affine representable étale squares as the
chart-tested condition (1) of Stacks 0ANW, so the affine case `h0GCV` turns it into that
condition for the property of being taut and topologically of finite type, and condition (4)
of Stacks 0ANW is that `f` is locally of finite type. -/
theorem isLocallyOfFiniteType_of_isRigEtale' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hf : IsRigEtale B S hS f)
    (h0GCV : TopologicalRing.IsTautTopologicallyOfFiniteTypeOfIsRigEtale.{u})
    (hchart : ChartPresentationIsNoetherianAdic B S hS) :
    IsLocallyOfFiniteType B S hS f := by
  have h0ANW := isLocallyOfFiniteType_tfae' f
    (isLocallyCountablyIndexed_of_isLocallyNoetherian' hX)
    (isLocallyCountablyIndexed_of_isLocallyNoetherian' hY)
  refine (h0ANW.out 1 4).mp ?_
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ _ _ hA D E eU eV g hg
  obtain ⟨hAnoeth, hAadic⟩ := hchart Y hY V b hV hb A D eV
  obtain ⟨hRnoeth, hRadic⟩ := hchart X hX U a hU ha R E eU
  have : IsNoetherianRing A := hAnoeth
  have : IsNoetherianRing R := hRnoeth
  exact h0GCV g.toRingHom hAadic hRadic
    (hf U V hU hV a b t ha.1 hb.1 ha.2 hb.2 hsq A R hAadic hRadic hA D E eU eV g hg)

end AlgebraicGeometry.FormalSpace

end
