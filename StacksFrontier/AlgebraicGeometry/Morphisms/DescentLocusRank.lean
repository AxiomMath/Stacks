module

public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.Idempotents
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The fibres of a family with `𝒪_T ≅ p_*𝒪_{X_T}` are connected

Let `f : X ⟶ S` be flat and locally of finite presentation, with `𝒪_T ⟶ p_*𝒪_{X_T}` an
isomorphism for the base change `p : X_T ⟶ T` along every point `T = Spec κ(s) ⟶ S`. Then the
fibres of `f` are nonempty and connected: "the fibres `X_s` of `f` are connected by our assumption
that `H⁰(X_s, 𝒪_{X_s}) = κ(s)`" ([Stacks, Tag 0BDP], first step of the proof).

## Main results

* `AlgebraicGeometry.bijective_appTop_of_isIso_structureSheafHom`: `𝒪_Y ≅ g_*𝒪_X` makes
  `Γ(Y, 𝒪) ⟶ Γ(X, 𝒪)` bijective.
* `AlgebraicGeometry.connectedSpace_fiber_of_isIso_structureSheafHom`: the fibres are connected.
* `AlgebraicGeometry.isConnected_preimage_singleton_of_isIso_structureSheafHom`: the preimage of
  a point is connected.

## References

* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- If `𝒪_Y ⟶ g_*𝒪_X` is an isomorphism, then so is `Γ(Y, 𝒪) ⟶ Γ(X, 𝒪)`. -/
theorem bijective_appTop_of_isIso_structureSheafHom {X Y : Scheme.{u}} (g : X ⟶ Y)
    (h : IsIso (structureSheafHom g.toLRSHom.toShHom)) : Function.Bijective g.appTop.hom := by
  have : IsIso ((sheafToPresheaf _ _).map (structureSheafHom g.toLRSHom.toShHom)) :=
    inferInstance
  exact ConcreteCategory.bijective_of_isIso
    (((sheafToPresheaf _ _).map (structureSheafHom g.toLRSHom.toShHom)).app (op ⊤))

/-- **The fibres are connected** when `κ(s) ⟶ Γ(X_s, 𝒪)` is bijective, as it is when
`𝒪 ⟶ p_*𝒪_{X_s}` is an isomorphism for the base change `p : X_s ⟶ Spec κ(s)`: a disconnected
`X_s` would carry a nontrivial idempotent function, and a field has none. -/
theorem connectedSpace_fiber_of_isIso_structureSheafHom {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (h : IsIso (structureSheafHom (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom)) :
    ConnectedSpace (f.fiber s) :=
  Stacks.AmpleSectionConnected.connectedSpace_of_bijective_appTop
    (pullback.snd f (S.fromSpecResidueField s))
    (bijective_appTop_of_isIso_structureSheafHom _ h)

/-- The fibre of `f` over `s` is connected and nonempty, as a subset of `X`. -/
theorem isConnected_preimage_singleton_of_isIso_structureSheafHom {X S : Scheme.{u}}
    (f : X ⟶ S) (s : S)
    (h : IsIso (structureSheafHom (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom)) :
    _root_.IsConnected (f ⁻¹' {s}) := by
  have := connectedSpace_fiber_of_isIso_structureSheafHom f s h
  have : ConnectedSpace (f ⁻¹' {s}) :=
    (f.fiberHomeo s).surjective.connectedSpace (f.fiberHomeo s).continuous
  exact isConnected_iff_connectedSpace.2 inferInstance

end AlgebraicGeometry

end
