module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.Separated
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Limits.EventuallySeparatedOverBase

/-!
# Relative separatedness at a finite stage of an inverse limit

Let `D` be a directed inverse system of quasi-compact, quasi-separated schemes with affine
transition morphisms, let `S` be a quasi-separated scheme and let `t : D ⟶ S` be a cone of
morphisms to `S` from the stages of the system. If the induced morphism from the limit of `D`
to `S` is separated, then `t.app i` is already separated for every sufficiently late stage `i`.

## Main results

* `AlgebraicGeometry.eventually_isSeparated_of_isLimit`: the statement above, with the system,
  its limit cone and the morphism to `S` as separate arguments.

## Implementation notes

The content of the statement is `AlgebraicGeometry.eventually_isSeparated_app`, which takes the
descent data bundled as an `AlgebraicGeometry.DescentSituation`. The form here unbundles it and
supplies the situation's chosen index from `Nonempty I`.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe v u

/-- If the limit of a directed inverse system of quasi-compact, quasi-separated schemes with
affine transition morphisms is separated over a quasi-separated scheme `S`, then every
sufficiently late stage of the system is separated over `S`. -/
theorem eventually_isSeparated_of_isLimit
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [EssentiallySmall.{u} I]
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
    (c : Cone D) (hc : IsLimit c) (f : c.pt ⟶ S)
    (hf : c.π ≫ t = (Functor.const Iᵒᵖ).map f)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)] [IsSeparated f] :
    ∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsSeparated (t.app (Opposite.op i)) := by
  classical
  have h : ∀ j : Iᵒᵖ, c.π.app j ≫ t.app j = f := fun j ↦ by
    simpa using congrArg (fun α ↦ α.app j) hf
  refine eventually_isSeparated_app
    { system := D
      transition_affine := fun g ↦ inferInstance
      quasiCompact := fun _ ↦ inferInstance
      quasiSeparated := fun _ ↦ inferInstance
      limitCone := c
      isLimit := hc
      base := Classical.choice ‹Nonempty I› } t ?_
  simpa only [h] using (inferInstance : IsSeparated f)

end AlgebraicGeometry

end
