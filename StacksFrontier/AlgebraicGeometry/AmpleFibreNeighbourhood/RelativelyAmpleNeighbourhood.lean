module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.FibreSectionFamily
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.FibreSectionLift
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.NeighbourhoodAssembly

/-!
# Stacks Tag 0D2N: an invertible module ample on one fibre is relatively ample nearby

Let `f : X ⟶ Y` be a proper morphism of schemes with `Y` Noetherian, let `ℒ` be an invertible
`𝒪_X`-module and let `y ∈ Y` be a point at which the restriction `ℒ_y` is ample on the fibre
`X_y`.  Then `y` has an open neighbourhood `V ⊂ Y` such that `ℒ|_{f⁻¹V}` is ample relative to
`f⁻¹V / V`.

This is [Stacks, Tag 0D2N], and this file registers it.

## Main results

* `Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre`, carrying
  `@[stacks 0D2N]`.

## The route, in one paragraph

The proof is the source's.  Tag 01VS on the fibre produces, for every large `d`, finitely many
sections of `ℒ_y ^⊗ d` generating it whose attached morphism `X_y ⟶ ℙʳ_{κ(y)}` is an immersion
(`exists_generatesStalks_isImmersion_toProjectiveSpaceOver_of_isAmple`, in the namespace
`Stacks.AmpleFibreNeighbourhood`).
Assertion (B) of [Stacks, Tag 0D2M] lifts them to sections over `f ⁻¹ᵁ U` for a neighbourhood `U`
of `y` — that is
`Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_fiberι_eq`, which reduces a general
Noetherian base to `Spec 𝒪_{Y, y}` by flat base change and reads the resulting section of
`ℒ ^⊗ d` on `X ×_Y Spec 𝒪_{Y, y}` back on a neighbourhood;
`Stacks.AmpleFibreNeighbourhood.exists_mem_forall_pullbackSection_fiberι_eq` makes one
neighbourhood serve the whole family.  Shrinking `U` so that the lifted sections generate
everywhere over the preimage, the morphism they attach to `ℙʳ` is finite over a neighbourhood of
the fibre, so `ℒ ^⊗ d` is relatively ample there and `ℒ` is too; that half is
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_exists_lift`.

## References

* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Ample
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.AmpleFibreNeighbourhood

/-- **Stacks Project, Tag 0D2N.**  Let `f : X ⟶ Y` be a proper morphism of schemes with `Y`
Noetherian, let `ℒ` be an invertible `𝒪_X`-module and let `y` be a point of `Y` such that `ℒ_y`
is ample on the fibre `X_y`.  Then there is an open neighbourhood `V` of `y` such that
`ℒ|_{f⁻¹V}` is ample relative to `f⁻¹V / V`.

Invertibility of `ℒ_y` is not a hypothesis: it is an instance, the pullback of an invertible
module being invertible (`Stacks.InvertiblePullback.isInvertibleModule_pullback`).

The two halves are
`Stacks.AmpleFibreNeighbourhood.exists_mem_pullbackSection_fiberι_eq` — the lifting of sections
from the fibre, which is where [Stacks, Tag 0D2M] and the reduction to `Spec 𝒪_{Y, y}` live — and
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_exists_lift`, which is the rest
of the source's argument. -/
@[stacks 0D2N]
theorem exists_mem_isRelativelyAmple_of_isAmple_fibre {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsNoetherian S] (L : X.Modules) [IsInvertibleModule X L] (y : S)
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    ∃ V : S.Opens, y ∈ V ∧
      Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  refine exists_mem_isRelativelyAmple_of_exists_lift f L y hL ?_
  obtain ⟨d₀, hd₀⟩ := exists_mem_pullbackSection_fiberι_eq f L y hL
  exact ⟨d₀, fun d hd k t => exists_mem_forall_pullbackSection_fiberι_eq f _ y t
    fun i => hd₀ d hd (t i)⟩

end Stacks.AmpleFibreNeighbourhood

end
