module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningInjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningInjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningInjectiveTensorUnit
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackFibre

/-!
# Flattening a map: a flat morphism whose image carries the relative assassin is separating

Let `S` be a scheme, let `g : X' ⟶ X` be a flat morphism of schemes over `S` with `X` locally of
finite type over `S`, and let `F` be a finite type quasi-coherent `𝒪_X`-module which is flat
over `S`. If `Ass_{X/S}(F) ⊆ g(X')` then the canonical map `F ⟶ g_* g^* F` is injective, and
remains injective after any base change on `S`.

## Main results

* `AlgebraicGeometry.mono_pullbackPushforwardUnit_of_relativeAssassin_subset_range`:
  **Stacks tag 05PD**, the injectivity.
* `AlgebraicGeometry.mono_baseChange_pullbackPushforwardUnit_of_relativeAssassin_subset_range`:
  **Stacks tag 05PD**, the injectivity after an arbitrary base change `T ⟶ S`.
* `AlgebraicGeometry.weaklyAssociatedPoints_subset_relativeAssassin`: the inclusion
  `WeakAss_X(F) ⊆ Ass_{X/S}(F)` which the proof rests on, the case `G = 𝒪_S` of Stacks tag
  05IJ.

## Implementation notes

Injectivity of a morphism of sheaves of modules is the categorical predicate
`CategoryTheory.Mono`; the canonical map is the unit of the adjunction
`Scheme.Modules.pullbackPushforwardAdjunction`. No quasi-coherence of `g_* g^* F` is used: it
would need `g` quasi-compact and quasi-separated, which the source does not assume.

The proof is the source's. The kernel of the map has no weakly associated point, because at a
weakly associated point `x` of `F` one has `x ∈ Ass_{X/S}(F) ⊆ g(X')` — this is the case
`G = 𝒪_S` of Stacks tag 05IJ, through the fibre clause of Stacks tag 05IH — and then
`𝒪_{X, x} ⟶ 𝒪_{X', x'}` is a flat local homomorphism, hence faithfully flat, so the stalk of
the map at `x` is injective by Stacks tag 05CK. The three steps are
`AlgebraicGeometry.weaklyAssociatedPoints_subset_relativeAssassin`,
`AlgebraicGeometry.stalk_pullbackPushforwardUnit_injective_of_flat` and
`AlgebraicGeometry.mono_of_stalk_injective_on_weaklyAssociatedPoints_of_source_quasicoherent`.

For the second assertion the base-changed situation is the chosen categorical pullback
`X ×_S T`, with the base-changed morphism `AlgebraicGeometry.compBaseChangeMap f g h`; flatness,
local finite type, finite type, flatness over the base and the containment of the relative
assassin are all stable under base change, the last by Stacks tag 05KL
(`AlgebraicGeometry.relativeAssassin_baseChange_subset_range`), so the first assertion applies
verbatim.

## References

* [Stacks Project, Tag 05PD](https://stacks.math.columbia.edu/tag/05PD)
* [Stacks Project, Tag 05IJ](https://stacks.math.columbia.edu/tag/05IJ)
* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05CK](https://stacks.math.columbia.edu/tag/05CK)
* [Stacks Project, Tag 05KL](https://stacks.math.columbia.edu/tag/05KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.RingedSpace

universe u

namespace AlgebraicGeometry

/-- **The case `G = 𝒪_S` of Stacks Project, Tag 05IJ.** For `f : X ⟶ S` locally of finite type
and `F` a finite type quasi-coherent `𝒪_X`-module flat over `S`, every weakly associated point
of `F` lies in the relative assassin `Ass_{X/S}(F)`.

Tensoring `F` with the pullback of the structure sheaf of `S` changes nothing
(`AlgebraicGeometry.isWeaklyAssociatedPoint_tensorPullback_structureSheaf_iff`), so this is the
fibre clause of the forward implication of Stacks tag 05IH, which assumes nothing beyond the
hypotheses here. -/
theorem weaklyAssociatedPoints_subset_relativeAssassin {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hF : IsFlatOver f.toLRSHom.toShHom F) :
    Stacks.Divisors.weaklyAssociatedPoints F ⊆ Stacks.Divisors.relativeAssassin f F := fun x hx =>
  Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType
    f F (structureSheafModule S) x (hF x)
    ((isWeaklyAssociatedPoint_tensorPullback_structureSheaf_iff f F x).mpr hx)

/-- **Stacks Project, Tag 05PD.** Let `S` be a scheme, let `g : X' ⟶ X` be a flat morphism of
schemes over `S` with `X` locally of finite type over `S`, and let `F` be a finite type
quasi-coherent `𝒪_X`-module which is flat over `S`. If `Ass_{X/S}(F) ⊆ g(X')`, then the
canonical map `F ⟶ g_* g^* F` is injective. -/
@[stacks 05PD "injectivity"]
theorem mono_pullbackPushforwardUnit_of_relativeAssassin_subset_range
    {X' X S : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hF : IsFlatOver f.toLRSHom.toShHom F)
    (hAss : Stacks.Divisors.relativeAssassin f F ⊆ Set.range g.base) :
    Mono ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F) :=
  mono_pullbackPushforwardUnit_of_weaklyAssociatedPoints_subset_range g F
    fun _ hx => hAss (weaklyAssociatedPoints_subset_relativeAssassin f F hF hx)

/-- **Stacks Project, Tag 05PD.** The canonical map of the preceding statement remains injective
after an arbitrary base change `h : T ⟶ S`: the map
`F_T ⟶ (g_T)_* (g_T)^* F_T` on `X ×_S T` is injective as well. -/
@[stacks 05PD "after arbitrary base change"]
theorem mono_baseChange_pullbackPushforwardUnit_of_relativeAssassin_subset_range
    {X' X S : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ X)
    [LocallyOfFiniteType f] [Flat g]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hF : IsFlatOver f.toLRSHom.toShHom F)
    (hAss : Stacks.Divisors.relativeAssassin f F ⊆ Set.range g.base) :
    ∀ (T : Scheme.{u}) (h : T ⟶ S),
      Mono ((Scheme.Modules.pullbackPushforwardAdjunction (compBaseChangeMap f g h)).unit.app
        ((Scheme.Modules.pullback (pullback.fst f h)).obj F)) := by
  intro T h
  let : Flat (compBaseChangeMap f g h) := flat_baseChangeMap f g h
  let : ((Scheme.Modules.pullback (pullback.fst f h)).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent (pullback.fst f h) F
  let : ((Scheme.Modules.pullback (pullback.fst f h)).obj F).IsFiniteType :=
    isFiniteType_modulePullback (pullback.fst f h) F
  exact mono_pullbackPushforwardUnit_of_relativeAssassin_subset_range (pullback.snd f h)
    (compBaseChangeMap f g h) ((Scheme.Modules.pullback (pullback.fst f h)).obj F)
    (@modulePullback_isFlatOver _ _ _ _ _ _ _ _ (IsPullback.of_hasPullback f h) F
      (show F.IsQuasicoherent from inferInstance) hF)
    (relativeAssassin_baseChange_subset_range f g F hAss T h)

end AlgebraicGeometry

end
