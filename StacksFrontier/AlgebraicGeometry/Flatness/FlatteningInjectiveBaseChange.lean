module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Base change of a morphism over a base, and of the relative assassin condition

Let `f : X ⟶ S`, let `g : X' ⟶ X` be a morphism over `S`, and let `h : T ⟶ S` be arbitrary.
This file records the induced morphism `X' ×_S T ⟶ X ×_S T`, the fact that the square it sits
in is a pullback square, and the consequence that matters for Stacks tag 05PD: if the image of
`g` contains the relative assassin `Ass_{X/S}(F)`, then the image of the base-changed morphism
contains the relative assassin `Ass_{X_T/T}(F_T)` of the base-changed module.

## Main definitions

* `AlgebraicGeometry.compBaseChangeMap f g h` is the morphism `X' ×_S T ⟶ X ×_S T` induced by `g`.

## Main results

* `AlgebraicGeometry.isPullback_baseChangeMap`: the square
  `X' ×_S T ⟶ X ×_S T`, `X' ⟶ X` is a pullback square.
* `AlgebraicGeometry.flat_baseChangeMap`: the base change of a flat morphism is flat.
* `AlgebraicGeometry.relativeAssassin_baseChange_subset_range`: the containment
  `Ass_{X/S}(F) ⊆ g(X')` is stable under base change.

## Implementation notes

The base-changed schemes are the chosen categorical pullbacks, `X ×_S T = pullback f h` with
its two projections, so that the base-changed morphism to the base is `pullback.snd f h` and the
base-changed module is the pullback of `F` along `pullback.fst f h`.

The stability of the containment is Stacks tag 05KL (here
`AlgebraicGeometry.relativeAssassin_pullback_subset_preimage`) together with surjectivity of a
pullback of schemes onto the set-theoretic fibre product
(`AlgebraicGeometry.Scheme.exists_preimage_of_isPullback`): a point of `Ass_{X_T/T}(F_T)` maps
into `Ass_{X/S}(F)`, hence lifts to `X'`, and the two lifts agree over `S`.

## References

* [Stacks Project, Tag 05KL](https://stacks.math.columbia.edu/tag/05KL)
* [Stacks Project, Tag 05PD](https://stacks.math.columbia.edu/tag/05PD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The morphism `X' ×_S T ⟶ X ×_S T` induced by a morphism `g : X' ⟶ X` over `S`. -/
noncomputable def compBaseChangeMap {X' X S T : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ X) (h : T ⟶ S) :
    pullback (g ≫ f) h ⟶ pullback f h :=
  pullback.lift (pullback.fst (g ≫ f) h ≫ g) (pullback.snd (g ≫ f) h)
    (by rw [Category.assoc, pullback.condition])

/-- The square formed by `compBaseChangeMap f g h` and the first projections over `g` is a pullback
square: base changing `g` along `h` is base changing it along `X ×_S T ⟶ X`. -/
theorem isPullback_baseChangeMap {X' X S T : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ X) (h : T ⟶ S) :
    IsPullback (compBaseChangeMap f g h) (pullback.fst (g ≫ f) h) (pullback.fst f h) g := by
  refine IsPullback.of_right (h₁₂ := pullback.snd f h) (h₂₂ := f) (v₁₃ := h) ?_
    (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f h).flip
  simpa only [compBaseChangeMap, pullback.lift_snd] using
    (IsPullback.of_hasPullback (g ≫ f) h).flip

/-- The base change of a flat morphism is flat. -/
theorem flat_baseChangeMap {X' X S T : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ X) [Flat g]
    (h : T ⟶ S) : Flat (compBaseChangeMap f g h) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMap f g h).flip (inferInstance : Flat g)

/-- The pullback of a module of finite type is of finite type, at the shape an `X.Modules`
presents. -/
theorem isFiniteType_modulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    [F.IsFiniteType] : ((Scheme.Modules.pullback f).obj F).IsFiniteType :=
  @SheafOfModules.pullback_isFiniteType _ _ f.toLRSHom.toShHom F
    (show F.IsFiniteType from inferInstance)

/-- **Stacks Project, Tag 05KL, in the form Tag 05PD uses it.** If the image of `g : X' ⟶ X`
contains the relative assassin `Ass_{X/S}(F)`, then after any base change `h : T ⟶ S` the image
of the induced morphism `X' ×_S T ⟶ X ×_S T` contains the relative assassin of the base-changed
module. -/
theorem relativeAssassin_baseChange_subset_range {X' X S : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ X)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent]
    (hAss : Stacks.Divisors.relativeAssassin f F ⊆ Set.range g.base)
    (T : Scheme.{u}) (h : T ⟶ S) :
    Stacks.Divisors.relativeAssassin (pullback.snd f h)
        ((Scheme.Modules.pullback (pullback.fst f h)).obj F) ⊆
      Set.range (compBaseChangeMap f g h).base := by
  intro z hz
  obtain ⟨x', hx'⟩ := hAss (relativeAssassin_pullback_subset_preimage f h F hz)
  obtain ⟨w, _, hw⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_baseChangeMap f g h).flip x' z hx'
  exact ⟨w, hw⟩

end AlgebraicGeometry

end
