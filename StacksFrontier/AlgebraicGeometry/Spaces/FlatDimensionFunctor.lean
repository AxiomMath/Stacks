module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleInDimensionsGE
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport

/-!
# Flatness in dimensions at least a bound as a functor on the test schemes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
locally of finite type and let `F` be a quasi-coherent `𝒪_X`-module of finite type. For a scheme
`T` over `Y` write `F_T` for the base change of `F` to `X_T = X ×_Y T`. Then `f_T : X_T ⟶ T` is
again locally of finite type by **Stacks 03XH** and `F_T` is again of finite type by
**Stacks 03DO**, so for each `n` the condition of **Stacks 0CWT** — that `F_T` is flat over `T`
in dimensions `≥ n` — makes sense at every test scheme. This is **Situation 0CWU**, and the
functor it introduces, equation **0CWV**, is

`F_n : (Sch/Y)^opp ⟶ Sets`, `T ↦ {*}` if `F_T` is flat over `T` in dimensions `≥ n`, `∅`
otherwise.

## Main definitions

* `AlgebraicGeometry.Space.FlatDimensionSituation`: the standing data of Situation 0CWU, the
  flatness situation of Stacks 0CWX together with local finite type of the morphism and finite
  type of the module.
* `AlgebraicGeometry.Space.FlatDimensionSituation.IsFlatInDimensionsGEAfterBaseChange`: the
  condition of Stacks 0CWT on the base change to a test scheme.
* `AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionFunctor`: the functor `F_n` of
  equation 0CWV.

## Main results

* `AlgebraicGeometry.Space.FlatDimensionSituation.isLocallyOfFiniteType_baseChangeInclusion`: the
  base-changed morphism is again locally of finite type — the first observation of the situation.
* `AlgebraicGeometry.Space.FlatDimensionSituation.isFiniteTypeOnSite_baseChangeModule`: the
  base-changed module is again of finite type — the second observation of the situation.
* `AlgebraicGeometry.Space.FlatDimensionSituation.isFlatInDimensionsGEAfterBaseChange_of_hom`:
  the condition is inherited along a morphism of test schemes, which is what makes the
  assignment of equation 0CWV a functor.
* `AlgebraicGeometry.Space.FlatDimensionSituation.nonempty_flatDimensionFunctor_obj_iff` and
  `AlgebraicGeometry.Space.FlatDimensionSituation.flatDimensionFunctor_obj_subsingleton`: the
  value of `F_n` at a test scheme is a one-point set exactly when the base change is flat in
  dimensions `≥ n`, and is empty otherwise, which is the reading of equation 0CWV.

## Implementation notes

The test schemes are `AlgebraicGeometry.Space.SchemesOver`, the base change and its two
projections are `AlgebraicGeometry.Space.baseChangeSpace`,
`AlgebraicGeometry.Space.baseChangeProjection` and `AlgebraicGeometry.Space.baseChangeInclusion`,
and `F_T` is `AlgebraicGeometry.Space.FlatnessSituation.baseChangeModule`, all as for the
flatness functor of Stacks 0CWX; the situation extends
`AlgebraicGeometry.Space.FlatnessSituation` so that none of this is duplicated. The bound `n` is
a parameter of the functor rather than a field of the situation, as in the source, where it is
fixed after the data.

The flatness condition is written as `IsFlatOverInDimensionsGEOnEveryChartDiagram`, which is the
body of the definition of Stacks 0CWT, rather than as `IsFlatOverInDimensionsGE` itself: the
latter takes quasi-coherence of the module as an instance argument, and quasi-coherence of a
pullback is not unconditional in this development — `isQuasicoherentOnSite_modulePullback` asks
for `HasLocalInverseImagePresentations` on the projection. The two agree whenever that instance
is available, which is `isFlatInDimensionsGEAfterBaseChange_iff_isFlatOverInDimensionsGE`; so
nothing is lost and the condition on a test scheme needs no hypothesis to state.

The source's first observation reads "`f_T : X_T → T` is of finite type", which its own
hypotheses do not give: `f` is assumed only locally of finite type, and that is what base change
preserves. It is recorded here in the corrected, locally-of-finite-type form — the half of
Stacks 03XH the source cites, and the form Definition 0CWT consumes. The finite-type half of
Stacks 03XH is in any case absent from this development, which
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeProperties.lean` records: it needs the
quasi-compactness statements of Stacks 03HG.

`subterminalFunctor` is the same construction as
`AlgebraicGeometry.Space.ModuleMapSituation.subterminalFunctor`, which is a method of that
structure and so cannot be applied here; it is repeated for the test schemes of an arbitrary
algebraic space, as `ModuleMapLociLimitPreserving.lean` repeats the private
`subterminalFunctor_congr` of its own neighbour.

## Functoriality

Equation 0CWV is a functor, so `F_n` must act on morphisms of test schemes: for `U ⟶ T` over
`Y`, flatness of `F_T` in dimensions `≥ n` must give flatness of `F_U`. That is exactly the
base-change clause of **Stacks 0CWS**, which
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleInDimensionsGE.lean` proves unconditionally as
`AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_isPullback`, so nothing here
is assumed: the whole situation, the two observations it makes and the functor it introduces are
all unconditional. The clause is applied at the cartesian square of `X_U ⟶ X_T` over `U ⟶ T`,
`AlgebraicGeometry.Space.isPullback_baseChangeMap`; its hypotheses on `f_T` and `F_T` are the two
observations of the situation, and its conclusion is transported across the composition
comparison of Stacks 03LU by
`AlgebraicGeometry.Space.isFlatOverInDimensionsGEOnEveryChartDiagram_iff_of_moduleIso`, exactly as
`AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_of_hom` does for the flatness
functor of Stacks 0CWX. So stability under base change is not an extra input of the functor.

## References

* [Stacks Project, Tag 0CWU](https://stacks.math.columbia.edu/tag/0CWU)
* [Stacks Project, Tag 0CWV](https://stacks.math.columbia.edu/tag/0CWV)
* [Stacks Project, Tag 0CWT](https://stacks.math.columbia.edu/tag/0CWT)
* [Stacks Project, Tag 0CWS](https://stacks.math.columbia.edu/tag/0CWS)
* [Stacks Project, Tag 0CWX](https://stacks.math.columbia.edu/tag/0CWX)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The subterminal presheaf on the test schemes over an algebraic space attached to a property
of test schemes which is inherited along their morphisms: its value is a one-point set where the
property holds and is empty where it does not. -/
def subterminalFunctor {Y : AlgebraicSpaces B S hS} (Q : SchemesOver Y → Prop)
    (stable : ∀ {T T' : SchemesOver Y}, (T' ⟶ T) → Q T → Q T') :
    (SchemesOver Y)ᵒᵖ ⥤ Type u where
  obj T := {x : PUnit.{u + 1} // Q T.unop}
  map g := ↾fun x => ⟨x.1, stable g.unop x.2⟩
  map_id := by
    intro T
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl
  map_comp := by
    intro T U V g k
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl

/-- **Situation 0CWU.** The standing data of Situation 0CWU: the flatness situation of
Stacks 0CWX — a morphism `f : X ⟶ Y` of algebraic spaces over `S` and a quasi-coherent
`𝒪_X`-module `F` — in which moreover `f` is locally of finite type and `F` is of finite type. -/
@[stacks_fixed 0CWU "standing data"]
structure FlatDimensionSituation extends FlatnessSituation.{u} B S hS where
  /-- The morphism is locally of finite type, as in the source. -/
  locallyOfFiniteType : IsLocallyOfFiniteType B S hS toFlatnessSituation.f.hom
  /-- The module is of finite type, as in the source. -/
  finiteType : SheafOfModules.IsFiniteTypeOnSite toFlatnessSituation.F

namespace FlatDimensionSituation

variable {B S hS}

/-- **Situation 0CWU, the first observation.** The base change `f_T : X_T ⟶ T` of a locally
finite type morphism to a test scheme is again locally of finite type. This is **Stacks 03XH**,
stability of the property under base change, at the fibre product square defining `X_T`.

The source says `f_T` is *of* finite type, which does not follow from its own hypotheses: `f` is
assumed only locally of finite type, and base change preserves exactly that. The half of
Stacks 03XH the source cites is the locally-of-finite-type one, and it is also what
Definition 0CWT consumes, so the corrected statement is the one that is used. -/
@[stacks 0CWU
  "the base-changed morphism is locally of finite type; corrected from the source's \"of finite \
type\", which does not follow from its hypothesis that f is only locally of finite type"]
theorem isLocallyOfFiniteType_baseChangeInclusion (D : FlatDimensionSituation.{u} B S hS)
    (T : SchemesOver D.Y) :
    IsLocallyOfFiniteType B S hS (baseChangeInclusion D.f T).hom :=
  have := isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃_F _G : AlgebraicSpaces B S hS⦄ (g : _F ⟶ _G) =>
      IsLocallyOfFiniteType B S hS g.hom)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.locallyOfFiniteType

/-- **Situation 0CWU, the second observation.** The base change `F_T` of a finite type module to
a test scheme is again of finite type. This is **Stacks 03DO** for the inverse image of
Stacks 03LU along the projection `X_T ⟶ X`. -/
@[stacks 0CWU "the base-changed module is of finite type"]
theorem isFiniteTypeOnSite_baseChangeModule (D : FlatDimensionSituation.{u} B S hS)
    (T : SchemesOver D.Y) :
    SheafOfModules.IsFiniteTypeOnSite (D.toFlatnessSituation.baseChangeModule T) :=
  isFiniteTypeOnSite_modulePullback B S hS (baseChangeProjection D.f T) D.F D.finiteType

/-- The base change `F_T` of the module to a test scheme is flat over that test scheme in
dimensions `≥ n`, in the sense of **Stacks 0CWT**. -/
def IsFlatInDimensionsGEAfterBaseChange (D : FlatDimensionSituation.{u} B S hS)
    (T : SchemesOver D.Y) (n : ℕ) : Prop :=
  IsFlatOverInDimensionsGEOnEveryChartDiagram B S hS (baseChangeSpace D.f T).2
    (baseChangeInclusion D.f T).hom (D.toFlatnessSituation.baseChangeModule T) n

/-- The condition on a test scheme is the definition of **Stacks 0CWT** for the base-changed
morphism and module, once quasi-coherence of the base-changed module is available. -/
theorem isFlatInDimensionsGEAfterBaseChange_iff_isFlatOverInDimensionsGE
    (D : FlatDimensionSituation.{u} B S hS) (T : SchemesOver D.Y) (n : ℕ)
    [(D.toFlatnessSituation.baseChangeModule T).IsQuasicoherentOnSite] :
    D.IsFlatInDimensionsGEAfterBaseChange T n ↔
      IsFlatOverInDimensionsGE B S hS (baseChangeInclusion D.f T)
        (D.toFlatnessSituation.baseChangeModule T) n :=
  Iff.rfl

/-- **Situation 0CWU, the functoriality of equation 0CWV.** The condition of **Stacks 0CWT** on
the base change is inherited along a morphism of test schemes: if `F_T` is flat over a test
scheme `T` in dimensions `≥ n`, then `F_U` is flat over `U` in dimensions `≥ n` for every test
scheme `U` over `T`. This is what makes the assignment of equation 0CWV a functor.

It is the base-change clause of **Stacks 0CWS**,
`AlgebraicGeometry.Space.isFlatOverInDimensionsGE_modulePullback_of_isPullback`, at the cartesian
square of `X_U ⟶ X_T` over `U ⟶ T`. That clause asks its morphism to be locally of finite type
and its module to be quasi-coherent and of finite type; for `f_T : X_T ⟶ T` and `F_T` those are
the two observations of the situation together with Stacks 03GA. Its conclusion is flatness in
dimensions `≥ n` of the pullback of `F_T` along `X_U ⟶ X_T`, which is `F_U` up to the
composition comparison of Stacks 03LU, across which the condition moves because it depends on
the module only through its isomorphism class. -/
theorem isFlatInDimensionsGEAfterBaseChange_of_hom (D : FlatDimensionSituation.{u} B S hS)
    {T U : SchemesOver D.Y} (g : U ⟶ T) (n : ℕ)
    (h : D.IsFlatInDimensionsGEAfterBaseChange T n) :
    D.IsFlatInDimensionsGEAfterBaseChange U n := by
  have : (D.toFlatnessSituation.baseChangeModule T).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (baseChangeProjection D.f T) D.F D.quasicoherent
  refine (isFlatOverInDimensionsGEOnEveryChartDiagram_iff_of_moduleIso B S hS
    (baseChangeSpace D.f U).2 (baseChangeInclusion D.f U).hom
    ((modulePullbackTriangle B S hS (baseChangeMap_comp_projection D.f g)).app D.F).symm n).mp ?_
  exact isFlatOverInDimensionsGE_modulePullback_of_isPullback B S hS
    (baseChangeInclusion D.f T) (D.toFlatnessSituation.baseChangeModule T)
    (D.isLocallyOfFiniteType_baseChangeInclusion T) (D.isFiniteTypeOnSite_baseChangeModule T)
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f g)) n h

/-- **Equation 0CWV, the functor `F_n` of Situation 0CWU**: the functor on the test schemes
over `Y` whose value at `T` is a one-point set when `F_T` is flat over `T` in dimensions `≥ n`,
and is empty otherwise.

That the condition is inherited along a morphism of test schemes, which is what makes the
assignment a functor, is
`AlgebraicGeometry.Space.FlatDimensionSituation.isFlatInDimensionsGEAfterBaseChange_of_hom`. -/
@[stacks 0CWU "the functor F_n of equation 0CWV"]
def flatDimensionFunctor (D : FlatDimensionSituation.{u} B S hS) (n : ℕ) :
    (SchemesOver D.Y)ᵒᵖ ⥤ Type u :=
  subterminalFunctor B S hS (fun T => D.IsFlatInDimensionsGEAfterBaseChange T n)
    fun g hT => D.isFlatInDimensionsGEAfterBaseChange_of_hom g n hT

/-- The value of `F_n` at a test scheme is nonempty exactly when the base change of `F` to that
test scheme is flat over it in dimensions `≥ n`. -/
@[simp]
theorem nonempty_flatDimensionFunctor_obj_iff (D : FlatDimensionSituation.{u} B S hS) (n : ℕ)
    (T : SchemesOver D.Y) :
    Nonempty ((D.flatDimensionFunctor n).obj (Opposite.op T)) ↔
      D.IsFlatInDimensionsGEAfterBaseChange T n :=
  ⟨fun ⟨x⟩ => x.2, fun hT => ⟨⟨PUnit.unit, hT⟩⟩⟩

/-- The value of `F_n` at a test scheme has at most one element; with
`nonempty_flatDimensionFunctor_obj_iff` this is the reading of equation 0CWV, that the value is
`{*}` where the base change is flat in dimensions `≥ n` and `∅` where it is not. -/
instance flatDimensionFunctor_obj_subsingleton (D : FlatDimensionSituation.{u} B S hS) (n : ℕ)
    (T : SchemesOver D.Y) :
    Subsingleton ((D.flatDimensionFunctor n).obj (Opposite.op T)) :=
  ⟨fun a b => Subtype.ext (Subsingleton.elim a.val b.val)⟩

/-- The value of `F_n` at a test scheme is empty exactly when the base change of `F` to that
test scheme is not flat over it in dimensions `≥ n`. -/
theorem isEmpty_flatDimensionFunctor_obj_iff (D : FlatDimensionSituation.{u} B S hS) (n : ℕ)
    (T : SchemesOver D.Y) :
    IsEmpty ((D.flatDimensionFunctor n).obj (Opposite.op T)) ↔
      ¬ D.IsFlatInDimensionsGEAfterBaseChange T n := by
  rw [← not_nonempty_iff, nonempty_flatDimensionFunctor_obj_iff]

end FlatDimensionSituation

end AlgebraicGeometry.Space

end
