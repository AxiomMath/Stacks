module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosureOfPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NonemptyLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Impurities descend along a directed limit of affine test schemes

In the situation of Stacks 0CV6, let `(g : T ⟶ Y, t' ⤳ t, ξ)` be an impurity of `ℱ` above `y`,
and suppose the test scheme `T` is a directed limit `T = lim_{i} Tᵢ` of affine schemes over the
target. Then for some stage `i` the triple `(Tᵢ ⟶ Y, t'ᵢ ⤳ tᵢ, ξᵢ)` obtained by pushing the
three points along the limit projections is again an impurity of `ℱ` above `y`.

## Main definitions

* `AlgebraicGeometry.Space.AffineLimitPresentation`: the presentation of the test scheme of an
  impurity diagram as a directed limit of affine schemes over the target.
* `AlgebraicGeometry.Space.AffineLimitPresentation.stageDiagram`: the impurity diagram at a
  stage, carrying the three pushed points.

## Main results

* `AlgebraicGeometry.Space.AffineLimitPresentation.exists_isImpurity_stageDiagram`:
  **Stacks 0CV9**: for some stage `i` the triple `(Tᵢ ⟶ Y, t'ᵢ ⤳ tᵢ, ξᵢ)` is an impurity of
  `ℱ` above `y`.
* `AlgebraicGeometry.Space.AffineLimitPresentation.isRelativeWeakAssassinPoint_stageDiagram`:
  the relative-assassin half of the conclusion, which in fact holds at **every** stage.
* `AlgebraicGeometry.Space.AffineLimitPresentation.isLimitBaseChangeCone`: `X_T` is the limit
  of the `X_{Tᵢ}`, which is what feeds Stacks 0CUK and Stacks 086W.

## Implementation notes

The statement's own index shift is resolved in favour of the target: Situation 0CV6 fixes a
morphism `f : X ⟶ Y` of algebraic spaces over the base scheme `S`, and the impurity diagram of
Stacks 0CV7 is a scheme `T` **over `Y`**, so the `g : T → S` of the source's statement of
Stacks 0CV9 is a slip for `g : T ⟶ Y`; the conclusion's `Tᵢ → Y` is the correct reading, and
it is the one formalized here. The system of test schemes is likewise a system over `Y`, as
the source's "directed limit of affine schemes over `Y`" says.

The limit hypothesis is carried as the universal property of `yoneda T` among the `yoneda Tᵢ`
rather than as a limit of schemes. For a cofiltered system of affine objects of the site the
two agree, by `AlgebraicGeometry.BigFppfOver.hasLimit_of_isAffine` together with preservation
of limits by `yoneda`; taking the presheaf form as the hypothesis is what the inputs from
Stacks 0CUK and Stacks 086W consume, since both are stated for the limit of a diagram of
presheaves.

The system of base changes `X_{Tᵢ} = Tᵢ ×_Y X` is produced as
`AffineLimitPresentation.baseChangeDiagram`, the composite of the lift of the system to
`Over Y` with `CategoryTheory.Over.pullback f` and the forgetful functor. This makes the stage
objects *literally* `Limits.pullback (base i) f`, so no transport is needed for the stagewise
hypotheses of Stacks 0CUK and Stacks 086W, while the limit identification
`X_T = lim X_{Tᵢ}` comes from `Over.pullback` preserving limits and `Over.forget` creating
connected ones — the same mechanism as
`AlgebraicGeometry.Space.isLimitPullbackLimitOverPost`, which cannot be used directly because
the base `Y` of the present system is not one of its stages.

The relative-assassin half is part (1) of Stacks 0CV2, which needs no finiteness hypothesis,
applied to the cartesian square exhibiting `X_T` as `T ×_{Tᵢ} X_{Tᵢ}`. It holds at every
stage; only the closure half needs a stage to be chosen.

The closure half is the source's compactness argument. The reduced closure `Z` of `ξ` in `X_T`
is the limit of the reduced closures `Zᵢ` of the `ξᵢ`, by Stacks 0CUK in the form
`AlgebraicGeometry.Space.exists_iso_limit_reducedClosure`. Choosing a field-valued
representative `κ` of `t` and setting `Wᵢ = Zᵢ ×_{Tᵢ} Spec κ`, the system `W` is a cofiltered
system of algebraic spaces whose limit is `Z ×_T Spec κ`; each `Wᵢ` is a closed subspace of
the single fibre `X ×_Y Spec κ`, which is quasi-compact because `f` is of finite type, so each
`Wᵢ` is quasi-compact and the transition morphisms of `W` are affine. If no stage worked then
every `Wᵢ` would be nonempty, so by Stacks 086W the limit would have a point, and that point
would exhibit a specialization of `ξ` lying over `t` — contradicting the impurity.

## What is not done here

* The conclusion is the existence of **one** stage, as in the source. Nothing is claimed
  about the set of stages that work, even though the relative-assassin half holds at all of
  them.
* The limit hypothesis is packaged as the presheaf-level universal property, which is the
  form Stacks 0CUK and Stacks 086W consume. For a cofiltered system of affine objects of the
  site this is equivalent to a limit of schemes, by
  `AlgebraicGeometry.BigFppfOver.hasLimit_of_isAffine` together with
  `AlgebraicGeometry.BigFppfOver.preservesLimit_toScheme` and preservation of limits by
  `yoneda`; but **no constructor is supplied** turning a scheme-level or site-level limit cone
  into an `AffineLimitPresentation`. A caller holding `T = lim Tᵢ` in the site must take that
  step itself.
* Nothing here is said about Stacks 0CVB, 0CVC or the other consumers of this lemma.

## References

* [Stacks Project, Tag 0CV9](https://stacks.math.columbia.edu/tag/0CV9)
* [Stacks Project, Tag 0CV6](https://stacks.math.columbia.edu/tag/0CV6)
* [Stacks Project, Tag 0CV7](https://stacks.math.columbia.edu/tag/0CV7)
* [Stacks Project, Tag 0CV8](https://stacks.math.columbia.edu/tag/0CV8)
* [Stacks Project, Tag 0CVA](https://stacks.math.columbia.edu/tag/0CVA)
* [Stacks Project, Tag 0CUK](https://stacks.math.columbia.edu/tag/0CUK)
* [Stacks Project, Tag 086W](https://stacks.math.columbia.edu/tag/086W)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- the default instance search for limits of presheaves on the big fppf site times out
/-- Limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_presheaf_ImpurityAffineLimitDescent
    (J : Type u) [Category.{u} J] :
    HasLimitsOfShape J ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- the default instance search for pullbacks of presheaves on the big fppf site times out
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ImpurityAffineLimitDescent :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ImpurityAffineLimitDescent
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Precomposing with an isomorphism does not change the image on points. -/
private theorem range_pointsMap_iso_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : F ≅ G) (g : G ⟶ H) :
    Set.range (pointsMap B S hS F (m.hom ≫ g)) = Set.range (pointsMap B S hS G g) := by
  have hsurj : Function.Surjective (pointsMap B S hS F m.hom) := fun y ↦
    ⟨pointsMap B S hS G m.inv y, by
      rw [← pointsMap_comp_apply, m.inv_hom_id, pointsMap_id, id_eq]⟩
  rw [pointsMap_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- A morphism of fibre products `T₁ ×_Y X ⟶ T₂ ×_Y X` induced by a morphism `T₁ ⟶ T₂` over `Y`
exhibits the source as the base change of the target. -/
private theorem isPullback_of_comp_fst_snd {C : Type*} [Category C] [HasPullbacks C]
    {T₁ T₂ Y X P : C} {g₁ : T₁ ⟶ Y} {g₂ : T₂ ⟶ Y} {f : X ⟶ Y} {p : P ⟶ T₁} {q : P ⟶ X}
    {u : T₁ ⟶ T₂} (h₁ : IsPullback p q g₁ f) (hu : u ≫ g₂ = g₁) (h : P ⟶ pullback g₂ f)
    (hfst : h ≫ pullback.fst g₂ f = p ≫ u) (hsnd : h ≫ pullback.snd g₂ f = q) :
    IsPullback p h u (pullback.fst g₂ f) := by
  refine IsPullback.of_bot (h₃₁ := f) ?_ hfst.symm (IsPullback.of_hasPullback g₂ f)
  rw [hsnd, hu]
  exact h₁

/-! ### The limit presentation -/

/-- **The cardinality clause of a limit presentation**: what keeps the limit of the system,
and of the systems derived from it, inside the size-bounded site. It is a requirement of the
limit-descent route — of Stacks 07SF and the results proved from it — and not of Stacks 0CV9,
and either of two *incomparable* packages supplies it.

* The left one is the source's own bookkeeping: fewer objects and fewer morphisms than the
  cofinality of the cutoff. Its drawback is that `AlgebraicGeometry.exists_size_cutoff`
  produces a cutoff of cofinality `ℵ₁`, so on that site it asks for a countable system, and the
  systems of affine neighbourhoods presenting `Spec 𝒪_{V, v}` are not countable.
* The middle one trades that for a bound by the cutoff itself — on the number of objects, and
  on all the morphism types by a single cardinal — at the cost of asking the transition
  morphisms of the system to be monomorphisms. All the cardinality steps of the route then
  go through a *uniform* bound instead of a supremum of unboundedly many cardinals, which
  needs no regularity: see `AlgebraicGeometry.Space.relativelyRepresentable_limitπ_of_mono`.
* The right one makes the same trade on the number of objects and the morphism types, and
  asks instead for one cardinal below the cutoff bounding the sizes of all the stages. The base
  changes of the stages along any test morphism are then uniformly bounded as well
  (`AlgebraicGeometry.Space.baseChangeSizeBounded_of_isPullback`), which is all the
  cofinality-free route uses. This is the package an inverse system of affine étale
  neighbourhoods of a geometric point satisfies, whose transition morphisms are not
  monomorphisms; it is what presents the strict henselization `Spec 𝒪_{Y, ȳ}` in
  Stacks 0CVB.

No package implies another, and the structure asks only for their disjunction, so it is
strictly easier to inhabit than with any one of them alone. -/
def SiteLimitBound {J : Type u} [Category.{u} J] (stage : J ⥤ BigFppfOver B S hS) : Prop :=
  (#J < B.cutoff.ord.cof ∧ ∀ i j : J, #(i ⟶ j) < B.cutoff.ord.cof) ∨
    (#J < B.cutoff ∧ ∃ ν : Cardinal.{u}, ν < B.cutoff ∧ (∀ i j : J, #(i ⟶ j) ≤ ν) ∧
      ∀ {i j : J} (a : i ⟶ j), Mono (yoneda.map (stage.map a))) ∨
    (#J < B.cutoff ∧ ∃ ν : Cardinal.{u}, ν < B.cutoff ∧ (∀ i j : J, #(i ⟶ j) ≤ ν) ∧
      ∃ μ : Cardinal.{u}, μ < B.cutoff ∧
        ∀ i : J, ((BigFppfOver.toScheme B S hS).obj (stage.obj i)).size ≤ μ)

/-- **The hypothesis of Stacks 0CV9.** A presentation of the test scheme `T` of an impurity
diagram as a directed limit `T = lim_{i} Tᵢ` of affine schemes over the target: a cofiltered
index category small enough for the site, a diagram `stage` of affine objects of the site with
compatible morphisms `base i : Tᵢ ⟶ Y` to the target, and compatible projections
`proj i : T ⟶ Tᵢ` over the target which exhibit `yoneda T` as the limit of the `yoneda Tᵢ`. -/
structure AffineLimitPresentation {P : PrePureSituation.{u, u} B S hS}
    (D : ImpurityDiagram P) where
  /-- The index category of the system. -/
  J : Type u
  /-- Its category structure. -/
  [category : Category.{u} J]
  /-- It is cofiltered, which is the source's "directed". -/
  [cofiltered : IsCofiltered J]
  /-- The system of test schemes. -/
  stage : J ⥤ BigFppfOver B S hS
  /-- The index category is small enough for the site to contain the limits the descent
  argument forms; see `AlgebraicGeometry.Space.SiteLimitBound`. -/
  bound : SiteLimitBound stage
  /-- Every stage is an affine scheme. -/
  isAffine : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (stage.obj i))
  /-- The projection from the test scheme of the diagram to a stage. -/
  proj : ∀ i, D.T ⟶ stage.obj i
  /-- The projections are compatible with the transition morphisms. -/
  proj_comp : ∀ {i j : J} (a : i ⟶ j), proj i ≫ stage.map a = proj j
  /-- The structure morphism of a stage to the target of the situation. -/
  base : ∀ i, yoneda.obj (stage.obj i) ⟶ P.Y
  /-- The system is a system over the target. -/
  base_comp : ∀ {i j : J} (a : i ⟶ j), yoneda.map (stage.map a) ≫ base j = base i
  /-- The projections are morphisms over the target. -/
  proj_base : ∀ i, yoneda.map (proj i) ≫ base i = D.g
  /-- The test scheme is the limit: the presheaf it represents has the universal property of
  the limit of the presheaves represented by the stages. -/
  isLimit : ∀ (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (m : ∀ i, W ⟶ yoneda.obj (stage.obj i)),
    (∀ {i j : J} (a : i ⟶ j), m i ≫ yoneda.map (stage.map a) = m j) →
    ∃! h : W ⟶ yoneda.obj D.T, ∀ i, h ≫ yoneda.map (proj i) = m i

attribute [instance] AffineLimitPresentation.category AffineLimitPresentation.cofiltered

namespace AffineLimitPresentation

variable {P : PrePureSituation.{u, u} B S hS} {D : ImpurityDiagram P}
  (A : AffineLimitPresentation D)

/-- A cofiltered index category is connected; this is what makes the forgetful functors from
the categories of presheaves over the target and over the source preserve the limits used
below. -/
instance isConnected_index : IsConnected A.J := IsCofiltered.isConnected A.J

/-- The system of test schemes, read in the category of presheaves. -/
noncomputable abbrev presheafDiagram : A.J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  A.stage ⋙ yoneda

/-- The cone on the system of test schemes with vertex the presheaf represented by the test
scheme of the diagram, given by the projections. -/
@[simps] noncomputable def projCone : Cone A.presheafDiagram where
  pt := yoneda.obj D.T
  π :=
    { app := fun i ↦ yoneda.map (A.proj i)
      naturality := fun i j a ↦ by
        simp [← Functor.map_comp, A.proj_comp a] }

/-- The projection cone is a limit cone: this is the limit hypothesis of the presentation. -/
noncomputable def isLimitProjCone : IsLimit A.projCone :=
  IsLimit.ofExistsUnique fun s ↦ A.isLimit s.pt (fun i ↦ s.π.app i)
    (fun {i j} a ↦ by simpa using s.w a)

/-! ### The system of base changes -/

/-- The system of test schemes lifted to the category of presheaves over the target. -/
@[simps] noncomputable def overDiagram : A.J ⥤ Over P.Y where
  obj i := Over.mk (A.base i)
  map {i j} a := Over.homMk (yoneda.map (A.stage.map a)) (A.base_comp a)
  map_id i := Over.OverMorphism.ext (by simp)
  map_comp {i j k} a b := Over.OverMorphism.ext (by simp)

/-- The cone on the lifted system with vertex the test scheme over the target. -/
@[simps] noncomputable def overCone : Cone A.overDiagram where
  pt := Over.mk D.g
  π :=
    { app := fun i ↦ Over.homMk (yoneda.map (A.proj i)) (A.proj_base i)
      naturality := fun i j a ↦ Over.OverMorphism.ext (by
        change 𝟙 (yoneda.obj D.T) ≫ yoneda.map (A.proj j) =
          yoneda.map (A.proj i) ≫ yoneda.map (A.stage.map a)
        rw [Category.id_comp, ← Functor.map_comp, A.proj_comp a]) }

/-- Forgetting the structure morphism to the target turns the cone over the target into the
projection cone. -/
theorem forget_mapCone_overCone :
    (Over.forget P.Y).mapCone A.overCone = A.projCone := rfl

/-- The cone over the target is a limit cone, because the forgetful functor from the category
of presheaves over the target creates limits of connected shape. -/
noncomputable def isLimitOverCone : IsLimit A.overCone := by
  have _ : IsConnected A.J := IsCofiltered.isConnected A.J
  exact isLimitOfReflects (Over.forget P.Y)
    (A.forget_mapCone_overCone ▸ A.isLimitProjCone)

/-- **The system of base changes `X_{Tᵢ} = Tᵢ ×_Y X`.** Its value at a stage is literally the
fibre product `Limits.pullback (base i) f`. -/
noncomputable abbrev baseChangeDiagram : A.J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  A.overDiagram ⋙ Over.pullback P.f ⋙ Over.forget P.X

/-- The cone on the system of base changes with vertex `X_T`, obtained from the cone over the
target by base change along the morphism of the situation. -/
noncomputable abbrev baseChangeCone : Cone A.baseChangeDiagram :=
  (Over.forget P.X).mapCone ((Over.pullback P.f).mapCone A.overCone)

/-- **`X_T` is the limit of the `X_{Tᵢ}`.** Base change along a fixed morphism preserves
limits, being a right adjoint, and the forgetful functor from presheaves over the source
preserves connected limits. -/
noncomputable def isLimitBaseChangeCone : IsLimit A.baseChangeCone := by
  have _ : IsConnected A.J := IsCofiltered.isConnected A.J
  exact isLimitOfPreserves (Over.forget P.X)
    (isLimitOfPreserves (Over.pullback P.f) A.isLimitOverCone)

/-- The projection of `X_T` to the stage `X_{Tᵢ}`. -/
noncomputable abbrev stageProj (i : A.J) : D.baseChange ⟶ pullback (A.base i) P.f :=
  A.baseChangeCone.π.app i

/-- The projection `X_T ⟶ X_{Tᵢ}` followed by the first projection to `Tᵢ` is the composite
`X_T ⟶ T ⟶ Tᵢ`. -/
@[simp] theorem stageProj_comp_fst (i : A.J) :
    A.stageProj i ≫ pullback.fst (A.base i) P.f = D.toT ≫ yoneda.map (A.proj i) := by
  have hw : (D.toT ≫ yoneda.map (A.proj i)) ≫ A.base i = D.toX ≫ P.f := by
    rw [Category.assoc, A.proj_base i]; exact pullback.condition
  have key : A.stageProj i = pullback.lift (D.toT ≫ yoneda.map (A.proj i)) D.toX hw := rfl
  rw [key, pullback.lift_fst]

/-- The projection `X_T ⟶ X_{Tᵢ}` followed by the second projection to `X` is the projection
`X_T ⟶ X`. -/
@[simp] theorem stageProj_comp_snd (i : A.J) :
    A.stageProj i ≫ pullback.snd (A.base i) P.f = D.toX :=
  Over.w ((Over.pullback P.f).map (A.overCone.π.app i))

/-- The transition morphism of the system of base changes, read as a morphism between the
fibre products `Limits.pullback (base i) f`. -/
noncomputable abbrev trans {i j : A.J} (a : i ⟶ j) :
    pullback (A.base i) P.f ⟶ pullback (A.base j) P.f :=
  A.baseChangeDiagram.map a

/-- The transition morphism `X_{Tᵢ} ⟶ X_{Tⱼ}` lies over the transition morphism `Tᵢ ⟶ Tⱼ`. -/
@[simp] theorem trans_comp_fst {i j : A.J} (a : i ⟶ j) :
    A.trans a ≫ pullback.fst (A.base j) P.f =
      pullback.fst (A.base i) P.f ≫ yoneda.map (A.stage.map a) := by
  have hw : (pullback.fst (A.base i) P.f ≫ yoneda.map (A.stage.map a)) ≫ A.base j =
      pullback.snd (A.base i) P.f ≫ P.f := by
    rw [Category.assoc, A.base_comp a]; exact pullback.condition
  have key : A.trans a =
      pullback.lift (pullback.fst (A.base i) P.f ≫ yoneda.map (A.stage.map a))
        (pullback.snd (A.base i) P.f) hw := rfl
  rw [key, pullback.lift_fst]

/-- The transition morphism `X_{Tᵢ} ⟶ X_{Tⱼ}` commutes with the projections to `X`. -/
@[simp] theorem trans_comp_snd {i j : A.J} (a : i ⟶ j) :
    A.trans a ≫ pullback.snd (A.base j) P.f = pullback.snd (A.base i) P.f :=
  Over.w ((Over.pullback P.f).map (A.overDiagram.map a))

/-! ### The stagewise hypotheses of Stacks 0CUK and Stacks 086W -/

/-- Every stage of the system of base changes is an algebraic space. -/
theorem isAlgebraicSpace_baseChangeDiagram_obj (i : A.J) :
    IsAlgebraicSpace B S hS (A.baseChangeDiagram.obj i) :=
  isAlgebraicSpace_pullback B S hS (A.base i) P.f
    (isAlgebraicSpace_yoneda B S hS (A.stage.obj i)) P.hX P.hY

/-- Every stage of the system of base changes is a decent algebraic space, because the
morphism of the situation is decent. -/
theorem isDecentSpace_baseChangeDiagram_obj (i : A.J) :
    IsDecentSpace B S hS (A.baseChangeDiagram.obj i) :=
  P.decent (A.stage.obj i) (A.base i)

/-- A transition morphism of the system of base changes exhibits an earlier stage as the base
change of a later one along the corresponding transition morphism of test schemes. -/
theorem isPullback_baseChangeDiagram_map {i j : A.J} (a : i ⟶ j) :
    IsPullback (pullback.fst (A.base i) P.f) (A.trans a)
      (yoneda.map (A.stage.map a)) (pullback.fst (A.base j) P.f) := by
  exact isPullback_of_comp_fst_snd (IsPullback.of_hasPullback (A.base i) P.f) (A.base_comp a)
    _ (A.trans_comp_fst a) (A.trans_comp_snd a)

/-- Every transition morphism of the system of base changes is affine, being the base change of
a morphism of affine schemes. -/
theorem isAffineHom_baseChangeDiagram_map {i j : A.J} (a : i ⟶ j) :
    IsAffineHom B S hS (A.trans a) := by
  have _ := A.isAffine i
  have _ := A.isAffine j
  exact IsAffineHom.of_isPullback (A.isPullback_baseChangeDiagram_map a)
    (isAffineHom_yoneda_map B S hS (A.stage.map a))

/-- Under the right package of `AlgebraicGeometry.Space.SiteLimitBound` the transition
morphisms of the system of base changes are monomorphisms as well, being base changes of the
transition morphisms of the system of test schemes. -/
theorem mono_trans (hmono : ∀ {i j : A.J} (a : i ⟶ j), Mono (yoneda.map (A.stage.map a)))
    {i j : A.J} (a : i ⟶ j) : Mono (A.trans a) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (A.isPullback_baseChangeDiagram_map a) (hmono a)

/-- **The cardinality clause, read on the system of base changes.** Either the source's own
bookkeeping holds, or the index category is bounded by the cutoff with its morphism types
bounded by one cardinal below it and the base changes of the system of base changes along any
test morphism are uniformly bounded. The middle package of
`AlgebraicGeometry.Space.SiteLimitBound` gives the latter by monomorphy of the transitions, the
right one by the uniform bound on the stages. -/
theorem bound_baseChangeDiagram :
    (#A.J < B.cutoff.ord.cof ∧ ∀ i j : A.J, #(i ⟶ j) < B.cutoff.ord.cof) ∨
      (#A.J < B.cutoff ∧ ∃ ν : Cardinal.{u}, ν < B.cutoff ∧ (∀ i j : A.J, #(i ⟶ j) ≤ ν) ∧
        BaseChangeSizeBounded B S hS A.baseChangeDiagram) := by
  rcases A.bound with h | ⟨hsize, ν, hν, hhom, hmono⟩ | ⟨hsize, ν, hν, hhom, μ, hμ, hstage⟩
  · exact Or.inl h
  · exact Or.inr ⟨hsize, ν, hν, hhom,
      baseChangeSizeBounded_of_mono B S hS _ fun {_i _j} a ↦ A.mono_trans hmono a⟩
  · exact Or.inr ⟨hsize, ν, hν, hhom,
      baseChangeSizeBounded_of_isPullback B S hS _ A.stage (fun i ↦ pullback.fst (A.base i) P.f)
        (fun {_i _j} a ↦ (A.isPullback_baseChangeDiagram_map a).flip) hμ hstage⟩

/-- **`X_T` is an algebraic space**, by Stacks 07SF applied to the system of base changes;
every package of the cardinality clause supplies the hypothesis it needs. -/
theorem isAlgebraicSpace_limit_baseChangeDiagram :
    IsAlgebraicSpace B S hS (limit A.baseChangeDiagram) := by
  rcases A.bound_baseChangeDiagram with ⟨hsize, hhom⟩ | ⟨hsize, ν, hν, hhom, hB⟩
  · exact isAlgebraicSpace_limit B S hS _ hsize hhom
      (fun i ↦ A.isAlgebraicSpace_baseChangeDiagram_obj i)
      (fun {_i _j} a ↦ A.isAffineHom_baseChangeDiagram_map a)
  · exact isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS _ hsize hν hhom
      (fun i ↦ A.isAlgebraicSpace_baseChangeDiagram_obj i)
      (fun {_i _j} a ↦ A.isAffineHom_baseChangeDiagram_map a) hB

/-! ### The impurity diagram at a stage -/

/-- The point of a stage test scheme below the generalization `t'`. -/
noncomputable abbrev stagePoint' (i : A.J) : points B S hS (yoneda.obj (A.stage.obj i)) :=
  pointsMap B S hS (yoneda.obj D.T) (yoneda.map (A.proj i)) D.t'

/-- The point of a stage test scheme below `t`. -/
noncomputable abbrev stagePoint (i : A.J) : points B S hS (yoneda.obj (A.stage.obj i)) :=
  pointsMap B S hS (yoneda.obj D.T) (yoneda.map (A.proj i)) D.t

/-- The point of a stage base change below the distinguished point `ξ`. -/
noncomputable abbrev stageXi (i : A.J) : points B S hS (pullback (A.base i) P.f) :=
  pointsMap B S hS D.baseChange (A.stageProj i) D.xi

/-- The specialization `t' ⤳ t` pushes to a specialization at every stage, by continuity of the
transition morphism on the representing schemes. -/
theorem specializes_stagePoint (i : A.J) :
    pointsToScheme B S hS (A.stage.obj i) (A.stagePoint' i) ⤳
      pointsToScheme B S hS (A.stage.obj i) (A.stagePoint i) := by
  have hcont : Continuous ((BigFppfOver.toScheme B S hS).map (A.proj i)).base :=
    ((BigFppfOver.toScheme B S hS).map (A.proj i)).base.hom.continuous_toFun
  have h := D.specializes.map hcont
  rwa [← pointsToScheme_pointsMap_yoneda, ← pointsToScheme_pointsMap_yoneda] at h

/-- The pushed point of a stage test scheme still lies over the chosen point of the target. -/
theorem pointsMap_base_stagePoint (i : A.J) :
    pointsMap B S hS (yoneda.obj (A.stage.obj i)) (A.base i) (A.stagePoint i) = P.y := by
  rw [← pointsMap_comp_apply, A.proj_base i]
  exact D.mapsToChosenPoint

/-- The pushed distinguished point of a stage base change lies over the pushed
generalization. -/
theorem pointsMap_fst_stageXi (i : A.J) :
    pointsMap B S hS (pullback (A.base i) P.f) (pullback.fst (A.base i) P.f) (A.stageXi i) =
      A.stagePoint' i := by
  rw [← pointsMap_comp_apply, A.stageProj_comp_fst i, pointsMap_comp_apply,
    D.pointsMap_toT_xi]

/-- **The impurity diagram at a stage.** The triple `(Tᵢ ⟶ Y, t'ᵢ ⤳ tᵢ, ξᵢ)` obtained by
pushing the three points of the given diagram along the limit projections. -/
noncomputable def stageDiagram (i : A.J) : ImpurityDiagram P where
  T := A.stage.obj i
  g := A.base i
  t' := A.stagePoint' i
  t := A.stagePoint i
  specializes := A.specializes_stagePoint i
  mapsToChosenPoint := A.pointsMap_base_stagePoint i
  xi := A.stageXi i
  xi_liesOver := A.pointsMap_fst_stageXi i

/-- The test scheme of the impurity diagram at a stage is the stage `Tᵢ`. -/
@[simp] theorem stageDiagram_T (i : A.J) : (A.stageDiagram i).T = A.stage.obj i := rfl

/-- The morphism to the target of the impurity diagram at a stage is `Tᵢ ⟶ Y`. -/
@[simp] theorem stageDiagram_g (i : A.J) : (A.stageDiagram i).g = A.base i := rfl

/-- The distinguished point of the impurity diagram at a stage is `ξᵢ`. -/
@[simp] theorem stageDiagram_xi (i : A.J) : (A.stageDiagram i).xi = A.stageXi i := rfl

/-- The specialized point of the impurity diagram at a stage is `tᵢ`. -/
@[simp] theorem stageDiagram_t (i : A.J) : (A.stageDiagram i).t = A.stagePoint i := rfl

/-! ### The relative-assassin half, at every stage -/

/-- `X_T` is the base change of the stage `X_{Tᵢ}` along the projection `T ⟶ Tᵢ`. -/
theorem isPullback_stageProj (i : A.J) :
    IsPullback D.toT (A.stageProj i) (yoneda.map (A.proj i)) (pullback.fst (A.base i) P.f) := by
  exact isPullback_of_comp_fst_snd (IsPullback.of_hasPullback D.g P.f) (A.proj_base i)
    _ (A.stageProj_comp_fst i) (A.stageProj_comp_snd i)

/-- The projection `X_T ⟶ X_{Tᵢ}`, as a morphism of algebraic spaces. -/
noncomputable abbrev stageProjSpace (i : A.J) :
    D.baseChangeSpace ⟶ P.baseChangeSpace (A.stage.obj i) (A.base i) :=
  ObjectProperty.homMk (A.stageProj i)

/-- The projection `T ⟶ Tᵢ`, as a morphism of algebraic spaces. -/
noncomputable abbrev projSpace (i : A.J) :
    (schemeSpace D.T : AlgebraicSpaces B S hS) ⟶
      schemeSpace (A.stage.obj i) :=
  ObjectProperty.homMk (yoneda.map (A.proj i))

/-- The square exhibiting `X_T ⟶ T` as the base change of `X_{Tᵢ} ⟶ Tᵢ`, in the orientation
that part (1) of Stacks 0CV2 consumes. -/
theorem isPullback_stageProjSpace (i : A.J) :
    IsPullback (A.stageProjSpace i).hom (P.baseChangeToBase D.T D.g).hom
      (P.baseChangeToBase (A.stage.obj i) (A.base i)).hom (A.projSpace i).hom :=
  (A.isPullback_stageProj i).flip

/-- The restriction `ℱ_T` of the module of the situation to `X_T` is the pullback along the
projection of the restriction `ℱ_{Tᵢ}` to a stage. -/
noncomputable def stageModuleIso (i : A.J) :
    (modulePullback B S hS (A.stageProjSpace i)).obj
        (P.baseChangeModule (A.stage.obj i) (A.base i)) ≅
      P.baseChangeModule D.T D.g :=
  (modulePullbackCompIso B S hS (A.stageProjSpace i)
      (P.baseChangeToSource (A.stage.obj i) (A.base i))).app P.F ≪≫
    eqToIso (congrArg
      (fun m : D.baseChangeSpace ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS) ↦
        (modulePullback B S hS m).obj P.F)
      (ObjectProperty.hom_ext _ (A.stageProj_comp_snd i) :
        A.stageProjSpace i ≫ P.baseChangeToSource (A.stage.obj i) (A.base i) =
          P.baseChangeToSource D.T D.g))

/-- **The relative-assassin half of Stacks 0CV9, at every stage.** The pushed distinguished
point `ξᵢ` lies in the relative weak assassin `WeakAss_{X_{Tᵢ}/Tᵢ}(ℱ_{Tᵢ})`.

This is part (1) of Stacks 0CV2 for the cartesian square exhibiting `X_T ⟶ T` as the base
change of `X_{Tᵢ} ⟶ Tᵢ`; it uses no finiteness hypothesis and no stage needs to be chosen. -/
theorem isRelativeWeakAssassinPoint_stageDiagram
    (hD : D.IsRelativeWeakAssassinPoint D.xi) (i : A.J) :
    (A.stageDiagram i).IsRelativeWeakAssassinPoint (A.stageDiagram i).xi := by
  rw [ImpurityDiagram.isRelativeWeakAssassinPoint_iff] at hD ⊢
  refine isRelativeWeaklyAssociatedPoint_of_baseChange B S hS
    (A.isPullback_stageProjSpace i) (P.baseChangeModule (A.stage.obj i) (A.base i)) ?_
  exact (isRelativeWeaklyAssociatedPoint_congr (P.baseChangeToBase D.T D.g)
    (A.stageModuleIso i) D.xi).2 hD


/-- Two morphisms into the presheaf represented by the test scheme agree as soon as they agree
after projection to every stage. This is the uniqueness half of the limit property. -/
theorem hom_ext_of_proj {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {h₁ h₂ : W ⟶ yoneda.obj D.T}
    (h : ∀ i, h₁ ≫ yoneda.map (A.proj i) = h₂ ≫ yoneda.map (A.proj i)) : h₁ = h₂ := by
  obtain ⟨k, -, huniq⟩ := A.isLimit W (fun i ↦ h₁ ≫ yoneda.map (A.proj i)) (by
    intro i j a
    rw [Category.assoc, ← Functor.map_comp, A.proj_comp a])
  rw [huniq h₁ fun i ↦ rfl, huniq h₂ fun i ↦ (h i).symm]

/-- The comparison isomorphism identifying `X_T` with the chosen limit of the system of base
changes, which is the form the inputs from Stacks 0CUK and Stacks 086W are stated in. -/
noncomputable def limitIso : D.baseChange ≅ limit A.baseChangeDiagram :=
  A.isLimitBaseChangeCone.conePointUniqueUpToIso (limit.isLimit A.baseChangeDiagram)

/-- The comparison isomorphism followed by a limit projection is the projection
`X_T ⟶ X_{Tᵢ}`. -/
theorem limitIso_hom_comp_π (i : A.J) :
    A.limitIso.hom ≫ limit.π A.baseChangeDiagram i = A.stageProj i :=
  A.isLimitBaseChangeCone.conePointUniqueUpToIso_hom_comp
    (limit.isLimit A.baseChangeDiagram) i

/-- The inverse comparison isomorphism followed by the projection `X_T ⟶ X_{Tᵢ}` is the limit
projection. -/
theorem limitIso_inv_comp_stageProj (i : A.J) :
    A.limitIso.inv ≫ A.stageProj i = limit.π A.baseChangeDiagram i :=
  A.limitIso.inv_comp_eq.2 (A.limitIso_hom_comp_π i).symm

/-- The transported distinguished point, a point of the chosen limit. -/
noncomputable abbrev limitXi : points B S hS (limit A.baseChangeDiagram) :=
  pointsMap B S hS D.baseChange A.limitIso.hom D.xi

/-- The image of the transported distinguished point under a limit projection is `ξᵢ`. -/
theorem pointsMap_π_limitXi (i : A.J) :
    pointsMap B S hS (limit A.baseChangeDiagram) (limit.π A.baseChangeDiagram i) A.limitXi =
      A.stageXi i := by
  rw [← pointsMap_comp_apply, A.limitIso_hom_comp_π i]
  rfl

/-- The inverse comparison isomorphism carries the transported distinguished point back to
`ξ`. -/
theorem pointsMap_limitIso_inv_limitXi :
    pointsMap B S hS (limit A.baseChangeDiagram) A.limitIso.inv A.limitXi = D.xi := by
  rw [← pointsMap_comp_apply, Iso.hom_inv_id, pointsMap_id, id_eq]

/-- **Stacks 0CUK, as sets, for `ξ` in `X_T`**: the closure of `ξ` is the intersection of the
preimages of the closures of the `ξᵢ`. Either package of the cardinality clause supplies the
hypothesis Stacks 0CUK needs. -/
theorem closure_singleton_limitXi :
    closure {A.limitXi} = ⋂ i : A.J,
      pointsMap B S hS (limit A.baseChangeDiagram) (limit.π A.baseChangeDiagram i) ⁻¹'
        closure {pointsMap B S hS (limit A.baseChangeDiagram)
                  (limit.π A.baseChangeDiagram i) A.limitXi} := by
  rcases A.bound_baseChangeDiagram with ⟨hsize, hhom⟩ | ⟨hsize, ν, hν, hhom, hB⟩
  · exact closure_singleton_limit B S hS _ hsize hhom
      (fun i ↦ A.isAlgebraicSpace_baseChangeDiagram_obj i)
      (fun {_i _j} a ↦ A.isAffineHom_baseChangeDiagram_map a) A.limitXi
  · exact closure_singleton_limit_of_baseChangeSizeBounded B S hS _ hsize hν hhom
      (fun i ↦ A.isAlgebraicSpace_baseChangeDiagram_obj i)
      (fun {_i _j} a ↦ A.isAffineHom_baseChangeDiagram_map a) hB A.limitXi

/-- **The limit of a system of reduced closed subspaces of the stages of `X_T` is a reduced
algebraic space.** This is the input that
`AlgebraicGeometry.Space.exists_iso_limit_reducedClosure_of_limitReduced` makes of its
cardinality hypotheses, discharged here from either package of the cardinality clause.

In the right package the trade has to survive the passage to the derived system `E`: the
component `η i` is a monomorphism and `E.map a ≫ η j = η i ≫ trans a` with `η i` and
`trans a` monomorphisms, so `E.map a` is one too, and the uniform-bound forms of Stacks 07SF
and Stacks 0CUI apply to `E` over the same index category. -/
theorem isAlgebraicSpace_and_isReduced_limit_of_mono_natTrans
    (E : A.J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (η : E ⟶ A.baseChangeDiagram)
    (hE : ∀ i, IsAlgebraicSpace B S hS (E.obj i))
    (hEAffine : ∀ {i j : A.J} (f : i ⟶ j), IsAffineHom B S hS (E.map f))
    (hηMono : ∀ i, Mono (η.app i))
    (hAred : ∀ i, HasEtaleLocalProperty B S hS (E.obj i) (fun Y : Scheme.{u} ↦ IsReduced Y)) :
    IsAlgebraicSpace B S hS (limit E) ∧
      HasEtaleLocalProperty B S hS (limit E) (fun Y : Scheme.{u} ↦ IsReduced Y) := by
  rcases A.bound_baseChangeDiagram with ⟨hsize, hhom⟩ | ⟨hsize, ν, hν, hhom, hB⟩
  · exact ⟨isAlgebraicSpace_limit B S hS E hsize hhom hE hEAffine,
      isReduced_limit B S hS E hsize hhom hE hEAffine hAred⟩
  · have hEB : BaseChangeSizeBounded B S hS E :=
      baseChangeSizeBounded_of_natTrans_mono B S hS _ η hηMono
        (fun i ↦ A.isAlgebraicSpace_baseChangeDiagram_obj i)
        (fun {_i _j} a ↦ A.isAffineHom_baseChangeDiagram_map a) hB
    exact ⟨isAlgebraicSpace_limit_of_baseChangeSizeBounded B S hS E hsize hν hhom hE hEAffine
        hEB,
      isReduced_limit_of_baseChangeSizeBounded B S hS E hsize hν hhom hE hEAffine hEB hAred⟩

/-- The component at a stage of a morphism of systems over the system of base changes, read
with its target in the fibre-product spelling. -/
noncomputable abbrev stageComp {E : A.J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (η : E ⟶ A.baseChangeDiagram) (i : A.J) : E.obj i ⟶ pullback (A.base i) P.f :=
  η.app i

/-- Naturality of such a morphism of systems, in the fibre-product spelling. -/
theorem naturality_trans {E : A.J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (η : E ⟶ A.baseChangeDiagram) {i j : A.J} (a : i ⟶ j) :
    A.stageComp η i ≫ A.trans a = E.map a ≫ A.stageComp η j :=
  (η.naturality a).symm

end AffineLimitPresentation

/-! ### The fibre of the situation over a field-valued point of the test scheme -/

/-- The morphism `Spec κ ⟶ T` presented by a field-valued point of the test scheme. -/
noncomputable abbrev impurityFieldMor {P : PrePureSituation.{u, u} B S hS}
    (D : ImpurityDiagram P) (κ : FieldValuedPoint B S hS (yoneda.obj D.T)) :
    yoneda.obj κ.siteObject ⟶ yoneda.obj D.T :=
  yonedaEquiv.symm κ.value

/-- **The common fibre.** The base change `X ×_Y Spec κ` of the morphism of the situation along
the composite `Spec κ ⟶ T ⟶ Y`. Every fibre `X_{Tᵢ} ×_{Tᵢ} Spec κ` is canonically this one,
because `X_{Tᵢ} = Tᵢ ×_Y X`; that is what makes the closed subspaces below live in a single
quasi-compact space. -/
noncomputable abbrev impurityFibre (P : PrePureSituation.{u, u} B S hS)
    (D : ImpurityDiagram P) (κ : FieldValuedPoint B S hS (yoneda.obj D.T)) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (impurityFieldMor D κ ≫ D.g) P.f

/-- The common fibre `X ×_Y Spec κ` is an algebraic space. -/
theorem isAlgebraicSpace_impurityFibre (P : PrePureSituation.{u, u} B S hS)
    (D : ImpurityDiagram P) (κ : FieldValuedPoint B S hS (yoneda.obj D.T)) :
    IsAlgebraicSpace B S hS (impurityFibre P D κ) :=
  isAlgebraicSpace_pullback B S hS (impurityFieldMor D κ ≫ D.g) P.f
    (isAlgebraicSpace_yoneda B S hS κ.siteObject) P.hX P.hY

/-- The common fibre is quasi-compact, because the morphism of the situation is of finite type,
hence quasi-compact, and the spectrum of a field is quasi-compact. -/
theorem isQuasiCompactSpace_impurityFibre (P : PrePureSituation.{u, u} B S hS)
    (D : ImpurityDiagram P) (κ : FieldValuedPoint B S hS (yoneda.obj D.T)) :
    IsQuasiCompactSpace B S hS (impurityFibre P D κ) := by
  have hspec : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.siteObject) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of κ.carrier)))
  exact P.finiteType.2 (yoneda.obj κ.siteObject)
    (isAlgebraicSpace_yoneda B S hS κ.siteObject)
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS κ.siteObject hspec)
    (impurityFieldMor D κ ≫ D.g)

namespace AffineLimitPresentation

variable {P : PrePureSituation.{u, u} B S hS} {D : ImpurityDiagram P}
  (A : AffineLimitPresentation D) (κ : FieldValuedPoint B S hS (yoneda.obj D.T))

/-- The identification of the common fibre with the fibre of a stage: the morphism
`X ×_Y Spec κ ⟶ X_{Tᵢ}`. -/
noncomputable def fibreToStage (i : A.J) :
    impurityFibre P D κ ⟶ pullback (A.base i) P.f :=
  pullback.lift
    (pullback.fst (impurityFieldMor D κ ≫ D.g) P.f ≫
      impurityFieldMor D κ ≫ yoneda.map (A.proj i))
    (pullback.snd (impurityFieldMor D κ ≫ D.g) P.f)
    (by
      rw [Category.assoc, Category.assoc, A.proj_base i]
      exact pullback.condition)

/-- The morphism `X ×_Y Spec κ ⟶ X_{Tᵢ}` followed by the projection to `Tᵢ` is the composite
`X ×_Y Spec κ ⟶ Spec κ ⟶ T ⟶ Tᵢ`. -/
theorem fibreToStage_comp_fst (i : A.J) :
    A.fibreToStage κ i ≫ pullback.fst (A.base i) P.f =
      pullback.fst (impurityFieldMor D κ ≫ D.g) P.f ≫
        impurityFieldMor D κ ≫ yoneda.map (A.proj i) :=
  pullback.lift_fst _ _ _

/-- The morphism `X ×_Y Spec κ ⟶ X_{Tᵢ}` commutes with the projections to `X`. -/
theorem fibreToStage_comp_snd (i : A.J) :
    A.fibreToStage κ i ≫ pullback.snd (A.base i) P.f =
      pullback.snd (impurityFieldMor D κ ≫ D.g) P.f :=
  pullback.lift_snd _ _ _

/-- The morphisms `X ×_Y Spec κ ⟶ X_{Tᵢ}` are compatible with the transition morphisms of the
system of base changes. -/
theorem fibreToStage_comp_trans {i j : A.J} (a : i ⟶ j) :
    A.fibreToStage κ i ≫ A.trans a = A.fibreToStage κ j := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, A.trans_comp_fst a, ← Category.assoc, A.fibreToStage_comp_fst κ i,
      A.fibreToStage_comp_fst κ j, Category.assoc, Category.assoc, ← Functor.map_comp,
      A.proj_comp a]
  · rw [Category.assoc, A.trans_comp_snd a, A.fibreToStage_comp_snd κ i,
      A.fibreToStage_comp_snd κ j]

/-- The common fibre is the fibre product of the stage `X_{Tᵢ}` with `Spec κ` over `Tᵢ`. -/
theorem isPullback_fibreToStage (i : A.J) :
    IsPullback (A.fibreToStage κ i) (pullback.fst (impurityFieldMor D κ ≫ D.g) P.f)
      (pullback.fst (A.base i) P.f) (impurityFieldMor D κ ≫ yoneda.map (A.proj i)) := by
  refine (isPullback_of_comp_fst_snd (IsPullback.of_hasPullback (impurityFieldMor D κ ≫ D.g) P.f)
    (by rw [Category.assoc, A.proj_base i]) _ (A.fibreToStage_comp_fst κ i)
    (A.fibreToStage_comp_snd κ i)).flip

/-! ### The system of fibres of the reduced closures -/

variable {E : A.J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (η : E ⟶ A.baseChangeDiagram)

/-- **The system `Wᵢ = Zᵢ ×_{Tᵢ} Spec κ`**, presented as the base change of the closed subspace
`Zᵢ ⟶ X_{Tᵢ}` along the identification of the common fibre with the fibre of the stage. -/
noncomputable abbrev closureFibre (i : A.J) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  pullback (A.stageComp η i) (A.fibreToStage κ i)

/-- The projection of `Wᵢ` to the reduced closure `Zᵢ`. -/
noncomputable abbrev closureFibreToClosure (i : A.J) : A.closureFibre κ η i ⟶ E.obj i :=
  pullback.fst (A.stageComp η i) (A.fibreToStage κ i)

/-- The projection of `Wᵢ` to the common fibre; it is a closed immersion. -/
noncomputable abbrev closureFibreToFibre (i : A.J) :
    A.closureFibre κ η i ⟶ impurityFibre P D κ :=
  pullback.snd (A.stageComp η i) (A.fibreToStage κ i)

/-- `Wᵢ` is the fibre product of `Zᵢ ⟶ X_{Tᵢ}` with `X ×_Y Spec κ ⟶ X_{Tᵢ}`. -/
theorem isPullback_closureFibre (i : A.J) :
    IsPullback (A.closureFibreToClosure κ η i) (A.closureFibreToFibre κ η i)
      (A.stageComp η i) (A.fibreToStage κ i) :=
  IsPullback.of_hasPullback _ _

/-- `Wᵢ` is the fibre product of `Zᵢ` with `Spec κ` over `Tᵢ`: the square obtained by pasting
the presentation of `Wᵢ` with the identification of the common fibre. -/
theorem isPullback_closureFibre_field (i : A.J) :
    IsPullback (A.closureFibreToClosure κ η i)
      (A.closureFibreToFibre κ η i ≫ pullback.fst (impurityFieldMor D κ ≫ D.g) P.f)
      (A.stageComp η i ≫ pullback.fst (A.base i) P.f)
      (impurityFieldMor D κ ≫ yoneda.map (A.proj i)) :=
  (A.isPullback_closureFibre κ η i).paste_vert (A.isPullback_fibreToStage κ i)

/-- The composites `Wᵢ ⟶ Zᵢ ⟶ Zⱼ ⟶ X_{Tⱼ}` and `Wᵢ ⟶ X ×_Y Spec κ ⟶ X_{Tⱼ}` agree. -/
theorem closureFibreMap_cond {i j : A.J} (a : i ⟶ j) :
    (A.closureFibreToClosure κ η i ≫ E.map a) ≫ A.stageComp η j =
      A.closureFibreToFibre κ η i ≫ A.fibreToStage κ j := by
  have h1 : A.closureFibreToClosure κ η i ≫ A.stageComp η i ≫ A.trans a =
      A.closureFibreToFibre κ η i ≫ A.fibreToStage κ i ≫ A.trans a := by
    rw [← Category.assoc, ← Category.assoc, pullback.condition]
  rw [Category.assoc, ← A.naturality_trans η a, h1, A.fibreToStage_comp_trans κ a]

/-- The transition morphism of the system `W`, the base change of the transition morphism of
the system of reduced closures. -/
noncomputable def closureFibreMap {i j : A.J} (a : i ⟶ j) :
    A.closureFibre κ η i ⟶ A.closureFibre κ η j :=
  pullback.lift (A.closureFibreToClosure κ η i ≫ E.map a) (A.closureFibreToFibre κ η i)
    (A.closureFibreMap_cond κ η a)

/-- The transition morphism `Wᵢ ⟶ Wⱼ` lies over the transition morphism `Zᵢ ⟶ Zⱼ`. -/
theorem closureFibreMap_comp_toClosure {i j : A.J} (a : i ⟶ j) :
    A.closureFibreMap κ η a ≫ A.closureFibreToClosure κ η j =
      A.closureFibreToClosure κ η i ≫ E.map a :=
  pullback.lift_fst _ _ _

/-- The transition morphism `Wᵢ ⟶ Wⱼ` commutes with the projections to the common fibre. -/
theorem closureFibreMap_comp_toFibre {i j : A.J} (a : i ⟶ j) :
    A.closureFibreMap κ η a ≫ A.closureFibreToFibre κ η j = A.closureFibreToFibre κ η i :=
  pullback.lift_snd _ _ _

/-- **The system `W`.** -/
noncomputable def closureFibreDiagram : A.J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj i := A.closureFibre κ η i
  map a := A.closureFibreMap κ η a
  map_id i := by
    refine pullback.hom_ext ?_ ?_
    · rw [A.closureFibreMap_comp_toClosure κ η, E.map_id, Category.comp_id, Category.id_comp]
    · rw [A.closureFibreMap_comp_toFibre κ η, Category.id_comp]
  map_comp a b := by
    refine pullback.hom_ext ?_ ?_
    · rw [A.closureFibreMap_comp_toClosure κ η, Category.assoc,
        A.closureFibreMap_comp_toClosure κ η, ← Category.assoc,
        A.closureFibreMap_comp_toClosure κ η, E.map_comp, Category.assoc]
    · rw [A.closureFibreMap_comp_toFibre κ η, Category.assoc,
        A.closureFibreMap_comp_toFibre κ η, A.closureFibreMap_comp_toFibre κ η]

/-- The value of the system `W` at a stage is `Wᵢ`. -/
theorem closureFibreDiagram_obj (i : A.J) :
    (A.closureFibreDiagram κ η).obj i = A.closureFibre κ η i := rfl

/-- The transition morphisms of the system `W` are the morphisms `Wᵢ ⟶ Wⱼ`. -/
theorem closureFibreDiagram_map {i j : A.J} (a : i ⟶ j) :
    (A.closureFibreDiagram κ η).map a = A.closureFibreMap κ η a := rfl

/-- The projection of `Wᵢ` to the common fibre is a closed immersion, being the base change of
the closed immersion `Zᵢ ⟶ X_{Tᵢ}`. -/
theorem isClosedImmersion_closureFibreToFibre
    (hci : ∀ i, IsClosedImmersion B S hS (A.stageComp η i)) (i : A.J) :
    IsClosedImmersion B S hS (A.closureFibreToFibre κ η i) :=
  (isClosedImmersion_isStableUnderBaseChange B S hS).of_isPullback
    (A.isPullback_closureFibre κ η i) (hci i)

/-- Every `Wᵢ` is quasi-compact, being a closed subspace of the common fibre. -/
theorem isQuasiCompactSpace_closureFibre
    (hci : ∀ i, IsClosedImmersion B S hS (A.stageComp η i)) (i : A.J) :
    IsQuasiCompactSpace B S hS (A.closureFibre κ η i) :=
  isQuasiCompactSpace_of_isClosedImmersion B S hS
    (isQuasiCompactSpace_impurityFibre P D κ) (A.closureFibreToFibre κ η i)
    (A.isClosedImmersion_closureFibreToFibre κ η hci i)

/-- Every `Wᵢ` is an algebraic space. -/
theorem isAlgebraicSpace_closureFibre (hE : ∀ i, IsAlgebraicSpace B S hS (E.obj i)) (i : A.J) :
    IsAlgebraicSpace B S hS (A.closureFibre κ η i) :=
  isAlgebraicSpace_pullback B S hS (A.stageComp η i) (A.fibreToStage κ i) (hE i)
    (isAlgebraicSpace_impurityFibre P D κ) (A.isAlgebraicSpace_baseChangeDiagram_obj i)

/-- Every transition morphism of the system `W` is affine: all the `Wᵢ` are closed subspaces of
the single common fibre, compatibly, and a morphism which becomes affine after composing with a
separated morphism is affine. -/
theorem isAffineHom_closureFibreMap
    (hci : ∀ i, IsClosedImmersion B S hS (A.stageComp η i)) {i j : A.J} (a : i ⟶ j) :
    IsAffineHom B S hS (A.closureFibreMap κ η a) := by
  refine isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS
    (A.closureFibreMap κ η a) (A.closureFibreToFibre κ η j) ?_
    (isSeparated_of_isClosedImmersion B S hS _
      (A.isClosedImmersion_closureFibreToFibre κ η hci j))
  rw [A.closureFibreMap_comp_toFibre κ η]
  exact isAffineHom_of_isClosedImmersion B S hS _
    (A.isClosedImmersion_closureFibreToFibre κ η hci i)

/-- Every `Wᵢ` has a point, provided some specialization of `ξᵢ` lies over `tᵢ`. The point of
`Zᵢ` above such a specialization and the unique point of `Spec κ` have the same image in `Tᵢ`,
so Stacks 03H4 produces a point of the fibre product. -/
theorem nonempty_points_closureFibre
    (hκ : κ.class B S hS (yoneda.obj D.T) = D.t)
    (hrange : ∀ i, Set.range (pointsMap B S hS (E.obj i) (A.stageComp η i)) =
      closure {A.stageXi i})
    (hmem : ∀ i, A.stagePoint i ∈
      pointsMap B S hS (pullback (A.base i) P.f) (pullback.fst (A.base i) P.f) ''
        closure {A.stageXi i})
    (i : A.J) : Nonempty (points B S hS (A.closureFibre κ η i)) := by
  obtain ⟨θ, hθcl, hθT⟩ := hmem i
  obtain ⟨z, hz⟩ : θ ∈ Set.range (pointsMap B S hS (E.obj i) (A.stageComp η i)) := by
    rw [hrange i]; exact hθcl
  have hcompat : pointsMap B S hS (E.obj i)
        (A.stageComp η i ≫ pullback.fst (A.base i) P.f) z =
      pointsMap B S hS (yoneda.obj κ.siteObject)
        (impurityFieldMor D κ ≫ yoneda.map (A.proj i))
        ((FieldValuedPoint.tautological B S hS κ).class B S hS
          (yoneda.obj κ.siteObject)) := by
    simp only [pointsMap_comp, Function.comp_apply]
    rw [hz, hθT, FieldValuedPoint.pointsMap_eq_class B S hS κ _, hκ]
  obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS
    (A.isPullback_closureFibre_field κ η i) z _ hcompat
  exact ⟨w⟩

/-! ### The two morphisms out of the limit of the system `W` -/

/-- The projections to the reduced closures, as a morphism of systems. -/
noncomputable def natToClosure : A.closureFibreDiagram κ η ⟶ E where
  app i := A.closureFibreToClosure κ η i
  naturality _ _ a := A.closureFibreMap_comp_toClosure κ η a

/-- The component at a stage of `natToClosure` is the projection `Wᵢ ⟶ Zᵢ`. -/
theorem natToClosure_app (i : A.J) :
    (A.natToClosure κ η).app i = A.closureFibreToClosure κ η i := rfl

/-- The projections to the common fibre, as a morphism of systems to a constant system. -/
noncomputable def natToFibre :
    A.closureFibreDiagram κ η ⟶ (Functor.const A.J).obj (impurityFibre P D κ) where
  app i := A.closureFibreToFibre κ η i
  naturality _ _ a :=
    (A.closureFibreMap_comp_toFibre κ η a).trans (Category.comp_id _).symm

/-- The component at a stage of `natToFibre` is the projection of `Wᵢ` to the common fibre. -/
theorem natToFibre_app (i : A.J) :
    (A.natToFibre κ η).app i = A.closureFibreToFibre κ η i := rfl

/-- The morphism from the limit of the system `W` to the common fibre, obtained from the
projections; being a limit of a constant system, it is independent of the stage used. -/
noncomputable def limitToFibre : limit (A.closureFibreDiagram κ η) ⟶ impurityFibre P D κ :=
  limMap (A.natToFibre κ η) ≫
    limit.π ((Functor.const A.J).obj (impurityFibre P D κ)) (Classical.arbitrary A.J)

/-- The defining equation of `limitToFibre`. -/
theorem limitToFibre_def : A.limitToFibre κ η =
    limMap (A.natToFibre κ η) ≫
      limit.π ((Functor.const A.J).obj (impurityFibre P D κ)) (Classical.arbitrary A.J) :=
  rfl

/-- The projections of a limit of a constant system are all the same morphism: a transition
morphism of the constant system is an identity. -/
theorem limit_π_const_eq (k l : A.J) :
    limit.π ((Functor.const A.J).obj (impurityFibre P D κ)) k =
      limit.π ((Functor.const A.J).obj (impurityFibre P D κ)) l := by
  have h1 : limit.π ((Functor.const A.J).obj (impurityFibre P D κ)) (IsCofiltered.min k l) =
      limit.π ((Functor.const A.J).obj (impurityFibre P D κ)) k :=
    (Category.comp_id _).symm.trans (limit.w _ (IsCofiltered.minToLeft k l))
  have h2 : limit.π ((Functor.const A.J).obj (impurityFibre P D κ)) (IsCofiltered.min k l) =
      limit.π ((Functor.const A.J).obj (impurityFibre P D κ)) l :=
    (Category.comp_id _).symm.trans (limit.w _ (IsCofiltered.minToRight k l))
  rw [← h1, ← h2]

/-- The projection of the limit of the system `W` to a stage, read with its target in the
fibre-product spelling. -/
noncomputable abbrev limitProj (i : A.J) :
    limit (A.closureFibreDiagram κ η) ⟶ A.closureFibre κ η i :=
  limit.π (A.closureFibreDiagram κ η) i

/-- The morphism from the limit of the system `W` to the common fibre factors through every
stage `Wᵢ`. -/
theorem limitToFibre_eq (i : A.J) :
    A.limitToFibre κ η = A.limitProj κ η i ≫ A.closureFibreToFibre κ η i := by
  rw [A.limitToFibre_def κ η, A.limit_π_const_eq κ (Classical.arbitrary A.J) i, limMap_π,
    A.natToFibre_app κ η i]
  rfl

/-- The morphism from the limit of the system `W` to `X_T`. -/
noncomputable def limitToBaseChange : limit (A.closureFibreDiagram κ η) ⟶ D.baseChange :=
  limMap (A.natToClosure κ η) ≫ limMap η ≫ A.limitIso.inv

/-- The defining equation of `limitToBaseChange`. -/
theorem limitToBaseChange_def : A.limitToBaseChange κ η =
    limMap (A.natToClosure κ η) ≫ limMap η ≫ A.limitIso.inv := rfl

/-- The common value, at a stage, of the two composites out of the limit of the system `W`. -/
noncomputable abbrev limitToStage (i : A.J) :
    limit (A.closureFibreDiagram κ η) ⟶ pullback (A.base i) P.f :=
  A.limitProj κ η i ≫ A.closureFibreToClosure κ η i ≫ A.stageComp η i

/-- The morphism from the limit of `W` to `X_T`, followed by the projection to `X_{Tᵢ}`, is
`limitToStage`. -/
theorem limitToBaseChange_comp_stageProj (i : A.J) :
    A.limitToBaseChange κ η ≫ A.stageProj i = A.limitToStage κ η i :=
  have h1 : A.limitToBaseChange κ η ≫ A.stageProj i =
      limMap (A.natToClosure κ η) ≫ limMap η ≫ limit.π A.baseChangeDiagram i :=
    (Category.assoc _ _ _).trans
      (congrArg (fun m ↦ limMap (A.natToClosure κ η) ≫ m)
        ((Category.assoc _ _ _).trans
          (congrArg (fun m ↦ limMap η ≫ m) (A.limitIso_inv_comp_stageProj i))))
  h1.trans
    ((congrArg (fun m ↦ limMap (A.natToClosure κ η) ≫ m) (limMap_π η i)).trans
      (((Category.assoc _ _ _).symm.trans
        (congrArg (fun m ↦ m ≫ A.stageComp η i)
          (limMap_π (A.natToClosure κ η) i))).trans (Category.assoc _ _ _)))

/-- The morphism from the limit of `W` to the common fibre, followed by the morphism to
`X_{Tᵢ}`, is `limitToStage`. -/
theorem limitToFibre_comp_fibreToStage (i : A.J) :
    A.limitToFibre κ η ≫ A.fibreToStage κ i = A.limitToStage κ η i :=
  (congrArg (fun m ↦ m ≫ A.fibreToStage κ i) (A.limitToFibre_eq κ η i)).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun m ↦ A.limitProj κ η i ≫ m) pullback.condition.symm))

/-- The two morphisms out of the limit of the system `W` agree over the test scheme: the
composite to `T` through `X_T` is the composite to `T` through `Spec κ`. -/
theorem limitToBaseChange_comp_toT :
    A.limitToBaseChange κ η ≫ D.toT =
      A.limitToFibre κ η ≫ pullback.fst (impurityFieldMor D κ ≫ D.g) P.f ≫
        impurityFieldMor D κ := by
  refine A.hom_ext_of_proj fun i ↦ ?_
  have hleft : (A.limitToBaseChange κ η ≫ D.toT) ≫ yoneda.map (A.proj i) =
      A.limitToStage κ η i ≫ pullback.fst (A.base i) P.f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ A.limitToBaseChange κ η ≫ m) (A.stageProj_comp_fst i).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun m ↦ m ≫ pullback.fst (A.base i) P.f)
            (A.limitToBaseChange_comp_stageProj κ η i))))
  have hright : (A.limitToFibre κ η ≫ pullback.fst (impurityFieldMor D κ ≫ D.g) P.f ≫
        impurityFieldMor D κ) ≫ yoneda.map (A.proj i) =
      A.limitToStage κ η i ≫ pullback.fst (A.base i) P.f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ A.limitToFibre κ η ≫ m) (Category.assoc _ _ _)).trans
        ((congrArg (fun m ↦ A.limitToFibre κ η ≫ m) (A.fibreToStage_comp_fst κ i).symm).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun m ↦ m ≫ pullback.fst (A.base i) P.f)
              (A.limitToFibre_comp_fibreToStage κ η i)))))
  exact hleft.trans hright.symm

end AffineLimitPresentation

/-! ### Stacks 0CV9 -/

namespace AffineLimitPresentation

variable {P : PrePureSituation.{u, u} B S hS} {D : ImpurityDiagram P}
  (A : AffineLimitPresentation D)

/-- **Stacks 0CV9.** In Situation 0CV6, let `(g : T ⟶ Y, t' ⤳ t, ξ)` be an impurity of `ℱ`
above `y` and let `T = lim_{i} Tᵢ` be a directed limit of affine schemes over `Y`. Then for
some stage `i` the triple `(Tᵢ ⟶ Y, t'ᵢ ⤳ tᵢ, ξᵢ)` is an impurity of `ℱ` above `y`, where the
three points are the images of `t'`, `t` and `ξ` under the canonical projections. -/
@[stacks 0CV9]
theorem exists_isImpurity_stageDiagram (hD : D.IsImpurity) :
    ∃ i : A.J, (A.stageDiagram i).IsImpurity := by
  classical
  obtain ⟨hDass, hDcl⟩ := hD
  by_contra hcon
  have hmem : ∀ i : A.J, A.stagePoint i ∈
      pointsMap B S hS (pullback (A.base i) P.f) (pullback.fst (A.base i) P.f) ''
        closure {A.stageXi i} := by
    intro i
    by_contra hni
    exact hcon ⟨i, A.isRelativeWeakAssassinPoint_stageDiagram hDass i, hni⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : FieldValuedPoint B S hS (yoneda.obj D.T),
      κ.class B S hS (yoneda.obj D.T) = D.t := by
    obtain ⟨q, hq⟩ := Quot.exists_rep D.t
    exact ⟨q, hq⟩
  obtain ⟨E, η, e, hEiso, hE, -, -, heIncl⟩ :=
    exists_iso_limit_reducedClosure_of_limitReduced B S hS A.baseChangeDiagram
      A.isAlgebraicSpace_limit_baseChangeDiagram
      (fun i ↦ A.isAlgebraicSpace_baseChangeDiagram_obj i)
      (fun {i j} a ↦ A.isAffineHom_baseChangeDiagram_map a) A.limitXi
      A.closure_singleton_limitXi
      (fun E η hE hEAffine hηMono hAred ↦
        A.isAlgebraicSpace_and_isReduced_limit_of_mono_natTrans E η hE hEAffine hηMono hAred)
  have hci : ∀ i, IsClosedImmersion B S hS (A.stageComp η i) := by
    intro i
    obtain ⟨eᵢ, hεᵢ⟩ := hEiso i
    have h : IsClosedImmersion B S hS (η.app i) :=
      hεᵢ ▸ isClosedImmersion_comp B S hS _ _
        (isClosedImmersion_of_isIso B S hS eᵢ.hom)
        (isClosedSubspace_reducedClosedSubspace B S hS (A.baseChangeDiagram.obj i)
          (A.isAlgebraicSpace_baseChangeDiagram_obj i) _ isClosed_closure).2
    exact h
  have hrange : ∀ i, Set.range (pointsMap B S hS (E.obj i) (A.stageComp η i)) =
      closure {A.stageXi i} := by
    intro i
    obtain ⟨eᵢ, hεᵢ⟩ := hEiso i
    exact (congrArg (fun m ↦ Set.range (pointsMap B S hS (E.obj i) m)) hεᵢ.symm).trans
      ((range_pointsMap_iso_comp eᵢ _).trans
        ((range_pointsMap_ι_reducedClosedSubspace B S hS _
            (A.isAlgebraicSpace_baseChangeDiagram_obj i) _ isClosed_closure).trans
          (congrArg (fun x ↦ closure {x}) (A.pointsMap_π_limitXi i))))
  obtain ⟨w⟩ : Nonempty (points B S hS (limit (A.closureFibreDiagram κ η))) := by
    rcases A.bound_baseChangeDiagram with ⟨hsize, hhom⟩ | ⟨hsize, ν, hν, hhom, -⟩
    · exact nonempty_points_limit B S hS (A.closureFibreDiagram κ η) hsize hhom
        (fun i ↦ A.isAlgebraicSpace_closureFibre κ η hE i)
        (fun {i j} a ↦ A.isAffineHom_closureFibreMap κ η hci a)
        (fun i ↦ A.isQuasiCompactSpace_closureFibre κ η hci i)
        (fun i ↦ A.nonempty_points_closureFibre κ η hκ hrange hmem i)
    · refine nonempty_points_limit_of_mono B S hS (A.closureFibreDiagram κ η) hsize hν hhom
        (fun i ↦ A.isAlgebraicSpace_closureFibre κ η hE i)
        (fun {i j} a ↦ A.isAffineHom_closureFibreMap κ η hci a) ?_
        (fun i ↦ A.isQuasiCompactSpace_closureFibre κ η hci i)
        (fun i ↦ A.nonempty_points_closureFibre κ η hκ hrange hmem i)
      intro i j a
      change Mono (A.closureFibreMap κ η a)
      let : Mono (A.closureFibreToFibre κ η i) := mono_of_isClosedImmersion B S hS _
        (A.isClosedImmersion_closureFibreToFibre κ η hci i)
      exact mono_of_mono_fac (A.closureFibreMap_comp_toFibre κ η a)
  refine hDcl ⟨pointsMap B S hS (limit (A.closureFibreDiagram κ η))
    (A.limitToBaseChange κ η) w, ?_, ?_⟩
  · have hZ : Set.range (pointsMap B S hS (limit E) (limMap η)) = closure {A.limitXi} :=
      (range_pointsMap_iso_comp e (limMap η)).symm.trans
        ((congrArg (fun m ↦ Set.range (pointsMap B S hS _ m)) heIncl).trans
          (range_pointsMap_ι_reducedClosedSubspace B S hS (limit A.baseChangeDiagram) _
            (closure {A.limitXi}) isClosed_closure))
    have hmemZ : pointsMap B S hS (limit A.baseChangeDiagram) A.limitIso.inv
        (pointsMap B S hS (limit E) (limMap η)
          (pointsMap B S hS (limit (A.closureFibreDiagram κ η))
            (limMap (A.natToClosure κ η)) w)) ∈ closure {D.xi} := by
      have himg := image_closure_subset_closure_image
        (continuous_pointsMap B S hS (F := limit A.baseChangeDiagram) A.limitIso.inv)
        (s := ({A.limitXi} : Set (points B S hS (limit A.baseChangeDiagram))))
      rw [Set.image_singleton, A.pointsMap_limitIso_inv_limitXi] at himg
      refine himg ⟨_, ?_, rfl⟩
      rw [← hZ]
      exact ⟨_, rfl⟩
    refine Eq.mpr ?_ hmemZ
    rw [A.limitToBaseChange_def κ η]
    simp only [pointsMap_comp, Function.comp_apply]
  · rw [← Function.comp_apply (f := pointsMap B S hS D.baseChange D.toT), ← pointsMap_comp,
      A.limitToBaseChange_comp_toT κ η]
    simp only [pointsMap_comp, Function.comp_apply]
    rw [FieldValuedPoint.pointsMap_eq_class B S hS κ _, hκ]

end AffineLimitPresentation

end AlgebraicGeometry.Space

end
