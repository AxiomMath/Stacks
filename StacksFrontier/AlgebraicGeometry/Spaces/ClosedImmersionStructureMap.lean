module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# The structure map of a closed immersion of algebraic spaces is surjective

Let `f : X ⟶ Y` be a closed immersion of algebraic spaces over a scheme `S`. Stacks 03MB
asserts, among other things, that the structure map

`f♯ : 𝒪_Y ⟶ f_*𝒪_X`

of `AlgebraicGeometry.Space.structureSharp` is *surjective*, that is locally surjective as a
morphism of sheaves on the small étale site of `Y`. That clause is proved here.

The two ingredients are both about an arbitrary *representable* morphism, and are stated at that
generality. The first is that the direct image of a sheaf on the small étale site is computed, over
an étale chart `V` of `Y`, by the single chart `X ×_Y V`: the sections of `f_*` over `V` are a
limit over the étale charts of `X` above `X ×_Y V` (`AlgebraicGeometry.Space.chartIsLimit`), and
when `f` is representable that indexing category has an *initial* object, namely the base-changed
chart `AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4). The second is that the
structure map, read through that initial object, is literally pullback of regular functions along
the cartesian projection `X ×_Y V ⟶ V` of schemes.

So the structure map is surjective over `V` as soon as `Γ(V) ⟶ Γ(X ×_Y V)` is, which for a closed
immersion is the case whenever `V` is affine
(`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine`). Since the affine charts
are a dense subsite of the small étale site (Stacks 04JS,
`AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`), every chart is covered by
affine ones and local surjectivity follows.

## Main definitions

* `AlgebraicGeometry.Space.chartBaseChangeArrow`: for a representable `f` and an étale chart `V`
  of `Y`, the base-changed chart `X ×_Y V` viewed as an object of the category indexing the limit
  that computes the sections of the direct image over `V`.

## Main results

* `AlgebraicGeometry.Space.chartBaseChangeArrowIsInitial`: that object is initial, so the limit
  computing the sections of the direct image over `V` is attained at the base-changed chart alone.
* `AlgebraicGeometry.Space.chartBaseChangeMap_chartBaseChangeArrow`: the morphism of schemes it
  induces is the cartesian projection `X ×_Y V ⟶ V`.
* `AlgebraicGeometry.Space.surjective_structureMapApp`: the structure map is surjective over `V`
  as soon as pullback of regular functions along that projection is.
* `AlgebraicGeometry.Space.isLocallySurjective_structureSharp` is the surjectivity clause of
  Stacks 03MB, the surjectivity of the structure map of a closed immersion, and
  `AlgebraicGeometry.Space.epi_structureSharp` the epimorphism it gives.

## Implementation notes

The initial object is produced from the comparison isomorphism
`AlgebraicGeometry.Space.smallBaseChangeComparisonIso` between the two base changes of a chart
together with full faithfulness of the comparison functor of Stacks 03G1: a chart of `X` over
`X ×_Y V` is a morphism of algebraic spaces into `X ×_Y V`, which the isomorphism turns into a
morphism into the base-changed chart, and full faithfulness descends it to a morphism of charts.

Surjectivity of the structure map over `V` is deduced from surjectivity at the initial object by
`AlgebraicGeometry.Space.chartProjection_ext`, every projection of the limit being the projection
at the initial object followed by a restriction.

`AlgebraicGeometry.Space.chartBaseChangeArrow` is an `abbrev` on purpose. Its underlying chart of
`X` has to be visible as `(smallBaseChange B S hS f hf).obj V` for the statement of
`AlgebraicGeometry.Space.chartBaseChangeMap_chartBaseChangeArrow` to typecheck at all: the two
sides of that equation are morphisms between the objects of the site underlying that chart and
`V`, and with a `def` the structured arrow's `right` field does not reduce.

The surjectivity proved is `CategoryTheory.Sheaf.IsLocallySurjective`, which is what "surjective"
means for a morphism of sheaves and is the hypothesis that the change-of-rings results consume;
`CategoryTheory.Sheaf.epi_of_isLocallySurjective` turns it into an epimorphism, of sheaves of rings
and of the underlying sheaves of sets.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The base-changed chart is initial among charts above `X ×_Y V` -/

/-- For a representable morphism `f : X ⟶ Y` and an étale chart `V` of `Y`, the base-changed
chart `X ×_Y V` of Stacks 03G2, part (4), viewed as an object of the category of étale charts of
`X` above `X ×_Y V` — the category over which
`AlgebraicGeometry.Space.chartIsLimit` computes the sections of the direct image over `V`.

This is an `abbrev` so that its underlying chart stays visible as
`(smallBaseChange B S hS f hf).obj V`; see the implementation notes. -/
abbrev chartBaseChangeArrow (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS Y.1) :
    StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op :=
  StructuredArrow.mk (Y := op ((smallBaseChange B S hS f hf).obj V))
    (smallBaseChangeComparisonIso B S hS f hf V).hom.op

/-- Every étale chart of `X` above `X ×_Y V` receives a morphism from the base-changed chart: the
structure morphism of the chart becomes, through
`AlgebraicGeometry.Space.smallBaseChangeComparisonIso`, a morphism of algebraic spaces into the
base-changed chart, and the comparison functor of Stacks 03G1 is full. -/
def chartBaseChangeArrowHom (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    chartBaseChangeArrow B S hS f hf V ⟶ j :=
  haveI := comparisonFunctor_full B S hS X
  StructuredArrow.homMk
    ((comparisonFunctor B S hS X).preimage
      (j.hom.unop ≫ (smallBaseChangeComparisonIso B S hS f hf V).inv)).op (by
    apply Quiver.Hom.unop_inj
    change (comparisonFunctor B S hS X).map ((comparisonFunctor B S hS X).preimage
          (j.hom.unop ≫ (smallBaseChangeComparisonIso B S hS f hf V).inv)) ≫
        (smallBaseChangeComparisonIso B S hS f hf V).hom = j.hom.unop
    rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- **The base-changed chart is initial.** For a representable morphism `f : X ⟶ Y` and an étale
chart `V` of `Y`, the base-changed chart `X ×_Y V` is an initial object of the category of étale
charts of `X` above `X ×_Y V`. So the sections of the direct image of a sheaf along `f` over `V`,
a limit over that category, are the sections over the single chart `X ×_Y V`.

Uniqueness of the morphism is faithfulness of the comparison functor of Stacks 03G1, the structure
morphism of the base-changed chart being an isomorphism. -/
def chartBaseChangeArrowIsInitial (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS Y.1) : IsInitial (chartBaseChangeArrow B S hS f hf V) := by
  have := comparisonFunctor_faithful B S hS X
  have : IsIso ((chartBaseChangeArrow B S hS f hf V).hom.unop) :=
    inferInstanceAs (IsIso (smallBaseChangeComparisonIso B S hS f hf V).hom)
  refine IsInitial.ofUniqueHom (chartBaseChangeArrowHom B S hS f hf V) (fun j m => ?_)
  apply StructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply (comparisonFunctor B S hS X).map_injective
  have hm := congrArg Quiver.Hom.unop (StructuredArrow.w m)
  have hd := congrArg Quiver.Hom.unop
    (StructuredArrow.w (chartBaseChangeArrowHom B S hS f hf V j))
  change (comparisonFunctor B S hS X).map m.right.unop ≫ _ = j.hom.unop at hm
  change (comparisonFunctor B S hS X).map
    (chartBaseChangeArrowHom B S hS f hf V j).right.unop ≫ _ = j.hom.unop at hd
  exact (cancel_mono _).mp (hm.trans hd.symm)

/-- The morphism of schemes induced by the base-changed chart is the cartesian projection
`X ×_Y V ⟶ V` of `AlgebraicGeometry.Space.smallBaseChange_projection`. -/
theorem chartBaseChangeMap_chartBaseChangeArrow (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    chartBaseChangeMap B S hS f V (chartBaseChangeArrow B S hS f hf V) = hf.snd V.1.hom := by
  apply yoneda.map_injective
  rw [yoneda_map_chartBaseChangeMap]
  exact congrArg (·.hom) (smallBaseChangeComparisonIso_hom_projection B S hS f hf V)

/-! ### Surjectivity of the structure map over a chart -/

/-- The projections of the limit computing the sections of the direct image of the structure sheaf
over an étale chart `V` of `Y` are compatible with morphisms of charts of `X` above `X ×_Y V`: this
is the cone condition, read on elements. -/
theorem chartProjection_naturality (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {j₁ j₂ : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op}
    (φ : j₁ ⟶ j₂)
    (t : ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).obj
      (op (chartBaseChange B S hS f V))) :
    (chartProjection B S hS f V j₂).app (structureSetSheaf B S hS X) t =
      (structureSetSheaf B S hS X).obj.map φ.right
        ((chartProjection B S hS f V j₁).app (structureSetSheaf B S hS X) t) := by
  rw [chartProjection_app_apply, chartProjection_app_apply]
  exact (congrArg (fun k => k t) (((Functor.RightExtension.mk _
    ((comparisonFunctor B S hS X).op.ranCounit.app
      (structureSetSheaf B S hS X).obj)).coneAt
    (op (chartBaseChange B S hS f V))).w φ)).symm

/-- The projection to the base-changed chart is injective on sections of the direct image. -/
private theorem injective_chartProjection_chartBaseChangeArrow_aux (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    Function.Injective ((chartProjection B S hS f V (chartBaseChangeArrow B S hS f hf V)).app
      (structureSetSheaf B S hS X)) := by
  intro a b hab
  refine chartProjection_ext B S hS f V fun j => ?_
  refine (chartProjection_naturality B S hS f V
    (chartBaseChangeArrowHom B S hS f hf V j) a).trans ?_
  refine Eq.trans ?_ (chartProjection_naturality B S hS f V
    (chartBaseChangeArrowHom B S hS f hf V j) b).symm
  exact congrArg ((structureSetSheaf B S hS X).obj.map
    (chartBaseChangeArrowHom B S hS f hf V j).right) hab

/-- For a representable morphism `f : X ⟶ Y`, the structure map is surjective on sections over an
étale chart `V` of `Y` as soon as pullback of regular functions along the cartesian projection
`X ×_Y V ⟶ V` is surjective.

A section of the direct image over `V` is determined by its projections to the étale charts of `X`
above `X ×_Y V`, and all of those are determined by the projection to the base-changed chart, which
is initial by `AlgebraicGeometry.Space.chartBaseChangeArrowIsInitial`. -/
theorem surjective_structureMapApp (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS Y.1)
    (h : Function.Surjective
      (chartPullback B S hS f V (chartBaseChangeArrow B S hS f hf V))) :
    Function.Surjective (structureMapApp B S hS f V) := by
  intro t
  obtain ⟨g, hg⟩ := h ((chartProjection B S hS f V (chartBaseChangeArrow B S hS f hf V)).app
    (structureSetSheaf B S hS X) t)
  exact ⟨g, injective_chartProjection_chartBaseChangeArrow_aux B S hS f hf V
    ((chartProjection_structureMapApp B S hS f V _ g).trans hg)⟩

/-- For a closed immersion `f : X ⟶ Y` of algebraic spaces and an étale chart `V` of `Y` whose
underlying scheme is affine, the structure map is surjective on sections over `V`.

The cartesian projection `X ×_Y V ⟶ V` is a closed immersion of schemes with affine target, so
pullback of regular functions along it is surjective by
`AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine`. -/
theorem surjective_structureMapApp_of_isAffine (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)) :
    Function.Surjective (structureMapApp B S hS f V) := by
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd V.1.hom)) := hf.property_snd V.1.hom
  refine surjective_structureMapApp B S hS f hf.rep V ?_
  rw [chartPullback, chartBaseChangeMap_chartBaseChangeArrow, Scheme.Γ_map_op]
  exact (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map (hf.rep.snd V.1.hom))).2

/-! ### Surjectivity of the structure map -/

/-- The structure map of a closed immersion is locally surjective in its right Kan extension form
`AlgebraicGeometry.Space.structureSharpRan`: every chart is covered by affine charts, over which
the map on sections is surjective. -/
theorem isLocallySurjective_structureSharpRan (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Sheaf.IsLocallySurjective (structureSharpRan B S hS f) := by
  have : (AffineEtale.inclusion B S hS Y.1).IsCoverDense (SmallEtale.topology B S hS Y.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2.isCoverDense'
  refine ⟨fun {V} s => ?_⟩
  refine (SmallEtale.topology B S hS Y.1).superset_covering ?_
    ((AffineEtale.inclusion B S hS Y.1).is_cover_of_isCoverDense
      (SmallEtale.topology B S hS Y.1) V)
  rintro W g ⟨⟨A, l, m, hfac⟩⟩
  refine hfac ▸ (Presheaf.imageSieve (structureSharpRan B S hS f).hom s).downward_closed ?_ l
  exact surjective_structureMapApp_of_isAffine B S hS f hf A.1 A.2 _

/-- **Stacks 03MB, surjectivity of the structure map.** For a closed immersion `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8 is
surjective: it is a locally surjective morphism of sheaves of rings on the small étale site
of `Y`. -/
theorem isLocallySurjective_structureSharp (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) :
    Sheaf.IsLocallySurjective (structureSharp B S hS f) := by
  have := isLocallySurjective_structureSharpRan B S hS f hf
  have : Sheaf.IsLocallySurjective (pullbackRingSheafMapOfNatTrans
      (SmallEtale.topology B S hS Y.1) (structureRingSheaf B S hS X)
      (smallEtaleDirectImageRanIso B S hS f).inv) := by
    refine (Presheaf.isLocallySurjective_iff_whisker_forget _ _).2 ?_
    change Presheaf.IsLocallySurjective _ ((sheafCompose (SmallEtale.topology B S hS Y.1)
      (forget RingCat.{u})).map (pullbackRingSheafMapOfNatTrans
        (SmallEtale.topology B S hS Y.1) (structureRingSheaf B S hS X)
        (smallEtaleDirectImageRanIso B S hS f).inv)).hom
    rw [ringSheafMap_pullbackRingSheafMapOfNatTrans]
    exact Sheaf.isLocallySurjective_of_iso ((smallEtaleDirectImageRanIso B S hS f).inv.app
      ((structureRingSheaf B S hS X).ringSheaf))
  exact Sheaf.isLocallySurjective_comp _ _

/-- The structure map of a closed immersion of algebraic spaces is an epimorphism of sheaves of
rings on the small étale site of the target. This is the epimorphism form of **Stacks 03MB**'s
surjectivity clause, `AlgebraicGeometry.Space.isLocallySurjective_structureSharp`. -/
theorem epi_structureSharp (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f.hom) :
    Epi (structureSharp B S hS f) :=
  have := isLocallySurjective_structureSharp B S hS f hf
  inferInstance

/-! ### Injectivity of the structure map on chart sections -/

/-- For a representable morphism the projection of the sections of the direct image over an
étale chart `V` of the target to the sections over the base-changed chart `X ×_Y V` is
injective: the base-changed chart is initial among the charts of `X` above `X ×_Y V`, so every
projection factors through it, and the sections over `V` are the limit of those. -/
theorem injective_chartProjection_chartBaseChangeArrow (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    Function.Injective ((chartProjection B S hS f V (chartBaseChangeArrow B S hS f hf V)).app
      (structureSetSheaf B S hS X)) :=
  injective_chartProjection_chartBaseChangeArrow_aux B S hS f hf V

/-- For a representable morphism `f : X ⟶ Y` the structure map is injective on sections over an
étale chart `V` of `Y` exactly when pullback of regular functions along the cartesian
projection `X ×_Y V ⟶ V` of schemes is injective. -/
theorem injective_structureMapApp_iff (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    Function.Injective (structureMapApp B S hS f V) ↔
      Function.Injective (Scheme.Γ.map
        ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op).hom := by
  have hcomp (g) : (chartProjection B S hS f V
      (chartBaseChangeArrow B S hS f hf V)).app (structureSetSheaf B S hS X)
        (structureMapApp B S hS f V g) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op).hom g := by
    refine (chartProjection_structureMapApp B S hS f V
      (chartBaseChangeArrow B S hS f hf V) g).trans ?_
    rw [chartPullback, chartBaseChangeMap_chartBaseChangeArrow]
    rfl
  exact ((injective_chartProjection_chartBaseChangeArrow B S hS f hf V).of_comp_iff _).symm.trans
    (iff_of_eq (congrArg Function.Injective (funext hcomp)))

/-- For a representable morphism the structure map is injective on sections over an étale
chart `V` of the target exactly when pullback of regular functions along the cartesian
projection `X ×_Y V ⟶ V` is injective on global sections. -/
theorem injective_structureMapApp_iff_appTop (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1) :
    Function.Injective (structureMapApp B S hS f V) ↔
      Function.Injective ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop.hom := by
  rw [injective_structureMapApp_iff B S hS f hf V, Scheme.Γ_map_op]
  exact Iff.rfl

end AlgebraicGeometry.Space

end
