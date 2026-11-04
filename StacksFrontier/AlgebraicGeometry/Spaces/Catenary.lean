module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionFunctionFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart
public import StacksFrontier.Topology.Dimension.Catenary
public import StacksFrontier.Topology.Dimension.DimensionFunctionDescent
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Catenary algebraic spaces and dimension functions

An algebraic space is catenary when its topological space of points is catenary, and
universally catenary when every decent algebraic space locally of finite type over it is
catenary. Over a locally Noetherian, universally catenary base scheme equipped with a
dimension function, an algebraic space locally of finite type carries a dimension function of
its own: at a point it is the base value at the image point plus the relative transcendence
degree there.

## Main definitions

* `AlgebraicGeometry.Space.IsCatenary` is catenarity of an algebraic space.
* `AlgebraicGeometry.Space.IsUniversallyCatenary` is universal catenarity of an algebraic
  space.

## Main results

* `AlgebraicGeometry.Space.isUniversallyCatenary_of_isLocallyOfFiniteType` is the inheritance
  of universal catenarity by an algebraic space locally of finite type over a universally
  catenary one.
* `AlgebraicGeometry.Space.inducedDimensionValue_isDimensionFunction` is the dimension
  function carried by an algebraic space locally of finite type over a locally Noetherian
  universally catenary scheme with a dimension function.

## Implementation notes

The topology on the set of points is `AlgebraicGeometry.Space.pointTopology`, the concrete
construction of the topology of Tag 03BX. It takes no algebraic-space hypothesis, being
defined for every presheaf on the big fppf site; the hypothesis is nevertheless retained as
an argument of `IsCatenary`, since the source states catenarity for an algebraic space and
downstream statements supply it.

Both predicates are abbreviations, so the API for catenary topological spaces
(`IrreducibleClosedsCodim.IsCatenarySpace`) applies directly after unfolding, and the
quantified condition of `IsUniversallyCatenary` is available to clients without an
unfolding lemma. As in the source, the contextual decency and local Noetherianity
assumptions on the base space are kept separate from the conditions themselves: neither
occurs in `IsCatenary`, and the source space of `IsUniversallyCatenary` is required to be a
decent algebraic space.

The dimension function on an algebraic space `X` locally of finite type over a base is
obtained by descent along a surjective étale scheme chart of `X`. On the chart, which is
identified with its scheme of definition by
`AlgebraicGeometry.Space.schemePointsHomeomorph`, the relative dimension of Tag 02JW is a
dimension function; generalizations lift from the space to the chart by Tag 03K2, and two
points of the chart above the same point of the space, one specializing to the other, are
equal by Tag 03K5, so that dimension function descends. Its values are recorded as
`AlgebraicGeometry.Space.inducedDimensionValue`, the base value at the image point plus the
relative transcendence degree of Tag 04NM, the base dimension function being read on the
points of the representable target through clause (1) of Tag 03BX. The target is an arbitrary
object of the site, the structure morphism of `X` being the case of the terminal one.

Tag 0ED5 assumes `X` decent, which Tag 03I8 defines by the equivalent conditions of Tag 03JV.
Two of those readings are available here: `AlgebraicGeometry.Space.IsDecentSpace`, which
spells decency as condition (4) of Tag 03JV — a quasi-compact monomorphism from the spectrum
of a field at every point — and condition `(α)` of Tag 03JX,
`AlgebraicGeometry.Space.HasFiniteChartFibersAtEveryPoint`, finiteness of the fibre of every
affine étale chart above every point. The comparison of the two is exactly the content of
Tag 03JV, which is not proved in this repository, so neither reading yields the other. The
statement is therefore given for condition `(α)`, which is weaker than decency and is all the
argument uses, being precisely the hypothesis of the two specialization results it invokes;
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/Specializations.lean` reads the same source
hypothesis the same way.

## References

* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 04NK](https://stacks.math.columbia.edu/tag/04NK)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 0ED4](https://stacks.math.columbia.edu/tag/0ED4)
* [Stacks Project, Tag 0ED5](https://stacks.math.columbia.edu/tag/0ED5)
* [Stacks Project, Tag 0ED7](https://stacks.math.columbia.edu/tag/0ED7)
* [Stacks Project, Tag 0ED8](https://stacks.math.columbia.edu/tag/0ED8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0ED4.** An algebraic space is catenary when its space of points, with the
topology of Tag 03BX, is a catenary topological space. -/
@[stacks 0ED4]
abbrev IsCatenary (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hX : IsAlgebraicSpace B S hS X) : Prop :=
  @IrreducibleClosedsCodim.IsCatenarySpace (points B S hS X) (pointTopology B S hS X)

/-- **Stacks 0ED7.** An algebraic space is universally catenary when every decent algebraic
space locally of finite type over it is catenary. -/
@[stacks 0ED7]
abbrev IsUniversallyCatenary (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
    (_hYdecent : IsDecentSpace B S hS Y) (f : Y ⟶ X),
    IsLocallyOfFiniteType B S hS f → IsCatenary B S hS Y hY

/-- **Stacks 0ED8.** An algebraic space locally of finite type over a universally catenary
algebraic space is universally catenary.

Universal catenarity of the target already quantifies over all decent algebraic spaces
locally of finite type over it, so the source needs no decency or local Noetherianity
hypothesis: a decent space locally of finite type over the source is locally of finite type
over the target by Stacks 03XG. -/
@[stacks 0ED8]
theorem isUniversallyCatenary_of_isLocallyOfFiniteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hXcat : IsUniversallyCatenary B S hS X) (f : Y ⟶ X)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsUniversallyCatenary B S hS Y := fun Z hZ hZdecent g hg =>
  hXcat Z hZ hZdecent (g ≫ f) (isLocallyOfFiniteType_comp B S hS hZ hY hX g f hg hf)

/-! ### The dimension function of an algebraic space of finite type over a scheme -/

attribute [local instance] pointTopology

/-- The relative transcendence degree of Stacks 04NM at a point of an algebraic space,
computed on a given étale chart whose target chart is the identity: it is the transcendence
degree of the residue field extension of the induced morphism of schemes. -/
private theorem hasTranscendenceDegreeAt_chart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T U : BigFppfOver B S hS} (f : X ⟶ yoneda.obj T)
    (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (h : U ⟶ T) (hcomm : yoneda.map h ≫ 𝟙 (yoneda.obj T) = φ ≫ f)
    (a : points B S hS (yoneda.obj U)) :
    HasTranscendenceDegreeAt B S hS f (pointsMap B S hS (yoneda.obj U) φ a)
      (Cardinal.toENat (@Algebra.trdeg
        (((BigFppfOver.toScheme B S hS).obj T).residueField
          ((BigFppfOver.toScheme B S hS).map h (pointsToScheme B S hS U a)))
        (((BigFppfOver.toScheme B S hS).obj U).residueField (pointsToScheme B S hS U a))
        _ _ (((BigFppfOver.toScheme B S hS).map h).residueFieldMap
          (pointsToScheme B S hS U a)).hom.toAlgebra)) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep a
  refine (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS _
    (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget _) f _
    { U := U
      V := T
      a := φ
      b := 𝟙 (yoneda.obj T)
      h := h
      a_etale := hφ
      b_etale := presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj T))
      comm := hcomm
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := rfl }).mpr ?_
  exact MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom
    ((BigFppfOver.toScheme B S hS).map h) (schemePoint B S hS U p)

/-- **Stacks 0ED5.** Let `T` be an object of the big fppf site over `S` whose underlying
scheme is locally Noetherian and universally catenary, and let `δ` be a dimension function on
that scheme. Let `X` be an algebraic space over `S`, locally of finite type over `T`, above
every point of which every étale chart by an affine scheme has a finite fibre. Then the
function sending a point `x` of `X` to the value of `δ` at the image of `x` plus the relative
transcendence degree of `x` over that image is a dimension function on the points of `X`.

The finiteness hypothesis is condition `(α)` of Stacks 03JX, which is weaker than the
condition (1) of Stacks 03JV through which Stacks 03I8 defines a decent algebraic space, and
which is all that the argument uses. Taking for `T` the terminal object
`Over.mk (𝟙 (B.obj hS))`, whose underlying scheme is `S`, gives the statement for the
structure morphism of `X`. -/
@[stacks 0ED5 "with decency read as condition (alpha) of Stacks 03JX",
  sga "6 X 1.5" "(1.5.2) is a dim. fn"]
theorem inducedDimensionValue_isDimensionFunction
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
    (hcat : Scheme.IsUniversallyCatenary ((BigFppfOver.toScheme B S hS).obj T))
    (δ : TopologicalSpace.DimensionFunction ((BigFppfOver.toScheme B S hS).obj T))
    (hX : IsAlgebraicSpace B S hS X)
    (hfib : HasFiniteChartFibersAtEveryPoint B S hS X)
    (f : X ⟶ yoneda.obj T) (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ d : TopologicalSpace.DimensionFunction (points B S hS X), ∀ x : points B S hS X,
      d x = inducedDimensionValue B S hS
        (fun y ↦ δ (pointsToScheme B S hS T y)) f x := by
  classical
  obtain ⟨U, φ, hφsurj, hφetale⟩ := hX.exists_atlas
  -- The chart of `f` as a morphism of the site, and its local finite-typeness.
  obtain ⟨h, hmap⟩ : ∃ h : U ⟶ T, yoneda.map h = φ ≫ f :=
    ⟨yoneda.preimage (φ ≫ f), yoneda.map_preimage _⟩
  have hcomm : yoneda.map h ≫ 𝟙 (yoneda.obj T) = φ ≫ f := by rw [Category.comp_id, hmap]
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    hf U T φ (𝟙 (yoneda.obj T)) h hφetale
      (presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj T))) hcomm
  -- The dimension function on the chart, Stacks 02JW, transported to its points.
  obtain ⟨dA, hdA⟩ := Stacks.Chow.relativeDimension_isDimensionFunction hcat δ
    ((BigFppfOver.toScheme B S hS).map h)
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) φ) :=
    (surjective_iff_surjective_pointsMap B S hS X hX U φ).mp hφsurj
  -- The value of the transported function at a point of the chart is the prescribed value at
  -- its image.
  have hform : ∀ a : points B S hS (yoneda.obj U),
      (dA.comp (schemePointsHomeomorph B S hS U).isOpenEmbedding) a =
        inducedDimensionValue B S hS (fun y ↦ δ (pointsToScheme B S hS T y)) f
          (pointsMap B S hS (yoneda.obj U) φ a) := by
    intro a
    have himage : pointsMap B S hS X f (pointsMap B S hS (yoneda.obj U) φ a) =
        pointsMap B S hS (yoneda.obj U) (yoneda.map h) a := by
      rw [hmap, pointsMap_comp_apply]
    rw [TopologicalSpace.DimensionFunction.comp_apply, hdA, schemePointsHomeomorph_apply,
      inducedDimensionValue_eq B S hS hX (isAlgebraicSpace_yoneda B S hS T) _ f hf _ _
        (hasTranscendenceDegreeAt_chart B S hS f φ hφetale h hcomm a),
      himage, pointsToScheme_pointsMap]
    simp only [Stacks.Chow.relativeDimension, Cardinal.toNat_toENat]
  -- The three hypotheses of the descent, the last two being Stacks 03K5 and Stacks 03K2.
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dimensionFunction_of_descends
    (pointsMap B S hS (yoneda.obj U) φ)
    (dA.comp (schemePointsHomeomorph B S hS U).isOpenEmbedding)
    (continuous_pointsMap B S hS φ) hsurj
    (fun a b hab ↦ by rw [hform a, hform b, hab])
    (fun a b hab heq ↦ (eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX
      hfib U φ hφetale b a heq.symm hab).symm)
    (fun _ x hs b hb ↦ exists_specializes_pointsMap_eq_of_isEtale B S hS hX hs (hfib x) U φ
      hφetale b hb)
  refine ⟨d, fun x ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hsurj x
  rw [hd a]
  exact hform a

end AlgebraicGeometry.Space

end
