module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# The relative weak assassin on an étale chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `F` be an
`𝒪_X`-module and let `x` be a point of `X` with image `y`. Membership of `x` in the relative
weak assassin `WeakAss_{X/Y}(F)` is tested on the fibre of `f` over a field-valued
representative of `y`: it asks for a point of that fibre above `x` which is weakly associated
to the restriction of `F` there. The test may be read at a single such representative, and
then in two strengths — *some* point of the fibre above `x` is weakly associated, or *every*
one is — and over the residue field of a point of an étale scheme chart of `Y` above `y`
these are the chart conditions of Stacks 0CUZ.

The fibre condition is insensitive to an étale morphism over `Y`: for `φ : X' ⟶ X` étale and a
point `x'` of `X'` above `x`, the fibre of `φ ≫ f` over a representative of `y` maps to the
fibre of `f` over the same representative by an étale morphism, that square is cartesian, and
the restriction of `φ^*F` to the one fibre is the pullback of the restriction of `F` to the
other. Weak association is invariant under étale pullback by Stacks 0CUU, and a point of the
smaller fibre above a prescribed pair of points exists by Stacks 03H4, so each strength of the
condition transfers in both directions. This is the chart-independence that the conditions
(1) to (4) of Stacks 0CUZ express.

## Main definitions

* `AlgebraicGeometry.Space.IsWeaklyAssociatedOnFibre`: some point of the fibre of `f` over a
  field-valued point of `Y` above `x` is weakly associated to the restriction of `F`.
* `AlgebraicGeometry.Space.IsWeaklyAssociatedOnFibreEvery`: every such point is.
* `AlgebraicGeometry.Space.IsWeaklyAssociatedOnSomeSchemeChartFibre` and
  `AlgebraicGeometry.Space.IsWeaklyAssociatedOnEverySchemeChartFibre`: conditions (1) and (2)
  of Stacks 0CUZ, the two conditions read over the residue field of a point of an étale scheme
  chart of `Y` above `y`.
* `AlgebraicGeometry.Space.fibreAtFieldValuedPointMap`: the morphism of fibres over a
  field-valued point of `Y` induced by a morphism over `Y`.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedOnFibre_modulePullback_iff` and
  `AlgebraicGeometry.Space.isWeaklyAssociatedOnFibreEvery_modulePullback_iff`: both strengths
  of the fibre condition are invariant under an étale morphism over `Y`.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_modulePullback_iff`: the relative
  weak assassin of `φ^*F` along `φ ≫ f` is the preimage of the relative weak assassin of `F`
  along `f`, for `φ` étale.
* `AlgebraicGeometry.Space.isWeaklyAssociatedOnFibre_of_every`: at a field-valued
  representative of the image of `x`, the every-point condition implies the some-point
  condition, because the fibre carries a point above `x`.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_someSchemeChart` and
  `AlgebraicGeometry.Space.isWeaklyAssociatedOnSomeSchemeChartFibre_of_every`: condition (1)
  of Stacks 0CUZ implies condition (5), and condition (2) implies condition (1).

## Implementation notes

The fibre over a field-valued point and its projection to the source are
`AlgebraicGeometry.Space.fibreAtFieldValuedPoint` and
`AlgebraicGeometry.Space.fibreAtFieldValuedPointProjection`, and the field-valued condition,
which is condition (5) of Stacks 0CUZ, is
`AlgebraicGeometry.Space.IsRelativeWeaklyAssociatedPoint`. The chart conditions are stated at
the canonical field-valued representative
`AlgebraicGeometry.Space.schemePointRepresentative` of the chosen scheme point, that is over
its residue field, which is what the source writes `X_v`.

That the fibre of `f` over a field-valued point `p` carries a point above every point of `X`
whose image is the class of `p` is Stacks 0AC8, in the form
`AlgebraicGeometry.Space.range_pointsMap_fibre_fieldMorphism`.

The comparison of the restriction of `φ^*F` with the pullback of the restriction of `F` is the
composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU on both
legs of the cartesian square, which commute by construction. The module universe is that of
the structure rings throughout, since Stacks 0CUU is available there.

## References

* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y : AlgebraicSpaces B S hS}

/-! ### The two strengths of the fibre condition -/

/-- Some point of the fibre of `f : X ⟶ Y` over a field-valued point `p` of `Y` lying above
`x` is weakly associated to the restriction of `F` to that fibre. -/
noncomputable def IsWeaklyAssociatedOnFibre (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (p : FieldValuedPoint B S hS Y.1) (x : points B S hS X.1) : Prop :=
  ∃ θ : points B S hS (fibreAtFieldValuedPoint B S hS f p).1,
    pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1
        (fibreAtFieldValuedPointProjection B S hS f p).hom θ = x ∧
      IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F) θ

/-- Every point of the fibre of `f : X ⟶ Y` over a field-valued point `p` of `Y` lying above
`x` is weakly associated to the restriction of `F` to that fibre. -/
noncomputable def IsWeaklyAssociatedOnFibreEvery (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (p : FieldValuedPoint B S hS Y.1)
    (x : points B S hS X.1) : Prop :=
  ∀ θ : points B S hS (fibreAtFieldValuedPoint B S hS f p).1,
    pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1
        (fibreAtFieldValuedPointProjection B S hS f p).hom θ = x →
      IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F) θ

/-- The relative weak assassin is the some-point condition on the fibre over some field-valued
representative of the image point. -/
theorem isRelativeWeaklyAssociatedPoint_iff_exists (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) :
    IsRelativeWeaklyAssociatedPoint B S hS f F x ↔
      ∃ p : FieldValuedPoint B S hS Y.1,
        p.class B S hS Y.1 = pointsMap B S hS X.1 f.hom x ∧
          IsWeaklyAssociatedOnFibre B S hS f F p x :=
  Iff.rfl

/-- The some-point condition on the fibre over a field-valued representative of the image of
`x` places `x` in the relative weak assassin. -/
theorem isRelativeWeaklyAssociatedPoint_of_isWeaklyAssociatedOnFibre (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) {p : FieldValuedPoint B S hS Y.1}
    {x : points B S hS X.1} (hp : p.class B S hS Y.1 = pointsMap B S hS X.1 f.hom x)
    (h : IsWeaklyAssociatedOnFibre B S hS f F p x) :
    IsRelativeWeaklyAssociatedPoint B S hS f F x :=
  ⟨p, hp, h⟩

/-- If the image of `x` under `|f|` is the class of a field-valued point `p` of `Y`, then the fibre
of `f` over `p` carries a point above `x`. -/
theorem exists_point_fibre_of_pointsMap_eq_class (f : X ⟶ Y)
    {p : FieldValuedPoint B S hS Y.1} {x : points B S hS X.1}
    (hp : p.class B S hS Y.1 = pointsMap B S hS X.1 f.hom x) :
    ∃ θ : points B S hS (fibreAtFieldValuedPoint B S hS f p).1,
      pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1
        (fibreAtFieldValuedPointProjection B S hS f p).hom θ = x := by
  have hmem : x ∈ Set.range (pointsMap B S hS
      (pullback f.hom (fieldMorphism B S hS Y.1 p))
      (pullback.fst f.hom (fieldMorphism B S hS Y.1 p))) := by
    rw [range_pointsMap_fibre_fieldMorphism B S hS f.hom p]
    exact hp.symm
  exact hmem

/-- At a field-valued representative of the image of `x`, the every-point condition on the
fibre implies the some-point condition: the fibre carries a point above `x`. -/
theorem isWeaklyAssociatedOnFibre_of_every (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    {p : FieldValuedPoint B S hS Y.1} {x : points B S hS X.1}
    (hp : p.class B S hS Y.1 = pointsMap B S hS X.1 f.hom x)
    (h : IsWeaklyAssociatedOnFibreEvery B S hS f F p x) :
    IsWeaklyAssociatedOnFibre B S hS f F p x := by
  obtain ⟨θ, hθ⟩ := exists_point_fibre_of_pointsMap_eq_class B S hS f hp
  exact ⟨θ, hθ, h θ hθ⟩

/-! ### The morphism of fibres of a morphism over the target -/

/-- The morphism of fibres over a field-valued point `p` of `Y` induced by a morphism
`φ : X' ⟶ X` over `Y`: the base change of `φ` along the projection from the fibre of `f`. -/
noncomputable def fibreAtFieldValuedPointMap (φ : X' ⟶ X) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y.1) :
    fibreAtFieldValuedPoint B S hS (φ ≫ f) p ⟶ fibreAtFieldValuedPoint B S hS f p :=
  ObjectProperty.homMk
    (pullback.lift (pullback.fst (φ ≫ f).hom (fieldMorphism B S hS Y.1 p) ≫ φ.hom)
      (pullback.snd (φ ≫ f).hom (fieldMorphism B S hS Y.1 p))
      (by rw [Category.assoc]; exact pullback.condition))

/-- The morphism of fibres is compatible with the projections to the sources. -/
theorem fibreAtFieldValuedPointMap_comp_projection (φ : X' ⟶ X) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y.1) :
    fibreAtFieldValuedPointMap B S hS φ f p ≫ fibreAtFieldValuedPointProjection B S hS f p =
      fibreAtFieldValuedPointProjection B S hS (φ ≫ f) p ≫ φ :=
  (ObjectProperty.fullyFaithfulι _).map_injective (pullback.lift_fst _ _ _)

/-- The square comparing the fibre of `φ ≫ f` over a field-valued point of `Y` with the fibre
of `f` over the same point is cartesian over `φ`, read on the underlying presheaves. -/
theorem isPullback_fibreAtFieldValuedPointMap_hom (φ : X' ⟶ X) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y.1) :
    IsPullback (fibreAtFieldValuedPointProjection B S hS (φ ≫ f) p).hom
      (fibreAtFieldValuedPointMap B S hS φ f p).hom φ.hom
      (fibreAtFieldValuedPointProjection B S hS f p).hom := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback f.hom (fieldMorphism B S hS Y.1 p))
  rw [show (fibreAtFieldValuedPointMap B S hS φ f p).hom ≫
        pullback.snd f.hom (fieldMorphism B S hS Y.1 p)
      = pullback.snd (φ ≫ f).hom (fieldMorphism B S hS Y.1 p) from pullback.lift_snd _ _ _]
  exact IsPullback.of_hasPullback (φ ≫ f).hom (fieldMorphism B S hS Y.1 p)

/-- The comparison square of fibres is cartesian in the category of algebraic spaces. -/
theorem isPullback_fibreAtFieldValuedPointMap (φ : X' ⟶ X) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y.1) :
    IsPullback (fibreAtFieldValuedPointProjection B S hS (φ ≫ f) p)
      (fibreAtFieldValuedPointMap B S hS φ f p) φ
      (fibreAtFieldValuedPointProjection B S hS f p) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F)
    (isPullback_fibreAtFieldValuedPointMap_hom B S hS φ f p)

/-- The morphism of fibres induced by an étale morphism over the target is étale. -/
theorem isEtale_fibreAtFieldValuedPointMap (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y.1) :
    IsEtale B S hS (fibreAtFieldValuedPointMap B S hS φ f p).hom :=
  isEtale_of_isPullback B S hS _ _ _ _ (isPullback_fibreAtFieldValuedPointMap B S hS φ f p) hφ

/-- The projection from the fibre of `φ ≫ f` followed by `φ` is the morphism of fibres
followed by the projection from the fibre of `f`, read on points. -/
theorem pointsMap_fibreAtFieldValuedPointMap (φ : X' ⟶ X) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y.1)
    (θ : points B S hS (fibreAtFieldValuedPoint B S hS (φ ≫ f) p).1) :
    pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1
        (fibreAtFieldValuedPointProjection B S hS f p).hom
        (pointsMap B S hS (fibreAtFieldValuedPoint B S hS (φ ≫ f) p).1
          (fibreAtFieldValuedPointMap B S hS φ f p).hom θ) =
      pointsMap B S hS X'.1 φ.hom
        (pointsMap B S hS (fibreAtFieldValuedPoint B S hS (φ ≫ f) p).1
          (fibreAtFieldValuedPointProjection B S hS (φ ≫ f) p).hom θ) := by
  simpa only [pointsMap_comp, Function.comp_apply] using
    congrArg (fun k ↦ pointsMap B S hS _ k θ)
      (isPullback_fibreAtFieldValuedPointMap_hom B S hS φ f p).w.symm

/-- The restriction of `φ^*F` to the fibre of `φ ≫ f` over a field-valued point of `Y` is the
pullback along the morphism of fibres of the restriction of `F` to the fibre of `f` over the
same point. -/
noncomputable def fibreAtFieldValuedPointModulePullbackIso (φ : X' ⟶ X) (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y.1) (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS (φ ≫ f) p)).obj
        ((modulePullback B S hS φ).obj F) ≅
      (modulePullback B S hS (fibreAtFieldValuedPointMap B S hS φ f p)).obj
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F) :=
  (modulePullbackCompIso B S hS
      (fibreAtFieldValuedPointProjection B S hS (φ ≫ f) p) φ).app F ≪≫
    eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj F)
      (fibreAtFieldValuedPointMap_comp_projection B S hS φ f p).symm) ≪≫
    ((modulePullbackCompIso B S hS (fibreAtFieldValuedPointMap B S hS φ f p)
      (fibreAtFieldValuedPointProjection B S hS f p)).app F).symm

/-! ### Étale invariance of the fibre condition -/

/-- A point of the fibre of `φ ≫ f` over a field-valued point of `Y` is weakly associated to
the restriction of `φ^*F` exactly when its image in the fibre of `f` over the same point is
weakly associated to the restriction of `F`, for `φ` étale: the morphism of fibres is étale, so
this is Stacks 0CUU. -/
theorem isWeaklyAssociatedPoint_fibre_modulePullback_iff (φ : X' ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (p : FieldValuedPoint B S hS Y.1)
    (θ : points B S hS (fibreAtFieldValuedPoint B S hS (φ ≫ f) p).1) :
    IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS (φ ≫ f) p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS (φ ≫ f) p)).obj
          ((modulePullback B S hS φ).obj F)) θ ↔
      IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f p)
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p)).obj F)
        (pointsMap B S hS (fibreAtFieldValuedPoint B S hS (φ ≫ f) p).1
          (fibreAtFieldValuedPointMap B S hS φ f p).hom θ) :=
  (isWeaklyAssociatedPoint_congr B S hS
      (fibreAtFieldValuedPointModulePullbackIso B S hS φ f p F) θ).trans
    (isWeaklyAssociatedPoint_modulePullback_iff B S hS
      (fibreAtFieldValuedPointMap B S hS φ f p)
      (isEtale_fibreAtFieldValuedPointMap B S hS φ hφ f p) _ θ)

/-- The chart-independence behind conditions (1) and (3) of Stacks 0CUZ, in the form of an étale
morphism over the target: for `φ : X' ⟶ X` étale and `x'` a point of `X'`, some point of the fibre
of `φ ≫ f` over a field-valued point `p` of `Y` above `x'` is weakly associated to the restriction
of `φ^*F` exactly when some point of the fibre of `f` over `p` above the image of `x'` is weakly
associated to the restriction of `F`. -/
theorem isWeaklyAssociatedOnFibre_modulePullback_iff (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) (p : FieldValuedPoint B S hS Y.1)
    (x : points B S hS X'.1) :
    IsWeaklyAssociatedOnFibre B S hS (φ ≫ f) ((modulePullback B S hS φ).obj F) p x ↔
      IsWeaklyAssociatedOnFibre B S hS f F p (pointsMap B S hS X'.1 φ.hom x) := by
  constructor
  · rintro ⟨θ, hθ, hwa⟩
    refine ⟨pointsMap B S hS _ (fibreAtFieldValuedPointMap B S hS φ f p).hom θ, ?_,
      (isWeaklyAssociatedPoint_fibre_modulePullback_iff B S hS φ hφ f F p θ).1 hwa⟩
    rw [pointsMap_fibreAtFieldValuedPointMap B S hS φ f p θ, hθ]
  · rintro ⟨θ, hθ, hwa⟩
    obtain ⟨w, hw₁, hw₂⟩ := exists_point_of_isPullback B S hS
      (isPullback_fibreAtFieldValuedPointMap B S hS φ f p) x θ hθ.symm
    exact ⟨w, hw₁,
      (isWeaklyAssociatedPoint_fibre_modulePullback_iff B S hS φ hφ f F p w).2 (hw₂ ▸ hwa)⟩

/-- The chart-independence behind conditions (2) and (4) of Stacks 0CUZ, in the form of an étale
morphism over the target: for `φ : X' ⟶ X` étale and `x'` a point of `X'`, every point of the fibre
of `φ ≫ f` over a field-valued point `p` of `Y` above `x'` is weakly associated to the restriction
of `φ^*F` exactly when every point of the fibre of `f` over `p` above the image of `x'` is weakly
associated to the restriction of `F`. -/
theorem isWeaklyAssociatedOnFibreEvery_modulePullback_iff (φ : X' ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (p : FieldValuedPoint B S hS Y.1) (x : points B S hS X'.1) :
    IsWeaklyAssociatedOnFibreEvery B S hS (φ ≫ f) ((modulePullback B S hS φ).obj F) p x ↔
      IsWeaklyAssociatedOnFibreEvery B S hS f F p (pointsMap B S hS X'.1 φ.hom x) := by
  constructor
  · intro h θ hθ
    obtain ⟨w, hw₁, hw₂⟩ := exists_point_of_isPullback B S hS
      (isPullback_fibreAtFieldValuedPointMap B S hS φ f p) x θ hθ.symm
    exact hw₂ ▸ (isWeaklyAssociatedPoint_fibre_modulePullback_iff B S hS φ hφ f F p w).1
      (h w hw₁)
  · intro h θ hθ
    refine (isWeaklyAssociatedPoint_fibre_modulePullback_iff B S hS φ hφ f F p θ).2
      (h _ ?_)
    rw [pointsMap_fibreAtFieldValuedPointMap B S hS φ f p θ, hθ]

/-- For `φ : X' ⟶ X` étale, a point of `X'` lies in `WeakAss_{X'/Y}(φ^*F)` exactly when its image
lies in `WeakAss_{X/Y}(F)`. -/
theorem isRelativeWeaklyAssociatedPoint_modulePullback_iff (φ : X' ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (x : points B S hS X'.1) :
    IsRelativeWeaklyAssociatedPoint B S hS (φ ≫ f) ((modulePullback B S hS φ).obj F) x ↔
      IsRelativeWeaklyAssociatedPoint B S hS f F (pointsMap B S hS X'.1 φ.hom x) := by
  rw [isRelativeWeaklyAssociatedPoint_iff_exists, isRelativeWeaklyAssociatedPoint_iff_exists]
  refine exists_congr fun p ↦ and_congr ?_ ?_
  · rw [show (φ ≫ f).hom = φ.hom ≫ f.hom from rfl, pointsMap_comp]
    rfl
  · exact isWeaklyAssociatedOnFibre_modulePullback_iff B S hS φ hφ f F p x

/-! ### The conditions over an étale scheme chart of the target -/

/-- Condition (1) of Stacks 0CUZ: for some étale chart `V ⟶ Y` by a scheme and some point `v` of `V`
above the image of `x`, some point of the fibre of `f` over the residue field of `v` lying above `x`
is weakly associated to the restriction of `F` to that fibre. -/
noncomputable def IsWeaklyAssociatedOnSomeSchemeChartFibre (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1)
      (v : (BigFppfOver.toScheme B S hS).obj V), IsEtale B S hS g ∧
    pointsMap B S hS (yoneda.obj V) g
        ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) =
      pointsMap B S hS X.1 f.hom x ∧
    IsWeaklyAssociatedOnFibre B S hS f F
      (FieldValuedPoint.map B S hS (yoneda.obj V) g
        (schemePointRepresentative B S hS V v)) x

/-- Condition (2) of Stacks 0CUZ: for every étale chart `V ⟶ Y` by a scheme and every point `v` of
`V` above the image of `x`, every point of the fibre of `f` over the residue field of `v` lying
above `x` is weakly associated to the restriction of `F` to that fibre. -/
noncomputable def IsWeaklyAssociatedOnEverySchemeChartFibre (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1)
      (v : (BigFppfOver.toScheme B S hS).obj V), IsEtale B S hS g →
    pointsMap B S hS (yoneda.obj V) g
        ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) =
      pointsMap B S hS X.1 f.hom x →
    IsWeaklyAssociatedOnFibreEvery B S hS f F
      (FieldValuedPoint.map B S hS (yoneda.obj V) g
        (schemePointRepresentative B S hS V v)) x

/-- Condition (1) of Stacks 0CUZ implies condition (5): the residue field of a point of an étale
scheme chart of `Y` above the image of `x` is a field-valued representative of that image, so the
chart condition places `x` in the relative weak assassin. -/
theorem isRelativeWeaklyAssociatedPoint_of_someSchemeChart (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) {x : points B S hS X.1}
    (h : IsWeaklyAssociatedOnSomeSchemeChartFibre B S hS f F x) :
    IsRelativeWeaklyAssociatedPoint B S hS f F x := by
  obtain ⟨V, g, v, -, hv, hwa⟩ := h
  exact isRelativeWeaklyAssociatedPoint_of_isWeaklyAssociatedOnFibre B S hS f F
    ((pointsMap_class B S hS (yoneda.obj V) g (schemePointRepresentative B S hS V v)).symm.trans
      hv) hwa

/-- Condition (2) of Stacks 0CUZ implies condition (1): the target of `f` admits an étale scheme
chart through the image of `x`, and the fibre over the residue field of a point of that chart above
the image carries a point above `x`. -/
theorem isWeaklyAssociatedOnSomeSchemeChartFibre_of_every (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) {x : points B S hS X.1}
    (h : IsWeaklyAssociatedOnEverySchemeChartFibre B S hS f F x) :
    IsWeaklyAssociatedOnSomeSchemeChartFibre B S hS f F x := by
  obtain ⟨V, a, w, ha, hw, -, -⟩ := exists_etale_scheme_chart_through_point B S hS Y.2
    (𝟙 Y.1) (isEtale_id B S hS Y.1) (pointsMap B S hS X.1 f.hom x)
  refine ⟨V, a, pointsToScheme B S hS V w, ha, ?_, ?_⟩
  · rwa [class_schemePointRepresentative_pointsToScheme B S hS V w]
  · refine isWeaklyAssociatedOnFibre_of_every B S hS f F ?_ (h V a _ ha ?_)
    · rwa [← pointsMap_class, class_schemePointRepresentative_pointsToScheme B S hS V w]
    · rwa [class_schemePointRepresentative_pointsToScheme B S hS V w]

end AlgebraicGeometry.Space

end
