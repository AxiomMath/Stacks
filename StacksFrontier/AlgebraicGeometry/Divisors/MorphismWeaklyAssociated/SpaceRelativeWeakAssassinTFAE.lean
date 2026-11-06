module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.RepresentedFibreComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtaleTargetDescent
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization

/-!
# The equivalent conditions defining the relative weak assassin

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `𝓕` be a
quasi-coherent `𝒪_X`-module, let `x ∈ |X|` and `y = f(x)`. Stacks 0CUZ gives five equivalent
ways of saying that `x` is relatively weakly associated to `𝓕` over `Y`:

1. for some étale `V ⟶ Y` with `V` a scheme, some `v ∈ V` above `y` and some `x' ∈ |X_v|`
   above `x`, the point `x'` is weakly associated to `𝓕|_{X_v}`;
2. the same for every such `V`, `v` and `x'`;
3. for some étale `V ⟶ Y` and some étale `U ⟶ X ×_Y V` with `U`, `V` schemes, and some
   `u ∈ U` above `x`, with image `v ∈ V`, the point `u` is weakly associated to `𝓕|_{U_v}`;
4. the same for every such `U`, `V` and `u`;
5. for some field-valued point `Spec(k) ⟶ Y` representing `y` and some `t ∈ |X_k|` above `x`,
   the point `t` is weakly associated to `𝓕|_{X_k}`.

When `y` is represented by a monomorphism `Spec(k₀) ⟶ Y`, they are also equivalent to
(6): the unique point `x₀ ∈ |X_{k₀}|` above `x` is weakly associated to `𝓕|_{X_{k₀}}`. When
the fibre of `f` over `y` is locally Noetherian, "weakly associated" may be replaced by
"associated" in (1), (2), (3), (4) and (6).

## Main definitions

* `AlgebraicGeometry.Space.IsWeaklyAssociatedOnSomeEtaleChartSquare` and
  `AlgebraicGeometry.Space.IsWeaklyAssociatedOnEveryEtaleChartSquare`: conditions (3) and (4).
  Conditions (1) and (2) are `AlgebraicGeometry.Space.IsWeaklyAssociatedOnSomeSchemeChartFibre`
  and `AlgebraicGeometry.Space.IsWeaklyAssociatedOnEverySchemeChartFibre`, and condition (5) is
  `AlgebraicGeometry.Space.IsRelativeWeaklyAssociatedPoint`, the definition of Stacks 0CV0.
* `AlgebraicGeometry.Space.IsAssociatedPoint`: the associated points of Stacks 0CTX on a locally
  Noetherian algebraic space.
* `AlgebraicGeometry.Space.IsAssociatedOnSomeSchemeChartFibre`,
  `AlgebraicGeometry.Space.IsAssociatedOnEverySchemeChartFibre`,
  `AlgebraicGeometry.Space.IsAssociatedOnSomeEtaleChartSquare` and
  `AlgebraicGeometry.Space.IsAssociatedOnEveryEtaleChartSquare`: conditions (1) to (4) with
  "associated" in place of "weakly associated".

## Main results

* `AlgebraicGeometry.Space.relativeWeakAssassin_tfae`: conditions (1) to (5) are equivalent.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_iff_of_mono`: at a monomorphic
  representative of `y`, condition (6) is equivalent to them.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_iff_associated`: when the fibre over
  `y` is locally Noetherian, "weakly associated" may be replaced by "associated".

## References

* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 0CUS](https://stacks.math.columbia.edu/tag/0CUS)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 0CUW](https://stacks.math.columbia.edu/tag/0CUW)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 05AR](https://stacks.math.columbia.edu/tag/05AR)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_SpaceRelativeWeakAssassinTFAE
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### A monomorphic representative of the image point -/

/-- **Stacks 0AC8 at a monomorphic representative.** If `Spec(k₀) ⟶ Y` is a monomorphism
representing `f(x)`, the fibre of `f` over it carries exactly one point above `x`. -/
theorem existsUnique_point_fibre_of_mono (f : X ⟶ Y) (p₀ : FieldValuedPoint B S hS Y.1)
    [Mono (fieldMorphism B S hS Y.1 p₀)] {x : points B S hS X.1}
    (rep : p₀.class B S hS Y.1 = pointsMap B S hS X.1 f.hom x) :
    ∃! x₀ : points B S hS (fibreAtFieldValuedPoint B S hS f p₀).1,
      pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p₀).1
        (fibreAtFieldValuedPointProjection B S hS f p₀).hom x₀ = x := by
  obtain ⟨x₀, hx₀⟩ := exists_point_fibre_of_pointsMap_eq_class B S hS f rep
  exact ⟨x₀, hx₀, fun x₁ hx₁ ↦ injective_pointsMap_fibre_fieldMorphism B S hS f.hom p₀
    inferInstance (hx₁.trans hx₀.symm)⟩

/-- A point of the relative weak assassin is weakly associated at every point above it of the
fibre over a monomorphic representative `Spec(k₀) ⟶ Y` of its image. -/
theorem isWeaklyAssociatedOnFibreEvery_of_mono (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (p₀ : FieldValuedPoint B S hS Y.1) [Mono (fieldMorphism B S hS Y.1 p₀)]
    {x : points B S hS X.1} (rep : p₀.class B S hS Y.1 = pointsMap B S hS X.1 f.hom x)
    (hx : IsRelativeWeaklyAssociatedPoint B S hS f F x) :
    IsWeaklyAssociatedOnFibreEvery B S hS f F p₀ x := by
  obtain ⟨p, hp, θ, hθ, hwa⟩ := hx
  have : Mono (yonedaEquiv.symm p₀.value) :=
    inferInstanceAs (Mono (fieldMorphism B S hS Y.1 p₀))
  obtain ⟨κ, hκ, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS Y.1 Y.2
    p₀ p (rep.trans hp.symm)
  have hκ' : yoneda.map κ ≫ fieldMorphism B S hS Y.1 p₀ = fieldMorphism B S hS Y.1 p := by
    show yoneda.map κ ≫ yonedaEquiv.symm p₀.value = yonedaEquiv.symm p.value
    rw [← hκ]
    exact yonedaEquiv_symm_naturality_left κ Y.1 p₀.value
  obtain ⟨π, hπ, sq⟩ := exists_fibreMap_isPullback_of_refines B S hS f κ hκ'
  have hwa₀ := isWeaklyAssociatedPoint_fibre_of_refines B S hS f F inferInstance κ hπ sq hwa
  intro x₀ hx₀
  have hhom : π.hom ≫ (fibreAtFieldValuedPointProjection B S hS f p₀).hom =
      (fibreAtFieldValuedPointProjection B S hS f p).hom :=
    congrArg (fun m : fibreAtFieldValuedPoint B S hS f p ⟶ X ↦ m.hom) hπ
  have hπθ : pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p₀).1
      (fibreAtFieldValuedPointProjection B S hS f p₀).hom
      (pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1 π.hom θ) = x := by
    have h := congrArg (fun k ↦ pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1 k θ)
      hhom
    simp only [pointsMap_comp, Function.comp_apply] at h
    rw [h, hθ]
  have heq : pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p).1 π.hom θ = x₀ :=
    injective_pointsMap_fibre_fieldMorphism B S hS f.hom p₀ inferInstance (hπθ.trans hx₀.symm)
  exact heq ▸ hwa₀

/-! ### Condition (5) implies condition (2) -/

/-- A point of the relative weak assassin is weakly associated at every point above it of the
fibre of `f` over the image, under an étale morphism `g : Y' ⟶ Y`, of a monomorphic
field-valued point `q` of `Y'`. -/
theorem isWeaklyAssociatedOnFibreEvery_map_of_isEtale_of_mono
    {X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (etale : IsEtale B S hS g.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (q : FieldValuedPoint B S hS Y'.1) [Mono (fieldMorphism B S hS Y'.1 q)]
    {x : points B S hS X.1} (hx : IsRelativeWeaklyAssociatedPoint B S hS f F x) :
    IsWeaklyAssociatedOnFibreEvery B S hS f F (FieldValuedPoint.map B S hS Y'.1 g.hom q) x := by
  have sqh : IsPullback g'.hom f'.hom f.hom g.hom :=
    sq.map (ObjectProperty.ι fun G ↦ IsAlgebraicSpace B S hS G)
  have hg' : IsEtale B S hS g'.hom := isEtale_of_isPullback B S hS f' g' g f sq.flip etale
  have : ((modulePullback B S hS g').obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' F inferInstance
  have : IsIso (baseChangeFibreMap B S hS sqh q).hom :=
    inferInstanceAs (IsIso (baseChangeFibreIso B S hS sqh q).hom)
  intro θ hθ
  obtain ⟨θ', rfl⟩ := pointsMap_surjective_of_isIso B S hS (baseChangeFibreMap B S hS sqh q).hom θ
  set x' := pointsMap B S hS (fibreAtFieldValuedPoint B S hS f' q).1
    (fibreAtFieldValuedPointProjection B S hS f' q).hom θ' with hx'
  have hx'x : pointsMap B S hS X'.1 g'.hom x' = x :=
    (pointsMap_baseChangeFibreMap B S hS sqh q θ').symm.trans hθ
  have h₁ : IsRelativeWeaklyAssociatedPoint B S hS (g' ≫ f) ((modulePullback B S hS g').obj F)
      x' :=
    (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS g' hg' f F x').2
      (by rw [hx'x]; exact hx)
  rw [sq.w] at h₁
  have h₂ := isRelativeWeaklyAssociatedPoint_of_comp_of_isEtale B S hS f' g etale _ h₁
  have hqx : q.class B S hS Y'.1 = pointsMap B S hS X'.1 f'.hom x' := by
    have hmem : x' ∈ Set.range (pointsMap B S hS (pullback f'.hom (fieldMorphism B S hS Y'.1 q))
        (pullback.fst f'.hom (fieldMorphism B S hS Y'.1 q))) := ⟨θ', rfl⟩
    rw [range_pointsMap_fibre_fieldMorphism B S hS f'.hom q] at hmem
    exact hmem.symm
  have h₃ := isWeaklyAssociatedOnFibreEvery_of_mono B S hS f' ((modulePullback B S hS g').obj F)
    q hqx h₂ θ' rfl
  exact (isWeaklyAssociatedPoint_baseChangeFibre_iff B S hS sqh q F θ').1 h₃

/-- **Condition (5) implies condition (2).** A point of the relative weak assassin is weakly
associated at every point above it of the fibre of `f` over the residue field of every point of
every étale scheme chart of `Y` above its image. -/
theorem isWeaklyAssociatedOnEverySchemeChartFibre_of_isRelativeWeaklyAssociatedPoint
    (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    {x : points B S hS X.1} (hx : IsRelativeWeaklyAssociatedPoint B S hS f F x) :
    IsWeaklyAssociatedOnEverySchemeChartFibre B S hS f F x := by
  intro V g v hg _
  have : Mono (fieldMorphism B S hS (yoneda.obj V) (schemePointRepresentative B S hS V v)) :=
    mono_fieldMorphism_schemePointRepresentative B S hS V v
  exact isWeaklyAssociatedOnFibreEvery_map_of_isEtale_of_mono B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f
      (ObjectProperty.homMk g : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ :
        AlgebraicSpaces B S hS) ⟶ Y)) hg F (schemePointRepresentative B S hS V v) hx

/-! ### Conditions (3) and (4): étale chart squares -/

/-- In a square formed by an étale morphism `g : V ⟶ Y` and an étale morphism
`a : U ⟶ X ×_Y V` from schemes, the morphism of algebraic spaces `U ⟶ X ×_Y V ⟶ X`. -/
noncomputable abbrev etaleChartSquareSource (f : X ⟶ Y) {V U : BigFppfOver B S hS}
    (g : yoneda.obj V ⟶ Y.1) (a : yoneda.obj U ⟶ pullback f.hom g) :
    (schemeSpace U : AlgebraicSpaces B S hS) ⟶ X :=
  ObjectProperty.homMk (a ≫ pullback.fst f.hom g)

/-- The pullback `𝓕|_U` of `𝓕` to the scheme `U` of an étale chart square, as a module on
the scheme `U`. -/
noncomputable abbrev etaleChartSquareModule (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    {V U : BigFppfOver B S hS} (g : yoneda.obj V ⟶ Y.1) (a : yoneda.obj U ⟶ pullback f.hom g) :
    ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  representedChartModule B S hS
    ((modulePullback B S hS (etaleChartSquareSource B S hS f g a)).obj F)

/-- **Stacks 0CUZ, condition (3).** For some étale morphism `g : V ⟶ Y` and some étale
morphism `a : U ⟶ X ×_Y V` with `U` and `V` schemes, the latter lying over `α : U ⟶ V`, and
some point `u ∈ U` above `x`, the point `u` is weakly associated to the restriction of `𝓕|_U`
to the fibre `U_v` of `α` over `v = α(u)`, that is `u ∈ WeakAss_{U/V}(𝓕|_U)` in the sense of
Stacks 05AV. -/
noncomputable def IsWeaklyAssociatedOnSomeEtaleChartSquare (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1) (U : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ pullback f.hom g) (α : U ⟶ V)
      (u : (BigFppfOver.toScheme B S hS).obj U),
    IsEtale B S hS g ∧ IsEtale B S hS a ∧ a ≫ pullback.snd f.hom g = yoneda.map α ∧
      pointsMap B S hS (yoneda.obj U) (a ≫ pullback.fst f.hom g)
          ((pointsEquivScheme B S hS U).symm u) = x ∧
        u ∈ _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
          ((BigFppfOver.toScheme B S hS).map α) (etaleChartSquareModule B S hS f F g a)

/-- **Stacks 0CUZ, condition (4).** For every étale morphism `g : V ⟶ Y`, every étale
morphism `a : U ⟶ X ×_Y V` with `U` and `V` schemes, lying over `α : U ⟶ V`, and every point
`u ∈ U` above `x`, the point `u` is weakly associated to the restriction of `𝓕|_U` to the fibre
`U_v` of `α` over `v = α(u)`. -/
noncomputable def IsWeaklyAssociatedOnEveryEtaleChartSquare (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1) (U : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ pullback f.hom g) (α : U ⟶ V)
      (u : (BigFppfOver.toScheme B S hS).obj U),
    IsEtale B S hS g → IsEtale B S hS a → a ≫ pullback.snd f.hom g = yoneda.map α →
      pointsMap B S hS (yoneda.obj U) (a ≫ pullback.fst f.hom g)
          ((pointsEquivScheme B S hS U).symm u) = x →
        u ∈ _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
          ((BigFppfOver.toScheme B S hS).map α) (etaleChartSquareModule B S hS f F g a)

/-- **Condition (3) at one chart square is condition (5).** In an étale chart square, a point
`u` of `U` lies in `WeakAss_{U/V}(𝓕|_U)` exactly when its image in `X` lies in
`WeakAss_{X/Y}(𝓕)`. -/
theorem mem_relativeWeaklyAssociatedPoints_etaleChartSquare_iff (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] {V U : BigFppfOver B S hS}
    (g : yoneda.obj V ⟶ Y.1) (hg : IsEtale B S hS g) (a : yoneda.obj U ⟶ pullback f.hom g)
    (ha : IsEtale B S hS a) (α : U ⟶ V) (hα : a ≫ pullback.snd f.hom g = yoneda.map α)
    (u : (BigFppfOver.toScheme B S hS).obj U) :
    u ∈ _root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints
        ((BigFppfOver.toScheme B S hS).map α) (etaleChartSquareModule B S hS f F g a) ↔
      IsRelativeWeaklyAssociatedPoint B S hS f F
        (pointsMap B S hS (yoneda.obj U) (a ≫ pullback.fst f.hom g)
          ((pointsEquivScheme B S hS U).symm u)) := by
  set φ := etaleChartSquareSource B S hS f g a with hφdef
  set N := (modulePullback B S hS φ).obj F with hN
  have hNqc : N.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ F inferInstance
  set w := (pointsEquivScheme B S hS U).symm u with hw
  have hwu : pointsToScheme B S hS U w = u := (pointsEquivScheme B S hS U).apply_symm_apply u
  let gY : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y :=
    ObjectProperty.homMk g
  have hφ : IsEtale B S hS φ.hom :=
    isEtale_comp B S hS ha (isEtale_pullback_fst B S hS X.2 Y.2
      (isAlgebraicSpace_yoneda B S hS V) f.hom g hg)
  have hcomm : representedSpaceMap B S hS α ≫ gY = φ ≫ f := by
    apply ObjectProperty.hom_ext
    show yoneda.map α ≫ g = (a ≫ pullback.fst f.hom g) ≫ f.hom
    rw [← hα, Category.assoc, Category.assoc, pullback.condition]
  rw [← hwu, ← isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints B S hS α N
    hNqc w, ← isRelativeWeaklyAssociatedPoint_comp_iff_of_isEtale B S hS
    (representedSpaceMap B S hS α) gY hg N w, hcomm]
  exact isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS φ hφ f F w

/-- Every point of `X` lies on some étale chart square: an étale scheme chart `V ⟶ Y` through
its image, a point of `X ×_Y V` above it and the given point of `V` by Stacks 03H4, and an
étale scheme chart of `X ×_Y V` through that point. -/
theorem exists_etaleChartSquare (f : X ⟶ Y) (x : points B S hS X.1) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1) (U : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ pullback f.hom g) (α : U ⟶ V)
      (u : (BigFppfOver.toScheme B S hS).obj U),
      IsEtale B S hS g ∧ IsEtale B S hS a ∧ a ≫ pullback.snd f.hom g = yoneda.map α ∧
        pointsMap B S hS (yoneda.obj U) (a ≫ pullback.fst f.hom g)
          ((pointsEquivScheme B S hS U).symm u) = x := by
  obtain ⟨V, g, v, hg, hv, -, -⟩ := exists_etale_scheme_chart_through_point B S hS Y.2 (𝟙 Y.1)
    (isEtale_id B S hS Y.1) (pointsMap B S hS X.1 f.hom x)
  obtain ⟨w, hw₁, -⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback f.hom g)
    x v hv.symm
  obtain ⟨U, a, u', ha, hu', -, -⟩ := exists_etale_scheme_chart_through_point B S hS
    (isAlgebraicSpace_pullback B S hS f.hom g X.2 (isAlgebraicSpace_yoneda B S hS V) Y.2)
    (𝟙 _) (isEtale_id B S hS _) w
  refine ⟨V, g, U, a, yoneda.preimage (a ≫ pullback.snd f.hom g), pointsToScheme B S hS U u',
    hg, ha, (yoneda.map_preimage _).symm, ?_⟩
  rw [show (pointsEquivScheme B S hS U).symm (pointsToScheme B S hS U u') = u' from
    (pointsEquivScheme B S hS U).symm_apply_apply u', pointsMap_comp, Function.comp_apply, hu',
    hw₁]

/-! ### Stacks 0CUZ -/

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`, let `𝓕` be a quasi-coherent `𝒪_X`-module and let `x ∈ |X|`. The following are
equivalent:

1. for some étale `V ⟶ Y` with `V` a scheme, some `v ∈ V` above `f(x)` and some `x' ∈ |X_v|`
   above `x`, the point `x'` is weakly associated to `𝓕|_{X_v}`;
2. for every such `V`, `v` and `x'`, the point `x'` is weakly associated to `𝓕|_{X_v}`;
3. for some étale `V ⟶ Y`, some étale `U ⟶ X ×_Y V` with `U`, `V` schemes and some `u ∈ U`
   above `x`, with image `v ∈ V`, the point `u` is weakly associated to `𝓕|_{U_v}`;
4. for every such `U`, `V` and `u`, the point `u` is weakly associated to `𝓕|_{U_v}`;
5. for some field `k`, some `Spec(k) ⟶ Y` representing `f(x)` and some `t ∈ |X_k|` above `x`,
   the point `t` is weakly associated to `𝓕|_{X_k}`. -/
@[stacks 0CUZ "conditions (1) to (5)"]
theorem relativeWeakAssassin_tfae (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (x : points B S hS X.1) :
    List.TFAE [IsWeaklyAssociatedOnSomeSchemeChartFibre B S hS f F x,
      IsWeaklyAssociatedOnEverySchemeChartFibre B S hS f F x,
      IsWeaklyAssociatedOnSomeEtaleChartSquare B S hS f F x,
      IsWeaklyAssociatedOnEveryEtaleChartSquare B S hS f F x,
      IsRelativeWeaklyAssociatedPoint B S hS f F x] := by
  tfae_have 1 → 5 := isRelativeWeaklyAssociatedPoint_of_someSchemeChart B S hS f F
  tfae_have 5 → 2 :=
    isWeaklyAssociatedOnEverySchemeChartFibre_of_isRelativeWeaklyAssociatedPoint B S hS f F
  tfae_have 2 → 1 := isWeaklyAssociatedOnSomeSchemeChartFibre_of_every B S hS f F
  tfae_have 3 → 5 := by
    rintro ⟨V, g, U, a, α, u, hg, ha, hα, hu, hmem⟩
    exact hu ▸ (mem_relativeWeaklyAssociatedPoints_etaleChartSquare_iff B S hS f F g hg a ha α
      hα u).1 hmem
  tfae_have 5 → 4 := by
    intro hx V g U a α u hg ha hα hu
    exact (mem_relativeWeaklyAssociatedPoints_etaleChartSquare_iff B S hS f F g hg a ha α hα
      u).2 (hu ▸ hx)
  tfae_have 4 → 3 := by
    intro h
    obtain ⟨V, g, U, a, α, u, hg, ha, hα, hu⟩ := exists_etaleChartSquare B S hS f x
    exact ⟨V, g, U, a, α, u, hg, ha, hα, hu, h V g U a α u hg ha hα hu⟩
  tfae_finish

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S`, let `𝓕` be a quasi-coherent `𝒪_X`-module, let `x ∈ |X|` and let `Spec(k₀) ⟶ Y` be a
monomorphism representing `f(x)`. Then there is a unique point `x₀ ∈ |X_{k₀}|` mapping to `x`,
and the equivalent conditions of `AlgebraicGeometry.Space.relativeWeakAssassin_tfae` hold
exactly when `x₀` is a weakly associated point of `𝓕|_{X_{k₀}}`. -/
@[stacks 0CUZ "condition (6), at a monomorphism from the spectrum of a field representing the \
image point"]
theorem isRelativeWeaklyAssociatedPoint_iff_of_mono (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (p₀ : FieldValuedPoint B S hS Y.1) [Mono (fieldMorphism B S hS Y.1 p₀)]
    {x : points B S hS X.1} (rep : p₀.class B S hS Y.1 = pointsMap B S hS X.1 f.hom x) :
    (∃! x₀ : points B S hS (fibreAtFieldValuedPoint B S hS f p₀).1,
      pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p₀).1
        (fibreAtFieldValuedPointProjection B S hS f p₀).hom x₀ = x) ∧
    ∀ x₀ : points B S hS (fibreAtFieldValuedPoint B S hS f p₀).1,
      pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p₀).1
          (fibreAtFieldValuedPointProjection B S hS f p₀).hom x₀ = x →
        (IsRelativeWeaklyAssociatedPoint B S hS f F x ↔
          IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f p₀)
            ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p₀)).obj F)
            x₀) :=
  ⟨existsUnique_point_fibre_of_mono B S hS f p₀ rep, fun x₀ hx₀ ↦
    ⟨fun hx ↦ isWeaklyAssociatedOnFibreEvery_of_mono B S hS f F p₀ rep hx x₀ hx₀,
      fun hwa ↦ ⟨p₀, rep, x₀, hx₀, hwa⟩⟩⟩

/-! ### The locally Noetherian case -/

/-- **Stacks 0CTX, associated points.** A point `z` of an algebraic space `Z` is *associated*
to an `𝒪_Z`-module `𝓕` when `Z` is locally Noetherian and `z` is weakly associated to `𝓕`. -/
def IsAssociatedPoint (Z : AlgebraicSpaces B S hS) (F : Modules.{u, u} B S hS Z.1 Z.2)
    (z : points B S hS Z.1) : Prop :=
  HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) ∧
    IsWeaklyAssociatedPoint B S hS Z F z

/-- **Stacks 0CUZ, condition (1) with associated points.** For some étale `V ⟶ Y` with `V` a
scheme, some `v ∈ V` above `f(x)` and some `x' ∈ |X_v|` above `x`, the point `x'` is an
associated point of `𝓕|_{X_v}`. -/
def IsAssociatedOnSomeSchemeChartFibre (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (x : points B S hS X.1) : Prop :=
  ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1)
      (v : (BigFppfOver.toScheme B S hS).obj V), IsEtale B S hS g ∧
    pointsMap B S hS (yoneda.obj V) g
        ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) =
      pointsMap B S hS X.1 f.hom x ∧
    ∃ θ : points B S hS (fibreAtFieldValuedPoint B S hS f
        (FieldValuedPoint.map B S hS (yoneda.obj V) g (schemePointRepresentative B S hS V v))).1,
      pointsMap B S hS _ (fibreAtFieldValuedPointProjection B S hS f
        (FieldValuedPoint.map B S hS (yoneda.obj V) g
          (schemePointRepresentative B S hS V v))).hom θ = x ∧
      IsAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f
          (FieldValuedPoint.map B S hS (yoneda.obj V) g (schemePointRepresentative B S hS V v)))
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f
          (FieldValuedPoint.map B S hS (yoneda.obj V) g
            (schemePointRepresentative B S hS V v)))).obj F) θ

/-- **Stacks 0CUZ, condition (2) with associated points.** For every étale `V ⟶ Y` with `V` a
scheme, every `v ∈ V` above `f(x)` and every `x' ∈ |X_v|` above `x`, the point `x'` is an
associated point of `𝓕|_{X_v}`. -/
def IsAssociatedOnEverySchemeChartFibre (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (x : points B S hS X.1) : Prop :=
  ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1)
      (v : (BigFppfOver.toScheme B S hS).obj V), IsEtale B S hS g →
    pointsMap B S hS (yoneda.obj V) g
        ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) =
      pointsMap B S hS X.1 f.hom x →
    ∀ θ : points B S hS (fibreAtFieldValuedPoint B S hS f
        (FieldValuedPoint.map B S hS (yoneda.obj V) g (schemePointRepresentative B S hS V v))).1,
      pointsMap B S hS _ (fibreAtFieldValuedPointProjection B S hS f
        (FieldValuedPoint.map B S hS (yoneda.obj V) g
          (schemePointRepresentative B S hS V v))).hom θ = x →
      IsAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f
          (FieldValuedPoint.map B S hS (yoneda.obj V) g (schemePointRepresentative B S hS V v)))
        ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f
          (FieldValuedPoint.map B S hS (yoneda.obj V) g
            (schemePointRepresentative B S hS V v)))).obj F) θ

/-- **Stacks 0CUZ, condition (3) with associated points.** For some étale chart square
`U ⟶ X ×_Y V ⟶ V ⟶ Y` and some `u ∈ U` above `x`, the point `u` is an associated point of the
restriction of `𝓕|_U` to the fibre `U_v` over `v = α(u)`, that is `u ∈ Ass_{U/V}(𝓕|_U)` in the
sense of Stacks 05AT. -/
noncomputable def IsAssociatedOnSomeEtaleChartSquare (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1) (U : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ pullback f.hom g) (α : U ⟶ V)
      (u : (BigFppfOver.toScheme B S hS).obj U),
    IsEtale B S hS g ∧ IsEtale B S hS a ∧ a ≫ pullback.snd f.hom g = yoneda.map α ∧
      pointsMap B S hS (yoneda.obj U) (a ≫ pullback.fst f.hom g)
          ((pointsEquivScheme B S hS U).symm u) = x ∧
        u ∈ Stacks.Divisors.relativeAssassin ((BigFppfOver.toScheme B S hS).map α)
          (etaleChartSquareModule B S hS f F g a)

/-- **Stacks 0CUZ, condition (4) with associated points.** For every étale chart square
`U ⟶ X ×_Y V ⟶ V ⟶ Y` and every `u ∈ U` above `x`, the point `u` is an associated point of
the restriction of `𝓕|_U` to the fibre `U_v` over `v = α(u)`. -/
noncomputable def IsAssociatedOnEveryEtaleChartSquare (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1) (U : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ pullback f.hom g) (α : U ⟶ V)
      (u : (BigFppfOver.toScheme B S hS).obj U),
    IsEtale B S hS g → IsEtale B S hS a → a ≫ pullback.snd f.hom g = yoneda.map α →
      pointsMap B S hS (yoneda.obj U) (a ≫ pullback.fst f.hom g)
          ((pointsEquivScheme B S hS U).symm u) = x →
        u ∈ Stacks.Divisors.relativeAssassin ((BigFppfOver.toScheme B S hS).map α)
          (etaleChartSquareModule B S hS f F g a)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

/-- A point `x` of `X` whose fibre `X_{f(x)}` is locally Noetherian lies in the relative
assassin `Ass_{X/S}(𝓕)` of Stacks 05AT exactly when it lies in the relative weak assassin
`WeakAss_{X/S}(𝓕)` of Stacks 05AV: on that fibre the two notions agree by Stacks 05AR. -/
theorem mem_relativeAssassin_iff_mem_relativeWeaklyAssociatedPoints {X S : Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules) (x : X) (noeth : IsLocallyNoetherian (f.fiber (f x))) :
    x ∈ Stacks.Divisors.relativeAssassin f F ↔ x ∈ relativeWeaklyAssociatedPoints f F := by
  have key : ∀ s : S, ∀ t : f.fiber s, f.fiberι s t = x →
      (t ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F) ↔
        t ∈ Stacks.Divisors.weaklyAssociatedPoints
          ((Scheme.Modules.pullback (f.fiberι s)).obj F)) := by
    intro s t ht
    have hs : f x = s := by
      have hmem : f.fiberι s t ∈ f.base ⁻¹' {s} := f.range_fiberι s ▸ Set.mem_range_self t
      rw [← ht]
      exact hmem
    subst hs
    rw [associatedPoints_eq_weaklyAssociatedPoints]
  simp only [Stacks.Divisors.relativeAssassin, relativeWeaklyAssociatedPoints, Set.mem_iUnion,
    Set.mem_image]
  exact exists_congr fun s ↦ ⟨fun ⟨t, h, ht⟩ ↦ ⟨t, (key s t ht).1 h, ht⟩,
    fun ⟨t, h, ht⟩ ↦ ⟨t, (key s t ht).2 h, ht⟩⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance high] hasPullback_presheaf_SpaceRelativeWeakAssassinTFAE

/-- In an étale chart square over a point of `Y` above which the fibre of `f` is locally
Noetherian, the fibre `U_v` of `α : U ⟶ V` over the image `v` of a point of `U` above `x` is
locally Noetherian, by Stacks 0CUW. -/
theorem isLocallyNoetherian_fiber_etaleChartSquare (f : X ⟶ Y) {x : points B S hS X.1}
    (noeth : IsLocallyNoetherianFiber B S hS f.hom (pointsMap B S hS X.1 f.hom x))
    {V U : BigFppfOver B S hS} (g : yoneda.obj V ⟶ Y.1) (hg : IsEtale B S hS g)
    (a : yoneda.obj U ⟶ pullback f.hom g) (ha : IsEtale B S hS a) (α : U ⟶ V)
    (hα : a ≫ pullback.snd f.hom g = yoneda.map α) (u : (BigFppfOver.toScheme B S hS).obj U)
    (hu : pointsMap B S hS (yoneda.obj U) (a ≫ pullback.fst f.hom g)
      ((pointsEquivScheme B S hS U).symm u) = x) :
    IsLocallyNoetherian (((BigFppfOver.toScheme B S hS).map α).fiber
      ((BigFppfOver.toScheme B S hS).map α u)) := by
  refine isLocallyNoetherian_fiber_of_etale_pullback_chart B S hS X.2 Y.2 f.hom V g
    ((isEtale_iff_presheaf_of_yoneda B S hS g).1 hg) U a α hα
    ((isEtale_iff_presheaf_of_yoneda B S hS a).1 ha) _ ?_
  set w := (pointsEquivScheme B S hS U).symm u with hw
  have hwu : pointsToScheme B S hS U w = u := (pointsEquivScheme B S hS U).apply_symm_apply u
  have hclass : (schemePointRepresentative B S hS V ((BigFppfOver.toScheme B S hS).map α u)).class
      B S hS (yoneda.obj V) = pointsMap B S hS (yoneda.obj U) (yoneda.map α) w := by
    rw [← hwu, ← pointsToScheme_pointsMap_yoneda B S hS α w,
      class_schemePointRepresentative_pointsToScheme]
  rw [hclass, ← Function.comp_apply (f := pointsMap B S hS (yoneda.obj V) g), ← pointsMap_comp,
    ← hα, Category.assoc, ← pullback.condition, ← Category.assoc, pointsMap_comp,
    Function.comp_apply, hu]
  exact noeth

/-- Over a point of `Y` above which the fibre of `f` is locally Noetherian, the fibre of `f`
over the residue field of a point of an étale scheme chart of `Y` is locally Noetherian, by
Stacks 0CUW. -/
theorem isLocallyNoetherianFiberAt_schemeChart (f : X ⟶ Y) {y : points B S hS Y.1}
    (noeth : IsLocallyNoetherianFiber B S hS f.hom y) (V : BigFppfOver B S hS)
    (g : yoneda.obj V ⟶ Y.1) (v : (BigFppfOver.toScheme B S hS).obj V) (hg : IsEtale B S hS g)
    (hv : pointsMap B S hS (yoneda.obj V) g
      ((schemePointRepresentative B S hS V v).class B S hS (yoneda.obj V)) = y) :
    HasEtaleLocalProperty B S hS (fibreAtFieldValuedPoint B S hS f
        (FieldValuedPoint.map B S hS (yoneda.obj V) g (schemePointRepresentative B S hS V v))).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) := by
  have key := (isLocallyNoetherianFiber_tfae B S hS X.2 Y.2 f.hom y).out 3 2
  exact key.1 noeth V g v hg hv

/-- Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`, let `𝓕` be a quasi-coherent `𝒪_X`-module and let `x ∈ |X|` be such that the
fibre of `f` over `f(x)` is locally Noetherian. Then in conditions (1), (2), (3), (4) and (6) of
`AlgebraicGeometry.Space.relativeWeakAssassin_tfae` and
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_iff_of_mono` "weakly associated" may
be replaced by "associated": each of the resulting conditions is equivalent to `x` lying in the
relative weak assassin `WeakAss_{X/Y}(𝓕)`. -/
@[stacks 0CUZ "the locally Noetherian case: weakly associated replaced by associated in \
conditions (1), (2), (3), (4) and (6)"]
theorem isRelativeWeaklyAssociatedPoint_iff_associated (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (x : points B S hS X.1)
    (noeth : IsLocallyNoetherianFiber B S hS f.hom (pointsMap B S hS X.1 f.hom x)) :
    (IsRelativeWeaklyAssociatedPoint B S hS f F x ↔
        IsAssociatedOnSomeSchemeChartFibre B S hS f F x) ∧
      (IsRelativeWeaklyAssociatedPoint B S hS f F x ↔
        IsAssociatedOnEverySchemeChartFibre B S hS f F x) ∧
      (IsRelativeWeaklyAssociatedPoint B S hS f F x ↔
        IsAssociatedOnSomeEtaleChartSquare B S hS f F x) ∧
      (IsRelativeWeaklyAssociatedPoint B S hS f F x ↔
        IsAssociatedOnEveryEtaleChartSquare B S hS f F x) ∧
      ∀ (p₀ : FieldValuedPoint B S hS Y.1) [Mono (fieldMorphism B S hS Y.1 p₀)],
        p₀.class B S hS Y.1 = pointsMap B S hS X.1 f.hom x →
        ∀ x₀ : points B S hS (fibreAtFieldValuedPoint B S hS f p₀).1,
          pointsMap B S hS (fibreAtFieldValuedPoint B S hS f p₀).1
              (fibreAtFieldValuedPointProjection B S hS f p₀).hom x₀ = x →
            (IsRelativeWeaklyAssociatedPoint B S hS f F x ↔
              IsAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS f p₀)
                ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS f p₀)).obj F)
                x₀) := by
  have tfae := relativeWeakAssassin_tfae B S hS f F x
  have h1 : IsWeaklyAssociatedOnSomeSchemeChartFibre B S hS f F x ↔
      IsAssociatedOnSomeSchemeChartFibre B S hS f F x :=
    ⟨fun ⟨V, g, v, hg, hv, θ, hθ, hwa⟩ ↦ ⟨V, g, v, hg, hv, θ, hθ,
        isLocallyNoetherianFiberAt_schemeChart B S hS f noeth V g v hg hv, hwa⟩,
      fun ⟨V, g, v, hg, hv, θ, hθ, _, hwa⟩ ↦ ⟨V, g, v, hg, hv, θ, hθ, hwa⟩⟩
  have h2 : IsWeaklyAssociatedOnEverySchemeChartFibre B S hS f F x ↔
      IsAssociatedOnEverySchemeChartFibre B S hS f F x :=
    ⟨fun h V g v hg hv θ hθ ↦ ⟨isLocallyNoetherianFiberAt_schemeChart B S hS f noeth V g v hg hv,
        h V g v hg hv θ hθ⟩,
      fun h V g v hg hv θ hθ ↦ (h V g v hg hv θ hθ).2⟩
  have key {V U : BigFppfOver B S hS} (g : yoneda.obj V ⟶ Y.1) (hg : IsEtale B S hS g)
      (a : yoneda.obj U ⟶ pullback f.hom g) (ha : IsEtale B S hS a) (α : U ⟶ V)
      (hα : a ≫ pullback.snd f.hom g = yoneda.map α) (u : (BigFppfOver.toScheme B S hS).obj U)
      (hu : pointsMap B S hS (yoneda.obj U) (a ≫ pullback.fst f.hom g)
        ((pointsEquivScheme B S hS U).symm u) = x) :=
    mem_relativeAssassin_iff_mem_relativeWeaklyAssociatedPoints _
      (etaleChartSquareModule B S hS f F g a) u
      (isLocallyNoetherian_fiber_etaleChartSquare B S hS f noeth g hg a ha α hα u hu)
  have h3 : IsWeaklyAssociatedOnSomeEtaleChartSquare B S hS f F x ↔
      IsAssociatedOnSomeEtaleChartSquare B S hS f F x :=
    ⟨fun ⟨V, g, U, a, α, u, hg, ha, hα, hu, hmem⟩ ↦
        ⟨V, g, U, a, α, u, hg, ha, hα, hu, (key g hg a ha α hα u hu).2 hmem⟩,
      fun ⟨V, g, U, a, α, u, hg, ha, hα, hu, hmem⟩ ↦
        ⟨V, g, U, a, α, u, hg, ha, hα, hu, (key g hg a ha α hα u hu).1 hmem⟩⟩
  have h4 : IsWeaklyAssociatedOnEveryEtaleChartSquare B S hS f F x ↔
      IsAssociatedOnEveryEtaleChartSquare B S hS f F x :=
    ⟨fun h V g U a α u hg ha hα hu ↦ (key g hg a ha α hα u hu).2 (h V g U a α u hg ha hα hu),
      fun h V g U a α u hg ha hα hu ↦ (key g hg a ha α hα u hu).1 (h V g U a α u hg ha hα hu)⟩
  refine ⟨(tfae.out 5 1).trans h1, (tfae.out 5 2).trans h2, (tfae.out 5 3).trans h3,
    (tfae.out 5 4).trans h4, fun p₀ _ rep x₀ hx₀ ↦ ?_⟩
  obtain ⟨p, hp, hpN⟩ := noeth
  have hN : HasEtaleLocalProperty B S hS (fibreAtFieldValuedPoint B S hS f p₀).1
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    (isLocallyNoetherianFiberAt_iff_exists B S hS X.2 Y.2 f.hom _ p₀ rep).2 ⟨p, hp, hpN⟩
  exact ((isRelativeWeaklyAssociatedPoint_iff_of_mono B S hS f F p₀ rep).2 x₀ hx₀).trans
    ⟨fun hwa ↦ ⟨hN, hwa⟩, fun hwa ↦ hwa.2⟩

end AlgebraicGeometry.Space

end
