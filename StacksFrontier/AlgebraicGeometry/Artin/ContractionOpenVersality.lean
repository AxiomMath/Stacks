module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityCase2
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityRestrict
public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.VersalSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.OfIsSmoothULift

/-!
# Artin's contraction functor satisfies openness of versality

In the situation of Stacks 0GH8, recorded by `AlgebraicGeometry.Artin.ContractionSituation`, let
`F` be Artin's functor of Stacks 0GHA, `AlgebraicGeometry.Artin.contractionFunctor`. Then `F`
satisfies openness of versality, axiom [5] of Section 0GE6,
`AlgebraicGeometry.LocallyNoetherianOver.HasOpenVersality`.

## Main results

* `AlgebraicGeometry.Artin.contractionFunctor_hasOpenVersality`: `F` satisfies openness of
  versality.
* `AlgebraicGeometry.Artin.ContractionSituation.hasOpenVersality_of_formallySmooth_near`: `F`
  satisfies openness of versality as soon as every versal adic morphism `V_{/Z} ⟶ W` is formally
  smooth over an open neighbourhood of the point.
* `ContractionSituation.hasOpenVersality_of_formallySmooth_near_closedPoint`: the same, with that
  hypothesis asked only at closed points.

## References

* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
* [Stacks Project, Tag 0GIA](https://stacks.math.columbia.edu/tag/0GIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- If every adic morphism `g : V_{/Z} ⟶ W` out of the completion of a scheme `V` locally of
finite type over `S` along a closed `Z`, versal at a finite type point `v ∈ Z`, has formally smooth
restriction to the completion of an open subscheme containing `v`, then `F` satisfies openness of
versality. -/
theorem hasOpenVersality_of_formallySmooth_near
    (hsm : ∀ (V : BigFppfOver B S hS) (Z : Set (Space.points B S hS (yoneda.obj V)))
      (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W)
      (v : ((Over.post B.inclusion).obj V).left),
      LocallyOfFiniteType ((Over.post B.inclusion).obj V).hom →
      @IsClosed _ (Space.pointTopology B S hS (yoneda.obj V)) Z →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom →
      IsFiniteTypePoint v → (Space.pointsEquivScheme B S hS V).symm v ∈ Z →
      FormalSpace.IsVersalAtCompletion B S hS V Z c.W g v →
      ∃ (V₀ : BigFppfOver B S hS) (ι₀ : V₀ ⟶ V),
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι₀) ∧
        v ∈ Set.range ((BigFppfOver.toScheme B S hS).map ι₀) ∧
        Space.FormallySmooth (Space.completionSheafMap B S hS (yoneda.map ι₀) Z ≫ g).hom) :
    LocallyNoetherianOver.HasOpenVersality B S hS (contractionFunctor c) := by
  intro U hU x hx u₀ hu₀ hver
  subst hx
  by_cases hZ : (Space.pointsEquivScheme B S hS x.unop.1.unop.obj).symm u₀ ∈
      (x.unop.2 : Triple c x.unop.1.unop.obj).Z
  · obtain ⟨V₀, ι₀, hι₀, hO, hFS⟩ := hsm x.unop.1.unop.obj (x.unop.2 : Triple c _).Z
      (x.unop.2 : Triple c _).xhat u₀ hU (x.unop.2 : Triple c _).isClosed_Z
      (x.unop.2 : Triple c _).adic_xhat hu₀ hZ
      ((isVersalAt_iff_isVersalAtCompletion c x u₀ hZ).1 hver)
    exact exists_isVersalAt_of_mem_of_formallySmooth c x hU u₀ hZ V₀ ι₀ hι₀ hO hFS
  · exact exists_isVersalAt_of_not_mem c x hU u₀ hu₀ hZ hver

/-- If every adic morphism `g : V_{/Z} ⟶ W` out of the completion of a scheme `V` locally of
finite type over `S` along a closed `Z`, versal at a closed point `v ∈ Z`, has formally smooth
restriction to the completion of an open subscheme containing `v`, then `F` satisfies openness of
versality. -/
theorem hasOpenVersality_of_formallySmooth_near_closedPoint
    (hsm : ∀ (V : BigFppfOver B S hS) (Z : Set (Space.points B S hS (yoneda.obj V)))
      (g : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ c.W)
      (v : ((Over.post B.inclusion).obj V).left),
      LocallyOfFiniteType ((Over.post B.inclusion).obj V).hom →
      @IsClosed _ (Space.pointTopology B S hS (yoneda.obj V)) Z →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom →
      IsClosed ({v} : Set ((Over.post B.inclusion).obj V).left) →
      (Space.pointsEquivScheme B S hS V).symm v ∈ Z →
      FormalSpace.IsVersalAtCompletion B S hS V Z c.W g v →
      ∃ (V₀ : BigFppfOver B S hS) (ι₀ : V₀ ⟶ V),
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι₀) ∧
        v ∈ Set.range ((BigFppfOver.toScheme B S hS).map ι₀) ∧
        Space.FormallySmooth (Space.completionSheafMap B S hS (yoneda.map ι₀) Z ≫ g).hom) :
    LocallyNoetherianOver.HasOpenVersality B S hS (contractionFunctor c) := by
  intro U hU x hx u₀ hu₀ hver
  subst hx
  by_cases hZ : (Space.pointsEquivScheme B S hS x.unop.1.unop.obj).symm u₀ ∈
      (x.unop.2 : Triple c x.unop.1.unop.obj).Z
  · have hu₀' : u₀ ∈ Scheme.finiteTypePoints x.unop.1.unop.obj.left.obj := hu₀
    rw [Scheme.finiteTypePoints_eq_iUnion_opens] at hu₀'
    obtain ⟨O, p, hpc, hpu⟩ := Set.mem_iUnion.mp hu₀'
    let x₁ := restrictElement c x O
    let ι₁ := BigFppfOver.openSubHom B S hS x.unop.1.unop.obj O
    let j := ((Over.post B.inclusion).map ι₁).left
    have : _root_.AlgebraicGeometry.IsOpenImmersion j :=
      inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion O.ι)
    let u₁ : ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x₁).left := p
    have hju : j u₁ = u₀ := hpu
    have hU₁ : LocallyOfFiniteType
        ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x₁).hom := by
      have hjU : j ≫ ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj
          x).hom = ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj
            x₁).hom := Over.w ((Over.post B.inclusion).map ι₁)
      rw [← hjU]
      exact @locallyOfFiniteType_comp _ _ _ j _
        (inferInstanceAs (LocallyOfFiniteType O.ι)) hU
    have hZ₁ : (Space.pointsEquivScheme B S hS x₁.unop.1.unop.obj).symm u₁ ∈
        (x₁.unop.2 : Triple c x₁.unop.1.unop.obj).Z := by
      show Space.pointsMap B S hS _ (yoneda.map ι₁)
        ((Space.pointsEquivScheme B S hS _).symm u₁) ∈ (x.unop.2 : Triple c _).Z
      have h : Space.pointsMap B S hS _ (yoneda.map ι₁)
          ((Space.pointsEquivScheme B S hS _).symm u₁) =
          (Space.pointsEquivScheme B S hS x.unop.1.unop.obj).symm u₀ := by
        apply (Space.pointsEquivScheme B S hS x.unop.1.unop.obj).injective
        refine Eq.trans ?_ ((Space.pointsEquivScheme B S hS _).apply_symm_apply u₀).symm
        rw [← hju]
        show Space.pointsToScheme B S hS _ _ = _
        rw [Space.pointsToScheme_pointsMap_yoneda]
        exact congrArg _ ((Space.pointsEquivScheme B S hS _).apply_symm_apply u₁)
      rwa [h]
    obtain ⟨V₀, ι₀, hι₀, hv, hFS⟩ := hsm x₁.unop.1.unop.obj (x₁.unop.2 : Triple c _).Z
      (x₁.unop.2 : Triple c _).xhat u₁ hU₁ (x₁.unop.2 : Triple c _).isClosed_Z
      (x₁.unop.2 : Triple c _).adic_xhat (mem_closedPoints_iff.mp hpc) hZ₁
      ((isVersalAt_iff_isVersalAtCompletion c x₁ u₁ hZ₁).1
        ((isVersalAt_restrictElement_iff c x O u₁).2 (hju ▸ hver)))
    obtain ⟨W₁, hW₁, hW₁v⟩ :=
      exists_isVersalAt_of_mem_of_formallySmooth c x₁ hU₁ u₁ hZ₁ V₀ ι₀ hι₀ hv hFS
    refine ⟨⟨j '' (W₁ : Set ((LocallyNoetherianOver.elementsToOver B S hS
        (contractionFunctor c)).obj x₁).left), j.isOpenEmbedding.isOpenMap _ W₁.2⟩,
      ⟨u₁, hW₁, hju⟩, ?_⟩
    rintro _ ⟨u', hu'W, rfl⟩ hft
    exact (isVersalAt_restrictElement_iff c x O u').1
      (hW₁v u' hu'W (Deformation.Artin.isFiniteTypePoint_of_isOpenImmersion j u' hft))
  · exact exists_isVersalAt_of_not_mem c x hU u₀ hu₀ hZ hver

end AlgebraicGeometry.Artin.ContractionSituation

namespace AlgebraicGeometry.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open ContractionSituation in
/-- In the situation of Stacks 0GH8 the functor `F` of Stacks 0GHA satisfies openness of versality:
for every scheme `V` locally of finite type over `S`, every `ξ ∈ F(V)` and every finite type point
`v₀ ∈ V` at which `ξ` is versal, there is an open neighbourhood of `v₀` in `V` at every finite type
point of which `ξ` is versal. -/
@[stacks 0GIA]
theorem contractionFunctor_hasOpenVersality (c : ContractionSituation B S hS) :
    LocallyNoetherianOver.HasOpenVersality B S hS (contractionFunctor c) := by
  have := c.isLocallyNoetherian_base
  refine c.hasOpenVersality_of_formallySmooth_near_closedPoint
    fun V Z g v hV hZ hg hvc hvZ hvers ↦ ?_
  obtain ⟨U, i, hi, hv, hrep, hsm⟩ :=
    FormalSpace.exists_isOpenImmersion_smooth_of_isVersalAtCompletion B S hS V hV Z hZ c.W
      c.isLocallyNoetherian_W c.Wred c.WredInclusion c.isReduction_WredInclusion
      c.isLocallyOfFiniteType_Wred g hg v hvc
      ⟨_, hvZ, (Space.pointsEquivScheme B S hS V).apply_symm_apply v⟩ hvers
  exact ⟨U, i, hi, hv, Space.formallySmooth_of_hasPropertyULift_isSmoothULift _ hrep hsm⟩

end AlgebraicGeometry.Artin

end
