module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraicSpace

/-!
# The relative homogeneous spectrum of a graded algebra on an algebraic space

In Situation 0849 the relative Proj `π : Proj_X(𝒜) ⟶ X` is the algebraic space `F` of
Stacks 084B over `X` (Stacks 084C). Its base change along a scheme point `g : Z ⟶ X` is
`Proj_Z(g^*𝒜)`, and on a surjective étale presentation `(U, R)` of `X` the relative Projs
`P_U = Proj_U(𝒜_U)` and `P_R = Proj_R(𝒜_R)` form an étale presentation of `Proj_X(𝒜)`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.Proj`: the algebraic space `Proj_X(𝒜)`.
* `AlgebraicGeometry.Space.RelativeProjSituation.π`: its structure morphism to `X`.
* `AlgebraicGeometry.Space.RelativeProjSituation.baseChangeIso`: the canonical isomorphism
  `γ : Proj_Z(g^*𝒜) ≅ Proj_X(𝒜) ×_X Z` over `Z`, for every scheme point `g : Z ⟶ X`.
* `AlgebraicGeometry.Space.RelativeProjSituation.chartPresentation`: the étale presentation of
  `Proj_X(𝒜)` by `P_U` and `P_R`, for an étale presentation `(U, R)` of `X`.

## References

* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- The relative homogeneous spectrum `Proj_X(𝒜)` of a quasi-coherent graded `𝒪_X`-algebra on
an algebraic space `X` over `S`: the algebraic space `F` of Stacks 084B, the functor of
quadruples, with structure morphism `π`. -/
@[stacks 084C "Proj_X(A): the algebraic space F of Tag 084B, with structure morphism pi"]
def Proj : AlgebraicSpaces s.site s.base s.containsBase :=
  ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩

/-- The structure morphism `π : Proj_X(𝒜) ⟶ X` of the relative Proj. -/
@[stacks 084C "the structure morphism pi : Proj_X(A) -> X"]
def π : s.Proj ⟶ s.space :=
  ObjectProperty.homMk s.relativeProjπ

/-- The underlying functor of `Proj_X(𝒜)` is `s.relativeProjFunctor`. -/
theorem Proj_obj : s.Proj.1 = s.relativeProjFunctor :=
  rfl

/-- The underlying morphism of functors of `π` is `s.relativeProjπ`. -/
theorem π_hom : s.π.hom = s.relativeProjπ :=
  rfl

section BaseChange

/-- The pullback of `π` along a scheme point exists, as a local instance: since Mathlib v4.35.0,
instance search for this `HasPullback` in the presheaf category times out. -/
local instance hasPullback_π (Z : BigFppfOver s.site s.base s.containsBase)
    (g : yoneda.obj Z ⟶ s.space.1) : HasPullback s.π.hom g :=
  (s.relativeProjPoints.isPullback Z g).hasPullback

/-- The same instance for `s.relativeProjπ`, the underlying morphism of `π`. -/
local instance hasPullback_relativeProjπ (Z : BigFppfOver s.site s.base s.containsBase)
    (g : yoneda.obj Z ⟶ s.space.1) : HasPullback s.relativeProjπ g :=
  (s.relativeProjPoints.isPullback Z g).hasPullback

/-- For a scheme point `g : Z ⟶ X`, the canonical isomorphism
`γ : Proj_Z(g^*𝒜) ≅ Proj_X(𝒜) ×_X Z` of Stacks 084B; the scheme of
`s.relativeProjPoints.fibre Z g` is `Proj_Z(g^*𝒜)` by `s.relativeProjPoints.fibreIso Z g`. -/
@[stacks 084C "the canonical isomorphism gamma : Proj_U(phi^*A) -> Proj_X(A) x_X U over U"]
def baseChangeIso (Z : BigFppfOver s.site s.base s.containsBase)
    (g : yoneda.obj Z ⟶ s.space.1) :
    yoneda.obj (s.relativeProjPoints.fibre Z g) ≅ pullback s.π.hom g :=
  (s.relativeProjPoints.isPullback Z g).isoPullback

/-- The isomorphism `γ` followed by the projection `Proj_X(𝒜) ×_X Z ⟶ Proj_X(𝒜)` is the map
`Proj_Z(g^*𝒜) ⟶ Proj_X(𝒜)`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_fst (Z : BigFppfOver s.site s.base s.containsBase)
    (g : yoneda.obj Z ⟶ s.space.1) :
    (s.baseChangeIso Z g).hom ≫ pullback.fst s.π.hom g = s.relativeProjPoints.fibreToSpace Z g :=
  (s.relativeProjPoints.isPullback Z g).isoPullback_hom_fst

/-- The isomorphism `γ` lies over `Z`. -/
@[reassoc (attr := simp)]
theorem baseChangeIso_hom_snd (Z : BigFppfOver s.site s.base s.containsBase)
    (g : yoneda.obj Z ⟶ s.space.1) :
    (s.baseChangeIso Z g).hom ≫ pullback.snd s.π.hom g =
      yoneda.map (s.relativeProjPoints.fibreHom Z g) :=
  (s.relativeProjPoints.isPullback Z g).isoPullback_hom_snd

end BaseChange

/-- The base change along a scheme point `Z ⟶ X` is the relative Proj over `Z` of the
restricted algebra: `Z ×_X Proj_X(𝒜) = Proj_Z(g^*𝒜)` as a cartesian square. -/
theorem isPullback_fibre (Z : BigFppfOver s.site s.base s.containsBase)
    (g : yoneda.obj Z ⟶ s.space.1) :
    IsPullback (s.relativeProjPoints.fibreToSpace Z g)
      (yoneda.map (s.relativeProjPoints.fibreHom Z g)) s.π.hom g :=
  s.relativeProjPoints.isPullback Z g

/-! ### The glueing description on an étale presentation -/

section Chart

variable {s}

variable (P : Presentation s.site s.base s.containsBase s.space.1 s.space.2)

/-- The relative Proj `P_U = Proj_U(𝒜_U)` over the chart of the presentation. -/
abbrev chartProj : BigFppfOver s.site s.base s.containsBase :=
  s.relativeProjPoints.fibre P.U P.toSpace

/-- The relative Proj `P_R = Proj_R(𝒜_R)` over the relation of the presentation, for the
restriction of `𝒜` along `R ⟶ U ⟶ X` through the target map. -/
abbrev relationProj : BigFppfOver s.site s.base s.containsBase :=
  s.relativeProjPoints.fibre P.R (yoneda.map P.target ≫ P.toSpace)

/-- The maps `P_R ⟶ Proj_X(𝒜) ⟶ X` and `P_R ⟶ R ⟶ U ⟶ X`, through the target map `R ⟶ U`,
agree. -/
theorem relationProj_w_target :
    s.relativeProjPoints.fibreToSpace P.R (yoneda.map P.target ≫ P.toSpace) ≫ s.π.hom =
      yoneda.map (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace) ≫
        P.target) ≫ P.toSpace := by
  rw [Functor.map_comp, Category.assoc]
  exact (s.relativeProjPoints.isPullback P.R (yoneda.map P.target ≫ P.toSpace)).w

/-- The maps `P_R ⟶ Proj_X(𝒜) ⟶ X` and `P_R ⟶ R ⟶ U ⟶ X`, through the source map `R ⟶ U`,
agree. -/
theorem relationProj_w_source :
    s.relativeProjPoints.fibreToSpace P.R (yoneda.map P.target ≫ P.toSpace) ≫ s.π.hom =
      yoneda.map (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace) ≫
        P.source) ≫ P.toSpace := by
  rw [Functor.map_comp, Category.assoc, ← P.isPullback.w]
  exact (s.relativeProjPoints.isPullback P.R (yoneda.map P.target ≫ P.toSpace)).w

/-- The target projection `P_R ⟶ P_U` of the relative Projs, lying over the target map
`R ⟶ U`. -/
def relationProjTarget : relationProj P ⟶ chartProj P :=
  Yoneda.fullyFaithful.preimage ((s.relativeProjPoints.isPullback P.U P.toSpace).lift
    (s.relativeProjPoints.fibreToSpace P.R (yoneda.map P.target ≫ P.toSpace))
    (yoneda.map (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace) ≫
      P.target)) (relationProj_w_target P))

/-- The source projection `P_R ⟶ P_U` of the relative Projs, lying over the source map
`R ⟶ U`. -/
def relationProjSource : relationProj P ⟶ chartProj P :=
  Yoneda.fullyFaithful.preimage ((s.relativeProjPoints.isPullback P.U P.toSpace).lift
    (s.relativeProjPoints.fibreToSpace P.R (yoneda.map P.target ≫ P.toSpace))
    (yoneda.map (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace) ≫
      P.source)) (relationProj_w_source P))

/-- The target projection `P_R ⟶ P_U` commutes with the maps to `Proj_X(𝒜)`. -/
@[reassoc]
theorem map_relationProjTarget_fibreToSpace :
    yoneda.map (relationProjTarget P) ≫ s.relativeProjPoints.fibreToSpace P.U P.toSpace =
      s.relativeProjPoints.fibreToSpace P.R (yoneda.map P.target ≫ P.toSpace) := by
  rw [relationProjTarget, Functor.FullyFaithful.map_preimage]
  exact (s.relativeProjPoints.isPullback P.U P.toSpace).lift_fst _ _ _

/-- The source projection `P_R ⟶ P_U` commutes with the maps to `Proj_X(𝒜)`. -/
@[reassoc]
theorem map_relationProjSource_fibreToSpace :
    yoneda.map (relationProjSource P) ≫ s.relativeProjPoints.fibreToSpace P.U P.toSpace =
      s.relativeProjPoints.fibreToSpace P.R (yoneda.map P.target ≫ P.toSpace) := by
  rw [relationProjSource, Functor.FullyFaithful.map_preimage]
  exact (s.relativeProjPoints.isPullback P.U P.toSpace).lift_fst _ _ _

/-- The target projection `P_R ⟶ P_U` lies over the target map `R ⟶ U`. -/
@[reassoc]
theorem relationProjTarget_fibreHom :
    relationProjTarget P ≫ s.relativeProjPoints.fibreHom P.U P.toSpace =
      s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace) ≫ P.target := by
  apply Yoneda.fullyFaithful.map_injective
  rw [Functor.map_comp, relationProjTarget, Functor.FullyFaithful.map_preimage]
  exact (s.relativeProjPoints.isPullback P.U P.toSpace).lift_snd _ _ _

/-- The source projection `P_R ⟶ P_U` lies over the source map `R ⟶ U`. -/
@[reassoc]
theorem relationProjSource_fibreHom :
    relationProjSource P ≫ s.relativeProjPoints.fibreHom P.U P.toSpace =
      s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace) ≫ P.source := by
  apply Yoneda.fullyFaithful.map_injective
  rw [Functor.map_comp, relationProjSource, Functor.FullyFaithful.map_preimage]
  exact (s.relativeProjPoints.isPullback P.U P.toSpace).lift_snd _ _ _

/-- If `f : P_R ⟶ P_U` lies over `e : R ⟶ U`, where `e` has the same composite with the chart
as the target map, then `P_R = P_U ×_{U, e} R` as presheaves. -/
private theorem isPullback_map_relationProj_of_comm (e : P.R ⟶ P.U)
    (he : yoneda.map P.target ≫ P.toSpace = yoneda.map e ≫ P.toSpace)
    (f : relationProj P ⟶ chartProj P)
    (hf : yoneda.map f ≫ s.relativeProjPoints.fibreToSpace P.U P.toSpace =
      s.relativeProjPoints.fibreToSpace P.R (yoneda.map P.target ≫ P.toSpace))
    (hf' : f ≫ s.relativeProjPoints.fibreHom P.U P.toSpace =
      s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace) ≫ e) :
    IsPullback (yoneda.map f)
      (yoneda.map (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace)))
      (yoneda.map (s.relativeProjPoints.fibreHom P.U P.toSpace)) (yoneda.map e) := by
  have hout := (congrArg (IsPullback
    (s.relativeProjPoints.fibreToSpace P.R (yoneda.map P.target ≫ P.toSpace))
    (yoneda.map (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace)))
    s.π.hom) he).mp
      (s.relativeProjPoints.isPullback P.R (yoneda.map P.target ≫ P.toSpace))
  rw [← hf] at hout
  refine IsPullback.of_right hout ?_ (s.relativeProjPoints.isPullback P.U P.toSpace)
  rw [← Functor.map_comp, ← Functor.map_comp, hf']

/-- `P_R = P_U ×_{U, t} R`, as presheaves. -/
theorem isPullback_map_relationProjTarget :
    IsPullback (yoneda.map (relationProjTarget P))
      (yoneda.map (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace)))
      (yoneda.map (s.relativeProjPoints.fibreHom P.U P.toSpace)) (yoneda.map P.target) :=
  isPullback_map_relationProj_of_comm P _ rfl _ (map_relationProjTarget_fibreToSpace P)
    (relationProjTarget_fibreHom P)

/-- `P_R = P_U ×_{U, s} R`, as presheaves. -/
theorem isPullback_map_relationProjSource :
    IsPullback (yoneda.map (relationProjSource P))
      (yoneda.map (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace)))
      (yoneda.map (s.relativeProjPoints.fibreHom P.U P.toSpace)) (yoneda.map P.source) :=
  isPullback_map_relationProj_of_comm P _ P.isPullback.w _ (map_relationProjSource_fibreToSpace P)
    (relationProjSource_fibreHom P)

/-- `P_R = P_U ×_{U, t} R`. -/
theorem isPullback_relationProjTarget :
    IsPullback (relationProjTarget P)
      (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace))
      (s.relativeProjPoints.fibreHom P.U P.toSpace) P.target :=
  IsPullback.of_map yoneda (relationProjTarget_fibreHom P) (isPullback_map_relationProjTarget P)

/-- `P_R = P_U ×_{U, s} R`. -/
theorem isPullback_relationProjSource :
    IsPullback (relationProjSource P)
      (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace))
      (s.relativeProjPoints.fibreHom P.U P.toSpace) P.source :=
  IsPullback.of_map yoneda (relationProjSource_fibreHom P) (isPullback_map_relationProjSource P)

/-- `P_U ×_{Proj_X(𝒜)} P_U = P_R`, with projections `relationProjTarget P` and
`relationProjSource P`. -/
theorem isPullback_relationProj :
    IsPullback (yoneda.map (relationProjTarget P)) (yoneda.map (relationProjSource P))
      (s.relativeProjPoints.fibreToSpace P.U P.toSpace)
      (s.relativeProjPoints.fibreToSpace P.U P.toSpace) := by
  have hout := (isPullback_map_relationProjTarget P).flip.paste_horiz P.isPullback.flip
  have hsrc : yoneda.map (s.relativeProjPoints.fibreHom P.R (yoneda.map P.target ≫ P.toSpace)) ≫
      yoneda.map P.source = yoneda.map (relationProjSource P) ≫
        yoneda.map (s.relativeProjPoints.fibreHom P.U P.toSpace) := by
    rw [← Functor.map_comp, ← Functor.map_comp, relationProjSource_fibreHom]
  rw [hsrc, ← (s.relativeProjPoints.isPullback P.U P.toSpace).w] at hout
  refine (IsPullback.of_right hout ?_ (s.relativeProjPoints.isPullback P.U P.toSpace).flip).flip
  rw [map_relationProjSource_fibreToSpace, map_relationProjTarget_fibreToSpace]

/-- The chart `P_U ⟶ Proj_X(𝒜)` lies over the chart `U ⟶ X`. -/
theorem chartPresentation_toSpace_comp :
    s.relativeProjPoints.fibreToSpace P.U P.toSpace ≫ s.π.hom =
      yoneda.map (s.relativeProjPoints.fibreHom P.U P.toSpace) ≫ P.toSpace :=
  (s.relativeProjPoints.isPullback P.U P.toSpace).w

/-- The chart `P_U = Proj_X(𝒜) ×_X U ⟶ Proj_X(𝒜)` is étale: it is the base change of the
étale chart `U ⟶ X`. -/
theorem chartProj_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme s.site s.base s.containsBase)))
    (s.relativeProjPoints.fibreToSpace P.U P.toSpace) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (s.relativeProjPoints.isPullback P.U P.toSpace).flip P.etale

/-- The chart `P_U = Proj_X(𝒜) ×_X U ⟶ Proj_X(𝒜)` is surjective: it is the base change of the
surjective chart `U ⟶ X`. -/
theorem chartProj_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme s.site s.base s.containsBase)))
    (s.relativeProjPoints.fibreToSpace P.U P.toSpace) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (s.relativeProjPoints.isPullback P.U P.toSpace).flip P.surjective

/-- The two projections `P_R ⇉ P_U` form an étale equivalence relation. -/
theorem isEtaleEquivalenceRelation_relationProj :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (prod.lift ((Over.post s.site.inclusion).map (relationProjTarget P))
        ((Over.post s.site.inclusion).map (relationProjSource P))) := by
  have hP := isPullback_relationProj P
  have hEt := chartProj_etale P
  have hRel := isEquivalenceRelation_of_isPullback s.site s.base s.containsBase
    (s.relativeProjPoints.fibreToSpace P.U P.toSpace) _ _ hP
  have hSe : Etale ((BigFppfOver.toScheme s.site s.base s.containsBase).map
      (relationProjSource P)) := hEt.property _ _ _ hP
  have hTe : Etale ((BigFppfOver.toScheme s.site s.base s.containsBase).map
      (relationProjTarget P)) := hEt.property _ _ _ hP.flip
  refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
  · simpa only [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
      prod.lift_fst, prod.lift_snd] using hRel
  · simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd]
    exact hSe
  · simp only [Stacks.Groupoids.PreRelation.target, prod.lift_fst]
    exact hTe

/-- For an étale presentation `(U, R)` of `X`, the relative Projs `P_U = Proj_U(𝒜_U)` and
`P_R = Proj_R(𝒜_R)` form an étale presentation of `Proj_X(𝒜)`: the chart
`P_U = Proj_X(𝒜) ×_X U ⟶ Proj_X(𝒜)` is surjective and étale and `P_U ×_{Proj_X(𝒜)} P_U = P_R`,
the two projections lying over the two maps `R ⇉ U` and exhibiting `P_R` as `P_U ×_U R` along
each. -/
@[stacks 084C "the etale covering P_U -> Proj_X(A) with P_U x_P P_U = P_R"]
def chartPresentation : Presentation s.site s.base s.containsBase s.Proj.1 s.Proj.2 where
  U := chartProj P
  R := relationProj P
  target := relationProjTarget P
  source := relationProjSource P
  isEtaleEquivalenceRelation := isEtaleEquivalenceRelation_relationProj P
  toSpace := s.relativeProjPoints.fibreToSpace P.U P.toSpace
  surjective := chartProj_surjective P
  etale := chartProj_etale P
  isPullback := isPullback_relationProj P

/-- The chart of `chartPresentation P` is `P_U`. -/
@[simp] theorem chartPresentation_U : (chartPresentation P).U = chartProj P := rfl
/-- The relation of `chartPresentation P` is `P_R`. -/
@[simp] theorem chartPresentation_R : (chartPresentation P).R = relationProj P := rfl
/-- The target map of `chartPresentation P` is `relationProjTarget P`. -/
@[simp] theorem chartPresentation_target :
    (chartPresentation P).target = relationProjTarget P := rfl
/-- The source map of `chartPresentation P` is `relationProjSource P`. -/
@[simp] theorem chartPresentation_source :
    (chartPresentation P).source = relationProjSource P := rfl
/-- The chart map of `chartPresentation P` is the map `P_U ⟶ Proj_X(𝒜)`. -/
@[simp] theorem chartPresentation_toSpace :
    (chartPresentation P).toSpace = s.relativeProjPoints.fibreToSpace P.U P.toSpace := rfl

end Chart

end RelativeProjSituation

end AlgebraicGeometry.Space

end
