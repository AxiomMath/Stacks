module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStack
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingFunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Situation 0DKU at a limit of test schemes in Situation 0DLE

Let `f : X ⟶ Y` be the proper, flat, finitely presented morphism of algebraic spaces of
Situation 0DLE, and let `T = lim Tᵢ` be a directed limit of affine test schemes over `Y`. The
proof of Stacks 0DLJ applies Stacks 0DKW to the system of base changes `X_{Tᵢ}` with limit
`X_T`, which is an instance of Situation 0DKU: the inverse system is `{Tᵢ}` read as algebraic
spaces, the space over the initial stage `i₀` is `X_{T_{i₀}} ⟶ T_{i₀}`, and its base changes to
the later stages and to the limit are `X_{Tᵢ}` and `X_T`. This file constructs that instance.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.relativeDescentSituation`: Situation 0DKU for the
  base changes of `f` along a directed limit of affine test schemes over `Y`.
* `AlgebraicGeometry.Space.ComplexesSituation.isLimitYonedaMapCone`: a directed limit of test
  schemes over `Y` whose underlying schemes form a limit is a limit of the presheaves they
  represent.

## Main results

* `AlgebraicGeometry.Space.exists_stage_comp_eq_of_isLocallyOfFinitePresentation` and
  `AlgebraicGeometry.Space.exists_map_comp_eq_of_isLocallyOfFinitePresentation`: for an algebraic
  space `Y` locally of finite presentation over `S` and a cofiltered limit `T = lim Tᵢ` of affine
  schemes, every morphism `T ⟶ Y` factors through a stage, and two factorizations agree at a later
  stage. This is the first step of the proof of Stacks 0DLJ, where Stacks 05N0 makes the
  comparison `colim Y(Tᵢ) ⟶ Y(T)` bijective and reduces to limits of schemes over `Y`.

## Implementation notes

The base changes in the situation are literally those of the standing data: `X₀ = X_{T_{i₀}}`,
`Xᵢ = X_{Tᵢ}` and `X = X_T` are `AlgebraicGeometry.Space.CoherentSituation.space`, and every map
between them is `AlgebraicGeometry.Space.CoherentSituation.relativeMap`. So an object of
`D(𝒪_{X_T})` is, with no transport, an object of the derived category of the limit base change of
the situation, which is what lets Stacks 0DKW be applied to the objects of `Complexes_{X/Y}` over
`T`. The cartesian squares are `AlgebraicGeometry.Space.isPullback_baseChangeMap`, read in
presheaves.

The limit cone is required to be a limit after passing to schemes, as in the definition of
limit preservation of Stacks 07XL. It is a limit of schemes over `S` because the forgetful
functor of a slice reflects connected limits, and then a limit of presheaves because the Yoneda
embedding preserves limits.

## References

* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DLE](https://stacks.math.columbia.edu/tag/0DLE)
* [Stacks Project, Tag 0DLJ](https://stacks.math.columbia.edu/tag/0DLJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

variable {D} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {T : Iᵒᵖ ⥤ SchemesOver D.Y} {c : Cone T}

/-- A directed limit of test schemes over `Y` whose underlying schemes form a limit is a limit
of the presheaves they represent: the forgetful functor of the slice of schemes over `S`
reflects connected limits, and the Yoneda embedding preserves limits. -/
def isLimitYonedaMapCone
    (hc : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone c)) :
    IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙ yoneda).mapCone c) := by
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected Iᵒᵖ
  have : ReflectsLimitsOfShape Iᵒᵖ (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme, BigFppfOver.forget]
    infer_instance
  have hc' : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).mapCone c) :=
    isLimitOfReflects (BigFppfOver.toScheme B S hS) hc
  exact isLimitOfPreserves yoneda hc'

variable (D) (hZ : B.Contains (⊤_ Scheme.{u})) (T) (c)

/-- **Situation 0DKU for the base changes along a directed limit of affine test schemes.**
For a directed inverse system `{Tᵢ}` of affine test schemes over `Y` with limit `T` and a stage
`i₀`, the inverse system of algebraic spaces is `{Tᵢ}`, the flat finitely presented space over
the initial stage is `X_{T_{i₀}} ⟶ T_{i₀}`, its base changes are `X_{Tᵢ}` for `i₀ ≤ i`, and its
base change to the limit is `X_T`. -/
def relativeDescentSituation
    (hc : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙
      BigFppfOver.toScheme B S hS).mapCone c))
    (hT : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj (op i)).left)) (i₀ : I) :
    RelativeDescentSituation B S hS hZ I where
  Y := T ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙ yoneda
  limitCone := (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y ⋙ yoneda).mapCone c
  isLimit := isLimitYonedaMapCone hc
  stage_isAlgebraicSpace i := isAlgebraicSpace_yoneda B S hS _
  limit_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS _
  stage_isQuasiCompact i := isQuasiCompactSpace_yoneda_of_isAffine B S hS _ (hT i)
  stage_isQuasiSeparated i := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).obj (T.obj (op i)))) := hT i
    exact isAbsolutelyQuasiSeparated_yoneda_obj B S hS hZ _ inferInstance
  transition_isAffine i j hij := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).obj (T.obj (op i)))) := hT i
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).obj (T.obj (op j)))) := hT j
    exact isAffineHom_of_presheaf
      ((presheaf_yoneda_map_iff B S hS
          (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance _).mpr
        (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
  i₀ := i₀
  X₀ := (D.space (T.obj (op i₀))).obj
  p₀ := (D.projection (T.obj (op i₀))).hom
  initial_isAlgebraicSpace := (D.space (T.obj (op i₀))).property
  initial_isFlat := D.projection_isFlat _
  initial_isFinitePresentation := D.toCoherentSituation.isFinitePresentation_projection _
  Xᵢ i _ := (D.space (T.obj (op i))).obj
  stageX_isAlgebraicSpace i _ := (D.space (T.obj (op i))).property
  toX₀ i hi := (D.relativeMap (T.map (homOfLE hi).op)).hom
  toYᵢ i _ := (D.projection (T.obj (op i))).hom
  stage_isPullback i hi :=
    (AlgebraicSpaces.isPullback_hom B S hS
      (isPullback_baseChangeMap D.f (T.map (homOfLE hi).op))).flip
  fᵢⱼ i j _ _ hij := (D.relativeMap (T.map (homOfLE hij).op)).hom
  fᵢⱼ_toYᵢ i j _ _ hij :=
    congrArg InducedCategory.Hom.hom (baseChangeMap_comp_inclusion D.f (T.map (homOfLE hij).op))
  fᵢⱼ_toX₀ i j hi hj hij := by
    have h : D.relativeMap (T.map (homOfLE hij).op) ≫ D.relativeMap (T.map (homOfLE hi).op) =
        D.relativeMap (T.map (homOfLE hj).op) := by
      rw [← baseChangeMap_comp, ← T.map_comp]
      rfl
    exact congrArg InducedCategory.Hom.hom h
  X := (D.space c.pt).obj
  X_isAlgebraicSpace := (D.space c.pt).property
  toInitial := (D.relativeMap (c.π.app (op i₀))).hom
  toLimit := (D.projection c.pt).hom
  limit_isPullback :=
    (AlgebraicSpaces.isPullback_hom B S hS
      (isPullback_baseChangeMap D.f (c.π.app (op i₀)))).flip
  fᵢ i _ := (D.relativeMap (c.π.app (op i))).hom
  fᵢ_toYᵢ i _ :=
    congrArg InducedCategory.Hom.hom (baseChangeMap_comp_inclusion D.f (c.π.app (op i)))
  fᵢ_toX₀ i hi := by
    have h : D.relativeMap (c.π.app (op i)) ≫ D.relativeMap (T.map (homOfLE hi).op) =
        D.relativeMap (c.π.app (op i₀)) := by
      rw [← baseChangeMap_comp, Cone.w]
    exact congrArg InducedCategory.Hom.hom h

end ComplexesSituation

/-! ### Morphisms to a space locally of finite presentation over a limit -/

/-- Two morphisms from a scheme-space to `Y` are equal when their Yoneda elements are. -/
private theorem schemeSpace_hom_ext_of_yonedaEquiv_eq {Y : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} {g g' : schemeSpace U ⟶ Y}
    (h : yonedaEquiv (show yoneda.obj U ⟶ Y.1 from g.hom) =
      yonedaEquiv (show yoneda.obj U ⟶ Y.1 from g'.hom)) : g = g' :=
  ObjectProperty.hom_ext _ (yonedaEquiv.injective h)

/-- The Yoneda element of a precomposition with `schemeSpaceMap f` is the restriction along `f`. -/
private theorem yonedaEquiv_schemeSpaceMap_comp {Y : AlgebraicSpaces B S hS}
    {U V : BigFppfOver B S hS} (f : U ⟶ V) (g : schemeSpace V ⟶ Y) :
    yonedaEquiv (show yoneda.obj U ⟶ Y.1 from (schemeSpaceMap f ≫ g).hom) =
      Y.1.map f.op (yonedaEquiv (show yoneda.obj V ⟶ Y.1 from g.hom)) :=
  (yonedaEquiv_naturality (show yoneda.obj V ⟶ Y.1 from g.hom) f).symm

section StageFactorization

variable {Y : AlgebraicSpaces B S hS}
  (hY : IsLocallyOfFinitePresentation B S hS (terminal.from Y.1))
  {J : Type u} [Category.{u} J] [IsCofiltered J] {F : J ⥤ BigFppfOver B S hS} {c : Cone F}
  (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
  (hF : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (F.obj j)))
  (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
include hY hc hF hpt

/-- **Existence half of the stage factorization of Stacks 05N0.** Let `T = lim Tᵢ` be a
cofiltered limit of affine schemes over `S` and let `Y` be an algebraic space locally of finite
presentation over `S`. Every morphism `T ⟶ Y` factors through some stage `Tᵢ`.

This is the bottom horizontal arrow of the proof of Stacks 0DLJ being essentially surjective:
`colim Y(Tᵢ) ⟶ Y(T)` is onto. -/
theorem exists_stage_comp_eq_of_isLocallyOfFinitePresentation (g : schemeSpace c.pt ⟶ Y) :
    ∃ (j : J) (gj : schemeSpace (F.obj j) ⟶ Y), schemeSpaceMap (c.π.app j) ≫ gj = g := by
  obtain ⟨hcol⟩ := limitPreserving_of_isLocallyOfFinitePresentation B S hS Y.2 hY J F c hc hF hpt
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcol (yonedaEquiv g.hom)
  refine ⟨unop j, ObjectProperty.homMk (yonedaEquiv.symm y), ?_⟩
  apply schemeSpace_hom_ext_of_yonedaEquiv_eq
  rw [yonedaEquiv_schemeSpaceMap_comp]
  exact (congrArg _ (Equiv.apply_symm_apply _ _)).trans hy

/-- **Uniqueness half of the stage factorization of Stacks 05N0.** Let `T = lim Tᵢ` be a
cofiltered limit of affine schemes over `S` and let `Y` be an algebraic space locally of finite
presentation over `S`. Two morphisms `Tᵢ ⟶ Y` which agree on `T` agree on some later stage.

This is the bottom horizontal arrow of the proof of Stacks 0DLJ being injective on the colimit
`colim Y(Tᵢ) ⟶ Y(T)`. -/
theorem exists_map_comp_eq_of_isLocallyOfFinitePresentation {j : J}
    (g g' : schemeSpace (F.obj j) ⟶ Y)
    (h : schemeSpaceMap (c.π.app j) ≫ g = schemeSpaceMap (c.π.app j) ≫ g') :
    ∃ (k : J) (m : k ⟶ j), schemeSpaceMap (F.map m) ≫ g = schemeSpaceMap (F.map m) ≫ g' := by
  obtain ⟨hcol⟩ := limitPreserving_of_isLocallyOfFinitePresentation B S hS Y.2 hY J F c hc hF hpt
  let x : Y.1.obj (op (F.obj j)) := yonedaEquiv (show yoneda.obj (F.obj j) ⟶ Y.1 from g.hom)
  let x' : Y.1.obj (op (F.obj j)) := yonedaEquiv (show yoneda.obj (F.obj j) ⟶ Y.1 from g'.hom)
  have hx : (Y.1.mapCocone c.op).ι.app (op j) x = (Y.1.mapCocone c.op).ι.app (op j) x' := by
    change Y.1.map (c.π.app j).op x = Y.1.map (c.π.app j).op x'
    rw [← yonedaEquiv_schemeSpaceMap_comp, ← yonedaEquiv_schemeSpaceMap_comp, h]
  obtain ⟨k, m, hm⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcol x x').1 hx
  refine ⟨unop k, m.unop, schemeSpace_hom_ext_of_yonedaEquiv_eq ?_⟩
  rw [yonedaEquiv_schemeSpaceMap_comp, yonedaEquiv_schemeSpaceMap_comp]
  exact hm

end StageFactorization

end AlgebraicGeometry.Space

end
