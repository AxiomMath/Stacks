module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpInjectivePoints

/-!
# `𝒪_T ≅ f_{T, *}𝒪_{X_T}` for every `T` forces `f` to be surjective

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  If the structure map
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the base change is an isomorphism for every scheme `T` over `Y` (the
hypothesis of Stacks 0D27, `AlgebraicGeometry.Space.PicardSituation.StructureSheafMapIso`), then
`f` is surjective: over a field-valued point `Spec(k) ⟶ Y` the base change `X_k` is not empty,
since `k` embeds in its functions.

## Main results

* `AlgebraicGeometry.Space.nonempty_points_baseChangeSpace_of_isIso_structureSharp`: if `T` is a
  nonempty test scheme and `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism, then `X_T` has a point.
* `AlgebraicGeometry.Space.isSurjective_of_isIso_structureSharp`: if this holds for every `T`,
  then `f` is surjective.

## References

* [Stacks Project, Tag 0D2C](https://stacks.math.columbia.edu/tag/0D2C)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

/-- **If `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism at a nonempty test scheme `T`, then `X_T` has
a point.** -/
theorem nonempty_points_baseChangeSpace_of_isIso_structureSharp (f : X ⟶ Y) (T : SchemesOver Y)
    (hT : Nonempty ((BigFppfOver.toScheme B S hS).obj T.left))
    (h : IsIso (structureSharp B S hS (baseChangeInclusion f T))) :
    Nonempty (points B S hS (baseChangeSpace f T).1) := by
  let V := idEtaleChart B S hS T.left
  have hV : Nontrivial ((structureRingSheaf B S hS
      ((schemeSpaceFunctor B S hS).obj T.left)).obj.obj (op V)) :=
    (((BigFppfOver.toScheme B S hS).obj T.left).presheaf.germ ⊤ hT.some
      trivial).hom.domain_nontrivial
  have hinj : Function.Injective
      ((structureSharp B S hS (baseChangeInclusion f T)).hom.app (op V)) := by
    have : IsIso (structureSharp B S hS (baseChangeInclusion f T)).hom :=
      inferInstanceAs (IsIso ((sheafToPresheaf _ _).map (structureSharp B S hS
        (baseChangeInclusion f T))))
    exact (ConcreteCategory.bijective_of_isIso
      ((structureSharp B S hS (baseChangeInclusion f T)).hom.app (op V))).1
  obtain ⟨w⟩ := nonempty_points_chartBaseChangeSpace B S hS (baseChangeInclusion f T) V hV hinj
  exact ⟨pointsMap B S hS _ ((SpacesEtale.inclusion B S hS (baseChangeSpace f T)).obj
    (chartBaseChange B S hS (baseChangeInclusion f T) V)).hom.hom w⟩

/-- **A morphism `f : X ⟶ Y` with `𝒪_T ≅ f_{T, *}𝒪_{X_T}` for every test scheme `T` is
surjective.** -/
theorem isSurjective_of_isIso_structureSharp (f : X ⟶ Y)
    (hiso : ∀ T : SchemesOver Y, IsIso (structureSharp B S hS (baseChangeInclusion f T))) :
    IsSurjective B S hS f.hom := by
  intro y
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  let h : (schemeSpaceFunctor B S hS).obj (p.siteObject B S hS Y.1) ⟶ Y :=
    ObjectProperty.homMk (yonedaEquiv.symm p.value)
  let T : SchemesOver Y := CostructuredArrow.mk h
  have hT : Nonempty ((BigFppfOver.toScheme B S hS).obj T.left) :=
    ⟨(pointsEquivScheme B S hS T.left)
      ((FieldValuedPoint.tautological B S hS p).class B S hS _)⟩
  obtain ⟨w⟩ := nonempty_points_baseChangeSpace_of_isIso_structureSharp f T hT (hiso T)
  refine ⟨pointsMap B S hS _ (baseChangeProjection f T).hom w, ?_⟩
  have hw : (baseChangeProjection f T).hom ≫ f.hom =
      (baseChangeInclusion f T).hom ≫ (yonedaEquiv.symm p.value) :=
    congrArg InducedCategory.Hom.hom (AlgebraicSpaces.isPullback_fiberProduct B S hS f T.hom).w
  rw [pointsMap_apply_comm B S hS hw]
  exact FieldValuedPoint.pointsMap_eq_class B S hS p _

end AlgebraicGeometry.Space

end
