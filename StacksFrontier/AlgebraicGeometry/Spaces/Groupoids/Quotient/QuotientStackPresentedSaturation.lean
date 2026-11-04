module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentedObjectCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackSchemePoints

/-!
# From algebraicity of a quotient stack to a saturating presented point

The converse of [Stacks, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ) asks, from
algebraicity of `[U/R]`, for a morphism `g : U' ⟶ U` whose saturation `U' ×_{g, U, t} R ⟶ U` is a
surjection of sheaves and whose restricted groupoid has flat, locally finitely presented source and
target. This file supplies the morphism and the surjectivity.

## Main results

* `AlgebraicGeometry.Stack.exists_presented_point_locallySurjective_saturation` — the geometric
  half of that converse: the presented point of a flat finitely presented refinement of a scheme
  atlas has locally surjective saturation.

## Implementation notes

The morphism is the [Stacks, Tag 044X](https://stacks.math.columbia.edu/tag/044X) presentation of
the pullback of an atlas object along a surjective flat finitely presented cover, and the
2-isomorphism clause pins it down as that presentation, so the existential is not satisfied by the
identity. The flatness and local finite presentation of the restricted source and target reduce,
by `AlgebraicGeometry.Stack.restrictionSource_property_of_saturation` and
`AlgebraicGeometry.Stack.restrictionTarget_property_of_restrictionSource`, to the single statement
that the saturation is flat and locally of finite presentation; that statement is not proved here.

## References

* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w u₁ v₁

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The geometric half of the converse of Stacks 06PJ.** If the quotient stack `[U/R]` of a
groupoid in algebraic spaces is an algebraic stack, then it has a presentation `f : 𝒮_W ⟶ [U/R]`
by a scheme of the site, representable by algebraic spaces with surjective and smooth base
changes, and a surjective, flat, locally finitely presented morphism `b : V ⟶ W` of the site such
that the pulled-back presentation is the 1-morphism presented by a morphism `g : U' ⟶ U` out of
the algebraic space of `V`, whose saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a surjection of
fppf sheaves.

This is the first half of the converse implication of Stacks 06PJ: it produces the morphism `g`
of its statement and condition (1) for it. Condition (2) — flatness and local finite presentation
of the source and target of the restriction along `g` — is not proved. -/
theorem exists_presented_point_locallySurjective_saturation
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (h𝒳 : IsAlgebraicStack.{u, w} C S hS (quotientStack G)) :
    ∃ (W V : BigFppfOver C S hS) (b : V ⟶ W)
      (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G)
      (g : (schemeSpace V : AlgebraicSpaces C S hS) ⟶
        G.objects),
      IsRepresentableByAlgebraicSpaces C S hS f ∧
      (∀ (T : BigFppfOver C S hS)
        (y : BigFppfOver C T.left.1 T.left.2 ⥤ (quotientStack G).obj)
        (_hy : y ⋙ (quotientStack G).p = Over.map T.hom)
        (F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace C T.left.1 T.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map T.hom)
            (schemeFibredCategory C S hS W).val.p (quotientStack G).p y (BasedFunctor.toFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsSurjective C S hS (algebraicSpaceMap C S hS T
            ((spacesOverSmallerBaseFunctor C T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)).hom ∧
          Space.IsSmooth C S hS (algebraicSpaceMap C S hS T
            ((spacesOverSmallerBaseFunctor C T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)).hom) ∧
      Flat (C.inclusion.map b.left) ∧
      LocallyOfFinitePresentation (C.inclusion.map b.left) ∧
      Surjective (C.inclusion.map b.left) ∧
      Nonempty (presentedSchemeMap G g.hom ≅ BasedFunctor.comp ⟨Over.map b, rfl⟩ f) ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
        ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom) := by
  classical
  obtain ⟨hFib, ⟨⟨-, -⟩, -, W, f, hf, hAtlas⟩⟩ := id h𝒳
  have hFibered := isFiberedInGroupoids_quotientStack G
  -- The base changes of the presentation are surjections of fppf sheaves, being surjective,
  -- flat and locally of finite presentation.
  have hatlasLS : ∀ (T : BigFppfOver C S hS)
      (y : BigFppfOver C T.left.1 T.left.2 ⥤ (quotientStack G).obj)
      (_hy : y ⋙ (quotientStack G).p = Over.map T.hom)
      (F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace C T.left.1 T.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map T.hom)
          (schemeFibredCategory C S hS W).val.p (quotientStack G).p y (BasedFunctor.toFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
        (algebraicSpaceMap C S hS T
          ((spacesOverSmallerBaseFunctor C T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)).hom := by
    intro T y hy F hF he
    obtain ⟨hsurj, hsmooth⟩ := hAtlas T y hy F hF he
    exact isLocallySurjective_of_surjective_flat_lfp C S hS _
      (fun A A' a a' k ha ha' hw => by
        have := hsmooth A A' a a' k ha ha' hw
        infer_instance)
      (fun A A' a a' k ha ha' hw => by
        have := hsmooth A A' a a' k ha ha' hw
        infer_instance) hsurj
  -- The object of `[U/R]` over `W` that the presentation names, and a point of the object space
  -- presenting its pullback along one surjective, flat, locally finitely presented morphism.
  let x : (quotientStack G).p.Fiber W := ⟨f.obj (Over.mk (𝟙 W)), f.w_obj (Over.mk (𝟙 W))⟩
  obtain ⟨V, b, hbFlat, hbLfp, hbSurj, a, ha⟩ := exists_fppf_cover_presented_object C S hS G W x
  let U' : AlgebraicSpaces C S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda C S hS V⟩
  let g : U' ⟶ G.objects := ObjectProperty.homMk (yonedaEquiv.symm a)
  have hbLocal := isLocallySurjective_yoneda_map_of_fppf C S hS b hbFlat hbLfp hbSurj
  have hRepresentative (Z : BigFppfOver C S hS) (l : Z ⟶ V) :
      Nonempty ((pointwiseToQuotientStackFiber G Z).obj (g.hom.app (Opposite.op Z) l) ≅
        schemePointFiber f (Over.mk (l ≫ b))) :=
    ⟨(presented_refinement_pullback_iso C S hS G x b a ha.some l).some ≪≫
      schemePointPullbackIso hFibered f (Over.mk (l ≫ b))⟩
  refine ⟨W, V, b, f, g, hf, hAtlas, hbFlat, hbLfp, hbSurj,
    ⟨presentedSchemeMapIso G f b a ha.some⟩, ?_⟩
  -- Condition (1) of Stacks 06PJ: every point of the object space is, locally, the source of an
  -- arrow whose target lifts through `g`.
  apply isLocallySurjective_saturation_of_local_presented_iso C S hS G g
  intro T x₀
  let z := (pointwiseToQuotientStackFiber G T).obj x₀
  obtain ⟨R, hR, hloc⟩ := exists_local_schemePoint_of_atlas C S hS G W f hf hatlasLS T z
  let J := BigFppfOver.topology C S hS
  let K : ∀ ⦃A⦄ (d : A ⟶ T), R.arrows d → Sieve A := fun {A} d hd =>
    Presheaf.imageSieve (yoneda.map b) (Classical.choose (hloc d hd))
  refine ⟨Sieve.bind R.arrows K, J.transitive hR _ ?_, ?_⟩
  · intro A d hd
    exact J.superset_covering (Sieve.le_pullback_bind R.arrows K d hd)
      (hbLocal.imageSieve_mem (Classical.choose (hloc d hd)))
  · rintro Z m ⟨A, c, d, hd, hc, rfl⟩
    obtain ⟨ek⟩ := Classical.choose_spec (hloc d hd)
    obtain ⟨l, hl⟩ := hc
    change l ≫ b = c ≫ Classical.choose (hloc d hd) at hl
    refine ⟨l, ⟨?_⟩⟩
    refine (presentedPullbackIso G T x₀ z rfl (Over.mk (c ≫ d))).symm ≪≫ ?_
    refine ((schemePointPullbackCompIso hFibered f (Classical.choose (hloc d hd)) c).symm ≪≫
      Functor.pullbackFiberIso ek c ≪≫ Functor.pullbackFiberCompIso z d c).symm ≪≫ ?_
    exact eqToIso (by rw [hl]) ≪≫ (hRepresentative Z l).some.symm



end AlgebraicGeometry.Stack

end
