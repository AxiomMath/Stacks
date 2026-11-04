module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPushoutGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutQuotientSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutGlueFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupportFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison

/-!
# The functor of quotients on a pushout along a thickening: surjectivity

The surjectivity half of Stacks 08IW: in Situation 082M, two quotients `F_Y ⟶ A` and
`F_{Z'} ⟶ B'` with the same pullback to `Z` come from a quotient of `F_{Y'}`, namely the
image of `F_{Y'}` in the glued module of Stacks 08KV.

## References

* [Stacks Project, Tag 08IW](https://stacks.math.columbia.edu/tag/08IW)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- The projection onto a pulled-back quotient, unfolded. -/
theorem quotientPullbackProjection_eq {T' T : SchemesOver D.Y} (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) :
    D.quotientPullbackProjection k K =
      (D.baseChangeComparison k).hom.app D.F ≫
        (modulePullback B S hS (D.relativeMap k)).map (D.quotientProjection T K) :=
  rfl

/-- The pulled-back quotient, unfolded: the kernel of the projection onto the inverse image of
the quotient. -/
theorem quotientPullback_eq_kernelSubobject {T' T : SchemesOver D.Y} (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) :
    D.quotientPullback k K = kernelSubobject (D.quotientPullbackProjection k K) :=
  rfl

/-- The comparison of base changes, unfolded. -/
theorem baseChangeComparison_eq {T' T : SchemesOver D.Y} (k : T' ⟶ T) :
    D.baseChangeComparison k =
      modulePullbackTriangle B S hS (X := D.space T') (Y := D.space T) (Z := D.X)
        (f := D.relativeMap k) (g := D.sourceProjection T) (k := D.sourceProjection T')
        (baseChangeMap_comp_projection D.f k) :=
  rfl

/-- **A pulled-back quotient is recognised by a monomorphism out of the inverse image of the
quotient**: if the projection onto `k^*(F_T/K)` followed by a monomorphism into `F_{T'}/K'` is the
projection onto `F_{T'}/K'`, then the pullback of `K` is `K'`. -/
theorem quotientPullback_eq_of_comp_mono {T' T : SchemesOver D.Y} (k : T' ⟶ T)
    (K : Subobject (D.baseChangeModule T)) (K' : Subobject (D.baseChangeModule T'))
    (j : (modulePullback B S hS (D.relativeMap k)).obj (D.quotientModule T K) ⟶
      D.quotientModule T' K') (hjm : Mono j)
    (hj : (modulePullbackTriangle B S hS (X := D.space T') (Y := D.space T) (Z := D.X)
        (f := D.relativeMap k) (g := D.sourceProjection T) (k := D.sourceProjection T')
        (baseChangeMap_comp_projection D.f k)).hom.app D.F ≫
      (modulePullback B S hS (D.relativeMap k)).map (D.quotientProjection T K) ≫ j =
        D.quotientProjection T' K') :
    D.quotientPullback k K = K' := by
  rewrite [quotientPullback_eq_kernelSubobject, quotientPullbackProjection_eq,
    baseChangeComparison_eq]
  exact (kernelSubobject_eq_of_comp_mono _ _ j (by rewrite [Category.assoc]; exact hj)).symm.trans
    (kernelSubobject_cokernel_π K')

/-- **The chart rings of `X_T` over `T` are of finite presentation** when `X ⟶ B` is locally of
finite presentation: `X_T ⟶ T` is a base change of it (Stacks 03XR), so on every diagram of
affine étale charts the map of rings of functions is of finite presentation. -/
theorem finitePresentation_chartDiagramRestrict_projection
    (hlfp : IsLocallyOfFinitePresentation B S hS D.f.hom) (T : SchemesOver D.Y)
    (dT : ChartDiagram B S hS (D.space T).1 ((schemeSpaceFunctor B S hS).obj T.left).1
      (D.projection T).hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS (D.space T).1 ⋙ BigFppfOver.toScheme B S hS).obj
      dT.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS ((schemeSpaceFunctor B S hS).obj T.left).1 ⋙
      BigFppfOver.toScheme B S hS).obj dT.V)) :
    (chartDiagramRestrict B S hS (D.projection T) dT).FinitePresentation := by
  have hP : IsLocallyOfFinitePresentation B S hS (D.projection T).hom := by
    have := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
    exact MorphismProperty.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        IsLocallyOfFinitePresentation B S hS f.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f
        ((schemesOverToOver D.Y).obj T).hom) hlfp
  have hl := locallyOfFinitePresentation_chartDiagram B S hS hP dT
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS (D.space T).1).obj dT.U)) := hU
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS ((schemeSpaceFunctor B S hS).obj T.left).1).obj dT.V)) := hV
  rw [chartDiagramRestrict_eq_appTop]
  exact HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _ hl

section Surjective

variable {Z Z' Y₀ Y' : SchemesOver D.Y} (i : Z ⟶ Z') (f : Z ⟶ Y₀) (g : Z' ⟶ Y') (h : Y₀ ⟶ Y')
  (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i.left)
    ((BigFppfOver.toScheme B S hS).map f.left) ((BigFppfOver.toScheme B S hS).map g.left)
    ((BigFppfOver.toScheme B S hS).map h.left))
  (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i.left))
  (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f.left))

include hpo hi hf in
/-- **Two compatible quotients over `Y` and `Z'` come from a quotient over the pushout** (the
surjectivity half of Stacks 08IW): the kernel of the map from `F_{Y'}` onto the glued module of
Stacks 08KV. -/
theorem exists_quotientPullback_eq (KY : Subobject (D.baseChangeModule Y₀))
    (KZ : Subobject (D.baseChangeModule Z')) (hKY : KY ∈ D.quotients Y₀)
    (hKZ : KZ ∈ D.quotients Z') (heq : D.quotientPullback f KY = D.quotientPullback i KZ) :
    ∃ K ∈ D.quotients Y', D.quotientPullback h K = KY ∧ D.quotientPullback g K = KZ ∧
      (IsLocallyOfFinitePresentation B S hS D.f.hom →
        (D.quotientModule Y₀ KY).IsFinitePresentationOnSite →
          (D.quotientModule Z' KZ).IsFinitePresentationOnSite →
            (D.quotientModule Y' K).IsFinitePresentationOnSite) := by
  have E := D.toThickeningPushoutSpaces i f g h hpo hi hf
  have q := congrArg (D.quotientModule Z) heq.symm
  have hcompat := D.pushoutGlue_compat i f KY KZ heq q
  rw [quotientPullbackProjection_eq, quotientPullbackProjection_eq, baseChangeComparison_eq,
    baseChangeComparison_eq, Category.assoc] at hcompat
  let θ := (D.quotientPullbackCokernelIso i KZ).inv ≫ eqToHom q ≫
    (D.quotientPullbackCokernelIso f KY).hom
  have hθ : IsIso θ := inferInstance
  have hc := E.glueLift_compat (X₀ := D.X) (sV := D.sourceProjection Y₀)
    (sU' := D.sourceProjection Z') (sU := D.sourceProjection Z) (D.sourceProjection Y')
    (baseChangeMap_comp_projection D.f h)
    (baseChangeMap_comp_projection D.f g) (baseChangeMap_comp_projection D.f f)
    (baseChangeMap_comp_projection D.f i) D.F (D.quotientProjection Y₀ KY)
    (D.quotientProjection Z' KZ) θ hcompat
  obtain ⟨lam, hfst, hsnd⟩ := ThickeningPushoutSpaces.exists_lift_glue _ _ hc
  have hM : (D.baseChangeModule Y').IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ D.F D.quasicoherent
  have hφ := fun dT x => E.counitApp_glueLeft dT (D.quotientModule Y₀ KY) x
  have hψ := fun dT y => E.counitApp_glueRight dT (D.quotientModule Y₀ KY)
    (D.quotientModule Z' KZ) θ y
  have := E.epi_lift lam hM hKY.1 hKZ.1 hθ
    (epi_comp' (IsIso.epi_of_iso _) (D.epi_quotientProjection Y₀ KY))
    (epi_comp' (IsIso.epi_of_iso _) (D.epi_quotientProjection Z' KZ)) hfst hsnd hφ hψ
  obtain ⟨K, hK₁, hK₂, ⟨j₁, hj₁, hju⟩, ⟨j₂, hj₂, hjv⟩, ⟨eK⟩⟩ :=
    E.exists_subobject_glue lam hKY.1 hKZ.1 hθ hKY.2 hKZ.2 hfst hsnd hφ hψ
  refine ⟨K, ⟨hK₁, hK₂⟩,
    D.quotientPullback_eq_of_comp_mono h K KY j₁ (@IsIso.mono_of_iso _ _ _ _ j₁ hj₁) ?_,
    D.quotientPullback_eq_of_comp_mono g K KZ j₂ (@IsIso.mono_of_iso _ _ _ _ j₂ hj₂) ?_,
    fun hlfp hYfp hZfp => ?_⟩
  · rewrite [hju]
    exact Iso.hom_inv_id_app_assoc _ _ _
  · rewrite [hjv]
    exact Iso.hom_inv_id_app_assoc _ _ _
  · exact (E.isFinitePresentationOnSite_glue _ hKY.1 hKZ.1 hθ hKY.2 hKZ.2 hYfp hZfp
      (D.finitePresentation_chartDiagramRestrict_projection hlfp Y') hφ hψ).of_iso eK.symm

include hpo hi hf in
/-- **The surjectivity half of Stacks 08IW.** -/
theorem quotientsPushoutMap_surjective :
    Function.Surjective (D.quotientsPushoutMap i f g h hpo) := by
  rintro ⟨⟨KY, KZ⟩, hKK⟩
  obtain ⟨K, hK, h₁, h₂, -⟩ := D.exists_quotientPullback_eq i f g h hpo hi hf KY.1 KZ.1 KY.2
    KZ.2 (congrArg Subtype.val hKK)
  exact ⟨⟨K, hK⟩, Subtype.ext (Prod.ext (Subtype.ext h₁) (Subtype.ext h₂))⟩

end Surjective

end QuotientSituation

end AlgebraicGeometry.Space

end
