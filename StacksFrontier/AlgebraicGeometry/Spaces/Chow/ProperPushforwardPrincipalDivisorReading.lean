module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericPointChartReading
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartIndependence

/-!
# Readings of rational functions at field points over the generic point

-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)

/-- A rational function is represented by a partial map `f₀`, and at a field point `q` over the
generic point its value is the coordinate of `f₀` pulled back along a lift `j` of `q`. -/
private theorem exists_evalRingHom_eq_coordinate (q : FieldValuedPoint B S hS X)
    (hq : q.class B S hS X = genericPoint B S hS hX hInt) (g : rationalFunctions B S hS hX) :
    ∃ (f₀ : PartialMap B S hS hX (affineLineFunctor B S hS))
      (j : yoneda.obj (q.siteObject B S hS X) ⟶ f₀.domain.toFunctor),
      g = f₀.toRationalMap B S hS ∧ j ≫ f₀.domain.ι = fieldMorphism B S hS X q ∧
        evalRingHom B S hS hX hInt q hq g = (Scheme.ΓSpecIso (CommRingCat.of q.carrier)).hom.hom
          (affineLineCoordinate B S hS (Opposite.op (q.siteObject B S hS X))
            (yonedaEquiv (j ≫ f₀.hom))) := by
  obtain ⟨f₀, rfl⟩ := RationalMap.exists_rep B S hS g
  obtain ⟨j, hj⟩ := exists_genericLift B S hS hX hInt q hq f₀.dense_open_domain
  refine ⟨f₀, j, rfl, hj, ?_⟩
  rw [evalRingHom_eq_appTop B S hS hX hInt q hq f₀ (q.siteObject B S hS X) j (𝟙 _)
      (by rw [CategoryTheory.Functor.map_id, Category.id_comp, hj]),
    CategoryTheory.Functor.map_id, Scheme.Hom.id_appTop]
  rfl

/-- **Evaluation at the generic point is natural along a factorization of field points.** If a
field point `p` over the generic point factors through another one `q` by a morphism of field
spectra which is `Spec φ`, then evaluating a rational function at `p` is `φ` of its value at
`q`. -/
theorem evalRingHom_eq_of_factor (p q : FieldValuedPoint B S hS X)
    (hp : p.class B S hS X = genericPoint B S hS hX hInt)
    (hq : q.class B S hS X = genericPoint B S hS hX hInt)
    (f : p.siteObject B S hS X ⟶ q.siteObject B S hS X)
    (hf : yoneda.map f ≫ fieldMorphism B S hS X q = fieldMorphism B S hS X p)
    (φ : q.carrier →+* p.carrier)
    (hφ : (BigFppfOver.toScheme B S hS).map f = Spec.map (CommRingCat.ofHom φ))
    (g : rationalFunctions B S hS hX) :
    evalRingHom B S hS hX hInt p hp g = φ (evalRingHom B S hS hX hInt q hq g) := by
  obtain ⟨f₀, j, rfl, hj, h⟩ := exists_evalRingHom_eq_coordinate B S hS hX hInt q hq g
  rw [evalRingHom_eq_appTop B S hS hX hInt p hp f₀ (q.siteObject B S hS X) j f
    (by rw [hj, hf]), h, hφ]
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) _

/-- **The value of a rational function at a generic point of an affine chart is the reading of
its image in `Q(Γ(V, 𝒪))`.** For an affine reduced locally Noetherian étale chart `V` of `X` and
a point `w` of `V` over the generic point of `X` with `𝒪_{V, w}` a field, evaluation at the field
point `Spec κ(w) ⟶ V ⟶ X` is `Q(Γ(V, 𝒪)) → κ(w)` composed with the first half of Stacks 0ENK. -/
theorem evalRingHom_chartSchemeFieldValuedPoint (V : SmallEtale B S hS X)
    [IsAffine V.obj.left.left.1] [IsReduced V.obj.left.left.1]
    [IsLocallyNoetherian V.obj.left.left.1] (w : chartScheme V)
    (hw : IsField ((chartScheme V).presheaf.stalk w))
    (hwgen : (chartSchemeFieldValuedPoint B S hS X V w).class B S hS X =
      genericPoint B S hS hX hInt)
    (g : rationalFunctions B S hS hX) :
    evalRingHom B S hS hX hInt (chartSchemeFieldValuedPoint B S hS X V w) hwgen g =
      Scheme.totalFractionRingToResidueField (T := V.obj.left.left.1) w hw
        (rationalFunctionsToTotalFractionRing B S hS hX V.obj.left V.obj.hom
          ((isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2 V.property) g) := by
  have hfac := Scheme.fromSpecResidueField_eq_SpecMap_comp_fromSpecTotalFractionRing
    (T := V.obj.left.left.1) w hw
  have hw' : Spec.map (CommRingCat.ofHom
      (Scheme.totalFractionRingToResidueField (T := V.obj.left.left.1) w hw)) ≫
      B.inclusion.map (totalFractionObject B S hS V.obj.left).hom =
      B.inclusion.map ((chartSchemeFieldValuedPoint B S hS X V w).siteObject B S hS X).hom := by
    have e3 : B.inclusion.map ((chartSchemeFieldValuedPoint B S hS X V w).siteObject B S hS
        X).hom = V.obj.left.left.1.fromSpecResidueField w ≫ B.inclusion.map V.obj.left.hom :=
      (Functor.map_comp _ _ _).trans (congrArg (· ≫ _) (map_siteMapOfSchemeMap B S hS _ _ _))
    refine Eq.trans ?_ e3.symm
    refine Eq.trans ?_ (congrArg (· ≫ B.inclusion.map V.obj.left.hom) hfac.symm)
    exact (Category.assoc _ _ _).symm
  obtain ⟨c, hc⟩ := exists_siteHom_toScheme_map_eq B S hS
    (A := (chartSchemeFieldValuedPoint B S hS X V w).siteObject B S hS X)
    (A' := totalFractionObject B S hS V.obj.left) _ hw'
  refine evalRingHom_eq_rationalFunctionsToTotalFractionRing B S hS hX hInt V.obj.left
    V.obj.hom _ _ _ _ c hc ?_ g
  have hsite : c ≫ totalFractionObjectMap B S hS V.obj.left =
      (canonicalSiteFieldPoint B S hS _ w).siteHom := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
    refine (congrArg (· ≫ _) hc).trans ?_
    exact hfac.symm.trans (map_siteFieldPointOfSchemeMap_value_left B S hS _ _ _).symm
  refine (congrArg (fun k ↦ yoneda.map k ≫ V.obj.hom) hsite).trans ?_
  exact (fieldMorphism_map_yoneda B S hS _ _ _).symm

/-- Evaluation of a rational function on the spectrum of the field of a field point over the
generic point is the global section of that spectrum given by its value. -/
theorem evalSiteRingHom_fieldMorphism (q : FieldValuedPoint B S hS X)
    (hq : q.class B S hS X = genericPoint B S hS hX hInt) (g : rationalFunctions B S hS hX) :
    evalSiteRingHom B S hS hX (factorsThroughDenseOpens_fieldMorphism B S hS hX hInt q hq) g =
      (Scheme.ΓSpecIso (CommRingCat.of q.carrier)).inv (evalRingHom B S hS hX hInt q hq g) := by
  obtain ⟨f₀, j, rfl, hj, h⟩ := exists_evalRingHom_eq_coordinate B S hS hX hInt q hq g
  rw [h, evalSiteRingHom_eq B S hS hX _ f₀ j hj]
  exact ((Scheme.ΓSpecIso (CommRingCat.of q.carrier)).hom_inv_id_apply _).symm

/-- **The two readings of a rational function on an object of the site lying over both a field
point over the generic point and the spectrum of the total ring of fractions of an affine
chart agree.** -/
theorem appTop_evalRingHom_eq_appTop_rationalFunctionsToTotalFractionRing
    (U : BigFppfOver B S hS) [IsAffine U.left.1] [IsReduced U.left.1]
    [IsLocallyNoetherian U.left.1] (c : yoneda.obj U ⟶ X) (hc : IsEtale B S hS c)
    {G : BigFppfOver B S hS} (k : G ⟶ totalFractionObject B S hS U)
    (q : FieldValuedPoint B S hS X) (hq : q.class B S hS X = genericPoint B S hS hX hInt)
    (r : G ⟶ q.siteObject B S hS X)
    (hcomm : yoneda.map (k ≫ totalFractionObjectMap B S hS U) ≫ c =
      yoneda.map r ≫ fieldMorphism B S hS X q)
    (g : rationalFunctions B S hS hX) :
    ((BigFppfOver.toScheme B S hS).map r).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of q.carrier)).inv (evalRingHom B S hS hX hInt q hq g)) =
      ((BigFppfOver.toScheme B S hS).map k).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).inv
          (rationalFunctionsToTotalFractionRing B S hS hX U c hc g)) := by
  have hm₁ := factorsThroughDenseOpens_fieldMorphism B S hS hX hInt q hq
  have hm₂ := factorsThroughDenseOpens_totalFractionObject B S hS hX U c hc
  have hinv : (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).inv
      (rationalFunctionsToTotalFractionRing B S hS hX U c hc g) =
        evalSiteRingHom B S hS hX hm₂ g := by
    rw [rationalFunctionsToTotalFractionRing_eq_ΓSpecIso B S hS hX U c hc hm₂]
    exact (Scheme.ΓSpecIso _).hom_inv_id_apply _
  rw [← evalSiteRingHom_fieldMorphism B S hS hX hInt q hq g,
    ← evalSiteRingHom_naturality B S hS hX r hm₁ (hm₁.comp B S hS hX r), hinv,
    ← evalSiteRingHom_naturality B S hS hX k hm₂ (hm₂.comp B S hS hX k)]
  refine evalSiteRingHom_congr_mor B S hS hX ?_ _ _ g
  rw [← hcomm, CategoryTheory.Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Space

end
