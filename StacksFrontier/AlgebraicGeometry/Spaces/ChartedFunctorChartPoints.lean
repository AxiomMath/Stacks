module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartedFunctorSpectra
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartLocalFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.RingTheory.Etale.Lifting

/-!
# Chart points of the functor attached to a smooth morphism over an affine

Let `T'` be an affine object of the big fppf site of `S`, `X` an algebraic space and
`p : X ⟶ h_{T'}` a smooth morphism, and let `F` be the functor on bounded `Γ(T')`-algebras
attached to `p` (`AlgebraicGeometry.Space.OverAffine.chartedFunctor`). This file shows that
every section of `F` over `Γ(T') ⧸ J`, for an ideal `J` of square zero, passes through an étale
chart of `F` after a faithfully flat étale extension `Γ(T') ⟶ P₁`, as the infinitesimal lifting
criterion for algebraic spaces ([Stacks Project, Tag 04AM]) needs: the section is a chart point
over `P₁ ⧸ J P₁`.

The geometric input is that a section of an algebraic space over an affine factors étale-locally
through a single affine étale chart
(`AlgebraicGeometry.Space.exists_affine_etale_cover_through_affine_chart`); the étale
neighbourhood is then an étale algebra over `Γ(T') ⧸ J`, which lifts to an étale algebra over
`Γ(T')` ([Stacks Project, Tag 04D1]).

## Main definitions

* `AlgebraicGeometry.Space.OverAffine.quotSection`: the section of `F` over `Γ(T') ⧸ I` named by
  a section of `X` over a closed subobject `T` of `T'` cut out by `I`.

## Main results

* `AlgebraicGeometry.Space.OverAffine.exists_isChartPoint_of_etale`: a section of `F` over
  `Γ(T') ⧸ J`, with `J ^ 2 = ⊥`, is a chart point of an étale chart of `F` after a faithfully
  flat étale extension of `Γ(T')`.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
-/

@[expose] public section

open CategoryTheory Opposite Cardinal Limits Stacks.ChartedFunctor

universe u

namespace AlgebraicGeometry.Space.OverAffine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- A finitely presented algebra over a bounded algebra is bounded. -/
lemma mk_lt_cutoff_of_finitePresentation {C : Type u} [CommRing C]
    [Algebra (sectionsRing T') C] [Algebra.FiniteType (sectionsRing T') C] : #C < B.cutoff := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    ‹Algebra.FiniteType (sectionsRing T') C›
  have h2 := MvPolynomial.cardinalMk_le_max_lift (σ := Fin n) (R := sectionsRing T')
  rw [Cardinal.lift_uzero, Cardinal.mk_fin, Cardinal.lift_natCast] at h2
  exact ((Cardinal.mk_le_of_surjective hf).trans h2).trans_lt (max_lt (max_lt (baseAlg T').2
    ((Cardinal.natCast_lt_aleph0 (n := n)).trans B.aleph0_lt_cutoff)) B.aleph0_lt_cutoff)

/-- For an ideal `J` of square zero, `Spec (Γ(T') ⧸ J) ⟶ Spec Γ(T')` is surjective. -/
private lemma surjective_spec_map_quotMk_of_sq_eq_bot (J : Ideal (baseAlg T').obj)
    (hJ : J ^ 2 = ⊥) :
    Surjective (Spec.map (ringHomOf T' (Stacks.ChartedFunctor.quotMk (baseAlg T') J))) :=
  ⟨(Stacks.Smooth.isFirstOrderThickening_specMap _
    Ideal.Quotient.mk_surjective (by convert hJ; exact Ideal.mk_ker)).isThickening.2⟩

/-- An étale algebra over `Γ(T') ⧸ J`, for `J` of square zero, whose spectrum covers that of
`Γ(T') ⧸ J`, is the reduction of an étale algebra over `Γ(T')` whose spectrum covers `T'`. -/
private theorem exists_etale_lift_of_quot (J : Ideal (baseAlg T').obj) (hJ : J ^ 2 = ⊥)
    {A₁ : BoundedAlg (sectionsRing T') B.cutoff}
    (m₁ : Stacks.ChartedFunctor.quot (baseAlg T') J ⟶ A₁)
    (hm₁E : Etale (Spec.map (ringHomOf T' m₁))) (hm₁S : Surjective (Spec.map (ringHomOf T' m₁))) :
    ∃ (P₁ : BoundedAlg (sectionsRing T') B.cutoff) (φ : baseAlg T' ⟶ P₁)
      (e : (Stacks.ChartedFunctor.quot P₁ (J.map (BoundedAlg.toAlgHom φ))).obj ≃ₐ[sectionsRing T']
        A₁.obj),
      Etale (Spec.map (ringHomOf T' φ)) ∧ Surjective (Spec.map (ringHomOf T' φ)) ∧
      Etale (Spec.map (ringHomOf T' (quotMap (J := J) φ (Ideal.le_comap_map
        (f := BoundedAlg.toAlgHom φ))))) ∧
      Surjective (Spec.map (ringHomOf T' (quotMap (J := J) φ (Ideal.le_comap_map
        (f := BoundedAlg.toAlgHom φ))))) ∧
      quotMap φ (Ideal.le_comap_map (f := BoundedAlg.toAlgHom φ)) ≫
        BoundedAlg.ofHom e.toAlgHom = m₁ := by
  let Q₀ := Stacks.ChartedFunctor.quot (baseAlg T') J
  let A' : Type u := sectionsRing T'
  let : Algebra Q₀.obj A₁.obj := (BoundedAlg.toAlgHom m₁).toRingHom.toAlgebra
  have : IsScalarTower A' Q₀.obj A₁.obj := IsScalarTower.of_algebraMap_eq fun a =>
    ((BoundedAlg.toAlgHom m₁).commutes a).symm
  have : Algebra.Etale Q₀.obj A₁.obj :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 hm₁E)
  obtain ⟨C, _, _, hCE, ψ, hψ, hψker⟩ :=
    etale_lift_along_surjection A' Q₀.obj A₁.obj Ideal.Quotient.mk_surjective
  rw [show RingHom.ker (algebraMap A' Q₀.obj) = J from Ideal.mk_ker] at hψker
  let P₁ : BoundedAlg (sectionsRing T') B.cutoff :=
    BoundedAlg.of C (mk_lt_cutoff_of_finitePresentation (T' := T'))
  let φ : baseAlg T' ⟶ P₁ := BoundedAlg.ofHom (Algebra.ofId A' C)
  let J₁ : Ideal P₁.obj := J.map (BoundedAlg.toAlgHom φ)
  have hker : RingHom.ker (ψ : C →+* A₁.obj) = J₁ := hψker
  let e : (Stacks.ChartedFunctor.quot P₁ J₁).obj ≃ₐ[A'] A₁.obj :=
    (Ideal.quotientEquivAlgOfEq A' hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hψ)
  have hme : quotMap φ (Ideal.le_comap_map (f := BoundedAlg.toAlgHom φ)) ≫
      BoundedAlg.ofHom e.toAlgHom = m₁ := by
    apply BoundedAlg.hom_ext
    apply Ideal.Quotient.algHom_ext
    ext
  have hiso : IsIso (ringHomOf T' (BoundedAlg.ofHom e.toAlgHom)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 e.bijective
  have : IsIso (Spec.map (ringHomOf T' (BoundedAlg.ofHom e.toAlgHom))) := inferInstance
  have hSpecQ : Spec.map (ringHomOf T' (quotMap (J := J) φ (Ideal.le_comap_map
      (f := BoundedAlg.toAlgHom φ)))) =
      inv (Spec.map (ringHomOf T' (BoundedAlg.ofHom e.toAlgHom))) ≫
        Spec.map (ringHomOf T' m₁) := by
    rw [IsIso.eq_inv_comp, ← Spec.map_comp, ← hme]
    rfl
  refine ⟨P₁, φ, e, ?_, ?_, ?_, ?_, hme⟩
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (RingHom.etale_algebraMap (R := A') (S := C) |>.2 hCE)
  · let ψR : CommRingCat.of C ⟶ CommRingCat.of A₁.obj := CommRingCat.ofHom ψ.toRingHom
    have hcomm : ringHomOf T' φ ≫ ψR =
        ringHomOf T' (Stacks.ChartedFunctor.quotMk (baseAlg T') J) ≫ ringHomOf T' m₁ := by
      ext a
      exact (ψ.commutes a).trans ((BoundedAlg.toAlgHom m₁).commutes a).symm
    have := surjective_spec_map_quotMk_of_sq_eq_bot J hJ
    have : Surjective (Spec.map ψR ≫ Spec.map (ringHomOf T' φ)) := by
      rw [← Spec.map_comp, hcomm, Spec.map_comp]
      infer_instance
    exact Surjective.of_comp (Spec.map ψR) _
  all_goals rw [hSpecQ]; infer_instance

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (p : X ⟶ yoneda.obj T')
  {T : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] (i : T ⟶ T')
  [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i)]

/-- The section of the functor attached to `p` over `Γ(T') ⧸ I` named by a section of `X` over
`T` lying over `i`. -/
noncomputable def quotSection (x : X.obj (op T)) (hx : p.app _ x = i) :
    (chartedFunctor T' X p).obj (Stacks.ChartedFunctor.quot (baseAlg T') (thickeningIdeal i)) :=
  ⟨X.map (specQuotToObj i).op x, by
    rw [NatTrans.naturality_apply, hx]
    exact specQuotToObj_comp i⟩

/-- The underlying section of `X` of `quotSection X p i x hx` is the pullback of `x` along
`specQuotToObj i`. -/
lemma quotSection_val (x : X.obj (op T)) (hx : p.app _ x = i) :
    (quotSection X p i x hx).1 = X.map (specQuotToObj i).op x := rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The morphism `q` with `a ≫ p = yoneda.map q`, for `a` étale and `p` smooth, is smooth. -/
private theorem smooth_map_of_comp_eq_yoneda_map (hp : IsSmooth B S hS p) {U₀ : BigFppfOver B S hS}
    {a : yoneda.obj U₀ ⟶ X} {q : U₀ ⟶ T'} (haq : a ≫ p = yoneda.map q)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Smooth ((BigFppfOver.toScheme B S hS).map q) := by
  refine hp U₀ T' a (𝟙 _) q ha ?_ ?_
  · simpa using (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS (@Etale.{u}) (𝟙 T')).2
      (by rw [(BigFppfOver.toScheme B S hS).map_id]; infer_instance)
  · rw [Category.comp_id, haq]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i)] in
/-- **A section of the functor over `Γ(T') ⧸ J` becomes a chart point after a faithfully flat
étale extension.** Let `X` be an algebraic space and `p : X ⟶ h_{T'}` smooth. For an ideal `J`
of square zero and a section `x` over `Γ(T') ⧸ J`, there are an étale algebra `P₁` over `Γ(T')`
whose spectrum maps onto `T'`, and an étale chart of the functor through which the image of `x`
over `P₁ ⧸ J P₁` passes. -/
theorem exists_isChartPoint_of_etale (hX : IsAlgebraicSpace B S hS X) (hp : IsSmooth B S hS p)
    (J : Ideal (baseAlg T').obj) (hJ : J ^ 2 = ⊥)
    (x : (chartedFunctor T' X p).obj (Stacks.ChartedFunctor.quot (baseAlg T') J)) :
    ∃ (P₁ : BoundedAlg (sectionsRing T') B.cutoff) (φ : baseAlg T' ⟶ P₁)
      (c : EtaleChart (chartedFunctor T' X p)),
      Etale (Spec.map (ringHomOf T' φ)) ∧ Surjective (Spec.map (ringHomOf T' φ)) ∧
      Etale (Spec.map (ringHomOf T' (quotMap (J := J) φ (Ideal.le_comap_map
        (f := BoundedAlg.toAlgHom φ))))) ∧
      Surjective (Spec.map (ringHomOf T' (quotMap (J := J) φ (Ideal.le_comap_map
        (f := BoundedAlg.toAlgHom φ))))) ∧
      c.IsChartPoint ((chartedFunctor T' X p).map
        (quotMap φ (Ideal.le_comap_map (f := BoundedAlg.toAlgHom φ))) x) := by
  let G := BigFppfOver.toScheme B S hS
  let Q₀ := Stacks.ChartedFunctor.quot (baseAlg T') J
  let TA := specOver T' Q₀
  have : IsAffine (G.obj TA) := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨T₁, U₀, w, g, a₀, hT₁, hU₀, hwE, hwS, ha₀, hga⟩ :=
    exists_affine_etale_cover_through_affine_chart hX x.1
  -- the chart
  let q : U₀ ⟶ T' := yoneda.preimage (a₀ ≫ p)
  have haq : a₀ ≫ p = yoneda.map q := (yoneda.map_preimage _).symm
  let c := etaleChart U₀ q a₀ haq ha₀ (smooth_map_of_comp_eq_yoneda_map X p hp haq ha₀)
  -- `T₁` as the spectrum of an algebra over `Γ(T') ⧸ J`
  let v₁ : T₁ ⟶ T' := w ≫ specOverToBase T' Q₀
  let A₁ := algOf T₁ v₁
  let ι₁ := specAlgOfHom T₁ v₁
  obtain ⟨m₁, hm₁⟩ := exists_specOverMap_eq T' (ι₁ ≫ w) (by
    rw [Category.assoc]
    exact specAlgOfHom_comp T₁ v₁)
  have hm₁ES : Etale (Spec.map (ringHomOf T' m₁)) ∧ Surjective (Spec.map (ringHomOf T' m₁)) := by
    change Etale (G.map (specOverMap T' m₁)) ∧ Surjective (G.map (specOverMap T' m₁))
    rw [hm₁, G.map_comp]
    exact ⟨inferInstance, inferInstance⟩
  -- the chart point over `A₁`
  have hgq : g ≫ q = v₁ := by
    have h1 : p.app _ (a₀.app (op T₁) g) = g ≫ q :=
      congrArg (fun t => t.app (op T₁) g) haq
    rw [← h1, hga, NatTrans.naturality_apply, x.2]
    rfl
  obtain ⟨ρ₁, hρ₁⟩ := exists_chartHom_eq U₀ q (ι₁ ≫ g) (by
    rw [Category.assoc, hgq]
    exact specAlgOfHom_comp T₁ v₁)
  have hpt : (chartTrans U₀ q a₀ haq).app A₁ ρ₁ = (chartedFunctor T' X p).map m₁ x := by
    apply Subtype.ext
    change a₀.app _ (chartHom U₀ q ρ₁) = X.map (specOverMap T' m₁).op x.1
    rw [hρ₁, hm₁]
    change a₀.app _ (ι₁ ≫ g) = _
    have : a₀.app _ (ι₁ ≫ g) = X.map ι₁.op (a₀.app _ g) := NatTrans.naturality_apply a₀ ι₁.op g
    rw [this, hga, ← Functor.map_comp_apply, ← op_comp]
  -- lift the étale algebra `A₁` over `Γ(T') ⧸ J` to an étale algebra over `Γ(T')`
  obtain ⟨P₁, φ, e, hφE, hφS, hqE, hqS, hme⟩ := exists_etale_lift_of_quot J hJ m₁ hm₁ES.1 hm₁ES.2
  have hee : BoundedAlg.ofHom e.toAlgHom ≫ BoundedAlg.ofHom e.symm.toAlgHom = 𝟙 _ :=
    BoundedAlg.hom_ext (AlgHom.ext e.symm_apply_apply)
  refine ⟨P₁, φ, c, hφE, hφS, hqE, hqS, ?_⟩
  have h1 : (chartedFunctor T' X p).map (quotMap φ (Ideal.le_comap_map
      (f := BoundedAlg.toAlgHom φ))) x =
      (chartedFunctor T' X p).map (BoundedAlg.ofHom e.symm.toAlgHom)
        ((chartedFunctor T' X p).map m₁ x) := by
    rw [← hme, Functor.map_comp_apply, ← Functor.map_comp_apply _
      (BoundedAlg.ofHom e.toAlgHom), hee, Functor.map_id_apply]
  rw [h1, ← hpt]
  exact EtaleChart.IsChartPoint.map c ⟨ρ₁, rfl⟩ _

end AlgebraicGeometry.Space.OverAffine

end
