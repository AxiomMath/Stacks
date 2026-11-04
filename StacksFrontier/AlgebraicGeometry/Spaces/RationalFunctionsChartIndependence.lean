module

public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartNaturality

/-!
# The pullback of rational functions to an affine chart is independent of the chart

Let `X` be an algebraic space over a scheme `S`, let `c : U → X` be an étale chart whose scheme
is affine, reduced and locally Noetherian, and let `g : V → U` be a morphism of the site with
`V` again affine, reduced and locally Noetherian, so that `yoneda.map g ≫ c` is a second such
chart. Then the two pullbacks of rational functions,
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing` at `U` and at `V`, agree in any
ring receiving `Q(Γ(U, 𝒪_U))` and `Q(Γ(V, 𝒪_V))` compatibly with restriction along `g`.

The comparison is made at the localization `R` of `A_V = Γ(V, 𝒪_V)` at the submonoid generated
by the nonzerodivisors of `A_V` together with the image of the nonzerodivisors of
`A_U = Γ(U, 𝒪_U)`. Both `Q(A_U)` and `Q(A_V)` map to `R`, so `Spec R` is a chart meeting every
dense open subspace of `X` which sits over `Spec Q(A_U)` and over `Spec Q(A_V)` compatibly with
`g`; evaluating a rational function there and reading the result in `R` therefore computes both
pullbacks, by
`AlgebraicGeometry.Space.evalSiteRingHom_naturality`. A ring receiving both total rings of
fractions compatibly receives `R` as well, which transports the identity out of `R`.

This is the verification the source of Stacks 0ENK omits — that the embedding of the function
field into the total ring of fractions of the henselian local ring at the generic point of a
prime divisor does not depend on the chosen elementary étale neighbourhood — in the form in
which the comparison of the two orders of vanishing of Stacks 0ENM needs it.

## Main results

* `AlgebraicGeometry.Scheme.specMap_comp_fromSpecTotalFractionRing`: two morphisms out of the
  spectrum of a ring, read through the canonical morphisms from spectra of total rings of
  fractions, agree as soon as the maps of global sections do.
* `AlgebraicGeometry.Space.FactorsThroughDenseOpens.comp`: the factorization property is
  inherited by a composite.
* `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_comp_eq`: the pullback of
  rational functions to an affine chart is independent of the chart, along a morphism of
  charts.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u v

namespace AlgebraicGeometry

/-- Reading a global section of `Spec R` in `R` commutes with pullback along the spectrum of a
ring homomorphism. -/
theorem Scheme.ΓSpecIso_hom_appTop_apply {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (s : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso T).hom ((Spec.map φ).appTop s) = φ ((Scheme.ΓSpecIso R).hom s) := by
  have h : ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso T).hom).hom s =
      ((Scheme.ΓSpecIso R).hom ≫ φ).hom s := by rw [Scheme.ΓSpecIso_naturality φ]
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using h

/-- Reading a global section of `Spec R` in `R` commutes with pullback along the spectrum of a
ring homomorphism, stated for a homomorphism of rings. -/
theorem Scheme.ΓSpecIso_hom_appTop_ofHom_apply {R T : Type u} [CommRing R] [CommRing T]
    (φ : R →+* T) (s : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of T)).hom ((Spec.map (CommRingCat.ofHom φ)).appTop s) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom s) :=
  Scheme.ΓSpecIso_hom_appTop_apply (CommRingCat.ofHom φ) s

/-- Two morphisms out of the spectrum of a ring into an affine scheme, read through the
canonical morphisms from the spectra of total rings of fractions, agree as soon as the
corresponding maps of global sections do. -/
theorem Scheme.specMap_comp_fromSpecTotalFractionRing {T T' : Scheme.{u}} [IsAffine T]
    [IsAffine T'] (h : T' ⟶ T) {R : Type u} [CommRing R]
    (ψ : FractionRing Γ(T, ⊤) →+* R) (ψ' : FractionRing Γ(T', ⊤) →+* R)
    (hcompat : ∀ a : Γ(T, ⊤), ψ (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)) a) =
      ψ' (algebraMap Γ(T', ⊤) (FractionRing Γ(T', ⊤)) (h.appTop a))) :
    Spec.map (CommRingCat.ofHom ψ) ≫ T.fromSpecTotalFractionRing =
      Spec.map (CommRingCat.ofHom ψ') ≫ T'.fromSpecTotalFractionRing ≫ h := by
  have hring : CommRingCat.ofHom (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤))) ≫
      CommRingCat.ofHom ψ =
      h.appTop ≫ CommRingCat.ofHom (algebraMap Γ(T', ⊤) (FractionRing Γ(T', ⊤))) ≫
        CommRingCat.ofHom ψ' := by
    ext a
    exact hcompat a
  calc Spec.map (CommRingCat.ofHom ψ) ≫ T.fromSpecTotalFractionRing
      = (Spec.map (CommRingCat.ofHom ψ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤))))) ≫
          T.isoSpec.inv := by
        rw [Scheme.fromSpecTotalFractionRing, Category.assoc]
    _ = ((Spec.map (CommRingCat.ofHom ψ') ≫
          Spec.map (CommRingCat.ofHom (algebraMap Γ(T', ⊤) (FractionRing Γ(T', ⊤))))) ≫
          Spec.map h.appTop) ≫ T.isoSpec.inv := by
        rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, hring]
    _ = Spec.map (CommRingCat.ofHom ψ') ≫ T'.fromSpecTotalFractionRing ≫ h := by
        rw [Scheme.fromSpecTotalFractionRing]
        simp only [Category.assoc]
        rw [Scheme.isoSpec_inv_naturality h]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism which factors through every dense open subspace of `X` still does so after
precomposition with a morphism of the site. -/
theorem FactorsThroughDenseOpens.comp (hX : IsAlgebraicSpace B S hS X)
    {W W' : BigFppfOver B S hS} {m : yoneda.obj W ⟶ X}
    (hm : FactorsThroughDenseOpens B S hS hX W m) (g : W' ⟶ W) :
    FactorsThroughDenseOpens B S hS hX W' (yoneda.map g ≫ m) := fun V hV ↦
  let ⟨j, hj⟩ := hm V hV
  ⟨yoneda.map g ≫ j, by rw [Category.assoc, hj]⟩

/-- The pullback of rational functions to an affine chart is the evaluation on the spectrum of
the total ring of fractions, read in that ring. -/
theorem rationalFunctionsToTotalFractionRing_eq_ΓSpecIso (hX : IsAlgebraicSpace B S hS X)
    (W : BigFppfOver B S hS) [IsAffine W.left.1] [IsReduced W.left.1]
    [IsLocallyNoetherian W.left.1] (c : yoneda.obj W ⟶ X) (hc : IsEtale B S hS c)
    (hm : FactorsThroughDenseOpens B S hS hX (totalFractionObject B S hS W)
      (yoneda.map (totalFractionObjectMap B S hS W) ≫ c))
    (f : rationalFunctions B S hS hX) :
    rationalFunctionsToTotalFractionRing B S hS hX W c hc f =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(W.left.1, ⊤)))).hom
        (evalSiteRingHom B S hS hX hm f) := rfl

/-- A ring homomorphism out of a localization is determined by its composite with the
localization map: a homomorphism `q` which agrees with `ψ` on the image of `A` composes with
`IsLocalization.lift` to `ψ`. -/
private theorem comp_lift_eq {A K R P : Type*} [CommRing A] [CommRing K] [CommRing R]
    [CommRing P] [Algebra A K] {M : Submonoid A} [IsLocalization M K] (f : A →+* R)
    (hf : ∀ y : M, IsUnit (f y)) (q : R →+* P) (ψ : K →+* P)
    (h : ∀ a, q (f a) = ψ (algebraMap A K a)) : q.comp (IsLocalization.lift (S := K) hf) = ψ :=
  IsLocalization.ringHom_ext M <| RingHom.ext fun a ↦
    (congrArg q (IsLocalization.lift_eq (S := K) hf a)).trans (h a)

section Comparison

variable {U V : BigFppfOver B S hS} (g : V ⟶ U)

/-- Restriction of global sections along a morphism of the site. -/
private abbrev chartRestrict : Γ(U.left.1, ⊤) →+* Γ(V.left.1, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map g).appTop.hom

/-- The submonoid of `Γ(V, 𝒪_V)` generated by its nonzerodivisors together with the
restrictions of the nonzerodivisors of `Γ(U, 𝒪_U)`. -/
private def chartComparisonSubmonoid : Submonoid Γ(V.left.1, ⊤) :=
  (Γ(V.left.1, ⊤))⁰ ⊔ Submonoid.map (chartRestrict B S hS g) (Γ(U.left.1, ⊤))⁰

/-- The localization of `Γ(V, 𝒪_V)` at which the two pullbacks of rational functions are
compared. -/
private abbrev chartComparisonRing : Type u :=
  Localization (chartComparisonSubmonoid B S hS g)

/-- The nonzerodivisors of `Γ(V, 𝒪_V)` become units in the comparison ring. -/
private theorem isUnit_chartComparisonRing_target (y : (Γ(V.left.1, ⊤))⁰) :
    IsUnit (algebraMap Γ(V.left.1, ⊤) (chartComparisonRing B S hS g) (y : Γ(V.left.1, ⊤))) :=
  IsLocalization.map_units (chartComparisonRing B S hS g)
    (⟨(y : Γ(V.left.1, ⊤)), Submonoid.mem_sup_left y.2⟩ : chartComparisonSubmonoid B S hS g)

/-- The restrictions of the nonzerodivisors of `Γ(U, 𝒪_U)` become units in the comparison
ring. -/
private theorem isUnit_chartComparisonRing_source (y : (Γ(U.left.1, ⊤))⁰) :
    IsUnit (((algebraMap Γ(V.left.1, ⊤) (chartComparisonRing B S hS g)).comp
      (chartRestrict B S hS g)) (y : Γ(U.left.1, ⊤))) :=
  IsLocalization.map_units (chartComparisonRing B S hS g)
    (⟨chartRestrict B S hS g (y : Γ(U.left.1, ⊤)),
      Submonoid.mem_sup_right (Submonoid.mem_map.2 ⟨(y : Γ(U.left.1, ⊤)), y.2, rfl⟩)⟩ :
      chartComparisonSubmonoid B S hS g)

/-- The map from the total ring of fractions of `Γ(V, 𝒪_V)` to the comparison ring. -/
private noncomputable def chartComparisonTarget :
    FractionRing Γ(V.left.1, ⊤) →+* chartComparisonRing B S hS g :=
  IsLocalization.lift (isUnit_chartComparisonRing_target B S hS g)

/-- The map from the total ring of fractions of `Γ(U, 𝒪_U)` to the comparison ring. -/
private noncomputable def chartComparisonSource :
    FractionRing Γ(U.left.1, ⊤) →+* chartComparisonRing B S hS g :=
  IsLocalization.lift (isUnit_chartComparisonRing_source B S hS g)

/-- The two maps of global sections which the comparison of the two charts rests on agree. -/
private theorem chartComparison_algebraMap (a : Γ(U.left.1, ⊤)) :
    chartComparisonSource B S hS g
        (algebraMap Γ(U.left.1, ⊤) (FractionRing Γ(U.left.1, ⊤)) a) =
      chartComparisonTarget B S hS g
        (algebraMap Γ(V.left.1, ⊤) (FractionRing Γ(V.left.1, ⊤))
          (((BigFppfOver.toScheme B S hS).map g).appTop a)) := by
  rw [chartComparisonSource, chartComparisonTarget, IsLocalization.lift_eq,
    IsLocalization.lift_eq]
  rfl

variable [IsAffine U.left.1] [IsAffine V.left.1]

omit [IsAffine U.left.1] in
/-- The spectrum of the comparison ring is an object of the big fppf site, being the spectrum
of a localization of the global sections of an affine object. -/
private theorem contains_specChartComparisonRing :
    B.Contains (Spec (CommRingCat.of (chartComparisonRing B S hS g))) := by
  have hV : (Spec (CommRingCat.of Γ(V.left.1, ⊤))).size < B.cutoff := by
    rw [Scheme.size_Spec]
    exact (Scheme.size_of_isAffine V.left.1) ▸ V.left.2
  exact Scheme.size_Spec_lt_of_isLocalization B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (chartComparisonSubmonoid B S hS g) (chartComparisonRing B S hS g) hV

/-- The comparison identity of the two canonical morphisms out of the spectrum of the
comparison ring. -/
private theorem specMap_chartComparison_comp :
    Spec.map (CommRingCat.ofHom (chartComparisonSource B S hS g)) ≫
        U.left.1.fromSpecTotalFractionRing =
      Spec.map (CommRingCat.ofHom (chartComparisonTarget B S hS g)) ≫
        V.left.1.fromSpecTotalFractionRing ≫ (BigFppfOver.toScheme B S hS).map g :=
  Scheme.specMap_comp_fromSpecTotalFractionRing (T := U.left.1) (T' := V.left.1)
    ((BigFppfOver.toScheme B S hS).map g) (chartComparisonSource B S hS g)
    (chartComparisonTarget B S hS g) (chartComparison_algebraMap B S hS g)

/-- The spectrum of the comparison ring, as an object of the big fppf site over `S`, placed
over the spectrum of the total ring of fractions of `Γ(V, 𝒪_V)`. -/
private noncomputable def chartComparisonObject : BigFppfOver B S hS :=
  Over.mk (⟨Spec.map (CommRingCat.ofHom (chartComparisonTarget B S hS g)) ≫
      (totalFractionObject B S hS V).hom.1⟩ :
    B.obj (contains_specChartComparisonRing B S hS g) ⟶ B.obj hS)

/-- The morphism from the spectrum of the comparison ring to the spectrum of the total ring of
fractions of `Γ(V, 𝒪_V)`. -/
private noncomputable def chartComparisonObjectMapTarget :
    chartComparisonObject B S hS g ⟶ totalFractionObject B S hS V :=
  Over.homMk (⟨Spec.map (CommRingCat.ofHom (chartComparisonTarget B S hS g))⟩ :
    B.obj (contains_specChartComparisonRing B S hS g) ⟶
      (totalFractionObject B S hS V).left)

/-- The morphism from the spectrum of the comparison ring to the spectrum of the total ring of
fractions of `Γ(U, 𝒪_U)`. -/
private noncomputable def chartComparisonObjectMapSource :
    chartComparisonObject B S hS g ⟶ totalFractionObject B S hS U :=
  Over.homMk (⟨Spec.map (CommRingCat.ofHom (chartComparisonSource B S hS g))⟩ :
      B.obj (contains_specChartComparisonRing B S hS g) ⟶
        (totalFractionObject B S hS U).left)
    (by
      apply ObjectProperty.hom_ext
      have hw : (BigFppfOver.toScheme B S hS).map g ≫ U.hom.1 = V.hom.1 :=
        congrArg (fun k : V.left ⟶ B.obj hS ↦ k.1) (Over.w g)
      change Spec.map (CommRingCat.ofHom (chartComparisonSource B S hS g)) ≫
          (U.left.1.fromSpecTotalFractionRing ≫ U.hom.1) =
        Spec.map (CommRingCat.ofHom (chartComparisonTarget B S hS g)) ≫
          (V.left.1.fromSpecTotalFractionRing ≫ V.hom.1)
      rw [← hw]
      simp only [← Category.assoc]
      rw [specMap_chartComparison_comp B S hS g]
      simp only [Category.assoc])

/-- The two morphisms from the spectrum of the comparison ring to `U` agree. -/
private theorem chartComparisonObjectMap_comp :
    (chartComparisonObjectMapTarget B S hS g ≫ totalFractionObjectMap B S hS V) ≫ g =
      chartComparisonObjectMapSource B S hS g ≫ totalFractionObjectMap B S hS U := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show (Spec.map (CommRingCat.ofHom (chartComparisonTarget B S hS g)) ≫
      V.left.1.fromSpecTotalFractionRing) ≫ (BigFppfOver.toScheme B S hS).map g =
    Spec.map (CommRingCat.ofHom (chartComparisonSource B S hS g)) ≫
      U.left.1.fromSpecTotalFractionRing
  rw [specMap_chartComparison_comp B S hS g, Category.assoc]

omit [IsAffine U.left.1] in
/-- Pulling a global section of the spectrum of the total ring of fractions of `Γ(V, 𝒪_V)`
back to the spectrum of the comparison ring is the map on total rings of fractions. -/
private theorem ΓSpecIso_appTop_chartComparisonObjectMapTarget
    (s : Γ((BigFppfOver.toScheme B S hS).obj (totalFractionObject B S hS V), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (chartComparisonRing B S hS g))).hom
        (((BigFppfOver.toScheme B S hS).map
          (chartComparisonObjectMapTarget B S hS g)).appTop s) =
      chartComparisonTarget B S hS g
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(V.left.1, ⊤)))).hom s) :=
  Scheme.ΓSpecIso_hom_appTop_ofHom_apply (chartComparisonTarget B S hS g) s

/-- Pulling a global section of the spectrum of the total ring of fractions of `Γ(U, 𝒪_U)`
back to the spectrum of the comparison ring is the map on total rings of fractions. -/
private theorem ΓSpecIso_appTop_chartComparisonObjectMapSource
    (s : Γ((BigFppfOver.toScheme B S hS).obj (totalFractionObject B S hS U), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (chartComparisonRing B S hS g))).hom
        (((BigFppfOver.toScheme B S hS).map
          (chartComparisonObjectMapSource B S hS g)).appTop s) =
      chartComparisonSource B S hS g
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).hom s) :=
  Scheme.ΓSpecIso_hom_appTop_ofHom_apply (chartComparisonSource B S hS g) s

variable [IsReduced U.left.1] [IsLocallyNoetherian U.left.1] [IsReduced V.left.1]
    [IsLocallyNoetherian V.left.1]

omit [IsAffine U.left.1] [IsReduced U.left.1] [IsLocallyNoetherian U.left.1] in
/-- The pullback of rational functions to `V`, read in the comparison ring, is the evaluation
on the spectrum of the comparison ring. -/
private theorem chartComparison_naturality_target
    (hX : IsAlgebraicSpace B S hS X) {c : yoneda.obj U ⟶ X}
    (hc' : IsEtale B S hS (yoneda.map g ≫ c))
    (hm : FactorsThroughDenseOpens B S hS hX (totalFractionObject B S hS V)
      (yoneda.map (totalFractionObjectMap B S hS V) ≫ (yoneda.map g ≫ c)))
    (hm' : FactorsThroughDenseOpens B S hS hX (chartComparisonObject B S hS g)
      (yoneda.map (chartComparisonObjectMapTarget B S hS g) ≫
        yoneda.map (totalFractionObjectMap B S hS V) ≫ (yoneda.map g ≫ c)))
    (f : rationalFunctions B S hS hX) :
    chartComparisonTarget B S hS g
        (rationalFunctionsToTotalFractionRing B S hS hX V (yoneda.map g ≫ c) hc' f) =
      (Scheme.ΓSpecIso (CommRingCat.of (chartComparisonRing B S hS g))).hom
        (evalSiteRingHom B S hS hX hm' f) := by
  rw [evalSiteRingHom_naturality B S hS hX (chartComparisonObjectMapTarget B S hS g) hm hm' f,
    ΓSpecIso_appTop_chartComparisonObjectMapTarget B S hS g,
    rationalFunctionsToTotalFractionRing_eq_ΓSpecIso B S hS hX V (yoneda.map g ≫ c) hc' hm f]

omit [IsReduced V.left.1] [IsLocallyNoetherian V.left.1] in
/-- The pullback of rational functions to `U`, read in the comparison ring, is the evaluation
on the spectrum of the comparison ring. -/
private theorem chartComparison_naturality_source
    (hX : IsAlgebraicSpace B S hS X) {c : yoneda.obj U ⟶ X} (hc : IsEtale B S hS c)
    (hm : FactorsThroughDenseOpens B S hS hX (totalFractionObject B S hS U)
      (yoneda.map (totalFractionObjectMap B S hS U) ≫ c))
    (hm' : FactorsThroughDenseOpens B S hS hX (chartComparisonObject B S hS g)
      (yoneda.map (chartComparisonObjectMapSource B S hS g) ≫
        yoneda.map (totalFractionObjectMap B S hS U) ≫ c))
    (f : rationalFunctions B S hS hX) :
    chartComparisonSource B S hS g
        (rationalFunctionsToTotalFractionRing B S hS hX U c hc f) =
      (Scheme.ΓSpecIso (CommRingCat.of (chartComparisonRing B S hS g))).hom
        (evalSiteRingHom B S hS hX hm' f) := by
  rw [evalSiteRingHom_naturality B S hS hX (chartComparisonObjectMapSource B S hS g) hm hm' f,
    ΓSpecIso_appTop_chartComparisonObjectMapSource B S hS g,
    rationalFunctionsToTotalFractionRing_eq_ΓSpecIso B S hS hX U c hc hm f]

/-- The pullback of rational functions to the two charts, read in the comparison ring, agree. -/
private theorem chartComparison_rationalFunctionsToTotalFractionRing
    (hX : IsAlgebraicSpace B S hS X) {c : yoneda.obj U ⟶ X} (hc : IsEtale B S hS c)
    (hc' : IsEtale B S hS (yoneda.map g ≫ c)) (f : rationalFunctions B S hS hX) :
    chartComparisonTarget B S hS g
        (rationalFunctionsToTotalFractionRing B S hS hX V (yoneda.map g ≫ c) hc' f) =
      chartComparisonSource B S hS g
        (rationalFunctionsToTotalFractionRing B S hS hX U c hc f) := by
  have hmV := factorsThroughDenseOpens_totalFractionObject B S hS hX V (yoneda.map g ≫ c) hc'
  have hmU := factorsThroughDenseOpens_totalFractionObject B S hS hX U c hc
  have hm'V := hmV.comp B S hS hX (chartComparisonObjectMapTarget B S hS g)
  have hm'U := hmU.comp B S hS hX (chartComparisonObjectMapSource B S hS g)
  have hmor : yoneda.map (chartComparisonObjectMapTarget B S hS g) ≫
        (yoneda.map (totalFractionObjectMap B S hS V) ≫ (yoneda.map g ≫ c)) =
      yoneda.map (chartComparisonObjectMapSource B S hS g) ≫
        (yoneda.map (totalFractionObjectMap B S hS U) ≫ c) := by
    simp only [← Category.assoc, ← Functor.map_comp, chartComparisonObjectMap_comp]
  rw [chartComparison_naturality_target B S hS g hX hc' hmV hm'V f,
    chartComparison_naturality_source B S hS g hX hc hmU hm'U f]
  exact congrArg _ (evalSiteRingHom_congr_mor B S hS hX hmor hm'V hm'U f)

end Comparison

/-- **The pullback of rational functions to an affine étale chart is independent of the chart.**
Let `c : U → X` be an étale chart of an algebraic space whose scheme is affine, reduced and
locally Noetherian, let `g : V → U` be a morphism of the site with `V` again affine, reduced
and locally Noetherian, and let `P` be a ring receiving the total rings of fractions of
`Γ(U, 𝒪_U)` and of `Γ(V, 𝒪_V)` compatibly with restriction along `g`. Then the two pullbacks
of a rational function of `X` have the same image in `P`.

The two pullbacks are compared in the localization of `Γ(V, 𝒪_V)` at the nonzerodivisors of
`Γ(V, 𝒪_V)` together with the restrictions of the nonzerodivisors of `Γ(U, 𝒪_U)`: the spectrum
of that localization is a chart meeting every dense open subspace of `X` which lies over both
`Spec Q(Γ(U, 𝒪_U))` and `Spec Q(Γ(V, 𝒪_V))`, so evaluation there computes both pullbacks, and
`P` receives the localization as well. -/
theorem rationalFunctionsToTotalFractionRing_comp_eq (hX : IsAlgebraicSpace B S hS X)
    {U V : BigFppfOver B S hS} [IsAffine U.left.1] [IsReduced U.left.1]
    [IsLocallyNoetherian U.left.1] [IsAffine V.left.1] [IsReduced V.left.1]
    [IsLocallyNoetherian V.left.1] (g : V ⟶ U) {c : yoneda.obj U ⟶ X}
    (hc : IsEtale B S hS c) (hc' : IsEtale B S hS (yoneda.map g ≫ c))
    {P : Type v} [CommRing P] (ψ : FractionRing Γ(U.left.1, ⊤) →+* P)
    (ψ' : FractionRing Γ(V.left.1, ⊤) →+* P)
    (hcompat : ∀ a : Γ(U.left.1, ⊤),
      ψ (algebraMap Γ(U.left.1, ⊤) (FractionRing Γ(U.left.1, ⊤)) a) =
        ψ' (algebraMap Γ(V.left.1, ⊤) (FractionRing Γ(V.left.1, ⊤))
          (((BigFppfOver.toScheme B S hS).map g).appTop a)))
    (f : rationalFunctions B S hS hX) :
    ψ' (rationalFunctionsToTotalFractionRing B S hS hX V (yoneda.map g ≫ c) hc' f) =
      ψ (rationalFunctionsToTotalFractionRing B S hS hX U c hc f) := by
  -- the nonzerodivisors of `Γ(V, 𝒪_V)` and the restricted nonzerodivisors of `Γ(U, 𝒪_U)`
  -- become units in `P`, so `P` receives the comparison ring
  have hunits : ∀ y : chartComparisonSubmonoid B S hS g,
      IsUnit ((ψ'.comp (algebraMap Γ(V.left.1, ⊤) (FractionRing Γ(V.left.1, ⊤))))
        (y : Γ(V.left.1, ⊤))) := by
    intro y
    obtain ⟨a, ha, b, hb, hab⟩ := Submonoid.mem_sup.1 y.2
    obtain ⟨b₀, hb₀, rfl⟩ := Submonoid.mem_map.1 hb
    have hbunit : IsUnit ((ψ'.comp (algebraMap Γ(V.left.1, ⊤)
        (FractionRing Γ(V.left.1, ⊤)))) (chartRestrict B S hS g b₀)) := by
      rw [RingHom.comp_apply, ← hcompat b₀]
      exact (IsLocalization.map_units (FractionRing Γ(U.left.1, ⊤)) ⟨b₀, hb₀⟩).map ψ
    rw [← hab, map_mul]
    exact ((IsLocalization.map_units (FractionRing Γ(V.left.1, ⊤)) ⟨a, ha⟩).map ψ').mul hbunit
  have hΨtarget : (IsLocalization.lift hunits).comp (chartComparisonTarget B S hS g) = ψ' :=
    comp_lift_eq _ _ _ _ fun a ↦ (IsLocalization.lift_eq _ _).trans rfl
  have hΨsource : (IsLocalization.lift hunits).comp (chartComparisonSource B S hS g) = ψ :=
    comp_lift_eq _ _ _ _ fun a ↦ ((IsLocalization.lift_eq _ _).trans (hcompat a).symm)
  rw [← hΨtarget, ← hΨsource, RingHom.comp_apply, RingHom.comp_apply,
    chartComparison_rationalFunctionsToTotalFractionRing B S hS g hX hc hc' f]

end AlgebraicGeometry.Space

end
