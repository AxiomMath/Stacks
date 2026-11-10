module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.EtaleLocalRingHub
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.StrictHenselizationRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGeneratorRatio

/-!
# The étale local ring of `Spec(𝒪_{U, u})` at a geometric point over the generic point

Let `Z ⊂ X` be a prime divisor of a decent algebraic space with generic point `ξ`, let `(U, u)` be
the chosen elementary étale neighbourhood of `ξ` and `A = 𝒪_{U, u}`, and let
`j : Spec(A) ⟶ X` be the canonical morphism. Every geometric point `x̄` of `X` over `ξ` comes from
a geometric point `ȳ` of `Spec(A)`, factoring through the residue field of the closed point, and
the homomorphism of étale local rings `𝒪_{X, x̄} → 𝒪_{Spec(A), ȳ}` of Stacks 04NG along `j` is an
isomorphism: both rings are strict henselizations of `A` and the map is a local `A`-algebra map.

This is what lets a comparison made over a chart of `Spec(A)` — where the generator of an
invertible module chosen at `ξ` lives — be read in `𝒪_{X, x̄}`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericStalkGeometricPoint`: the geometric point `ȳ` of
  `Spec(A)` induced by a geometric point of `X` over `ξ`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericStalkNeighborhood`: the identity chart of
  `Spec(A)` as a small étale neighbourhood of a geometric point.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.geometricPointMap_genericStalkGeometricPoint`: `ȳ` lies
  over `x̄` on the nose.
* `AlgebraicGeometry.Space.PrimeDivisor.etaleLocalRingMap_comp_genericStalkToEtaleLocalRing`: the
  map of Stacks 04NG along `j` lies over `A`.
* `AlgebraicGeometry.Space.PrimeDivisor.bijective_etaleLocalRingMap_genericStalkMorphism`: it is
  bijective.

## References

* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-! ### Two neighbourhoods with the same chart and equal lifts -/

/-- The chart leg of Stacks 05VP depends on a small étale neighbourhood only through its chart and
its lift, so two neighbourhoods with one chart and equal lifts have the same chart leg at every
spelling of the chart point. -/
theorem chartStalkToEtaleLocalRing_congr {x : GeometricPoint B S hS X} {W : SmallEtale B S hS X}
    {ℓ₁ ℓ₂ : x.val.siteObject ⟶ W.obj.left}
    (h₁ : W.obj.hom.app (op x.val.siteObject) ℓ₁ = x.val.value)
    (h₂ : W.obj.hom.app (op x.val.siteObject) ℓ₂ = x.val.value) (hℓ : ℓ₁ = ℓ₂)
    {p : chartScheme W}
    (hp₁ : chartPoint B S hS X (⟨W, ℓ₁, h₁⟩ : SmallEtaleNeighborhood x) = p)
    (hp₂ : chartPoint B S hS X (⟨W, ℓ₂, h₂⟩ : SmallEtaleNeighborhood x) = p) :
    chartStalkToEtaleLocalRing B S hS hX (⟨W, ℓ₁, h₁⟩ : SmallEtaleNeighborhood x) hp₁ =
      chartStalkToEtaleLocalRing B S hS hX (⟨W, ℓ₂, h₂⟩ : SmallEtaleNeighborhood x) hp₂ := by
  subst hℓ
  rfl

/-! ### The stalk of `Spec` of a stalk at its closed point -/

/-- Through `Spec(𝒪_{T, x}) ⟶ T`, the stalk of `T` at `x` is identified with the stalk of
`Spec(𝒪_{T, x})` at its closed point: the identification of stalks at the two spellings of `x`
followed by the stalk map is the inverse of `AlgebraicGeometry.stalkClosedPointIso`. -/
theorem stalkCongr_hom_comp_stalkMap_fromSpecStalk {T : Scheme.{u}} (x : T)
    {g : Spec (T.presheaf.stalk x) ⟶ T} (hg : g = T.fromSpecStalk x)
    {y : Spec (T.presheaf.stalk x)} (hy : y = closedPoint (T.presheaf.stalk x))
    (h : Inseparable x (g.base y)) :
    (T.presheaf.stalkCongr h).hom ≫ g.stalkMap y =
      (stalkClosedPointIso (T.presheaf.stalk x)).inv ≫ eqToHom (by rw [hy]) := by
  subst hg hy
  have key := Scheme.stalkClosedPointTo_fromSpecStalk x
  rw [Scheme.stalkClosedPointTo, ← Iso.eq_comp_inv] at key
  have hss : ∀ {a b : T} (h₁ : a ⤳ b) (h₂ : b ⤳ a),
      T.presheaf.stalkSpecializes h₁ ≫ T.presheaf.stalkSpecializes h₂ = 𝟙 _ := fun h₁ h₂ ↦ by
    rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]
  rw [eqToHom_refl, Category.comp_id, key, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  exact (congrArg (· ≫ _) (hss _ _)).trans (Category.id_comp _)

/-- The composite of `stalkCongr_hom_comp_stalkMap_fromSpecStalk` is an isomorphism. -/
theorem isIso_stalkCongr_hom_comp_stalkMap_fromSpecStalk {T : Scheme.{u}} (x : T)
    {g : Spec (T.presheaf.stalk x) ⟶ T} (hg : g = T.fromSpecStalk x)
    {y : Spec (T.presheaf.stalk x)} (hy : y = closedPoint (T.presheaf.stalk x))
    (h : Inseparable x (g.base y)) :
    IsIso ((T.presheaf.stalkCongr h).hom ≫ g.stalkMap y) := by
  rw [stalkCongr_hom_comp_stalkMap_fromSpecStalk x hg hy h]
  infer_instance

/-- On global sections of `Spec(𝒪_{T, x})`, read in `𝒪_{T, x}`, the composite of
`stalkCongr_hom_comp_stalkMap_fromSpecStalk` is the germ at the closed point. -/
theorem ΓSpecIso_hom_comp_stalkCongr_hom_comp_stalkMap_fromSpecStalk {T : Scheme.{u}} (x : T)
    {g : Spec (T.presheaf.stalk x) ⟶ T} (hg : g = T.fromSpecStalk x)
    {y : Spec (T.presheaf.stalk x)} (hy : y = closedPoint (T.presheaf.stalk x))
    (h : Inseparable x (g.base y)) :
    (Scheme.ΓSpecIso (T.presheaf.stalk x)).hom ≫ (T.presheaf.stalkCongr h).hom ≫ g.stalkMap y =
      (Spec (T.presheaf.stalk x)).presheaf.germ ⊤ y trivial := by
  rw [stalkCongr_hom_comp_stalkMap_fromSpecStalk x hg hy h]
  subst hy
  rw [eqToHom_refl, Category.comp_id]
  exact ΓSpecIso_hom_stalkClosedPointIso_inv _

/-! ### The geometric point of `Spec(A)` -/

/-- The residue-field point of the closed point of `Spec(A)`, as a morphism of the site from the
residue-field point of the chosen elementary étale neighbourhood of the generic point. -/
def PrimeDivisor.genericStalkResidueFieldPoint :
    residueFieldObject B S hS (Z.genericChart B S hS hX hdec).scheme
        (Z.genericChart B S hS hX hdec).point
        (Z.genericChart B S hS hX hdec).residueField_contained ⟶
      Z.genericStalkSpec B S hS hX hdec :=
  Over.homMk (B.inclusion.preimage (Spec.map
    (((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme).residue
      (Z.genericChart B S hS hX hdec).point))) (by
    have hpre : ∀ {V W : B.Schemes} (f : B.inclusion.obj V ⟶ B.inclusion.obj W),
        (B.inclusion.preimage f).hom = f := fun f ↦ by
      simpa [AlgebraicGeometry.BigFppfSite.inclusion, AlgebraicGeometry.schemeBelowInclusion,
        ObjectProperty.ι_map] using B.inclusion.map_preimage f
    apply B.inclusion.map_injective
    simp [PrimeDivisor.genericStalkSpec, residueFieldObject, Scheme.fromSpecResidueField, hpre])

/-- The residue-field point of the closed point of `Spec(A)` followed by `Spec(A) ⟶ U` is the
residue-field point of `U` at `u`. -/
theorem PrimeDivisor.genericStalkResidueFieldPoint_comp :
    Z.genericStalkResidueFieldPoint B S hS hX hdec ≫ Z.genericStalkSpecToChart B S hS hX hdec =
      residueFieldMap B S hS (Z.genericChart B S hS hX hdec).scheme
        (Z.genericChart B S hS hX hdec).point
        (Z.genericChart B S hS hX hdec).residueField_contained := by
  ext1
  apply B.inclusion.map_injective
  rw [Over.comp_left, Functor.map_comp]
  change B.inclusion.map (B.inclusion.preimage _) ≫ B.inclusion.map (B.inclusion.preimage _) = _
  exact (congrArg₂ (· ≫ ·) (B.inclusion.map_preimage _) (B.inclusion.map_preimage _)).trans rfl

variable {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver (Z.genericPoint B S hS X))

/-- The geometric point of `Spec(A)` induced by a geometric point of `X` over the generic point:
the factorization of the geometric point through the residue field of `u`, followed by the
residue-field point of the closed point of `Spec(A)`. -/
def PrimeDivisor.genericStalkGeometricPoint :
    GeometricPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1 :=
  ⟨{ carrier := xbar.val.carrier
     contained := xbar.val.contained
     toBase := xbar.val.toBase
     value := (Z.genericChart B S hS hX hdec).liftResidueField xbar hxbar ≫
        Z.genericStalkResidueFieldPoint B S hS hX hdec }, xbar.property⟩

/-- The lift of the induced geometric point of `Spec(A)` followed by `Spec(A) ⟶ U` is the lift of
the geometric point to the chosen elementary étale neighbourhood. -/
theorem PrimeDivisor.genericStalkGeometricPoint_value_comp :
    (Z.genericStalkGeometricPoint B S hS hX hdec hxbar).val.value ≫
        Z.genericStalkSpecToChart B S hS hX hdec =
      (Z.genericChart B S hS hX hdec).liftGeometricPoint xbar hxbar := by
  change ((Z.genericChart B S hS hX hdec).liftResidueField xbar hxbar ≫
      Z.genericStalkResidueFieldPoint B S hS hX hdec) ≫ _ = _
  rw [Category.assoc, Z.genericStalkResidueFieldPoint_comp]
  rfl

/-- **The induced geometric point of `Spec(A)` lies over `x̄` on the nose.** -/
theorem PrimeDivisor.geometricPointMap_genericStalkGeometricPoint :
    geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom
        (Z.genericStalkGeometricPoint B S hS hX hdec hxbar) = xbar := by
  have hval : (Z.genericStalkMorphism B S hS hX hdec).hom.app
      (op (Z.genericStalkGeometricPoint B S hS hX hdec hxbar).val.siteObject)
      (Z.genericStalkGeometricPoint B S hS hX hdec hxbar).val.value = xbar.val.value := by
    change (Z.genericChart B S hS hX hdec).toSpace.app _
      ((Z.genericStalkGeometricPoint B S hS hX hdec hxbar).val.value ≫
        Z.genericStalkSpecToChart B S hS hX hdec) = _
    rw [Z.genericStalkGeometricPoint_value_comp]
    exact (Z.genericChart B S hS hX hdec).toSpace_liftGeometricPoint xbar hxbar
  have key : ∀ (p : FieldValuedPoint B S hS X) (v : X.obj (op p.siteObject)), v = p.value →
      ({ p with value := v } : FieldValuedPoint B S hS X) = p := by
    intro p v hv
    subst hv
    rfl
  exact Subtype.ext (key xbar.val _ hval)

/-! ### The identity chart of `Spec(A)` as a neighbourhood -/

/-- The identity chart of `Spec(A)` as a small étale neighbourhood of a geometric point of
`Spec(A)`, the lift being the geometric point itself. -/
def PrimeDivisor.genericStalkNeighborhood
    (ybar : GeometricPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1) :
    SmallEtaleNeighborhood ybar where
  chart := Z.genericStalkChart B S hS hX hdec
  point := ybar.val.value
  point_comp := rfl

/-- The square of charts over `j : Spec(A) ⟶ X` formed by the identity chart of `Spec(A)` and the
chosen elementary étale neighbourhood of the generic point commutes. -/
theorem PrimeDivisor.genericStalkChart_comm :
    (Z.genericStalkChart B S hS hX hdec).obj.hom ≫ (Z.genericStalkMorphism B S hS hX hdec).hom =
      yoneda.map (Z.genericStalkSpecToChart B S hS hX hdec) ≫
        (Z.genericChart B S hS hX hdec).chart.obj.hom :=
  Category.id_comp _

/-! ### The map of étale local rings along `j : Spec(A) ⟶ X` -/

section EtaleLocalRingMap

variable (ybar : GeometricPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1)
  (hy : (geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar).LiesOver
    (Z.genericPoint B S hS X))
  (hlift : ybar.val.value ≫ Z.genericStalkSpecToChart B S hS hX hdec =
    (Z.genericChart B S hS hX hdec).liftGeometricPoint _ hy)

include hlift in
/-- The image in `U` of the chart point of the identity chart of `Spec(A)` is `u`. -/
theorem PrimeDivisor.genericStalkSpecToChart_chartPoint :
    ((BigFppfOver.toScheme B S hS).map (Z.genericStalkSpecToChart B S hS hX hdec)).base
        (chartPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkNeighborhood B S hS hX hdec ybar)) =
      (Z.genericChart B S hS hX hdec).point := by
  have h1 := (congrArg (fun ℓ : ybar.val.siteObject ⟶ (Z.genericChart B S hS hX hdec).scheme ↦
      ((BigFppfOver.toScheme B S hS).map ℓ).base (closedPoint ybar.val.carrier)) hlift).trans
    (chartPoint_smallEtaleNeighborhood B S hS X hX (Z.genericChart B S hS hX hdec) _ hy)
  exact h1

include hlift in
/-- **The map of Stacks 04NG along `j` lies over `A`.** The canonical map of Stacks 05VP from `A`
into the étale local ring of `X`, followed by the map of étale local rings along `j`, is the
canonical map of Stacks 05VP of the identity chart of `Spec(A)` precomposed with the stalk map
of `Spec(A) ⟶ U`. -/
theorem PrimeDivisor.etaleLocalRingMap_comp_genericStalkToEtaleLocalRing :
    (etaleLocalRingMap (Z.genericStalkSpace B S hS hX hdec).2
        (Z.genericStalkMorphism B S hS hX hdec).hom ybar).comp
        (Z.genericStalkToEtaleLocalRing B S hS hX hdec hy) =
      (chartLocalRingToEtaleLocalRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
          (Z.genericStalkSpace B S hS hX hdec).2
          (Z.genericStalkNeighborhood B S hS hX hdec ybar)).comp
        ((((BigFppfOver.toScheme B S hS).map (Z.genericStalkSpecToChart B S hS hX hdec)).stalkMap
          (chartPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1
            (Z.genericStalkNeighborhood B S hS hX hdec ybar))).hom.comp
          (((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX
              hdec).scheme).presheaf.stalkCongr
            (Inseparable.of_eq
              (Z.genericStalkSpecToChart_chartPoint B S hS hX hdec ybar hy hlift).symm)).hom.hom)
                  := by
  have sq := etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS
    (Z.genericStalkMorphism B S hS hX hdec) ybar (Z.genericStalkNeighborhood B S hS hX hdec ybar)
    (Z.genericChart B S hS hX hdec).chart (Z.genericStalkSpecToChart B S hS hX hdec)
    (Z.genericStalkChart_comm B S hS hX hdec)
  have hθ := chartStalkToEtaleLocalRing_congr B S hS hX (W := (Z.genericChart B S hS hX hdec).chart)
    (ℓ₁ := (Z.genericChart B S hS hX hdec).liftGeometricPoint _ hy)
    (ℓ₂ := ybar.val.value ≫ Z.genericStalkSpecToChart B S hS hX hdec)
    ((Z.genericChart B S hS hX hdec).toSpace_liftGeometricPoint _ hy)
    (targetNeighborhood B S hS (Z.genericStalkNeighborhood B S hS hX hdec ybar)
      (Z.genericChart B S hS hX hdec).chart (Z.genericStalkSpecToChart B S hS hX hdec)
      (Z.genericStalkChart_comm B S hS hX hdec)).point_comp hlift.symm
    (chartPoint_smallEtaleNeighborhood B S hS X hX (Z.genericChart B S hS hX hdec) _ hy)
    (Z.genericStalkSpecToChart_chartPoint B S hS hX hdec ybar hy hlift)
  refine (congrArg (fun φ ↦ (etaleLocalRingMap (Z.genericStalkSpace B S hS hX hdec).2
    (Z.genericStalkMorphism B S hS hX hdec).hom ybar).comp φ) hθ).trans ?_
  exact (congrArg (fun φ ↦ RingHom.comp φ ((((BigFppfOver.toScheme B S hS).obj
    (Z.genericChart B S hS hX hdec).scheme).presheaf.stalkCongr (Inseparable.of_eq
      (Z.genericStalkSpecToChart_chartPoint B S hS hX hdec ybar hy hlift).symm)).hom.hom)) sq).symm

include hlift in
/-- The chart point of the identity chart of `Spec(A)` is the closed point: its image in `U` is
`u`, and `Spec(A) ⟶ U` is injective. -/
theorem PrimeDivisor.chartPoint_genericStalkNeighborhood :
    chartPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkNeighborhood B S hS hX hdec ybar) =
      closedPoint ↥(Z.genericStalkRing B S hS hX hdec) := by
  have hinj : Function.Injective
      ((BigFppfOver.toScheme B S hS).map (Z.genericStalkSpecToChart B S hS hX hdec)).base := by
    rw [Z.toScheme_map_genericStalkSpecToChart B S hS hX hdec]
    exact (IsPreimmersion.isEmbedding (((BigFppfOver.toScheme B S hS).obj
      (Z.genericChart B S hS hX hdec).scheme).fromSpecStalk
        (Z.genericChart B S hS hX hdec).point)).injective
  refine hinj ((Z.genericStalkSpecToChart_chartPoint B S hS hX hdec ybar hy hlift).trans ?_)
  rw [Z.toScheme_map_genericStalkSpecToChart B S hS hX hdec]
  exact Scheme.fromSpecStalk_closedPoint.symm

/-- The identification `A ≅ 𝒪_{Spec(A), ȳ}` of `A` with the local ring of the identity chart of
`Spec(A)` at its chart point: the stalk map of `Spec(A) ⟶ U` after the identification of the two
spellings of `u`. -/
abbrev PrimeDivisor.genericStalkToSpecStalk :
    ↥(Z.genericStalkRing B S hS hX hdec) →+* ↥(chartLocalRing B S hS
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkNeighborhood B S hS hX hdec ybar)) :=
  (((BigFppfOver.toScheme B S hS).map (Z.genericStalkSpecToChart B S hS hX hdec)).stalkMap
      (chartPoint B S hS (Z.genericStalkSpace B S hS hX hdec).1
        (Z.genericStalkNeighborhood B S hS hX hdec ybar))).hom.comp
    (((BigFppfOver.toScheme B S hS).obj (Z.genericChart B S hS hX hdec).scheme).presheaf.stalkCongr
      (Inseparable.of_eq
        (Z.genericStalkSpecToChart_chartPoint B S hS hX hdec ybar hy hlift).symm)).hom.hom

/-- The identification `A ≅ 𝒪_{Spec(A), ȳ}` is bijective. -/
theorem PrimeDivisor.bijective_genericStalkToSpecStalk :
    Function.Bijective (Z.genericStalkToSpecStalk B S hS hX hdec ybar hy hlift) := by
  have h := isIso_stalkCongr_hom_comp_stalkMap_fromSpecStalk (Z.genericChart B S hS hX hdec).point
    (Z.toScheme_map_genericStalkSpecToChart B S hS hX hdec)
    (Z.chartPoint_genericStalkNeighborhood B S hS hX hdec ybar hy hlift)
    (Inseparable.of_eq (Z.genericStalkSpecToChart_chartPoint B S hS hX hdec ybar hy hlift).symm)
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- **Rigidity of strict henselizations, up to a ring isomorphism.** Let `ρ : C → D` be a local
map of henselian local rings with `C` of separably closed residue field, `C` ind-étale over `A` via
`ψ`, `D` ind-étale over `R` via `χ` with separable residue field extension, and `e : A ≃+* R` such
that `ρ ∘ ψ = χ ∘ e`. Then `ρ` is bijective. -/
theorem _root_.StacksDraft.bijective_of_comp_eq_comp_ringEquiv {A R C D : Type*} [CommRing A]
    [Nontrivial A] [CommRing R] [CommRing C] [CommRing D] [IsLocalRing R] [IsLocalRing C]
    [IsLocalRing D]
    [HenselianLocalRing C] [HenselianLocalRing D] [IsSepClosed (ResidueField C)]
    (ρ : C →+* D) [IsLocalHom ρ] (ψ : A →+* C) [IsLocalHom ψ] (χ : R →+* D) [IsLocalHom χ]
    (e : A ≃+* R) (h : ρ.comp ψ = χ.comp e)
    (hψ : letI := ψ.toAlgebra; StacksDraft.IndEtale A C)
    (hχ : letI := χ.toAlgebra; StacksDraft.IndEtale R D)
    (hsep : letI := (ResidueField.map χ).toAlgebra
      Algebra.IsSeparable (ResidueField R) (ResidueField D)) :
    Function.Bijective ρ := by
  let := ψ.toAlgebra
  let := χ.toAlgebra
  let : Algebra A D := (χ.comp e).toAlgebra
  have : IsLocalHom e.symm.toRingHom := IsLocalHom.of_surjective _ e.symm.surjective
  let : Algebra (ResidueField R) (ResidueField C) :=
    (ResidueField.map (ψ.comp e.symm.toRingHom)).toAlgebra
  let : Algebra (ResidueField R) (ResidueField D) := (ResidueField.map χ).toAlgebra
  have := hsep
  let f : C →ₐ[A] D := { ρ with commutes' := fun a ↦ RingHom.congr_fun h a }
  refine StacksDraft.bijective_of_indEtale_of_bijective_residueField_map hψ
    (StacksDraft.indEtale_of_equiv e.symm (RingEquiv.refl _)
      (fun a ↦ congrArg χ (e.apply_symm_apply a).symm) hχ)
    f ⟨fun a ha ↦ IsLocalHom.map_nonunit (f := ρ) a ha⟩
    (StacksDraft.bijective_residueField_map_of_isSeparable (K := ResidueField R) ρ ?_)
  change (ResidueField.map ρ).comp (ResidueField.map (ψ.comp e.symm.toRingHom)) =
    ResidueField.map χ
  rw [← ResidueField.map_comp]
  congr 1
  refine RingHom.ext fun a ↦ ?_
  change (ρ.comp ψ) (e.symm a) = χ a
  rw [h]
  exact congrArg χ (e.apply_symm_apply a)

include hlift in
/-- **The map of étale local rings along `j : Spec(A) ⟶ X` is bijective.** Both étale local rings
are strict henselizations of `A`, the map is a local `A`-algebra map, and it is bijective on
residue fields since the residue field of the source is separably closed and that of the target
is separable over the residue field of `A`; Stacks 04GU then provides an inverse. -/
theorem PrimeDivisor.bijective_etaleLocalRingMap_genericStalkMorphism :
    Function.Bijective (etaleLocalRingMap (Z.genericStalkSpace B S hS hX hdec).2
      (Z.genericStalkMorphism B S hS hX hdec).hom ybar) := by
  let ρ := etaleLocalRingMap (Z.genericStalkSpace B S hS hX hdec).2
    (Z.genericStalkMorphism B S hS hX hdec).hom ybar
  let xb := geometricPointMap (Z.genericStalkMorphism B S hS hX hdec).hom ybar
  let τe : ↥(Z.genericStalkRing B S hS hX hdec) ≃+* ↥(chartLocalRing B S hS (Z.genericStalkSpace B
      S hS hX hdec).1 (Z.genericStalkNeighborhood B S hS hX hdec ybar)) :=
    RingEquiv.ofBijective (Z.genericStalkToSpecStalk B S hS hX hdec ybar hy hlift)
      (Z.bijective_genericStalkToSpecStalk B S hS hX hdec ybar hy hlift)
  let := isLocalRing_etaleLocalRing B S hS X hX xb
  let := isLocalRing_etaleLocalRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 ybar
  have hshR := strictlyHenselianLocalRing_etaleLocalRing B S hS X hX xb
  have := hshR.toHenselianLocalRing
  have := (strictlyHenselianLocalRing_etaleLocalRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 ybar).toHenselianLocalRing
  have := hshR.toIsSepClosed
  have : IsLocalHom ρ := isLocalHom_etaleLocalRingMap B S hS
    (Z.genericStalkSpace B S hS hX hdec).2 hX (Z.genericStalkMorphism B S hS hX hdec).hom ybar
  let ψA := Z.genericStalkToEtaleLocalRing B S hS hX hdec hy
  let χ := chartLocalRingToEtaleLocalRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkNeighborhood B S hS hX hdec ybar)
  -- the source is ind-étale over `A`
  let algR : Algebra ↥(Z.genericStalkRing B S hS hX hdec) (etaleLocalRing B S hS X xb : Type (u +
      1)) := ψA.toAlgebra
  let := Z.isHenselization_genericStalkToEtaleLocalRing B S hS hX hdec hy
  have h₁ : StacksDraft.IndEtale ↥(Z.genericStalkRing B S hS hX hdec) (etaleLocalRing B S hS X xb :
      Type (u + 1)) :=
    IsHenselization.ind_etale (R := ↥(Z.genericStalkRing B S hS hX hdec)) (L :=
        SeparableClosure (ResidueField ↥(Z.genericStalkRing B S hS hX hdec)))
      (Rh := (etaleLocalRing B S hS X xb : Type (u + 1)))
  have : IsLocalHom ψA := IsHenselization.isLocalHom (R := ↥(Z.genericStalkRing B S hS hX hdec))
    (L := SeparableClosure (ResidueField ↥(Z.genericStalkRing B S hS hX hdec)))
    (Rh := (etaleLocalRing B S hS X xb : Type (u + 1)))
  -- the target is ind-étale over `𝒪_{Spec(A), ȳ}`
  let algR'' : Algebra ↥(chartLocalRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkNeighborhood B S hS hX hdec ybar)) (etaleLocalRing B S hS (Z.genericStalkSpace
      B S hS hX hdec).1 ybar :
      Type (u + 1)) := χ.toAlgebra
  let hH' := isHenselization_chartLocalRingToEtaleLocalRing B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
    (Z.genericStalkNeighborhood B S hS hX hdec ybar)
  have : IsLocalHom χ := @IsHenselization.isLocalHom _ _ _ _ _ _ _ _ _ _ hH'
  exact StacksDraft.bijective_of_comp_eq_comp_ringEquiv ρ ψA χ τe
    (Z.etaleLocalRingMap_comp_genericStalkToEtaleLocalRing B S hS hX hdec ybar hy hlift) h₁
    hH'.ind_etale
    (@StacksDraft.isSeparable_residueField_of_isHenselization _ _ _ _ _ _ _ _ _ _ _ hH')

include hlift in
/-- **On regular functions of `Spec(A)` the map of étale local rings along `j` is the germ.** A
regular function `a` on `Spec(A)`, read in `A` and sent to the étale local ring of `X` by the
canonical map of Stacks 05VP, goes under the map of étale local rings along `j` to the germ of
`a` at `ȳ`. -/
theorem PrimeDivisor.etaleLocalRingMap_genericStalkToEtaleLocalRing_ΓSpecIso
    (a : (structurePresheaf B S hS (Z.genericStalkSpace B S hS hX hdec).1).obj
      (op (Z.genericStalkChart B S hS hX hdec))) :
    etaleLocalRingMap (Z.genericStalkSpace B S hS hX hdec).2
        (Z.genericStalkMorphism B S hS hX hdec).hom ybar
        (Z.genericStalkToEtaleLocalRing B S hS hX hdec hy
          ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom.hom a)) =
      etaleLocalRingGerm B S hS (Z.genericStalkSpace B S hS hX hdec).1 ybar
        (op (Z.genericStalkNeighborhood B S hS hX hdec ybar)) a := by
  have hsq := RingHom.congr_fun
    (Z.etaleLocalRingMap_comp_genericStalkToEtaleLocalRing B S hS hX hdec ybar hy hlift)
    ((Scheme.ΓSpecIso (Z.genericStalkRing B S hS hX hdec)).hom.hom a)
  refine hsq.trans (Eq.trans ?_ (chartLocalRingToEtaleLocalRing_germ B S hS
    (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericStalkSpace B S hS hX hdec).2
    (Z.genericStalkNeighborhood B S hS hX hdec ybar) a))
  refine congrArg (chartLocalRingToEtaleLocalRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
    (Z.genericStalkSpace B S hS hX hdec).2 (Z.genericStalkNeighborhood B S hS hX hdec ybar)) ?_
  exact ConcreteCategory.congr_hom
    (ΓSpecIso_hom_comp_stalkCongr_hom_comp_stalkMap_fromSpecStalk
      (Z.genericChart B S hS hX hdec).point (Z.toScheme_map_genericStalkSpecToChart B S hS hX hdec)
      (Z.chartPoint_genericStalkNeighborhood B S hS hX hdec ybar hy hlift)
      (Inseparable.of_eq
        (Z.genericStalkSpecToChart_chartPoint B S hS hX hdec ybar hy hlift).symm)) a

end EtaleLocalRingMap

end AlgebraicGeometry.Space

end
