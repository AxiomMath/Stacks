module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreChartFunctoriality
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityLift
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.AffineLineIso
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.StandardChart
public import StacksFrontier.AlgebraicGeometry.Blowup.ChartSectionRing
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.ChartMembership
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth
public import StacksFrontier.RingTheory.AffineBlowup.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension

/-!
# The charts `D₊(S)` of the blowup at infinity

Let `X` be a scheme, `ℐ` a quasi-coherent ideal sheaf on `X` and `W` the blowup of `𝐏¹_X` in the
centre `∞(Z)` (`Stacks.Chow.blowupAtInfinity`). Over an affine open `U = Spec A` of `X`, with
`I = ℐ(U)`, the chart at infinity of `𝐏¹_U` is `Spec A[s]`, the centre is `J = (I, s)` there and
the divisor at infinity is `(s)`. This file builds the standard affine chart `D₊(S)` of `W`
attached to `s`, with coordinate ring the affine blowup algebra `A[s][J/s]`, and identifies it
with the complement of the strict transform `X'` over the chart at infinity.

## Main definitions

* `Stacks.Chow.infinityChartOver`: the chart at infinity `Spec Γ(X, U)[s] ⟶ 𝐏¹_X` over `U`.
* `Stacks.Chow.blowupAtInfinityPolyChart`: the chart `D₊(a⁽¹⁾) ⟶ W` for `a ∈ J`, with source the
  spectrum of `Γ(X, U)[s][J/a]`; `Stacks.Chow.blowupAtInfinityChartS` is the chart `D₊(S)`.

## Main results

* `Stacks.Chow.ideal_comap_infinityCentreIdeal_infinityChartOver` and
  `Stacks.Chow.ideal_comap_lineInfinityDivisor_infinityChartOver`: on the chart at infinity the
  centre is `J = (I, s)` and the divisor at infinity is `(s)`.
* `Stacks.Chow.blowupAtInfinityPolyChart_comp`: the chart lies over the chart at infinity.
* `Stacks.Chow.ideal_comap_exceptionalIdealAtInfinity_polyChart`: on `D₊(a⁽¹⁾)` the exceptional
  divisor is cut out by `a`.
* `Stacks.Chow.mem_range_blowupAtInfinityChartS_iff_notMem`: **over the chart at infinity,
  `D₊(S) = W ∖ X'`.**
* `Stacks.Chow.specMap_infinityChartAlgebraMap_blowupAtInfinityChartS`: the charts `D₊(S)` are
  compatible with restriction to smaller affine opens of `X`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0BFL](https://stacks.math.columbia.edu/tag/0BFL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The chart at infinity of `𝐏¹_X` over an affine open of `X` -/

/-- The base change `𝔸¹_Y ⟶ 𝔸¹_X` of an open immersion `Y ⟶ X` is an open immersion. -/
instance {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    IsOpenImmersion (affineLineOverMap f) := by
  have : affineLineOverMap f =
      pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (terminal.hom_ext _ _) (by simp) := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  rw [this]
  infer_instance

/-- The canonical coordinate is compatible with base change of the affine line. -/
theorem affineLineOverMap_appTop_affineCoordinate {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (affineLineOverMap f).appTop (affineCoordinate X) = affineCoordinate Y := by
  rw [affineCoordinate, affineCoordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    affineLineOverMap_snd]

variable {X : Scheme.{u}}

/-- **The chart at infinity of `𝐏¹_X` over an affine open `U` of `X`**: the open immersion
`Spec Γ(X, U)[s] ⟶ 𝐏¹_X` onto the part over `U` of the affine chart containing the divisor at
infinity, `s` being the coordinate cutting that divisor out. -/
def infinityChartOver (U : X.affineOpens) : Spec (CommRingCat.of (Polynomial Γ(X, U.1))) ⟶
    relativeProjectiveLine X :=
  (affineLineOverIsoSpecPolynomial Γ(X, U.1)).inv ≫ affineLineOverMap U.2.fromSpec ≫
    affineYChart X

/-- The chart at infinity over `U` is an open immersion. -/
instance (U : X.affineOpens) : IsOpenImmersion (infinityChartOver U) := by
  have := U.2.isOpenImmersion_fromSpec
  dsimp only [infinityChartOver]
  infer_instance

/-- The chart at infinity over `U` lies over `U`: composed with `𝐏¹_X ⟶ X` it is `Spec` of the
inclusion of constants followed by the affine identification of `U`. -/
@[reassoc]
theorem infinityChartOver_comp (U : X.affineOpens) :
    infinityChartOver U ≫ (relativeProjectiveLine X ↘ X) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1))) ≫
        U.2.fromSpec := by
  rw [infinityChartOver, Category.assoc, Category.assoc, affineYChart_comp,
    affineLineOverMap_fst, ← Category.assoc, affineLineOverIsoSpecPolynomial_inv_comp]

/-- The coordinate of the chart at infinity is the polynomial variable. -/
theorem affineLineOverIsoSpecPolynomial_inv_appTop (R : CommRingCat.{u}) :
    (affineLineOverIsoSpecPolynomial R).inv.appTop (affineCoordinate (Spec R)) =
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial R))).inv Polynomial.X := by
  rw [← appTop_affineLineOverIsoSpecPolynomial_hom R, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
  rfl

/-- Extending a principal ideal along a ring map gives the principal ideal of the image. -/
private theorem map_span_singleton_eq {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (x : R) : (Ideal.span {x}).map f = Ideal.span {f x} := by
  rw [Ideal.map_span, Set.image_singleton]

/-- On the chart at infinity over `U`, the divisor at infinity is cut out by the variable. -/
theorem ideal_comap_lineInfinityDivisor_infinityChartOver (U : X.affineOpens) :
    ((lineInfinityDivisor X).comap (infinityChartOver U)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of (Polynomial Γ(X, U.1)))).inv
                    Polynomial.X} := by
  set q : Spec (CommRingCat.of (Polynomial Γ(X, U.1))) ⟶ affineLineOver X :=
    (affineLineOverIsoSpecPolynomial Γ(X, U.1)).inv ≫ affineLineOverMap U.2.fromSpec with hqdef
  have := U.2.isOpenImmersion_fromSpec
  have hA₀ : IsAffineOpen (q ''ᵁ ⊤) := (isAffineOpen_top _).image_of_isOpenImmersion q
  have hle : (⊤ : (Spec (CommRingCat.of (Polynomial Γ(X, U.1)))).Opens) ≤ q ⁻¹ᵁ (q ''ᵁ ⊤) :=
    (q.preimage_image_eq ⊤).ge
  have hchart : infinityChartOver U = q ≫ affineYChart X := by
    rw [infinityChartOver, hqdef, Category.assoc]
  rw [hchart, Scheme.IdealSheafData.comap_comp,
    Stacks.IdealSheaf.ideal_comap_appLE _ q ⟨_, hA₀⟩ ⟨⊤, isAffineOpen_top _⟩ hle,
    infinityDivisor_ideal_comap_affineYChart X ⟨_, hA₀⟩, map_span_singleton_eq]
  congr 2
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  show q.appTop (affineCoordinate X) = _
  rw [hqdef, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineLineOverMap_appTop_affineCoordinate, affineLineOverIsoSpecPolynomial_inv_appTop]

/-- Two ring maps out of `ULift ℤ[T]` agree as soon as they agree on the variable. -/
theorem polynomial_ulift_int_ringHom_ext {R : Type*} [Semiring R]
    {f g : Polynomial (ULift.{u} ℤ) →+* R} (h : f Polynomial.X = g Polynomial.X) : f = g := by
  refine Polynomial.ringHom_ext (fun a => ?_) h
  have hc : (f.comp Polynomial.C).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom =
      (g.comp Polynomial.C).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom :=
    RingHom.ext_int _ _
  have := RingHom.congr_fun hc (ULift.ringEquiv a)
  simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply] using this

/-- The structure map `ULift ℤ[T] ⟶ R[T]` of a polynomial ring over a commutative ring. -/
abbrev polynomialStructureMap (R : CommRingCat.{u}) :
    CommRingCat.of (Polynomial (ULift.{u} ℤ)) ⟶ CommRingCat.of (Polynomial R) :=
  CommRingCat.ofHom (Polynomial.mapRingHom
    ((Int.castRingHom R).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom))

/-- The identification `𝔸¹_{Spec R} ≅ Spec R[T]` carries the projection of `𝔸¹_{Spec R}` to
`𝔸¹_ℤ` to `Spec` of the structure map `ℤ[T] ⟶ R[T]`. -/
theorem affineLineOverIsoSpecPolynomial_inv_snd (R : CommRingCat.{u}) :
    (affineLineOverIsoSpecPolynomial R).inv ≫
        pullback.snd (terminal.from (Spec R))
          (terminal.from (Spec (CommRingCat.of (Polynomial (ULift.{u} ℤ))))) =
      Spec.map (polynomialStructureMap R) := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ULift.{u} ℤ)))).inv]
  apply CommRingCat.hom_ext
  refine polynomial_ulift_int_ringHom_ext ?_
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← affineCoordinate_eq,
    affineLineOverIsoSpecPolynomial_inv_appTop]
  have h2 := congrArg (fun φ => φ Polynomial.X)
    (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (polynomialStructureMap R)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [← h2]
  simp

/-- The chart at infinity over `U`, as a morphism to `𝔸¹_X`. -/
def infinityChartBase (U : X.affineOpens) :
    Spec (CommRingCat.of (Polynomial Γ(X, U.1))) ⟶ affineLineOver X :=
  (affineLineOverIsoSpecPolynomial Γ(X, U.1)).inv ≫ affineLineOverMap U.2.fromSpec

/-- Composed with `𝔸¹_X ⟶ X`, the chart at infinity over `U` is `Spec` of the inclusion of
constants followed by the affine identification of `U`. -/
theorem infinityChartBase_fst (U : X.affineOpens) :
    infinityChartBase U ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1))) ≫
        U.2.fromSpec := by
  rw [infinityChartBase, Category.assoc, affineLineOverMap_fst, ← Category.assoc,
    affineLineOverIsoSpecPolynomial_inv_comp]

/-- Composed with `𝔸¹_X ⟶ 𝔸¹_ℤ`, the chart at infinity over `U` is `Spec` of the structure map
`ℤ[T] ⟶ Γ(X, U)[T]`. -/
theorem infinityChartBase_snd (U : X.affineOpens) :
    infinityChartBase U ≫ pullback.snd _ _ = Spec.map (polynomialStructureMap Γ(X, U.1)) := by
  rw [infinityChartBase, Category.assoc, affineLineOverMap_snd,
    affineLineOverIsoSpecPolynomial_inv_snd]

/-- **The point `s = 0` of the chart at infinity is the infinity section**: `Spec` of evaluation
at `0`, followed by the chart at infinity over `U`, is the affine identification of `U` followed
by `∞ : X ⟶ 𝐏¹_X`. -/
@[reassoc]
theorem specMap_evalZero_infinityChartOver (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X, U.1)))) ≫
        infinityChartOver U = U.2.fromSpec ≫ lineInfinitySection X := by
  rw [← lineInfinitySection_eq, infinityChartOver]
  simp only [← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, affineLineOverMap_fst, Category.assoc, ← Category.assoc _ _ U.2.fromSpec,
      affineLineOverIsoSpecPolynomial_inv_comp, ← Category.assoc, ← Spec.map_comp,
      Category.assoc, affineLineConstantSection, pullback.lift_fst, Category.comp_id]
    have hid : CommRingCat.ofHom (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1)) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X, U.1))) = 𝟙 _ := by
      ext x
      simp
    rw [hid, Spec.map_id, Category.id_comp]
  · rw [Category.assoc, affineLineOverMap_snd, Category.assoc,
      affineLineOverIsoSpecPolynomial_inv_snd, Category.assoc, affineLineConstantSection,
      pullback.lift_snd, ← Category.assoc, terminal.comp_from, integralAffineZeroSection,
      ← Category.assoc, ← Spec.map_comp]
    have ht : terminal.from (Spec (CommRingCat.of Γ(X, U.1))) ≫
        specULiftZIsTerminal.from (⊤_ Scheme.{u}) =
        Spec.map (CommRingCat.ofHom ((Int.castRingHom Γ(X, U.1)).comp
          (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)) :=
      specULiftZIsTerminal.hom_ext _ _
    rw [ht, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    refine polynomial_ulift_int_ringHom_ext ?_
    simp


/-! ### The centre at infinity on the chart at infinity -/

section Centre

variable (ℐ : X.IdealSheafData)

/-- **On the chart at infinity over `U`, the centre `∞(Z)` is `J = (I, s)`**, where `I = ℐ(U)`
and `s` is the coordinate of the chart. -/
theorem ideal_comap_infinityCentreIdeal_infinityChartOver (U : X.affineOpens) :
    ((infinityCentreIdeal ℐ).comap (infinityChartOver U)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (infinityChartIdeal (ℐ.ideal U)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial Γ(X, U.1)))).inv.hom := by
  have h1 : (infinityCentreIdeal ℐ).comap (infinityChartOver U) =
      ℐ.comap (Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1))) ≫
          U.2.fromSpec) ⊔ (lineInfinityDivisor X).comap (infinityChartOver U) := by
    rw [infinityCentreIdeal_eq_sup, (Scheme.IdealSheafData.map_gc (infinityChartOver U)).l_sup,
      ← Scheme.IdealSheafData.comap_comp, infinityChartOver_comp]
  have h2 : (ℐ.comap (Spec.map (CommRingCat.ofHom
      (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1))) ≫ U.2.fromSpec)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      ((ℐ.ideal U).map (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1))).map
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial Γ(X, U.1)))).inv.hom := by
    rw [Scheme.IdealSheafData.comap_comp, Stacks.IdealSheaf.ideal_comap_top_of_isAffine,
      Stacks.Blowup.ideal_comap_fromSpec_top ℐ U, Ideal.map_map, Ideal.map_map,
      ← CommRingCat.hom_comp, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have h3 := congrFun (Scheme.IdealSheafData.ideal_sup (I := ℐ.comap (Spec.map (CommRingCat.ofHom
      (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1))) ≫ U.2.fromSpec))
      (J := (lineInfinityDivisor X).comap (infinityChartOver U))) ⟨⊤, isAffineOpen_top _⟩
  rw [h1, h3, Pi.sup_apply, h2, ideal_comap_lineInfinityDivisor_infinityChartOver,
    infinityChartIdeal, Ideal.map_sup, map_span_singleton_eq]

end Centre

/-! ### The chart `D₊(S)` of the blowup at infinity over an affine open of `X` -/

section Chart

variable (ℐ : X.IdealSheafData) (U : X.affineOpens)

/-- The affine open of `𝐏¹_X` underlying the chart at infinity over `U`. -/
def infinityChartAffineOpen : (relativeProjectiveLine X).affineOpens :=
  ⟨infinityChartOver U ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩

/-- The identification `Γ(X, U)[s] ≅ Γ(𝐏¹_X, chart at infinity over U)`. -/
def infinityChartSectionsEquiv :
    Polynomial Γ(X, U.1) ≃+* Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial Γ(X, U.1)))).symm ≪≫
    ((infinityChartOver U).appIso ⊤).symm).commRingCatIsoToRingEquiv

/-- `infinityChartSectionsEquiv U p` is the image of `p` under the inverses of
`Scheme.ΓSpecIso` and of `(infinityChartOver U).appIso ⊤`. -/
theorem infinityChartSectionsEquiv_apply (p : Polynomial Γ(X, U.1)) :
    infinityChartSectionsEquiv U p =
      ((infinityChartOver U).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial Γ(X, U.1)))).inv p) := rfl

/-- On the chart at infinity over `U`, the divisor at infinity is the extension of `(s)`. -/
private theorem ideal_comap_lineInfinityDivisor_infinityChartOver_eq_map (U : X.affineOpens) :
    ((lineInfinityDivisor X).comap (infinityChartOver U)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {(Polynomial.X : Polynomial Γ(X, U.1))}).map
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial Γ(X, U.1)))).inv.hom := by
  rw [ideal_comap_lineInfinityDivisor_infinityChartOver, map_span_singleton_eq]

/-- An ideal sheaf on `𝐏¹_X`, read on the chart at infinity over `U`, is its inverse image along
the chart, transported through `infinityChartSectionsEquiv`. -/
theorem ideal_infinityChartAffineOpen_eq_map (K : (relativeProjectiveLine X).IdealSheafData)
    (J : Ideal (Polynomial Γ(X, U.1)))
    (hK : (K.comap (infinityChartOver U)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      J.map (Scheme.ΓSpecIso (CommRingCat.of (Polynomial Γ(X, U.1)))).inv.hom) :
    K.ideal (infinityChartAffineOpen U) = J.map (infinityChartSectionsEquiv U) := by
  have h1 := K.ideal_comap_of_isOpenImmersion (infinityChartOver U) ⟨⊤, isAffineOpen_top _⟩
  rw [hK, Stacks.Blowup.comap_inv_eq_map_hom] at h1
  have h2 := congrArg (Ideal.map ((infinityChartOver U).appIso ⊤).inv.hom) h1
  simp only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
    Ideal.map_id] at h2
  exact h2.symm

/-- **The centre `∞(Z)` on the chart at infinity over `U` is `J = (ℐ(U), s)`.** -/
theorem ideal_infinityCentreIdeal_infinityChartAffineOpen :
    (infinityCentreIdeal ℐ).ideal (infinityChartAffineOpen U) =
      (infinityChartIdeal (ℐ.ideal U)).map (infinityChartSectionsEquiv U) :=
  ideal_infinityChartAffineOpen_eq_map U _ _
    (ideal_comap_infinityCentreIdeal_infinityChartOver ℐ U)

/-- **The divisor at infinity on the chart at infinity over `U` is `(s)`.** -/
theorem ideal_lineInfinityDivisor_infinityChartAffineOpen :
    (lineInfinityDivisor X).ideal (infinityChartAffineOpen U) =
      Ideal.span {infinityChartSectionsEquiv U Polynomial.X} := by
  rw [ideal_infinityChartAffineOpen_eq_map U _ (Ideal.span {Polynomial.X})
    (ideal_comap_lineInfinityDivisor_infinityChartOver_eq_map U), map_span_singleton_eq]

/-- The coordinate `s` of the chart at infinity, as a section of the centre `∞(Z)`. -/
def infinityChartCoordinateSection : (infinityCentreIdeal ℐ).ideal (infinityChartAffineOpen U) :=
  ⟨infinityChartSectionsEquiv U Polynomial.X, by
    rw [ideal_infinityCentreIdeal_infinityChartAffineOpen]
    exact Ideal.mem_map_of_mem _ (X_mem_infinityChartIdeal _)⟩

/-- **The chart `D₊(S)` of the blowup at infinity over `U`**: the standard affine chart of
`W = Bl_{∞(Z)} 𝐏¹_X` attached to the chart at infinity over `U` and its coordinate `s`. -/
def blowupAtInfinityChart :
    Spec (.of (blowUpAffineChartRing (infinityCentreIdeal ℐ) (infinityChartAffineOpen U)
      (infinityChartCoordinateSection ℐ U))) ⟶ blowupAtInfinity ℐ :=
  blowUpAffineChart (infinityCentreIdeal ℐ) (infinityChartAffineOpen U)
    (infinityChartCoordinateSection ℐ U)

/-- The chart `D₊(S)` of the blowup at infinity over `U` is an open immersion. -/
instance : IsOpenImmersion (blowupAtInfinityChart ℐ U) :=
  isOpenImmersion_blowUpAffineChart _ _ _

end Chart

/-! ### Transport of the affine charts of the blowup at infinity to the polynomial ring -/

section ChartRing

/-- The localization `R_a ≅ R'_{e(a)}` induced by a ring isomorphism `e : R ≃+* R'`. -/
def localizationAwayEquivOfRingEquiv {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R')
    (a : R) : Localization.Away a ≃+* Localization.Away (e a) :=
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers a)
    (T := Submonoid.powers (e a)) (Localization.Away a) (Localization.Away (e a)) e
    (by rw [Submonoid.map_powers]; rfl)

/-- The isomorphism `R_a ≃+* R'_{e(a)}` sends the image of `x` to the image of `e x`. -/
theorem localizationAwayEquivOfRingEquiv_algebraMap {R R' : Type*} [CommRing R] [CommRing R']
    (e : R ≃+* R') (a x : R) :
    localizationAwayEquivOfRingEquiv e a (algebraMap _ _ x) = algebraMap _ _ (e x) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ x

/-- For `e : R ≃+* R'` and `J' = e(J)`, there is a ring isomorphism
`R[J/a] ≃+* R'[J'/e(a)]` of affine blowup algebras given on underlying elements of the
localizations by `localizationAwayEquivOfRingEquiv e a`. -/
theorem exists_affineBlowupAlgebraRingEquivOfRingEquiv {R R' : Type*} [CommRing R]
    [CommRing R'] (e : R ≃+* R') (J : Ideal R) (J' : Ideal R') (hJ : J' = J.map e) (a : R) :
    ∃ E : affineBlowupAlgebra J a (Localization.Away a) ≃+*
      affineBlowupAlgebra J' (e a) (Localization.Away (e a)),
      ∀ x, (E x : Localization.Away (e a)) =
        localizationAwayEquivOfRingEquiv e a (x : Localization.Away a) :=
  Stacks.Blowup.exists_ringEquiv_affineBlowupAlgebra' e
    (localizationAwayEquivOfRingEquiv e a) a J J' (e a)
    (localizationAwayEquivOfRingEquiv_algebraMap e a) hJ rfl

/-- **Transport of the affine blowup algebra along a ring isomorphism**: for `e : R ≃+* R'` and
`J' = e(J)`, the affine blowup algebras `R[J/a]` and `R'[J'/e(a)]` are isomorphic, compatibly
with the localizations. -/
def affineBlowupRingEquivOfRingEquiv {R R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R')
    (J : Ideal R) (J' : Ideal R') (hJ : J' = J.map e) (a : R) :
    affineBlowup J a ≃+* affineBlowupAlgebra J' (e a) (Localization.Away (e a)) :=
  (Subalgebra.equivOfEq _ _ (affineBlowup_eq_affineBlowupAlgebra J a)).toRingEquiv.trans
    (exists_affineBlowupAlgebraRingEquivOfRingEquiv e J J' hJ a).choose

/-- On underlying elements of the localizations, `affineBlowupRingEquivOfRingEquiv` is
`localizationAwayEquivOfRingEquiv e a`. -/
theorem affineBlowupRingEquivOfRingEquiv_coe {R R' : Type*} [CommRing R] [CommRing R']
    (e : R ≃+* R') (J : Ideal R) (J' : Ideal R') (hJ : J' = J.map e) (a : R)
    (x : affineBlowup J a) :
    (affineBlowupRingEquivOfRingEquiv e J J' hJ a x : Localization.Away (e a)) =
      localizationAwayEquivOfRingEquiv e a (x : Localization.Away a) := by
  rw [affineBlowupRingEquivOfRingEquiv, RingEquiv.trans_apply,
    (exists_affineBlowupAlgebraRingEquivOfRingEquiv e J J' hJ a).choose_spec,
    AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Subalgebra.equivOfEq_apply]

/-- `affineBlowupRingEquivOfRingEquiv` sends the image of `x ∈ R` to the image of `e x`. -/
theorem affineBlowupRingEquivOfRingEquiv_algebraMap {R R' : Type*} [CommRing R] [CommRing R']
    (e : R ≃+* R') (J : Ideal R) (J' : Ideal R') (hJ : J' = J.map e) (a x : R) :
    affineBlowupRingEquivOfRingEquiv e J J' hJ a (algebraMap _ _ x) =
      algebraMap _ _ (e x) := by
  apply Subtype.ext
  rw [affineBlowupRingEquivOfRingEquiv_coe]
  exact localizationAwayEquivOfRingEquiv_algebraMap e a x

variable (ℐ : X.IdealSheafData) (U : X.affineOpens)

/-- For `a ∈ J = (ℐ(U), s)`, the section `infinityChartSectionsEquiv U a` lies in the centre
`∞(Z)` on the chart at infinity. -/
theorem infinityChartSectionsEquiv_mem (a : Polynomial Γ(X, U.1))
    (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) :
    infinityChartSectionsEquiv U a ∈ (infinityCentreIdeal ℐ).ideal (infinityChartAffineOpen U) := by
  rw [ideal_infinityCentreIdeal_infinityChartAffineOpen]
  exact Ideal.mem_map_of_mem _ ha

/-- The identification of the coordinate ring of the chart `D₊(a⁽¹⁾)` of `W` with
`Γ(X, U)[s][J/a]`. -/
def infinityChartRingEquiv (a : Polynomial Γ(X, U.1)) (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) :
    affineBlowup (infinityChartIdeal (ℐ.ideal U)) a ≃+*
      blowUpAffineChartRing (infinityCentreIdeal ℐ) (infinityChartAffineOpen U)
        ⟨infinityChartSectionsEquiv U a, infinityChartSectionsEquiv_mem ℐ U a ha⟩ :=
  affineBlowupRingEquivOfRingEquiv (infinityChartSectionsEquiv U) _ _
    (ideal_infinityCentreIdeal_infinityChartAffineOpen ℐ U) a

/-- `infinityChartRingEquiv` sends the image of `x ∈ Γ(X, U)[s]` to the image of
`infinityChartSectionsEquiv U x`. -/
theorem infinityChartRingEquiv_algebraMap (a : Polynomial Γ(X, U.1))
    (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) (x : Polynomial Γ(X, U.1)) :
    infinityChartRingEquiv ℐ U a ha (algebraMap _ _ x) =
      algebraMap _ _ (infinityChartSectionsEquiv U x) :=
  affineBlowupRingEquivOfRingEquiv_algebraMap _ _ _ _ a x

/-- The inverse of `infinityChartRingEquiv` sends the image of a section `y` of the chart at
infinity to the image of `(infinityChartSectionsEquiv U).symm y`. -/
theorem infinityChartRingEquiv_symm_algebraMap (a : Polynomial Γ(X, U.1))
    (ha : a ∈ infinityChartIdeal (ℐ.ideal U))
    (y : Γ(relativeProjectiveLine X, (infinityChartAffineOpen U).1)) :
    (infinityChartRingEquiv ℐ U a ha).symm (algebraMap _ _ y) =
      algebraMap _ _ ((infinityChartSectionsEquiv U).symm y) := by
  apply (infinityChartRingEquiv ℐ U a ha).injective
  rw [RingEquiv.apply_symm_apply, infinityChartRingEquiv_algebraMap, RingEquiv.apply_symm_apply]

/-- **The standard chart `D₊(a⁽¹⁾) ⟶ W` over the chart at infinity**, with source the spectrum of
`Γ(X, U)[s][J/a]`. -/
def blowupAtInfinityPolyChart (a : Polynomial Γ(X, U.1))
    (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) :
    Spec (.of (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a)) ⟶ blowupAtInfinity ℐ :=
  Spec.map (infinityChartRingEquiv ℐ U a ha).toCommRingCatIso.inv ≫
    (blowUpAffineChart (infinityCentreIdeal ℐ) (infinityChartAffineOpen U) _ :
      _ ⟶ blowupAtInfinity ℐ)

/-- The chart `D₊(a⁽¹⁾) ⟶ W` is an open immersion. -/
instance (a : Polynomial Γ(X, U.1)) (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) :
    IsOpenImmersion (blowupAtInfinityPolyChart ℐ U a ha) :=
  IsOpenImmersion.comp (Spec.map _)
    (blowUpAffineChart (infinityCentreIdeal ℐ) (infinityChartAffineOpen U) _)

/-- **The standard chart lies over the chart at infinity**: composed with `b : W ⟶ 𝐏¹_X` it is
`Spec` of the structure map `Γ(X, U)[s] ⟶ Γ(X, U)[s][J/a]` followed by the chart at infinity. -/
@[reassoc]
theorem blowupAtInfinityPolyChart_comp (a : Polynomial Γ(X, U.1))
    (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) :
    blowupAtInfinityPolyChart ℐ U a ha ≫ blowupAtInfinityToLine ℐ =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial Γ(X, U.1))
        (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a))) ≫ infinityChartOver U := by
  show (Spec.map _ ≫ blowUpAffineChart (infinityCentreIdeal ℐ) (infinityChartAffineOpen U)
    ⟨infinityChartSectionsEquiv U a, infinityChartSectionsEquiv_mem ℐ U a ha⟩) ≫
      blowUpToBase (infinityCentreIdeal ℐ) = _
  rw [Category.assoc, blowUpAffineChart_comp_blowUpToBase, ← Spec.map_comp_assoc]
  have hm := SpecMap_appIso_ΓSpecIso_fromSpec (infinityChartOver U)
  rw [← hm, ← Spec.map_comp_assoc]
  have hfrom : (infinityChartAffineOpen U).2.isoSpec.inv ≫ (infinityChartAffineOpen U).1.ι =
      ((isAffineOpen_top _).image_of_isOpenImmersion (infinityChartOver U)).fromSpec := rfl
  rw [hfrom]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext (infinityChartRingEquiv_symm_algebraMap ℐ U a ha))

end ChartRing

/-! ### Recognizing the charts `D₊(a⁽¹⁾)` by the exceptional ideal -/

section Recognition

variable (ℐ : X.IdealSheafData) (U : X.affineOpens)

/-- The range of a composite with an isomorphism on the left. -/
theorem range_isIso_comp {T T' T'' : Scheme.{u}} (f : T ⟶ T') [IsIso f] (g : T' ⟶ T'') :
    Set.range (f ≫ g) = Set.range g := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have : Set.range f = Set.univ := f.homeomorph.surjective.range_eq
  rw [this, Set.image_univ]

/-- **Stacks 0BFL on the blowup at infinity.** A point `w` of `W` over the chart at infinity over
`U` lies in the chart `D₊(a⁽¹⁾)`, `a ∈ J = (ℐ(U), s)`, exactly when `a` generates the exceptional
ideal in the local ring of `W` at `w`. -/
theorem mem_range_blowupAtInfinityPolyChart_iff (a : Polynomial Γ(X, U.1))
    (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) (w : blowupAtInfinity ℐ)
    (hw : blowupAtInfinityToLine ℐ w ∈ (infinityChartAffineOpen U).1) :
    w ∈ Set.range (blowupAtInfinityPolyChart ℐ U a ha) ↔
      IdealSheafData.stalk (exceptionalIdealAtInfinity ℐ) w =
        Ideal.span
          {(blowupAtInfinityToLine ℐ).stalkMap w
            ((relativeProjectiveLine X).presheaf.germ (infinityChartAffineOpen U).1 _ hw
              (infinityChartSectionsEquiv U a))} := by
  let := (reesSituation (infinityCentreIdeal ℐ)).sectionRingGradedRing
    (infinityChartAffineOpen U).1
  let := (reesSituation (infinityCentreIdeal ℐ)).sectionRingGradingGradedRing
    (infinityChartAffineOpen U).1
  have h1 : Set.range (blowupAtInfinityPolyChart ℐ U a ha) =
      Set.range (blowUpAffineChart (infinityCentreIdeal ℐ) (infinityChartAffineOpen U)
        ⟨infinityChartSectionsEquiv U a, infinityChartSectionsEquiv_mem ℐ U a ha⟩) :=
    range_isIso_comp _ _
  have h2 : Set.range (blowUpAffineChart (infinityCentreIdeal ℐ) (infinityChartAffineOpen U)
        ⟨infinityChartSectionsEquiv U a, infinityChartSectionsEquiv_mem ℐ U a ha⟩) =
      Set.range ((Proj.basicOpen ((reesSituation (infinityCentreIdeal ℐ)).sectionRingGrading
          (infinityChartAffineOpen U).1)
        (reesDegreeOne (infinityCentreIdeal ℐ) (infinityChartAffineOpen U)
          ⟨infinityChartSectionsEquiv U a, infinityChartSectionsEquiv_mem ℐ U a ha⟩).1).ι ≫
        Stacks.RelativeProj.Situation.relativeProjChart (reesSituation (infinityCentreIdeal ℐ))
          (infinityChartAffineOpen U)) := by
    unfold blowUpAffineChart
    exact range_isIso_comp _ _
  rw [h1, h2]
  exact mem_affineBlowupStandardOpen_iff_exceptionalIdeal_stalk_eq_span
    (infinityCentreIdeal ℐ) (infinityChartAffineOpen U)
    ⟨infinityChartSectionsEquiv U a, infinityChartSectionsEquiv_mem ℐ U a ha⟩ w hw

/-- **The fibre at infinity in the local rings of `W` over the chart at infinity** is generated
by the coordinate `s`. -/
theorem stalk_fibreIdealAtInfinity (w : blowupAtInfinity ℐ)
    (hw : blowupAtInfinityToLine ℐ w ∈ (infinityChartAffineOpen U).1) :
    IdealSheafData.stalk (fibreIdealAtInfinity ℐ) w =
      Ideal.span
        {(blowupAtInfinityToLine ℐ).stalkMap w
            ((relativeProjectiveLine X).presheaf.germ (infinityChartAffineOpen U).1 _ hw
              (infinityChartSectionsEquiv U Polynomial.X))} := by
  rw [fibreIdealAtInfinity, IdealSheafData.stalk_comap,
    IdealSheafData.stalk_eq_map_germ _ _ (infinityChartAffineOpen U) hw,
    ideal_lineInfinityDivisor_infinityChartAffineOpen, map_span_singleton_eq,
    map_span_singleton_eq]

/-- **A point over the chart at infinity lies in `D₊(S)` exactly when the exceptional divisor and
the fibre at infinity have the same local ideal there.** -/
theorem mem_range_blowupAtInfinityChartS_iff (w : blowupAtInfinity ℐ)
    (hw : blowupAtInfinityToLine ℐ w ∈ (infinityChartAffineOpen U).1) :
    w ∈ Set.range (blowupAtInfinityPolyChart ℐ U Polynomial.X (X_mem_infinityChartIdeal _)) ↔
      IdealSheafData.stalk (exceptionalIdealAtInfinity ℐ) w =
        IdealSheafData.stalk (fibreIdealAtInfinity ℐ) w := by
  rw [mem_range_blowupAtInfinityPolyChart_iff, stalk_fibreIdealAtInfinity ℐ U w hw]

end Recognition

/-! ### The exceptional divisor and the fibre at infinity on the charts `D₊(a⁽¹⁾)` -/

/-- Extending an ideal along two composites of ring maps that agree gives the same ideal. -/
theorem _root_.Ideal.map_map_eq_of_comp_eq {R S T S' : Type*} [CommRing R] [CommRing S]
    [CommRing T] [CommRing S'] (ψ : R →+* S) (φ : S →+* T) (α : R →+* S') (χ : S' →+* T)
    (h : φ.comp ψ = χ.comp α) (J : Ideal R) : (J.map ψ).map φ = (J.map α).map χ := by
  rw [Ideal.map_map, Ideal.map_map, h]

section ChartIdeals

variable (ℐ : X.IdealSheafData) (U : X.affineOpens)

/-- An ideal sheaf `K` of `𝐏¹_X`, pulled back to `W` and then to the chart `D₊(a⁽¹⁾)`, is the
extension of its ideal on the chart at infinity. -/
theorem ideal_comap_comap_blowupAtInfinityPolyChart (a : Polynomial Γ(X, U.1))
    (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) (K : (relativeProjectiveLine X).IdealSheafData)
    (J₀ : Ideal (Polynomial Γ(X, U.1)))
    (hK : (K.comap (infinityChartOver U)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      J₀.map (Scheme.ΓSpecIso (CommRingCat.of (Polynomial Γ(X, U.1)))).inv.hom) :
    ((K.comap (blowupAtInfinityToLine ℐ)).comap (blowupAtInfinityPolyChart ℐ U a ha)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      (J₀.map (algebraMap (Polynomial Γ(X, U.1))
        (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a))).map
          (Scheme.ΓSpecIso
            (CommRingCat.of (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a))).inv.hom := by
  have h1 : (K.comap (blowupAtInfinityToLine ℐ)).comap (blowupAtInfinityPolyChart ℐ U a ha) =
      (K.comap (infinityChartOver U)).comap (Spec.map (CommRingCat.ofHom
        (algebraMap (Polynomial Γ(X, U.1))
          (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a)))) := by
    rw [← Scheme.IdealSheafData.comap_comp K (blowupAtInfinityPolyChart ℐ U a ha)
        (blowupAtInfinityToLine ℐ), blowupAtInfinityPolyChart_comp,
      Scheme.IdealSheafData.comap_comp]
  have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
    (algebraMap (Polynomial Γ(X, U.1)) (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a)))
  refine (congrArg (fun K' : (Spec (CommRingCat.of
    (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a))).IdealSheafData =>
      K'.ideal ⟨⊤, isAffineOpen_top _⟩) h1).trans ?_
  refine (Stacks.IdealSheaf.ideal_comap_top_of_isAffine _ _).trans ?_
  refine (congrArg (Ideal.map (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial Γ(X, U.1))
    (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a)))).appTop.hom) hK).trans ?_
  exact Ideal.map_map_eq_of_comp_eq _ _ _ _
    (RingHom.ext fun x => (congrArg (fun g => CommRingCat.Hom.hom g x) hnat).symm) J₀

/-- **On the chart `D₊(a⁽¹⁾)` the exceptional divisor is cut out by `a`.** -/
theorem ideal_comap_exceptionalIdealAtInfinity_polyChart (a : Polynomial Γ(X, U.1))
    (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) :
    ((exceptionalIdealAtInfinity ℐ).comap (blowupAtInfinityPolyChart ℐ U a ha)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span
        {(Scheme.ΓSpecIso (CommRingCat.of
            (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a))).inv.hom
              (algebraMap _ (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a) a)} := by
  have h := ideal_comap_comap_blowupAtInfinityPolyChart ℐ U a ha (infinityCentreIdeal ℐ) _
      (ideal_comap_infinityCentreIdeal_infinityChartOver ℐ U)
  exact h.trans ((congrArg (Ideal.map _)
    (Stacks.Blowup.affineBlowup_idealMap_eq_span _ a ha)).trans (map_span_singleton_eq _ _))

/-- **On the chart `D₊(a⁽¹⁾)` the fibre at infinity is cut out by `s`.** -/
theorem ideal_comap_fibreIdealAtInfinity_polyChart (a : Polynomial Γ(X, U.1))
    (ha : a ∈ infinityChartIdeal (ℐ.ideal U)) :
    ((fibreIdealAtInfinity ℐ).comap (blowupAtInfinityPolyChart ℐ U a ha)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span
        {(Scheme.ΓSpecIso (CommRingCat.of
            (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a))).inv.hom
              (algebraMap (Polynomial Γ(X, U.1)) (affineBlowup (infinityChartIdeal (ℐ.ideal U)) a)
                Polynomial.X)} := by
  have h := ideal_comap_comap_blowupAtInfinityPolyChart ℐ U a ha (lineInfinityDivisor X)
    (Ideal.span {(Polynomial.X : Polynomial Γ(X, U.1))})
    (ideal_comap_lineInfinityDivisor_infinityChartOver_eq_map U)
  exact h.trans ((congrArg (Ideal.map _) (map_span_singleton_eq _ _)).trans
    (map_span_singleton_eq _ _))

end ChartIdeals

/-! ### `D₊(S)` is the complement of `X'` over the chart at infinity -/

section ComplementChart

variable (ℐ : X.IdealSheafData) (U : X.affineOpens)

/-- In a commutative ring, `(g) · J = (g)` for a regular element `g` forces `J = ⊤`. -/
theorem _root_.Ideal.eq_top_of_span_singleton_mul_eq {R : Type*} [CommRing R] {g : R}
    (hg : IsRegular g) {J : Ideal R} (h : Ideal.span {g} * J = Ideal.span {g}) : J = ⊤ := by
  have hmem : g ∈ Ideal.span {g} * J := h.symm ▸ Ideal.mem_span_singleton_self g
  rw [Ideal.mem_span_singleton_mul] at hmem
  obtain ⟨j, hj, hgj⟩ := hmem
  have h1 : j = 1 := hg.left (show g * j = g * 1 by rw [hgj, mul_one])
  exact (Ideal.eq_top_iff_one J).mpr (h1 ▸ hj)

/-- **Over the chart at infinity, `D₊(S) = W ∖ X'`**: a point of `W` over the chart at infinity
lies in `D₊(S)` exactly when it is not in the support of the strict transform `X'`. -/
theorem mem_range_blowupAtInfinityChartS_iff_notMem (w : blowupAtInfinity ℐ)
    (hw : blowupAtInfinityToLine ℐ w ∈ (infinityChartAffineOpen U).1) :
    w ∈ Set.range (blowupAtInfinityPolyChart ℐ U Polynomial.X (X_mem_infinityChartIdeal _)) ↔
      w ∉ (strictTransformIdealAtInfinity ℐ).support := by
  rw [mem_range_blowupAtInfinityChartS_iff ℐ U w hw,
    fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity, IdealSheafData.stalk_mul,
    ← IdealSheafData.stalk_eq_top_iff_not_mem_support]
  obtain ⟨g, hg, hgen⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _
    (isEffectiveCartierDivisor_exceptionalIdealAtInfinity ℐ) w
  rw [hgen]
  exact ⟨fun h => Ideal.eq_top_of_span_singleton_mul_eq hg h.symm, fun h => by
    rw [h, Ideal.mul_top]⟩

end ComplementChart

/-! ### Naturality of the charts in the affine open of `X` -/

section Naturality

variable (ℐ : X.IdealSheafData)

/-- The restriction map `Γ(X, U) ⟶ Γ(X, V)` for `V ⊆ U`. -/
abbrev affineRestrict {U V : X.affineOpens} (h : V.1 ≤ U.1) : Γ(X, U.1) →+* Γ(X, V.1) :=
  (X.presheaf.map (homOfLE h).op).hom

/-- **The charts at infinity are compatible with restriction**: for `V ⊆ U`, the chart at
infinity over `V` is `Spec` of the polynomial map of the restriction, followed by the chart at
infinity over `U`. -/
theorem specMap_map_infinityChartOver {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (affineRestrict h))) ≫
      infinityChartOver U = infinityChartOver V := by
  have key : ∀ W : X.affineOpens, infinityChartOver W = infinityChartBase W ≫ affineYChart X :=
    fun W => (Category.assoc _ _ _).symm
  rw [key, key, ← Category.assoc]
  congr 1
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, infinityChartBase_fst, infinityChartBase_fst, ← Category.assoc,
      ← Spec.map_comp, ← IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE h).op, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    refine RingHom.ext fun a => ?_
    simp
  · rw [Category.assoc, infinityChartBase_snd, infinityChartBase_snd, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    refine polynomial_ulift_int_ringHom_ext ?_
    simp

/-- For `V ⊆ U`, the restriction map sends `ℐ(U)` into `ℐ(V)`. -/
theorem map_ideal_infinityChart_le {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    (ℐ.ideal U).map (affineRestrict h) ≤ ℐ.ideal V :=
  (ℐ.map_ideal (U := V) (V := U) h).le

/-- The chart `D₊(S)` over `U`. -/
abbrev blowupAtInfinityChartS (U : X.affineOpens) :
    Spec (.of (infinityChartAlgebra (ℐ.ideal U))) ⟶ blowupAtInfinity ℐ :=
  blowupAtInfinityPolyChart ℐ U Polynomial.X (X_mem_infinityChartIdeal _)

/-- The exceptional divisor pulls back to an effective Cartier divisor along the chart
`D₊(S)`: it is cut out there by the nonzerodivisor `s`. -/
theorem isEffectiveCartierDivisor_comap_blowupAtInfinityChartS (U : X.affineOpens) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((exceptionalIdealAtInfinity ℐ).comap (blowupAtInfinityChartS ℐ U)) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun _ =>
    ⟨⊤, isAffineOpen_top _, trivial, _, ?_,
      ideal_comap_exceptionalIdealAtInfinity_polyChart ℐ U Polynomial.X
        (X_mem_infinityChartIdeal _)⟩
  rw [isRegular_iff_mem_nonZeroDivisors]
  exact Stacks.Blowup.mem_nonZeroDivisors_iso (Scheme.ΓSpecIso _).symm
    (Stacks.Blowup.algebraMap_affineBlowup_mem_nonZeroDivisors _ _)

/-- **The charts `D₊(S)` are compatible with restriction.** For `V ⊆ U`, the chart over `V` is
`Spec` of the induced map of affine blowup algebras followed by the chart over `U`. -/
theorem specMap_infinityChartAlgebraMap_blowupAtInfinityChartS {U V : X.affineOpens}
    (h : V.1 ≤ U.1) :
    Spec.map (CommRingCat.ofHom (infinityChartAlgebraMap (affineRestrict h)
        (map_ideal_infinityChart_le ℐ h))) ≫ blowupAtInfinityChartS ℐ U =
      blowupAtInfinityChartS ℐ V := by
  have hg : Stacks.Blowup.IsCartierOver (infinityCentreIdeal ℐ)
      (Over.mk (blowupAtInfinityChartS ℐ V ≫ blowupAtInfinityToLine ℐ)) := by
    show Stacks.Divisors.IsEffectiveCartierDivisor
      ((infinityCentreIdeal ℐ).comap (blowupAtInfinityChartS ℐ V ≫ blowupAtInfinityToLine ℐ))
    rw [Scheme.IdealSheafData.comap_comp]
    exact isEffectiveCartierDivisor_comap_blowupAtInfinityChartS ℐ V
  have h1 : (Spec.map (CommRingCat.ofHom (infinityChartAlgebraMap (affineRestrict h)
        (map_ideal_infinityChart_le ℐ h))) ≫ blowupAtInfinityChartS ℐ U) ≫
      blowUpToBase (infinityCentreIdeal ℐ) =
      blowupAtInfinityChartS ℐ V ≫ blowupAtInfinityToLine ℐ := by
    show _ ≫ blowupAtInfinityToLine ℐ = _
    rw [Category.assoc, blowupAtInfinityChartS, blowupAtInfinityChartS,
      blowupAtInfinityPolyChart_comp, blowupAtInfinityPolyChart_comp,
      ← specMap_map_infinityChartOver h, ← Category.assoc, ← Spec.map_comp, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    exact RingHom.ext (infinityChartAlgebraMap_algebraMap _ (map_ideal_infinityChart_le ℐ h))
  exact (blowUpLift_unique _ _ hg _ h1).trans (blowUpLift_unique _ _ hg _ rfl).symm

end Naturality

end Stacks.Chow

end
