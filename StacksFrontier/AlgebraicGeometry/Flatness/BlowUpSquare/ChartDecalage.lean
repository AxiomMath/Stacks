module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalChart
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedBoundedAffine
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedRestrictOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfectOffDivisor
public import StacksFrontier.AlgebraicGeometry.Modules.TildeTransportRestrict

/-!
# Perfectness of the derived décalage of a good triple

Let `X` be a scheme, `D ⊆ X` an effective Cartier divisor with ideal sheaf `I` and `M` a perfect
object of `D(𝒪_X)`. If `(X, D, M)` is a good triple, then `Lη_I M` is perfect (Stacks tag 0GTW).

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.chartDerivedEtaIso`: on an affine chart
  `(U, A, f, M^•)`, the restriction of `Lη_I M` to `U` is the complex of `𝒪_U`-modules attached
  to `η_f M^•` (the second assertion of Stacks tag 0GTV read at an affine open).
* `AlgebraicGeometry.ComplexAndDivisorSituation.standardM`: the object of a triple carried to the
  standard model of `D(𝒪_X)`, in which `Stacks.Divisors.Eta.derivedEtaData` is constructed.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.chartDecalage`: these comparisons, as the roofs
  of `AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage` for `Lη_I = derivedEtaData D`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEtaData_obj_of_isGoodTriple`:
  Stacks tag 0GTW for a triple at the standard model.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedEtaData_obj`: Stacks tag 0GTW.

## Implementation notes

The chart comparison composes four identifications: `Lη` commutes with restriction to `U`
(`Stacks.Divisors.Eta.derivedEtaRestrictModulesObjIso`) and with restriction along
`U ≅ Spec A` (`Stacks.Divisors.Eta.derivedEtaRestrictOpenObjIso`), applied to the inverse image
`D'` of `D` on `Spec A`; on `Spec A` the comparison is
`Stacks.Divisors.Eta.derivedEtaTildeChartIso`, `D'` being cut out by `f`
(`Stacks.Blowup.ideal_comap_fromSpec_top`); and the transport along `U ≅ Spec A` is
`Stacks.AffineTilde.transportTildeComplexIsoRestrict`.

## References

* [Stacks Project, Tag 0GTW](https://stacks.math.columbia.edu/tag/0GTW)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

open Stacks.Divisors.Eta (derivedEtaData)

variable {X : Scheme.{u}} (D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
  (M : DerivedCategory X.Modules) (hM : RingedSpace.IsPerfect (X := X.toRingedSpace) M)

/-- The derived décalage depends on the divisor only through its equality class. -/
theorem nonempty_derivedEtaData_obj_iso_of_eq {Y : Scheme.{u}} {D₁ D₂ : Y.IdealSheafData}
    [Stacks.Divisors.IsEffectiveCartierDivisor D₁] [Stacks.Divisors.IsEffectiveCartierDivisor D₂]
    (h : D₁ = D₂) (L : DerivedCategory Y.Modules) :
    Nonempty ((derivedEtaData D₁).functor.obj L ≅ (derivedEtaData D₂).functor.obj L) := by
  subst h
  exact ⟨Iso.refl _⟩

include hD in
/-- The inverse image of the divisor along `Spec Γ(X, U) ⟶ X` is cut out by the equation of an
affine chart, read in the global sections of `Spec Γ(X, U)`. -/
theorem ideal_comap_fromSpec_top_eq_span (C : AffineChart
      { X := X, D := D, isEffectiveCartierDivisor := hD, M := M, isPerfect := hM }) :
    (D.comap C.U.2.fromSpec).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {algebraMap Γ(X, C.U.1) (Stacks.Divisors.Eta.GammaTop Γ(X, C.U.1)) C.f} := by
  rw [Stacks.Blowup.ideal_comap_fromSpec_top D C.U, C.divisor_ideal, Ideal.map_span,
    Set.image_singleton]
  rfl

/-- The inverse image of the divisor along `Spec Γ(X, U) ⟶ X`, pulled back along
`U ≅ Spec Γ(X, U)`, is the inverse image of the divisor on `U`. -/
theorem comap_fromSpec_comap_isoSpec_hom (U : X.affineOpens) :
    (D.comap U.2.fromSpec).comap U.2.isoSpec.hom = D.comap U.1.ι := by
  rw [← Scheme.IdealSheafData.comap_comp]
  exact congrArg D.comap U.2.isoSpec_hom_fromSpec

include hD in
/-- **The derived décalage on an affine chart** (the second assertion of Stacks tag 0GTV read
at an affine open): on an affine chart `(U, A, f, M^•)` of `(X, D, M)`, the restriction of
`Lη_I M` to `U` is the complex of `𝒪_U`-modules attached to `η_f M^•`. -/
def chartDerivedEtaIso (C : AffineChart
      { X := X, D := D, isEffectiveCartierDivisor := hD, M := M, isPerfect := hM }) :
    (RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace C.U.1).mapDerivedCategory.obj
        ((derivedEtaData D).functor.obj M) ≅
      DerivedCategory.Q.obj C.specEtaComplex :=
  haveI := hD
  haveI : IsOpenImmersion C.U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec C.U.2
  haveI : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap C.U.2.fromSpec) :=
    Stacks.Divisors.Eta.isEffectiveCartierDivisor_comap_of_isOpenImmersion D C.U.2.fromSpec
  let j := C.U.2.isoSpec.hom
  let E := C.represents.choose
  let eM : DerivedCategory.Q.obj E ≅ M := C.represents.choose_spec.1.some
  let eU := C.represents.choose_spec.2.some
  Stacks.Divisors.Eta.derivedEtaRestrictModulesObjIso D C.U.1 M ≪≫
    (derivedEtaData (D.comap C.U.1.ι)).functor.mapIso
      ((RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace
          C.U.1).mapDerivedCategory.mapIso eM.symm ≪≫
        (RingedSpace.derivedRestrictModulesIsoRestrictFunctor X C.U.1).app _ ≪≫
        (Scheme.Modules.restrictFunctor C.U.1.ι).mapDerivedCategoryFactors.app E ≪≫ eU ≪≫
        DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (tilde.functor Γ(X, C.U.1) ⋙ Scheme.Modules.restrictFunctor j))
          (ComplexShape.up ℤ)).app C.complex.toCochainComplex).symm ≪≫
        ((Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app _).symm) ≪≫
    (nonempty_derivedEtaData_obj_iso_of_eq (comap_fromSpec_comap_isoSpec_hom D C.U).symm
      _).some ≪≫
    (Stacks.Divisors.Eta.derivedEtaRestrictOpenObjIso (D.comap C.U.2.fromSpec) j _).symm ≪≫
    (Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapIso
      (Stacks.Divisors.Eta.derivedEtaTildeChartIso Γ(X, C.U.1) (D.comap C.U.2.fromSpec) C.f
        C.complex (ideal_comap_fromSpec_top_eq_span D hD M hM C)) ≪≫
    (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor Γ(X, C.U.1) ⋙ Scheme.Modules.restrictFunctor j))
      (ComplexShape.up ℤ)).app C.etaComplex) ≪≫
    DerivedCategory.Q.mapIso
      (Stacks.AffineTilde.transportTildeComplexIsoRestrict Γ(X, C.U.1) C.U.2.isoSpec.symm
        C.etaComplex).symm

include hD in
/-- The affine-chart comparisons of a triple at the standard model of `D(𝒪_X)`, for the derived
décalage of tag 0F8Q: each is the roof of quasi-isomorphisms read off `chartDerivedEtaIso`. -/
theorem chartDecalage :
    ChartDecalage { X := X, D := D, isEffectiveCartierDivisor := hD, M := M, isPerfect := hM }
      (@derivedEtaData X D hD) where
  roof C _ := ChartDecalage.roof_of_iso C (chartDerivedEtaIso D hD M hM C)

include hD in
/-- Stacks tag 0GTW for a triple whose object lies in the standard model of `D(𝒪_X)`. -/
theorem isPerfect_derivedEtaData_obj_of_isGoodTriple
    (hgood : IsGoodTriple
      { X := X, D := D, isEffectiveCartierDivisor := hD, M := M, isPerfect := hM }) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) ((@derivedEtaData X D hD).functor.obj M) :=
  isPerfect_derivedEta_obj_of_isGoodTriple _ (@derivedEtaData X D hD) hgood
    (chartDecalage D hD M hM)

/-- The perfect object of a triple, carried to the standard model of `D(𝒪_X)`, in which the
derived décalage `Lη_I` of tag 0F8Q is constructed. -/
abbrev standardM (S : ComplexAndDivisorSituation.{u, d}) :
    DerivedCategory (StrictlyPerfect.OXMod.{u, u} S.X.toRingedSpace) :=
  (Localization.uniq (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
    (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u} S.X.toRingedSpace)))
    (HomologicalComplex.quasiIso (StrictlyPerfect.OXMod.{u, u} S.X.toRingedSpace)
      (ComplexShape.up ℤ))).functor.obj S.M

/-- The object of a triple stays perfect when carried to the standard model. -/
theorem isPerfect_standardM (S : ComplexAndDivisorSituation.{u, d}) :
    RingedSpace.IsPerfect (X := S.X.toRingedSpace) S.standardM :=
  RingedSpace.KFlatDerivedPullback.isPerfect_uniqFunctor_obj S.hasDerivedCategory
    (HasDerivedCategory.standard _) S.M S.isPerfect

/-- A good triple stays good when its object is carried to the standard model: an affine chart
of the one is an affine chart of the other. -/
theorem isGoodTriple_standardM (S : ComplexAndDivisorSituation.{u, d}) (hS : IsGoodTriple S) :
    IsGoodTriple
      { X := S.X, D := S.D, isEffectiveCartierDivisor := S.isEffectiveCartierDivisor,
        hasDerivedCategory := HasDerivedCategory.standard _, M := S.standardM,
        isPerfect := S.isPerfect_standardM } := by
  intro x hx
  obtain ⟨C, hxC, hI⟩ := hS x hx
  obtain ⟨E, ⟨hE⟩, hrest⟩ := C.represents
  let W := HomologicalComplex.quasiIso (StrictlyPerfect.OXMod.{u, u} S.X.toRingedSpace)
    (ComplexShape.up ℤ)
  let L := Localization.uniq (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
    (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
      (StrictlyPerfect.OXMod.{u, u} S.X.toRingedSpace))) W
  have eE : _ ≅ S.standardM :=
    ((Localization.compUniqFunctor (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
      (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
        (StrictlyPerfect.OXMod.{u, u} S.X.toRingedSpace))) W).app E).symm ≪≫
      L.functor.mapIso hE
  exact ⟨AffineChart.mk C.U C.f C.regular C.divisor_ideal C.complex ⟨E, ⟨eE⟩, hrest⟩, hxC, hI⟩

attribute [local instance] ComplexAndDivisorSituation.isEffectiveCartierDivisor in
/-- **[Stacks, Tag 0GTW].** Let `X, D, I, M` be as in Situation 0F8S. If `(X, D, M)` is a good
triple, then `Lη_I M` is a perfect object of `D(𝒪_X)`. Here `Lη_I` is the derived décalage of
tag 0F8Q and `M` is read in the model of `D(𝒪_X)` in which it is constructed. -/
@[stacks 0GTW "Lη_I M is perfect for a good triple (X, D, M); Lη_I is \
Stacks.Divisors.Eta.derivedEtaData, and M is carried to its model of D(𝒪_X) by the canonical \
equivalence of localizations"]
theorem isPerfect_derivedEtaData_obj (S : ComplexAndDivisorSituation.{u, d})
    (hS : IsGoodTriple S) :
    RingedSpace.IsPerfect (X := S.X.toRingedSpace)
      ((derivedEtaData S.D).functor.obj S.standardM) :=
  isPerfect_derivedEtaData_obj_of_isGoodTriple S.D S.isEffectiveCartierDivisor S.standardM
    S.isPerfect_standardM (S.isGoodTriple_standardM hS)

end AlgebraicGeometry.ComplexAndDivisorSituation

end
