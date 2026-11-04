module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.StructureSheafClass
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.UnitClassCup

/-!
# Uniqueness of the trace of relative Poincaré duality

Let `f : X ⟶ S` be a morphism of schemes and `t : Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S` a map whose pairing

`Rf_*Ω^0_{X/S} ⊗^L Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S`

(relative cup product, wedge product, `t`) is perfect. Then every map
`t' : Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S` is `g · t` for a unique `g ∈ Γ(X, 𝒪_X)`, and if the pairing of `t'`
in degree zero is perfect as well, `g` is a unit. This is the uniqueness half of
[Stacks, Tag 0G8I].

The argument is the source's, read in `D(𝒪_S)`: a map `t'` is determined by its precomposite with
the isomorphism `𝒪_S ⊗^L Rf_*Ω^n[n] ≅ Rf_*Ω^n[n]` (the cup product with the class of the unit),
that is, by a map `𝒪_S ⟶ R𝓗om(Rf_*Ω^n[n], 𝒪_S)`; through the isomorphism
`Rf_*Ω^0 ≅ R𝓗om(Rf_*Ω^n[n], 𝒪_S)` given by `t` this is a map `𝒪_S ⟶ Rf_*Ω^0`, the class of a
global function `g` (`AlgebraicGeometry.Scheme.Hom.bijective_globalFunctionClass`), and
`t' = g · t` by the `Γ(X, 𝒪_X)`-linearity of the pairing.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_eq_formsShiftSMul_comp`,
  `AlgebraicGeometry.Scheme.Hom.formsShiftSMul_comp_injective`: `t' = g · t` for a unique `g`.
* `AlgebraicGeometry.RelativeDualitySituation.IsRelativePoincareTrace.exists_units`: two traces
  differ by a unit.

## References

* [Stacks Project, Tag 0G8I](https://stacks.math.columbia.edu/tag/0G8I)
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedRelativeCupProduct (isIso_homEquiv_map_app_comp_relativeCupProduct)
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi (TensorHomAdjunction)

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The cup product with the class of the unit**: the composite

`𝒪_S ⊗^L Rf_*Ω^n[n] ⟶ Rf_*Ω^0 ⊗^L Rf_*Ω^n[n] ⟶ Rf_*(Ω^0 ⊗^L Ω^n[n]) ⟶ Rf_*Ω^n[n]`

of the class of `1`, the relative cup product of [Stacks, Tag 0B68] and `Rf_*` of the wedge
product. Precomposing the pairing of `t` in degree `p = 0` with the class of `g` gives this map
followed by `g · t`. -/
def unitCupWedge (n : ℤ) :
    ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O).obj
        (Stacks.Duality.derivedStructureSheafInDegree S 0).obj).obj
        ((Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f (n - 0))⟦n⟧)) ⟶
      (Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f n)⟦n⟧) :=
  (((derivedTensorProductFunctor S.toRingedSpace.sheaf).map (structureSheafClass f)).app
      ((derivedPushforward f.toLRSHom.toShHom).obj ((formsInDegreeZero f (n - 0))⟦n⟧)) ≫
    Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct f.toLRSHom.toShHom
      (formsInDegreeZero f 0) ((formsInDegreeZero f (n - 0))⟦n⟧)) ≫
    (Stacks.Duality.derivedPushforward f).map (formsDerivedWedgeShift f n 0 (n - 0) n (by ring))

/-- **The cup product with the class of the unit is an isomorphism**
`𝒪_S ⊗^L Rf_*Ω^n[n] ≅ Rf_*Ω^n[n]`:
the cup product with the class of an isomorphism `Lf^*𝒪_S ≅ K` is an isomorphism (the projection
formula at `𝒪_S`), and the wedge product with forms of degree zero is an isomorphism. -/
theorem isIso_unitCupWedge (n : ℤ) : IsIso (unitCupWedge f n) := by
  have h₁ := @isIso_homEquiv_map_app_comp_relativeCupProduct
    _ _ f.toLRSHom.toShHom _ _ _ _ (formsInDegreeZero f 0) ((formsInDegreeZero f (n - 0))⟦n⟧)
    (formsZeroUnitComparison f).hom (Iso.isIso_hom _)
  have h₂ : IsIso ((Stacks.Duality.derivedPushforward f).map
      (formsDerivedWedgeShift f n 0 (n - 0) n (by ring))) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_formsDerivedWedgeShift_zero f n (n - 0) n _)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

/-- **The pairing of `t` in degree zero on the class of `g`.** For a tensor–internal-Hom adjunction
`DY` on `D(𝒪_S)`, the map `𝒪_S ⟶ R𝓗om(Rf_*Ω^n[n], 𝒪_S)` determined by the cup product with the
class of the unit followed by `g · t` is the class of `g` followed by the map
`Rf_*Ω^0 ⟶ R𝓗om(Rf_*Ω^n[n], 𝒪_S)` determined by the pairing of `t` in degree zero. -/
theorem homEquiv_symm_unitCupWedge_comp (DY : DerivedTensorHomAdjunction S) (n : ℤ)
    (g : Γ(X, ⊤))
    (t : (Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj) :
    (DY.homEquiv _ _ _).symm (unitCupWedge f n ≫ f.formsShiftSMul n g ≫ t) =
      globalFunctionClass f g ≫
        (DY.homEquiv _ _ _).symm (f.relativeHodgePairing n 0 (n - 0) (by ring) t) := by
  have h₂ := relativeHodgePairing_formsShiftSMul f n 0 (n - 0) (by ring) g t
  have h₁ : unitCupWedge f n ≫ f.formsShiftSMul n g ≫ t =
      ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O).map
        (structureSheafClass f)).app
          ((Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f (n - 0))⟦n⟧)) ≫
        f.relativeHodgePairing n 0 (n - 0) (by ring) (f.formsShiftSMul n g ≫ t) :=
    (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) rfl))
  have h₃ : ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O).map
        (structureSheafClass f)).app
          ((Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f (n - 0))⟦n⟧)) ≫
        ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O).map
          ((Stacks.Duality.derivedPushforward f).map (f.formsInDegreeZeroSMul g 0))).app
            ((Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f (n - 0))⟦n⟧)) =
      ((derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite S.sheaf).O).map
        (globalFunctionClass f g)).app
          ((Stacks.Duality.derivedPushforward f).obj ((formsInDegreeZero f (n - 0))⟦n⟧)) :=
    (NatTrans.comp_app _ _ _).symm.trans (congrArg (fun k => NatTrans.app k _)
      ((Functor.map_comp _ _ _).symm.trans (congrArg _ (globalFunctionClass_eq f g).symm)))
  refine (congrArg (DY.homEquiv _ _ _).symm (h₁.trans ((congrArg (_ ≫ ·) h₂).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h₃))))).trans ?_
  exact TensorHomAdjunction.homEquiv_symm_map_app_comp
    DY (globalFunctionClass f g) (f.relativeHodgePairing n 0 (n - 0) (by ring) t)


variable {f} in
/-- **Every map `Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S` is a multiple of `t`** once the pairing of `t` in
degree zero is perfect: `t' = g · t` for some `g ∈ Γ(X, 𝒪_X)`. Precomposing with the isomorphism
`unitCupWedge`, the map `𝒪_S ⟶ R𝓗om(Rf_*Ω^n[n], 𝒪_S)` determined by `t'` factors through the
isomorphism `Rf_*Ω^0 ≅ R𝓗om(Rf_*Ω^n[n], 𝒪_S)` given by `t`, hence is the class of some `g`. -/
theorem exists_eq_formsShiftSMul_comp (DY : DerivedTensorHomAdjunction S) (n : ℤ)
    {t : (Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj}
    (ht : IsIso ((DY.homEquiv _ _ _).symm (f.relativeHodgePairing n 0 (n - 0) (by ring) t)))
    (t' : (Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj) :
    ∃ g : Γ(X, ⊤), t' = f.formsShiftSMul n g ≫ t := by
  obtain ⟨g, hg⟩ := (bijective_globalFunctionClass f).2
    ((DY.homEquiv _ _ _).symm (unitCupWedge f n ≫ t') ≫
      @inv _ _ _ _ ((DY.homEquiv _ _ _).symm (f.relativeHodgePairing n 0 (n - 0) (by ring) t)) ht)
  refine ⟨g, ?_⟩
  have e := (homEquiv_symm_unitCupWedge_comp f DY n g t).trans
    ((congrArg (· ≫ _) hg).trans ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (@IsIso.inv_hom_id _ _ _ _ _ ht)).trans (Category.comp_id _))))
  have := isIso_unitCupWedge f n
  exact (@cancel_epi _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (isIso_unitCupWedge f n)) _ _).1
    ((DY.homEquiv _ _ _).symm.injective e).symm

variable {f} in
/-- **The multiple `g · t` determines `g`** once the pairing of `t` in degree zero is perfect. -/
theorem formsShiftSMul_comp_injective (DY : DerivedTensorHomAdjunction S) (n : ℤ)
    {t : (Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj}
    (ht : IsIso ((DY.homEquiv _ _ _).symm (f.relativeHodgePairing n 0 (n - 0) (by ring) t))) :
    Function.Injective (fun g : Γ(X, ⊤) => f.formsShiftSMul n g ≫ t) := fun g g' h => by
  have e := ((homEquiv_symm_unitCupWedge_comp f DY n g t).symm.trans
    (congrArg (fun s => (DY.homEquiv _ _ _).symm (unitCupWedge f n ≫ s)) h)).trans
      (homEquiv_symm_unitCupWedge_comp f DY n g' t)
  exact (bijective_globalFunctionClass f).1
    ((@cancel_mono _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ ht) _ _).1 e)

/-- Multiplication by `g` and then by `h` is multiplication by `h g`. -/
theorem formsShiftSMul_comp_formsShiftSMul (n : ℤ) (g h : Γ(X, ⊤)) :
    f.formsShiftSMul n g ≫ f.formsShiftSMul n h = f.formsShiftSMul n (h * g) :=
  (Functor.map_comp _ _ _).symm.trans (congrArg (Stacks.Duality.derivedPushforward f).map
    ((Functor.map_comp _ _ _).symm.trans (congrArg (shiftFunctor _ n).map
      ((DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
        (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map_comp _ _).symm.trans
          (congrArg (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map
            (Stacks.Cohomology.InvertibleDerived.smulHom_comp (X := X.toRingedSpace) g h _))))))))

/-- Multiplication by `1` is the identity. -/
theorem formsShiftSMul_one (n : ℤ) : f.formsShiftSMul n 1 = 𝟙 _ :=
  (congrArg (Stacks.Duality.derivedPushforward f).map ((congrArg (shiftFunctor _ n).map
    ((congrArg DerivedCategory.Q.map ((congrArg
      (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map
        (AlgebraicGeometry.SheafOfModules.smulHom_one _)).trans
      ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map_id _))).trans
      (DerivedCategory.Q.map_id _))).trans (CategoryTheory.Functor.map_id _ _))).trans
    (CategoryTheory.Functor.map_id _ _)

variable {f} in
/-- **Two maps with perfect pairings in degree zero differ by a unit**: if the pairings of `t` and
`t'` in degree zero are perfect then `t' = u · t` for a unit `u` of `Γ(X, 𝒪_X)`. -/
theorem exists_units_eq_formsShiftSMul_comp (DY : DerivedTensorHomAdjunction S) (n : ℤ)
    {t t' : (Stacks.Duality.derivedPushforward f).obj ((f.formsInDegreeZero n)⟦n⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree S 0).obj}
    (ht : IsPerfectDerivedPairing DY (f.relativeHodgePairing n 0 (n - 0) (by ring) t))
    (ht' : IsPerfectDerivedPairing DY (f.relativeHodgePairing n 0 (n - 0) (by ring) t')) :
    ∃ u : (Γ(X, ⊤))ˣ, t' = f.formsShiftSMul n u ≫ t := by
  obtain ⟨g, hg⟩ := exists_eq_formsShiftSMul_comp DY n ht.2.2 t'
  obtain ⟨h, hh⟩ := exists_eq_formsShiftSMul_comp DY n ht'.2.2 t
  have e : f.formsShiftSMul n (g * h) ≫ t = f.formsShiftSMul n 1 ≫ t :=
    ((congrArg (· ≫ t) (f.formsShiftSMul_comp_formsShiftSMul n h g).symm).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hg.symm).trans hh.symm))).trans
      ((Category.id_comp t).symm.trans (congrArg (· ≫ t) (f.formsShiftSMul_one n).symm))
  have hgh : g * h = 1 := formsShiftSMul_comp_injective DY n ht.2.2 e
  exact ⟨⟨g, h, hgh, (mul_comm h g).trans hgh⟩, hg⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.RelativeDualitySituation

/-- **Uniqueness in [Stacks, Tag 0G8I]**: two maps `t, t' : Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S` with the
property of that lemma differ by multiplication by a unit of `Γ(X, 𝒪_X)`. -/
theorem IsRelativePoincareTrace.exists_units {D : RelativeDualitySituation.{u}}
    {t t' : (Stacks.Duality.derivedPushforward D.f).obj ((D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧) ⟶
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj}
    (ht : D.IsRelativePoincareTrace t) (ht' : D.IsRelativePoincareTrace t') :
    ∃ u : (Γ(D.X, ⊤))ˣ, t' = D.f.formsShiftSMul D.n u ≫ t :=
  Scheme.Hom.exists_units_eq_formsShiftSMul_comp _ D.n (ht 0) (ht' 0)

end AlgebraicGeometry.RelativeDualitySituation

end
