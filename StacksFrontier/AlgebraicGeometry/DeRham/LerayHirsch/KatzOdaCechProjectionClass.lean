module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechProjection
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechCup
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.CechClassLeray
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DeRhamComparisonAdjoint
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationEdge

/-!
# The Čech class of the projection of a cocycle to forms relative to `Y`

For `f : X ⟶ Y` smooth and `g : Y ⟶ S` with `Y`, `S` affine, and a finite covering `U` of `X` by
affine opens with affine intersections, the class in `H^*_{dR}(X/Y)` of the image of a cocycle `x`
of `Tot(Č(U, Ω^•_{X/S}))` under the projection of forms (`Stacks.KatzOda.Cech.projHom`) is the
de Rham pullback along the square `(𝟙 X, g)` ([Stacks, Tag 0FL6]) of the class of `x`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject sectionsPresheafFunctor)
open Stacks.Cech.LinearCupProduct (PresheafModules totalCechComplexFunctor)

universe u

namespace Stacks.CategoryTheory.CechComplex

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance] totIndexFintype

variable {C : Type u} [Category.{u} C] [HasFiniteProducts C] {ι : Type u} (W : ι → C)
  {R : Type u} [CommRing R]

/-- **The comparison of the two concrete models of a total Čech complex**: going to the
library's total complex through one identification of the terms and back through another is the
map of concrete total complexes induced by a map of coefficients compatible with both. -/
theorem totalTo_totalFrom_apply {K : CochainComplex (PresheafModules.{u} C R) ℤ}
    {P P' : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ} (e : ∀ b : ℕ, K.X (b : ℤ) ≅ P.X b)
    (e' : ∀ b : ℕ, K.X (b : ℤ) ≅ P'.X b) (Φ : P ⟶ P')
    (hΦ : ∀ b : ℕ, (e b).hom ≫ Φ.f b = (e' b).hom) (n : ℤ) (x : TotX W P n) :
    (totalTo W K P' e' n).hom ((totalFrom W K P e n).hom x) = totMap Φ n x := by
  have h := totalTo_naturality W e e' (𝟙 K) Φ (fun b => by
    rw [HomologicalComplex.id_f, Category.id_comp]
    exact (hΦ b).symm) n
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, Category.id_comp] at h
  refine (ConcreteCategory.congr_hom h ((totalFrom W K P e n).hom x)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  have hx : (totalTo W K P e n).hom ((totalFrom W K P e n).hom x) = x :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (totalFrom_totalTo W K P e n)) x
  exact congrArg ((cechTotMap W P Φ).f n).hom hx

end Stacks.CategoryTheory.CechComplex

namespace Stacks.Cech.RingChange

open AlgebraicGeometry.SheafOfModules (baseRingedSpace)

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance] totIndexFintype

/-- `ecl`, read in the elementwise total complexes. -/
theorem cechNatIso_hom_ecl {X : AlgebraicGeometry.RingedSpace.{u, u}}
    {A A' : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    (h : baseRingedSpace A ⟶ baseRingedSpace A') (hh : h.hom.base = 𝟙 X.carrier)
    {ι : Type u} (U : ι → Opens X.carrier) (hU : ⊤ = ⨆ i, U i)
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).X n) :
    (((cechNatIso A U hU M hM).hom.f n).hom (ecl h hh U hU M hM n z) : TotX _ _ n) =
      totMap (pushSectionsIso h hh M).hom n
        (((cechNatIso A' U hU (pushC h M) (isZero_pushC_X h M hM)).hom.f n).hom z) :=
  (congrArg ((cechNatIso A U hU M hM).hom.f n).hom (ecl_apply h hh U hU M hM n z)).trans
    (iso_inv_hom_f_apply _ (cechNatIso A U hU M hM) n _)

end Stacks.Cech.RingChange

namespace AlgebraicGeometry.DeRhamKatzOdaCech

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance] totIndexFintype

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- The slice de Rham complex, read as the sections of the de Rham complex in nonnegative
degrees. -/
def sliceToNat : sliceDeRhamComplex p ⟶
    Stacks.Cech.RingChange.natSections (baseSheaf p) (deRhamPlus p).obj where
  f b := (sliceExtendXIso p b).inv
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    exact (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 (sliceExtendXIso_comm p i)).trans
      (Category.assoc _ _ _))

/-- The de Rham complex `(deRhamPlus p).obj` vanishes in negative degrees. -/
theorem isZero_deRhamPlus_X (a : ℤ) (ha : a < 0) : IsZero ((deRhamPlus p).obj.X a) :=
  (deRhamPlus p).obj.isZero_of_isStrictlyGE 0 a ha

variable {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)

/-- **The two comparisons of the elementwise total Čech complex of the de Rham complex with the
library's agree**, up to the identification of the slice de Rham complex with its sections. -/
theorem cechNatIso_hom_cechIso (n : ℤ) (z : TotX U p.sectionsDeRhamComplex n) :
    ((Stacks.Cech.RingChange.cechNatIso (baseSheaf p) U hU (deRhamPlus p).obj
        (isZero_deRhamPlus_X p)).hom.f n).hom (((cechIso p U hU).hom.f n).hom z) =
      totMap (sliceToNat p) n (sliceTot p U hU n z) := by
  let := Stacks.Cech.ModuleCupProduct.sectionCommRing (baseSheaf p) ⊤
  change (totalTo (coverObject U hU) (Stacks.Cech.RingChange.sectionsK (baseSheaf p)
      (deRhamPlus p).obj) (Stacks.Cech.RingChange.natSections (baseSheaf p) (deRhamPlus p).obj)
      (Stacks.Cech.RingChange.natSectionsXIso (baseSheaf p) (deRhamPlus p).obj) n).hom
    ((totalFrom (R := SectionRing (Stacks.SheafOfModules.Tensor.ringSheaf (baseSheaf p)) ⊤)
        (coverObject U hU)
        (sliceDeRhamComplexInt p) (sliceDeRhamComplex p) (sliceExtendXIso p) n).hom
      (sliceTot p U hU n z)) = _
  exact totalTo_totalFrom_apply (coverObject U hU) (sliceExtendXIso p)
    (Stacks.Cech.RingChange.natSectionsXIso (baseSheaf p) (deRhamPlus p).obj) (sliceToNat p)
    (fun b => (sliceExtendXIso p b).hom_inv_id) n _


section RingChange

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The change of base rings `(X, f⁻¹𝒪_Y) ⟶ (X, (f ≫ g)⁻¹𝒪_S)` of the square `(𝟙 X, g)`, the
identity on the underlying space. -/
abbrev relBaseMap : AlgebraicGeometry.SheafOfModules.baseRingedSpace (baseSheaf f) ⟶
    AlgebraicGeometry.SheafOfModules.baseRingedSpace (baseSheaf (f ≫ g)) :=
  Stacks.DeRhamBaseChange.inverseImageBaseMap (𝟙 X) f (f ≫ g) g (Category.id_comp _)

/-- The change of base rings `relBaseMap f g` is the identity on the underlying space of `X`. -/
theorem relBaseMap_base : (relBaseMap f g).hom.base = 𝟙 X.carrier := rfl

/-- The canonical map `Ω^•_{X/S} ⟶ Ω^•_{X/Y}` of the square `(𝟙 X, g)`, as a map of complexes
of `(f ≫ g)⁻¹𝒪_S`-modules into the direct image along the change of base rings. -/
def relPushforwardInt : (deRhamPlus (f ≫ g)).obj ⟶
    Stacks.Cech.RingChange.pushC (relBaseMap f g) (deRhamPlus f).obj :=
  Stacks.DeRhamBaseChange.deRhamPushforwardInt (𝟙 X) f (f ≫ g) g (Category.id_comp _)

/-- **The canonical map of de Rham complexes of the square `(𝟙 X, g)`, on sections**, is the map
`relSections` of forms. -/
theorem deRhamPushforwardChain_f_apply (a : ℕ) (V : X.Opens)
    (y : Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ), V)) :
    ((Stacks.DeRhamBaseChange.deRhamPushforwardChain (𝟙 X) f (f ≫ g) g
        (Category.id_comp _)).f a).val.app (op V) y = relSections f g a V y :=
  (Stacks.DeRhamBaseChange.pushforwardSquareIso_inv_val_app (𝟙 X) f (f ≫ g) g
    (Category.id_comp _) (Scheme.Hom.relativeDifferentialForms f (a : ℤ)) (op V)
    ((Stacks.DeRhamBaseChange.formsAdjoint (𝟙 X) f (f ≫ g) g (Category.id_comp _) a).val.app
      (op V) y)).trans
    (congrArg (fun φ => φ.val.app (op V) y)
      (Stacks.DeRhamBaseChange.formsAdjoint_eq_deRhamFormsPushforwardHom (𝟙 X) f (f ≫ g) g
        (Category.id_comp _) a))


/-- `relSections` commutes with restriction. -/
theorem relSections_restrict (a : ℕ) {V V' : X.Opens} (i : V' ⟶ V)
    (y : Γ(Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ), V)) :
    (Scheme.Hom.relativeDifferentialForms f (a : ℤ)).presheaf.map i.op (relSections f g a V y) =
      relSections f g a V' ((Scheme.Hom.relativeDifferentialForms (f ≫ g) (a : ℤ)).presheaf.map
        i.op y) :=
  (PresheafOfModules.naturality_apply ((Scheme.Hom.deRhamFormsPushforwardHom (𝟙 X) (f ≫ g) f g
    (Category.id_comp _)).app (a : ℤ)).val i.op y).symm

/-- **The canonical map of de Rham complexes, read on the sections over an object of the slice**:
through the identifications of the slice de Rham complexes with the sections and of the sections
of a direct image along the change of base rings with the sections, it is `relSections`. -/
theorem slice_relPushforwardInt_apply (a : ℕ) (W : Over (⊤ : X.Opens))
    (z : ((sliceDeRhamComplex (f ≫ g)).X a).obj (op W)) :
    (((Stacks.Cech.RingChange.pushSectionsIso (relBaseMap f g) (relBaseMap_base f g)
        (deRhamPlus f).obj).hom.f a).app (op W)).hom
      ((((Stacks.Cech.RingChange.natSectionsMap (baseSheaf (f ≫ g))
          (relPushforwardInt f g)).f a).app (op W)).hom
        ((((sliceToNat (f ≫ g)).f a).app (op W)).hom z)) =
      (((sliceToNat f).f a).app (op W)).hom (relSections f g a W.left z) := by
  change (((deRhamPlus f).obj.X a).val.map (eqToHom (Stacks.Cech.RingChange.map_obj_eq
      (relBaseMap f g) (relBaseMap_base f g) W.left).symm).op).hom
    ((((relPushforwardInt f g).f a).val.app (op W.left)).hom
      ((((sliceExtendXIso (f ≫ g) a).inv).app (op W)).hom z)) =
    ((((sliceExtendXIso f a).inv).app (op W)).hom (relSections f g a W.left z))
  let E' := (Scheme.Hom.deRhamComplex (f ≫ g)).extendXIso ComplexShape.embeddingUpNat (i := a)
    (i' := (a : ℤ)) rfl
  let E := (Scheme.Hom.deRhamComplex f).extendXIso ComplexShape.embeddingUpNat (i := a)
    (i' := (a : ℤ)) rfl
  change (((deRhamPlus f).obj.X a).val.map (eqToHom (Stacks.Cech.RingChange.map_obj_eq
      (relBaseMap f g) (relBaseMap_base f g) W.left).symm).op).hom
    ((((relPushforwardInt f g).f a).val.app (op W.left)).hom
      ((E'.inv.val.app (op W.left)).hom z)) =
    (E.inv.val.app (op W.left)).hom (relSections f g a W.left z)
  have hI := congrArg (fun φ => (φ.val.app (op W.left)).hom ((E'.inv.val.app (op W.left)).hom z))
    (Stacks.DeRhamBaseChange.deRhamPushforwardInt_f (𝟙 X) f (f ≫ g) g (Category.id_comp _) a)
  have hc : (E'.hom.val.app (op W.left)).hom ((E'.inv.val.app (op W.left)).hom z) = z :=
    congrArg (fun φ => (φ.val.app (op W.left)).hom z) E'.inv_hom_id
  refine (congrArg (((deRhamPlus f).obj.X a).val.map (eqToHom (Stacks.Cech.RingChange.map_obj_eq
      (relBaseMap f g) (relBaseMap_base f g) W.left).symm).op).hom hI).trans ?_
  change (((deRhamPlus f).obj.X a).val.map (eqToHom (Stacks.Cech.RingChange.map_obj_eq
      (relBaseMap f g) (relBaseMap_base f g) W.left).symm).op).hom
    ((E.inv.val.app (op W.left)).hom
      ((((Stacks.DeRhamBaseChange.deRhamPushforwardChain (𝟙 X) f (f ≫ g) g
        (Category.id_comp _)).f a).val.app (op W.left)).hom
        ((E'.hom.val.app (op W.left)).hom ((E'.inv.val.app (op W.left)).hom z)))) = _
  rw [hc]
  refine (congrArg (fun r => (((deRhamPlus f).obj.X a).val.map (eqToHom
    (Stacks.Cech.RingChange.map_obj_eq (relBaseMap f g) (relBaseMap_base f g) W.left).symm).op).hom
      ((E.inv.val.app (op W.left)).hom r)) (deRhamPushforwardChain_f_apply f g a W.left z)).trans ?_
  refine (PresheafOfModules.naturality_apply E.inv.val (eqToHom (Stacks.Cech.RingChange.map_obj_eq
      (relBaseMap f g) (relBaseMap_base f g) W.left).symm).op _).symm.trans ?_
  exact congrArg (E.inv.val.app (op W.left)).hom
    (Stacks.Cech.RingChange.presheafOfModules_map_self _ _ _)


variable [IsAffine Y] [IsAffine S] [Smooth f] {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) [Fintype ι] [DecidableEq ι]

/-- The projection of a cochain to forms relative to `Y`, read on the slice, is `relSections`
componentwise. -/
theorem sliceTot_projHom (n : ℤ) (x : TotX U (f ≫ g).sectionsDeRhamComplex n)
    (i : TotIndex n) (t : Fin (i.1.1 + 1) → ι) :
    sliceTot f U hU n ((Stacks.KatzOda.Cech.projHom (chartData f g U haff)
        (formsDataTotal f g U haff) (formsDataRel f g U haff)).totAddHom n x) i t =
      relSections f g i.1.2 (inter (coverObject U hU) t).left (sliceTot (f ≫ g) U hU n x i t) := by
  change (Scheme.Hom.relativeDifferentialForms f (i.1.2 : ℤ)).presheaf.map
      (homOfLE (le_of_eq (interOver_left_eq U (fun _ => le_top) t))).op
      (Stacks.KatzOda.Cech.projAt (chartData f g U haff) (formsDataTotal f g U haff)
        (formsDataRel f g U haff) i.1.2 t (x i t)) = _
  rw [projAt_eq_relSections]
  exact relSections_restrict f g i.1.2 _ _

/-- The canonical map of de Rham complexes, read in the elementwise total complexes. -/
theorem cechNatIso_hom_cech_relPushforwardInt (n : ℤ)
    (x : TotX U (f ≫ g).sectionsDeRhamComplex n) :
    (((Stacks.Cech.RingChange.cechNatIso (baseSheaf (f ≫ g)) U hU
        (Stacks.Cech.RingChange.pushC (relBaseMap f g) (deRhamPlus f).obj)
        (Stacks.Cech.RingChange.isZero_pushC_X (relBaseMap f g) (deRhamPlus f).obj
          (isZero_deRhamPlus_X f))).hom.f n).hom
        ((((Stacks.Cech.Hypercohomology.cech (baseSheaf (f ≫ g)) U hU).map
          (relPushforwardInt f g)).f n).hom (((cechIso (f ≫ g) U hU).hom.f n).hom x))) =
      totMap (Stacks.Cech.RingChange.natSectionsMap (baseSheaf (f ≫ g)) (relPushforwardInt f g)) n
        (totMap (sliceToNat (f ≫ g)) n (sliceTot (f ≫ g) U hU n x)) := by
  have h1 := Stacks.Cech.RingChange.cechNatIso_hom_f_naturality_apply (O := baseSheaf (f ≫ g))
    (M := (deRhamPlus (f ≫ g)).obj)
    (M' := Stacks.Cech.RingChange.pushC (relBaseMap f g) (deRhamPlus f).obj) U hU
    (isZero_deRhamPlus_X (f ≫ g))
    (Stacks.Cech.RingChange.isZero_pushC_X (relBaseMap f g) (deRhamPlus f).obj
      (isZero_deRhamPlus_X f)) (relPushforwardInt f g) n (((cechIso (f ≫ g) U hU).hom.f n).hom x)
  convert h1.trans (congrArg _ (cechNatIso_hom_cechIso (f ≫ g) U hU n x)) using 2

/-- On the elementwise total complexes, the canonical map of de Rham complexes followed by the
identification of the sections of the direct image is the projection of forms
`Stacks.KatzOda.Cech.projHom`, read on the slices. -/
theorem totMap_pushSectionsIso_relPushforwardInt (n : ℤ)
    (x : TotX U (f ≫ g).sectionsDeRhamComplex n) :
    (totMap (Stacks.Cech.RingChange.pushSectionsIso (relBaseMap f g) (relBaseMap_base f g)
        (deRhamPlus f).obj).hom n
      (totMap (Stacks.Cech.RingChange.natSectionsMap (baseSheaf (f ≫ g)) (relPushforwardInt f g)) n
        (totMap (sliceToNat (f ≫ g)) n (sliceTot (f ≫ g) U hU n x))) : TotX _ _ n) =
      totMap (sliceToNat f) n (sliceTot f U hU n ((Stacks.KatzOda.Cech.projHom
        (chartData f g U haff) (formsDataTotal f g U haff)
        (formsDataRel f g U haff)).totAddHom n x)) := by
  funext i t
  refine (slice_relPushforwardInt_apply f g i.1.2 (inter (coverObject U hU) t)
    (sliceTot (f ≫ g) U hU n x i t)).trans ?_
  exact congrArg (((sliceToNat f).f i.1.2).app (op (inter (coverObject U hU) t))).hom
    (sliceTot_projHom f g U hU haff n x i t).symm

/-- The comparison `ecl`, applied to the image of a cochain under the canonical map of de Rham
complexes and read in the elementwise total complexes, is the image of the cochain read on the
slice under the canonical map of de Rham complexes and the identification of the sections. -/
theorem cechNatIso_hom_ecl_cech (n : ℤ) (x : TotX U (f ≫ g).sectionsDeRhamComplex n) :
    (((Stacks.Cech.RingChange.cechNatIso (baseSheaf f) U hU (deRhamPlus f).obj
        (isZero_deRhamPlus_X f)).hom.f n).hom
      (Stacks.Cech.RingChange.ecl (relBaseMap f g) (relBaseMap_base f g) U hU (deRhamPlus f).obj
        (isZero_deRhamPlus_X f) n
        ((((Stacks.Cech.Hypercohomology.cech (baseSheaf (f ≫ g)) U hU).map
          (relPushforwardInt f g)).f n).hom (((cechIso (f ≫ g) U hU).hom.f n).hom x)))) =
      totMap (Stacks.Cech.RingChange.pushSectionsIso (relBaseMap f g) (relBaseMap_base f g)
        (deRhamPlus f).obj).hom n
      (totMap (Stacks.Cech.RingChange.natSectionsMap (baseSheaf (f ≫ g)) (relPushforwardInt f g)) n
        (totMap (sliceToNat (f ≫ g)) n (sliceTot (f ≫ g) U hU n x))) := by
  have e1 := Stacks.Cech.RingChange.cechNatIso_hom_ecl (relBaseMap f g) (relBaseMap_base f g) U hU
    (deRhamPlus f).obj (isZero_deRhamPlus_X f) n
    ((((Stacks.Cech.Hypercohomology.cech (baseSheaf (f ≫ g)) U hU).map
      (relPushforwardInt f g)).f n).hom (((cechIso (f ≫ g) U hU).hom.f n).hom x))
  have e2 := congrArg (totMap (Stacks.Cech.RingChange.pushSectionsIso (relBaseMap f g)
    (relBaseMap_base f g) (deRhamPlus f).obj).hom n)
    (cechNatIso_hom_cech_relPushforwardInt f g U hU n x)
  convert e1.trans e2 using 2

/-- **The comparison `ecl` of the total Čech complexes across the change of base rings, on the
image of the canonical map of de Rham complexes**, is the projection of forms
`Stacks.KatzOda.Cech.projHom`, read through the comparisons `cechIso`. -/
theorem ecl_cech_relPushforwardInt (n : ℤ) (x : TotX U (f ≫ g).sectionsDeRhamComplex n) :
    Stacks.Cech.RingChange.ecl (relBaseMap f g) (relBaseMap_base f g) U hU (deRhamPlus f).obj
        (isZero_deRhamPlus_X f) n
        ((((Stacks.Cech.Hypercohomology.cech (baseSheaf (f ≫ g)) U hU).map
          (relPushforwardInt f g)).f n).hom (((cechIso (f ≫ g) U hU).hom.f n).hom x)) =
      ((cechIso f U hU).hom.f n).hom ((Stacks.KatzOda.Cech.projHom (chartData f g U haff)
        (formsDataTotal f g U haff) (formsDataRel f g U haff)).totAddHom n x) := by
  let C := Stacks.Cech.RingChange.cechNatIso (baseSheaf f) U hU (deRhamPlus f).obj
    (isZero_deRhamPlus_X f)
  have inj : Function.Injective (C.hom.f n).hom := fun a b hab =>
    (Stacks.Cech.RingChange.iso_hom_inv_f_apply _ C n a).symm.trans
      ((congrArg (C.inv.f n).hom hab).trans (Stacks.Cech.RingChange.iso_hom_inv_f_apply _ C n b))
  apply inj
  have e := (cechNatIso_hom_ecl_cech f g U hU n x).trans
    ((totMap_pushSectionsIso_relPushforwardInt f g U hU haff n x).trans
      (cechNatIso_hom_cechIso f U hU n _).symm)
  convert e using 2

end RingChange


section Classes

open Stacks.Cech.Hypercohomology (cocycleClass toMor cechClass)
open Stacks.Cohomology.DerivedSectionsLeray Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- A cocycle of the elementwise total Čech complex of the de Rham complex of `p` is carried by
`cechIso` to a cocycle of the total Čech complex of `(deRhamPlus p).obj`. -/
theorem Θ_cocycle' {T : Scheme.{u}} (p : X ⟶ T) {ι : Type u} (U : ι → X.Opens)
    (hU : ⊤ = ⨆ i, U i) (n : ℤ) (z : TotX U p.sectionsDeRhamComplex n)
    (hz : ((cechTot U p.sectionsDeRhamComplex).d n (n + 1)).hom z = 0) :
    (((Stacks.Cech.Hypercohomology.cech (baseSheaf p) U hU).obj (deRhamPlus p).obj).d n
      (n + 1)).hom (((cechIso p U hU).hom.f n).hom z) = 0 :=
  Θ_cocycle p U hU n z hz

/-- **The class of a cocycle in `H^n_{dR}(X/T)` is its Čech class**, read through `sideA`. -/
theorem classMap_cocycleClass_eq_sideA {T : Scheme.{u}} (p : X ⟶ T) {ι : Type u}
    (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i) (n : ℤ) (z : TotX U p.sectionsDeRhamComplex n)
    (hz : ((cechTot U p.sectionsDeRhamComplex).d n (n + 1)).hom z = 0) :
    (classMap p U hU n).hom ((cocycleClass n (toMor z) (toMor_comp_d_eq_zero _ hz)).hom 1) =
      (Stacks.Cech.RingChange.sideA (A := baseSheaf p) U hU (deRhamPlus p) n).hom
        (Stacks.Cech.RingChange.cls _ n (((cechIso p U hU).hom.f n).hom z)
          (Θ_cocycle' p U hU n z hz)) :=
  (classMap_cocycleClass p U hU n z hz).trans rfl


variable [IsAffine Y] [IsAffine S] [Smooth f] {ι : Type u} (U : ι → X.Opens) (hU : ⊤ = ⨆ i, U i)
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) [Fintype ι] [DecidableEq ι]

/-- **The Čech class over `f⁻¹𝒪_Y` of the projection of a cocycle** is the class over
`(f ≫ g)⁻¹𝒪_S` of the image of the cocycle under the canonical map of de Rham complexes, carried
by `h_* ⟶ Rh_*` and the Leray identification. -/
theorem sideA_projHom_eq_sideA' (n : ℤ) (x : TotX U (f ≫ g).sectionsDeRhamComplex n)
    (hz : (((Stacks.Cech.Hypercohomology.cech (baseSheaf (f ≫ g)) U hU).obj
      (Stacks.Cech.RingChange.pushC (relBaseMap f g) (deRhamPlus f).obj)).d n (n + 1)).hom
      ((((Stacks.Cech.Hypercohomology.cech (baseSheaf (f ≫ g)) U hU).map
        (relPushforwardInt f g)).f n).hom (((cechIso (f ≫ g) U hU).hom.f n).hom x)) = 0)
    (hy : (((Stacks.Cech.Hypercohomology.cech (baseSheaf f) U hU).obj (deRhamPlus f).obj).d n
      (n + 1)).hom (((cechIso f U hU).hom.f n).hom ((Stacks.KatzOda.Cech.projHom
        (chartData f g U haff) (formsDataTotal f g U haff) (formsDataRel f g U haff)).totAddHom n
          x)) = 0) :
    (Stacks.Cech.RingChange.sideA (A := baseSheaf f) U hU (deRhamPlus f) n).hom
        (Stacks.Cech.RingChange.cls _ n _ hy) =
      (Stacks.Cech.RingChange.sideA' (relBaseMap f g) U hU (deRhamPlus f) inferInstance n).hom
        (Stacks.Cech.RingChange.cls _ n _ hz) := by
  have e1 := Stacks.Cech.RingChange.sideA'_cls (relBaseMap f g) (relBaseMap_base f g) U hU
    (deRhamPlus f) inferInstance n _ hz
  refine Eq.trans ?_ e1.symm
  have e2 := congrArg (Stacks.Cech.RingChange.sideA (A := baseSheaf f) U hU (deRhamPlus f) n).hom
    (Stacks.Cech.RingChange.cls_congr
      ((Stacks.Cech.Hypercohomology.cech (baseSheaf f) U hU).obj (deRhamPlus f).obj) n
      (ecl_cech_relPushforwardInt f g U hU haff n x).symm hy
      (Stacks.Cech.RingChange.ecl_cocycle (relBaseMap f g) (relBaseMap_base f g) U hU
        (deRhamPlus f).obj (Stacks.Cech.RingChange.isZero_of_isStrictlyGE_zero inferInstance)
        n _ hz))
  convert e2 using 2

end Classes

end AlgebraicGeometry.DeRhamKatzOdaCech

end
