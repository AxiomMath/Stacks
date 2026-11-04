module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.KatzOdaCechProjectionClass
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The class of the projection of a cocycle is the de Rham pullback of its class

For `f : X ⟶ Y` smooth and `g : Y ⟶ S` with `Y`, `S` affine, and a finite covering `U` of `X` by
affine opens with affine intersections, the class in `H^n_{dR}(X/Y)` of the image of a cocycle `x`
of `Tot(Č(U, Ω^•_{X/S}))` under the projection of forms (`Stacks.KatzOda.Cech.projHom`) is the de
Rham pullback ([Stacks, Tag 0FL6]) along the square `(𝟙 X, g)` of the class of `x` in
`H^n_{dR}(X/S)`, read in the module realization of de Rham cohomology through the comparison of
the two realizations ([Stacks, Tag 01F1]).

## Main results

* `AlgebraicGeometry.DeRhamKatzOdaCech.classMap_projHom`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.Hypercohomology (cocycleClass toMor)
open Stacks.Cohomology.DerivedSectionsLeray Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.DeRhamKatzOdaCech

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance] totIndexFintype

/-- A functor applied to a composite, then evaluated on an element. -/
theorem map_map_comp_apply {C D : Type*} [Category* C] [Category* D] {R : Type u} [Ring R]
    (F : C ⥤ D) (H : D ⥤ ModuleCat.{u} R) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c)
    (z : H.obj (F.obj a)) :
    (H.map (F.map (φ ≫ ψ))).hom z = (H.map (F.map ψ)).hom ((H.map (F.map φ)).hom z) := by
  rw [F.map_comp, H.map_comp]
  rfl

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) {ι : Type u} (U : ι → X.Opens)
  (hU : ⊤ = ⨆ i, U i)

/-- The canonical map `Ω^•_{X/S} ⟶ Ω^•_{X/Y}` of the square `(𝟙 X, g)`, as a map of bounded below
complexes of `(f ≫ g)⁻¹𝒪_S`-modules into the direct image along the change of base rings. -/
def relPushforwardPlus : deRhamPlus (f ≫ g) ⟶
    Stacks.Cech.RingChange.pushPlus (relBaseMap f g) (deRhamPlus f) inferInstance :=
  ObjectProperty.homMk (relPushforwardInt f g)

/-- The image of a cocycle under the canonical map of de Rham complexes of the square `(𝟙 X, g)`,
on total Čech complexes over `(f ≫ g)⁻¹𝒪_S`, is a cocycle. -/
theorem cech_relPushforwardInt_cocycle (n : ℤ) (x : TotX U (f ≫ g).sectionsDeRhamComplex n)
    (hx : ((cechTot U (f ≫ g).sectionsDeRhamComplex).d n (n + 1)).hom x = 0) :
    (((Stacks.Cech.Hypercohomology.cech (baseSheaf (f ≫ g)) U hU).obj
      (Stacks.Cech.RingChange.pushC (relBaseMap f g) (deRhamPlus f).obj)).d n (n + 1)).hom
      ((((Stacks.Cech.Hypercohomology.cech (baseSheaf (f ≫ g)) U hU).map
        (relPushforwardInt f g)).f n).hom (((cechIso (f ≫ g) U hU).hom.f n).hom x)) = 0 :=
  Stacks.Cech.RingChange.d_f_apply_eq_zero _
    ((Stacks.Cech.Hypercohomology.cech (baseSheaf (f ≫ g)) U hU).map (relPushforwardInt f g)) n _
    (Θ_cocycle' (f ≫ g) U hU n x hx)

variable [IsAffine Y] [IsAffine S] [Smooth f]
  (haff : ∀ {m : ℕ} (t : Fin (m + 1) → ι), IsAffineOpen (inter U t)) [Fintype ι] [DecidableEq ι]

/-- `Ω^•_{X/S} ⟶ Ω^•_{X/Y}` on Čech classes, before identification with the de Rham pullback:
the class of the image of a cocycle under the canonical map of de Rham complexes, carried by
`h_* ⟶ Rh_*` and the Leray identification, is the class of its projection. -/
theorem classMap_projHom_eq_lerayCohomologyIso (n : ℤ) (x : TotX U (f ≫ g).sectionsDeRhamComplex n)
    (hx : ((cechTot U (f ≫ g).sectionsDeRhamComplex).d n (n + 1)).hom x = 0)
    (hpx : ((cechTot U f.sectionsDeRhamComplex).d n (n + 1)).hom ((Stacks.KatzOda.Cech.projHom
        (chartData f g U haff) (formsDataTotal f g U haff)
          (formsDataRel f g U haff)).totAddHom n x) = 0) :
    (classMap f U hU n).hom ((cocycleClass n (toMor ((Stacks.KatzOda.Cech.projHom
        (chartData f g U haff) (formsDataTotal f g U haff)
          (formsDataRel f g U haff)).totAddHom n x))
        (toMor_comp_d_eq_zero _ hpx)).hom 1) =
      (lerayCohomologyIso (relBaseMap f g) (DerivedCategory.Q.obj (deRhamPlus f).obj) n).hom
        (((DerivedCategory.homologyFunctor _ n).map
          ((baseSections (AlgebraicGeometry.SheafOfModules.baseRingedSpace (baseSheaf (f ≫ g)))).map
            (pushforwardComparisonQ (relBaseMap f g) (deRhamPlus f).obj))).hom
          (((DerivedCategory.homologyFunctor _ n).map
            ((baseSections (AlgebraicGeometry.SheafOfModules.baseRingedSpace
              (baseSheaf (f ≫ g)))).map (DerivedCategory.Q.map (relPushforwardInt f g)))).hom
            ((classMap (f ≫ g) U hU n).hom ((cocycleClass n (toMor x)
              (toMor_comp_d_eq_zero _ hx)).hom 1)))) := by
  have hz := cech_relPushforwardInt_cocycle f g U hU n x hx
  have e3 := Stacks.Cech.RingChange.sideA_cls_naturality (A := baseSheaf (f ≫ g)) U hU
    (M := deRhamPlus (f ≫ g))
    (I := Stacks.Cech.RingChange.pushPlus (relBaseMap f g) (deRhamPlus f) inferInstance)
    (relPushforwardPlus f g) n _ (Θ_cocycle' (f ≫ g) U hU n x hx) hz
  have e4 := classMap_cocycleClass_eq_sideA (f ≫ g) U hU n x hx
  refine (classMap_cocycleClass_eq_sideA f U hU n _ hpx).trans
    ((sideA_projHom_eq_sideA' f g U hU haff n x hz (Θ_cocycle' f U hU n _ hpx)).trans ?_)
  simp only [e4]
  refine Eq.trans ?_ (congrArg (fun c => (lerayCohomologyIso (relBaseMap f g)
    (DerivedCategory.Q.obj (deRhamPlus f).obj) n).hom
      (((DerivedCategory.homologyFunctor _ n).map
        ((baseSections (AlgebraicGeometry.SheafOfModules.baseRingedSpace (baseSheaf (f ≫ g)))).map
          (pushforwardComparisonQ (relBaseMap f g) (deRhamPlus f).obj))).hom c)) e3).symm
  exact Stacks.Cech.RingChange.sideA'_apply (relBaseMap f g) U hU (deRhamPlus f) inferInstance n _

/-- **The class of the projection of a cocycle is the de Rham pullback of its class**: for a
cocycle `x` of `Tot(Č(U, Ω^•_{X/S}))`, the class in `H^n_{dR}(X/Y)` of its image under the
projection of forms `Ω^•_{X/S} ⟶ Ω^•_{X/Y}` is the de Rham pullback along the square `(𝟙 X, g)`
([Stacks, Tag 0FL6]) of its class in `H^n_{dR}(X/S)`, read in the module realization through the
comparison of the two realizations ([Stacks, Tag 01F1]). -/
theorem classMap_projHom (n : ℤ) (x : TotX U (f ≫ g).sectionsDeRhamComplex n)
    (hx : ((cechTot U (f ≫ g).sectionsDeRhamComplex).d n (n + 1)).hom x = 0)
    (hpx : ((cechTot U f.sectionsDeRhamComplex).d n (n + 1)).hom
      ((Stacks.KatzOda.Cech.projHom (chartData f g U haff) (formsDataTotal f g U haff)
          (formsDataRel f g U haff)).totAddHom n x) = 0) :
    (classMap f U hU n).hom ((cocycleClass n (toMor ((Stacks.KatzOda.Cech.projHom
        (chartData f g U haff) (formsDataTotal f g U haff)
          (formsDataRel f g U haff)).totAddHom n x))
        (toMor_comp_d_eq_zero _ hpx)).hom 1) =
      (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology (Scheme.Hom.deRhamAlgebras f)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) n).hom.hom
        ((Scheme.Hom.deRhamCohomologyPullback (𝟙 X) (f ≫ g) f g (Category.id_comp _) n).hom
          ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
            (Scheme.Hom.deRhamAlgebras (f ≫ g))
            (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) n).inv.hom
            ((classMap (f ≫ g) U hU n).hom ((cocycleClass n (toMor x)
              (toMor_comp_d_eq_zero _ hx)).hom 1)))) := by
  refine (classMap_projHom_eq_lerayCohomologyIso f g U hU haff n x hx hpx).trans ?_
  have e :=
    Stacks.DeRhamBaseChange.deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback
    (𝟙 X) f (f ≫ g) g (Category.id_comp _) n
    ((SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) n).inv.hom
      ((classMap (f ≫ g) U hU n).hom ((cocycleClass n (toMor x)
        (toMor_comp_d_eq_zero _ hx)).hom 1)))
  refine Eq.trans ?_ e.symm
  have h2 := Iso.inv_hom_id_apply (SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) n)
    ((classMap (f ≫ g) U hU n).hom ((cocycleClass n (toMor x) (toMor_comp_d_eq_zero _ hx)).hom 1))
  refine Eq.trans ?_ (congrArg (fun z => (lerayCohomologyIso (relBaseMap f g)
    (DerivedCategory.Q.obj (deRhamPlus f).obj) n).hom
      (((DerivedCategory.homologyFunctor _ n).map
        ((baseSections (AlgebraicGeometry.SheafOfModules.baseRingedSpace (baseSheaf (f ≫ g)))).map
          (DerivedCategory.Q.map (relPushforwardInt f g) ≫
            pushforwardComparisonQ (relBaseMap f g) (deRhamPlus f).obj))).hom z)) h2).symm
  exact congrArg (lerayCohomologyIso (relBaseMap f g)
    (DerivedCategory.Q.obj (deRhamPlus f).obj) n).hom
    (map_map_comp_apply _ (DerivedCategory.homologyFunctor _ n) _ _ _).symm

end AlgebraicGeometry.DeRhamKatzOdaCech

end
