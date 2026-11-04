module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.DerivedActionPushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DeRhamComparisonAdjoint
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductSummand
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapOnSections
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaCechClasses
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyPullbackShift
public import StacksFrontier.CategoryTheory.LinearOfUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.GlobalMorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.DerivedActionUnit

/-!
# The canonical map `Ω^•_{X/S} ⟶ Rh_*Ω^•_{X'/S'}` and the actions of the de Rham algebras

Let `X' ⟶ X` over `S' ⟶ S` be a commutative square of schemes and
`h : (X', p'⁻¹𝒪_{S'}) ⟶ (X, p⁻¹𝒪_S)` the induced morphism of ringed spaces. The canonical map
`d : Ω^•_{X/S} ⟶ h_*Ω^•_{X'/S'}` is multiplicative: it pulls back differential forms, and pulling
back forms commutes with the wedge product. This file records that multiplicativity in the shape
in which Tag 0FP3 turns it into a statement about derived actions: a map of complexes into a
direct image, multiplicative on local sections, is compatible with the actions on total tensor
complexes through the naive cup product.

## Main results

* `AlgebraicGeometry.SheafOfModules.dgAction_comp_eq_of_mul`: a map into a direct image which is
  multiplicative on local sections is compatible with the actions on total tensor complexes.
* `AlgebraicGeometry.DeRhamLerayHirsch.dgaPushforward_mul`: the canonical map of de Rham
  complexes is multiplicative on local sections.

## References

* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] structureSheafRing StacksDraft.KFlat.modulePushforward
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {S S' : RingedSpace.{u, u}} (h : S' ⟶ S)
  {𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf)}
  {𝒜' : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf S'.sheaf)}
  (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜)
  (M' : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜')
  (dM : M.complex ⟶
    (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj M'.complex)
  (d : 𝒜.complex ⟶
    (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj 𝒜'.complex)

/-- **A map into a direct image multiplicative on local sections is compatible with the actions
on total tensor complexes**: if `d_M(x · a) = d_M(x) · d(a)` for local sections `x` of `M` and `a`
of `𝒜`, then `d_M ∘ act_M = h_*(act_{M'}) ∘ (naive cup product) ∘ Tot(d_M ⊗ d)`. -/
theorem dgAction_comp_eq_of_mul
    (hmul : ∀ (a b : ℤ) (U : (Opens S.carrier)ᵒᵖ) (x : (M.complex.X a).val.obj U)
      (y : (𝒜.complex.X b).val.obj U),
      (dM.f (a + b)).val.app U ((M.mul a b).app U x y) =
        (M'.mul a b).app ((Opens.map h.hom.base).op.obj U) ((dM.f a).val.app U x)
          ((d.f b).val.app U y)) :
    dgAction M ≫ dM =
      HomologicalComplex.mapBifunctorMap dM d (sheafTensor S.sheaf) (ComplexShape.up ℤ) ≫
        Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupProduct h M'.complex 𝒜'.complex ≫
        (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).map
          (dgAction M') := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  obtain rfl : a + b = k := hab
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, dgAction_f,
    ι_dgActionDesc_assoc, HomologicalComplex.ι_mapBifunctorMap_assoc]
  refine sheafTensor_hom_ext fun U x y => ?_
  refine (congrArg (fun z => (dM.f (a + b)).val.app U
      ((M.complex.XIsoOfEq (rfl : a + b = a + b)).hom.val.app U z))
    (dgActionComponent_unit_apply M a b U x y)).trans ?_
  refine (hmul a b U x y).trans ?_
  have hA := tensorFunctor_map_unit_apply (A := S.sheaf) (N := 𝒜.complex.X b) (dM.f a) U x y
  have hB := tensorFunctor_obj_map_unit_apply (A := S.sheaf)
    (M := ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj
      M'.complex).X a)
    (d.f b) U ((dM.f a).val.app U x) y
  have hN := congrArg (fun φ => φ.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf).obj)).unit.app
        (PresheafOfModules.tensorObj
          (((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj
            M'.complex).X a).val
          (((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj
            𝒜'.complex).X b).val)).app U
        ((dM.f a).val.app U x ⊗ₜ[S.sheaf.obj.obj U] (d.f b).val.app U y)))
    (Stacks.Cohomology.NaiveCupProductSummand.ι_naiveCupProduct h M'.complex 𝒜'.complex a b
      (a + b) rfl)
  have hT := Stacks.RingedSpace.pushforwardTensorMap_unit_tmul h (M'.complex.X a) (𝒜'.complex.X b) U
    ((dM.f a).val.app U x) ((d.f b).val.app U y)
  have hD := (congrArg (fun φ => φ.val.app ((Opens.map h.hom.base).op.obj U)
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf S'.sheaf)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf S'.sheaf).obj)).unit.app
        (PresheafOfModules.tensorObj (M'.complex.X a).val (𝒜'.complex.X b).val)).app
          ((Opens.map h.hom.base).op.obj U)
        ((dM.f a).val.app U x ⊗ₜ[S'.sheaf.obj.obj ((Opens.map h.hom.base).op.obj U)]
          (d.f b).val.app U y)))
    (ι_dgActionDesc M' a b (a + b) rfl)).trans
    ((XIsoOfEq_hom_val_app _ rfl _ _).trans
      (congrArg _ (dgActionComponent_unit_apply M' a b ((Opens.map h.hom.base).op.obj U)
        ((dM.f a).val.app U x) ((d.f b).val.app U y))))
  have hAB := (congrArg (fun z => (((sheafTensor S.sheaf).obj
    (((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj
      M'.complex).X a)).map
      (d.f b)).val.app U z) hA).trans hB
  refine Eq.symm ?_
  refine (congrArg (fun z =>
    (((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).map (dgAction M')).f
      (a + b)).val.app U
      (((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.naiveCupProduct h M'.complex 𝒜'.complex).f
        (a + b)).val.app U
        ((HomologicalComplex.ιMapBifunctor
          ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj M'.complex)
          ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj 𝒜'.complex)
          (sheafTensor S.sheaf) (ComplexShape.up ℤ) a b (a + b) rfl).val.app U z))) hAB).trans ?_
  refine (congrArg (fun z =>
    (((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).map (dgAction M')).f
      (a + b)).val.app U z) hN).trans ?_
  refine (congrArg (fun z => ((dgAction M').f (a + b)).val.app ((Opens.map h.hom.base).op.obj U)
    ((HomologicalComplex.ιMapBifunctor M'.complex 𝒜'.complex (sheafTensor S'.sheaf)
      (ComplexShape.up ℤ) a b (a + b) rfl).val.app ((Opens.map h.hom.base).op.obj U) z))
    hT).trans ?_
  exact hD.trans rfl

/-- Inserting an identity in a composite. -/
private theorem eq_comp_id_comp {C : Type*} [Category* C] {A B D : C} {f : A ⟶ D} (a : A ⟶ B)
    (b : B ⟶ D) (h : f = a ≫ b) : f = a ≫ 𝟙 B ≫ b := by
  rwa [Category.id_comp]

/-- The comparison `Q(h_*K) ⟶ Rh_*(QK)` is the component of the unit of `Rh_*` read on cochain
complexes. -/
theorem pushforwardComparisonQ_eq_app
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules S') ℤ) :
    Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h K =
      (Stacks.DeRham.GysinCohomologyBaseChange.derivedPushforwardUnitQ h).app K := by
  have e : DerivedCategory.Qh.map
      (((RingedSpaceModuleAdjunction.modulePushforward h).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app K) = 𝟙 _ := DerivedCategory.Qh.map_id _
  simp only [Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ,
    Stacks.DeRham.GysinCohomologyBaseChange.derivedPushforwardUnitQ, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, e, Category.id_comp, Category.comp_id]
  exact eq_comp_id_comp _ _ rfl

/-- **The comparison `h_* ⟶ Rh_*` commutes with the shift**: at the translate `K[n]` it is the
translate of the comparison at `K`, read through the commutation of `h_*`, `Q` and `Rh_*` with
the shift. -/
theorem pushforwardComparisonQ_shift
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules S') ℤ) (n : ℤ) :
    Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
        (K⟦n⟧) =
      DerivedCategory.Q.map
          ((((RingedSpaceModuleAdjunction.modulePushforward h).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso n).hom.app K) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app _ ≫
        (Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
          K)⟦n⟧' ≫
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).commShiftIso
          n).inv.app _ ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map
          ((DerivedCategory.Q.commShiftIso n).inv.app K) := by
  rw [pushforwardComparisonQ_eq_app, pushforwardComparisonQ_eq_app]
  refine (NatTrans.app_shift (Stacks.DeRham.GysinCohomologyBaseChange.derivedPushforwardUnitQ h)
    n K).trans ?_
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_inv_app]
  simp only [Category.assoc]

/-- The two spellings of the commutation of `h_*` with the shift on complexes cancel. -/
theorem pushforwardComplex_commShiftIso_inv_hom_app
    (K : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules S') ℤ) (n : ℤ) :
    ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).commShiftIso
        n).inv.app K ≫
      (((RingedSpaceModuleAdjunction.modulePushforward h).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).hom.app K = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => by
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_inv_app_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.id_comp,
      HomologicalComplex.id_f]
    rfl

/-- The cancellations behind `shift_pushforwardComparisonQ`, with every object and morphism a
variable. -/
theorem shiftPushforward_paste {C : Type*} [Category* C] {X₀ X₁ X₂ X₄ X₅ X₇ X₈ X₉ X₁₀ X₁₁ X₁₂ : C}
    (a : X₀ ⟶ X₁) (e : X₁ ⟶ X₂) (m : X₂ ⟶ X₁) (q : X₁ ⟶ X₄) (i : X₄ ⟶ X₅) (j : X₅ ⟶ X₄)
    (k : X₄ ⟶ X₇) (l : X₇ ⟶ X₈) (c : X₈ ⟶ X₉) (r : X₉ ⟶ X₁₀) (s : X₁₀ ⟶ X₁₁) (t : X₁₁ ⟶ X₁₂)
    (v : X₁₂ ⟶ X₉) (D : X₀ ⟶ X₇) (h₁ : e ≫ m = 𝟙 _) (h₂ : i ≫ j = 𝟙 _) (h₃ : a ≫ q ≫ k = D)
    (h₄ : r ≫ s ≫ t ≫ v = 𝟙 _) :
    D ≫ l ≫ c = a ≫ e ≫ m ≫ q ≫ i ≫ (j ≫ k ≫ l ≫ c ≫ r) ≫ s ≫ t ≫ v := by
  simp only [Category.assoc, reassoc_of% h₁, reassoc_of% h₂, h₄, Category.comp_id]
  rw [← reassoc_of% h₃]

/-- A morphism of sheaves of modules which is a transport along an equality is the identity on
local sections, up to the transport of their types. -/
theorem val_app_heq_of_eq_eqToHom {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} {M N : _root_.SheafOfModules.{u} R}
    (φ : M ⟶ N) (e : M = N) (hφ : φ = eqToHom e) (U : (Opens T)ᵒᵖ) (x : M.val.obj U) :
    HEq (φ.val.app U x) x := by
  subst hφ e
  rfl

section Shift

variable (n : ℤ) (N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜)
  (N' : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜')
  (hN : N.complex = 𝒜.complex⟦n⟧) (hN' : N'.complex = 𝒜'.complex⟦n⟧)

/-- The map `d[n] : 𝒜[n] ⟶ h_*(𝒜'[n])`, read on modules `N`, `N'` whose complexes are the
translates `𝒜[n]`, `𝒜'[n]`. -/
noncomputable def shiftedPushforward :
    N.complex ⟶
      (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj N'.complex :=
  eqToHom hN ≫ d⟦n⟧' ≫
    ((Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).commShiftIso n).inv.app
      𝒜'.complex ≫
    (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).map (eqToHom hN'.symm)

/-- On local sections the map `d[n]` is `d` in the shifted degree. -/
theorem shiftedPushforward_f_app_heq (k j : ℤ) (hj : k + n = j) (U : (Opens S.carrier)ᵒᵖ)
    (x : (N.complex.X k).val.obj U) (x' : (𝒜.complex.X j).val.obj U) (hx : HEq x x') :
    HEq (((shiftedPushforward h d n N N' hN hN').f k).val.app U x) ((d.f j).val.app U x') := by
  subst hj
  have e : (shiftedPushforward h d n N N' hN hN').f k = (eqToHom hN).f k ≫ d.f (k + n) ≫
      (StacksDraft.KFlat.modulePushforward h).map
        (eqToHom (congrArg (fun K => K.X k) hN'.symm)) := by
    simp [shiftedPushforward, HomologicalComplex.eqToHom_f]
  rw [e]
  refine (val_app_heq_of_eq_eqToHom (T := S'.carrier)
    ((eqToHom (congrArg (fun K => K.X k) hN'.symm) :
      (𝒜'.complex⟦n⟧).X k ⟶ N'.complex.X k))
    (congrArg (fun K => K.X k) hN'.symm) rfl _ _).trans ?_
  have h₁ := val_app_heq_of_eq_eqToHom (T := S.carrier) ((eqToHom hN).f k)
    (congrArg (fun K => K.X k) hN) (HomologicalComplex.eqToHom_f _ _) U x
  have h₂ : ((eqToHom hN).f k).val.app U x = x' := eq_of_heq (h₁.trans hx)
  exact heq_of_eq ((congrArg (fun z => (d.f (k + n)).val.app U z) h₂).trans rfl)

/-- **The map `d[n]` is multiplicative on local sections** as soon as `d` is, for modules `N`,
`N'` whose complexes are the translates `𝒜[n]`, `𝒜'[n]` with the actions of `𝒜`, `𝒜'` in the
shifted degree. -/
theorem shiftedPushforward_mul
    (hmul : ∀ (a b : ℤ) (U : (Opens S.carrier)ᵒᵖ) (x : (𝒜.complex.X a).val.obj U)
      (y : (𝒜.complex.X b).val.obj U),
      (d.f (a + b)).val.app U ((𝒜.mul a b).app U x y) =
        (𝒜'.mul a b).app ((Opens.map h.hom.base).op.obj U) ((d.f a).val.app U x)
          ((d.f b).val.app U y))
    (hNmul : ∀ (p q : ℤ) (U : (Opens S.carrier)ᵒᵖ) (x : (N.complex.X p).val.obj U)
      (x' : (𝒜.complex.X (p + n)).val.obj U) (y : (𝒜.complex.X q).val.obj U), HEq x x' →
        HEq ((N.mul p q).app U x y) ((𝒜.mul (p + n) q).app U x' y))
    (hN'mul : ∀ (p q : ℤ) (U : (Opens S'.carrier)ᵒᵖ) (x : (N'.complex.X p).val.obj U)
      (x' : (𝒜'.complex.X (p + n)).val.obj U) (y : (𝒜'.complex.X q).val.obj U), HEq x x' →
        HEq ((N'.mul p q).app U x y) ((𝒜'.mul (p + n) q).app U x' y))
    (a b : ℤ) (U : (Opens S.carrier)ᵒᵖ) (x : (N.complex.X a).val.obj U)
    (y : (𝒜.complex.X b).val.obj U) :
    ((shiftedPushforward h d n N N' hN hN').f (a + b)).val.app U ((N.mul a b).app U x y) =
      (N'.mul a b).app ((Opens.map h.hom.base).op.obj U)
        (((shiftedPushforward h d n N N' hN hN').f a).val.app U x) ((d.f b).val.app U y) := by
  let x' : (𝒜.complex.X (a + n)).val.obj U :=
    cast (congrArg (fun K : CochainComplex _ ℤ => ((K.X a).val.obj U : Type u)) hN) x
  have hx : HEq x x' := (cast_heq _ x).symm
  have hL := shiftedPushforward_f_app_heq h d n N N' hN hN' (a + b) (a + n + b) (by omega) U _ _
    (hNmul a b U x x' y hx)
  have hR := hN'mul a b ((Opens.map h.hom.base).op.obj U)
    (((shiftedPushforward h d n N N' hN hN').f a).val.app U x) ((d.f (a + n)).val.app U x')
    ((d.f b).val.app U y) (shiftedPushforward_f_app_heq h d n N N' hN hN' a (a + n) rfl U x x' hx)
  exact eq_of_heq ((hL.trans (heq_of_eq (hmul (a + n) b U x' y))).trans hR.symm)

/-- **The translate of the canonical map is the canonical map of the translates**: conjugated by
the identifications of `Q(N)` with `Q(𝒜)[n]`, of `Q(N')` with `Q(𝒜')[n]` and the commutation of
`Rh_*` with the shift, `(Q(d) ≫ (h_* ⟶ Rh_*))[n]` is `Q(d[n]) ≫ (h_* ⟶ Rh_*)`. -/
theorem shift_pushforwardComparisonQ :
    (DerivedCategory.Q.map d ≫
        Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
          𝒜'.complex)⟦n⟧' ≫
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).commShiftIso
        n).inv.app (DerivedCategory.Q.obj 𝒜'.complex) =
    ((DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex ≫
        eqToHom (congrArg DerivedCategory.Q.obj hN.symm)) ≫
      (DerivedCategory.Q.map (shiftedPushforward h d n N N' hN hN') ≫
        Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
          N'.complex) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map
        (eqToHom (congrArg DerivedCategory.Q.obj hN') ≫
          (DerivedCategory.Q.commShiftIso n).hom.app 𝒜'.complex) := by
  have hnat :=
   Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ_naturality
    h (eqToHom hN'.symm)
  simp only [shiftedPushforward, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, pushforwardComparisonQ_shift]
  refine shiftPushforward_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · rw [eqToHom_map, eqToHom_trans, eqToHom_refl]
  · rw [← Functor.map_comp]
    exact (congrArg DerivedCategory.Q.map (pushforwardComplex_commShiftIso_inv_hom_app h _ n)).trans
      (DerivedCategory.Q.map_id _)
  · exact (congrArg (fun t => (DerivedCategory.Q.commShiftIso n).inv.app 𝒜.complex ≫ t)
      (DerivedCategory.Q.commShiftIso_hom_naturality (d : 𝒜.complex ⟶
        ((RingedSpaceModuleAdjunction.modulePushforward h).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj 𝒜'.complex) n)).trans (Iso.inv_hom_id_app_assoc _ _ _)
  · have hq : DerivedCategory.Q.map (eqToHom hN'.symm) ≫
        eqToHom (congrArg DerivedCategory.Q.obj hN') = 𝟙 _ := by
      rw [eqToHom_map, eqToHom_trans, eqToHom_refl]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, reassoc_of% hq,
      Iso.inv_hom_id_app]
    exact CategoryTheory.Functor.map_id _ _

end Shift

/-- The pasting behind `relativeCupProduct_derivedShiftedMul`, with every object and morphism a
variable. -/
theorem shiftedMul_paste {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ Y₀ Y₁ : C}
    (x : X₀ ⟶ X₁) (y : X₁ ⟶ X₂) (z : X₂ ⟶ X₃) (w : X₃ ⟶ X₄) (w₀ : X₂ ⟶ X₅) (u : X₅ ⟶ X₄)
    (u' : X₄ ⟶ X₅) (a : X₅ ⟶ X₆) (b : X₆ ⟶ X₇) (e : X₁ ⟶ Y₀) (f : Y₀ ⟶ X₆) (g : Y₀ ⟶ Y₁)
    (k : Y₁ ⟶ Y₀) (T : X₀ ⟶ X₃) (M : X₄ ⟶ X₇) (hT : T = x ≫ y ≫ z) (hM : M = u' ≫ a ≫ b)
    (h₁ : z ≫ w = w₀ ≫ u) (h₂ : u ≫ u' = 𝟙 _)
    (h₃ : y ≫ w₀ ≫ a = e ≫ f) (h₄ : g ≫ k = 𝟙 _) :
    T ≫ w ≫ M = (x ≫ e ≫ g) ≫ k ≫ f ≫ b := by
  subst hT hM
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄]

/-- A bifunctor applied to a composite of three morphisms in the first variable. -/
theorem map_prod_comp_comp_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (T : C × D ⥤ E) {X₀ X₁ X₂ X₃ : C} {Y₀ Y₁ : D} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (g : Y₀ ⟶ Y₁) (g' : Y₁ ⟶ Y₁) (hg' : g' = 𝟙 Y₁) :
    T.map ((a ≫ b ≫ c) ×ₘ g) = T.map (a ×ₘ 𝟙 Y₀) ≫ T.map (b ×ₘ g) ≫ T.map (c ×ₘ g') := by
  subst hg'
  rw [← T.map_comp, ← T.map_comp, prod_comp, prod_comp, Category.id_comp, Category.comp_id]

/-- Two morphisms inverse to each other in the first variable of a bifunctor, followed by a
functor. -/
theorem map_map_prod_comp_eq_id {C D E F : Type*} [Category* C] [Category* D] [Category* E]
    [Category* F] (R : E ⥤ F) (T : C × D ⥤ E) {X Y : C} (x : X ⟶ Y) (y : Y ⟶ X) (Z : D)
    (hxy : x ≫ y = 𝟙 X) :
    R.map (T.map (x ×ₘ 𝟙 Z)) ≫ R.map (T.map (y ×ₘ 𝟙 Z)) = 𝟙 _ := by
  rw [← R.map_comp, ← T.map_comp]
  simp [hxy]

/-- Inverse isomorphisms around transports along equalities. -/
theorem eqToHom_comp_hom_inv_comp_eqToHom {C : Type*} [Category* C] {X Y Z : C} (e : X = Y)
    (i : Y ≅ Z) : (eqToHom e ≫ i.hom) ≫ i.inv ≫ eqToHom e.symm = 𝟙 X := by
  simp

/-- The two variables of a bifunctor, composed in either order. -/
theorem map_comp_prod_id_comp_map_id_prod {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (T : C × D ⥤ E) {X₀ X₁ X₂ : C} {Y₀ Y₁ : D} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (c : Y₀ ⟶ Y₁) :
    T.map ((a ≫ b) ×ₘ 𝟙 Y₀) ≫ T.map (𝟙 X₂ ×ₘ c) = T.map (a ×ₘ 𝟙 Y₀) ≫ T.map (b ×ₘ c) := by
  rw [← T.map_comp, ← T.map_comp, prod_comp, prod_comp]
  simp

/-- The two variables of a bifunctor, composed in the other order. -/
theorem map_comp_prod_id_comp_map_id_prod' {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (T : C × D ⥤ E) {X₀ X₁ X₂ : C} {Y₀ Y₁ : D} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (c : Y₀ ⟶ Y₁) :
    T.map ((a ≫ b) ×ₘ 𝟙 Y₀) ≫ T.map (𝟙 X₂ ×ₘ c) = T.map (a ×ₘ c) ≫ T.map (b ×ₘ 𝟙 Y₁) := by
  rw [← T.map_comp, ← T.map_comp, prod_comp, prod_comp]
  simp

/-- The pasting behind the linearity of `c ≫ Rh_*F'`, with every object and morphism a
variable. -/
theorem linear_pushforward_paste {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ : C} (A : X₀ ⟶ X₁) (ν₁ : X₁ ⟶ X₂) (ν₂ : X₂ ⟶ X₃)
    (ν₃ : X₃ ⟶ X₄) (Xm : X₀ ⟶ X₅) (Y : X₅ ⟶ X₂) (W : X₅ ⟶ X₆) (V : X₆ ⟶ X₇) (RF : X₇ ⟶ X₄)
    (μ : X₀ ⟶ X₈) (c : X₈ ⟶ X₇) (e₁ : A ≫ ν₁ = Xm ≫ Y) (e₂ : Y ≫ ν₂ ≫ ν₃ = (W ≫ V) ≫ RF)
    (e₃ : Xm ≫ W ≫ V = μ ≫ c) : A ≫ ν₁ ≫ ν₂ ≫ ν₃ = μ ≫ c ≫ RF := by
  rw [reassoc_of% e₁, e₂, ← Category.assoc, e₃, Category.assoc]

/-- The pasting behind the linearity of `F ≫ c[n] ≫ cs`, with every object and morphism a
variable. -/
theorem linear_shift_paste {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₈ X₉ : C} (A : X₀ ⟶ X₁) (ν₁ : X₁ ⟶ X₂) (ν₂ : X₂ ⟶ X₃)
    (ν₃ : X₃ ⟶ X₄) (Fm : X₀ ⟶ X₅) (Gc : X₅ ⟶ X₂) (sh : X₅ ⟶ X₉) (G : X₉ ⟶ X₄) (μ : X₀ ⟶ X₈)
    (F : X₈ ⟶ X₉) (e₁ : A ≫ ν₁ = Fm ≫ Gc) (e₂ : Gc ≫ ν₂ ≫ ν₃ = sh ≫ G)
    (e₃ : Fm ≫ sh = μ ≫ F) : A ≫ ν₁ ≫ ν₂ ≫ ν₃ = μ ≫ F ≫ G := by
  rw [reassoc_of% e₁, e₂, reassoc_of% e₃]

section Mult

variable (hmul : ∀ (a b : ℤ) (U : (Opens S.carrier)ᵒᵖ) (x : (𝒜.complex.X a).val.obj U)
      (y : (𝒜.complex.X b).val.obj U),
      (d.f (a + b)).val.app U ((𝒜.mul a b).app U x y) =
        (𝒜'.mul a b).app ((Opens.map h.hom.base).op.obj U) ((d.f a).val.app U x)
          ((d.f b).val.app U y))

include hmul

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **The canonical map is compatible with the multiplications of the translates**: for
`c = Q(d) ≫ (h_* ⟶ Rh_*)` and the multiplications `μ_{𝒜[n]}`, `μ_{𝒜'[n]}` of the translates,
`((c[n] ≫ cs) ⊗ c) ≫ μ_{rel} ≫ Rh_*(μ_{𝒜'[n]}) = μ_{𝒜[n]} ≫ c[n] ≫ cs`. -/
theorem relativeCupProduct_derivedShiftedMul (n : ℤ) :
    Eq ((Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          S.sheaf)).map
          (((DerivedCategory.Q.map d ≫
              Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
                h
                𝒜'.complex)⟦n⟧' ≫
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).commShiftIso
              n).inv.app (DerivedCategory.Q.obj 𝒜'.complex)) ×ₘ
            (DerivedCategory.Q.map d ≫
              Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
                h
                𝒜'.complex)) ≫
        Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct h
          ((DerivedCategory.Q.obj 𝒜'.complex)⟦n⟧) (DerivedCategory.Q.obj 𝒜'.complex) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map
          (derivedShiftedMul 𝒜' n))
      (derivedShiftedMul 𝒜 n ≫
        (DerivedCategory.Q.map d ≫
          Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
            𝒜'.complex)⟦n⟧' ≫
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).commShiftIso
          n).inv.app (DerivedCategory.Q.obj 𝒜'.complex)) := by
  let N := _root_.SheafOfModules.DifferentialGradedModule.shiftedModule
    (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜
    (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n
  let N' := _root_.SheafOfModules.DifferentialGradedModule.shiftedModule
    (X := Stacks.SheafOfModules.opensRingedSite S'.sheaf) 𝒜'
    (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜') n
  have hN : N.complex = 𝒜.complex⟦n⟧ :=
    _root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.shiftFunctor_obj_complex
      (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜 n
      (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)
  have hN' : N'.complex = 𝒜'.complex⟦n⟧ :=
    _root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.shiftFunctor_obj_complex
      (X := Stacks.SheafOfModules.opensRingedSite S'.sheaf) 𝒜' n
      (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜')
  have multN := relativeCupProduct_derivedAction_pushforwardComparisonQ h N N'
    (shiftedPushforward h d n N N' hN hN') d (dgAction_comp_eq_of_mul h N N' _ d
      (shiftedPushforward_mul h d n N N' hN hN' hmul
        (_root_.SheafOfModules.DifferentialGradedModule.shiftedModule_mul_heq
          (X := Stacks.SheafOfModules.opensRingedSite S.sheaf) 𝒜
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) n)
        (_root_.SheafOfModules.DifferentialGradedModule.shiftedModule_mul_heq
          (X := Stacks.SheafOfModules.opensRingedSite S'.sheaf) 𝒜'
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜') n)))
  have hnat := Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural h
    (eqToHom (congrArg DerivedCategory.Q.obj hN') ≫
      (DerivedCategory.Q.commShiftIso n).hom.app 𝒜'.complex) (𝟙 (DerivedCategory.Q.obj 𝒜'.complex))
  unfold derivedShiftedMul derivedActionOfShift
  rw [shift_pushforwardComparisonQ h d n N N' hN hN']
  refine shiftedMul_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))) hnat ?_ multN ?_
  · exact map_prod_comp_comp_comp _ _ _ _ _ _ (CategoryTheory.Functor.map_id _ _)
  · exact map_map_prod_comp_eq_id _ _ _ _ _
      (eqToHom_comp_hom_inv_comp_eqToHom _ ((DerivedCategory.Q.commShiftIso n).app 𝒜'.complex))
  · exact eqToHom_comp_hom_inv_comp_eqToHom _ ((DerivedCategory.Q.commShiftIso n).app 𝒜.complex)

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat in
/-- **Linear morphisms out of the algebra commute with the canonical map into a direct image.**
Let `c = Q(d) ≫ (h_* ⟶ Rh_*) : 𝒜 ⟶ Rh_*𝒜'` for a map `d` multiplicative on local sections,
let `F : 𝒜 ⟶ 𝒜[n]` and `F' : 𝒜' ⟶ 𝒜'[n]` be linear for the derived actions, and let
`u : O ⟶ 𝒜` be a morphism along which the action is invertible. If
`u ≫ c ≫ Rh_*F' = u ≫ F ≫ c[n] ≫ cs`, then `c ≫ Rh_*F' = F ≫ c[n] ≫ cs`: both sides are
linear for the action `(1 ⊗ c) ≫ μ_{rel} ≫ Rh_*(μ_{𝒜'[n]})` on `Rh_*(𝒜'[n])`. -/
theorem comp_derivedPushforward_map_eq_of_linear (n : ℤ)
    (F : DerivedCategory.Q.obj 𝒜.complex ⟶ (DerivedCategory.Q.obj 𝒜.complex)⟦n⟧)
    (hF : (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        S.sheaf)).map
        (F ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫ derivedShiftedMul 𝒜 n =
      derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) ≫ F)
    (F' : DerivedCategory.Q.obj 𝒜'.complex ⟶ (DerivedCategory.Q.obj 𝒜'.complex)⟦n⟧)
    (hF' : (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        S'.sheaf)).map
        (F' ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜'.complex)) ≫ derivedShiftedMul 𝒜' n =
      derivedAction 𝒜' (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜') ≫ F')
    {O : DerivedCategory
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf))}
    (u : O ⟶ DerivedCategory.Q.obj 𝒜.complex)
    (hiso : IsIso ((Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        S.sheaf)).map
        (u ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫
      derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)))
    (hu : u ≫ (DerivedCategory.Q.map d ≫
        Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
          𝒜'.complex) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map F' =
      u ≫ F ≫ (DerivedCategory.Q.map d ≫
        Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
          𝒜'.complex)⟦n⟧' ≫
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).commShiftIso
          n).inv.app (DerivedCategory.Q.obj 𝒜'.complex)) :
    (DerivedCategory.Q.map d ≫
        Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
          𝒜'.complex) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map F' =
      F ≫ (DerivedCategory.Q.map d ≫
        Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
          𝒜'.complex)⟦n⟧' ≫
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).commShiftIso
          n).inv.app (DerivedCategory.Q.obj 𝒜'.complex) := by
  have mult := relativeCupProduct_derivedAction_pushforwardComparisonQ h
    (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)
    (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜') d d
    (dgAction_comp_eq_of_mul h (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)
      (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜') d d hmul)
  refine @CategoryTheory.eq_of_comp_eq_of_linear _ _
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf))
    _ _ _ u
    (derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))
    ((Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        (𝟙 _ ×ₘ (DerivedCategory.Q.map d ≫
          Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ h
            𝒜'.complex)) ≫
      Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct h
        ((DerivedCategory.Q.obj 𝒜'.complex)⟦n⟧) (DerivedCategory.Q.obj 𝒜'.complex) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map
        (derivedShiftedMul 𝒜' n)) hiso _ _ ?_ ?_ hu
  · exact linear_pushforward_paste _ _ _ _ _ _ _ _ _ _ _
      (map_comp_prod_id_comp_map_id_prod' _ _ _ _)
      (relativeCupProduct_comp_of_derivedAction 𝒜' h n F' hF') mult
  · exact linear_shift_paste _ _ _ _ _ _ _ _ _ _
      (map_comp_prod_id_comp_map_id_prod _ _ _ _)
      (relativeCupProduct_derivedShiftedMul h d hmul n) hF

end Mult

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.DeRhamLerayHirsch

open DeRhamKatzOdaCech (baseSheaf)


variable {X X' S S' : Scheme.{u}} (ι : X' ⟶ X) (p' : X' ⟶ S') (p : X ⟶ S) (h₀ : S' ⟶ S)
  (w : ι ≫ p = p' ≫ h₀)

/-- The de Rham differential graded algebra of `p`. -/
noncomputable abbrev dga (p : X ⟶ S) :=
  SheafOfModules.deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))

/-- The canonical map of de Rham complexes, typed at the differential graded algebras. -/
noncomputable abbrev dgaPushforward :
    (dga p).complex ⟶ (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex
      (inverseImageBaseMap ι p' p h₀ w : SheafOfModules.baseRingedSpace (baseSheaf p') ⟶
        SheafOfModules.baseRingedSpace (baseSheaf p))).obj (dga p').complex :=
  deRhamPushforwardInt ι p' p h₀ w

/-- The morphism of inverse-image ringed spaces of the square, between the base ringed spaces. -/
noncomputable abbrev squareMap : SheafOfModules.baseRingedSpace (baseSheaf p') ⟶
    SheafOfModules.baseRingedSpace (baseSheaf p) :=
  inverseImageBaseMap ι p' p h₀ w

/-- A transport along an equality of sheaves of modules is the identity on local sections, up to
the transport of their types. -/
theorem eqToHom_val_app_heq {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    {M N : _root_.SheafOfModules.{u} R} (h : M = N) (U : (Opens T)ᵒᵖ) (x : M.val.obj U) :
    HEq ((eqToHom h).val.app U x) x := by
  subst h
  rfl

/-- The reindexing of the extension of a complex along `ℕ ⊆ ℤ` is the identity on local sections,
up to the transport of their types. -/
theorem extendXIso_hom_val_app_heq {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (K : CochainComplex (_root_.SheafOfModules.{u} R) ℕ) {i' : ℤ} {i : ℕ}
    (h : ComplexShape.embeddingUpNat.f i = i') (U : (Opens T)ᵒᵖ)
    (x : ((K.extend ComplexShape.embeddingUpNat).X i').val.obj U) :
    HEq ((K.extendXIso ComplexShape.embeddingUpNat h).hom.val.app U x) x := by
  unfold HomologicalComplex.extendXIso HomologicalComplex.extend.XIso
  rw [eqToIso.hom]
  exact eqToHom_val_app_heq _ U x

/-- The inverse reindexing, on local sections. -/
theorem extendXIso_inv_val_app_heq {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (K : CochainComplex (_root_.SheafOfModules.{u} R) ℕ) {i' : ℤ} {i : ℕ}
    (h : ComplexShape.embeddingUpNat.f i = i') (U : (Opens T)ᵒᵖ) (x : (K.X i).val.obj U) :
    HEq ((K.extendXIso ComplexShape.embeddingUpNat h).inv.val.app U x) x := by
  unfold HomologicalComplex.extendXIso HomologicalComplex.extend.XIso
  rw [eqToIso.inv]
  exact eqToHom_val_app_heq _ U x

/-- Local sections of a composite of three morphisms of sheaves of modules. -/
theorem comp_comp_val_app {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    {M N P Q : _root_.SheafOfModules.{u} R} (a : M ⟶ N) (b : N ⟶ P) (c : P ⟶ Q)
    (U : (Opens T)ᵒᵖ) (x : M.val.obj U) :
    (a ≫ b ≫ c).val.app U x = c.val.app U (b.val.app U (a.val.app U x)) :=
  rfl

/-- **The canonical map of de Rham complexes on local sections** is the pullback of differential
forms, in every nonnegative degree. -/
theorem dgaPushforward_f_app_heq (i : ℤ) (q : ℕ) (hi : i = q) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((dga p).complex.X i).val.obj U)
    (x' : Γ(Scheme.Hom.relativeDifferentialForms p (q : ℤ), U.unop)) (hx : HEq x x') :
    HEq (((dgaPushforward ι p' p h₀ w).f i).val.app U x)
      (Scheme.Hom.relativeDifferentialFormsPullback ι p p' h₀ w (q : ℤ) U.unop x') := by
  subst hi
  rw [show dgaPushforward ι p' p h₀ w = deRhamPushforwardInt ι p' p h₀ w from rfl,
    deRhamPushforwardInt_f ι p' p h₀ w q]
  refine (heq_of_eq (comp_comp_val_app (T := X.carrier) _ _ _ U x)).trans ?_
  refine (extendXIso_inv_val_app_heq (T := X'.carrier) _ _ _ _).trans ?_
  have h₁ : ((ProperSmoothDeRham.deRhamComplexNat p).extendXIso ComplexShape.embeddingUpNat
      (i := q) rfl).hom.val.app U x = x' :=
    eq_of_heq ((extendXIso_hom_val_app_heq (T := X.carrier) _ _ _ _).trans hx)
  exact heq_of_eq ((congrArg (fun z => ((deRhamPushforwardChain ι p' p h₀ w).f q).val.app U z)
    h₁).trans rfl)

/-- The local sections of a negative-degree term of the extended de Rham complex vanish. -/
theorem dga_section_eq_zero (a : ℤ) (ha : a < 0) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((dga p).complex.X a).val.obj U) : x = 0 := by
  have hz : Limits.IsZero ((dga p).complex.X a) :=
    (Scheme.Hom.deRhamComplex p).isZero_extend_X ComplexShape.embeddingUpNat a fun n hn =>
      absurd ha (not_lt_of_ge (hn ▸ Int.natCast_nonneg n))
  let ev : _root_.SheafOfModules.{u} (SheafOfModules.underlyingRingSheaf.{u, u} (baseSheaf p)) ⥤
      ModuleCat.{u} ((SheafOfModules.underlyingRingSheaf.{u, u} (baseSheaf p)).obj.obj U) :=
    _root_.SheafOfModules.evaluation (SheafOfModules.underlyingRingSheaf.{u, u} (baseSheaf p)) U
  have hev : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact (ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero ev hz)).elim x 0

/-- The canonical map of de Rham complexes is multiplicative on local sections of nonnegative
degrees. -/
private theorem dgaPushforward_mul_natCast (m n : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((dga p).complex.X m).val.obj U) (y : ((dga p).complex.X n).val.obj U) :
    ((dgaPushforward ι p' p h₀ w).f (m + n)).val.app U (((dga p).mul m n).app U x y) =
      ((dga p').mul m n).app ((Opens.map (squareMap ι p' p h₀ w).hom.base).op.obj U)
        (((dgaPushforward ι p' p h₀ w).f m).val.app U x)
        (((dgaPushforward ι p' p h₀ w).f n).val.app U y) := by
  have key : ∀ (k : ℕ) (z : ((dga p).complex.X k).val.obj U),
      ∃ z' : Γ(Scheme.Hom.relativeDifferentialForms p (k : ℤ), U.unop), HEq z z' := fun k z =>
    ⟨cast (congrArg (fun M : _root_.SheafOfModules.{u}
      (SheafOfModules.underlyingRingSheaf.{u, u} (baseSheaf p)) => (M.val.obj U : Type u))
      (SheafOfModules.deRhamComplexInt_X_of_nonneg (Scheme.Hom.deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) (k : ℤ)
        (Int.natCast_nonneg k))) z, (cast_heq _ z).symm⟩
  obtain ⟨x', hx⟩ := key m x
  obtain ⟨y', hy⟩ := key n y
  have hL := dgaPushforward_f_app_heq ι p' p h₀ w ((m : ℤ) + (n : ℤ)) (m + n) (by omega) U
    (((dga p).mul m n).app U x y)
    (((Scheme.Hom.relativeDifferentialFormsAlgebra p).mul m n).app (op U.unop) x' y')
    (SheafOfModules.deRhamDifferentialGradedAlgebra_mul (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) m n U x y x' y' hx hy)
  have hM :=
    Scheme.Hom.relativeDifferentialFormsPullback_mul ι p p' h₀ w (m : ℤ) (n : ℤ) U.unop x' y'
  have hR := SheafOfModules.deRhamDifferentialGradedAlgebra_mul (Scheme.Hom.deRhamAlgebras p')
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p')) m n
    ((Opens.map (squareMap ι p' p h₀ w).hom.base).op.obj U)
    (((dgaPushforward ι p' p h₀ w).f m).val.app U x)
    (((dgaPushforward ι p' p h₀ w).f n).val.app U y)
    (Scheme.Hom.relativeDifferentialFormsPullback ι p p' h₀ w (m : ℤ) U.unop x')
    (Scheme.Hom.relativeDifferentialFormsPullback ι p p' h₀ w (n : ℤ) U.unop y')
    (dgaPushforward_f_app_heq ι p' p h₀ w m m rfl U x x' hx)
    (dgaPushforward_f_app_heq ι p' p h₀ w n n rfl U y y' hy)
  exact eq_of_heq (hL.trans ((heq_of_eq hM).trans hR.symm))

/-- **The canonical map of de Rham complexes is multiplicative on local sections**: it carries
the wedge product of two local forms to the wedge product of their pullbacks. -/
theorem dgaPushforward_mul (a b : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((dga p).complex.X a).val.obj U) (y : ((dga p).complex.X b).val.obj U) :
    ((dgaPushforward ι p' p h₀ w).f (a + b)).val.app U (((dga p).mul a b).app U x y) =
      ((dga p').mul a b).app ((Opens.map (squareMap ι p' p h₀ w).hom.base).op.obj U)
        (((dgaPushforward ι p' p h₀ w).f a).val.app U x)
        (((dgaPushforward ι p' p h₀ w).f b).val.app U y) := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb
      exact dgaPushforward_mul_natCast ι p' p h₀ w m n U x y
    · obtain rfl := dga_section_eq_zero p b (by omega) U y
      simp only [map_zero]
      exact (map_zero ((((dga p').mul a b).app _) _)).symm
  · obtain rfl := dga_section_eq_zero p a (by omega) U x
    simp only [map_zero, AddMonoidHom.zero_apply]
    exact ((DFunLike.congr_fun (map_zero (((dga p').mul a b).app _)) _).trans
      (AddMonoidHom.zero_apply _)).symm

end AlgebraicGeometry.DeRhamLerayHirsch
