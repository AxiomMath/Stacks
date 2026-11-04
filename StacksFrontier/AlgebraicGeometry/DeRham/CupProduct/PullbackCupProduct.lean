module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.GlobalCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ActionWedge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductSummand
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductOnSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductOnCohomology
import all StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic

/-!
# The canonical map of de Rham complexes is multiplicative

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes and `g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` the induced
morphism of ringed spaces. Section 0FM1 of the Stacks project asserts that the pullback maps on de
Rham cohomology are compatible with the cup product. This file proves the complex-level input:
the canonical map `Ω^•_{X/S} ⟶ g₀_*Ω^•_{X'/S'}` carries the wedge product of `Ω^•_{X/S}` to the
naive cup product of Tag 0FP3 followed by `g₀_*` of the wedge product of `Ω^•_{X'/S'}`.

## Main definitions

* `Stacks.DeRhamBaseChange.deRhamWedge`: the wedge product `Tot(Ω^• ⊗ Ω^•) ⟶ Ω^•`, the action of
  the relative de Rham differential graded algebra on itself, at the spelling of the total tensor
  complex of sheaves of modules on `(X, f⁻¹𝒪_S)`.

## Main results

* `Stacks.DeRhamBaseChange.formsPushforward_formProduct` and
  `Stacks.DeRhamBaseChange.deRhamPushforwardInt_mul`: on local sections the canonical map is
  multiplicative, in natural and in integer degrees.
* `Stacks.DeRhamBaseChange.deRhamWedge_comp_deRhamPushforwardInt`: **the canonical map of de Rham
  complexes is multiplicative**, as a morphism of complexes.

## Implementation notes

The complexes come in two spellings, the module category of `(X, f⁻¹𝒪_S)` in which the naive cup
product is stated and that of the base ring sheaf `f⁻¹𝒪_S` in which the differential graded
algebra is; they agree definitionally. The wedge product and the de Rham complex are therefore
retyped once (`Stacks.DeRhamBaseChange.deRhamWedge`,
`Stacks.DeRhamBaseChange.deRhamComplexModules`) and the comparison is done on local pure tensors,
where both sides are computed by the multiplicativity of the graded homomorphism of Tag 07HX.

## References

* [Stacks Project, Section 0FM1](https://stacks.math.columbia.edu/tag/0FM1)
* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage AlgebraicGeometry.ProperSmoothDeRham
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens CategoryTheory.Prod

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace Stacks.DeRhamBaseChange

open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (naiveCupProduct pushforwardComplex)

/-- `⊗` preserves zero morphisms in its first variable, being additive. -/
local instance preservesZeroMorphisms_sheafTensor (Y : RingedSpace.{u, u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- `⊗` preserves zero morphisms in its first variable, being additive. -/
local instance preservesZeroMorphisms_sheafTensor' (T : TopCat.{u})
    (Rc : TopCat.Sheaf CommRingCat.{u} T) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Rc).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- `F ⊗ -` preserves zero morphisms, being additive. -/
local instance preservesZeroMorphisms_sheafTensor_obj (Y : RingedSpace.{u, u})
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
      M).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The relative de Rham differential graded algebra of a morphism of schemes. -/
abbrev deRhamDGA (p : X ⟶ S) :=
  AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra (Scheme.Hom.deRhamAlgebras p)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p))

example : (deRhamDGA f).complex = deRhamComplexInt f := rfl

/-- The relative de Rham complex `Ω^•_{X/S}`, extended by zero, at the spelling of the category of
modules over `(X, p⁻¹𝒪_S)` that the tensor product of sheaves of modules is stated at. -/
abbrev deRhamComplexModules (p : X ⟶ S) :
    CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (inverseImageBase p))
      ℤ :=
  deRhamComplexInt p

/-- The wedge product of the relative de Rham complex, `Tot(Ω^• ⊗ Ω^•) ⟶ Ω^•`, as a morphism of
`ℤ`-indexed complexes of `p⁻¹𝒪_S`-modules at the spelling of the total tensor complex. -/
def deRhamWedge (p : X ⟶ S) :
    (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase p).sheaf)).obj
        (deRhamComplexModules p, deRhamComplexModules p) ⟶ deRhamComplexModules p :=
  AlgebraicGeometry.SheafOfModules.dgAction
    (_root_.SheafOfModules.DifferentialGradedModule.regularModule (deRhamDGA p))

/-- On the `(a, b)` summand of the total tensor complex, the wedge product is the multiplication
`Ω^a ⊗ Ω^b ⟶ Ω^{a+b}` of the differential graded algebra. -/
theorem ι_deRhamWedge_f (p : X ⟶ S) (a b : ℤ) :
    HomologicalComplex.ιMapBifunctor (deRhamComplexModules p) (deRhamComplexModules p)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase p).sheaf)
        (ComplexShape.up ℤ) a b (a + b) rfl ≫ (deRhamWedge p).f (a + b) =
      AlgebraicGeometry.SheafOfModules.dgActionComponent
        (_root_.SheafOfModules.DifferentialGradedModule.regularModule (deRhamDGA p)) a b ≫
        ((deRhamDGA p).complex.XIsoOfEq rfl).hom :=
  HomologicalComplex.ι_mapBifunctorDesc (K₁ := deRhamComplexModules p)
    (K₂ := deRhamComplexModules p)
    (F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase p).sheaf)
    (c := ComplexShape.up ℤ) (fun a b h => AlgebraicGeometry.SheafOfModules.dgActionComponent
        (_root_.SheafOfModules.DifferentialGradedModule.regularModule (deRhamDGA p)) a b ≫
        ((deRhamDGA p).complex.XIsoOfEq h).hom) a b rfl

/-- An `eqToHom` between sheaves of modules is the transport of local sections. -/
theorem eqToHom_val_app_heq {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R} (h : M = N) (U : Cᵒᵖ)
    (x : M.val.obj U) : HEq ((eqToHom h).val.app U x) x := by
  subst h
  rfl

/-- **On local sections, the canonical map `Ω^p_{X/S} ⟶ (g₀)_*Ω^p_{X'/S'}` is the degree-`p`
component of the graded homomorphism `⋀ Ω_{X/S} ⟶ g'_*(⋀ Ω_{X'/S'})` of Tag 07HX.** -/
theorem formsPushforward_val_app (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (σ : ((Scheme.Hom.deRhamComplex f).X p).val.obj U) :
    (formsPushforward g' f' f g w p).val.app U σ =
      ((Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).app (p : ℤ)).val.app U σ :=
  congrArg (fun φ => φ.val.app U σ) (formsAdjoint_eq_deRhamFormsPushforwardHom g' f' f g w p)

/-- **The canonical map of de Rham complexes is multiplicative**: on local sections it carries the
wedge product `σ ∧ τ` of a `p`-form and a `q`-form to the wedge product of their pullbacks. This
is the multiplicativity of the graded homomorphism of Tag 07HX. -/
theorem formsPushforward_formProduct (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (σ : ((Scheme.Hom.deRhamAlgebras f).exteriorPower p).val.obj U)
    (τ : ((Scheme.Hom.deRhamAlgebras f).exteriorPower q).val.obj U) :
    (formsPushforward g' f' f g w (p + q)).val.app U
        (AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras f) p q U σ τ) =
      AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras f') p q
        ((Opens.map g'.base).op.obj U) ((formsPushforward g' f' f g w p).val.app U σ)
        ((formsPushforward g' f' f g w q).val.app U τ) := by
  refine (formsPushforward_val_app g' f' f g w (p + q) U _).trans ?_
  refine ((Scheme.Hom.deRhamFormsPushforwardHom g' f f' g w).map_mul (p : ℤ) (q : ℤ) U σ τ).trans ?_
  exact congrArg₂ (AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras f') p q
    ((Opens.map g'.base).op.obj U)) (formsPushforward_val_app g' f' f g w p U σ).symm
    (formsPushforward_val_app g' f' f g w q U τ).symm

/-- The identification of a term of a complex extended by zero with the term it extends is the
transport of local sections. -/
theorem extendXIso_hom_val_app_heq {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (K : CochainComplex (_root_.SheafOfModules.{u} R) ℕ) (p : ℕ)
    (U : Cᵒᵖ) (x : ((K.extend ComplexShape.embeddingUpNat).X (p : ℤ)).val.obj U) :
    HEq ((K.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom.val.app U x) x := by
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.hom]
  exact eqToHom_val_app_heq _ U x

/-- The inverse identification of a term of a complex extended by zero with the term it extends
is the transport of local sections. -/
theorem extendXIso_inv_val_app_heq {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (K : CochainComplex (_root_.SheafOfModules.{u} R) ℕ) (p : ℕ)
    (U : Cᵒᵖ) (x : (K.X p).val.obj U) :
    HEq ((K.extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv.val.app U x) x := by
  simp only [HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.inv]
  exact eqToHom_val_app_heq _ U x

/-- **The canonical map of de Rham complexes is multiplicative, in integer degrees**: on local
sections of the relative de Rham complex extended by zero, it carries the product of the
differential graded algebra `Ω^•_{X/S}` to the product of `Ω^•_{X'/S'}`. -/
theorem deRhamPushforwardInt_mul (a b : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((deRhamDGA f).complex.X a).val.obj U) (y : ((deRhamDGA f).complex.X b).val.obj U) :
    ((deRhamPushforwardInt g' f' f g w).f (a + b)).val.app U (((deRhamDGA f).mul a b).app U x y) =
      ((deRhamDGA f').mul a b).app ((Opens.map g'.base).op.obj U)
        (((deRhamPushforwardInt g' f' f g w).f a).val.app U x)
        (((deRhamPushforwardInt g' f' f g w).f b).val.app U y) := by
  have hzero : ∀ c : ℤ, c < 0 → ∀ z, ((deRhamPushforwardInt g' f' f g w).f c).val.app U z = 0 :=
    fun c hc z => by
      obtain rfl := AlgebraicGeometry.SheafOfModules.deRhamComplexInt_section_eq_zero _ _ c hc U z
      exact map_zero (ConcreteCategory.hom (((deRhamPushforwardInt g' f' f g w).f c).val.app U))
  by_cases ha : a < 0
  · rw [AlgebraicGeometry.SheafOfModules.bilinear_app_eq_zero_left _ U y
      (AlgebraicGeometry.SheafOfModules.deRhamComplexInt_section_eq_zero _ _ a ha U x)]
    exact (map_zero _).trans
      (AlgebraicGeometry.SheafOfModules.bilinear_app_eq_zero_left ((deRhamDGA f').mul a b)
        ((Opens.map g'.base).op.obj U) _ (hzero a ha x)).symm
  by_cases hb : b < 0
  · rw [AlgebraicGeometry.SheafOfModules.bilinear_app_eq_zero_right _ U x
      (AlgebraicGeometry.SheafOfModules.deRhamComplexInt_section_eq_zero _ _ b hb U y)]
    exact (map_zero _).trans
      (AlgebraicGeometry.SheafOfModules.bilinear_app_eq_zero_right ((deRhamDGA f').mul a b)
        ((Opens.map g'.base).op.obj U) _ (hzero b hb y)).symm
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 ha)
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hb)
  let σ :=
    ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom.val.app U x
  let τ :=
    ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := q) rfl).hom.val.app U y
  have hx : HEq x σ := (extendXIso_hom_val_app_heq _ p U x).symm
  have hy : HEq y τ := (extendXIso_hom_val_app_heq _ q U y).symm
  have hmul : HEq (((deRhamDGA f).mul (p : ℤ) (q : ℤ)).app U x y)
      (AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras f) p q U σ τ) :=
    AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_mul _ _ p q U x y σ τ hx hy
  have hf : ∀ (n : ℕ) (z : ((deRhamDGA f).complex.X (n : ℤ)).val.obj U),
      ((deRhamPushforwardInt g' f' f g w).f (n : ℤ)).val.app U z =
        ((deRhamComplexNat f').extendXIso ComplexShape.embeddingUpNat (i := n) rfl).inv.val.app
          ((Opens.map g'.base).op.obj U) ((formsPushforward g' f' f g w n).val.app U
            (((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := n)
              rfl).hom.val.app U z)) :=
    fun n z => congrArg (fun φ => φ.val.app U z) (deRhamPushforwardInt_f g' f' f g w n)
  have hL := hf (p + q) (((deRhamDGA f).mul (p : ℤ) (q : ℤ)).app U x y)
  have hz : ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := p + q)
      rfl).hom.val.app U (((deRhamDGA f).mul (p : ℤ) (q : ℤ)).app U x y) =
        AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras f) p q U σ τ :=
    eq_of_heq ((extendXIso_hom_val_app_heq _ (p + q) U _).trans hmul)
  have hL' := hL.trans (congrArg (fun t => ((deRhamComplexNat f').extendXIso
      ComplexShape.embeddingUpNat (i := p + q) rfl).inv.val.app ((Opens.map g'.base).op.obj U) t)
    ((congrArg (fun t => (formsPushforward g' f' f g w (p + q)).val.app U t) hz).trans
      (formsPushforward_formProduct g' f' f g w p q U σ τ)))
  have hR : HEq (((deRhamDGA f').mul (p : ℤ) (q : ℤ)).app ((Opens.map g'.base).op.obj U)
      (((deRhamPushforwardInt g' f' f g w).f (p : ℤ)).val.app U x)
      (((deRhamPushforwardInt g' f' f g w).f (q : ℤ)).val.app U y))
      (AlgebraicGeometry.SheafOfModules.formProduct (Scheme.Hom.deRhamAlgebras f') p q
        ((Opens.map g'.base).op.obj U) ((formsPushforward g' f' f g w p).val.app U σ)
        ((formsPushforward g' f' f g w q).val.app U τ)) :=
    AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra_mul _ _ p q _ _ _ _ _
      ((heq_of_eq (hf p x)).trans (extendXIso_inv_val_app_heq _ p _ _))
      ((heq_of_eq (hf q y)).trans (extendXIso_inv_val_app_heq _ q _ _))
  have hLH := (heq_of_eq hL').trans (extendXIso_inv_val_app_heq _ (p + q)
    ((Opens.map g'.base).op.obj U) _)
  exact eq_of_heq (hLH.trans hR.symm)

/-- The canonical map of de Rham complexes `Ω^•_{X/S} ⟶ (g₀)_*Ω^•_{X'/S'}`, at the spelling of the
category of modules that the tensor product of sheaves of modules is stated at. -/
abbrev deRhamPushforwardModules :
    deRhamComplexModules f ⟶
      (pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (deRhamComplexModules f') :=
  deRhamPushforwardInt g' f' f g w

/-- The class of a local pure tensor `x ⊗ y` in the tensor product of two sheaves of modules over
`(X, p⁻¹𝒪_S)`. -/
abbrev unitTensor (p : X ⟶ S)
    {F G : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (inverseImageBase p)}
    (U : (Opens X.carrier)ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase p).sheaf).obj
      F).obj G).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageBase p).sheaf).obj)).unit.app
      (F.val.tensorObj G.val)).app U (x ⊗ₜ[(inverseImageBase p).sheaf.obj.obj U] y)

/-- The wedge product on the `(a, b)` summand, on a local pure tensor. -/
theorem ι_deRhamWedge_f_unitTensor (p : X ⟶ S) (a b : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((deRhamComplexModules p).X a).val.obj U) (y : ((deRhamComplexModules p).X b).val.obj U) :
    (HomologicalComplex.ιMapBifunctor (deRhamComplexModules p) (deRhamComplexModules p)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase p).sheaf)
        (ComplexShape.up ℤ) a b (a + b) rfl ≫ (deRhamWedge p).f (a + b)).val.app U
          (unitTensor p U x y) = ((deRhamDGA p).mul a b).app U x y := by
  have h0 : AlgebraicGeometry.SheafOfModules.dgActionComponent
        (_root_.SheafOfModules.DifferentialGradedModule.regularModule (deRhamDGA p)) a b ≫
        ((deRhamDGA p).complex.XIsoOfEq rfl).hom =
      AlgebraicGeometry.SheafOfModules.dgActionComponent
        (_root_.SheafOfModules.DifferentialGradedModule.regularModule (deRhamDGA p)) a b := by
    rw [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    exact Category.comp_id _
  have e := congrArg (fun φ => φ.val.app U (unitTensor p U x y)) ((ι_deRhamWedge_f p a b).trans h0)
  have e2 := AlgebraicGeometry.SheafOfModules.dgActionComponent_unit_apply
    (_root_.SheafOfModules.DifferentialGradedModule.regularModule (deRhamDGA p)) a b U x y
  exact e.trans e2

/-- The total tensor complex of the canonical map with itself, on a local pure tensor of the
`(a, b)` summand. -/
theorem ι_mapBifunctorMap_deRhamPushforwardInt_unitTensor (a b : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((deRhamComplexModules f).X a).val.obj U) (y : ((deRhamComplexModules f).X b).val.obj U) :
    (HomologicalComplex.ιMapBifunctor (deRhamComplexModules f) (deRhamComplexModules f)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)
        (ComplexShape.up ℤ) a b (a + b) rfl ≫
      (HomologicalComplex.mapBifunctorMap (deRhamPushforwardModules g' f' f g w)
        (deRhamPushforwardModules g' f' f g w)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)
        (ComplexShape.up ℤ)).f (a + b)).val.app U (unitTensor f U x y) =
    (HomologicalComplex.ιMapBifunctor
        ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (deRhamComplexModules f'))
        ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (deRhamComplexModules f'))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)
        (ComplexShape.up ℤ) a b (a + b) rfl).val.app U
      (unitTensor f U (((deRhamPushforwardModules g' f' f g w).f a).val.app U x)
        (((deRhamPushforwardModules g' f' f g w).f b).val.app U y)) := by
  have r1 := congrArg (fun φ => φ.val.app U (unitTensor f U x y))
    (HomologicalComplex.ι_mapBifunctorMap (deRhamPushforwardModules g' f' f g w)
      (deRhamPushforwardModules g' f' f g w)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)
      (ComplexShape.up ℤ) a b (a + b) rfl)
  refine r1.trans ?_
  exact congrArg (fun t => (HomologicalComplex.ιMapBifunctor
        ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (deRhamComplexModules f'))
        ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (deRhamComplexModules f'))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)
        (ComplexShape.up ℤ) a b (a + b) rfl).val.app U t)
    (Stacks.RingedSpace.tensorSheaf_map_unit_tmul (Z := inverseImageBase f)
      ((deRhamPushforwardModules g' f' f g w).f a) ((deRhamPushforwardModules g' f' f g w).f b)
      U x y)

/-- The naive cup product of `g₀` followed by the pushforward of the wedge product of
`Ω^•_{X'/S'}`, on a local pure tensor of the `(a, b)` summand of `Tot(g₀_*Ω^• ⊗ g₀_*Ω^•)`: it is
the product of the two sections in `Ω^•_{X'/S'}`. -/
theorem ι_naiveCupProduct_deRhamWedge_unitTensor (a b : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (u : (((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj
      (deRhamComplexModules f')).X a).val.obj U)
    (v : (((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj
      (deRhamComplexModules f')).X b).val.obj U) :
    (HomologicalComplex.ιMapBifunctor
        ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (deRhamComplexModules f'))
        ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (deRhamComplexModules f'))
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)
        (ComplexShape.up ℤ) a b (a + b) rfl ≫
      (naiveCupProduct (inverseImageBaseMap g' f' f g w) (deRhamComplexModules f')
        (deRhamComplexModules f')).f (a + b) ≫
      ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).map (deRhamWedge f')).f
        (a + b)).val.app U (unitTensor f U u v) =
      ((deRhamDGA f').mul a b).app ((Opens.map g'.base).op.obj U) u v := by
  have r2 := congrArg (fun φ => (((pushforwardComplex (inverseImageBaseMap g' f' f g w)).map
      (deRhamWedge f')).f (a + b)).val.app U (φ.val.app U (unitTensor f U u v)))
    (Stacks.Cohomology.NaiveCupProductSummand.ι_naiveCupProduct (inverseImageBaseMap g' f' f g w)
      (deRhamComplexModules f') (deRhamComplexModules f') a b (a + b) rfl)
  refine r2.trans ?_
  have r3 := Stacks.RingedSpace.pushforwardTensorMap_unit_tmul (inverseImageBaseMap g' f' f g w)
    ((deRhamComplexModules f').X a) ((deRhamComplexModules f').X b) U u v
  refine (congrArg (fun t => (((pushforwardComplex (inverseImageBaseMap g' f' f g w)).map
      (deRhamWedge f')).f (a + b)).val.app U
      (((StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g' f' f g w)).map
        (HomologicalComplex.ιMapBifunctor (deRhamComplexModules f') (deRhamComplexModules f')
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase f').sheaf)
          (ComplexShape.up ℤ) a b (a + b) rfl)).val.app U t)) r3).trans ?_
  exact ι_deRhamWedge_f_unitTensor f' a b ((Opens.map g'.base).op.obj U) u v

/-- **The canonical map of de Rham complexes is multiplicative** (Stacks, Section 0FM1): the
square

`Tot(Ω^•_{X/S} ⊗ Ω^•_{X/S}) --∧--> Ω^•_{X/S}`, `Tot(g₀_*Ω^•_{X'/S'} ⊗ g₀_*Ω^•_{X'/S'}) ⟶
g₀_*Tot(Ω^•_{X'/S'} ⊗ Ω^•_{X'/S'}) --g₀_*∧--> g₀_*Ω^•_{X'/S'}`

commutes, the vertical maps being the canonical map `Ω^•_{X/S} ⟶ g₀_*Ω^•_{X'/S'}` and the
bottom-left map the naive cup product of Tag 0FP3. On local pure tensors it is the
multiplicativity of the graded homomorphism of Tag 07HX. -/
theorem deRhamWedge_comp_deRhamPushforwardInt :
    deRhamWedge f ≫ deRhamPushforwardInt g' f' f g w =
    (Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase f).sheaf)).map
        (deRhamPushforwardInt g' f' f g w ×ₘ deRhamPushforwardInt g' f' f g w) ≫
      naiveCupProduct (inverseImageBaseMap g' f' f g w) (deRhamComplexInt f')
        (deRhamComplexInt f') ≫
      (pushforwardComplex (inverseImageBaseMap g' f' f g w)).map (deRhamWedge f') := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  obtain rfl : a + b = n := hab
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map]
  dsimp only
  refine AlgebraicGeometry.SheafOfModules.sheafTensor_hom_ext (X := inverseImageBase f)
    (A := (inverseImageBase f).sheaf) (fun U x y => ?_)
  refine (congrArg (fun t => ((deRhamPushforwardModules g' f' f g w).f (a + b)).val.app U t)
    (ι_deRhamWedge_f_unitTensor f a b U x y)).trans ?_
  refine (deRhamPushforwardInt_mul g' f' f g w a b U x y).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => ((naiveCupProduct (inverseImageBaseMap g' f' f g w)
      (deRhamComplexModules f') (deRhamComplexModules f')).f (a + b) ≫
      ((pushforwardComplex (inverseImageBaseMap g' f' f g w)).map (deRhamWedge f')).f
        (a + b)).val.app U t)
    (ι_mapBifunctorMap_deRhamPushforwardInt_unitTensor g' f' f g w a b U x y)).symm
  exact (ι_naiveCupProduct_deRhamWedge_unitTensor g' f' f g w a b U _ _).symm

end Stacks.DeRhamBaseChange
