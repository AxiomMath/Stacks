module

public import StacksFrontier.Deformation.ToposThickening.DerivedLiftShift
public import StacksFrontier.Deformation.ToposThickening.CoefficientSquareZeroReduction

/-!
# Derived base change along a composite commutes with the shift

Derived base change `- ⊗^L_O O₀` along `f : O ⟶ O₀` commutes with the shift, being left adjoint
to derived restriction of scalars (`Deformation.ComplexLift.derivedExtensionOfScalars_commShift`),
and the derived adjunction is compatible with these commutations
(`Deformation.ComplexLift.derivedAdjunction_commShift`). For `f = g ≫ f'` the identification
`(- ⊗^L_O O') ⊗^L_{O'} O₀ ≅ - ⊗^L_O O₀` of
`Deformation.ComplexLift.derivedExtensionOfScalarsCompIso` is the comparison of two left adjoints
of derived restriction along `f` whose adjunctions are compatible with the shift, hence it
commutes with the shift
(`Deformation.ComplexLift.commShift_derivedExtensionOfScalarsCompIso_hom`). The general fact is
`CategoryTheory.Adjunction.commShift_leftAdjointUniq_hom`.

So the base changes `O₀[V] ⟶ O₀[W]` between the reduction triangles of the trivial square-zero
extensions `O₀[V] = O₀ ⊕ (O₀ ⊗_k V)` commute with the shift, functor and comparison
(`Deformation.ComplexLift.coefficientReductionBaseChange_functor_commShift`,
`Deformation.ComplexLift.coefficientReductionBaseChange_baseChangeIso_commShift`): these are the
hypotheses under which shifting lifts commutes with base change of lifts
(`Deformation.ComplexLift.DerivedLift.liftClassMap_classShift`), in the proof of Stacks 0DLL.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] (A : Type*) [AddMonoid A] [HasShift C A]
  [HasShift D A]

/-- **Transporting an adjunction along an isomorphism of right adjoints commuting with the shift
keeps it compatible with the shift.** -/
theorem commShift_ofNatIsoRight {F : C ⥤ D} {G G' : D ⥤ C} (adj : F ⊣ G) (e : G ≅ G')
    [F.CommShift A] [G.CommShift A] [G'.CommShift A] [adj.CommShift A]
    [NatTrans.CommShift e.hom A] : (adj.ofNatIsoRight e).CommShift A := by
  refine CommShift.mk' _ _ ?_
  have h : (adj.ofNatIsoRight e).unit = adj.unit ≫ Functor.whiskerLeft F e.hom := by
    ext X
    simp
  rw [h]
  infer_instance

/-- **The comparison of two left adjoints of one functor commutes with the shift**, when both
adjunctions are compatible with the shift. -/
theorem commShift_leftAdjointUniq_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    [F.CommShift A] [F'.CommShift A] [G.CommShift A] [adj1.CommShift A] [adj2.CommShift A] :
    NatTrans.CommShift (leftAdjointUniq adj1 adj2).hom A := ⟨fun a => by
  ext X
  apply (adj1.homEquiv _ _).injective
  rw [← cancel_mono ((G.commShiftIso a).hom.app (F'.obj X))]
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality, ← Category.assoc (adj1.unit.app _),
    ← Category.assoc (adj1.unit.app _), ← Category.assoc ((adj1.unit.app _) ≫ _),
    Category.assoc (adj1.unit.app _), ← shift_unit_app, ← Functor.map_comp,
    unit_leftAdjointUniq_hom_app, unit_leftAdjointUniq_hom_app, ← shift_unit_app]⟩

end CategoryTheory.Adjunction

/- `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is stated for sheaves of modules in a `max`
universe and makes the universe unifier get stuck on the abelian structure of `SheafOfModules.{u}`;
Mathlib's instance is the one the derived categories here are taken for. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe d d' d₀ v' u u'

namespace Deformation.ComplexLift

section Comp

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section One

variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The canonical identification of a derived base change with itself is the identity. -/
theorem DerivedExtensionOfScalars.baseChangeIso_self_hom (T : DerivedExtensionOfScalars.{d, d₀} f) :
    (DerivedExtensionOfScalars.baseChangeIso T T).hom = 𝟙 _ :=
  Functor.leftDerivedNatTrans_id _ _
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))

/-- The adjunction of `Deformation.ComplexLift.derivedAdjunctionOf` at the constructed derived
base change has the unit of the derived adjunction. -/
theorem derivedAdjunctionOf_derivedExtensionOfScalarsData_unit :
    (derivedAdjunctionOf.{d, d₀} f (derivedExtensionOfScalarsData.{d, d₀} f)).unit =
      (derivedAdjunction.{d, d₀} f).unit := by
  ext X
  change (derivedAdjunction.{d, d₀} f).unit.app X ≫ (restrictionOnDerived.{d, d₀} f).map
      ((DerivedExtensionOfScalars.baseChangeIso (derivedExtensionOfScalarsData.{d, d₀} f)
        (derivedExtensionOfScalarsData.{d, d₀} f)).hom.app X) = _
  rw [DerivedExtensionOfScalars.baseChangeIso_self_hom, NatTrans.id_app]
  exact (congrArg (fun t => (derivedAdjunction.{d, d₀} f).unit.app X ≫ t)
    ((restrictionOnDerived.{d, d₀} f).map_id _)).trans (Category.comp_id _)

/-- **Derived base change commutes with the shift**, through the commutation of
`Deformation.ComplexLift.derivedExtensionOfScalarsData_commShift`. -/
instance derivedExtensionOfScalars_commShift :
    (derivedExtensionOfScalars.{d, d₀} f).CommShift ℤ :=
  derivedExtensionOfScalarsData_commShift (f := f)

/-- **The derived adjunction is compatible with the shift.** -/
instance derivedAdjunction_commShift : (derivedAdjunction.{d, d₀} f).CommShift ℤ := by
  have h := (derivedAdjunctionOf.{d, d₀} f
    (derivedExtensionOfScalarsData.{d, d₀} f)).commShift_of_rightAdjoint ℤ
  refine Adjunction.CommShift.mk' _ _ ?_
  rw [← derivedAdjunctionOf_derivedExtensionOfScalarsData_unit]
  exact h.commShift_unit

end One

variable {O O' O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀} {f' : O' ⟶ O₀} (g : O ⟶ O')
  (hg : g ≫ f' = f)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O'))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- The composite of the derived adjunctions along `g` and `f'`, read with derived restriction
along `f` as right adjoint, is compatible with the shift. -/
instance derivedAdjunctionComp_commShift :
    (derivedAdjunctionComp.{d, d', d₀} g hg).CommShift ℤ :=
  Adjunction.commShift_ofNatIsoRight ℤ _ _

/-- **Derived base change along a composite commutes with the shift**: the identification of
derived base change along `g` and then along `f'` with derived base change along `f = g ≫ f'` is
compatible with the commutations of the three functors with the shift. -/
instance commShift_derivedExtensionOfScalarsCompIso_hom :
    NatTrans.CommShift (derivedExtensionOfScalarsCompIso.{d, d', d₀} g hg).hom ℤ :=
  Adjunction.commShift_leftAdjointUniq_hom ℤ _ _

end Comp

section Coefficient

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {k : Type u} [Field k] {O₀ : Sheaf J CommRingCat.{u}}
  (θ : Stacks.TensorByBaseModule.constantRingPresheaf (C := C) k ⟶ O₀.obj)
variable [∀ V : FGModuleCat.{u} k, HasDerivedCategory.{d} (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (coefficientRing θ V)))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **The base change `O₀[V] ⟶ O₀[W]` of reduction triangles commutes with the shift.** -/
instance coefficientReductionBaseChange_functor_commShift {V W : FGModuleCat.{u} k}
    (f : V ⟶ W) : (coefficientReductionBaseChange.{d, d₀} θ f).functor.CommShift ℤ :=
  derivedExtensionOfScalars_commShift (coefficientRingMap θ f)

/-- **The comparison of the base change `O₀[V] ⟶ O₀[W]` of reduction triangles commutes with the
shift.** -/
instance coefficientReductionBaseChange_baseChangeIso_commShift {V W : FGModuleCat.{u} k}
    (f : V ⟶ W) :
    NatTrans.CommShift (coefficientReductionBaseChange.{d, d₀} θ f).baseChangeIso.hom ℤ :=
  commShift_derivedExtensionOfScalarsCompIso_hom (coefficientRingMap θ f)
    (sqZeroExtSheafAnySiteMap_comp_proj ((coefficientModule θ).map f))

end Coefficient

end Deformation.ComplexLift

end
