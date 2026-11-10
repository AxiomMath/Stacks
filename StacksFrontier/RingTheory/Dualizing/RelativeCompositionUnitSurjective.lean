module

public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionUnitDescent
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Resolution

/-!
# The unit of extension of scalars along a surjection, after a flat base change

Let `p : B →+* C` be a flat ring map and `i : C →+* C'` a surjective ring map with `i ∘ p` flat.
For every complex `P` of `B`-modules the unit `C ⊗_B P ⟶ C' ⊗_C (C ⊗_B P)` of extension of
scalars along `i` is surjective on cohomology.  Both `C ⊗_B -` and `C' ⊗_C (C ⊗_B -)` are exact
functors of `B`-modules, so cohomology commutes with both, and on a module the unit
`m ↦ 1 ⊗ m` is surjective because `i` is.

## Main results

* `Dualizing.epi_homologyMap_unit_extendScalars` -- the statement on complexes.
* `Dualizing.epi_homologyFunctor_map_derivedUnit_of_flat` -- the same for the unit of derived
  extension of scalars at the derived base change along `p` of any object of `D(B)`.
-/

@[expose] public section

open CategoryTheory Limits
open scoped ChangeOfRings

universe u

namespace Dualizing

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {B C C' : Type u} [CommRing B] [CommRing C] [CommRing C']

/-- On modules, the unit of extension of scalars along a surjective ring map is surjective. -/
theorem surjective_extendRestrictScalarsAdj_unit_app (i : C →+* C') (hi : Function.Surjective i)
    (M : ModuleCat.{u} C) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj.{u} i).unit.app M) := by
  intro y
  change ((ModuleCat.extendScalars i).obj M : Type u) at y
  induction y using TensorProduct.inductionOn with
  | tmul c' m =>
    obtain ⟨c, rfl⟩ := hi c'
    refine ⟨c • m, ?_⟩
    rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    change (1 : C') ⊗ₜ[C, i] (c • m) = (i c) ⊗ₜ[C, i] m
    let : Module C C' := Module.compHom C' i
    rw [← TensorProduct.smul_tmul]
    congr 1
    change i c * 1 = i c
    rw [mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

section Complexes

variable (p : B →+* C) (i : C →+* C')

/-- Extension of scalars along `p` followed by extension and restriction of scalars along `i`. -/
abbrev extendExtendRestrict : ModuleCat.{u} B ⥤ ModuleCat.{u} C :=
  ModuleCat.extendScalars.{u, u, u} p ⋙ ModuleCat.extendScalars.{u, u, u} i ⋙
    ModuleCat.restrictScalars.{u} i

/-- The unit of extension of scalars along `i`, whiskered by extension of scalars along `p`. -/
def extendUnit : ModuleCat.extendScalars.{u, u, u} p ⟶ extendExtendRestrict p i :=
  Functor.whiskerLeft (ModuleCat.extendScalars.{u, u, u} p)
    (ModuleCat.extendRestrictScalarsAdj.{u} i).unit

/-- `extendExtendRestrict p i` is extension of scalars along `i ∘ p` followed by restriction. -/
def extendExtendRestrictIso :
    extendExtendRestrict p i ≅
      ModuleCat.extendScalars.{u, u, u} (i.comp p) ⋙ ModuleCat.restrictScalars.{u} i :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ModuleCat.extendScalarsComp p i).symm _

/-- Extension of scalars is additive, being a left adjoint. -/
instance extendScalars_additive_unitSurjective : (ModuleCat.extendScalars.{u, u, u} p).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u} p).left_adjoint_additive

/-- `extendExtendRestrict p i` is additive. -/
instance extendExtendRestrict_additive : (extendExtendRestrict p i).Additive := by
  have : (ModuleCat.extendScalars.{u, u, u} i).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u} i).left_adjoint_additive
  infer_instance

/-- Extension of scalars along a ring map preserves finite colimits. -/
theorem extendScalars_preservesFiniteColimits (f : B →+* C) :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) := by
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} f) :=
    (ModuleCat.extendRestrictScalarsAdj.{u} f).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

variable {p i}

/-- If `i ∘ p` is flat, then `extendExtendRestrict p i` preserves finite limits. -/
theorem preservesFiniteLimits_extendExtendRestrict (hp' : (i.comp p).Flat) :
    PreservesFiniteLimits (extendExtendRestrict p i) := by
  have := extendScalars_preservesFiniteLimits_of_flat'.{u, u} (i.comp p) hp'
  exact preservesFiniteLimits_of_natIso (extendExtendRestrictIso p i).symm

/-- `extendExtendRestrict p i` preserves finite colimits. -/
theorem preservesFiniteColimits_extendExtendRestrict :
    PreservesFiniteColimits (extendExtendRestrict p i) := by
  have := extendScalars_preservesFiniteColimits.{u} (i.comp p)
  exact preservesFiniteColimits_of_natIso (extendExtendRestrictIso p i).symm

/-- **The unit is surjective on cohomology, on complexes.**  For `p` flat, `i` surjective and
`i ∘ p` flat, the unit of extension of scalars along `i` at the base change `C ⊗_B X` of any
complex of `B`-modules is an epimorphism on every cohomology module. -/
theorem epi_homologyMap_unit_extendScalars (hp : p.Flat) (hi : Function.Surjective i)
    (hp' : (i.comp p).Flat) (X : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    Epi (HomologicalComplex.homologyMap
      (((ModuleCat.extendRestrictScalarsAdj.{u} i).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app
          (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            X)) n) := by
  have := extendScalars_preservesFiniteLimits_of_flat'.{u, u} p hp
  have := extendScalars_preservesFiniteColimits p
  have := preservesFiniteLimits_extendExtendRestrict hp'
  have := preservesFiniteColimits_extendExtendRestrict (p := p) (i := i)
  have h := Functor.mapHomologicalComplexCompHomologyFunctorIso_hom_naturality
    (extendUnit p i) n X
  have hα : Epi ((extendUnit p i).app
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ) n).obj X)) :=
    (ModuleCat.epi_iff_surjective _).2 (surjective_extendRestrictScalarsAdj_unit_app i hi _)
  have : Epi ((HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) n).map
        ((NatTrans.mapHomologicalComplex (extendUnit p i) (ComplexShape.up ℤ)).app X) ≫
      ((extendExtendRestrict p i).mapHomologicalComplexCompHomologyFunctorIso n).hom.app X) := by
    rw [h]
    infer_instance
  have h2 := (epi_comp_iff_of_isIso _ _).1 this
  exact h2

/-- **The derived unit is surjective on cohomology.**  For `p` flat, `i` surjective and `i ∘ p`
flat, let `F` be any total left derived functor of extension of scalars along `i` and let `W` be
an object of `D(C)` isomorphic to the base change along `p` of a K-flat complex of `B`-modules.
Then the unit of `F ⊣ i_*` at `W` is surjective on every cohomology module. -/
theorem epi_homologyFunctor_map_derivedUnit_of_flat (hp : p.Flat) (hi : Function.Surjective i)
    (hp' : (i.comp p).Flat)
    (F : DerivedCategory (ModuleCat.{u} C) ⥤ DerivedCategory (ModuleCat.{u} C'))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u} i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} C) (ComplexShape.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (hP : P.KFlat) (W : DerivedCategory (ModuleCat.{u} C))
    (e : DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        W)
    (n : ℤ) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) n).map
      ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u} i F
        comparison).unit.app W)) := by
  let Y := ((ModuleCat.extendScalars.{u, u, u} p).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hY : CochainComplex.KFlat.{u, u} Y := _root_.kFlat_baseChange p P hP
  let adjE := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
    i F comparison
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} C) n
  have hnat := adjE.unit.naturality e.hom
  have hW : adjE.unit.app W = e.inv ≫ adjE.unit.app (DerivedCategory.Q.obj Y) ≫
      (F ⋙ (ModuleCat.restrictScalars.{u} i).mapDerivedCategory).map e.hom := by
    rw [← hnat]
    simp
  have hQ :=
    CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat
      i F comparison Y hY
  have hu := epi_homologyMap_unit_extendScalars hp hi hp' P n
  have hHQ : Epi (H.map (DerivedCategory.Q.map
      (((ModuleCat.extendRestrictScalarsAdj.{u} i).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app Y))) := by
    have h := DerivedCategory.homologyFunctorFactors_hom_naturality
      (((ModuleCat.extendRestrictScalarsAdj.{u} i).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app Y) n
    have h2 : Epi ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} C) n).hom.app
        ((𝟭 (HomologicalComplex (ModuleCat.{u} C) (ComplexShape.up ℤ))).obj Y) ≫
        HomologicalComplex.homologyMap
          (((ModuleCat.extendRestrictScalarsAdj.{u} i).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app Y) n) :=
      @epi_comp _ _ _ _ _ _ inferInstance _ hu
    rw [← h] at h2
    exact (@epi_comp_iff_of_isIso _ _ _ _ _ _ _
      (Iso.isIso_hom ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} C) n).app _))).1 h2
  have hUY : Epi (H.map (adjE.unit.app (DerivedCategory.Q.obj Y))) := by
    rw [hQ]
    simp only [Functor.map_comp]
    infer_instance
  rw [hW]
  simp only [Functor.map_comp]
  infer_instance

end Complexes

end

end Dualizing

end
