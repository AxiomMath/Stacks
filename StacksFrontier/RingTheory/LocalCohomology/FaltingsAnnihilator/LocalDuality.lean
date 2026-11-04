module

public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator.DerivedAnnihilators
import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom

/-!
# Local duality and its base change to a prime

`Ext` into a complex of finite injective dimension as the cohomology of derived Hom; the `𝔪`-adic
form of local duality, [Stacks, Tag 0AAK], with local cohomology spelled as support in `V(𝔪)`,
and the resulting equality of the annihilators of `Ext^{-i}(K, ω)` and `H^i_{V(𝔪)}(K)`; flat base
change of a dualizing complex and of derived Hom along `A → A_𝔮`; local duality at an arbitrary
prime, objectwise in the complex.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (krullDimToEInt)

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.LocalCohomology

open CategoryTheory.Limits CategoryTheory.Pretriangulated

private noncomputable def homologyExtEquiv
    {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension K)
    (L : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    DerivedCategory.Ext (DerivedCategory.Q.obj L) K i ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} A K).obj
          (.op (DerivedCategory.Q.obj L))) : Type (u)) := by
  classical
  let hfinite := hK
  let a := Classical.choose hfinite
  have hIa := Classical.choose_spec hfinite
  let b := Classical.choose hIa
  have hIb := Classical.choose_spec hIa
  let I := Classical.choose hIb
  have hparts := Classical.choose_spec hIb
  let hGE := hparts.1
  let hLE := hparts.2.1
  let hI := hparts.2.2.1
  let eK : DerivedCategory.Q.obj I ≅ K := (Classical.choice hparts.2.2.2).symm
  letI : I.IsStrictlyGE a := hGE
  letI : I.IsStrictlyLE b := hLE
  letI (j : ℤ) : Injective (I.X j) := hI j
  letI : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let d := StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u,
    u + 1} A
  let dUL := StacksDraft.DerivedHom.derivedHomAdjunctionULift.{u, u,
    u + 1} (R := A)
  let eMod := StacksDraft.DerivedHom.uliftModuleEquivalence.{u, u, u} A
  letI : Algebra (ULift.{u} A) A := RingHom.toAlgebra ULift.ringEquiv.toRingHom
  letI : CategoryTheory.Linear (ULift.{u} A) (ModuleCat.{u} A) :=
    ModuleCat.Algebra.instLinear
  letI : Functor.Linear (ULift.{u} A) eMod.functor := by
    refine ⟨?_⟩
    intro X Y f r
    ext x
    change (r • f.hom) x = r • f.hom x
    rfl
  let eDer := StacksDraft.DerivedHom.derivedScalarEquivalence.{u, u,
    u + 1} A
  letI : Functor.Linear (ULift.{u} A) eDer.functor := by
    change Functor.Linear (ULift.{u} A) (eMod.functor.mapDerivedCategory)
    infer_instance
  let eComplex := eMod.mapHomologicalComplex (ComplexShape.up ℤ)
  let L' := (eMod.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let I' := (eMod.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  letI : CochainComplex.IsStrictlyGE I' a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    change Limits.IsZero (eMod.inverse.obj (I.X j))
    exact Functor.map_isZero eMod.inverse
      ((CochainComplex.isStrictlyGE_iff I a).mp hGE j hj)
  letI (j : ℤ) : Injective (I'.X j) := by
    change Injective (eMod.inverse.obj (I.X j))
    infer_instance
  letI : CochainComplex.IsKInjective I' := CochainComplex.isKInjective_of_injective I' a
  let eL : eDer.functor.obj (DerivedCategory.Q.obj L') ≅ DerivedCategory.Q.obj L :=
    eMod.functor.mapDerivedCategoryFactors.app L' ≪≫
      DerivedCategory.Q.mapIso (eComplex.counitIso.app L)
  let eI : eDer.functor.obj (DerivedCategory.Q.obj I') ≅ DerivedCategory.Q.obj I :=
    eMod.functor.mapDerivedCategoryFactors.app I' ≪≫
      DerivedCategory.Q.mapIso (eComplex.counitIso.app I)
  let eKI := eI ≪≫ eK
  let H := CochainComplex.HomComplexR (ULift.{u} A) L' I'
  let eModel : d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), K) ≅
      eDer.functor.obj (DerivedCategory.Q.obj H) :=
    d.hom.mapIso (eL.op.prod eKI.symm) ≪≫
      (StacksDraft.DerivedHom.derivedHomULiftIso.{u, u,
        u + 1} A).app
        (Opposite.op (DerivedCategory.Q.obj L'), DerivedCategory.Q.obj I') ≪≫
      eDer.functor.mapIso (dUL.homIso L' I')
  let qUL := HomotopyCategory.quotient
    (ModuleCat.{u} (ULift.{u} A)) (ComplexShape.up ℤ)
  let eLQh := (DerivedCategory.quotientCompQhIso
    (ModuleCat.{u} (ULift.{u} A))).app L'
  let eIQh := (DerivedCategory.quotientCompQhIso
    (ModuleCat.{u} (ULift.{u} A))).app (I'⟦i⟧) ≪≫
      (DerivedCategory.Q.commShiftIso i).app I'
  let eQhUL : (qUL.obj L' ⟶ qUL.obj (I'⟦i⟧)) ≃
      (DerivedCategory.Q.obj L' ⟶ (DerivedCategory.Q.obj I')⟦i⟧) :=
    (Equiv.ofBijective DerivedCategory.Qh.map
      (CochainComplex.IsKInjective.Qh_map_bijective (qUL.obj L') (I'⟦i⟧))).trans
      (CategoryTheory.Iso.homCongr eLQh eIQh)
  let eExtUL : CochainComplex.HomComplex.CohomologyClass L' I' i ≃
      DerivedCategory.Ext (DerivedCategory.Q.obj L') (DerivedCategory.Q.obj I') i :=
    (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (K := L') (L := I') (n := i)).toEquiv.trans eQhUL
  letI : eMod.functor.mapDerivedCategory.CommShift ℤ := inferInstance
  letI : eDer.functor.CommShift ℤ := by
    change eMod.functor.mapDerivedCategory.CommShift ℤ
    infer_instance
  let eShift : eDer.functor.obj
        ((shiftFunctor (DerivedCategory (ModuleCat.{u} (ULift.{u} A))) i).obj
          (DerivedCategory.Q.obj I')) ≅
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) i).obj K :=
    (eDer.functor.commShiftIso i).app
      (DerivedCategory.Q.obj I') ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) i).mapIso eKI
  let eExt : CochainComplex.HomComplex.CohomologyClass L' I' i ≃
      DerivedCategory.Ext (DerivedCategory.Q.obj L) K i :=
    eExtUL.trans <|
      (Functor.FullyFaithful.homEquiv (F := eDer.functor)
        (hF := eDer.fullyFaithfulFunctor)).trans
        (CategoryTheory.Iso.homCongr eL eShift)
  let eExtAdd : CochainComplex.HomComplex.CohomologyClass L' I' i ≃+
      DerivedCategory.Ext (DerivedCategory.Q.obj L) K i := by
    let eQhIsoAdd : _ ≃+ _ := by
      let φ : _ →+ _ := {
        toFun := fun f => eLQh.inv ≫ f ≫ eIQh.hom
        map_zero' := by simp
        map_add' := by
          intro x y
          simp [Preadditive.comp_add, Preadditive.add_comp]
      }
      exact AddEquiv.ofBijective φ (eLQh.homCongr eIQh).bijective
    let eQhAdd : (qUL.obj L' ⟶ qUL.obj (I'⟦i⟧)) ≃+
        (DerivedCategory.Q.obj L' ⟶ (DerivedCategory.Q.obj I')⟦i⟧) :=
      (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
        (CochainComplex.IsKInjective.Qh_map_bijective (qUL.obj L') (I'⟦i⟧))).trans
        eQhIsoAdd
    let eULAdd := (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
        (K := L') (L := I') (n := i)).trans eQhAdd
    let eDerAdd : _ ≃+ _ := by
      let f := eDer.fullyFaithfulFunctor.homEquiv
        (X := DerivedCategory.Q.obj L') (Y := (DerivedCategory.Q.obj I')⟦i⟧)
      refine { f with map_add' := ?_ }
      intro x y
      simp [f]
    let eShiftAdd : _ ≃+ _ := by
      let φ : _ →+ _ := {
        toFun := fun f => eL.inv ≫ f ≫ eShift.hom
        map_zero' := by simp
        map_add' := by
          intro x y
          simp [Preadditive.comp_add, Preadditive.add_comp]
      }
      exact AddEquiv.ofBijective φ (eL.homCongr eShift).bijective
    exact eULAdd.trans (eDerAdd.trans eShiftAdd)
  let eFact : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (eDer.functor.obj (DerivedCategory.Q.obj H)) ≅
        ModuleCat.of A ((eComplex.functor.obj H).homology i) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (eMod.functor.mapDerivedCategoryFactors.app H) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app
        (eComplex.functor.obj H)
  let eHmod : (eComplex.functor.obj H).homology i ≅
      eMod.functor.obj (ModuleCat.of (ULift.{u} A) (H.homology i)) :=
    (H.sc i).mapHomologyIso eMod.functor
  let eH := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eModel ≪≫
    eFact ≪≫ eHmod
  let eHC := Dualizing.LocalDuality.homComplexRHomologyAddEquiv L' I' i
  let eClassHom := CochainComplex.HomComplex.CohomologyClass.homAddEquiv
    (K := L') (L := I') (n := i)
  letI : Module (ULift.{u} A) (CochainComplex.HomComplex.CohomologyClass L' I' i) :=
    eClassHom.module (ULift.{u} A)
  let eHCLinear : H.homology i ≃ₗ[ULift.{u} A]
      CochainComplex.HomComplex.CohomologyClass L' I' i :=
    eHC.toLinearEquiv (by
      intro r x
      let S := H.sc i
      obtain ⟨z, hz⟩ :=
        CochainComplex.HomComplex.CohomologyClass.mk_surjective (eHC x)
      let cyc : H.cycles i := H.cyclesMk z.val (i + 1) (by simp)
        (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _)
      let y := H.homologyπ i cyc
      have hy := Dualizing.LocalDuality.homComplexRHomologyAddEquiv_cyclesMk L' I' i z
      have hx : x = y := eHC.injective (hz.symm.trans hy.symm)
      have hsmul : r • y = H.homologyπ i
          (H.cyclesMk (r • z).val (i + 1) (by simp)
            (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _)) := by
        dsimp [y, S]
        change r • (H.homologyπ i).hom cyc =
          (H.homologyπ i).hom
            (S.cyclesMk (r • z).val
              (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _))
        rw [← (H.homologyπ i).hom.map_smul]
        congr 1
        apply (ModuleCat.mono_iff_injective (H.iCycles i)).mp inferInstance
        rw [(H.iCycles i).hom.map_smul]
        have hz := HomologicalComplex.i_cyclesMk H z.val (i + 1) (by simp)
          (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _)
        have hrz := HomologicalComplex.i_cyclesMk H (r • z).val (i + 1) (by simp)
          (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _)
        have hz' : (H.iCycles i).hom cyc = z.val := by
          dsimp [cyc]
          simpa [HomologicalComplex.cyclesMk, ConcreteCategory.forget₂_comp_apply] using hz
        have hrz' : (H.iCycles i).hom
              (H.cyclesMk (r • z).val (i + 1) (by simp)
                (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _)) = (r • z).val := by
          simpa [HomologicalComplex.cyclesMk, ConcreteCategory.forget₂_comp_apply] using hrz
        change r • (H.iCycles i).hom cyc = (H.iCycles i).hom
          (H.cyclesMk (r • z).val (i + 1) (by simp)
            (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _))
        rw [hz', hrz', CochainComplex.HomComplex.Cocycle.coe_smul]
        rfl
      have hmk : r • CochainComplex.HomComplex.CohomologyClass.mk z =
          CochainComplex.HomComplex.CohomologyClass.mk (r • z) := by
        apply eClassHom.injective
        let eClassLinear := eClassHom.linearEquiv (ULift.{u} A)
        have heq := eClassLinear.map_smul r
          (CochainComplex.HomComplex.CohomologyClass.mk z)
        change eClassHom (r • CochainComplex.HomComplex.CohomologyClass.mk z) =
          r • eClassHom (CochainComplex.HomComplex.CohomologyClass.mk z) at heq
        rw [heq]
        change r • CochainComplex.HomComplex.CohomologyClass.toHom
            (CochainComplex.HomComplex.CohomologyClass.mk z) =
          CochainComplex.HomComplex.CohomologyClass.toHom
            (CochainComplex.HomComplex.CohomologyClass.mk (r • z))
        rw [CochainComplex.HomComplex.CohomologyClass.toHom_mk,
          CochainComplex.HomComplex.CohomologyClass.toHom_mk,
          ← Functor.map_smul]
        have hshift : CochainComplex.HomComplex.Cocycle.equivHomShift.symm (r • z) =
            r • CochainComplex.HomComplex.Cocycle.equivHomShift.symm z := by
          apply CochainComplex.HomComplex.Cocycle.equivHomShift.injective
          ext p q hpq x
          rfl
        rw [← hshift]
      have hrep := Dualizing.LocalDuality.homComplexRHomologyAddEquiv_cyclesMk L' I' i (r • z)
      have hrep' : eHC (H.homologyπ i
          (H.cyclesMk (r • z).val (i + 1) (by simp)
            (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _))) =
          CochainComplex.HomComplex.CohomologyClass.mk (r • z) := by
        simpa [HomologicalComplex.cyclesMk] using hrep
      have hclass : eHC y = CochainComplex.HomComplex.CohomologyClass.mk z := by
        change Dualizing.LocalDuality.homComplexRHomologyAddEquiv L' I' i
          (H.homologyπ i
            (H.cyclesMk z.val (i + 1) (by simp)
              (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _))) = _
        exact Dualizing.LocalDuality.homComplexRHomologyAddEquiv_cyclesMk L' I' i z
      rw [hx, hsmul, hclass, hmk]
      exact hrep')
  let eHUL : ↑(eMod.functor.obj (ModuleCat.of (ULift.{u} A) (H.homology i))) ≃ₗ[ULift.{u} A]
      ↑((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), K))) := {
    toAddEquiv := eH.toLinearEquiv.toAddEquiv.symm
    map_smul' := by
      intro r x
      simp
  }
  let eCoh : CochainComplex.HomComplex.CohomologyClass L' I' i ≃ₗ[ULift.{u} A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), K)) : Type (u)) :=
    eHCLinear.symm.trans eHUL
  letI : Module (ULift.{u} A) (DerivedCategory.Ext (DerivedCategory.Q.obj L) K i) :=
    Module.compHom _ (ULift.ringEquiv.toRingHom)
  let eExtLin : CochainComplex.HomComplex.CohomologyClass L' I' i ≃ₗ[ULift.{u} A]
      DerivedCategory.Ext (DerivedCategory.Q.obj L) K i :=
    eExtAdd.toLinearEquiv (by
      intro r f
      let eClassLinear := eClassHom.linearEquiv (ULift.{u} A)
      have hsClass :
          CochainComplex.HomComplex.CohomologyClass.homAddEquiv
              (K := L') (L := I') (n := i) (r • f) =
            r • CochainComplex.HomComplex.CohomologyClass.homAddEquiv
              (K := L') (L := I') (n := i) f := by
        change eClassLinear (r • f) = r • eClassLinear f
        exact eClassLinear.map_smul r f
      change eExt (r • f) = r • eExt f
      dsimp [eExt]
      dsimp [eExtUL]
      rw [hsClass]
      dsimp [eQhUL]
      simp [Functor.map_smul, Linear.comp_smul, Linear.smul_comp]
      rfl)
  let eLinearUL : DerivedCategory.Ext (DerivedCategory.Q.obj L) K i ≃ₗ[ULift.{u} A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (d.hom.obj (Opposite.op (DerivedCategory.Q.obj L), K)) : Type (u)) :=
    eExtLin.symm.trans eCoh
  exact eLinearUL.toAddEquiv.toLinearEquiv (by
    intro r x
    exact eLinearUL.map_smul (ULift.ringEquiv.symm r) x)

private noncomputable def extDualCohomologyLinearEquiv
    {A : Type u} [CommRing A]
    (K ω : DerivedCategory (ModuleCat.{u} A))
    (hω : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension ω) (i : ℤ) :
    DerivedCategory.Ext K ω i ≃ₗ[A]
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K)) := by
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  exact (CategoryTheory.Linear.homCongr A e.symm (Iso.refl _)).trans
    ((homologyExtEquiv.{u} ω hω L i).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).mapIso e.symm.op)).toLinearEquiv)

private theorem finite_ext_of_isDualizingComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K))
    (i : ℤ) : Module.Finite A (DerivedCategory.Ext K ω i) := by
  let L := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let φ : DerivedCategory.Ext K ω i ≃ₗ[A] DerivedCategory.Ext (DerivedCategory.Q.obj L) ω i :=
    CategoryTheory.Linear.homCongr A e.symm (Iso.refl _)
  have hL : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        (DerivedCategory.Q.obj L)) := by
    intro j
    have := hK j
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).mapIso e).symm.toLinearEquiv
  have := Dualizing.dualizingDerivedHom_finiteCohomology.{u, u} A ω hω
    (DerivedCategory.Q.obj L) hL i
  exact Module.Finite.equiv ((φ.trans (homologyExtEquiv ω hω.finiteInjectiveDimension L i)).symm)

/-- **Stacks Project, Tag 0AAK** in the spelling of local cohomology with support in `V(𝔪)`.
Over a Noetherian local ring with a normalized dualizing complex, the `𝔪`-adic completion of
`Ext^{-i}(K, ω)` is the Matlis dual of `H^i_{V(𝔪)}(K)`. -/
@[stacks 0AAK "the module form, with the support-closed-subset model of local cohomology in \
place of the torsion-complex model"]
theorem nonempty_adicCompletion_ext_linearEquiv_matlisDual_localCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K ω : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K))
    (hω : Dualizing.IsNormalizedDualizingComplex ω)
    (E : ModuleCat.{u} A)
    (e : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono e] (he : Module.IsInjectiveHull e) (i : ℤ) :
    Nonempty
      (AdicCompletion (maximalIdeal A) (DerivedCategory.Ext K ω (-i)) ≃ₗ[A]
        (localCohomologyWithSupportIn
          A (PrimeSpectrum.zeroLocus (maximalIdeal A : Set A)) K i →ₗ[A] E)) := by
  have : Injective E := he.1
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (maximalIdeal A))
  obtain ⟨ψ⟩ :=
    Dualizing.LocalDuality.nonempty_adicCompletion_ext_linearEquiv_linearMap_localCohomology
      A f hf ω hω K hK e he i
  have hIso : IsIso ((compareSectionsWithSupportLocalCohomology.{u, u}
      A (maximalIdeal A) (IsNoetherian.noetherian _)).app K) :=
    isIso_compareSectionsWithSupportLocalCohomology_app.{u, u}
      A (maximalIdeal A) (IsNoetherian.noetherian _) K
  let cmp : localCohomologyWithSupportIn A
        (PrimeSpectrum.zeroLocus (maximalIdeal A : Set A)) K i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((Dualizing.derivedPowerTorsionProperty A (maximalIdeal A)
            (IsNoetherian.noetherian _)).ι.obj
          ((Dualizing.localCohomologyFunctor A (maximalIdeal A)
            (IsNoetherian.noetherian _)).obj K)) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (@asIso _ _ _ _ _ hIso)
  exact ⟨ψ.trans (LinearEquiv.arrowCongr cmp.toLinearEquiv.symm (LinearEquiv.refl A E))⟩

/-- **Stacks Project, Tag 0AAK** for a bounded-below complex. -/
@[stacks 0AAK "the module form for a bounded-below complex, with the support-closed-subset \
model of local cohomology"]
theorem nonempty_adicCompletion_ext_linearEquiv_matlisDual_localCohomologyPlus
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) j).obj K))
    (hω : Dualizing.IsNormalizedDualizingComplex ω)
    (E : ModuleCat.{u} A)
    (e : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono e] (he : Module.IsInjectiveHull e) (i : ℤ) :
    Nonempty
      (AdicCompletion (maximalIdeal A) (DerivedCategory.Ext K.obj ω (-i)) ≃ₗ[A]
        (localCohomologyWithSupportInPlus
          A (PrimeSpectrum.zeroLocus (maximalIdeal A : Set A)) K i →ₗ[A] E)) := by
  obtain ⟨φ⟩ := nonempty_adicCompletion_ext_linearEquiv_matlisDual_localCohomology
    A K.obj ω hK hω E e he i
  exact ⟨φ.trans (LinearEquiv.arrowCongr
    (localCohomologyPlusIso A (PrimeSpectrum.zeroLocus (maximalIdeal A : Set A))
      K i).symm.toLinearEquiv (LinearEquiv.refl A E))⟩

private theorem annihilator_ext_eq_localCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K ω : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K))
    (hω : Dualizing.IsNormalizedDualizingComplex ω)
    (E : ModuleCat.{u} A)
    (e : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono e] (he : Module.IsInjectiveHull e) (i : ℤ) :
    Module.annihilator A (DerivedCategory.Ext K ω (-i)) =
      Module.annihilator A
        (localCohomologyWithSupportIn
          A (PrimeSpectrum.zeroLocus (maximalIdeal A : Set A)) K i) := by
  have : Injective E := he.1
  have := finite_ext_of_isDualizingComplex ω hω.1 K hK (-i)
  obtain ⟨φ⟩ := nonempty_adicCompletion_ext_linearEquiv_matlisDual_localCohomology
    A K ω hK hω E e he i
  exact (annihilator_adicCompletion (maximalIdeal A) _).symm.trans
    ((annihilator_eq_of_linearEquiv φ).trans (annihilator_matlisDual A _ E e))

private theorem annihilator_ext_eq_localCohomologyPlus
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) j).obj K))
    (hω : Dualizing.IsNormalizedDualizingComplex ω)
    (E : ModuleCat.{u} A)
    (e : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono e] (he : Module.IsInjectiveHull e) (i : ℤ) :
    Module.annihilator A (DerivedCategory.Ext K.obj ω (-i)) =
      Module.annihilator A
        (localCohomologyWithSupportInPlus
          A (PrimeSpectrum.zeroLocus (maximalIdeal A : Set A)) K i) :=
  (annihilator_ext_eq_localCohomology A K.obj ω hK hω E e he i).trans
    (annihilator_eq_of_linearEquiv
      (localCohomologyPlusIso A (PrimeSpectrum.zeroLocus (maximalIdeal A : Set A))
        K i).symm.toLinearEquiv)

private theorem finite_extendScalars
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    (f : A →+* B) (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite B ((ModuleCat.extendScalars.{u, w, u} f).obj M) := by
  let : Algebra A B := f.toAlgebra
  have heq : (inferInstance : Module A B) = Module.compHom B f :=
    Module.ext' _ _ (by intro a b; rfl)
  cases heq
  exact Module.Finite.base_change A B M

private theorem finite_homology_flatExtension
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      extendScalars_preservesFiniteLimits_of_flat' _ hf
    ∀ i : ℤ, Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        ((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory.obj K)) := by
  let F := ModuleCat.extendScalars.{u, u, u} f
  let : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _ hf
  intro i
  have := hK i
  have : Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ⋙ F).obj K) :=
    finite_extendScalars f ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)
  exact Module.Finite.equiv
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso F i).app K).symm.toLinearEquiv

private theorem finite_homology_localizedComplex
    {A : Type u} [CommRing A] (p : PrimeSpectrum A)
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (i : ℤ) : Module.Finite (Localization.AtPrime p.asIdeal)
      ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat.{u} (Localization.AtPrime p.asIdeal)) i).obj
          (localizedComplex.{u, u} p K)) :=
  finite_homology_flatExtension (algebraMap A (Localization.AtPrime p.asIdeal))
    (RingHom.flat_algebraMap_iff.mpr inferInstance) K.obj hK i

noncomputable def derivedExtensionScalarsIsoMap
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) :
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max u v} f) :=
      extendScalars_preservesFiniteLimits_of_flat' _ hf
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u} f).functor ≅
      (ModuleCat.extendScalars.{u, u, max u v} f).mapDerivedCategory := by
  let F := ModuleCat.extendScalars.{u, u, max u v} f
  letI : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _ hf
  let D := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u} f
  let W := HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)
  exact @Functor.leftDerivedUnique _ _ _ _ _ _ F.mapDerivedCategory D.functor _ _
    D.comparison F.mapDerivedCategoryFactors.hom W inferInstance D.isLeftDerived
    (Functor.isLeftDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactors)

theorem isDualizingComplex_of_iso
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K L : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ L)
    (hK : Dualizing.IsDualizingComplex K) : Dualizing.IsDualizingComplex L := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
    exact ⟨a, b, I, hge, hle, hinj, ⟨e.symm ≪≫ eI⟩⟩
  · intro i
    have := hK.finiteCohomology i
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e).toLinearEquiv
  · intro I hI hinj hb
    exact hK.homothetyQuasiIso I ⟨hI.some ≪≫ e.symm⟩ hinj hb

private noncomputable def uliftDerivedObjIso
    (A : Type u) [CommRing A] (K : DerivedCategory (ModuleCat.{u} A)) :
    (ModuleCat.uliftFunctor.{u, u} A).mapDerivedCategory.obj K ≅ K := by
  let U := ModuleCat.uliftFunctor.{u, u} A
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  let eL : (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ L :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (ULift.moduleEquiv : ULift.{u} (L.X i) ≃ₗ[A] L.X i).toModuleIso)
      (fun i j h => by ext x; rfl)
  exact U.mapDerivedCategory.mapIso e.symm ≪≫ U.mapDerivedCategoryFactors.app L ≪≫
    DerivedCategory.Q.mapIso eL ≪≫ e

private noncomputable def pseudoExtensionScalarsObjIsoMap
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (K : DerivedCategory (ModuleCat.{u} A)) :
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      extendScalars_preservesFiniteLimits_of_flat' _ hf
    (StacksDraft.PseudoCoherence.derivedExtensionScalars f).obj K ≅
      (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory.obj K := by
  let F := ModuleCat.extendScalars.{u, u, u} f
  letI : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' _ hf
  exact (derivedExtensionScalarsIsoMap.{u, u} f hf).app _ ≪≫
    F.mapDerivedCategory.mapIso (uliftDerivedObjIso A K)

theorem isDualizingComplex_localizedMap
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (q : PrimeSpectrum A) (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : Dualizing.IsDualizingComplex ω) :
    let B := Localization.AtPrime q.asIdeal
    letI : IsNoetherianRing B :=
      IsLocalization.isNoetherianRing q.asIdeal.primeCompl B inferInstance
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
      extendScalars_preservesFiniteLimits_of_flat' _ (RingHom.flat_algebraMap_iff.mpr inferInstance)
    Dualizing.IsDualizingComplex
      ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory.obj ω) := by
  let B := Localization.AtPrime q.asIdeal
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing q.asIdeal.primeCompl B inferInstance
  have hf : (algebraMap A B).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  exact isDualizingComplex_of_iso (pseudoExtensionScalarsObjIsoMap (algebraMap A B) hf ω)
    (Dualizing.isDualizingComplex_localization q.asIdeal.primeCompl ω hω)

private noncomputable def flatDerivedDualIsoOfPseudoCoherent
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat)
    (K ω : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hω : ∃ a : ℤ, ω.IsGE a) :
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      extendScalars_preservesFiniteLimits_of_flat' _ hf
    let F := (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory
    F.obj ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K)) ≅
      (Dualizing.dualizingDerivedHomFunctor.{u, u} B (F.obj ω)).obj (.op (F.obj K)) := by
  let G := ModuleCat.extendScalars.{u, u, u} f
  letI : PreservesFiniteLimits G := extendScalars_preservesFiniteLimits_of_flat' _ hf
  let F := G.mapDerivedCategory
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
  letI : F.IsLeftDerivedFunctor G.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F G.mapDerivedCategoryFactors
  letI : G.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj f).isLeftAdjoint
  letI : (ModuleCat.restrictScalars.{u} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj f).isRightAdjoint
  letI : (ModuleCat.restrictScalars.{u} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj f).isLeftAdjoint
  let t := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u}
    f F G.mapDerivedCategoryFactors.hom K ω
  have ht : IsIso t := Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, u}
    f F G.mapDerivedCategoryFactors.hom K ω (Or.inr (Or.inr (Or.inl ⟨hf, hK, hω⟩)))
  exact @asIso _ _ _ _ t ht

private noncomputable def dualizingBidualIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    K ≅ (Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj
      (.op ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K))) :=
  (ObjectProperty.ι _).mapIso
    ((Dualizing.coherentDerivedBidualityIso.{u, u} A ω hω).app ⟨K, hK⟩)

theorem boundedBelow_of_isDualizingComplex
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω) :
    ∃ a : ℤ, ω.IsGE a := by
  obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hω.finiteInjectiveDimension
  refine ⟨a, ?_⟩
  exact DerivedCategory.TStructure.t.isGE_of_iso eI.symm a

private noncomputable def flatDerivedDualIsoOfBoundedBelow
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : f.Flat)
    (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω) :
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      extendScalars_preservesFiniteLimits_of_flat' _ hf
    let F := (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory
    Dualizing.IsDualizingComplex (F.obj ω) →
    (F.obj ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K.obj)) ≅
      (Dualizing.dualizingDerivedHomFunctor.{u, u} B (F.obj ω)).obj (.op (F.obj K.obj))) := by
  dsimp only
  intro hωB
  apply Classical.choice
  let G := ModuleCat.extendScalars.{u, u, u} f
  let : PreservesFiniteLimits G := extendScalars_preservesFiniteLimits_of_flat' _ hf
  let F := G.mapDerivedCategory
  let D := Dualizing.dualizingDerivedHomFunctor.{u, u} A ω
  let D' := Dualizing.dualizingDerivedHomFunctor.{u, u} B (F.obj ω)
  let L := D.obj (.op K.obj)
  have hL := Dualizing.dualizingDerivedHom_finiteCohomology.{u, u} A ω hω K.obj hK
  obtain ⟨b, hb⟩ :=
    (Dualizing.dualizingDerivedHom_plus_iff_minus.{u, u} A ω hω K.obj hK).mp K.property
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent L :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology L 0
      (ULift.{u} A)).2.1.mpr ⟨⟨b, (DerivedCategory.isLE_iff _ b).mp hb⟩, hL⟩
  let eK : F.obj K.obj ≅ D'.obj (.op (F.obj L)) :=
    F.mapIso (dualizingBidualIso A ω hω K.obj hK) ≪≫
      flatDerivedDualIsoOfPseudoCoherent f hf L ω hpc (boundedBelow_of_isDualizingComplex A ω hω)
  exact ⟨dualizingBidualIso B (F.obj ω) hωB (F.obj L)
    (finite_homology_flatExtension f hf L hL) ≪≫ D'.mapIso eK.op⟩

private noncomputable def localizedDualCohomologyLinearEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (q : PrimeSpectrum A) (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (i : ℤ) :
    let B := Localization.AtPrime q.asIdeal
    letI : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
      extendScalars_preservesFiniteLimits_of_flat' _ (RingHom.flat_algebraMap_iff.mpr inferInstance)
    LocalizedModule q.asIdeal.primeCompl
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K.obj))) ≃ₗ[B]
      DerivedCategory.Ext (localizedComplex.{u, u} q K).obj
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A B)).mapDerivedCategory.obj ω) i := by
  let B := Localization.AtPrime q.asIdeal
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing q.asIdeal.primeCompl B inferInstance
  let f := algebraMap A B
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let G := ModuleCat.extendScalars.{u, u, u} f
  letI : PreservesFiniteLimits G := extendScalars_preservesFiniteLimits_of_flat' _ hf
  let F := G.mapDerivedCategory
  let L := (Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K.obj)
  let E := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj L
  have hωB := isDualizingComplex_localizedMap q ω hω
  let eL := flatDerivedDualIsoOfBoundedBelow f hf K hK ω hω hωB
  let e₁ := (IsLocalizedModule.isBaseChange q.asIdeal.primeCompl B
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl E)).equiv.symm
  let e₂ := (StacksDraft.PseudoCoherence.extendScalarsTensorIso (S := B) E).symm ≪≫
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso G i).app L).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso eL
  exact e₁.trans (e₂.toLinearEquiv.trans
    (extDualCohomologyLinearEquiv (F.obj K.obj) (F.obj ω) hωB.finiteInjectiveDimension i).symm)

/-- `Ext^n(X, ω) ≃ Ext^{-i}(X, ω'⟦-δ⟧)` for `ω ≅ ω'` and `-δ + -i = n`. -/
private noncomputable def extShiftLinearEquiv
    {B : Type u} [CommRing B] (X ω ω' : DerivedCategory (ModuleCat.{u} B)) (e : ω ≅ ω')
    (δ n i : ℤ) (h : -δ + -i = n) :
    DerivedCategory.Ext X ω n ≃ₗ[B] DerivedCategory.Ext X (ω'⟦-δ⟧) (-i) :=
  CategoryTheory.Linear.homCongr B (Iso.refl _)
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} B)) n).mapIso e ≪≫
      (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} B)) (-δ) (-i) n h).app ω')

theorem annihilator_localizedDualCohomology_eq_localCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (q : PrimeSpectrum A) (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (i : ℤ) :
    Module.annihilator (Localization.AtPrime q.asIdeal)
      (LocalizedModule q.asIdeal.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K.obj)))) =
    Module.annihilator (Localization.AtPrime q.asIdeal)
      (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
        (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
        (localizedComplex.{u, u} q K) (-Dualizing.dualizingDimension ω q - i)) := by
  let B := Localization.AtPrime q.asIdeal
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing q.asIdeal.primeCompl B inferInstance
  let f := algebraMap A B
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let G := ModuleCat.extendScalars.{u, u, u} f
  let : PreservesFiniteLimits G := extendScalars_preservesFiniteLimits_of_flat' _ hf
  let ωB := G.mapDerivedCategory.obj ω
  let ωP := (StacksDraft.PseudoCoherence.derivedExtensionScalars f).obj ω
  let δ := Dualizing.dualizingDimension ω q
  let j := -δ - i
  let eω : ωB ≅ ωP := (pseudoExtensionScalarsObjIsoMap f hf ω).symm
  let eExt := extShiftLinearEquiv (localizedComplex.{u, u} q K).obj ωB ωP eω δ i j
    (by dsimp [j]; omega)
  obtain ⟨E, e, he, hE⟩ := Module.exists_isInjectiveHull B
    ((ModuleCat.uliftFunctor.{u} B).obj (ModuleCat.of B (ResidueField B)))
  let : Mono e := he
  have hn := Dualizing.dualizingDimension_spec ω hω q
  exact ((localizedDualCohomologyLinearEquiv q K hK ω hω i).annihilator_eq.trans
    eExt.annihilator_eq).trans
      (annihilator_ext_eq_localCohomologyPlus B (localizedComplex.{u, u} q K) (ωP⟦-δ⟧)
        (finite_homology_localizedComplex q K hK) hn E e hE j)

/-- **Local duality at an arbitrary prime.** Let `A` be Noetherian with dualizing complex `ω`
and dimension function `δ`, let `q` be a prime, and let `E` be an injective hull of the residue
field of `A_q`. For `K` in `D⁺_{Coh}(A)` and `n + i = -δ(q)`, the `qA_q`-adic completion of
`H^n(RHom_A(K, ω))_q` is the Matlis dual of `H^i_{qA_q}(K_q)`.

This is [Stacks, Tag 0AAK] at a general prime: the localization `ω_q⟦-δ(q)⟧` is a normalized
dualizing complex over `A_q` by [Stacks, Tag 0A7Z], and flat base change identifies
`H^n(RHom_A(K, ω))_q` with `Ext^n_{A_q}(K_q, ω_q)`. It is the local-duality input to the proof
of [Stacks, Tag 0EFX]. The two sides are isomorphic as `A_q`-modules for each `K` separately;
no naturality in `K` is claimed, and 0AAK provides none. -/
@[stacks 0AAK "local duality at an arbitrary prime of a Noetherian ring with a dualizing \
complex, reached from the local case through the normalizing shift of 0A7Z and flat base change \
of Ext; objectwise, with no naturality in the complex"]
theorem nonempty_adicCompletion_localizedDualCohomology_linearEquiv_matlisDual
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (q : PrimeSpectrum A) (K : DerivedCategory.Plus (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsDualizingComplex ω)
    (E : ModuleCat.{u} (Localization.AtPrime q.asIdeal))
    (e : (ModuleCat.uliftFunctor.{u} (Localization.AtPrime q.asIdeal)).obj
      (ModuleCat.of (Localization.AtPrime q.asIdeal)
        (ResidueField (Localization.AtPrime q.asIdeal))) ⟶ E)
    [Mono e] (he : Module.IsInjectiveHull e)
    (n i : ℤ) (hni : n + i = -Dualizing.dualizingDimension ω q) :
    Nonempty
      (AdicCompletion (maximalIdeal (Localization.AtPrime q.asIdeal))
          (LocalizedModule q.asIdeal.primeCompl
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
              ((Dualizing.dualizingDerivedHomFunctor.{u, u} A ω).obj (.op K.obj))))
          ≃ₗ[Localization.AtPrime q.asIdeal]
        (localCohomologyWithSupportInPlus (Localization.AtPrime q.asIdeal)
          (PrimeSpectrum.zeroLocus (maximalIdeal (Localization.AtPrime q.asIdeal) : Set _))
          (localizedComplex.{u, u} q K) i →ₗ[Localization.AtPrime q.asIdeal] E)) := by
  let B := Localization.AtPrime q.asIdeal
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing q.asIdeal.primeCompl B inferInstance
  let f := algebraMap A B
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let G := ModuleCat.extendScalars.{u, u, u} f
  let : PreservesFiniteLimits G := extendScalars_preservesFiniteLimits_of_flat' _ hf
  let ωB := G.mapDerivedCategory.obj ω
  let ωP := (StacksDraft.PseudoCoherence.derivedExtensionScalars f).obj ω
  let δ := Dualizing.dualizingDimension ω q
  let eω : ωB ≅ ωP := (pseudoExtensionScalarsObjIsoMap f hf ω).symm
  let eExt := extShiftLinearEquiv (localizedComplex.{u, u} q K).obj ωB ωP eω δ n i
    (by dsimp [δ]; omega)
  have hn := Dualizing.dualizingDimension_spec ω hω q
  obtain ⟨φ⟩ := nonempty_adicCompletion_ext_linearEquiv_matlisDual_localCohomologyPlus
    B (localizedComplex.{u, u} q K) (ωP⟦-δ⟧)
    (finite_homology_localizedComplex q K hK) hn E e he i
  exact ⟨((AdicCompletion.congr (maximalIdeal B)
    ((localizedDualCohomologyLinearEquiv q K hK ω hω n).trans eExt)).restrictScalars B).trans φ⟩

end Stacks.LocalCohomology
