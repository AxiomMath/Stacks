module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.CechReflection
public import StacksFrontier.Homology.DerivedComplete.NoetherianCohomologyAdicCompletion
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDuality
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.DerivedHomCompletionTorsion
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated
import StacksFrontier.Algebra.Homology.DerivedCategory.HomToInjectiveSingle

/-!
# Local duality between completed Ext and the Matlis dual of local cohomology

Let `(A, 𝔪, κ)` be a Noetherian local ring, let `ω` be a normalized dualizing complex, let `E`
be an injective hull of the residue field, and let `K` be an object of `D_Coh(A)`. Local duality
in its module form is the identification

`Ext^{-i}_A(K, ω)^∧ = Hom_A(H^i_𝔪(K), E)`

of the `𝔪`-adic completion of a negative Ext module with the Matlis dual of a local cohomology
module. Here local cohomology at `𝔪` is `RΓ_Z` for `Z = V(𝔪)`.

For arbitrary `K` in `D(A)` there are `A`-linear isomorphisms

`H^0(RHom_A(K, ω⟦-i⟧)^∧) ≅ Hom_A(H^i_𝔪(K), E)`

natural in `K`, whose left-hand side is `Ext^{-i}_A(K, ω)` before derived completion. Composed
with the derived-completion unit they give the local duality map
`Ext^{-i}_A(K, ω) ⟶ Hom_A(H^i_𝔪(K), E)`, natural in `K`.

## Main results

* `Dualizing.LocalDuality.nonempty_adicCompletion_ext_linearEquiv_linearMap_localCohomology` —
  [Stacks, Tag 0AAK], the module form of local duality.
* `Dualizing.LocalDuality.exists_localDualityExtNatEquiv` — [Stacks, Tag 0AAK] natural in `K`.
* `Dualizing.LocalDuality.exists_natural_extToMatlisDualMap` — the local duality map
  `Ext^{-i}_A(K, ω) ⟶ Hom_A(H^i_𝔪(K), E)`, with its naturality square.
* `Dualizing.LocalDuality.extHomologyZeroLinearEquiv` — `Hom_{D(A)}(Y, N) ≅ H^0(RHom_A(Y, N))`,
  natural in `Y`.
* `Dualizing.LocalDuality.homologySingleLinearEquiv` and
  `Dualizing.LocalDuality.bijective_homologyToSingleLinearMap` — maps into an injective module
  placed in degree `i` are detected on degree-`i` cohomology, by the evaluation map
  `Dualizing.LocalDuality.homologyToSingleLinearMap`, which is natural in the source.
* `Dualizing.LocalDuality.derivedHomAdjunction_map_smul_id_left` — the canonical derived-Hom
  bifunctor is `A`-linear in its source variable.

## References

* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
* [Stacks Project, Tag 0A84](https://stacks.math.columbia.edu/tag/0A84)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 0A64](https://stacks.math.columbia.edu/tag/0A64)
* [Stacks Project, Tag 0G3E](https://stacks.math.columbia.edu/tag/0G3E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing.LocalDuality

/-- The degree-`n` cohomology of the Hom complex of `R`-modules is the group of degree-`n`
cohomology classes of the underlying Hom complex of abelian groups. -/
noncomputable def homComplexRHomologyAddEquiv {R : Type u} [CommRing R]
    (P F : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (CochainComplex.HomComplexR R P F).homology n ≃+
      CochainComplex.HomComplex.CohomologyClass P F n :=
  (((CochainComplex.HomComplexR R P F).sc n).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).symm.addCommGroupIsoToAddEquiv.trans
    (CochainComplex.HomComplex.homologyAddEquiv P F n)

/-- The homology class of a cycle, computed through a left homology datum of a short complex of
abelian groups. -/
lemma homologyIso_cyclesMk (S : ShortComplex Ab.{w})
    (h : S.LeftHomologyData) (y : h.K) (x : S.X₂) (hx : S.g x = 0)
    (hy : h.i y = x) :
    h.homologyIso.hom (S.homologyπ (S.abCyclesIso.inv ⟨x, hx⟩)) = h.π y := by
  have hcy : h.cyclesIso.hom (S.abCyclesIso.inv ⟨x, hx⟩) = y := by
    apply (AddCommGrpCat.mono_iff_injective h.i).mp inferInstance
    have hi := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i
      (S.abCyclesIso.inv ⟨x, hx⟩)
    exact hi.trans ((S.abCyclesIso_inv_apply_iCycles ⟨x, hx⟩).trans hy.symm)
  have hi := ConcreteCategory.congr_hom (h.homologyπ_comp_homologyIso_hom S)
    (S.abCyclesIso.inv ⟨x, hx⟩)
  simpa only [ConcreteCategory.comp_apply, hcy] using hi

/-- Forgetting the module structure sends the homology class of a cycle to the homology class of
the same element. -/
lemma mapHomologyIso_cyclesMk {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) (x : S.X₂) (hx : S.g x = 0) :
    (S.mapHomologyIso (forget₂ (ModuleCat.{u} R) Ab)).inv
        (S.homologyπ (S.cyclesMk x hx)) =
      (S.map (forget₂ (ModuleCat.{u} R) Ab)).homologyπ
        ((S.map (forget₂ (ModuleCat.{u} R) Ab)).abCyclesIso.inv ⟨x, hx⟩) := by
  let U := forget₂ (ModuleCat.{u} R) Ab
  let h := S.homologyData.left
  let k := h.map U
  rw [h.mapHomologyIso_eq U]
  show k.homologyIso.inv (h.homologyIso.hom (S.homologyπ (S.cyclesMk x hx))) = _
  have hh := ConcreteCategory.congr_hom (h.homologyπ_comp_homologyIso_hom S)
    (S.cyclesMk x hx)
  change h.homologyIso.hom (S.homologyπ (S.cyclesMk x hx)) =
    h.π (h.cyclesIso.hom (S.cyclesMk x hx)) at hh
  rw [hh]
  apply (ConcreteCategory.bijective_of_isIso k.homologyIso.hom).1
  have hcancel := ConcreteCategory.congr_hom k.homologyIso.inv_hom_id
    (h.π (h.cyclesIso.hom (S.cyclesMk x hx)))
  change k.homologyIso.hom (k.homologyIso.inv _) = _ at hcancel
  rw [hcancel]
  symm
  apply homologyIso_cyclesMk
  have hi := ConcreteCategory.congr_hom h.cyclesIso_hom_comp_i (S.cyclesMk x hx)
  exact hi.trans (S.i_cyclesMk x hx)

/-- The identification of Hom-complex cohomology with cohomology classes sends the class of a
cocycle to that cocycle's class. -/
lemma homComplexRHomologyAddEquiv_cyclesMk {A : Type u} [CommRing A]
    (P F : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle P F n) :
    homComplexRHomologyAddEquiv P F n
      ((CochainComplex.HomComplexR A P F).homologyπ n
        (((CochainComplex.HomComplexR A P F).sc n).cyclesMk z.val
          (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _))) =
      CochainComplex.HomComplex.CohomologyClass.mk z := by
  let S := (CochainComplex.HomComplexR A P F).sc n
  show CochainComplex.HomComplex.homologyAddEquiv P F n
      ((S.mapHomologyIso (forget₂ (ModuleCat.{u} A) AddCommGrpCat)).inv
        (S.homologyπ (S.cyclesMk z.val
          (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _)))) =
    CochainComplex.HomComplex.CohomologyClass.mk z
  exact (congrArg (fun x => CochainComplex.HomComplex.homologyAddEquiv P F n x)
      (mapHomologyIso_cyclesMk S z.val
        (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _))).trans
    (homologyIso_cyclesMk _ (CochainComplex.HomComplex.leftHomologyData P F n)
      z z.val _ rfl)

/-- The degree-`i` cohomology module of `RHom_A(X, Y)` is `Hom_{D(A)}(X, Y⟦i⟧)`, the `A`-module
`Ext^i_A(X, Y)`. -/
private noncomputable def homologyDerivedHomLinearEquiv {A : Type u} [CommRing A]
    (X Y : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op X, Y)) : Type u) ≃ₗ[A] (X ⟶ Y⟦i⟧) := by
  classical
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let L := DerivedCategory.Q.objPreimage X
  let eL : DerivedCategory.Q.obj L ≅ X := DerivedCategory.Q.objObjPreimageIso X
  let hmod := CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage Y)
  let J : CochainComplex (ModuleCat.{u} A) ℤ := hmod.choose
  let f := hmod.choose_spec.choose
  haveI : QuasiIso f := hmod.choose_spec.choose_spec.choose
  haveI : J.IsKInjective := hmod.choose_spec.choose_spec.choose_spec
  let eJ : DerivedCategory.Q.obj J ≅ Y :=
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Y
  let H := CochainComplex.HomComplexR A L J
  let eModel : d.hom.obj (Opposite.op X, Y) ≅ DerivedCategory.Q.obj H :=
    d.hom.mapIso (eL.op.prod eJ.symm) ≪≫ d.homIso L J
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (d.hom.obj (Opposite.op X, Y)) ≅ H.homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eModel ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app H
  let q := HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)
  let eHC := homComplexRHomologyAddEquiv L J i
  let eClassHom := CochainComplex.HomComplex.CohomologyClass.homAddEquiv
    (K := L) (L := J) (n := i)
  letI : Module A (CochainComplex.HomComplex.CohomologyClass L J i) := eClassHom.module A
  let eClassLinear := eClassHom.linearEquiv A
  let eHCLinear : H.homology i ≃ₗ[A]
      CochainComplex.HomComplex.CohomologyClass L J i :=
    eHC.toLinearEquiv (by
      intro r x
      let S := H.sc i
      obtain ⟨z, hz⟩ :=
        CochainComplex.HomComplex.CohomologyClass.mk_surjective (eHC x)
      let cyc : H.cycles i := H.cyclesMk z.val (i + 1) (by simp)
        (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _)
      let y := H.homologyπ i cyc
      have hy := homComplexRHomologyAddEquiv_cyclesMk L J i z
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
        have hi (w : CochainComplex.HomComplex.Cocycle L J i) : (H.iCycles i).hom
            (H.cyclesMk w.val (i + 1) (by simp)
              (CochainComplex.HomComplex.Cocycle.δ_eq_zero w _)) = w.val := by
          simpa [HomologicalComplex.cyclesMk, ConcreteCategory.forget₂_comp_apply] using
            HomologicalComplex.i_cyclesMk H w.val (i + 1) (by simp)
              (CochainComplex.HomComplex.Cocycle.δ_eq_zero w _)
        change r • (H.iCycles i).hom cyc = (H.iCycles i).hom
          (H.cyclesMk (r • z).val (i + 1) (by simp)
            (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _))
        rw [hi z, hi (r • z), CochainComplex.HomComplex.Cocycle.coe_smul]
        rfl
      have hmk : r • CochainComplex.HomComplex.CohomologyClass.mk z =
          CochainComplex.HomComplex.CohomologyClass.mk (r • z) := by
        apply eClassHom.injective
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
      have hrep := homComplexRHomologyAddEquiv_cyclesMk L J i (r • z)
      have hrep' : eHC (H.homologyπ i
          (H.cyclesMk (r • z).val (i + 1) (by simp)
            (CochainComplex.HomComplex.Cocycle.δ_eq_zero (r • z) _))) =
          CochainComplex.HomComplex.CohomologyClass.mk (r • z) := by
        simpa [HomologicalComplex.cyclesMk] using hrep
      have hclass : eHC y = CochainComplex.HomComplex.CohomologyClass.mk z := by
        change homComplexRHomologyAddEquiv L J i
          (H.homologyπ i
            (H.cyclesMk z.val (i + 1) (by simp)
              (CochainComplex.HomComplex.Cocycle.δ_eq_zero z _))) = _
        exact homComplexRHomologyAddEquiv_cyclesMk L J i z
      rw [hx, hsmul, hclass, hmk]
      exact hrep')
  let eLQh := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app L
  let eJQh := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app (J⟦i⟧) ≪≫
    (DerivedCategory.Q.commShiftIso i).app J
  let eQh : (q.obj L ⟶ q.obj (J⟦i⟧)) ≃ₗ[A]
      (DerivedCategory.Q.obj L ⟶ (DerivedCategory.Q.obj J)⟦i⟧) :=
    (LinearEquiv.ofBijective (DerivedCategory.Qh.mapLinearMap A
        (X := q.obj L) (Y := q.obj (J⟦i⟧)))
      (CochainComplex.IsKInjective.Qh_map_bijective (q.obj L) (J⟦i⟧))).trans
      (Linear.homCongr A eLQh eJQh)
  exact eH.toLinearEquiv.trans (eHCLinear.trans (eClassLinear.trans (eQh.trans
    (Linear.homCongr A eL ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) i).mapIso eJ)))))

/-! ### Maps into a single injective object are detected on homology -/

section

open HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An injective object placed in a single degree is a K-injective complex. -/
private lemma isKInjective_singleFunctor_obj (E : C) [Injective E] (i : ℤ) :
    ((CochainComplex.singleFunctor C i).obj E).IsKInjective := by
  have : ((CochainComplex.singleFunctor C i).obj E).IsStrictlyGE i := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have (j : ℤ) : Injective (((CochainComplex.singleFunctor C i).obj E).X j) :=
    instInjectiveXObjSingle i j E
  exact CochainComplex.isKInjective_of_injective _ i

private lemma homology_to_single_surjective (K : CochainComplex C ℤ)
    (E : C) [Injective E] (i : ℤ) :
    Function.Surjective (fun f : K ⟶ (CochainComplex.singleFunctor C i).obj E =>
      homologyMap f i ≫ (singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom) := by
  simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  intro f
  let t := Injective.factorThru f (K.homologyι i)
  let g : K ⟶ (CochainComplex.singleFunctor C i).obj E :=
    mkHomToSingle (K.pOpcycles i ≫ t) (by intros; simp)
  refine ⟨g, ?_⟩
  apply (cancel_epi (K.homologyπ i)).mp
  rw [homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom, cyclesMap_i_assoc]
  dsimp [g]
  rw [mkHomToSingle_f]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← homology_π_ι, Category.assoc]
  exact congrArg (fun q => K.homologyπ i ≫ q) (Injective.comp_factorThru f (K.homologyι i))

/-- A chain map into an injective object in degree `i` that is zero on `Hⁱ` is null-homotopic. -/
private alias nullhomotopy_of_homology_to_single_zero :=
  CochainComplex.nonempty_homotopy_zero_of_homologyMap_eq_zero

private lemma complexHomology_linear (R : Type*) [Ring R] [Linear R C] (i : ℤ) :
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).Linear R where
  map_smul f r :=
    ShortComplex.homologyMap_smul ((shortComplexFunctor C (ComplexShape.up ℤ) i).map f) r

private noncomputable def homotopyHomologyToSingle (R : Type*) [Ring R] [Linear R C]
    (K : CochainComplex C ℤ) (E : C) (i : ℤ) :
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C i).obj E)) →ₗ[R] (K.homology i ⟶ E) := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i
  letI := complexHomology_linear (C := C) R i
  letI : H.Linear R := by
    have : (q ⋙ H).Linear R := Functor.linear_of_iso R
      (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).symm
    exact Functor.linear_of_full_essSurj_comp q H
  let eK := (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app K
  let eJ := (HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app
    ((CochainComplex.singleFunctor C i).obj E) ≪≫
      singleObjHomologySelfIso (ComplexShape.up ℤ) i E
  exact (Linear.homCongr R eK eJ).toLinearMap.comp (H.mapLinearMap R)

/-- Cancelling a retraction against a naturality square: if `v ≫ w = w' ≫ v'` and `u ≫ w'`
is the identity, then `(u ≫ v) ≫ (w ≫ t) = v' ≫ t`. -/
private lemma comp_naturality_cancel {D : Type*} [Category D] {X Y Y' Z T : D}
    (u : X ⟶ Y) (v : Y ⟶ Y') (w : Y' ⟶ Z) (v' : X ⟶ Z) (w' : Y ⟶ X) (t : Z ⟶ T)
    (hvw : v ≫ w = w' ≫ v') (huw : u ≫ w' = 𝟙 X) :
    (u ≫ v) ≫ (w ≫ t) = v' ≫ t := by
  rw [Category.assoc, ← Category.assoc v w t, hvw, Category.assoc,
    ← Category.assoc u w' (v' ≫ t), huw, Category.id_comp]

private lemma homotopyHomologyToSingle_map (R : Type*) [Ring R] [Linear R C]
    (K : CochainComplex C ℤ) (E : C) (i : ℤ)
    (f : K ⟶ (CochainComplex.singleFunctor C i).obj E) :
    homotopyHomologyToSingle R K E i
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) =
      homologyMap f i ≫ (singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i
  let e := HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i
  let J := (CochainComplex.singleFunctor C i).obj E
  let s := (singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom
  show (e.inv.app K ≫ H.map (q.map f)) ≫ (e.hom.app J ≫ s) = homologyMap f i ≫ s
  exact comp_naturality_cancel (e.inv.app K) (H.map (q.map f)) (e.hom.app J)
    (homologyMap f i) (e.hom.app K) s (e.hom.naturality f) (e.inv_hom_id_app K)

private noncomputable def homotopyHomologyToSingleEquiv (R : Type*) [Ring R] [Linear R C]
    (K : CochainComplex C ℤ) (E : C) [Injective E] (i : ℤ) :
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C i).obj E)) ≃ₗ[R] (K.homology i ⟶ E) := by
  apply LinearEquiv.ofBijective (homotopyHomologyToSingle R K E i)
  constructor
  · apply (homotopyHomologyToSingle R K E i).ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
    rw [homotopyHomologyToSingle_map] at hf
    have hg : homologyMap g i = 0 :=
      (cancel_mono (singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom).mp (by simpa using hf)
    exact (HomotopyCategory.quotient_map_eq_zero_iff g).mpr
      (nullhomotopy_of_homology_to_single_zero K E i g hg)
  · intro f
    obtain ⟨g, hg⟩ := homology_to_single_surjective K E i f
    exact ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g,
      (homotopyHomologyToSingle_map R K E i g).trans hg⟩

private noncomputable def derivedHomToSingleEquiv (R : Type*) [Ring R] [Linear R C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) (E : C) [Injective E] (i : ℤ) :
    (DerivedCategory.Q.obj K ⟶ (DerivedCategory.singleFunctor C i).obj E) ≃ₗ[R]
      (K.homology i ⟶ E) := by
  let J := (CochainComplex.singleFunctor C i).obj E
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  letI : J.IsKInjective := isKInjective_singleFunctor_obj E i
  let eQ := LinearEquiv.ofBijective (DerivedCategory.Qh.mapLinearMap R
      (X := q.obj K) (Y := q.obj J))
    (CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) J)
  let eK := (DerivedCategory.quotientCompQhIso C).app K
  let eJ := (DerivedCategory.quotientCompQhIso C).app J ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C i).app E).symm
  exact (Linear.homCongr R eK.symm eJ.symm).trans
    (eQ.symm.trans (homotopyHomologyToSingleEquiv R K E i))

attribute [local instance] HasDerivedCategory.standard

private noncomputable def derivedExtToInjectiveEquiv
    {A : Type u} [CommRing A] (X : DerivedCategory (ModuleCat.{v} A))
    (E : ModuleCat.{v} A) [Injective E] (i : ℤ) :
    (X ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj E)⟦-i⟧) ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj X ⟶ E) := by
  let K := DerivedCategory.Q.objPreimage X
  let eK := DerivedCategory.Q.objObjPreimageIso X
  let eShift : ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj E)⟦-i⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{v} A) i).obj E :=
    ((DerivedCategory.singleFunctors (ModuleCat.{v} A)).shiftIso (-i) i 0 (by omega)).app E
  let eH : K.homology i ≅ (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj X :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) i).app K).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).mapIso eK
  exact (Linear.homCongr A eK.symm eShift).trans
    ((derivedHomToSingleEquiv A K E i).trans (Linear.homCongr A eH (Iso.refl E)))

end


section SourceLinearity

open CochainComplex CategoryTheory.MonoidalCategory

variable (A : Type u) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The canonical derived-Hom bifunctor is `A`-linear in its source variable, at a source
presented by a cochain complex and a K-injective target. -/
theorem derivedHomAdjunction_map_smul_id_left_model
    (L J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective] (a : A) :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
        (show (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J) ⟶
            (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J) from
          ((a • 𝟙 (DerivedCategory.Q.obj L)).op, 𝟙 (DerivedCategory.Q.obj J))) =
      a • 𝟙 ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj J)) := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  have hnat := d.homIso_naturality (L := L) (L' := L) (I := J) (I' := J) (a • 𝟙 L) (𝟙 J)
  have hQ (X : CochainComplex (ModuleCat.{u} A) ℤ) :
      DerivedCategory.Q.map (a • 𝟙 X) = a • 𝟙 (DerivedCategory.Q.obj X) := by
    rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  rw [hQ L, StacksDraft.DerivedHom.ExtComparison.precomp_smul_id A L J a] at hnat
  refine (cancel_mono (d.homIso L J).hom).mp ?_
  rw [Linear.smul_comp, Category.id_comp]
  simp only [CategoryTheory.Functor.map_id] at hnat
  rw [hnat, Stacks.HomComplex.TensorHomMap.postcomp_id, Category.comp_id, hQ,
    Linear.comp_smul, Category.comp_id]

/-- Degree-zero derived Hom at a derived-Hom datum is natural in its source variable. -/
theorem homZeroEquiv_naturality_left {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)]
    (d : StacksDraft.DerivedHom.DerivedHomData R)
    {K K' M : DerivedCategory (ModuleCat.{u} R)} (f : K' ⟶ K)
    (a : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) ⟶
      d.hom.obj (Opposite.op K, M)) :
    d.homZeroEquiv K' M (a ≫ d.hom.map (show (Opposite.op K, M) ⟶ (Opposite.op K', M) from
        (f.op, 𝟙 M))) =
      f ≫ d.homZeroEquiv K M a := by
  dsimp [StacksDraft.DerivedHom.DerivedHomData.homZeroEquiv]
  rw [d.homEquiv_dinaturality]
  have h := d.tensorUnitLeft_naturality f
  apply (cancel_epi (d.tensorUnitLeft K').hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h]
  simp

/-- The canonical derived-Hom bifunctor is `A`-linear in its source variable. -/
theorem derivedHomAdjunction_map_smul_id_left
    (K M : DerivedCategory (ModuleCat.{u} A)) (a : A) :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
        (show (Opposite.op K, M) ⟶ (Opposite.op K, M) from ((a • 𝟙 K).op, 𝟙 M)) =
      a • 𝟙 ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op K, M)) := by
  obtain ⟨J, q, hq, hJ⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage M)
  let ρ : M ≅ DerivedCategory.Q.obj J :=
    (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫ asIso (DerivedCategory.Q.map q)
  refine StacksDraft.DerivedHom.ExtComparison.map_smul_id_of_natIso
    (derivedHomIntoMapIso A ρ) ((a • 𝟙 K).op) a ?_
  refine StacksDraft.DerivedHom.ExtComparison.map_op_smul_id_of_iso
    (derivedHomInto A (DerivedCategory.Q.obj J))
    (DerivedCategory.Q.objObjPreimageIso K).symm a a ?_
  exact derivedHomAdjunction_map_smul_id_left_model A _ J a

/-- Degree-zero derived Hom at the canonical adjunction is `A`-linear. -/
theorem derivedHomZeroEquiv_map_smul (Y N : DerivedCategory (ModuleCat.{u} A)) (a : A)
    (u : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) ⟶
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj (Opposite.op Y, N)) :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).homZeroEquiv Y N (a • u) =
      a • (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).homZeroEquiv Y N u := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  have h1 : a • u = u ≫ d.hom.map
      (show (Opposite.op Y, N) ⟶ (Opposite.op Y, N) from ((a • 𝟙 Y).op, 𝟙 N)) := by
    rw [derivedHomAdjunction_map_smul_id_left A Y N a, Linear.comp_smul, Category.comp_id]
  rw [h1, homZeroEquiv_naturality_left d (a • 𝟙 Y) u, Linear.smul_comp,
    Category.id_comp]

/-- Degree-zero derived Hom at the canonical adjunction, as an `A`-linear equivalence. -/
def derivedHomZeroLinearEquiv (Y N : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) ⟶
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op Y, N)) ≃ₗ[A] (Y ⟶ N) :=
  ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).homZeroEquiv Y N).toLinearEquiv
    (derivedHomZeroEquiv_map_smul A Y N)

/-- `Dualizing.LocalDuality.derivedHomZeroLinearEquiv` is the degree-zero derived-Hom
equivalence of the canonical adjunction. -/
theorem derivedHomZeroLinearEquiv_apply (Y N : DerivedCategory (ModuleCat.{u} A))
    (u : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) ⟶
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj (Opposite.op Y, N)) :
    derivedHomZeroLinearEquiv A Y N u =
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).homZeroEquiv Y N u := rfl

/-- Evaluation at `1` identifies morphisms out of the free rank-one module with the module. -/
def unitEvalLinearEquiv (N : ModuleCat.{u} A) : (ModuleCat.of A A ⟶ N) ≃ₗ[A] (N : Type u) :=
  (ModuleCat.homLinearEquiv (S := A)).trans (LinearMap.ringLmapEquivSelf A A (N : Type u))

/-- `Dualizing.LocalDuality.unitEvalLinearEquiv` evaluates a morphism at `1`. -/
@[simp] theorem unitEvalLinearEquiv_apply (N : ModuleCat.{u} A) (φ : ModuleCat.of A A ⟶ N) :
    unitEvalLinearEquiv A N φ = φ.hom 1 := rfl

/-- The free rank-one module in degree zero corepresents degree-zero cohomology. -/
def homologyZeroFromSingleLinearEquiv (X : DerivedCategory (ModuleCat.{u} A)) :
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ X) ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj X : Type u) :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of A A) X 0 A).trans
    (unitEvalLinearEquiv A _)

/-- The identification of `Dualizing.LocalDuality.homologyZeroFromSingleLinearEquiv` is natural
in the target. -/
theorem homologyZeroFromSingleLinearEquiv_naturality
    {X X' : DerivedCategory (ModuleCat.{u} A)} (h : X ⟶ X')
    (φ : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶ X) :
    homologyZeroFromSingleLinearEquiv A X' (φ ≫ h) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map h).hom
        (homologyZeroFromSingleLinearEquiv A X φ) := by
  dsimp only [homologyZeroFromSingleLinearEquiv, LinearEquiv.trans_apply]
  rw [DerivedCategory.homologyFromSingleLinearEquiv_comp]
  rfl

/-- The cohomology of derived Hom in degree zero is `Hom` in the derived category:
`Hom_{D(A)}(Y, N) ≅ H^0(RHom_A(Y, N))`, for the canonical derived-Hom bifunctor. -/
public def extHomologyZeroLinearEquiv (Y N : DerivedCategory (ModuleCat.{u} A)) :
    (Y ⟶ N) ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op Y, N)) : Type u) :=
  (derivedHomZeroLinearEquiv A Y N).symm.trans (homologyZeroFromSingleLinearEquiv A _)

/-- The identification of `Dualizing.LocalDuality.extHomologyZeroLinearEquiv` is natural in the
source object: it carries precomposition by `g` to the map induced on cohomology by
contravariant derived Hom. -/
public theorem extHomologyZeroLinearEquiv_naturality
    {Y Y' N : DerivedCategory (ModuleCat.{u} A)} (g : Y' ⟶ Y) (u : Y ⟶ N) :
    extHomologyZeroLinearEquiv A Y' N (g ≫ u) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
          (show (Opposite.op Y, N) ⟶ (Opposite.op Y', N) from (g.op, 𝟙 N)))).hom
        (extHomologyZeroLinearEquiv A Y N u) := by
  have hv : (derivedHomZeroLinearEquiv A Y' N).symm (g ≫ u) =
      (derivedHomZeroLinearEquiv A Y N).symm u ≫
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
          (show (Opposite.op Y, N) ⟶ (Opposite.op Y', N) from (g.op, 𝟙 N)) := by
    apply (derivedHomZeroLinearEquiv A Y' N).injective
    rw [LinearEquiv.apply_symm_apply, derivedHomZeroLinearEquiv_apply,
      homZeroEquiv_naturality_left (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)) g,
      ← derivedHomZeroLinearEquiv_apply, LinearEquiv.apply_symm_apply]
  dsimp only [extHomologyZeroLinearEquiv, LinearEquiv.trans_apply]
  rw [hv]
  exact homologyZeroFromSingleLinearEquiv_naturality A _ _

end SourceLinearity

section InjectiveDetection

open HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- Every morphism of the derived category into the image of a K-injective complex is the image
of a chain map. -/
private lemma Q_map_surjective_of_isKInjective (K J : CochainComplex C ℤ) [J.IsKInjective] :
    Function.Surjective (fun g : K ⟶ J => DerivedCategory.Q.map g) := by
  intro w
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let eK := (DerivedCategory.quotientCompQhIso C).app K
  let eJ := (DerivedCategory.quotientCompQhIso C).app J
  obtain ⟨α, hα⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) J).2
    (eK.hom ≫ w ≫ eJ.inv)
  obtain ⟨g, rfl⟩ := q.map_surjective α
  refine ⟨g, ?_⟩
  have hn := (DerivedCategory.quotientCompQhIso C).hom.naturality g
  change DerivedCategory.Qh.map (q.map g) ≫ eJ.hom = eK.hom ≫ DerivedCategory.Q.map g at hn
  rw [hα] at hn
  refine (cancel_epi eK.hom).mp ?_
  rw [← hn]
  simp

/-- A chain map into a K-injective complex becomes zero in the derived category exactly when it
is null-homotopic. -/
private lemma Q_map_eq_zero_iff_of_isKInjective (K J : CochainComplex C ℤ) [J.IsKInjective]
    (g : K ⟶ J) :
    DerivedCategory.Q.map g = 0 ↔ Nonempty (Homotopy g 0) := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let eK := (DerivedCategory.quotientCompQhIso C).app K
  let eJ := (DerivedCategory.quotientCompQhIso C).app J
  have hn := (DerivedCategory.quotientCompQhIso C).hom.naturality g
  change DerivedCategory.Qh.map (q.map g) ≫ eJ.hom = eK.hom ≫ DerivedCategory.Q.map g at hn
  have key : DerivedCategory.Qh.map (q.map g) =
      eK.hom ≫ DerivedCategory.Q.map g ≫ eJ.inv := by
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← HomotopyCategory.quotient_map_eq_zero_iff]
  constructor
  · intro h
    refine (CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) J).1 ?_
    rw [key, h]
    simp
  · intro h
    have h0 : eK.hom ≫ DerivedCategory.Q.map g ≫ eJ.inv = 0 := by rw [← key, h]; simp
    simpa using h0

end InjectiveDetection

section HomologyDetection

variable (A : Type u) [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The degree-`i` cohomology of `E` placed in degree `i` is `E`. -/
def singleHomologySelfIso (E : ModuleCat.{u} A) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) ≅ E :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) i).app E) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) i).obj E) ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i E

/-- Taking degree-`i` cohomology turns a morphism into `E` placed in degree `i` into an
`A`-linear map out of degree-`i` cohomology. -/
public def homologyToSingleLinearMap (X : DerivedCategory (ModuleCat.{u} A)) (E : ModuleCat.{u} A)
    (i : ℤ) :
    (X ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) →ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X ⟶ E) where
  toFun v := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map v ≫
    (singleHomologySelfIso A E i).hom
  map_add' v w := by
    simp only [Functor.map_add, Preadditive.add_comp]
  map_smul' r v := by
    have h : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map (r • v) =
        r • (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map v :=
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapLinearMap A).map_smul r v
    simp only [RingHom.id_apply, h, Linear.smul_comp]

/-- The evaluation map is natural in the source object. -/
public theorem homologyToSingleLinearMap_naturality
    {X X' : DerivedCategory (ModuleCat.{u} A)} (g : X' ⟶ X) (E : ModuleCat.{u} A) (i : ℤ)
    (v : X ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) :
    homologyToSingleLinearMap A X' E i (g ≫ v) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map g ≫
        homologyToSingleLinearMap A X E i v := by
  dsimp only [homologyToSingleLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Functor.map_comp, Category.assoc]

/-- The evaluation map at a complex, computed on a chain map. -/
private lemma homologyToSingleLinearMap_Q_map
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (E : ModuleCat.{u} A) (i : ℤ)
    (g : K ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} A) i).obj E) :
    homologyToSingleLinearMap A (DerivedCategory.Q.obj K) E i
        (DerivedCategory.Q.map g ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) i).app E).inv) =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app K).hom ≫
        HomologicalComplex.homologyMap g i ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  let sfc := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) i).app E
  let F := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i
  let J := (CochainComplex.singleFunctor (ModuleCat.{u} A) i).obj E
  have h2 : H.map (DerivedCategory.Q.map g) ≫ (F.app J).hom =
      (F.app K).hom ≫ HomologicalComplex.homologyMap g i := F.hom.naturality g
  show H.map (DerivedCategory.Q.map g ≫ sfc.inv) ≫
      (H.mapIso sfc).hom ≫ (F.app J).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom = _
  rw [Functor.map_comp, Category.assoc]
  show H.map (DerivedCategory.Q.map g) ≫ H.map sfc.inv ≫ H.map sfc.hom ≫
    (F.app J).hom ≫ _ = _
  rw [← Category.assoc (H.map sfc.inv), ← H.map_comp, Iso.inv_hom_id, H.map_id,
    Category.id_comp]
  calc H.map (DerivedCategory.Q.map g) ≫ (F.app J).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom
      = (H.map (DerivedCategory.Q.map g) ≫ (F.app J).hom) ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom :=
        (Category.assoc _ _ _).symm
    _ = ((F.app K).hom ≫ HomologicalComplex.homologyMap g i) ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom := by
        rw [h2]
        rfl
    _ = _ := Category.assoc _ _ _

/-- Maps into a single injective object are detected on cohomology: for an injective module `E`
the evaluation map `Hom_{D(A)}(X, E[i]) ⟶ Hom_A(H^i(X), E)` is bijective. -/
public theorem bijective_homologyToSingleLinearMap (X : DerivedCategory (ModuleCat.{u} A))
    (E : ModuleCat.{u} A) [Injective E] (i : ℤ) :
    Function.Bijective (homologyToSingleLinearMap A X E i) := by
  have key : ∀ K : CochainComplex (ModuleCat.{u} A) ℤ,
      Function.Bijective (homologyToSingleLinearMap A (DerivedCategory.Q.obj K) E i) := by
    intro K
    have := isKInjective_singleFunctor_obj (C := ModuleCat.{u} A) E i
    constructor
    · apply (homologyToSingleLinearMap A (DerivedCategory.Q.obj K) E i).ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      obtain ⟨g, hg⟩ := Q_map_surjective_of_isKInjective K
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) i).obj E)
        (v ≫ ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) i).app E).hom)
      dsimp only at hg
      have hvg : v = DerivedCategory.Q.map g ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) i).app E).inv := by
        rw [hg, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [hvg, homologyToSingleLinearMap_Q_map] at hv
      have h1 : HomologicalComplex.homologyMap g i ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom = 0 :=
        (cancel_epi ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app K).hom).mp
          (hv.trans Limits.comp_zero.symm)
      have h2 : HomologicalComplex.homologyMap g i = 0 :=
        (cancel_mono
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) i E).hom).mp
          (h1.trans Limits.zero_comp.symm)
      rw [hvg, (Q_map_eq_zero_iff_of_isKInjective K
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) i).obj E) g).mpr
        (nullhomotopy_of_homology_to_single_zero K E i g h2), Limits.zero_comp]
    · intro ψ
      obtain ⟨g, hg⟩ := homology_to_single_surjective K E i
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app K).inv ≫ ψ)
      dsimp only at hg
      refine ⟨DerivedCategory.Q.map g ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) i).app E).inv, ?_⟩
      have hc := congrArg (fun z =>
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app K).hom ≫ z) hg
      rw [homologyToSingleLinearMap_Q_map]
      exact hc.trans (Iso.hom_inv_id_assoc _ ψ)
  let eX := DerivedCategory.Q.objObjPreimageIso X
  have hnat := fun v => homologyToSingleLinearMap_naturality A eX.hom E i v
  constructor
  · intro v w h
    have hv := hnat v
    have hw := hnat w
    refine (cancel_epi eX.hom).mp ?_
    refine (key (DerivedCategory.Q.objPreimage X)).1 ?_
    rw [hv, hw, h]
  · intro ψ
    obtain ⟨v, hv⟩ := (key (DerivedCategory.Q.objPreimage X)).2
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map eX.hom ≫ ψ)
    refine ⟨eX.inv ≫ v, ?_⟩
    have h := homologyToSingleLinearMap_naturality A eX.hom E i (eX.inv ≫ v)
    rw [Iso.hom_inv_id_assoc, hv] at h
    have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map eX.hom) :=
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)).mapIso eX).isIso_hom
    exact (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map eX.hom)).mp h.symm

/-- Maps into a single injective object are detected on cohomology, as an `A`-linear equivalence
`Hom_{D(A)}(X, E[i]) ≅ Hom_A(H^i(X), E)`. -/
public def homologySingleLinearEquiv (X : DerivedCategory (ModuleCat.{u} A)) (E : ModuleCat.{u} A)
    [Injective E] (i : ℤ) :
    (X ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) ≃ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X ⟶ E) :=
  LinearEquiv.ofBijective _ (bijective_homologyToSingleLinearMap A X E i)

end HomologyDetection


/-! ### Local duality in terms of Ext and Matlis duality -/

attribute [local instance] Dualizing.hasProductsOfShape_nat_derivedCategory

/-- Let `(A, 𝔪, κ)` be a Noetherian local ring, let `ω` be a normalized dualizing complex, let
`ι : κ ⟶ E` be an injective hull of the residue field, and let `K` be an object of `D_Coh(A)`,
that is, a complex all of whose cohomology modules are finite. Then the `𝔪`-adic completion of
`Ext^{-i}_A(K, ω)` is isomorphic to the module of `A`-linear maps from `H^i_𝔪(K)` to `E`.
Local cohomology is `RΓ_Z` for `Z = V(𝔪)`, and `Ext^{-i}_A(K, ω)` is `Hom_{D(A)}(K, ω⟦-i⟧)`. -/
@[stacks 0AAK, sga "2 V 2.1" "Ext^{-i}≅Hom(H^i,E)"]
public theorem nonempty_adicCompletion_ext_linearEquiv_linearMap_localCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K))
    {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono ι] (hι : Module.IsInjectiveHull ι) (i : ℤ) :
    Nonempty
      (AdicCompletion (IsLocalRing.maximalIdeal A)
          (DerivedCategory.Ext K ω (-i)) ≃ₗ[A]
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            ((derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
                (IsNoetherian.noetherian _)).ι.obj
              ((localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
                (IsNoetherian.noetherian _)).obj K)) →ₗ[A] E)) := by
  classical
  let m := IsLocalRing.maximalIdeal A
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let RK := d.hom.obj (Opposite.op K, ω)
  have : Injective E := hι.1
  have hfin : ∀ n : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj RK) := by
    intro n
    have := Dualizing.dualizingDerivedHom_finiteCohomology.{u, u} A ω hω.1 K hK n
    exact Module.Finite.equiv
      ((homologyDerivedHomLinearEquiv K ω n).trans
        (((StacksDraft.DerivedHom.ExtComparison.extCohomologyComparisonIso.{u, u}
            A ω n).app (Opposite.op K)).toLinearEquiv.trans ULift.moduleEquiv)).symm
  let F := DerivedCompletion.derivedCompletionFunctor A f
  let eps := DerivedCompletion.derivedCompletionUnit A f
  have hrefl := DerivedCompletion.derivedCompletion_isReflection A f
  have hFc : ∀ X, derivedCompleteProperty A m (F.obj X) := fun X => by
    have h := hrefl.1 X
    rwa [hf] at h
  have hb : ∀ X Z, derivedCompleteProperty A m Z →
      Function.Bijective (fun g : F.obj X ⟶ Z ↦ eps.app X ≫ g) :=
    fun X Z hZ => hrefl.2 X Z (by rw [hf]; exact hZ)
  let Cfun := (derivedCompleteProperty A m).lift F hFc
  let adj := reflectionAdjunctionOfUniversal (derivedCompleteProperty A m) F eps hFc hb
  obtain ⟨hcomp⟩ := AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion
    A m RK hfin Cfun adj (-i)
  obtain ⟨duality⟩ :=
    nonempty_derivedCompletion_derivedHom_iso_derivedHom_injectiveHull A f hf ω hω ι hι K
  let Lobj := (derivedPowerTorsionProperty A m (IsNoetherian.noetherian _)).ι.obj
    ((localCohomologyFunctor A m (IsNoetherian.noetherian _)).obj K)
  let Esingle := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E
  let step : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
        ((Cfun ⋙ (derivedCompleteProperty A m).ι).obj RK)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
        (d.hom.obj (Opposite.op Lobj, Esingle)) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).mapIso
      (((derivedCompleteProperty A m).liftCompιIso F hFc).app RK ≪≫ duality)
  exact ⟨((AdicCompletion.congr m
      (homologyDerivedHomLinearEquiv K ω (-i))).restrictScalars A).symm.trans
    (hcomp.symm.toLinearEquiv.trans (step.toLinearEquiv.trans
      ((homologyDerivedHomLinearEquiv Lobj Esingle (-i)).trans
        ((derivedExtToInjectiveEquiv Lobj E i).trans ModuleCat.homLinearEquiv))))⟩

section ModuleLocalDuality

open Stacks.LocalCohomology Stacks.LocalCohomology.CechFormula

attribute [local instance] Stacks.LocalCohomology.derivedPowerTorsionProperty_isTriangulated
attribute [local instance]
  Stacks.LocalCohomology.derivedPowerTorsionProperty_isClosedUnderIsomorphisms

variable (A : Type u) [CommRing A]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.hasProductsOfShape_nat_derivedCategory

/-- Local cohomology with support in `V(I)`, as an endofunctor of `D(A)`, commutes with the
shift. -/
@[instance_reducible]
public def localCohomologyEndofunctorCommShift (I : Ideal A) (hI : I.FG) :
    (localCohomologyEndofunctor A I hI).CommShift ℤ :=
  letI := Stacks.LocalCohomology.localCohomologyFunctorCommShift.{u, u} A I hI
  Functor.CommShift.comp _ _

/-- A commuting square `f ≫ g = f' ≫ g'` gives equal values on elements after applying a functor
into modules. -/
private lemma functor_map_apply_eq_of_comp_eq {D : Type*} [Category D] {R : Type u} [Ring R]
    (F : D ⥤ ModuleCat.{u} R) {X Y Z W : D} (f : X ⟶ Y) (g : Y ⟶ W) (f' : X ⟶ Z) (g' : Z ⟶ W)
    (h : f ≫ g = f' ≫ g') (x : F.obj X) :
    (F.map g).hom ((F.map f).hom x) = (F.map g').hom ((F.map f').hom x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, h]

/-- Let `(A, 𝔪, κ)` be a Noetherian local ring, let `ω` be a normalized dualizing complex, let
`ι : κ ⟶ E` be an injective hull of the residue field, and let `Z = V(𝔪)`. For every integer
`i` there is a family of `A`-linear isomorphisms

`H^0(RHom_A(K, ω⟦-i⟧)^∧) ≅ Hom_A(H^i_Z(K), E)`

indexed by the objects `K` of `D(A)`, compatible with the maps induced by every morphism of
`D(A)`: local duality in its module form, natural in `K`.

The left-hand side is the degree-zero cohomology of the derived `𝔪`-adic completion of
`RHom_A(K, ω⟦-i⟧)`, whose degree-zero cohomology is `Ext^{-i}_A(K, ω)`; the right-hand side is
the Matlis dual of the degree-`i` local cohomology module. -/
@[stacks 0AAK "natural in K"]
public theorem exists_localDualityExtNatEquiv
    [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono ι] (hι : Module.IsInjectiveHull ι) (i : ℤ) :
    ∃ θ : ∀ K : DerivedCategory (ModuleCat.{u} A),
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((DerivedCompletion.derivedCompletionFunctor A f).obj
              ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
                (Opposite.op K,
                  (CategoryTheory.shiftFunctor
                    (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω))) : Type u) ≃ₗ[A]
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
              ((localCohomologyEndofunctor A (IsLocalRing.maximalIdeal A)
                (IsNoetherian.noetherian _)).obj K) : Type u) →ₗ[A] (E : Type u)),
      ∀ (K K' : DerivedCategory (ModuleCat.{u} A)) (g : K' ⟶ K)
        (x : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((DerivedCompletion.derivedCompletionFunctor A f).obj
            ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
              (Opposite.op K,
                (CategoryTheory.shiftFunctor
                  (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω))) : Type u)),
        θ K' (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
              ((DerivedCompletion.derivedCompletionFunctor A f).map
                ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
                  (show (Opposite.op K, (CategoryTheory.shiftFunctor
                        (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) ⟶
                      (Opposite.op K', (CategoryTheory.shiftFunctor
                        (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) from
                    (g.op, 𝟙 _))))).hom x) =
          (θ K x).comp
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
              ((localCohomologyEndofunctor A (IsLocalRing.maximalIdeal A)
                (IsNoetherian.noetherian _)).map g)).hom := by
  classical
  set m := IsLocalRing.maximalIdeal A with hm'
  set hm : m.FG := IsNoetherian.noetherian _ with hmfg
  set G := localCohomologyEndofunctor A m hm with hG
  let : G.CommShift ℤ := localCohomologyEndofunctorCommShift A m hm
  set W := (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω with hW
  have : CategoryTheory.Injective E := hι.1
  obtain ⟨concentrated⟩ :=
    Dualizing.LocalDuality.nonempty_localCohomology_iso_single_homology_zero.{u, u} A ω hω
  obtain ⟨j, hj, hjhull⟩ :=
    Dualizing.LocalDuality.exists_isInjectiveHull_homology_zero_localCohomology.{u, u} A ω hω
  let := hj
  obtain ⟨hullIso, -⟩ := Module.exists_iso_of_isInjectiveHull j ι hjhull hι
  let fix : G.obj W ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E :=
    (Functor.CommShift.commShiftIso G (-i)).app ω ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).mapIso
        (concentrated ≪≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso hullIso) ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso (-i) i 0 (by omega)).app E
  let e : derivedHomInto A W ⋙ DerivedCompletion.derivedCompletionFunctor A f ≅
      G.op ⋙ derivedHomInto A ((DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) :=
    derivedCompletionDerivedHomTorsionNatIso A m hm f hf W ≪≫
      Functor.isoWhiskerLeft G.op (derivedHomIntoMapIso A fix)
  refine ⟨fun K =>
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
        (e.app (Opposite.op K))).toLinearEquiv.trans
      (((extHomologyZeroLinearEquiv A (G.obj K)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E)).symm.trans
        (homologySingleLinearEquiv A (G.obj K) E i)).trans ModuleCat.homLinearEquiv), ?_⟩
  intro K K' g x
  have hnat : (DerivedCompletion.derivedCompletionFunctor A f).map
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
          (show (Opposite.op K, W) ⟶ (Opposite.op K', W) from (g.op, 𝟙 W))) ≫
        e.hom.app (Opposite.op K') =
      e.hom.app (Opposite.op K) ≫
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
          (show (Opposite.op (G.obj K),
                (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) ⟶
              (Opposite.op (G.obj K'),
                (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) from
            ((G.map g).op, 𝟙 _)) := e.hom.naturality g.op
  dsimp only [LinearEquiv.trans_apply]
  have step1 : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
          (e.app (Opposite.op K'))).toLinearEquiv
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((DerivedCompletion.derivedCompletionFunctor A f).map
            ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
              (show (Opposite.op K, W) ⟶ (Opposite.op K', W) from (g.op, 𝟙 W))))).hom x) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
            (show (Opposite.op (G.obj K),
                  (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) ⟶
                (Opposite.op (G.obj K'),
                  (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) from
              ((G.map g).op, 𝟙 _)))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
          (e.app (Opposite.op K))).toLinearEquiv x) := by
    exact functor_map_apply_eq_of_comp_eq (DerivedCategory.homologyFunctor _ 0) _ _ _ _ hnat x
  rw [step1]
  set y := ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
    (e.app (Opposite.op K))).toLinearEquiv x with hy
  set v := (extHomologyZeroLinearEquiv A (G.obj K)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E)).symm y with hv
  have step2 : (extHomologyZeroLinearEquiv A (G.obj K')
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E)).symm
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
            (show (Opposite.op (G.obj K),
                  (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) ⟶
                (Opposite.op (G.obj K'),
                  (DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E) from
              ((G.map g).op, 𝟙 _)))).hom y) = G.map g ≫ v := by
    apply (extHomologyZeroLinearEquiv A (G.obj K')
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) i).obj E)).symm_apply_eq.mpr
    rw [extHomologyZeroLinearEquiv_naturality A (G.map g) v, hv,
      LinearEquiv.apply_symm_apply]
  rw [step2]
  have step3 : homologySingleLinearEquiv A (G.obj K') E i (G.map g ≫ v) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map (G.map g) ≫
        homologySingleLinearEquiv A (G.obj K) E i v :=
    homologyToSingleLinearMap_naturality A (G.map g) E i v
  rw [step3]
  rfl

/-- With the notation of `Dualizing.LocalDuality.exists_localDualityExtNatEquiv`, there is a
family of `A`-linear maps

`Ext^{-i}_A(K, ω) ⟶ Hom_A(H^i_Z(K), E)`

indexed by the objects of `D(A)` and compatible with precomposition: for every `g : K' ⟶ K` the
square built from precomposition by `g` on the left and from `H^i_Z(g)` on the right commutes.
Here `Ext^{-i}_A(K, ω)` is `Hom_{D(A)}(K, ω⟦-i⟧)`. -/
public theorem exists_natural_extToMatlisDualMap
    [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    {E : ModuleCat.{u} A}
    (ι : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono ι] (hι : Module.IsInjectiveHull ι) (i : ℤ) :
    ∃ μ : ∀ K : DerivedCategory (ModuleCat.{u} A),
        (K ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω) →ₗ[A]
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
              ((localCohomologyEndofunctor A (IsLocalRing.maximalIdeal A)
                (IsNoetherian.noetherian _)).obj K) : Type u) →ₗ[A] (E : Type u)),
      ∀ (K K' : DerivedCategory (ModuleCat.{u} A)) (g : K' ⟶ K)
        (u : K ⟶ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-i)).obj ω),
        μ K' (g ≫ u) =
          (μ K u).comp
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
              ((localCohomologyEndofunctor A (IsLocalRing.maximalIdeal A)
                (IsNoetherian.noetherian _)).map g)).hom := by
  obtain ⟨θ, hθ⟩ := exists_localDualityExtNatEquiv A f hf ω hω ι hι i
  refine ⟨fun K => (θ K).toLinearMap.comp
    ((((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
        ((DerivedCompletion.derivedCompletionUnit A f).app
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
            (Opposite.op K, (ω⟦-i⟧))))).hom).comp
      (extHomologyZeroLinearEquiv A K (ω⟦-i⟧)).toLinearMap), ?_⟩
  intro K K' g u
  show θ K' (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((DerivedCompletion.derivedCompletionUnit A f).app
        ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op K', (ω⟦-i⟧))))).hom (extHomologyZeroLinearEquiv A K' (ω⟦-i⟧) (g ≫ u))) = _
  rw [extHomologyZeroLinearEquiv_naturality A g u]
  have hε : (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
        (show (Opposite.op K, (ω⟦-i⟧)) ⟶ (Opposite.op K', (ω⟦-i⟧)) from (g.op, 𝟙 (ω⟦-i⟧))) ≫
        (DerivedCompletion.derivedCompletionUnit A f).app
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
            (Opposite.op K', (ω⟦-i⟧))) =
      (DerivedCompletion.derivedCompletionUnit A f).app
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
            (Opposite.op K, (ω⟦-i⟧))) ≫
        (DerivedCompletion.derivedCompletionFunctor A f).map
          ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
            (show (Opposite.op K, (ω⟦-i⟧)) ⟶ (Opposite.op K', (ω⟦-i⟧)) from (g.op, 𝟙 (ω⟦-i⟧)))) :=
    (DerivedCompletion.derivedCompletionUnit A f).naturality _
  have hstep := functor_map_apply_eq_of_comp_eq (DerivedCategory.homologyFunctor _ 0) _ _ _ _ hε
    (extHomologyZeroLinearEquiv A K (ω⟦-i⟧) u)
  rw [hstep, hθ K K' g]
  rfl

end ModuleLocalDuality

end Dualizing.LocalDuality

end
