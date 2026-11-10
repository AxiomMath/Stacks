module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRestrictionIntegralDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedTwistAcyclicTransport

/-!
# `RΓ` of the geometric fibre along a proper morphism, Frobenius-equivariantly

Let `i : Z ⟶ Y` be a proper morphism of schemes over a finite field `k` and let `k̄` be an
extension of `k`. For a bounded below complex `M` of sheaves of `Λ`-modules on `Z_étale` whose
restrictions `Mⁿ|_{Z_k̄}` are acyclic for the direct image along `i_k̄ : Z_k̄ ⟶ Y_k̄`,

`RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})`,

naturally in `M` and compatibly with the canonical geometric Frobenius endomorphisms of the two
sides. The base change map `(i_* M)|_{Y_k̄} ⟶ (i_k̄)_*(M|_{Z_k̄})` is an isomorphism by proper base
change in degree zero ([Stacks, Tag 0A3U],
`Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isProper`) and carries
the Frobenius twist of `Y` to `(i_k̄)_*` of that of `Z`; the acyclicity makes `(i_k̄)_*(M|_{Z_k̄})`
compute `R(i_k̄)_*(M|_{Z_k̄})` (Leray's acyclicity lemma, [Stacks, Tag 015E]), so that
`RΓ(Y_k̄, -)` of it is `RΓ(Z_k̄, M|_{Z_k̄})`
(`CategoryTheory.Functor.acyclicTwistTransportIso`).

This is the integral case `Stacks.EtaleCohomology.frobeniusRestrictionDirectImageIso`, where the
acyclicity is automatic, for a proper morphism. With `M = j_! K` for a compactification `j` and
a complex `K` of torsion sheaves, and `i` a morphism of compactifications, it gives the
independence of `RΓ_c(X_k̄, K)` and of its Frobenius from the compactification
([Stacks, Tag 0F7I]).

## Main definitions

* `Stacks.EtaleCohomology.properFieldBaseChangeComplexIso`:
  `(i_* M)|_{Y_k̄} ≅ (i_k̄)_*(M|_{Z_k̄})`, degreewise.
* `Stacks.EtaleCohomology.frobeniusRestrictionProperDirectImageIso`:
  `RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})`.

## Main results

* `Stacks.EtaleCohomology.frobeniusRestrictionProperDirectImageIso_hom_naturality`.
* `Stacks.EtaleCohomology.frobeniusRestrictionProperDirectImageIso_hom_frobenius`.

## References

* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))}
  (i : Z ⟶ Y) [IsProper i.left] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The base change map `(i_* M)|_{Y_k̄} ≅ (i_k̄)_*(M|_{Z_k̄})` of a proper morphism over `k`,
degreewise on a bounded below complex. -/
def properFieldBaseChangeComplexIso (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)) :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
        ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj M) ≅
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          M) :=
  haveI := isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isProper Λ i kbar
  Functor.baseChangePlusIso (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
    (etaleModuleDirectImage.{u, 0} Λ i.left)
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar))
    (asIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
      (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar))) M

omit [Fintype k] in
/-- The base change map is natural in the complex. -/
lemma properFieldBaseChangeComplexIso_hom_naturality
    {M M' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)} (φ : M ⟶ M') :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
        ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.map φ) ≫
      (properFieldBaseChangeComplexIso Λ i kbar M').hom =
    (properFieldBaseChangeComplexIso Λ i kbar M).hom ≫
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar)).mapCochainComplexPlus.map
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.map
          φ) := by
  have := isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isProper Λ i kbar
  exact Functor.baseChangePlusIso_hom_naturality _ _ _ _ _ φ

/-- The restrictions `Mⁿ|_{Z_k̄}` of the terms of `M` are acyclic for the direct image along
`i_k̄ : Z_k̄ ⟶ Y_k̄`. -/
def FieldBaseChangeDirectImageAcyclic (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)) :
    Prop :=
  ∀ n, (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar)).rightAcyclic
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).obj (M.obj.X n))

omit [Fintype k] [IsProper i.left] in
/-- On such a complex the degreewise direct image along `i_k̄` computes the derived one. -/
lemma isIso_mapCochainComplexPlusDerivedUnit_app_fieldBaseChangeMap
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left))
    (hM : FieldBaseChangeDirectImageAcyclic Λ i kbar M) :
    IsIso ((Functor.mapCochainComplexPlusDerivedUnit
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))).app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          M)) :=
  isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic _ _ hM

/-- **`RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})`** for a proper morphism `i : Z ⟶ Y` over
`k` and a complex `M` whose restrictions to `Z_k̄` are acyclic for `(i_k̄)_*`:
`RΓ(Z_k̄, -) = RΓ(Y_k̄, R(i_k̄)_* -)` and `R(i_k̄)_*(M|_{Z_k̄}) = (i_k̄)_*(M|_{Z_k̄})`, followed by
the inverse of the base change isomorphism. -/
def frobeniusRestrictionProperDirectImageIso
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left))
    (hM : FieldBaseChangeDirectImageAcyclic Λ i kbar M) :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Z kbar M)) ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar
            ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj M))) :=
  haveI := isIso_mapCochainComplexPlusDerivedUnit_app_fieldBaseChangeMap Λ i kbar M hM
  Functor.acyclicTwistTransportIso
      (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
      (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
      (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap i kbar)
        (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
        (fieldBaseChangeMap_comp_snd i kbar).symm)
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
        M) ≪≫
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).mapIso
        (DerivedCategory.Plus.Q.mapIso (properFieldBaseChangeComplexIso Λ i kbar M)))).symm

omit [Fintype k] in
/-- **The identification is natural in the complex.** -/
theorem frobeniusRestrictionProperDirectImageIso_hom_naturality
    {M M' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)} (φ : M ⟶ M')
    (hM : FieldBaseChangeDirectImageAcyclic Λ i kbar M)
    (hM' : FieldBaseChangeDirectImageAcyclic Λ i kbar M') :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).map
          ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Z kbar).map φ)) ≫
      (frobeniusRestrictionProperDirectImageIso Λ i kbar M' hM').hom =
    (frobeniusRestrictionProperDirectImageIso Λ i kbar M hM).hom ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map
            ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.map φ))) := by
  have := isIso_mapCochainComplexPlusDerivedUnit_app_fieldBaseChangeMap Λ i kbar M hM
  have := isIso_mapCochainComplexPlusDerivedUnit_app_fieldBaseChangeMap Λ i kbar M' hM'
  have hT := Functor.acyclicTwistTransportIso_hom_naturality
    (F₁ := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (Φ := etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
    (F₁' := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
    (κ := etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.map φ)
  have hB := properFieldBaseChangeComplexIso_hom_naturality Λ i kbar φ
  refine comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ hT ((Iso.comp_inv_eq _).2 ?_)
  rw [Category.assoc]
  refine (Iso.eq_inv_comp _).2 ?_
  symm
  change (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map _ ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map _ =
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map _ ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [Functor.mapIso_hom, ← Functor.map_comp]
  dsimp only [fieldBaseChangeRestrictionFunctor, Functor.comp_map]
  rw [← Functor.map_comp, hB]

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification `RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})` commutes with the
canonical geometric Frobenius.** -/
theorem frobeniusRestrictionProperDirectImageIso_hom_frobenius
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left))
    (hM : FieldBaseChangeDirectImageAcyclic Λ i kbar M) :
    frobeniusRestrictionCohomologyEndo.{u, 0} Λ Z kbar p q hcard M ≫
        (frobeniusRestrictionProperDirectImageIso Λ i kbar M hM).hom =
      (frobeniusRestrictionProperDirectImageIso Λ i kbar M hM).hom ≫
        frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
          ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj M) := by
  have := isIso_mapCochainComplexPlusDerivedUnit_app_fieldBaseChangeMap Λ i kbar M hM
  rw [frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo,
    frobeniusRestrictionCohomologyEndo_eq_derivedTwistEndo]
  let ρ : etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard) ⋙
        etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar) ≅
      etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar) ⋙
        etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard) :=
    etaleModuleDirectImageComp.{u, 0} Λ _ _ _ rfl ≪≫
      (etaleModuleDirectImageComp.{u, 0} Λ _ _ _
        (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)).symm
  have hT := Functor.derivedTwistEndo_acyclicTransport
    (P := etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (F₁ := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (Φ := etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
    (F₁' := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar)))
    (κ := etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap i kbar)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd i kbar).symm)
    (P' := etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard))
    (θ := etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    (θ' := etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard)
      (pullback.snd Z.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm)
    (ρ := ρ)
    (fun X => directImageTwistTransfer_compat Λ (fieldBaseChangeMap i kbar)
      (geometricFrobeniusBaseChange Z kbar p q hcard)
      (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Z.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap i p q hcard kbar)
      (fieldBaseChangeMap_comp_snd i kbar).symm
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm
      (geometricFrobeniusBaseChange_comp_toBase Z kbar p q hcard).symm X)
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj M)
    (zTwist Λ kbar p q hcard M)
  have := isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isProper Λ i kbar
  have hN := Functor.derivedTwistEndo_baseChangePlusIso
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Z kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
    (etaleModuleDirectImage.{u, 0} Λ i.left)
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar))
    (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
    ρ.hom
    (asIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
      (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar)))
    (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard)
    (frobeniusBaseChangeTwist.{u, 0} Λ Z kbar p q hcard)
    (etaleModuleBaseChange_comp_frobeniusBaseChangeTwist Λ i p q hcard kbar) M
  exact comp_comp_eq_comp_comp_of_squares _ _ _ _ _ _ _ hT
    (comp_inv_eq_inv_comp_of_hom_comm _ _ _ _ hN)

end Stacks.EtaleCohomology

end
