module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRestrictionProperDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperBaseChangeQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExactPushforwardTwistTrace

/-!
# `RΓ` of the geometric fibre along a proper morphism, for complexes of injectives

Let `i : Z ⟶ Y` be a proper morphism of schemes over a finite field `k` and `k̄` an extension of
`k`. `Stacks.EtaleCohomology.frobeniusRestrictionProperDirectImageIso` identifies
`RΓ(Z_k̄, M|_{Z_k̄})` with `RΓ(Y_k̄, (i_* M)|_{Y_k̄})`, Frobenius-equivariantly, for a complex `M`
whose restrictions to `Z_k̄` are acyclic for `(i_k̄)_*`. The acyclicity is used only to make the
comparison `(i_k̄)_*(M|_{Z_k̄}) ⟶ R(i_k̄)_*(M|_{Z_k̄})` invertible. This file states the
identification under that invertibility, and proves the invertibility for a bounded below complex
`M` of injective sheaves of `Λ`-modules with torsion cohomology sheaves, by the proper base change
theorem on resolutions ([Stacks, Tag 0DDE],
`Stacks.EtaleCohomology.quasiIso_etaleModuleBaseChange_comp_of_isProper`): the restrictions of
such an `M` need not be acyclic, its terms not being torsion.

## Main definitions

* `Stacks.EtaleCohomology.frobeniusRestrictionProperDirectImageIsoOfIsIso`.

## Main results

* `Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app_of_quasiIso_map`: the unit
  `Q(Φ L) ⟶ RΦ(Q L)` is invertible when `Φ` carries an injective resolution of `L` to a
  quasi-isomorphism.
* `isIso_mapCochainComplexPlusDerivedUnit_app_fieldBaseChangeMap_of_injective`: the comparison
  `(i_k̄)_*(M|_{Z_k̄}) ⟶ R(i_k̄)_*(M|_{Z_k̄})` is invertible for a bounded below complex `M` of
  injective sheaves with torsion cohomology sheaves.
* `Stacks.EtaleCohomology.frobeniusRestrictionProperDirectImageIsoOfIsIso_hom_naturality`,
  `Stacks.EtaleCohomology.frobeniusRestrictionProperDirectImageIsoOfIsIso_hom_frobenius`.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Unit

variable {C' C : Type*} [Category* C'] [Category* C] [Abelian C'] [Abelian C] [EnoughInjectives C']
  (Φ : C' ⥤ C) [Φ.Additive]

/-- The localization `Comp⁺ ⥤ D⁺` inverts quasi-isomorphisms. -/
theorem isIso_plusQ_map_of_quasiIso_of_abelian {A : Type*} [Category* A] [Abelian A]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) (hf : QuasiIso f.hom) :
    IsIso (DerivedCategory.Plus.Q.map f) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hf
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

/-- **The unit `Q(Φ L) ⟶ RΦ(Q L)` is invertible when `Φ` carries an injective resolution of `L`
to a quasi-isomorphism**: by naturality it is then the unit at the resolution, invertible by
Leray's acyclicity lemma, up to isomorphisms. -/
theorem isIso_mapCochainComplexPlusDerivedUnit_app_of_quasiIso_map {L T : CochainComplex.Plus C'}
    (ψ : L ⟶ T) [QuasiIso ψ.hom] (hT : ∀ n, Injective (T.obj.X n))
    (hΦ : QuasiIso ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ.hom)) :
    IsIso ((Functor.mapCochainComplexPlusDerivedUnit Φ).app L) := by
  have hu : IsIso ((Functor.mapCochainComplexPlusDerivedUnit Φ).app T) :=
    isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic Φ T
      fun n => have := hT n; Functor.rightAcyclic_of_injective Φ _
  have := isIso_plusQ_map_of_quasiIso_of_abelian (Φ.mapCochainComplexPlus.map ψ) hΦ
  have := isIso_plusQ_map_of_quasiIso_of_abelian ψ inferInstance
  have hn := (Functor.mapCochainComplexPlusDerivedUnit Φ).naturality ψ
  dsimp only [Functor.comp_map] at hn
  have : IsIso ((Functor.mapCochainComplexPlusDerivedUnit Φ).app L ≫
      Φ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (Φ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ))

end Unit

/-- **The unit of `G` is invertible at `g'(M)` when a componentwise invertible base change map
`βn : I ⋙ g ⟶ g' ⋙ G` is a quasi-isomorphism on resolutions at `M`**
(`CategoryTheory.Functor.BaseChangeQuasiIsoAt`): `G` then carries an injective resolution of
`g'(M)` to a quasi-isomorphism. -/
theorem isIso_mapCochainComplexPlusDerivedUnit_app_of_baseChangeQuasiIsoAt.{v₁, u₁}
    {D' D : Type u₁} [Category.{v₁} D'] [Category.{v₁} D] [Abelian D'] [Abelian D]
    [EnoughInjectives D'] [EnoughInjectives D] (Φ : D' ⥤ D) [Φ.Additive]
    [Φ.PreservesInjectiveObjects]
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (I : A ⥤ B) (g : B ⥤ D) (g' : A ⥤ D') [I.Additive] [g.Additive] [g'.Additive]
    (βn : I ⋙ g ⟶ g' ⋙ Φ) [IsIso βn] (M : CochainComplex.Plus A)
    (h : Functor.BaseChangeQuasiIsoAt Φ I g g' βn M) :
    IsIso ((Functor.mapCochainComplexPlusDerivedUnit Φ).app (g'.mapCochainComplexPlus.obj M)) := by
  obtain ⟨T, ψ, hq, hinj, -, -⟩ := Functor.exists_twist_lift_of_injectiveResolution (𝟭 _)
    (g'.mapCochainComplexPlus.obj M) (𝟙 _)
  have := hq
  have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex βn (ComplexShape.up ℤ)).app M.obj).f n) :=
    fun n => (inferInstance : IsIso (βn.app (M.obj.X n)))
  have : IsIso ((NatTrans.mapHomologicalComplex βn (ComplexShape.up ℤ)).app M.obj) :=
    HomologicalComplex.Hom.isIso_of_components _
  have := h T ψ hq hinj
  exact isIso_mapCochainComplexPlusDerivedUnit_app_of_quasiIso_map Φ ψ hinj
    (quasiIso_of_comp_left ((NatTrans.mapHomologicalComplex βn (ComplexShape.up ℤ)).app M.obj) _)


variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {Z Y : Over (Spec (.of k))}
  (i : Z ⟶ Y) [IsProper i.left] (kbar : Type u) [Field kbar] [Algebra k kbar]

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

omit [Fintype k] in
/-- **The comparison `(i_k̄)_*(M|_{Z_k̄}) ⟶ R(i_k̄)_*(M|_{Z_k̄})` is invertible for a bounded below
complex `M` of injective sheaves with torsion cohomology sheaves**: the base change map
`(i_* M)|_{Y_k̄} ⟶ (i_k̄)_*(M|_{Z_k̄})` is an isomorphism ([Stacks, Tag 0A3U]), and followed by
`(i_k̄)_*` of an injective resolution of `M|_{Z_k̄}` it is a quasi-isomorphism by proper base
change ([Stacks, Tag 0DDE],
`Stacks.EtaleCohomology.quasiIso_etaleModuleBaseChange_comp_of_isProper`). -/
theorem isIso_mapCochainComplexPlusDerivedUnit_app_fieldBaseChangeMap_of_injective [Finite k]
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)) (hMi : ∀ n, Injective (M.obj.X n))
    (hM : isTorsionPlus.{u, 0} Λ Z.left
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj M))) :
    IsIso ((Functor.mapCochainComplexPlusDerivedUnit
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))).app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          M)) :=
  have := Fintype.ofFinite k
  have := isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isProper Λ i kbar
  have := hMi
  isIso_mapCochainComplexPlusDerivedUnit_app_of_baseChangeQuasiIsoAt
    (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))
    (etaleModuleDirectImage.{u, 0} Λ i.left)
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar))
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar))
    (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Y kbar)
      (fieldBaseChangeProj Z kbar) (fieldBaseChangeMap_comp_fst i kbar)) M
    (quasiIso_etaleModuleBaseChange_comp_of_isProper Λ i.left
      (isPullback_fieldBaseChangeMap i kbar).flip (fieldBaseChangeMap_comp_fst i kbar) M hM)


/-- **`RΓ(Z_k̄, M|_{Z_k̄}) ≅ RΓ(Y_k̄, (i_* M)|_{Y_k̄})`** for a proper morphism `i : Z ⟶ Y` over
`k` and a complex `M` at which `(i_k̄)_*(M|_{Z_k̄}) ⟶ R(i_k̄)_*(M|_{Z_k̄})` is invertible:
`RΓ(Z_k̄, -) = RΓ(Y_k̄, R(i_k̄)_* -)`, followed by the inverse of the base change isomorphism. -/
def frobeniusRestrictionProperDirectImageIsoOfIsIso
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left))
    [IsIso ((Functor.mapCochainComplexPlusDerivedUnit
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))).app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          M))] :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Z kbar M)) ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar
            ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj M))) :=
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

/-- **The identification is natural in the complex.** -/
theorem frobeniusRestrictionProperDirectImageIsoOfIsIso_hom_naturality
    {M M' : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left)} (φ : M ⟶ M')
    [IsIso ((Functor.mapCochainComplexPlusDerivedUnit
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))).app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          M))]
    [IsIso ((Functor.mapCochainComplexPlusDerivedUnit
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))).app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          M'))] :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Z.hom (specAlgebraMap k kbar))).map
          ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Z kbar).map φ)) ≫
      (frobeniusRestrictionProperDirectImageIsoOfIsIso Λ i kbar M').hom =
    (frobeniusRestrictionProperDirectImageIsoOfIsIso Λ i kbar M).hom ≫
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).map
          ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar).map
            ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.map φ))) := by
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
  show (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).map _ ≫
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
theorem frobeniusRestrictionProperDirectImageIsoOfIsIso_hom_frobenius
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z.left))
    [IsIso ((Functor.mapCochainComplexPlusDerivedUnit
      (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap i kbar))).app
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Z kbar)).mapCochainComplexPlus.obj
          M))] :
    frobeniusRestrictionCohomologyEndo.{u, 0} Λ Z kbar p q hcard M ≫
        (frobeniusRestrictionProperDirectImageIsoOfIsIso Λ i kbar M).hom =
      (frobeniusRestrictionProperDirectImageIsoOfIsIso Λ i kbar M).hom ≫
        frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
          ((etaleModuleDirectImage.{u, 0} Λ i.left).mapCochainComplexPlus.obj M) := by
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
