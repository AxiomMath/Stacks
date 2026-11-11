module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.AffineRightAdjointDerivedHom
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QcqsTrace
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChange

/-!
# The trace map of an affine morphism

Let `A → B` be a homomorphism of commutative rings, let `Y = Spec A` and `X = Spec B`, and let
`f : X ⟶ Y` be the induced morphism. The right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`
sends an object `K` of `D(A) = D_QCoh(𝒪_Y)` to `RHom_A(B, K)` in `D(B) = D_QCoh(𝒪_X)`
([Stacks, Tag 0A9F]), and the trace map `Tr_{f, K} : Rf_* a(K) ⟶ K` of [Stacks, Tag 0AWG] is the
map `RHom_A(B, K) ⟶ RHom_A(A, K) = K` induced by the `A`-module map `A ⟶ B`. This is
[Stacks, Example 0B6L], and this file proves it for the trace `Stacks.Duality.qcqsTrace` of the
scheme morphism `Spec B ⟶ Spec A`.

## Main definitions

* `Dualizing.AnyModel.derivedHomAdjunction` — the derived restriction–Hom adjunction
  `Res ⊣ RHom_A(B, -)` at arbitrary chosen models of `D(A)` and `D(B)` (morphisms in `Type u`,
  as at the locally small models), whose counit is the
  Kan-extension lift of the evaluation counit `Hom_A(B, M) ⟶ M`, `g ↦ g(1)`.
* `AlgebraicGeometry.derivedTildeCompTwistedInverseImageIsoDerivedHom` — the identification
  `a(K~) ≅ RHom_A(B, K)~` of [Stacks, Tag 0A9F] for the right adjoint `a` of [Stacks, Tag 0A9E]
  whose counit is `Stacks.Duality.qcqsTrace`, chosen compatibly with the two counits.

## Main results

* `Dualizing.AnyModel.derivedHomAdjunction_counit_app` — on complexes the counit of the derived
  adjunction is induced by evaluation at `1`, that is by precomposition with `A ⟶ B` followed by
  `Hom_A(A, M) = M`.
* `AlgebraicGeometry.qcqsTrace_specMap_app_derivedTilde` — **[Stacks, Example 0B6L]**: under the
  identifications `a(K~) ≅ RHom_A(B, K)~` and `Rf_*(M~) ≅ (M_A)~` of [Stacks, Tag 0A9F], the trace
  `Tr_{f, K~}` is derived sheafification of the counit `RHom_A(B, K) ⟶ K` of the algebraic
  adjunction.
* `AlgebraicGeometry.qcqsTrace_specMap_app_derivedTilde_Qh` — the same on a complex `K` of
  `A`-modules: through the comparison `Hom_A(B, K) ⟶ RHom_A(B, K)`, the trace is derived
  sheafification of the map `Hom_A(B, K) ⟶ K`, `g ↦ g(1)`, induced by `A ⟶ B`. For `K`
  K-injective that comparison is an isomorphism, so this computes the trace outright.

## Implementation notes

The algebraic adjunction must be the one at the locally small model `ModuleCat.hasDerivedCategory`,
at which derived sheafification `AlgebraicGeometry.derivedTilde` and the scheme-level derived
categories are stated; `Dualizing.derivedHomAdjunction` is the same construction at
`CategoryTheory.HasDerivedCategory.standard`. The existence statement
`Dualizing.AnyModel.restrictScalarsDerived_adj_derivedHom` gives the adjunction only up to
`Nonempty`, so its counit is not determined, which is why the adjunction is rebuilt here from the
underived one by `CategoryTheory.Adjunction.derived`.

The right adjoint `a` of `Rf_*` is `Stacks.Duality.twistedInverseImage`, a choice of right adjoint;
two right adjoints are canonically isomorphic, compatibly with their counits
(`CategoryTheory.Adjunction.rightAdjointUniq`). The identification of `a(K~)` with
`RHom_A(B, K)~` used below is that canonical isomorphism to the explicit right adjoint
`AlgebraicGeometry.affineTwistedInverseImage`, followed by the cancellation of derived
sheafification with its quasi-inverse.

## References

* [Stacks Project, Tag 0B6L](https://stacks.math.columbia.edu/tag/0B6L)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe u

namespace Dualizing.AnyModel

variable {A B : Type u} [CommRing A] [CommRing B]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]

/-- The comparison `Hom_A(B, -) ⟶ RHom_A(B, -)` from coextension of scalars on complexes to its
total right derived functor, at arbitrary chosen models of `D(A)` and `D(B)` whose morphisms lie
in `Type u`. -/
def derivedHomComparison (f : A →+* B) :
    (ModuleCat.coextendScalars.{u, u, u} f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedHom.{u, u, u, u, u} f := by
  have := Dualizing.AnyModel.coextendScalars_hasPointwiseRightDerivedFunctor.{u, u, u, u} f
  exact Functor.totalRightDerivedUnit _ DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ))

/-- **The derived restriction–Hom adjunction at arbitrary chosen models** of `D(A)` and `D(B)`
whose morphisms lie in `Type u`, such as the locally small models. Restriction of scalars
`D(B) ⥤ D(A)` is left adjoint to `RHom_A(B, -)`, by the adjunction induced from the ordinary
restriction–coextension adjunction, so that its counit is the Kan-extension lift of the ordinary
evaluation counit. -/
def derivedHomAdjunction (f : A →+* B) :
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⊣
      derivedHom.{u, u, u, u, u} f := by
  have := Dualizing.AnyModel.coextendScalars_hasPointwiseRightDerivedFunctor.{u, u, u, u} f
  let G := ModuleCat.restrictScalars.{u} f
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)
  let W' := HomotopyCategory.quasiIso (ModuleCat.{u} B) (.up ℤ)
  let α := G.mapDerivedCategoryFactorsh.hom
  let β := derivedHomComparison f
  have : (derivedHom.{u, u, u, u, u} f).IsRightDerivedFunctor β W := by
    dsimp [derivedHom, β, derivedHomComparison, W]
    infer_instance
  have : G.mapDerivedCategory.IsLeftDerivedFunctor α W' :=
    Functor.isLeftDerivedFunctor_of_inverts W' _ G.mapDerivedCategoryFactorsh
  let a := (restrictScalarsDerived_adj_derivedHom.{u, u, u, u, u} f).some
  have : G.mapDerivedCategory.IsLeftAdjoint := a.isLeftAdjoint
  have : (derivedHom.{u, u, u, u, u} f).IsRightAdjoint := a.isRightAdjoint
  exact (homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{u} f)
    (.up ℤ)).derived W' W α β

/-- **On complexes the derived counit is induced by evaluation at `1`.** For a complex `K` of
`A`-modules, the counit `Res RHom_A(B, K) ⟶ K` of `Dualizing.AnyModel.derivedHomAdjunction`,
precomposed with the comparison `Hom_A(B, K) ⟶ RHom_A(B, K)`, is the map induced by the ordinary
counit `Hom_A(B, K) ⟶ K`, `g ↦ g(1)`: precomposition with the `A`-module map `A ⟶ B` followed by
`Hom_A(A, K) = K`. -/
theorem derivedHomAdjunction_counit_app (f : A →+* B)
    (K : HomotopyCategory (ModuleCat.{u} A) (.up ℤ)) :
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
        ((derivedHomComparison f).app K) ≫
      (derivedHomAdjunction f).counit.app (DerivedCategory.Qh.obj K) =
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactorsh.hom.app
        (((ModuleCat.coextendScalars.{u, u, u} f).mapHomotopyCategory
          (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{u} f)
          (.up ℤ)).counit.app K) := by
  have := Dualizing.AnyModel.coextendScalars_hasPointwiseRightDerivedFunctor.{u, u, u, u} f
  let G := ModuleCat.restrictScalars.{u} f
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)
  let W' := HomotopyCategory.quasiIso (ModuleCat.{u} B) (.up ℤ)
  let α := G.mapDerivedCategoryFactorsh.hom
  let β := derivedHomComparison f
  have : (derivedHom.{u, u, u, u, u} f).IsRightDerivedFunctor β W := by
    dsimp [derivedHom, β, derivedHomComparison, W]
    infer_instance
  have : G.mapDerivedCategory.IsLeftDerivedFunctor α W' :=
    Functor.isLeftDerivedFunctor_of_inverts W' _ G.mapDerivedCategoryFactorsh
  let a := (restrictScalarsDerived_adj_derivedHom.{u, u, u, u, u} f).some
  have : G.mapDerivedCategory.IsLeftAdjoint := a.isLeftAdjoint
  have : (derivedHom.{u, u, u, u, u} f).IsRightAdjoint := a.isRightAdjoint
  exact (homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{u} f)
    (.up ℤ)).derivedε_fac_app W α β K

/-- On a K-injective complex `I` the comparison `Hom_A(B, I) ⟶ RHom_A(B, I)` is an isomorphism. -/
theorem isIso_derivedHomComparison_app_of_isKInjective (f : A →+* B)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedHomComparison f).app
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj I)) := by
  have := Dualizing.AnyModel.coextendScalars_hasPointwiseRightDerivedFunctor.{u, u, u, u} f
  have : (derivedHom.{u, u, u, u, u} f).IsRightDerivedFunctor
      (derivedHomComparison f)
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (.up ℤ)) := by
    dsimp [derivedHom, derivedHomComparison]
    infer_instance
  have : EnoughInjectives (ModuleCat.{u} A) := ModuleCat.enoughInjectives.{u, u} A
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      ((ModuleCat.coextendScalars.{u, u, u} f).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K ↦
        let ⟨J, q, hq, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective K
        ⟨J, q, hJ, hq⟩)).2
    DerivedCategory.Qh (derivedHom.{u, u, u, u, u} f) (derivedHomComparison f)
    I hI

end Dualizing.AnyModel

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']

/-- **The counit of a conjugated adjunction.** In the situation of
`CategoryTheory.Adjunction.ofSquare`, at an object `eR.functor K` the counit of
`P ⊣ eR.inverse ⋙ RH ⋙ eS.functor` is the counit of `Res ⊣ RH` at `K`, transported by the square
`h` and by the unit of `eR`. -/
theorem ofSquare_counit_app_functor (eR : C ≌ C') (eS : D ≌ D')
    {P : D' ⥤ C'} {Res : D ⥤ C} {RH : C ⥤ D} (adjRes : Res ⊣ RH)
    (h : eS.functor ⋙ P ≅ Res ⋙ eR.functor) (K : C) :
    (ofSquare eR eS adjRes h).counit.app (eR.functor.obj K) =
      P.map (eS.functor.map (RH.map (eR.unitInv.app K))) ≫ h.hom.app (RH.obj K) ≫
        eR.functor.map (adjRes.counit.app K) := by
  have hn₁ := h.hom.naturality (eS.unit.app (RH.obj (eR.inverse.obj (eR.functor.obj K))))
  have hn₂ := h.hom.naturality (RH.map (eR.unitInv.app K))
  have hn₃ := adjRes.counit.naturality (eR.unitInv.app K)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn₁ hn₂ hn₃
  simp only [ofSquare, ofNatIsoLeft, comp_counit_app, Equivalence.toAdjunction,
    Equivalence.symm_inverse, Trans.trans, Equivalence.symm_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id, Category.assoc,
    Functor.comp_obj]
  rw [Equivalence.counitInv_app_functor, reassoc_of% hn₁, Equivalence.counit_app_functor,
    reassoc_of% hn₂]
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  rw [hn₃]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Equivalence.unitIso_hom_inv_id_app, Functor.map_id,
    Category.id_comp]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

/-- Cancelling an isomorphism against its inverse inside a functor: if `T = F.map i.hom ≫ g`, then
`F.map (a ≫ i.inv) ≫ T = F.map a ≫ g`. -/
private theorem map_comp_inv_comp_eq_map_comp {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B Z : C} {W : D} (a : A ⟶ B) (i : Z ≅ B) (T : F.obj Z ⟶ W)
    (g : F.obj B ⟶ W) (h : T = F.map i.hom ≫ g) :
    F.map (a ≫ i.inv) ≫ T = F.map a ≫ g := by
  rw [h, ← Category.assoc, ← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The adjunction `Rf_* ⊣ AlgebraicGeometry.affineTwistedInverseImage φ` for `f = Spec φ`,
obtained by conjugating `Dualizing.AnyModel.derivedHomAdjunction` along derived sheafification. -/
def derivedQuasicoherentPushforwardAdjAffineTwistedInverseImage :
    derivedQuasicoherentPushforward (Spec.map φ) ⊣ affineTwistedInverseImage φ :=
  Adjunction.ofSquare (derivedTilde R).asEquivalence (derivedTilde S).asEquivalence
    (Dualizing.AnyModel.derivedHomAdjunction φ.hom)
    (derivedTildeCompDerivedQuasicoherentPushforwardIso φ)

/-- **The counit of the conjugated adjunction.** At `K~`, the counit of
`AlgebraicGeometry.derivedQuasicoherentPushforwardAdjAffineTwistedInverseImage φ` is, under
`a(K~) ≅ RHom_R(S, K)~` and `Rf_*(M~) ≅ (M_R)~`, derived sheafification of the counit of the
algebraic adjunction `Dualizing.AnyModel.derivedHomAdjunction`. -/
theorem derivedQuasicoherentPushforwardAdjAffineTwistedInverseImage_counit_app
    (K : DerivedCategory (ModuleCat.{u} R)) :
    (derivedQuasicoherentPushforwardAdjAffineTwistedInverseImage φ).counit.app
        ((derivedTilde R).obj K) =
      (derivedQuasicoherentPushforward (Spec.map φ)).map
          ((derivedTilde_comp_affineTwistedInverseImageIsoDerivedHom φ).hom.app K) ≫
        (derivedTildeCompDerivedQuasicoherentPushforwardIso φ).hom.app
          ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom).obj K) ≫
        (derivedTilde R).map
          ((Dualizing.AnyModel.derivedHomAdjunction φ.hom).counit.app K) := by
  have hdt : (derivedTilde_comp_affineTwistedInverseImageIsoDerivedHom φ).hom.app K =
      (derivedTilde S).map ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom).map
        ((derivedTilde R).asEquivalence.unitInv.app K)) := by
    exact (Category.id_comp _).trans (Category.comp_id _)
  rw [hdt]
  exact Adjunction.ofSquare_counit_app_functor _ _ _ _ K

/-- **The right adjoint of `Rf_*` for `f = Spec φ` is `RHom_R(S, -)`, compatibly with the trace.**
For the right adjoint `a = Stacks.Duality.twistedInverseImage (Spec.map φ) _` of
[Stacks, Tag 0A9E], whose counit is the trace `Stacks.Duality.qcqsTrace`, this is the isomorphism
`a(K~) ≅ RHom_R(S, K)~` of [Stacks, Tag 0A9F]: the canonical isomorphism of right adjoints from
`a` to `AlgebraicGeometry.affineTwistedInverseImage φ`
(`CategoryTheory.Adjunction.rightAdjointUniq`, which respects the counits), followed by
`AlgebraicGeometry.derivedTilde_comp_affineTwistedInverseImageIsoDerivedHom`. -/
def derivedTildeCompTwistedInverseImageIsoDerivedHom :
    derivedTilde R ⋙ Stacks.Duality.twistedInverseImage (Spec.map φ)
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map φ)) ≅
      Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom ⋙ derivedTilde S :=
  Functor.isoWhiskerLeft (derivedTilde R)
      (Adjunction.rightAdjointUniq
        (Stacks.Duality.twistedInverseImageAdjunction (Spec.map φ)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map φ)))
        (derivedQuasicoherentPushforwardAdjAffineTwistedInverseImage φ)) ≪≫
    derivedTilde_comp_affineTwistedInverseImageIsoDerivedHom φ

/-- **Stacks 0B6L.** Let `φ : R ⟶ S` be a ring map, `Y = Spec R`, `X = Spec S` and
`f = Spec φ : X ⟶ Y`, and let `a` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.
For `K` in `D(R)`, identify `a(K~)` with `RHom_R(S, K)~`
(`AlgebraicGeometry.derivedTildeCompTwistedInverseImageIsoDerivedHom`, [Stacks, Tag 0A9F]) and
`Rf_*(M~)` with `(M_R)~` (`AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso`,
[Stacks, Tag 0DJK]). Then the trace `Tr_{f, K~} : Rf_* a(K~) ⟶ K~` of [Stacks, Tag 0AWG] is
derived sheafification of the map `RHom_R(S, K) ⟶ K` which is the counit of the derived
restriction–Hom adjunction `Dualizing.AnyModel.derivedHomAdjunction`.

That counit is the map induced by the `R`-module map `R ⟶ S`: on complexes it is evaluation at
`1`, `Hom_R(S, K) ⟶ Hom_R(R, K) = K`
(`Dualizing.AnyModel.derivedHomAdjunction_counit_app`); the statement with that substituted is
`AlgebraicGeometry.qcqsTrace_specMap_app_derivedTilde_Qh`. -/
@[stacks 0B6L "the trace map Tr_f of f = Spec(S) → Spec(R) is, under a(K~) ≅ RHom_R(S, K)~ and \
Rf_*(M~) ≅ (M_R)~, the map RHom_R(S, K) → K of the derived restriction–Hom adjunction"]
theorem qcqsTrace_specMap_app_derivedTilde (K : DerivedCategory (ModuleCat.{u} R)) :
    (Stacks.Duality.qcqsTrace (Spec.map φ)).app ((derivedTilde R).obj K) =
      (derivedQuasicoherentPushforward (Spec.map φ)).map
          ((derivedTildeCompTwistedInverseImageIsoDerivedHom φ).hom.app K) ≫
        (derivedTildeCompDerivedQuasicoherentPushforwardIso φ).hom.app
          ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom).obj K) ≫
        (derivedTilde R).map
          ((Dualizing.AnyModel.derivedHomAdjunction φ.hom).counit.app K) := by
  have h₁ := Adjunction.rightAdjointUniq_hom_app_counit
    (Stacks.Duality.twistedInverseImageAdjunction (Spec.map φ)
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs (Spec.map φ)))
    (derivedQuasicoherentPushforwardAdjAffineTwistedInverseImage φ) ((derivedTilde R).obj K)
  simp only [derivedQuasicoherentPushforwardAdjAffineTwistedInverseImage_counit_app] at h₁
  refine h₁.symm.trans ?_
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((derivedQuasicoherentPushforward (Spec.map φ)).map_comp _ _).symm)

/-- **Stacks 0B6L, on complexes: the trace is induced by `R ⟶ S`.** Let `φ : R ⟶ S`,
`f = Spec φ`, and let `K` be a complex of `R`-modules. Through the comparison
`Hom_R(S, K) ⟶ RHom_R(S, K)` and the identifications of
`AlgebraicGeometry.qcqsTrace_specMap_app_derivedTilde`, the trace `Tr_{f, K~}` is derived
sheafification of the map `Hom_R(S, K) ⟶ K`, `g ↦ g(1)`, that is of precomposition with the
`R`-module map `R ⟶ S` followed by `Hom_R(R, K) = K`. When `K` is K-injective the comparison is an
isomorphism (`Dualizing.AnyModel.isIso_derivedHomComparison_app_of_isKInjective`), so this
computes `Tr_{f, K~}` itself. -/
@[stacks 0B6L "on complexes: through Hom_R(S, K) → RHom_R(S, K), the trace is the map \
Hom_R(S, K) → K induced by R → S, an isomorphism for K K-injective"]
theorem qcqsTrace_specMap_app_derivedTilde_Qh
    (K : HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :
    (derivedQuasicoherentPushforward (Spec.map φ)).map
        ((derivedTilde S).map
            ((Dualizing.AnyModel.derivedHomComparison φ.hom).app K) ≫
          (derivedTildeCompTwistedInverseImageIsoDerivedHom φ).inv.app
            (DerivedCategory.Qh.obj K)) ≫
      (Stacks.Duality.qcqsTrace (Spec.map φ)).app
        ((derivedTilde R).obj (DerivedCategory.Qh.obj K)) =
    (derivedTildeCompDerivedQuasicoherentPushforwardIso φ).hom.app
        (DerivedCategory.Qh.obj
          (((ModuleCat.coextendScalars.{u, u, u} φ.hom).mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (derivedTilde R).map
        ((ModuleCat.restrictScalars.{u} φ.hom).mapDerivedCategoryFactorsh.hom.app
            (((ModuleCat.coextendScalars.{u, u, u} φ.hom).mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Dualizing.homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{u} φ.hom)
              (.up ℤ)).counit.app K)) := by
  have hn : (derivedQuasicoherentPushforward (Spec.map φ)).map
        ((derivedTilde S).map ((Dualizing.AnyModel.derivedHomComparison φ.hom).app K)) ≫
      (derivedTildeCompDerivedQuasicoherentPushforwardIso φ).hom.app
        ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom).obj (DerivedCategory.Qh.obj K)) =
      (derivedTildeCompDerivedQuasicoherentPushforwardIso φ).hom.app
        (DerivedCategory.Qh.obj
          (((ModuleCat.coextendScalars.{u, u, u} φ.hom).mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (derivedTilde R).map ((ModuleCat.restrictScalars.{u} φ.hom).mapDerivedCategory.map
        ((Dualizing.AnyModel.derivedHomComparison φ.hom).app K)) :=
    (derivedTildeCompDerivedQuasicoherentPushforwardIso φ).hom.naturality
      ((Dualizing.AnyModel.derivedHomComparison φ.hom).app K)
  refine (map_comp_inv_comp_eq_map_comp _ _
    ((derivedTildeCompTwistedInverseImageIsoDerivedHom φ).app (DerivedCategory.Qh.obj K)) _ _
    (qcqsTrace_specMap_app_derivedTilde φ (DerivedCategory.Qh.obj K))).trans ?_
  have key : (derivedQuasicoherentPushforward (Spec.map φ)).map
        ((derivedTilde S).map ((Dualizing.AnyModel.derivedHomComparison φ.hom).app K)) ≫
      (derivedTildeCompDerivedQuasicoherentPushforwardIso φ).hom.app
        ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u} φ.hom).obj (DerivedCategory.Qh.obj K)) ≫
      (derivedTilde R).map ((Dualizing.AnyModel.derivedHomAdjunction φ.hom).counit.app
        (DerivedCategory.Qh.obj K)) =
    (derivedTildeCompDerivedQuasicoherentPushforwardIso φ).hom.app
        (DerivedCategory.Qh.obj
          (((ModuleCat.coextendScalars.{u, u, u} φ.hom).mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (derivedTilde R).map
        ((ModuleCat.restrictScalars.{u} φ.hom).mapDerivedCategoryFactorsh.hom.app
            (((ModuleCat.coextendScalars.{u, u, u} φ.hom).mapHomotopyCategory (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map
            ((Dualizing.homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{u} φ.hom)
              (.up ℤ)).counit.app K)) := by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (((derivedTilde R).map_comp _ _).symm.trans
        (congrArg (derivedTilde R).map
          (Dualizing.AnyModel.derivedHomAdjunction_counit_app φ.hom K))))))
  exact key

end AlgebraicGeometry

end
