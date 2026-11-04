module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedTwistOuterTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusExtensionCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalFrobeniusAdditivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleSetsVerticalPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusRestrictScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision

/-!
# `RΓ_c(X_k̄, -)` does not depend on the algebraic closure

Let `k` be a finite field, `Y` a scheme over `k` and `σ : k̄₁ ≃ₐ[k] k̄₂` an isomorphism of
`k`-algebras between two fields (two algebraic closures of `k`, say). Then `Spec σ` identifies
the two geometric fibres `Y_{k̄₂} ≅ Y_{k̄₁}` over `Y`, and this identifies
`RΓ(Y_{k̄₁}, C|_{Y_{k̄₁}}) ≅ RΓ(Y_{k̄₂}, C|_{Y_{k̄₂}})` for every bounded below complex `C` on
`Y_étale`, naturally in `C` and compatibly with the canonical Frobenius actions. For `Y` a
compactification of `X` and `C = j_! K` this is the independence of `RΓ_c(X_k̄, K)` and of its
Frobenius from the choice of `k̄`, which the identification of the fibres of Laumon's Fourier
family needs ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the fibre over `v` is read
over an algebraic closure of `κ(v)`, the reference fibre over one of `k' ≅ κ(v)`.

## Main definitions

* `Stacks.EtaleCohomology.algebraClosureBaseIso`, `Stacks.EtaleCohomology.algebraClosureFibreIso`:
  `Spec k̄₂ ≅ Spec k̄₁` and `Y_{k̄₂} ≅ Y_{k̄₁}`.
* `Stacks.EtaleCohomology.algebraClosureCohomologyIso`:
  `RΓ(Y_{k̄₁}, C|_{Y_{k̄₁}}) ≅ RΓ(Y_{k̄₂}, C|_{Y_{k̄₂}})`.
* `Stacks.EtaleCohomology.compactSupportFrobeniusFunctorAlgEquivIso`:
  `RΓ_c(X_{k̄₁}, -) ≅ RΓ_c(X_{k̄₂}, -)`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleGlobalSectionsDirectImageIso_comp`: the identifications
  `Γ(Z, g_* -) = Γ(X, -)` compose.
* `Stacks.EtaleCohomology.algebraClosureCohomologyIso_comm`: the identification carries the
  Frobenius over `k̄₁` to the Frobenius over `k̄₂`.
* `Stacks.EtaleCohomology.compactSupportFrobeniusFunctorAlgEquivIso_hom_frobenius`.

The standard model `HasDerivedCategory.standard` is used because `RΓ_c` and its Frobenius are
defined there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The two geometric fibres -/

section Fibres

variable {k : Type u} [Field k] (Y : Over (Spec (.of k))) {kbar₁ kbar₂ : Type u} [Field kbar₁]
  [Algebra k kbar₁] [Field kbar₂] [Algebra k kbar₂] (σ : kbar₁ ≃ₐ[k] kbar₂)

/-- `Spec σ : Spec k̄₂ ≅ Spec k̄₁` for an isomorphism `σ : k̄₁ ≃ₐ[k] k̄₂`. -/
public def algebraClosureBaseIso : Spec (.of kbar₂) ≅ Spec (.of kbar₁) :=
  Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op

/-- `Spec σ` lies over `Spec k`. -/
@[reassoc]
public lemma algebraClosureBaseIso_hom_comp :
    (algebraClosureBaseIso σ).hom ≫ specAlgebraMap k kbar₁ = specAlgebraMap k kbar₂ := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact σ.commutes x

/-- **The identification `Y_{k̄₂} ≅ Y_{k̄₁}` of the geometric fibres**, `id_Y × Spec σ`. -/
public def algebraClosureFibreMap : fieldBaseChange Y kbar₂ ⟶ fieldBaseChange Y kbar₁ :=
  pullback.map Y.hom (specAlgebraMap k kbar₂) Y.hom (specAlgebraMap k kbar₁) (𝟙 _)
    (algebraClosureBaseIso σ).hom (𝟙 _) (by simp)
    (by rw [Category.comp_id, algebraClosureBaseIso_hom_comp])

/-- `id_Y × Spec σ : Y_{k̄₂} ⟶ Y_{k̄₁}` is an isomorphism. -/
public instance isIso_algebraClosureFibreMap : IsIso (algebraClosureFibreMap Y σ) := by
  unfold algebraClosureFibreMap
  infer_instance

/-- `id_Y × Spec σ` lies over `Y`. -/
@[reassoc]
public lemma algebraClosureFibreMap_fst :
    algebraClosureFibreMap Y σ ≫ pullback.fst Y.hom (specAlgebraMap k kbar₁) =
      pullback.fst Y.hom (specAlgebraMap k kbar₂) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- `id_Y × Spec σ` lies over `Spec σ`. -/
@[reassoc]
public lemma algebraClosureFibreMap_snd :
    algebraClosureFibreMap Y σ ≫ pullback.snd Y.hom (specAlgebraMap k kbar₁) =
      pullback.snd Y.hom (specAlgebraMap k kbar₂) ≫ (algebraClosureBaseIso σ).hom :=
  pullback.lift_snd _ _ _

variable [Fintype k] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- `id_Y × Spec σ` commutes with the base changes `π_Y × id` of the geometric Frobenius. -/
public lemma geometricFrobeniusBaseChange_comp_algebraClosureFibreMap :
    geometricFrobeniusBaseChange Y kbar₂ p q hcard ≫ algebraClosureFibreMap Y σ =
      algebraClosureFibreMap Y σ ≫ geometricFrobeniusBaseChange Y kbar₁ p q hcard := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, algebraClosureFibreMap_fst,
      geometricFrobeniusBaseChange_comp_fst, geometricFrobeniusBaseChange_comp_fst,
      algebraClosureFibreMap_fst_assoc]
  · rw [Category.assoc, Category.assoc, geometricFrobeniusBaseChange_comp_snd,
      algebraClosureFibreMap_snd, geometricFrobeniusBaseChange_comp_snd_assoc]

end Fibres

/-! ### The cohomology of the two geometric fibres -/

section Cohomology

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  {kbar₁ kbar₂ : Type u} [Field kbar₁] [Algebra k kbar₁] [Field kbar₂] [Algebra k kbar₂]
  (σ : kbar₁ ≃ₐ[k] kbar₂)

/-- The structure morphism `Y_{k̄₂} ⟶ Spec k̄₂ ≅ Spec k̄₁`. -/
public abbrev algebraClosureStructureMap : fieldBaseChange Y kbar₂ ⟶ Spec (.of kbar₁) :=
  pullback.snd Y.hom (specAlgebraMap k kbar₂) ≫ (algebraClosureBaseIso σ).hom

omit [Fintype k] in
/-- The structure morphism `Y_{k̄₂} ⟶ Spec k̄₁` factors through `id_Y × Spec σ`. -/
public lemma algebraClosureStructureMap_eq :
    algebraClosureStructureMap Y σ =
      algebraClosureFibreMap Y σ ≫ pullback.snd Y.hom (specAlgebraMap k kbar₁) :=
  (algebraClosureFibreMap_snd Y σ).symm

/-- The base change map `pr₁⁻¹ L ⟶ e_* pr₂⁻¹ 𝟙⁻¹ L` along `e = id_Y × Spec σ`. -/
public abbrev algebraClosureBaseChangeMap :=
  etaleModuleBaseChangeMap Λ (fieldBaseChangeProj Y kbar₁) (fieldBaseChangeProj Y kbar₂)
    (𝟙 Y.left) (algebraClosureFibreMap Y σ) (fieldBaseChangeProj Y kbar₂)
    (Category.comp_id _).symm (algebraClosureFibreMap_fst Y σ).symm

/-- The base change map `pr₁⁻¹ L ⟶ e_* pr₂⁻¹ 𝟙⁻¹ L` along `e = id_Y × Spec σ` is an isomorphism. -/
public instance isIso_algebraClosureBaseChangeMap (L : EtaleModules.{u, 0} Λ Y.left) :
    IsIso ((algebraClosureBaseChangeMap Λ Y σ).app L) :=
  isIso_etaleModuleBaseChangeMap_app Λ _ _ _ _ _ _ _ L

/-- The base change map applied degreewise, as an isomorphism
`C|_{Y_{k̄₁}} ≅ e_* ((𝟙⁻¹ C)|_{Y_{k̄₂}})` of bounded below complexes. -/
public def algebraClosureBaseChangeComplexIso
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar₁)).mapCochainComplexPlus.obj C ≅
      (etaleModuleDirectImage.{u, 0} Λ (algebraClosureFibreMap Y σ)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar₂)).mapCochainComplexPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ (𝟙 Y.left)).mapCochainComplexPlus.obj C)) :=
  haveI : IsIso (algebraClosureBaseChangeMap Λ Y σ) := NatIso.isIso_of_isIso_app _
  ObjectProperty.isoMk _
    ((NatIso.mapHomologicalComplex (asIso (algebraClosureBaseChangeMap Λ Y σ)) _).app C.obj)

/-- The identification `snd₂_* ⋙ Γ(Spec k̄₂, -) ≅ (snd₂ ≫ Spec σ)_* ⋙ Γ(Spec k̄₁, -)`. -/
public def algebraClosureSectionsIso :
    etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₂)) ⋙
        etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₂)) ≅
      etaleModuleDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ) ⋙
        etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁)) :=
  Functor.isoWhiskerLeft _ (etaleModuleGlobalSectionsDirectImageIso
      (algebraClosureBaseIso σ).hom Λ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (etaleModuleDirectImageComp.{u, 0} Λ _ _ _ rfl) _

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- `(snd₂ ≫ Spec σ)` is invariant under `π̄₂`. -/
public lemma algebraClosureStructureMap_frobenius :
    algebraClosureStructureMap Y σ =
      geometricFrobeniusBaseChange Y kbar₂ p q hcard ≫ algebraClosureStructureMap Y σ := by
  rw [← Category.assoc, geometricFrobeniusBaseChange_comp_toBase]

/-- The comparison `π̄₂_* ⋙ (snd₂ ≫ Spec σ)_* ≅ (snd₂ ≫ Spec σ)_*`. -/
public abbrev algebraClosureTwistComp :
    etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₂ p q hcard) ⋙
        etaleModuleDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ) ≅
      etaleModuleDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ) :=
  etaleModuleDirectImageComp.{u, 0} Λ _ _ _ (algebraClosureStructureMap_frobenius Y σ p q hcard)

/-- The sections identification is compatible with the two comparisons for `π̄₂`. -/
public lemma algebraClosureSectionsIso_comm (X : EtaleModules.{u, 0} Λ (fieldBaseChange Y kbar₂)) :
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₂))).map
        ((etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₂ p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar₂))
          (pullback.snd Y.hom (specAlgebraMap k kbar₂))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar₂ p q hcard).symm).hom.app X) ≫
        (algebraClosureSectionsIso Λ Y σ).hom.app X =
      (algebraClosureSectionsIso Λ Y σ).hom.app
          ((etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange Y kbar₂ p q hcard)).obj X) ≫
        (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).map
          ((algebraClosureTwistComp Λ Y σ p q hcard).hom.app X) := by
  have hn := (etaleModuleGlobalSectionsDirectImageIso
      (algebraClosureBaseIso σ).hom Λ).inv.naturality
    ((etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₂ p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar₂)) (pullback.snd Y.hom (specAlgebraMap k kbar₂))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar₂ p q hcard).symm).hom.app X)
  have ha := smallEtalePushforwardComp'_assoc_app (geometricFrobeniusBaseChange Y kbar₂ p q hcard)
    (pullback.snd Y.hom (specAlgebraMap k kbar₂)) (algebraClosureBaseIso σ).hom
    (pullback.snd Y.hom (specAlgebraMap k kbar₂))
    (geometricFrobeniusBaseChange_comp_toBase Y kbar₂ p q hcard).symm
    (algebraClosureStructureMap Y σ) rfl (algebraClosureStructureMap Y σ) rfl
    (algebraClosureStructureMap_frobenius Y σ p q hcard) (ModuleCat.{u + 1} Λ) X
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [algebraClosureSectionsIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hn).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (_ ≫ ·) ?_
  refine ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).map_comp _ _).symm.trans ?_
  refine Eq.trans ?_ ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).map_comp _ _)
  exact congrArg (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).map ha

/-- `C ≅ 𝟙⁻¹ C`, degreewise. -/
public def algebraClosureIdComplexIso (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    C ≅ (etaleModuleInverseImage.{u, 0} Λ (𝟙 Y.left)).mapCochainComplexPlus.obj C :=
  ObjectProperty.isoMk _
    ((NatIso.mapHomologicalComplex (etaleModuleInverseImageIdIso Λ Y.left).symm _).app C.obj)

/-- The transport of `RΓ(Spec k̄₁, R(snd₂ ≫ Spec σ)_* -)` along `e = id_Y × Spec σ`, followed by
the inverse of the base change map: `RΓ(Spec k̄₁, R(snd₂ ≫ Spec σ)_* ((𝟙⁻¹ C)|_{Y_{k̄₂}})) ≅
RΓ(Y_{k̄₁}, C|_{Y_{k̄₁}})`. -/
public def algebraClosureTransportIso (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ)).obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} Λ
              (fieldBaseChangeProj Y kbar₂)).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, 0} Λ (𝟙 Y.left)).mapCochainComplexPlus.obj C)))) ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₁))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar₁ C)) :=
  Functor.twistTransportIso
      (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₁)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁)))
      (etaleModuleDirectImage.{u, 0} Λ (algebraClosureFibreMap Y σ))
      (etaleModuleDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ))
      (etaleModuleDirectImageComp.{u, 0} Λ _ _ _ (algebraClosureStructureMap_eq Y σ)) _ ≪≫
    ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₁))).mapIso
        (DerivedCategory.Plus.Q.mapIso (algebraClosureBaseChangeComplexIso Λ Y σ C)))).symm

/-- **`RΓ(Y_{k̄₂}, C|_{Y_{k̄₂}}) ≅ RΓ(Y_{k̄₁}, C|_{Y_{k̄₁}})`** for `σ : k̄₁ ≃ₐ[k] k̄₂`:
`C ≅ 𝟙⁻¹ C`, the base `Spec k̄₂` read as `Spec k̄₁` through `Spec σ`, and the transport along
`e = id_Y × Spec σ : Y_{k̄₂} ≅ Y_{k̄₁}`. -/
public def algebraClosureCohomologyIso (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₂))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₂))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar₂ C)) ≅
      (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₁))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar₁ C)) :=
  (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₂))).mapIso
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₂))).mapIso
        (DerivedCategory.Plus.Q.mapIso
          ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj Y kbar₂)).mapCochainComplexPlus.mapIso
            (algebraClosureIdComplexIso Λ Y C)))) ≪≫
    (Functor.outerTwistIso
      (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₂)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₂)))
      (etaleModuleDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁)))
      (algebraClosureSectionsIso Λ Y σ)).app _ ≪≫
    algebraClosureTransportIso Λ Y σ C

/-- Pasting four naturality squares along a composite ending with an inverse; stated on
variables. -/
private lemma comp_four_naturality {D : Type*} [Category* D] {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : D}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₄ ≅ A₃) (a' : B₀ ⟶ B₁) (b' : B₁ ⟶ B₂)
    (c' : B₂ ⟶ B₃) (d' : B₄ ≅ B₃) (v₀ : A₀ ⟶ B₀) (v₁ : A₁ ⟶ B₁) (v₂ : A₂ ⟶ B₂) (v₃ : A₃ ⟶ B₃)
    (v₄ : A₄ ⟶ B₄) (h₀ : v₀ ≫ a' = a ≫ v₁) (h₁ : v₁ ≫ b' = b ≫ v₂) (h₂ : v₂ ≫ c' = c ≫ v₃)
    (h₃ : v₄ ≫ d'.hom = d.hom ≫ v₃) :
    v₀ ≫ a' ≫ b' ≫ c' ≫ d'.inv = (a ≫ b ≫ c ≫ d.inv) ≫ v₄ := by
  have h₃' : v₃ ≫ d'.inv = d.inv ≫ v₄ := by
    rw [Iso.comp_inv_eq, Category.assoc, h₃, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h₀, reassoc_of% h₁, reassoc_of% h₂, h₃']
  simp only [Category.assoc]

omit [Fact p.Prime] [CharP k p] in
include hcard in
/-- `q ≠ 0`, since `k` has more than one element. -/
lemma ne_zero_of_card_eq_pow_algebraClosure : q ≠ 0 := by
  rintro rfl
  rw [pow_zero] at hcard
  exact Nat.ne_of_gt Fintype.one_lt_card hcard

/-- **The identification of the cohomology of the two geometric fibres carries the Frobenius over
`k̄₂` to the Frobenius over `k̄₁`.** -/
public theorem algebraClosureCohomologyIso_comm
    (C : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)) :
    frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar₂ p q hcard C ≫
        (algebraClosureCohomologyIso Λ Y σ C).hom =
      (algebraClosureCohomologyIso Λ Y σ C).hom ≫
        frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar₁ p q hcard C := by
  have hq := ne_zero_of_card_eq_pow_algebraClosure p q hcard
  let K₂' := (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar₂)).mapCochainComplexPlus.obj
    ((etaleModuleInverseImage.{u, 0} Λ (𝟙 Y.left)).mapCochainComplexPlus.obj C)
  let τ₂ : K₂' ⟶ (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange Y kbar₂ p q hcard)).mapCochainComplexPlus.obj K₂' :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar₂ p q hcard) (ComplexShape.up ℤ)).app
        ((etaleModuleInverseImage.{u, 0} Λ (𝟙 Y.left)).mapCochainComplexPlus.obj C).obj)
  let ρ := etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₂ p q hcard)
      (algebraClosureFibreMap Y σ)
      (geometricFrobeniusBaseChange Y kbar₂ p q hcard ≫ algebraClosureFibreMap Y σ) rfl ≪≫
    (etaleModuleDirectImageComp.{u, 0} Λ (algebraClosureFibreMap Y σ)
      (geometricFrobeniusBaseChange Y kbar₁ p q hcard)
      (geometricFrobeniusBaseChange Y kbar₂ p q hcard ≫ algebraClosureFibreMap Y σ)
      (geometricFrobeniusBaseChange_comp_algebraClosureFibreMap Y σ p q hcard)).symm
  -- step 1: `C ≅ 𝟙⁻¹ C`
  have h₀ := (frobeniusRestrictionCohomologyEndo_naturality (Λ := Λ) Y kbar₂ p q hcard
    (algebraClosureIdComplexIso Λ Y C).hom).symm
  -- step 2: the base `Spec k̄₂` read as `Spec k̄₁`
  have h₁ := Functor.derivedTwistEndo_outerTwistIso
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₂ p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₂)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₂)))
    (etaleModuleDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁)))
    (algebraClosureSectionsIso Λ Y σ)
    (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₂ p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar₂)) (pullback.snd Y.hom (specAlgebraMap k kbar₂))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar₂ p q hcard).symm)
    (algebraClosureTwistComp Λ Y σ p q hcard) (algebraClosureSectionsIso_comm Λ Y σ p q hcard)
    K₂' τ₂
  -- step 3: the transport along `e`
  have h₂ := Functor.derivedTwistEndo_transport
    (P := etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₁ p q hcard))
    (F₁ := etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₁)))
    (F₂ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁)))
    (Φ := etaleModuleDirectImage.{u, 0} Λ (algebraClosureFibreMap Y σ))
    (F₁' := etaleModuleDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ))
    (κ := etaleModuleDirectImageComp.{u, 0} Λ _ _ _ (algebraClosureStructureMap_eq Y σ))
    (P' := etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₂ p q hcard))
    (θ := etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₁ p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar₁)) (pullback.snd Y.hom (specAlgebraMap k kbar₁))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar₁ p q hcard).symm)
    (θ' := algebraClosureTwistComp Λ Y σ p q hcard) (ρ := ρ)
    (fun X => map_transportTwist_comp_overDirectImageComp Λ _ _ _ _ _ _ rfl
      (geometricFrobeniusBaseChange_comp_algebraClosureFibreMap Y σ p q hcard)
      (geometricFrobeniusBaseChange_comp_toBase Y kbar₁ p q hcard).symm
      (algebraClosureStructureMap_frobenius Y σ p q hcard) (algebraClosureStructureMap_eq Y σ) X)
    K₂' τ₂
  -- step 4: the base change map intertwines the twists
  have h₃ := Functor.derivedTwistEndo_naturality
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₁ p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₁)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁)))
    (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₁ p q hcard)
      (pullback.snd Y.hom (specAlgebraMap k kbar₁)) (pullback.snd Y.hom (specAlgebraMap k kbar₁))
      (geometricFrobeniusBaseChange_comp_toBase Y kbar₁ p q hcard).symm)
    (algebraClosureBaseChangeComplexIso Λ Y σ C).hom
    (ObjectProperty.homMk ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar₁ p q hcard) (ComplexShape.up ℤ)).app C.obj))
    ((etaleModuleDirectImage.{u, 0} Λ (algebraClosureFibreMap Y σ)).mapCochainComplexPlus.map τ₂ ≫
      Functor.transportTwistMap
        (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₁ p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (algebraClosureFibreMap Y σ))
        (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar₂ p q hcard)) ρ K₂')
    (congrArg DerivedCategory.Plus.Q.map (by
      ext n : 2
      exact (etaleModuleBaseChangeMap_comp_twist Λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
        (geometricFrobeniusBaseChange_comp_algebraClosureFibreMap Y σ p q hcard)
        (geometricFrobenius Y p q hcard).left (Category.comp_id _).symm (Category.id_comp _).symm
        _ _ (fun M => smallEtalePushforward_map_etaleSheafPushforwardComparison (𝟙 Y.left) p
          (isInCharacteristic_of_over Y) (isInCharacteristic_of_over Y) hq
          (geometricFrobenius Y p q hcard).left (Category.comp_id _).symm
          (Category.id_comp _).symm (ModuleCat.{u + 1} Λ) M) (C.obj.X n)).symm))
  exact comp_four_naturality _ _ _ _ _ _ _ _ _ _ _ _ _ h₀ h₁ h₂ h₃

omit [Fintype k] in
/-- **The identification of the cohomology of the two geometric fibres is natural** in the
complex. -/
public theorem algebraClosureCohomologyIso_hom_naturality
    {C D : CochainComplex.Plus (EtaleModules.{u, 0} Λ Y.left)} (φ : C ⟶ D) :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₂))).map
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₂))).map
          ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar₂).map φ)) ≫
        (algebraClosureCohomologyIso Λ Y σ D).hom =
      (algebraClosureCohomologyIso Λ Y σ C).hom ≫
        (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).map
          ((etaleModuleDerivedDirectImage.{u, 0} Λ
            (pullback.snd Y.hom (specAlgebraMap k kbar₁))).map
            ((fieldBaseChangeRestrictionFunctor.{u, 0} Λ Y kbar₁).map φ)) := by
  let φ' := (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj Y kbar₂)).mapCochainComplexPlus.map
    ((etaleModuleInverseImage.{u, 0} Λ (𝟙 Y.left)).mapCochainComplexPlus.map φ)
  have hι : φ ≫ (algebraClosureIdComplexIso Λ Y D).hom =
      (algebraClosureIdComplexIso Λ Y C).hom ≫
        (etaleModuleInverseImage.{u, 0} Λ (𝟙 Y.left)).mapCochainComplexPlus.map φ := by
    ext n : 2
    exact ((etaleModuleInverseImageIdIso Λ Y.left).inv.naturality (φ.hom.f n))
  have h₀ := congrArg (fun t => (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₂))).map
    ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₂))).map
      (DerivedCategory.Plus.Q.map
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar₂)).mapCochainComplexPlus.map
          t)))) hι
  simp only [CategoryTheory.Functor.map_comp] at h₀
  have h₁ := (Functor.outerTwistIso
      (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₂)))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₂)))
      (etaleModuleDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ))
      (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁)))
      (algebraClosureSectionsIso Λ Y σ)).hom.naturality (DerivedCategory.Plus.Q.map φ')
  have h₂ := Functor.twistTransportIso_hom_naturality
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₁)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar₁)))
    (etaleModuleDirectImage.{u, 0} Λ (algebraClosureFibreMap Y σ))
    (etaleModuleDirectImage.{u, 0} Λ (algebraClosureStructureMap Y σ))
    (etaleModuleDirectImageComp.{u, 0} Λ _ _ _ (algebraClosureStructureMap_eq Y σ)) φ'
  have hB : (etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj Y kbar₁)).mapCochainComplexPlus.map φ ≫
      (algebraClosureBaseChangeComplexIso Λ Y σ D).hom =
      (algebraClosureBaseChangeComplexIso Λ Y σ C).hom ≫
        (etaleModuleDirectImage.{u, 0} Λ
          (algebraClosureFibreMap Y σ)).mapCochainComplexPlus.map φ' := by
    ext n : 2
    exact (algebraClosureBaseChangeMap Λ Y σ).naturality (φ.hom.f n)
  have h₃ := congrArg (fun t => (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar₁))).map
    ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar₁))).map
      (DerivedCategory.Plus.Q.map t))) hB
  simp only [CategoryTheory.Functor.map_comp] at h₃
  exact comp_four_naturality _ _ _ _ _ _ _ _ _ _ _ _ _ h₀ h₁ h₂ h₃

end Cohomology

/-! ### `RΓ_c(X_k̄, -)` does not depend on `k̄` -/

section CompactSupport

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) {kbar₁ kbar₂ : Type u} [Field kbar₁]
  [Algebra k kbar₁] [Field kbar₂] [Algebra k kbar₂] (σ : kbar₁ ≃ₐ[k] kbar₂)

/-- **`RΓ_c(X_{k̄₂}, -) ≅ RΓ_c(X_{k̄₁}, -)`** for `σ : k̄₁ ≃ₐ[k] k̄₂`, naturally in the bounded
below complex: `Stacks.EtaleCohomology.algebraClosureCohomologyIso` for the compactification and
`j_! K`. -/
public def compactSupportFrobeniusFunctorAlgEquivIso :
    compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar₂ ≅
      compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar₁ :=
  NatIso.ofComponents (fun K => algebraClosureCohomologyIso Λ (Over.mk j.toBase) σ
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K))
    (fun g => algebraClosureCohomologyIso_hom_naturality Λ (Over.mk j.toBase) σ
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.map g))

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The identification `RΓ_c(X_{k̄₂}, -) ≅ RΓ_c(X_{k̄₁}, -)` carries the canonical Frobenius over
`k̄₂` to the canonical Frobenius over `k̄₁`.** -/
public theorem compactSupportFrobeniusFunctorAlgEquivIso_hom_frobenius :
    canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar₂ p q hcard ≫
        (compactSupportFrobeniusFunctorAlgEquivIso Λ f j σ).hom =
      (compactSupportFrobeniusFunctorAlgEquivIso Λ f j σ).hom ≫
        canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar₁ p q hcard := by
  ext K : 2
  exact algebraClosureCohomologyIso_comm Λ (Over.mk j.toBase) σ p q hcard
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj K)

/-- **`Hⁱ_c(X_{k̄₂}, -) ≅ Hⁱ_c(X_{k̄₁}, -)`** on sheaves, naturally. -/
public def compactSupportSheafCohomologyAlgEquivIso (i : ℤ) :
    compactSupportSheafCohomology Λ f j kbar₂ i ≅ compactSupportSheafCohomology Λ f j kbar₁ i :=
  Functor.isoWhiskerLeft (sheafSingleComplex Λ)
    (Functor.isoWhiskerRight (compactSupportFrobeniusFunctorAlgEquivIso Λ f j σ)
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i))

/-- The identification of `Hⁱ_c` on sheaves carries `π_X^*` over `k̄₂` to `π_X^*` over `k̄₁`. -/
public theorem compactSupportSheafCohomologyAlgEquivIso_hom_frobenius (i : ℤ) :
    compactSupportSheafFrobenius Λ f j kbar₂ p q hcard i ≫
        (compactSupportSheafCohomologyAlgEquivIso Λ f j σ i).hom =
      (compactSupportSheafCohomologyAlgEquivIso Λ f j σ i).hom ≫
        compactSupportSheafFrobenius Λ f j kbar₁ p q hcard i := by
  ext G : 2
  have h := congrArg (fun t => NatTrans.app t ((sheafSingleComplex Λ).obj G))
    (compactSupportFrobeniusFunctorAlgEquivIso_hom_frobenius Λ f j σ p q hcard)
  simp only [NatTrans.comp_app] at h
  simp only [compactSupportSheafCohomologyAlgEquivIso, compactSupportSheafFrobenius,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, ← CategoryTheory.Functor.map_comp, h]

end CompactSupport

end Stacks.EtaleCohomology

end
