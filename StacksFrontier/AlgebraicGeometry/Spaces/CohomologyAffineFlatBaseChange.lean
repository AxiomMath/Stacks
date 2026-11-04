module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangePushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapseUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerCohomologyReesFinite

/-!
# Flat base change of cohomology over an affine base

Let `q : W ⟶ V` be a flat morphism of affine schemes of the site, `A = Γ(V, 𝒪)`, `R = Γ(W, 𝒪)`,
let `p : X ⟶ V` be a quasi-compact and quasi-separated morphism from an algebraic space, let
`X' = W ×_V X` with projections `pr : X' ⟶ X`, `pr' : X' ⟶ W`, and let `ℱ` be a quasi-coherent
`𝒪_X`-module with pullback `ℱ' = pr^* ℱ`.  Then

`H^i(X, ℱ) ⊗_A R ≅ H^i(X', ℱ')`

as `R`-modules, for every `i ≥ 0`.

## Main definitions

* `AlgebraicGeometry.Space.cohomologyIsoOfAbelianSheafIso`: an isomorphism of an abelian sheaf
  with the underlying abelian sheaf of an `𝒪_X`-module induces one of cohomologies.
* `AlgebraicGeometry.Space.cohomologySectionsTensorBaseChangeIso`:
  `H^i(X, ℱ ⊗_A R) ≅ H^i(X', ℱ')`.
* `AlgebraicGeometry.Space.cohomologyFlatBaseChangeEquiv`: the `R`-linear isomorphism
  `R ⊗_A H^i(X, ℱ) ≅ H^i(X', ℱ')`.

## Main results

* `AlgebraicGeometry.Space.cohomologyFlatBaseChangeEquiv_tmul`: the isomorphism sends `r ⊗ x`
  to `r · c(x)`, where `c : H^i(X, ℱ) ⟶ H^i(X', ℱ')` is its value on `1 ⊗ x`.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cohomology of an abelian sheaf isomorphic to a module -/

section Comparison

variable {X : AlgebraicSpaces B S hS}

/-- An isomorphism `𝒢 ≅ M` of an abelian sheaf with the underlying abelian sheaf of an
`𝒪_X`-module induces `H^i(X, 𝒢) ≅ H^i(X, M)`, the latter computed as cohomology of
`𝒪_X`-modules. -/
def cohomologyIsoOfAbelianSheafIso
    {𝒢 : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}}
    {M : Modules.{u, u} B S hS X.1 X.2} (e : 𝒢 ≅ (moduleToAbelianSheaf B S hS X).obj M) (i : ℕ) :
    ((Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived i).obj 𝒢 ≅
      (forget₂ _ AddCommGrpCat.{u + 1}).obj ((spaceCohomology B S hS X i).obj M) :=
  ((Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived i).mapIso e ≪≫
    ((moduleCohomologyForgetIso B S hS X i).app M).symm

/-- Naturality of a composite `e₁ ≪≫ e₂.symm` whose two factors are natural for the same `m`. -/
private theorem trans_symm_hom_naturality {C : Type*} [Category C] {P Q R : C} (e₁ : P ≅ Q)
    (e₂ : R ≅ Q) (w : P ⟶ P) (m : Q ⟶ Q) (n : R ⟶ R) (h₁ : w ≫ e₁.hom = e₁.hom ≫ m)
    (h₂ : n ≫ e₂.hom = e₂.hom ≫ m) : w ≫ (e₁ ≪≫ e₂.symm).hom = (e₁ ≪≫ e₂.symm).hom ≫ n := by
  have h₂' : m ≫ e₂.inv = e₂.inv ≫ n := by
    rw [Iso.comp_inv_eq, Category.assoc, h₂, Iso.inv_hom_id_assoc]
  rw [Iso.trans_hom, Iso.symm_hom, reassoc_of% h₁, h₂', Category.assoc]

/-- `AlgebraicGeometry.Space.cohomologyIsoOfAbelianSheafIso` carries an endomorphism of `𝒢` to
the endomorphism of `M` it corresponds to. -/
theorem cohomologyIsoOfAbelianSheafIso_hom_naturality
    {𝒢 : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}}
    {M : Modules.{u, u} B S hS X.1 X.2} (e : 𝒢 ≅ (moduleToAbelianSheaf B S hS X).obj M) (i : ℕ)
    (w : 𝒢 ⟶ 𝒢) (g : M ⟶ M) (h : w ≫ e.hom = e.hom ≫ (moduleToAbelianSheaf B S hS X).map g) :
    ((Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived i).map w ≫
        (cohomologyIsoOfAbelianSheafIso B S hS e i).hom =
      (cohomologyIsoOfAbelianSheafIso B S hS e i).hom ≫
        (forget₂ _ AddCommGrpCat.{u + 1}).map ((spaceCohomology B S hS X i).map g) := by
  have h1 := congrArg ((Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).rightDerived
    i).map h
  rw [Functor.map_comp, Functor.map_comp] at h1
  exact trans_symm_hom_naturality _ _ _ _ _ h1
    ((moduleCohomologyForgetIso B S hS X i).hom.naturality g)

/-- On cohomology of `𝒪_X`-modules, multiplication by a global function `s` is `s • -`. -/
theorem spaceCohomology_map_globalSmul_apply (i : ℕ) (M : Modules.{u, u} B S hS X.1 X.2)
    (s : GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (y : (spaceCohomology B S hS X i).obj M) :
    ((spaceCohomology B S hS X i).map (globalSmul _ s M)).hom y = s • y := by
  have h' : (spaceCohomology B S hS X i).map (globalSmul _ s M) = s • 𝟙 _ :=
    (congrArg (spaceCohomology B S hS X i).map (globalSmul_eq_smul_id _ s M)).trans
      ((Functor.map_smul (spaceCohomology B S hS X i) s (𝟙 M)).trans
        (congrArg (s • ·) ((spaceCohomology B S hS X i).map_id M)))
  rw [h']
  rfl

end Comparison

/-! ### The comparison over an affine base -/

section Affine

variable {V W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (q : W ⟶ V) {X : AlgebraicSpaces B S hS}
  (p : X ⟶ schemeSpace V) (F : Modules.{u, u} B S hS X.1 X.2)

/-- The projection `pr : X' = W ×_V X ⟶ X` is affine. -/
theorem isAffineHom_pullback_snd_schemeSpaceMap :
    IsAffineHom B S hS (pullback.snd (schemeSpaceMap q) p).hom :=
  IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _
    (IsPullback.of_hasPullback (schemeSpaceMap q) p)) (isAffineHom_yoneda_map B S hS q)

/-- The isomorphism `H^i(X, ℱ ⊗_A R) ≅ H^i(X', ℱ')` for a quasi-coherent `ℱ`. -/
abbrev cohomologySectionsTensorBaseChangeIso (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i).obj
        (baseChangeTensorModule B S hS q) ≅
      (forget₂ _ AddCommGrpCat.{u + 1}).obj ((spaceCohomology B S hS (pullback (schemeSpaceMap q) p)
        i).obj ((modulePullback B S hS (pullback.snd (schemeSpaceMap q) p)).obj F)) :=
  cohomologyIsoOfAbelianSheafIso B S hS (sectionsTensorPushforwardPullbackIso B S hS p q
      (pullback.fst _ _) (IsPullback.of_hasPullback (schemeSpaceMap q) p)
      (relativelyRepresentable_of_isAffineHom B S hS _
        (isAffineHom_pullback_snd_schemeSpaceMap B S hS q p)) F hF) i ≪≫
    (cohomologyIsoOfIsAffineHom B S hS _ (isAffineHom_pullback_snd_schemeSpaceMap B S hS q p) _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ F hF) i).symm

/-- `H^i(X, ℱ ⊗_A R) ≅ H^i(X', ℱ')` carries multiplication by `r` on `R` to multiplication by
`pr'^♯ r`. -/
theorem cohomologySectionsTensorBaseChangeIso_hom_naturality (hF : F.IsQuasicoherentOnSite)
    (i : ℕ) (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) :
    (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i).map
        (baseChangeTensorModuleMul B S hS q r) ≫
        (cohomologySectionsTensorBaseChangeIso B S hS q p F hF i).hom =
      (cohomologySectionsTensorBaseChangeIso B S hS q p F hF i).hom ≫
        (forget₂ _ AddCommGrpCat.{u + 1}).map
          ((spaceCohomology B S hS (pullback (schemeSpaceMap q) p) i).map
            (globalSmul _ (pullbackFunction B S hS (pullback.fst (schemeSpaceMap q) p) r)
              ((modulePullback B S hS (pullback.snd (schemeSpaceMap q) p)).obj F))) := by
  have hpr := isAffineHom_pullback_snd_schemeSpaceMap B S hS q p
  have hF' := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (pullback.snd (schemeSpaceMap q) p) F hF
  have h1 := cohomologyIsoOfAbelianSheafIso_hom_naturality B S hS
    (sectionsTensorPushforwardPullbackIso B S hS p q
      (pullback.fst _ _) (IsPullback.of_hasPullback (schemeSpaceMap q) p)
      (relativelyRepresentable_of_isAffineHom B S hS _ hpr) F hF) i _ _
    (sectionsTensorPushforwardPullbackIso_hom_naturality B S hS p q (pullback.fst _ _)
      (IsPullback.of_hasPullback (schemeSpaceMap q) p)
      (relativelyRepresentable_of_isAffineHom B S hS _ hpr) F hF r)
  have h2 := cohomologyIsoOfIsAffineHom_hom_naturality B S hS _ hpr
    (globalSmul _ (pullbackFunction B S hS (pullback.fst (schemeSpaceMap q) p) r)
      ((modulePullback B S hS (pullback.snd (schemeSpaceMap q) p)).obj F)) hF' hF' i
  exact trans_symm_hom_naturality _ _ _ _ _ h1
    (by convert h2 using 2)

/-- The isomorphism `H^i(X, ℱ ⊗_A A) ≅ H^i(X, ℱ)`. -/
abbrev cohomologySectionsTensorUnitIso (i : ℕ) :
    (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ≅
      (forget₂ _ AddCommGrpCat.{u + 1}).obj ((spaceCohomology B S hS X i).obj F) :=
  cohomologyIsoOfAbelianSheafIso B S hS
    (sectionsTensorSheafUnitIso B S hS X (baseFunctionsToGlobalSections B S hS p) F) i

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- `H^i(X, ℱ ⊗_A A) ≅ H^i(X, ℱ)` is `A`-linear: multiplication by `a` on the factor `A` is
multiplication by `p^♯ a`. -/
theorem cohomologySectionsTensorUnitIso_hom_naturality (i : ℕ)
    (a : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ a)) ≫
        (cohomologySectionsTensorUnitIso B S hS p F i).hom =
      (cohomologySectionsTensorUnitIso B S hS p F i).hom ≫
        (forget₂ _ AddCommGrpCat.{u + 1}).map ((spaceCohomology B S hS X i).map
          (globalSmul _ (baseFunctionsToGlobalSections B S hS p a) F)) :=
  cohomologyIsoOfAbelianSheafIso_hom_naturality B S hS _ i _ _
    (sectionsTensorSheaf_map_toSpanSingleton_comp_unitIso_hom B S hS p F a)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] in
/-- Multiplication by `r` on `R ⊗_A M` is `μ_r ⊗ id`. -/
theorem smul_eq_map_baseChangeTensorModuleMul (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    {M : Type*} [AddCommGroup M] [Module Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) M] :
    letI := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
    ∀ z : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)] M,
      r • z = TensorProduct.map (baseChangeTensorModuleMul B S hS q r).hom LinearMap.id z := by
  let := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact (smul_zero r).trans (map_zero _).symm
  | add x y hx hy =>
    exact (smul_add r x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | tmul s x => exact TensorProduct.smul_tmul' r s x

/-- `H^i(X, ℱ ⊗_A A) ≅ H^i(X, ℱ)` as `A`-modules, `A` acting on the left through its action on
the factor `A` and on the right through `p^♯`. -/
def cohomologySectionsTensorUnitLinearEquiv (i : ℕ) :
    letI := Functor.unitObjModule.{u + 1, u}
      (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i)
    (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
      ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
      cohomologyRes (baseFunctionsToGlobalSections B S hS p) i F :=
  letI := Functor.unitObjModule.{u + 1, u}
    (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i)
  AddEquiv.toLinearEquiv (cohomologySectionsTensorUnitIso B S hS p F i).addCommGroupIsoToAddEquiv
    fun a x => by
      have h := ConcreteCategory.congr_hom
        (cohomologySectionsTensorUnitIso_hom_naturality B S hS p F i a) x
      simp only [ConcreteCategory.comp_apply] at h
      exact h.trans (spaceCohomology_map_globalSmul_apply B S hS i F _ _)

/-- The `R`-linear isomorphism `R ⊗_A H^i(X, ℱ ⊗_A A) ≅ H^i(X', ℱ')`: Lazard's comparison
`R ⊗_A H^i(X, ℱ ⊗_A A) ≅ H^i(X, ℱ ⊗_A R)` for the flat `A`-module `R`, followed by
`AlgebraicGeometry.Space.cohomologySectionsTensorBaseChangeIso`. -/
def cohomologySectionsTensorFlatBaseChangeEquiv [Flat ((BigFppfOver.toScheme B S hS).map q)]
    (hpc : IsQuasiCompact B S hS p.hom) (hps : IsQuasiSeparated B S hS p.hom)
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    letI := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
    letI := Functor.unitObjModule.{u + 1, u}
      (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i)
    Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
        (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i).obj
          (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)]
      cohomologyRes (baseFunctionsToGlobalSections B S hS (pullback.fst (schemeSpaceMap q) p)) i
        ((modulePullback B S hS (pullback.snd (schemeSpaceMap q) p)).obj F) :=
  letI := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
  letI := Functor.unitObjModule.{u + 1, u}
    (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i)
  haveI : Module.Flat Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (baseChangeTensorModule B S hS q) :=
    HasRingHomProperty.appTop @Flat ((BigFppfOver.toScheme B S hS).map q) inferInstance
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  have hqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS (isAlgebraicSpace_yoneda B S hS V)
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V inferInstance) hpc
  have hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X.2
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj V) hZ
        ⟨V, inferInstance, ⟨Functor.RepresentableBy.yoneda V⟩⟩) hps
  AddEquiv.toLinearEquiv
    ((AddEquiv.ofBijective _ (bijective_tensorUnitComparison_cohomologySectionsTensor B S hS X
      (baseFunctionsToGlobalSections B S hS p) hZ hqc hqs F i
      (baseChangeTensorModule B S hS q))).trans
      (cohomologySectionsTensorBaseChangeIso B S hS q p F hF i).addCommGroupIsoToAddEquiv)
    fun r z => by
      have h1 := smul_eq_map_baseChangeTensorModuleMul B S hS q r z
      have h2 := Functor.tensorUnitComparison_naturality.{u + 1, u}
        (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i)
        (fun a x => (Functor.unitObjModule_smul.{u + 1, u} _ a x).symm)
        (baseChangeTensorModuleMul B S hS q r) z
      have h3 := ConcreteCategory.congr_hom
        (cohomologySectionsTensorBaseChangeIso_hom_naturality B S hS q p F hF i r)
        (Functor.tensorUnitComparison.{u + 1, u} _
          (fun a x => (Functor.unitObjModule_smul.{u + 1, u} _ a x).symm) _ z)
      simp only [ConcreteCategory.comp_apply] at h3
      exact (congrArg (fun w => (cohomologySectionsTensorBaseChangeIso B S hS q p F hF i).hom
          (Functor.tensorUnitComparison.{u + 1, u} _
            (fun a x => (Functor.unitObjModule_smul.{u + 1, u} _ a x).symm) _ w)) h1).trans
        ((congrArg (cohomologySectionsTensorBaseChangeIso B S hS q p F hF i).hom h2).trans
          (h3.trans (spaceCohomology_map_globalSmul_apply B S hS i _ _ _)))

/-- Flat base change of cohomology over an affine base.

Let `q : W ⟶ V` be a flat morphism of affine schemes of the site, `A = Γ(V, 𝒪)` and
`R = Γ(W, 𝒪)`.  Let `p : X ⟶ V` be a quasi-compact and quasi-separated morphism of algebraic
spaces over `S`, `X' = W ×_V X` with projections `pr' : X' ⟶ W` and `pr : X' ⟶ X`, and `ℱ` a
quasi-coherent `𝒪_X`-module with pullback `ℱ' = pr^* ℱ`.  Then for every `i ≥ 0`

`R ⊗_A H^i(X, ℱ) ≅ H^i(X', ℱ')`

as `R`-modules, `A` acting on `H^i(X, ℱ)` through `p` and `R` acting on `H^i(X', ℱ')` through
`pr'`. -/
@[stacks 073K "part (2)"]
def cohomologyFlatBaseChangeEquiv [Flat ((BigFppfOver.toScheme B S hS).map q)]
    (hpc : IsQuasiCompact B S hS p.hom) (hps : IsQuasiSeparated B S hS p.hom)
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    letI := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
    Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) ⊗[Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
        cohomologyRes (baseFunctionsToGlobalSections B S hS p) i F
      ≃ₗ[Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)]
      cohomologyRes (baseFunctionsToGlobalSections B S hS (pullback.fst (schemeSpaceMap q) p)) i
        ((modulePullback B S hS (pullback.snd (schemeSpaceMap q) p)).obj F) :=
  letI := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
  letI := Functor.unitObjModule.{u + 1, u}
    (cohomologySectionsTensor B S hS X (baseFunctionsToGlobalSections B S hS p) F i)
  (LinearEquiv.baseChange Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) _ _
    (cohomologySectionsTensorUnitLinearEquiv B S hS p F i).symm).trans
    (cohomologySectionsTensorFlatBaseChangeEquiv B S hS q p F hpc hps hF i)

/-- The isomorphism `AlgebraicGeometry.Space.cohomologyFlatBaseChangeEquiv` sends `r ⊗ x` to `r`
times the image of `1 ⊗ x`. -/
theorem cohomologyFlatBaseChangeEquiv_tmul [Flat ((BigFppfOver.toScheme B S hS).map q)]
    (hpc : IsQuasiCompact B S hS p.hom) (hps : IsQuasiSeparated B S hS p.hom)
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) (r : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))
    (x : cohomologyRes (baseFunctionsToGlobalSections B S hS p) i F) :
    letI := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
    cohomologyFlatBaseChangeEquiv B S hS q p F hpc hps hF i (r ⊗ₜ x) =
      r • cohomologyFlatBaseChangeEquiv B S hS q p F hpc hps hF i (1 ⊗ₜ x) := by
  let := ((BigFppfOver.toScheme B S hS).map q).appTop.hom.toAlgebra
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end Affine

end AlgebraicGeometry.Space
