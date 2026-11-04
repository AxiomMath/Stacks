module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeAffine
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartConverse
public import StacksFrontier.RingTheory.Dualizing.RelativeAlgEquivTransport
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RingEquivIso

/-!
# Derived sections of a base change of affine schemes

Let `f : X ⟶ S` be flat and locally of finite presentation with `X`, `S`, `S'` affine, and let
`X'` be the base change along `g : S' ⟶ S`, with `g' : X' ⟶ X`. Write `A = Γ(X, ⊤)`,
`R = Γ(S, ⊤)` and `R' = Γ(S', ⊤)`. Then `Γ(X', ⊤) = A ⊗_R R'` (the global sections of a pullback of
affine schemes are the pushout of rings), and for `K` with quasi-coherent cohomology
`RΓ(X', L(g')^*K) = RΓ(X, K) ⊗ᴸ_A Γ(X', ⊤)` (Stacks 08DW). Consequently, if `RΓ(X, K)` is a
relative dualizing complex for `R → A`, then `RΓ(X', L(g')^*K)` is one for `R' → Γ(X', ⊤)` (Stacks
0E2F (2)), and `R ℰom(𝒪_{X'}, L pr₁^*L(g')^*K|_{W'}) ≅ 𝒪_{X'}[0]` on every diagonal open `W'` of
`f'`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.baseChangeSectionsAlgEquiv`: `A ⊗_R R' ≃ₐ[R'] Γ(X', ⊤)`.
* `AlgebraicGeometry.Scheme.Hom.isRelativeDualizingComplex_derivedSections_baseChange`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_diagonalExactSupport_baseChange_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace AlgebraicGeometry.Scheme.Hom

/-- The base change of a flat, locally of finite presentation morphism is again one. -/
private theorem flat_and_locallyOfFinitePresentation_of_isPullback {X S S' X' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'} (hpb : IsPullback g' f' f g) [Flat f]
    [LocallyOfFinitePresentation f] : Flat f' ∧ LocallyOfFinitePresentation f' :=
  ⟨MorphismProperty.of_isPullback (P := @Flat) hpb ‹_›,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb ‹_›⟩

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  (hpb : IsPullback g' f' f g) [IsAffine X] [IsAffine S] [IsAffine S']

include hpb in
/-- The base change `X'` of the affine scheme `X` along a morphism of affine schemes is affine. -/
theorem isAffine_of_isPullback : IsAffine X' := .of_isPullback hpb

include hpb in
/-- The pushout square of global sections, with the structure maps `f.appLE ⊤ ⊤`. -/
theorem isPushout_appLE_of_isPullback :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    IsPushout (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(S', ⊤))) g'.appTop f'.appTop := by
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  have := isAffine_of_isPullback hpb
  have h₁ : CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)) = f.appTop := appLE_top_top f le_top
  have h₂ : CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(S', ⊤)) = g.appTop := appLE_top_top g le_top
  rw [h₁, h₂]
  exact isPushout_appTop_of_isPullback hpb

include hpb in
/-- **`A ⊗_R R' ≅ Γ(X', ⊤)`** as rings: both are the pushout of `R ⟶ A` and `R ⟶ R'`. -/
def baseChangeSectionsIso :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    CommRingCat.of (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)) ≅ Γ(X', ⊤) :=
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  (CommRingCat.isPushout_tensorProduct Γ(S, ⊤) Γ(X, ⊤) Γ(S', ⊤)).isoPushout ≪≫
    (isPushout_appLE_of_isPullback hpb).isoPushout.symm

include hpb in
/-- `baseChangeSectionsIso` composed with `A ⟶ A ⊗_R R'` is `g'.appTop : A ⟶ Γ(X', ⊤)`. -/
theorem includeLeft_baseChangeSectionsIso :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)) ≫ (baseChangeSectionsIso hpb).hom =
      g'.appTop := by
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  simp only [baseChangeSectionsIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, (CommRingCat.isPushout_tensorProduct _ _ _).inl_isoPushout_hom,
    IsPushout.inl_isoPushout_inv]

include hpb in
/-- `baseChangeSectionsIso` composed with `R' ⟶ A ⊗_R R'` is `f'.appTop : R' ⟶ Γ(X', ⊤)`. -/
theorem includeRight_baseChangeSectionsIso :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    CommRingCat.ofHom (algebraMap Γ(S', ⊤) (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤))) ≫
        (baseChangeSectionsIso hpb).hom = f'.appTop := by
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  simp only [baseChangeSectionsIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, (CommRingCat.isPushout_tensorProduct _ _ _).inr_isoPushout_hom,
    IsPushout.inr_isoPushout_inv]

include hpb in
/-- `A ⊗_R R' ≃ₐ[R'] Γ(X', ⊤)`, with `Γ(X', ⊤)` an `R'`-algebra through `f'`. -/
def baseChangeSectionsAlgEquiv :
    letI := affineSectionsAlgebra f
    letI := affineSectionsAlgebra g
    letI := affineSectionsAlgebra f'
    (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)) ≃ₐ[Γ(S', ⊤)] Γ(X', ⊤) :=
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  let := affineSectionsAlgebra f'
  AlgEquiv.ofRingEquiv (f := (baseChangeSectionsIso hpb).commRingCatIsoToRingEquiv) fun r => by
    have h := congrArg (fun k => k.hom r) (includeRight_baseChangeSectionsIso hpb)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    change (baseChangeSectionsIso hpb).hom.hom (algebraMap Γ(S', ⊤) _ r) =
      (f'.appLE ⊤ ⊤ le_top).hom r
    rw [h, appLE_top_top f' le_top]

include hpb in
/-- **`RΓ(X', L(g')^*K) = RΓ(X, K) ⊗ᴸ_A Γ(X', ⊤)`** for `K` and `L(g')^*K` with quasi-coherent
cohomology (Stacks 06Z0 and 08DW). -/
theorem nonempty_derivedSections_baseChange_iso (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hK' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X'.Modules i).obj
      (DiagonalOpen.baseChangeComplex g' K)).IsQuasicoherent) :
    haveI := isAffine_of_isPullback hpb
    Nonempty ((derivedSectionsUnbounded X' ⊤).obj (DiagonalOpen.baseChangeComplex g' K) ≅
      (totalDerivedExtensionScalars.{u, u, u} g'.appTop.hom).functor.obj
        ((derivedSectionsUnbounded X ⊤).obj K)) := by
  have := isAffine_of_isPullback hpb
  obtain ⟨eK⟩ := nonempty_derivedPullback_isoSpec_inv_iso K hK
  obtain ⟨eK'⟩ := nonempty_derivedPullback_isoSpec_inv_iso _ hK'
  let c : (derivedPullback X'.isoSpec.inv.toLRSHom.toShHom).obj
      (DiagonalOpen.baseChangeComplex g' K) ≅
      (tilde.functor Γ(X', ⊤)).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} g'.appTop.hom).functor.obj
          ((derivedSectionsUnbounded X ⊤).obj K)) :=
    Scheme.derivedPullbackCompObj X'.isoSpec.inv g' K ≪≫
      Scheme.derivedPullbackCongrObj (Scheme.isoSpec_inv_naturality g').symm K ≪≫
      (Scheme.derivedPullbackCompObj (Spec.map g'.appTop) X.isoSpec.inv K).symm ≪≫
      (derivedPullback (Spec.map g'.appTop).toLRSHom.toShHom).mapIso eK ≪≫
      (StandardModel.affinePullbackComparison Γ(X, ⊤) Γ(X', ⊤) g'.appTop).app
        ((derivedSectionsUnbounded X ⊤).obj K)
  exact ⟨(StandardModel.mapDerivedCategoryFullyFaithful Γ(X', ⊤)).preimageIso (eK'.symm ≪≫ c)⟩

include hpb in
/-- **Stacks 0E2F (2) read on `Γ(X', ⊤)`.** If `K_A` is a relative dualizing complex for
`Γ(S, ⊤) → Γ(X, ⊤)`, then `K_A ⊗ᴸ_A Γ(X', ⊤)` is one for `Γ(S', ⊤) → Γ(X', ⊤)`. -/
theorem isRelativeDualizingComplex_baseChange_sections [Flat f] [LocallyOfFinitePresentation f]
    (KA : DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
    (hKA : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
        moduleFlat_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      letI : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
        algebraFinitePresentation_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      Dualizing.IsRelativeDualizingComplex Γ(S, ⊤) Γ(X, ⊤) KA) :
    haveI := isAffine_of_isPullback hpb
    haveI : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb (inferInstance : Flat f)
    haveI : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback
      (P := @LocallyOfFinitePresentation) hpb (inferInstance : LocallyOfFinitePresentation f)
    letI : Algebra Γ(S', ⊤) Γ(X', ⊤) := (f'.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module.Flat Γ(S', ⊤) Γ(X', ⊤) :=
      moduleFlat_appLE f' (isAffineOpen_top S') (isAffineOpen_top X') le_top rfl
    letI : Algebra.FinitePresentation Γ(S', ⊤) Γ(X', ⊤) :=
      algebraFinitePresentation_appLE f' (isAffineOpen_top S') (isAffineOpen_top X') le_top rfl
    Dualizing.IsRelativeDualizingComplex Γ(S', ⊤) Γ(X', ⊤)
      ((totalDerivedExtensionScalars.{u, u, u} g'.appTop.hom).functor.obj KA) := by
  have := isAffine_of_isPullback hpb
  obtain ⟨_, _⟩ := flat_and_locallyOfFinitePresentation_of_isPullback hpb
  let := affineSectionsAlgebra f
  let := affineSectionsAlgebra g
  let := affineSectionsAlgebra f'
  let : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
    moduleFlat_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
  let : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
    algebraFinitePresentation_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
  let : Module.Flat Γ(S', ⊤) Γ(X', ⊤) :=
    moduleFlat_appLE f' (isAffineOpen_top S') (isAffineOpen_top X') le_top rfl
  let : Algebra.FinitePresentation Γ(S', ⊤) Γ(X', ⊤) :=
    algebraFinitePresentation_appLE f' (isAffineOpen_top S') (isAffineOpen_top X') le_top rfl
  let : Module.Flat Γ(S', ⊤) (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)) :=
    Dualizing.flat_baseChange Γ(S, ⊤) Γ(X, ⊤) Γ(S', ⊤)
  let : Algebra.FinitePresentation Γ(S', ⊤) (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤)) :=
    Algebra.FinitePresentation.equiv (Dualizing.baseChangeComm Γ(S, ⊤) Γ(X, ⊤) Γ(S', ⊤))
  let e := baseChangeSectionsAlgEquiv hpb
  have h₂ := Dualizing.RelativeExistence.isRelativeDualizingComplex_of_algEquiv e _
    (hKA.baseChange Γ(S', ⊤))
  let eC := e.symm.toRingEquiv
  let incl : Γ(X, ⊤) →+* Γ(X, ⊤) ⊗[Γ(S, ⊤)] Γ(S', ⊤) := Algebra.TensorProduct.includeLeftRingHom
  let Df := totalDerivedExtensionScalars.{u, u, u} incl
  let f'' := eC.symm.toRingHom.comp (incl.comp (RingEquiv.refl Γ(X, ⊤)).toRingHom)
  let Dg := totalDerivedExtensionScalars.{u, u, u} f''
  have e₁ := @StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRight _ _ _ _ _ _ eC
    incl Df.functor Df.comparison Df.isLeftDerived Dg.functor Dg.comparison Dg.isLeftDerived
  have hf'' : f'' = g'.appTop.hom := by
    ext a
    exact congrArg (fun k => k.hom a) (includeLeft_baseChangeSectionsIso hpb)
  have e₂ : (totalDerivedExtensionScalars.{u, u, u} g'.appTop.hom).functor.obj KA ≅
      Dg.functor.obj KA :=
    eqToIso (congrArg (fun φ => (totalDerivedExtensionScalars.{u, u, u} φ).functor.obj KA)
      hf''.symm)
  exact Dualizing.isRelativeDualizingComplex_of_iso _ _ h₂ ((e₂ ≪≫ e₁.app KA).symm)

include hpb in
/-- **`R ℰom(𝒪_{X'}, L pr₁^*L(g')^*K|_{W'}) ≅ 𝒪_{X'}[0]`** on every diagonal open `W'` of `f'`,
when `RΓ(X, K)` is a relative dualizing complex for `Γ(S, ⊤) → Γ(X, ⊤)`. -/
theorem DiagonalOpen.nonempty_diagonalExactSupport_baseChange_iso [Flat f]
    [LocallyOfFinitePresentation f] (D' : DiagonalOpen f') (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hK' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X'.Modules i).obj
      (DiagonalOpen.baseChangeComplex g' K)).IsQuasicoherent)
    (hKA : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
        moduleFlat_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      letI : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
        algebraFinitePresentation_appLE f (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      Dualizing.IsRelativeDualizingComplex Γ(S, ⊤) Γ(X, ⊤) ((derivedSectionsUnbounded X ⊤).obj K)) :
    Nonempty (D'.diagonalExactSupport (DiagonalOpen.baseChangeComplex g' K) ≅
      structureSingle X') := by
  have := isAffine_of_isPullback hpb
  obtain ⟨_, _⟩ := flat_and_locallyOfFinitePresentation_of_isPullback hpb
  obtain ⟨eΓ⟩ := nonempty_derivedSections_baseChange_iso hpb K hK hK'
  have hR := isRelativeDualizingComplex_baseChange_sections hpb _ hKA
  let : Algebra Γ(S', ⊤) Γ(X', ⊤) := (f'.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Module.Flat Γ(S', ⊤) Γ(X', ⊤) :=
    moduleFlat_appLE f' (isAffineOpen_top S') (isAffineOpen_top X') le_top rfl
  let : Algebra.FinitePresentation Γ(S', ⊤) Γ(X', ⊤) :=
    algebraFinitePresentation_appLE f' (isAffineOpen_top S') (isAffineOpen_top X') le_top rfl
  have hR' := Dualizing.isRelativeDualizingComplex_of_iso _ _ hR eΓ.symm
  exact D'.nonempty_diagonalExactSupport_iso_of_top (isAffineOpen_top X') (isAffineOpen_top S')
    le_top rfl _ hK' hR'

end AlgebraicGeometry.Scheme.Hom

end
