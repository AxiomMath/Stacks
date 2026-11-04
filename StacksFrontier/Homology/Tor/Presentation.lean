module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TotallySplit
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Tor via finite free presentations

For a finite free presentation `0 → K → Aᵗ → M → 0` of an `A`-module `M`, this file identifies
`Tor₁(M, -)` with the kernel of `K ⊗ - → Aᵗ ⊗ -`, naturally in the second variable, shows that
free modules are Tor-acyclic in positive degrees, and constructs the dimension-shifting
isomorphisms `Tor_{q+2}(M, N) ≅ Tor_{q+1}(K, N)` together with their naturality.
-/

open CategoryTheory

variable {A : Type*} [CommRing A]

open CategoryTheory.Limits in
/-- The natural transformation `K ⊗ - ⟶ Aᵗ ⊗ -` induced (via `tensoringLeft`) by the
inclusion `ι : K ↪ Aᵗ` of the kernel `K = LinearMap.ker φ` of a finite free
presentation `φ : Aᵗ ↠ M`. Its categorical kernel (a functor `ModuleCat A ⥤ ModuleCat A`)
is the explicit model of `Tor₁(M, -)`. -/
noncomputable def torBaseNT {t : ℕ} (M : ModuleCat A) (φ : (Fin t → A) →ₗ[A] M) :
    (MonoidalCategory.tensoringLeft (ModuleCat A)).obj (ModuleCat.of A (LinearMap.ker φ)) ⟶
    (MonoidalCategory.tensoringLeft (ModuleCat A)).obj (ModuleCat.of A (Fin t → A)) :=
  (MonoidalCategory.tensoringLeft (ModuleCat A)).map
    (ModuleCat.ofHom (LinearMap.ker φ).subtype)

/-- The short exact sequence `0 → K → Aᵗ → M → 0` (with `K = ker φ`, `Aᵗ = Fin t → A`,
`φ : Aᵗ ↠ M`) packaged as a `ShortComplex (ModuleCat A)`. -/
noncomputable def torBaseSES {t : ℕ} (M : ModuleCat A) (φ : (Fin t → A) →ₗ[A] M) :
    ShortComplex (ModuleCat A) where
  X₁ := ModuleCat.of A (LinearMap.ker φ)
  X₂ := ModuleCat.of A (Fin t → A)
  X₃ := M
  f := ModuleCat.ofHom (LinearMap.ker φ).subtype
  g := ModuleCat.ofHom φ
  zero := by
    ext x
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    exact x.property

/-- With `φ` surjective and `K = ker φ`, the sequence `0 → K → Aᵗ → M → 0` is short exact in
`ModuleCat A`. -/
theorem torBaseSES_shortExact {t : ℕ} (M : ModuleCat A) (φ : (Fin t → A) →ₗ[A] M)
    (hφ : Function.Surjective φ) : (torBaseSES M φ).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    exact Subtype.coe_injective
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    exact hφ

/-- An additive functor preserving homology sends `ExactAt` to `ExactAt`. -/
theorem exactAt_mapHomologicalComplex {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] {ι : Type*} (c : ComplexShape ι) (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] (K : HomologicalComplex C c) (i : ι) (h : K.ExactAt i) :
    ((F.mapHomologicalComplex c).obj K).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff]
  rw [HomologicalComplex.exactAt_iff] at h
  have : ((F.mapHomologicalComplex c).obj K).sc i = (K.sc i).map F := rfl
  rw [this]
  exact h.map F

/-- `X ⊗ -` preserves finite colimits, since `tensorLeft X` is a left adjoint. -/
private theorem preservesFiniteColimits_tensorLeft (X : ModuleCat A) :
    Limits.PreservesFiniteColimits (MonoidalCategory.tensorLeft X) := by
  have : Limits.PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  exact Limits.PreservesColimitsOfSize.preservesFiniteColimits _

open CategoryTheory.Limits in
/-- **A flat module is Tor-acyclic in every positive degree.** If `X` is a flat `A`-module, then
`Tor_{p+1}(X, N) = 0` for every `N`; in particular this applies to `Aᵗ = Fin t → A`, which is
free hence flat. -/
@[sga "1 IV 4.3" "(iii) ⇒ (iv)"]
theorem isZero_Tor_succ_of_flat (X : ModuleCat A) [Module.Flat A X] (N : ModuleCat A) (p : ℕ) :
    IsZero (((Tor (ModuleCat A) (p + 1)).obj X).obj N) := by
  have P : ProjectiveResolution N := (HasProjectiveResolution.out (Z := N)).some
  set FT := (MonoidalCategory.tensoringLeft (ModuleCat A)).obj X with hFT
  have iAdd : FT.Additive := by rw [hFT]; infer_instance
  have hFC : Limits.PreservesFiniteColimits FT := preservesFiniteColimits_tensorLeft X
  have hFL : Limits.PreservesFiniteLimits FT := by rw [hFT]; infer_instance
  have iPH : FT.PreservesHomology := Functor.preservesHomologyOfExact FT
  have hexact : ((FT.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).ExactAt (p + 1) :=
    exactAt_mapHomologicalComplex _ FT P.complex (p + 1) (P.complex_exactAt_succ p)
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hexact
  have hz : IsZero ((HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ)
          (p + 1)).obj ((FT.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)) := hexact
  exact IsZero.of_iso hz (P.isoLeftDerivedObj FT (p + 1))

open CategoryTheory.Limits in
/-- A flat module is `Tor₁`-acyclic: the degree-one case of `isZero_Tor_succ_of_flat`. -/
theorem isZero_Tor_one_of_flat (X : ModuleCat A) [Module.Flat A X] (N : ModuleCat A) :
    IsZero (((Tor (ModuleCat A) 1).obj X).obj N) :=
  isZero_Tor_succ_of_flat X N 0

open CategoryTheory.Limits in
/-- The categorical kernel of `torBaseNT` evaluates pointwise:
`(kernel (torBaseNT M φ)).obj N ≅ kernel ((torBaseNT M φ).app N)`, since kernels in the functor
category `ModuleCat A ⥤ ModuleCat A` are computed objectwise. -/
noncomputable def torKerPointwise (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M)
    (N : ModuleCat A) :
    (kernel (torBaseNT M φ)).obj N ≅ kernel ((torBaseNT M φ).app N) :=
  PreservesKernel.iso ((evaluation (ModuleCat A) (ModuleCat A)).obj N) (torBaseNT M φ)

/-- Functor-variable naturality of `Functor.fromLeftDerivedZero`: the natural
transformation `F.leftDerived 0 ⟶ F` is compatible with a natural transformation
`α : F ⟶ G` of additive functors. -/
theorem fromLeftDerivedZero_natural {C D : Type*} [Category C] [Abelian C]
    [HasProjectiveResolutions C] [Category D] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (X : C) :
    (NatTrans.leftDerived α 0).app X ≫ G.fromLeftDerivedZero.app X
      = F.fromLeftDerivedZero.app X ≫ α.app X := by
  have P : ProjectiveResolution X := (HasProjectiveResolution.out (Z := X)).some
  rw [ProjectiveResolution.leftDerived_app_eq α P 0,
      ProjectiveResolution.fromLeftDerivedZero_eq P G,
      ProjectiveResolution.fromLeftDerivedZero_eq P F]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [Iso.cancel_iso_hom_left]
  set β := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex with hβ
  have hnat : (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) 0).map β
        ≫ (ChainComplex.isoHomologyι₀
            ((G.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).hom
      = (ChainComplex.isoHomologyι₀
            ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).hom
        ≫ HomologicalComplex.opcyclesMap β 0 :=
    HomologicalComplex.homologyι_naturality β 0
  rw [reassoc_of% hnat, Iso.cancel_iso_hom_left]
  rw [← cancel_epi
        (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).pOpcycles 0)]
  rw [ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
  rw [HomologicalComplex.p_opcyclesMap_assoc]
  rw [ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero']
  have hbf : β.f 0 = α.app (P.complex.X 0) := by rw [hβ]; rfl
  rw [hbf]
  exact (α.naturality (P.π.f 0)).symm

open CategoryTheory.Limits in
/-- The degreewise tensor of the presentation SES with a projective resolution `P` of `N`,
as a short complex of chain complexes. Each entry is `(F.mapHomologicalComplex _).obj P.complex`
for the three tensoring functors `F` attached to `torBaseSES`. -/
noncomputable def torOneCxSES (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M)
    {N : ModuleCat A} (P : ProjectiveResolution N) :
    ShortComplex (HomologicalComplex (ModuleCat A) (ComplexShape.down ℕ)) :=
  -- The three projected tensoring functors carry `PreservesZeroMorphisms`, but on their
  -- UNREDUCED projection form `inferInstance` selects the poisoned (`sorryAx`-backed) global
  -- instance. We redirect to the clean instance on the reduced `tensoringLeft.obj _` form
  -- via `inferInstanceAs` (a `Prop`-class, so the data/type are unchanged).
  haveI iz1 : (((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat
      A))).X₁).PreservesZeroMorphisms :=
    inferInstanceAs (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
      (ModuleCat.of A (LinearMap.ker φ))).PreservesZeroMorphisms)
  haveI iz2 : (((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat
      A))).X₂).PreservesZeroMorphisms :=
    inferInstanceAs (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
      (ModuleCat.of A (Fin t → A))).PreservesZeroMorphisms)
  haveI iz3 : (((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat
      A))).X₃).PreservesZeroMorphisms :=
    inferInstanceAs (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj M).PreservesZeroMorphisms)
  { X₁ := ((((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat
      A))).X₁).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex
    X₂ := ((((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat
        A))).X₂).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex
    X₃ := ((((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat
        A))).X₃).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj P.complex
    f := (NatTrans.mapHomologicalComplex
            ((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat A))).f
            (ComplexShape.down ℕ)).app P.complex
    g := (NatTrans.mapHomologicalComplex
            ((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat A))).g
            (ComplexShape.down ℕ)).app P.complex
    zero := by
      rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp]
      have h0 : ((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat A))).f
            ≫ ((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat A))).g = 0 :=
        ((torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat A))).zero
      rw [h0]; ext i; simp [NatTrans.mapHomologicalComplex] }

open CategoryTheory.Limits in
/-- For a surjection `φ : Aᵗ → M` and a projective resolution `P` of `N`, the degreewise
tensor product of `0 → ker φ → Aᵗ → M → 0` with `P` is a short exact sequence of chain
complexes. -/
theorem torOneCxSES_shortExact (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M)
    (hφ : Function.Surjective φ) {N : ModuleCat A} (P : ProjectiveResolution N) :
    (torOneCxSES M φ P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  -- `map_of_exact` needs `PreservesFiniteLimits` + `PreservesFiniteColimits` for
  -- `tensorRight (P.complex.X i) = - ⊗ Pᵢ`. The ambient global instances for these are
  -- backed by `sorryAx` in this environment, so we build them cleanly:
  -- limits from flatness of the projective term `Pᵢ`, colimits via the braiding from the
  -- (left-adjoint) `tensorLeft Pᵢ`.
  set X := P.complex.X i with hX
  have hProj : CategoryTheory.Projective X := P.projective i
  have : Small.{_, _} A := small_self A
  have hMP : Module.Projective A X := ModuleCat.projective_of_module_projective X
  have hflat : Module.Flat A X := Module.Flat.of_projective
  have hFL : Limits.PreservesFiniteLimits (MonoidalCategory.tensorRight X) :=
    Module.Flat.instPreservesFiniteLimitsModuleCatTensorRightOfCarrier X
  have hFCL := preservesFiniteColimits_tensorLeft X
  have hFC : Limits.PreservesFiniteColimits (MonoidalCategory.tensorRight X) :=
    Limits.preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  exact (torBaseSES_shortExact M φ hφ).map_of_exact (MonoidalCategory.tensorRight X)

-- Works around the stricter isDefEq-transparency change: the `tensoringLeft`
-- object types in the left-derived / homology identifications are only defeq,
-- not syntactically equal.
set_option backward.isDefEq.respectTransparency.types false in
open CategoryTheory.Limits in
/-- **`Tor₁(M, N) ≅ kernel ((torBaseNT M φ).app N)`.** For a surjection `φ : Aᵗ → M` with kernel
`K`, the connecting map of the homology sequence of the degreewise tensor product of
`0 → K → Aᵗ → M → 0` with a projective resolution of `N` identifies `Tor₁(M, N)` with the kernel
of `K ⊗ N → Aᵗ ⊗ N`, since `Tor₁(Aᵗ, N) = 0`. -/
@[ega "IV 11.2.3" "Tor₁(M, special case"]
noncomputable def torOneIsoKerApp (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M)
    (hφ : Function.Surjective φ) (N : ModuleCat A) :
    ((Tor (ModuleCat A) 1).obj M).obj N ≅ kernel ((torBaseNT M φ).app N) := by
  have P : ProjectiveResolution N := (HasProjectiveResolution.out (Z := N)).some
  set FK := (MonoidalCategory.tensoringLeft (ModuleCat A)).obj (ModuleCat.of A (LinearMap.ker φ))
    with hFK
  set FT := (MonoidalCategory.tensoringLeft (ModuleCat A)).obj (ModuleCat.of A (Fin t → A))
    with hFT
  set FM := (MonoidalCategory.tensoringLeft (ModuleCat A)).obj M with hFM
  haveI iFKa : FK.Additive := by rw [hFK]; infer_instance
  haveI iFTa : FT.Additive := by rw [hFT]; infer_instance
  haveI iFMa : FM.Additive := by rw [hFM]; infer_instance
  -- Build the `PreservesFiniteColimits` instances directly from the tensor–hom adjunction
  -- (`tensorLeft X` is a left adjoint, hence preserves colimits), rather than through the
  -- ambient `infer_instance` for `PreservesFiniteColimits (tensoringLeft.obj _)`.
  haveI iFKc : Limits.PreservesFiniteColimits FK := by
    rw [hFK]
    have : Limits.PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorLeft (ModuleCat.of A (LinearMap.ker φ))) :=
      (ihom.adjunction (ModuleCat.of A (LinearMap.ker φ))).leftAdjoint_preservesColimits
    exact Limits.PreservesColimitsOfSize.preservesFiniteColimits _
  haveI iFTc : Limits.PreservesFiniteColimits FT := by
    rw [hFT]
    have : Limits.PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorLeft (ModuleCat.of A (Fin t → A))) :=
      (ihom.adjunction (ModuleCat.of A (Fin t → A))).leftAdjoint_preservesColimits
    exact Limits.PreservesColimitsOfSize.preservesFiniteColimits _
  set S := torOneCxSES M φ P with hS
  have hSE : S.ShortExact := torOneCxSES_shortExact M φ hφ P
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down]
  have hz : IsZero (S.X₂.homology 1) :=
    IsZero.of_iso (isZero_Tor_one_of_flat (ModuleCat.of A (Fin t → A)) N)
      (P.isoLeftDerivedObj FT 1).symm
  have hmono : Mono (hSE.δ 1 0 hrel) := hSE.mono_δ 1 0 hrel hz
  have hex := hSE.homology_exact₁ 1 0 hrel
  have hker : S.X₃.homology 1 ≅ kernel (HomologicalComplex.homologyMap S.f 0) :=
    hex.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  set uK : S.X₁.homology 0 ≅ FK.obj N :=
    (P.isoLeftDerivedObj FK 0).symm ≪≫ (FK.leftDerivedZeroIsoSelf).app N with huK
  set uT : S.X₂.homology 0 ≅ FT.obj N :=
    (P.isoLeftDerivedObj FT 0).symm ≪≫ (FT.leftDerivedZeroIsoSelf).app N with huT
  have hsq : HomologicalComplex.homologyMap S.f 0 ≫ uT.hom = uK.hom ≫ (torBaseNT M φ).app N := by
    rw [huK, huT]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.leftDerivedZeroIsoSelf_hom, Iso.app_hom]
    rw [show HomologicalComplex.homologyMap S.f 0
          = (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 0).map
              ((NatTrans.mapHomologicalComplex (torBaseNT M φ)
                  (ComplexShape.down ℕ)).app P.complex) from rfl]
    have hle := ProjectiveResolution.leftDerived_app_eq (torBaseNT M φ) P 0
    have hm : (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) 0).map
              ((NatTrans.mapHomologicalComplex (torBaseNT M φ) (ComplexShape.down ℕ)).app P.complex)
          = (P.isoLeftDerivedObj FK 0).inv
              ≫ (NatTrans.leftDerived (torBaseNT M φ) 0).app N
              ≫ (P.isoLeftDerivedObj FT 0).hom := by
      rw [hle]
      simp only [Category.assoc]
      rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hm]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [fromLeftDerivedZero_natural (torBaseNT M φ) N]
  exact (P.isoLeftDerivedObj FM 1) ≪≫ hker
    ≪≫ kernel.mapIso (HomologicalComplex.homologyMap S.f 0) ((torBaseNT M φ).app N) uK uT hsq

open CategoryTheory.Limits in
/-- For each `N`, the isomorphism `Tor₁(M, N) ≅ (kernel (torBaseNT M φ)).obj N`, obtained from
`torOneIsoKerApp` and the pointwise computation `torKerPointwise` of the kernel. -/
@[ega "IV 11.2.3" "Tor₁(M, special case"]
noncomputable def torOneTensorKernelIsoApp
    (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M) (hφ : Function.Surjective φ)
    (N : ModuleCat A) :
    ((Tor (ModuleCat A) 1).obj M).obj N ≅ (kernel (torBaseNT M φ)).obj N :=
  torOneIsoKerApp M φ hφ N ≪≫ (torKerPointwise M φ N).symm

/-- The tensoring functor `(tensoringLeft (ModuleCat A)).obj X = X ⊗ -` preserves finite
colimits, since `tensorLeft X` is a left adjoint. -/
@[ega "0 4.1.5" "special case", sga "4 IV 12.9" "special case", sga "5 V 1.2.1" "Module case"]
instance (priority := 10000) tensoringLeftPreservesFiniteColimits (X : ModuleCat A) :
    Limits.PreservesFiniteColimits ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj X) := by
  have : Limits.PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft X) :=
    (ihom.adjunction X).leftAdjoint_preservesColimits
  exact Limits.PreservesColimitsOfSize.preservesFiniteColimits _

/-- The tensoring functor `(tensoringLeft (ModuleCat A)).obj X` preserves zero morphisms. -/
instance (priority := 10000) tensoringLeftPreservesZeroMorphisms (X : ModuleCat A) :
    ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj X).PreservesZeroMorphisms :=
  inferInstanceAs ((MonoidalCategory.tensorLeft X).PreservesZeroMorphisms)

open CategoryTheory.Limits in
/-- Characterization of `torOneIsoKerApp` composed with the kernel inclusion: it is the
connecting map `δ` of the tensored SES (post-composed with the `H₀ = FK` identification),
pre-composed with the `Tor₁ = H₁` identification. -/
@[ega "IV 11.2.3" "partial"]
theorem torOneIsoKerApp_hom_ι (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M)
    (hφ : Function.Surjective φ) (N : ModuleCat A)
    (hrel : (ComplexShape.down ℕ).Rel 1 0) :
    (torOneIsoKerApp M φ hφ N).hom ≫ kernel.ι ((torBaseNT M φ).app N)
      = (((HasProjectiveResolution.out (Z := N)).some).isoLeftDerivedObj
            ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj M) 1).hom
          ≫ (torOneCxSES_shortExact M φ hφ (HasProjectiveResolution.out (Z := N)).some).δ 1 0 hrel
          ≫ ((((HasProjectiveResolution.out (Z := N)).some).isoLeftDerivedObj
                ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
                  (ModuleCat.of A (LinearMap.ker φ))) 0).symm
              ≪≫ (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
                  (ModuleCat.of A (LinearMap.ker φ))).leftDerivedZeroIsoSelf).app N).hom := by
  unfold torOneIsoKerApp
  simp only [Iso.trans_hom, Category.assoc, kernel.mapIso_hom, kernel.lift_ι]
  have hmono : Mono ((torOneCxSES_shortExact M φ hφ (HasProjectiveResolution.out (Z := N)).some).δ
      1 0 hrel) :=
    (torOneCxSES_shortExact M φ hφ (HasProjectiveResolution.out (Z := N)).some).mono_δ 1 0 hrel
      (IsZero.of_iso (isZero_Tor_one_of_flat (ModuleCat.of A (Fin t → A)) N)
        (((HasProjectiveResolution.out (Z := N)).some).isoLeftDerivedObj
          ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj (ModuleCat.of A (Fin t → A))) 1).symm)
  have hδ : (((torOneCxSES_shortExact M φ hφ (HasProjectiveResolution.out (Z :=
      N)).some).homology_exact₁
      1 0 hrel).fIsKernel.conePointUniqueUpToIso
      (limit.isLimit (parallelPair
        (HomologicalComplex.homologyMap (torOneCxSES M φ (HasProjectiveResolution.out (Z :=
            N)).some).f 0) 0))).hom
      ≫ kernel.ι (HomologicalComplex.homologyMap
          (torOneCxSES M φ (HasProjectiveResolution.out (Z := N)).some).f 0)
      = (torOneCxSES_shortExact M φ hφ (HasProjectiveResolution.out (Z := N)).some).δ 1 0 hrel := by
    have := ((torOneCxSES_shortExact M φ hφ (HasProjectiveResolution.out (Z :=
        N)).some).homology_exact₁
      1 0 hrel).fIsKernel.conePointUniqueUpToIso_hom_comp
      (limit.isLimit (parallelPair
        (HomologicalComplex.homologyMap (torOneCxSES M φ (HasProjectiveResolution.out (Z :=
            N)).some).f 0) 0))
      WalkingParallelPair.zero
    simp
  rw [reassoc_of% hδ]

/-- The connecting maps of the tensored presentation, conjugated by the `Tor = H` identifications,
commute with the maps induced by `f : N ⟶ N'` (for resolutions `P`, `Q` of `N`, `N'`). -/
private theorem leftDerived_map_comp_torOneCxSES_δ (M : ModuleCat A) {t : ℕ}
    (φ : (Fin t → A) →ₗ[A] M) (hφ : Function.Surjective φ) {N N' : ModuleCat A} (f : N ⟶ N')
    (P : ProjectiveResolution N) (Q : ProjectiveResolution N') (i j : ℕ)
    (hrel : (ComplexShape.down ℕ).Rel i j) :
    (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj M).leftDerived i).map f
        ≫ (Q.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj M) i).hom
        ≫ (torOneCxSES_shortExact M φ hφ Q).δ i j hrel
        ≫ (Q.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
            (ModuleCat.of A (LinearMap.ker φ))) j).inv
      = (P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj M) i).hom
        ≫ (torOneCxSES_shortExact M φ hφ P).δ i j hrel
        ≫ (P.isoLeftDerivedObj ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
            (ModuleCat.of A (LinearMap.ker φ))) j).inv
        ≫ (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
            (ModuleCat.of A (LinearMap.ker φ))).leftDerived j).map f := by
  set FK := (MonoidalCategory.tensoringLeft (ModuleCat A)).obj (ModuleCat.of A (LinearMap.ker φ))
    with hFK
  set FM := (MonoidalCategory.tensoringLeft (ModuleCat A)).obj M with hFM
  have iFKa : FK.Additive := by rw [hFK]; infer_instance
  have iFMa : FM.Additive := by rw [hFM]; infer_instance
  set g : P.complex ⟶ Q.complex := ProjectiveResolution.lift f P Q with hg
  have hgπ : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ (ModuleCat A)).map f :=
    ProjectiveResolution.lift_commutes f P Q
  set SES := (torBaseSES M φ).map (MonoidalCategory.tensoringLeft (ModuleCat A)) with hSES
  have iz1 : (SES.X₁).PreservesZeroMorphisms :=
    inferInstanceAs (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
      (ModuleCat.of A (LinearMap.ker φ))).PreservesZeroMorphisms)
  have iz2 : (SES.X₂).PreservesZeroMorphisms :=
    inferInstanceAs (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
      (ModuleCat.of A (Fin t → A))).PreservesZeroMorphisms)
  have iz3 : (SES.X₃).PreservesZeroMorphisms :=
    inferInstanceAs (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj M).PreservesZeroMorphisms)
  set φm : torOneCxSES M φ P ⟶ torOneCxSES M φ Q :=
    { τ₁ := (SES.X₁.mapHomologicalComplex (ComplexShape.down ℕ)).map g
      τ₂ := (SES.X₂.mapHomologicalComplex (ComplexShape.down ℕ)).map g
      τ₃ := (SES.X₃.mapHomologicalComplex (ComplexShape.down ℕ)).map g
      comm₁₂ :=
        (NatTrans.mapHomologicalComplex SES.f (ComplexShape.down ℕ)).naturality g
      comm₂₃ :=
        (NatTrans.mapHomologicalComplex SES.g (ComplexShape.down ℕ)).naturality g }
    with hφm
  have hδnat := HomologicalComplex.HomologySequence.δ_naturality φm
    (torOneCxSES_shortExact M φ hφ P) (torOneCxSES_shortExact M φ hφ Q) i j hrel
  change (FM.leftDerived i).map f ≫ (Q.isoLeftDerivedObj FM i).hom
        ≫ (torOneCxSES_shortExact M φ hφ Q).δ i j hrel ≫ (Q.isoLeftDerivedObj FK j).inv
      = (P.isoLeftDerivedObj FM i).hom ≫ (torOneCxSES_shortExact M φ hφ P).δ i j hrel
        ≫ (P.isoLeftDerivedObj FK j).inv ≫ (FK.leftDerived j).map f
  have hFMmap : (FM.leftDerived i).map f
      = (P.isoLeftDerivedObj FM i).hom
          ≫ HomologicalComplex.homologyMap φm.τ₃ i ≫ (Q.isoLeftDerivedObj FM i).inv :=
    Functor.leftDerived_map_eq FM i f g hgπ
  have hFKmap : (FK.leftDerived j).map f
      = (P.isoLeftDerivedObj FK j).hom
          ≫ HomologicalComplex.homologyMap φm.τ₁ j ≫ (Q.isoLeftDerivedObj FK j).inv :=
    Functor.leftDerived_map_eq FK j f g hgπ
  rw [hFMmap, hFKmap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% hδnat]

open CategoryTheory.Limits in
/-- **Naturality of `torOneIsoKerApp` followed by `kernel.ι`.** For `f : N ⟶ N'`, the
composite `(torOneIsoKerApp M φ hφ -).hom ≫ kernel.ι ((torBaseNT M φ).app -)` commutes with
`Tor₁(M, f)` and with `FK.map f`, where
`FK = (tensoringLeft (ModuleCat A)).obj (ModuleCat.of A (LinearMap.ker φ))`. -/
theorem torOneIsoKerApp_hom_ι_naturality
    (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M) (hφ : Function.Surjective φ)
    {N N' : ModuleCat A} (f : N ⟶ N') :
    ((Tor (ModuleCat A) 1).obj M).map f
        ≫ (torOneIsoKerApp M φ hφ N').hom ≫ kernel.ι ((torBaseNT M φ).app N')
      = ((torOneIsoKerApp M φ hφ N).hom ≫ kernel.ι ((torBaseNT M φ).app N))
          ≫ ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
              (ModuleCat.of A (LinearMap.ker φ))).map f := by
  have hrel : (ComplexShape.down ℕ).Rel 1 0 := by simp [ComplexShape.down]
  rw [torOneIsoKerApp_hom_ι M φ hφ N hrel, torOneIsoKerApp_hom_ι M φ hφ N' hrel]
  have key := congrArg
    (· ≫ (((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
      (ModuleCat.of A (LinearMap.ker φ))).leftDerivedZeroIsoSelf).hom.app N')
    (leftDerived_map_comp_torOneCxSES_δ M φ hφ f (HasProjectiveResolution.out (Z := N)).some
      (HasProjectiveResolution.out (Z := N')).some 1 0 hrel)
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc] at key ⊢
  refine key.trans ?_
  rw [((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
    (ModuleCat.of A (LinearMap.ker φ))).leftDerivedZeroIsoSelf.hom.naturality f]


open CategoryTheory.Limits in
/-- The isomorphisms `torOneTensorKernelIsoApp` are natural in `N`. -/
theorem torOneTensorKernelIsoApp_naturality
    (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M) (hφ : Function.Surjective φ)
    {N N' : ModuleCat A} (f : N ⟶ N') :
    ((Tor (ModuleCat A) 1).obj M).map f ≫ (torOneTensorKernelIsoApp M φ hφ N').hom
      = (torOneTensorKernelIsoApp M φ hφ N).hom ≫ (kernel (torBaseNT M φ)).map f := by
  have hcomp : ∀ X, (torKerPointwise M φ X).hom ≫ kernel.ι ((torBaseNT M φ).app X)
      = (kernel.ι (torBaseNT M φ)).app X := fun X => by
    rw [torKerPointwise, PreservesKernel.iso_hom]
    exact kernelComparison_comp_ι (torBaseNT M φ) ((evaluation (ModuleCat A) (ModuleCat A)).obj X)
  have hinv : ∀ X, (torKerPointwise M φ X).inv ≫ (kernel.ι (torBaseNT M φ)).app X
      = kernel.ι ((torBaseNT M φ).app X) := fun X => by
    rw [Iso.inv_comp_eq, ← hcomp]
  have hmono : Mono ((kernel.ι (torBaseNT M φ)).app N') := by
    rw [← hcomp]; infer_instance
  rw [← cancel_mono ((kernel.ι (torBaseNT M φ)).app N')]
  simp only [torOneTensorKernelIsoApp, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hinv N', (kernel.ι (torBaseNT M φ)).naturality f,
    ← Category.assoc ((torKerPointwise M φ N).inv), hinv N]
  exact torOneIsoKerApp_hom_ι_naturality M φ hφ f

open CategoryTheory.Limits in
/-- **The natural isomorphism `Tor₁(M, -) ≅ ker(K ⊗ - → Aᵗ ⊗ -)`** for a finite free
presentation `φ : Aᵗ ↠ M` with kernel `K`. -/
@[ega "IV 11.2.3" "Tor₁(M, special case"]
noncomputable def torOneTensorKernelNatIso
    (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M) (hφ : Function.Surjective φ) :
    (Tor (ModuleCat A) 1).obj M ≅ kernel (torBaseNT M φ) :=
  NatIso.ofComponents (fun N => torOneTensorKernelIsoApp M φ hφ N)
    (fun {_ _} f => torOneTensorKernelIsoApp_naturality M φ hφ f)

open CategoryTheory.Limits in
/-- **Dimension-shifting δ as iso, pointwise.** For a finite free presentation
`0 → K → Aᵗ → M → 0` (`K = ker φ`, `φ` surjective) and a module `N`, the connecting map
of the homology long exact sequence of the tensored SES `torOneCxSES M φ P_N` is, in degrees
`(q+2, q+1)`, an isomorphism `Tor_{q+2}(M, N) ≅ Tor_{q+1}(K, N)`, because the middle term
`Aᵗ ⊗ -` is Tor-acyclic in both degrees `q+2` and `q+1`. -/
@[ega "III 7.6.11" "special case"]
noncomputable def torShiftIsoApp (q : ℕ) (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M)
    (hφ : Function.Surjective φ) (N : ModuleCat A) :
    ((Tor (ModuleCat A) (q + 2)).obj M).obj N
      ≅ ((Tor (ModuleCat A) (q + 1)).obj (ModuleCat.of A (LinearMap.ker φ))).obj N := by
  have P : ProjectiveResolution N := (HasProjectiveResolution.out (Z := N)).some
  set FK := (MonoidalCategory.tensoringLeft (ModuleCat A)).obj (ModuleCat.of A (LinearMap.ker φ))
    with hFK
  set FT := (MonoidalCategory.tensoringLeft (ModuleCat A)).obj (ModuleCat.of A (Fin t → A))
    with hFT
  set FM := (MonoidalCategory.tensoringLeft (ModuleCat A)).obj M with hFM
  haveI iFKa : FK.Additive := by rw [hFK]; infer_instance
  haveI iFTa : FT.Additive := by rw [hFT]; infer_instance
  haveI iFMa : FM.Additive := by rw [hFM]; infer_instance
  set S := torOneCxSES M φ P with hS
  have hSE : S.ShortExact := torOneCxSES_shortExact M φ hφ P
  have hrel : (ComplexShape.down ℕ).Rel (q + 2) (q + 1) := by simp [ComplexShape.down]
  have hz1 : IsZero (S.X₂.homology (q + 2)) :=
    IsZero.of_iso (isZero_Tor_succ_of_flat (ModuleCat.of A (Fin t → A)) N (q + 1))
      (P.isoLeftDerivedObj FT (q + 2)).symm
  have hz2 : IsZero (S.X₂.homology (q + 1)) :=
    IsZero.of_iso (isZero_Tor_succ_of_flat (ModuleCat.of A (Fin t → A)) N q)
      (P.isoLeftDerivedObj FT (q + 1)).symm
  haveI hiso : IsIso (hSE.δ (q + 2) (q + 1) hrel) := hSE.isIso_δ (q + 2) (q + 1) hrel hz1 hz2
  exact (P.isoLeftDerivedObj FM (q + 2)) ≪≫ asIso (hSE.δ (q + 2) (q + 1) hrel)
    ≪≫ (P.isoLeftDerivedObj FK (q + 1)).symm

open CategoryTheory.Limits in
/-- Explicit δ-form of `torShiftIsoApp.hom`: it is the connecting map `δ` of the tensored
SES `torOneCxSES M φ P_N` in degrees `(q+2, q+1)`, conjugated by the `Tor = H` identifications
(`isoLeftDerivedObj`). -/
theorem torShiftIsoApp_hom (q : ℕ) (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M)
    (hφ : Function.Surjective φ) (N : ModuleCat A)
    (hrel : (ComplexShape.down ℕ).Rel (q + 2) (q + 1)) :
    (torShiftIsoApp q M φ hφ N).hom
      = (((HasProjectiveResolution.out (Z := N)).some).isoLeftDerivedObj
            ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj M) (q + 2)).hom
          ≫ (torOneCxSES_shortExact M φ hφ (HasProjectiveResolution.out (Z := N)).some).δ
              (q + 2) (q + 1) hrel
          ≫ (((HasProjectiveResolution.out (Z := N)).some).isoLeftDerivedObj
                ((MonoidalCategory.tensoringLeft (ModuleCat A)).obj
                  (ModuleCat.of A (LinearMap.ker φ))) (q + 1)).inv := by
  unfold torShiftIsoApp
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom]

open CategoryTheory.Limits in
/-- **Naturality of the dimension-shifting iso `torShiftIsoApp` in `N`.** The pointwise isos
`torShiftIsoApp q M φ hφ -` are natural in `N`. -/
theorem torShiftIsoApp_naturality (q : ℕ) (M : ModuleCat A) {t : ℕ} (φ : (Fin t → A) →ₗ[A] M)
    (hφ : Function.Surjective φ) {N N' : ModuleCat A} (f : N ⟶ N') :
    ((Tor (ModuleCat A) (q + 2)).obj M).map f ≫ (torShiftIsoApp q M φ hφ N').hom
      = (torShiftIsoApp q M φ hφ N).hom
          ≫ ((Tor (ModuleCat A) (q + 1)).obj (ModuleCat.of A (LinearMap.ker φ))).map f := by
  have hrel : (ComplexShape.down ℕ).Rel (q + 2) (q + 1) := by simp [ComplexShape.down]
  rw [torShiftIsoApp_hom q M φ hφ N hrel, torShiftIsoApp_hom q M φ hφ N' hrel]
  exact leftDerived_map_comp_torOneCxSES_δ M φ hφ f (HasProjectiveResolution.out (Z := N)).some
    (HasProjectiveResolution.out (Z := N')).some (q + 2) (q + 1) hrel
