module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexSpecChart
public import StacksFrontier.RingTheory.Dualizing.RelativeExistenceInputs
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalExcision

/-!
# Generators on the diagonal open of a morphism of spectra, and base change

Let `A` be a flat, finitely presented `R`-algebra and `f : X ⟶ S` a morphism identified with
`Spec A ⟶ Spec R`. On the diagonal open `Spec(A ⊗_R A)` of `f`, a morphism
`ξ : Δ_*𝒪_X ⟶ L pr₁^*K`, with `K` read on `Spec A` as the sheaf associated to `K_A`, is the
sheaf associated to a morphism `ξ_A : A ⟶ K_A ⊗ᴸ_A (A ⊗_R A)` of `D(A ⊗_R A)`, and `ξ` generates
its Hom group under precomposition by endomorphisms of `Δ_*𝒪_X` exactly when `ξ_A` generates
`Hom_{D(A ⊗_R A)}(A, K_A ⊗ᴸ_A (A ⊗_R A))`.

For a ring map `R ⟶ R'` with `A' = A ⊗_R R'`, derived pullback along
`Spec(A' ⊗_{R'} A') ⟶ Spec(A ⊗_R A)` is derived base change along `A ⊗_R A ⟶ A' ⊗_{R'} A'`
(Stacks 08DW). So the "moreover" clause of Stacks 0E2F says: if `K_A` is a relative dualizing
complex for `R → A` and `ξ` is a generator, the derived pullback of `ξ`, read through any
identifications of the diagonal objects and of the projections, is a generator. This is the
algebraic input of Stacks 0E2Y.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.ofSpec_isPostcompGenerator_iff`: the dictionary for
  generators.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.ofSpec_isPostcompGenerator_baseChange`: derived
  base change of a generator is a generator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

variable {C D C' E : Type*} [Category* C] [Category* D] [Category* C'] [Category* E]

/-- Reading a morphism through a functor and conjugating isomorphisms. -/
theorem eq_hom_map_inv_of_preimage {F₀ : C ⥤ D} (hF₀ : F₀.FullyFaithful) {X Y : D} {X₀ Y₀ : C}
    (e₁ : X ≅ F₀.obj X₀) (e₂ : Y ≅ F₀.obj Y₀) (ξ : X ⟶ Y) :
    ξ = e₁.hom ≫ F₀.map (hF₀.preimage (e₁.inv ≫ ξ ≫ e₂.hom)) ≫ e₂.inv := by
  simp

/-- A functor applied to a conjugate of the image of `ξr` under `F₀`, rewritten through a
natural isomorphism `F₀ ⋙ L ≅ G ⋙ F'`. -/
theorem conj_map_eq_of_natIso {F₀ : C ⥤ D} {L : D ⥤ E} {G : C ⥤ C'} {F' : C' ⥤ E}
    (c : F₀ ⋙ L ≅ G ⋙ F') {X Y : D} {X₀ Y₀ : C} {X' Y' : E}
    (e₁ : X ≅ F₀.obj X₀) (e₂ : Y ≅ F₀.obj Y₀) (ξr : X₀ ⟶ Y₀)
    (φ : X' ≅ L.obj X) (ψ : L.obj Y ≅ Y') :
    φ.hom ≫ L.map (e₁.hom ≫ F₀.map ξr ≫ e₂.inv) ≫ ψ.hom =
      (φ ≪≫ L.mapIso e₁ ≪≫ c.app X₀).hom ≫ F'.map (G.map ξr) ≫
        ((c.app Y₀).symm ≪≫ L.mapIso e₂.symm ≪≫ ψ).hom := by
  have h := c.hom.naturality ξr
  simp only [Functor.comp_map] at h
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc, L.map_comp]
  rw [reassoc_of% h.symm, Iso.hom_inv_id_app_assoc]

/-- The image under a fully faithful functor of a morphism conjugated by preimages of
isomorphisms. -/
theorem map_preimageIso_conj {F' : C' ⥤ E} (hF' : F'.FullyFaithful) {A B A' B' : C'}
    {X' Y' : E} (a : X' ≅ F'.obj A) (a' : X' ≅ F'.obj A') (b : F'.obj B ≅ Y') (b' : Y' ≅ F'.obj B')
    (g : A ⟶ B) :
    F'.map ((hF'.preimageIso (a.symm ≪≫ a')).inv ≫ g ≫ (hF'.preimageIso (b ≪≫ b')).hom) =
      a'.inv ≫ (a.hom ≫ F'.map g ≫ b.hom) ≫ b'.hom := by
  simp

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} (f : X ⟶ S) {R A : CommRingCat.{u}} [Algebra R A]
  (eX : X ≅ Spec A) (eS : S ≅ Spec R)
  (hf : eX.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = f ≫ eS.hom)

/-- **The dictionary for generators on `Spec(A ⊗_R A)`.** A morphism `ξ : Δ_*𝒪_X ⟶ L pr₁^*K`
generates its Hom group under precomposition by endomorphisms of `Δ_*𝒪_X` exactly when the
corresponding morphism `A ⟶ K_A ⊗ᴸ_A (A ⊗_R A)` of `D(A ⊗_R A)` does. -/
theorem ofSpec_isPostcompGenerator_iff [Module.Flat R A] (K : DerivedCategory X.Modules)
    (KA : DerivedCategory (ModuleCat.{u} A))
    (eK : (derivedPullback eX.inv.toLRSHom.toShHom).obj K ≅
      (tilde.functor A).mapDerivedCategory.obj KA)
    (ξ : (ofSpec f eX eS hf).diagonalObject ⟶ (ofSpec f eX eS hf).derivedPullbackProj K) :
    Dualizing.IsPostcompGenerator ξ ↔ Dualizing.IsPostcompGenerator
      ((StandardModel.mapDerivedCategoryFullyFaithful (envelopingRing R A)).preimage
        ((ofSpecDiagonalObjectIso f eX eS hf).inv ≫ ξ ≫
          (ofSpecDerivedPullbackProjIso f eX eS hf K KA eK).hom)) := by
  let hff := StandardModel.mapDerivedCategoryFullyFaithful (envelopingRing R A)
  have := hff.full
  have := hff.faithful
  rw [← Dualizing.IsPostcompGenerator.map_iff_of_bijective (tilde.functor _).mapDerivedCategory
    _ (hff.map_bijective _ _) (hff.map_surjective), hff.map_preimage]
  exact (Dualizing.IsPostcompGenerator.conj_iff (ofSpecDiagonalObjectIso f eX eS hf)
    (ofSpecDerivedPullbackProjIso f eX eS hf K KA eK) ξ).symm

variable {X' S' : Scheme.{u}} (f' : X' ⟶ S') {R' : CommRingCat.{u}} [Algebra R R']
  (eX' : X' ≅ Spec (CommRingCat.of (A ⊗[R] R'))) (eS' : S' ≅ Spec R')
  (hf' : eX'.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R' (A ⊗[R] R'))) = f' ≫ eS'.hom)

variable (R A R') in
/-- `A ⊗_R A ⟶ A' ⊗_{R'} A'` for `A' = A ⊗_R R'`, as a morphism of commutative rings. -/
abbrev envelopingBaseChangeHom :
    envelopingRing R A ⟶ envelopingRing R' (CommRingCat.of (A ⊗[R] R')) :=
  CommRingCat.ofHom (Dualizing.envelopingBaseChangeRingHom R A R')

/-- **Derived base change of a generator is a generator** (the "moreover" clause of Stacks
0E2F, read on the diagonal opens `Spec(A ⊗_R A)` and `Spec(A' ⊗_{R'} A')`). Let `K` on `X` be the
sheaf associated to a relative dualizing complex `K_A` for `R → A`, and `K'` on `X'` the sheaf
associated to `K_A ⊗ᴸ_A A'`. If `ξ : Δ_*𝒪_X ⟶ L pr₁^*K` is a generator, then so is its derived
pullback along `Spec(A' ⊗_{R'} A') ⟶ Spec(A ⊗_R A)`, read through any identifications `φ` of the
diagonal objects and `ψ` of the projections. -/
theorem ofSpec_isPostcompGenerator_baseChange [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory X.Modules) (KA : DerivedCategory (ModuleCat.{u} A))
    (eK : (derivedPullback eX.inv.toLRSHom.toShHom).obj K ≅
      (tilde.functor A).mapDerivedCategory.obj KA)
    (hKA : Dualizing.IsRelativeDualizingComplex R A KA)
    (K' : DerivedCategory X'.Modules)
    (eK' : haveI : Module.Flat R' (A ⊗[R] R') := Dualizing.flat_baseChange R A R'
      (derivedPullback eX'.inv.toLRSHom.toShHom).obj K' ≅
        (tilde.functor (CommRingCat.of (A ⊗[R] R'))).mapDerivedCategory.obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj KA))
    (ξ : (ofSpec f eX eS hf).diagonalObject ⟶ (ofSpec f eX eS hf).derivedPullbackProj K)
    (hξ : Dualizing.IsPostcompGenerator ξ)
    (φ : (ofSpec f' eX' eS' hf').diagonalObject ≅
      (derivedPullback (Spec.map (envelopingBaseChangeHom R A R')).toLRSHom.toShHom).obj
        (ofSpec f eX eS hf).diagonalObject)
    (ψ : (derivedPullback (Spec.map (envelopingBaseChangeHom R A R')).toLRSHom.toShHom).obj
        ((ofSpec f eX eS hf).derivedPullbackProj K) ≅
      (ofSpec f' eX' eS' hf').derivedPullbackProj K') :
    Dualizing.IsPostcompGenerator (φ.hom ≫
      (derivedPullback (Spec.map (envelopingBaseChangeHom R A R')).toLRSHom.toShHom).map ξ ≫
        ψ.hom) := by
  have : Module.Flat R' (A ⊗[R] R') := Dualizing.flat_baseChange R A R'
  let B := envelopingRing R A
  let B' := envelopingRing R' (CommRingCat.of (A ⊗[R] R'))
  let γ := envelopingBaseChangeHom R A R'
  let hff := StandardModel.mapDerivedCategoryFullyFaithful B
  let hff' := StandardModel.mapDerivedCategoryFullyFaithful B'
  have := hff'.full
  have := hff'.faithful
  let F' := (tilde.functor B').mapDerivedCategory
  let BC := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    γ.hom).functor
  let Lw := derivedPullback (Spec.map γ).toLRSHom.toShHom
  let c := StandardModel.affinePullbackComparison B B' γ
  let D₁ := ofSpecDiagonalObjectIso f eX eS hf
  let D₂ := ofSpecDerivedPullbackProjIso f eX eS hf K KA eK
  let D₁' := ofSpecDiagonalObjectIso f' eX' eS' hf'
  let D₂' := ofSpecDerivedPullbackProjIso f' eX' eS' hf' K' _ eK'
  let ξr := hff.preimage (D₁.inv ≫ ξ ≫ D₂.hom)
  have hspan : Submodule.span B ({ξr} : Set _) = ⊤ :=
    Dualizing.span_singleton_of_postcomp_surjective ξr
      (Dualizing.diagonal_endomorphism_eq_smul_id R A)
      ((ofSpec_isPostcompGenerator_iff f eX eS hf K KA eK ξ).1 hξ)
  -- the conjugating isomorphisms
  let α : (ofSpec f' eX' eS' hf').diagonalObject ≅ F'.obj (BC.obj (Dualizing.diagonalSingle R A)) :=
    φ ≪≫ Lw.mapIso D₁ ≪≫ c.app _
  let β : F'.obj (BC.obj ((Dualizing.diagonalDerivedExtension R A).obj KA)) ≅
      (ofSpec f' eX' eS' hf').derivedPullbackProj K' :=
    (c.app _).symm ≪≫ Lw.mapIso D₂.symm ≪≫ ψ
  have hξ' : φ.hom ≫ Lw.map ξ ≫ ψ.hom = α.hom ≫ F'.map (BC.map ξr) ≫ β.hom := by
    have h := conj_map_eq_of_natIso c D₁ D₂ ξr φ ψ
    rwa [← eq_hom_map_inv_of_preimage hff D₁ D₂ ξ] at h
  let eΔ := hff'.preimageIso (α.symm ≪≫ D₁')
  let eM := hff'.preimageIso (β ≪≫ D₂')
  have hgen' : Dualizing.IsPostcompGenerator (F'.map (eΔ.inv ≫ BC.map ξr ≫ eM.hom)) :=
    Dualizing.IsPostcompGenerator.map (Dualizing.postcomp_surjective_of_span_singleton _
      (hKA.span_derivedBaseChange_diagonalGenerator R' ξr hspan eΔ eM)) F'
  have hF : F'.map (eΔ.inv ≫ BC.map ξr ≫ eM.hom) =
      D₁'.inv ≫ (α.hom ≫ F'.map (BC.map ξr) ≫ β.hom) ≫ D₂'.hom :=
    map_preimageIso_conj hff' α D₁' β D₂' (BC.map ξr)
  rw [hF, ← hξ'] at hgen'
  exact (Dualizing.IsPostcompGenerator.conj_iff D₁' D₂' _).1 hgen'

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
