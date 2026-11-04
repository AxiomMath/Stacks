module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullbackNaturality

/-!
# Coherence of `c2` with base change along a morphism of square-zero thickenings

Let `X ⟶ X_V ⟶ X` and `X ⟶ X_W ⟶ X` be the base changes of `Spec k ⟶ Spec k[V] ⟶ Spec k` and
`Spec k ⟶ Spec k[W] ⟶ Spec k` along one `p : X ⟶ Spec k`, `H : X_W ⟶ X_V` a morphism under `X`
(so that the section of `X_V` is `X ⟶ X_W ⟶ X_V`), and `g : 𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X[𝒪_X ⊗_k W]` a
ring map over `𝒪_X` compatible with `H`. This file proves the coherence (`**`) of the proof of
`toLift_pullback` in Stacks 0DLL: the identification `c2` of derived base change along
`𝒪_X[𝒪_X ⊗_k W] ⟶ 𝒪_X` with the derived pullback along `X ⟶ X_W`
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso`), the identification `χ` of
`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturality`, and the composition comparison of
derived pullbacks along `X ⟶ X_W ⟶ X_V` compose to the identification of derived base change along
`g` and then along `𝒪_X[𝒪_X ⊗_k W] ⟶ 𝒪_X` with derived base change along
`𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`, followed by `c2` for `V`
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_of_degreewise`), given the
degreewise coherence of `G2` (`AlgebraicGeometry.Space.squareZeroComplexPullbackNaturalityIso`)
with `AlgebraicGeometry.Space.squareZeroComplexPullbackIso` and the composition comparison.

The junction of the derived equivalence with the composition comparison is proved for an arbitrary
equivalence of abelian categories
(`AlgebraicGeometry.Space.app_comp_precompDerivedEquivalenceComparison_app`) and applied with the
instances of the concrete terms. The sheafification instances of the small étale site are put first
locally: found by the default search, each costs a large part of the heartbeat budget.

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe d d' u

namespace AlgebraicGeometry.Space

section GenericJunction

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  (E : C₁ ≌ C₂) [E.functor.Additive] {T : Type*} [Category* T]

/-- A natural transformation `θ : L ⋙ P ⟶ LF` at the derived equivalence of a localized complex,
followed by the comparison `AlgebraicGeometry.Space.precompDerivedEquivalenceComparison` of `LF`,
is the factorization of the derived equivalence pushed along `L ⋙ P`, then `θ`, then the
comparison of `LF`: the naturality of `θ`. -/
theorem app_comp_precompDerivedEquivalenceComparison_app {T' : Type*} [Category* T']
    (LF : DerivedCategory C₂ ⥤ T) (L : DerivedCategory C₂ ⥤ T') (P : T' ⥤ T)
    (θ : L ⋙ P ⟶ LF) {F' : CochainComplex C₂ ℤ ⥤ T} (α : DerivedCategory.Q ⋙ LF ⟶ F')
    {F : CochainComplex C₁ ℤ ⥤ T} (e : F ≅ E.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ F')
    (K : CochainComplex C₁ ℤ) :
    θ.app ((Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor.obj
        (DerivedCategory.Q.obj K)) ≫ (precompDerivedEquivalenceComparison E LF α e).app K =
      P.map (L.map (E.functor.mapDerivedCategoryFactors.hom.app K)) ≫
        θ.app (DerivedCategory.Q.obj ((E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
            ≫
          α.app ((E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ e.inv.app K := by
  rw [precompDerivedEquivalenceComparison_app]
  exact (θ.naturality_assoc _ _).symm

/-- Removing the identities from the factorization of `χ` on complexes, with the objects
abstract. -/
theorem comp_eq_comp_of_id_comp_comp_id {E : Type*} [Category E] {A B C D F G : E} (chi : A ⟶ B)
    (r : B ⟶ C) (dH : C ⟶ D) (q : D ⟶ F) (eW : A ⟶ G) (ρW : G ⟶ F)
    (h : chi ≫ r ≫ dH ≫ q = eW ≫ 𝟙 G ≫ ρW ≫ 𝟙 F) :
    chi ≫ r ≫ dH ≫ q = eW ≫ ρW := by
  simpa using h

/-- The naturality of a natural transformation between two composites, with the composites
written out. -/
theorem comp_naturality_comp {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E) (η : F ⋙ G ⟶ F' ⋙ G') {X Y : C}
    (f : X ⟶ Y) : G.map (F.map f) ≫ η.app Y = η.app X ≫ G'.map (F'.map f) :=
  η.naturality f

/-- Reassociating the left side of the coherence, with the objects abstract. -/
theorem squareZeroCoherence_left_assoc {E : Type*} [Category E] {A B C D F : E} (a : A ⟶ B)
    (b : B ⟶ C)
    (c : C ⟶ D) (d : D ⟶ F) {z : A ⟶ F} (h : a ≫ b ≫ c ≫ d = z) : (a ≫ b ≫ c) ≫ d = z := by
  rw [← h]
  simp only [Category.assoc]

/-- Reassociating the right side of the coherence, with the objects abstract. -/
theorem squareZeroCoherence_right_assoc {E : Type*} [Category E] {A B C F : E} (a : A ⟶ B)
    (b : B ⟶ C)
    (c : C ⟶ F) {y : B ⟶ F} {z : A ⟶ F} (hy : b ≫ c = y) (h : a ≫ y = z) : (a ≫ b) ≫ c = z := by
  rw [Category.assoc, hy, h]

/-- Inserting identities into the left side of the coherence, with the objects abstract. -/
theorem comp_id_comp_id_comp_eq {E : Type*} [Category E] {A B B' C F : E} (x : A ⟶ B)
    (y : B ⟶ B') (z : B' ⟶ C) (c : C ⟶ F) {w : A ⟶ F} (h : (x ≫ y ≫ z) ≫ c = w) :
    (x ≫ 𝟙 B ≫ y ≫ 𝟙 B' ≫ z) ≫ c = w := by
  simpa using h

/-- Removing identities from the left side of the coherence, with the objects abstract. -/
theorem eq_of_comp_id_comp_id_comp_eq {E : Type*} [Category E] {A B B' C : E} (x : A ⟶ B)
    (y : B ⟶ B') (z : B' ⟶ C) {w : A ⟶ C} (h : x ≫ 𝟙 B ≫ y ≫ 𝟙 B' ≫ z = w) :
    x ≫ y ≫ z = w := by
  simpa using h

end GenericJunction

section Coherence

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  hasSheafCompose_smallEtale_forget₂_ringCat

variable {k : Type u} [CommRing k] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))} {V W : SiteModule k B}
  {X X'V X'W : AlgebraicSpaces B S hS} {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {iW : X ⟶ X'W} (hiW : IsThickeningHom B S hS iW)
  {qW : X'W ⟶ X} (hW : iW ≫ qW = 𝟙 X) {hqW : yoneda.relativelyRepresentable qW.hom}
  {p'W : X'W.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS W)}
  {τW : squareZeroOver k B S hS toS W ⟶ algebraOver k B S hS toS hk}
  (hipW : iW.hom ≫ p'W = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk W))
  (hpbW : IsPullback qW.hom p'W p (yoneda.map τW))
  (hβτW : squareZeroArrow k B S hS toS hk W ≫ τW = 𝟙 _)
  {H : X'W ⟶ X'V} (hiV : IsThickeningHom B S hS (iW ≫ H))
  {qV : X'V ⟶ X} (hV : (iW ≫ H) ≫ qV = 𝟙 X) {hqV : yoneda.relativelyRepresentable qV.hom}
  {p'V : X'V.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τV : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hipV : (iW ≫ H).hom ≫ p'V = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpbV : IsPullback qV.hom p'V p (yoneda.map τV))
  (hβτV : squareZeroArrow k B S hS toS hk V ≫ τV = 𝟙 _)
  [hDV : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
      (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))]
      [hDW : HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
      (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))))]

/-- `AlgebraicGeometry.Space.squareZeroDerivedComparison` is
`AlgebraicGeometry.Space.precompDerivedEquivalenceComparison` of the derived pullback. -/
theorem squareZeroDerivedComparison_eq_precomp :
    squareZeroDerivedComparison (hq := hqV) hiV hV hipV hpbV hβτV =
      @precompDerivedEquivalenceComparison _ _ _ hDV _ _ _ _
        (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV)
        (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV) _ _
        (derivedPull B S hS (hasDerivedModulePullbacks B S hS) (iW ≫ H)) _
        (derivedPullComparison B S hS (iW ≫ H)) _
        (squareZeroComplexPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV) :=
  rfl

/-- The composition comparison of derived pullbacks along `X ⟶ X_W ⟶ X_V` at the derived
equivalence of a localized complex, followed by
`AlgebraicGeometry.Space.squareZeroDerivedComparison`: the naturality of the composition
comparison, read through
`AlgebraicGeometry.Space.app_comp_precompDerivedEquivalenceComparison_app`. -/
theorem squareZero_triangle_inv_app_comp_squareZeroDerivedComparison_app
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2) ((tensorByBaseModuleOfHom k
    (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
    (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) ℤ) :
    ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : iW ≫ H = iW ≫ H)).inv.app
        ((squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.obj
            (DerivedCategory.Q.obj M)) ≫
      (squareZeroDerivedComparison (hq := hqV) hiV hV hipV hpbV hβτV).app M =
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW).map
        ((derivedPull B S hS (hasDerivedModulePullbacks B S hS) H).map
        ((squareZeroDerivedEquivalenceFactors (hqV := hqV) hiV hV hipV hpbV hβτV).hom.app M)) ≫
      ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : iW ≫ H = iW ≫ H)).inv.app _ ≫
        (derivedPullComparison B S hS (iW ≫ H)).app _ ≫
          (squareZeroComplexPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV).inv.app M :=
  @app_comp_precompDerivedEquivalenceComparison_app _ _ _ hDV _ _ _ _
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV)
    (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV) _ _ _ _
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) (iW ≫ H))
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) H)
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW)
    ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : iW ≫ H = iW ≫ H)).inv _
    (derivedPullComparison B S hS (iW ≫ H)) _
    (squareZeroComplexPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV) M

variable (hH : yoneda.relativelyRepresentable H.hom) {g : (sqZeroExtSheafAnySite
    (structureSheaf B S hS X.1 X.2) ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS
    hk p)).obj V.obj)) ⟶ (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
    ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
    (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))}

attribute [local instance] isContinuous_smallBaseChange



/-- **The coherence (`**`) of `c2` with base change along `H`, at a complex**, given the
degreewise coherence `hMC` of `G2` with `AlgebraicGeometry.Space.squareZeroComplexPullbackIso`
and the composition comparison. -/
theorem squareZeroDerivedPullbackIso_comp_coherence_app_Q (hg :
    (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH rfl
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k
        (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)) =
        (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
        (hMC : ∀ (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
        (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) ℤ),
      (squareZeroComplexPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW).hom.app
          ((extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g).obj M) ≫
        (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
            ((((modulePullbackDataTopos B S hS).pull iW).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((squareZeroComplexPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH
              rfl hg).inv.app M)) ≫
        (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
            ((NatTrans.mapHomologicalComplex ((RingedToposHom.pullbackModulesCompIso
            (smallEtaleRingedToposHom B S hS iW) (smallEtaleRingedToposHom B S hS H)).symm ≪≫
            pullbackModulesCompTransport B S hS iW H).hom (ComplexShape.up ℤ)).app
          (((squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV
              hβτV).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        (squareZeroComplexPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV).inv.app M =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (extensionOfScalarsCompIso g hgp) (ComplexShape.up ℤ)).hom.app M))
            (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
            (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) ℤ) :
    ((squareZeroDerivedPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW
        (derivedExtensionOfScalarsData.{d', u + 1} (sqZeroExtSheafAnySiteProj
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))).hom.app
            ((derivedExtensionOfScalars.{d, d'} g).obj (DerivedCategory.Q.obj M)) ≫
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW).map
          ((squareZeroDerivedPullbackNaturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH rfl
          hg).hom.app (DerivedCategory.Q.obj M)) ≫
      ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : iW ≫ H = iW ≫ H)).inv.app
          ((squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.obj
          (DerivedCategory.Q.obj M))) ≫
        (squareZeroDerivedComparison (hq := hqV) hiV hV hipV hpbV hβτV).app M =
    ((derivedExtensionOfScalarsCompIso.{d, d', u + 1} g hgp).hom.app (DerivedCategory.Q.obj M) ≫
        (squareZeroDerivedPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))).hom.app
            (DerivedCategory.Q.obj M)) ≫
        (squareZeroDerivedComparison (hq := hqV) hiV hV hipV hpbV hβτV).app M := by
  have hcmp := squareZero_triangle_inv_app_comp_squareZeroDerivedComparison_app (hqV := hqV) hiV hV
      hipV hpbV hβτV M
  have hcomp := squareZero_triangle_inv_app_Q_comp_derivedPullComparison (iW := iW) (H := H)
    (((squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M)
  have hchi0 := @derivedEquivalenceLeftDerivedIso_fac _ _ _ hDV _ _ _ hDW _ _ _ _ _ _ _ _
      (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV)
    (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV)
        (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW)
    (squareZeroModuleEquivalence_functor_additive (hq := hqW) hiW hW hipW hpbW hβτW)
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) H)
        (((modulePullbackDataTopos B S hS).pull H).mapHomologicalComplex (ComplexShape.up ℤ))
    (derivedPullComparison B S hS H) (isLeftDerivedFunctor_derivedPullComparison B S hS H)
    (derivedExtensionOfScalars.{d, d'} g) (extensionOfScalarsCochainComplex
        (SmallEtale.topology B S hS X.1) g) (derivedExtensionOfScalarsCounit.{d, d'} g)
    (isLeftDerivedFunctor_derivedExtensionOfScalarsCounit.{d, d'} g)
        (squareZeroComplexPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH rfl
        hg) M
  have hchi := comp_comp_eq_of_comp_comp_comp_hom_eq _ _ _ (DerivedCategory.Q.mapIso
      ((squareZeroComplexPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH rfl
      hg).app M)) _ _
    (comp_eq_comp_of_id_comp_comp_id _ _ _ _ _ _ hchi0)
  have hc2 := ((squareZeroDerivedPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW
        (derivedExtensionOfScalarsData.{d', u + 1} (sqZeroExtSheafAnySiteProj
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))).hom.naturality
            ((derivedExtensionOfScalarsCounit.{d, d'} g).app M)).symm
  have hdpc := (comp_naturality_comp _ _ _ _ (derivedPullComparison B S hS iW)
    (X := ((squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW
        hβτW).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g).obj M))
    (Y := (((modulePullbackDataTopos B S hS).pull H).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV
          hβτV).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj M))
          ((squareZeroComplexPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH
          rfl hg).inv.app M))
  have hfacW := squareZeroDerivedPullbackIso_hom_app_Q_comp (hq := hqW) hiW hW hipW hpbW hβτW
    (derivedExtensionOfScalarsData.{d', u + 1} (sqZeroExtSheafAnySiteProj
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
        (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))
        ((extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g).obj M)
  have hL := derivedExtensionOfScalarsCompIso_hom_app_comp_counit.{d, d', u + 1} g hgp M
  have hfacV := NatTrans.congr_app (baseChangeIso_fac _ (derivedExtensionOfScalarsData.{d, u + 1}
      (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (squareZeroDerivedExtensionOfScalars (hq := hqV) hiV hV hipV hpbV hβτV)) M
  have hMCM := hMC M
  refine (squareZeroCoherence_left_assoc _ _ _ _ (squareZero_coherence_chain
    (P := derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _
    hcmp hcomp hchi hc2 hdpc hfacW hMCM)).trans ?_
  · exact (squareZeroCoherence_right_assoc _ _ _ hfacV hL).symm

/-- **Stacks 0DLL, the coherence (`**`) of `c2` with base change along `H`**: the identification
`c2` for `W` at `g^* K`, followed by the derived pullback along `i_W` of `χ` and the composition
comparison of derived pullbacks along `X ⟶ X_W ⟶ X_V`, is the identification of derived base change
along `g` and then along `𝒪_X[𝒪_X ⊗_k W] ⟶ 𝒪_X` with derived base change along
`𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`, followed by `c2` for `V`; given the degreewise coherence `hMC`. Both
sides are natural transformations into a left derived functor, so they agree as soon as they agree
on complexes (`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence_app_Q`). -/
theorem squareZeroDerivedPullbackIso_comp_coherence_of_degreewise
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH rfl
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (hgp : g ≫ (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k
        (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)) =
        (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
        (hMC : ∀ (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
        (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) ℤ),
      (squareZeroComplexPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW).hom.app
          ((extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g).obj M) ≫
        (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
            ((((modulePullbackDataTopos B S hS).pull iW).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((squareZeroComplexPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH
              rfl hg).inv.app M)) ≫
        (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
            ((NatTrans.mapHomologicalComplex ((RingedToposHom.pullbackModulesCompIso
            (smallEtaleRingedToposHom B S hS iW) (smallEtaleRingedToposHom B S hS H)).symm ≪≫
            pullbackModulesCompTransport B S hS iW H).hom (ComplexShape.up ℤ)).app
          (((squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV
              hβτV).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        (squareZeroComplexPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV).inv.app M =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (extensionOfScalarsCompIso g hgp) (ComplexShape.up ℤ)).hom.app M))
            (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
            (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))) :
    (squareZeroDerivedPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW
        (derivedExtensionOfScalarsData.{d', u + 1} (sqZeroExtSheafAnySiteProj
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))).hom.app
            ((derivedExtensionOfScalars.{d, d'} g).obj K) ≫
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW).map
          ((squareZeroDerivedPullbackNaturality hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH rfl
          hg).hom.app K) ≫
      ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : iW ≫ H = iW ≫ H)).inv.app
          ((squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.obj K) =
    (derivedExtensionOfScalarsCompIso.{d, d', u + 1} g hgp).hom.app K ≫
        (squareZeroDerivedPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))).hom.app K := by
  have := (squareZeroDerivedExtensionOfScalars (hq := hqV) hiV hV hipV hpbV hβτV).isLeftDerived
  have h := Functor.leftDerived_ext (squareZeroDerivedExtensionOfScalars (hq := hqV) hiV hV hipV
      hpbV hβτV).baseChange (squareZeroDerivedExtensionOfScalars (hq := hqV) hiV hV hipV hpbV
      hβτV).comparison (HomologicalComplex.quasiIso (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
      (SheafOfModules.unit _) (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))
      (ComplexShape.up ℤ))
    ((derivedExtensionOfScalars.{d, d'} g) ⋙ (derivedExtensionOfScalars.{d', u + 1}
        (sqZeroExtSheafAnySiteProj ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))))
    (Functor.whiskerLeft (derivedExtensionOfScalars.{d, d'} g)
        (squareZeroDerivedPullbackIso (hq := hqW) hiW hW hipW hpbW hβτW
        (derivedExtensionOfScalarsData.{d', u + 1} (sqZeroExtSheafAnySiteProj
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))).hom ≫
            (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (squareZeroDerivedPullbackNaturality hiV hV hipV hpbV hβτV hiW hW hipW
          hpbW hβτW hH rfl hg).hom (derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW) ≫
          (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor
          ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : iW ≫ H = iW ≫ H)).inv)
    ((derivedExtensionOfScalarsCompIso.{d, d', u + 1} g hgp).hom ≫
        (squareZeroDerivedPullbackIso (hq := hqV) hiV hV hipV hpbV hβτV
        (derivedExtensionOfScalarsData.{d, u + 1} (sqZeroExtSheafAnySiteProj
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))).hom) (by
      ext M
      exact comp_id_comp_id_comp_eq _ _ _ _
        (squareZeroDerivedPullbackIso_comp_coherence_app_Q hiW hW hipW hpbW hβτW hiV hV hipV hpbV
            hβτV
          hH hg hgp hMC M))
  exact eq_of_comp_id_comp_id_comp_eq _ _ _ (NatTrans.congr_app h K)

end Coherence

end AlgebraicGeometry.Space

end
