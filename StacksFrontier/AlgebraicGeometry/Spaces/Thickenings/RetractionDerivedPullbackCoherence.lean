module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivedPullComparisonCompDegreewise
public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsCompCounit
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionFac

/-!
# Coherence of `c2` with base change along a morphism of square-zero thickenings

Let `X ⟶ X_V ⟶ X` and `X ⟶ X_W ⟶ X` be the base changes of `Spec k ⟶ Spec k[V] ⟶ Spec k` and
`Spec k ⟶ Spec k[W] ⟶ Spec k` along one `p : X ⟶ Spec k`, `H : X_W ⟶ X_V` a morphism under `X`,
and `g : 𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X[𝒪_X ⊗_k W]` a ring map over `𝒪_X`. Given an identification `χ` of
derived base change along `g` with the derived pullback along `H`, read through the derived
equivalences, compatible with a degreewise identification `G2` of pullback along `H` with
extension of scalars along `g`, and given the degreewise coherence of `G2` with the comparisons
`AlgebraicGeometry.Space.squareZeroPullbackIso` and the composition comparisons, the
identifications `c2` of Stacks 0DLL for `V` and `W`
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso`) are compatible with `χ`, the composition
comparison of derived pullbacks along `X ⟶ X_W ⟶ X_V`, and the identification of derived base
change along `g` and then along `𝒪_X[𝒪_X ⊗_k W] ⟶ 𝒪_X` with derived base change along
`𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X`.

This file holds the pieces of that computation on complexes: the abstract shape of the chain
(`AlgebraicGeometry.Space.squareZero_coherence_chain`), the comparison
`AlgebraicGeometry.Space.squareZeroDerivedComparison` written out
(`AlgebraicGeometry.Space.squareZeroDerivedComparison_app`), the compatibility of `c2` with the
comparisons with complexes (`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_hom_app_Q_comp`),
and the composition comparison along `X ⟶ X_W ⟶ X_V` read on complexes
(`AlgebraicGeometry.Space.squareZero_triangle_inv_app_Q_comp_derivedPullComparison`).

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

/-- The abstract shape of the coherence of `c2` with base change along a morphism of square-zero
thickenings, read on complexes: seven commuting pieces, with the objects abstract so that the
different spellings of one object meet only when it is applied. -/
theorem squareZero_coherence_chain {D E F : Type*} [Category D] [Category E] [Category F]
    (P : D ⥤ E) (T : F ⥤ E) {A₁ A₂ : F} {B₀ B₁ B₂ B₃ B₄ B₅ : D} {C₁ C₂ C₂' C₃ C₅ C₆ E₀ : E}
    (x₁ : T.obj A₁ ⟶ P.obj B₀) (chi : B₀ ⟶ B₁) (x₃ : P.obj B₁ ⟶ C₁) (cmp : C₁ ⟶ E₀)
    (r : B₁ ⟶ B₂) (t : P.obj B₂ ⟶ C₂) (dV : C₂ ⟶ C₂') (sV : C₂' ⟶ E₀) (dH : B₂ ⟶ B₃)
    (dW' : P.obj B₃ ⟶ C₃) (qτ : C₃ ⟶ C₂') (eW : B₀ ⟶ B₄) (ρW : B₄ ⟶ B₅) (qG : B₅ ⟶ B₃)
    (αg : A₁ ⟶ A₂) (c2N : T.obj A₂ ⟶ P.obj B₄) (dW : P.obj B₅ ⟶ C₅) (qiG : C₅ ⟶ C₃)
    (αW : T.obj A₂ ⟶ C₆) (sWh : C₆ ⟶ C₅) (qE : C₆ ⟶ E₀)
    (hcmp : x₃ ≫ cmp = P.map r ≫ t ≫ dV ≫ sV) (hcomp : t ≫ dV = P.map dH ≫ dW' ≫ qτ)
    (hchi : chi ≫ r ≫ dH = eW ≫ ρW ≫ qG) (hc2 : x₁ ≫ P.map eW = T.map αg ≫ c2N)
    (hdpc : P.map qG ≫ dW' = dW ≫ qiG) (hfacW : c2N ≫ P.map ρW ≫ dW = αW ≫ sWh)
    (hMC : sWh ≫ qiG ≫ qτ ≫ sV = qE) :
    x₁ ≫ P.map chi ≫ x₃ ≫ cmp = T.map αg ≫ αW ≫ qE := by
  have h1 : P.map chi ≫ P.map r ≫ P.map dH = P.map eW ≫ P.map ρW ≫ P.map qG := by
    simp only [← Functor.map_comp]
    rw [hchi]
  rw [hcmp, reassoc_of% hcomp, reassoc_of% h1, reassoc_of% hc2, reassoc_of% hdpc,
    reassoc_of% hfacW, hMC]

/-- Removing the identities from a composite, with the objects abstract. -/
theorem id_comp_id_comp_comp_id_comp_eq {E : Type*} [Category E] {A B C F : E} {c : A ⟶ F}
    (l : A ⟶ B) (dv : B ⟶ C) (sv : C ⟶ F) (h : c = 𝟙 A ≫ 𝟙 A ≫ l ≫ 𝟙 B ≫ dv ≫ sv) :
    c = l ≫ dv ≫ sv := by
  simpa using h

/-- Moving the inverse of a component of a natural isomorphism across an equation, with the
objects abstract. -/
theorem comp_comp_eq_comp_hom_of_comp_comp_comp_inv_eq {E C : Type*} [Category E] [Category C]
    {G G' : C ⥤ E} {A B D : E} {Y : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ G'.obj Y) (e : G ≅ G')
    (d : A ⟶ G.obj Y) (h : a ≫ b ≫ c ≫ e.inv.app Y = d) : a ≫ b ≫ c = d ≫ e.hom.app Y := by
  rw [← h]
  simp

/-- Replacing a factor by a definitionally equal composite with an identity, with the objects
abstract. -/
theorem comp_eq_of_eq_comp_id {E : Type*} [Category E] {A B C : E} {t x : A ⟶ B} {d : B ⟶ C}
    {r : A ⟶ C} (hx : t = x ≫ 𝟙 B) (h : x ≫ d = r) : t ≫ d = r := by
  rw [hx, Category.comp_id, h]

/-- The final bookkeeping of `AlgebraicGeometry.Space.squareZeroDerivedPullbackIso_comp_coherence`,
with the objects abstract. -/
theorem comp_comp_eq_of_eq_of_eq_id {E : Type*} [Category E] {A A' B B' C _D F : E}
    (cI : A ⟶ A') (c2v : A' ⟶ C) (cmp : C ⟶ F) (c2w : A ⟶ B) (pchi : B ⟶ B') (tri : B' ⟶ C)
    {Z : A ⟶ F} (hL : cI ≫ c2v ≫ cmp = Z) (hR : c2w ≫ pchi ≫ tri ≫ cmp = Z) :
    (cI ≫ c2v) ≫ cmp = (c2w ≫ 𝟙 B ≫ pchi ≫ 𝟙 B' ≫ tri) ≫ cmp := by
  simp only [Category.id_comp, Category.assoc, hL, hR]

/-- Removing identities from a composite, with the objects abstract. -/
theorem eq_of_eq_comp_id_comp {E : Type*} [Category E] {A _A' B B' C : E} {x y : A ⟶ C}
    (c2w : A ⟶ B) (pchi : B ⟶ B') (tri : B' ⟶ C) (hx : x = c2w ≫ pchi ≫ tri)
    (hy : y = c2w ≫ 𝟙 B ≫ pchi ≫ 𝟙 B' ≫ tri) : x = y := by
  rw [hx, hy]
  simp only [Category.id_comp]

/-- Rearranging the factorization of `χ` on complexes, with the objects abstract. -/
theorem comp_comp_eq_of_comp_comp_comp_hom_eq {E : Type*} [Category E] {A B C D F G : E}
    (chi : A ⟶ B) (r : B ⟶ C) (dH : C ⟶ D) (q : D ≅ F) (eW : A ⟶ G) (ρW : G ⟶ F)
    (h : chi ≫ r ≫ dH ≫ q.hom = eW ≫ ρW) : chi ≫ r ≫ dH = eW ≫ ρW ≫ q.inv := by
  rw [← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

section Retraction

attribute [local instance 10000] HasDerivedCategory.standard

variable {k : Type u} [CommRing k] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))} {V : SiteModule k B}
  {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'} (hi : IsThickeningHom B S hS i)
  {q : X' ⟶ X} (h : i ≫ q = 𝟙 X) {hq : yoneda.relativelyRepresentable q.hom}
  {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {p' : X'.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τ : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hip : i.hom ≫ p' = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpb : IsPullback q.hom p' p (yoneda.map τ))
  (hβτ : squareZeroArrow k B S hS toS hk V ≫ τ = 𝟙 _)
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))]

/-- `AlgebraicGeometry.Space.squareZeroDerivedComparison` at a complex, unfolded: the derived
pullback of the factorization of the derived equivalence, the comparison of the derived pullback
with degreewise pullback, and `AlgebraicGeometry.Space.squareZeroPullbackIso` applied
degreewise. -/
theorem squareZeroDerivedComparison_app_aux
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) ℤ) :
    (squareZeroDerivedComparison (hq := hq) hi h hip hpb hβτ).app M =
      𝟙 _ ≫ 𝟙 _ ≫ (derivedPull B S hS (hasDerivedModulePullbacks B S hS) i).map
          ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
            (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor
            (squareZeroModuleEquivalence_functor_additive (hq := hq) hi h hip hpb hβτ) _
            _).hom.app M) ≫
        𝟙 _ ≫ (derivedPullComparison B S hS i).app
          (((squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        (squareZeroComplexPullbackIso (hq := hq) hi h hip hpb hβτ).inv.app M :=
  rfl

/-- The comparison `AlgebraicGeometry.Space.squareZeroDerivedComparison` at a complex, written
out: the derived pullback of the factorization of the derived equivalence, the comparison of the
derived pullback with degreewise pullback, and `AlgebraicGeometry.Space.squareZeroPullbackIso`
applied degreewise. -/
theorem squareZeroDerivedComparison_app
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) ℤ) :
    (squareZeroDerivedComparison (hq := hq) hi h hip hpb hβτ).app M =
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) i).map
          ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
            (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor
            (squareZeroModuleEquivalence_functor_additive (hq := hq) hi h hip hpb hβτ) _
            _).hom.app M) ≫
        (derivedPullComparison B S hS i).app
          (((squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        (squareZeroComplexPullbackIso (hq := hq) hi h hip hpb hβτ).inv.app M :=
  id_comp_id_comp_comp_id_comp_eq _ _ _ (squareZeroDerivedComparison_app_aux hi h hip hpb hβτ M)

/-- **`c2` is compatible with the comparisons with complexes**: for any derived base change `T`
along the projection, at the localization of a complex `N`, the identification
`AlgebraicGeometry.Space.squareZeroDerivedPullbackIso` followed by the comparison of the derived
pullback along `i` with degreewise pullback is the comparison of `T` followed by
`AlgebraicGeometry.Space.squareZeroComplexPullbackIso`. -/
theorem squareZeroDerivedPullbackIso_hom_app_Q_comp
    (T : DerivedExtensionOfScalars.{d, u + 1} (sqZeroExtSheafAnySiteProj
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) ℤ) :
    (squareZeroDerivedPullbackIso (hq := hq) hi h hip hpb hβτ T).hom.app (DerivedCategory.Q.obj N) ≫
        (derivedPull B S hS (hasDerivedModulePullbacks B S hS) i).map
          ((@Functor.mapDerivedCategoryFactors _ _ _ _ _ _ _ _
            (squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor
            (squareZeroModuleEquivalence_functor_additive (hq := hq) hi h hip hpb hβτ) _
            _).hom.app N) ≫
        (derivedPullComparison B S hS i).app
          (((squareZeroModuleEquivalence (hq := hq) hi h hip hpb hβτ).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) =
      T.comparison.app N ≫
        (squareZeroComplexPullbackIso (hq := hq) hi h hip hpb hβτ).hom.app N := by
  have h₁ := NatTrans.congr_app (baseChangeIso_fac _ T
    (squareZeroDerivedExtensionOfScalars (hq := hq) hi h hip hpb hβτ)) N
  rw [NatTrans.comp_app, Functor.whiskerLeft_app] at h₁
  exact comp_comp_eq_comp_hom_of_comp_comp_comp_inv_eq _ _ _
    (squareZeroComplexPullbackIso (hq := hq) hi h hip hpb hβτ) _
    ((congrArg (_ ≫ ·) (squareZeroDerivedComparison_app hi h hip hpb hβτ N).symm).trans h₁)

end Retraction

section Coherence

attribute [local instance 10000] HasDerivedCategory.standard

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
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))))]

/-- The composition comparison of derived pullbacks along `X ⟶ X_W ⟶ X_V` at a complex `N`,
followed by the comparison along `X ⟶ X_V` with degreewise pullback: Stacks 0D6D read on
complexes. -/
theorem squareZero_triangle_inv_app_Q_comp_derivedPullComparison
    (N : CochainComplex (Modules.{u, u} B S hS X'V.1 X'V.2) ℤ) :
    ((smallEtaleDerivedPullbackData B S hS).triangle (rfl : iW ≫ H = iW ≫ H)).inv.app
          (DerivedCategory.Q.obj N) ≫
        (derivedPullComparison B S hS (iW ≫ H)).app N =
      (derivedPull B S hS (hasDerivedModulePullbacks B S hS) iW).map
          ((derivedPullComparison B S hS H).app N) ≫
        (derivedPullComparison B S hS iW).app
          ((((modulePullbackDataTopos B S hS).pull H).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) ≫
        (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
          ((NatTrans.mapHomologicalComplex
            ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS iW)
                (smallEtaleRingedToposHom B S hS H)).symm ≪≫
              pullbackModulesCompTransport B S hS iW H).hom (ComplexShape.up ℤ)).app N) :=
  comp_eq_of_eq_comp_id rfl
    (smallEtaleDerivedPullbackData_compIso_inv_app_Q_comp_derivedPullComparison_degreewise
      B S hS iW H N)

end Coherence

end AlgebraicGeometry.Space

end
