module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeChangeBase
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeComputesCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TensorConstantCech
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CohomologicalDimensionFiniteCover
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DerivedChangeBaseResolution
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.EtaleCoordinatesCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusSemilinearAction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorConstantModule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedBaseChangeOfSections
public import StacksFrontier.Homology.KFlat.TensorExactAbove
public import StacksFrontier.Homology.KFlat.TensorExactAboveSmall

/-!
# Base change for crystalline cohomology with `p` nilpotent and a smooth source

Let `f : S ⟶ S'` be a morphism of divided power bases with `A' = Γ(S', 𝒪)` and `A = Γ(S, 𝒪)`,
`p` nilpotent in `A'`, and `g : X ⟶ X'` with `X = X' ×_{S'₀} S₀`, `X' ⟶ S'₀` smooth. For a crystal
`N'` in finite locally free modules on `CRIS(X'/S')` the base change map
`RΓ(CRIS(X'/S'), N') ⊗^L_{A'} A ⟶ RΓ(CRIS(X/S), u^* N')`, the adjoint transpose under
`derivedBaseChangeTensorAdjunction f` of `derivedChangeBaseBigGlobalSectionsMap`, is an
isomorphism ([Stacks, Tag 07MU] in the case needed by [Stacks, Tag 07N5]).

The proof computes both sides by Čech complexes of the divided power envelopes of a finite affine
cover of `X'` with smooth lifts and of its base change to `X`, and this file is organised along
that computation.

## Main result

* `isIso_baseChange_of_isNilpotent_smooth` — the base change map is an isomorphism, for
  `S`, `S'` affine, `p` nilpotent, `X = Y ×_{S'₀} S₀` with `Y` smooth over `S'₀`, separated and
  quasi-compact, and a crystal in finite locally free modules; no dimension hypothesis.

## The algebraic reduction

`isIso_derivedBaseChangeTensorAdjunction_homEquiv_symm_of_complexes`: if a map
`φ : K' ⟶ res_* L` of `D(A')` is presented, under isomorphisms `Q(C') ≅ K'` and `Q(C) ≅ L`, by a
map of complexes `c : C' ⟶ res_* C`, if `C'` has flat terms and its termwise tensor products
`C' ⊗_{A'} M` have no cohomology above a fixed degree for every `A'`-module `M`, and if the
degreewise transpose `c♭ : C' ⊗_{A'} A ⟶ C` is a quasi-isomorphism, then the adjoint transpose of
`φ`, a map `K' ⊗^L_{A'} A ⟶ L`, is an isomorphism. The derived tensor product is computed on `C'`
termwise because `C'` is K-flat
(`...TotalDerivedExtensionScalars.comparison_isIso_of_isZero_homology_tensorComplex`),
and the transpose of `Q(c)` is that comparison followed by `Q(c♭)`
(`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_homEquiv_symm`).

## The Čech presentation

For charts `U_i` of `X` and `U'_i` of `Y` with smooth lifts, their objects `D_i`, `D'_i` of the
big crystalline sites and maps `γ i : u(D_i) ⟶ D'_i`, restriction of sections along the induced
maps `u(D_x) ⟶ D'_x` of products is a map of Čech complexes `Č(D', N) ⟶ res Č(D, u^* N)`
(`changeBaseCechMap`), and under the Čech comparisons it is the comparison
`derivedChangeBaseBigGlobalSectionsMap`
(`cechToDerived_comp_derivedChangeBaseBigGlobalSectionsMap`, from
`Stacks.CechSite.FinalCover.cechToDerivedGlobalSections_comp_derivedSquareMap_pushforward`).
With the algebraic reduction this gives `isIso_baseChange_of_cech`: the base change map is an
isomorphism once the Čech comparisons are, the terms of `Č(D', N)` are flat, its tensor products
with `A'`-modules are uniformly bounded, and the transpose of the Čech map is a
quasi-isomorphism.

## References

* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v wA wA' wB

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The base change transpose of a map presented by complexes is an isomorphism** when the
source complex is K-flat by a uniform bound on its tensor products and the degreewise transpose
is a quasi-isomorphism. Precisely: let `φ : K' ⟶ res_* L` in `D(A')`, presented under
`e : Q(C') ≅ K'` and `e' : Q(C) ≅ L` by `c : C' ⟶ res_* C`. If the terms of `C'` are flat over
`A'`, every `C' ⊗_{A'} M` has no cohomology in degrees `> m`, and the degreewise adjoint
transpose `c♭ : C' ⊗_{A'} A ⟶ C` is a quasi-isomorphism, then the adjoint transpose
`K' ⊗^L_{A'} A ⟶ L` of `φ` under `derivedBaseChangeTensorAdjunction f` is an isomorphism. -/
theorem isIso_derivedBaseChangeTensorAdjunction_homEquiv_symm_of_complexes (f : S.S ⟶ S'.S)
    {X' : DerivedCategory (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))}
    {Y' : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))}
    (φ : X' ⟶ (ModuleCat.restrictScalars (baseChangeRingHom f)).mapDerivedCategory.obj Y')
    (C' : CochainComplex (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) ℤ)
    (c : C' ⟶ ((ModuleCat.restrictScalars (baseChangeRingHom f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C)
    (e : DerivedCategory.Q.obj C' ≅ X') (e' : DerivedCategory.Q.obj C ≅ Y')
    (hφ : e.hom ≫ φ = DerivedCategory.Q.map c ≫
      (ModuleCat.restrictScalars (baseChangeRingHom f)).mapDerivedCategoryFactors.inv.app C ≫
        (ModuleCat.restrictScalars (baseChangeRingHom f)).mapDerivedCategory.map e'.hom)
    [∀ i, Module.Flat Γ(S'.S.scheme, ⊤) (C'.X i)] (m : ℤ)
    (hC' : ∀ (M : ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)) (k : ℤ), m < k →
      IsZero ((StacksDraft.TorAmplitude.tensorComplex C' M).homology k))
    (hc : QuasiIso
      ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
        (baseChangeRingHom f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv C' C).symm c)) :
    IsIso (((derivedBaseChangeTensorAdjunction f).homEquiv X' Y').symm φ) := by
  have hF : (derivedBaseChangeTensor f).IsLeftDerivedFunctor
      (derivedBaseChangeTensorBundle f).comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)) (ComplexShape.up ℤ)) :=
    (derivedBaseChangeTensorBundle f).isLeftDerived
  have h1 :=
    @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_homEquiv_symm.{u, u,
      u + 1, wA', wA} _ _ _ _ (baseChangeRingHom f) _ _ (derivedBaseChangeTensor f)
      (derivedBaseChangeTensorBundle f).comparison hF C' C c
  have hcomp : IsIso ((derivedBaseChangeTensorBundle f).comparison.app C') :=
    (derivedBaseChangeTensorBundle f).comparison_isIso_of_isZero_homology_tensorComplex C' m hC'
  have hQ : IsIso (DerivedCategory.Q.map
      ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
        (baseChangeRingHom f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv C' C).symm c)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hc
  have h2 : (derivedBaseChangeTensor f).map e.hom ≫
      ((derivedBaseChangeTensorAdjunction f).homEquiv X' Y').symm φ =
        ((derivedBaseChangeTensorBundle f).comparison.app C' ≫ DerivedCategory.Q.map
          ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
            (baseChangeRingHom f)).mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv C' C).symm
              c)) ≫ e'.hom := by
    rw [← Adjunction.homEquiv_naturality_left_symm, hφ, ← Category.assoc,
      Adjunction.homEquiv_naturality_right_symm]
    exact congrArg (· ≫ e'.hom) h1
  have : IsIso ((derivedBaseChangeTensor f).map e.hom ≫
      ((derivedBaseChangeTensorAdjunction f).homEquiv X' Y').symm φ) := by
    rw [h2]
    exact IsIso.comp_isIso' (IsIso.comp_isIso' hcomp hQ) inferInstance
  exact IsIso.of_isIso_comp_left ((derivedBaseChangeTensor f).map e.hom) _

/-- `isIso_derivedBaseChangeTensorAdjunction_homEquiv_symm_of_complexes` with the uniform bound on
`C' ⊗_{A'} M` tested only on `A'`-modules `M` in the universe of `A'`: for a complex of flat
modules the bound propagates to modules in every universe
(`CochainComplex.KFlat.isZero_homology_tensorComplex_of_small`). -/
theorem isIso_derivedBaseChangeTensorAdjunction_homEquiv_symm_of_complexes_small
    (f : S.S ⟶ S'.S)
    {X' : DerivedCategory (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))}
    {Y' : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))}
    (φ : X' ⟶ (ModuleCat.restrictScalars (baseChangeRingHom f)).mapDerivedCategory.obj Y')
    (C' : CochainComplex (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤)) ℤ)
    (C : CochainComplex (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) ℤ)
    (c : C' ⟶ ((ModuleCat.restrictScalars (baseChangeRingHom f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C)
    (e : DerivedCategory.Q.obj C' ≅ X') (e' : DerivedCategory.Q.obj C ≅ Y')
    (hφ : e.hom ≫ φ = DerivedCategory.Q.map c ≫
      (ModuleCat.restrictScalars (baseChangeRingHom f)).mapDerivedCategoryFactors.inv.app C ≫
        (ModuleCat.restrictScalars (baseChangeRingHom f)).mapDerivedCategory.map e'.hom)
    [∀ i, Module.Flat Γ(S'.S.scheme, ⊤) (C'.X i)] (m : ℤ)
    (hC' : ∀ (M : ModuleCat.{u} Γ(S'.S.scheme, ⊤)) (k : ℤ), m < k →
      IsZero ((StacksDraft.TorAmplitude.tensorComplex C' M).homology k))
    (hc : QuasiIso
      ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
        (baseChangeRingHom f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).homEquiv C' C).symm c)) :
    IsIso (((derivedBaseChangeTensorAdjunction f).homEquiv X' Y').symm φ) :=
  isIso_derivedBaseChangeTensorAdjunction_homEquiv_symm_of_complexes f φ C' C c e e' hφ m
    (fun M k hk ↦ CochainComplex.KFlat.isZero_homology_tensorComplex_of_small C' m hC' M k hk) hc

end Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### From the bounded below to the unbounded derived category -/

namespace CategoryTheory.Functor

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
  {ℬ : Type*} [Category* ℬ] [Abelian ℬ] [HasDerivedCategory ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **A map of complexes `c : K ⟶ F(L)` read through the homotopy category**, for an exact
functor `F`: the class `Q(c) ≫ (F(Q L) ≅ Q(F L))⁻¹` in `D(ℬ)` is the zigzag through
`DerivedCategory.Qh`. -/
theorem quotientCompQhIso_inv_app_comp_Qh_map_comp_mapDerivedCategory_map
    {K : CochainComplex ℬ ℤ} {L : CochainComplex 𝒜 ℤ}
    (c : K ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :
    (DerivedCategory.quotientCompQhIso ℬ).inv.app K ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map c) ≫
      F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj L) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜).hom.app L) =
    DerivedCategory.Q.map c ≫ F.mapDerivedCategoryFactors.inv.app L := by
  have h := F.mapDerivedCategoryFactorsh_hom_app L
  have e6 : DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app L) =
      𝟙 _ := DerivedCategory.Qh.map_id _
  have h2 : F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj L) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜).hom.app L) ≫
        F.mapDerivedCategoryFactors.hom.app L ≫
        (DerivedCategory.quotientCompQhIso ℬ).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
    rw [h]
    refine congrArg (fun t ↦ _ ≫ _ ≫ t) ?_
    exact (congrArg (fun t ↦ _ ≫ t) e6).trans (Category.comp_id _)
  have h' : F.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ _).obj L) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜).hom.app L) =
      (DerivedCategory.quotientCompQhIso ℬ).hom.app _ ≫
        F.mapDerivedCategoryFactors.inv.app L := by
    refine (Iso.inv_comp_eq (F.mapDerivedCategoryFactorsh.app _)).2 ?_
    rw [Iso.app_hom, h2]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    have h3 : F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜).hom.app L) =
        F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso 𝒜).hom.app L) ≫
          (F.mapDerivedCategoryFactors.hom.app L ≫
          (DerivedCategory.quotientCompQhIso ℬ).inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) ≫
          (DerivedCategory.quotientCompQhIso ℬ).hom.app _ ≫
          F.mapDerivedCategoryFactors.inv.app L := by
      simp
    exact h3
  refine (congrArg (fun t ↦ _ ≫ _ ≫ t) h').trans ?_
  have hn := DerivedCategory.quotientCompQhIso_hom_naturality c
  refine (congrArg (fun t ↦ _ ≫ t)
    ((reassoc_of% hn) (F.mapDerivedCategoryFactors.inv.app L))).trans ?_
  exact Iso.inv_hom_id_app_assoc _ _ _

/-- **The unbounded image of a map of `D⁺` presented by a map of complexes through the homotopy
category.** For an exact functor `F`, bounded below complexes `K`, `L`, a map of complexes
`c : K ⟶ F(L)` and `E : Q(L) ⟶ Y` in `D⁺(𝒜)`, the image in `D(ℬ)` of
`Q(K) ≅ Qh(K) ⟶ Qh(F L) ≅ F(Qh L) ≅ F(Q L) ⟶ F(Y)` is `Q(c) ≫ (F(Q L) ≅ Q(F L))⁻¹ ≫ F(E)`. -/
theorem ι_map_qhQIso_inv_comp_Qh_map_comp_mapDerivedCategoryPlus_map
    {K : CochainComplex.Plus ℬ} {L : CochainComplex.Plus 𝒜}
    (c : K.obj ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
    {Y : DerivedCategory.Plus 𝒜} (E : DerivedCategory.Plus.Q.obj L ⟶ Y) :
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.qhQIso K).inv ≫
      DerivedCategory.Plus.Qh.map (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map c) :
        (HomotopyCategory.Plus.quotient ℬ).obj K ⟶
          F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient 𝒜).obj L)) ≫
      F.mapDerivedCategoryPlusFactorsh.inv.app _ ≫
      F.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.qhQIso L).hom ≫ E)) =
    DerivedCategory.Q.map c ≫ F.mapDerivedCategoryFactors.inv.app L.obj ≫
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map E) := by
  rw [Functor.map_comp F.mapDerivedCategoryPlus, ← Category.assoc, ← Category.assoc,
    ← Category.assoc, Functor.map_comp, Category.assoc, Category.assoc]
  rw [show DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.qhQIso K).inv ≫
      DerivedCategory.Plus.Qh.map (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map c) :
        (HomotopyCategory.Plus.quotient ℬ).obj K ⟶
          F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient 𝒜).obj L)) ≫
      F.mapDerivedCategoryPlusFactorsh.inv.app _ ≫
      F.mapDerivedCategoryPlus.map (DerivedCategory.Plus.qhQIso L).hom) =
        DerivedCategory.Q.map c ≫ F.mapDerivedCategoryFactors.inv.app L.obj from
    quotientCompQhIso_inv_app_comp_Qh_map_comp_mapDerivedCategory_map F c]
  exact Category.assoc _ _ _

end CategoryTheory.Functor

/-! ### The Čech presentation of the comparison -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CechEnvelope Stacks.CechSite.FinalCover

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' : GlobalCrystallineSituation.{u}}

/-- The base ring maps are compatible with change of divided power base on the sections of the
structure sheaves: the ring map `A' ⟶ Γ(CRIS(Y/S'), 𝒪)` read at the image of an object of
`CRIS(X/S)` is `A' ⟶ A ⟶ Γ(CRIS(X/S), 𝒪)` read at that object. -/
theorem changeBaseStructureHom_app_bigBaseRingHom (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (a : Γ(S'.S.scheme, ⊤)) (V : (Thickening S)ᵒᵖ) :
    ((changeBaseStructureHom S S' f g h).hom.app V).hom
      ((bigBaseRingHom S (baseChangeRingHom f a)).1 V) =
      (bigBaseRingHom S' a).1 (op ((changeBase S S' f g h).obj V.unop)) :=
  (congrArg (fun r ↦ (r a).1 V)
    (changeBaseSectionRingHom_comp_bigBaseRingHom (S := S) (S' := S') (f := f) (g := g)
      (h := h))).symm

/-- The pullback along change of divided power base is exact, as a pushforward of sheaves of
modules: its finite colimits. -/
instance preservesFiniteColimits_pushforward_changeBaseStructureHom (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    PreservesFiniteColimits (SheafOfModules.pushforward.{u + 1}
      (changeBaseStructureHom S S' f g h)) :=
  inferInstanceAs (PreservesFiniteColimits (changeBaseBigModulePullback S S' f g h))

/-- The pullback along change of divided power base, as a pushforward of sheaves of modules,
preserves finite limits. -/
instance preservesFiniteLimits_pushforward_changeBaseStructureHom (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    PreservesFiniteLimits (SheafOfModules.pushforward.{u + 1}
      (changeBaseStructureHom S S' f g h)) :=
  inferInstanceAs (PreservesFiniteLimits (changeBaseBigModulePullback S S' f g h))

/-- The pullback along change of divided power base, as a pushforward of sheaves of modules, is
additive. -/
instance additive_pushforward_changeBaseStructureHom (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    (SheafOfModules.pushforward.{u + 1} (changeBaseStructureHom S S' f g h)).Additive :=
  inferInstanceAs ((changeBaseBigModulePullback S S' f g h).Additive)

variable [IsAffine S.S.scheme] [IsAffine S'.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (hp' : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)))
  [S.X.IsSeparated] [S'.X.IsSeparated] {ι : Type}
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)] (hU : ∀ x, ∃ i, x ∈ U i)
  (L : ∀ i, SmoothLift S (U i).ι)
  {U' : ι → S'.X.Opens} [∀ i, IsAffine (U' i)] (hU' : ∀ x, ∃ i, x ∈ U' i)
  (L' : ∀ i, SmoothLift S' (U' i).ι)
  (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  (γ : ∀ i, (changeBase S S' f g h).obj (cechObjects hp L i) ⟶ cechObjects hp' L' i)

/-- **The map of Čech complexes along change of divided power base**,
`Č(D', N) ⟶ res Č(D, u^* N)` in integer degrees, for maps `γ i : u(D_i) ⟶ D'_i` from the
smooth-lift objects of `CRIS(X/S)` to those of `CRIS(Y/S')`: on the factor of a tuple `x` it is
restriction of sections along `u(D_x) ⟶ D'_x`. -/
abbrev changeBaseCechMap (N : BigModuleSheaf S') :
    (cechIntFunctor (crystallineStructureSheaf S') (bigBaseRingHom S') (cechObjects hp' L')).obj N ⟶
      ((ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        ((cechIntFunctor (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)).obj
          ((changeBaseBigModulePullback S S' f g h).obj N)) :=
  (cechIntMap (crystallineStructureSheaf S') (bigBaseRingHom S') (cechObjects hp' L')
    (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)
    (SheafOfModules.pushforward.{u + 1} (changeBaseStructureHom S S' f g h))
    (baseChangeRingHom f)
    (pushforwardCechMap (crystallineStructureSheaf S') (bigBaseRingHom S') (cechObjects hp' L')
      (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)
      (changeBase S S' f g h) (changeBaseStructureHom S S' f g h) (baseChangeRingHom f)
      (τ := id) γ (changeBaseStructureHom_app_bigBaseRingHom f g h))).app N

variable [HasDerivedCategory.{wB} (BigModuleSheaf S)] [HasDerivedCategory.{wB} (BigModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The comparison along change of divided power base is the Čech map.** Let `D_i` and `D'_i`
be the smooth-lift objects of charts of `X` and `Y` and `γ i : u(D_i) ⟶ D'_i`. Under the Čech
comparisons `Č(D', N) ⟶ RΓ(CRIS(Y/S'), N)` and `Č(D, u^* N) ⟶ RΓ(CRIS(X/S), u^* N)`, read in
the unbounded derived categories, `derivedChangeBaseBigGlobalSectionsMap f g h N` is the class of
the Čech map `changeBaseCechMap`. -/
theorem cechToDerived_comp_derivedChangeBaseBigGlobalSectionsMap (N : BigModuleSheaf S') :
    DerivedCategory.Plus.ι.map ((cechToDerivedGlobalSections (crystallineStructureSheaf S')
      (bigBaseRingHom S') (cechObjects hp' L') (coversTop_object hp' U' hU' L')).app N) ≫
      DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap f g h N) =
    DerivedCategory.Q.map (changeBaseCechMap hp hp' L L' f g h γ N) ≫
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryFactors.inv.app
        _ ≫
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map ((cechToDerivedGlobalSections (crystallineStructureSheaf S)
          (bigBaseRingHom S) (cechObjects hp L) (coversTop_object hp U hU L)).app
            ((changeBaseBigModulePullback S S' f g h).obj N))) := by
  have key := cechToDerivedGlobalSections_comp_derivedSquareMap_pushforward
    (crystallineStructureSheaf S') (bigBaseRingHom S') (cechObjects hp' L')
    (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)
    (changeBase S S' f g h) (changeBaseStructureHom S S' f g h) (baseChangeRingHom f) (τ := id) γ
    (changeBaseStructureHom_app_bigBaseRingHom f g h) (coversTop_object hp' U' hU' L')
    (coversTop_object hp U hU L) (changeBaseBigBaseGlobalSectionsTrans f g h)
    (fun _ _ _ ↦ rfl) N
  refine ((Functor.map_comp _ _ _).symm.trans
    (congrArg DerivedCategory.Plus.ι.map (Eq.trans ?_ key))).trans ?_
  · exact congrArg _ (derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap f g h N)
  exact Functor.ι_map_qhQIso_inv_comp_Qh_map_comp_mapDerivedCategoryPlus_map
    (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f))
    (K := (cechPlusFunctor (crystallineStructureSheaf S') (bigBaseRingHom S')
      (cechObjects hp' L')).obj N)
    (L := (cechPlusFunctor (crystallineStructureSheaf S) (bigBaseRingHom S)
      (cechObjects hp L)).obj
        ((SheafOfModules.pushforward.{u + 1} (changeBaseStructureHom S S' f g h)).obj N))
    (changeBaseCechMap hp hp' L L' f g h γ N)
    ((cechToDerivedGlobalSections (crystallineStructureSheaf S)
      (bigBaseRingHom S) (cechObjects hp L) (coversTop_object hp U hU L)).app
        ((changeBaseBigModulePullback S S' f g h).obj N))

/-- **The base change map is an isomorphism as soon as its Čech map is a good presentation.**
In the situation of `cechToDerived_comp_derivedChangeBaseBigGlobalSectionsMap`, suppose that
both Čech comparisons are isomorphisms, that the terms of `Č(D', N)` are flat over `A'`, that
`Č(D', N) ⊗_{A'} M` has no cohomology above `m` for every `A'`-module `M`, and that the degreewise
adjoint transpose `Č(D', N) ⊗_{A'} A ⟶ Č(D, u^* N)` of the Čech map is a quasi-isomorphism. Then
the base change map `RΓ(CRIS(Y/S'), N) ⊗^L_{A'} A ⟶ RΓ(CRIS(X/S), u^* N)` is an isomorphism. -/
theorem isIso_baseChange_of_cech (N : BigModuleSheaf S')
    [IsIso ((cechToDerivedGlobalSections (crystallineStructureSheaf S')
      (bigBaseRingHom S') (cechObjects hp' L') (coversTop_object hp' U' hU' L')).app N)]
    [IsIso ((cechToDerivedGlobalSections (crystallineStructureSheaf S)
      (bigBaseRingHom S) (cechObjects hp L) (coversTop_object hp U hU L)).app
        ((changeBaseBigModulePullback S S' f g h).obj N))]
    [∀ i, Module.Flat Γ(S'.S.scheme, ⊤) (((cechIntFunctor (crystallineStructureSheaf S')
      (bigBaseRingHom S') (cechObjects hp' L')).obj N).X i)] (m : ℤ)
    (hbound : ∀ (M : ModuleCat.{u} Γ(S'.S.scheme, ⊤)) (k : ℤ), m < k →
      IsZero ((StacksDraft.TorAmplitude.tensorComplex ((cechIntFunctor
        (crystallineStructureSheaf S') (bigBaseRingHom S') (cechObjects hp' L')).obj N)
          M).homology k))
    (hc : QuasiIso
      ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
        (baseChangeRingHom f)).mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _).symm
          (changeBaseCechMap hp hp' L L' f g h γ N))) :
    IsIso (((derivedBaseChangeTensorAdjunction f).homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map (derivedChangeBaseBigGlobalSectionsMap f g h N))) :=
  isIso_derivedBaseChangeTensorAdjunction_homEquiv_symm_of_complexes_small f _ _ _
    (changeBaseCechMap hp hp' L L' f g h γ N)
    (DerivedCategory.Plus.ι.mapIso (asIso ((cechToDerivedGlobalSections
      (crystallineStructureSheaf S') (bigBaseRingHom S') (cechObjects hp' L')
        (coversTop_object hp' U' hU' L')).app N)))
    (DerivedCategory.Plus.ι.mapIso (asIso ((cechToDerivedGlobalSections
      (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)
        (coversTop_object hp U hU L)).app ((changeBaseBigModulePullback S S' f g h).obj N))))
    (cechToDerived_comp_derivedChangeBaseBigGlobalSectionsMap hp hp' hU L hU' L' f g h γ N) m
    hbound hc

end Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The uniform bound -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CechEnvelope Stacks.CechSite.FinalCover

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated]

/-- The products `D_x` of the smooth-lift objects have affine ambient schemes: `D_x` is the
divided power envelope object, whose ambient scheme is the spectrum of the envelope. -/
theorem isAffine_inter_cechObjects_target {ι : Type} {U : ι → S.X.Opens} [∀ i, IsAffine (U i)]
    (L : ∀ i, SmoothLift S (U i).ι) (k : ℕ) (x : Fin (k + 1) → ι) :
    IsAffine (inter (cechObjects hp L) x).thickening.target.scheme := by
  let e := interIsoEnvelopeObject hp L x
  let φ : (inter (cechObjects hp L) x).thickening.target.scheme ≅
      (envelopeObject hp (fun a ↦ L (x a))).thickening.target.scheme :=
    { hom := e.hom.targetHom.hom
      inv := e.inv.targetHom.hom
      hom_inv_id := by
        have := congrArg (fun k ↦ k.targetHom.hom) e.hom_inv_id
        simpa only [Thickening.comp_targetHom, DividedPowerScheme.Hom.comp_hom,
          Thickening.id_targetHom, DividedPowerScheme.Hom.id_hom] using this
      inv_hom_id := by
        have := congrArg (fun k ↦ k.targetHom.hom) e.inv_hom_id
        simpa only [Thickening.comp_targetHom, DividedPowerScheme.Hom.comp_hom,
          Thickening.id_targetHom, DividedPowerScheme.Hom.id_hom] using this }
  exact @IsAffine.of_isIso _ _ φ.hom (Iso.isIso_hom φ) inferInstance

/-- The intersection of the opens indexed by a finset, read through its enumeration. -/
theorem iInf_orderIsoOfFin {n : ℕ} (U : Fin n → S.X.Opens) (s : Finset (Fin n)) {k : ℕ}
    (hk : s.card = k) : (⨅ a, U (s.orderIsoOfFin hk a)) = ⨅ i ∈ s, U i := by
  refine le_antisymm (le_iInf₂ fun i hi ↦ ?_) (le_iInf fun a ↦ iInf₂_le _ (s.orderIsoOfFin hk a).2)
  simpa using iInf_le (fun a ↦ U (s.orderIsoOfFin hk a)) ((s.orderIsoOfFin hk).symm ⟨i, hi⟩)

include hp in
/-- **The hypothesis of the finite-cover vanishing on the intersections of charts with étale
coordinates**: for affine opens `U_i` of a separated `X`, each carrying a smooth lift with étale
coordinates, every nonempty finite intersection `⋂_{i ∈ s} U_i` has, for some `d`, crystalline
cohomology vanishing above `d` for every crystal in quasi-coherent modules. -/
theorem exists_subsingleton_cohomology_iInf {n : ℕ} {U : Fin n → S.X.Opens}
    [∀ i, IsAffine (U i)]
    (hL : ∀ i, ∃ (L : SmoothLift S (U i).ι) (d : ℕ) (t : Fin d → L.ring),
      (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale)
    (s : Finset (Fin n)) (hs : s.Nonempty) :
    ∃ d : ℕ, ∀ Fc : QuasiCoherentCrystal S,
      ∃ (W : S.S.scheme.Opens) (hVW : (⨅ i ∈ s, U i) ≤ sourceToBase S ⁻¹ᵁ W), ∀ j : ℕ, d < j →
        Subsingleton (cohomology (restrict S W (⨅ i ∈ s, U i) hVW)
          ((smallExtendAbelianRestriction S W (⨅ i ∈ s, U i) hVW).obj
            (abelianSheaf Fc.obj)) j) := by
  obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, by have := hs.card_pos; omega⟩
  let V : Fin (k + 1) → S.X.Opens := fun a ↦ U (s.orderIsoOfFin hk a)
  obtain ⟨L', d, t, ht⟩ := exists_smoothLift_etaleCoordinates_inter_of_forall V
    (fun a ↦ hL (s.orderIsoOfFin hk a))
  have hV : CechEnvelope.inter V = ⨅ i ∈ s, U i := iInf_orderIsoOfFin U s hk
  refine ⟨d, fun Fc ↦ ?_⟩
  have h := exists_restrict_subsingleton_cohomology_of_smoothLift hp (CechEnvelope.inter V)
    (inferInstance : IsAffine (CechEnvelope.inter V).toScheme) L' t ht Fc
  rwa [hV] at h

include hp in
/-- **The uniform bound on the tensor products of the Čech complex.** For a finite cover of a
separated `X` by affine opens `U_i`, each carrying a smooth lift with étale coordinates, and smooth
lifts `L_i` of the `U_i`, there is an `m` such that for every quasi-coherent `𝒪_{X/S}`-module `N`
and every `A`-module `M`, `Č(D, N) ⊗_A M` has no cohomology in degrees `> m`. Indeed
`Č(D, N) ⊗_A M = Č(D, N ⊗_A M)` (`...TensorConstant.cechTensorConstantModuleIso`) computes
`H^*(CRIS(X/S), N ⊗_A M) = H^*(Cris(X/S), N ⊗_A M)` (`...CechEnvelope.cechEnvelopeDerivedIso`),
which vanishes in degrees `≥ d + n` by the finite-cover vanishing
(`isZero_homology_moduleULiftDerivedGlobalSections_of_finiteCover`) and the vanishing above `d` on
the intersections. No Krull dimension enters. -/
theorem exists_isZero_homology_tensorComplex_cech {n : ℕ} {U : Fin n → S.X.Opens}
    [∀ i, IsAffine (U i)] (hU : ∀ x, ∃ i, x ∈ U i) (L : ∀ i, SmoothLift S (U i).ι)
    (hL : ∀ i, ∃ (L : SmoothLift S (U i).ι) (d : ℕ) (t : Fin d → L.ring),
      (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    ∃ m : ℤ, ∀ (N : SheafOfModules.{u} (crystallineStructureSheaf S)) [N.IsQuasicoherentOnSite]
      (M : ModuleCat.{u} Γ(S.S.scheme, ⊤)) (k : ℤ), m < k →
      IsZero ((StacksDraft.TorAmplitude.tensorComplex ((cechIntFunctor
        (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)).obj
          ((bigModuleULift S).obj N)) M).homology k) := by
  classical
  have hex : ∀ s : Finset (Fin n), ∃ d : ℕ, s.Nonempty → ∀ Fc : QuasiCoherentCrystal S,
      ∃ (W : S.S.scheme.Opens) (hVW : (⨅ i ∈ s, U i) ≤ sourceToBase S ⁻¹ᵁ W), ∀ j : ℕ, d < j →
        Subsingleton (cohomology (restrict S W (⨅ i ∈ s, U i) hVW)
          ((smallExtendAbelianRestriction S W (⨅ i ∈ s, U i) hVW).obj
            (abelianSheaf Fc.obj)) j) := fun s ↦ by
    by_cases hs : s.Nonempty
    · obtain ⟨d, hd⟩ := exists_subsingleton_cohomology_iInf hp hL s hs
      exact ⟨d, fun _ ↦ hd⟩
    · exact ⟨0, fun h ↦ (hs h).elim⟩
  choose d hd using hex
  let D : ℕ := Finset.univ.sup d
  refine ⟨(D : ℤ) + n - 1, fun N _ M k hk ↦ ?_⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, k = q := ⟨k.toNat, by omega⟩
  let := HasDerivedCategory.standard (BigModuleSheaf S)
  let := HasDerivedCategory.standard (ModuleSheaf S)
  let := HasDerivedCategory.standard (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))
  let NM := tensorConstantModule N M
  have hcov : ⨆ i, U i = ⊤ := eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 (hU x)
  have hH2 := isZero_homology_moduleULiftDerivedGlobalSections_of_finiteCover S
    (restrictSheafOfModules NM) D n U hcov (fun s hs ↦ by
      obtain ⟨W, hVW, h⟩ := hd s hs ⟨restrictSheafOfModules NM,
        isQuasiCoherentCrystal_restrictSheafOfModules inferInstance⟩
      exact ⟨W, hVW, fun j hj ↦ h j (lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ s)) hj)⟩)
    (q : ℤ) (by omega)
  refine IsZero.of_iso hH2 ?_
  exact HomologicalComplex.homologyMapIso (Stacks.DerivedIndexing.mapExtendIso
      (StacksDraft.TorAmplitude.tensorRightMixed M) ComplexShape.embeddingUpNat _).symm q ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f q) ≪≫
    (TensorConstant.cechTensorConstantModuleHomologyIso N M (cechObjects hp L)
      (isAffine_inter_cechObjects_target hp L) q).symm ≪≫
    cechEnvelopeComplexHomologyIso hp hU L NM inferInstance q ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      (derivedRestrictModuleGlobalSectionsULiftIso S NM)

end Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The transpose of the Čech map, flatness, and the assembly -/

namespace ModuleCat

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] (ρ : R →+* S)

/-- **The transpose of a map into a restriction of scalars of a finite product.** Let
`φ : X ⟶ res W` with `X = ∏_k Y_k` and `W = ∏_k Z_k` finite products, whose components are
`π_k ≫ θ_k` for maps `θ_k : Y_k ⟶ res Z_k`. If every transpose `S ⊗_R Y_k ⟶ Z_k` of a `θ_k` is
an isomorphism, so is the transpose `S ⊗_R X ⟶ W` of `φ`: extension of scalars preserves finite
products. -/
theorem isIso_homEquiv_symm_of_isLimit {κ : Type} [Finite κ] {Y : κ → ModuleCat.{max v u} R}
    {Z : κ → ModuleCat.{max v u} S} {X : ModuleCat.{max v u} R} {πX : ∀ k, X ⟶ Y k}
    (hX : IsLimit (Fan.mk X πX)) {W : ModuleCat.{max v u} S} {πW : ∀ k, W ⟶ Z k}
    (hW : IsLimit (Fan.mk W πW)) (φ : X ⟶ (restrictScalars.{max v u} ρ).obj W)
    (θ : ∀ k, Y k ⟶ (restrictScalars.{max v u} ρ).obj (Z k))
    (hφ : ∀ k, φ ≫ (restrictScalars.{max v u} ρ).map (πW k) = πX k ≫ θ k)
    (hθ : ∀ k, IsIso (((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm (θ k))) :
    IsIso (((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm φ) := by
  have : Fintype κ := Fintype.ofFinite κ
  let E := extendScalars.{u, u, max v u} ρ
  have hE : IsLimit (Fan.mk (E.obj X) fun k ↦ E.map (πX k)) :=
    (isLimitMapConeFanMkEquiv E Y πX).1 (isLimitOfPreserves E hX)
  let e := hE.conePointsIsoOfNatIso hW (Discrete.natIso fun k ↦
    @asIso _ _ _ _ (((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm (θ k.as))
      (hθ k.as))
  have he : e.hom = ((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm φ := by
    refine Fan.IsLimit.hom_ext hW _ _ fun k ↦ ?_
    refine (IsLimit.conePointsIsoOfNatIso_hom_comp hE hW _ ⟨k⟩).trans ?_
    show E.map (πX k) ≫ ((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm (θ k) = _
    rw [← Adjunction.homEquiv_naturality_left_symm, ← hφ k,
      Adjunction.homEquiv_naturality_right_symm]
    rfl
  rw [← he]
  infer_instance

/-- The transpose of `a ≫ b ≫ res(c)` for isomorphisms `a`, `c` is an isomorphism when that of
`b` is. -/
theorem isIso_homEquiv_symm_comp {X X' : ModuleCat.{max v u} R} {Y Y' : ModuleCat.{max v u} S}
    (a : X ⟶ X') [ha : IsIso a] (b : X' ⟶ (restrictScalars.{max v u} ρ).obj Y') (c : Y' ⟶ Y)
    [hc : IsIso c] (hb : IsIso (((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm b)) :
    IsIso (((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm
      (a ≫ b ≫ (restrictScalars.{max v u} ρ).map c)) := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm]
  infer_instance

end ModuleCat

namespace Module.Flat

/-- A subsingleton module is flat, as a retract of the ring. -/
theorem of_subsingleton' (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Subsingleton M] : Module.Flat R M :=
  Module.Flat.of_retract (M := R) 0 0 (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)

/-- A finite product of flat modules is flat. -/
theorem pi_of_finite (R : Type*) [CommRing R] {κ : Type*} [Finite κ] (M : κ → Type*)
    [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)] [∀ k, Module.Flat R (M k)] :
    Module.Flat R (∀ k, M k) := by
  have : Fintype κ := Fintype.ofFinite κ
  classical
  exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R) (M := M)).symm

end Module.Flat

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CechEnvelope Stacks.CechSite.FinalCover AlgebraicGeometry

variable {S S' : GlobalCrystallineSituation.{u}}
  [IsAffine S.S.scheme] [IsAffine S'.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (hp' : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)))
  [S.X.IsSeparated] [S'.X.IsSeparated] {ι : Type}
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)]
  (L : ∀ i, SmoothLift S (U i).ι)
  {U' : ι → S'.X.Opens} [∀ i, IsAffine (U' i)]
  (L' : ∀ i, SmoothLift S' (U' i).ι)
  (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  (γ : ∀ i, (changeBase S S' f g h).obj (cechObjects hp L i) ⟶ cechObjects hp' L' i)

/-- The component of the Čech map at a tuple `x`: restriction of sections of `N` along
`u(D_x) ⟶ D'_x`. -/
abbrev changeBaseCechComponent (N : BigModuleSheaf S') {n : ℕ} (x : Fin (n + 1) → ι) :
    ((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S')
      (bigBaseRingHom S')).obj N).obj
        (Opposite.op (inter (cechObjects hp' L') x)) ⟶
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).obj
        (((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S) (bigBaseRingHom S)).obj
          ((changeBaseBigModulePullback S S' f g h).obj N)).obj
            (Opposite.op (inter (cechObjects hp L) x))) :=
  ((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S') (bigBaseRingHom S')).obj N).map
      (cechLiftMap (cechObjects hp' L') (cechObjects hp L) (changeBase S S' f g h) (τ := id) γ
        x).op ≫
    pushforwardSectionsHom.{0, u, u + 1, u, u, u} (crystallineStructureSheaf S') (bigBaseRingHom S')
      (crystallineStructureSheaf S) (bigBaseRingHom S) (changeBase S S' f g h)
      (changeBaseStructureHom S S' f g h) (baseChangeRingHom f)
      (changeBaseStructureHom_app_bigBaseRingHom f g h) N (inter (cechObjects hp L) x)

/-- **The transpose of the Čech map is a quasi-isomorphism when it is one tuple by tuple**: for
`ι` finite, if for every tuple `x` the transpose `A ⊗_{A'} N(D'_x) ⟶ N(u D_x)` of the restriction
of sections along `u(D_x) ⟶ D'_x` is an isomorphism, then the degreewise transpose
`Č(D', N) ⊗_{A'} A ⟶ Č(D, u^* N)` of `changeBaseCechMap` is an isomorphism of complexes, hence a
quasi-isomorphism. -/
theorem quasiIso_transpose_changeBaseCechMap [Finite ι] (N : BigModuleSheaf S')
    (hθ : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsIso
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} (baseChangeRingHom f)).homEquiv _ _).symm
        (changeBaseCechComponent hp hp' L L' f g h γ N x))) :
    QuasiIso
      ((((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
        (baseChangeRingHom f)).mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _).symm
          (changeBaseCechMap hp hp' L L' f g h γ N)) := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} (baseChangeRingHom f)
  let res := ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)
  let c₀ := pushforwardCechMap (crystallineStructureSheaf S') (bigBaseRingHom S')
      (cechObjects hp' L') (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)
      (changeBase S S' f g h) (changeBaseStructureHom S S' f g h) (baseChangeRingHom f)
      (τ := id) γ (changeBaseStructureHom_app_bigBaseRingHom f g h)
  let K' := (cechFunctor (crystallineStructureSheaf S') (bigBaseRingHom S')
    (cechObjects hp' L')).obj N
  let K := (cechFunctor (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)).obj
    ((changeBaseBigModulePullback S S' f g h).obj N)
  have hiso : ∀ i : ℤ, IsIso ((adj.homEquiv _ _).symm
      ((changeBaseCechMap hp hp' L L' f g h γ N).f i)) := by
    intro i
    rcases i with q | q
    · have h0 : ComplexShape.embeddingUpNat.f q = Int.ofNat q := rfl
      have hcq : (changeBaseCechMap hp hp' L L' f g h γ N).f (Int.ofNat q) =
          (K'.extendXIso ComplexShape.embeddingUpNat h0).hom ≫ (c₀.app N).f q ≫
            res.map (K.extendXIso ComplexShape.embeddingUpNat h0).inv := by
        dsimp only [changeBaseCechMap, cechIntMap]
        rw [NatTrans.comp_app, HomologicalComplex.comp_f, Functor.whiskerRight_app,
          Functor.whiskerLeft_app, ComplexShape.Embedding.extendFunctor_map,
          HomologicalComplex.extendMap_f (c₀.app N) ComplexShape.embeddingUpNat h0]
        exact (Category.assoc _ _ _).trans (congrArg _ ((Category.assoc _ _ _).trans
          (congrArg _ (Stacks.DerivedIndexing.extendXIso_inv_comp_mapExtendIso_hom_f res
            ComplexShape.embeddingUpNat K h0))))
      rw [hcq]
      refine ModuleCat.isIso_homEquiv_symm_comp (baseChangeRingHom f) _ _ _
        (ha := Iso.isIso_hom _) (hc := Iso.isIso_inv _) ?_
      exact ModuleCat.isIso_homEquiv_symm_of_isLimit (baseChangeRingHom f)
          (isLimitFan (cechObjects hp' L') _ q) (isLimitFan (cechObjects hp L) _ q) _
          (fun x ↦ changeBaseCechComponent hp hp' L L' f g h γ N x)
          (fun x ↦ pushforwardCechMapF_comp (crystallineStructureSheaf S') (bigBaseRingHom S')
            (cechObjects hp' L') (crystallineStructureSheaf S) (bigBaseRingHom S)
            (cechObjects hp L) (changeBase S S' f g h) (changeBaseStructureHom S S' f g h)
            (baseChangeRingHom f) (τ := id) γ (changeBaseStructureHom_app_bigBaseRingHom f g h)
            N q x)
          (fun x ↦ hθ q x)
    · exact ⟨⟨0, ((ModuleCat.extendScalars.{u, u, u + 1} (baseChangeRingHom f)).map_isZero
        (isZero_cechIntFunctor_X (crystallineStructureSheaf S') (bigBaseRingHom S')
          (cechObjects hp' L') N _ (Int.negSucc_lt_zero q))).eq_of_src _ _,
        (isZero_cechIntFunctor_X (crystallineStructureSheaf S) (bigBaseRingHom S)
          (cechObjects hp L) _ _ (Int.negSucc_lt_zero q)).eq_of_src _ _⟩⟩
  have : ∀ i, IsIso ((((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _).symm
      (changeBaseCechMap hp hp' L L' f g h γ N)).f i) := hiso
  have := HomologicalComplex.Hom.isIso_of_components
    (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv _ _).symm
      (changeBaseCechMap hp hp' L L' f g h γ N))
  infer_instance

omit [IsAffine S.S.scheme] [S.X.IsSeparated] [∀ i, IsAffine (U i)] in
/-- **The terms of the Čech complex are flat** when the sections over the products `D'_x` are:
they are finite products of these. -/
theorem flat_cechIntFunctor_X [Finite ι] (N : BigModuleSheaf S')
    (hflat : ∀ (n : ℕ) (x : Fin (n + 1) → ι), Module.Flat Γ(S'.S.scheme, ⊤)
      (((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S')
        (bigBaseRingHom S')).obj N).obj (Opposite.op (inter (cechObjects hp' L') x))))
    (i : ℤ) : Module.Flat Γ(S'.S.scheme, ⊤) (((cechIntFunctor (crystallineStructureSheaf S')
      (bigBaseRingHom S') (cechObjects hp' L')).obj N).X i) := by
  rcases i with q | q
  · have h0 : ComplexShape.embeddingUpNat.f q = Int.ofNat q := rfl
    let K' := (cechFunctor (crystallineStructureSheaf S') (bigBaseRingHom S')
      (cechObjects hp' L')).obj N
    let Z : (Fin (q + 1) → ι) → ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤) := fun x ↦
      ((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S')
        (bigBaseRingHom S')).obj N).obj (Opposite.op (inter (cechObjects hp' L') x))
    let e := K'.extendXIso ComplexShape.embeddingUpNat h0 ≪≫
      (isLimitFan (cechObjects hp' L') _ q).conePointUniqueUpToIso
        (ModuleCat.productConeIsLimit Z)
    have : ∀ x, Module.Flat Γ(S'.S.scheme, ⊤) (Z x) := fun x ↦ hflat q x
    have : Module.Flat Γ(S'.S.scheme, ⊤) (ModuleCat.productCone Z).pt :=
      Module.Flat.pi_of_finite Γ(S'.S.scheme, ⊤) (fun x ↦ Z x)
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  · have hs : IsZero (((cechIntFunctor (crystallineStructureSheaf S') (bigBaseRingHom S')
        (cechObjects hp' L')).obj N).X (Int.negSucc q)) :=
      isZero_cechIntFunctor_X _ _ _ N _ (Int.negSucc_lt_zero q)
    have := ModuleCat.subsingleton_of_isZero hs
    exact Module.Flat.of_subsingleton' _ _

end Crystalline.GlobalCrystallineSituation.SmallSite

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open AlgebraicGeometry

/-- **Finitely many affine open charts with smooth lifts carrying étale coordinates, indexed by
`Fin n`**, for `X` quasi-compact and smooth over `S₀`. -/
theorem exists_fin_opens_smoothLift_etaleCoordinates (S : GlobalCrystallineSituation.{u})
    [IsAffine S.S.scheme] [CompactSpace S.X] (hsm : Smooth S.toClosedFiber) :
    ∃ (n : ℕ) (U : Fin n → S.X.Opens), (∀ i, IsAffine (U i)) ∧ (∀ x, ∃ i, x ∈ U i) ∧
      ∀ i, ∃ (L : SmoothLift S (U i).ι) (d : ℕ) (t : Fin d → L.ring),
        (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale := by
  obtain ⟨ι, _, V, j, hj, hV, hcov, hL⟩ := exists_finite_smoothLift_etaleCoordinates S hsm
  let e := Finite.equivFin ι
  refine ⟨Nat.card ι, fun i ↦ (j (e.symm i)).opensRange, fun i ↦ ?_, fun x ↦ ?_, fun i ↦ ?_⟩
  · have := hV (e.symm i)
    exact IsAffine.of_isIso (j (e.symm i)).isoOpensRange.inv
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcov.symm ▸ Set.mem_univ x)
    refine ⟨e k, ?_⟩
    show x ∈ Set.range (j (e.symm (e k)))
    rw [e.symm_apply_apply]
    exact hk
  · have := hV (e.symm i)
    have : IsAffine (j (e.symm i)).opensRange :=
      IsAffine.of_isIso (j (e.symm i)).isoOpensRange.inv
    obtain ⟨L, d, t, ht⟩ := hL (e.symm i)
    let L' := L.restrict (i := (j (e.symm i)).isoOpensRange.inv)
      (Scheme.Hom.isoOpensRange_inv_comp _)
    obtain ⟨t', ht'⟩ := L.exists_etaleCoordinates_restrict (i := (j (e.symm i)).isoOpensRange.inv)
      (Scheme.Hom.isoOpensRange_inv_comp _) ht
    exact ⟨L', d, t', ht'⟩

end Crystalline.GlobalCrystallineSituation.CechEnvelope

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CechEnvelope Stacks.CechSite.FinalCover AlgebraicGeometry

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wB} (BigModuleSheaf S)] [HasDerivedCategory.{wB} (BigModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **Base change for a cover by charts with smooth lifts and étale coordinates.** Let
`X = Y ×_{S'₀} S₀`, `p` nilpotent on `S` and `S'`, `Y` separated, `U'_i` (`i : Fin n`) an affine
open cover of `Y` by charts with smooth lifts `B'_i` and étale coordinates, and `N` a
quasi-coherent `𝒪_{Y/S'}`-module on `CRIS(Y/S')`. Let `D'_i` be the objects of the `B'_i`, `D_i`
those of their base changes `A ⊗_{A'} B'_i` (smooth lifts of the `g⁻¹ U'_i`), and
`γ i : u(D_i) ⟶ D'_i`. If for every tuple `x` the sections `N(D'_x)` are flat over `A'` and the
transpose `A ⊗_{A'} N(D'_x) ⟶ N(u D_x)` is an isomorphism, then the base change map
`RΓ(CRIS(Y/S'), N) ⊗^L_{A'} A ⟶ RΓ(CRIS(X/S), u^* N)` is an isomorphism. -/
theorem isIso_baseChange_of_charts [IsAffine S.S.scheme] [IsAffine S'.S.scheme]
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
    (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (hp' : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)))
    [S.X.IsSeparated] [S'.X.IsSeparated] {n : ℕ}
    {U' : Fin n → S'.X.Opens} [∀ i, IsAffine (U' i)] [∀ i, IsAffine (g ⁻¹ᵁ U' i)]
    (hU' : ∀ x, ∃ i, x ∈ U' i) (L' : ∀ i, SmoothLift S' (U' i).ι)
    (hL' : ∀ i, ∃ (L : SmoothLift S' (U' i).ι) (d : ℕ) (t : Fin d → L.ring),
      (MvPolynomial.aeval (R := baseSectionsRing S') t).toRingHom.Etale)
    (γ : ∀ i, (changeBase S S' f g h).obj (cechObjects hp (fun i ↦ (L' i).baseChange hpb) i) ⟶
      cechObjects hp' L' i)
    (N' : SheafOfModules.{u} (crystallineStructureSheaf S')) [N'.IsQuasicoherentOnSite]
    (hθ : ∀ (k : ℕ) (x : Fin (k + 1) → Fin n), IsIso
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} (baseChangeRingHom f)).homEquiv _ _).symm
        (changeBaseCechComponent hp hp' (fun i ↦ (L' i).baseChange hpb) L' f g h γ
          ((bigModuleULift S').obj N') x)))
    (hflat : ∀ (k : ℕ) (x : Fin (k + 1) → Fin n), Module.Flat Γ(S'.S.scheme, ⊤)
      (((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S')
        (bigBaseRingHom S')).obj ((bigModuleULift S').obj N')).obj
          (Opposite.op (inter (cechObjects hp' L') x)))) :
    IsIso (((derivedBaseChangeTensorAdjunction f).homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map
        (derivedChangeBaseBigGlobalSectionsMap f g h ((bigModuleULift S').obj N')))) := by
  let L : ∀ i, SmoothLift S (g ⁻¹ᵁ U' i).ι := fun i ↦ (L' i).baseChange hpb
  have hU : ∀ x, ∃ i, x ∈ g ⁻¹ᵁ U' i := fun x ↦ hU' (g x)
  have : IsIso ((cechToDerivedGlobalSections (crystallineStructureSheaf S')
      (bigBaseRingHom S') (cechObjects hp' L') (coversTop_object hp' U' hU' L')).app
        ((bigModuleULift S').obj N')) :=
    isIso_cechEnvelopeToDerived_app hp' hU' L' N' inferInstance
  have : IsIso ((cechToDerivedGlobalSections (crystallineStructureSheaf S)
      (bigBaseRingHom S) (cechObjects hp L) (coversTop_object hp (fun i ↦ g ⁻¹ᵁ U' i) hU L)).app
        ((changeBaseBigModulePullback S S' f g h).obj ((bigModuleULift S').obj N'))) :=
    isIso_cechEnvelopeToDerived_app hp hU L ((changeBaseModulePullback S S' f g h).obj N')
      (isQuasicoherentOnSite_changeBaseModulePullback f g h N' inferInstance)
  have := flat_cechIntFunctor_X hp' L' ((bigModuleULift S').obj N') hflat
  obtain ⟨m, hm⟩ := exists_isZero_homology_tensorComplex_cech hp' hU' L' hL'
  exact isIso_baseChange_of_cech hp hp' hU L hU' L' f g h γ ((bigModuleULift S').obj N') m
    (fun M k hk ↦ hm N' M k hk)
    (quasiIso_transpose_changeBaseCechMap hp hp' L L' f g h γ _ hθ)

end Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Reading tuplewise base change on the universe lifts -/

namespace ModuleCat

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] (ρ : R →+* S)

/-- An `R`-linear map `X → Y` out of a map `X ⟶ res Y` of `ModuleCat`. -/
def restrictScalarsHomLinearMap {X : ModuleCat.{max v u} R} {Y : ModuleCat.{max v u} S}
    (θ : X ⟶ (restrictScalars.{max v u} ρ).obj Y) :
    letI : Module R Y := Module.compHom Y ρ
    X →ₗ[R] Y :=
  letI : Module R Y := Module.compHom Y ρ
  { toFun := θ.hom
    map_add' := map_add θ.hom
    map_smul' := map_smul θ.hom }

/-- **A transpose is an isomorphism when the map is a base change**: for `θ : X ⟶ res Y`, if
`θ : X → Y` exhibits `Y` as the base change `S ⊗_R X` (`IsBaseChange`), its adjoint transpose
`S ⊗_R X ⟶ Y` is an isomorphism. -/
theorem isIso_homEquiv_symm_of_isBaseChange {X : ModuleCat.{max v u} R}
    {Y : ModuleCat.{max v u} S} (θ : X ⟶ (restrictScalars.{max v u} ρ).obj Y)
    (hθ : letI := ρ.toAlgebra
      letI : Module R Y := Module.compHom Y ρ
      haveI : IsScalarTower R S Y := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      IsBaseChange S (restrictScalarsHomLinearMap ρ θ)) :
    IsIso (((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm θ) := by
  let := ρ.toAlgebra
  let : Module R Y := Module.compHom Y ρ
  have : IsScalarTower R S Y := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hfun : ∀ z, (((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm θ).hom z =
      hθ.equiv z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul s x => exact (IsBaseChange.equiv_tmul hθ (show S from s) x).symm
    | add z z' hz hz' =>
      exact (map_add _ _ _).trans ((congrArg₂ _ hz hz').trans (map_add _ _ _).symm)
  have hb : Function.Bijective
      (((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm θ).hom := by
    have : ⇑(((extendRestrictScalarsAdj.{v, u, u} ρ).homEquiv _ _).symm θ).hom = ⇑hθ.equiv :=
      funext hfun
    rw [this]
    exact hθ.equiv.bijective
  exact (ConcreteCategory.isIso_iff_bijective _).2 hb

end ModuleCat

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CechEnvelope Stacks.CechSite.FinalCover AlgebraicGeometry Opposite

variable {S S' : GlobalCrystallineSituation.{u}} (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- The restriction of the sections of the universe lift of `N` along `m : u(P) ⟶ P'`, as a map of
`A'`-modules into the restriction of scalars of the sections of the pullback over `P`. -/
abbrev changeBaseSectionsRestrict {P : Thickening S} {P' : Thickening S'}
    (m : (changeBase S S' f g h).obj P ⟶ P')
    (N : SheafOfModules.{u} (crystallineStructureSheaf S')) :
    ((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S')
        (bigBaseRingHom S')).obj ((bigModuleULift S').obj N)).obj (op P') ⟶
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).obj
        (((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S) (bigBaseRingHom S)).obj
          ((changeBaseBigModulePullback S S' f g h).obj ((bigModuleULift S').obj N))).obj
            (op P)) :=
  ((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S')
      (bigBaseRingHom S')).obj ((bigModuleULift S').obj N)).map m.op ≫
    pushforwardSectionsHom.{0, u, u + 1, u, u, u} (crystallineStructureSheaf S') (bigBaseRingHom S')
      (crystallineStructureSheaf S) (bigBaseRingHom S) (changeBase S S' f g h)
      (changeBaseStructureHom S S' f g h) (baseChangeRingHom f)
      (changeBaseStructureHom_app_bigBaseRingHom f g h) ((bigModuleULift S').obj N) P

/-- **The transpose of the restriction along `u(P) ⟶ P'` is an isomorphism when the restriction
`N(P') → N(u P)` exhibits `N(u P)` as `A ⊗_{A'} N(P')`**, read on the universe lifts. -/
theorem isIso_transpose_changeBaseSectionsRestrict {P : Thickening S} {P' : Thickening S'}
    (m : (changeBase S S' f g h).obj P ⟶ P') (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (φ₀ :
      letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
        Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
      letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
        Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
          (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
      N.val.obj (op P') →ₗ[Γ(S'.S.scheme, ⊤)] N.val.obj (op ((changeBase S S' f g h).obj P)))
    (hφ₀ : ∀ x, φ₀ x = moduleSiteRestrict N m x)
    (hb : letI : Algebra Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) := (baseChangeRingHom f).toAlgebra
      letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
        Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
      letI : Module Γ(S.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
        Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
          P.toBase.hom.appTop.hom
      letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
        Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
          (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
      haveI : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤)
          (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      IsBaseChange Γ(S.S.scheme, ⊤) φ₀) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} (baseChangeRingHom f)).homEquiv _
      _).symm (changeBaseSectionsRestrict f g h m N)) := by
  refine ModuleCat.isIso_homEquiv_symm_of_isBaseChange (baseChangeRingHom f) _ ?_
  let : Algebra Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤) := (baseChangeRingHom f).toAlgebra
  let : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
    Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
  let : Module Γ(S.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
      P.toBase.hom.appTop.hom
  let : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    Module.compHom (R := crysSheafRing S' ((changeBase S S' f g h).obj P)) _
      (P.toBase.hom.appTop.hom.comp (baseChangeRingHom f))
  have : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤)
      (N.val.obj (op ((changeBase S S' f g h).obj P))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module Γ(S'.S.scheme, ⊤)
      (((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S) (bigBaseRingHom S)).obj
          ((changeBaseBigModulePullback S S' f g h).obj ((bigModuleULift S').obj N))).obj
            (op P)) :=
    Module.compHom _ (baseChangeRingHom f)
  have : IsScalarTower Γ(S'.S.scheme, ⊤) Γ(S.S.scheme, ⊤)
      (((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S) (bigBaseRingHom S)).obj
          ((changeBaseBigModulePullback S S' f g h).obj ((bigModuleULift S').obj N))).obj
            (op P)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine (IsBaseChange.iff_of_equiv_comm
    (ULift.moduleEquiv.symm : _ ≃ₗ[Γ(S'.S.scheme, ⊤)] ULift.{u + 1} (N.val.obj (op P')))
    (ULift.moduleEquiv.symm : _ ≃ₗ[Γ(S.S.scheme, ⊤)]
      ULift.{u + 1} (N.val.obj (op ((changeBase S S' f g h).obj P))))
    (LinearMap.ext fun x ↦ ?_)).1 hb
  exact congrArg ULift.up (hφ₀ x).symm

/-- **The sections of the universe lift over `P'` are flat over `A'`** when the sections of `N`
over `P'` are, for the `A'`-module structure through `P' ⟶ S'`. -/
theorem flat_basePresheaf_bigModuleULift {P' : Thickening S'}
    (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (hfl : letI : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
        Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
      Module.Flat Γ(S'.S.scheme, ⊤) (N.val.obj (op P'))) :
    Module.Flat Γ(S'.S.scheme, ⊤)
      (((basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S')
        (bigBaseRingHom S')).obj ((bigModuleULift S').obj N)).obj (op P')) := by
  let : Module Γ(S'.S.scheme, ⊤) (N.val.obj (op P')) :=
    Module.compHom (R := crysSheafRing S' P') _ P'.toBase.hom.appTop.hom
  exact Module.Flat.of_linearEquiv ULift.moduleEquiv

end Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Base change with `p` nilpotent and a smooth source -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open CechEnvelope Stacks.CechSite.FinalCover

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wB} (BigModuleSheaf S)] [HasDerivedCategory.{wB} (BigModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **Base change for crystalline cohomology with `p` nilpotent and a smooth source**
([Stacks, Tag 07MU] when `p` is nilpotent, the case needed by [Stacks, Tag 07N5]). Let
`f : S ⟶ S'` be a morphism of divided power bases with `S`, `S'` affine, `A = Γ(S, 𝒪)`,
`A' = Γ(S', 𝒪)`, `p` nilpotent in `A` and `A'`, and `g : X ⟶ Y` with `X = Y ×_{S'₀} S₀` (the
closed-fibre square `h` is cartesian, `hpb`), where `Y ⟶ S'₀` is smooth and `Y` is separated and
quasi-compact. For every crystal `N` in finite locally free modules on `CRIS(Y/S')`, the base
change map

`RΓ(CRIS(Y/S'), N) ⊗^L_{A'} A ⟶ RΓ(CRIS(X/S), u^* N)`,

the adjoint transpose under `derivedBaseChangeTensorAdjunction f` of
`derivedChangeBaseBigGlobalSectionsMap f g h N`, is an isomorphism. No dimension hypothesis is
made.

Proof: cover `Y` by finitely many affine charts with smooth lifts carrying étale coordinates;
their base changes are smooth lifts of the charts `g⁻¹ U'_i` of `X`, mapped to them along change
of base; on the Čech complexes of the divided power envelopes the base change map is the Čech
map (`isIso_baseChange_of_charts`), whose terms are flat and base change termwise
(`...CechEnvelope.isBaseChange_changeBaseValuesMap_of_isLimit`,
`...CechEnvelope.flat_values_of_isLimit`), and whose tensor products are uniformly bounded. -/
theorem isIso_baseChange_of_isNilpotent_smooth [IsAffine S.S.scheme] [IsAffine S'.S.scheme]
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (hpb : IsPullback g S.toClosedFiber S'.toClosedFiber (DividedPowerScheme.closedFiberMap f))
    (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (hp' : IsNilpotent (S'.p : Γ(S'.S.scheme, ⊤)))
    (hsm : Smooth S'.toClosedFiber) [S'.X.IsSeparated] [CompactSpace S'.X]
    (N' : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (hN' : GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal N') :
    IsIso (((derivedBaseChangeTensorAdjunction f).homEquiv _ _).symm
      (DerivedCategory.Plus.ι.map
        (derivedChangeBaseBigGlobalSectionsMap f g h ((bigModuleULift S').obj N')))) := by
  obtain ⟨n, U', hU'a, hU', hL'⟩ := exists_fin_opens_smoothLift_etaleCoordinates S' hsm
  have := hU'a
  have : ∀ i, IsAffine (g ⁻¹ᵁ U' i) := fun i ↦ isAffine_preimage hpb (U' i)
  have : S.X.IsSeparated := by
    have hg : IsSeparated g := MorphismProperty.of_isPullback hpb.flip
      (inferInstance : IsSeparated (DividedPowerScheme.closedFiberMap f))
    refine ⟨?_⟩
    rw [show terminal.from S.X = g ≫ terminal.from S'.X from (terminal.comp_from g).symm]
    infer_instance
  have : N'.IsQuasicoherentOnSite := hN'.isQuasicoherentOnSite
  choose L' hL'' using hL'
  refine isIso_baseChange_of_charts f g h hpb hp hp' hU' L' (fun i ↦ ⟨L' i, hL'' i⟩)
    (fun i ↦ changeBaseHom hpb h hp hp' (L' i)) N' (fun k x ↦ ?_) (fun k x ↦ ?_)
  · refine isIso_transpose_changeBaseSectionsRestrict f g h _ N' (changeBaseValuesMap _ N')
      (fun _ ↦ rfl) ?_
    exact isBaseChange_changeBaseValuesMap_of_isLimit hpb h hp hp' (fun a ↦ L' (x a))
      (isLimitInterFan (cechObjects hp (fun i ↦ (L' i).baseChange hpb)) x)
      (isLimitInterFan (cechObjects hp' L') x)
      (fun a ↦ cechLiftMap_comp_interπ (cechObjects hp' L')
        (cechObjects hp (fun i ↦ (L' i).baseChange hpb)) (changeBase S S' f g h) (τ := id)
        (fun i ↦ changeBaseHom hpb h hp hp' (L' i)) x a) N' hN'.isQuasicoherentOnSite
  · exact flat_basePresheaf_bigModuleULift N' (flat_values_of_isLimit hp' (fun a ↦ L' (x a))
      (isLimitInterFan (cechObjects hp' L') x) N' hN')

end Crystalline.GlobalCrystallineSituation.SmallSite
