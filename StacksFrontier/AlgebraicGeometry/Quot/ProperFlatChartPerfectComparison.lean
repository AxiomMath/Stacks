module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesChartDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModule
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtTensorPullbackPerfectApproximation
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituationTransport
public import StacksFrontier.Deformation.Artin.Obstruction.NatIsoOfNaturalAddEquiv
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartTildeExact
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent

/-!
# The perfect complex of Situation 07YX at a chart of `Spaces'_{fp, flat, proper}`

Let `x` be a flat, proper, finitely presented algebraic space `f : X → Spec A` over a Noetherian
ring `A`, and let `T^i(M) = Ext^i_{𝒪_X}(L_{X/A}, 𝒪_X ⊗_A M)` (`i = 1, 2`) be the deformation and
obstruction functors of [Stacks, Remark 0D1P], with their connecting map. The first proof of
[Stacks, Tag 08WA] (followed by Remark 0D1P) produces from [Stacks, Tag 08JR] a perfect complex
`K` of `A`-modules and isomorphisms `H^i(K ⊗ᴸ_A M) ≅ T^i(M)` for `i = 1, 2`, functorial in `M` and
compatible with the boundary maps: this is the datum that turns the deformation theory of `x` into
Situation 07YX.

This file assembles that datum. Part (A) of 08JR applied to `E`, `𝒢^• = 𝒪_X[0]` and `m = 2` gives
a perfect `K` on `(Spec A)_étale` and isomorphisms
`Ext^i_{𝒪_X}(E, 𝒪_X ⊗ f^*ℱ) ≅ H^i(Spec A, K ⊗ᴸ ℱ)` for `i ≤ 2` and quasi-coherent `ℱ`, natural
and compatible with boundary maps. At `ℱ = M~` these are composed with

* the identification of the left side with `T^i(M)` (`β` below), and
* the identification of `H^i(Spec A, K ⊗ᴸ M~)` with `H^i(K_A ⊗ᴸ_A M)` for a perfect complex `K_A`
  of `A`-modules corresponding to `K` (`hperfect` below),

and the composite is `A`-linear because all three factors are natural in `M`.

## The arguments taken, not proved here

The following enter as explicit arguments of
`ProperFlatLift.exists_isPerfect_derivedCohomology_iso_cotangentExt_of_comparison`:

* `hEcoh`, `hEb`: `E` lies in `D^-_{Coh}(𝒪_X)`. Here `E` is to be `L_{X/A}` read on the small
  étale site of `X`; that the cotangent complex of a morphism locally of finite type into a
  Noetherian base has coherent cohomology and is bounded above is Stacks 08PZ / 08SW for spaces.
* `hperfect`: on `(Spec A)_étale`, a perfect `K` corresponds to a perfect complex `K_A` of
  `A`-modules with `H^i(Spec A, K ⊗ᴸ M~) ≅ H^i(K_A ⊗ᴸ_A M)`, naturally in `M` and compatibly with
  the boundary maps; this needs `D_QCoh((Spec A)_étale) ≃ D(A)` compatible with `⊗ᴸ` and `RΓ`.
* `β`, `hβnat`, `hβδ`: the identification of `Ext^i_{𝒪_X}(E, 𝒪_X ⊗ f^*M~)` on the small étale site
  of `X` with `T^i(M)` on its `Type u` model, natural in `M` and carrying the boundary map to the
  connecting map of `T^•`.
* `hG`: `𝒪_X[0]` is a bounded complex of coherent modules, flat over `Spec A`, with proper support.
* `hlin`: `r : A` acts on `H^i(K ⊗ᴸ_A M)` through `H^i(K ⊗ᴸ_A (r • 𝟙_M))`.

## Main definitions

* `AlgebraicGeometry.Space.affineBaseTilde`: `M ↦ M~` on the small étale site of `Spec A`, the
  module `𝒪_{Spec A} ⊗_A M` of Stacks 0D3F.
* `AlgebraicGeometry.Space.structureSingleComplex`: the complex `𝒪_X[0]`.

## Main results

* `ProperFlatLift.exists_isPerfect_derivedCohomology_iso_cotangentExt_of_comparison`: the perfect
  complex of Situation 07YX at the chart `x`.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] pointTopology

/-- `𝒪_X ⊗_R −` is a left adjoint, so it preserves zero morphisms. -/
instance baseRingTensorModule_preservesZeroMorphisms {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
    (φ : R →+* modelGlobalFunctions B S hS X) :
    (baseRingTensorModule B S hS X φ).PreservesZeroMorphisms :=
  haveI := (baseRingTensorModuleAdjunction B S hS X φ).isLeftAdjoint
  Functor.preservesZeroMorphisms_of_isLeftAdjoint _

/-- **`M ↦ M~` on the small étale site of `Spec A`**: the module `𝒪_{Spec A} ⊗_A M` of Stacks
0D3F, for the base-ring datum `A ≅ Γ(Spec A) → Γ(𝒪_{Spec A})` of the identity of `Spec A`. -/
abbrev affineBaseTilde (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) :
    ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS
        (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))) :=
  baseRingTensorModule B S hS (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA))
    ((baseRingHomOfMap (𝟙 (schemeSpace (Deformation.Artin.algebraOver A B S hS toS hA)))).comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)

/-- `M ↦ M~` preserves zero morphisms. -/
instance affineBaseTilde_preservesZeroMorphisms (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (toS : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) : (affineBaseTilde A B S hS toS hA).PreservesZeroMorphisms :=
  baseRingTensorModule_preservesZeroMorphisms _ _

/-- **The complex `𝒪_X[0]`**: the structure sheaf of `X` placed in degree `0`. -/
abbrev structureSingleComplex {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X : AlgebraicSpaces B S hS) :
    CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ :=
  (HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _)

namespace ProperFlatLift

open Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  [HasDerivedCategory.{t} (modelModules x.obj.obj.left)]

/-- `M~` is quasi-coherent. -/
theorem isQuasicoherentOnSite_affineBaseTilde (M : ModuleCat.{u} A) :
    ((affineBaseTilde A B S hS toS hA).obj M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_baseRingTensorModule B S hS _ _ M

/-- **The perfect complex of Situation 07YX at a chart, from 08JR.** Let `x` be a flat, proper,
finitely presented `f : X → Spec A` with `Spec A` Noetherian, and
`T^i(M) = Ext^i(L_{X/A}, 𝒪_X ⊗_A M)` (`cotangentExtOne`, `cotangentExtTwo`) with connecting map
`chartExtConnecting x hx`. Given

* `E ∈ D^-_{Coh}(𝒪_X)` on the small étale site of `X` and an identification `β` of
  `Ext^i(E, 𝒪_X ⊗ f^*M~)` with `T^i(M)`, natural in `M` and carrying the boundary map of `E` to the
  connecting map of `T^•`,
* the hypotheses on `𝒢^• = 𝒪_X[0]` of 08JR,
* `hperfect`: a perfect `K` on `(Spec A)_étale` corresponds to a perfect complex of `A`-modules,
  with comparison of `H^i(Spec A, K ⊗ᴸ M~)` and `H^i(K_A ⊗ᴸ_A M)` natural in `M` and compatible
  with the boundary maps,

there are a perfect complex `K` of `A`-modules and natural isomorphisms
`e_i : H^i(K ⊗ᴸ_A −) ≅ T^i` for `i = 1, 2`, carrying the boundary map of `K` to the connecting
map of `T^•`: the hypotheses of
`Deformation.Artin.FunctorDeformationTheory.toDualDeformationSituation` and
`obstructionBoundaryCondition_toDualDeformationSituation`. -/
theorem exists_isPerfect_derivedCohomology_iso_cotangentExt_of_comparison
    (hTop : B.Contains (⊤_ Scheme.{u}))
    (hf : IsLocallyOfFiniteType B S hS (chartStructureMap x hx).hom)
    (hfqs : IsQuasiSeparated B S hS (chartStructureMap x hx).hom)
    (hY : IsNoetherian B S hS hTop (schemeSpace (algebraOver A B S hS toS hA)).1)
    (hqc : ∀ M : ModuleCat.{u} A,
      ((affineBaseTilde A B S hS toS hA).obj M).IsQuasicoherentOnSite)
    (hexact : ∀ {Sq : ShortComplex (ModuleCat.{u} A)}, Sq.ShortExact →
      (Sq.map (affineBaseTilde A B S hS toS hA)).ShortExact)
    (E : DerivedCategory (Modules.{u, u} B S hS x.obj.obj.left.1 x.obj.obj.left.2))
    (hEcoh : ∀ q : ℤ, IsCoherent B S hS x.obj.obj.left.1 x.obj.obj.left.2
      ((DerivedCategory.homologyFunctor _ q).obj E))
    (hEb : DerivedCategoryB.IsBoundedAbove E)
    (hG : FlatProperSupportComplex B S hS (chartStructureMap x hx) hf
      (structureSingleComplex x.obj.obj.left))
    (β : ∀ (M : ModuleCat.{u} A) (i : ℤ),
      tensorPullbackExtGroup B S hS E (chartStructureMap x hx)
          (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).obj M) i ≃+
        (cotangentExtFunctor (chartStructureMap x hx) (chartBaseRingHom x hx) i).obj M)
    (hβnat : ∀ {M N : ModuleCat.{u} A} (g : M ⟶ N) (i : ℤ) (y),
      β N i ((tensorPullbackExtGroupMap B S hS E (chartStructureMap x hx)
          (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).map g) i) y) =
        (cotangentExtFunctor (chartStructureMap x hx) (chartBaseRingHom x hx) i).map g (β M i y))
    (hβδ : ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) (y),
      β Sq.X₁ 2 ((tensorPullbackExtGroupDelta B S hS E (chartStructureMap x hx)
          (structureSingleComplex x.obj.obj.left) (Sq.map (affineBaseTilde A B S hS toS hA))
          (shortExact_tensorPullbackComplex_map_single
            (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) (hexact hSq))
          1 2 rfl) y) =
        chartExtConnecting x hx hSq (β Sq.X₃ 1 y))
    (hperfect : ∀ (K : smallEtaleModulesDerived B S hS (schemeSpace (algebraOver A B S hS toS hA))),
      SmallEtaleIsPerfect B S hS K →
      ∃ (K_A : DerivedCategory (ModuleCat.{u} A)) (_ : StacksDraft.Perfect.IsPerfect K_A)
        (γ : ∀ (M : ModuleCat.{u} A) (i : ℤ),
          smallEtaleTensorCohomology B S hS K ((affineBaseTilde A B S hS toS hA).obj M) i ≃+
            (derivedCohomology A K_A i).obj M),
        (∀ {M N : ModuleCat.{u} A} (g : M ⟶ N) (i : ℤ) (y),
          γ N i ((smallEtaleTensorCohomologyMap B S hS K
              ((affineBaseTilde A B S hS toS hA).map g) i) y) =
            (derivedCohomology A K_A i).map g (γ M i y)) ∧
        (∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
          (hT : (Sq.map (affineBaseTilde A B S hS toS hA)).ShortExact) (y),
          γ Sq.X₁ 2 ((smallEtaleTensorCohomologyDelta B S hS K
              (Sq.map (affineBaseTilde A B S hS toS hA)) hT 1 2 rfl) y) =
            boundaryMap A K_A hSq (γ Sq.X₃ 1 y)))
    (hlin : ∀ (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) (M : ModuleCat.{u} A) (r : A)
      (y : (derivedCohomology A K i).obj M), (derivedCohomology A K i).map (r • 𝟙 M) y = r • y) :
    ∃ (K : DerivedCategory (ModuleCat.{u} A))
      (e₁ : derivedCohomology A K 1 ≅
        cotangentExtOne (chartStructureMap x hx) (chartBaseRingHom x hx))
      (e₂ : derivedCohomology A K 2 ≅
        cotangentExtTwo (chartStructureMap x hx) (chartBaseRingHom x hx)),
      StacksDraft.Perfect.IsPerfect K ∧
        ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact),
          boundaryMap A K hSq ≫ e₂.hom.app Sq.X₁ =
            e₁.hom.app Sq.X₃ ≫ chartExtConnecting x hx hSq := by
  obtain ⟨K, hK, α, hiso, hαnat, hαδ⟩ :=
    exists_isPerfect_tensorPullbackExtGroup_smallEtaleTensorCohomology B S hS hTop
      (chartStructureMap x hx) hf hfqs hY E hEcoh hEb (structureSingleComplex x.obj.obj.left) hG 2
  obtain ⟨KA, hKA, γ, hγnat, hγδ⟩ := hperfect K hK
  let a : ∀ (M : ModuleCat.{u} A) (i : ℤ), i ≤ 2 →
      (tensorPullbackExtGroup B S hS E (chartStructureMap x hx)
          (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).obj M) i ≃+
        smallEtaleTensorCohomology B S hS K ((affineBaseTilde A B S hS toS hA).obj M) i) :=
    fun M i hi =>
      have := hiso _ (hqc M) i hi
      (asIso (α _ (hqc M) i)).addCommGroupIsoToAddEquiv
  have ha : ∀ (M : ModuleCat.{u} A) (i : ℤ) (hi : i ≤ 2) (w), a M i hi w = α _ (hqc M) i w :=
    fun _ _ _ _ => rfl
  let ε : ∀ (i : ℤ), i ≤ 2 → ∀ M : ModuleCat.{u} A,
      (derivedCohomology A KA i).obj M ≃+
        (cotangentExtFunctor (chartStructureMap x hx) (chartBaseRingHom x hx) i).obj M :=
    fun i hi M => ((γ M i).symm.trans (a M i hi).symm).trans (β M i)
  have hεnat : ∀ (i : ℤ) (hi : i ≤ 2) {M N : ModuleCat.{u} A} (g : M ⟶ N) (y),
      ε i hi N ((derivedCohomology A KA i).map g y) =
        (cotangentExtFunctor (chartStructureMap x hx) (chartBaseRingHom x hx) i).map g
          (ε i hi M y) := by
    intro i hi M N g y
    have hγ : (γ N i).symm ((derivedCohomology A KA i).map g y) =
        (smallEtaleTensorCohomologyMap B S hS K ((affineBaseTilde A B S hS toS hA).map g) i)
          ((γ M i).symm y) := by
      apply (γ N i).injective
      rw [AddEquiv.apply_symm_apply, hγnat, AddEquiv.apply_symm_apply]
    have hα : ∀ w, (a N i hi).symm
        ((smallEtaleTensorCohomologyMap B S hS K ((affineBaseTilde A B S hS toS hA).map g) i) w) =
          (tensorPullbackExtGroupMap B S hS E (chartStructureMap x hx)
            (structureSingleComplex x.obj.obj.left) ((affineBaseTilde A B S hS toS hA).map g) i)
            ((a M i hi).symm w) := by
      intro w
      apply (a N i hi).injective
      rw [AddEquiv.apply_symm_apply, ha N i hi]
      have h := ConcreteCategory.congr_hom
        (hαnat (hqc M) (hqc N) ((affineBaseTilde A B S hS toS hA).map g) i) ((a M i hi).symm w)
      simp only [ConcreteCategory.comp_apply] at h
      rw [h, ← ha M i hi, AddEquiv.apply_symm_apply]
    change β N i ((a N i hi).symm ((γ N i).symm ((derivedCohomology A KA i).map g y))) =
      (cotangentExtFunctor (chartStructureMap x hx) (chartBaseRingHom x hx) i).map g
        (β M i ((a M i hi).symm ((γ M i).symm y)))
    rw [hγ, hα, hβnat]
  have hlinT : ∀ (i : ℤ) (M : ModuleCat.{u} A) (r : A)
      (y : (cotangentExtFunctor (chartStructureMap x hx) (chartBaseRingHom x hx) i).obj M),
      (cotangentExtFunctor (chartStructureMap x hx) (chartBaseRingHom x hx) i).map (r • 𝟙 M) y =
        r • y :=
    fun i M r y => (moduleFunctorOfAdditive_smul _ M r y).symm
  refine ⟨KA,
    natIsoOfNaturalAddEquiv (ε 1 (by norm_num)) (hεnat 1 (by norm_num)) (hlin KA 1) (hlinT 1),
    natIsoOfNaturalAddEquiv (ε 2 le_rfl) (hεnat 2 le_rfl) (hlin KA 2) (hlinT 2), hKA, ?_⟩
  intro Sq hSq
  have h12 : (1 : ℤ) ≤ 2 := by norm_num
  ext y
  change ε 2 le_rfl Sq.X₁ (boundaryMap A KA hSq y) =
    chartExtConnecting x hx hSq (ε 1 h12 Sq.X₃ y)
  obtain ⟨z, rfl⟩ := (γ Sq.X₃ 1).surjective y
  obtain ⟨w, rfl⟩ := (a Sq.X₃ 1 h12).surjective z
  have hδ := ConcreteCategory.congr_hom
    (hαδ (Sq.map (affineBaseTilde A B S hS toS hA)) (hexact hSq) (hqc Sq.X₁) (hqc Sq.X₃) 1 2 rfl) w
  simp only [ConcreteCategory.comp_apply] at hδ
  rw [← hγδ hSq (hexact hSq)]
  change β Sq.X₁ 2 ((a Sq.X₁ 2 le_rfl).symm ((γ Sq.X₁ 2).symm (γ Sq.X₁ 2 _))) =
    chartExtConnecting x hx hSq
      (β Sq.X₃ 1 ((a Sq.X₃ 1 h12).symm ((γ Sq.X₃ 1).symm (γ Sq.X₃ 1 (a Sq.X₃ 1 h12 w)))))
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    ha Sq.X₃ 1 h12 w]
  exact (congrArg (fun t => β Sq.X₁ 2 ((a Sq.X₁ 2 le_rfl).symm t)) hδ.symm).trans
    ((congrArg (β Sq.X₁ 2) ((a Sq.X₁ 2 le_rfl).symm_apply_apply _)).trans (hβδ hSq w))

/-- Composing with an equivalence of abelian categories keeps a short complex short exact. -/
theorem _root_.CategoryTheory.ShortComplex.ShortExact.map_comp_of_isEquivalence {𝒞 𝒟 ℰ : Type*}
    [Category 𝒞] [Category 𝒟] [Category ℰ] [HasZeroMorphisms 𝒞] [Abelian 𝒟] [Abelian ℰ]
    {F : 𝒞 ⥤ 𝒟} (hF : F.IsLeftAdjoint) (G : 𝒟 ⥤ ℰ) (hG : G.IsEquivalence)
    {Sq : ShortComplex 𝒞} (h : (Sq.map F).ShortExact) : (Sq.map (F ⋙ G)).ShortExact := by
  have := hF
  have := hG
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : G.IsLeftAdjoint := G.asEquivalence.toAdjunction.isLeftAdjoint
  have : G.IsRightAdjoint := G.asEquivalence.symm.toAdjunction.isRightAdjoint
  have : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact h.map_of_exact G

section TildeExact

/-- The modules on the small étale site of an algebraic space form an abelian category, with the
sheafification of `AlgebraicGeometry.Space.smallEtaleRingedSite`. -/
local instance (priority := high) smallEtaleModules_abelian (Z : AlgebraicSpaces B S hS) :
    Abelian (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) :=
  @SheafOfModules.instAbelian _ _ _ _ (smallEtaleRingedSite_hasSheafify B S hS Z.1 Z.2)
    (smallEtaleRingedSite_wEqualsLocallyBijective B S hS Z.1 Z.2)

/-- **`M ↦ M~` is exact**: `M~` is the inverse of the model equivalence applied to
`𝒪_{Spec A} ⊗_A M` on the model, which is exact because the identity of `Spec A` is flat. -/
theorem shortExact_map_affineBaseTilde {Sq : ShortComplex (ModuleCat.{u} A)}
    (hSq : Sq.ShortExact) : (Sq.map (affineBaseTilde A B S hS toS hA)).ShortExact := by
  have hQ := shortExact_map_modelTensorFunctor_of_isFlat_algebraOver
    (𝟙 (schemeSpace (algebraOver A B S hS toS hA)))
    (isFlat_id B S hS (schemeSpace (algebraOver A B S hS toS hA)).2) hSq
  exact hQ.map_comp_of_isEquivalence
    (Stacks.Cohomology.SiteModules.baseRingTensorAdjunction.{u, u, u, u, u} ((baseRingHomOfMap
      (𝟙 (schemeSpace (algebraOver A B S hS toS hA)))).comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).isLeftAdjoint
          (smallEtaleModelModulesEquiv B S hS
    (schemeSpace (algebraOver A B S hS toS hA))).inverse
    (smallEtaleModelModulesEquiv B S hS
      (schemeSpace (algebraOver A B S hS toS hA))).isEquivalence_inverse

end TildeExact

end ProperFlatLift

end AlgebraicGeometry.Space

end
