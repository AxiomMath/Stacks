module

public import StacksFrontier.AlgebraicGeometry.Quot.DegreeZeroSectionsLocalRepresentability
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessCriterionGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.ChartSliceTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08JX, part (2): local strictly perfect models in degrees `≥ 0`

Let `K` be a pseudo-coherent object of `D(𝒪_X)` on an algebraic space `X` such that
`Hⁱ(Lg^*K) = 0` for every scheme `g : T → X` and every `i < 0`, and let `P₀` be a K-flat complex
with flat terms representing `K`.  Every point of every scheme over `X` has an étale
neighbourhood `d` on which the pullback of `P₀` is quasi-isomorphic to a strictly perfect complex
concentrated in degrees `≥ 0`.

This is the second paragraph of the source's proof: near a point, a strictly perfect
approximation `P` of `K` has, by the vanishing of `H⁻¹` on the fibres, a free cokernel
`Coker(P⁻¹ → P⁰)` (Stacks 068U); the canonical truncation `τ_{≥ 0}P`, whose degree-zero term is
that cokernel, is then strictly perfect, and it represents `K` there because `K` has no
cohomology in negative degrees.

## Main results

* `AlgebraicGeometry.Space.FreeTruncation.exists_basicOpen_opcyclesIso`: the free cokernel near a
  point.
* `AlgebraicGeometry.Space.exists_etale_strictlyPerfect_model`: the local model.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### K-flat representatives -/

/-- **Every object of `D(𝒪_X)` is represented by a K-flat complex with flat terms**
(Stacks 06YS). -/
theorem exists_isKFlat_representative {X : AlgebraicSpaces B S hS} (K : derivedModules B S hS X) :
    ∃ P₀ : CochainComplex (toposModules B S hS X) ℤ,
      IsKFlat (Y := smallEtaleRingedTopos B S hS X)
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀) ∧
      Nonempty (DerivedCategory.Q.obj P₀ ≅ K) := by
  have : (toposQh X).EssSurj := Localization.essSurj _ (smallEtaleModuleQuasiIso B S hS X)
  obtain ⟨L, hL, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.hasResolutions_isKFlat'
      (Y := smallEtaleRingedTopos B S hS X) ((toposQh X).objPreimage K)
  have hs' : IsIso ((toposQh X).map s) := (DerivedCategory.isIso_Qh_map_iff s).2 hs
  exact ⟨L.as, hL, ⟨((DerivedCategory.quotientCompQhIso _).app L.as).symm ≪≫
    @asIso _ _ _ _ ((toposQh X).map s) hs' ≪≫ (toposQh X).objObjPreimageIso K⟩⟩

/-! ### The free cokernel near a point -/

namespace FreeTruncation

variable {T : BigFppfOver B S hS}
  {G : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj T)) ℤ}

/-- **Near a point where `H⁻¹` vanishes on the fibres, the degree-zero opcycles of a complex with
free terms in degrees `-2, …, 1` are free**: on a principal open neighbourhood of the point the
cokernel of `D₁` is free and split (`Matrix.exists_away_split_of_fibre_exact`). -/
theorem exists_basicOpen_opcyclesIso (Φ : FreeTruncation G)
    (x : (BigFppfOver.toScheme B S hS).obj T)
    (hvan : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T),
      IsZero (((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          G).homology (-1))) :
    ∃ (d : BigFppfOver B S hS) (t : d ⟶ T),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map t).base ∧
        ∃ r : ℕ, Nonempty (((((toposModulePullbackData B S hS).pull
          ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            G).opcycles 0 ≅ freeObj (unitT d) r) := by
  obtain ⟨f, hf, r, hB⟩ := Matrix.exists_away_split_of_fibre_exact _ Φ.D₂ Φ.D₁ Φ.D₂_mul_D₁
    (Φ.fibre_exact x hvan)
  obtain ⟨d, t, hoi, hrange, hunit⟩ := exists_basicOpen_test T f
  let : Algebra (Gam T) (Gam d) := ((BigFppfOver.toScheme B S hS).map t).appTop.hom.toAlgebra
  obtain ⟨q, s, t', h₁, h₂, h₃⟩ := hB (Gam d) hunit
  let Φ' := Φ.pull t
  refine ⟨d, t, hoi, ?_, r, ⟨opcyclesFreeIso _ Φ'.e₁ Φ'.e₀ Φ'.D₁ Φ'.hd₁ q s t' h₁ h₂ h₃⟩⟩
  rw [hrange, SetLike.mem_coe, ← Scheme.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) _ x trivial]
  exact fun h => hf (RingHom.mem_ker.mpr h)

end FreeTruncation

/-- **Near a point where `H⁻¹` vanishes on the fibres, the degree-zero opcycles of a complex of
direct summands of free modules are free.** -/
theorem exists_open_opcyclesIso {c : BigFppfOver B S hS}
    (F : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj c)) ℤ)
    (hF : ∀ j : ℤ, ∃ (n : ℕ) (i : F.X j ⟶ freeObj (unitT c) n) (r : freeObj (unitT c) n ⟶ F.X j),
      i ≫ r = 𝟙 _)
    (hvan : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ c),
      IsZero (((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          F).homology (-1)))
    (x : (BigFppfOver.toScheme B S hS).obj c) :
    ∃ (d : BigFppfOver B S hS) (t : d ⟶ c),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t) ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map t).base ∧
        ∃ r : ℕ, Nonempty (((((toposModulePullbackData B S hS).pull
          ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            F).opcycles 0 ≅ freeObj (unitT d) r) := by
  obtain ⟨d₁, t₁, hoi₁, ⟨y, hy⟩, ⟨Φ⟩⟩ := exists_basicOpen_freeTruncation F hF x
  have hvan' : ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ d₁),
      IsZero (((((toposModulePullbackData B S hS).pull
        ((schemeSpaceFunctor B S hS).map t)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((((toposModulePullbackData B S hS).pull
            ((schemeSpaceFunctor B S hS).map t₁)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj F)).homology (-1)) := fun T' t =>
    (hvan T' (t ≫ t₁)).of_iso
      (HomologicalComplex.homologyMapIso (pullCompComplexIso t t₁ F) (-1)).symm
  obtain ⟨d, t₂, hoi₂, ⟨z, hz⟩, r, ⟨e⟩⟩ := Φ.exists_basicOpen_opcyclesIso y hvan'
  refine ⟨d, t₂ ≫ t₁, ?_, ⟨z, ?_⟩, r,
    ⟨(HomologicalComplex.opcyclesFunctor _ _ 0).mapIso (pullCompComplexIso t₂ t₁ F) ≪≫ e⟩⟩
  · rw [Functor.map_comp]; infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app, hz, hy]

/-- A module isomorphic to a free module of finite rank is a direct summand of a finite free
module. -/
theorem isDirectSummandOfFiniteFree_of_iso_freeObj {c : BigFppfOver B S hS}
    {M : toposModules B S hS ((schemeSpaceFunctor B S hS).obj c)} {r : ℕ}
    (e : M ≅ freeObj (unitT c) r) :
    IsDirectSummandOfFiniteFree
      (ringedToposStructureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj c)) M := by
  let ι : SheafOfModules.free (R := ringedToposStructureRingSheaf B S hS
      ((schemeSpaceFunctor B S hS).obj c)) (ULift.{u} (Fin r)) ≅ freeObj (unitT c) r :=
    Sigma.whiskerEquiv (f := fun _ : ULift.{u} (Fin r) => SheafOfModules.unit
        (ringedToposStructureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj c)))
      (g := fun _ : Fin r => unitT c) Equiv.ulift (fun _ => Iso.refl _) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin r => unitT c)).symm
  exact (isDirectSummandOfFiniteFree_iff_free _ M).2
    ⟨r, (e ≪≫ ι.symm).hom, (e ≪≫ ι.symm).inv, (e ≪≫ ι.symm).hom_inv_id⟩

/-! ### The local model -/

section Model

variable {X : AlgebraicSpaces B S hS} (P₀ : CochainComplex (toposModules B S hS X) ℤ)
  (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
  {K : derivedModules B S hS X} (hK : IsPseudoCoherentObject K)
  (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
  (hvan : HasVanishingNegativeDerivedPullback hL K) (e : DerivedCategory.Q.obj P₀ ≅ K)

include hvan hP₀ e in
/-- **The hypothesis of Stacks 08JX, part (2), on a K-flat representative**: the pullback of
`P₀` to every scheme over `X` has no cohomology in negative degrees, the derived pullback being
computed degreewise on `P₀` (Stacks 06YY). -/
theorem isZero_homology_pull_of_hasVanishingNegative {T : BigFppfOver B S hS}
    (h : (schemeSpaceFunctor B S hS).obj T ⟶ X) (i : ℤ) (hi : i < 0) :
    IsZero (((((toposModulePullbackData B S hS).pull h).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀).homology i) :=
  (hvan (CostructuredArrow.mk h) i hi).of_iso
    (((DerivedCategory.homologyFunctorFactors (toposModules B S hS _) i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (toposModules B S hS _) i).mapIso
        ((derivedPullbackQIso h P₀ hP₀).symm ≪≫
          (smallEtaleDerivedModulePullback B S hS h).mapIso e))

include hvan hP₀ hK e in
/-- **Stacks 08JX, part (2), the local model.**  Every point of a scheme `Z` over `X` lies in
the image of an étale morphism `q : d ⟶ Z` such that the pullback of `P₀` to `d` is
quasi-isomorphic to a strictly perfect complex concentrated in degrees `≥ 0`: the canonical
truncation `τ_{≥ 0}` of a strictly perfect approximation whose degree-zero opcycles are free. -/
theorem exists_etale_strictlyPerfect_model (Z : SchemesOver X)
    (z : (BigFppfOver.toScheme B S hS).obj Z.left) :
    ∃ (d : BigFppfOver B S hS) (q : d ⟶ Z.left),
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        z ∈ Set.range ((BigFppfOver.toScheme B S hS).map q).base ∧
        ∃ (P' M : CochainComplex (toposModules B S hS ((schemeSpaceFunctor B S hS).obj d)) ℤ)
          (α : P' ⟶ M) (β : (((toposModulePullbackData B S hS).pull
            ((schemeSpaceFunctor B S hS).map q ≫ Z.hom)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P₀ ⟶ M),
          IsStrictlyPerfect (ringedToposStructureRingSheaf B S hS
            ((schemeSpaceFunctor B S hS).obj d)) P' ∧ (∀ i : ℤ, i < 0 → IsZero (P'.X i)) ∧
            QuasiIso α ∧ QuasiIso β := by
  obtain ⟨c, p, V, a, P, hP, γ, hγ₁, hγ₂, hpe, ⟨x, hx⟩, hcomm⟩ :=
    exists_etale_chart_data P₀ hK e Z z
  obtain ⟨d, t, hoi, ⟨y, hy⟩, r, ⟨eop⟩⟩ := exists_open_opcyclesIso _ (exists_retract_pull P hP a)
    (isZero_homology_pull_chart P₀ hP₀ (chartMorphism V) P hP γ hγ₁ hγ₂ hL
      hvan.hasVanishingDegreeNegOne e a) x
  obtain ⟨hPd, φ, hφ₁, -⟩ := exists_approximation_pull P₀ hP₀ (chartMorphism V) P hP γ hγ₁ hγ₂
    (t ≫ a)
  let F := (((toposModulePullbackData B S hS).pull
    ((schemeSpaceFunctor B S hS).map (t ≫ a))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let K' := (((toposModulePullbackData B S hS).pull ((schemeSpaceFunctor B S hS).map (t ≫ a) ≫
    chartMorphism V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀
  have eop' : F.opcycles 0 ≅ freeObj (unitT d) r :=
    (HomologicalComplex.opcyclesFunctor _ _ 0).mapIso (pullCompComplexIso t a P) ≪≫ eop
  have hK'ge : CochainComplex.IsGE K' 0 := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_homology_pull_of_hasVanishingNegative P₀ hP₀ hL hvan e _ i hi)
  have hq : QuasiIso (CochainComplex.truncGEMap φ 0) :=
    (CochainComplex.quasiIso_truncGEMap_iff φ 0).2 fun i hi =>
      (quasiIsoAt_iff_isIso_homologyMap φ i).2 (hφ₁ i (by omega))
  have hPd' : IsStrictlyPerfect (ringedToposStructureRingSheaf B S hS
      ((schemeSpaceFunctor B S hS).obj d)) F := hPd
  have hmor : (schemeSpaceFunctor B S hS).map (t ≫ p) ≫ Z.hom =
      (schemeSpaceFunctor B S hS).map (t ≫ a) ≫ chartMorphism V := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hcomm]
  have hge : ∀ i : ℤ, i < 0 → IsZero ((CochainComplex.truncGE F 0).X i) := fun i hi =>
    (CochainComplex.truncGE F 0).isZero_of_isStrictlyGE 0 i hi
  refine ⟨d, t ≫ p, ?_, ⟨y, ?_⟩, ?_⟩
  · rw [Functor.map_comp]; infer_instance
  · rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app, hy, hx]
  · rw [hmor]
    exact ⟨CochainComplex.truncGE F 0, CochainComplex.truncGE K' 0, CochainComplex.truncGEMap φ 0,
      CochainComplex.πTruncGE K' 0, SheafOfModules.isStrictlyPerfect_truncGE_general hPd' 0
        (isDirectSummandOfFiniteFree_of_iso_freeObj eop'), hge, hq, inferInstance⟩

end Model

/-- **The transport of modules from a chart to the slice at the chart** (Stacks 04M0), with its
source spelled as the modules of the small étale ringed topos of the chart. -/
abbrev chartSliceTransport {X : AlgebraicSpaces B S hS} (W : SmallEtale B S hS X.1) :
    toposModules B S hS (chartSpace B S hS X W) ⥤
      SheafOfModules.{u} ((structureRingSheaf B S hS X).over W) :=
  (chartModuleSliceEquiv B S hS X W).inverse

/-- The transport `chartSliceTransport W` of modules from a chart to the slice at the chart is an
equivalence of categories. -/
instance chartSliceTransport_isEquivalence {X : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS X.1) : (chartSliceTransport W).IsEquivalence :=
  inferInstanceAs (chartModuleSliceEquiv B S hS X W).inverse.IsEquivalence

/-- The transport `chartSliceTransport W` of modules from a chart to the slice at the chart is an
additive functor. -/
instance chartSliceTransport_additive {X : AlgebraicSpaces B S hS} (W : SmallEtale B S hS X.1) :
    (chartSliceTransport W).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Restriction of `𝒪_X`-modules to the slice at a chart**, with its source spelled as the
modules of the small étale ringed topos of `X`. -/
abbrev sliceRestriction {X : AlgebraicSpaces B S hS} (W : SmallEtale B S hS X.1) :
    toposModules B S hS X ⥤ SheafOfModules.{u} ((structureRingSheaf B S hS X).over W) :=
  SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) W

/-- Restriction `sliceRestriction W` of `𝒪_X`-modules to the slice at a chart is an additive
functor. -/
instance sliceRestriction_additive {X : AlgebraicSpaces B S hS} (W : SmallEtale B S hS X.1) :
    (sliceRestriction W).Additive :=
  ⟨rfl⟩

/-- Restriction `sliceRestriction W` of `𝒪_X`-modules to the slice at a chart preserves finite
limits. -/
instance sliceRestriction_preservesFiniteLimits {X : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS X.1) : PreservesFiniteLimits (sliceRestriction W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := structureRingSheaf B S hS X) W

/-- Restriction `sliceRestriction W` of `𝒪_X`-modules to the slice at a chart preserves finite
colimits. -/
instance sliceRestriction_preservesFiniteColimits {X : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS X.1) : PreservesFiniteColimits (sliceRestriction W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u, u, u}
    (R := structureRingSheaf B S hS X) W

/-- The transport from the chart to the slice is exact, so it preserves quasi-isomorphisms. -/
theorem quasiIso_map_chartSliceTransport {X : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS X.1)
    {A A' : CochainComplex (toposModules B S hS (chartSpace B S hS X W)) ℤ} (φ : A ⟶ A')
    (hφ : QuasiIso φ) :
    QuasiIso (((chartSliceTransport W).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) :=
  HomologicalComplex.quasiIso_map_of_preservesHomology (φ := φ) (F := chartSliceTransport W)
    (hφ := hφ)

/-! ### From the chart to the slice -/

section Slice

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.iterHasSheafifyAll RingedSite.iterWEqAll
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

variable {X : AlgebraicSpaces B S hS}

/-- The `𝒪_X`-modules on a slice of the small étale site form an abelian category. -/
local instance (priority := high) perfectOfVanishing_sliceModules_abelian
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    Abelian (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over U)) :=
  SheafOfModules.instAbelian _

/-- The `𝒪_X`-modules on a slice of the small étale site, in the spelling of the structure ring
sheaf, form an abelian category. -/
local instance (priority := high) perfectOfVanishing_structureSliceModules_abelian
    (U : SmallEtale B S hS X.1) :
    Abelian (SheafOfModules.{u} ((structureRingSheaf B S hS X).over U)) :=
  SheafOfModules.instAbelian _

/-- The transport of the structure sheaf of a chart to the slice at the chart is the structure
sheaf of the slice. -/
def chartModuleSliceEquivInverseUnitIso (W : SmallEtale B S hS X.1) :
    SheafOfModules.unit ((structureRingSheaf B S hS X).over W) ≅
      (chartModuleSliceEquiv B S hS X W).inverse.obj
        (SheafOfModules.unit (structureRingSheaf B S hS (chartSpace B S hS X W))) :=
  (chartSliceOverIso B S hS X W).app (SheafOfModules.unit (structureRingSheaf B S hS X)) ≪≫
    (chartModuleSliceEquiv B S hS X W).inverse.mapIso
      (((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W)).app _).symm ≪≫
        modulePullbackUnitIso B S hS (chartToSpace B S hS X W))

variable (P₀ : CochainComplex (toposModules B S hS X) ℤ) {K : derivedModules B S hS X}
  (e : DerivedCategory.Q.obj P₀ ≅ K)

include e in
/-- **A strictly perfect model on a chart is one on the slice at the chart.**  A strictly
perfect complex `P'` on the algebraic space of an étale chart `W` of `X`, concentrated in degrees
`≥ 0` and joined to the pullback of `P₀` by two quasi-isomorphisms, is carried by the
comparison of Stacks 04M0 to a strictly perfect complex on the slice `X_étale/W`, concentrated in
degrees `≥ 0`, which represents the restriction `K|_W`. -/
theorem exists_slice_model_of_chartSpace (W : SmallEtale B S hS X.1)
    (P' M : CochainComplex (toposModules B S hS (chartSpace B S hS X W)) ℤ) (α : P' ⟶ M)
    (β : (((toposModulePullbackData B S hS).pull (chartToSpace B S hS X W)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀ ⟶ M)
    (hP' : IsStrictlyPerfect (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X W)) P')
    (hge : ∀ i : ℤ, i < 0 → IsZero (P'.X i)) (hα : QuasiIso α) (hβ : QuasiIso β) :
    ∃ P : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS X).over W)) ℤ,
      IsStrictlyPerfect ((structureRingSheaf B S hS X).over W) P ∧
        (∀ i : ℤ, i < 0 → IsZero (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (sliceRestriction W).mapDerivedCategory.obj K) := by
  have : (modulePullback B S hS (chartToSpace B S hS X W)).Additive :=
    toposModulePullbackData_additive (chartToSpace B S hS X W)
  let G := chartSliceTransport W
  let GC := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let F := (toposModulePullbackData B S hS).pull (chartToSpace B S hS X W)
  let N := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀
  let O := sliceRestriction W
  let m : F ≅ etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X W)
      (isEtale_chartToSpace B S hS X W) :=
    modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X W)
      (isEtale_chartToSpace B S hS X W)
  let eF : F ⋙ G ≅ O := Functor.isoWhiskerRight m G ≪≫ (chartSliceOverIso B S hS X W).symm
  let cc : GC.obj N ≅
      (O.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀ :=
    (Functor.mapHomologicalComplexCompIso eF (ComplexShape.up ℤ)).app P₀
  let β' : N ⟶ M := β
  have qi : ∀ {A A'} (φ : A ⟶ A'), QuasiIso φ →
      (DerivedCategory.Q.obj (GC.obj A) ≅ DerivedCategory.Q.obj (GC.obj A')) :=
    fun φ hφ =>
      have := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (quasiIso_map_chartSliceTransport W φ hφ)
      asIso (DerivedCategory.Q.map (GC.map φ))
  exact ⟨GC.obj P',
    Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex G
      (chartModuleSliceEquivInverseUnitIso W) hP',
    fun i hi => G.map_isZero (hge i hi),
    ⟨qi α hα ≪≫ (qi β' hβ).symm ≪≫ DerivedCategory.Q.mapIso cc ≪≫
      (O.mapDerivedCategoryFactors.app P₀).symm ≪≫ O.mapDerivedCategory.mapIso e⟩⟩

include e in
/-- **A strictly perfect model on a chart is one on the slice at the chart**, for a chart given
as an algebraic space `Y` over `X` equal to the algebraic space of the chart. -/
theorem exists_slice_model_of_chart (W : SmallEtale B S hS X.1) {Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ X) (hY : Y = chartSpace B S hS X W) (hg : HEq g (chartToSpace B S hS X W))
    (P' M : CochainComplex (toposModules B S hS Y) ℤ) (α : P' ⟶ M)
    (β : (((toposModulePullbackData B S hS).pull g).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P₀ ⟶ M)
    (hP' : IsStrictlyPerfect (ringedToposStructureRingSheaf B S hS Y) P')
    (hge : ∀ i : ℤ, i < 0 → IsZero (P'.X i)) (hα : QuasiIso α) (hβ : QuasiIso β) :
    ∃ P : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS X).over W)) ℤ,
      IsStrictlyPerfect ((structureRingSheaf B S hS X).over W) P ∧
        (∀ i : ℤ, i < 0 → IsZero (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ (sliceRestriction W).mapDerivedCategory.obj K) := by
  subst hY
  obtain rfl := eq_of_heq hg
  exact exists_slice_model_of_chartSpace P₀ e W P' M α β hP' hge hα hβ

end Slice

/-! ### Local models on a covering of every object of the small étale site -/

section Covering

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.iterHasSheafifyAll RingedSite.iterWEqAll
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

variable {X : AlgebraicSpaces B S hS} (P₀ : CochainComplex (toposModules B S hS X) ℤ)
  (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
  {K : derivedModules B S hS X} (hK : IsPseudoCoherentObject K)
  (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
  (hvan : HasVanishingNegativeDerivedPullback hL K) (e : DerivedCategory.Q.obj P₀ ≅ K)

/-- The `𝒪_X`-modules on a slice of the small étale site form an abelian category. -/
local instance (priority := high) perfectOfVanishing_sliceModules_abelian'
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    Abelian (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over U)) :=
  SheafOfModules.instAbelian _

include hP₀ hK hvan e in
/-- **Stacks 08JX, part (2): strictly perfect models in degrees `≥ 0` on a covering of every
object of the small étale site.**  Every étale chart `U` of `X` is covered by étale charts `V`
over which the restriction `K|_V` is represented by a strictly perfect complex concentrated in
degrees `≥ 0`. -/
theorem exists_covering_slice_models (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    ∃ T : Presieve U, Sieve.generate T ∈ (smallEtaleRingedSite B S hS X.1 X.2).J U ∧
      ∀ ⦃V : (smallEtaleRingedSite B S hS X.1 X.2).C⦄ (f : V ⟶ U), T f →
        ∃ P : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).over V)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).over V) P ∧
            (∀ i : ℤ, i < 0 → IsZero (P.X i)) ∧
            Nonempty (DerivedCategory.Q.obj P ≅ (SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
                V).mapDerivedCategory.obj K) := by
  let U' : SmallEtale B S hS X.1 := U
  let Z : SchemesOver X := CostructuredArrow.mk (Y := U'.1.left) (chartToSpace B S hS X U')
  choose d q hq hz P' M α β hP' hge hα hβ using fun z =>
    exists_etale_strictlyPerfect_model P₀ hP₀ hK hL hvan e Z z
  let W : ∀ z, SmallEtale B S hS X.1 := fun z =>
    ⟨CostructuredArrow.mk (yoneda.map (q z) ≫ U'.1.hom),
      etale_comp_of_scheme B S hS (q z) U'.1.hom (hq z) U'.2⟩
  let a : ∀ z, W z ⟶ U' := fun z =>
    ObjectProperty.homMk (CostructuredArrow.homMk (q z) rfl)
  refine ⟨Presieve.ofArrows W a, ?_, ?_⟩
  · refine SmallEtale.ofArrows_mem_topology B S hS X.1 W a ?_
    exact (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun z => ⟨z, hz z⟩, fun z => hq z⟩
  · rintro V f ⟨z⟩
    obtain ⟨P, hP, hPz, ⟨eP⟩⟩ := exists_slice_model_of_chart P₀ e (W z)
      ((schemeSpaceFunctor B S hS).map (q z) ≫ Z.hom) rfl HEq.rfl (P' z) (M z) (α z)
      (β z) (hP' z) (hge z) (hα z) (hβ z)
    exact ⟨P, hP, hPz, ⟨eP⟩⟩

include hP₀ hK hvan e in
/-- **Stacks 08JX, part (2): `K` is perfect.**  If `Hⁱ(Lg^*K) = 0` for every scheme `g : T → X`
and every `i < 0`, then the pseudo-coherent object `K` is perfect (Stacks 08G5): every étale
chart is covered by charts over which `K` is represented by a strictly perfect complex. -/
theorem isPerfect_of_hasVanishingNegativeDerivedPullback :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K :=
  RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect_general _ K fun U => by
    obtain ⟨T, hT, h⟩ := exists_covering_slice_models P₀ hP₀ hK hL hvan e U
    exact ⟨T, hT, fun V f hf => by
      obtain ⟨P, hP, -, he⟩ := h f hf
      exact ⟨P, hP, he⟩⟩

end Covering

/-! ### Tor amplitude -/

section TorAmplitude

open Stacks.SheafOfModules (DerivedTensorProduct)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.iterHasSheafifyAll RingedSite.iterWEqAll
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

variable {X : AlgebraicSpaces B S hS}
  [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max (u + 1) u, u, u, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).O).Additive]
  [∀ (U : (smallEtaleRingedSite B S hS X.1 X.2).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max (u + 1) u, u, u, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).O).obj M).Additive]
  [∀ (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (K L : CochainComplex
      (RingedSite.Modules.{max (u + 1) u, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{max (u + 1) u, u, u, u, u}
        ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)
      (ComplexShape.up ℤ)]
  (P₀ : CochainComplex (toposModules B S hS X) ℤ)
  (hP₀ : IsKFlat (Y := smallEtaleRingedTopos B S hS X)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P₀))
  {K : derivedModules B S hS X} (hK : IsPseudoCoherentObject K)
  (hL : BottomRankStratum.HasDerivedModulePullbacks B S hS)
  (hvan : HasVanishingNegativeDerivedPullback hL K) (e : DerivedCategory.Q.obj P₀ ≅ K)

include hP₀ hK hvan e in
/-- **Stacks 08JX, part (2): `K` locally has tor amplitude in `[0, b]`.**  If `Hⁱ(Lg^*K) = 0`
for every scheme `g : T → X` and every `i < 0`, then every étale chart of `X` is covered by charts
`V` over which the restriction `K|_V` has tor amplitude in `[0, b_V]` for some `b_V ≥ 0`
(Stacks 08FZ), against any derived tensor product on the slices: there `K|_V` is represented by
a bounded complex of flat modules concentrated in degrees `≥ 0` (Stacks 08G1). -/
theorem locally_hasTorAmplitude_of_hasVanishingNegativeDerivedPullback
    (T : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      DerivedTensorProduct.{u + 1, u, u, u + 1} ((smallEtaleRingedSite B S hS X.1 X.2).over U))
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    ∃ P : Presieve U, Sieve.generate P ∈ (smallEtaleRingedSite B S hS X.1 X.2).J U ∧
      ∀ ⦃V : (smallEtaleRingedSite B S hS X.1 X.2).C⦄ (f : V ⟶ U), P f →
        ∃ b : ℤ, 0 ≤ b ∧ DerivedTensorProduct.HasTorAmplitude (T V)
          ((RingedSite.derivedRestriction.{u + 1, u, u, u + 1} _ V).obj K) 0 b := by
  obtain ⟨R, hR, h⟩ := exists_covering_slice_models P₀ hP₀ hK hL hvan e U
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨Pm, hPm, hPz, ⟨eP⟩⟩ := h f hf
  obtain ⟨b, hb⟩ := hPm.bounded.bddAbove
  refine ⟨max b 0, le_max_right _ _, ?_⟩
  refine DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative (T V) _ 0 (max b 0) Pm
    (fun i => Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree'
      (Y := (smallEtaleRingedSite B S hS X.1 X.2).over V) _ (hPm.termDirectSummand i))
    (fun i hi => ?_) eP
  simp only [Set.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hi | hi
  · exact hPz i hi
  · by_contra hnz
    exact absurd (hb hnz) (by omega)

include hK hvan in
/-- **Stacks 08JX, part (2), the first two conclusions.**  Let `K` be a pseudo-coherent object of
`D(𝒪_X)` on an algebraic space `X` such that `Hⁱ(Lg^*K) = 0` for every scheme `g : T → X` and
every `i < 0`.  Then `K` is perfect, and `K` locally has tor amplitude in `[0, b]`: every étale
chart of `X` is covered by charts `V` over which `K|_V` has tor amplitude in `[0, b_V]` for some
`b_V ≥ 0`, against any derived tensor product on the slices.

The proof is the source's: near every point a strictly perfect approximation of `K` has a free
cokernel `Coker(P⁻¹ → P⁰)` (Stacks 068U, from the vanishing of `H⁻¹` on the fibres), so its
canonical truncation `τ_{≥ 0}` is strictly perfect, and it represents `K` there because `K` has
no cohomology in negative degrees
(`AlgebraicGeometry.Space.exists_covering_slice_models`). -/
@[stacks 08JX "part (2), the conclusions that K is perfect and locally has tor amplitude in \
[0, b]"]
theorem isPerfect_and_locally_hasTorAmplitude_of_hasVanishingNegativeDerivedPullback
    (T : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      DerivedTensorProduct.{u + 1, u, u, u + 1} ((smallEtaleRingedSite B S hS X.1 X.2).over U)) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K ∧
      ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
        ∃ P : Presieve U, Sieve.generate P ∈ (smallEtaleRingedSite B S hS X.1 X.2).J U ∧
          ∀ ⦃V : (smallEtaleRingedSite B S hS X.1 X.2).C⦄ (f : V ⟶ U), P f →
            ∃ b : ℤ, 0 ≤ b ∧ DerivedTensorProduct.HasTorAmplitude (T V)
              ((RingedSite.derivedRestriction.{u + 1, u, u, u + 1} _ V).obj K) 0 b := by
  obtain ⟨P₀, hP₀, ⟨e⟩⟩ := exists_isKFlat_representative K
  exact ⟨isPerfect_of_hasVanishingNegativeDerivedPullback P₀ hP₀ hK hL hvan e,
    locally_hasTorAmplitude_of_hasVanishingNegativeDerivedPullback P₀ hP₀ hK hL hvan e T⟩

end TorAmplitude

end AlgebraicGeometry.Space

end
