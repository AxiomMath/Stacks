module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.LocalGeneration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PresentationUnderFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# Local types of modules across the lower shriek of the small `τ`-site

Let `S` be a scheme of a big fppf site, `τ ∈ {smooth, syntomic, fppf}`, and let
`ι : S_τ ⊆ (Sch/S)_τ` be the inclusion of the small `τ`-site into the big one, with lower shriek
`ι_! : Mod(S_τ, 𝒪) ⥤ Mod((Sch/S)_τ, 𝒪)`.  This file proves that **each of the local conditions of
Modules on Sites, Definition 03DL — local generation by `r` sections, finite type, finite
presentation, finite local freeness and quasi-coherence — holds for a module `𝓝` on `S_τ` if and
only if it holds for `ι_! 𝓝` on `(Sch/S)_τ`.**

Each of these conditions asks that the restrictions of the module to the members of some family
covering the final object have a global property (Stacks 03DN).  The two directions are:

* a covering family of the final object of `S_τ` is carried by `ι` to one of `(Sch/S)_τ`, and on
  a member `V` the restriction of `ι_! 𝓝` is the localized lower shriek of the restriction of `𝓝`
  (`AlgebraicGeometry.SmallFlatSite.lowerShriekOverIso`), which preserves the global property,
  being colimit-preserving and carrying the structure sheaf to the structure sheaf;
* a covering family of the final object of `(Sch/S)_τ` is refined, `ι` being cocontinuous, by the
  objects `W` of `S_τ` mapping to one of its members; the global property passes to the
  restriction to `ι W`, and is reflected back to `𝓝|_W` by the localized lower shriek, which is
  fully faithful.

## Main results

* `AlgebraicGeometry.SmallFlatSite.exists_cover_iff_lowerShriek`: the transfer, for an arbitrary
  global property invariant under isomorphism and stable under restriction along arrows.
* `AlgebraicGeometry.SmallFlatSite.isLocallyGeneratedByOnSite_lowerShriek_iff`,
  `AlgebraicGeometry.SmallFlatSite.isFiniteType_lowerShriek_iff`,
  `AlgebraicGeometry.SmallFlatSite.isFinitePresentation_lowerShriek_iff`,
  `AlgebraicGeometry.SmallFlatSite.isFiniteLocallyFreeOnSite_lowerShriek_iff` and
  `AlgebraicGeometry.SmallFlatSite.isQuasicoherentOnSite_lowerShriek_iff`: the five conditions.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallFlatSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-! ### Coverings of the final object -/

/-- A family of objects covering the final object of the small `τ`-site covers the final object
of the big `τ`-site. -/
theorem coversTop_inclusion {I : Type*} {U : I → SmallFlatSite B S hS κ}
    (hU : (topology B S hS κ).CoversTop U) :
    (BigFppfOver.baseOverTopology B S hS κ.toSiteKind).CoversTop
      (fun i ↦ (inclusion B S hS κ).obj (U i)) := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ (isTerminalInclusionFinal B S hS κ)]
  refine (BigFppfOver.baseOverTopology B S hS κ.toSiteKind).superset_covering ?_
    ((mem_topology_iff B S hS κ _).1 (hU (final B S hS κ)))
  rintro Z g ⟨W, a, b, ⟨i, ⟨c⟩⟩, rfl⟩
  exact ⟨i, ⟨b ≫ (inclusion B S hS κ).map c⟩⟩

/-- A family of objects covering the final object of the big `τ`-site is refined by the objects
of the small `τ`-site mapping to one of its members, which cover the final object of the small
site: the inclusion is cocontinuous. -/
theorem coversTop_refine {I : Type*} {X : I → BigFppfOver B S hS}
    (hX : (BigFppfOver.baseOverTopology B S hS κ.toSiteKind).CoversTop X) :
    (topology B S hS κ).CoversTop
      (fun j : (Σ i, Σ W : SmallFlatSite B S hS κ, (inclusion B S hS κ).obj W ⟶ X i) ↦ j.2.1) := by
  intro Y
  refine (topology B S hS κ).superset_covering ?_
    ((inclusion B S hS κ).cover_lift (topology B S hS κ)
      (BigFppfOver.baseOverTopology B S hS κ.toSiteKind) (hX ((inclusion B S hS κ).obj Y)))
  rintro W g ⟨i, ⟨c⟩⟩
  exact ⟨⟨i, W, c⟩, ⟨𝟙 W⟩⟩

/-! ### The transfer -/

/-- **A local condition on `𝓝` is the same local condition on `ι_! 𝓝`.**  Let `G₁` and `G₂` be
global properties of modules on the localizations of the small and of the big `τ`-site, which
correspond under the localized lower shriek, are invariant under isomorphism on the big site and
pass to restrictions along arrows of the big site.  Then `𝓝` has `G₁` on the members of some
family covering the final object of `S_τ` if and only if `ι_! 𝓝` has `G₂` on the members of some
family covering the final object of `(Sch/S)_τ`. -/
theorem exists_cover_iff_lowerShriek
    (G₁ : ∀ V : SmallFlatSite B S hS κ,
      SheafOfModules.{u} ((ringStructureSheaf B S hS κ).over V) → Prop)
    (G₂ : ∀ X : BigFppfOver B S hS,
      SheafOfModules.{u} ((FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind).over X) → Prop)
    (hG : ∀ V M, G₁ V M ↔ G₂ ((inclusion B S hS κ).obj V) ((overLowerShriek B S hS κ V).obj M))
    (hiso : ∀ X {M M'} (_ : M ≅ M'), G₂ X M → G₂ X M')
    (hres : ∀ {X Y : BigFppfOver B S hS} (_ : X ⟶ Y)
      (M : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind)),
      G₂ Y (M.over Y) → G₂ X (M.over X))
    (𝓝 : SheafOfModules.{u} (ringStructureSheaf B S hS κ)) :
    (∃ (I : Type (u + 1)) (U : I → SmallFlatSite B S hS κ), (topology B S hS κ).CoversTop U ∧
        ∀ i, G₁ (U i) (𝓝.over (U i))) ↔
      ∃ (I : Type (u + 1)) (X : I → BigFppfOver B S hS),
        (BigFppfOver.baseOverTopology B S hS κ.toSiteKind).CoversTop X ∧
          ∀ i, G₂ (X i) (((lowerShriek B S hS κ).obj 𝓝).over (X i)) := by
  constructor
  · rintro ⟨I, U, hU, hG₁⟩
    exact ⟨I, fun i ↦ (inclusion B S hS κ).obj (U i), coversTop_inclusion B S hS κ hU,
      fun i ↦ hiso _ ((lowerShriekOverIso B S hS κ (U i)).app 𝓝) ((hG _ _).1 (hG₁ i))⟩
  · rintro ⟨I, X, hX, hG₂⟩
    exact ⟨_, _, coversTop_refine B S hS κ hX, fun j ↦ (hG _ _).2
      (hiso _ ((lowerShriekOverIso B S hS κ j.2.1).app 𝓝).symm (hres j.2.2 _ (hG₂ j.1)))⟩

/-! ### Local generation by `r` sections, Definition 03DL (4) -/

/-- **Local generation by `r` sections of a module on the small `τ`-site is local generation by `r`
sections of its lower shriek on the big `τ`-site.** -/
theorem isLocallyGeneratedByOnSite_lowerShriek_iff
    (𝓝 : SheafOfModules.{u} (ringStructureSheaf B S hS κ)) (r : ℕ) :
    SheafOfModules.IsLocallyGeneratedByOnSite 𝓝 r ↔
      SheafOfModules.IsLocallyGeneratedByOnSite ((lowerShriek B S hS κ).obj 𝓝) r :=
  (Stacks.SheafOfModules.isLocallyGeneratedByOnSite_iff_exists_cover_generators
      (ringedSite B S hS κ) 𝓝 r).trans <|
    (exists_cover_iff_lowerShriek B S hS κ
      (fun _ M ↦ M.IsGeneratedByGlobalSectionsOfCard r)
      (fun _ M ↦ M.IsGeneratedByGlobalSectionsOfCard r)
      (fun V M ↦ Stacks.Sheaves.GlobalTypeComparison.isGeneratedByGlobalSectionsOfCard_iff
        (overLowerShriek B S hS κ V) (overLowerShriekUnitIso B S hS κ V) M r)
      (fun _ _ _ e h ↦ Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSectionsOfCard_of_iso
        e r h)
      (fun f M h ↦ ⟨Stacks.SheafOfModules.generatingSectionsOverMap M f h.choose,
        h.choose_spec⟩) 𝓝).trans <|
    (Stacks.SheafOfModules.isLocallyGeneratedByOnSite_iff_exists_cover_generators
      (BigFppfOver.baseRingedSite B S hS κ.toSiteKind) ((lowerShriek B S hS κ).obj 𝓝) r).symm

/-! ### Finite type, Definition 03DL (5) -/

/-- **A module on the small `τ`-site is of finite type if and only if its lower shriek is.** -/
theorem isFiniteType_lowerShriek_iff (𝓝 : SheafOfModules.{u} (ringStructureSheaf B S hS κ)) :
    𝓝.IsFiniteType ↔ ((lowerShriek B S hS κ).obj 𝓝).IsFiniteType :=
  (Stacks.SheafOfModules.isFiniteType_iff_exists_cover_finite_generators 𝓝).trans <|
    (exists_cover_iff_lowerShriek B S hS κ
      (fun _ M ↦ ∃ σ : M.GeneratingSections, σ.IsFiniteType)
      (fun _ M ↦ ∃ σ : M.GeneratingSections, σ.IsFiniteType)
      (fun V M ↦ ⟨fun ⟨σ, hσ⟩ ↦ ⟨Stacks.Sheaves.GlobalTypeComparison.generatingSectionsMap
          (overLowerShriek B S hS κ V) (overLowerShriekUnitIso B S hS κ V) σ, ⟨hσ.finite⟩⟩,
        fun ⟨σ, hσ⟩ ↦ ⟨Stacks.Sheaves.GlobalTypeComparison.generatingSectionsOfMap
          (overLowerShriek B S hS κ V) (overLowerShriekUnitIso B S hS κ V) σ, ⟨hσ.finite⟩⟩⟩)
      (fun _ _ _ e ⟨σ, _⟩ ↦ ⟨σ.ofEpi e.hom, inferInstance⟩)
      (fun f M ⟨σ, hσ⟩ ↦ ⟨Stacks.SheafOfModules.generatingSectionsOverMap M f σ, ⟨hσ.finite⟩⟩)
      𝓝).trans <|
    (Stacks.SheafOfModules.isFiniteType_iff_exists_cover_finite_generators _).symm

/-! ### Finite presentation, Definition 03DL (7) -/

/-- A finite presentation of a restriction passes to a further restriction along an arrow. -/
theorem exists_finite_presentation_over_of_hom {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X : C, EssentiallySmall.{u} (Over X)] [∀ X : C, LocallySmall.{u} (Over X)]
    {X Y : C} (f : X ⟶ Y) (M : SheafOfModules.{u} R)
    (h : ∃ P : (M.over Y).Presentation, P.IsFinite) :
    ∃ P : (M.over X).Presentation, P.IsFinite := by
  obtain ⟨P, hP⟩ := h
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.overMap.{u} R f) :=
    Stacks.SheafOfModules.preservesColimitsOfSize_overMap R f
  have := Stacks.SheafOfModules.presentation_map_isFinite (SheafOfModules.overMap.{u} R f)
    (SheafOfModules.overMapUnitIso (R := R) f).symm P
  exact ⟨(P.map (SheafOfModules.overMap.{u} R f)
    (SheafOfModules.overMapUnitIso (R := R) f).symm).ofIsIso
    ((SheafOfModules.overFunctorMap R f).app M).hom, inferInstance⟩

/-- **A module on the small `τ`-site is of finite presentation if and only if its lower shriek
is.** -/
theorem isFinitePresentation_lowerShriek_iff
    (𝓝 : SheafOfModules.{u} (ringStructureSheaf B S hS κ)) :
    𝓝.IsFinitePresentation ↔ ((lowerShriek B S hS κ).obj 𝓝).IsFinitePresentation :=
  (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations 𝓝).trans <|
    (exists_cover_iff_lowerShriek B S hS κ
      (fun _ M ↦ ∃ P : M.Presentation, P.IsFinite)
      (fun _ M ↦ ∃ P : M.Presentation, P.IsFinite)
      (fun V M ↦ ⟨fun ⟨P, _⟩ ↦ ⟨P.map (overLowerShriek B S hS κ V)
          (overLowerShriekUnitIso B S hS κ V).symm,
          Stacks.SheafOfModules.presentation_map_isFinite _ _ P⟩,
        fun ⟨P, _⟩ ↦ ⟨Stacks.SheafOfModules.presentationOfMap (overLowerShriek B S hS κ V)
          (overLowerShriekUnitIso B S hS κ V).symm P,
          Stacks.SheafOfModules.presentationOfMap_isFinite _ _ P⟩⟩)
      (fun _ _ _ e ⟨P, _⟩ ↦ ⟨P.ofIsIso e.hom, inferInstance⟩)
      exists_finite_presentation_over_of_hom 𝓝).trans <|
    (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_finite_presentations _).symm

/-! ### Finite local freeness, Definition 03DL (2) -/

/-- A coproduct of `n` copies of the structure sheaf is carried by an isomorphism to one. -/
theorem exists_isColimit_cofan_of_iso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M M' : SheafOfModules.{u} R} (e : M ≅ M')
    (h : ∃ n : ℕ, ∃ ι : ∀ _ : Fin n, SheafOfModules.unit R ⟶ M,
      Nonempty (IsColimit (Cofan.mk M ι))) :
    ∃ n : ℕ, ∃ ι : ∀ _ : Fin n, SheafOfModules.unit R ⟶ M',
      Nonempty (IsColimit (Cofan.mk M' ι)) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  exact ⟨n, fun i ↦ ι i ≫ e.hom, ⟨hc.ofIsoColimit (Cocone.ext e (fun _ ↦ rfl))⟩⟩

/-- A finite free restriction passes to a further restriction along an arrow. -/
theorem exists_isColimit_cofan_over_of_hom {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X : C, EssentiallySmall.{u} (Over X)] [∀ X : C, LocallySmall.{u} (Over X)]
    {X Y : C} (f : X ⟶ Y) (M : SheafOfModules.{u} R)
    (h : ∃ n : ℕ, ∃ ι : ∀ _ : Fin n, SheafOfModules.unit (R.over Y) ⟶ M.over Y,
      Nonempty (IsColimit (Cofan.mk (M.over Y) ι))) :
    ∃ n : ℕ, ∃ ι : ∀ _ : Fin n, SheafOfModules.unit (R.over X) ⟶ M.over X,
      Nonempty (IsColimit (Cofan.mk (M.over X) ι)) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  have : PreservesColimitsOfSize.{u, u} (SheafOfModules.overMap.{u} R f) :=
    Stacks.SheafOfModules.preservesColimitsOfSize_overMap R f
  have : PreservesColimitsOfSize.{0, 0} (SheafOfModules.overMap.{u} R f) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  exact exists_isColimit_cofan_of_iso ((SheafOfModules.overFunctorMap R f).app M)
    ⟨n, _, ⟨Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap
      (SheafOfModules.overMap.{u} R f) (SheafOfModules.overMapUnitIso (R := R) f) ι hc⟩⟩

/-- **A module on the small `τ`-site is finite locally free if and only if its lower shriek
is.** -/
theorem isFiniteLocallyFreeOnSite_lowerShriek_iff
    (𝓝 : SheafOfModules.{u} (ringStructureSheaf B S hS κ)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite 𝓝 ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite ((lowerShriek B S hS κ).obj 𝓝) :=
  (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      (ringedSite B S hS κ) 𝓝).trans <|
    (exists_cover_iff_lowerShriek B S hS κ
      (fun V M ↦ ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
        SheafOfModules.unit ((ringStructureSheaf B S hS κ).over V) ⟶ M,
        Nonempty (IsColimit (Cofan.mk M ι)))
      (fun X M ↦ ∃ n : ℕ, ∃ ι : ∀ _ : Fin n,
        SheafOfModules.unit ((FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind).over X) ⟶ M,
        Nonempty (IsColimit (Cofan.mk M ι)))
      (fun V M ↦ by
        have : PreservesColimitsOfSize.{0, 0} (overLowerShriek B S hS κ V) :=
          preservesColimitsOfSize_shrink.{0, u, 0, u} _
        exact ⟨fun ⟨n, ι, ⟨hc⟩⟩ ↦ ⟨n, _, ⟨Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap
            (overLowerShriek B S hS κ V) (overLowerShriekUnitIso B S hS κ V) ι hc⟩⟩,
          fun ⟨n, ι, ⟨hc⟩⟩ ↦ ⟨n, _, ⟨Stacks.Sheaves.GlobalTypeComparison.isColimitCofanOfMap
            (overLowerShriek B S hS κ V) (overLowerShriekUnitIso B S hS κ V) ι hc⟩⟩⟩)
      (fun _ _ _ e h ↦ exists_isColimit_cofan_of_iso e h)
      exists_isColimit_cofan_over_of_hom 𝓝).trans <|
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      (BigFppfOver.baseRingedSite B S hS κ.toSiteKind) ((lowerShriek B S hS κ).obj 𝓝)).symm

/-! ### Quasi-coherence, Definition 03DL (6) -/

/-- **A module on the small `τ`-site is quasi-coherent if and only if its lower shriek is.**  On
the members of a covering, a global presentation is the same thing as a presentation, the
localized sites being essentially small, and presentations travel across the localized lower
shriek in both directions. -/
theorem isQuasicoherentOnSite_lowerShriek_iff
    (𝓝 : SheafOfModules.{u} (ringStructureSheaf B S hS κ)) :
    𝓝.IsQuasicoherentOnSite ↔ ((lowerShriek B S hS κ).obj 𝓝).IsQuasicoherentOnSite :=
  (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation 𝓝).trans <|
    (exists_cover_iff_lowerShriek B S hS κ
      (fun _ M ↦ M.HasGlobalPresentation)
      (fun _ M ↦ M.HasGlobalPresentation)
      (fun V M ↦ ⟨fun h ↦
          ((Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation h).some.map
            (overLowerShriek B S hS κ V) (overLowerShriekUnitIso B S hS κ V).symm
            ).hasGlobalPresentation,
        fun h ↦ (Stacks.SheafOfModules.presentationOfMap (overLowerShriek B S hS κ V)
            (overLowerShriekUnitIso B S hS κ V).symm
            (Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation h).some
            ).hasGlobalPresentation⟩)
      (fun _ _ _ e h ↦
        ((Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation h).some.ofIsIso
          e.hom).hasGlobalPresentation)
      (fun f M h ↦ Stacks.SheafOfModules.hasGlobalPresentation_overMap M f h) 𝓝).trans <|
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation _).symm

end AlgebraicGeometry.SmallFlatSite

end
