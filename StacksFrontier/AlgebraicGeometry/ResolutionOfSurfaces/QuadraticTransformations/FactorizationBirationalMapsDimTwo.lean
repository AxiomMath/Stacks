module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.CartierCentre
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.StalkwiseRegular
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMapDimTwo
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMaps
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMapsUnconditional
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalAssembly
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMaps

/-!
# Factorization of birational maps of regular surfaces, with the granted inputs discharged

`ResolutionOfSurfaces/QuadraticTransformations/FactorizationBirationalMaps.lean` states
[Stacks, Tag 0C5S] and the results leading to it over four granted inputs: `descent`, the local
splitting of [Stacks, Tag 0AGT]; `reduction`, the enlargement of the domain of an `S`-rational
map; `blowUpSurface`, the globalization of [Stacks, Tag 0AGR]; and `h0C5R`,
[Stacks, Tag 0C5R]. The first three are discharged here, and the forms of those results with
only [Stacks, Tag 0C5R] remaining are stated below.

## Main definitions

None. Every declaration here is a theorem.

## Main results

* `Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_blowUp_vanishingIdeal` — **the
  globalization of [Stacks, Tag 0AGR]**: the blowup of an integral Noetherian scheme regular of
  dimension two at a closed point is again such a scheme. This is the `blowUpSurface` input, and
  `Stacks.ResolutionOfSurfaces.blowUpSurface_of_isIntegralRegularSurface` is it in the shape the
  declarations of `FactorizationBirationalMaps.lean` expect.
* `Stacks.ResolutionOfSurfaces.birationalOver_blowUpToBase_of_isIntegral` — the blowup of an
  integral scheme of dimension two at a closed point is birational to it over any base, with
  regularity no longer needed.
* `Stacks.ResolutionOfSurfaces.isIntegral_and_topologicalKrullDim_and_isProper_of_pointBlowupChain`
  and `Stacks.ResolutionOfSurfaces.birationalOver_comp_of_pointBlowupChain_of_isIntegral` — the
  same for a chain of such blowups.
* `Stacks.ResolutionOfSurfaces.exists_factorsAsPointBlowups_of_birationalOver_of_dim_two` and
  `Stacks.ResolutionOfSurfaces.birationalOver_iff_exists_factorsAsPointBlowups_of_dim_two` —
  [Stacks, Tag 0C5S] over [Stacks, Tag 0C5R] alone.

## Implementation notes

The globalization of [Stacks, Tag 0AGR] goes as follows. At a closed point the local ring of an
integral scheme regular of dimension two has Krull dimension one or two. In the first case the
ideal sheaf of the point is an effective Cartier divisor, by
[Stacks, Tag 0AG8](https://stacks.math.columbia.edu/tag/0AG8), and the blowup is an isomorphism;
in the second case regularity of the local rings of the blowup is
`AlgebraicGeometry.isRegularLocalRing_stalk_blowUp`, which is Tag 0AGR carried along the flat
base change of [Stacks, Tag 0805](https://stacks.math.columbia.edu/tag/0805). Integrality and
dimension are carried along a chain by [Stacks, Tag 0AAZ], a blowup at a closed point being a
modification.

`descent` and `reduction` are discharged by
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_resolving_partialMap_of_dim_two` of
`DominateRationalMapDimTwo.lean`, which is [Stacks, Tag 0C5H] with no granted inputs on a
regular Noetherian scheme of dimension two.

The declarations of `FactorizationBirationalMaps.lean` keep their granted inputs: they are the
forms the rest of the development was compiled against, and what is here is an addition to them,
not a replacement. That file's private birationality lemmas and `pointBlowupChain_univ` are
reached through `import all` rather than copied.

## References

* [Stacks Project, Tag 0C5S](https://stacks.math.columbia.edu/tag/0C5S)
* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR)
* [Stacks Project, Tag 0AG8](https://stacks.math.columbia.edu/tag/0AG8)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0AAZ](https://stacks.math.columbia.edu/tag/0AAZ)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0BAD](https://stacks.math.columbia.edu/tag/0BAD)
* [Stacks Project, Tag 0A20](https://stacks.math.columbia.edu/tag/0A20)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The blowup at a closed point of a regular surface -/

/-- On an integral scheme of dimension two which is regular the local ring at a closed point has
Krull dimension one or two. -/
public theorem ringKrullDim_stalk_eq_one_or_two {X : Scheme.{u}}
    (hX : IsIntegralRegularSurface X) (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = 1 ∨ ringKrullDim (X.presheaf.stalk x) = 2 := by
  have hint := hX.isIntegral
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
    rw [← hX.topologicalKrullDim_eq, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (X.fromSpecStalk x).isEmbedding.isInducing.topologicalKrullDim_le
  have hne : ringKrullDim (X.presheaf.stalk x) ≠ 0 := by
    intro h0
    rw [ringKrullDim_stalk_eq_coheight] at h0
    have hc : Order.coheight x = 0 := by exact_mod_cast h0
    have hs : x ⤳ genericPoint X := Order.coheight_eq_zero.mp hc (show x ≤ (⊤ : X) from le_top)
    have hxη : x = genericPoint X := (hs.antisymm (genericPoint_specializes x)).eq
    refine genericPoint_notMem_supportSet
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X))
      (vanishingIdeal_singleton_ne_bot hX.topologicalKrullDim_eq x hx) ?_
    show genericPoint X ∈
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    simpa using hxη.symm
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX.isRegular x
  have h := (isRegularLocalRing_iff (X.presheaf.stalk x)).mp hreg
  rw [← h] at hle hne ⊢
  have hn : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank ≤ 2 := by
    exact_mod_cast hle
  have hn0 : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank ≠ 0 := by
    exact_mod_cast hne
  rcases (show (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank = 1 ∨
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank = 2 by omega) with h1 | h2
  · exact Or.inl (by exact_mod_cast h1)
  · exact Or.inr (by exact_mod_cast h2)

/-- At a closed point whose local ring is regular of dimension one the ideal sheaf of the point
is an effective Cartier divisor: its stalk there is the maximal ideal, which is generated by a
single nonzero element, and a nonzero element of a domain is a nonzerodivisor. -/
private theorem isEffectiveCartierDivisor_vanishingIdeal_of_ringKrullDim_stalk_eq_one
    {X : Scheme.{u}} [IsLocallyNoetherian X] [AlgebraicGeometry.IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hreg : IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
    fun y hy => ?_
  have hyx : y = x := by
    have hy' : y ∈ ((Scheme.IdealSheafData.vanishingIdeal
        (⟨{x}, hx⟩ : Closeds X)).support : Set X) := hy
    rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hy'
  subst hyx
  have hrank : (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).spanFinrank = 1 := by
    have h := (isRegularLocalRing_iff (X.presheaf.stalk y)).mp hreg
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨⟨a, ha⟩, hane⟩ :=
    (Submodule.spanFinrank_eq_one_iff (IsLocalRing.maximalIdeal (X.presheaf.stalk y))).mp hrank
  have ha0 : a ≠ 0 := fun h => hane (by simpa [h] using ha)
  refine ⟨a, mem_nonZeroDivisors_of_ne_zero ha0, ?_⟩
  rwa [AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton]

/-- The blowup of an integral Noetherian scheme of dimension two at a closed point is integral of
dimension two. -/
private theorem isIntegral_and_topologicalKrullDim_blowUp_vanishingIdeal {W : Scheme.{u}}
    (hW : AlgebraicGeometry.IsIntegral W) (hnoeth : AlgebraicGeometry.IsNoetherian W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W)) :
    AlgebraicGeometry.IsIntegral
        (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) ∧
      topologicalKrullDim
        (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) = 2 := by
  have hWLN : IsLocallyNoetherian W := hnoeth.toIsLocallyNoetherian
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
  have hMbot : M ≠ ⊥ := vanishingIdeal_singleton_ne_bot hdim w hw
  have hBint : AlgebraicGeometry.IsIntegral (blowUp M) := isIntegral_blowUp M hMbot
  exact ⟨hBint, (topologicalKrullDim_eq_of_isModification (blowUpToBase M)
    ⟨isBirational_blowUpToBase M hMbot, inferInstance, hBint⟩).trans hdim⟩

/-- **The globalization of [Stacks, Tag 0AGR].** The blowup of an integral Noetherian scheme
regular of dimension two at a closed point is again an integral Noetherian scheme regular of
dimension two. -/
public theorem isIntegralRegularSurface_blowUp_vanishingIdeal {A : Scheme.{u}} (a : A)
    (ha : IsClosed ({a} : Set A)) (hA : IsIntegralRegularSurface A) :
    IsIntegralRegularSurface
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))) := by
  have hint := hA.isIntegral
  have hnoeth := hA.isNoetherian
  have hreg := AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hA.isRegular
  set M : A.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A) with hM
  obtain ⟨hBint, hBdim⟩ := isIntegral_and_topologicalKrullDim_blowUp_vanishingIdeal
    hint hnoeth hA.topologicalKrullDim_eq a ha
  have hBnoeth : AlgebraicGeometry.IsNoetherian (blowUp M) := isNoetherian_blowUp M
  have hBLN : IsLocallyNoetherian (blowUp M) := hBnoeth.toIsLocallyNoetherian
  refine ⟨hBint, hBnoeth, ?_, hBdim⟩
  have hLN : IsLocallyNoetherian A := hnoeth.toIsLocallyNoetherian
  rcases ringKrullDim_stalk_eq_one_or_two hA a ha with hdim1 | hdim2
  · -- The centre is already an effective Cartier divisor, so the blowup is an isomorphism.
    have hiso : IsIso (blowUpToBase M) :=
      Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor M
        (isEffectiveCartierDivisor_vanishingIdeal_of_ringKrullDim_stalk_eq_one a ha (hreg a)
          hdim1)
    refine (isRegular_iff_regular_stalks _).mpr ⟨hBLN, fun q => ?_⟩
    have := hreg (blowUpToBase M q)
    exact IsRegularLocalRing.of_ringEquiv
      (asIso ((blowUpToBase M).stalkMap q)).commRingCatIsoToRingEquiv
  · exact (isRegular_iff_regular_stalks _).mpr ⟨hBLN, isRegularLocalRing_stalk_blowUp a ha hreg
      hdim2 M hM⟩

/-- `Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_blowUp_vanishingIdeal` in the shape of
the `blowUpSurface` hypothesis of
`Stacks.ResolutionOfSurfaces.isIntegralRegularSurface_and_isProper_of_pointBlowupChain` and of
the results of `FactorizationBirationalMaps.lean` built on it. -/
public theorem blowUpSurface_of_isIntegralRegularSurface :
    ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A)), IsIntegralRegularSurface A →
      IsIntegralRegularSurface
        (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))) :=
  fun _ a ha hA => isIntegralRegularSurface_blowUp_vanishingIdeal a ha hA

/-! ### A single blowup at a closed point is birational -/

/-- The blowup of an integral scheme of dimension two at a closed point is birational to it over
any base: the blowup is an isomorphism away from the point, and the complement of the point is a
nonempty open. -/
public theorem birationalOver_blowUpToBase_of_isIntegral {S W : Scheme.{u}}
    (hW : AlgebraicGeometry.IsIntegral W) (hWdim : topologicalKrullDim W = 2) (w : W)
    (hw : IsClosed ({w} : Set W)) (sW : W ⟶ S) :
    Scheme.BirationalOver
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) ≫ sW) sW := by
  have hint := hW
  set M : W.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)
  have hMbot : M ≠ ⊥ := vanishingIdeal_singleton_ne_bot hWdim w hw
  have hblow : AlgebraicGeometry.IsIntegral (blowUp M) := isIntegral_blowUp M hMbot
  set V : W.Opens := ⟨(M.support : Set W)ᶜ, M.support.isClosed.isOpen_compl⟩
  have hiso : IsIso (blowUpToBase M ∣_ V) := isIso_blowUp_restrict_compl_support M
  have hVne : (V : Set W).Nonempty :=
    ⟨genericPoint W, genericPoint_notMem_supportSet M hMbot⟩
  have hUne : ((blowUpToBase M ⁻¹ᵁ V : (blowUp M).Opens) : Set (blowUp M)).Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    obtain ⟨z, -⟩ := (asIso (blowUpToBase M ∣_ V)).hom.surjective ⟨v, hv⟩
    exact ⟨z.1, z.2⟩
  refine (birationalOver_iff_exists_nonempty_open_iso (blowUpToBase M ≫ sW) sW).mpr
    ⟨blowUpToBase M ⁻¹ᵁ V, V, hUne, hVne, asIso (blowUpToBase M ∣_ V), ?_⟩
  simp only [asIso_hom]
  rw [← Category.assoc, morphismRestrict_ι (blowUpToBase M) V, Category.assoc]

/-! ### Chains of blowups at closed points of a surface -/

/-- The source of a chain of blowups at closed points of an integral Noetherian scheme of
dimension two is again such a scheme, and the composite morphism is proper. -/
public theorem isIntegral_and_topologicalKrullDim_and_isProper_of_pointBlowupChain
    {X Z : Scheme.{u}} {T : Set X} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p)
    (hint : AlgebraicGeometry.IsIntegral X) (hnoeth : AlgebraicGeometry.IsNoetherian X)
    (hdim : topologicalKrullDim X = 2) :
    AlgebraicGeometry.IsIntegral Z ∧ AlgebraicGeometry.IsNoetherian Z ∧
      topologicalKrullDim Z = 2 ∧ IsProper p := by
  induction hp with
  | refl => exact ⟨hint, hnoeth, hdim, inferInstance⟩
  | step hh w hw hwT ih =>
    obtain ⟨hWint, hWnoeth, hWdim, hWproper⟩ := ih
    have := hWnoeth.toIsLocallyNoetherian
    set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds _)
    obtain ⟨hBint, hBdim⟩ :=
      isIntegral_and_topologicalKrullDim_blowUp_vanishingIdeal hWint hWnoeth hWdim w hw
    exact ⟨hBint, isNoetherian_blowUp M, hBdim,
      MorphismProperty.comp_mem _ _ _ (inferInstance : IsProper (blowUpToBase M)) hWproper⟩

/-- A chain of blowups at closed points of an integral Noetherian scheme of dimension two makes
its source birational to the target over any base. -/
public theorem birationalOver_comp_of_pointBlowupChain_of_isIntegral {S X Z : Scheme.{u}}
    (sX : X ⟶ S)
    {T : Set X} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p)
    (hint : AlgebraicGeometry.IsIntegral X) (hnoeth : AlgebraicGeometry.IsNoetherian X)
    (hdim : topologicalKrullDim X = 2) : Scheme.BirationalOver (p ≫ sX) sX := by
  induction hp with
  | refl => simpa using Scheme.BirationalOver.refl sX
  | step hh w hw hwT ih =>
    obtain ⟨hWint, -, hWdim, -⟩ :=
      isIntegral_and_topologicalKrullDim_and_isProper_of_pointBlowupChain hh hint hnoeth hdim
    rw [Category.assoc]
    exact (birationalOver_blowUpToBase_of_isIntegral hWint hWdim w hw _).trans ih

/-! ### Tag 0C5S -/

/-- **The forward direction of [Stacks, Tag 0C5S].** Let `S` be a Noetherian scheme and let `X`
and `Y` be proper integral schemes over `S` which are regular of dimension two. If `X` and `Y`
are `S`-birational then there is a scheme `Z` with `S`-morphisms `f : Z ⟶ X` and `g : Z ⟶ Y`,
each a finite sequence of blowups at closed points.

The one input carried as a hypothesis is `hfactors`, which is [Stacks, Tag 0C5R]. -/
public theorem exists_factorsAsPointBlowups_of_birationalOver_of_dim_two
    (hfactors : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g →
        FactorsAsPointBlowups A Set.univ B g)
    {S X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [X.Over S] [Y.Over S]
    [IsProper (X ↘ S)] [IsProper (Y ↘ S)]
    (hX : IsIntegralRegularSurface X) (hY : IsIntegralRegularSurface Y)
    (hbirational : Scheme.BirationalOver (X ↘ S) (Y ↘ S)) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
      f ≫ (X ↘ S) = g ≫ (Y ↘ S) ∧
        FactorsAsPointBlowups X Set.univ Z f ∧ FactorsAsPointBlowups Y Set.univ Z g := by
  have hXint := hX.isIntegral
  have hYint := hY.isIntegral
  have hXnoetherian := hX.isNoetherian
  set pIso := hbirational.partialIso (X ↘ S) (Y ↘ S)
  have hpmOver : pIso.toPartialMap.IsOver S := by
    refine ⟨?_⟩
    show (pIso.iso.hom ≫ pIso.target.ι) ≫ (Y ↘ S) = pIso.source.ι ≫ (X ↘ S)
    rw [Category.assoc]
    exact hbirational.partialIso_isOver (X ↘ S) (Y ↘ S)
  obtain ⟨Z, p, q, hchain, hqS, hagree⟩ :=
    exists_pointBlowupChain_resolving_partialMap_of_dim_two (S := S)
      (AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX.isRegular)
      hX.topologicalKrullDim_eq pIso.toPartialMap
  obtain ⟨hZsurface, hZproper⟩ :=
    isIntegralRegularSurface_and_isProper_of_pointBlowupChain
      blowUpSurface_of_isIntegralRegularSurface hchain hX
  have hZint := hZsurface.isIntegral
  have hpbirational : IsBirational p :=
    isBirational_of_birationalOver_id p
      (by
        simpa using birationalOver_comp_of_pointBlowupChain_of_isIntegral (𝟙 X) hchain
          hXint hXnoetherian hX.topologicalKrullDim_eq)
  have hqbirational : IsBirational q :=
    isBirational_of_resolves_partialIso pIso p q hpbirational hagree
  have hqproper : IsProper q := by
    have hcomp : IsProper (p ≫ (X ↘ S)) := inferInstance
    rw [← hqS] at hcomp
    exact IsProper.of_comp q (Y ↘ S)
  exact ⟨Z, p, q, hqS.symm,
    ⟨Z, p, pointBlowupChain_univ hchain, Iso.refl Z, by simp⟩,
    hfactors Y Z q hY hZsurface hqproper hqbirational⟩

/-- **Stacks Project, Tag 0C5S.** Let `S` be a Noetherian scheme and let `X` and `Y` be proper
integral schemes over `S` which are regular of dimension two. Then `X` and `Y` are `S`-birational
if and only if there is a scheme `Z` with `S`-morphisms `f : Z ⟶ X` and `g : Z ⟶ Y`, each a
finite sequence of blowups at closed points — the diagram
`X = X₀ ← … ← Xₙ = Y_m → … → Y₀ = Y` of the source.

The one input carried as a hypothesis is `hfactors`, which is [Stacks, Tag 0C5R]; only the
forward direction uses it, the converse, whose proof the source omits, being unconditional.

**No `@[stacks 0C5S]` attribute is placed here.** This form still carries [Stacks, Tag 0C5R] as
a hypothesis, so it is not an unconditional statement of the tag; the registration is on
`birationalOver_iff_exists_factorsAsPointBlowups_of_isIntegralRegularSurface` of
`PointBlowupFactorizationStep.lean`, which proves the tag outright. The converse direction, which
*is* unconditional, is
`Stacks.ResolutionOfSurfaces.birationalOver_comp_of_factorsAsPointBlowups_unconditional` of
`FactorizationBirationalMapsUnconditional.lean`, and it carries the registration for that
direction. -/
public theorem birationalOver_iff_exists_factorsAsPointBlowups_of_dim_two
    (hfactors : ∀ (A B : Scheme.{u}) (g : B ⟶ A), IsIntegralRegularSurface A →
      IsIntegralRegularSurface B → IsProper g → IsBirational g →
        FactorsAsPointBlowups A Set.univ B g)
    {S X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [X.Over S] [Y.Over S]
    [IsProper (X ↘ S)] [IsProper (Y ↘ S)]
    (hX : IsIntegralRegularSurface X) (hY : IsIntegralRegularSurface Y) :
    Scheme.BirationalOver (X ↘ S) (Y ↘ S) ↔
      ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
        f ≫ (X ↘ S) = g ≫ (Y ↘ S) ∧
          FactorsAsPointBlowups X Set.univ Z f ∧ FactorsAsPointBlowups Y Set.univ Z g := by
  refine ⟨exists_factorsAsPointBlowups_of_birationalOver_of_dim_two hfactors hX hY, ?_⟩
  rintro ⟨Z, f, g, hfg, hf, hg⟩
  have hgY : Scheme.BirationalOver (f ≫ (X ↘ S)) (Y ↘ S) := by
    rw [hfg]
    exact birationalOver_comp_of_factorsAsPointBlowups_unconditional (Y ↘ S) hY hg
  exact (birationalOver_comp_of_factorsAsPointBlowups_unconditional (X ↘ S) hX hf).symm.trans hgY

end Stacks.ResolutionOfSurfaces

end
