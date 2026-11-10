module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.SupportedSections.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.BlowUpChartCover.Cartier
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0CZQ: the strict transform under a Fitting blowup

Stacks Tag 0CZQ says that if `F` is a finite type quasi-coherent module on `S` which is finite
locally free of rank `k` away from the support of its `k`th Fitting ideal `I`, then the strict
transform of `F` under the blowup of `I` is finite locally free of rank `k` everywhere.

This file proves Stacks 0CZQ with every ingredient expressed through the library's existing
names, and with no `set_option maxHeartbeats`: the two expensive declarations
(`isFiniteLocallyFreeOfRank_of_iso` and the main theorem) compile at the default budget.

## The blowup used

The library blowup
`AlgebraicGeometry.blowUp` (`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/BlowUp.lean`) is
the
relative `Proj` of the Rees algebra outright, with no choice of data, so the statement below
depends on no unproved choice of Rees algebra data.

## What is proved unconditionally, and what is named as a hypothesis

Everything the source's proof does *itself* is proved here with no hypothesis:

* `ideal_eq_bot_of_comap_eq_bot`, `ideal_eq_top_of_stalk_eq_top`,
  `isFiniteType_of_isGeneratedByNear`, `fittingIdeal_eq_top_of_isGeneratedByNear`;
* `isSchemeTheoreticallyDominant_exceptionalPreimageCompl`, where the dominance comes from
  `Stacks.BlowUpChartCover.isEffectiveCartierDivisor_exceptionalIdeal` (Tag 02OS (2)) and
  `Stacks.CartierAffineLocal.isSchemeTheoreticallyDense_supportCompl` (Tag 07ZU density half),
  so the Tag 02OO and Tag 07ZU inputs are **discharged**, not assumed;
* `restrict_supportedSectionsSubmodule_ι_eq_zero` and `pullbackSupportedSectionsCokernelIso`;
* `isFiniteLocallyFreeOfRank_of_iso`;
* `isFiniteLocallyFreeOfRank_pullback` and
  `isFiniteLocallyFreeOfRank_of_generated_of_dense_open`, the heart of the argument.

Three inputs of the source's proof are named as hypotheses rather than assumed silently. The
third of them is discharged, in
`StacksFrontier/AlgebraicGeometry/StrictTransformFittingRank/Quasicoherent.lean`,
which also restates the main theorem below without it
(`Stacks.StrictTransformFittingRank.isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp'`);
the first two are not yet available in the library.

* `FittingRankCriterion` is **Stacks Tag 0C3G**, the sheaf-level Fitting-ideal criterion for being
  finite locally free of rank `r`. Its *ring-level* counterpart is proved as
  `finiteLocallyFreeOfRank_fittingIdeal_tfae` (`StacksFrontier/RingTheory/Fitting/Rank.lean`); what
  remains is the globalisation.
* `StrictTransformGeneration` is **Stacks Tag 0CZP**. Its ring-level counterpart is proved as
  `fittingIdeal_strictTransform_affineBlowup_eq_top`, **Stacks Tag 0CZM**
  (`StacksFrontier/RingTheory/Flat/Blowup.lean`), and the ring-level form of Tag 0CZQ itself is
  proved there too as `isFiniteLocallyFreeOfRank_strictTransform_affineBlowup`, **Stacks Tag
  0CZN** (`:393`). So the whole algebra is already proved; what remains is the
  comparison of the sheaf-level strict transform with the ring-level one on a blowup chart. Part
  of that comparison is proved: by
  `Stacks.StrictTransform.sectionsSheafEquivQuotientTorsion`
  (`StacksFrontier/AlgebraicGeometry/Blowup/StrictTransformChartTorsion.lean`) the sections of the
  sheaf-level strict transform over an affine open on which the inverse image of the exceptional
  ideal is generated
  by a single section `a` are the sections of the pullback modulo their `a`-power torsion, which
  is the ring-level construction; what is still missing is the identification of those sections of
  the pullback with the base change `R[I/a] ⊗_R M` itself.
* `StrictTransformQuasicoherent` is the quasi-coherence of the strict transform (the subsheaf half
  is Tag 07ZP). **It is discharged**, as
  `Stacks.StrictTransformFittingRank.strictTransformQuasicoherent` in
  `StacksFrontier/AlgebraicGeometry/StrictTransformFittingRank/Quasicoherent.lean`: the subsheaf
  half
  is `supportedSectionsSubmodule_isQuasicoherent`
  (`StacksFrontier/AlgebraicGeometry/Divisors/SupportedSections/Basic.lean`, Tag 07ZP) and cokernels
  of quasi-coherent modules are quasi-coherent
  (`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`), and the
  `IsRetrocompact` input the former needs — which nothing supplied *here* — comes from the
  exceptional divisor being an effective Cartier divisor (Tag 02OS) and the complement of such
  being affine over the base (Tag 07ZT). The assembled statement is the instance
  `Stacks.StrictTransform.isQuasicoherent_sheaf`, whose quasi-compactness hypothesis
  `Stacks.StrictTransform.quasiCompact_ι_compl_support_exceptionalIdeal` discharges at a blowup.

## No Stacks Tag 0CZQ attribute is attached, and none should be

`isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp` below carries three hypotheses that
Tag 0CZQ does not, so it carries no Stacks attribute.

## Main definitions

* `baseChange`, `exceptionalPreimage`, `strictTransformSheaf`: the three **Stacks Tag
  080D** constructions of the statement, each a thin alias for the general construction of
  `StacksFrontier/AlgebraicGeometry/StrictTransform/Basic.lean` at the blowup of `I` and its
  exceptional ideal. They are names, not definitions: the mathematics lives at
  `Stacks.StrictTransform.baseChange`, `Stacks.StrictTransform.exceptionalPreimage` and
  `Stacks.StrictTransform.sheaf`, which carry the 080D registrations.
* `FittingRankCriterion`, `StrictTransformGeneration`, `StrictTransformQuasicoherent`: the three
  named hypotheses. The first two are Tags 0C3G and 0CZP; the third is the quasi-coherence
  assertion of Tag 080D, and is discharged in
  `StacksFrontier/AlgebraicGeometry/StrictTransformFittingRank/Quasicoherent.lean`.

## Main results

* `isFiniteLocallyFreeOfRank_of_iso`: rank-`k` finite local freeness transports along an
  isomorphism of modules. A `private` twin of this, `rank_of_module_iso`, exists at
  `StacksFrontier/AlgebraicGeometry/Different/FiniteSyntomicMorphisms/Rank.lean`, also without any
  `set_option`.
* `isSchemeTheoreticallyDominant_exceptionalPreimageCompl`: unconditional.
* `isFiniteLocallyFreeOfRank_of_generated_of_dense_open`: the reduction step of the source's
  proof, from `FittingRankCriterion` alone.
* `isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp`: **Stacks Tag 0CZQ** from the three
  named hypotheses.

## References

* [Stacks Project, Tag 0CZQ](https://stacks.math.columbia.edu/tag/0CZQ)
* [Stacks Project, Tag 0CZP](https://stacks.math.columbia.edu/tag/0CZP)
* [Stacks Project, Tag 0CZN](https://stacks.math.columbia.edu/tag/0CZN)
* [Stacks Project, Tag 0C3G](https://stacks.math.columbia.edu/tag/0C3G)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.StrictTransformFittingRank

/-- The base change of `f` along the blowup of `I`: the general
`Stacks.StrictTransform.baseChange` at that blowup. -/
abbrev baseChange {X S : Scheme.{u}} (f : X ⟶ S) (I : S.IdealSheafData) : Scheme.{u} :=
  Stacks.StrictTransform.baseChange f (blowUpToBase I)

/-- The inverse image of the exceptional divisor in the base change: the general
`Stacks.StrictTransform.exceptionalPreimage` at that blowup and its exceptional ideal. -/
abbrev exceptionalPreimage {X S : Scheme.{u}} (f : X ⟶ S) (I : S.IdealSheafData) :
    Set (baseChange f I) :=
  Stacks.StrictTransform.exceptionalPreimage f (blowUpToBase I) (exceptionalIdeal I)

/-- The strict transform of a quasi-coherent module along the blowup of the base: the general
`Stacks.StrictTransform.sheaf` at that blowup and its exceptional ideal. The quasi-coherence
binder is not needed for the construction and is kept only so that the consumers below read as
the source does. -/
abbrev strictTransformSheaf {X S : Scheme.{u}} (f : X ⟶ S) (I : S.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] : (baseChange f I).Modules :=
  Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F

/-- An ideal vanishing after a schematically dominant base change vanishes. -/
@[ega "IV 11.10.1" "(a) ⇒ (c), special case"]
theorem ideal_eq_bot_of_comap_eq_bot {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSchemeTheoreticallyDominant f] (I : Y.IdealSheafData) (hI : I.comap f = ⊥) : I = ⊥ := by
  apply le_bot_iff.mp
  simpa only [hI, Scheme.IdealSheafData.map_bot, f.ker_eq_bot] using I.le_map_comap f

/-- An ideal sheaf whose stalk ideals are all the unit ideal is the unit ideal. -/
theorem ideal_eq_top_of_stalk_eq_top {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ∀ x, IdealSheafData.stalk I x = ⊤) : I = ⊤ := by
  apply I.support_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  have hle : IdealSheafData.stalk I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    apply iSup_le
    intro U
    apply iSup_le
    intro hxU
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change X.presheaf.germ U.1 x hxU a ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal]
    intro haunit
    have hzero := (I.mem_support_iff.mp hx) U
    exact (X.mem_zeroLocus_iff _ x).mp hzero a ha ((X.mem_basicOpen a x hxU).mpr haunit)
  rw [hI x] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top (top_le_iff.mp hle)

/-- Pointwise finite generating families assemble into finite type data. -/
theorem isFiniteType_of_isGeneratedByNear {X : Scheme.{u}} (F : X.Modules) (k : ℕ)
    (h : ∀ x, IsGeneratedByNear F k x) : F.IsFiniteType := by
  classical
  choose U hx g hg using h
  let q : F.LocalGeneratorsData.{u} :=
    { I := X
      X := U
      coversTop := (Opens.coversTop_iff X U).mpr
        (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩)
      generators := g }
  constructor
  refine ⟨q, ?_⟩
  constructor
  intro x
  exact ⟨Finite.of_equiv (Fin k) (hg x).some.symm⟩

/-- A sheaf isomorphism transports finite local bases and their rank. -/
theorem isFiniteLocallyFreeOfRank_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (k : ℕ)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F k) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G k := by
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  let q' : G.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((SheafOfModules.overFunctor _ (q.X i)).mapIso e).hom }
  constructor
  refine ⟨q', ?_, hrank⟩
  constructor
  intro i
  simp only [q', SheafOfModules.GeneratingSections.ofEpi_π]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hfree.isIso i) inferInstance

/-- On an open disjoint from the support condition, the supported-sections inclusion is zero. -/
theorem restrict_supportedSectionsSubmodule_ι_eq_zero {X : Scheme.{u}} (F : X.Modules)
    (Z : Set X) (U : X.Opens) (hU : Disjoint (U : Set X) Z) :
    (Scheme.Modules.restrictFunctor U.ι).map
      (Scheme.Modules.supportedSectionsSubmodule Z F).ι = 0 := by
  ext V s
  change (s.1 : Γ(F, U.ι ''ᵁ V)) = 0
  apply TopCat.Presheaf.section_ext ⟨F.val.presheaf, F.isSheaf⟩
  intro x hx
  have hxZ : x ∉ Z := by
    obtain ⟨y, -, rfl⟩ := hx
    exact Set.disjoint_left.mp hU y.property
  exact (s.property x hx hxZ).trans
    (map_zero (TopCat.Presheaf.germ F.val.presheaf (U.ι ''ᵁ V) x hx).hom).symm

/-- The quotient by supported sections restricts to the original module on the complement of
the support condition. -/
def pullbackSupportedSectionsCokernelIso {X : Scheme.{u}} (F : X.Modules) (Z : Set X)
    (U : X.Opens) (hU : Disjoint (U : Set X) Z) :
    (Scheme.Modules.pullback U.ι).obj
        (cokernel (Scheme.Modules.supportedSectionsSubmodule Z F).ι) ≅
      (Scheme.Modules.pullback U.ι).obj F := by
  let T := Scheme.Modules.restrictFunctor U.ι
  let i := (Scheme.Modules.supportedSectionsSubmodule Z F).ι
  let e := Scheme.Modules.restrictFunctorIsoPullback U.ι
  let : T.Additive := Functor.additive_of_iso e.symm
  exact (e.app _).symm ≪≫ PreservesCokernel.iso T i ≪≫
    cokernelIsoOfEq (restrict_supportedSectionsSubmodule_ι_eq_zero F Z U hU) ≪≫
    cokernelZeroIsoTarget ≪≫ e.app F

/-- **Stacks Tag 0C3G, as a named hypothesis.** A finite type quasi-coherent module is finite
locally free of rank `r` exactly when its `(r-1)`st Fitting ideal vanishes and its `r`th is the
unit ideal. -/
def FittingRankCriterion : Prop :=
  ∀ {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ),
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r ↔
      ((r = 0 ∨ AlgebraicGeometry.fittingIdeal F ((r : ℤ) - 1) = ⊥) ∧
        AlgebraicGeometry.fittingIdeal F (r : ℤ) = ⊤)

/-- Generation by `k` sections near every point makes the `k`th Fitting ideal the unit ideal. -/
theorem fittingIdeal_eq_top_of_isGeneratedByNear {X : Scheme.{u}} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (k : ℕ) (h : ∀ x, IsGeneratedByNear F k x) :
    AlgebraicGeometry.fittingIdeal F (k : ℤ) = ⊤ :=
  ideal_eq_top_of_stalk_eq_top _ fun x ↦
    (isGeneratedByNear_iff_fittingIdeal_stalk_eq_top F k x).mp (h x)

/-- The pullback of a finite type quasi-coherent module is finite type and quasi-coherent. -/
private theorem pullback_isFiniteType_and_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Y.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj F).IsFiniteType ∧
      ((Scheme.Modules.pullback f).obj F).IsQuasicoherent :=
  ⟨SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom F,
    @SheafOfModules.modulePullback_isQuasicoherent X.toRingedSpace Y.toRingedSpace
      f.toLRSHom.toShHom F ‹F.IsQuasicoherent›⟩

/-- Finite local freeness of a fixed rank is preserved by base change. -/
theorem isFiniteLocallyFreeOfRank_pullback (hcrit : FittingRankCriterion.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (k : ℕ) (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F k) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj F) k := by
  obtain ⟨hFT, hQC⟩ := pullback_isFiniteType_and_isQuasicoherent f F
  have hp := (hcrit F k).mp h
  refine (hcrit ((Scheme.Modules.pullback f).obj F) k).mpr ?_
  simp only [← AlgebraicGeometry.fittingIdeal_comap]
  refine ⟨hp.1.imp id fun he ↦ ?_, ?_⟩
  · simp only [he, Scheme.IdealSheafData.comap_bot]
  · simp only [hp.2, Scheme.IdealSheafData.comap_top]

/-- **The heart of Stacks Tag 0CZQ's argument.** A module generated by `k` sections near every
point whose restriction to a scheme-theoretically dominant open is finite locally free of rank
`k` is finite locally free of rank `k` everywhere. -/
theorem isFiniteLocallyFreeOfRank_of_generated_of_dense_open (hcrit : FittingRankCriterion.{u})
    {X : Scheme.{u}} (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (k : ℕ)
    (U : X.Opens) [IsSchemeTheoreticallyDominant U.ι]
    (hgen : ∀ x, IsGeneratedByNear F k x)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) k) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F k := by
  obtain ⟨hFT, hQC⟩ := pullback_isFiniteType_and_isQuasicoherent U.ι F
  refine (hcrit F k).mpr ⟨?_, fittingIdeal_eq_top_of_isGeneratedByNear F k hgen⟩
  exact ((hcrit _ k).mp hrank).1.imp id fun hk ↦
    ideal_eq_bot_of_comap_eq_bot U.ι _ (by rwa [AlgebraicGeometry.fittingIdeal_comap])

/-- **Stacks Tag 0CZP, as a named hypothesis.** The strict transform of a finite type
quasi-coherent module along the blowup of its `k`th Fitting ideal is generated by `k` sections
near every point. -/
def StrictTransformGeneration : Prop :=
  ∀ {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (k : ℕ)
    (s : baseChange (𝟙 S) (AlgebraicGeometry.fittingIdeal F (k : ℤ))),
      IsGeneratedByNear
        (strictTransformSheaf (𝟙 S) (AlgebraicGeometry.fittingIdeal F (k : ℤ)) F) k s

/-- **The quasi-coherence assertion of Stacks Tag 080D, as a named hypothesis.** The strict
transform of a finite type quasi-coherent module is quasi-coherent.

This is discharged by `Stacks.StrictTransformFittingRank.strictTransformQuasicoherent` in
`StacksFrontier/AlgebraicGeometry/StrictTransformFittingRank/Quasicoherent.lean`. It is kept as a
named hypothesis so that the theorem below is not moved, and so that the discharge lives in the
file that may import `StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent`. -/
def StrictTransformQuasicoherent : Prop :=
  ∀ {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (k : ℕ),
    (strictTransformSheaf (𝟙 S) (AlgebraicGeometry.fittingIdeal F (k : ℤ)) F).IsQuasicoherent

/-- The inclusion of the complement of the exceptional preimage is schematically dominant. -/
theorem isSchemeTheoreticallyDominant_exceptionalPreimageCompl {S : Scheme.{u}}
    (I : S.IdealSheafData) :
    IsSchemeTheoreticallyDominant
      ((pullback.snd (𝟙 S) (blowUpToBase I)) ⁻¹ᵁ
        ((exceptionalIdeal I).support.compl : (blowUp I).Opens)).ι := by
  set p : baseChange (𝟙 S) I ⟶ blowUp I := pullback.snd (𝟙 S) (blowUpToBase I) with hp
  set W : (blowUp I).Opens := (exceptionalIdeal I).support.compl
  have hpiso : IsIso p := by
    rw [hp]
    infer_instance
  have hWdom : IsSchemeTheoreticallyDominant W.ι :=
    Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense W
      (Stacks.CartierAffineLocal.isSchemeTheoreticallyDense_supportCompl (exceptionalIdeal I)
        (Stacks.BlowUpChartCover.isEffectiveCartierDivisor_exceptionalIdeal I))
  have hfac : (p ⁻¹ᵁ W).ι = (p ∣_ W) ≫ W.ι ≫ inv p := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [hfac]
  infer_instance

/-- **Stacks Tag 0CZQ**, from the three named hypotheses. -/
theorem isFiniteLocallyFreeOfRank_strictTransform_fittingBlowUp
    (hcrit : FittingRankCriterion.{u}) (hgenz : StrictTransformGeneration.{u})
    (hqc : StrictTransformQuasicoherent.{u})
    {S : Scheme.{u}} (F : S.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (k : ℕ)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback
          (Scheme.Opens.ι (AlgebraicGeometry.fittingIdeal F (k : ℤ)).support.compl)).obj F) k) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (strictTransformSheaf (𝟙 S) (AlgebraicGeometry.fittingIdeal F (k : ℤ)) F) k := by
  set I := AlgebraicGeometry.fittingIdeal F (k : ℤ)
  set b : baseChange (𝟙 S) I ⟶ S := pullback.fst (𝟙 S) (blowUpToBase I)
  set p : baseChange (𝟙 S) I ⟶ blowUp I := pullback.snd (𝟙 S) (blowUpToBase I)
  set W : (blowUp I).Opens := (exceptionalIdeal I).support.compl
  set V : (baseChange (𝟙 S) I).Opens := p ⁻¹ᵁ W
  set U : S.Opens := I.support.compl
  set G := strictTransformSheaf (𝟙 S) I F
  have hbp : b = p ≫ blowUpToBase I := (Category.comp_id b).symm.trans (pullback.condition ..)
  have hgen : ∀ x, IsGeneratedByNear G k x := hgenz F k
  have hGFT : G.IsFiniteType := isFiniteType_of_isGeneratedByNear G k hgen
  have hGQC : G.IsQuasicoherent := hqc F k
  have hVdom : IsSchemeTheoreticallyDominant V.ι :=
    isSchemeTheoreticallyDominant_exceptionalPreimageCompl I
  have hVU : Set.range (V.ι ≫ b).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : p.base (V.ι.base x) ∉ ((exceptionalIdeal I).support : Set (blowUp I)) :=
      x.property
    rw [Scheme.IdealSheafData.support_comap] at hx
    have : (V.ι ≫ b).base x = (blowUpToBase I).base (p.base (V.ι.base x)) := by
      rw [hbp]
      rfl
    rwa [this]
  let g : V.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι (V.ι ≫ b) hVU
  have hg : g ≫ U.ι = V.ι ≫ b := IsOpenImmersion.lift_fac _ _ hVU
  obtain ⟨hUFT, hUQC⟩ := pullback_isFiniteType_and_isQuasicoherent U.ι F
  refine isFiniteLocallyFreeOfRank_of_generated_of_dense_open hcrit G k V hgen ?_
  have hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback U.ι).obj F)) k :=
    isFiniteLocallyFreeOfRank_pullback hcrit g _ k h
  have hdisj : Disjoint (V : Set (baseChange (𝟙 S) I)) (exceptionalPreimage (𝟙 S) I) :=
    disjoint_compl_left
  let e : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback U.ι).obj F) ≅
      (Scheme.Modules.pullback V.ι).obj G :=
    (Scheme.Modules.pullbackComp g U.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr hg).app F ≪≫
      ((Scheme.Modules.pullbackComp V.ι b).app F).symm ≪≫
      (pullbackSupportedSectionsCokernelIso ((Scheme.Modules.pullback b).obj F)
        (exceptionalPreimage (𝟙 S) I) V hdisj).symm
  exact isFiniteLocallyFreeOfRank_of_iso e k hrank

end Stacks.StrictTransformFittingRank

end
