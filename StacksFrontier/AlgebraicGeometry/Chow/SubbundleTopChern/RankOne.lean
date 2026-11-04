module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.RankOneInputs
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.VectorBundleQuotient
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleRankOne
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.RationalEquivalenceDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraAffineSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass

/-!
# The class of a subbundle: closed embedding, and the case of corank one

Let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact sequence of finite locally free `𝒪_X`-modules, with
vector bundles `N' = 𝐕((𝒩')^∨)` and `N = 𝐕(𝒩^∨)`, projections `p'`, `p` and the morphism
`i : N' ⟶ N` of Stacks 0FAA. Dualizing gives a short exact sequence
`0 ⟶ ℰ^∨ ⟶ 𝒩^∨ ⟶ (𝒩')^∨ ⟶ 0`, and `N'` is the fibre of `q : N ⟶ 𝐕(ℰ^∨)` over the zero section of
`𝐕(ℰ^∨)`. Hence `i` is a closed immersion, and `q` is flat of relative dimension the rank of `𝒩'`.

When `ℰ = ℒ` is invertible, `𝐕(ℒ^∨)` is the line bundle of `ℒ^∨` and Stacks 0F96 (5) computes the
pushforward along its zero section, `o_* β = -p_{ℒ^∨}^*(c₁(ℒ^∨) ∩ β) = p_{ℒ^∨}^*(c₁(ℒ) ∩ β)`.
Pulling this back along `q` (Stacks 02RG for the cartesian square, Stacks 02RD for the composite
`q ≫ p_{ℒ^∨} = p`) gives

  `i_* (p')^* α = p^*(c₁(ℒ) ∩ α)`,

which is Stacks 0FAA for a sequence whose quotient is invertible.

## Main results

* `Stacks.Chow.isClosedImmersion_subbundleEmbedding_of_shortExact` — `i` is a closed immersion.
* `Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_of_rank_one` — the formula when the
  quotient is invertible.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

section Dual

variable {X : Scheme.{u}} (N' N E : X.Modules)
  [hN' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
  (hseq : (ShortComplex.mk inc pr w).ShortExact)

include hseq in
/-- The composite of the duals `dualMap pr ≫ dualMap inc` of a short exact sequence is zero. -/
theorem dualMap_comp_dualMap_eq_zero : dualMap pr ≫ dualMap inc = 0 :=
  (exists_dualSheaf_shortExact inc pr w hseq.mono_f hseq.epi_g hseq.exact
    (inferInstance) (inferInstance)
    (inferInstance)).choose

include hseq in
/-- **The dual sequence `0 ⟶ ℰ^∨ ⟶ 𝒩^∨ ⟶ (𝒩')^∨ ⟶ 0` is short exact.** -/
theorem dualShortComplex_shortExact :
    (ShortComplex.mk (dualMap pr) (dualMap inc)
      (dualMap_comp_dualMap_eq_zero N' N E inc pr w hseq)).ShortExact :=
  (exists_dualSheaf_shortExact inc pr w hseq.mono_f hseq.epi_g hseq.exact
    (inferInstance) (inferInstance)
    (inferInstance)).choose_spec

/-- The dual of a finite locally free `𝒪_X`-module is finite locally free. -/
instance isFiniteLocallyFree_dualSheaf' (M : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf M) :=
  isFiniteLocallyFree_dualSheaf M h

include hseq in
/-- **`N'` is the fibre of `N ⟶ 𝐕(ℰ^∨)` over the zero section of `𝐕(ℰ^∨)`.** -/
theorem isPullback_subbundleEmbedding :
    IsPullback (subbundleEmbedding N' N inc) (dualVectorBundleToBase N')
      (vectorBundleMap X (dualMap pr)).left (vectorBundleOverZeroSection (dualSheaf E)).left :=
  isPullback_vectorBundleMap_zeroSection (dualMap pr) (dualMap inc)
    (dualMap_comp_dualMap_eq_zero N' N E inc pr w hseq)
    (dualShortComplex_shortExact N' N E inc pr w hseq).gIsCokernel

include hseq in
/-- **Stacks 0FAA, the closed embedding.** For a short exact sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of
finite locally free `𝒪_X`-modules, of arbitrary ranks, the morphism
`i : N' = Spec_X(Sym((𝒩')^∨)) ⟶ N = Spec_X(Sym(𝒩^∨))` is a closed immersion: it is the base change
of the zero section of `𝐕(ℰ^∨)`, a section of a separated morphism. -/
@[stacks 0FAA "the closed embedding i : N' = Spec_X(Sym((N')^dual)) -> N = Spec_X(Sym(N^dual)) \
of the statement, for a short exact sequence of finite locally free modules of arbitrary ranks"]
theorem isClosedImmersion_subbundleEmbedding_of_shortExact :
    IsClosedImmersion (subbundleEmbedding N' N inc) := by
  have := isAffineHom_vectorBundleToBase X (dualSheaf E)
  have : IsSeparated (vectorBundleToBase X (dualSheaf E)) := IsSeparated.of_isAffineHom _
  have : IsClosedImmersion (vectorBundleOverZeroSection (dualSheaf E)).left :=
    Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section
      (vectorBundleToBase X (dualSheaf E)) _ (vectorBundleOverZeroSection_left_comp _)
  exact MorphismProperty.of_isPullback (isPullback_subbundleEmbedding N' N E inc pr w hseq).flip
    inferInstance

end Dual

section Flat

variable {X : Scheme.{u}} (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
  (hseq : (ShortComplex.mk inc pr w).ShortExact)
  (r' : ℕ) [hr' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']

/-- The dual of a finite locally free `𝒪_X`-module of rank `r` is finite locally free of rank
`r`. -/
instance isFiniteLocallyFreeOfRank_dualSheaf' (M : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf M) r :=
  isFiniteLocallyFreeOfRank_dualSheaf M r inferInstance

include hseq hr' in
/-- The morphism `q : N ⟶ 𝐕(ℰ^∨)` is flat. -/
theorem flat_vectorBundleMap_dualMap : Flat (vectorBundleMap X (dualMap pr)).left :=
  flat_vectorBundleMap_of_shortExact _ (dualShortComplex_shortExact N' N E inc pr w hseq) r'

include hseq hr' in
/-- The morphism `q : N ⟶ 𝐕(ℰ^∨)` is locally of finite type. -/
theorem locallyOfFiniteType_vectorBundleMap_dualMap :
    LocallyOfFiniteType (vectorBundleMap X (dualMap pr)).left :=
  locallyOfFiniteType_vectorBundleMap_of_shortExact _
    (dualShortComplex_shortExact N' N E inc pr w hseq) r'

include hseq hr' in
/-- The morphism `q : N ⟶ 𝐕(ℰ^∨)` has relative dimension the rank of `𝒩'`. -/
theorem relativeDimension_vectorBundleMap_dualMap :
    haveI := locallyOfFiniteType_vectorBundleMap_dualMap N' N E inc pr w hseq r'
    AlgebraicGeometry.RelativeDimension (vectorBundleMap X (dualMap pr)).left r' :=
  relativeDimension_vectorBundleMap_of_shortExact _
    (dualShortComplex_shortExact N' N E inc pr w hseq) r'

end Flat

/-! ### Pullback to a vector bundle and pushforward along a subbundle, on Chow groups -/

section Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The projection `p : 𝐕(ℰ^∨) ⟶ X` of the vector bundle of a module of rank `r` is locally of
finite type. -/
theorem locallyOfFiniteType_dualVectorBundleToBase (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    LocallyOfFiniteType (dualVectorBundleToBase E) :=
  locallyOfFiniteType_vectorBundleToBase (dualSheaf E) r

/-- The projection `p : 𝐕(ℰ^∨) ⟶ X` of the vector bundle of a module of rank `r` is flat. -/
theorem flat_dualVectorBundleToBase (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    Flat (dualVectorBundleToBase E) :=
  flat_vectorBundleToBase (dualSheaf E) r

/-- The projection `p : 𝐕(ℰ^∨) ⟶ X` of the vector bundle of a module of rank `r` has relative
dimension `r`. -/
theorem relativeDimension_dualVectorBundleToBase (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    haveI := locallyOfFiniteType_dualVectorBundleToBase E r
    AlgebraicGeometry.RelativeDimension (dualVectorBundleToBase E) r :=
  relativeDimension_vectorBundleToBase (dualSheaf E) r

/-- For a finite locally free `𝒪_X`-module `ℰ`, the composite `𝐕(ℰ^∨) ⟶ X ⟶ S` is locally of
finite type. -/
instance locallyOfFiniteType_dualVectorBundleToBase_comp (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    LocallyOfFiniteType (dualVectorBundleToBase E ≫ sX) :=
  haveI : LocallyOfFinitePresentation (dualVectorBundleToBase E) :=
    haveI := Stacks.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree (dualSheaf E)
    Stacks.SymAlgSections.locallyOfFinitePresentation_vectorBundleToBase (dualSheaf E)
  inferInstance

/-- **The flat pullback `p^* : A_k(X) ⟶ A_{k+r}(N)`** along the projection of the vector bundle
`N = 𝐕(𝒩^∨)` of a finite locally free module `𝒩` of rank `r` (Stacks 02S1). -/
def dualBundlePullback (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) :
    chowGroup C sX k →+ chowGroup C (dualVectorBundleToBase E ≫ sX) (k + r) :=
  haveI := locallyOfFiniteType_dualVectorBundleToBase E r
  haveI := flat_dualVectorBundleToBase E r
  flatPullbackChowOfRelativeDimension C _ sX (dualVectorBundleToBase E) rfl r
    (relativeDimension_dualVectorBundleToBase E r) k

end Chow

section RankOneFormula

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The line bundle `𝐕(ℒ^∨)`** of the dual of an invertible module, as a line-bundle situation
over `X`. -/
abbrev dualLineSituation (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Stacks.LineBundle.Situation.{u} where
  X := X
  S := X
  f := 𝟙 X
  L := dualSheaf L
  invertible := isInvertible_dualSheaf L

/-- Negation respects heterogeneous equality of Chow classes in equal degrees. -/
theorem heq_neg {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {a b : ℤ} (h : a = b)
    {x : chowGroup C sY a} {y : chowGroup C sY b} (hxy : x ≍ y) : -x ≍ -y := by
  subst h; cases hxy; rfl

variable (K N L : X.Modules) (m : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} K]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L]
  [hKm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} K m]
  [hNm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N (m + 1)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (inc : K ⟶ N) (pr : N ⟶ L) (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)


/-- The morphism `N ⟶ 𝐕(ℒ^∨) ⟶ Tot(ℒ^∨)`. -/
def toDualLine : dualVectorBundle N ⟶ (dualLineSituation L).totalSpace :=
  (vectorBundleMap X (dualMap pr)).left ≫ (dualLineSituation L).vectorBundleToTotalSpace

/-- The morphism from the vector bundle of a line-bundle situation to its total space is an open
immersion. -/
instance isOpenImmersion_vectorBundleToTotalSpace (D : Stacks.LineBundle.Situation.{u}) :
    IsOpenImmersion D.vectorBundleToTotalSpace :=
  haveI := Stacks.LineBundle.Situation.isIso_vectorBundleToTotalSpace D
  inferInstance

/-- The morphism from the vector bundle of a line-bundle situation to its total space is locally
of finite type. -/
instance locallyOfFiniteType_vectorBundleToTotalSpace (D : Stacks.LineBundle.Situation.{u}) :
    LocallyOfFiniteType D.vectorBundleToTotalSpace := by
  have := Stacks.LineBundle.Situation.isIso_vectorBundleToTotalSpace D
  exact inferInstance

include hseq hKm in
omit hNm [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] in
/-- The morphism `N ⟶ Tot(ℒ^∨)` is locally of finite type. -/
theorem locallyOfFiniteType_toDualLine : LocallyOfFiniteType (toDualLine N L pr) :=
  MorphismProperty.comp_mem @LocallyOfFiniteType _ _
    (locallyOfFiniteType_vectorBundleMap_dualMap K N L inc pr w hseq m) inferInstance

include hseq hKm in
omit hNm [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] in
/-- The morphism `N ⟶ Tot(ℒ^∨)` is flat. -/
theorem flat_toDualLine : Flat (toDualLine N L pr) :=
  MorphismProperty.comp_mem @Flat _ _ (flat_vectorBundleMap_dualMap K N L inc pr w hseq m)
    inferInstance

include hseq hKm in
omit hNm [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] in
/-- The morphism `N ⟶ Tot(ℒ^∨)` has relative dimension `m`, the rank of `𝒦`. -/
theorem relativeDimension_toDualLine :
    haveI := locallyOfFiniteType_toDualLine K N L m inc pr w hseq
    AlgebraicGeometry.RelativeDimension (toDualLine N L pr) m := by
  have := locallyOfFiniteType_vectorBundleMap_dualMap K N L inc pr w hseq m
  have := flat_vectorBundleMap_dualMap K N L inc pr w hseq m
  have hφ0 : AlgebraicGeometry.RelativeDimension
      (dualLineSituation L).vectorBundleToTotalSpace 0 :=
    have := Stacks.LineBundle.Situation.isIso_vectorBundleToTotalSpace (dualLineSituation L)
    (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero _).mp inferInstance
  have h := AlgebraicGeometry.RelativeDimension.comp_of_flat
    (vectorBundleMap X (dualMap pr)).left (dualLineSituation L).vectorBundleToTotalSpace
    (relativeDimension_vectorBundleMap_dualMap K N L inc pr w hseq m) hφ0
  exact h

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] in
/-- The composite `N ⟶ Tot(ℒ^∨) ⟶ X` is the projection `p : N ⟶ X`. -/
theorem toDualLine_comp_totalSpaceToBase :
    toDualLine N L pr ≫ (dualLineSituation L).totalSpaceToBase = dualVectorBundleToBase N :=
  (Category.assoc (vectorBundleMap X (dualMap pr)).left
      (dualLineSituation L).vectorBundleToTotalSpace (dualLineSituation L).totalSpaceToBase).trans
    ((congrArg ((vectorBundleMap X (dualMap pr)).left ≫ ·)
      (dualLineSituation L).vectorBundleToTotalSpace_comp_totalSpaceToBase).trans
        (vectorBundleMap_left_comp X (dualMap pr)))

include hseq in
omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1] in
/-- The subbundle `N' = 𝐕(𝒦^∨)` is the fibre of `N ⟶ Tot(ℒ^∨)` over the zero section of
`Tot(ℒ^∨)`. -/
theorem isPullback_toDualLine :
    IsPullback (dualVectorBundleToBase K) (subbundleEmbedding K N inc)
      (dualLineSituation L).zeroSection (toDualLine N L pr) := by
  have := Stacks.LineBundle.Situation.isIso_vectorBundleToTotalSpace (dualLineSituation L)
  refine (isPullback_subbundleEmbedding K N L inc pr w hseq).flip.of_iso (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (asIso (dualLineSituation L).vectorBundleToTotalSpace) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Stacks.LineBundle.Situation.vectorBundleOverZeroSection_comp_vectorBundleToTotalSpace
      (dualLineSituation L)).trans (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

/-- **Stacks 0FAA when the quotient is invertible.** For `0 ⟶ 𝒦 ⟶ 𝒩 ⟶ ℒ ⟶ 0` short exact with `ℒ`
invertible, `𝒦` of rank `m` and `𝒩` of rank `m + 1`, and `α ∈ A_{k+1}(X)`,

  `i_* (p')^* α = p^*(c₁(ℒ) ∩ α)`  in  `A_{k+1+m}(N)`. -/
theorem subbundleEmbedding_pushforward_flatPullback_of_rank_one (k : ℤ)
    (α : chowGroup C sX (k + 1)) :
    haveI := isClosedImmersion_subbundleEmbedding_of_shortExact K N L inc pr w hseq
    chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase K ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding K N inc)
        (subbundleEmbedding_comp_base K N sX inc) (k + 1 + m)
        (dualBundlePullback C sX K m (k + 1) α) ≍
      dualBundlePullback C sX N (m + 1) (k + 1 - 1)
        (GenuineChern.chernCap C 1 sX L (k + 1) (Fin.last 1) α) := by
  have := isClosedImmersion_subbundleEmbedding_of_shortExact K N L inc pr w hseq
  have := locallyOfFiniteType_dualVectorBundleToBase K m
  have := flat_dualVectorBundleToBase K m
  have := locallyOfFiniteType_dualVectorBundleToBase N (m + 1)
  have := flat_dualVectorBundleToBase N (m + 1)
  have := Stacks.LineBundle.Situation.flat_totalSpaceToBase (dualLineSituation L)
  have := locallyOfFiniteType_toDualLine K N L m inc pr w hseq
  have := flat_toDualLine K N L m inc pr w hseq
  have hqD := relativeDimension_toDualLine K N L m inc pr w hseq
  have hsq := isPullback_toDualLine K N L inc pr w hseq
  have hbase := toDualLine_comp_totalSpaceToBase N L pr
  have hg : toDualLine N L pr ≫ (dualLineSituation L).totalSpaceToBase ≫ sX =
      dualVectorBundleToBase N ≫ sX :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ sX) hbase)
  -- Stacks 02RG for the cartesian square over the zero section
  have e1 := flatPullbackChow_properChowPushforward_unconditional C sX
    ((dualLineSituation L).totalSpaceToBase ≫ sX) (dualVectorBundleToBase K ≫ sX)
    (dualVectorBundleToBase N ≫ sX) (dualLineSituation L).zeroSection (toDualLine N L pr)
    (dualVectorBundleToBase K) (subbundleEmbedding K N inc) hsq
    (zeroSection_comp_totalSpaceToBase_comp C (dualLineSituation L) sX) hg rfl m hqD (k + 1) α
  -- Stacks 0F96 (5) for the line bundle of `ℒ^∨`
  have e2 := zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow C
    (dualLineSituation L) sX k α
  have := isInvertible_dualSheaf L
  -- `c₁(ℒ^∨) = -c₁(ℒ)`
  have e3 := firstChernClassCapChow_dualSheaf L C sX k α
  -- the composite of the two flat pullbacks
  have e5 := flatPullbackChow_comp C (dualVectorBundleToBase N ≫ sX)
    ((dualLineSituation L).totalSpaceToBase ≫ sX) sX (toDualLine N L pr)
    (dualLineSituation L).totalSpaceToBase hg rfl m 1 hqD
    (dualLineSituation L).relativeDimension_totalSpaceToBase k
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _)
    (flatPullbackDescends C _ _ _ _ _ _ _) (firstChernClassCapChow C k sX L α)
  -- the genuine first Chern class of `ℒ` is the cap with `ℒ`
  have e6 : GenuineChern.chernCap C 1 sX L (k + 1) (Fin.last 1) α ≍
      firstChernClassCapChow C k sX L α := by
    have h := GenuineChern.chernCap_one_eq_invCap C sX L (k + 1) α
    refine (heq_of_eq h).trans ?_
    exact heq_apply_of_degree C sX sX (fun d => d + 1) (fun d => d)
      (fun d => firstChernClassCapChow C d sX L) (by omega)
      (chowGroupCast_heq C sX _ α)
  refine HEq.trans (heq_of_eq e1.symm) ?_
  have e4 : properChowPushforward C sX ((dualLineSituation L).totalSpaceToBase ≫ sX)
      (dualLineSituation L).zeroSection
      (zeroSection_comp_totalSpaceToBase_comp C (dualLineSituation L) sX) (k + 1)
      (properPushforwardDescends C _ _ _ _ _) α =
    chowGroupCast C ((dualLineSituation L).totalSpaceToBase ≫ sX)
        (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
        (flatPullbackChowOfRelativeDimension C ((dualLineSituation L).totalSpaceToBase ≫ sX) sX
          (dualLineSituation L).totalSpaceToBase rfl 1
          (dualLineSituation L).relativeDimension_totalSpaceToBase k
          (firstChernClassCapChow C k sX L α)) := by
    refine e2.trans ?_
    rw [e3, map_neg, map_neg, neg_neg]
  rw [e4]
  refine (flatPullbackChow_heq_of_degree C _ _ (toDualLine N L pr) hg m hqD
    (show k + 1 = k + ((1 : ℕ) : ℤ) by simp) _ (flatPullbackDescends C _ _ _ _ _ _ _)
    (chowGroupCast_heq C _ _ _)).trans ?_
  refine e5.trans ?_
  exact flatPullbackChow_heq_congr C _ sX _ (dualVectorBundleToBase N) _ rfl hbase
    (show m + 1 = m + 1 from rfl) _ (relativeDimension_dualVectorBundleToBase N (m + 1))
    (by omega) _ (flatPullbackDescends C _ _ _ _ _ _ _) _ _ e6.symm

end RankOneFormula

end Stacks.Chow

end
