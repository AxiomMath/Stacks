module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleChowInjective
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleInjectiveLine
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.SplittingTowerRecovery
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundlePoints
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceVectorBundle
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# Flat pullback along a vector bundle is an isomorphism on Chow groups

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S`, let `ℰ` be a
finite locally free `𝒪_X`-module of rank `r` and let `p : E = \underline{\Spec}(\Sym^*(ℰ)) ⟶ X`
be the associated vector bundle. Then

  `p^* : A_k(X) ⟶ A_{k+r}(E)`

is an isomorphism for every `k` ([Stacks, Tag 02TY]).

Surjectivity is [Stacks, Tag 02TT], `p` being Zariski locally on `X` the projection
`𝔸^r_U ⟶ U`. Injectivity is proved by induction on the rank. In rank zero `p` is an isomorphism,
and in rank one `E` is a line bundle, for which injectivity is the zero-section argument of
[Stacks, Tag 0B74]. For the inductive step let `ℰ` have rank `m + 2` and let
`π : P = 𝐏(ℰ^∨) ⟶ X` be the projective bundle of the dual. The tautological sequence
`0 ⟶ 𝒦 ⟶ π^*ℰ^∨ ⟶ 𝒪_P(1) ⟶ 0` dualizes to

  `0 ⟶ 𝒪_P(-1) ⟶ π^*ℰ ⟶ 𝒦^∨ ⟶ 0`,

so `𝐕(𝒦^∨) ⊆ 𝐕(π^*ℰ)` is a relative effective Cartier divisor over `P`, and by [Stacks, Tag 02TR]
injectivity of flat pullback along `𝐕(𝒦^∨) ⟶ P`, which is the induction hypothesis, gives
injectivity along `𝐕(π^*ℰ) ⟶ P`
(`Stacks.Chow.flatPullbackChow_injective_vectorBundleToBase_of_line`). Flat pullback along `π` is
injective by the projective space bundle formula [Stacks, Tag 02TX]. Finally
`𝐕(π^*ℰ) = E ×_X P`, so the composite `𝐕(π^*ℰ) ⟶ P ⟶ X` is also `𝐕(π^*ℰ) ⟶ E ⟶ X`, and by
[Stacks, Tag 02RD] its injective flat pullback factors through `p^*`.

This replaces the source's projective completion `𝐏(ℰ ⊕ 𝒪_X) ⊇ E` by the splitting construction;
the inputs are the same results of the chapter: 02TT, 02TX, 02TR, 02RD and 0B74.

## Main results

* `Stacks.Chow.flatPullbackChow_injective_vectorBundleToBase` — injectivity of `p^*` in every rank.
* `Stacks.Chow.flatPullbackChow_bijective_vectorBundleToBase` — **[Stacks, Tag 02TY]**.
* `Stacks.Chow.vectorBundleFlatPullbackChowEquiv` — `p^*` as an isomorphism of groups.

## References

* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 0B74](https://stacks.math.columbia.edu/tag/0B74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-! ### Two transport lemmas -/

/-- **Injectivity of flat pullback descends along a factorization.** If `p = f ≫ g` with `f`, `g`
flat of relative dimensions `r`, `s`, and `p^*` is injective in degree `k`, then so is `g^*`: by
Stacks 02RD, `p^* = f^* ∘ g^*` up to the transport of degrees. -/
theorem flatPullbackChow_injective_of_comp_eq_of_injective (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (g : Y ⟶ Z) [LocallyOfFiniteType g] [Flat g]
    (p : X ⟶ Z) [LocallyOfFiniteType p] [Flat p] (hp : f ≫ g = p)
    (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) (hpbase : p ≫ sZ = sX)
    (r s t : ℕ) (ht : t = r + s)
    (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s)
    (hpt : AlgebraicGeometry.RelativeDimension p t) (k : ℤ)
    (hfacf : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hfbase r hf (k + (s : ℤ)))
    (hfacg : FlatPullbackFactorsThroughRationalEquivalence C sY sZ g hgbase s hg k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C sX sZ p hpbase t hpt k)
    (hinjp : Function.Injective (flatPullbackChow C sX sZ p hpbase t hpt k hfacp)) :
    Function.Injective (flatPullbackChow C sY sZ g hgbase s hg k hfacg) := by
  subst hp ht
  exact fun α β hab => hinjp <| eq_of_heq <|
    (flatPullbackChow_comp C sX sY sZ f g hfbase hgbase r s hf hg k hfacf hfacg hfacp
      α).symm.trans
    ((heq_of_eq (congrArg _ hab)).trans
      (flatPullbackChow_comp C sX sY sZ f g hfbase hgbase r s hf hg k hfacf hfacg hfacp β))

/-- **Injectivity of flat pullback along `𝐕(ℰ) ⟶ Y` depends only on the isomorphism class of
`ℰ`.** An isomorphism `ℰ ≅ ℰ'` of quasi-coherent modules induces an isomorphism
`𝐕(ℰ') ≅ 𝐕(ℰ)` over `Y`. -/
theorem flatPullbackChow_injective_vectorBundleToBase_of_iso {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {E E' : Y.Modules} [E.IsQuasicoherent] [E'.IsQuasicoherent]
    (e : E ≅ E') (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' n] (k : ℤ)
    (hE : letI := locallyOfFiniteType_vectorBundleToBase E n
      letI := flat_vectorBundleToBase E n
      Function.Injective (flatPullbackChowOfRelativeDimension C
        (Scheme.Modules.vectorBundleToBase Y E ≫ sY) sY (Scheme.Modules.vectorBundleToBase Y E)
        rfl n (relativeDimension_vectorBundleToBase E n) k)) :
    letI := locallyOfFiniteType_vectorBundleToBase E' n
    letI := flat_vectorBundleToBase E' n
    Function.Injective (flatPullbackChowOfRelativeDimension C
      (Scheme.Modules.vectorBundleToBase Y E' ≫ sY) sY (Scheme.Modules.vectorBundleToBase Y E')
      rfl n (relativeDimension_vectorBundleToBase E' n) k) := by
  have := locallyOfFiniteType_vectorBundleToBase E n
  have := flat_vectorBundleToBase E n
  have := locallyOfFiniteType_vectorBundleToBase E' n
  have := flat_vectorBundleToBase E' n
  have hiso : IsIso (Scheme.Modules.vectorBundleMap Y e.hom) :=
    ⟨⟨Scheme.Modules.vectorBundleMap Y e.inv,
      (Scheme.Modules.vectorBundleMap_comp Y e.inv e.hom).symm.trans
        ((congrArg (Scheme.Modules.vectorBundleMap Y) e.inv_hom_id).trans
          (Scheme.Modules.vectorBundleMap_id Y)),
      (Scheme.Modules.vectorBundleMap_comp Y e.hom e.inv).symm.trans
        ((congrArg (Scheme.Modules.vectorBundleMap Y) e.hom_inv_id).trans
          (Scheme.Modules.vectorBundleMap_id Y))⟩⟩
  have : IsIso (Scheme.Modules.vectorBundleMap Y e.hom).left :=
    inferInstanceAs (IsIso ((Over.forget Y).map (Scheme.Modules.vectorBundleMap Y e.hom)))
  have hp := Scheme.Modules.vectorBundleMap_left_comp Y e.hom
  exact flatPullbackChow_injective_of_isIso_comp C _ (Scheme.Modules.vectorBundleToBase Y E ≫ sY)
    sY (Scheme.Modules.vectorBundleMap Y e.hom).left (Scheme.Modules.vectorBundleToBase Y E)
    (Scheme.Modules.vectorBundleToBase Y E') hp (by rw [← Category.assoc, hp]) rfl rfl n
    (relativeDimension_vectorBundleToBase E n) (relativeDimension_vectorBundleToBase E' n) k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) hE

/-! ### Rank one -/

/-- **Injectivity of flat pullback along a vector bundle of rank one.** A finite locally free
module of rank one is invertible, its vector bundle is the total space of the corresponding line
bundle (`Stacks.LineBundle.Situation.totalSpaceIsoVectorBundle`), and there injectivity is the
zero-section argument of [Stacks, Tag 0B74]. -/
theorem flatPullbackChow_injective_vectorBundleToBase_one {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (E : Y.Modules) [E.IsQuasicoherent]
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 1] (k : ℤ) :
    letI := locallyOfFiniteType_vectorBundleToBase E 1
    letI := flat_vectorBundleToBase E 1
    Function.Injective (flatPullbackChowOfRelativeDimension C
      (Scheme.Modules.vectorBundleToBase Y E ≫ sY) sY (Scheme.Modules.vectorBundleToBase Y E)
      rfl 1 (relativeDimension_vectorBundleToBase E 1) k) := by
  have := locallyOfFiniteType_vectorBundleToBase E 1
  have := flat_vectorBundleToBase E 1
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      Y.ringCatSheaf.property E :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      ((Stacks.SheafOfModules.Scheme.isInvertible_iff_isFiniteLocallyFreeOfRank_one Y E).mpr hE)
  let D : Stacks.LineBundle.Situation.{u} := { X := Y, S := Y, f := 𝟙 Y, L := E }
  have := Stacks.LineBundle.Situation.flat_totalSpaceToBase D
  have hp : D.totalSpaceIsoVectorBundle.inv ≫ D.totalSpaceToBase =
      Scheme.Modules.vectorBundleToBase Y E :=
    D.totalSpaceIsoVectorBundle_inv_comp_totalSpaceToBase
  exact flatPullbackChow_injective_of_isIso_comp C _ (D.totalSpaceToBase ≫ sY) sY
    D.totalSpaceIsoVectorBundle.inv D.totalSpaceToBase (Scheme.Modules.vectorBundleToBase Y E) hp
    (by rw [← Category.assoc, hp]) rfl rfl 1 D.relativeDimension_totalSpaceToBase
    (relativeDimension_vectorBundleToBase E 1) k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackChow_totalSpaceToBase_injective C D sY D.relativeDimension_totalSpaceToBase k _)

/-! ### The inductive step -/

/-- A module that is finite locally free of rank `n` and its dual are finite locally free, and the
dual is quasi-coherent. -/
private theorem isFiniteLocallyFree_and_dualSheaf_isQuasicoherent {Y : Scheme.{u}} (M : Y.Modules)
    (n : ℕ) [hM : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M n] :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} M ∧
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf M) ∧
      (dualSheaf M).IsQuasicoherent :=
  have := isFiniteLocallyFreeOfRank_dualSheaf M n hM
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (dualSheaf M) n
  ⟨hM.isFiniteLocallyFree M n, this,
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _⟩

/-- **The inductive step.** Let `ℰ` be finite locally free of rank `m + 2` on `Y`, and let `D` be a
layer `π : P ⟶ Y` of the splitting tower for the dual `ℰ^∨`: a flat proper morphism with
injective flat pullback, carrying a tautological sequence `0 ⟶ 𝒦 ⟶ π^*ℰ^∨ ⟶ 𝒪_P(1) ⟶ 0` with `𝒦`
of rank `m + 1`. If flat pullback along every vector bundle of rank `m + 1` is injective, then
flat pullback along `𝐕(ℰ) ⟶ Y` is injective.

The dual sequence `0 ⟶ 𝒪_P(1)^∨ ⟶ (π^*ℰ^∨)^∨ ⟶ 𝒦^∨ ⟶ 0` exhibits an invertible subsheaf with
locally free quotient of rank `m + 1`, so the induction hypothesis for `𝒦^∨` and Stacks 02TR give
injectivity along `𝐕((π^*ℰ^∨)^∨) ⟶ P`; and `(π^*ℰ^∨)^∨ ≅ π^*ℰ^∨∨ ≅ π^*ℰ`. Then
`𝐕(π^*ℰ) = 𝐕(ℰ) ×_Y P`, and the two factorizations of `𝐕(π^*ℰ) ⟶ Y` conclude. -/
theorem flatPullbackChow_injective_vectorBundleToBase_of_bundleStep (m : ℕ)
    (ih : ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (E : Y.Modules)
      [E.IsQuasicoherent] [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1)]
      (k : ℤ),
      letI := locallyOfFiniteType_vectorBundleToBase E (m + 1)
      letI := flat_vectorBundleToBase E (m + 1)
      Function.Injective (flatPullbackChowOfRelativeDimension C
        (Scheme.Modules.vectorBundleToBase Y E ≫ sY) sY (Scheme.Modules.vectorBundleToBase Y E)
        rfl (m + 1) (relativeDimension_vectorBundleToBase E (m + 1)) k))
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (E : Y.Modules)
    [E.IsQuasicoherent] [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1)]
    (D : BundleStep C sY (dualSheaf E) (m + 1)) (k : ℤ) :
    letI := locallyOfFiniteType_vectorBundleToBase E (m + 1 + 1)
    letI := flat_vectorBundleToBase E (m + 1 + 1)
    Function.Injective (flatPullbackChowOfRelativeDimension C
      (Scheme.Modules.vectorBundleToBase Y E ≫ sY) sY (Scheme.Modules.vectorBundleToBase Y E)
      rfl (m + 1 + 1) (relativeDimension_vectorBundleToBase E (m + 1 + 1)) k) := by
  have := locallyOfFiniteType_vectorBundleToBase E (m + 1 + 1)
  have := flat_vectorBundleToBase E (m + 1 + 1)
  have hEd := isFiniteLocallyFreeOfRank_dualSheaf E (m + 1 + 1) ‹_›
  obtain ⟨_, _, _⟩ := isFiniteLocallyFree_and_dualSheaf_isQuasicoherent E (m + 1 + 1)
  -- the three terms of the tautological sequence on `P` and their duals
  set G := (Scheme.Modules.pullback D.π).obj (dualSheaf E)
  have hGr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} G (m + 1 + 1) :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback D.π (dualSheaf E) (m + 1 + 1)
  have hLr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.twistModule 1 :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible _
      D.twistModule_isInvertible
  have hKr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} D.sub (m + 1) := D.sub_rank
  have hGd := isFiniteLocallyFreeOfRank_dualSheaf G (m + 1 + 1) hGr
  have hLd := isFiniteLocallyFreeOfRank_dualSheaf D.twistModule 1 hLr
  have hKd := isFiniteLocallyFreeOfRank_dualSheaf D.sub (m + 1) hKr
  obtain ⟨_, _, _⟩ := isFiniteLocallyFree_and_dualSheaf_isQuasicoherent G (m + 1 + 1)
  obtain ⟨_, _, _⟩ := isFiniteLocallyFree_and_dualSheaf_isQuasicoherent D.twistModule 1
  obtain ⟨_, _, _⟩ := isFiniteLocallyFree_and_dualSheaf_isQuasicoherent D.sub (m + 1)
  obtain ⟨w', hS'⟩ := exists_dualSheaf_shortExact D.incl D.quot D.incl_comp_quot
    D.shortExact.mono_f D.shortExact.epi_g D.shortExact.exact
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree D.sub)
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree G)
    (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree D.twistModule)
  -- injectivity along `𝐕((π^*ℰ^∨)^∨) ⟶ P`
  have hinjG : ∀ j : ℤ,
      let := locallyOfFiniteType_vectorBundleToBase (dualSheaf G) (m + 1 + 1)
      let := flat_vectorBundleToBase (dualSheaf G) (m + 1 + 1)
      Function.Injective (flatPullbackChowOfRelativeDimension C
        (Scheme.Modules.vectorBundleToBase D.P (dualSheaf G) ≫ D.sP) D.sP
        (Scheme.Modules.vectorBundleToBase D.P (dualSheaf G)) rfl (m + 1 + 1)
        (relativeDimension_vectorBundleToBase (dualSheaf G) (m + 1 + 1)) j) := fun j =>
    flatPullbackChow_injective_vectorBundleToBase_of_line C D.sP (dualMap D.quot)
      (dualMap D.incl) w' hS' (m + 1) (fun i => ih D.sP (dualSheaf D.sub) i) j
  -- `(π^*ℰ^∨)^∨ ≅ π^*ℰ`
  set N := (Scheme.Modules.pullback D.π).obj E
  have hNr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N (m + 1 + 1) :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback D.π E (m + 1 + 1)
  have := isIso_toDoubleDual_of_isFiniteLocallyFree E
  let e₂ : (Scheme.Modules.pullback D.π).obj (dualSheaf (dualSheaf E)) ≅ dualSheaf G :=
    @asIso _ _ _ _ (pullbackDualMap D.π (dualSheaf E))
      (pullbackDualMap_isIso D.π (dualSheaf E)
        (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ (m + 1 + 1)))
  let eN : N ≅ dualSheaf G :=
    (Scheme.Modules.pullback D.π).mapIso (asIso (toDoubleDual E)) ≪≫ e₂
  have hinjN : ∀ j : ℤ,
      let := locallyOfFiniteType_vectorBundleToBase N (m + 1 + 1)
      let := flat_vectorBundleToBase N (m + 1 + 1)
      Function.Injective (flatPullbackChowOfRelativeDimension C
        (Scheme.Modules.vectorBundleToBase D.P N ≫ D.sP) D.sP
        (Scheme.Modules.vectorBundleToBase D.P N) rfl (m + 1 + 1)
        (relativeDimension_vectorBundleToBase N (m + 1 + 1)) j) := fun j =>
    flatPullbackChow_injective_vectorBundleToBase_of_iso C D.sP eN.symm (m + 1 + 1) j (hinjG j)
  -- the base-change square `𝐕(π^*ℰ) = 𝐕(ℰ) ×_Y P`
  have := locallyOfFiniteType_vectorBundleToBase N (m + 1 + 1)
  have := flat_vectorBundleToBase N (m + 1 + 1)
  have hsq := Scheme.Modules.isPullback_vectorBundleBaseChangeMap D.π E
  set q := Scheme.Modules.vectorBundleBaseChangeMap D.π E
  have : Flat q := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hqr : AlgebraicGeometry.RelativeDimension q (m + 1) :=
    RelativeDimension.of_isPullback hsq.flip D.relDim
  -- the composite `𝐕(π^*ℰ) ⟶ P ⟶ Y` has injective flat pullback
  have hcomp : Scheme.Modules.vectorBundleToBase D.P N ≫ D.π =
      q ≫ Scheme.Modules.vectorBundleToBase Y E := hsq.w.symm
  have hinjc := flatPullbackChow_injective_of_comp_eq C
    (Scheme.Modules.vectorBundleToBase D.P N ≫ D.sP) D.sP sY
    (Scheme.Modules.vectorBundleToBase D.P N) D.π
    (Scheme.Modules.vectorBundleToBase D.P N ≫ D.π) rfl rfl D.hsP
    (by rw [Category.assoc, D.hsP]) (m + 1 + 1) (m + 1) ((m + 1 + 1) + (m + 1)) rfl
    (relativeDimension_vectorBundleToBase N (m + 1 + 1)) D.relDim
    (AlgebraicGeometry.RelativeDimension.comp_of_flat _ _
      (relativeDimension_vectorBundleToBase N (m + 1 + 1)) D.relDim) k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) (D.hfac k)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (hinjN _) (D.injective_pullbackChow k)
  exact flatPullbackChow_injective_of_comp_eq_of_injective C
    (Scheme.Modules.vectorBundleToBase D.P N ≫ D.sP)
    (Scheme.Modules.vectorBundleToBase Y E ≫ sY) sY q (Scheme.Modules.vectorBundleToBase Y E)
    (Scheme.Modules.vectorBundleToBase D.P N ≫ D.π) hcomp.symm
    (by rw [← Category.assoc, ← hcomp, Category.assoc, D.hsP]) rfl
    (by rw [Category.assoc, D.hsP]) (m + 1) (m + 1 + 1) ((m + 1 + 1) + (m + 1)) (by ring)
    hqr (relativeDimension_vectorBundleToBase E (m + 1 + 1))
    (AlgebraicGeometry.RelativeDimension.comp_of_flat _ _
      (relativeDimension_vectorBundleToBase N (m + 1 + 1)) D.relDim) k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) hinjc

/-! ### Every rank -/

/-- **Flat pullback along a vector bundle is injective on Chow groups**, in every rank: for `ℰ`
finite locally free of rank `r` on `Y`, `p^* : A_k(Y) ⟶ A_{k+r}(𝐕(ℰ))` is
injective. The injectivity half of [Stacks, Tag 02TY]. -/
theorem flatPullbackChow_injective_vectorBundleToBase (r : ℕ) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (E : Y.Modules) [E.IsQuasicoherent]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) :
    letI := locallyOfFiniteType_vectorBundleToBase E r
    letI := flat_vectorBundleToBase E r
    Function.Injective (flatPullbackChowOfRelativeDimension C
      (Scheme.Modules.vectorBundleToBase Y E ≫ sY) sY (Scheme.Modules.vectorBundleToBase Y E)
      rfl r (relativeDimension_vectorBundleToBase E r) k) := by
  induction r generalizing Y k with
  | zero =>
    exact (flatPullbackChow_bijective_vectorBundleToBase_zero C sY E k).1
  | succ n ih =>
    cases n with
    | zero => exact flatPullbackChow_injective_vectorBundleToBase_one C sY E k
    | succ m =>
      have hEd := isFiniteLocallyFreeOfRank_dualSheaf E (m + 1 + 1) ‹_›
      exact flatPullbackChow_injective_vectorBundleToBase_of_bundleStep C m
        (fun sY' _ E' _ _ j => ih sY' E' j) sY E (projectiveBundleStep C sY (dualSheaf E) m hEd) k

/-- **[Stacks, Tag 02TY].** Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type
over `S`, let `ℰ` be a finite locally free `𝒪_X`-module of rank `r` and let
`p : E = \underline{\Spec}(\Sym^*(ℰ)) ⟶ X` be the associated vector bundle. Then

  `p^* : A_k(X) ⟶ A_{k+r}(E)`

is an isomorphism for every `k`.

Surjectivity is [Stacks, Tag 02TT] for the affine-space bundle `p`; injectivity is
`Stacks.Chow.flatPullbackChow_injective_vectorBundleToBase`. The instance `[E.IsQuasicoherent]`,
which the construction of `𝐕(ℰ)` takes, restricts nothing: a finite locally free module is
quasi-coherent, by
`Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree`, and the
instance is a proposition. -/
@[stacks 02TY]
theorem flatPullbackChow_bijective_vectorBundleToBase {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) :
    letI := locallyOfFiniteType_vectorBundleToBase E r
    letI := flat_vectorBundleToBase E r
    Function.Bijective (flatPullbackChowOfRelativeDimension C
      (Scheme.Modules.vectorBundleToBase X E ≫ sX) sX (Scheme.Modules.vectorBundleToBase X E)
      rfl r (relativeDimension_vectorBundleToBase E r) k) :=
  have := locallyOfFiniteType_vectorBundleToBase E r
  have := flat_vectorBundleToBase E r
  ⟨flatPullbackChow_injective_vectorBundleToBase C r sX E k,
    flatPullbackChow_surjective_isAffineSpaceBundle C sX (Scheme.Modules.vectorBundleToBase X E) r
      (relativeDimension_vectorBundleToBase E r) (isAffineSpaceBundle_vectorBundleToBase E r) k⟩

/-- The flat pullback `p^* : A_k(X) ≃+ A_{k+r}(E)` along a vector bundle of rank `r`, as an
isomorphism of groups ([Stacks, Tag 02TY]). -/
def vectorBundleFlatPullbackChowEquiv {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ) :
    letI := locallyOfFiniteType_vectorBundleToBase E r
    chowGroup C sX k ≃+ chowGroup C (Scheme.Modules.vectorBundleToBase X E ≫ sX) (k + (r : ℤ)) :=
  have := locallyOfFiniteType_vectorBundleToBase E r
  have := flat_vectorBundleToBase E r
  AddEquiv.ofBijective _ (flatPullbackChow_bijective_vectorBundleToBase C sX E r k)

end Stacks.Chow

end
