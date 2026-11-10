module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass.Regularity
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapLocallyFinite
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlatGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleFlatGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.CarrierAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ComapBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.CapProduct
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf

/-!
# Chern classes and sections: the class of a subbundle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let

  `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`

be a short exact sequence of finite locally free `𝒪_X`-modules. Dualising and taking relative
spectra of symmetric algebras gives the vector bundles `N' = Spec_X(Sym((𝒩')^∨))` and
`N = Spec_X(Sym(𝒩^∨))` with their projections `p' : N' ⟶ X` and `p : N ⟶ X`, and the closed
embedding `i : N' ⟶ N` over `X` (`StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass` and
`Stacks.Chow.subbundleEmbedding_isClosedImmersion_of_shortExact`).
[Stacks, Tag 0FAA] says that for `α ∈ CH_k(X)`

  `i_*(p')^*α = p^*(c_top(ℰ) ∩ α)`.

This file proves it for modules of constant ranks `r'`, `r` and `e`, where `c_top(ℰ) = c_e(ℰ)`. The
statement for modules of arbitrary rank is
`Stacks.Chow.subbundleEmbeddingRestrict_pushforward_flatPullback_eq_topChernCap`, in
`StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChernClass.ArbitraryRank`.

## Main results

* `Stacks.Chow.flatPullback_apply_eq_finsum` — the flat pullback of a cycle on its canonical
  presentation.
* `Stacks.Chow.subbundleComapIso` — `(p')⁻¹ Y = N' ∩ p⁻¹ Y`.
* `Stacks.Chow.chernCap_comap_fundamentalCycle_eq_subbundle` — [Stacks, Tag 0FA9] on `p⁻¹ Y`.
* `Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_heq_chernCap` —
  `i_*(p')^*α = c_e(p^*ℰ) ∩ p^*α`.
* `Stacks.Chow.subbundleEmbedding_pushforward_flatPullback_eq_chernCap_of_point` —
  [Stacks, Tag 0FAA] for modules of constant rank.

## Implementation notes

The ranks of `𝒩'`, `𝒩` and `ℰ` are taken constant, which is the case the source reduces to in
the first line of its proof: `c_top(ℰ)` is assembled from the Chern classes of the restrictions of
`ℰ` to the open and closed loci where its rank is constant (Stacks 0FA4,
`Stacks.Chow.topChernTotalClass`), and on such a locus `c_top(ℰ) = c_e(ℰ)`. The cap product with
`c_e(ℰ)` is `Stacks.Chow.GenuineChern.chernCap`, the operation of the Chern class of
[Stacks, Tag 0B7H] on `CH_*(X)`.

The two sides of the identity lie in `CH_{k+r'}(N)` and `CH_{(k-e)+r}(N)`, which are the same
group because `r = r' + e`. That equation is read off the short exact sequence at a point of `X`
(`Stacks.Chow.subbundleDegree_eq`), so a point of `X` is an argument of the statement; on an empty
scheme both groups are zero.

## References

* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 0FA9](https://stacks.math.columbia.edu/tag/0FA9)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### The projections of the vector bundles -/

section Projection

variable {X : Scheme.{u}} (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]

/-- The projection `p : 𝐕(𝒩^∨) ⟶ X` of the vector bundle of a finite locally free module of
constant rank is locally of finite type. -/
theorem dualVectorBundleToBase_locallyOfFiniteType (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r] :
    LocallyOfFiniteType (dualVectorBundleToBase N) :=
  locallyOfFiniteType_vectorBundleToBase (dualSheaf N) r

/-- The projection `p : 𝐕(𝒩^∨) ⟶ X` of the vector bundle of a finite locally free module of
constant rank is flat. -/
theorem dualVectorBundleToBase_flat (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r] :
    Flat (dualVectorBundleToBase N) :=
  flat_vectorBundleToBase (dualSheaf N) r

/-- The projection `p : 𝐕(𝒩^∨) ⟶ X` of the vector bundle of a finite locally free module of
constant rank `r` has relative dimension `r`. -/
theorem dualVectorBundleToBase_relativeDimension (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r] :
    letI := dualVectorBundleToBase_locallyOfFiniteType N r
    AlgebraicGeometry.RelativeDimension (dualVectorBundleToBase N) r :=
  relativeDimension_vectorBundleToBase (dualSheaf N) r

end Projection

/-! ### Flat pullback of the canonical presentation of a cycle -/

section Presentation

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
  (hf : f ≫ sX = sX') (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension f d)

/-- **The flat pullback of a cycle, on its canonical presentation.** Writing a `k`-cycle as the
locally finite sum `∑ₓ nₓ [Yₓ]` over the points of its support, with `Yₓ` the integral closed
subscheme with generic point `x`, its flat pullback along `f` is `∑ₓ nₓ [f⁻¹ Yₓ]`. -/
theorem flatPullback_apply_eq_finsum (k : ℤ) (c : CycleGroup C sX k) (y : X') :
    (flatPullback C sX' sX f hf d hd k c).1 y =
      ∑ᶠ x : cycleSupportIndex c, c.1 x.1 *
        (cycleAssociatedToClosedSubscheme C sX'
          (pullback.fst f (integralComponentAt x.1).subschemeι) (k + (d : ℤ))).1 y := by
  have hterm : ∀ x : cycleSupportIndex c,
      (cycleAssociatedToClosedSubscheme C sX'
        (pullback.fst f (integralComponentAt x.1).subschemeι) (k + (d : ℤ))).1 y =
      (cycleAssociatedToClosedSubscheme C sX (integralComponentAt x.1).subschemeι k).1
          (f.base y) * flatPullbackWeight C sX' f (k + (d : ℤ)) y := by
    intro x
    have := isIntegral_integralComponentAt x.1
    rw [← flatPullback_cycleAssociatedToClosedSubscheme C sX' sX f hf d hd k
      (integralComponentAt x.1).subschemeι (schemeDeltaDimension_cycleSupportIndex c x),
      flatPullback_apply]
  rw [flatPullback_apply]
  simp_rw [hterm]
  by_cases hy : c.1 (f.base y) = 0
  · rw [hy, zero_mul, eq_comm]
    refine finsum_eq_zero_of_forall_eq_zero fun x ↦ ?_
    have hne : f.base y ≠ x.1 := fun h ↦ x.2 (h ▸ hy)
    rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sX k x.1 hne]
    ring
  · rw [finsum_eq_single _ (⟨f.base y, hy⟩ : cycleSupportIndex c) fun x hx ↦ ?_]
    · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_self C sX (f.base y)
        (schemeDeltaDimension_cycleSupportIndex c ⟨_, hy⟩)]
      ring
    · have hne : f.base y ≠ x.1 := fun h ↦ hx (Subtype.ext h.symm)
      rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sX k x.1 hne]
      ring

end Presentation


/-! ### The subbundle over a closed subscheme of the base -/

section OverClosed

variable {X : Scheme.{u}} (N' N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  (inc : N' ⟶ N) [IsClosedImmersion (subbundleEmbedding N' N inc)] (Y : X.IdealSheafData)

/-- The morphism from the trace of `N'` on `p⁻¹ Y` to `N'`. -/
def subbundleComapToSubbundle :
    ((subbundleEmbedding N' N inc).ker.comap
      (Y.comap (dualVectorBundleToBase N)).subschemeι).subscheme ⟶ dualVectorBundle N' :=
  IsClosedImmersion.lift (subbundleEmbedding N' N inc)
    (((subbundleEmbedding N' N inc).ker.comap
      (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι ≫
        (Y.comap (dualVectorBundleToBase N)).subschemeι) (by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
    exact (subbundleEmbedding N' N inc).ker.le_map_comap _)

/-- The morphism from the trace of `N'` on `p⁻¹ Y` to `N'`, followed by `i : N' ⟶ N`, is the
inclusion of the trace into `p⁻¹ Y` followed by `p⁻¹ Y ⟶ N`. -/
theorem subbundleComapToSubbundle_comp :
    subbundleComapToSubbundle N' N inc Y ≫ subbundleEmbedding N' N inc =
      ((subbundleEmbedding N' N inc).ker.comap
        (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι ≫
          (Y.comap (dualVectorBundleToBase N)).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

/-- **The trace of `N'` on `p⁻¹ Y` is `(p')⁻¹ Y`.** The closed subscheme of `p⁻¹ Y` cut out by
the ideal of `N'` is the scheme-theoretic inverse image `N' ×_X Y` of `Y` under `p'`: both are
`N' ×_N (N ×_X Y)`. -/
theorem isPullback_subbundleComap :
    IsPullback (subbundleComapToSubbundle N' N inc Y)
      (((subbundleEmbedding N' N inc).ker.comap
        (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι ≫
          comapSubschemeMap Y (dualVectorBundleToBase N))
      (dualVectorBundleToBase N') Y.subschemeι := by
  have sq1 := isPullback_of_isClosedImmersion
    ((subbundleEmbedding N' N inc).ker.comap
      (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι
    (subbundleEmbedding N' N inc) (subbundleComapToSubbundle N' N inc Y)
    (Y.comap (dualVectorBundleToBase N)).subschemeι
    (subbundleComapToSubbundle_comp N' N inc Y).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι])
  have sq := sq1.flip.paste_vert (isPullback_comapSubschemeMap Y (dualVectorBundleToBase N))
  rwa [subbundleEmbedding_comp_dualVectorBundleToBase] at sq

/-- The identification of `(p')⁻¹ Y = N' ×_X Y` with the trace of `N'` on `p⁻¹ Y`. -/
def subbundleComapIso : pullback (dualVectorBundleToBase N') Y.subschemeι ≅
    ((subbundleEmbedding N' N inc).ker.comap
      (Y.comap (dualVectorBundleToBase N)).subschemeι).subscheme :=
  (isPullback_subbundleComap N' N inc Y).isoPullback.symm

/-- The identification `subbundleComapIso` commutes with the maps to `N`: followed by the
inclusion of the trace of `N'` into `N`, it is the first projection `N' ×_X Y ⟶ N'` followed by
`i : N' ⟶ N`. -/
theorem subbundleComapIso_hom_comp :
    (subbundleComapIso N' N inc Y).hom ≫
        ((subbundleEmbedding N' N inc).ker.comap
          (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι ≫
          (Y.comap (dualVectorBundleToBase N)).subschemeι =
      pullback.fst (dualVectorBundleToBase N') Y.subschemeι ≫ subbundleEmbedding N' N inc := by
  rw [← subbundleComapToSubbundle_comp, subbundleComapIso, Iso.symm_hom, ← Category.assoc,
    IsPullback.isoPullback_inv_fst]

end OverClosed

/-! ### The Chern class on the inverse image of a closed subscheme -/

section ChernCap

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (N' N E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r' r e : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N' r']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} N r]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E e]
  (inc : N' ⟶ N) (pr : N ⟶ E) (w : inc ≫ pr = 0)
  (hseq : (ShortComplex.mk inc pr w).ShortExact)

/-- The regular-sequence hypothesis of [Stacks, Tag 0FA9] read through an identification of the
zero scheme with a given closed subscheme. -/
theorem isRegularZeroSchemeSequence_of_zeroScheme_eq {T : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (F : T.Modules) (σ : Γ(F, ⊤)) (n : ℕ) (m : ℤ)
    (A : T.IdealSheafData) (h : RegularSectionSequence.zeroScheme T F σ = A)
    (H : ∀ ξ : genericPoints A.subscheme,
      relativeDimension C.dimensionFunction q (A.subschemeι ξ.1) = m →
        ∃ rs : List (T.presheaf.stalk (A.subschemeι ξ.1)), rs.length = n ∧
          RingTheory.Sequence.IsRegular (T.presheaf.stalk (A.subschemeι ξ.1)) rs ∧
          Ideal.ofList rs = RingHom.ker (A.subschemeι.stalkMap ξ.1).hom) :
    IsRegularSequenceOnZeroScheme C q F σ n m := by
  subst h
  exact H

include pr w hseq in
/-- **[Stacks, Tag 0FA9] on the inverse image of a closed subscheme of the base.** Let `Y ⊆ X`
be a closed subscheme with `dim_δ(Y) ≤ k`, let `v : p⁻¹ Y ⟶ N` be its inverse image in `N` and
`ℱ = (p^*(ℰ^∨))^∨`. Then

  `c_e(v^*ℱ) ∩ [p⁻¹ Y]_{k+r} = [N' ∩ p⁻¹ Y]_{k+r-e}`  in  `CH_*(p⁻¹ Y)`. -/
theorem chernCap_comap_fundamentalCycle_eq_subbundle (Y : X.IdealSheafData) (k : ℤ)
    (hY : schemeDeltaDimension C (Y.subschemeι ≫ sX) ≤ (k : EInt)) (hdeg : (r : ℤ) = r' + e) :
    letI := subbundleEmbedding_isClosedImmersion_of_shortExact N' N E inc pr w hseq
    letI := dualVectorBundleToBase_locallyOfFiniteType N r
    GenuineChern.chernCap C e
        ((Y.comap (dualVectorBundleToBase N)).subschemeι ≫ dualVectorBundleToBase N ≫ sX)
        ((Scheme.Modules.pullback (Y.comap (dualVectorBundleToBase N)).subschemeι).obj
          (dualSheaf (subbundleDualPullback N E))) (k + r) (Fin.last e)
        (QuotientAddGroup.mk' (rationalEquivalences C
          ((Y.comap (dualVectorBundleToBase N)).subschemeι ≫ dualVectorBundleToBase N ≫ sX)
          (k + r))
          (cycleAssociatedToClosedSubscheme C
            ((Y.comap (dualVectorBundleToBase N)).subschemeι ≫ dualVectorBundleToBase N ≫ sX)
            (𝟙 _) (k + r))) =
      QuotientAddGroup.mk' (rationalEquivalences C
          ((Y.comap (dualVectorBundleToBase N)).subschemeι ≫ dualVectorBundleToBase N ≫ sX)
          ((k + r) - e))
        (cycleAssociatedToClosedSubscheme C
          ((Y.comap (dualVectorBundleToBase N)).subschemeι ≫ dualVectorBundleToBase N ≫ sX)
          ((subbundleEmbedding N' N inc).ker.comap
            (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι ((k + r) - e)) := by
  let hi := subbundleEmbedding_isClosedImmersion_of_shortExact N' N E inc pr w hseq
  let := dualVectorBundleToBase_locallyOfFiniteType N r
  have := dualVectorBundleToBase_flat N r
  have := dualVectorBundleToBase_locallyOfFiniteType N' r'
  have := dualVectorBundleToBase_flat N' r'
  obtain ⟨w', hS⟩ := exists_dualSheaf_shortExact inc pr w hseq.mono_f hseq.epi_g hseq.exact
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
      (R := X.ringCatSheaf) (M := N')
      ((‹AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N'›)
        |>.exists_isFiniteLocallyFreeData))
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
      (R := X.ringCatSheaf) (M := N)
      ((‹AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N›)
        |>.exists_isFiniteLocallyFreeData))
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u}
      (R := X.ringCatSheaf) (M := E)
      ((‹AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E›)
        |>.exists_isFiniteLocallyFreeData))
  have hZv : RegularSectionSequence.zeroScheme (Y.comap (dualVectorBundleToBase N)).subscheme
      ((Scheme.Modules.pullback (Y.comap (dualVectorBundleToBase N)).subschemeι).obj
        (dualSheaf (subbundleDualPullback N E)))
      (pullbackGlobalSections (Y.comap (dualVectorBundleToBase N)).subschemeι
        (dualSheaf (subbundleDualPullback N E)) (subbundleSection N E pr)) =
      (subbundleEmbedding N' N inc).ker.comap (Y.comap (dualVectorBundleToBase N)).subschemeι := by
    rw [Stacks.RegularSectionSequence.zeroScheme_pullbackGlobalSections _ _ e,
      zeroScheme_subbundleSection N' N E e inc pr w' hS]
  have hX : schemeDeltaDimension C ((Y.comap (dualVectorBundleToBase N)).subschemeι ≫
      dualVectorBundleToBase N ≫ sX) ≤ ((k + (r : ℤ) : ℤ) : EInt) :=
    schemeDeltaDimension_comap_le_of_relativeDimension C (dualVectorBundleToBase N ≫ sX) sX
      (dualVectorBundleToBase N) rfl r (dualVectorBundleToBase_relativeDimension N r) Y k hY
  have hcomp : (subbundleComapIso N' N inc Y).hom ≫
      (((subbundleEmbedding N' N inc).ker.comap
        (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι ≫
        (Y.comap (dualVectorBundleToBase N)).subschemeι ≫ dualVectorBundleToBase N ≫ sX) =
      pullback.fst (dualVectorBundleToBase N') Y.subschemeι ≫ (dualVectorBundleToBase N' ≫ sX) := by
    calc _ = ((subbundleComapIso N' N inc Y).hom ≫
          ((subbundleEmbedding N' N inc).ker.comap
            (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι ≫
            (Y.comap (dualVectorBundleToBase N)).subschemeι) ≫ dualVectorBundleToBase N ≫ sX := by
          simp only [Category.assoc]
      _ = (pullback.fst (dualVectorBundleToBase N') Y.subschemeι ≫
          subbundleEmbedding N' N inc) ≫ dualVectorBundleToBase N ≫ sX := by
          rw [subbundleComapIso_hom_comp]
      _ = _ := by
          rw [Category.assoc, subbundleEmbedding_comp_base]
  have hZ : schemeDeltaDimension C ((RegularSectionSequence.zeroScheme
      (Y.comap (dualVectorBundleToBase N)).subscheme
      ((Scheme.Modules.pullback (Y.comap (dualVectorBundleToBase N)).subschemeι).obj
        (dualSheaf (subbundleDualPullback N E)))
      (pullbackGlobalSections (Y.comap (dualVectorBundleToBase N)).subschemeι
        (dualSheaf (subbundleDualPullback N E)) (subbundleSection N E pr))).subschemeι ≫
        ((Y.comap (dualVectorBundleToBase N)).subschemeι ≫ dualVectorBundleToBase N ≫ sX)) ≤
      (((k + (r : ℤ)) - (e : ℤ) : ℤ) : EInt) := by
    rw [schemeDeltaDimension_subschemeι_comp_of_eq C hZv rfl]
    refine le_of_eq_of_le ((schemeDeltaDimension_comp_iso C (subbundleComapIso N' N inc Y)
      _).symm.trans (schemeDeltaDimension_congr C hcomp)) ?_
    have h := schemeDeltaDimension_pullback_le C (dualVectorBundleToBase N' ≫ sX) sX
      (dualVectorBundleToBase N') rfl r' (dualVectorBundleToBase_relativeDimension N' r')
      Y.subschemeι k hY
    rwa [show k + (r : ℤ) - (e : ℤ) = k + (r' : ℤ) by omega]
  have hreg : IsRegularSequenceOnZeroScheme C
      ((Y.comap (dualVectorBundleToBase N)).subschemeι ≫ dualVectorBundleToBase N ≫ sX)
      ((Scheme.Modules.pullback (Y.comap (dualVectorBundleToBase N)).subschemeι).obj
        (dualSheaf (subbundleDualPullback N E)))
      (pullbackGlobalSections (Y.comap (dualVectorBundleToBase N)).subschemeι
        (dualSheaf (subbundleDualPullback N E)) (subbundleSection N E pr))
      e ((k + (r : ℤ)) - (e : ℤ)) := by
    refine isRegularZeroSchemeSequence_of_zeroScheme_eq C _ _ _ e _ _ hZv fun ξ _ ↦ ?_
    have hmem : (Y.comap (dualVectorBundleToBase N)).subschemeι.base
        (((subbundleEmbedding N' N inc).ker.comap
          (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι ξ.1) ∈
        (subbundleEmbedding N' N inc).ker.support := by
      have h : ((subbundleEmbedding N' N inc).ker.comap
          (Y.comap (dualVectorBundleToBase N)).subschemeι).subschemeι ξ.1 ∈
          ((((subbundleEmbedding N' N inc).ker.comap
            (Y.comap (dualVectorBundleToBase N)).subschemeι).support : Set _)) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨_, rfl⟩
      rw [Scheme.IdealSheafData.support_comap] at h
      exact h
    obtain ⟨rs, hlen, hrs, hofList⟩ := exists_isRegular_stalk_comap_subbundle N' N E inc pr w' hS
      e r' Y _ hmem
    refine ⟨rs, hlen, hrs, ?_⟩
    rw [hofList, ker_stalkMap_subschemeι_eq_stalk, IdealSheafData.stalk_comap]
  have key := chernCap_cap_fundamentalCycle_eq_zeroScheme C
    ((Y.comap (dualVectorBundleToBase N)).subschemeι ≫ dualVectorBundleToBase N ≫ sX)
    _ e _ (k + (r : ℤ)) hX hZ hreg
  rw [hZv] at key
  exact key

/-- `(p^*(ℰ^∨))^∨ ≅ p^*ℰ`: duality commutes with pullback of finite locally free modules, and a
finite locally free module is reflexive. -/
def subbundleDualPullbackDualIso :
    dualSheaf (subbundleDualPullback N E) ≅
      (Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E :=
  haveI := toDoubleDual_isIso_of_isFiniteLocallyFree
    ((Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E)
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ e)
  (dualMapIso (Stacks.FundamentalGroup.pullbackDualSheafIso (dualVectorBundleToBase N) E
    inferInstance)).symm ≪≫
    (asIso (toDoubleDual ((Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E))).symm

/-- A class and its transport along an equality of degrees are heterogeneously equal. -/
theorem mk_cycleGroupOfEq_heq {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q] {d d' : ℤ}
    (h : d = d') (β : CycleGroup C q d) :
    QuotientAddGroup.mk' (rationalEquivalences C q d) β ≍
      QuotientAddGroup.mk' (rationalEquivalences C q d') (cycleGroupOfEq h β) := by
  subst h
  rfl

/-- The cycle of a closed subscheme in two degrees known to be equal. -/
theorem cycleAssociatedToClosedSubscheme_val_congr_degree {T W : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (j : W ⟶ T) [IsClosedImmersion j] {d d' : ℤ} (h : d = d') :
    (cycleAssociatedToClosedSubscheme C q j d).1 = (cycleAssociatedToClosedSubscheme C q j d').1 :=
  by subst h; rfl

/-- **The key identity of [Stacks, Tag 0FAA] before moving the Chern class past `p^*`.** For a
short exact sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` of finite locally free modules of constant ranks
`r'`, `r = r' + e` and `e`, and `α ∈ CH_k(X)`,

  `i_*(p')^*α = c_e(p^*ℰ) ∩ p^*α`

in `CH_{k+r'}(N) = CH_{(k+r)-e}(N)`. -/
theorem subbundleEmbedding_pushforward_flatPullback_heq_chernCap (hdeg : (r : ℤ) = r' + e)
    (k : ℤ) (α : chowGroup C sX k) :
    letI := subbundleEmbedding_isClosedImmersion_of_shortExact N' N E inc pr w hseq
    letI := dualVectorBundleToBase_locallyOfFiniteType N' r'
    letI := dualVectorBundleToBase_flat N' r'
    letI := dualVectorBundleToBase_locallyOfFiniteType N r
    letI := dualVectorBundleToBase_flat N r
    chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase N' ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding N' N inc)
        (subbundleEmbedding_comp_base N' N sX inc) (k + (r' : ℤ))
        (flatPullbackChow C (dualVectorBundleToBase N' ≫ sX) sX (dualVectorBundleToBase N') rfl
          r' (dualVectorBundleToBase_relativeDimension N' r') k
          (flatPullbackDescends C _ _ _ _ _ _ _) α) ≍
      GenuineChern.chernCap C e (dualVectorBundleToBase N ≫ sX)
        ((Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E) (k + r) (Fin.last e)
        (flatPullbackChow C (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r
          (dualVectorBundleToBase_relativeDimension N r) k
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl r _ k) α) := by
  let hi := subbundleEmbedding_isClosedImmersion_of_shortExact N' N E inc pr w hseq
  let := dualVectorBundleToBase_locallyOfFiniteType N' r'
  let := dualVectorBundleToBase_flat N' r'
  let := dualVectorBundleToBase_locallyOfFiniteType N r
  let := dualVectorBundleToBase_flat N r
  have hdeg' : k + (r' : ℤ) = (k + r) - e := by omega
  induction α using QuotientAddGroup.induction_on with
  | H c =>
  let J := cycleSupportIndex c
  let Yc : J → X.IdealSheafData := fun t ↦ integralComponentAt t.1
  let v : ∀ t : J, ((Yc t).comap (dualVectorBundleToBase N)).subscheme ⟶ dualVectorBundle N :=
    fun t ↦ ((Yc t).comap (dualVectorBundleToBase N)).subschemeι
  let wt : ∀ t : J, ((subbundleEmbedding N' N inc).ker.comap (v t)).subscheme ⟶
      ((Yc t).comap (dualVectorBundleToBase N)).subscheme :=
    fun t ↦ ((subbundleEmbedding N' N inc).ker.comap (v t)).subschemeι
  have hlf : LocallyFinite fun t : J ↦ Set.range (v t) := by
    have h0 : LocallyFinite fun t : J ↦ Set.range (integralComponentAt t.1).subschemeι :=
      locallyFinite_range_subschemeι_support C sX k c
    refine (h0.preimage_continuous
      (dualVectorBundleToBase N).continuous).subset fun t ↦ ?_
    change Set.range ((Yc t).comap (dualVectorBundleToBase N)).subschemeι ⊆ _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.range_subschemeι]
    exact subset_rfl
  have hcap : ∀ t : J, GenuineChern.chernCap C e (v t ≫ dualVectorBundleToBase N ≫ sX)
      ((Scheme.Modules.pullback (v t)).obj
        ((Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E)) (k + r) (Fin.last e)
      (QuotientAddGroup.mk' (rationalEquivalences C (v t ≫ dualVectorBundleToBase N ≫ sX) (k + r))
        (cycleAssociatedToClosedSubscheme C (v t ≫ dualVectorBundleToBase N ≫ sX)
          (𝟙 _) (k + r))) =
      QuotientAddGroup.mk' (rationalEquivalences C (v t ≫ dualVectorBundleToBase N ≫ sX)
          ((k + r) - e))
        (cycleAssociatedToClosedSubscheme C (v t ≫ dualVectorBundleToBase N ≫ sX)
          (wt t) ((k + r) - e)) := by
    intro t
    rw [← GenuineChern.chernCap_congr C _ e
      ((Scheme.Modules.pullback (v t)).mapIso (subbundleDualPullbackDualIso N E e))]
    exact chernCap_comap_fundamentalCycle_eq_subbundle C sX N' N E r' r e inc pr w hseq (Yc t) k
      (schemeDeltaDimension_cycleSupportIndex c t).le hdeg
  have ha : ∀ y, (flatPullback C (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N)
      rfl r (dualVectorBundleToBase_relativeDimension N r) k c).1 y =
      ∑ᶠ t : J, c.1 t.1 *
        (cycleAssociatedToClosedSubscheme C (dualVectorBundleToBase N ≫ sX) (v t) (k + r)).1 y := by
    intro y
    rw [flatPullback_apply_eq_finsum]
    refine finsum_congr fun t ↦ ?_
    rw [cycleAssociatedToClosedSubscheme_pullbackFst_eq_comap]
  set β := properPushforward C (dualVectorBundleToBase N' ≫ sX) (dualVectorBundleToBase N ≫ sX)
    (subbundleEmbedding N' N inc) (subbundleEmbedding_comp_base N' N sX inc) (k + (r' : ℤ))
    (flatPullback C (dualVectorBundleToBase N' ≫ sX) sX (dualVectorBundleToBase N') rfl r'
      (dualVectorBundleToBase_relativeDimension N' r') k c) with hβ
  have hb : ∀ y, (cycleGroupOfEq hdeg' β).1 y =
      ∑ᶠ t : J, c.1 t.1 * (cycleAssociatedToClosedSubscheme C (dualVectorBundleToBase N ≫ sX)
        (wt t ≫ v t) ((k + r) - e)).1 y := by
    intro y
    rw [coe_cycleGroupOfEq, hβ, properPushforward_apply_finsum_of_isClosedImmersion C _ _ _ _ _
      _ (fun t : J ↦ c.1 t.1 • cycleAssociatedToClosedSubscheme C (dualVectorBundleToBase N' ≫ sX)
        (pullback.fst (dualVectorBundleToBase N') (Yc t).subschemeι) (k + (r' : ℤ)))
      (fun z ↦ by rw [flatPullback_apply_eq_finsum]; rfl)]
    refine finsum_congr fun t ↦ ?_
    rw [← properPushforwardHom_apply, map_zsmul, properPushforwardHom_apply,
      properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
      cycleAssociatedToClosedSubscheme_eq_of_iso C _ _ _ (subbundleComapIso N' N inc (Yc t))
        (subbundleComapIso_hom_comp N' N inc (Yc t))]
    calc _ = c.1 t.1 * (cycleAssociatedToClosedSubscheme C (dualVectorBundleToBase N ≫ sX)
          (wt t ≫ v t) (k + (r' : ℤ))).1 y := rfl
      _ = _ := by rw [cycleAssociatedToClosedSubscheme_val_congr_degree C _ _ hdeg']
  have hL1 := GenuineChern.chernCap_mk_eq_mk_of_locallyFinite C (dualVectorBundleToBase N ≫ sX)
    ((Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E) e (k + r) (Fin.last e)
    (fun t : J ↦ ((Yc t).comap (dualVectorBundleToBase N)).subscheme) v hlf
    (fun t : J ↦ ((subbundleEmbedding N' N inc).ker.comap (v t)).subscheme) wt (fun t ↦ c.1 t.1)
    hcap _ ha _ hb
  have eL : chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase N' ≫ sX)
      (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding N' N inc)
      (subbundleEmbedding_comp_base N' N sX inc) (k + (r' : ℤ))
      (flatPullbackChow C (dualVectorBundleToBase N' ≫ sX) sX (dualVectorBundleToBase N') rfl
        r' (dualVectorBundleToBase_relativeDimension N' r') k
        (flatPullbackDescends C _ _ _ _ _ _ _) (QuotientAddGroup.mk' _ c)) =
      QuotientAddGroup.mk' _ β := by
    rw [flatPullbackChow_mk, chowPushforwardOfIsClosedImmersion_mk]
  have eR : GenuineChern.chernCap C e (dualVectorBundleToBase N ≫ sX)
      ((Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E) (k + r) (Fin.last e)
      (flatPullbackChow C (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r
        (dualVectorBundleToBase_relativeDimension N r) k
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl r _ k)
        (QuotientAddGroup.mk' _ c)) =
      QuotientAddGroup.mk' _ (cycleGroupOfEq hdeg' β) := by
    rw [flatPullbackChow_mk, hL1]
  exact (heq_of_eq eL).trans ((mk_cycleGroupOfEq_heq C _ hdeg' β).trans (heq_of_eq eR.symm))

/-- **[Stacks, Tag 0FAA] for modules of constant rank.** Let `(S, δ)` be the base situation of
chapter 42, let `X` be locally of finite type over `S` and let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short
exact sequence of finite locally free `𝒪_X`-modules, of constant ranks `r'`, `r` and `e`. Let
`i : N' = Spec_X(Sym((𝒩')^∨)) ⟶ N = Spec_X(Sym(𝒩^∨))` be the canonical closed embedding and
`p' : N' ⟶ X`, `p : N ⟶ X` the structure morphisms. Then for `α ∈ CH_k(X)`

  `i_*(p')^*α = p^*(c_e(ℰ) ∩ α)`

in `CH_{k+r'}(N)`, the two degrees `k + r'` and `(k - e) + r` agreeing because `r = r' + e`. -/
theorem subbundleEmbedding_pushforward_flatPullback_eq_chernCap_of_point (x : X) (k : ℤ)
    (α : chowGroup C sX k) :
    letI := subbundleEmbedding_isClosedImmersion_of_shortExact N' N E inc pr w hseq
    letI := dualVectorBundleToBase_locallyOfFiniteType N' r'
    letI := dualVectorBundleToBase_flat N' r'
    letI := dualVectorBundleToBase_locallyOfFiniteType N r
    letI := dualVectorBundleToBase_flat N r
    chowPushforwardOfIsClosedImmersion C (dualVectorBundleToBase N' ≫ sX)
        (dualVectorBundleToBase N ≫ sX) (subbundleEmbedding N' N inc)
        (subbundleEmbedding_comp_base N' N sX inc) (k + (r' : ℤ))
        (flatPullbackChow C (dualVectorBundleToBase N' ≫ sX) sX (dualVectorBundleToBase N') rfl
          r' (dualVectorBundleToBase_relativeDimension N' r') k
          (flatPullbackDescends C _ _ _ _ _ _ _) α) =
      Eq.mp (congrArg (chowGroup C (dualVectorBundleToBase N ≫ sX))
          (subbundleDegree_eq N' N E r' r e inc pr w hseq x k))
        (flatPullbackChow C (dualVectorBundleToBase N ≫ sX) sX (dualVectorBundleToBase N) rfl r
          (dualVectorBundleToBase_relativeDimension N r) (k - (e : ℤ))
          (flatPullbackDescends C _ _ _ _ _ _ _)
          (GenuineChern.chernCap C e sX E k (Fin.last e) α)) := by
  let := dualVectorBundleToBase_locallyOfFiniteType N r
  let := dualVectorBundleToBase_flat N r
  have hrank := subbundleRank_add N' N E r' r e inc pr w hseq x
  have hdeg : (r : ℤ) = r' + e := by omega
  have h02U8 := GenuineChern.chernCap_flatPullback_heq_general C sX (dualVectorBundleToBase N ≫ sX)
    (dualVectorBundleToBase N) rfl r (dualVectorBundleToBase_relativeDimension N r) E e
    ((Scheme.Modules.pullback (dualVectorBundleToBase N)).obj E) (Iso.refl _) k (Fin.last e) α
  exact (cast_eq_iff_heq.mpr
    ((subbundleEmbedding_pushforward_flatPullback_heq_chernCap C sX N' N E r' r e inc pr w hseq
      hdeg k α).trans h02U8).symm).symm

end ChernCap

end Stacks.Chow

end
