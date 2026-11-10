module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchAmbientPullback
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionBranchIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChernComponentAmbient
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowDevissage
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowPrimeCycleContained

/-!
# `[W₁ ∩ W₂]` as the push of the zero section's fundamental cycle

In the situation of [Stacks, Tag 0F97] let `W ⊆ Y` be a closed subscheme contained in the divisor
`D = Z(s)`. The case `W ⊆ D` of [Stacks, Tag 0F98] produces, as the uncontained branch of the
Gysin rule of `i₁`, the fundamental cycle of

  `D₁ ∩ (D₂ ⊔ p^{-1}W)`, the inverse image of `D₂ ⊔ p^{-1}W` in `D₁`,

and the source's final sentence identifies that with the zero section of the line bundle
`W₁ ⟶ W`. This file performs the identification **at the level of cycles**: the fundamental cycle
above is the pushforward, along the immersion `j : W₁ ⟶ D₁` of
`Stacks.Chow.TensorZeroScheme.branchTotalSpaceToBranch₁`, of the pushforward along the bundle's
zero section of the fundamental cycle of the bundle's base.

## Main results

* `Stacks.Chow.TensorZeroScheme.map_sup_branches_decompositionComap` — the intersection of the two
  branches of the base-changed diagram, pushed into `L`, is the triple join
  `D₁ ⊔ (D₂ ⊔ p^{-1}W)`.
* `Stacks.Chow.TensorZeroScheme.exists_iso_sup_branches_comap_branch₁` — consequently that
  intersection and the inverse image of `D₂ ⊔ p^{-1}W` in `D₁` are isomorphic over `D₁`.
* `Stacks.Chow.TensorZeroScheme.cycleAssociatedToClosedSubscheme_comap_branch₁_eq` — **the cycle
  identity**: `[W₁ ∩ W₂] = j_*o_*[D']`.

## Implementation notes

### Nothing is transported

Two spellings of one scheme occur throughout — `(decompositionComap …).total` and
`(W.comap (proj …)).subscheme`, and `(branchSituation …).X` and the restricted divisor — and they
agree only at default transparency. So every step below is a `congrArg` at an explicitly typed
function, an `Eq.trans`, or a `calc` step proved by one of those: all three unify at default
transparency, where the two spellings are interchangeable, whereas `rw` builds its motive at
`instances` transparency and is rejected. The two equalities of ideal sheaves that carry the
content are consumed in `Prop`, as the hypothesis of `Stacks.Chow.exists_iso_of_ker_eq`, so no
`Eq.rec` on a scheme or on an ideal sheaf is formed.

### Why the base's fundamental cycle is taken at `⊥`

The cycle `[D']` is the fundamental cycle of the bundle's base. Taken as
`Stacks.Chow.cycleAssociatedToClosedSubscheme` of the identity it would be inert, but the
dévissage also has to recognize it as the value of a component rule, and
`Stacks.Chow.IntegralComponentRule.extendCycleGroup_cycleAssociatedToClosedSubscheme` evaluates a
rule at the closed immersion of an *ideal sheaf*. The ideal sheaf whose subscheme is everything is
`⊥`, and `AlgebraicGeometry.Scheme.IdealSheafData.isIso_subschemeι_iff_eq_bot` makes its immersion
an isomorphism, so the two readings of `[D']` agree by
`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso`. Taking `⊥` from the start avoids that
comparison twice over.

### No `@[stacks]` attribute here

This is the clause "`W₁ ∩ W₂` is the zero section of the line bundle `W₁ → W`" of the case
`W ⊆ D` of [Stacks, Tag 0F98], read on cycles; the clause itself is
`Stacks.Chow.TensorZeroScheme.Decomposition.ker_inclusion_comp_branch₁_eq_ker_zeroSection`, and
conditions (6) and (7) of [Stacks, Tag 0F97] that prove it are asserted elsewhere. Nothing here
asserts [Stacks, Tag 0F98], which is a single identity of maps; see the convention note in
`StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.ChowMaps`.

## References

* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.PullbackTensorIso (pullbackTensorSection)

universe u

namespace Stacks.Chow.TensorZeroScheme

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

variable {Y : Scheme.{u}} (L₁ L₂ : Y.Modules)
  [h₁ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
  [h₂ : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
  (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤)) (R : Decomposition Y L₁ L₂ s)
  (W : Y.IdealSheafData)

attribute [local instance] isClosedImmersion_branchComapToBranch₁
  isClosedImmersion_branchTotalSpaceToBranch₁

/-! ### The intersection of the two branches over `W`, pushed into `L` -/

include h₁ h₂ in
/-- **The intersection of the two branches of the base-changed diagram, pushed into `L`, is
`D₁ ⊔ (D₂ ⊔ p^{-1}W)`.**

The two branches of the diagram over `W` are the inverse images of `D₁` and `D₂` in `p^{-1}(W)`
(`Stacks.Chow.TensorZeroScheme.comap_branch₁_decompositionComap` and `…₂…`), and inverse image is
the lower adjoint of pushforward, so it preserves joins; pushing a join of inverse images back out
is `AlgebraicGeometry.Scheme.IdealSheafData.map_comap_subschemeι`. -/
theorem map_sup_branches_decompositionComap :
    ((decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂ :
          (W.comap R.normalize.p).subscheme.IdealSheafData).map
        (W.comap R.normalize.p).subschemeι =
      R.normalize.D₁ ⊔ (R.normalize.D₂ ⊔ W.comap R.normalize.p) := by
  have hD : ((decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂ :
        (W.comap R.normalize.p).subscheme.IdealSheafData) =
      (R.normalize.D₁ ⊔ R.normalize.D₂).comap
        (W.comap R.normalize.p).subschemeι := by
    refine Eq.trans ?_ (Scheme.IdealSheafData.comap_sup R.normalize.D₁ R.normalize.D₂
      (W.comap R.normalize.p).subschemeι).symm
    exact ((congrArg (fun I : (W.comap R.normalize.p).subscheme.IdealSheafData =>
        I ⊔ (decompositionComap L₁ L₂ s R W).D₂)
      (comap_branch₁_decompositionComap L₁ L₂ s R W)).trans
      (congrArg (fun I : (W.comap R.normalize.p).subscheme.IdealSheafData =>
          R.normalize.D₁.comap (W.comap R.normalize.p).subschemeι ⊔ I)
        (comap_branch₂_decompositionComap L₁ L₂ s R W)))
  refine ((congrArg (fun I : (W.comap R.normalize.p).subscheme.IdealSheafData =>
      I.map (W.comap R.normalize.p).subschemeι) hD).trans
    (Scheme.IdealSheafData.map_comap_subschemeι (W.comap R.normalize.p)
      (R.normalize.D₁ ⊔ R.normalize.D₂))).trans ?_
  rw [sup_comm, sup_assoc]

include h₁ h₂ in
/-- **The intersection of the two branches over `W` and the inverse image of `D₂ ⊔ p^{-1}W` in
`D₁` are isomorphic over `D₁`.**

Both are closed subschemes of `L`, by the composite immersion through `p^{-1}(W)` on one side and
through `D₁` on the other, and the two composites have the same kernel:
`Stacks.Chow.TensorZeroScheme.map_sup_branches_decompositionComap` for the first and
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_subschemeι` for the second. So
`Stacks.Chow.exists_iso_of_ker_eq` identifies them over `L`, and the mono `D₁ ↪ L` cancels to give
the identification over `D₁`. -/
theorem exists_iso_sup_branches_comap_branch₁ :
    ∃ e : ((decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂).subscheme ≅
        ((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
          R.normalize.D₁.subschemeι).subscheme,
      e.hom ≫ ((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
          R.normalize.D₁.subschemeι).subschemeι =
        Scheme.IdealSheafData.inclusion (le_sup_left :
            (decompositionComap L₁ L₂ s R W).D₁ ≤
              (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
          branchComapToBranch₁ L₁ L₂ s R W := by
  have hker :
      (((decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂).subschemeι ≫
          (W.comap R.normalize.p).subschemeι).ker =
        (((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
            R.normalize.D₁.subschemeι).subschemeι ≫ R.normalize.D₁.subschemeι).ker :=
    (map_sup_branches_decompositionComap L₁ L₂ s R W).trans
      (Scheme.IdealSheafData.map_comap_subschemeι R.normalize.D₁
        (R.normalize.D₂ ⊔ W.comap R.normalize.p)).symm
  -- the two composite immersions into `L`; instance search does not cross the two spellings of
  -- the total space of the base-changed diagram, so both are supplied by hand
  have : IsClosedImmersion
      (((decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂).subschemeι ≫
        (W.comap R.normalize.p).subschemeι) :=
    @IsClosedImmersion.comp _ _ _ _ _
      (inferInstanceAs (IsClosedImmersion
        ((decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂).subschemeι))
      (inferInstanceAs (IsClosedImmersion (W.comap R.normalize.p).subschemeι))
  have : IsClosedImmersion
      (((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
          R.normalize.D₁.subschemeι).subschemeι ≫ R.normalize.D₁.subschemeι) :=
    IsClosedImmersion.comp _ _
  obtain ⟨e, he⟩ := Stacks.Chow.exists_iso_of_ker_eq
    (((decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂).subschemeι ≫
      (W.comap R.normalize.p).subschemeι)
    (((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
      R.normalize.D₁.subschemeι).subschemeι ≫ R.normalize.D₁.subschemeι) hker
  refine ⟨e, (cancel_mono R.normalize.D₁.subschemeι).1 ?_⟩
  calc (e.hom ≫ ((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
          R.normalize.D₁.subschemeι).subschemeι) ≫ R.normalize.D₁.subschemeι
      = e.hom ≫ (((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
          R.normalize.D₁.subschemeι).subschemeι ≫ R.normalize.D₁.subschemeι) :=
        Category.assoc _ _ _
    _ = ((decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂).subschemeι ≫
          (W.comap R.normalize.p).subschemeι := he
    _ = (Scheme.IdealSheafData.inclusion (le_sup_left :
            (decompositionComap L₁ L₂ s R W).D₁ ≤
              (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
          (decompositionComap L₁ L₂ s R W).D₁.subschemeι) ≫
          (W.comap R.normalize.p).subschemeι :=
        congrArg (fun t : ((decompositionComap L₁ L₂ s R W).D₁ ⊔
              (decompositionComap L₁ L₂ s R W).D₂).subscheme ⟶
            (W.comap R.normalize.p).subscheme =>
          t ≫ (W.comap R.normalize.p).subschemeι)
          (Scheme.IdealSheafData.inclusion_subschemeι _).symm
    _ = Scheme.IdealSheafData.inclusion (le_sup_left :
            (decompositionComap L₁ L₂ s R W).D₁ ≤
              (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
          ((decompositionComap L₁ L₂ s R W).D₁.subschemeι ≫
            (W.comap R.normalize.p).subschemeι) := Category.assoc _ _ _
    _ = Scheme.IdealSheafData.inclusion (le_sup_left :
            (decompositionComap L₁ L₂ s R W).D₁ ≤
              (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
          (branchComapToBranch₁ L₁ L₂ s R W ≫ R.normalize.D₁.subschemeι) :=
        congrArg (fun t : (decompositionComap L₁ L₂ s R W).D₁.subscheme ⟶
            R.normalize.total =>
          Scheme.IdealSheafData.inclusion (le_sup_left :
              (decompositionComap L₁ L₂ s R W).D₁ ≤
                (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫ t)
          (branchComapToBranch₁_subschemeι L₁ L₂ s R W).symm
    _ = (Scheme.IdealSheafData.inclusion (le_sup_left :
            (decompositionComap L₁ L₂ s R W).D₁ ≤
              (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
          branchComapToBranch₁ L₁ L₂ s R W) ≫ R.normalize.D₁.subschemeι :=
        (Category.assoc _ _ _).symm

/-! ### The cycle identity -/

variable (C : Stacks.Chow.ChowSituation.{u}) (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sD : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
    ((Scheme.Modules.pullback W.subschemeι).obj L₂)
    (pullbackTensorSection W.subschemeι L₁ L₂ s)
    ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X ⟶ C.S) [LocallyOfFiniteType sD]
  (hsD : zeroIdealBaseChangeMap s W.subschemeι ≫
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) = sD)

/-- Rational equivalence to zero within a carrier is closed under `(a - b) + (b - c) = a - c`. -/
private theorem isRationallyEquivalentToZeroWithin_sub_add_sub {X : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {k : ℤ} {T : Set X} {a b c : Stacks.Chow.CycleGroup C sX k}
    (h₁ : Stacks.Chow.IsRationallyEquivalentToZeroWithin C sX k (a - b) T)
    (h₂ : Stacks.Chow.IsRationallyEquivalentToZeroWithin C sX k (b - c) T) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C sX k (a - c) T :=
  sub_add_sub_cancel a b c ▸ Stacks.Chow.isRationallyEquivalentToZeroWithin_add C sX k h₁ h₂

include h₁ h₂ hsD in
/-- **`[W₁ ∩ W₂] = j_*o_*[D']`.** The fundamental cycle, in `D₁`, of the inverse image of
`D₂ ⊔ p^{-1}W` is the pushforward along `j : W₁ ⟶ D₁` of the pushforward along the zero section of
the branch bundle over `W` of the fundamental cycle of that bundle's base.

Both pushforwards are along closed immersions, so
`Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp` turns
the right-hand side into the fundamental cycle of the composite immersion
`D' ⟶ W₁ ⟶ D₁`. That composite and the immersion of the inverse image differ by an isomorphism of
their sources — the zero section's image is the intersection of the two branches
(`Stacks.Chow.TensorZeroScheme.Decomposition.intersectionIsoKerZeroSection`) and that intersection
is the inverse image (`Stacks.Chow.TensorZeroScheme.exists_iso_sup_branches_comap_branch₁`) — and
a fundamental cycle does not see such an isomorphism, by
`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso`. -/
theorem cycleAssociatedToClosedSubscheme_comap_branch₁_eq (k : ℤ) :
    Stacks.Chow.cycleAssociatedToClosedSubscheme C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        ((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
          R.normalize.D₁.subschemeι).subschemeι (k + 1) =
      Stacks.Chow.properPushforward C
        ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        (branchTotalSpaceToBranch₁ L₁ L₂ s R W)
        (branchTotalSpaceToBranch₁_comp_base L₁ L₂ s R W C sY sD hsD) (k + 1)
        (Stacks.Chow.properPushforward C sD
          ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
          (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection
          (Stacks.Chow.zeroSection_comp_totalSpaceToBase_comp C
            (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)) sD) (k + 1)
          (Stacks.Chow.cycleAssociatedToClosedSubscheme C sD
            (⊥ : (branchSituation W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι
            (k + 1))) := by
  have : IsIso (⊥ : (branchSituation W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot _).2 rfl
  have : IsClosedImmersion ((⊥ : (branchSituation W.subscheme
        ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection) :=
    IsClosedImmersion.comp _ _
  have : IsClosedImmersion (((⊥ : (branchSituation W.subscheme
          ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
        (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection) ≫
      branchTotalSpaceToBranch₁ L₁ L₂ s R W) := IsClosedImmersion.comp _ _
  -- the zero section presented through its own kernel ideal
  obtain ⟨e₀, he₀⟩ := Stacks.Chow.exists_iso_of_ker_eq
    (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection
    (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection.ker.subschemeι
    (Scheme.IdealSheafData.ker_subschemeι _).symm
  obtain ⟨e₂, he₂⟩ := exists_iso_sup_branches_comap_branch₁ L₁ L₂ s R W
  -- the zero section's image is the intersection of the two branches
  have hker2 : ((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
          ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫
        (Scheme.IdealSheafData.inclusion (le_sup_left :
            (decompositionComap L₁ L₂ s R W).D₁ ≤
              (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
          (decompositionComap L₁ L₂ s R W).branch₁.hom) =
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection.ker.subschemeι :=
    (congrArg (fun t ↦ ((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
        ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫ t)
      ((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection_hom_comp_subschemeι
        W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)).symm).trans
      (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
        ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv_hom_id_assoc _)
  -- the composite immersion `D' ⟶ W₁ ⟶ D₁` through the zero section
  have ho : e₀.hom ≫ (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
          ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫
        (Scheme.IdealSheafData.inclusion (le_sup_left :
            (decompositionComap L₁ L₂ s R W).D₁ ≤
              (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
          branchComapToBranch₁ L₁ L₂ s R W)) =
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection ≫
        branchTotalSpaceToBranch₁ L₁ L₂ s R W := by
    calc e₀.hom ≫ (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
            ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫
          (Scheme.IdealSheafData.inclusion (le_sup_left :
              (decompositionComap L₁ L₂ s R W).D₁ ≤
                (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
            branchComapToBranch₁ L₁ L₂ s R W))
        = e₀.hom ≫ (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫
            (Scheme.IdealSheafData.inclusion (le_sup_left :
                (decompositionComap L₁ L₂ s R W).D₁ ≤
                  (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
              ((decompositionComap L₁ L₂ s R W).branch₁.hom ≫
                ((decompositionComap L₁ L₂ s R W).branch₁.inv ≫
                  branchComapToBranch₁ L₁ L₂ s R W)))) :=
          congrArg (fun t ↦ e₀.hom ≫
              (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
                ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫
              (Scheme.IdealSheafData.inclusion (le_sup_left :
                  (decompositionComap L₁ L₂ s R W).D₁ ≤
                    (decompositionComap L₁ L₂ s R W).D₁ ⊔
                      (decompositionComap L₁ L₂ s R W).D₂) ≫ t)))
            ((decompositionComap L₁ L₂ s R W).branch₁.hom_inv_id_assoc
              (branchComapToBranch₁ L₁ L₂ s R W)).symm
      _ = (e₀.hom ≫ (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫
            (Scheme.IdealSheafData.inclusion (le_sup_left :
                (decompositionComap L₁ L₂ s R W).D₁ ≤
                  (decompositionComap L₁ L₂ s R W).D₁ ⊔ (decompositionComap L₁ L₂ s R W).D₂) ≫
              (decompositionComap L₁ L₂ s R W).branch₁.hom))) ≫
            ((decompositionComap L₁ L₂ s R W).branch₁.inv ≫
              branchComapToBranch₁ L₁ L₂ s R W) := by
          simp only [Category.assoc]
      _ = (e₀.hom ≫ (branchSituation W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection.ker.subschemeι) ≫
            ((decompositionComap L₁ L₂ s R W).branch₁.inv ≫
              branchComapToBranch₁ L₁ L₂ s R W) :=
          congrArg (fun t ↦ (e₀.hom ≫ t) ≫
            ((decompositionComap L₁ L₂ s R W).branch₁.inv ≫
              branchComapToBranch₁ L₁ L₂ s R W)) hker2
      _ = (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection ≫
            branchTotalSpaceToBranch₁ L₁ L₂ s R W :=
          congrArg (fun t ↦ t ≫ ((decompositionComap L₁ L₂ s R W).branch₁.inv ≫
            branchComapToBranch₁ L₁ L₂ s R W)) he₀
  refine Eq.symm (Eq.trans ?_ (Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso C
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
    (((⊥ : (branchSituation W.subscheme
          ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
        (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection) ≫
      branchTotalSpaceToBranch₁ L₁ L₂ s R W)
    ((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
      R.normalize.D₁.subschemeι).subschemeι
    (asIso (⊥ : (branchSituation W.subscheme
          ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≪≫
      e₀ ≪≫ ((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
        ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)).symm ≪≫ e₂) ?_ (k + 1)))
  · refine Eq.trans (congrArg (Stacks.Chow.properPushforward C
      ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (branchTotalSpaceToBranch₁ L₁ L₂ s R W)
      (branchTotalSpaceToBranch₁_comp_base L₁ L₂ s R W C sY sD hsD) (k + 1))
      (Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
        C sD ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
        (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection
        (Stacks.Chow.zeroSection_comp_totalSpaceToBase_comp C
          (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)) sD)
        (⊥ : (branchSituation W.subscheme
          ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι
        (k + 1))) ?_
    exact Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp
      C ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (branchTotalSpaceToBranch₁ L₁ L₂ s R W)
      (branchTotalSpaceToBranch₁_comp_base L₁ L₂ s R W C sY sD hsD) _ (k + 1)
  · calc ((⊥ : (branchSituation W.subscheme
            ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
          (e₀.hom ≫ (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫ e₂.hom))) ≫
        ((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
          R.normalize.D₁.subschemeι).subschemeι
        = (⊥ : (branchSituation W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
            (e₀.hom ≫ (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection
                W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫
              (e₂.hom ≫ ((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
                R.normalize.D₁.subschemeι).subschemeι))) := by
          simp only [Category.assoc]
      _ = (⊥ : (branchSituation W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
            (e₀.hom ≫ (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection
                W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫
              (Scheme.IdealSheafData.inclusion (le_sup_left :
                  (decompositionComap L₁ L₂ s R W).D₁ ≤
                    (decompositionComap L₁ L₂ s R W).D₁ ⊔
                      (decompositionComap L₁ L₂ s R W).D₂) ≫
                branchComapToBranch₁ L₁ L₂ s R W))) :=
          congrArg (fun t ↦ (⊥ : (branchSituation W.subscheme
                ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                (pullbackTensorSection W.subschemeι L₁ L₂ s)
                ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
              (e₀.hom ≫ (((decompositionComap L₁ L₂ s R W).intersectionIsoKerZeroSection
                W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                (pullbackTensorSection W.subschemeι L₁ L₂ s)).inv ≫ t))) he₂
      _ = (⊥ : (branchSituation W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
            ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                (pullbackTensorSection W.subschemeι L₁ L₂ s)
                ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection ≫
              branchTotalSpaceToBranch₁ L₁ L₂ s R W) :=
          congrArg (fun t ↦ (⊥ : (branchSituation W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫ t)
            ho
      _ = ((⊥ : (branchSituation W.subscheme
              ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫
            (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).zeroSection) ≫
            branchTotalSpaceToBranch₁ L₁ L₂ s R W := (Category.assoc _ _ _).symm

/-! ### The cap product on the bundle's base, read on the total space -/

include h₁ h₂ in
/-- **`L₂|_W`, restricted to the restricted divisor, is invertible** — at the spelling
`(branchSituation …).X` of the bundle's base. -/
theorem isInvertible_pullback_zeroIdeal_pullbackTensorSection_pullback :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.sheaf.obj
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.ringCatSheaf.property
      ((Scheme.Modules.pullback (zeroIdeal W.subscheme
          ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι).obj
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)) :=
  Stacks.Divisors.pullback_isInvertible _ _

attribute [local instance] isInvertible_pullback_zeroIdeal_pullbackTensorSection_pullback

include h₁ h₂ hsD in
/-- **The last sentence of the case `W ⊆ D` of [Stacks, Tag 0F98], half way: `[W₁ ∩ W₂]` against
`j_*π^*(c₁(L₂|_{D'}) ∩ [D'])`.** The two differ by a cycle rationally equivalent to zero on `D₁`
witnessed inside the preimage of `W`. -/
theorem cycleAssociatedToClosedSubscheme_comap_branch₁_sub_properPushforward_isRatEquivZeroWithin
    (k : ℤ) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      (Stacks.Chow.cycleAssociatedToClosedSubscheme C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          ((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
            R.normalize.D₁.subschemeι).subschemeι (k + 1) -
        Stacks.Chow.properPushforward C
          ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          (branchTotalSpaceToBranch₁ L₁ L₂ s R W)
          (branchTotalSpaceToBranch₁_comp_base L₁ L₂ s R W C sY sD hsD) (k + 1)
          (Stacks.Chow.flatPullback C
            ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD) sD
            (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase rfl 1
            (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)
              (pullbackTensorSection W.subschemeι L₁ L₂ s)
              ((Scheme.Modules.pullback W.subschemeι).obj L₂)).relativeDimension_totalSpaceToBase
            k ((Stacks.Chow.firstChernCapRule C sD k
                (Stacks.Chow.firstChernComponentCycleRule C sD k
                  ((Scheme.Modules.pullback (zeroIdeal W.subscheme
                      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι).obj
                    ((Scheme.Modules.pullback W.subschemeι).obj L₂)))).extendCycleGroup
              (Stacks.Chow.cycleAssociatedToClosedSubscheme C sD
                (⊥ : (branchSituation W.subscheme
                  ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                  ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                  (pullbackTensorSection W.subschemeι L₁ L₂ s)
                  ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι
                (k + 1)))))
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) := by
  have hclause :=
    isRationallyEquivalentToZeroWithin_properPushforward_zeroSection_branchSituation_subschemeι
      L₁ L₂ s W ((Scheme.Modules.pullback W.subschemeι).obj L₂) C sD k
      (Stacks.Chow.cycleAssociatedToClosedSubscheme C sD
        (⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)
          (pullbackTensorSection W.subschemeι L₁ L₂ s)
          ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι (k + 1))
      _ rfl (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (branchTotalSpaceToBranch₁ L₁ L₂ s R W)
      (branchTotalSpaceToBranch₁_comp_base L₁ L₂ s R W C sY sD hsD)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p)
      ((decompositionComap L₁ L₂ s R W).branch₁.inv ≫
        (decompositionComap L₁ L₂ s R W).p₁ ≫
          (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι)
      (branchTotalSpaceToBranch₁_comp_subschemeι_comp_proj L₁ L₂ s R W)
  refine Eq.mpr (congrArg (fun z ↦ Stacks.Chow.IsRationallyEquivalentToZeroWithin C
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
    (z - Stacks.Chow.properPushforward C
      ((branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)
        (pullbackTensorSection W.subschemeι L₁ L₂ s)
        ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      (branchTotalSpaceToBranch₁ L₁ L₂ s R W)
      (branchTotalSpaceToBranch₁_comp_base L₁ L₂ s R W C sY sD hsD) (k + 1) _)
    ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)))
    (cycleAssociatedToClosedSubscheme_comap_branch₁_eq L₁ L₂ s R W C sY sD hsD k)) hclause

/-! ### The cap product on the base, compared with the cap product on `D` -/

include h₁ h₂ in
/-- **`δ^*(L₂|_D) ≅ (L₂|_W)|_{D'}`.** The two ways of restricting `L₂` to the restricted divisor
`D'` — through `D` and through `W` — agree, because the two composites `D' ⟶ D ⟶ Y` and
`D' ⟶ W ⟶ Y` are the same morphism, which is
`Stacks.Chow.TensorZeroScheme.zeroIdealBaseChangeMap_comp_subschemeι`.

This is `AlgebraicGeometry.Scheme.Modules.pullbackComp` twice against
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` at that identity of morphisms: the equation is
consumed as the argument of `pullbackCongr`, which is where an equality of morphisms may be
eliminated without putting a scheme under a `cast`. -/
def pullbackZeroIdealBaseChangeIso :
    (Scheme.Modules.pullback (zeroIdeal W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
    ((Scheme.Modules.pullback W.subschemeι).obj L₂)
    (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι).obj
        ((Scheme.Modules.pullback W.subschemeι).obj L₂) ≅
      (Scheme.Modules.pullback (zeroIdealBaseChangeMap s W.subschemeι)).obj
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂) :=
  (Scheme.Modules.pullbackComp (zeroIdeal W.subscheme
    ((Scheme.Modules.pullback W.subschemeι).obj L₁)
    ((Scheme.Modules.pullback W.subschemeι).obj L₂)
    (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι W.subschemeι).app L₂ ≪≫
    (Scheme.Modules.pullbackCongr
        (zeroIdealBaseChangeMap_comp_subschemeι s W.subschemeι).symm).app L₂ ≪≫
      ((Scheme.Modules.pullbackComp (zeroIdealBaseChangeMap s W.subschemeι)
        (zeroIdeal Y L₁ L₂ s).subschemeι).app L₂).symm

attribute [local instance] isClosedImmersion_zeroIdealBaseChangeMap_subschemeι
  isProper_zeroIdealBaseChangeMap_subschemeι

include h₁ h₂ hsD in
/-- **`j_*γ` against `p₁^*(c₁(L₂|_D) ∩ [W|_D])`.** The two differ by a cycle rationally equivalent
to zero on `D₁` witnessed inside the preimage of `W`. -/
theorem properPushforward_flatPullback_sub_flatPullback_isRationallyEquivalentToZeroWithin
    (k : ℤ)
    (hbotInt : IsIntegral (⊥ : (branchSituation W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subscheme)
    (hbotDim : Stacks.Chow.schemeDeltaDimension C
      ((⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫ sD) =
        ((k + 1 : ℤ) : EInt))
    (hWDint : IsIntegral (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subscheme)
    (hWDdim : Stacks.Chow.schemeDeltaDimension C
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      (Stacks.Chow.properPushforward C ((branchSituation W.subscheme
            ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD)
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          (branchTotalSpaceToBranch₁ L₁ L₂ s R W)
          (branchTotalSpaceToBranch₁_comp_base L₁ L₂ s R W C sY sD hsD) (k + 1)
          (Stacks.Chow.flatPullback C ((branchSituation W.subscheme
            ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase ≫ sD) sD
            (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).totalSpaceToBase rfl 1
            (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)
            (pullbackTensorSection W.subschemeι L₁ L₂ s)
            ((Scheme.Modules.pullback W.subschemeι).obj L₂)).relativeDimension_totalSpaceToBase
            k ((Stacks.Chow.firstChernCapRule C sD k
                (Stacks.Chow.firstChernComponentCycleRule C sD k
                  ((Scheme.Modules.pullback (zeroIdeal W.subscheme
                      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι).obj
                    ((Scheme.Modules.pullback W.subschemeι).obj L₂)))).extendCycleGroup
              (Stacks.Chow.cycleAssociatedToClosedSubscheme C sD
                (⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
                  ((Scheme.Modules.pullback W.subschemeι).obj L₂)
                  (pullbackTensorSection W.subschemeι L₁ L₂ s)
                  ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι
                    (k + 1)))) -
        Stacks.Chow.flatPullback C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
          (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
          ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
          (Stacks.Chow.firstChernComponentCycle C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
            (Stacks.Chow.firstChernComponentCycleRule C
              ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂))
            (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim))
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.sheaf.obj
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.ringCatSheaf.property
      ((Scheme.Modules.pullback (zeroIdealBaseChangeMap s W.subschemeι)).obj
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂)) :=
    Stacks.Divisors.pullback_isInvertible _ _
  -- `δ` and the comparison immersion `g`, with their sources and targets pinned at the spelling
  -- `(branchSituation …).X` of the bundle's base, which is where `sD` types them
  have : @IsClosedImmersion
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X
      (zeroIdeal Y L₁ L₂ s).subscheme (zeroIdealBaseChangeMap s W.subschemeι) :=
    isClosedImmersion_zeroIdealBaseChangeMap_subschemeι L₁ L₂ s W
  have : @IsClosedImmersion (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subscheme
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X
      (zeroIdealBaseChangeIsoComap L₁ L₂ s W).hom :=
    inferInstanceAs (IsClosedImmersion (zeroIdealBaseChangeIsoComap L₁ L₂ s W).hom)
  have : @IsProper (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subscheme
      (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X
      (zeroIdealBaseChangeIsoComap L₁ L₂ s W).hom :=
    inferInstanceAs (IsProper (zeroIdealBaseChangeIsoComap L₁ L₂ s W).hom)
  -- the two comparisons on `D'`
  have hiso := Stacks.Chow.firstChernComponentCycle_sub_isRationallyEquivalentToZeroWithin_of_iso
    C sD k ((Scheme.Modules.pullback (zeroIdeal W.subscheme
      ((Scheme.Modules.pullback W.subschemeι).obj L₁)
    ((Scheme.Modules.pullback W.subschemeι).obj L₂)
    (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι).obj
      ((Scheme.Modules.pullback W.subschemeι).obj L₂))
    ((Scheme.Modules.pullback (zeroIdealBaseChangeMap s W.subschemeι)).obj
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂))
    (pullbackZeroIdealBaseChangeIso L₁ L₂ s W)
    (⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData) hbotInt hbotDim
  have hamb :=
    Stacks.Chow.firstChernComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin
      C sD ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) (zeroIdealBaseChangeMap s W.subschemeι) hsD k
      ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂)
      (⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData) hbotInt hbotDim
      (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι)
      ((Scheme.IdealSheafData.map_bot (zeroIdealBaseChangeMap s W.subschemeι)).trans
        (ker_zeroIdealBaseChangeMap_subschemeι L₁ L₂ s W))
      (zeroIdealBaseChangeIsoComap L₁ L₂ s W).hom
      (zeroIdealBaseChangeIsoComap_hom_comp L₁ L₂ s W) hWDint hWDdim
  have hD' := isRationallyEquivalentToZeroWithin_sub_add_sub C hiso hamb
  -- push the comparison along the closed immersion `δ`
  have hpush :=
    Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion_of_within
      C sD ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) (zeroIdealBaseChangeMap s W.subschemeι) hsD k
      (⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
       ((Scheme.Modules.pullback W.subschemeι).obj L₂)
       (pullbackTensorSection W.subschemeι L₁ L₂ s)
       ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).support.isClosed hD'
  rw [Stacks.Chow.properPushforward_sub C sD ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
    (zeroIdealBaseChangeMap s W.subschemeι) hsD k] at hpush
  -- the two pushforwards compose into the immersion of `W|_D`
  have hgfac : (zeroIdealBaseChangeIsoComap L₁ L₂ s W).hom ≫ sD =
      (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY := by
    rw [← hsD, ← Category.assoc, zeroIdealBaseChangeIsoComap_hom_comp]
  have hF4 : Stacks.Chow.properPushforward C sD ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
        (zeroIdealBaseChangeMap s W.subschemeι) hsD k
        (Stacks.Chow.properPushforward C
          ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
            (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) sD
          (zeroIdealBaseChangeIsoComap L₁ L₂ s W).hom hgfac k
          (Stacks.Chow.firstChernComponentCycleRule C
            ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
            ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂)
            (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim)) =
      Stacks.Chow.firstChernComponentCycle C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
        (Stacks.Chow.firstChernComponentCycleRule C
          ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
          ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂))
        (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim :=
    (congrFun (Stacks.Chow.properPushforward_comp C
        ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
          (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) sD
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
        (zeroIdealBaseChangeIsoComap L₁ L₂ s W).hom (zeroIdealBaseChangeMap s W.subschemeι)
        hgfac hsD k)
      (Stacks.Chow.firstChernComponentCycleRule C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
        ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂)
        (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim)).trans
      (Stacks.Chow.properPushforward_hom_congr C
        ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
          (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
        (zeroIdealBaseChangeIsoComap_hom_comp L₁ L₂ s W) _ rfl k _)
  rw [hF4] at hpush
  -- the image of `δ` lies in the support of `W|_D`
  have hδfac : zeroIdealBaseChangeMap s W.subschemeι =
      (zeroIdealBaseChangeIsoComap L₁ L₂ s W).inv ≫
        (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι :=
    ((zeroIdealBaseChangeIsoComap L₁ L₂ s W).inv_hom_id_assoc
        (zeroIdealBaseChangeMap s W.subschemeι)).symm.trans
      (congrArg (fun t ↦ (zeroIdealBaseChangeIsoComap L₁ L₂ s W).inv ≫ t)
        (zeroIdealBaseChangeIsoComap_hom_comp L₁ L₂ s W))
  have hsub : (zeroIdealBaseChangeMap s W.subschemeι).base ''
        ((⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
       ((Scheme.Modules.pullback W.subschemeι).obj L₂)
       (pullbackTensorSection W.subschemeι L₁ L₂ s)
       ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).support :
          Set (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
       ((Scheme.Modules.pullback W.subschemeι).obj L₂)
       (pullbackTensorSection W.subschemeι L₁ L₂ s)
       ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X) ⊆
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).support :
        Set (zeroIdeal Y L₁ L₂ s).subscheme) := by
    rintro x ⟨y, -, rfl⟩
    rw [← (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).range_subschemeι]
    exact ⟨(zeroIdealBaseChangeIsoComap L₁ L₂ s W).inv.base y,
      congrArg (fun t ↦ t.base y) hδfac.symm⟩
  -- the `p₁`-preimage of the support of `W|_D` is the preimage of `W` in `D₁`
  have hcar : R.normalize.p₁.base ⁻¹'
        ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).support :
          Set (zeroIdeal Y L₁ L₂ s).subscheme) =
      (R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y) := by
    rw [preimage_branch₁_proj, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage]
  -- Stacks 02S1 with its carrier retained
  have h02S1 := Stacks.Chow.flatPullback_isRationallyEquivalentToZeroWithin C
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
    ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
    (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
    ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k (hpush.mono hsub)
  rw [map_sub] at h02S1
  -- `j_*γ` is the flat pullback along `p₁` of `δ_*` of the component cycle on `D'`
  have hC2 := (Stacks.Chow.firstChernCapRule C sD k
    (Stacks.Chow.firstChernComponentCycleRule C sD k
      ((Scheme.Modules.pullback (zeroIdeal W.subscheme
        ((Scheme.Modules.pullback W.subschemeι).obj L₁)
      ((Scheme.Modules.pullback W.subschemeι).obj L₂)
      (pullbackTensorSection W.subschemeι L₁ L₂ s)).subschemeι).obj
        ((Scheme.Modules.pullback
          W.subschemeι).obj L₂)))).extendCycleGroup_cycleAssociatedToClosedSubscheme
    (⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)
     (pullbackTensorSection W.subschemeι L₁ L₂ s)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData) hbotInt hbotDim
  have hgoal := Eq.trans
    (properPushforward_branchTotalSpaceToBranch₁_flatPullback_totalSpaceToBase
      L₁ L₂ s R W C sY sD hsD k _)
    (congrArg (fun z ↦ Stacks.Chow.flatPullback C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
      ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
      (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
      ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
      (Stacks.Chow.properPushforward C sD ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY)
        (zeroIdealBaseChangeMap s W.subschemeι) hsD k z)) hC2)
  exact Eq.mp (congrArg (fun z ↦ Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      (z - Stacks.Chow.flatPullback C
        (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
        ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
        (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
        ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
        (Stacks.Chow.firstChernComponentCycle C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
          (Stacks.Chow.firstChernComponentCycleRule C
            ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
            ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂))
          (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim))
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)))
    hgoal.symm) (h02S1.mono (le_of_eq hcar))

/-! ### The last sentence, and the sum of the four comparisons -/

include h₁ h₂ hsD in
/-- **The last sentence of the case `W ⊆ D` of [Stacks, Tag 0F98]: `[W₁ ∩ W₂]` against
`p₁^*(c₁(L₂|_D) ∩ [W|_D])`.** The two differ by a cycle rationally equivalent to zero on `D₁`
witnessed inside the preimage of `W`. -/
theorem cycleAssociatedToClosedSubscheme_comap_branch₁_sub_flatPullback_isRatEquivZeroWithin
    (k : ℤ)
    (hbotInt : IsIntegral (⊥ : (branchSituation W.subscheme
     ((Scheme.Modules.pullback W.subschemeι).obj L₁)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)
     (pullbackTensorSection W.subschemeι L₁ L₂ s)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subscheme)
    (hbotDim : Stacks.Chow.schemeDeltaDimension C
      ((⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)
     (pullbackTensorSection W.subschemeι L₁ L₂ s)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫ sD) =
       ((k + 1 : ℤ) : EInt))
    (hWDint : IsIntegral (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subscheme)
    (hWDdim : Stacks.Chow.schemeDeltaDimension C
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt)) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      (Stacks.Chow.cycleAssociatedToClosedSubscheme C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          ((R.normalize.D₂ ⊔ W.comap R.normalize.p).comap
            R.normalize.D₁.subschemeι).subschemeι (k + 1) -
        Stacks.Chow.flatPullback C
          (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY)
          ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) R.normalize.p₁
          (proj₁_comp_zeroIdeal_subschemeι_comp C Y L₁ L₂ s R sY) 1
          ((Decomposition.relativeDimension_p₁ Y L₁ L₂ s R.normalize)) k
          (Stacks.Chow.firstChernComponentCycle C ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
            (Stacks.Chow.firstChernComponentCycleRule C
              ((zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) k
              ((Scheme.Modules.pullback (zeroIdeal Y L₁ L₂ s).subschemeι).obj L₂))
            (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι) hWDint hWDdim))
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) :=
  isRationallyEquivalentToZeroWithin_sub_add_sub C
      (cycleAssociatedToClosedSubscheme_comap_branch₁_sub_properPushforward_isRatEquivZeroWithin
        L₁ L₂ s R W C sY sD hsD k)
      (properPushforward_flatPullback_sub_flatPullback_isRationallyEquivalentToZeroWithin
        L₁ L₂ s R W C sY sD hsD k hbotInt hbotDim hWDint hWDdim)

include h₁ h₂ hsD in
/-- **The case `W ⊆ D` of [Stacks, Tag 0F98] at a prime cycle.** For `W ⊆ Y` an integral closed
subscheme of δ-dimension `k+1` contained in the divisor `D`, the two cycles `i₁^*p^*[W]` and
`p₁^*i^*[W]` differ by a cycle rationally equivalent to zero on `D₁` witnessed inside the
preimage of `W`. -/
theorem leftRule_cycle_sub_rightRule_cycle_isRationallyEquivalentToZeroWithin_of_le
    (k : ℤ) (hWint : IsIntegral W.subscheme)
    (hDim : Stacks.Chow.schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hW : zeroIdeal Y L₁ L₂ s ≤ W)
    (hW₁int : IsIntegral (R.normalize.D₁ ⊔ W.comap R.normalize.p).subscheme)
    (hW₁dim : Stacks.Chow.schemeDeltaDimension C
      ((R.normalize.D₁ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) =
        ((k + 1 + 1 : ℤ) : EInt))
    (hW₂int : IsIntegral (R.normalize.D₂ ⊔ W.comap R.normalize.p).subscheme)
    (hW₂dim : Stacks.Chow.schemeDeltaDimension C
      ((R.normalize.D₂ ⊔ W.comap R.normalize.p).subschemeι ≫ R.normalize.p ≫ sY) =
        ((k + 1 + 1 : ℤ) : EInt))
    (hnle : ¬ R.normalize.D₁ ≤ R.normalize.D₂ ⊔ W.comap R.normalize.p)
    (hbotInt : IsIntegral (⊥ : (branchSituation W.subscheme
     ((Scheme.Modules.pullback W.subschemeι).obj L₁)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)
     (pullbackTensorSection W.subschemeι L₁ L₂ s)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subscheme)
    (hbotDim : Stacks.Chow.schemeDeltaDimension C
      ((⊥ : (branchSituation W.subscheme ((Scheme.Modules.pullback W.subschemeι).obj L₁)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)
     (pullbackTensorSection W.subschemeι L₁ L₂ s)
     ((Scheme.Modules.pullback W.subschemeι).obj L₂)).X.IdealSheafData).subschemeι ≫ sD) =
       ((k + 1 : ℤ) : EInt))
    (hWDint : IsIntegral (W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subscheme)
    (hWDdim : Stacks.Chow.schemeDeltaDimension C
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).subschemeι ≫
        (zeroIdeal Y L₁ L₂ s).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hVint : IsIntegral
      ((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁).subscheme)
    (hVdim : Stacks.Chow.schemeDeltaDimension C
      (((W.comap (zeroIdeal Y L₁ L₂ s).subschemeι).comap R.normalize.p₁).subschemeι ≫
        R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) = ((k + 1 + 1 : ℤ) : EInt)) :
    Stacks.Chow.IsRationallyEquivalentToZeroWithin C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      ((leftRule C Y L₁ L₂ s R sY k).cycle W hWint hDim -
        (rightRule C Y L₁ L₂ s R sY k).cycle W hWint hDim)
      ((R.normalize.D₁.subschemeι ≫ R.normalize.p).base ⁻¹' (W.support : Set Y)) := by
  have htot := Stacks.Chow.isRationallyEquivalentToZeroWithin_add C
    (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
    (Stacks.Chow.isRationallyEquivalentToZeroWithin_add C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      (gysinRuleBranch₁_cycle_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_le
        C Y L₁ L₂ s R sY k W hW₁int hW₁dim hWDint hWDdim hVint hVdim)
      (cycleAssociatedToClosedSubscheme_comap_branch₁_sub_flatPullback_isRatEquivZeroWithin
        L₁ L₂ s R W C sY sD hsD k hbotInt hbotDim hWDint hWDdim))
    (Stacks.Chow.isRationallyEquivalentToZeroWithin_neg C
      (R.normalize.D₁.subschemeι ≫ R.normalize.p ≫ sY) (k + 1)
      (rightRule_cycle_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_le
        C Y L₁ L₂ s R sY k W hWint hDim hW hWDint hWDdim))
  convert htot using 1
  rw [leftRule_cycle_eq_add_of_le C Y L₁ L₂ s R sY k W hWint hDim hW hW₁int hW₁dim hW₂int hW₂dim
    hnle]
  abel

end Stacks.Chow.TensorZeroScheme

end
