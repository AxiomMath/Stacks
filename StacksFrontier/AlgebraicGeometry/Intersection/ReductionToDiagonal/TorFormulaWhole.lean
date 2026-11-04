module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.StructureSheafCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.FlatPullbackVariety
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.AssociatedToModule
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.ProperIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaAdditivity
public import
  StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaSubvarietyCase
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorSideAdditivity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafIso
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0B0W: the Tor formula for the intersection product of two coherent sheaves

Let `X` be a nonsingular variety over an algebraically closed field — the chapter's convention,
Tag 0AZ8 — and let `ℱ`, `𝒢` be coherent `𝒪_X`-modules with

`dim (Supp ℱ) ≤ r`,  `dim (Supp 𝒢) ≤ s`,  `dim (Supp ℱ ∩ Supp 𝒢) ≤ r + s - dim X`.

Then the cycles `[ℱ]_r` and `[𝒢]_s` intersect properly and

`[ℱ]_r · [𝒢]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_{r + s - dim X}`.

That is Tag 0B0W, and it is `Stacks.Intersection.ReductionToDiagonal.torFormula` below.

## The proof

The properness clause is dimension bookkeeping and is
`Stacks.Intersection.ReductionToDiagonal.intersectProperly_coherentSheafCycle`. For the equality
of cycles the source's proof is a dévissage, and this file runs it.

Write `RHS(ℱ, 𝒢) = [ℱ]_r · [𝒢]_s` and `LHS(ℱ, 𝒢) = ∑ₚ (-1)ᵖ [Torₚ(ℱ, 𝒢)]_n`. Both are additive
along a short exact sequence in either variable: for `RHS` that is
`torFormulaCycleIntersectionProduct_coherentSheafCycle_add_left` of this namespace
and its right-hand companion, from additivity of `[-]_r` (Tag 02QZ) and bilinearity of
the product; for `LHS` it is
`Stacks.Intersection.ReductionToDiagonal.intersectionProductCycle_add_left` and
`intersectionProductCycle_add_right`, from the long exact sequence of `Tor` sheaves and
additivity of length. So the property

`P(ℱ) : for every pair of dimension bounds, LHS(ℱ, 𝒢) = RHS(ℱ, 𝒢)`

passes along extensions, and also from the two outer terms of a short exact sequence to the
first term when that term has the same support as the middle one — which is the case for
`0 → i_* ℐ → i_* 𝒪_Z → i_* (𝒪_Z ⧸ ℐ) → 0` on an integral closed subscheme. Those are exactly the
hypotheses of
`Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_structureSheafAt`, the
dévissage of Tag 01YG run down to the structure sheaves of the closed subvarieties, so `P` holds
on every coherent sheaf as soon as it holds on each `𝒪_V`. Running the dévissage twice, once in
each variable, reduces the whole statement to the pair of structure sheaves, which is
`Stacks.Intersection.ReductionToDiagonal.torFormula_structureSheafAt`.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.torFormula` — **Tag 0B0W**, both clauses.
* `Stacks.Intersection.ReductionToDiagonal.torFormula_coherent` — the equality of cycles alone,
  with the dimension bounds stated pointwise.

## Implementation notes

The dimension bounds are read in two equivalent ways. The statement of the tag uses
`topologicalKrullDim` of the three sets, which is the source's `dim`; the dévissage uses the
pointwise form `∀ w ∈ Supp, relativeDimension w ≤ r`, which is what
`Stacks.Chow.schemeDeltaDimension_reducedSupport_le_iff` says the delta-dimension bound of
`Stacks.Chow.coherentSheafCycle` amounts to and which is the form that descends to a subsheaf.
The two are matched by `Stacks.Chow.relativeDimension_le_of_topologicalKrullDim_le` and
`Stacks.Chow.schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le`, i.e. by
Tag 02QO.

`WithBot ℕ∞` has no subtraction, so the source's `n = r + s - dim X` is written as the relation
`r + s = dim X + n` between natural numbers.

## References

* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 02QZ](https://stacks.math.columbia.edu/tag/02QZ)
* [Stacks Project, Tag 0AZ8](https://stacks.math.columbia.edu/tag/0AZ8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.TorFormula
open Stacks.Chow

namespace Stacks.Intersection.ReductionToDiagonal

universe u

/-! ### The dévissage in the first variable -/

/-- The support of a short exact sequence's first term lies in that of its middle term. -/
private theorem supp_X₁_subset_supp_X₂ {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) : SheafOfModules.supp S.X₁ ⊆ SheafOfModules.supp S.X₂ :=
  have := hS.mono_f
  Stacks.Chow.supp_subset_of_mono S.f

/-- The support of a short exact sequence's last term lies in that of its middle term. -/
private theorem supp_X₃_subset_supp_X₂ {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) : SheafOfModules.supp S.X₃ ⊆ SheafOfModules.supp S.X₂ :=
  have := hS.epi_g
  Stacks.Chow.supp_subset_of_epi S.g

/-- A zero module has empty support. -/
private theorem notMem_supp_of_isZero {X : Scheme.{u}} {F : X.Modules} (hF : IsZero F) (z : X) :
    z ∉ SheafOfModules.supp F := fun hz =>
  (Scheme.Modules.notMem_supp_iff_isZero_stalk F z).mpr
    (Functor.map_isZero (Scheme.Modules.stalkFunctor X z) hF) hz

/-- **The Tor formula for an arbitrary coherent sheaf against the structure sheaf of a closed
subvariety.** The dévissage of Tag 01YG, run down to the structure sheaves, reduces this to
`Stacks.Intersection.ReductionToDiagonal.torFormula_structureSheafAt`. -/
theorem torFormula_right_structureSheafAt (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsVariety k f] [IsLocallyNoetherian X]
    (hX : IsRegular X) (r s n : ℤ) (dX : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) (hrs : r + s = (dX : ℤ) + n) (y : X)
    (hy : ∀ w ∈ SheafOfModules.supp (structureSheafAt y),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s)
    (F : X.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hr : ∀ w ∈ SheafOfModules.supp F,
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r)
    (hn : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp (structureSheafAt y),
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n) :
    letI := hFc
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
        (coherentSheafCycle (fieldChowSituation k) f F r
          (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f F hr))
        (coherentSheafCycle (fieldChowSituation k) f (structureSheafAt y) s
          (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f _ hy))
      = intersectionProductCycle (fieldChowSituation k) f hX F (structureSheafAt y) hFc
          (isCoherent_structureSheafAt y) n
          (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F
            (structureSheafAt y) hFc (isCoherent_structureSheafAt y) n hn) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hd : topologicalKrullDim X ≤ (dX : WithBot ℕ∞) := hdX.le
  refine Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_structureSheafAt X
    (fun F => ∀ (hFc : _root_.SheafOfModules.IsCoherent F)
      (hr' : ∀ w ∈ SheafOfModules.supp F,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r)
      (hn' : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp (structureSheafAt y),
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n),
      letI := hFc
      torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
          (coherentSheafCycle (fieldChowSituation k) f F r
            (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f F hr'))
          (coherentSheafCycle (fieldChowSituation k) f (structureSheafAt y) s
            (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f _ hy))
        = intersectionProductCycle (fieldChowSituation k) f hX F (structureSheafAt y) hFc
            (isCoherent_structureSheafAt y) n
            (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F
              (structureSheafAt y) hFc (isCoherent_structureSheafAt y) n hn'))
    ?_ ?_ ?_ ?_ ?_ F hFc hFc hr hn
  · -- transport along an isomorphism
    rintro F F' e hF hF'c hr' hn'
    have := hF'c
    have hsupp : SheafOfModules.supp F = SheafOfModules.supp F' :=
      SheafOfModules.supp_eq_of_iso e
    have hFc : _root_.SheafOfModules.IsCoherent F :=
      Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e
    have hrF : ∀ w ∈ SheafOfModules.supp F,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r := by
      rwa [hsupp]
    have hnF : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp (structureSheafAt y),
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n := by
      rwa [hsupp]
    rw [← Stacks.Chow.coherentSheafCycle_eq_of_iso (fieldChowSituation k) f e r
        (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f F hrF) _,
      hF hFc hrF hnF]
    exact intersectionProductCycle_congr_left_of_iso (fieldChowSituation k) f hX e
      (structureSheafAt y) hFc hF'c (isCoherent_structureSheafAt y) n _ _
  · -- the zero sheaf
    rintro F hFzero hFc hr' hn'
    have := hFc
    have hsupp := notMem_supp_of_isZero hFzero
    rw [coherentSheafCycle_eq_zero_of_relativeDimension_ne (fieldChowSituation k) f F r _
      (fun z hz => absurd hz (hsupp z))]
    refine Eq.trans (cycleIntersectionProduct_zero_left _ _) ?_
    refine (finsum_eq_zero_of_forall_eq_zero fun i => ?_).symm
    have := isCoherent_torSheaf_of_isRegular X hX F (structureSheafAt y) hFc
      (isCoherent_structureSheafAt y) i
    rw [coherentSheafCycle_eq_zero_of_relativeDimension_ne (fieldChowSituation k) f
      (torSheaf X F (structureSheafAt y) i) n _
      (fun z hz => absurd (supp_torSheaf_subset_inter X F (structureSheafAt y) i hz).1
        (hsupp z)), smul_zero]
  · -- extensions
    rintro S hS h₁ h₂ h₃ hP₁ hP₃ hFc hr' hn'
    have hsub₁ := supp_X₁_subset_supp_X₂ S hS
    have hsub₃ := supp_X₃_subset_supp_X₂ S hS
    have hr₁ : ∀ w ∈ SheafOfModules.supp S.X₁,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r :=
      fun w hw => hr' w (hsub₁ hw)
    have hr₃ : ∀ w ∈ SheafOfModules.supp S.X₃,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r :=
      fun w hw => hr' w (hsub₃ hw)
    have hn₁ : ∀ w ∈ SheafOfModules.supp S.X₁ ∩ SheafOfModules.supp (structureSheafAt y),
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n :=
      fun w hw => hn' w ⟨hsub₁ hw.1, hw.2⟩
    have hn₃ : ∀ w ∈ SheafOfModules.supp S.X₃ ∩ SheafOfModules.supp (structureSheafAt y),
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n :=
      fun w hw => hn' w ⟨hsub₃ hw.1, hw.2⟩
    have := h₁; have := h₂; have := h₃
    rw [torFormulaCycleIntersectionProduct_coherentSheafCycle_add_left (fieldChowSituation k) f hX
        n S hS r (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₁ hr₁)
        (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₂ hr')
        (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₃ hr₃) _,
      hP₁ h₁ hr₁ hn₁, hP₃ h₃ hr₃ hn₃,
      intersectionProductCycle_add_left (fieldChowSituation k) f hX S hS (structureSheafAt y)
        h₁ h₂ h₃ (isCoherent_structureSheafAt y) n _ _ _ dX hd]
  · -- the first term of a short exact sequence with the same support as the middle one
    rintro S hS h₁ h₂ h₃ hsupp hP₂ hP₃ hFc hr' hn'
    have hsub₃ := supp_X₃_subset_supp_X₂ S hS
    have hr₂ : ∀ w ∈ SheafOfModules.supp S.X₂,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r := by
      rwa [hsupp]
    have hr₃ : ∀ w ∈ SheafOfModules.supp S.X₃,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r :=
      fun w hw => hr₂ w (hsub₃ hw)
    have hn₂ : ∀ w ∈ SheafOfModules.supp S.X₂ ∩ SheafOfModules.supp (structureSheafAt y),
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n := by
      rwa [hsupp]
    have hn₃ : ∀ w ∈ SheafOfModules.supp S.X₃ ∩ SheafOfModules.supp (structureSheafAt y),
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n :=
      fun w hw => hn₂ w ⟨hsub₃ hw.1, hw.2⟩
    have := h₁; have := h₂; have := h₃
    have hLHS := torFormulaCycleIntersectionProduct_coherentSheafCycle_add_left
      (fieldChowSituation k) f hX n S hS r
      (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₁ hr')
      (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₂ hr₂)
      (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₃ hr₃)
      (coherentSheafCycle (fieldChowSituation k) f (structureSheafAt y) s
        (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f _ hy))
    have hRHS := intersectionProductCycle_add_left (fieldChowSituation k) f hX S hS
      (structureSheafAt y) h₁ h₂ h₃ (isCoherent_structureSheafAt y) n
      (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX S.X₁
        (structureSheafAt y) h₁ (isCoherent_structureSheafAt y) n hn')
      (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX S.X₂
        (structureSheafAt y) h₂ (isCoherent_structureSheafAt y) n hn₂)
      (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX S.X₃
        (structureSheafAt y) h₃ (isCoherent_structureSheafAt y) n hn₃) dX hd
    rw [hP₂ h₂ hr₂ hn₂, hP₃ h₃ hr₃ hn₃, hRHS] at hLHS
    exact (add_right_cancel hLHS).symm
  · -- the structure sheaves
    rintro x hFc hr' hn'
    exact torFormula_structureSheafAt k f hX r s n dX hdX hrs x y hr' hy hn'

/-! ### The dévissage in the second variable -/

/-- **The Tor formula of Tag 0B0W for two coherent sheaves**, with the source's dimension bounds
read pointwise. The dévissage of Tag 01YG in the second variable reduces this to
`Stacks.Intersection.ReductionToDiagonal.torFormula_right_structureSheafAt`. -/
theorem torFormula_coherent (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] [IsLocallyNoetherian X] (hX : IsRegular X)
    (r s n : ℤ) (dX : ℕ) (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hrs : r + s = (dX : ℤ) + n)
    (F : X.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hr : ∀ w ∈ SheafOfModules.supp F,
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ r)
    (G : X.Modules) (hGc : _root_.SheafOfModules.IsCoherent G)
    (hs : ∀ w ∈ SheafOfModules.supp G,
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s)
    (hn : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp G,
      relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n) :
    letI := hFc
    letI := hGc
    torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
        (coherentSheafCycle (fieldChowSituation k) f F r
          (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f F hr))
        (coherentSheafCycle (fieldChowSituation k) f G s
          (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f G hs))
      = intersectionProductCycle (fieldChowSituation k) f hX F G hFc hGc n
          (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F G hFc hGc
            n hn) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have := hFc
  have hd : topologicalKrullDim X ≤ (dX : WithBot ℕ∞) := hdX.le
  refine Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent_of_structureSheafAt X
    (fun G => ∀ (hGc : _root_.SheafOfModules.IsCoherent G)
      (hs' : ∀ w ∈ SheafOfModules.supp G,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s)
      (hn' : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp G,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n),
      letI := hGc
      torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX n
          (coherentSheafCycle (fieldChowSituation k) f F r
            (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f F hr))
          (coherentSheafCycle (fieldChowSituation k) f G s
            (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f G hs'))
        = intersectionProductCycle (fieldChowSituation k) f hX F G hFc hGc n
            (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F G hFc
              hGc n hn'))
    ?_ ?_ ?_ ?_ ?_ G hGc hGc hs hn
  · -- transport along an isomorphism
    rintro G G' e hG hG'c hs' hn'
    have := hG'c
    have hsupp : SheafOfModules.supp G = SheafOfModules.supp G' :=
      SheafOfModules.supp_eq_of_iso e
    have hGc : _root_.SheafOfModules.IsCoherent G :=
      Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e
    have hsG : ∀ w ∈ SheafOfModules.supp G,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s := by
      rwa [hsupp]
    have hnG : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp G,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n := by
      rwa [hsupp]
    rw [← Stacks.Chow.coherentSheafCycle_eq_of_iso (fieldChowSituation k) f e s
        (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f G hsG) _,
      hG hGc hsG hnG]
    exact intersectionProductCycle_congr_right_of_iso (fieldChowSituation k) f hX F e hFc hGc
      hG'c n _ _
  · -- the zero sheaf
    rintro G hGzero hGc hs' hn'
    have := hGc
    have hsupp := notMem_supp_of_isZero hGzero
    rw [coherentSheafCycle_eq_zero_of_relativeDimension_ne (fieldChowSituation k) f G s _
      (fun z hz => absurd hz (hsupp z))]
    refine Eq.trans (cycleIntersectionProduct_zero_right _ _) ?_
    refine (finsum_eq_zero_of_forall_eq_zero fun i => ?_).symm
    have := isCoherent_torSheaf_of_isRegular X hX F G hFc hGc i
    rw [coherentSheafCycle_eq_zero_of_relativeDimension_ne (fieldChowSituation k) f
      (torSheaf X F G i) n _
      (fun z hz => absurd (supp_torSheaf_subset_inter X F G i hz).2 (hsupp z)), smul_zero]
  · -- extensions
    rintro S hS h₁ h₂ h₃ hP₁ hP₃ hGc hs' hn'
    have hsub₁ := supp_X₁_subset_supp_X₂ S hS
    have hsub₃ := supp_X₃_subset_supp_X₂ S hS
    have hs₁ : ∀ w ∈ SheafOfModules.supp S.X₁,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s :=
      fun w hw => hs' w (hsub₁ hw)
    have hs₃ : ∀ w ∈ SheafOfModules.supp S.X₃,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s :=
      fun w hw => hs' w (hsub₃ hw)
    have hn₁ : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp S.X₁,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n :=
      fun w hw => hn' w ⟨hw.1, hsub₁ hw.2⟩
    have hn₃ : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp S.X₃,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n :=
      fun w hw => hn' w ⟨hw.1, hsub₃ hw.2⟩
    have := h₁; have := h₂; have := h₃
    rw [torFormulaCycleIntersectionProduct_coherentSheafCycle_add_right (fieldChowSituation k) f
        hX n S hS s (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₁ hs₁)
        (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₂ hs')
        (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₃ hs₃) _,
      hP₁ h₁ hs₁ hn₁, hP₃ h₃ hs₃ hn₃,
      intersectionProductCycle_add_right (fieldChowSituation k) f hX S hS F hFc h₁ h₂ h₃ n
        _ _ _ dX hd]
  · -- the first term of a short exact sequence with the same support as the middle one
    rintro S hS h₁ h₂ h₃ hsupp hP₂ hP₃ hGc hs' hn'
    have hsub₃ := supp_X₃_subset_supp_X₂ S hS
    have hs₂ : ∀ w ∈ SheafOfModules.supp S.X₂,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s := by
      rwa [hsupp]
    have hs₃ : ∀ w ∈ SheafOfModules.supp S.X₃,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ s :=
      fun w hw => hs₂ w (hsub₃ hw)
    have hn₂ : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp S.X₂,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n := by
      rwa [hsupp]
    have hn₃ : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp S.X₃,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ n :=
      fun w hw => hn₂ w ⟨hw.1, hsub₃ hw.2⟩
    have := h₁; have := h₂; have := h₃
    have hLHS := torFormulaCycleIntersectionProduct_coherentSheafCycle_add_right
      (fieldChowSituation k) f hX n S hS s
      (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₁ hs')
      (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₂ hs₂)
      (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f S.X₃ hs₃)
      (coherentSheafCycle (fieldChowSituation k) f F r
        (schemeDeltaDimension_reducedSupport_le (fieldChowSituation k) f F hr))
    have hRHS := intersectionProductCycle_add_right (fieldChowSituation k) f hX S hS F hFc
      h₁ h₂ h₃ n
      (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F S.X₁ hFc h₁
        n hn')
      (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F S.X₂ hFc h₂
        n hn₂)
      (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F S.X₃ hFc h₃
        n hn₃) dX hd
    rw [hP₂ h₂ hs₂ hn₂, hP₃ h₃ hs₃ hn₃, hRHS] at hLHS
    exact (add_right_cancel hLHS).symm
  · -- the structure sheaves
    rintro y hGc hs' hn'
    exact torFormula_right_structureSheafAt k f hX r s n dX hdX hrs y hs' F hFc hr hn'

/-! ### Tag 0B0W -/

/-- **Stacks Project, Tag 0B0W.** Let `X` be a nonsingular variety over an algebraically closed
field — the chapter's convention, Tag 0AZ8 — of dimension `dX`, and let `ℱ`, `𝒢` be coherent
`𝒪_X`-modules with `dim (Supp ℱ) ≤ r`, `dim (Supp 𝒢) ≤ s` and
`dim (Supp ℱ ∩ Supp 𝒢) ≤ r + s - dX`. Then the cycles `[ℱ]_r` and `[𝒢]_s` intersect properly and

`[ℱ]_r · [𝒢]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_{r + s - dX}`.

The intersection product of cycles is the one of Tag 0B08, the bilinear extension of the
Section 43.14 product of two closed subvarieties, and the right-hand side is the alternating sum
of Tag 0AZR. -/
@[stacks 0B0W "the whole lemma in the case `r + s ≥ dim X`, the expected dimension being a \
natural number `n`; every case, `r + s < dim X` included, is \
`Stacks.Intersection.ReductionToDiagonal.torFormula_integerDimension`. Here: the properness of \
`[ℱ]_r` and `[𝒢]_s` and \
the Tor formula \
`[ℱ]_r · [𝒢]_s = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_{r + s - dim X}`, for a nonsingular variety over \
an algebraically closed field — the chapter's own convention, Tag 0AZ8 — under the source's own \
three dimension bounds, read as bounds on the topological dimension of the two supports and of \
their intersection. `WithBot ℕ∞` has no subtraction, so `n = r + s - dim X` is the relation \
`r + s = dim X + n`. The left-hand side is the intersection product of Tag 0B08 for the \
Section 43.14 product of two closed subvarieties, and the right-hand side the alternating sum \
of Tag 0AZR."]
theorem torFormula (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] (hX : IsRegular X)
    (F G : X.Modules) (hFc : _root_.SheafOfModules.IsCoherent F)
    (hGc : _root_.SheafOfModules.IsCoherent G) (r s n dX : ℕ)
    (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞)) (hrs : r + s = dX + n)
    (hFr : topologicalKrullDim (SheafOfModules.supp F : Set X) ≤ (r : WithBot ℕ∞))
    (hGs : topologicalKrullDim (SheafOfModules.supp G : Set X) ≤ (s : WithBot ℕ∞))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set X) ≤
      (n : WithBot ℕ∞)) :
    letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    letI := hFc
    letI := hGc
    letI := isFiniteType_of_isCoherent F
    letI := isFiniteType_of_isCoherent G
    have hFr' := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f F r hFr
    have hGs' := schemeDeltaDimension_reducedSupport_le_of_topologicalKrullDim_le k f G s hGs
    have hn : ∀ w ∈ SheafOfModules.supp F ∩ SheafOfModules.supp G,
        relativeDimension (fieldChowSituation k).dimensionFunction f w ≤ (n : ℤ) := fun _w hw =>
      relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k) (fun _ _ => rfl) f
        ((SheafOfModules.isClosed_supp F).inter (SheafOfModules.isClosed_supp G)) hFG hw
    AlgebraicCycle.IntersectProperly
        (coherentSheafCycle (fieldChowSituation k) f F (r : ℤ) hFr')
        (coherentSheafCycle (fieldChowSituation k) f G (s : ℤ) hGs') ∧
      torFormulaCycleIntersectionProduct (fieldChowSituation k) f hX (n : ℤ)
          (coherentSheafCycle (fieldChowSituation k) f F (r : ℤ) hFr')
          (coherentSheafCycle (fieldChowSituation k) f G (s : ℤ) hGs')
        = intersectionProductCycle (fieldChowSituation k) f hX F G hFc hGc (n : ℤ)
            (torSheafDeltaDimension_le_of_forall_mem_inter (fieldChowSituation k) f hX F G hFc
              hGc (n : ℤ) hn) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have := hFc
  have := hGc
  have := isFiniteType_of_isCoherent F
  have := isFiniteType_of_isCoherent G
  refine ⟨?_, ?_⟩
  · refine intersectProperly_coherentSheafCycle k f F G r s _ _ ?_
    calc topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set X) +
          topologicalKrullDim X
        ≤ (n : WithBot ℕ∞) + topologicalKrullDim X := add_le_add_left hFG _
      _ ≤ (n : WithBot ℕ∞) + (dX : WithBot ℕ∞) := add_le_add_right hdX.le _
      _ = (r : WithBot ℕ∞) + (s : WithBot ℕ∞) := by
        rw [← Nat.cast_add, ← Nat.cast_add, show n + dX = r + s by omega]
  · exact torFormula_coherent k f hX (r : ℤ) (s : ℤ) (n : ℤ) dX hdX (by exact_mod_cast hrs)
      F hFc
      (fun w hw => relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k)
        (fun _ _ => rfl) f (SheafOfModules.isClosed_supp F) hFr hw)
      G hGc
      (fun w hw => relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k)
        (fun _ _ => rfl) f (SheafOfModules.isClosed_supp G) hGs hw)
      (fun w hw => relativeDimension_le_of_topologicalKrullDim_le (fieldChowSituation k)
        (fun _ _ => rfl) f ((SheafOfModules.isClosed_supp F).inter
          (SheafOfModules.isClosed_supp G)) hFG hw)

end Stacks.Intersection.ReductionToDiagonal

end
