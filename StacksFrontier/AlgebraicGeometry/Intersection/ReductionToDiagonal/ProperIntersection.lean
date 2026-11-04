module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProduct
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.Base
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.Defs
public import
  StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.DiagonalRegularImmersion
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension

/-!
# Proper intersections in the reduction to the diagonal

Let `X` be a variety over a field `k`. Two cycles on `X` intersect properly when every pair of
components occurring in them meets in dimension at most the expected one. This file proves the
two properness statements of the section "Reduction to the diagonal".

For coherent `𝒪_X`-modules `ℱ` and `𝒢` whose supports have dimension at most `r` and `s` and meet
in dimension at most `r + s - dim X`, the cycles `[ℱ]_r` and `[𝒢]_s` intersect properly. For an
`r`-cycle `α` and an `s`-cycle `β` that intersect properly, the exterior product `α × β` and the
cycle `[Δ]` of the diagonal intersect properly on `X ×_k X`.

Dimensions are `WithBot ℕ∞`-valued, so the condition `dim(Supp ℱ ∩ Supp 𝒢) ≤ r + s - dim X` is
written additively, with `dim X` on the left.

## Main definitions

* `Stacks.Intersection.ReductionToDiagonal.diagonalCycle` — the cycle `[Δ]` of the diagonal.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.intersectProperly_coherentSheafCycle` — the cycles of
  two coherent sheaves intersect properly.
* `Stacks.Intersection.ReductionToDiagonal.intersectProperly_exteriorProduct_diagonalCycle` — the
  exterior product `α × β` and the diagonal cycle `[Δ]` intersect properly.

## References

* [Stacks Project, Lemma 43.19.2 (Tag 0B0U)](https://stacks.math.columbia.edu/tag/0B0U)
* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 0AZM](https://stacks.math.columbia.edu/tag/0AZM)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow

namespace Stacks.Intersection.ReductionToDiagonal

universe u

/-! ### Dimension of a point closure -/

/-- An irreducible closed subset is the closure of its generic point. -/
private theorem coe_eq_closure_genericPoint {Y : Scheme.{u}} (W : IrreducibleCloseds Y) :
    (W : Set Y) = closure {W.isIrreducible.genericPoint} :=
  (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).symm

/-- The closure of a point of relative dimension `n` has topological dimension `n`. -/
private theorem topologicalKrullDim_closure_singleton_of_relativeDimension_eq (k : Type u)
    [Field k] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] (z : Y) (n : ℕ)
    (h : relativeDimension (fieldChowSituation k).dimensionFunction p z = (n : ℤ)) :
    topologicalKrullDim (closure ({z} : Set Y)) = (n : WithBot ℕ∞) := by
  rw [topologicalKrullDim_closure_singleton_eq k p z, h]
  simp

/-- An irreducible closed subset whose generic point lies in a closed set lies in that set. -/
private theorem coe_subset_of_genericPoint_mem {Y : Scheme.{u}} {T : Set Y} (hT : IsClosed T)
    (W : IrreducibleCloseds Y) (h : W.isIrreducible.genericPoint ∈ T) : (W : Set Y) ⊆ T := by
  rw [coe_eq_closure_genericPoint W]
  exact hT.closure_subset_iff.2 (by simpa using h)

/-! ### The cycles of two coherent sheaves intersect properly -/

/-- Let `ℱ` and `𝒢` be coherent `𝒪_X`-modules whose supports have dimension at most `r` and `s`
and meet in dimension at most `r + s - dim X`. Then the cycles `[ℱ]_r` and `[𝒢]_s` intersect
properly. -/
@[stacks 0B0W "the clause that `[ℱ]_r` and `[𝒢]_s` intersect properly, for any scheme locally \
of finite type over a field: no nonsingularity and no variety hypothesis is used. The Tor \
formula `[ℱ]_r · [𝒢]_s = ∑ (-1)^p [Tor_p(ℱ, 𝒢)]_{r+s-dim X}` is not stated, because the \
intersection product of two cycles on a nonsingular variety is not defined in this library; \
its proof also needs the higher `Tor_i` of Stacks 0B0T, which is \
`Stacks.Intersection.Diagonal.torDiagonalIso`"]
theorem intersectProperly_coherentSheafCycle (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (F G : X.Modules)
    [F.IsCoherent] [G.IsCoherent] (r s : ℕ)
    (hF : schemeDeltaDimension (fieldChowSituation k)
      ((reducedSupport F).subschemeι ≫ f) ≤ ((r : ℤ) : EInt))
    (hG : schemeDeltaDimension (fieldChowSituation k)
      ((reducedSupport G).subschemeι ≫ f) ≤ ((s : ℤ) : EInt))
    (hFG : topologicalKrullDim (SheafOfModules.supp F ∩ SheafOfModules.supp G : Set X) +
      topologicalKrullDim X ≤ (r : WithBot ℕ∞) + (s : WithBot ℕ∞)) :
    AlgebraicCycle.IntersectProperly
      (coherentSheafCycle (fieldChowSituation k) f F (r : ℤ) hF)
      (coherentSheafCycle (fieldChowSituation k) f G (s : ℤ) hG) := by
  classical
  intro W V hW hV
  have hWc : sheafCycleCoeff (fieldChowSituation k) f F (r : ℤ)
      W.isIrreducible.genericPoint ≠ 0 := hW
  have hVc : sheafCycleCoeff (fieldChowSituation k) f G (s : ℤ)
      V.isIrreducible.genericPoint ≠ 0 := hV
  simp only [sheafCycleCoeff, ne_eq, ite_eq_right_iff, Classical.not_imp] at hWc hVc
  obtain ⟨⟨hWsupp, hWdim⟩, -⟩ := hWc
  obtain ⟨⟨hVsupp, hVdim⟩, -⟩ := hVc
  have _ := isFiniteType_of_isCoherent F
  have _ := isFiniteType_of_isCoherent G
  have hWset := coe_subset_of_genericPoint_mem (SheafOfModules.isClosed_supp F) W
    (by simpa using hWsupp)
  have hVset := coe_subset_of_genericPoint_mem (SheafOfModules.isClosed_supp G) V
    (by simpa using hVsupp)
  have hWdim' : topologicalKrullDim (W : Set X) = (r : WithBot ℕ∞) := by
    rw [coe_eq_closure_genericPoint W]
    exact topologicalKrullDim_closure_singleton_of_relativeDimension_eq k f _ r hWdim
  have hVdim' : topologicalKrullDim (V : Set X) = (s : WithBot ℕ∞) := by
    rw [coe_eq_closure_genericPoint V]
    exact topologicalKrullDim_closure_singleton_of_relativeDimension_eq k f _ s hVdim
  rw [AlgebraicGeometry.intersectProperly_iff, hWdim', hVdim']
  exact le_trans (add_le_add_left
    (topologicalKrullDim_le_of_subset (Set.inter_subset_inter hWset hVset)) _) hFG

/-! ### The exterior product and the diagonal -/

/-- A topological embedding is a homeomorphism onto its range. -/
private noncomputable def homeoRange {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    {g : A → B} (hg : Topology.IsEmbedding g) : A ≃ₜ (Set.range g) :=
  (Homeomorph.Set.univ A).symm.trans <|
    (hg.homeomorphImage Set.univ).trans (Homeomorph.setCongr (by rw [Set.image_univ]))

/-- The cycle `[Δ]` of the diagonal of a variety: the prime cycle on `X ×_k X` carried by the
image of the diagonal morphism, with coefficient one. -/
noncomputable def diagonalCycle {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] :
    AlgebraicCycle (pullback f f) ℤ :=
  letI := Classical.decEq (pullback f f : Scheme.{u})
  Function.locallyFinsuppWithin.single ((pullback.diagonal f) (genericPoint X)) 1

/-- The coefficient of `[Δ]` at the generic point of the diagonal is one. -/
@[simp]
theorem diagonalCycle_apply_genericPoint {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] :
    diagonalCycle f ((pullback.diagonal f) (genericPoint X)) = 1 := by
  classical
  simp [diagonalCycle, Function.locallyFinsuppWithin.single_apply]

/-- The cycle of the diagonal is not the zero cycle. -/
theorem diagonalCycle_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] : diagonalCycle f ≠ 0 := by
  intro h
  simpa [h] using diagonalCycle_apply_genericPoint f

/-- The only point carrying a nonzero coefficient in `[Δ]` is the generic point of the
diagonal. -/
private theorem eq_of_diagonalCycle_ne_zero {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f]
    {z : (pullback f f : Scheme.{u})} (hz : diagonalCycle f z ≠ 0) :
    z = (pullback.diagonal f) (genericPoint X) := by
  classical
  by_contra h
  simp [diagonalCycle, Function.locallyFinsuppWithin.single_apply, h] at hz

/-- Let `X` be a variety, let `α` be an `r`-cycle and `β` an `s`-cycle on `X`, and assume `α` and
`β` intersect properly. Then the exterior product `α × β` and the diagonal cycle `[Δ]` intersect
properly on `X ×_k X`. -/
@[stacks 0B0U "part (1): `α × β` and `[Δ]` intersect properly, for any variety over a field: no \
nonsingularity is used. Parts (2) and (3), `Δ_*(α · β) = [Δ] · α × β` and \
`pr_{1,*}([Δ] · α × β) = α · β`, are not stated, because the intersection product of two cycles \
on a nonsingular variety is not defined in this library; their proof also needs the higher \
`Tor_i` of Stacks 0B0T, which is `Stacks.Intersection.Diagonal.torDiagonalIso`"]
theorem intersectProperly_exteriorProduct_diagonalCycle (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] (r s : ℕ)
    (α : CycleGroup (fieldChowSituation k) f (r : ℤ))
    (β : CycleGroup (fieldChowSituation k) f (s : ℤ))
    (hαβ : AlgebraicCycle.IntersectProperly α.1 β.1) :
    AlgebraicCycle.IntersectProperly
      (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1
      (diagonalCycle f) := by
  classical
  have hemb : Topology.IsEmbedding ⇑(pullback.diagonal f) :=
    (pullback.diagonal f).isClosedEmbedding.isEmbedding
  have hfst : ∀ x : X, (pullback.fst f f) ((pullback.diagonal f) x) = x := fun x => by
    show (pullback.diagonal f ≫ pullback.fst f f) x = x
    rw [pullback.diagonal_fst]; rfl
  have hsnd : ∀ x : X, (pullback.snd f f) ((pullback.diagonal f) x) = x := fun x => by
    show (pullback.diagonal f ≫ pullback.snd f f) x = x
    rw [pullback.diagonal_snd]; rfl
  intro W V hW hV
  set z := W.isIrreducible.genericPoint
  set v := (pullback.fst f f) z
  set w := (pullback.snd f f) z
  set Cv : IrreducibleCloseds X := IrreducibleCloseds.closureSingleton v
  set Cw : IrreducibleCloseds X := IrreducibleCloseds.closureSingleton w
  have hVset : (V : Set (pullback f f : Scheme.{u})) = Set.range ⇑(pullback.diagonal f) := by
    rw [coe_eq_closure_genericPoint V, eq_of_diagonalCycle_ne_zero f hV, ← Set.image_singleton,
      (pullback.diagonal f).isClosedEmbedding.closure_image_eq, genericPoint_spec X,
      Set.image_univ]
  have hdimV : topologicalKrullDim (V : Set (pullback f f : Scheme.{u})) =
      topologicalKrullDim X := by
    rw [hVset]
    exact ((homeoRange hemb).isHomeomorph.topologicalKrullDim_eq).symm
  have hcoeff : α.1 v * β.1 w *
      exteriorProductWeight (fieldChowSituation k) f f ((r : ℤ) + (s : ℤ)) v w z ≠ 0 := hW
  have hα : α.1 v ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hcoeff)
  have hβ : β.1 w ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hcoeff)
  have hgenv : Cv.isIrreducible.genericPoint = v :=
    (Cv.isIrreducible.isGenericPoint_genericPoint Cv.isClosed).eq
      (show IsGenericPoint v (Cv : Set X) from rfl)
  have hgenw : Cw.isIrreducible.genericPoint = w :=
    (Cw.isIrreducible.isGenericPoint_genericPoint Cw.isClosed).eq
      (show IsGenericPoint w (Cw : Set X) from rfl)
  have hproper := hαβ Cv Cw (by rwa [hgenv]) (by rwa [hgenw])
  rw [AlgebraicGeometry.intersectProperly_iff] at hproper
  have hdimv : topologicalKrullDim (Cv : Set X) = (r : WithBot ℕ∞) :=
    topologicalKrullDim_closure_singleton_of_relativeDimension_eq k f v r
      ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) f (r : ℤ) α.1).1 α.2 v hα)
  have hdimw : topologicalKrullDim (Cw : Set X) = (s : WithBot ℕ∞) :=
    topologicalKrullDim_closure_singleton_of_relativeDimension_eq k f w s
      ((mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k) f (s : ℤ) β.1).1 β.2 w hβ)
  have hdimW : topologicalKrullDim (W : Set (pullback f f : Scheme.{u})) =
      (r : WithBot ℕ∞) + (s : WithBot ℕ∞) := by
    have hrs := (mem_cyclesOfDimension_iff_forall_point (fieldChowSituation k)
      (pullback.fst f f ≫ f) ((r : ℤ) + (s : ℤ))
      (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).1).1
      (exteriorProduct (fieldChowSituation k) f f (r : ℤ) (s : ℤ) α β).2 z hW
    rw [coe_eq_closure_genericPoint W]
    exact_mod_cast topologicalKrullDim_closure_singleton_of_relativeDimension_eq k
      (pullback.fst f f ≫ f) z (r + s) (by rw [hrs]; push_cast; rfl)
  set S : Set X := ⇑(pullback.diagonal f) ⁻¹' ((W : Set (pullback f f : Scheme.{u})) ∩
    (V : Set (pullback f f : Scheme.{u}))) with hS
  have hSsub : S ⊆ (Cv : Set X) ∩ (Cw : Set X) := by
    intro x hx
    have hxW : (pullback.diagonal f) x ∈ (W : Set (pullback f f : Scheme.{u})) := hx.1
    have hspec : z ⤳ (pullback.diagonal f) x :=
      specializes_iff_mem_closure.2 (by rwa [← coe_eq_closure_genericPoint W])
    exact ⟨specializes_iff_mem_closure.1 (hfst x ▸ hspec.map (pullback.fst f f).continuous),
      specializes_iff_mem_closure.1 (hsnd x ▸ hspec.map (pullback.snd f f).continuous)⟩
  have himg : ⇑(pullback.diagonal f) '' S = (W : Set (pullback f f : Scheme.{u})) ∩
      (V : Set (pullback f f : Scheme.{u})) := by
    rw [hS, Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_self_of_subset_left (hVset ▸ Set.inter_subset_right)
  have hdimInter : topologicalKrullDim ((W : Set (pullback f f : Scheme.{u})) ∩
      (V : Set (pullback f f : Scheme.{u})) : Set (pullback f f : Scheme.{u})) ≤
      topologicalKrullDim ((Cv : Set X) ∩ (Cw : Set X) : Set X) := by
    exact (IsHomeomorph.topologicalKrullDim_eq _
      ((hemb.homeomorphImage S).trans (Homeomorph.setCongr himg)).isHomeomorph).symm.trans_le
      (topologicalKrullDim_le_of_subset hSsub)
  rw [AlgebraicGeometry.intersectProperly_iff, hdimV, hdimW,
    topologicalKrullDim_pullback_of_isVariety k f f]
  calc topologicalKrullDim ((W : Set (pullback f f : Scheme.{u})) ∩
        (V : Set (pullback f f : Scheme.{u})) : Set (pullback f f : Scheme.{u})) +
        (topologicalKrullDim X + topologicalKrullDim X)
      ≤ topologicalKrullDim ((Cv : Set X) ∩ (Cw : Set X) : Set X) +
          (topologicalKrullDim X + topologicalKrullDim X) := add_le_add_left hdimInter _
    _ = topologicalKrullDim ((Cv : Set X) ∩ (Cw : Set X) : Set X) +
          topologicalKrullDim X + topologicalKrullDim X := (add_assoc _ _ _).symm
    _ ≤ topologicalKrullDim (Cv : Set X) + topologicalKrullDim (Cw : Set X) +
          topologicalKrullDim X := add_le_add_left hproper _
    _ = (r : WithBot ℕ∞) + (s : WithBot ℕ∞) + topologicalKrullDim X := by
          rw [hdimv, hdimw]

end Stacks.Intersection.ReductionToDiagonal

end
