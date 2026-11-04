module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree

/-!
# A proper morphism contracting no component of a curve is finite

Let `f : X' ⟶ X` be a proper morphism out of a scheme of dimension at most one. If `f` maps no
one-dimensional irreducible component of `X'` to a point, then `f` is finite: two distinct points
of a fibre related by specialization would be the generic point of a one-dimensional component
and a closed point of it, and the closed image of the latter would force `f` to map the whole
component to that point. So every fibre is a `T1` scheme, of dimension at most zero, and a proper
morphism with zero-dimensional fibres is finite (Zariski's main theorem).

Over a field, this applies to `f` whenever `f^*L` is isomorphic to an ample invertible module
for some invertible `L`: an ample module has positive degree on every one-dimensional component
([Stacks, Tag 0B5Y]), while the pullback along a morphism with one-point image is trivial.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isFinite_of_forall_genericPointsOne_exists_ne`.
* `AlgebraicGeometry.Scheme.Hom.isFinite_of_pullback_iso_of_isAmple`.

## References

* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
-/

@[expose] public noncomputable section

open CategoryTheory Topology
open Stacks.AlgebraicGeometry.ComponentDegrees Stacks.AlgebraicGeometry.BirationalCurveFinite

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **A proper morphism out of a scheme of dimension at most one which maps no one-dimensional
irreducible component to a point is finite.** Each fibre is `T1`: if `a ⤳ b` are distinct points
of a fibre over `y`, then `a` is the generic point of a one-dimensional component and `b` is a
closed point (a non-closed `b` would be the generic point of a component inside the closure of
`a`, hence equal to `a`), so `y = f b` is closed and `f` maps the closure of `a` to `y`. A `T1`
scheme has dimension at most zero, and a proper morphism with zero-dimensional fibres is finite. -/
theorem isFinite_of_forall_genericPointsOne_exists_ne {X' X : Scheme.{u}} (f : X' ⟶ X)
    [IsProper f] (hdim : topologicalKrullDim X' ≤ 1)
    (hnc : ∀ ξ ∈ genericPointsOne X', ∃ z ∈ closure ({ξ} : Set X'), f.base z ≠ f.base ξ) :
    IsFinite f := by
  refine isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero f fun y => ?_
  have hT1 : T1Space (f.base ⁻¹' {y}) := by
    rw [t1Space_iff_specializes_imp_eq]
    intro a b hab
    have hab' : a.1 ⤳ b.1 := hab.map continuous_subtype_val
    by_contra hne
    have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
    -- a non-closed point is the generic point of a one-dimensional component
    have hgen : ∀ x : X', ¬ IsClosed ({x} : Set X') → x ∈ genericPointsOne X' := fun x hx =>
      by_contra fun h => hx (isClosed_singleton_of_notMem_genericPointsOne hdim h)
    have ha : a.1 ∈ genericPointsOne X' := hgen _ fun hcl => hne'
      (Set.mem_singleton_iff.mp (hcl.closure_eq ▸ specializes_iff_mem_closure.mp hab')).symm
    -- `b` is closed
    have hb : IsClosed ({b.1} : Set X') := by
      by_contra hb
      have hbg := hgen _ hb
      have hcomp : closure ({b.1} : Set X') ∈ irreducibleComponents X' :=
        (mem_genericPointsOne_iff.mp hbg).1
      have hsub : closure ({b.1} : Set X') ⊆ closure ({a.1} : Set X') :=
        specializes_iff_closure_subset.mp hab'
      have hsup := hcomp.2 (isIrreducible_singleton (x := a.1)).closure hsub
      exact hne' (hab'.antisymm (specializes_iff_closure_subset.mpr hsup)).eq
    -- so `y` is closed, and `f` maps the closure of `a` to `y`
    have hy : IsClosed ({y} : Set X) := by
      simpa [show f.base b.1 = y from b.2] using f.isClosedMap _ hb
    obtain ⟨z, hz, hzne⟩ := hnc a.1 ha
    have hfz : f.base a.1 ⤳ f.base z := (specializes_iff_mem_closure.mpr hz).map f.continuous
    rw [show f.base a.1 = y from a.2] at hfz hzne
    exact hzne (Set.mem_singleton_iff.mp (hy.closure_eq ▸ specializes_iff_mem_closure.mp hfz))
  have : T1Space (f.fiber y) := (f.fiberHomeo y).isEmbedding.t1Space
  simpa using Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space
    (S := f.fiber y)

/-- **A proper morphism pulling an invertible module back to an ample one is finite**, on a
scheme proper of dimension at most one over a field. Let `g : X' ⟶ Spec k` be proper with
`dim X' ≤ 1`, `f : X' ⟶ X` proper, `L` invertible on `X` and `f^*L ≅ L₀` with `L₀` ample. If `f`
mapped a one-dimensional component `E` of `X'` to a point, `L₀|_E ≅ (f|_E)^*L` would be trivial,
of degree zero; but an ample module has positive degree on `E` ([Stacks, Tag 0B5Y]). So
`isFinite_of_forall_genericPointsOne_exists_ne` applies. -/
theorem isFinite_of_pullback_iso_of_isAmple (k : Type u) [Field k] {X' X : Scheme.{u}}
    (g : X' ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim X' ≤ 1)
    (f : X' ⟶ X) [IsProper f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (L₀ : X'.Modules)
    [SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 L₀]
    (hL₀ : Scheme.Modules.IsAmple X' L₀) (e : (Scheme.Modules.pullback f).obj L ≅ L₀) :
    IsFinite f := by
  refine f.isFinite_of_forall_genericPointsOne_exists_ne hdim fun ξ hξ => ?_
  by_contra hcon'
  have hcon : ∀ z ∈ closure ({ξ} : Set X'), f.base z = f.base ξ := fun z hz =>
    by_contra fun h => hcon' ⟨z, hz, h⟩
  let ξ' : genericPointsOne X' := ⟨ξ, hξ⟩
  let ι := reducedComponentι X' ξ'
  have := isProper_reducedComponentι_comp k g ξ'
  have hdimE := topologicalKrullDim_reducedComponent_le X' hdim ξ'
  have hpos := invertibleCurveDegree_reducedComponent_pos_of_isAmple k g hdim L₀ hL₀ ξ'
  have hmem : ∀ w, ι.base w ∈ closure ({ξ} : Set X') := fun w => by
    have hw : ι.base w ∈ Set.range ι.base := ⟨w, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at hw
    exact hw
  have hzero := invertibleCurveDegree_pullback_eq_zero_of_forall_eq k (ι ≫ g) hdimE (ι ≫ f) L
    (f.base ξ) fun w => hcon _ (hmem w)
  let e' : (Scheme.Modules.pullback (ι ≫ f)).obj L ≅ (Scheme.Modules.pullback ι).obj L₀ :=
    ((Scheme.Modules.pullbackComp ι f).app L).symm ≪≫ (Scheme.Modules.pullback ι).mapIso e
  rw [invertibleCurveDegree_eq_of_iso k (ι ≫ g) hdimE e'] at hzero
  exact hpos.ne' hzero

end AlgebraicGeometry.Scheme.Hom

end
