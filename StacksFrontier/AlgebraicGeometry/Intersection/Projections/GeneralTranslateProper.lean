module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersectionOfCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionFibrePoint
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.DeterminantHypersurface
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.EndProjectionFinite
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersection
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionProper
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericImageFibre
public import StacksFrontier.RingTheory.Sequence.RegularLocus

/-!
# For a general class the translate meets any closed subvariety properly

Let `C, T` be closed subvarieties of `𝐏(V)`. This file proves that there is a nonempty Zariski
open subset of the parameter space `𝐏 = 𝐏((End V)ᵛ)` every closed point of which is *good* for the
pair `(C, T)`: for every representative `g` of such a class, `C ⊆ U(g)` and `r_g(C)` meets `T`
properly. This is the step the source of Tag 0B1T states as

> a general point `∞ = [g] ∈ ℓ` is a general point of `𝐏` and for such a point `r_g(C) ∩ T` is a
> proper intersection for any closed subvariety `T` of `𝐏(V)`

and leaves without proof. No proper intersection of `C` with `T` is assumed — that is the whole
point of moving `C`.

The argument is the incidence correspondence of Tag 0B1S taken over `C × T`,

`W = {(x, y, [h]) : x ∈ C, y ∈ T, r_h(x) = y}`,

whose dimension is at most `dim C + dim T + (dim V)² - dim V` by
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_transitionVariety_le`. The
projection `π : W ⟶ 𝐏` is a morphism of schemes of finite type over `k` with `W` proper over `k`
and `𝐏` irreducible of dimension `(dim V)² - 1`, so over a nonempty open subset of `𝐏` the
closure of the image of a fibre of `π` under the target projection has dimension at most

`(dim C + dim T + (dim V)² - dim V) - ((dim V)² - 1) = dim C + dim T - dim 𝐏(V)`,

by `AlgebraicGeometry.exists_nonempty_open_topologicalKrullDim_closure_image_fiber_le`, which is
Tag 0B2L for an irreducible piece of the source together with Tag 05F7. Intersecting that open
subset with the invertible locus `G = 𝐏 ∖ Z` makes `U(g) = 𝐏(V)`, so clause (1) is free and
`r_g(C)` has the dimension of `C`; and the closed points of `r_g(C) ∩ T` lie in the image of the
fibre over `[g]` by
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_image_fibre_transitionVarietyToPar`, so the bound
on the fibre is a bound on `dim (r_g(C) ∩ T)`. That is the dimension criterion defining
`AlgebraicGeometry.IntersectProperly`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_nonempty_forall_isGoodEndomorphism`:
  **a nonempty open subset of `𝐏` all of whose closed points are good for `(C, T)`.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.notMem_badParameterLocus_of_mem_generalLocus`: the
  same read on `AlgebraicGeometry.ProjectiveSpaceOfModule.badParameterLocus`, the form Tag 0B1T
  consumes.

## Implementation notes

**Only codimension one is needed, and that is why no proper intersection is assumed.** Tag 0B1S
needs its bad locus to have codimension at least *two*, because a general line through `[id_V]`
has to avoid it entirely; here only the single general point `∞` of the line has to avoid the bad
locus of `(C, T i)`, so codimension one suffices. Codimension one is what the dimension count
above gives with no hypothesis relating `C` and `T`, whereas the codimension-two bound of Tag
0B1S genuinely uses that `C` and `X` already intersect properly — which for `T ⊆ X` of small
dimension is false of the pair `(C, T)`.

**Why the invertible locus.** Two things are wanted of the general class: that `C` lie in `U(g)`,
and that `dim r_g(C) = dim C`. The second is
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_eq` and needs
only `C ⊆ U(g)`; the first is clause (1) of Tag 0B1S and is free on the invertible locus, where
`U(g) = 𝐏(V)` by `AlgebraicGeometry.ProjectiveSpaceOfModule.mapDomain_eq_top`. The invertible
locus is a nonempty open subset of the irreducible `𝐏` — it contains `[id_V]` — so intersecting
with it costs nothing.

**The dimension of `C` as a natural number.** The fibre bound of
`AlgebraicGeometry.exists_nonempty_open_topologicalKrullDim_closure_image_fiber_le` is indexed by
natural numbers, so `dim C` and `dim T` have to be pinned as naturals: they are neither `⊥`, the
subvarieties being nonempty, nor `⊤`, being bounded by `dim 𝐏(V)`, and
`eq_natCast_unbotD_toNat` turns that into a cast. The final inequality then cancels the common
summand `(dim V)² - dim V` with
`Stacks.RegularSequence.FibrewiseLocus.le_of_add_le_add_right_of_ne_bot_of_ne_top`.

## References

* [Stacks Project, Tag 0B1T](https://stacks.math.columbia.edu/tag/0B1T)
* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0AZQ](https://stacks.math.columbia.edu/tag/0AZQ)
* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
  [Nontrivial (ParameterModule k V)]

omit [Nontrivial (ParameterModule k V)] in
/-- **`[id_V]` is an invertible class**, so the invertible locus is nonempty. -/
public theorem identityParameterPoint_mem_invertibleLocus :
    identityParameterPoint k V ∈ invertibleLocus k V := by
  refine (coe_mem_invertibleLocus_iff_det_ne_zero k V
    ((dualEndClosedPointsEquiv k V).symm
      (Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V)))
    LinearMap.id (linearMapId_ne_zero k V) (by rw [Equiv.apply_symm_apply])).mpr ?_
  rw [LinearMap.det_id]
  exact one_ne_zero

omit [IsAlgClosed k] [Nontrivial V] [Nontrivial (ParameterModule k V)] in
/-- **An invertible class has full domain of definition.** A nonzero determinant makes the
endomorphism a unit, and `AlgebraicGeometry.ProjectiveSpaceOfModule.mapDomain_eq_top` applies. -/
public theorem endDomain_eq_top_of_det_ne_zero {g : V →ₗ[k] V} (hdet : LinearMap.det g ≠ 0) :
    endDomain k V g = ⊤ := by
  have hu : IsUnit g := (LinearMap.isUnit_iff_isUnit_det g).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hval : (hu.unit : V →ₗ[k] V) = g := hu.unit_spec
  rw [← hval]
  exact mapDomain_eq_top k V hu.unit

/-- **For a general class the translate of `C` meets `T` properly.** Let `C, T` be closed
subvarieties of `𝐏(V)`. There is a nonempty Zariski open subset of the parameter space
`𝐏 = 𝐏((End V)ᵛ)` such that for every closed point of it and every representative `g` of that
class, `C ⊆ U(g)` and `r_g(C)` intersects `T` properly. Nothing is assumed of the pair `(C, T)`.

This is the sentence the source of Tag 0B1T leaves without proof. -/
public theorem exists_isOpen_nonempty_forall_isGoodEndomorphism
    (C T : IrreducibleCloseds (projectiveSpaceOfModule k V)) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ p : ClosedPoints k (ParameterModule k V),
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ U →
        ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g →
          IsGoodEndomorphism k V (C : Set (projectiveSpaceOfModule k V))
            (T : Set (projectiveSpaceOfModule k V)) g := by
  classical
  have hprojproper : IsProper (projectiveSpaceOfModuleToSpec k V) :=
    isProper_projectiveSpaceOfModuleToSpec k V
  have hparproper : IsProper (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) :=
    isProper_projectiveSpaceOfModuleToSpec k (ParameterModule k V)
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := inferInstance
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) :=
    inferInstance
  have hjac : JacobsonSpace (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)
  set Cs := (C : Set (projectiveSpaceOfModule k V)) with hCs
  set Ts := (T : Set (projectiveSpaceOfModule k V)) with hTs
  set fb := prodOfClosedToProdTwo k V Cs Ts C.isClosed' T.isClosed' with hfb
  have : LocallyOfFiniteType fb :=
    locallyOfFiniteType_prodOfClosedToProdTwo k V Cs Ts C.isClosed' T.isClosed'
  have : IsProper (prodTwoToSpec k V) := by rw [prodTwoToSpec]; infer_instance
  have hbaseproper : IsProper (fb ≫ prodTwoToSpec k V) := inferInstance
  -- the numerics of the two projective spaces
  obtain ⟨n, hV⟩ : ∃ n, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  have hm : Module.finrank k (ParameterModule k V) = (n * n + n) + n + 1 := by
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap, hV]
    ring
  have hdimPV : topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k (ParameterModule k V)) =
      (((n * n + n) + n : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hm
  -- the dimensions of `C` and of `T`, as natural numbers
  have hnat : ∀ S : Set (projectiveSpaceOfModule k V), S.Nonempty →
      ∃ d : ℕ, topologicalKrullDim ↥S = (d : WithBot ℕ∞) := by
    intro S hS
    have : Nonempty ↥S := hS.to_subtype
    have hbot : topologicalKrullDim ↥S ≠ ⊥ := fun h =>
      (not_isEmpty_of_nonempty ↥S) ((topologicalKrullDim_eq_bot_iff_isEmpty ↥S).mp h)
    have hle : topologicalKrullDim ↥S ≤ (n : WithBot ℕ∞) := by
      rw [← hdimPV]
      exact topologicalKrullDim_subspace_le (projectiveSpaceOfModule k V) S
    have htop : topologicalKrullDim ↥S ≠ ⊤ := fun h =>
      natCast_ne_top_withBot n (top_le_iff.mp (h ▸ hle))
    exact ⟨_, eq_natCast_unbotD_toNat hbot htop⟩
  obtain ⟨dC, hdC⟩ := hnat Cs C.isIrreducible'.nonempty
  obtain ⟨dT, hdT⟩ := hnat Ts T.isIrreducible'.nonempty
  -- the correspondence over `C × T`, its dimension and its structure morphism
  have hdimW : topologicalKrullDim (transitionVariety k V fb) ≤
      (((dC + dT) + (n * n + n) : ℕ) : WithBot ℕ∞) := by
    refine le_trans (topologicalKrullDim_transitionVariety_le k V Cs Ts C.isClosed'
      T.isClosed' hV hm) ?_
    rw [hdC, hdT]
    push_cast
    exact le_rfl
  set pX := transitionVarietyToPar k V fb ≫
    projectiveSpaceOfModuleToSpec k (ParameterModule k V) with hpX
  have : LocallyOfFiniteType pX := by
    rw [hpX, transitionVarietyToPar_comp_toSpec]
    infer_instance
  have : IsProper pX := by
    rw [hpX, transitionVarietyToPar_comp_toSpec]
    infer_instance
  have : CompactSpace (transitionVariety k V fb) :=
    QuasiCompact.compactSpace_of_compactSpace pX
  have hirrP : IrreducibleSpace (projectiveSpaceOfModule k (ParameterModule k V)) :=
    irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k (ParameterModule k V) hm
  -- the target projection of the correspondence, as a morphism over `Spec k`
  set hT := transitionVarietyι k V Cs Ts C.isClosed' T.isClosed' ≫ tpTarget k V with hhT
  have hhTspec : hT ≫ projectiveSpaceOfModuleToSpec k V = pX := by
    rw [hhT, hpX, Category.assoc, tpTarget_comp_toSpec, transitionVarietyToPar,
      transitionProjPar, transitionVarietyι, Category.assoc, Category.assoc]
    rfl
  obtain ⟨U, hUopen, hUne, hUdim⟩ :=
    exists_nonempty_open_topologicalKrullDim_closure_image_fiber_le k pX
      (projectiveSpaceOfModuleToSpec k (ParameterModule k V))
      (projectiveSpaceOfModuleToSpec k V) (transitionVarietyToPar k V fb) rfl hT hhTspec
      hdimW hdimP
  refine ⟨U ∩ (invertibleLocus k V : Set (projectiveSpaceOfModule k (ParameterModule k V))),
    hUopen.inter (invertibleLocus k V).isOpen, ?_, ?_⟩
  · have h := (IrreducibleSpace.isIrreducible_univ
      (projectiveSpaceOfModule k (ParameterModule k V))).2 U
      (invertibleLocus k V : Set (projectiveSpaceOfModule k (ParameterModule k V)))
      hUopen (invertibleLocus k V).isOpen (by simpa using hUne)
      (by exact ⟨identityParameterPoint k V, Set.mem_univ _,
        identityParameterPoint_mem_invertibleLocus k V⟩)
    simpa using h
  · rintro p ⟨hpU, hpG⟩ g hgrep
    obtain ⟨hg0, hgeq⟩ := hgrep
    -- clause (1): the class is invertible, so the domain of definition is everything
    have hdet : LinearMap.det g ≠ 0 :=
      (coe_mem_invertibleLocus_iff_det_ne_zero k V p g hg0 hgeq).mp hpG
    have hCg : Cs ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)) := by
      rw [endDomain_eq_top_of_det_ne_zero k V hdet]
      exact fun x _ => trivial
    refine ⟨hCg, ?_⟩
    -- clause (2): the closed points of the intersection lie in the image of the fibre
    have hAcl : IsClosed (endProjectionImage k V g Cs ∩ Ts) :=
      (isClosed_endProjectionImage k V g C.isClosed' hCg).inter T.isClosed'
    have hsub : endProjectionImage k V g Cs ∩ Ts ⊆
        closure (hT.base '' ((transitionVarietyToPar k V fb).base ⁻¹'
          {(p : projectiveSpaceOfModule k (ParameterModule k V))})) := by
      refine Set.subset_of_isClosed_of_closedPoints_subset hAcl isClosed_closure
        fun z hz hzc => subset_closure ?_
      exact mem_image_fibre_transitionVarietyToPar k V Cs Ts C.isClosed' T.isClosed'
        p.property ⟨hg0, hgeq⟩ hCg hzc hz.1 hz.2
    have hdimfib := hUdim (p : projectiveSpaceOfModule k (ParameterModule k V)) hpU p.property
    -- the dimension count
    have hkey : topologicalKrullDim ↥(endProjectionImage k V g Cs ∩ Ts) +
        (((n * n + n) + n : ℕ) : WithBot ℕ∞) ≤ (((dC + dT) + (n * n + n) : ℕ) : WithBot ℕ∞) :=
      le_trans (add_le_add (topologicalKrullDim_le_of_subset hsub) le_rfl) hdimfib
    have hcancel : topologicalKrullDim ↥(endProjectionImage k V g Cs ∩ Ts) +
        (n : WithBot ℕ∞) ≤ ((dC : ℕ) : WithBot ℕ∞) + ((dT : ℕ) : WithBot ℕ∞) := by
      refine Stacks.RegularSequence.FibrewiseLocus.le_of_add_le_add_right_of_ne_bot_of_ne_top
        (c := (((n * n + n : ℕ)) : WithBot ℕ∞)) (WithBot.natCast_ne_bot _)
        (natCast_ne_top_withBot _) ?_
      refine le_trans (le_of_eq ?_) (le_trans hkey (le_of_eq ?_)) <;> push_cast <;> ring
    rw [topologicalKrullDim_endProjectionImage_eq k V g (S := Cs) C.isClosed' hCg, hdC, hdT,
      hdimPV]
    exact hcancel

/-- **A general class is not in the bad locus of `(C, T)`.** The nonempty open subset of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_nonempty_forall_isGoodEndomorphism`
misses `AlgebraicGeometry.ProjectiveSpaceOfModule.badParameterLocus` altogether, a class being
bad exactly when *some* representative of it fails one of the two clauses. -/
public theorem exists_isOpen_nonempty_disjoint_badParameterLocus
    (C T : IrreducibleCloseds (projectiveSpaceOfModule k V)) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ p : ClosedPoints k (ParameterModule k V),
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ U →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∉
          badParameterLocus k V (C : Set (projectiveSpaceOfModule k V))
            (T : Set (projectiveSpaceOfModule k V)) := by
  obtain ⟨U, hUopen, hUne, hU⟩ := exists_isOpen_nonempty_forall_isGoodEndomorphism k V C T
  refine ⟨U, hUopen, hUne, fun p hp => ?_⟩
  rintro ⟨p', g, hpq, hgrep, hbad⟩
  exact hbad (hU p' (hpq ▸ hp) g hgrep)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
