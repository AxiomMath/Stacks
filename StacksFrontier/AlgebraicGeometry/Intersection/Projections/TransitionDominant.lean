module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ClauseTwoFibre
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ClauseTwoFibreScheme
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersectionOfCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.SingularGoodEndomorphism
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionClassifyingRange
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionFibreDimension
public import StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.SubvarietyIntersection
public import StacksFrontier.Topology.Dimension.CodimensionOpen

/-!
# The incidence correspondence of Tag 0B1S dominates the parameter space

Let `X, Y` be closed subvarieties of `𝐏(V)` and let `T` be the incidence correspondence
`{(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}` over `X × Y`. A class `[g]` lies in the image of the
projection `π : T ⟶ 𝐏` as soon as `r_g(X)` meets `Y`: a closed point of
`F(g) = X ∩ r_g⁻¹(Y)` is a pair `([f], [f ∘ g])` of closed points of `𝐏(V)` lying in `X` and in
`Y`, and the point of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` it forms with `[g]` lies on the transition locus
because `f ∘ g` lies on its own line.

With `AlgebraicGeometry.ProjectiveSpaceOfModule.nonempty_endProjectionImage_inter` this is what
makes `π` dominant, which is the hypothesis Tag 0B2L needs in order for the generic relative
dimension of `π` to be `dim T - dim 𝐏`: the reduced closure of the image of `π` has to be the
whole of `𝐏` and not a proper closed subset of it.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_range_transitionVarietyToPar`: **the class of an
  endomorphism `g` with `X ⊆ U(g)` and `r_g(X) ∩ Y ≠ ∅` is in the image of `π`.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_transitionVarietyToPar_eq_univ`: **`π` is
  surjective**, for `X, Y` intersecting properly with `X ≠ 𝐏(V)` and `X ∩ Y ≠ ∅`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_clauseTwo_badLocus`: **the
  clause-(2) half of the bad locus**, closed, of codimension at least two at each of its points,
  containing every bad class at which clause (1) holds and containing only bad closed points.
* `…ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_badParameterLocus_subset`: the
  whole bad locus is contained in such a closed set, which misses `[id_V]`.
* `…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_isGood_of_intersectProperly`:
  both clauses of Tag 0B1S along a general line through `[id_V]`, at exactly the source's three
  hypotheses, clause (2) read as the dimension criterion on the image set.

## Implementation notes

**Why the class is named by `Module.Dual.eval`.** A closed point of the parameter space `𝐏` is
the point `AlgebraicGeometry.ProjectiveSpaceOfModule.linearFunctionalPoint` cut out by a nonzero
functional on `(End V)ᵛ`, and the functional naming the class of `g` is evaluation at `g`. That
is the spelling both bridges to the parameter space use — `val_eq_linearFunctionalPoint` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.DeterminantHypersurface` reads a
`ClosedPoints` element in it, and the fibre bound
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_transitionLocus_inter_le` recovers
`g` from such a functional through `Module.evalEquiv` — so stating the conclusion at
`Module.Dual.eval k (End V) g` is what lets a consumer reach it from either side.

**The point of the triple product is built, not found.** `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` is a `pullback`,
so a point of it over prescribed closed points of the factors comes from a `k`-point: the pair
`([f], [f ∘ g])` gives a `k`-point of `𝐏(V) ×_k 𝐏(V)` by `pullback.lift` of the two rational
points, and `AlgebraicGeometry.ProjectiveSpaceOfModule.parFibreSection` carries that to the
fibre of the projection to `𝐏` over `[g]`.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [IsAlgClosed k]
  [FiniteDimensional k V] [Nontrivial V]

/-- The parameter space `(End V)ᵛ` is nontrivial. -/
private theorem nontrivial_parameterModule (K W : Type u) [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] [Nontrivial W] : Nontrivial (ParameterModule K W) := by
  refine Module.nontrivial_of_finrank_pos (R := K) ?_
  rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
  exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

/-- **The class of `g` is in the image of the projection `π : T ⟶ 𝐏`** as soon as `X ⊆ U(g)` and
`r_g(X)` meets `Y`.

A closed point of `F(g) = X ∩ r_g⁻¹(Y)` — which is nonempty because its translate is
`r_g(X) ∩ Y` — is cut out by a nonzero functional `f`, and then `[f] ∈ X` and `[f ∘ g] ∈ Y` by
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_endProjectionFibre_linearFunctionalPoint_iff`. The
triple `([f], [f ∘ g], [g])` lies on the transition locus because `f ∘ g` lies on the line of
`f ∘ g`, so it is a point of the correspondence over `X × Y`, and its class is `[g]`.

Together with `AlgebraicGeometry.ProjectiveSpaceOfModule.nonempty_endProjectionImage_inter` this
makes `π` dominant: its image contains the class of every endomorphism whose domain of definition
contains `X`, in particular of every invertible one. -/
public theorem mem_range_transitionVarietyToPar
    {X Y : Set (projectiveSpaceOfModule k V)} (hXc : IsClosed X) (hYc : IsClosed Y)
    (g : V →ₗ[k] V) (hg : g ≠ 0)
    (hdom : X ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V)))
    (hne : (endProjectionImage k V g X ∩ Y).Nonempty) :
    linearFunctionalPoint k (ParameterModule k V) (Module.Dual.eval k (V →ₗ[k] V) g)
        (eval_ne_zero k V hg) ∈
      Set.range (transitionVarietyToPar k V
        (prodOfClosedToProdTwo k V X Y hXc hYc)).base := by
  have hntP := nontrivial_parameterModule k V
  set f₃ := Module.Dual.eval k (V →ₗ[k] V) g
  have hf₃ : f₃ ≠ 0 := eval_ne_zero k V hg
  have hgval : ∀ ψ : ParameterModule k V, f₃ ψ = ψ g := fun _ => rfl
  set q := linearFunctionalPoint k (ParameterModule k V) f₃ hf₃
  have hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))) :=
    linearFunctionalPoint_isClosed k (ParameterModule k V) f₃ hf₃
  -- a closed point of `F(g) = X ∩ r_g⁻¹(Y)`
  have hFc : IsClosed (endProjectionFibre k V g X Y) :=
    isClosed_endProjectionFibre k V g hXc hYc hdom
  have hFne : (endProjectionFibre k V g X Y).Nonempty := by
    rw [← endProjectionImage_endProjectionFibre k V g X Y] at hne
    obtain ⟨-, y, hy, -⟩ := hne
    exact ⟨(endDomain k V g).ι.base y, hy⟩
  obtain ⟨f, hf, hfF⟩ := exists_linearFunctionalPoint_mem_of_isClosed k V hFne hFc
  have hfdom : linearFunctionalPoint k V f hf ∈ endDomain k V g :=
    hdom (endProjectionFibre_subset k V g X Y hfF)
  have hfg : f ∘ₗ g ≠ 0 := fun h =>
    (notMem_endDomain_linearFunctionalPoint_iff k V f hf g).mpr h hfdom
  obtain ⟨hfX, hfgY⟩ :=
    (mem_endProjectionFibre_linearFunctionalPoint_iff k V g X Y hf hfg).mp hfF
  -- the `k`-point of `𝐏(V) ×_k 𝐏(V)` at the pair `([f], [f ∘ g])`
  have hxc : IsClosed ({linearFunctionalPoint k V f hf} :
      Set (projectiveSpaceOfModule k V)) := linearFunctionalPoint_isClosed k V f hf
  have hyc : IsClosed ({linearFunctionalPoint k V (f ∘ₗ g) hfg} :
      Set (projectiveSpaceOfModule k V)) := linearFunctionalPoint_isClosed k V _ hfg
  have hw : pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) _ hxc ≫
      projectiveSpaceOfModuleToSpec k V =
    pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) _ hyc ≫
      projectiveSpaceOfModuleToSpec k V := by
    rw [pointOfClosedPoint_comp, pointOfClosedPoint_comp]
  set wpt : Spec (.of k) ⟶ prodTwo k V :=
    pullback.lift (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) _ hxc)
      (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) _ hyc) hw with hwptdef
  obtain ⟨cp⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨IsLocalRing.closedPoint k⟩
  set t : transitionProd k V := (parFibreSection k V hq).base (wpt.base cp) with htdef
  -- the three projections of that point
  have hfstw : (tpFst k V).base t = wpt.base cp := by
    have h := congrArg (fun m : prodTwo k V ⟶ prodTwo k V => m.base (wpt.base cp))
      (parFibreSection_comp_tpFst k V hq)
    simpa only [Scheme.Hom.comp_apply, Scheme.Hom.id_base, TopCat.id_app] using h
  have hsrc : (tpSource k V).base t = linearFunctionalPoint k V f hf := by
    have h := congrArg (fun m : Spec (.of k) ⟶ projectiveSpaceOfModule k V => m.base cp)
      (pullback.lift_fst (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) _ hxc)
        (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) _ hyc) hw)
    simp only [Scheme.Hom.comp_apply] at h
    change (pullback.fst (projectiveSpaceOfModuleToSpec k V)
      (projectiveSpaceOfModuleToSpec k V)).base ((tpFst k V).base t) = _
    rw [hfstw, hwptdef, h]
    exact pointOfClosedPoint_apply (projectiveSpaceOfModuleToSpec k V) _ hxc cp
  have htgt : (tpTarget k V).base t = linearFunctionalPoint k V (f ∘ₗ g) hfg := by
    have h := congrArg (fun m : Spec (.of k) ⟶ projectiveSpaceOfModule k V => m.base cp)
      (pullback.lift_snd (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) _ hxc)
        (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k V) _ hyc) hw)
    simp only [Scheme.Hom.comp_apply] at h
    change (pullback.snd (projectiveSpaceOfModuleToSpec k V)
      (projectiveSpaceOfModuleToSpec k V)).base ((tpFst k V).base t) = _
    rw [hfstw, hwptdef, h]
    exact pointOfClosedPoint_apply (projectiveSpaceOfModuleToSpec k V) _ hyc cp
  have hpar : (tpPar k V).base t = q := by
    have h := congrArg
      (fun m : prodTwo k V ⟶ projectiveSpaceOfModule k (ParameterModule k V) =>
        m.base (wpt.base cp)) (parFibreSection_comp_tpPar k V hq)
    simp only [Scheme.Hom.comp_apply] at h
    rw [htdef, h]
    exact pointOfClosedPoint_apply (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) q hq _
  -- the point lies on the correspondence over `X × Y`
  have hloc : t ∈ transitionLocus k V :=
    (mem_transitionLocus_iff_of_linearFunctionalPoint k V t f hf hsrc (f ∘ₗ g) hfg htgt
      f₃ hf₃ hpar g hgval).mpr (Submodule.mem_span_singleton_self _)
  have hover : t ∈ transitionLocusOver k V X Y :=
    ⟨⟨hloc, by rwa [Set.mem_preimage, hsrc]⟩, by rwa [Set.mem_preimage, htgt]⟩
  obtain ⟨z, hz⟩ := (range_transitionVarietyι k V X Y hXc hYc).symm.subset hover
  refine ⟨z, ?_⟩
  have hcomp : (transitionVarietyToPar k V (prodOfClosedToProdTwo k V X Y hXc hYc)).base z =
      (tpPar k V).base ((transitionVarietyι k V X Y hXc hYc).base z) := rfl
  rw [hcomp, hz, hpar]

/-- **The projection `π : T ⟶ 𝐏` is surjective, under the dimension bound alone.** For `X, Y`
closed subvarieties of `𝐏(V)` with `dim 𝐏(V) ≤ dim X + dim Y` and `X ≠ 𝐏(V)`, every point of the
parameter space is the
class of some triple of the incidence correspondence over `X × Y`.

The image is closed, `π` being proper over a base proper over the ground field
(`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar`), and it
contains every closed point `[g]` at which clause (1) of Tag 0B1S holds, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_range_transitionVarietyToPar` fed with
`AlgebraicGeometry.ProjectiveSpaceOfModule.nonempty_endProjectionImage_inter`. The classes at
which clause (1) fails lie in the closed set of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_notMem_endDomain`,
which sits inside the determinant hypersurface and so is a *proper* closed subset of `𝐏`; two
proper closed subsets do not cover the irreducible `𝐏`, and a proper closed subset of `𝐏` misses
a closed point.

This is the hypothesis Tag 0B2L needs of `π`: the reduced closure of its image is the whole of
`𝐏`, so the generic relative dimension is `dim T - dim 𝐏` and the codimension that part (2c)
bounds below is a codimension in `𝐏`. -/
public theorem range_transitionVarietyToPar_eq_univ_of_le
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hle : topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule k V)) +
        topologicalKrullDim ↥(Y : Set (projectiveSpaceOfModule k V)))
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ) :
    Set.range (transitionVarietyToPar k V
        (prodOfClosedToProdTwo k V (X : Set (projectiveSpaceOfModule k V))
          (Y : Set (projectiveSpaceOfModule k V)) X.isClosed' Y.isClosed')).base =
      Set.univ := by
  have h2 : 2 ≤ Module.finrank k V :=
    two_le_finrank_of_isClosed_ne_univ k V X.isClosed' hXne X.isIrreducible'.nonempty
  have hntP := nontrivial_parameterModule k V
  obtain ⟨nP, hnP⟩ : ∃ n, Module.finrank k (ParameterModule k V) = n + 1 :=
    ⟨Module.finrank k (ParameterModule k V) - 1, by
      have := Module.finrank_pos (R := k) (M := ParameterModule k V); omega⟩
  have hirrP : IrreducibleSpace (projectiveSpaceOfModule k (ParameterModule k V)) :=
    irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k (ParameterModule k V) hnP
  set C := Set.range (transitionVarietyToPar k V
    (prodOfClosedToProdTwo k V (X : Set (projectiveSpaceOfModule k V))
      (Y : Set (projectiveSpaceOfModule k V)) X.isClosed' Y.isClosed')).base with hCdef
  have hCc : IsClosed C := by
    have h := isClosed_image_transitionVarietyToPar k V
      (prodOfClosedToProdTwo k V (X : Set (projectiveSpaceOfModule k V))
        (Y : Set (projectiveSpaceOfModule k V)) X.isClosed' Y.isClosed')
      (isProper_prodOfClosedToProdTwo_comp_toSpec k V
        (X : Set (projectiveSpaceOfModule k V)) (Y : Set (projectiveSpaceOfModule k V))
        X.isClosed' Y.isClosed') isClosed_univ
    rw [Set.image_univ] at h
    rw [hCdef]
    exact h
  obtain ⟨B₁, hB₁c, hB₁Z, hB₁sup, -⟩ :=
    exists_isClosed_two_le_codimension_notMem_endDomain k V
      (X : Set (projectiveSpaceOfModule k V)) X.isClosed' hXne h2
  have hB₁ne : B₁ ≠ Set.univ := fun h =>
    determinantHypersurface_ne_univ k V h2
      (Set.Subset.antisymm (Set.subset_univ _) (h ▸ hB₁Z))
  have hcover : C ∪ B₁ = Set.univ := by
    by_contra hcov
    obtain ⟨f₃, hf₃, hf₃not⟩ := exists_linearFunctionalPoint_notMem_of_ne_univ k
      (ParameterModule k V) (hCc.union hB₁c) hcov
    set g := (Module.evalEquiv k (V →ₗ[k] V)).symm f₃
    have hgval : ∀ ψ : ParameterModule k V, f₃ ψ = ψ g := fun ψ =>
      (Module.apply_evalEquiv_symm_apply k (V →ₗ[k] V) ψ f₃).symm
    have hg0 : g ≠ 0 := by
      intro h0
      refine hf₃ (LinearMap.ext fun ψ => ?_)
      rw [hgval ψ, h0, map_zero, LinearMap.zero_apply]
    have hpeq : linearFunctionalPoint k (ParameterModule k V)
        (Module.Dual.eval k (V →ₗ[k] V) g) (eval_ne_zero k V hg0) =
      linearFunctionalPoint k (ParameterModule k V) f₃ hf₃ :=
      linearFunctionalPoint_eq_of_eq k (ParameterModule k V) _ hf₃
        (LinearMap.ext fun ψ => (hgval ψ).symm)
    have hdom : (X : Set (projectiveSpaceOfModule k V)) ⊆
        (endDomain k V g : Set (projectiveSpaceOfModule k V)) := by
      by_contra hcon
      refine hf₃not (Or.inr ?_)
      have hpc := hB₁sup
        ((dualEndClosedPointsEquiv k V).symm (Projectivization.mk k g hg0)) g hg0
        (Equiv.apply_symm_apply _ _) hcon
      rwa [val_eq_linearFunctionalPoint k V _ g hg0 (Equiv.apply_symm_apply _ _), hpeq] at hpc
    have hne := nonempty_endProjectionImage_inter_of_le k V g X Y hle hdom
    exact hf₃not (Or.inl (hpeq ▸ mem_range_transitionVarietyToPar k V X.isClosed' Y.isClosed'
      g hg0 hdom hne))
  by_contra hCne
  exact union_ne_univ_of_ne_univ hCc hB₁c hCne hB₁ne hcover

/-- Properly intersecting subvarieties with nonempty intersection satisfy
`dim 𝐏(V) ≤ dim X + dim Y`. -/
private theorem le_add_of_intersectProperly (K W : Type u) [Field K] [AddCommGroup W]
    [Module K W] (X Y : IrreducibleCloseds (projectiveSpaceOfModule K W))
    (hXY : IntersectProperly X Y)
    (hXYne : ((X : Set (projectiveSpaceOfModule K W)) ∩
      (Y : Set (projectiveSpaceOfModule K W))).Nonempty) :
    topologicalKrullDim (projectiveSpaceOfModule K W) ≤
      topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule K W)) +
        topologicalKrullDim ↥(Y : Set (projectiveSpaceOfModule K W)) := by
  obtain ⟨x₀, hx₀⟩ := hXYne
  have : Nonempty (IrreducibleCloseds ↥((X : Set (projectiveSpaceOfModule K W)) ∩
      (Y : Set (projectiveSpaceOfModule K W)))) :=
    ⟨⟨closure {(⟨x₀, hx₀⟩ : ↥((X : Set (projectiveSpaceOfModule K W)) ∩
        (Y : Set (projectiveSpaceOfModule K W))))},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  calc topologicalKrullDim (projectiveSpaceOfModule K W)
      = 0 + topologicalKrullDim (projectiveSpaceOfModule K W) := (zero_add _).symm
    _ ≤ topologicalKrullDim ↥((X : Set (projectiveSpaceOfModule K W)) ∩
          (Y : Set (projectiveSpaceOfModule K W))) +
        topologicalKrullDim (projectiveSpaceOfModule K W) :=
          add_le_add Order.krullDim_nonneg le_rfl
    _ ≤ _ := hXY

/-- **The projection `π : T ⟶ 𝐏` is surjective.** For `X, Y` closed subvarieties of `𝐏(V)` which
intersect properly, with `X ≠ 𝐏(V)` and `X ∩ Y ≠ ∅`, every point of the parameter space is the
class of some triple of the incidence correspondence over `X × Y`.

The image is closed, `π` being proper over a base proper over the ground field
(`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar`), and it
contains every closed point `[g]` at which clause (1) of Tag 0B1S holds, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_range_transitionVarietyToPar` fed with
`AlgebraicGeometry.ProjectiveSpaceOfModule.nonempty_endProjectionImage_inter`. The classes at
which clause (1) fails lie in the closed set of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_notMem_endDomain`,
which sits inside the determinant hypersurface and so is a *proper* closed subset of `𝐏`; two
proper closed subsets do not cover the irreducible `𝐏`, and a proper closed subset of `𝐏` misses
a closed point.

This is the hypothesis Tag 0B2L needs of `π`: the reduced closure of its image is the whole of
`𝐏`, so the generic relative dimension is `dim T - dim 𝐏` and the codimension that part (2c)
bounds below is a codimension in `𝐏`. -/
public theorem range_transitionVarietyToPar_eq_univ
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty) :
    Set.range (transitionVarietyToPar k V
        (prodOfClosedToProdTwo k V (X : Set (projectiveSpaceOfModule k V))
          (Y : Set (projectiveSpaceOfModule k V)) X.isClosed' Y.isClosed')).base =
      Set.univ := by
  exact range_transitionVarietyToPar_eq_univ_of_le k V X Y
    (le_add_of_intersectProperly k V X Y hXY hXYne) hXne

/-! ### The clause-(2) bad locus -/

open Stacks.AlgebraicGeometry.CodimensionOneDivisor in
/-- **The clause-(2) half of the bad locus, under the dimension bound alone.** For `X, Y` closed
subvarieties of `𝐏(V)` with `dim 𝐏(V) ≤ dim X + dim Y` and `X ≠ 𝐏(V)`, there is a closed
subset `BG` of the parameter space such that

* every closed point of `BG` is bad,
* every closed point at which clause (1) holds and clause (2) fails lies in `BG`, and
* `BG` has codimension at least two at each of its points.

`BG` is the image under `π : T ⟶ 𝐏` of the locus where the local fibre dimension of `π` exceeds
`e = dim X + dim Y - dim 𝐏(V)`; equivalently it is the set of classes over which the fibre of `π`
has dimension greater than `e`. It is closed because that locus is closed, by upper
semicontinuity of the local fibre dimension (Tag 02FZ), and `π` is a closed map
(`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar`) — which is
the step the source asserts without proof.

The first two conditions are the identification of the fibre of `π` over a closed class with
`F(g) = X ∩ r_g⁻¹(Y)`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_fiber_transitionVarietyToPar_eq`)
read against
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_topologicalKrullDim_fibre_le`;
the threshold `e` alone decides both, which is why no lower bound on `dim T` is needed. The third
is Tag 0B2L part (2c): a jump of the fibre dimension above the generic relative dimension
`d = dim T - dim Z` forces the local ring of `Z` at the class to have dimension at least two.
Here `Z = 𝐏` by `AlgebraicGeometry.ProjectiveSpaceOfModule.range_transitionVarietyToPar_eq_univ`,
so that dimension is a codimension in `𝐏` and not in a proper closed subset of it, and
`d ≤ e` by `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_transitionVariety_le` —
the only place the upper bound on `dim T` is used. -/
public theorem exists_isClosed_clauseTwo_badLocus_of_le
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hle : topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule k V)) +
        topologicalKrullDim ↥(Y : Set (projectiveSpaceOfModule k V)))
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ) :
    ∃ BG : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsClosed BG ∧
      (∀ p : ClosedPoints k (ParameterModule k V),
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ BG →
          (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
            badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
              (Y : Set (projectiveSpaceOfModule k V))) ∧
      (∀ (p : ClosedPoints k (ParameterModule k V)) (g : V →ₗ[k] V),
        RepresentsParameterPoint k V p g →
        (X : Set (projectiveSpaceOfModule k V)) ⊆
          (endDomain k V g : Set (projectiveSpaceOfModule k V)) →
        ¬ IsGoodEndomorphism k V (X : Set (projectiveSpaceOfModule k V))
            (Y : Set (projectiveSpaceOfModule k V)) g →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ BG) ∧
      (∀ x ∈ BG, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) := by
  classical
  -- the three dimensions and the threshold `e`
  have hXc : IsClosed (X : Set (projectiveSpaceOfModule k V)) := X.isClosed'
  have hYc : IsClosed (Y : Set (projectiveSpaceOfModule k V)) := Y.isClosed'
  have hXn : (X : Set (projectiveSpaceOfModule k V)).Nonempty := X.isIrreducible'.nonempty
  have hYn : (Y : Set (projectiveSpaceOfModule k V)).Nonempty := Y.isIrreducible'.nonempty
  have hntP := nontrivial_parameterModule k V
  have h2 : 2 ≤ Module.finrank k V :=
    two_le_finrank_of_isClosed_ne_univ k V hXc hXne hXn
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 := ⟨Module.finrank k V - 1, by omega⟩
  have hdimPV : topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn
  have hfrP : Module.finrank k (ParameterModule k V) =
      Module.finrank k V * Module.finrank k V := by
    rw [Subspace.dual_finrank_eq, Module.finrank_linearMap]
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank k (ParameterModule k V) = m + n + 1 := by
    refine ⟨Module.finrank k (ParameterModule k V) - n - 1, ?_⟩
    have hge : n + 1 ≤ Module.finrank k (ParameterModule k V) := by
      rw [hfrP, hn]
      nlinarith
    omega
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k (ParameterModule k V)) =
      ((m + n : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (by rw [hm])
  obtain ⟨dX, hdX⟩ := natCast_eq_topologicalKrullDim_of_nonempty hXn hdimPV
  obtain ⟨dY, hdY⟩ := natCast_eq_topologicalKrullDim_of_nonempty hYn hdimPV
  have hnle : n ≤ dX + dY := by
    have h := hle
    rw [hdimPV, hdX, hdY] at h
    exact_mod_cast h
  obtain ⟨e, he⟩ : ∃ e : ℕ, dX + dY = e + n := ⟨dX + dY - n, by omega⟩
  have hcast : (dX : WithBot ℕ∞) + (dY : WithBot ℕ∞) =
      (e : WithBot ℕ∞) + (n : WithBot ℕ∞) := by
    rw [← Nat.cast_add, ← Nat.cast_add, he]
  have hnbot : (n : WithBot ℕ∞) ≠ ⊥ := by simp
  have h1bot : (1 : WithBot ℕ∞) ≠ ⊥ := by simp
  have h1top : (1 : WithBot ℕ∞) ≠ ⊤ := by
    have h := natCast_ne_top_withBot 1
    rwa [Nat.cast_one] at h
  -- the correspondence and its projection to the parameter space
  set Fb := prodOfClosedToProdTwo k V (X : Set (projectiveSpaceOfModule k V))
    (Y : Set (projectiveSpaceOfModule k V)) hXc hYc with hFb
  set π := transitionVarietyToPar k V Fb with hπ
  have hftV : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
    have := isProper_projectiveSpaceOfModuleToSpec k V
    infer_instance
  have hftP : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) := by
    have := isProper_projectiveSpaceOfModuleToSpec k (ParameterModule k V)
    infer_instance
  have hFbft : LocallyOfFiniteType Fb :=
    locallyOfFiniteType_prodOfClosedToProdTwo k V _ _ hXc hYc
  have hirrT : IrreducibleSpace (transitionVariety k V Fb) :=
    irreducibleSpace_transitionVariety k V _ _ hXc hYc (Module.finBasis k V)
      X.isIrreducible' Y.isIrreducible'
  set pY := projectiveSpaceOfModuleToSpec k (ParameterModule k V)
  set pT := π ≫ pY with hpT
  have hpTft : LocallyOfFiniteType pT := by
    rw [hpT, hπ, transitionVarietyToPar_comp_toSpec]
    infer_instance
  have hπft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π pY
  -- the jump locus and its image
  set J : Set (transitionVariety k V Fb) :=
    {t | topologicalKrullDimAt (π.fiber (π.base t)) (π.asFiber t) ≤ (e : WithBot ℕ∞)}ᶜ
  have hJc : IsClosed J := (isOpen_setOf_fiberDimensionAt_le π e).isClosed_compl
  set BG : Set (projectiveSpaceOfModule k (ParameterModule k V)) := π.base '' J
  have hBGc : IsClosed BG :=
    isClosed_image_transitionVarietyToPar k V Fb
      (isProper_prodOfClosedToProdTwo_comp_toSpec k V _ _ hXc hYc) hJc
  have hmem : ∀ q : projectiveSpaceOfModule k (ParameterModule k V),
      q ∈ BG ↔ ¬ (topologicalKrullDim (π.fiber q) ≤ (e : WithBot ℕ∞)) := by
    intro q
    constructor
    · rintro ⟨t, htJ, rfl⟩ hle
      exact htJ ((Scheme.Hom.fiberDimension_le_iff π _ _).mp hle t rfl)
    · intro hq
      obtain ⟨t, ht⟩ := not_forall.mp
        (fun h => hq ((Scheme.Hom.fiberDimension_le_iff π q _).mpr h))
      have h1 : π.base t = q := by
        by_contra hc
        exact ht (fun h => absurd h hc)
      exact ⟨t, fun h => ht (fun _ => h), h1⟩
  refine ⟨BG, hBGc, ?_, ?_, ?_⟩
  -- every closed point of `BG` is bad
  · intro p hp
    obtain ⟨g, hg0, hgmk⟩ : ∃ (g : V →ₗ[k] V) (hg : g ≠ 0),
        dualEndClosedPointsEquiv k V p = Projectivization.mk k g hg :=
      ⟨(dualEndClosedPointsEquiv k V p).rep, Projectivization.rep_nonzero _,
        (Projectivization.mk_rep _).symm⟩
    refine ⟨p, g, rfl, ⟨hg0, hgmk⟩, ?_⟩
    by_cases hdom : (X : Set (projectiveSpaceOfModule k V)) ⊆
        (endDomain k V g : Set (projectiveSpaceOfModule k V))
    · have hqrep := val_eq_linearFunctionalPoint k V p g hg0 hgmk
      have hfib := topologicalKrullDim_fiber_transitionVarietyToPar_eq
        hXc hYc hg0 hdom p.property hqrep
      have hgt : ¬ (topologicalKrullDim ↥(endProjectionFibre k V g
          (X : Set (projectiveSpaceOfModule k V))
          (Y : Set (projectiveSpaceOfModule k V))) ≤ (e : WithBot ℕ∞)) := by
        rw [← hfib]
        exact (hmem _).mp hp
      intro hgood
      rw [isGoodEndomorphism_iff_topologicalKrullDim_fibre_le k V g hXc hYc hdom,
        hdimPV, hdX, hdY, hcast] at hgood
      exact hgt
        ((WithBot.add_le_add_iff_right' hnbot (natCast_ne_top_withBot n)).mp hgood)
    · exact fun hgood => hdom hgood.1
  -- every bad closed point at which clause (1) holds lies in `BG`
  · intro p g hg hdom hbad
    obtain ⟨hg0, hgmk⟩ := hg
    have hqrep := val_eq_linearFunctionalPoint k V p g hg0 hgmk
    have hfib := topologicalKrullDim_fiber_transitionVarietyToPar_eq
      hXc hYc hg0 hdom p.property hqrep
    refine (hmem _).mpr ?_
    rw [hfib]
    intro hle
    refine hbad ?_
    rw [isGoodEndomorphism_iff_topologicalKrullDim_fibre_le k V g hXc hYc hdom,
      hdimPV, hdX, hdY, hcast]
    exact add_le_add hle le_rfl
  -- the codimension bound
  · intro x hx
    obtain ⟨t, htJ, htx⟩ := hx
    have hjump : ¬ (topologicalKrullDimAt (π.fiber (π.base t)) (π.asFiber t) ≤
      (e : WithBot ℕ∞)) := htJ
    -- `Z = 𝐏`
    have hrange : Set.range (fun s : transitionVariety k V Fb => π.base s) = Set.univ := by
      rw [hπ, hFb]
      exact range_transitionVarietyToPar_eq_univ_of_le k V X Y hle hXne
    have hcl : Closeds.closure (Set.range (fun s : transitionVariety k V Fb => π.base s)) =
        ⊤ := by
      refine TopologicalSpace.Closeds.ext ?_
      rw [TopologicalSpace.Closeds.coe_closure, hrange, closure_univ]
      rfl
    set ZI := Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range (fun s : transitionVariety k V Fb => π.base s))) with hZI
    have hZrange : Set.range ZI.subschemeι.base = Set.univ := by
      rw [Scheme.IdealSheafData.range_subschemeι, hZI, hcl,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hZemb : Topology.IsEmbedding ZI.subschemeι.base :=
      (IsClosedImmersion.isClosedEmbedding ZI.subschemeι).isEmbedding
    have hZopen : Topology.IsOpenEmbedding ZI.subschemeι.base :=
      ⟨hZemb, by rw [hZrange]; exact isOpen_univ⟩
    have hZhom : IsHomeomorph ZI.subschemeι.base :=
      isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hZemb, Set.range_eq_univ.mp hZrange⟩
    have hdimZ : topologicalKrullDim ZI.subscheme = ((m + n : ℕ) : WithBot ℕ∞) := by
      rw [IsHomeomorph.topologicalKrullDim_eq _ hZhom, hdimP]
    -- the generic relative dimension is at most the threshold
    set d : ℕ := ((topologicalKrullDim (transitionVariety k V Fb)).unbotD 0).toNat -
      ((topologicalKrullDim ZI.subscheme).unbotD 0).toNat with hd
    have hTle : topologicalKrullDim (transitionVariety k V Fb) ≤
        ((e + n + m : ℕ) : WithBot ℕ∞) := by
      have h := topologicalKrullDim_transitionVariety_le k V _ _ hXc hYc hn hm
      rw [hdX, hdY, hcast] at h
      refine h.trans (le_of_eq ?_)
      rw [← Nat.cast_add, ← Nat.cast_add]
    have hTbot : topologicalKrullDim (transitionVariety k V Fb) ≠ ⊥ := by
      rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
      exact fun h => (not_isEmpty_of_nonempty (transitionVariety k V Fb)) h
    have hTtop : topologicalKrullDim (transitionVariety k V Fb) ≠ ⊤ := fun h =>
      natCast_ne_top_withBot (e + n + m) (top_le_iff.mp (h ▸ hTle))
    have hTnat : ((topologicalKrullDim (transitionVariety k V Fb)).unbotD 0).toNat ≤
        e + n + m := by
      rw [eq_natCast_unbotD_toNat hTbot hTtop] at hTle
      exact_mod_cast hTle
    have hZbot : topologicalKrullDim ZI.subscheme ≠ ⊥ := by
      rw [hdimZ]
      exact fun h => absurd h (by simp)
    have hZtop : topologicalKrullDim ZI.subscheme ≠ ⊤ := by
      rw [hdimZ]
      exact natCast_ne_top_withBot _
    have hZnat : ((topologicalKrullDim ZI.subscheme).unbotD 0).toNat = m + n := by
      have h := eq_natCast_unbotD_toNat hZbot hZtop
      rw [hdimZ] at h
      rw [hdimZ]
      exact_mod_cast h.symm
    have hdle : d ≤ e := by
      rw [hd, hZnat]
      omega
    have hdcast : (d : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) := by exact_mod_cast hdle
    -- the point of `Z` above `x`
    obtain ⟨z, hz⟩ : x ∈ Set.range ZI.subschemeι.base := by
      rw [hZrange]
      exact Set.mem_univ x
    have hzπ : ZI.subschemeι.base z = π.base t := hz.trans htx.symm
    have hirrP : IrreducibleSpace (projectiveSpaceOfModule k (ParameterModule k V)) :=
      irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k (ParameterModule k V)
        (by rw [hm])
    by_cases hxuniv : closure ({x} : Set (projectiveSpaceOfModule k (ParameterModule k V))) =
        Set.univ
    · -- `x` is the generic point of `𝐏`, where the fibre dimension is exactly `d`
      refine absurd ?_ hjump
      set η := genericPoint (transitionVariety k V Fb)
      have hηgen : IsGenericPoint η (Set.univ : Set (transitionVariety k V Fb)) :=
        genericPoint_spec _
      have hπη : IsGenericPoint (π.base η)
          (Set.univ : Set (projectiveSpaceOfModule k (ParameterModule k V))) := by
        refine isGenericPoint_iff_specializes.mpr fun y => iff_of_true ?_ (Set.mem_univ y)
        obtain ⟨s, rfl⟩ : y ∈ Set.range (fun s : transitionVariety k V Fb => π.base s) := by
          rw [hrange]
          exact Set.mem_univ y
        exact ((isGenericPoint_iff_specializes.mp hηgen s).2 (Set.mem_univ s)).map
          π.base.hom.continuous
      have hxg : IsGenericPoint x
          (Set.univ : Set (projectiveSpaceOfModule k (ParameterModule k V))) := hxuniv
      have hxη : x = π.base η := hxg.eq hπη
      have hgen := topologicalKrullDim_fiber_genericPoint_eq_imageClosure_sub k pT pY π rfl η hηgen
      calc topologicalKrullDimAt (π.fiber (π.base t)) (π.asFiber t)
          ≤ topologicalKrullDim (π.fiber (π.base t)) :=
            topologicalKrullDimAt_le_topologicalKrullDim _
        _ = topologicalKrullDim (π.fiber (π.base η)) := by rw [htx, hxη]
        _ = (d : WithBot ℕ∞) := by rw [hgen, hd]
        _ ≤ (e : WithBot ℕ∞) := hdcast
    · -- otherwise the closure of `x` is not maximal, and Tag 0B2L part (2c) applies
      have hnotmax : ¬ IsMax (IrreducibleCloseds.closureSingleton x) := by
        intro hmax
        refine hxuniv (Set.Subset.antisymm (Set.subset_univ _) ?_)
        have hle : IrreducibleCloseds.closureSingleton x ≤
            (⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ :
              IrreducibleCloseds (projectiveSpaceOfModule k (ParameterModule k V))) :=
          SetLike.coe_subset_coe.mp (Set.subset_univ _)
        have h := hmax hle
        rw [← IrreducibleCloseds.coe_closureSingleton]
        exact SetLike.coe_subset_coe.mpr h
      have h1c : 1 ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
        rw [codimension_eq_coheight]
        refine Order.one_le_iff_ne_zero.mpr fun h => hnotmax ?_
        exact Order.coheight_eq_zero.mp h
      -- the codimension in `Z` is the codimension in `𝐏`
      have hnep : (ZI.subschemeι.base ⁻¹'
          (IrreducibleCloseds.closureSingleton x : Set _)).Nonempty := by
        refine ⟨z, ?_⟩
        rw [Set.mem_preimage, hz]
        exact subset_closure rfl
      have hcomap : (IrreducibleCloseds.closureSingleton x).comapOpenEmbedding hZopen hnep =
          IrreducibleCloseds.closureSingleton z := by
        refine TopologicalSpace.IrreducibleCloseds.ext ?_
        rw [TopologicalSpace.IrreducibleCloseds.coe_comapOpenEmbedding,
          IrreducibleCloseds.coe_closureSingleton, IrreducibleCloseds.coe_closureSingleton,
          hZemb.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hz]
      have hcod : codimension (IrreducibleCloseds.closureSingleton x) =
          codimension (IrreducibleCloseds.closureSingleton z) := by
        rw [codimension_eq_coheight, codimension_eq_coheight,
          TopologicalSpace.IrreducibleCloseds.coheight_comapOpenEmbedding
            (IrreducibleCloseds.closureSingleton x) hZopen hnep, hcomap]
      have hstalk : ringKrullDim (ZI.subscheme.presheaf.stalk z) =
          (codimension (IrreducibleCloseds.closureSingleton z) : WithBot ℕ∞) :=
        ringKrullDim_stalk_eq_codimension_closureSingleton z
      by_contra hcon
      have hc1 : codimension (IrreducibleCloseds.closureSingleton x) ≤ 1 := by
        have hlt : codimension (IrreducibleCloseds.closureSingleton x) < 1 + 1 := by
          have h := lt_of_not_ge hcon
          norm_num at h ⊢
          exact h
        exact (ENat.lt_add_one_iff (by simp)).mp hlt
      have hge1 : 1 ≤ ringKrullDim (ZI.subscheme.presheaf.stalk z) := by
        rw [hstalk, ← hcod]
        exact_mod_cast h1c
      have hle1 : ringKrullDim (ZI.subscheme.presheaf.stalk z) ≤ 1 := by
        rw [hstalk, ← hcod]
        exact_mod_cast hc1
      have hkey := topologicalKrullDimAt_fiber_add_one_le_of_one_le_ringKrullDim_imageClosure
        k pT pY π rfl d hd t z hzπ hge1
      refine hjump ?_
      have hstep : topologicalKrullDimAt (π.fiber (π.base t)) (π.asFiber t) + 1 ≤
          (d : WithBot ℕ∞) + 1 := hkey.trans (add_le_add le_rfl hle1)
      exact ((WithBot.add_le_add_iff_right' h1bot h1top).mp hstep).trans hdcast

/-- **The clause-(2) half of the bad locus of Tag 0B1S, with its codimension.** For `X, Y` closed
subvarieties of `𝐏(V)` intersecting properly, with `X ≠ 𝐏(V)` and `X ∩ Y ≠ ∅`, there is a closed
subset `BG` of the parameter space such that

* every closed point of `BG` is bad,
* every closed point at which clause (1) holds and clause (2) fails lies in `BG`, and
* `BG` has codimension at least two at each of its points.

`BG` is the image under `π : T ⟶ 𝐏` of the locus where the local fibre dimension of `π` exceeds
`e = dim X + dim Y - dim 𝐏(V)`; equivalently it is the set of classes over which the fibre of `π`
has dimension greater than `e`. It is closed because that locus is closed, by upper
semicontinuity of the local fibre dimension (Tag 02FZ), and `π` is a closed map
(`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar`) — which is
the step the source asserts without proof.

The first two conditions are the identification of the fibre of `π` over a closed class with
`F(g) = X ∩ r_g⁻¹(Y)`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_fiber_transitionVarietyToPar_eq`)
read against
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_topologicalKrullDim_fibre_le`;
the threshold `e` alone decides both, which is why no lower bound on `dim T` is needed. The third
is Tag 0B2L part (2c): a jump of the fibre dimension above the generic relative dimension
`d = dim T - dim Z` forces the local ring of `Z` at the class to have dimension at least two.
Here `Z = 𝐏` by `AlgebraicGeometry.ProjectiveSpaceOfModule.range_transitionVarietyToPar_eq_univ`,
so that dimension is a codimension in `𝐏` and not in a proper closed subset of it, and
`d ≤ e` by `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_transitionVariety_le` —
the only place the upper bound on `dim T` is used. -/
public theorem exists_isClosed_clauseTwo_badLocus
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty) :
    ∃ BG : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsClosed BG ∧
      (∀ p : ClosedPoints k (ParameterModule k V),
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ BG →
          (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
            badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
              (Y : Set (projectiveSpaceOfModule k V))) ∧
      (∀ (p : ClosedPoints k (ParameterModule k V)) (g : V →ₗ[k] V),
        RepresentsParameterPoint k V p g →
        (X : Set (projectiveSpaceOfModule k V)) ⊆
          (endDomain k V g : Set (projectiveSpaceOfModule k V)) →
        ¬ IsGoodEndomorphism k V (X : Set (projectiveSpaceOfModule k V))
            (Y : Set (projectiveSpaceOfModule k V)) g →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ BG) ∧
      (∀ x ∈ BG, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) := by
  exact exists_isClosed_clauseTwo_badLocus_of_le k V X Y
    (le_add_of_intersectProperly k V X Y hXY hXYne) hXne

/-- **The bad locus of Tag 0B1S is contained in a closed set of codimension at least two.** For
`X, Y` closed subvarieties of `𝐏(V)` intersecting properly, with `X ≠ 𝐏(V)` and `X ∩ Y ≠ ∅`,
there is a closed subset `B` of the parameter space containing every bad closed point, having
codimension at least two at each of its points, and missing `[id_V]`.

This is the form the genericity argument of Tag 0B2T consumes, and the reason it is recorded
separately from
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_isGood_of_intersectProperly` is
that the same statement for a different pair of subvarieties is what the corresponding step of Tag
0B1T needs.

`B` is the union of the clause-(1) locus of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_two_le_codimension_notMem_endDomain`
and the clause-(2) locus of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_clauseTwo_badLocus`. It is a
*superset* of the bad locus and not the bad locus itself: the clause-(1) piece is the
adjugate-substitution locus together with the leading-minor locus, which is where the
codimension bound is available, and which may contain classes at which clause (1) in fact holds.
Equality would need the locus `{[g] | X ⊄ U(g)}` itself to be closed — true, by the same
properness argument as for the clause-(2) locus, applied to the incidence correspondence
`{(x, [g]) : x ∈ X, f_x ∘ g = 0}` — and is not proved here. -/
public theorem exists_isClosed_two_le_codimension_badParameterLocus_subset
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty) :
    ∃ B : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsClosed B ∧
      (∀ p : ClosedPoints k (ParameterModule k V),
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
          badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
            (Y : Set (projectiveSpaceOfModule k V)) →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ B) ∧
      (∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) ∧
      identityParameterPoint k V ∉ B := by
  have h2 : 2 ≤ Module.finrank k V :=
    two_le_finrank_of_isClosed_ne_univ k V X.isClosed' hXne X.isIrreducible'.nonempty
  obtain ⟨B₁, hB₁c, hB₁Z, hB₁sup, hB₁codim⟩ :=
    exists_isClosed_two_le_codimension_notMem_endDomain k V
      (X : Set (projectiveSpaceOfModule k V)) X.isClosed' hXne h2
  obtain ⟨BG, hBGc, hBGbad, hBGsup, hBGcodim⟩ :=
    exists_isClosed_clauseTwo_badLocus k V X Y hXY hXne hXYne
  refine ⟨B₁ ∪ BG, hB₁c.union hBGc, ?_, fun x hx => hx.elim (hB₁codim x) (hBGcodim x), ?_⟩
  · rintro p ⟨p', g, hpp, ⟨hg0, hgmk⟩, hbad⟩
    have hp' : p' = p := Subtype.ext hpp
    subst hp'
    by_cases hdom : (X : Set (projectiveSpaceOfModule k V)) ⊆
        (endDomain k V g : Set (projectiveSpaceOfModule k V))
    · exact Or.inr (hBGsup p' g ⟨hg0, hgmk⟩ hdom hbad)
    · exact Or.inl (hB₁sup p' g hg0 hgmk hdom)
  · set pid : ClosedPoints k (ParameterModule k V) := (dualEndClosedPointsEquiv k V).symm
      (Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V)) with hpiddef
    have hpidc : (pid : projectiveSpaceOfModule k (ParameterModule k V)) =
        identityParameterPoint k V := rfl
    have hpid : dualEndClosedPointsEquiv k V pid =
        Projectivization.mk k (LinearMap.id : V →ₗ[k] V) (linearMapId_ne_zero k V) := by
      rw [hpiddef, Equiv.apply_symm_apply]
    rintro (h₁ | h₂)
    · refine (mem_determinantHypersurface_iff k V).mp (hB₁Z h₁) ?_
      refine (coe_mem_invertibleLocus_iff_det_ne_zero k V pid (LinearMap.id : V →ₗ[k] V)
        (linearMapId_ne_zero k V) hpid).mpr ?_
      simp
    · refine identityParameterPoint_notMem_badParameterLocus k V hXY ?_
      rw [← hpidc]
      exact hBGbad pid (by rw [hpidc]; exact h₂)

/-- **Tag 0B1S, clause (2) as a dimension criterion.** Let `X, Y` be closed subvarieties of `𝐏(V)`
which intersect properly, with `X ≠ 𝐏(V)` and `X ∩ Y ≠ ∅`. Then for a general line
`ℓ ⊆ 𝐏 = 𝐏((End V)ᵛ)` through `[id_V]` — that is, for a line through `[id_V]` and any closed point of a nonempty
Zariski open subset of `𝐏` — every representative `g` of every closed point of `ℓ` satisfies

* **clause (1)** `X ⊆ U(g)`, so that `r_g` is defined on the whole of `X`, and
* **clause (2)** `r_g(X)` intersects `Y` properly,

both being the predicate
`AlgebraicGeometry.ProjectiveSpaceOfModule.IsGoodEndomorphism`.

The hypotheses are exactly the source's, and all three do work: `X ≠ 𝐏(V)` gives
`2 ≤ dim_k V`, which is what makes the determinant hypersurface a proper closed subset of `𝐏`
(at `dim_k V = 1` it is the whole of `𝐏`); `X ∩ Y ≠ ∅` together with the proper intersection
gives `dim 𝐏(V) ≤ dim X + dim Y`, which is what makes `r_g(X)` meet `Y` at all and hence the
projection of the incidence correspondence to `𝐏` surjective (without it, two disjoint lines in
`𝐏³` satisfy `IntersectProperly` vacuously and the conclusion fails).

Clause (2) is stated here through `AlgebraicGeometry.ProjectiveSpaceOfModule.IsGoodEndomorphism`,
on the image set `r_g(X)`; the form stating it as `AlgebraicGeometry.IntersectProperly` of the
closed subvariety `r_g(X)` with `Y`, which is where Tag 0B1S is registered, is
`…ProjectiveSpaceOfModule.exists_isOpen_forall_closedPoint_line_subset_endDomain_intersectProperly`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineIntersectProperly`. -/
public theorem exists_isOpen_forall_closedPoint_line_isGood_of_intersectProperly
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty) :
    ∃ U : Set (projectiveSpaceOfModule k (ParameterModule k V)), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V))) →
        ∃ L : Submodule k (ParameterModule k V),
          Module.finrank k (ParameterModule k V ⧸ L) = 2 ∧
          identityParameterPoint k V ∈ linearSubspace k (ParameterModule k V) L ∧
          q ∈ linearSubspace k (ParameterModule k V) L ∧
          ∀ p : ClosedPoints k (ParameterModule k V),
            (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
              linearSubspace k (ParameterModule k V) L →
            ∀ g : V →ₗ[k] V, RepresentsParameterPoint k V p g →
              IsGoodEndomorphism k V (X : Set (projectiveSpaceOfModule k V))
                (Y : Set (projectiveSpaceOfModule k V)) g := by
  obtain ⟨BG, hBGc, hBGbad, hBGsup, hBGcodim⟩ :=
    exists_isClosed_clauseTwo_badLocus k V X Y hXY hXne hXYne
  exact exists_isOpen_closedPoint_line_isGood_of_clauseTwo k V X Y hXY hXne hXYne BG hBGc
    hBGbad hBGsup hBGcodim

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
