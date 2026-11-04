module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement

/-!
# The complement of a locally principal closed subspace, read on a chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`Z ⊆ X` be a closed subspace.  The open complement `X \ Z` is cut out by the complement of the
point set of `Z` (`AlgebraicGeometry.Space.openComplement_eq_openSubspaceOfPoints_compl`), so
the subscheme of an étale scheme chart which the complement cuts out is the complement of the
preimage of that point set.  This file identifies that preimage with a closed subscheme of the
chart, and, when `Z` is locally principal, with the zero locus of a single global regular
function on a suitable affine chart.

## Main results

* `AlgebraicGeometry.Space.mem_range_pointsMap_yoneda_map_iff`: a point of a represented
  presheaf lies in the image of the points of a morphism of the site exactly when its
  underlying scheme point lies in the image of the underlying morphism of schemes.
* `AlgebraicGeometry.Space.mem_range_pointsMap_ι_iff`: the preimage along a chart of the point
  set of a closed subspace is the image of the canonical base change of its inclusion.
* `AlgebraicGeometry.Space.range_eq_zeroLocus_ker_appTop`: the image of a closed immersion into
  an affine scheme is the zero locus of the kernel of pullback of global regular functions.
* `AlgebraicGeometry.Space.range_rep_snd_eq_zeroLocus_definingIdealAt`: on an affine étale
  scheme chart, the image of the canonical base change of a closed subspace is the zero locus
  of the defining ideal there.
* `AlgebraicGeometry.Space.exists_affine_chart_mem_range_pointsMap_iff`: for a locally
  principal closed subspace, every point of an étale scheme chart lifts to an affine étale
  chart over it on which the preimage of the point set of the subspace is the zero locus of a
  single global regular function.

## References

* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points in the image of a morphism of the site -/

/-- A point of a represented presheaf lies in the image of the points of a morphism of the site
exactly when its underlying scheme point lies in the image of the underlying morphism of
schemes. -/
theorem mem_range_pointsMap_yoneda_map_iff {A A' : BigFppfOver B S hS} (h : A' ⟶ A)
    (w : points B S hS (yoneda.obj A)) :
    w ∈ Set.range (pointsMap B S hS (yoneda.obj A') (yoneda.map h)) ↔
      pointsToScheme B S hS A w ∈ Set.range ((BigFppfOver.toScheme B S hS).map h) := by
  refine ⟨?_, mem_range_pointsMap_yoneda_map B S hS h w⟩
  rintro ⟨w', rfl⟩
  exact ⟨pointsToScheme B S hS A' w', (pointsToScheme_pointsMap_yoneda B S hS h w').symm⟩

/-! ### The point set of a closed subspace, read on a chart -/

/-- A point of a chart `A` of `X` has image in the point set of a closed subspace `Z ⊆ X` exactly
when it lies in the image of the canonical base change `Z ×_X A ⟶ A`. -/
theorem mem_range_pointsMap_ι_iff (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ X.1)
    (w : points B S hS (yoneda.obj A)) :
    pointsMap B S hS (yoneda.obj A) q w ∈
        Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ↔
      pointsToScheme B S hS A w ∈
        Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd q)) := by
  rw [← mem_range_pointsMap_yoneda_map_iff B S hS (Z.2.2.rep.snd q) w,
    ← preimage_range_pointsMap_eq_range_pointsMap_snd B S hS Z.2.2.rep q]
  exact Iff.rfl

/-! ### The image of a closed immersion into an affine scheme -/

/-- The image of a closed immersion `m : T' ⟶ T` into an affine scheme is the zero locus of the
kernel of `m.appTop`, the pullback of global regular functions. -/
theorem range_eq_zeroLocus_ker_appTop {T T' : Scheme.{u}} (m : T' ⟶ T)
    [_root_.AlgebraicGeometry.IsClosedImmersion m] (hT : IsAffineOpen (⊤ : T.Opens)) :
    Set.range m = T.zeroLocus (RingHom.ker m.appTop.hom : Set Γ(T, ⊤)) := by
  have hclosed : IsClosed (Set.range m) :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion.mp ‹_›).2
  have h1 : (m.ker.support : Set T) = Set.range m := by
    rw [m.support_ker, hclosed.closure_eq]
  have h2 := m.ker.coe_support_inter ⟨⊤, hT⟩
  rw [Scheme.Hom.ker_apply] at h2
  simp only [TopologicalSpace.Opens.coe_top, Set.inter_univ] at h2
  rw [← h1, h2]
  rfl

/-! ### The defining ideal on an affine chart cuts out the point set -/

/-- On an affine étale scheme chart `W` of `X`, the image of the canonical base change
`Z ×_X W ⟶ W` of a closed subspace `Z` is the zero locus of the defining ideal of `Z` on `W`. -/
theorem range_rep_snd_eq_zeroLocus_definingIdealAt (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (W : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left)] :
    Set.range ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd W.1.hom)) =
      ((BigFppfOver.toScheme B S hS).obj W.1.left).zeroLocus
        {k : Γ((BigFppfOver.toScheme B S hS).obj W.1.left, ⊤) |
          k ∈ definingIdealAt B S hS X Z (op W)} := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd W.1.hom)) :=
    Z.2.2.property_snd W.1.hom
  rw [range_eq_zeroLocus_ker_appTop _
    (isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj W.1.left))]
  congr 1
  refine Set.ext fun k => ?_
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, definingIdealAt_eq_ker B S hS X Z W]
  exact Iff.rfl

/-! ### One section cuts out the point set on an affine chart -/

/-- Let `Z` be a locally principal closed subspace of an algebraic space `X` over `S`.  Every
point of an étale scheme chart `U` of `X` lifts to an affine étale chart `W` over `U` carrying a
global regular function `a` whose zero locus is exactly the preimage in `W` of the point set of
`Z`. -/
theorem exists_affine_chart_mem_range_pointsMap_iff (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (hZ : IsLocallyPrincipal B S hS X Z)
    (U : SmallEtale B S hS X.1) (x : (BigFppfOver.toScheme B S hS).obj U.1.left) :
    ∃ (W : SmallEtale B S hS X.1) (g : W ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) ∧
      (∃ x' : (BigFppfOver.toScheme B S hS).obj W.1.left,
        ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X.1).map g)) x' = x) ∧
      ∃ a : Γ((BigFppfOver.toScheme B S hS).obj W.1.left, ⊤),
        ∀ w : points B S hS (yoneda.obj W.1.left),
          pointsMap B S hS (yoneda.obj W.1.left) W.1.hom w ∈
              Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) ↔
            pointsToScheme B S hS W.1.left w ∈
              ((BigFppfOver.toScheme B S hS).obj W.1.left).zeroLocus {a} := by
  obtain ⟨W, g, hWaff, hlift, a, ha⟩ :=
    exists_affine_chart_zeroLocus_definingIdealAt_eq B S hS X Z hZ U x
  refine ⟨W, g, hWaff, hlift, a, fun w => ?_⟩
  have := hWaff
  rw [mem_range_pointsMap_ι_iff B S hS X Z W.1.hom w,
    range_rep_snd_eq_zeroLocus_definingIdealAt B S hS X Z W, ha]

end AlgebraicGeometry.Space

end
