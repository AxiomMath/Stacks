module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCompactification
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaReductions
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeUniversalHomeo
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange

/-!
# From a proper compactifiable cover over a gerbe locus to a Chow cover

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space and `V ⊆ Y` an open
subspace over which `𝒳` is a gerbe. The conclusion of [Stacks, Tag 0CQ7] for `(f, V)` is a proper
`h : Z ⟶ 𝒳` from an algebraic space, compactifiable over `Y`, whose image in `|Y|` contains `|V|`.
If the points of `𝒳` lying over `V` are dense, `h` is surjective, so this is the conclusion of
Chow's lemma (Stacks 0CQ8) for `f`. This is the step of the proof of Stacks 0CQ8 after the
application of Stacks 0CQ7.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_hasProperCompactifiableCover`.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A proper compactifiable cover over a dense gerbe locus is a Chow cover.** Let
`f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space and `V ⊆ Y` an open
subspace such that `V ×_Y 𝒳 ⟶ V` is a gerbe and the points of `𝒳` over `V` (the image of
`|V ×_Y 𝒳|`) are dense in `|𝒳|`. If the conclusion of [Stacks, Tag 0CQ7] holds for `(f, V)`, the
conclusion of Stacks 0CQ8 holds for `f`.

The cover `h : Z ⟶ 𝒳` is proper, so its image is closed; it contains every point `x` of `𝒳` over
`V`: some point `z` of `Z` maps to the image `v` of `x` in `|V|`, and `x` and `h(z)` are two points
of `𝒳` over `v`, hence come from two points of `V ×_Y 𝒳` over `v` (Stacks 04XH), which agree since
a gerbe is injective on points (Stacks 06R9). -/
theorem HasChowCover.of_hasProperCompactifiableCover {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (V : Subfunctor Y)
    (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    (hdense : @Dense _ (pointTopology B S hS 𝒳.val) (Set.range (pointsMap B S hS
      (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).snd)))
    (h : HasProperCompactifiableCover.{u, w} B S hS hY f V) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨Zbar, Z, hZbar, hZ, j, gbar, a, hj, hgbar, ha, ⟨ea⟩, hcov⟩ := h
  refine ⟨Z, Zbar, hZ, hZbar, a, j, gbar, ha, ?_, hj, hgbar, ⟨ea⟩⟩
  let P := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ f
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
  let _ := pointTopology B S hS P.pt.val
  let _ := pointTopology B S hS (algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1).val
  -- the image of `h` is closed
  have hclosed : _root_.IsClosed (Set.range (pointsMap B S hS a)) :=
    (isClosed_of_universallyClosed B S hS a ha.2.2).isClosed_range
  -- the points of `𝒳` over `V` are in the image of `h`
  have hsub : Set.range (pointsMap B S hS P.snd) ⊆ Set.range (pointsMap B S hS a) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨v₀, hv₀⟩ := (spacePointMap_id_bijective B S hS V.toFunctor).2
      (pointsMap B S hS P.fst p)
    obtain ⟨z₀, hz₀⟩ := hcov ⟨v₀, rfl⟩
    let z := spacePointMap B S hS Z (fibredCategory B S hS Z)
      (BasedFunctor.id (fibredCategory B S hS Z).val) z₀
    have hPw : pointsMap B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι)
        (pointsMap B S hS P.fst p) = pointsMap B S hS f (pointsMap B S hS P.snd p) := by
      have h1 := congrFun (pointsMap_eq_of_iso B S hS P.iso) p
      rwa [pointsMap_comp, pointsMap_comp] at h1
    have hfa : pointsMap B S hS f (pointsMap B S hS a z) =
        pointsMap B S hS (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι)
          (pointsMap B S hS P.fst p) := by
      have h1 := congrFun (pointsMap_eq_of_iso B S hS ea) z
      rw [pointsMap_comp] at h1
      refine h1.trans ?_
      have h2 := spacePointMap_pointsMap_associatedMap B S hS (j ≫ gbar) z₀
      have h3 := spacePointMap_pointsMap_associatedMap B S hS V.ι v₀
      refine h2.symm.trans ?_
      rw [hz₀, h3, hv₀]
    obtain ⟨p', hp'1, hp'2⟩ := exists_point_of_isTwoFibreProduct B S hS P hP
      (pointsMap B S hS P.fst p) (pointsMap B S hS a z) hfa.symm
    have hpp : p' = p :=
      (isHomeomorph_pointsMap_of_isGerbeOver B S hS P.fst hG).injective hp'1
    exact ⟨z, by rw [← hp'2, hpp]⟩
  have huniv : Set.range (pointsMap B S hS a) = Set.univ :=
    Set.eq_univ_of_subset (hclosed.closure_subset_iff.2 hsub) hdense.closure_eq
  exact Set.range_eq_univ.1 huniv

end AlgebraicGeometry.Stack.AlgebraicStacks

end
