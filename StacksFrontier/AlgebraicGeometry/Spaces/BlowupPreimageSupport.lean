module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents

/-!
# The points of a closed subspace whose inverse image under a blowup is prescribed

Let `b : X' ⟶ X` be the blowup of an algebraic space `X` in a closed subspace `Z`, let
`Z' ⊆ X'` be a closed subspace and let `W ⊆ X` be a closed subspace whose inverse image under
`b` is `Z' + dE`, the sum of `Z'` with `d` copies of the exceptional divisor `E = b^{-1}(Z)`.
Then every point of `W` lies in `|Z| ∪ |b|(|Z'|)`.

This is the support clause of the second centre that Stacks 0860 forms on the base: in the
source it is read off Stacks 085N, but it is in fact automatic once the inverse image is known.
A point `x` of `W` outside `Z` lies in the open complement `X ∖ Z`, over which `b` is an
isomorphism by Stacks 085T part (1), so `x = |b|(x')` for a point `x'` of `b^{-1}(W) = Z' + dE`;
since `x ∉ |Z|`, the point `x'` is not on `E`, so it is on `Z'`.

## Main results

* `AlgebraicGeometry.Space.subspacePointSet_subset_union_image_of_preimage_eq`: the inclusion
  `|W| ⊆ |Z| ∪ |b|(|Z'|)`.

## References

* [Stacks Project, Tag 0860](https://stacks.math.columbia.edu/tag/0860)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X X' : AlgebraicSpaces B S hS}

/-- **The points of a closed subspace with inverse image `Z' + dE` lie in `|Z| ∪ |b|(|Z'|)`.**
Let `b : X' ⟶ X` be the blowup of `X` in `Z` and let `W ⊆ X` be a closed subspace with
`b^{-1}(W) = Z' + dE`, where `E = b^{-1}(Z)`.  Then `|W| ⊆ |Z| ∪ |b|(|Z'|)`.

Off `Z` the blowup is an isomorphism (Stacks 085T part (1),
`AlgebraicGeometry.Space.isIso_fromPreimage_openComplement`), so a point of `W` outside `Z` is
the image of a point of `b^{-1}(W)` outside `E`, and the points of the sum `Z' + dE` outside `E`
are points of `Z'`. -/
theorem subspacePointSet_subset_union_image_of_preimage_eq
    {Z : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    (Z' : ClosedSubspaces B S hS X'.1) (W : ClosedSubspaces B S hS X.1) (d : ℕ)
    (hWpre : preimageClosedSubspace b W =
      sumClosedSubspacesList X' (fun _ : Unit => preimageClosedSubspace b Z) Z'
        (List.replicate d ())) :
    subspacePointSet B S hS X.1 W.1 ⊆
      subspacePointSet B S hS X.1 Z.1 ∪
        pointsMap B S hS X'.1 b.hom '' subspacePointSet B S hS X'.1 Z'.1 := by
  intro x hxW
  by_cases hxZ : x ∈ subspacePointSet B S hS X.1 Z.1
  · exact Or.inl hxZ
  right
  set U := openComplementOfClosedSubspace B S hS X Z with hU
  have hxU : x ∈ subspacePointSet B S hS X.1 U.1 := by
    rw [subspacePointSet_openComplement]
    exact hxZ
  obtain ⟨u, rfl⟩ := hxU
  have := isIso_fromPreimage_openComplement hb
  obtain ⟨v, hv⟩ := pointsMap_surjective_of_isIso B S hS (U.1.fromPreimage b.hom) u
  set x' := pointsMap B S hS _ (U.1.preimage b.hom).ι v with hx'
  have hbx' : pointsMap B S hS X'.1 b.hom x' = pointsMap B S hS U.1.toFunctor U.1.ι u := by
    rw [hx', ← hv, ← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  have hx'D : x' ∈ subspacePointSet B S hS X'.1
      (sumClosedSubspacesList X' (fun _ : Unit => preimageClosedSubspace b Z) Z'
        (List.replicate d ())).1 := by
    rw [← hWpre]
    show x' ∈ subspacePointSet B S hS X'.1 (W.1.preimage b.hom)
    rw [subspacePointSet_preimage, Set.mem_preimage, hbx']
    exact hxW
  have hx'E : x' ∉ subspacePointSet B S hS X'.1 (preimageClosedSubspace b Z).1 := by
    show x' ∉ subspacePointSet B S hS X'.1 (Z.1.preimage b.hom)
    rw [subspacePointSet_preimage, Set.mem_preimage, hbx']
    exact hxZ
  by_cases hx'Z' : x' ∈ subspacePointSet B S hS X'.1 Z'.1
  · exact ⟨x', hx'Z', hbx'⟩
  · exact absurd hx'D (Set.disjoint_singleton_left.1
      (disjoint_subspacePointSet_sumClosedSubspacesList X'
        (fun _ : Unit => preimageClosedSubspace b Z) Z' {x'}
        (Set.disjoint_singleton_left.2 hx'Z') (fun _ => Set.disjoint_singleton_left.2 hx'E)
        (List.replicate d ())))

end AlgebraicGeometry.Space

end
