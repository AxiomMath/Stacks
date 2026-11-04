module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfUniversallyClosedSurjection
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineViewOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceSurjectiveViewOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineStageOfAffineLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfFirstOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.NilpotentApproximation

/-!
# A thickening of an affine algebraic space is affine

Let `Z ⊆ W` be a closed subspace of an algebraic space with the same points as `W`, i.e. a
thickening (Stacks 05ZK). If `Z` is affine then so is `W`. This is the case of Stacks 07VT (an
algebraic space receiving a surjective universally closed morphism from an affine scheme is affine)
in which the morphism is a surjective closed immersion. It is the only case that the proof of
Stacks 07VU, equivalently Remark 049D, uses.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isClosedSubspace_of_isSurjective`: a closed subspace
  with all the points of `W`, if affine, forces `W` to be affine;
  `AlgebraicGeometry.Space.isAffineSpace_of_isClosedSubspace_of_isSurjective_terminal` is the same
  statement over `Spec ℤ`.
* `AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`: the same for a
  surjective closed immersion `Z ⟶ W` with affine source.

## Implementation notes

The source's proof of 07VT writes the morphism as a directed limit of finite morphisms of finite
presentation (Stacks 09YA) and takes an affine stage (Stacks 07SQ). It then needs the finite,
finitely presented case, which rests on Noetherian approximation of algebraic spaces (Stacks
07SU) and on Stacks 07VP. For a thickening none of this is needed:

* `W` is quasi-compact (Stacks 040W) and separated (Stacks 05Z2), so an affine surjective étale
  chart `V ⟶ W` has affine relation `R = V ×_W V`
  (`AlgebraicGeometry.Space.isAffine_of_isAbsolutelySeparated`);
* `Z` is the intersection of the directed family of closed subspaces `Z_G ⊇ Z` of
  `StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/NilpotentApproximation.lean`, each of which
  has a nilpotent ideal on the chart;
* all the `Z_G` are closed subspaces of the one space `W`, so their intersection is their limit,
  and Stacks 07SQ holds for them with no bound on the index,
  `AlgebraicGeometry.Space.exists_isAffineSpace_of_closedSubspaces_terminal`. So some `Z_G` is
  affine;
* `Z_G ⊆ W` is of finite order, so `W` is affine by
  `AlgebraicGeometry.Space.isAffineSpace_of_chartKer_pow_eq_bot`, the finite-order case of
  Stacks 05ZR.

## References

* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 05Z2](https://stacks.math.columbia.edu/tag/05Z2)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If a surjective morphism factors as `f ≫ g`, then `g` is surjective. -/
private theorem isSurjective_of_comp_eq {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h) (hh : IsSurjective B S hS h) :
    IsSurjective B S hS g := by
  intro y
  obtain ⟨x, rfl⟩ := hh y
  exact ⟨pointsMap B S hS X f x, by rw [← pointsMap_comp_apply, hfg]⟩

/-- **A thickening of an affine algebraic space is affine, over `Spec ℤ`** (the thickening case
of Stacks 07VT). Let `Z ⊆ W` be a closed subspace of an algebraic space over `Spec ℤ` whose
inclusion is surjective on points. If `Z` is affine, then so is `W`. -/
theorem isAffineSpace_of_isClosedSubspace_of_isSurjective_terminal
    (W : AlgebraicSpaces B (⊤_ Scheme.{u}) B.contains_terminal)
    (Z : ClosedSubspaces B _ B.contains_terminal W.1)
    (hsurj : IsSurjective B _ B.contains_terminal Z.1.ι)
    (haff : IsAffineSpace B _ B.contains_terminal Z.1.toFunctor) :
    IsAffineSpace B _ B.contains_terminal W.1 := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let Zs : AlgebraicSpaces B _ hZ := ⟨Z.1.toFunctor, Z.2.1⟩
  let V₀ : SpacesEtale B _ hZ Zs := ⟨Over.mk (𝟙 Zs), fun U φ hφ ↦ hφ⟩
  have hZqcsep : IsQuasiCompactSeparated B _ hZ hZ Z.1.toFunctor :=
    isQuasiCompactSeparated_of_isAffineSpace B _ hZ hZ Zs V₀ haff
  have hWqc : IsQuasiCompactSpace B _ hZ W.1 :=
    IsQuasiCompactSpace.of_isSurjective B _ hZ Z.2.1 W.2 hsurj hZqcsep.1
  have hWsep : IsAbsolutelySeparated B _ hZ hZ W.1 :=
    isAbsolutelySeparated_of_isSurjective_of_universallyClosed B _ hZ hZ Z.2.1 W.2 Z.1.ι hsurj
      (universallyClosed_of_isClosedImmersion B _ hZ Z.2.1 W.2 Z.1.ι Z.2.2) hZqcsep.2
  have hWqs : IsAbsolutelyQuasiSeparated B _ hZ hZ W.1 :=
    isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B _ hZ hZ W.1 hWsep
  obtain ⟨V, φ, hV, hs, hφe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B _ hZ W.1 W.2).1 hWqc
  have he := presheaf_etale_of_isEtale B _ hZ hφe
  have : IsAffine ((BigFppfOver.toScheme B _ hZ).obj V) := hV
  have : IsAffine ((BigFppfOver.toScheme B _ hZ).obj (atlasRelation B _ hZ hs)) :=
    isAffine_of_isAbsolutelySeparated B _ hZ hZ hWsep
      (isPullback_yoneda_map_atlasRelation B _ hZ hs) hV hV
  have : IsDirected (ApproxIndex B _ hZ he Z) (· ≤ ·) := isDirected_approxIndex B _ hZ he Z
  have hinf := eq_iInf_approxStage B _ hZ hs he Z hWqs
  obtain ⟨G, -, hGaff⟩ := exists_isAffineSpace_of_closedSubspaces_terminal W hWqc hWsep
    (⟨∅, by simp⟩ : ApproxIndex B _ hZ he Z) (approxStage B _ hZ he Z)
    (approxStage_antitone B _ hZ he Z) (hinf ▸ haff)
  obtain ⟨n, hn⟩ := exists_chartKer_approxStage_pow_eq_bot B _ hZ he Z hWqs hsurj G
  have hGsurj : IsSurjective B _ hZ (approxStage B _ hZ he Z G).1.ι :=
    isSurjective_of_comp_eq B _ hZ
      (Subfunctor.homOfLe_ι (le_approxStage B _ hZ hs he Z hWqs G)) hsurj
  exact isAffineSpace_of_chartKer_pow_eq_bot W _ φ hs he hV hGsurj hn hGaff

/-- **A thickening of an affine algebraic space is affine** (the thickening case of Stacks 07VT).
Let `Z ⊆ W` be a closed subspace of an algebraic space `W` over `S` whose inclusion is surjective
on points. If `Z` is affine, then so is `W`.

Viewing everything over `Spec ℤ` (Spaces, Definition 65.16.2) changes neither affineness
(`AlgebraicGeometry.Space.isAffineSpace_viewOverIntegers_iff`) nor the closed subspace and its
surjectivity (`AlgebraicGeometry.Space.exists_closedSubspace_viewOverIntegers_of_isSurjective`),
so this is `AlgebraicGeometry.Space.isAffineSpace_of_isClosedSubspace_of_isSurjective_terminal`. -/
theorem isAffineSpace_of_isClosedSubspace_of_isSurjective
    (W : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS W.1)
    (hsurj : IsSurjective B S hS Z.1.ι) (haff : IsAffineSpace B S hS Z.1.toFunctor) :
    IsAffineSpace B S hS W.1 := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  obtain ⟨Z', hZ'surj, ⟨e⟩⟩ :=
    exists_closedSubspace_viewOverIntegers_of_isSurjective B S hS W Z hsurj
  let W' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ :=
    ⟨viewOverIntegers B S hS hZ W.1,
      isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) ⟨terminal.from S⟩ _ W.2⟩
  exact (isAffineSpace_viewOverIntegers_iff B S hS hZ).1
    (isAffineSpace_of_isClosedSubspace_of_isSurjective_terminal B W' Z' hZ'surj
      (((isAffineSpace_viewOverIntegers_iff B S hS hZ).2 haff).of_iso e.symm))

/-- **The target of a surjective closed immersion with affine source is affine** (the thickening
case of Stacks 07VT). -/
theorem isAffineSpace_of_isClosedImmersion_of_isSurjective
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hg : IsClosedImmersion B S hS g) (hsurj : IsSurjective B S hS g)
    (haff : IsAffineSpace B S hS X) : IsAffineSpace B S hS Y := by
  have : Mono g := mono_of_isClosedImmersion B S hS g hg
  let Z : ClosedSubspaces B S hS Y :=
    ⟨Subfunctor.range g, isClosedSubspace_range_of_isClosedImmersion B S hS g hX hg⟩
  have hZsurj : IsSurjective B S hS Z.1.ι :=
    isSurjective_of_comp_eq B S hS (Subfunctor.toRange_ι g) hsurj
  exact isAffineSpace_of_isClosedSubspace_of_isSurjective B S hS ⟨Y, hY⟩ Z hZsurj
    (haff.of_iso (rangeIsoOfMono B S hS g))

end AlgebraicGeometry.Space

end
