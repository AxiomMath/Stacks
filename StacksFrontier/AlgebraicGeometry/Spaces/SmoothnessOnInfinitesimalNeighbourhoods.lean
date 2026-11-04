module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleAtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtLiftingCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InfinitesimalNeighbourhoodFactorization

/-!
# Smoothness and étaleness tested on the infinitesimal neighbourhoods of a closed subspace

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian, let `Z ⊆ Y` be a closed subspace with `n`th infinitesimal
neighbourhood `Zₙ ⊆ Y`, and set `Xₙ = Zₙ ×_Y X`. If `Xₙ ⟶ Zₙ` is smooth for every `n`, then `f`
is smooth at every point of `f⁻¹(Z)`; if `Xₙ ⟶ Zₙ` is étale for every `n`, then `f` is étale at
every point of `f⁻¹(Z)`. This is Stacks 0APQ.

## Main results

* `AlgebraicGeometry.Space.isSmoothAt_of_isSmooth_nthOrderInfinitesimalNeighbourhood` is
  **Stacks 0APQ, part (1)**.
* `AlgebraicGeometry.Space.isEtaleAt_of_isEtale_nthOrderInfinitesimalNeighbourhood` is
  **Stacks 0APQ, part (2)**.

## Implementation notes

The infinitesimal neighbourhoods are those of Stacks 05ZV,
`AlgebraicGeometry.Space.nthOrderInfinitesimalNeighbourhood`, built on a surjective étale chart
`φ : U ⟶ Y` from the sheaf of ideals `J ⊆ 𝒪_U` cutting out `Z`. Such a `J` exists for every
closed subspace and every surjective étale chart, and it is unique: these are
`AlgebraicGeometry.Space.exists_isInvariantIdealSheaf_invariantSubspace_eq` and
`AlgebraicGeometry.Space.ker_rep_snd_eq_of_invariantSubspace_eq`. So the statements below apply
to an arbitrary closed subspace of `Y`. The base changes `Xₙ` may be any fibre products.

Part (1) follows the source. A lifting problem for `f` at a point above `Z` along a small
extension `B' ⟶ B` of Artinian local rings has its test morphism `Spec B' ⟶ Y` centred in `Z`,
so it factors through some `Zₙ`
(`AlgebraicGeometry.Space.exists_mem_nthOrderInfinitesimalNeighbourhood_of_isArtinianRing`).
The cartesian square then moves the problem to `Xₙ ⟶ Zₙ`. That morphism is smooth, hence
formally smooth by Stacks 04AM (`AlgebraicGeometry.Space.formallySmooth_of_isSmooth'`), which
solves the problem. Stacks 0APN
(`AlgebraicGeometry.Space.isSmoothAt_of_liftsAt_isSmallExtension`) turns the lifting property
back into smoothness at the point.

Part (2) is part (1) together with unramifiedness at the point. The source instead uses that a
morphism is étale exactly when it is smooth of relative dimension zero. Étaleness of every
`Xₙ ⟶ Zₙ` gives smoothness of every `Xₙ ⟶ Zₙ`, hence smoothness of `f` at the point by part (1).
It also gives unramifiedness of `X₀ ⟶ Z₀`, hence unramifiedness of `f` at the point, by the
transfer along a cartesian square
`AlgebraicGeometry.Space.isUnramifiedAt_of_isEtale_baseChange`. Stacks 02GK for algebraic
spaces, `AlgebraicGeometry.Space.isEtaleAt_of_isSmoothAt_of_isUnramifiedAt`, then gives
étaleness at the point.

## References

* [Stacks Project, Tag 02GK](https://stacks.math.columbia.edu/tag/02GK)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
* [Stacks Project, Tag 0APN](https://stacks.math.columbia.edu/tag/0APN)
* [Stacks Project, Tag 0APQ](https://stacks.math.columbia.edu/tag/0APQ)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ Y.1}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- **Stacks 0APQ, part (1).** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which
is locally of finite type, with `Y` locally Noetherian. Let `Z ⊆ Y` be a closed subspace, cut out
on a surjective étale chart `φ : U ⟶ Y` by the invariant sheaf of ideals `J`, so that its `n`th
infinitesimal neighbourhood is `Zₙ = nthOrderInfinitesimalNeighbourhood φ J n`, and let
`Xₙ = Zₙ ×_Y X`. If `Xₙ ⟶ Zₙ` is smooth for every `n`, then `f` is smooth at every point of
`f⁻¹(Z)`.

Every closed subspace is cut out on every surjective étale chart by exactly one invariant sheaf
of ideals (`AlgebraicGeometry.Space.exists_isInvariantIdealSheaf_invariantSubspace_eq`), so this
applies to every closed subspace of `Y`. -/
@[stacks 0APQ "part (1): smooth. Z is an arbitrary closed subspace and Zₙ its nth
infinitesimal neighbourhood (Tag 05ZV), built on a surjective étale chart from the invariant
ideal sheaf cutting out Z, which exists and is unique by
exists_isInvariantIdealSheaf_invariantSubspace_eq and ker_rep_snd_eq_of_invariantSubspace_eq;
Xₙ is any fibre product Zₙ ×_Y X"]
theorem isSmoothAt_of_isSmooth_nthOrderInfinitesimalNeighbourhood
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y.1)
    (hNoeth : HasEtaleLocalProperty B S hS Y.1 (fun W : Scheme.{u} => IsLocallyNoetherian W))
    (hFiniteType : IsLocallyOfFiniteType B S hS f)
    (Z : ClosedSubspaces B S hS Y.1)
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : IsInvariantIdealSheaf B S hS hs J)
    (hZJ : invariantSubspace B S hS φ (Subobject.mk J.subschemeι) = Z.1)
    (Xn : ℕ → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (fn : ∀ n, Xn n ⟶ (nthOrderInfinitesimalNeighbourhood B S hS φ J n).toFunctor)
    (pn : ∀ n, Xn n ⟶ X)
    (hcart : ∀ n, IsPullback (pn n) (fn n) f (nthOrderInfinitesimalNeighbourhood B S hS φ J n).ι)
    (hsmooth : ∀ n, IsSmooth B S hS (fn n))
    (x : points B S hS X)
    (hx : pointsMap B S hS X f x ∈ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι)) :
    IsSmoothAt B S hS f x := by
  refine isSmoothAt_of_liftsAt_isSmallExtension B S hS hX Y.2 f x hNoeth hFiniteType ?_
  intro R' R ψ hψ T T' i e e' hi hRloc p hp α β hpx hcomm
  obtain ⟨hR'loc, -, hR'art, -, -, -⟩ := id hψ
  -- The test morphism to `Y` is centred in `Z`, so it lands in some neighbourhood `Zₙ`.
  have hcentre :
      pointsMap B S hS (yoneda.obj T') β
          (pointsMap B S hS (yoneda.obj T) (yoneda.map i) (p.class B S hS (yoneda.obj T))) =
        pointsMap B S hS X f x := by
    rw [← pointsMap_comp_apply, ← hcomm, pointsMap_comp_apply, hpx]
  obtain ⟨n, hn⟩ := exists_mem_nthOrderInfinitesimalNeighbourhood_of_isArtinianRing B S hS hs
    Z hJ hZJ e' β _ (by rwa [hcentre])
  set Zn := nthOrderInfinitesimalNeighbourhood B S hS φ J n
  have hZn : IsClosedSubspace B S hS Zn :=
    isClosedSubspace_nthOrderInfinitesimalNeighbourhood B S hS hs he hJ n
  have hrange : Subfunctor.range β ≤ Zn := by
    rintro W _ ⟨g, rfl⟩
    have h : Y.1.map g.op (yonedaEquiv β) ∈ Zn.obj W := Zn.map g.op hn
    rwa [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map] at h
  let βn : yoneda.obj T' ⟶ Zn.toFunctor := Subfunctor.lift β hrange
  have hβn : βn ≫ Zn.ι = β := Subfunctor.lift_ι β hrange
  -- The other side of the square factors through the base change.
  have hw : α ≫ f = (yoneda.map i ≫ βn) ≫ Zn.ι := by rwa [Category.assoc, hβn]
  let αn : yoneda.obj T ⟶ Xn n := (hcart n).lift α (yoneda.map i ≫ βn) hw
  have hαn₁ : αn ≫ pn n = α := (hcart n).lift_fst α (yoneda.map i ≫ βn) hw
  have hαn₂ : αn ≫ fn n = yoneda.map i ≫ βn := (hcart n).lift_snd α (yoneda.map i ≫ βn) hw
  -- Smoothness of the base change, hence its formal smoothness, solves the problem there.
  have hXn : IsAlgebraicSpace B S hS (Xn n) :=
    isAlgebraicSpace_of_isPullback hX hZn.1 Y.2.isSheaf Y.2.diagonal_representable (hcart n)
  obtain ⟨γn, hγn₁, hγn₂⟩ := (formallySmooth_of_isSmooth' hXn hZn.1 (hsmooth n)).liftsAt B S hS
    (pointsMap B S hS (yoneda.obj T) αn (p.class B S hS (yoneda.obj T)))
    (fun ⦃_ _⦄ φ => InfinitesimalLifting.IsSmallExtension φ)
    (fun _ _ φ hφ => InfinitesimalLifting.IsSmallExtension.isSquareZeroSurjection φ hφ)
    ψ hψ T T' i e e' hi p hp αn βn rfl hαn₂
  refine ⟨γn ≫ pn n, ?_, ?_⟩
  · rw [← Category.assoc, hγn₁, hαn₁]
  · rw [Category.assoc, (hcart n).w, ← Category.assoc, hγn₂, hβn]

include hs he in
/-- **Stacks 0APQ, part (2).** In the situation of
`AlgebraicGeometry.Space.isSmoothAt_of_isSmooth_nthOrderInfinitesimalNeighbourhood`, if
`Xₙ = Zₙ ×_Y X ⟶ Zₙ` is étale for every `n`, then `f` is étale at every point of `f⁻¹(Z)`.

Étaleness of every base change gives smoothness of every base change, hence smoothness of `f`
at the point by part (1). It also gives unramifiedness of the zeroth base change, hence
unramifiedness of `f` at the point, which lies in the image of `X₀` because the zeroth square
is cartesian. Stacks 02GK for algebraic spaces assembles the two. -/
@[stacks 0APQ "part (2): étale. Z is an arbitrary closed subspace and Zₙ its nth
infinitesimal neighbourhood (Tag 05ZV), built on a surjective étale chart from the invariant
ideal sheaf cutting out Z, which exists and is unique by
exists_isInvariantIdealSheaf_invariantSubspace_eq and ker_rep_snd_eq_of_invariantSubspace_eq;
Xₙ is any fibre product Zₙ ×_Y X"]
theorem isEtaleAt_of_isEtale_nthOrderInfinitesimalNeighbourhood
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y.1)
    (hNoeth : HasEtaleLocalProperty B S hS Y.1 (fun W : Scheme.{u} => IsLocallyNoetherian W))
    (hFiniteType : IsLocallyOfFiniteType B S hS f)
    (Z : ClosedSubspaces B S hS Y.1)
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : IsInvariantIdealSheaf B S hS hs J)
    (hZJ : invariantSubspace B S hS φ (Subobject.mk J.subschemeι) = Z.1)
    (Xn : ℕ → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (fn : ∀ n, Xn n ⟶ (nthOrderInfinitesimalNeighbourhood B S hS φ J n).toFunctor)
    (pn : ∀ n, Xn n ⟶ X)
    (hcart : ∀ n, IsPullback (pn n) (fn n) f (nthOrderInfinitesimalNeighbourhood B S hS φ J n).ι)
    (hetale : ∀ n, IsEtale B S hS (fn n))
    (x : points B S hS X)
    (hx : pointsMap B S hS X f x ∈ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι)) :
    IsEtaleAt B S hS f x := by
  have hZn : ∀ n, IsClosedSubspace B S hS (nthOrderInfinitesimalNeighbourhood B S hS φ J n) :=
    isClosedSubspace_nthOrderInfinitesimalNeighbourhood B S hS hs he hJ
  have hsm := isSmoothAt_of_isSmooth_nthOrderInfinitesimalNeighbourhood B S hS hs he hX f hNoeth
    hFiniteType Z hJ hZJ Xn fn pn hcart
    (fun n => isSmooth_of_isEtale B S hS (hZn n).1 (hetale n)) x hx
  refine isEtaleAt_of_isSmoothAt_of_isUnramifiedAt B S hS hX Y.2 f x hsm ?_
  -- The point lies over a point of the zeroth neighbourhood, which is `Z` itself.
  have hZ₀ : Z.1 ≤ nthOrderInfinitesimalNeighbourhood B S hS φ J 0 := by
    rw [nthOrderInfinitesimalNeighbourhood_zero, hZJ]
  obtain ⟨z, hz⟩ := range_pointsMap_ι_le B S hS hZ₀ hx
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS (hcart 0) x z hz.symm
  have hX₀ : IsAlgebraicSpace B S hS (Xn 0) :=
    isAlgebraicSpace_of_isPullback hX (hZn 0).1 Y.2.isSheaf Y.2.diagonal_representable (hcart 0)
  rw [← hw]
  exact isUnramifiedAt_of_isEtale_baseChange B S hS hX hX₀ Y.2 (hZn 0).1 (hcart 0) hFiniteType
    (hetale 0) w

end AlgebraicGeometry.Space

end
