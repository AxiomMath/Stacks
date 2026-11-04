module

public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.SingularPointNeighborhoods

/-!
# Elementary étale neighbourhoods of finitely many closed points of a decent space

Let `X` be a decent algebraic space over a scheme `S` and let `x₁, …, xₙ` be pairwise distinct
closed points of `X`. Section 0BH9 of the Stacks project chooses, for each `i`, an elementary
étale neighbourhood `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` with `Uᵢ` affine, such that `uᵢ` is the only point of
`Uᵢ` over `xᵢ` and no point of `Uᵢ` lies over `xⱼ` for `j ≠ i`. This file makes that choice, as
the datum `AlgebraicGeometry.Space.ClosedPointNeighborhoods` with the given space and the given
points.

## Main results

* `AlgebraicGeometry.Space.exists_elementaryEtaleNeighborhood_avoiding_of_isDecentSpace`: one
  neighbourhood, avoiding a finite set of closed points not containing the given one.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.ofPoints`: the whole family.

## References

* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **One neighbourhood of Section 0BH9.** At a point `x` of a decent algebraic space `X` and a
finite set `T` of closed points not containing `x`, there is an elementary étale neighbourhood of
`x` whose scheme is affine, which carries a single point over `x` and no point over `T`: take an
affine elementary étale neighbourhood with a single point over `x` (Stacks 0BBP) and shrink it to
a basic open avoiding the closed preimage of `T`. -/
theorem exists_elementaryEtaleNeighborhood_avoiding_of_isDecentSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (x : points B S hS X) (T : Set (points B S hS X))
    (hT : T.Finite) (hTc : ∀ t ∈ T, IsClosed ({t} : Set (points B S hS X))) (hxT : x ∉ T) :
    ∃ E : ElementaryEtaleNeighborhood B S hS X hX x,
      IsAffine E.scheme.left.1 ∧
      (∀ y : points B S hS (yoneda.obj E.scheme),
        pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y = x →
          y = presheafPoint B S hS E.scheme E.point E.residueField_contained) ∧
      (∀ y : points B S hS (yoneda.obj E.scheme),
        pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y ∉ T) := by
  classical
  obtain ⟨E, hEaff, huniq, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX hdec x
  let Es := E.scheme.left.1
  let e := schemePointsHomeomorph B S hS E.scheme
  let π : Es → points B S hS X := fun w => pointsMap B S hS _ E.toSpace (e.symm w)
  have hπc : Continuous π := (continuous_pointsMap B S hS E.toSpace).comp e.symm.continuous
  have hπpt (z : points B S hS (yoneda.obj E.scheme)) :
      π (pointsToScheme B S hS E.scheme z) = pointsMap B S hS _ E.toSpace z := by
    simp only [π]
    rw [← schemePointsHomeomorph_apply, e.symm_apply_apply]
  have hTclosed : IsClosed T := by
    rw [← Set.biUnion_of_singleton T]
    exact hT.isClosed_biUnion hTc
  have hptx : π E.point = x := by
    simpa only [pointsToScheme_presheafPoint] using
      (hπpt (presheafPoint B S hS E.scheme E.point E.residueField_contained)).trans E.map_point
  let O : Es.Opens := ⟨(π ⁻¹' T)ᶜ, (hTclosed.preimage hπc).isOpen_compl⟩
  have hEaff' : IsAffine Es := hEaff
  obtain ⟨f, hfle, hfmem⟩ := (isAffineOpen_top Es).exists_basicOpen_le (V := O)
    ⟨E.point, fun h => hxT (hptx ▸ h)⟩ (Set.mem_univ _)
  let W : Es.Opens := Es.basicOpen f
  let E' := openRestrictionNeighborhood B S hS X hX x E W hfmem
  have hpts (y : points B S hS (yoneda.obj E'.scheme)) :
      pointsMap B S hS _ E'.toSpace y =
        π (W.ι (pointsToScheme B S hS E'.scheme y)) := by
    rw [pointsMap_openRestrictionNeighborhood_toSpace B S hS hX x E W hfmem y, ← hπpt,
      pointsToScheme_pointsMap_yoneda]
    rfl
  refine ⟨E', ?_, ?_, ?_⟩
  · exact ((isAffineOpen_top Es).basicOpen f : IsAffineOpen W)
  · intro y hy
    rw [hpts] at hy
    have hw : W.ι (pointsToScheme B S hS E'.scheme y) = E.point := by
      have := congrArg (pointsToScheme B S hS E.scheme)
        (huniq (e.symm (W.ι (pointsToScheme B S hS E'.scheme y))) hy)
      rwa [← schemePointsHomeomorph_apply, e.apply_symm_apply, pointsToScheme_presheafPoint]
        at this
    apply injective_pointsToScheme B S hS E'.scheme
    rw [pointsToScheme_presheafPoint]
    exact W.ι.isOpenEmbedding.injective hw
  · intro y hy
    rw [hpts] at hy
    exact hfle ((Scheme.Opens.range_ι W).subset (Set.mem_range_self _)) hy

namespace ClosedPointNeighborhoods

/-- **The neighbourhoods of Section 0BH9 for given closed points of a decent space.** For pairwise
distinct closed points `x₁, …, xₙ` of a decent algebraic space `X`, a choice of affine elementary
étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` with `uᵢ` the only point over `xᵢ` and no point over
`xⱼ` for `j ≠ i`. The space of the datum is `X` and its points are the `xᵢ`, by definition. -/
def ofPoints (X : AlgebraicSpaces B S hS) (hdec : IsDecentSpace B S hS X.obj) {n : ℕ}
    (pt : Fin n → points B S hS X.obj) (hinj : Function.Injective pt)
    (hcl : ∀ i, IsClosed ({pt i} : Set (points B S hS X.obj))) :
    ClosedPointNeighborhoods B S hS n :=
  have hE := fun i : Fin n =>
    exists_elementaryEtaleNeighborhood_avoiding_of_isDecentSpace X.property hdec (pt i)
      (pt '' {j | j ≠ i}) (Set.toFinite _) (Set.forall_mem_image.2 fun j _ => hcl j)
      fun ⟨_, hj, hji⟩ => hj (hinj hji)
  { space := X
    decent := hdec
    point := pt
    point_injective := hinj
    isClosed_point := hcl
    neighborhood := fun i => (hE i).choose
    isAffine_neighborhood := fun i => (hE i).choose_spec.1
    eq_of_map_eq_point := fun i => (hE i).choose_spec.2.1
    map_ne_point := fun i j hij y hy =>
      (hE i).choose_spec.2.2 y ⟨j, fun h => hij h.symm, hy.symm⟩ }

/-- The space of the datum `ofPoints X hdec pt hinj hcl` is `X`. -/
@[simp]
theorem ofPoints_space (X : AlgebraicSpaces B S hS) (hdec : IsDecentSpace B S hS X.obj)
    {n : ℕ} (pt : Fin n → points B S hS X.obj) (hinj : Function.Injective pt)
    (hcl : ∀ i, IsClosed ({pt i} : Set (points B S hS X.obj))) :
    (ofPoints X hdec pt hinj hcl).space = X := rfl

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
