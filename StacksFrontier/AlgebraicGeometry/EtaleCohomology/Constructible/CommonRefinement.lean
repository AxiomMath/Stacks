module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# Common refinement of two constructible stratifications

A constructible sheaf on the small étale site of a scheme `X` is one which becomes finite
locally constant on the strata of *some* finite partition of each affine open by constructible
locally closed subschemes, namely a `AlgebraicGeometry.ConstructibleStratification`. Two
constructible sheaves therefore come with two unrelated partitions, and every argument which
compares them — a morphism of constructible sheaves, a short exact sequence of them — must
first replace the two partitions by a single one adapted to both.

This file constructs that single partition. The strata of
`AlgebraicGeometry.ConstructibleStratification.inf` are the fibre products of a stratum of the
first partition with a stratum of the second, and each of them comes with a morphism to the
stratum of either partition that it refines, compatible with the inclusion into the ambient
scheme.

## Main definitions

* `AlgebraicGeometry.ConstructibleStratification.interPiece`, `.interFst`, `.interSnd` and
  `.interInclusion`: the fibre product of two strata, its two projections and its inclusion
  into the ambient scheme.
* `AlgebraicGeometry.ConstructibleStratification.inf`: the common refinement of two
  constructible stratifications of the same open subscheme.

## Main results

* `AlgebraicGeometry.ConstructibleStratification.range_interInclusion`: the image of the fibre
  product of two strata is the intersection of their images.
* `AlgebraicGeometry.ConstructibleStratification.isImmersion_interFst` and
  `AlgebraicGeometry.ConstructibleStratification.isImmersion_interSnd`: the two projections of a
  refined stratum onto the strata it refines are again immersions.
* `AlgebraicGeometry.ConstructibleStratification.inf_factorsThrough_fst` and
  `AlgebraicGeometry.ConstructibleStratification.inf_factorsThrough_snd`: each stratum of the
  refinement maps to the stratum of the first, resp. the second, partition that contains it,
  and this map composed with that stratum's inclusion is the refined stratum's own inclusion.
* `AlgebraicGeometry.ConstructibleStratification.exists_common_refinement`: the packaged
  statement, which is the form consumers use.

## Implementation notes

A stratum is recorded as an object of the big étale site together with an immersion into the
ambient scheme, so the refinement has to produce such an object. The fibre product of the two
immersions is one: `AlgebraicGeometry.Scheme.size_pullback_lt` keeps it below the site's
cardinal cutoff. That the resulting map to the ambient scheme is again an immersion is
composition of immersions together with stability of immersions under base change, and that its
image is the intersection of the two images is
`AlgebraicGeometry.Scheme.Pullback.range_fst_comp` — the fibre product of two immersions
surjects onto the intersection of their images, not merely into it, which is what makes the
refinement cover the open subscheme again.

Morphisms of the big étale site are morphisms of a full subcategory of schemes, so they are
built with `CategoryTheory.ObjectProperty.homMk` and their underlying scheme morphisms are read
off by `CategoryTheory.ObjectProperty.ι_map`; both are definitional, which is why the
compatibilities below hold by `rfl`.

The index type is `Fin (s.n * t.n)`, reindexed from `Fin s.n × Fin t.n` by `finProdFinEquiv`,
because `AlgebraicGeometry.ConstructibleStratification` fixes `Fin n` as the shape of its
family of strata.

Disjointness of the refined strata uses only disjointness of the given ones: a refined stratum
is contained in both of the strata it refines, and two distinct refined strata differ in at
least one of the two coordinates.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace ConstructibleStratification

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {U : X.obj.Opens}
  (s t : ConstructibleStratification B X U)

/-- The fibre product of the `i`-th stratum of `s` with the `j`-th stratum of `t`, as an object
of the big étale site: the fibre product of two schemes below the cutoff is below the cutoff. -/
public def interPiece (i : Fin s.n) (j : Fin t.n) : B.Scheme :=
  ⟨pullback (B.inclusion.map (s.inclusion i)) (B.inclusion.map (t.inclusion j)),
    Scheme.size_pullback_lt _ _ (s.piece i).property (t.piece j).property⟩

/-- The projection of an intersection stratum onto the stratum of `s` it refines. -/
public def interFst (i : Fin s.n) (j : Fin t.n) : interPiece s t i j ⟶ s.piece i :=
  ObjectProperty.homMk
    (pullback.fst (B.inclusion.map (s.inclusion i)) (B.inclusion.map (t.inclusion j)))

/-- The projection of an intersection stratum onto the stratum of `t` it refines. -/
public def interSnd (i : Fin s.n) (j : Fin t.n) : interPiece s t i j ⟶ t.piece j :=
  ObjectProperty.homMk
    (pullback.snd (B.inclusion.map (s.inclusion i)) (B.inclusion.map (t.inclusion j)))

/-- The inclusion of an intersection stratum into the ambient scheme. -/
public def interInclusion (i : Fin s.n) (j : Fin t.n) : interPiece s t i j ⟶ X :=
  interFst s t i j ≫ s.inclusion i

/-- The underlying scheme morphism of the inclusion of an intersection stratum is the first
projection of the fibre product followed by the inclusion of the stratum of `s`. -/
public theorem map_interInclusion (i : Fin s.n) (j : Fin t.n) :
    B.inclusion.map (interInclusion s t i j) =
      pullback.fst (B.inclusion.map (s.inclusion i)) (B.inclusion.map (t.inclusion j)) ≫
        B.inclusion.map (s.inclusion i) :=
  rfl

/-- The inclusion of an intersection stratum also factors through the stratum of `t`. -/
public theorem interInclusion_eq_snd (i : Fin s.n) (j : Fin t.n) :
    interInclusion s t i j = interSnd s t i j ≫ t.inclusion j :=
  ObjectProperty.hom_ext _ pullback.condition

/-- The image of an intersection stratum is the intersection of the images of the two strata it
refines. This is where the fibre product is used as a scheme-theoretic intersection: a point of
the ambient scheme lying in both images has a preimage in the fibre product. -/
public theorem range_interInclusion (i : Fin s.n) (j : Fin t.n) :
    Set.range (B.inclusion.map (interInclusion s t i j)).base =
      Set.range (B.inclusion.map (s.inclusion i)).base ∩
        Set.range (B.inclusion.map (t.inclusion j)).base :=
  Scheme.Pullback.range_fst_comp (B.inclusion.map (s.inclusion i))
    (B.inclusion.map (t.inclusion j))

/-- The projection of an intersection stratum onto a stratum of `s` is itself an immersion, being
the base change of the immersion cutting out the stratum of `t`. -/
public theorem isImmersion_interFst (i : Fin s.n) (j : Fin t.n) :
    IsImmersion (B.inclusion.map (interFst s t i j)) := by
  have ht := t.isImmersion j
  exact (inferInstance : IsImmersion
    (pullback.fst (B.inclusion.map (s.inclusion i)) (B.inclusion.map (t.inclusion j))))

/-- The projection of an intersection stratum onto a stratum of `t` is itself an immersion, being
the base change of the immersion cutting out the stratum of `s`. -/
public theorem isImmersion_interSnd (i : Fin s.n) (j : Fin t.n) :
    IsImmersion (B.inclusion.map (interSnd s t i j)) := by
  have hs := s.isImmersion i
  exact (inferInstance : IsImmersion
    (pullback.snd (B.inclusion.map (s.inclusion i)) (B.inclusion.map (t.inclusion j))))

/-- An intersection stratum is immersed in the ambient scheme: its inclusion is the base change
of one immersion followed by the other. -/
public theorem isImmersion_interInclusion (i : Fin s.n) (j : Fin t.n) :
    IsImmersion (B.inclusion.map (interInclusion s t i j)) := by
  have hs := s.isImmersion i
  have ht := t.isImmersion j
  exact (inferInstance : IsImmersion
    (pullback.fst (B.inclusion.map (s.inclusion i)) (B.inclusion.map (t.inclusion j)) ≫
      B.inclusion.map (s.inclusion i)))

/-- **The common refinement of two constructible stratifications of the same open subscheme.**
Its strata are the fibre products of a stratum of the first with a stratum of the second. -/
public def inf : ConstructibleStratification B X U where
  n := s.n * t.n
  piece k := interPiece s t (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  inclusion k := interInclusion s t (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  isImmersion k := isImmersion_interInclusion s t _ _
  contained k := by
    rw [range_interInclusion]
    exact Set.inter_subset_left.trans (s.contained _)
  constructible k := by
    rw [range_interInclusion, Set.preimage_inter]
    exact (s.constructible _).inter (t.constructible _)
  pairwise_disjoint k l hkl := by
    rw [range_interInclusion, range_interInclusion]
    have hne : finProdFinEquiv.symm k ≠ finProdFinEquiv.symm l := fun h =>
      hkl (finProdFinEquiv.symm.injective h)
    by_cases h₁ : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1
    · have h₂ : (finProdFinEquiv.symm k).2 ≠ (finProdFinEquiv.symm l).2 := fun h₂ =>
        hne (Prod.ext h₁ h₂)
      exact (t.pairwise_disjoint _ _ h₂).mono Set.inter_subset_right Set.inter_subset_right
    · exact (s.pairwise_disjoint _ _ h₁).mono Set.inter_subset_left Set.inter_subset_left
  covers := by
    refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (s.covers ▸ hx)
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (t.covers ▸ hx)
      refine Set.mem_iUnion.mpr ⟨finProdFinEquiv (i, j), ?_⟩
      rw [Equiv.symm_apply_apply, range_interInclusion]
      exact ⟨hi, hj⟩
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      rw [range_interInclusion] at hk
      exact s.contained _ hk.1

/-- The common refinement has one stratum for each pair of strata of the two given
stratifications. -/
@[simp]
public theorem inf_n : (s.inf t).n = s.n * t.n := rfl

/-- Each stratum of the common refinement maps to the stratum of the first stratification which
contains it, compatibly with the inclusions into the ambient scheme, and the map is an
immersion. -/
public theorem inf_factorsThrough_fst (k : Fin (s.inf t).n) :
    ∃ (i : Fin s.n) (a : (s.inf t).piece k ⟶ s.piece i),
      IsImmersion (B.inclusion.map a) ∧ a ≫ s.inclusion i = (s.inf t).inclusion k :=
  ⟨_, interFst s t _ _, isImmersion_interFst s t _ _, rfl⟩

/-- Each stratum of the common refinement maps to the stratum of the second stratification which
contains it, compatibly with the inclusions into the ambient scheme, and the map is an
immersion. -/
public theorem inf_factorsThrough_snd (k : Fin (s.inf t).n) :
    ∃ (j : Fin t.n) (b : (s.inf t).piece k ⟶ t.piece j),
      IsImmersion (B.inclusion.map b) ∧ b ≫ t.inclusion j = (s.inf t).inclusion k :=
  ⟨_, interSnd s t _ _, isImmersion_interSnd s t _ _, (interInclusion_eq_snd s t _ _).symm⟩

/-- **Any two constructible stratifications of the same open subscheme have a common
refinement**: a stratification each of whose strata factors through a stratum of either given
one. This is the form in which the refinement is used, a morphism or a short exact sequence of
constructible sheaves being compared on a single stratification adapted to both sheaves. -/
public theorem exists_common_refinement :
    ∃ r : ConstructibleStratification B X U, ∀ k : Fin r.n,
      (∃ (i : Fin s.n) (a : r.piece k ⟶ s.piece i),
          IsImmersion (B.inclusion.map a) ∧ a ≫ s.inclusion i = r.inclusion k) ∧
        ∃ (j : Fin t.n) (b : r.piece k ⟶ t.piece j),
          IsImmersion (B.inclusion.map b) ∧ b ≫ t.inclusion j = r.inclusion k :=
  ⟨s.inf t, fun k => ⟨inf_factorsThrough_fst s t k, inf_factorsThrough_snd s t k⟩⟩

end ConstructibleStratification

end AlgebraicGeometry

end
