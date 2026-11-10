module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GenericProjectionIntersection
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines

/-!
# The secant cone of a closed subset at a point

Let `V` be a finite-dimensional vector space over an algebraically closed field `k`, let
`X ⊆ 𝐏(V)` be a closed subset and let `x` be a closed point of `𝐏(V)`. The projection `r_x` away
from `x` is defined on the complement of `x`, and the closure of the image of `X ∖ {x}` is the
set of *secant directions* of `X` at `x`: the directions of the lines joining `x` to the points
of `X` other than `x`. The cone over it with vertex `x` is the *secant cone*. It is a closed
subset of `𝐏(V)` containing `X` and every line joining `x` to a point of `X ∖ {x}`, so for a
closed point `p` outside it the line through `p` and `x` meets `X` only in `x`, and the
projection away from `p` separates `x` from the rest of `X`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.secantDirections`: the closed set of secant
  directions of `X` at `x`, a subset of `𝐏(W_x)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.secantCone`: the cone with vertex `x` over the
  secant directions, a subset of `𝐏(V)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_secantCone`: the secant cone is closed.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.projectionCone_subset_secantCone` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.subset_secantCone`: the secant cone contains the
  lines joining `x` to the points of `X ∖ {x}`, and it contains `X`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.eq_of_projection_eq_of_notMem_secantCone`: for a
  closed point `p` off the secant cone the only point of `X` with the same image as `x` under
  the projection away from `p` is `x` itself.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_secantDirections_le`: for an
  irreducible closed `X` the secant directions have dimension at most `dim X`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.secantDirections_ne_univ_of_topologicalKrullDim_lt`
  and `AlgebraicGeometry.ProjectiveSpaceOfModule.secantDirections_ne_univ_of_isIrreducible`:
  secant directions of dimension less than that of `𝐏(W_x)` are a proper subset of it, as are
  those of an irreducible closed subset of dimension less than `dim 𝐏(W_x)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isClosed_singleton_notMem_secantCone` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_nonempty_forall_eq_of_projection_eq`:
  if the secant directions are not all of `𝐏(W_x)` then a nonempty open subset of `𝐏(V)`
  consists of closed points off the secant cone, hence of centres whose projection separates `x`
  from the rest of `X`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_nonempty_forall_eq_of_isIrreducible`:
  the same conclusion for an irreducible closed subset of dimension less than `dim 𝐏(W_x)`, with
  no hypothesis on the secant directions.

## Implementation notes

The image of `X ∖ {x}` under `r_x` is in general not closed, so the closure in
`secantDirections` cannot be dropped: `x` lies on `X`, so
`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_projection`, which asks that the
closed subset be disjoint from the centre, does not apply, and indeed the projection of a
twisted cubic away from a point on it is a plane conic with the tangent direction at that point
removed. Taking the closure makes the cone closed and keeps the inclusion
`AlgebraicGeometry.ProjectiveSpaceOfModule.projectionCone_subset_secantCone`, which is the
direction used to produce centres off every secant.

The dimension statement proved here is the bound `dim (secantDirections k V x X) ≤ dim X` on the
base of the cone rather than the bound `dim T ≤ dim X + 1` on the cone `T` itself. What a
projection away from a general point needs is that the complement of `T` is nonempty, and that
is governed by the directions alone: a proper closed subset of `𝐏(W_x)` misses a closed point,
and any point of `𝐏(V)` over it lies off `T`. Passing from the bound on the base to
`dim T ≤ dim X + 1` would need in addition that a cone has dimension one more than its base,
that is the fibre dimension of the `𝐏¹`-bundle `r_x`.

Since `x` lies on `X` the source `X ∖ {x}` is not proper, so the bound used is not the one for a
proper image but the one for a morphism locally of finite type over a field,
`AlgebraicGeometry.topologicalKrullDim_closure_image_le`: out of a Noetherian space, the closure
of the image of a *closed* subset has dimension at most that of the subset. That bound is false
for a general subset — the closed points of a curve are a subset of dimension zero whose
closure is the curve — and it is applied here to `X ∖ {x}`, closed in the domain of the
projection away from `x`, an open of `𝐏(V)`, whose space is Noetherian because `𝐏(V)` is
locally of finite type and quasi-compact over the field.

Irreducibility of `X` is a hypothesis of
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_secantDirections_le` and of the
statements built on it, but the dimension bound itself uses only that `X` is closed.

The constancy of the projection away from `W` on a linear subspace
through the centre is used in the form
`AlgebraicGeometry.ProjectiveSpaceOfModule.projection_eq_linearFunctionalPoint_of_mem`, which
takes a submodule whose degree-one equations are killed by the chosen functional, not in the
weaker form `AlgebraicGeometry.ProjectiveSpaceOfModule.projection_eq_linearFunctionalPoint`,
which applies only to a point already known to be cut out by a linear functional.

## References

* [Stacks Project, Tag 0B1Q](https://stacks.math.columbia.edu/tag/0B1Q)
* [Stacks Project, Tag 0B1P](https://stacks.math.columbia.edu/tag/0B1P)
* [Stacks Project, Tag 054J](https://stacks.math.columbia.edu/tag/054J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The secant directions and the secant cone of a closed subset at a point -/

/-- **The secant directions of a subset at a point.** The closure of the image of `X ∖ {x}`
under the projection away from `x`: the directions of the lines joining `x` to the points of `X`
other than `x`. -/
public def secantDirections (x : projectiveSpaceOfModule k V)
    (X : Set (projectiveSpaceOfModule k V)) :
    Set (projectiveSpaceOfModule k ↥(pointSubmodule k V x)) :=
  closure ((projection k V (pointSubmodule k V x)).base ''
    ((projectionDomain k V (pointSubmodule k V x)).ι.base ⁻¹' X))

/-- The set of secant directions is closed, being a closure. -/
public theorem isClosed_secantDirections (x : projectiveSpaceOfModule k V)
    (X : Set (projectiveSpaceOfModule k V)) : IsClosed (secantDirections k V x X) :=
  isClosed_closure

/-- **The secant cone of a subset at a point.** The cone with vertex `x` over the secant
directions of `X` at `x`: the lines joining `x` to the points of `X ∖ {x}`, together with their
limits and with `x` itself. -/
public def secantCone (x : projectiveSpaceOfModule k V)
    (X : Set (projectiveSpaceOfModule k V)) : Set (projectiveSpaceOfModule k V) :=
  (projectionDomain k V (pointSubmodule k V x)).ι.base ''
      ((projection k V (pointSubmodule k V x)).base ⁻¹' secantDirections k V x X) ∪ {x}

/-- The vertex lies on the secant cone. -/
public theorem mem_secantCone_self (x : projectiveSpaceOfModule k V)
    (X : Set (projectiveSpaceOfModule k V)) : x ∈ secantCone k V x X :=
  Set.mem_union_right _ rfl

/-- **A point on a line joining `x` to a point of `X` lies on the secant cone.** Two points of
the domain of the projection away from `x` with the same image lie on one line through `x`, so a
point whose image is that of a point of `X` lies on the secant cone. -/
public theorem mem_secantCone_of_projection_eq (x : projectiveSpaceOfModule k V)
    (X : Set (projectiveSpaceOfModule k V))
    (p y : (projectionDomain k V (pointSubmodule k V x)).toScheme)
    (hy : (y.val : projectiveSpaceOfModule k V) ∈ X)
    (h : projection k V (pointSubmodule k V x) p =
      projection k V (pointSubmodule k V x) y) :
    (p.val : projectiveSpaceOfModule k V) ∈ secantCone k V x X :=
  Set.mem_union_left _ ⟨p, subset_closure ⟨y, hy, h.symm⟩, rfl⟩

/-- The cone swept out by the projection away from `x` through `X` is contained in the secant
cone, which is its closure together with `x`. -/
public theorem projectionCone_subset_secantCone (x : projectiveSpaceOfModule k V)
    (X : Set (projectiveSpaceOfModule k V)) :
    projectionCone k V x X ⊆ secantCone k V x X :=
  (Set.image_mono (Set.preimage_mono subset_closure)).trans Set.subset_union_left

/-- **The secant cone is closed.** The secant directions form a closed subset of `𝐏(W_x)`, so
their preimage is closed in the complement of `x`, and adding the closed point `x` makes it
closed in `𝐏(V)`. -/
public theorem isClosed_secantCone [IsAlgClosed k] [Module.Finite k V]
    (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (X : Set (projectiveSpaceOfModule k V)) :
    IsClosed (secantCone k V x X) := by
  obtain ⟨C, hC, hCeq⟩ :=
    (projectionDomain k V (pointSubmodule k V x)).ι.isOpenEmbedding.isInducing.isClosed_iff.mp
      ((isClosed_secantDirections k V x X).preimage
        (projection k V (pointSubmodule k V x)).continuous)
  have hcone : secantCone k V x X = C ∪ {x} := by
    rw [secantCone, ← hCeq, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι,
      coe_mapDomain_pointSubmodule k V x hx]
    ext z
    by_cases hz : z = x <;> simp [hz]
  rw [hcone]
  exact hC.union hx

/-- **A closed subset lies on its own secant cone at a closed point.** Every point of `X` other
than `x` lies on the line joining it to `x`, and `x` is the vertex. -/
public theorem subset_secantCone [IsAlgClosed k] [Module.Finite k V]
    (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (X : Set (projectiveSpaceOfModule k V)) :
    X ⊆ secantCone k V x X := by
  intro y hy
  by_cases hyx : y = x
  · rw [hyx]
    exact mem_secantCone_self k V x X
  · have hmem : y ∈ Set.range (projectionDomain k V (pointSubmodule k V x)).ι.base := by
      rw [Scheme.Opens.range_ι, coe_mapDomain_pointSubmodule k V x hx]
      exact hyx
    obtain ⟨y', rfl⟩ := hmem
    exact mem_secantCone_of_projection_eq k V x X y' y' hy rfl

/-- **Secant directions of small dimension are not all directions.** If `V` has dimension
`m + 2`, so that `𝐏(W_x)` has dimension `m`, a set of secant directions of dimension less than
`m` is a proper subset of `𝐏(W_x)`. -/
public theorem secantDirections_ne_univ_of_topologicalKrullDim_lt [IsAlgClosed k]
    [FiniteDimensional k V] {m : ℕ} (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hV : Module.finrank k V = m + 2) (X : Set (projectiveSpaceOfModule k V))
    (hdim : topologicalKrullDim (secantDirections k V x X) < (m : WithBot ℕ∞)) :
    secantDirections k V x X ≠ Set.univ := by
  intro hcontra
  have huniv : topologicalKrullDim
      (Set.univ : Set (projectiveSpaceOfModule k ↥(pointSubmodule k V x))) =
        (m : WithBot ℕ∞) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph]
    refine topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq ?_
    have h := finrank_pointSubmodule_add_one k V x hx
    omega
  rw [hcontra, huniv] at hdim
  exact hdim.false

/-- **The secant directions have dimension at most that of `X`.** The part of `X` away from `x`
is closed in the domain of the projection away from `x`, and the closure of the image of a
closed subset of a Noetherian space under a morphism of schemes locally of finite type over the
ground field has dimension at most that of the subset. -/
public theorem topologicalKrullDim_secantDirections_le [IsAlgClosed k] [FiniteDimensional k V]
    (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hV : 2 ≤ Module.finrank k V) {X : Set (projectiveSpaceOfModule k V)}
    (hXc : IsClosed X) :
    topologicalKrullDim (secantDirections k V x X) ≤ topologicalKrullDim X := by
  have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have hWnt : Nontrivial ↥(pointSubmodule k V x) := by
    refine Module.nontrivial_of_finrank_pos (R := k) ?_
    have h := finrank_pointSubmodule_add_one k V x hx
    omega
  have hrange : Set.range (projectionDomain k V (pointSubmodule k V x)).ι.base =
      ({x} : Set (projectiveSpaceOfModule k V))ᶜ := by
    rw [Scheme.Opens.range_ι, coe_mapDomain_pointSubmodule k V x hx]
  rw [secantDirections]
  by_cases hne : (X ∩ ({x} : Set (projectiveSpaceOfModule k V))ᶜ).Nonempty
  · have hSc : IsClosed ((projectionDomain k V (pointSubmodule k V x)).ι.base ⁻¹' X) :=
      hXc.preimage (projectionDomain k V (pointSubmodule k V x)).ι.continuous
    have : IsLocallyNoetherian (projectiveSpaceOfModule k V) :=
      LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOfModuleToSpec k V)
    have : CompactSpace (projectiveSpaceOfModule k V) :=
      QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOfModuleToSpec k V)
    have : IsNoetherian (projectiveSpaceOfModule k V) := {}
    have : NoetherianSpace (projectionDomain k V (pointSubmodule k V x)).toScheme :=
      (projectionDomain k V (pointSubmodule k V x)).ι.isOpenEmbedding.isInducing.noetherianSpace
    have hmain := topologicalKrullDim_closure_image_le k
      (projection k V (pointSubmodule k V x))
      ((projectionDomain k V (pointSubmodule k V x)).ι ≫ projectiveSpaceOfModuleToSpec k V)
      (projectiveSpaceOfModuleToSpec k ↥(pointSubmodule k V x))
      (projection_comp_toSpec k V (pointSubmodule k V x)) hSc
    refine hmain.trans ?_
    refine Topology.IsInducing.topologicalKrullDim_le
      (f := fun z : ↥((projectionDomain k V (pointSubmodule k V x)).ι.base ⁻¹' X) =>
        (⟨(projectionDomain k V (pointSubmodule k V x)).ι.base z.1, z.2⟩ : ↥X)) ?_
    refine Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val ?_
    exact (projectionDomain k V (pointSubmodule k V x)).ι.isOpenEmbedding.isInducing.comp
      Topology.IsInducing.subtypeVal
  · have hempty : (projectionDomain k V (pointSubmodule k V x)).ι.base ⁻¹' X = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun z hz =>
        hne ⟨_, hz, hrange ▸ Set.mem_range_self z⟩
    rw [hempty, Set.image_empty, closure_empty,
      (topologicalKrullDim_eq_bot_iff_isEmpty
        (↥(∅ : Set (projectiveSpaceOfModule k ↥(pointSubmodule k V x))))).mpr inferInstance]
    exact bot_le

/-- **An irreducible closed subset of small dimension does not have all secant directions.**
With `dim V = m + 2`, so that `𝐏(V)` has dimension `m + 1` and `𝐏(W_x)` has dimension `m`, an
irreducible closed subset of dimension less than `m` leaves a direction at `x` unused. -/
public theorem secantDirections_ne_univ_of_isIrreducible [IsAlgClosed k] [FiniteDimensional k V]
    {m : ℕ} (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hV : Module.finrank k V = m + 2) {X : Set (projectiveSpaceOfModule k V)}
    (hXc : IsClosed X)
    (hdim : topologicalKrullDim X < (m : WithBot ℕ∞)) :
    secantDirections k V x X ≠ Set.univ :=
  secantDirections_ne_univ_of_topologicalKrullDim_lt k V x hx hV X
    (lt_of_le_of_lt
      (topologicalKrullDim_secantDirections_le k V x hx (by omega) hXc) hdim)

/-- **A centre off the secant cone separates `x` from the rest of `X`.** Let `p` be a closed
point outside the secant cone of `X` at a closed point `x`. A point of `X` lying, like `x`, in
the domain of the projection away from `p` and having the same image as `x` is `x`: otherwise it
would lie on a line joining `x` to a point of `X`, and that line passes through `p`. -/
public theorem eq_of_projection_eq_of_notMem_secantCone [IsAlgClosed k] [Module.Finite k V]
    (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (X : Set (projectiveSpaceOfModule k V)) {p : projectiveSpaceOfModule k V}
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hp : p ∉ secantCone k V x X)
    (y x' : (projectionDomain k V (pointSubmodule k V p)).toScheme)
    (hyX : (y.val : projectiveSpaceOfModule k V) ∈ X)
    (hx' : (x'.val : projectiveSpaceOfModule k V) = x)
    (h : projection k V (pointSubmodule k V p) y =
      projection k V (pointSubmodule k V p) x') :
    (y.val : projectiveSpaceOfModule k V) = x := by
  by_contra hyx
  have hpx : p ≠ x := fun h0 => hp (h0 ▸ mem_secantCone_self k V x X)
  have hline : (y.val : projectiveSpaceOfModule k V) ∈
      linearSubspace k V (pointSubmodule k V p ⊓ pointSubmodule k V x) := by
    have hmem := mem_linearSubspace_inf_of_projection_eq k V (pointSubmodule k V p) y x' h
    rwa [hx'] at hmem
  obtain ⟨f, hf, hfp⟩ := exists_eq_linearFunctionalPoint k V p hpc
  have hker : pointSubmodule k V p = LinearMap.ker f := by
    rw [hfp, pointSubmodule_linearFunctionalPoint]
  have hg : f ∘ₗ (pointSubmodule k V x).subtype ≠ 0 := by
    intro h0
    refine hpx ?_
    have hle : pointSubmodule k V x ≤ pointSubmodule k V p := by
      intro w hw
      rw [hker]
      exact LinearMap.mem_ker.mpr
        (congrArg (fun g : Module.Dual k ↥(pointSubmodule k V x) => g ⟨w, hw⟩) h0)
    have hmem := (mem_linearSubspace_iff k V (pointSubmodule k V x) p).mpr hle
    rwa [linearSubspace_pointSubmodule k V x hx, Set.mem_singleton_iff] at hmem
  have hdom : ((projectionDomain k V (pointSubmodule k V x) :
      (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) = {x}ᶜ :=
    coe_mapDomain_pointSubmodule k V x hx
  have hpd : p ∈ ((projectionDomain k V (pointSubmodule k V x) :
      (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
    rw [hdom]
    exact hpx
  have hyd : (y.val : projectiveSpaceOfModule k V) ∈
      ((projectionDomain k V (pointSubmodule k V x) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
    rw [hdom]
    exact hyx
  have h1 : projection k V (pointSubmodule k V x) ⟨(y.val : projectiveSpaceOfModule k V), hyd⟩ =
      linearFunctionalPoint k ↥(pointSubmodule k V x)
        (f ∘ₗ (pointSubmodule k V x).subtype) hg := by
    refine projection_eq_linearFunctionalPoint_of_mem k V (pointSubmodule k V x) _ _ hg
      (pointSubmodule k V p ⊓ pointSubmodule k V x) (fun w hw => ?_) hline
    refine Submodule.mem_inf.mpr ⟨?_, w.2⟩
    rw [hker]
    exact LinearMap.mem_ker.mpr hw
  have h2 : projection k V (pointSubmodule k V x) ⟨p, hpd⟩ =
      linearFunctionalPoint k ↥(pointSubmodule k V x)
        (f ∘ₗ (pointSubmodule k V x).subtype) hg :=
    projection_eq_linearFunctionalPoint k V (pointSubmodule k V x) ⟨p, hpd⟩ f hf hg hfp
  exact hp (mem_secantCone_of_projection_eq k V x X ⟨p, hpd⟩
    ⟨(y.val : projectiveSpaceOfModule k V), hyd⟩ hyX (h2.trans h1.symm))

/-- **A closed point off the secant cone.** If the secant directions of `X` at a closed point
`x` are not all of `𝐏(W_x)`, a nonzero functional on `W_x` cuts out a direction off them, and
any extension of it to `V` cuts out a closed point of `𝐏(V)` off the secant cone. -/
public theorem exists_isClosed_singleton_notMem_secantCone [IsAlgClosed k]
    [FiniteDimensional k V] (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hV : 2 ≤ Module.finrank k V) (X : Set (projectiveSpaceOfModule k V))
    (hX : secantDirections k V x X ≠ Set.univ) :
    ∃ p : projectiveSpaceOfModule k V,
      IsClosed ({p} : Set (projectiveSpaceOfModule k V)) ∧ p ∉ secantCone k V x X := by
  have hWnt : Nontrivial ↥(pointSubmodule k V x) := by
    refine Module.nontrivial_of_finrank_pos (R := k) ?_
    have h := finrank_pointSubmodule_add_one k V x hx
    omega
  obtain ⟨g, hg, hgS⟩ := exists_linearFunctionalPoint_notMem_of_ne_univ k
    ↥(pointSubmodule k V x) (isClosed_secantDirections k V x X) hX
  obtain ⟨f, hfg⟩ := LinearMap.dualMap_surjective_of_injective
    (pointSubmodule k V x).injective_subtype g
  have hcomp : f ∘ₗ (pointSubmodule k V x).subtype = g := by
    refine LinearMap.ext fun w => ?_
    rw [← hfg, LinearMap.dualMap_apply]
    rfl
  subst hcomp
  have hf : f ≠ 0 := fun h0 => hg (by rw [h0, LinearMap.zero_comp])
  have hqne : linearFunctionalPoint k V f hf ≠ x := by
    intro h0
    refine hg (LinearMap.ext fun w => ?_)
    have hps : pointSubmodule k V x = LinearMap.ker f := by
      rw [← h0, pointSubmodule_linearFunctionalPoint]
    have hw : (w : V) ∈ LinearMap.ker f := by
      rw [← hps]
      exact w.2
    simpa using LinearMap.mem_ker.mp hw
  have hqD : linearFunctionalPoint k V f hf ∈
      ((projectionDomain k V (pointSubmodule k V x) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
    rw [coe_mapDomain_pointSubmodule k V x hx]
    exact hqne
  refine ⟨linearFunctionalPoint k V f hf, linearFunctionalPoint_isClosed k V f hf, ?_⟩
  rintro (⟨z, hzS, hz⟩ | hzx)
  · refine hgS ?_
    have hzval : (z.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f hf := hz
    rwa [Set.mem_preimage,
      projection_eq_linearFunctionalPoint k V (pointSubmodule k V x) z f hf hg hzval] at hzS
  · exact hqne (Set.mem_singleton_iff.mp hzx)

/-- **A nonempty open of centres separating `x` from the rest of `X`.** If the secant directions
of a closed subset `X` at a closed point `x` are not all of `𝐏(W_x)`, the complement of the
secant cone is a nonempty open subset of `𝐏(V)`, every closed point `p` of which lies outside
`X` and is such that `x` is the only point of `X` with the same image as `x` under the
projection away from `p`. -/
public theorem exists_isOpen_nonempty_forall_eq_of_projection_eq [IsAlgClosed k]
    [FiniteDimensional k V] (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hV : 2 ≤ Module.finrank k V) (X : Set (projectiveSpaceOfModule k V))
    (hX : secantDirections k V x X ≠ Set.univ) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) → p ∉ X ∧
        ∀ y x' : (projectionDomain k V (pointSubmodule k V p)).toScheme,
          (y.val : projectiveSpaceOfModule k V) ∈ X →
          (x'.val : projectiveSpaceOfModule k V) = x →
          projection k V (pointSubmodule k V p) y =
            projection k V (pointSubmodule k V p) x' →
          (y.val : projectiveSpaceOfModule k V) = x := by
  obtain ⟨p₀, hp₀c, hp₀⟩ := exists_isClosed_singleton_notMem_secantCone k V x hx hV X hX
  refine ⟨(secantCone k V x X)ᶜ, (isClosed_secantCone k V x hx X).isOpen_compl, ⟨p₀, hp₀⟩,
    fun p hp hpc => ⟨fun hpX => hp (subset_secantCone k V x hx X hpX), fun y x' => ?_⟩⟩
  exact eq_of_projection_eq_of_notMem_secantCone k V x hx X hpc hp y x'

/-- **A nonempty open of centres separating `x` from the rest of an irreducible closed subset of
small dimension.** Let `V` have dimension `m + 2`, so that `𝐏(V)` has dimension `m + 1` and
`𝐏(W_x)` has dimension `m`, let `x` be a closed point and let `X` be an irreducible closed
subset of dimension less than `m`. Then the complement of the secant cone is a nonempty open
subset of `𝐏(V)`, every closed point `p` of which lies outside `X` and is such that `x` is the
only point of `X` with the same image as `x` under the projection away from `p`. -/
public theorem exists_isOpen_nonempty_forall_eq_of_isIrreducible [IsAlgClosed k]
    [FiniteDimensional k V] {m : ℕ} (x : projectiveSpaceOfModule k V)
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V)))
    (hV : Module.finrank k V = m + 2) {X : Set (projectiveSpaceOfModule k V)}
    (hXc : IsClosed X)
    (hdim : topologicalKrullDim X < (m : WithBot ℕ∞)) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) → p ∉ X ∧
        ∀ y x' : (projectionDomain k V (pointSubmodule k V p)).toScheme,
          (y.val : projectiveSpaceOfModule k V) ∈ X →
          (x'.val : projectiveSpaceOfModule k V) = x →
          projection k V (pointSubmodule k V p) y =
            projection k V (pointSubmodule k V p) x' →
          (y.val : projectiveSpaceOfModule k V) = x :=
  exists_isOpen_nonempty_forall_eq_of_projection_eq k V x hx (by omega) X
    (secantDirections_ne_univ_of_isIrreducible k V x hx hV hXc hdim)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
