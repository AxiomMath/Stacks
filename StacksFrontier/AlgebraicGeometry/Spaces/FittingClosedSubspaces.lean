module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingStratification

/-!
# The Fitting closed subspaces of an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `G` be
an `𝒪_X`-module whose Fitting ideal sheaves `AlgebraicGeometry.Space.fittingIdeal` are
quasi-coherent and whose sections over the affine étale charts are finite modules.  The
surjectivity half of Stacks 03MB then cuts a closed subspace `Z_r ⊆ X` out of each `Fit_r(G)`,
and the chain

`X ⊇ Z_0 ⊇ Z_1 ⊇ Z_2 ⊇ …`

of Stacks 0CZ9 is the chain of closed subspaces so obtained.  This file constructs that chain and
proves clause (1) of Stacks 0CZ9: the intersection of the `Z_r` is empty.

## Main results

* `AlgebraicGeometry.Scheme.isEmpty_of_one_eq_zero`: a scheme whose unit function vanishes is
  empty.
* `AlgebraicGeometry.Space.isEmpty_of_mem_obj_of_definingIdealAt_eq_top`: a point of `X` lying in
  a closed subspace `Z` and factoring through an affine étale chart on which the defining ideal of
  `Z` is the unit ideal is a point over an empty scheme.
* `AlgebraicGeometry.Space.notMem_range_pointsMap_ι_of_definingIdealAt_eq_top`: consequently the
  point set of `Z` misses the image of such a chart.
* `AlgebraicGeometry.Space.exists_affine_chart_span_eq_top_of_module_finite`: an affine étale
  chart through a prescribed point over which the sections of `G` are spanned by finitely many
  elements.
* `AlgebraicGeometry.Space.exists_fittingClosedSubspaces`: **the chain of closed subspaces cut
  out by the Fitting ideals of `G`**, decreasing, with prescribed defining ideal sheaves.
* `AlgebraicGeometry.Space.iInter_range_pointsMap_ι_fittingClosedSubspace_eq_empty`: the point
  sets of the Fitting closed subspaces have empty intersection.
* `AlgebraicGeometry.Space.isClosedSubspace_iInf`: the intersection of the chain is itself a
  closed subspace.
* `AlgebraicGeometry.Space.iInf_fittingClosedSubspace_eq_sheafify_bot`: **clause (1) of Stacks
  0CZ9** — that intersection is the empty algebraic space.

## Implementation notes

The bridge from the sheaf of ideals to the subspace is the chart-local membership criterion
`AlgebraicGeometry.Space.mem_obj_iff_definingIdealAt_le`: a point of `X` over a site object `a`
factoring through an affine étale chart `U` by `k : a ⟶ U` lies in `Z` exactly when the defining
ideal of `Z` at `U` is killed by pullback of functions along `k`.  When that ideal is the *unit*
ideal the criterion forces the unit function on `a` to vanish, so `a` is an empty scheme; a
field-valued point is never over an empty scheme, because the spectrum of a field has a closed
point.  That is the whole content of "`Fit_r(G)|_U = 𝒪_U` implies `Z_r` misses `U`", and it is
what turns the point-set statement
`AlgebraicGeometry.Space.iInter_idealZeroLocus_fittingIdeal_eq_empty` about the Fitting ideals
into a statement about the Fitting closed subspaces.

The chain is produced as an existential rather than as a definition: a closed subspace with
prescribed quasi-coherent defining ideal exists by
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite` and is unique by
`AlgebraicGeometry.Space.definingIdealSheaf_injective`, but the existence statement is not a
construction, and choosing from it is not one either.  Everything downstream is therefore stated
for an arbitrary family of closed subspaces whose defining ideal sheaves are the Fitting ideals,
which is exactly the hypothesis the existential supplies.

Quasi-coherence of `Fit_r(G)` is the assertion of the preamble of Stacks 0CZ3, refined by Stacks
0CZ5 for a finitely presented module; it is carried here as the hypothesis `hqc` of
`AlgebraicGeometry.Space.exists_fittingClosedSubspaces`.

The remaining input is `hfin`: that the sections of `G` over every affine étale chart form a
finite module over the chart ring.  That is the shape in which the neighbouring statements about
Fitting ideals take the finite type hypothesis on `G`, because
`SheafOfModules.IsFiniteTypeOnSite` supplies finitely many generators only on a covering of a
chart, and an epimorphism of sheaves of modules is only locally surjective on sections.  Granted
`hfin`, local generation near every point is
`AlgebraicGeometry.Space.exists_affine_chart_span_eq_top_of_module_finite`.

**Both inputs follow from the hypotheses of Stacks 0CZ9.**  `hfin` follows from
quasi-coherence and finite type by
`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`, and `hqc` then follows by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_fittingIdeal`.  The statements of this file with
both discharged — so with exactly the hypotheses Stacks 0CZ9 makes on its module — are
`AlgebraicGeometry.Space.exists_fittingClosedSubspaces_of_isFiniteTypeOnSite` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_fittingIdeal_of_isFiniteTypeOnSite`.

## References

* [Stacks Project, Tag 0CZ9](https://stacks.math.columbia.edu/tag/0CZ9)
* [Stacks Project, Tag 0CZ3](https://stacks.math.columbia.edu/tag/0CZ3)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- **A scheme on which the unit function vanishes is empty.**  The germ of the unit function at
a point is the unit of the stalk, which is a nonzero local ring. -/
theorem Scheme.isEmpty_of_one_eq_zero {V : Scheme.{u}} (h : (1 : Γ(V, ⊤)) = 0) : IsEmpty V := by
  refine ⟨fun v ↦ ?_⟩
  have hg := congrArg (V.presheaf.germ ⊤ v (by trivial)) h
  rw [map_one, map_zero] at hg
  exact one_ne_zero hg

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Charts on which the defining ideal of a closed subspace is the unit ideal -/

/-- **A closed subspace misses the affine étale charts on which its defining ideal is the unit
ideal.**  If the defining ideal of `Z` at an affine étale chart `U` is all of `𝒪_X(U)`, then a
point of `X` over a site object `a`, factoring through `U`, which lies in `Z` forces `a` to be an
empty scheme.

The chart-local membership criterion `AlgebraicGeometry.Space.mem_obj_iff_definingIdealAt_le`
turns membership in `Z` into the vanishing of the defining ideal after pullback along `k`; the
unit function is in that ideal, so it vanishes on `a`. -/
theorem isEmpty_of_mem_obj_of_definingIdealAt_eq_top
    (Z : ClosedSubspaces B S hS X.1) (U : SmallEtale B S hS X.1)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left))
    (hU : definingIdealAt B S hS X Z (op U) = ⊤)
    {a : BigFppfOver B S hS} (k : a ⟶ U.1.left)
    (hk : U.1.hom.app (op a) k ∈ Z.1.obj (op a)) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj a) := by
  have := hUaff
  rw [mem_obj_iff_definingIdealAt_le, hU] at hk
  have h1 : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom 1 = 0 :=
    RingHom.mem_ker.1 (hk Submodule.mem_top)
  rw [map_one] at h1
  exact Scheme.isEmpty_of_one_eq_zero h1

/-- **The point set of a closed subspace misses the image of an affine étale chart on which its
defining ideal is the unit ideal.**

A point in both would have a field-valued representative dominating a representative on each
side, and the spectrum of a field is not empty. -/
theorem notMem_range_pointsMap_ι_of_definingIdealAt_eq_top
    (Z : ClosedSubspaces B S hS X.1) (U : SmallEtale B S hS X.1)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left))
    (hU : definingIdealAt B S hS X Z (op U) = ⊤)
    {x : points B S hS X.1}
    (hx : x ∈ Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom)) :
    x ∉ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) := by
  rintro ⟨pz, hpz⟩
  obtain ⟨q, hq⟩ := hx
  obtain ⟨Q, rfl⟩ := Quot.exists_rep q
  obtain ⟨P, rfl⟩ := Quot.exists_rep pz
  rw [pointsMap_class] at hq hpz
  obtain ⟨R, ⟨α, hα⟩, ⟨β, hβ⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS X.1 _ _).1 (hq.trans hpz.symm)
  -- `R.value` lies in `Z`, being a restriction of the image of a point of `Z`.
  have hmemZ : R.value ∈ Z.1.obj (op R.siteObject) := hβ ▸ Z.1.map β.op P.value.2
  -- `R.value` factors through the chart `U`, along `α ≫ Q.value`.
  have hfac : R.value = U.1.hom.app (op R.siteObject) (α ≫ Q.value) := by
    rw [← hα]
    exact (congrArg (fun k ↦ k Q.value) (U.1.hom.naturality α.op)).symm
  rw [hfac] at hmemZ
  exact (isEmpty_of_mem_obj_of_definingIdealAt_eq_top B S hS X Z U hUaff hU _ hmemZ).elim
    (IsLocalRing.closedPoint R.carrier)

/-- **The point set of a closed subspace is contained in the zero locus of its defining ideal
sheaf**, provided the charts witnessing the unit locus may be taken affine.

This is `AlgebraicGeometry.Space.notMem_range_pointsMap_ι_of_definingIdealAt_eq_top` for a sheaf
of ideals `I` equal to the defining ideal sheaf of `Z`, the form in which the Fitting chain
supplies it. -/
theorem notMem_range_pointsMap_ι_of_definingIdealSheaf_obj_eq_top
    (Z : ClosedSubspaces B S hS X.1)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hZI : definingIdealSheaf B S hS X Z = I) (U : SmallEtale B S hS X.1)
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left))
    (hU : I.obj (op U) = ⊤)
    {x : points B S hS X.1}
    (hx : x ∈ Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom)) :
    x ∉ Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) :=
  notMem_range_pointsMap_ι_of_definingIdealAt_eq_top B S hS X Z U hUaff
    (by rw [← definingIdealSheaf_obj B S hS X Z (op U), hZI]; exact hU) hx

/-! ### Local generation from finiteness of the sections over the affine charts -/

/-- **An affine étale chart through a prescribed point over which the sections of `G` are spanned
by finitely many elements.**  This is the local generation of `G` in the form clause (1) of Stacks
0CZ9 consumes it.

An affine étale chart through the point is
`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`, and finiteness of the sections
over it produces the spanning family. -/
theorem exists_affine_chart_span_eq_top_of_module_finite
    (G : Modules.{u, u} B S hS X.1 X.2)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W)))
    (x : points B S hS X.1) :
    ∃ (r : ℕ) (U : SmallEtale B S hS X.1) (s : Fin r → G.val.obj (op U)),
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U) ∧
        Submodule.span (chartRing B S hS X.1 X.2 U) (Set.range s) = ⊤ ∧
        x ∈ Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom) := by
  obtain ⟨W, b, hWaff, hbe, w, hw⟩ := exists_affine_etale_chart_at_point B S hS X.1 X.2 x
  let U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b, hbe⟩
  have := hfin U hWaff
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := chartRing B S hS X.1 X.2 U)
    (M := G.val.obj (op U))
  exact ⟨r, U, s, hWaff, hs, w, hw⟩

/-! ### The chain of Fitting closed subspaces -/

/-- **The closed subspaces cut out by the Fitting ideals of an `𝒪_X`-module.**  If every Fitting
ideal sheaf of `G` is quasi-coherent, there is a decreasing chain of closed subspaces of `X` whose
defining ideal sheaves are the Fitting ideals of `G`.  This is the chain
`X ⊇ Z_0 ⊇ Z_1 ⊇ …` of Stacks 0CZ9.

Each subspace comes from the surjectivity half of Stacks 03MB,
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite`, and the chain
decreases because the Fitting ideals increase and the correspondence of Stacks 03MB reverses
inclusions. -/
@[stacks 0CZ9 "the decreasing chain of closed subspaces cut out by the Fitting ideals"]
theorem exists_fittingClosedSubspaces (G : Modules.{u, u} B S hS X.1 X.2)
    (hqc : ∀ r : ℕ,
      (fittingIdeal B S hS X.1 X.2 G r).toSheafOfModules.IsQuasicoherentOnSite) :
    ∃ Z : ℕ → ClosedSubspaces B S hS X.1,
      (∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r) ∧
        Antitone fun r ↦ (Z r).1 := by
  choose Z hZ using fun r : ℕ ↦ exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X
    (fittingIdeal B S hS X.1 X.2 G r) (hqc r)
  refine ⟨Z, hZ, fun r s hrs ↦ ?_⟩
  refine le_of_definingIdealSheaf_le B S hS X (Z s) (Z r) ?_
  rw [hZ r, hZ s]
  exact fittingIdeal_mono G hrs

/-- **Clause (1) of Stacks 0CZ9: the Fitting closed subspaces have empty intersection.**  For a
chain of closed subspaces whose defining ideal sheaves are the Fitting ideals of `G`, the point
sets of the subspaces have empty intersection, as soon as the sections of `G` over every affine
étale chart form a finite module.

Near every point the Fitting ideal sheaf is the whole structure sheaf from some index on
(`AlgebraicGeometry.Space.fittingIdeal_obj_eq_top_of_span_eq_top`), and a closed subspace misses
the image of a chart on which its defining ideal is the unit ideal. -/
theorem iInter_range_pointsMap_ι_fittingClosedSubspace_eq_empty
    (G : Modules.{u, u} B S hS X.1 X.2) (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W))) :
    (⋂ r : ℕ, Set.range (pointsMap B S hS (Z r).1.toFunctor (Z r).1.ι)) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
  obtain ⟨r, U, s, hU, hs, hxU⟩ :=
    exists_affine_chart_span_eq_top_of_module_finite B S hS X G hfin x
  exact notMem_range_pointsMap_ι_of_definingIdealSheaf_obj_eq_top B S hS X (Z r) _ (hZ r) U hU
    (fittingIdeal_obj_eq_top_of_span_eq_top G U hU s hs) hxU (Set.mem_iInter.1 hx r)

/-- The intersection of a chain of closed subspaces of an algebraic space is a closed
subspace. -/
theorem isClosedSubspace_iInf (Z : ℕ → ClosedSubspaces B S hS X.1) :
    IsClosedSubspace B S hS (⨅ r : ℕ, (Z r).1) := by
  rw [iInf]
  exact isClosedSubspace_sInf B S hS X.2 _ (by rintro W ⟨r, rfl⟩; exact (Z r).2)

/-- The point set of the intersection of a family of closed subspaces is empty as soon as the
intersection of their point sets is. -/
theorem range_pointsMap_ι_iInf_eq_empty_of_iInter_eq_empty
    (Z : ℕ → ClosedSubspaces B S hS X.1)
    (h : (⋂ r : ℕ, Set.range (pointsMap B S hS (Z r).1.toFunctor (Z r).1.ι)) = ∅) :
    Set.range (pointsMap B S hS (⨅ r : ℕ, (Z r).1).toFunctor (⨅ r : ℕ, (Z r).1).ι) = ∅ := by
  rw [← Set.subset_empty_iff, ← h]
  exact Set.subset_iInter fun r ↦ range_pointsMap_ι_le B S hS (iInf_le _ r)

/-- **Clause (1) of Stacks 0CZ9: the intersection of the Fitting closed subspaces is the empty
algebraic space.**  For a chain of closed subspaces of `X` whose defining ideal sheaves are the
Fitting ideals of `G`, the intersection of the chain is the sheafification of the bottom
subfunctor, as soon as the sections of `G` over every affine étale chart form a finite module.

The intersection has no points, by
`AlgebraicGeometry.Space.iInter_range_pointsMap_ι_fittingClosedSubspace_eq_empty`, and an
inclusion into the empty open subspace is detected on points by Stacks 03BZ; the reverse inclusion
holds for any family of subsheaves. -/
@[stacks 0CZ9 "(1) the intersection is empty; (2), (3) and finite presentation not covered"]
theorem iInf_fittingClosedSubspace_eq_sheafify_bot
    (G : Modules.{u, u} B S hS X.1 X.2) (Z : ℕ → ClosedSubspaces B S hS X.1)
    (hZ : ∀ r, definingIdealSheaf B S hS X (Z r) = fittingIdeal B S hS X.1 X.2 G r)
    (hfin : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Module.Finite (chartRing B S hS X.1 X.2 W) (G.val.obj (op W))) :
    (⨅ r : ℕ, (Z r).1) = (⊥ : Subfunctor X.1).sheafify (BigFppfOver.topology B S hS) := by
  refine le_antisymm ?_ (le_iInf fun r ↦ Subfunctor.sheafify_le (⊥ : Subfunctor X.1) (Z r).1
    bot_le ((isSheaf_iff_isSheaf_of_type _ _).1 X.2.isSheaf)
    ((isSheaf_iff_isSheaf_of_type _ _).1 (Z r).2.1.isSheaf))
  refine le_of_range_pointsMap_ι_subset B S hS (isOpenSubspace_sheafify_bot B S hS X.1 X.2) ?_
  rw [range_pointsMap_ι_iInf_eq_empty_of_iInter_eq_empty B S hS X Z
    (iInter_range_pointsMap_ι_fittingClosedSubspace_eq_empty B S hS X G Z hZ hfin)]
  exact Set.empty_subset _

end Space

end AlgebraicGeometry

end
