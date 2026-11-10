module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusReducible
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.EndProjectionFinite
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GeneralLineProperIntersectionOfCodimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GenericProjectionIntersectionBound
public import StacksFrontier.Topology.Dimension.UnionDimension

/-!
# A singular class at which both clauses of Tag 0B1S hold

Let `X, Y` be closed subvarieties of `𝐏(V)` which intersect properly, with `X ≠ 𝐏(V)`, and let
`𝐏 = 𝐏((End V)ᵛ)` be the parameter space of the projective transformations of `𝐏(V)`. This file
produces a **singular** nonzero endomorphism `g` of `V` with `X ⊆ U(g)` for which `r_g(X)` meets
`Y` properly: a closed point of the determinant hypersurface `Z = 𝐏 ∖ PGL(V)` at which neither
clause of Tag 0B1S fails. Consequently a closed subset of `Z` whose closed points are all bad is
a *proper* closed subset of the irreducible `Z`, and therefore has codimension at least two at
each of its points — which is what the reducible form of Tag 0B2T consumes.

This is the step the source of Tag 0B1S carries out with *"Some details omitted"*, and the
argument here is not the source's. The source fixes the hyperplane `H = 𝐏(Im g)` and moves
`r_g(X)` inside `H` by postcomposing `g` with automorphisms of `H`, so that the dimension count
has to be redone inside `H` for the pair `r_g(X)`, `H ∩ Y`. Instead the `g` is taken to be the
*retraction* `AlgebraicGeometry.ProjectiveSpaceOfModule.hyperplaneProjection` of `𝐏(V)` onto a
hyperplane `H` away from a closed point `p ∉ X` — the endomorphism clause (1) of the tag is
already proved with, in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusCodimension` — and `p` is chosen
*general*, in the sense of Tag 0B1R. Then

* `r_g` fixes `H` pointwise and is the projection away from `p`, so `r_g(X) ∩ Y` is contained in
  `(Y ∩ H) ∩ r_p^{-1}(r_p(X))`, and
* Tag 0B1R, applied to the pair `Y ∩ H` and `X`, writes that set as
  `((Y ∩ H) ∩ X) ∪ E` with `dim E + dim 𝐏(V) ≤ dim (Y ∩ H) + dim X + 1`.

The first piece lies in `X ∩ Y`, which has the expected dimension by hypothesis; the second has
`dim E + dim 𝐏(V) ≤ dim X + dim Y` because `H ∩ Y` has dimension one less than `Y`. So no moving
argument inside `H` is needed, and the general-position input is the one Tag 0B1R already
supplies. Of the source's three omitted ingredients, the finiteness of `r_g|_X` is
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.EndProjectionFinite` and the dimension
drop of `H ∩ Y` is proved below; the moving argument is replaced.

## Main results

* `topologicalKrullDim_inter_add_one_le_of_not_subset`: **the dimension drop.** A closed subset
  not containing an irreducible closed subset meets it in dimension at least one less.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.union_ne_univ_of_ne_univ`: two proper closed subsets
  do not cover an irreducible space.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_smul`: the two clauses of Tag
  0B1S depend only on the class `[g]`, for *all* points of `𝐏(V)` and not only the closed ones.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjectionImage_subset_projectionCone`: the
  image of a subset under the retraction onto a hyperplane lies in the cone swept out by the
  projection away from the omitted point. That the image lies in the hyperplane itself needs
  nothing new: it is `endProjectionImage_subset_linearSubspace` of
  `StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusReducible` applied to the line
  of `w`, which the retraction kills.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_det_eq_zero_isGoodEndomorphism`: **the
  singular good class.**
* `exists_mem_determinantHypersurface_notMem_badParameterLocus`, of the same namespace: the bad
  locus does not contain the whole of `Z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.two_le_codimension_of_isClosed_subset_bad`: a
  closed subset of `Z` whose closed points are bad has codimension at least two at each of its
  points.
* `exists_isOpen_closedPoint_line_isGood_of_clauseTwo_split`, of the same namespace: Tag 0B1S
  with clause (1) and the codimension of the clause-(2) locus *inside `Z`* discharged, that
  locus being split along the determinant.

## Implementation notes

**Scalar invariance.** `AlgebraicGeometry.ProjectiveSpaceOfModule.badParameterLocus` collects
the classes having *some* bad representative, so ruling a class out of it means ruling out every
representative, that is every unit multiple of `g`. The library had that only on closed points,
as `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_smul_apply`; the global form is
proved here, by the observation that `Sym (c • g)` is `c ^ d` times `Sym g` in degree `d`, so the
two induce the same map on homogeneous primes.

**The general point.** The open subset of centres that Tag 0B1R produces is intersected with the
complements of `X` and of `H`, and a closed point is taken in the result: three proper closed
subsets do not cover the irreducible `𝐏(V)`, and a proper closed subset of `𝐏(V)` misses a
closed point. The centre has to miss `X` for clause (1) and to miss `H` for the retraction onto
`H` away from it to exist at all.

**What this does not do.** It does not show that the bad locus inside `Z` is *closed*; that is
the one thing the source asserts without proof ("Moreover, `B` is closed") and it needs the
incidence correspondence over `Z`, which the library does not have. So Tag 0B1S is not
registered here: what is discharged is the codimension bound for a closed subset of `Z`, given
that such a closed subset is available.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

/-- **The dimension drop of a hyperplane section.** A closed subset `C` of a Noetherian space
which does not contain an irreducible closed subset `Y` meets it in a nowhere dense closed
subset of `Y`, hence in dimension at least one less. This is the second of the ingredients the
source of Tag 0B1S leaves to "Some details omitted", in the form it is used in: for `C` a
hyperplane of `𝐏(V)` not containing `Y`. -/
public theorem topologicalKrullDim_inter_add_one_le_of_not_subset {T : Type*}
    [TopologicalSpace T] [NoetherianSpace T] {Y C : Set T} (hY : IsIrreducible Y)
    (hC : IsClosed C) (hYC : ¬ Y ⊆ C) :
    topologicalKrullDim ↥(Y ∩ C) + 1 ≤ topologicalKrullDim ↥Y := by
  have : IrreducibleSpace ↥Y := Subtype.irreducibleSpace hY
  set A : Set ↥Y := (Subtype.val : ↥Y → T) ⁻¹' (Y ∩ C) with hA
  have hApre : A = (Subtype.val : ↥Y → T) ⁻¹' C := by
    rw [hA]
    ext x
    simp
  have hAclosed : IsClosed A := by
    rw [hApre]
    exact hC.preimage continuous_subtype_val
  have hAcompl : (Aᶜ : Set ↥Y).Nonempty := by
    obtain ⟨y, hyY, hyC⟩ := Set.not_subset.mp hYC
    exact ⟨⟨y, hyY⟩, by simp [hApre, hyC]⟩
  have hAnd : IsNowhereDense A := by
    rw [IsNowhereDense, hAclosed.closure_eq]
    by_contra hne
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨b, hb⟩ := hAcompl
    obtain ⟨c, -, hc⟩ := (IrreducibleSpace.isIrreducible_univ ↥Y).isPreirreducible
      (interior A) Aᶜ isOpen_interior hAclosed.isOpen_compl ⟨a, Set.mem_univ a, ha⟩
      ⟨b, Set.mem_univ b, hb⟩
    exact hc.2 (interior_subset hc.1)
  have h := hAnd.topologicalKrullDim_add_one_le hAclosed
  rwa [hA, topologicalKrullDim_preimage_val Y (Y ∩ C) Set.inter_subset_left] at h

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The two clauses depend only on the class of `g` -/

/-- `Sym (c • g)` is the lift of `c • (ι ∘ g)`: both are determined by their values on the
degree-one generators. -/
private theorem symAlgMap_smul_eq_lift (c : k) (g : V →ₗ[k] V) :
    SymPow.symAlgMap (c • g) =
      SymmetricAlgebra.lift (c • ((SymmetricAlgebra.ι k V).comp g)) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun v => ?_)
  change SymPow.symAlgMap (c • g) (SymmetricAlgebra.ι k V v) =
    SymmetricAlgebra.lift (c • ((SymmetricAlgebra.ι k V).comp g)) (SymmetricAlgebra.ι k V v)
  rw [SymPow.symAlgMap_ι, SymmetricAlgebra.lift_ι_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, map_smul]

/-- **`Sym (c • g)` is `c ^ d` times `Sym g` in degree `d`.** -/
public theorem symAlgMap_smul_of_mem_symmetricPower (c : k) (g : V →ₗ[k] V) {d : ℕ}
    {x : SymmetricAlgebra k V} (hx : x ∈ SymPow.symmetricPower d k V) :
    SymPow.symAlgMap (c • g) x = c ^ d • SymPow.symAlgMap g x := by
  rw [symAlgMap_smul_eq_lift, SymmetricAlgebra.lift_smul_of_mem_symmetricPower c _ hx]
  rfl

/-- **`r_g` depends only on the class of `g`**, at every point of `𝐏(V)` and not only at the
closed ones: a unit multiple of `g` multiplies `Sym g` by a unit in each degree, so the two
morphisms have the same homogeneous prime at every point of the common domain of definition.

The closed-point form is
`AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_smul_apply`. -/
public theorem endProjection_smul_eq (c : kˣ) (g : V →ₗ[k] V)
    (y : (endDomain k V ((c : k) • g)).toScheme) (y' : (endDomain k V g).toScheme)
    (hy : (y.val : projectiveSpaceOfModule k V) = (y'.val : projectiveSpaceOfModule k V)) :
    endProjection k V ((c : k) • g) y = endProjection k V g y' := by
  refine eq_of_forall_homogeneous_mem_iff k V fun d hd x hx => ?_
  rw [mem_endProjection_iff k V _ y hd hx, mem_endProjection_iff k V g y' hd hx, hy,
    symAlgMap_smul_of_mem_symmetricPower k V (c : k) g hx]
  constructor
  · intro h
    have h' := Ideal.mul_mem_left
      (y'.val : projectiveSpaceOfModule k V).asHomogeneousIdeal.toIdeal
      (algebraMap k (SymmetricAlgebra k V) (((c : k) ^ d)⁻¹)) h
    rwa [Algebra.smul_def, ← _root_.mul_assoc, ← _root_.map_mul,
      inv_mul_cancel₀ (pow_ne_zero d c.ne_zero), _root_.map_one, one_mul] at h'
  · intro h
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ h

/-- **Membership in the image `r_g(S)`**, with the points of the open `U(g)` named by a point of
`𝐏(V)` together with a proof that it lies in `U(g)`. -/
public theorem mem_endProjectionImage_iff (g : V →ₗ[k] V)
    (S : Set (projectiveSpaceOfModule k V)) (z : projectiveSpaceOfModule k V) :
    z ∈ endProjectionImage k V g S ↔
      ∃ (x : projectiveSpaceOfModule k V) (hx : x ∈ endDomain k V g), x ∈ S ∧
        endProjection k V g ⟨x, hx⟩ = z := by
  constructor
  · rintro ⟨y, hyS, rfl⟩
    exact ⟨y.val, y.2, hyS, rfl⟩
  · rintro ⟨x, hx, hxS, rfl⟩
    exact ⟨⟨x, hx⟩, hxS, rfl⟩

/-- **The image `r_g(S)` depends only on the class of `g`.** -/
public theorem endProjectionImage_smul (c : kˣ) (g : V →ₗ[k] V)
    (S : Set (projectiveSpaceOfModule k V)) :
    endProjectionImage k V ((c : k) • g) S = endProjectionImage k V g S := by
  have hdom : endDomain k V ((c : k) • g) = endDomain k V g := endDomain_smul k V c g
  ext z
  rw [mem_endProjectionImage_iff, mem_endProjectionImage_iff]
  constructor
  · rintro ⟨x, hx, hxS, rfl⟩
    have hx' : x ∈ endDomain k V g := by rw [← hdom]; exact hx
    exact ⟨x, hx', hxS, (endProjection_smul_eq k V c g ⟨x, hx⟩ ⟨x, hx'⟩ rfl).symm⟩
  · rintro ⟨x, hx, hxS, rfl⟩
    have hx' : x ∈ endDomain k V ((c : k) • g) := by rw [hdom]; exact hx
    exact ⟨x, hx', hxS, endProjection_smul_eq k V c g ⟨x, hx'⟩ ⟨x, hx⟩ rfl⟩

/-- **The two clauses of Tag 0B1S depend only on the class of `g`.** -/
public theorem isGoodEndomorphism_smul (c : kˣ) (g : V →ₗ[k] V)
    (X Y : Set (projectiveSpaceOfModule k V)) :
    IsGoodEndomorphism k V X Y ((c : k) • g) ↔ IsGoodEndomorphism k V X Y g := by
  unfold IsGoodEndomorphism
  rw [endDomain_smul k V c g, endProjectionImage_smul k V c g]

/-! ### The retraction onto a hyperplane -/

/-- The point cut out by `f` lies on the hyperplane `𝐏(span {w})` exactly when `f w = 0`. -/
private theorem linearFunctionalPoint_mem_linearSubspace_span_iff {f : Module.Dual k V}
    (hf : f ≠ 0) (w : V) :
    linearFunctionalPoint k V f hf ∈ linearSubspace k V (Submodule.span k {w}) ↔ f w = 0 := by
  rw [mem_linearSubspace_iff, pointSubmodule_linearFunctionalPoint,
    Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]

variable [IsAlgClosed k] [FiniteDimensional k V]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- **The domain of definition of the retraction** onto the hyperplane `ker f` away from the
point cut out by `f` is the complement of that point. -/
public theorem coe_endDomain_hyperplaneProjection {f : Module.Dual k V} (hf : f ≠ 0) {w : V}
    (hw : f w ≠ 0) :
    ((endDomain k V (hyperplaneProjection k V f w) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) =
      {linearFunctionalPoint k V f hf}ᶜ := by
  rw [coe_endDomain, range_hyperplaneProjection k V hw, linearSubspace_ker]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- **The retraction kills `w`**, which is what puts its image inside the hyperplane cut out by
the line of `w`. -/
public theorem hyperplaneProjection_self_eq_zero (f : Module.Dual k V) {w : V} (hw : f w ≠ 0) :
    hyperplaneProjection k V f w w = 0 := by
  refine LinearMap.mem_ker.mp ?_
  rw [ker_hyperplaneProjection k V hw]
  exact Submodule.mem_span_singleton_self w

/-- **The retraction is the projection away from its omitted point**, as far as the cone it
sweeps out is concerned: the image of a subset `S` missing that point lies in
`r_p^{-1}(r_p(S))`.

The two morphisms agree after composing with the projection because the retraction is the
identity on the hyperplane `ker f`, so `Sym` of the retraction composed with `Sym` of the
inclusion of the hyperplane is `Sym` of that inclusion. -/
public theorem endProjectionImage_subset_projectionCone {f : Module.Dual k V} (hf : f ≠ 0)
    {w : V} (hw : f w ≠ 0) {S : Set (projectiveSpaceOfModule k V)}
    (hpS : linearFunctionalPoint k V f hf ∉ S) :
    endProjectionImage k V (hyperplaneProjection k V f w) S ⊆
      projectionCone k V (linearFunctionalPoint k V f hf) S := by
  set p := linearFunctionalPoint k V f hf with hp
  set W := pointSubmodule k V p with hW
  set g := hyperplaneProjection k V f w with hg
  have hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)) :=
    linearFunctionalPoint_isClosed k V f hf
  have hWker : W = LinearMap.ker f := by rw [hW, hp, pointSubmodule_linearFunctionalPoint]
  have hgW : g ∘ₗ W.subtype = W.subtype := by
    refine LinearMap.ext fun u => ?_
    have hu : f (u : V) = 0 := by
      refine LinearMap.mem_ker.mp ?_
      rw [← hWker]
      exact u.2
    exact hyperplaneProjection_apply_of_apply_eq_zero k V f w hu
  have hpH : p ∉ linearSubspace k V (Submodule.span k {w}) := by
    rw [hp]
    exact fun h => hw ((linearFunctionalPoint_mem_linearSubspace_span_iff k V hf w).mp h)
  have hdomp : ((projectionDomain k V W) : Set (projectiveSpaceOfModule k V)) = {p}ᶜ := by
    rw [hW]
    exact coe_mapDomain_pointSubmodule k V p hpc
  intro z hz
  rw [mem_endProjectionImage_iff] at hz
  obtain ⟨x, hx, hxS, rfl⟩ := hz
  -- the image point and the source point both lie in the domain of the projection away from `p`
  have hzH : endProjection k V g ⟨x, hx⟩ ∈ linearSubspace k V (Submodule.span k {w}) := by
    rw [← ker_hyperplaneProjection k V hw]
    exact range_endProjection_subset k V g ⟨⟨x, hx⟩, rfl⟩
  have hzdom : endProjection k V g ⟨x, hx⟩ ∈ projectionDomain k V W := by
    rw [← SetLike.mem_coe, hdomp]
    exact fun hzp => hpH (hzp ▸ hzH)
  have hxdom : x ∈ projectionDomain k V W := by
    rw [← SetLike.mem_coe, hdomp]
    exact fun hxp => hpS (hxp ▸ hxS)
  refine ⟨⟨_, hzdom⟩, ⟨⟨x, hxdom⟩, hxS, ?_⟩, rfl⟩
  -- the two have the same image under the projection away from `p`
  refine eq_of_forall_homogeneous_mem_iff k ↥W fun d hd u hu => ?_
  have husym : SymPow.symAlgMap W.subtype u ∈ SymPow.symmetricPower d k V :=
    SymPow.symAlgMap_mapsTo d W.subtype u hu
  rw [mem_projection_iff k V W ⟨x, hxdom⟩ hd hu,
    mem_projection_iff k V W ⟨endProjection k V g ⟨x, hx⟩, hzdom⟩ hd hu,
    show ((⟨endProjection k V g ⟨x, hx⟩, hzdom⟩ :
        (projectionDomain k V W).toScheme).val : projectiveSpaceOfModule k V) =
      endProjection k V g ⟨x, hx⟩ from rfl,
    mem_endProjection_iff k V g ⟨x, hx⟩ hd husym, ← SymPow.symAlgMap_comp_apply, hgW]

/-! ### The singular class at which both clauses hold -/

/-- Two proper closed subsets do not cover an irreducible space: their complements would be
disjoint nonempty opens. -/
public theorem union_ne_univ_of_ne_univ {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    {A B : Set T} (hA : IsClosed A) (hB : IsClosed B) (hAne : A ≠ Set.univ)
    (hBne : B ≠ Set.univ) : A ∪ B ≠ Set.univ := by
  intro hcov
  obtain ⟨a, ha⟩ := Set.nonempty_compl.mpr hAne
  obtain ⟨b, hb⟩ := Set.nonempty_compl.mpr hBne
  obtain ⟨c, -, hc⟩ := (IrreducibleSpace.isIrreducible_univ T).isPreirreducible Aᶜ Bᶜ
    hA.isOpen_compl hB.isOpen_compl ⟨a, Set.mem_univ a, ha⟩ ⟨b, Set.mem_univ b, hb⟩
  rcases Set.eq_univ_iff_forall.mp hcov c with h | h
  · exact hc.1 h
  · exact hc.2 h

/-- **The analysis of the determinant hypersurface in the proof of Tag 0B1S.** For `X, Y` closed
subvarieties of `𝐏(V)` which intersect properly with `X ≠ 𝐏(V)` there is a **singular** nonzero
endomorphism `g` of `V` with `X ⊆ U(g)` for which `r_g(X)` meets `Y` properly: the bad locus of
Tag 0B1S does not contain the whole of `Z = 𝐏 ∖ PGL(V)`.

`g` is the retraction of `𝐏(V)` onto the hyperplane cut out by the line of a vector `w` away
from a closed point `p = [f₀]`, where `w` is chosen so that `Y` is not contained in that
hyperplane — then `Y ∩ H` has dimension one less than `Y` — and where `p` is chosen off `X`,
off that hyperplane, and in the nonempty open subset of centres that Tag 0B1R produces for the
pair `Y ∩ H`, `X`. Then `r_g(X) ∩ Y` lies in `(Y ∩ H) ∩ r_p^{-1}(r_p(X))`, which Tag 0B1R writes
as `((Y ∩ H) ∩ X) ∪ E`: the first piece lies in `X ∩ Y`, of the expected dimension by
hypothesis, and the second has `dim E + dim 𝐏(V) ≤ dim (Y ∩ H) + dim X + 1 ≤ dim X + dim Y`.
Finally `dim r_g(X) = dim X` because `r_g` is finite on `X`.

The source's hypothesis `X ∩ Y ≠ ∅` is not needed: when `X ∩ Y` is empty the proper-intersection
hypothesis is vacuous and the argument goes through unchanged. -/
public theorem exists_det_eq_zero_isGoodEndomorphism [Nontrivial V]
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ) :
    ∃ g : V →ₗ[k] V, g ≠ 0 ∧ LinearMap.det g = 0 ∧
      IsGoodEndomorphism k V (X : Set (projectiveSpaceOfModule k V))
        (Y : Set (projectiveSpaceOfModule k V)) g := by
  have hXc : IsClosed (X : Set (projectiveSpaceOfModule k V)) := X.isClosed'
  have hYc : IsClosed (Y : Set (projectiveSpaceOfModule k V)) := Y.isClosed'
  have hXirr : IsIrreducible (X : Set (projectiveSpaceOfModule k V)) := X.isIrreducible'
  have hYirr : IsIrreducible (Y : Set (projectiveSpaceOfModule k V)) := Y.isIrreducible'
  have h2 : 2 ≤ Module.finrank k V :=
    two_le_finrank_of_isClosed_ne_univ k V hXc hXne hXirr.nonempty
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 := ⟨Module.finrank k V - 1, by omega⟩
  have hirrP : IrreducibleSpace (projectiveSpaceOfModule k V) :=
    irreducibleSpace_projectiveSpaceOfModule_of_finrank_eq k V hn
  -- a hyperplane missing a closed point of `Y`
  obtain ⟨f₁, hf₁, hf₁Y⟩ := exists_linearFunctionalPoint_mem_of_isClosed k V
    hYirr.nonempty hYc
  obtain ⟨w, hw₁⟩ : ∃ w : V, f₁ w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf₁ (LinearMap.ext fun v => hc v)
  set H := linearSubspace k V (Submodule.span k {w}) with hH
  have hHc : IsClosed H := isClosed_linearSubspace k V _
  have hf₁H : linearFunctionalPoint k V f₁ hf₁ ∉ H := by
    exact fun h => hw₁ ((linearFunctionalPoint_mem_linearSubspace_span_iff k V hf₁ w).mp h)
  have hYH : ¬ (Y : Set (projectiveSpaceOfModule k V)) ⊆ H := fun hsub => hf₁H (hsub hf₁Y)
  have hHne : H ≠ Set.univ := fun h => hf₁H (h ▸ Set.mem_univ _)
  have hdrop := topologicalKrullDim_inter_add_one_le_of_not_subset hYirr hHc hYH
  -- the general centre of Tag 0B1R for the pair `Y ∩ H`, `X`
  have hunion : ((Y : Set (projectiveSpaceOfModule k V)) ∩ H) ∪
      (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ :=
    union_ne_univ_of_ne_univ (hYc.inter hHc) hXc
      (fun h => hHne (Set.Subset.antisymm (Set.subset_univ _)
        (by rw [← h]; exact Set.inter_subset_right))) hXne
  obtain ⟨U, hUopen, hUne, hU⟩ := exists_isOpen_inter_projectionCone_eq_of_isClosed k V hn
    (hYc.inter hHc) hXc hunion
  obtain ⟨f₀, hf₀, hf₀mem⟩ : ∃ (f : Module.Dual k V) (hf : f ≠ 0),
      linearFunctionalPoint k V f hf ∉ (Uᶜ ∪ (X : Set (projectiveSpaceOfModule k V))) ∪ H := by
    refine exists_linearFunctionalPoint_notMem_of_ne_univ k V
      ((hUopen.isClosed_compl.union hXc).union hHc) ?_
    refine union_ne_univ_of_ne_univ (hUopen.isClosed_compl.union hXc) hHc ?_ hHne
    exact union_ne_univ_of_ne_univ hUopen.isClosed_compl hXc
      (fun h => (Set.nonempty_iff_ne_empty.mp hUne) (Set.compl_univ_iff.mp h)) hXne
  have hf₀U : linearFunctionalPoint k V f₀ hf₀ ∈ U := by
    by_contra h
    exact hf₀mem (Or.inl (Or.inl h))
  have hf₀X : linearFunctionalPoint k V f₀ hf₀ ∉ (X : Set (projectiveSpaceOfModule k V)) :=
    fun h => hf₀mem (Or.inl (Or.inr h))
  have hf₀H : linearFunctionalPoint k V f₀ hf₀ ∉ H := fun h => hf₀mem (Or.inr h)
  have hf₀w : f₀ w ≠ 0 := fun h0 =>
    hf₀H ((linearFunctionalPoint_mem_linearSubspace_span_iff k V hf₀ w).mpr h0)
  -- the retraction onto that hyperplane away from that point
  have hker₀ : LinearMap.ker f₀ ≠ ⊥ := by
    intro hbot
    have := finrank_ker_add_one k V hf₀
    rw [hbot, finrank_bot] at this
    omega
  have hgne : hyperplaneProjection k V f₀ w ≠ 0 := hyperplaneProjection_ne_zero k V hker₀ w
  have hgdet : LinearMap.det (hyperplaneProjection k V f₀ w) = 0 :=
    det_eq_zero_of_comp_eq_zero k V hf₀ (comp_hyperplaneProjection_eq_zero k V hf₀w)
  have hdom : (X : Set (projectiveSpaceOfModule k V)) ⊆
      ((endDomain k V (hyperplaneProjection k V f₀ w) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
    rw [coe_endDomain_hyperplaneProjection k V hf₀ hf₀w]
    exact Set.subset_compl_singleton_iff.mpr hf₀X
  obtain ⟨E, hEc, -, hEdim, hEeq⟩ := hU (linearFunctionalPoint k V f₀ hf₀) hf₀U
    (linearFunctionalPoint_isClosed k V f₀ hf₀)
  -- the image of `X` lies in the hyperplane, the retraction killing `w`
  have hHimg : endProjectionImage k V (hyperplaneProjection k V f₀ w)
      (X : Set (projectiveSpaceOfModule k V)) ⊆ H := by
    rw [hH]
    refine endProjectionImage_subset_linearSubspace k V (hyperplaneProjection k V f₀ w)
      (Submodule.span k {w}) _ fun q _ => (mem_linearSubspace_iff k V _ q).mpr ?_
    rw [Submodule.map_span, Set.image_singleton, hyperplaneProjection_self_eq_zero k V f₀ hf₀w,
      Submodule.span_zero_singleton]
    exact bot_le
  -- the image meets `Y` inside the decomposition Tag 0B1R provides
  have hTsub : endProjectionImage k V (hyperplaneProjection k V f₀ w)
        (X : Set (projectiveSpaceOfModule k V)) ∩ (Y : Set (projectiveSpaceOfModule k V)) ⊆
      (((Y : Set (projectiveSpaceOfModule k V)) ∩ H) ∩
        (X : Set (projectiveSpaceOfModule k V))) ∪ E := by
    rintro z ⟨hz1, hz2⟩
    have hmem : z ∈ ((Y : Set (projectiveSpaceOfModule k V)) ∩ H) ∩
        projectionCone k V (linearFunctionalPoint k V f₀ hf₀)
          (X : Set (projectiveSpaceOfModule k V)) :=
      ⟨⟨hz2, hHimg hz1⟩, endProjectionImage_subset_projectionCone k V hf₀ hf₀w hf₀X hz1⟩
    rw [hEeq] at hmem
    exact hmem
  have hdimP : topologicalKrullDim (projectiveSpaceOfModule k V) = (n : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn
  have hb1 : topologicalKrullDim ↥((((Y : Set (projectiveSpaceOfModule k V)) ∩ H) ∩
        (X : Set (projectiveSpaceOfModule k V)))) + (n : WithBot ℕ∞) ≤
      topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule k V)) +
        topologicalKrullDim ↥(Y : Set (projectiveSpaceOfModule k V)) := by
    refine le_trans (add_le_add (topologicalKrullDim_le_of_subset
      (show (((Y : Set (projectiveSpaceOfModule k V)) ∩ H) ∩
          (X : Set (projectiveSpaceOfModule k V))) ⊆
        ((X : Set (projectiveSpaceOfModule k V)) ∩
          (Y : Set (projectiveSpaceOfModule k V))) from fun z hz => ⟨hz.2, hz.1.1⟩))
      le_rfl) ?_
    rw [← hdimP]
    exact hXY
  have hb2 : topologicalKrullDim ↥E + (n : WithBot ℕ∞) ≤
      topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule k V)) +
        topologicalKrullDim ↥(Y : Set (projectiveSpaceOfModule k V)) := by
    refine hEdim.trans ?_
    calc topologicalKrullDim ↥((Y : Set (projectiveSpaceOfModule k V)) ∩ H) +
          topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule k V)) + 1
        = topologicalKrullDim ↥((Y : Set (projectiveSpaceOfModule k V)) ∩ H) + 1 +
            topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule k V)) :=
          add_right_comm _ _ _
      _ ≤ topologicalKrullDim ↥(Y : Set (projectiveSpaceOfModule k V)) +
            topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule k V)) :=
          add_le_add hdrop le_rfl
      _ = topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule k V)) +
            topologicalKrullDim ↥(Y : Set (projectiveSpaceOfModule k V)) := add_comm _ _
  refine ⟨hyperplaneProjection k V f₀ w, hgne, hgdet, hdom, ?_⟩
  rw [hdimP, topologicalKrullDim_endProjectionImage_eq k V (hyperplaneProjection k V f₀ w)
    hXc hdom]
  refine le_trans (add_le_add ((topologicalKrullDim_le_of_subset hTsub).trans
    (topologicalKrullDim_union_le ((hYc.inter hHc).inter hXc) hEc)) le_rfl) ?_
  rcases max_cases (topologicalKrullDim ↥(((Y : Set (projectiveSpaceOfModule k V)) ∩ H) ∩
      (X : Set (projectiveSpaceOfModule k V)))) (topologicalKrullDim ↥E) with
    ⟨hmax, -⟩ | ⟨hmax, -⟩
  · rw [hmax]
    exact hb1
  · rw [hmax]
    exact hb2

/-- **The bad locus of Tag 0B1S does not contain the whole of `Z = 𝐏 ∖ PGL(V)`:** some closed
point of `Z` has no bad representative. This is the set-theoretic form of the source's "it
suffices to prove that `B` does not contain the generic point of `Z`", and it is where the
scalar invariance
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_smul` is used — the bad locus
collects the classes with *some* bad representative, so a class is ruled out of it only by
ruling out every unit multiple of the endomorphism. -/
public theorem exists_mem_determinantHypersurface_notMem_badParameterLocus [Nontrivial V]
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ) :
    ∃ p : ClosedPoints k (ParameterModule k V),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ determinantHypersurface k V ∧
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∉
        badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
          (Y : Set (projectiveSpaceOfModule k V)) := by
  obtain ⟨g, hgne, hgdet, hgood⟩ := exists_det_eq_zero_isGoodEndomorphism k V X Y hXY hXne
  set p₀ : ClosedPoints k (ParameterModule k V) :=
    (dualEndClosedPointsEquiv k V).symm (Projectivization.mk k g hgne) with hp₀def
  have hp₀ : dualEndClosedPointsEquiv k V p₀ = Projectivization.mk k g hgne := by
    rw [hp₀def, Equiv.apply_symm_apply]
  refine ⟨p₀, (mem_determinantHypersurface_iff k V).mpr fun hmem =>
    (coe_mem_invertibleLocus_iff_det_ne_zero k V p₀ g hgne hp₀).mp hmem hgdet, ?_⟩
  rintro ⟨p', g', hpq, ⟨hg'0, hg'eq⟩, hbad⟩
  have hp' : p' = p₀ := Subtype.ext hpq
  have hmk : Projectivization.mk k g' hg'0 = Projectivization.mk k g hgne := by
    rw [← hg'eq, hp', hp₀]
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff k g' g hg'0 hgne).mp hmk
  have hg'c : g' = (c : k) • g := by rw [← hc, Units.smul_def]
  refine hbad ?_
  rw [hg'c]
  exact (isGoodEndomorphism_smul k V c g _ _).mpr hgood

/-- **A closed subset of `Z = 𝐏 ∖ PGL(V)` whose closed points are all bad has codimension at
least two at each of its points** — which is what the reducible form of Tag 0B2T consumes. It is
a *proper* closed subset of `Z` by
`exists_mem_determinantHypersurface_notMem_badParameterLocus` above, and `Z` is irreducible and
is itself a proper closed subset of `𝐏`, so the closure of each point of the subset is the
bottom of a strict chain of length two. -/
public theorem two_le_codimension_of_isClosed_subset_bad [Nontrivial V]
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (B : Set (projectiveSpaceOfModule k (ParameterModule k V))) (hBc : IsClosed B)
    (hBZ : B ⊆ determinantHypersurface k V)
    (hBbad : ∀ p : ClosedPoints k (ParameterModule k V),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ B →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
          badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
            (Y : Set (projectiveSpaceOfModule k V))) :
    ∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  have h2 : 2 ≤ Module.finrank k V :=
    two_le_finrank_of_isClosed_ne_univ k V X.isClosed' hXne X.isIrreducible'.nonempty
  obtain ⟨p₀, hZmem, hbad₀⟩ :=
    exists_mem_determinantHypersurface_notMem_badParameterLocus k V X Y hXY hXne
  have hnotB : (p₀ : projectiveSpaceOfModule k (ParameterModule k V)) ∉ B :=
    fun hmem => hbad₀ (hBbad p₀ hmem)
  exact fun x hx => two_le_codimension_of_mem_of_isClosed_ssubset hBc
    (isClosed_determinantHypersurface k V) (isIrreducible_determinantHypersurface k V h2) hBZ
    (fun heq => hnotB (heq ▸ hZmem)) (determinantHypersurface_ne_univ k V h2) hx

/-- **Tag 0B1S with clause (1) and the codimension of the clause-(2) locus inside `Z`
discharged.** The clause-(2) half of the source's intermediate claim is split along the
determinant: a closed `B₂ᴳ` carrying the invertible classes at which clause (2) fails, which is
asked for the codimension bound as before, and a closed `B₂ᶻ ⊆ Z` carrying the singular ones,
which is **not** — the bound for it is
`AlgebraicGeometry.ProjectiveSpaceOfModule.two_le_codimension_of_isClosed_subset_bad`.

So what is still carried of the source's proof is its incidence correspondence, together with
Tag 0B2L. The correspondence is wanted over *all* of `𝐏` and not only over `PGL(V)`: taken over
all of `𝐏` its projection to the parameter space is proper, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionProper`, which discharges the
one assertion the source makes without proof, that the bad locus is closed; the projection from a
product with `PGL(V)` as its last factor is not proper, `PGL(V)` not being closed in `𝐏`. What
`hBGsup` then has to be fed is the translation of a jump in the fibre dimension into badness,
which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_topologicalKrullDim_fibre_le` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.ClauseTwoFibre`. Nothing is registered
against Tag 0B1S: clause (2) is not discharged.
The conclusion is that of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_clauseTwo`,
whose hypotheses these imply. -/
public theorem exists_isOpen_closedPoint_line_isGood_of_clauseTwo_split [Nontrivial V]
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXne : (X : Set (projectiveSpaceOfModule k V)) ≠ Set.univ)
    (_hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty)
    (BG : Set (projectiveSpaceOfModule k (ParameterModule k V))) (hBGc : IsClosed BG)
    (hBGbad : ∀ p : ClosedPoints k (ParameterModule k V),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ BG →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
          badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
            (Y : Set (projectiveSpaceOfModule k V)))
    (hBGsup : ∀ (p : ClosedPoints k (ParameterModule k V)) (g : V →ₗ[k] V),
      RepresentsParameterPoint k V p g → LinearMap.det g ≠ 0 →
      (X : Set (projectiveSpaceOfModule k V)) ⊆
        ((endDomain k V g : (projectiveSpaceOfModule k V).Opens) :
          Set (projectiveSpaceOfModule k V)) →
      ¬ IsGoodEndomorphism k V (X : Set (projectiveSpaceOfModule k V))
          (Y : Set (projectiveSpaceOfModule k V)) g →
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ BG)
    (hBGcodim : ∀ x ∈ BG, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (BZ : Set (projectiveSpaceOfModule k (ParameterModule k V))) (hBZc : IsClosed BZ)
    (hBZZ : BZ ⊆ determinantHypersurface k V)
    (hBZbad : ∀ p : ClosedPoints k (ParameterModule k V),
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ BZ →
        (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
          badParameterLocus k V (X : Set (projectiveSpaceOfModule k V))
            (Y : Set (projectiveSpaceOfModule k V)))
    (hBZsup : ∀ (p : ClosedPoints k (ParameterModule k V)) (g : V →ₗ[k] V),
      RepresentsParameterPoint k V p g → LinearMap.det g = 0 →
      (X : Set (projectiveSpaceOfModule k V)) ⊆
        ((endDomain k V g : (projectiveSpaceOfModule k V).Opens) :
          Set (projectiveSpaceOfModule k V)) →
      ¬ IsGoodEndomorphism k V (X : Set (projectiveSpaceOfModule k V))
          (Y : Set (projectiveSpaceOfModule k V)) g →
      (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈ BZ) :
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
  refine exists_isOpen_closedPoint_line_isGood_of_clauseTwo k V X Y hXY hXne _hXYne (BG ∪ BZ)
    (hBGc.union hBZc) (fun p hp => hp.elim (hBGbad p) (hBZbad p)) (fun p g hg hdom hbad => ?_)
    (fun x hx => hx.elim (hBGcodim x) ?_)
  · rcases eq_or_ne (LinearMap.det g) 0 with hdet | hdet
    · exact Or.inr (hBZsup p g hg hdet hdom hbad)
    · exact Or.inl (hBGsup p g hg hdet hdom hbad)
  · exact two_le_codimension_of_isClosed_subset_bad k V X Y hXY hXne BZ hBZc hBZZ hBZbad x

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
