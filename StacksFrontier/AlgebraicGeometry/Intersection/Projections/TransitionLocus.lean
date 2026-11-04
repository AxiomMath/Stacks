module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusReducible
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TwoPointFibre

/-!
# The classes carrying one point of a projective space to another form a linear subspace

A closed point of `𝐏(V) = Proj (Sym V)` is the class `[f]` of a nonzero functional on `V`, and
the projective transformation attached to an endomorphism `g` sends `[f]` to `[f ∘ g]`. So the
classes `[g]` of the parameter space `𝐏 = 𝐏((End V)ᵛ)` carrying `[f]` to `[f']` are cut out by
the condition `f ∘ g ∈ k ∙ f'`, which is *linear* in `g`:
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubmodule` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TwoPointFibre` is a subspace of `End V`
of corank `dim V - 1`. This file reads that subspace back on the parameter space, as the
projective linear subspace cut out by its annihilator: a closed irreducible subset of `𝐏` of
dimension `(dim V)² - dim V`, which is `dim 𝐏 - dim 𝐏(V)`.

This is the fibre of the incidence correspondence
`T = {(x, y, [g]) : x ∈ X, y ∈ Y, r_g(x) = y}` of Tag 0B1S over a pair of closed points of
`𝐏(V) × 𝐏(V)`, and the point of recording it is that the dimension and the irreducibility are
*the same over every pair*, the diagonal included: the condition `f ∘ g ∈ k ∙ f'` has corank
`dim V - 1` whether or not `[f] = [f']`. The incidence variety of lines of Tag 0B1R behaves
differently — over a pair of coinciding points its fibre is a whole copy of `𝐏(V)` and not a
line, which is `range_diagThree_subset_collinearLocus` of
`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Diagonal` — and that is why Tag 0B1R has
to be taken over the distinct-pairs base `prodOfClosedOffSndToProdTwo`. No such restriction is
needed here.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEquations`: the degree-one forms on `𝐏`
  cutting out the classes carrying `[f]` to `[f']`, namely the annihilator of
  `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubmodule`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_eq_linearFunctionalPoint_iff`: inside
  `U(g)`, `r_g` carries `[f]` to `[f']` exactly when `f ∘ g` lies on the line of `f'`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_linearSubspace_transitionEquations_iff`: a
  closed point of `𝐏` lies on the transition locus exactly when its representatives satisfy
  that condition.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_transitionEquations`: the equations are
  `dim V - 1` in number.
* `ProjectiveSpaceOfModule.topologicalKrullDim_linearSubspace_transitionEquations` and
  `ProjectiveSpaceOfModule.isIrreducible_linearSubspace_transitionEquations`:
  the transition locus is irreducible of dimension `(dim V)² - dim V`.

## Implementation notes

**Where this sits in Tag 0B1S.** Clause (1) of Tag 0B1S is proved in
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.BadLocusCodimension`, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_clauseTwo`
there reduces the tag to the clause-(2) half of the bad locus: a *closed* `B₂ ⊆ 𝐏` of pointwise
codimension at least two containing every class at which `X ⊆ U(g)` holds and `r_g(X)` fails to
meet `Y` properly. The source gets that from the incidence correspondence `T` over `X × Y`,
whose fibre over a pair of closed points is what this file computes, together with Tag 0B2L.
What remains, and is *not* in the library, is:

* `T` itself as a scheme. It is cut out of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏` by the `2 × 2` minors of the
  pair `(f', f ∘ g)`, sections of `𝒪(1,1,1)`, exactly as the determinant sections of
  `StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus` are built — but
  that module builds `𝒪(1,1,1)` and its sections only for three copies of one and the same
  projective space, so the two-different-spaces version has to be written. The minors are not
  tensors of three tautological sections but finite *sums* of such, because `f (g v)` is
  bilinear in `(f, g)`: expanding `g v` in a basis writes it as `∑ f(eᵢ) · φᵢ(g)` with
  `φᵢ ∈ (End V)ᵛ`.
* `IrreducibleSpace T`. Tag 004Z is available, as
  `irreducibleSpace_of_isOpenMap_of_dense_isIrreducible_fiber` of
  `StacksFrontier.Topology.Irreducible.DenseFibres`: it asks that `T ⟶ X × Y` be an *open* map with
  a dense set of irreducible fibres. The fibres are irreducible, by
  `isIrreducible_linearSubspace_transitionEquations` below, over *every* pair of closed points
  and not only off the diagonal, which is what makes that route available here and not for Tag
  0B1R. Openness is the part still owed and must be proved, not assumed: it is false for the
  analogous projection of Tag 0B1R over a base meeting the diagonal. There is a second route,
  which needs no openness at all and is the one the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionCorrespondence` describe:
  `T` over `X × Y` is the closure of the image of the *product*
  `X × Y × 𝔸(k × V × V × V × End V)` under the bilinear parametrisation
  `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd`, and a product of irreducibles over
  an algebraically closed field is irreducible. What that route owes instead is the classifying
  morphism to `𝐏`, for which an `𝒪(1,1)` on a scheme over two projective spaces has to be
  written.
* The pointwise codimension bound. No lemma bounding the dimension of the locus where the fibre
  dimension jumps exists in the tree, and none is needed: Tag 0B2L part (2c),
  `topologicalKrullDimAt_fiber_add_one_le_of_one_le_ringKrullDim_imageClosure` of
  `StacksFrontier.AlgebraicGeometry.Variety.FibreDimension`, bounds
  `dim_x(T_{π x}) + 1 ≤ d + dim 𝒪_{Z, π x}` with `d = dim T - dim Z` for `Z` the reduced closure
  of the image of `π : T ⟶ 𝐏`, and
  `ringKrullDim_stalk_eq_codimension_closureSingleton` of the namespace
  `Stacks.AlgebraicGeometry.CodimensionOneDivisor`, in
  `StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic`, turns that local ring dimension
  into `codimension (closureSingleton (π x))`. At a class where the fibre dimension exceeds the
  generic value `d` by one this reads `2 ≤ codimension (closureSingleton (π x))`, which is
  literally the hypothesis of
  `exists_isOpen_subset_union_lines_disjoint_of_forall_codimension_ge_two`. Part (2c) requires
  `IrreducibleSpace T`, which is why the previous item is needed.

The analysis on `Z = 𝐏 ∖ PGL(V)` is **available**. It is
`AlgebraicGeometry.ProjectiveSpaceOfModule.two_le_codimension_of_isClosed_subset_bad` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.SingularGoodEndomorphism`, which gets the
codimension bound for a closed subset of `Z` whose closed points are all bad out of the existence
of one good *singular* class, and the split of the bad locus along the determinant is
`exists_isOpen_closedPoint_line_isGood_of_clauseTwo_split` there. So what the clause-(2) half
still needs is a closed subset of `𝐏` containing the **invertible** bad classes, and for that
only the three items above.

Two further steps of that half are also done, and neither is where the determinant enters. The
source's "`r_g|_X : X → r_g(X)` is finite, hence `dim r_g(X) = dim X`" is
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_eq` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.EndProjectionFinite`, for an arbitrary
endomorphism and an arbitrary closed subset of `U(g)`; and with it clause (2) becomes a bound on
the dimension of the single closed set `X ∩ r_g⁻¹(Y)`, which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.isGoodEndomorphism_iff_topologicalKrullDim_fibre_le` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.ClauseTwoFibre`. Neither asks
invertibility of `g` nor irreducibility of `X`. Closedness of the bad locus — the one assertion
the source makes without proof — is
`AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_image_transitionVarietyToPar` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionProper`, the projection of the
correspondence to the parameter space being proper over a base proper over the ground field.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
* [Stacks Project, Tag 004Z](https://stacks.math.columbia.edu/tag/004Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

variable [IsAlgClosed k] [FiniteDimensional k V]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- **`r_g` carries `[f]` to `[f']` exactly when `f ∘ g` lies on the line of `f'`.** On `U(g)`
the transformation sends the point cut out by `f` to the point cut out by `f ∘ g`, and two
nonzero functionals cut out the same point exactly when they are proportional. -/
public theorem endProjection_eq_linearFunctionalPoint_iff (g : V →ₗ[k] V)
    (y : (endDomain k V g).toScheme) {f f' : Module.Dual k V} (hf : f ≠ 0) (hf' : f' ≠ 0)
    (hfg : f ∘ₗ g ≠ 0)
    (hy : (y.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f hf) :
    endProjection k V g y = linearFunctionalPoint k V f' hf' ↔
      f ∘ₗ g ∈ Submodule.span k {f'} := by
  rw [endProjection_eq_linearFunctionalPoint k V g y f hf hfg hy]
  refine ⟨fun heq => ?_, fun hmem => ?_⟩
  · have hcl : closedPointOfDual k V (Projectivization.mk k (f ∘ₗ g) hfg) =
        closedPointOfDual k V (Projectivization.mk k f' hf') := Subtype.ext heq
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff k (f ∘ₗ g) f' hfg hf').mp
      (closedPointOfDual_injective k V hcl)
    rw [← hc, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f')
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 : c ≠ 0 := fun h => hfg (by rw [← hc, h, zero_smul])
    have hcf : ((Units.mk0 c hc0 : kˣ) : k) • f' = f ∘ₗ g := by rw [Units.val_mk0, hc]
    rw [linearFunctionalPoint_eq_of_eq k V hfg (hcf ▸ hfg) hcf.symm]
    exact linearFunctionalPoint_units_smul k V (Units.mk0 c hc0) f' hf' (hcf ▸ hfg)

/-- **The degree-one forms on the parameter space cutting out the classes carrying `[f]` to
`[f']`:** the annihilator of
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubmodule`, read as a submodule of
`(End V)ᵛ`, which is the module whose projective space is the parameter space. -/
public def transitionEquations (f f' : Module.Dual k V) : Submodule k (ParameterModule k V) :=
  (transitionSubmodule k V f f').dualAnnihilator

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- **What those forms say.** Every one of them kills `g` exactly when `f ∘ g` lies on the line
spanned by `f'`: in finite dimension a subspace is the common zero locus of its annihilator. -/
public theorem forall_apply_eq_zero_transitionEquations_iff (f f' : Module.Dual k V)
    (g : V →ₗ[k] V) :
    (∀ φ ∈ transitionEquations k V f f', φ g = 0) ↔ f ∘ₗ g ∈ Submodule.span k {f'} := by
  rw [← mem_transitionSubmodule_iff k V f f' g]
  refine ⟨fun hall => ?_, fun hg φ hφ => (Submodule.mem_dualAnnihilator _).mp hφ g hg⟩
  have hmem : g ∈ (transitionSubmodule k V f f').dualAnnihilator.dualCoannihilator :=
    (Submodule.mem_dualCoannihilator _).mpr hall
  rwa [Subspace.dualAnnihilator_dualCoannihilator_eq] at hmem

/-- **A closed point of `𝐏` lies on the transition locus exactly when its representatives carry
`[f]` into the line of `f'`.** -/
public theorem mem_linearSubspace_transitionEquations_iff
    {p : ClosedPoints k (ParameterModule k V)} {g : V →ₗ[k] V}
    (hg : RepresentsParameterPoint k V p g) (f f' : Module.Dual k V) :
    (p : projectiveSpaceOfModule k (ParameterModule k V)) ∈
        linearSubspace k (ParameterModule k V) (transitionEquations k V f f') ↔
      f ∘ₗ g ∈ Submodule.span k {f'} := by
  rw [mem_linearSubspace_iff_forall_apply_eq_zero k V hg,
    forall_apply_eq_zero_transitionEquations_iff]

omit [IsAlgClosed k] in
/-- **The transition locus is cut out by `dim V - 1` equations**, the corank of
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSubmodule`. -/
public theorem finrank_transitionEquations {n : ℕ} (hV : Module.finrank k V = n + 1)
    {f f' : Module.Dual k V} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    Module.finrank k (transitionEquations k V f f') = n := by
  show Module.finrank k ((transitionSubmodule k V f f').dualAnnihilator) = n
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (transitionSubmodule k V f f' : Subspace k (V →ₗ[k] V))
  have h2 := Submodule.finrank_quotient_add_finrank (transitionSubmodule k V f f')
  have h3 := finrank_quotient_transitionSubmodule k V hf hf'
  rw [hV] at h3
  omega

omit [IsAlgClosed k] in
/-- The transition locus is not empty: the equations do not exhaust `(End V)ᵛ`. -/
public theorem transitionEquations_ne_top {n m : ℕ} (hV : Module.finrank k V = n + 1)
    (hm : Module.finrank k (ParameterModule k V) = m + n + 1)
    {f f' : Module.Dual k V} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    transitionEquations k V f f' ≠ ⊤ := by
  intro htop
  have h := finrank_transitionEquations k V hV hf hf'
  rw [htop, finrank_top, hm] at h
  omega

omit [IsAlgClosed k] in
/-- **The transition locus has dimension `(dim V)² - dim V`.** Stated without subtraction: `m` is
that number, pinned by `dim 𝐏 = m + dim V`, that is by
`dim_k (End V)ᵛ = m + dim_k V`. -/
public theorem topologicalKrullDim_linearSubspace_transitionEquations {n m : ℕ}
    (hV : Module.finrank k V = n + 1)
    (hm : Module.finrank k (ParameterModule k V) = m + n + 1)
    {f f' : Module.Dual k V} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    topologicalKrullDim
        (linearSubspace k (ParameterModule k V) (transitionEquations k V f f')) =
      ((m : ℕ) : WithBot ℕ∞) := by
  refine topologicalKrullDim_linearSubspace_of_finrank_eq k (ParameterModule k V) _ (m := m) ?_
  have hq := Submodule.finrank_quotient_add_finrank (transitionEquations k V f f')
  have h := finrank_transitionEquations k V hV hf hf'
  rw [hm] at hq
  omega

omit [IsAlgClosed k] in
/-- **The transition locus is irreducible.** It is a projective linear subspace, hence the image
of the projective space of a quotient. This holds over *every* pair of closed points of
`𝐏(V) × 𝐏(V)`, the diagonal included. -/
public theorem isIrreducible_linearSubspace_transitionEquations {n m : ℕ}
    (hV : Module.finrank k V = n + 1)
    (hm : Module.finrank k (ParameterModule k V) = m + n + 1)
    {f f' : Module.Dual k V} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    IsIrreducible
      (linearSubspace k (ParameterModule k V) (transitionEquations k V f f')) :=
  isIrreducible_linearSubspace k (ParameterModule k V)
    (transitionEquations_ne_top k V hV hm hf hf')

omit [IsAlgClosed k] in
/-- The dimension of the transition locus over a pair of closed points of `𝐏(V) × 𝐏(V)`, with
the two numerical hypotheses discharged from `dim_k V` alone. -/
public theorem topologicalKrullDim_linearSubspace_transitionEquations_of_finrank_eq {n : ℕ}
    (hV : Module.finrank k V = n + 1) {f f' : Module.Dual k V} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    topologicalKrullDim
        (linearSubspace k (ParameterModule k V) (transitionEquations k V f f')) =
      (((n + 1) * (n + 1) - (n + 1) : ℕ) : WithBot ℕ∞) := by
  refine topologicalKrullDim_linearSubspace_transitionEquations k V hV ?_ hf hf'
  rw [finrank_parameterModule, hV]
  cases n with
  | zero => simp
  | succ m =>
    ring_nf
    omega

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
