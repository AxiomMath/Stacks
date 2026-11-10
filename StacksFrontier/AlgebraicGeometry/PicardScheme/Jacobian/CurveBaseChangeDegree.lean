module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import
  StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointsCurveJacobian
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveFibreDegree

/-!
# The degree of an invertible module with one section on a base change of a curve

Let `X` be a smooth proper geometrically irreducible curve of genus `g` over a field `k`, and
`X_K` its base change to a field extension `K`. Then `χ(X_K, 𝒪) = 1 - g`, and an invertible
module `ℒ` on `X_K` with `h⁰(ℒ) = 1` and no higher cohomology has degree
`deg ℒ = χ(ℒ) - χ(𝒪) = g`. This is the degree computation in the proof of [Stacks, Tag 0B9X].

The fibres of a base change `X_T ⟶ T` are such base changes
(`AlgebraicGeometry.isPullback_fiberι_fst`).

## Main results

* `AlgebraicGeometry.finsum_finrank_cohomologyOverField_unit_baseChange`: `χ(X_K, 𝒪) = 1 - g`.
* `AlgebraicGeometry.invertibleCurveDegree_eq_genus_of_cohomology`: `deg ℒ = g`.

No Stacks tag is attached.

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A scheme smooth of relative dimension one over a field has dimension at most one. -/
theorem topologicalKrullDim_le_one_of_smoothOfRelativeDimension {K : Type u} [Field K]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p] :
    topologicalKrullDim Z ≤ 1 := by
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · rw [(topologicalKrullDim_eq_bot_iff_isEmpty Z).2 hZ]
    exact bot_le
  · exact (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 p).le

/-- **The cohomology of the structure sheaf of a base change of a curve to a field extension.**
Its dimensions are those over `k`. -/
theorem finrank_cohomologyOverField_unit_baseChange [IsProper f] {K : Type u} [Field K]
    [Algebra k K] {X' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (n : ℕ) :
    Module.finrank K (cohomologyOverField K f' (SheafOfModules.unit X'.ringCatSheaf) n) =
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) := by
  refine Eq.trans ?_ (finrank_cohomologyOverField_baseChange_field k K g' f' f h
    (SheafOfModules.unit X.ringCatSheaf) n)
  exact (cohomologyOverFieldIso K f'
    (Scheme.Modules.pullbackUnitIso g').symm n).toLinearEquiv.finrank_eq

/-- **The Euler characteristic of the structure sheaf of a base change of a curve.** For `X`
smooth, proper and geometrically irreducible of relative dimension one over `k`, every base change
to a field `K` has `χ(𝒪) = 1 - g`. -/
theorem finsum_finrank_cohomologyOverField_unit_baseChange [SmoothOfRelativeDimension 1 f]
    [IsProper f] [GeometricallyIrreducible f] {K : Type u} [Field K] [Algebra k K]
    {X' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank K (cohomologyOverField K f' (SheafOfModules.unit X'.ringCatSheaf) n) : ℤ) =
      1 - (genus f : ℤ) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have h0 := Stacks.WeilCohomology.curveHasOneDimensionalSections k f
  have hdim := topologicalKrullDim_le_one_of_smoothOfRelativeDimension f
  have hv : ∀ n : ℕ, 2 ≤ n → Module.finrank k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) = 0 := fun n hn =>
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cohomologyOverField_of_topologicalKrullDim_le k f
        (SheafOfModules.unit X.ringCatSheaf) (d := 1) (i := n) hdim (by omega))
    Module.finrank_zero_of_subsingleton
  simp_rw [finrank_cohomologyOverField_unit_baseChange f g' f' h]
  rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
  · rw [Finset.sum_pair (by norm_num), genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq,
      ← (structureSheafCohomologyIsoCohomologyOverField k f 0).toLinearEquiv.finrank_eq, h0]
    ring
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hc
    exact hn (by rw [hv n (by omega)]; simp)

/-- **The degree of an invertible module with `h⁰ = 1` and no higher cohomology on a base change
of a curve of genus `g` is `g`.** This is `deg ℒ = χ(ℒ) - χ(𝒪) = 1 - (1 - g)`. -/
theorem invertibleCurveDegree_eq_genus_of_cohomology [SmoothOfRelativeDimension 1 f]
    [IsProper f] [GeometricallyIrreducible f] {K : Type u} [Field K] [Algebra k K]
    {X' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of K))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) [IsProper f']
    (hdim : topologicalKrullDim X' ≤ 1) (L : X'.Modules)
    [SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 L]
    (h0 : Module.finrank K (cohomologyOverField K f' L 0) = 1)
    (hpos : ∀ n : ℕ, 0 < n → Subsingleton (cohomologyOverField K f' L n)) :
    invertibleCurveDegree K f' hdim L = genus f := by
  rw [invertibleCurveDegree, finsum_finrank_cohomologyOverField_unit_baseChange f g' f' h,
    finsum_eq_single _ 0]
  · rw [h0]
    ring
  · intro n hn
    have := hpos n (Nat.pos_of_ne_zero hn)
    rw [Module.finrank_zero_of_subsingleton]
    simp

/-- **The fibre of a base change of `X` over a point is the base change of `X` to the residue
field.** -/
theorem isPullback_fiberι_fst (T : Over (Spec (.of k))) (t : T.left)
    [Algebra k (T.left.residueField t)]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap k (T.left.residueField t))) =
      T.left.fromSpecResidueField t ≫ T.hom) :
    IsPullback ((pullback.snd f T.hom).fiberι t ≫ pullback.fst f T.hom)
      ((pullback.snd f T.hom).fiberToSpecResidueField t) f
      (Spec.map (CommRingCat.ofHom (algebraMap k (T.left.residueField t)))) :=
  hφ ▸ Stacks.RigidifiedPicard.isPullback_fiber_bcProj f T t

/-- The algebra structure on the residue field of a point of a `k`-scheme. -/
abbrev overResidueFieldAlgebra (T : Over (Spec (.of k))) (t : T.left) :
    Algebra k (T.left.residueField t) :=
  (Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)).hom.toAlgebra

/-- The morphism `Spec κ(t) ⟶ Spec k` is `Spec` of the algebra map of
`AlgebraicGeometry.overResidueFieldAlgebra`. -/
theorem spec_map_algebraMap_overResidueFieldAlgebra (T : Over (Spec (.of k))) (t : T.left) :
    letI := overResidueFieldAlgebra T t
    Spec.map (CommRingCat.ofHom (algebraMap k (T.left.residueField t))) =
      T.left.fromSpecResidueField t ≫ T.hom := by
  let := overResidueFieldAlgebra T t
  change Spec.map (CommRingCat.ofHom (Spec.preimage _).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

end AlgebraicGeometry

end
