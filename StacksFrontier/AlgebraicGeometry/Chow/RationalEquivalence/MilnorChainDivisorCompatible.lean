module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorChainBoundaryCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointClosureImmersionDivisor

/-!
# The degreewise localization sequence and the second differential of Stacks 0GU9

Stacks 0GUA asserts that the degreewise split short exact sequences of locally finite Milnor
K-chains attached to an open subscheme and its closed complement are compatible with the two
differentials of the complex of Stacks 0GU9. This file proves that compatibility for the *second*
differential, the divisor differential `K₁ ⟶ K₀` of Stacks 0GU3; the companion file
`MilnorChainBoundaryCompatible.lean` proves it for the first.

Both squares reduce to one point at a time. The degree-zero coordinate of the differential at a
point `y` is a locally finite sum, over the points `x'` of relative dimension `k + 1`, of the
coefficient at `y` of the principal divisor on `closure {x'}` of the rational function attached to
the Milnor K₁-class of the chain there
(`Stacks.Chow.pointwiseDivisorDifferential_apply_eq_finsum`); and the degree-zero transport of
Milnor K-theory is the identity on `ℤ` (`Stacks.Chow.milnorKTheoryZeroAddEquiv_milnorKTransport`),
so no identification of residue fields survives into the coefficients. Restriction to an open
subscheme loses no summand: a point specializing into the open subscheme lies in it. Extension by
zero from the closed subscheme gains none: the closure of a point of a closed subscheme lies in
it. What remains in each case is that the local coefficients agree, which is
`Stacks.Chow.pointClosureOrd_isOpenImmersion`, respectively
`Stacks.Chow.pointClosureOrd_isClosedImmersion`.

## Main results

* `Stacks.Chow.milnorChainComap_pointwiseDivisorDifferential` — **Stacks 0GUA** for the second
  differential and the restriction map: restriction to the open subscheme commutes with the
  divisor differential.
* `Stacks.Chow.pointwiseDivisorDifferential_milnorChainExtend` — **Stacks 0GUA** for the second
  differential and the extension-by-zero map from the closed subscheme.

## References

* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X U Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (j : U ⟶ X) [IsOpenImmersion j]

/-! ### Restriction to the open subscheme -/

/-- **Stacks 0GUA for the second differential and the restriction map.** Restriction of locally
finite Milnor K-chains to an open subscheme commutes with the divisor differential of
Stacks 0GU3: the square formed by the two differentials and the two restriction maps, in Milnor
degrees one and zero, commutes. -/
@[stacks 0GUA "the compatibility of the restriction map of the degreewise localization sequence \
of the tag with the SECOND boundary map of the complex of Stacks 0GU9, the divisor differential \
of Stacks 0GU3: for an open immersion j into a scheme locally of finite type over a Chow \
situation, restriction of locally finite Milnor K-chains to the open subscheme carries the \
divisor differential in relative dimensions k + 1 and k to the divisor differential of the open \
subscheme. The companion square for the extension-by-zero map from the closed complement is \
Stacks.Chow.pointwiseDivisorDifferential_milnorChainExtend"]
theorem milnorChainComap_pointwiseDivisorDifferential (k : ℤ) :
    (pointwiseDivisorDifferential C (j ≫ p) k).comp
        (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) (k + 1) 1) =
      (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) k 0).comp
        (pointwiseDivisorDifferential C p k) := by
  refine AddMonoidHom.ext fun a ↦ Subtype.ext (funext fun u ↦ ?_)
  refine (milnorKTheoryZeroAddEquiv ↥(U.residueField u.1)).injective ?_
  change milnorKTheoryZeroAddEquiv ↥(U.residueField u.1)
      ((pointwiseDivisorDifferential C (j ≫ p) k
        (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) (k + 1) 1 a)).1 u) =
    milnorKTheoryZeroAddEquiv ↥(U.residueField u.1)
      (milnorKTransport
        ((immersionResidueFieldEquiv j (bijective_residueFieldMap_openImmersion j) u.1 :
          _ →+* _)) 0
        ((pointwiseDivisorDifferential C p k a).1
          (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) k u)))
  rw [milnorKTheoryZeroAddEquiv_milnorKTransport,
    pointwiseDivisorDifferential_apply_eq_finsum, pointwiseDivisorDifferential_apply_eq_finsum,
    finsum_eq_finsum_of_injective
      (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 1))
      (immersionPoint_injective C p j (injective_base_of_isOpenImmersion j)
        (bijective_residueFieldMap_openImmersion j) (k + 1)) _ ?_]
  · refine finsum_congr fun w ↦ ?_
    change pointClosureOrd C (j ≫ p) w.1
        ((milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) (k + 1) 1 a).1 w) u.1 =
      pointClosureOrd C p (j.base w.1)
        (a.1 (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 1) w))
        (j.base u.1)
    rw [milnorChainComap_apply]
    exact pointClosureOrd_isOpenImmersion C p (j ≫ p) j
      (bijective_residueFieldMap_openImmersion j) w.1
      (a.1 (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 1) w)) u.1
  · intro x hx
    have hxrange : (x.1 : X) ∉ Set.range j.base := fun hcon ↦
      hx (exists_immersionPoint_eq C p j (bijective_residueFieldMap_openImmersion j) x hcon)
    change pointClosureOrd C p x.1 (a.1 x) (j.base u.1) = 0
    exact pointClosureOrd_eq_zero_of_notMem_closure C p x.1 (a.1 x)
      (fun hcon ↦ j.isOpenEmbedding.isOpen_range.not_specializes hxrange ⟨u.1, rfl⟩
        (specializes_iff_mem_closure.mpr hcon))

/-! ### Extension by zero from the closed subscheme -/

variable (i : Y ⟶ X) [IsClosedImmersion i]

/-- Off the closed subscheme the divisor differential of an extension by zero vanishes: the
closure of a point of the closed subscheme lies in it. -/
theorem pointwiseDivisorDifferential_milnorChainExtend_of_notMem_range (k : ℤ)
    (b : PointwiseKOneGroup C (i ≫ p) k) (x' : pointsOfDimension C p k)
    (hx' : (x'.1 : X) ∉ Set.range i.base) :
    milnorKTheoryZeroAddEquiv ↥(X.residueField x'.1)
      ((pointwiseDivisorDifferential C p k
        (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 1) 1 b)).1 x') = 0 := by
  rw [pointwiseDivisorDifferential_apply_eq_finsum, finsum_congr fun x ↦ ?_, finsum_zero]
  by_cases hx : (x.1 : X) ∈ Set.range i.base
  · change pointClosureOrd C p x.1 _ x'.1 = 0
    exact pointClosureOrd_eq_zero_of_notMem_closure C p x.1 _
      (fun hcon ↦ i.isClosedEmbedding.isClosed_range.not_specializes hx hx'
        (specializes_iff_mem_closure.mpr hcon))
  · have hzero : (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
        (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 1) 1 b).1 x = 0 := by
      rw [milnorChainExtend_apply,
        milnorChainExtendAtHom_of_notMem_range C p i
          (bijective_residueFieldMap_closedImmersion i) x hx, AddMonoidHom.zero_apply]
    rw [hzero, map_zero]

/-- **Stacks 0GUA for the second differential and the extension-by-zero map.** Extension by zero
of locally finite Milnor K-chains from a closed subscheme commutes with the divisor differential
of Stacks 0GU3. -/
@[stacks 0GUA "the compatibility of the extension-by-zero map of the degreewise localization \
sequence of the tag with the SECOND boundary map of the complex of Stacks 0GU9, the divisor \
differential of Stacks 0GU3: for a closed immersion i into a scheme locally of finite type over \
a Chow situation, extension by zero of locally finite Milnor K-chains from the closed subscheme \
carries its divisor differential in relative dimensions k + 1 and k to the divisor differential \
of the ambient scheme. The companion square for the restriction map to the open complement is \
Stacks.Chow.milnorChainComap_pointwiseDivisorDifferential"]
theorem pointwiseDivisorDifferential_milnorChainExtend (k : ℤ) :
    (pointwiseDivisorDifferential C p k).comp
        (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 1) 1) =
      (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) inferInstance k 0).comp
        (pointwiseDivisorDifferential C (i ≫ p) k) := by
  refine AddMonoidHom.ext fun b ↦ Subtype.ext (funext fun x' ↦ ?_)
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  refine (milnorKTheoryZeroAddEquiv ↥(X.residueField x'.1)).injective ?_
  by_cases hx' : (x'.1 : X) ∈ Set.range i.base
  · obtain ⟨y, rfl⟩ :=
      exists_immersionPoint_eq C p i (bijective_residueFieldMap_closedImmersion i) x' hx'
    rw [milnorChainExtend_apply_immersionPoint C p i (injective_base_of_isClosedImmersion i)
        (bijective_residueFieldMap_closedImmersion i) inferInstance k 0
        (pointwiseDivisorDifferential C (i ≫ p) k b) y,
      milnorKTheoryZeroAddEquiv_milnorKTransport,
      pointwiseDivisorDifferential_apply_eq_finsum C p k,
      pointwiseDivisorDifferential_apply_eq_finsum C (i ≫ p) k b y,
      finsum_eq_finsum_of_injective
        (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 1))
        (immersionPoint_injective C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) (k + 1)) _ ?_]
    · refine finsum_congr fun y' ↦ ?_
      simp only [pointClosureOrdHom_apply]
      rw [milnorChainExtend_apply_immersionPoint C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 1) 1 b y',
        ← pointClosureOrd_isClosedImmersion C p (i ≫ p) i
          (bijective_residueFieldMap_closedImmersion i) y'.1 _ y.1,
        milnorKTransport_milnorKTransport_symm]
    · intro x hx
      have hxrange : (x.1 : X) ∉ Set.range i.base := fun hcon ↦
        hx (exists_immersionPoint_eq C p i (bijective_residueFieldMap_closedImmersion i) x hcon)
      have hzero : (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 1) 1 b).1 x = 0 := by
        rw [milnorChainExtend_apply,
          milnorChainExtendAtHom_of_notMem_range C p i
            (bijective_residueFieldMap_closedImmersion i) x hxrange, AddMonoidHom.zero_apply]
      rw [hzero, map_zero]
  · rw [pointwiseDivisorDifferential_milnorChainExtend_of_notMem_range C p i k b x' hx',
      milnorChainExtend_apply,
      milnorChainExtendAtHom_of_notMem_range C p i
        (bijective_residueFieldMap_closedImmersion i) x' hx', AddMonoidHom.zero_apply]
    exact (AddEquiv.map_zero _).symm

end Stacks.Chow

end
