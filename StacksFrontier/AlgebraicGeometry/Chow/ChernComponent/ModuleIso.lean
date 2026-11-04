module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport

/-!
# The divisor cycle of a meromorphic section under an isomorphism of modules

Let `X` be an integral scheme and let `φ : M ≅ N` be an isomorphism of `𝒪_X`-modules. A
meromorphic section `s` of `M`, in the generic-stalk model of
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`, is carried by the stalk map of `φ` at the
generic point to a meromorphic section of `N`, and

  `div_N(φ s) = div_M(s)`.

Indeed `φ` carries a basis of the stalk `M_x` to a basis of `N_x`, so a coordinate of `s` at `x`
in the sense of [Stacks, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF) is also a
coordinate of `φ s` there, and the order of vanishing is computed from any coordinate.

Combined with [Stacks, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ) (2) — the
independence of the class of the divisor cycle from the section, which this repository has as
`Stacks.Chow.mk_chernComponentCycle_eq` — this says that the class of the divisor cycle of a
nonzero meromorphic section of an invertible module depends only on the isomorphism class of the
module. That is what identifies the two spellings of the restriction of an invertible module to
an irreducible component of an inverse image, one obtained by restricting along the component and
one by restricting along the inverse image first.

## Main results

* `Stacks.Divisors.IsStalkBasis.ofModuleIso` and `Stacks.Divisors.IsCoordinateAt.ofModuleIso` —
  bases and coordinates transport.
* `Stacks.Divisors.orderOfVanishing_ofModuleIso` — the order of vanishing is unchanged.
* `Stacks.Chow.chernComponentCycle_ofModuleIso` — the divisor cycle is unchanged.
* `Stacks.Chow.mk_chernComponentCycle_eq_of_moduleIso` — the class of the divisor cycle of a
  nonzero meromorphic section is the same for two isomorphic modules.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The stalk map of an isomorphism of modules, spelled through the underlying linear map. -/
theorem stalkLinearEquiv_apply (φ : M ≅ N) (x : X) (m : M.presheaf.stalk x) :
    AlgebraicGeometry.stalkLinearEquiv M N φ.hom x m =
      AlgebraicGeometry.stalkLinearMap M N φ.hom x m :=
  rfl

/-- An isomorphism of modules carries a basis of a stalk to a basis of the corresponding stalk:
multiplication by the image is multiplication by the original followed by a bijection. -/
theorem IsStalkBasis.ofModuleIso (φ : M ≅ N) {x : X} {m : M.presheaf.stalk x}
    (hm : IsStalkBasis M x m) :
    IsStalkBasis N x (AlgebraicGeometry.stalkLinearEquiv M N φ.hom x m) := by
  set Φ := AlgebraicGeometry.stalkLinearEquiv M N φ.hom x with hΦ
  refine ⟨fun r r' hrr' ↦ hm.injective (Φ.injective ?_), fun n ↦ ?_⟩
  · rw [map_smul, map_smul]
    exact hrr'
  · obtain ⟨r, hr⟩ := hm.surjective (Φ.symm n)
    refine ⟨r, ?_⟩
    have hrn : Φ (r • m) = n := by
      rw [show r • m = Φ.symm n from hr]
      exact Φ.apply_symm_apply n
    rw [map_smul] at hrn
    exact hrn

variable [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- A coordinate of a meromorphic section at a point is also a coordinate of its image under an
isomorphism of modules: the basis witnessing it is carried across, and the specialization map to
the generic stalk is natural in the module. -/
theorem IsCoordinateAt.ofModuleIso (φ : M ≅ N) {x : X}
    {s : M.presheaf.stalk (genericPoint X)} {a : X.functionField}
    (ha : IsCoordinateAt M x s a) :
    IsCoordinateAt N x
      (AlgebraicGeometry.stalkLinearEquiv M N φ.hom (genericPoint X) s) a := by
  obtain ⟨m, hm, hsa⟩ := ha
  refine ⟨AlgebraicGeometry.stalkLinearEquiv M N φ.hom x m, hm.ofModuleIso φ, ?_⟩
  rw [hsa, map_smul]
  refine congrArg _ ?_
  rw [stalkLinearEquiv_apply, stalkLinearEquiv_apply]
  exact AlgebraicGeometry.stalkLinearMap_stalkSpecializes M N φ.hom
    ((genericPoint_spec X).specializes trivial) m

/-- **The order of vanishing is unchanged by an isomorphism of modules.** Both orders are the
order of vanishing of one and the same coordinate. -/
theorem orderOfVanishing_ofModuleIso (φ : M ≅ N) (hM : ∀ x : X, IsTrivializedNear M x)
    (hN : ∀ x : X, IsTrivializedNear N x) (s : M.presheaf.stalk (genericPoint X))
    (Z : PrimeDivisor X) :
    orderOfVanishing N (AlgebraicGeometry.stalkLinearEquiv M N φ.hom (genericPoint X) s) Z =
      orderOfVanishing M s Z := by
  obtain ⟨a, ha⟩ := exists_isCoordinateAt (hM Z.genericPoint) s
  rw [orderOfVanishing_eq (hN Z.genericPoint) (ha.ofModuleIso φ),
    orderOfVanishing_eq (hM Z.genericPoint) ha]

/-- **The Weil divisor of a meromorphic section is unchanged by an isomorphism of modules.** -/
theorem weilDivisorOfMeromorphicSection_ofModuleIso (φ : M ≅ N)
    (hM : ∀ x : X, IsTrivializedNear M x) (hN : ∀ x : X, IsTrivializedNear N x)
    (s : M.presheaf.stalk (genericPoint X)) :
    weilDivisorOfMeromorphicSection hN
        (AlgebraicGeometry.stalkLinearEquiv M N φ.hom (genericPoint X) s) =
      weilDivisorOfMeromorphicSection hM s :=
  Subtype.ext (funext fun Z ↦ orderOfVanishing_ofModuleIso φ hM hN s Z)

end Stacks.Divisors

namespace Stacks.Chow

open Stacks.Divisors

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] [IsLocallyNoetherian X] {k : ℤ}
  (hk : schemeDeltaDimension C p = ((k + 1 : ℤ) : EInt)) {M N : X.Modules}

/-- **The component cycle of the first Chern class is unchanged by an isomorphism of modules.** -/
theorem chernComponentCycle_ofModuleIso (φ : M ≅ N) (hM : ∀ x : X, IsTrivializedNear M x)
    (hN : ∀ x : X, IsTrivializedNear N x) (s : M.presheaf.stalk (genericPoint X)) :
    chernComponentCycle C p hk hN
        (AlgebraicGeometry.stalkLinearEquiv M N φ.hom (genericPoint X) s) =
      chernComponentCycle C p hk hM s :=
  Subtype.ext (congrArg weilDivisorAlgebraicCycle
    (weilDivisorOfMeromorphicSection_ofModuleIso φ hM hN s))

/-- **The class of the divisor cycle depends only on the isomorphism class of the module.** For
two isomorphic modules of rank one on an integral scheme of delta-dimension `k + 1`, the classes
in `A_k(X)` of the divisor cycles of any two nonzero meromorphic sections agree.

The cycle of the image of the first section under the isomorphism is the cycle of that section
(`Stacks.Chow.chernComponentCycle_ofModuleIso`), and the image is again nonzero, so Stacks 02SJ
(2) compares it with the second section. -/
theorem mk_chernComponentCycle_eq_of_moduleIso (φ : M ≅ N) (hM : ∀ x : X, IsTrivializedNear M x)
    (hN : ∀ x : X, IsTrivializedNear N x) {s : M.presheaf.stalk (genericPoint X)}
    {t : N.presheaf.stalk (genericPoint X)} (hs : s ≠ 0) (ht : t ≠ 0) :
    (QuotientAddGroup.mk (chernComponentCycle C p hk hM s) : chowGroup C p k) =
      QuotientAddGroup.mk (chernComponentCycle C p hk hN t) := by
  have hΦ : AlgebraicGeometry.stalkLinearEquiv M N φ.hom (genericPoint X) s ≠ 0 := fun h ↦
    hs ((AlgebraicGeometry.stalkLinearEquiv M N φ.hom (genericPoint X)).map_eq_zero_iff.1 h)
  rw [← chernComponentCycle_ofModuleIso C p hk φ hM hN s]
  exact mk_chernComponentCycle_eq C p hk hN hΦ ht

end Stacks.Chow

end
