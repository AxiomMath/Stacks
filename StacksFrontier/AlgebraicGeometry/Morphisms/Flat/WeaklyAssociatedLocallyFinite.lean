module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.PullbackOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteTypeII.WeaklyAssociatedPointsFinite
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.RingEquiv

/-!
# Local finiteness of the weakly associated points of a scheme

The openness theorems for the flat locus of a morphism of finite type ask that the weakly
associated points of the base be *locally finite*: every point of the base has an open
neighbourhood meeting them in a finite set. This file records the two facts about that
hypothesis which the reduction to the affine case needs.

First, an affine scheme `Spec R` has finitely many weakly associated points as soon as the ring
`R` has finitely many weakly associated primes, so the geometric hypothesis follows from the
ring-theoretic one. Second, the hypothesis passes to open subschemes: the weakly associated
points of an open subscheme map into those of the ambient scheme, so an open neighbourhood
witnessing local finiteness upstairs restricts to one downstairs.

## Main results

* `AlgebraicGeometry.schemeWeaklyAssociatedPoints_spec_finite`: finitely many weakly associated
  primes of `R` give finitely many weakly associated points of `Spec R`.
* `AlgebraicGeometry.schemeWeaklyAssociatedPoints_map_of_isOpenImmersion`: the weakly associated
  points of an open subscheme map into those of the ambient scheme.
* `AlgebraicGeometry.exists_finite_schemeWeaklyAssociatedPoints_inter_of_isOpenImmersion`: local
  finiteness is inherited by an open subscheme.
* `AlgebraicGeometry.schemeWeaklyAssociatedPoints_finite_of_isIntegral`: an integral scheme has
  exactly one weakly associated point, its generic point.

## Implementation notes

The weakly associated points of a scheme are those of its structure sheaf
(`Stacks.Divisors.schemeWeaklyAssociatedPoints`), so the first result is the global-sections
case of `AlgebraicGeometry.weaklyAssociatedPrimes_sections_finite_iff` combined with the
identification of the global sections of `Spec R` with `R`. Transporting weakly associated
primes across that identification is `isWeaklyAssociatedPrime_map_of_semilinearEquiv`: a ring
isomorphism carries weakly associated primes to weakly associated primes, because it carries
the annihilator of an element to the annihilator of its image and is an order isomorphism on
ideals.

The second result uses that the structure sheaf of an open subscheme is the pullback of the
structure sheaf of the ambient scheme (`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`
together with `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), under which weak
association of points is
`AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 056M](https://stacks.math.columbia.edu/tag/056M)
* [Stacks Project, Tag 0EME](https://stacks.math.columbia.edu/tag/0EME)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- **The weakly associated points of an affine scheme.** If the ring `R` has only finitely many
weakly associated primes, then `Spec R` has only finitely many weakly associated points. -/
theorem schemeWeaklyAssociatedPoints_spec_finite (R : Type u) [CommRing R]
    (hR : (weaklyAssociatedPrimes R R).Finite) :
    (schemeWeaklyAssociatedPoints (Spec (CommRingCat.of R))).Finite := by
  refine ((weaklyAssociatedPrimes_sections_finite_iff
    (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) (isAffineOpen_top _)).mp ?_).subset
    fun x hx => ⟨hx, trivial⟩
  let e : (Γ(Spec (CommRingCat.of R), ⊤) : Type u) ≃+* R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  have hinj : Function.Injective
      (fun p : Ideal (Γ(Spec (CommRingCat.of R), ⊤) : Type u) => p.map e.toRingHom) :=
    fun a b hab => by
      simpa only [Ideal.comap_map_of_bijective e.toRingHom e.bijective] using
        congrArg (Ideal.comap e.toRingHom) hab
  exact (hR.preimage hinj.injOn).subset fun p hp =>
    isWeaklyAssociatedPrime_map_of_semilinearEquiv e e.toAddEquiv (fun r m => map_mul e r m) hp

/-- **Weakly associated points of an open subscheme.** A point weakly associated to an open
subscheme has weakly associated image in the ambient scheme. -/
theorem schemeWeaklyAssociatedPoints_map_of_isOpenImmersion {X S : Scheme.{u}} (j : X ⟶ S)
    [IsOpenImmersion j] {x : X} (hx : x ∈ schemeWeaklyAssociatedPoints X) :
    j.base x ∈ schemeWeaklyAssociatedPoints S := by
  let e : (Scheme.Modules.pullback j).obj (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app
      (SheafOfModules.unit S.ringCatSheaf)) ≪≫ Scheme.Modules.restrictUnitIso j
  exact (isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion j
    (SheafOfModules.unit S.ringCatSheaf) x).mp ((isWeaklyAssociatedPoint_iff_of_iso e x).mpr hx)

/-- **Local finiteness of the weakly associated points passes to an open subscheme.** If every
point of `S` has an open neighbourhood meeting the weakly associated points of `S` in a finite
set, the same holds for an open subscheme of `S`. -/
theorem exists_finite_schemeWeaklyAssociatedPoints_inter_of_isOpenImmersion {X S : Scheme.{u}}
    (j : X ⟶ S) [IsOpenImmersion j]
    (hS : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      (schemeWeaklyAssociatedPoints S ∩ (V : Set S)).Finite) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ (schemeWeaklyAssociatedPoints X ∩ (U : Set X)).Finite := by
  obtain ⟨V, hxV, hfin⟩ := hS (j.base x)
  refine ⟨j ⁻¹ᵁ V, hxV, ?_⟩
  exact (hfin.preimage j.isOpenEmbedding.injective.injOn).subset fun y hy =>
    ⟨schemeWeaklyAssociatedPoints_map_of_isOpenImmersion j hy.1, hy.2⟩

/-- **An integral scheme has finitely many weakly associated points.** On a reduced scheme the
weakly associated points are the generic points of the irreducible components, and an integral
scheme is irreducible, so there is exactly one. -/
theorem schemeWeaklyAssociatedPoints_finite_of_isIntegral (S : Scheme.{u}) [IsIntegral S] :
    (schemeWeaklyAssociatedPoints S).Finite := by
  have : IrreducibleSpace S :=
    ((isIntegral_iff_irreducibleSpace_and_isReduced S).mp inferInstance).1
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints, genericPoints_eq_singleton]
  exact Set.finite_singleton _

end AlgebraicGeometry
