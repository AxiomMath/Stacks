module

public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantStalkColength
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismDivisorBound

/-!
# The determinant line bundles differ by at most `min s r` copies of the divisor

This is the second assertion of [Stacks, Tag 0B3T] at the point where it has become a statement
about one point: the determinant comparison map `σ(f, r)` of a morphism `f : F ⟶ F'` of modules
on an integral locally Noetherian scheme, nonzero and a stalkwise epimorphism away from an
integral effective Cartier divisor `D`, exhibits the determinant of `F'` as the twist of the
determinant of `F` by `D ^ k` with `k ≤ min s r`.

The exponent is bounded by combining
`AlgebraicGeometry.exists_pow_le_tensorIso_of_surjective_stalk_off`, which bounds it by the
colength of the stalk map at the generic point of `D`, with
`AlgebraicGeometry.length_quotient_range_map_detMap_le_min`, which bounds that colength by
`min s r`.

## Main results

* `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap`: **the bounded Cartier twist**, from
  hypotheses stated at the generic point of the divisor.

## Implementation notes

**No `@[stacks]` attribute.** The hypotheses at the generic point — that the local ring there is
a discrete valuation ring, that the cokernel of the stalk map of `f` is `κ ^ s`, that the
torsion-free quotients of the stalks have rank `r`, that the determinant modules are invertible,
that `σ(f, r)` is nonzero and a stalkwise epimorphism off `D` — are taken as given here, so what
is stated here is a step of the proof and not the assertion. On the regular integral surface of
the tag they follow from the right-exact sequence and the local freeness of its terms, and that
derivation **is** in the library, downstream: the prime divisor and the discrete valuation ring
at its generic point are supplied by
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap_of_isEffectiveCartierDivisor` of
`StacksFrontier/AlgebraicGeometry/Divisors/DeterminantTwistBoundCartier.lean`, the cokernel
identification by `AlgebraicGeometry.linearEquiv_quotient_range_stalkHom_fin` of
`StacksFrontier/AlgebraicGeometry/Divisors/DivisorStalkResidueCokernel.lean`, and the fully derived
assertion, which carries the tag, is
`AlgebraicGeometry.exists_reflexiveHull_exteriorPower_iso_tensor_cartier` of
`StacksFrontier/AlgebraicGeometry/Divisors/DeterminantTwistBoundDivisorQuotient.lean`. An earlier
version of this paragraph said that derivation is not in the library; that is false.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry

open Scheme.Modules Stacks.SheafOfModules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {F F' : X.Modules} (f : F ⟶ F')
  (r s : ℕ)
  [(exteriorPower F (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F (r : ℤ))).IsFinitePresentation]
  [(exteriorPower F' (r : ℤ)).IsFinitePresentation]
  [(dualSheaf (exteriorPower F' (r : ℤ))).IsFinitePresentation]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
    (reflexiveHull (exteriorPower F (r : ℤ)))]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
    (reflexiveHull (exteriorPower F' (r : ℤ)))]

/-- **The determinant comparison map of [Stacks, Tag 0B3T] twists by at most `min s r` copies of
the divisor.** -/
theorem exists_pow_le_min_tensorIso_detMap
    (D : X.IdealSheafData) (hDint : IsIntegral D.subscheme)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (Z : PrimeDivisor X) (hZ : Z.genericPoint ∈ ((D.support : Closeds X) : Set X))
    [IsDomain (ringStalk X.sheaf Z.genericPoint)]
    [IsLocalRing (ringStalk X.sheaf Z.genericPoint)]
    [IsDiscreteValuationRing (ringStalk X.sheaf Z.genericPoint)]
    [Module.Finite (ringStalk X.sheaf Z.genericPoint) (modStalk F Z.genericPoint)]
    [Module.Finite (ringStalk X.sheaf Z.genericPoint) (modStalk F' Z.genericPoint)]
    (e : (modStalk F' Z.genericPoint ⧸ LinearMap.range (stalkHom f Z.genericPoint))
      ≃ₗ[ringStalk X.sheaf Z.genericPoint]
        (Fin s → IsLocalRing.ResidueField (ringStalk X.sheaf Z.genericPoint)))
    (hr : Module.finrank (ringStalk X.sheaf Z.genericPoint)
      (modStalk F Z.genericPoint ⧸
        Submodule.torsion (ringStalk X.sheaf Z.genericPoint) (modStalk F Z.genericPoint)) = r)
    (hr' : Module.finrank (ringStalk X.sheaf Z.genericPoint)
      (modStalk F' Z.genericPoint ⧸
        Submodule.torsion (ringStalk X.sheaf Z.genericPoint) (modStalk F' Z.genericPoint)) = r)
    (hf : detMap f (r : ℤ) ≠ 0)
    (hoff : ∀ x : X, x ∉ D.supportSet →
      Function.Surjective (Stacks.ModuleStalk.mapFun (detMap f (r : ℤ)) x)) :
    ∃ k : ℕ, k ≤ min s r ∧ Nonempty ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
        (X.ringCatSheaf.property)⟩).obj ((Stacks.Divisors.invertibleSheaf' (D ^ k)))).obj
          ((reflexiveHull (exteriorPower F (r : ℤ))))) ≅
      reflexiveHull (exteriorPower F' (r : ℤ))) :=
  exists_pow_le_tensorIso_of_surjective_stalk_off _ _ D hDint hD Z hZ hf (min s r)
    (length_quotient_range_map_detMap_le_min f r s Z.genericPoint e hr hr') hoff

end AlgebraicGeometry

end
