module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomCorepresentability
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChange

/-!
# Base change of relative dualizing complexes, from the morphism groups

Let `R → A` be flat of finite presentation, `R → R'` a ring map, `A' = A ⊗[R] R'`,
`B' = A' ⊗[R'] A'`, `K` a relative dualizing complex for `R → A`, `K' = K ⊗ᴸ_A A'` and
`Y = K' ⊗ᴸ_{A'} B'`. The criterion `Dualizing.isRelativeDualizingComplex_baseChange_of_homology`
is stated on the cohomology of `RHom_{B'}(A', Y)`. Since the cohomology of derived Hom is
corepresented by the unit, `A'`-linearly, the same criterion holds with the cohomology replaced
by the morphism groups `Hom_{D(B')}(A'[0], Y⟦j⟧)`.

## Main definitions

* `Dualizing.diagonalBaseChangeTarget`: the object `Y = K' ⊗ᴸ_{A'} B'` of `D(B')`.

## Main results

* `Dualizing.isRelativeDualizingComplex_baseChange_of_hom`: if there are no nonzero morphisms
  `A'[0] ⟶ Y⟦j⟧` for `j ≠ 0` and the morphisms `A'[0] ⟶ Y` are `A'` itself, then `K'` is a
  relative dualizing complex for `R' → A'`. Here `A'[0]` is `A'`, viewed as a `B'`-module through
  the multiplication map `Δ'`, placed in degree zero.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Dualizing.smulHomRestrictedUnitSingle

universe u

namespace Dualizing

noncomputable section

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R'] [Module.Flat R A] [Algebra.FinitePresentation R A]

/-- The object `Y = (K ⊗ᴸ_A A') ⊗ᴸ_{A'} B'` of `D(B')`, where `A' = A ⊗[R] R'` and
`B' = A' ⊗[R'] A'`. -/
abbrev diagonalBaseChangeTarget (K : DerivedCategory (ModuleCat.{u} A)) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))) :=
  letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  (diagonalDerivedExtension R' (A ⊗[R] R')).obj
    ((totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)

/-- Let `R → A` be flat of finite presentation, let `K` be a relative dualizing complex for
`R → A` and let `R → R'` be any ring map. Put `A' = A ⊗[R] R'`, `B' = A' ⊗[R'] A'`,
`K' = K ⊗ᴸ_A A'` and `Y = K' ⊗ᴸ_{A'} B'`. If there is no nonzero morphism `A'[0] ⟶ Y⟦j⟧` in
`D(B')` for `j ≠ 0`, and the morphisms `A'[0] ⟶ Y` are `A'` as an `A'`-module, then `K'` is a
relative dualizing complex for `R' → A'`.

Here `A'[0]` is `A'`, viewed as a `B'`-module through the multiplication map `Δ' : B' → A'` and
placed in degree zero, and `A'` acts on the morphism groups through the source
(`Dualizing.smulHomRestrictedUnitSingle`). -/
theorem isRelativeDualizingComplex_baseChange_of_hom
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hvan : letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
      ∀ j : ℤ, j ≠ 0 →
        Subsingleton (restrictedUnitSingle
            (Algebra.TensorProduct.lmul' R' :
              (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
          (CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).obj
              (diagonalBaseChangeTarget R A R' K)))
    (h0 : letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
      (restrictedUnitSingle
            (Algebra.TensorProduct.lmul' R' :
              (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
          (CategoryTheory.shiftFunctor
            (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) (0 : ℤ)).obj
              (diagonalBaseChangeTarget R A R' K)) ≃ₗ[A ⊗[R] R'] (A ⊗[R] R')) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K) := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  exact isRelativeDualizingComplex_baseChange_of_homology R A R' K hK
    (fun j hj => isZero_homology_derivedHom_of_subsingleton _ _ j (hvan j hj))
    (nonempty_homology_derivedHom_iso _ _ 0 h0)

end

end Dualizing

end
