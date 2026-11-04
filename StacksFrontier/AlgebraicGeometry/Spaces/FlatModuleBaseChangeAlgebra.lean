module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.IsTensorProduct
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra

/-!
# Flatness of a base change of modules over a pushout of rings

Let `R → A` and `R → S` be ring homomorphisms, let `P = A ⊗_R S` be the pushout, and let `T` be a
flat `P`-algebra.  For an `A`-module `M` which is flat over `R`, the base change `T ⊗_A M` is flat
over `S`.  This is the commutative algebra behind the base-change clause of Stacks 05VW: there
`R`, `A`, `S` and `T` are the étale local rings of the four corners of a cartesian square of
algebraic spaces at a geometric point of the upper-left corner, and `M` is the geometric stalk of
the module being pulled back.

Two companion results read a flatness assertion about an extension of scalars
`ModuleCat.extendScalars` as one about a tensor product, and transport one along an isomorphism of
modules.

## Main results

* `Module.Flat.tensorProduct_of_isPushout`: flatness over `S` of `T ⊗_A M`.
* `ModuleCat.flat_extendScalars_obj_iff`: the carrier of `(extendScalars γ).obj M` is the tensor
  product `A' ⊗_A M`, with the same module structure, so flatness over a third ring acting through
  `A'` is the same assertion for both spellings.
* `ModuleCat.flat_iff_of_iso`: isomorphic `A'`-modules are flat together over a ring acting
  through `A'`.

## Implementation notes

The proof of `Module.Flat.tensorProduct_of_isPushout` factors the base change `T ⊗_A M` through
the pushout: `T ⊗_A M = T ⊗_P (P ⊗_A M)` and `P ⊗_A M = S ⊗_R M`, the latter flat over `S`
because `M` is flat over `R`.  Flatness of `T` over `P` then carries it to `T ⊗_P (P ⊗_A M)` by
Stacks 0584 (1).

`ModuleCat.flat_extendScalars_obj_iff` is `Iff.rfl`: the module structure that
`ModuleCat.extendScalars` puts on `A' ⊗_A M` restricts scalars along `γ`, which is the module
structure `RingHom.toAlgebra` gives, and the action of the third ring is in both cases the one
obtained from the action of `A'` by composing with the homomorphism to `A'`.

## References

* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe v w

/-- **Flatness of a base change of modules over a pushout of rings.**  Let `R → A` and `R → S` be
ring homomorphisms, let `P` be the pushout `A ⊗_R S`, and let `T` be a flat `P`-algebra.  If an
`A`-module `M` is flat over `R`, then `T ⊗_A M` is flat over `S`.

Writing the base change in two steps, `T ⊗_A M = T ⊗_P (P ⊗_A M)`, the inner factor `P ⊗_A M` is
`S ⊗_R M` because `P` is the pushout, hence flat over `S`; flatness of `T` over `P` then gives the
assertion by Stacks 0584 (1). -/
theorem Module.Flat.tensorProduct_of_isPushout (R A S P T M : Type*)
    [CommRing R] [CommRing A] [CommRing S] [CommRing P] [CommRing T]
    [Algebra R A] [Algebra R S] [Algebra R P]
    [Algebra A P] [Algebra S P] [IsScalarTower R A P] [IsScalarTower R S P]
    [Algebra A T] [Algebra S T] [Algebra P T]
    [IsScalarTower A P T] [IsScalarTower S P T]
    [Algebra.IsPushout R S A P] [Module.Flat P T]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M] :
    Module.Flat S (T ⊗[A] M) := by
  have hP : Module.Flat S (P ⊗[A] M) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange R S A P M)
  have hT : Module.Flat S (T ⊗[P] (P ⊗[A] M)) := Module.Flat.tensorProduct_of_flat
  exact Module.Flat.of_linearEquiv
    ((AlgebraTensorModule.cancelBaseChange A P T T M).restrictScalars S).symm

/-- **Extension of scalars is the tensor product.**  For ring homomorphisms `γ : A → A'` and
`δ : R → A'` and an `A`-module `M`, flatness over `R` of the extension of scalars
`(extendScalars γ).obj M`, with `R` acting through `δ`, is flatness over `R` of `A' ⊗_A M`. -/
theorem ModuleCat.flat_extendScalars_obj_iff {R A A' : Type w}
    [CommRing R] [CommRing A] [CommRing A'] (γ : A →+* A') (δ : R →+* A') (M : ModuleCat.{v} A) :
    (letI : Module R ↥((ModuleCat.extendScalars γ).obj M) := Module.compHom _ δ;
      Module.Flat R ↥((ModuleCat.extendScalars γ).obj M)) ↔
      (letI : Algebra A A' := γ.toAlgebra;
        letI : Algebra R A' := δ.toAlgebra;
        Module.Flat R (A' ⊗[A] M)) :=
  Iff.rfl

/-- **Flatness of a module over a ring acting through the scalars depends only on the isomorphism
class of the module.**  Isomorphic `A'`-modules are flat together over a ring `R` acting through a
homomorphism `δ : R → A'`. -/
theorem ModuleCat.flat_iff_of_iso {R A' : Type w} [CommRing R] [CommRing A'] (δ : R →+* A')
    {N P : ModuleCat.{v} A'} (e : N ≅ P) :
    letI : Module R ↥N := Module.compHom _ δ
    letI : Module R ↥P := Module.compHom _ δ
    (Module.Flat R ↥N ↔ Module.Flat R ↥P) := by
  let : Module R ↥N := Module.compHom _ δ
  let : Module R ↥P := Module.compHom _ δ
  let : Algebra R A' := δ.toAlgebra
  let : IsScalarTower R A' ↥N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R A' ↥P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Flat.equiv_iff (e.toLinearEquiv.restrictScalars R)

end
