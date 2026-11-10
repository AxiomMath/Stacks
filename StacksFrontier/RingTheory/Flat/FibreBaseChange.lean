module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.FlatHenselization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre of a module over the fibre of the base, across a base change

Let `R → A` and `R → R'` be ring homomorphisms with `R` and `R'` local and `R → R'` local, let
`T = A ⊗_R R'` be the pushout and let `A'` be a flat `T`-algebra.  Write

```
I  = 𝔪_R A  ⊆ A,     I' = 𝔪_{R'} A' ⊆ A'
```

for the two ideals cutting out the *fibres*, so that `A/I` and `A'/I'` are the local rings of the
two fibres.  This file proves that `A'/I'` is **faithfully flat** over `A/I`, and that for an
`A`-module `M` the fibre of the base change is the base change of the fibre,

```
(A' ⊗_A M) / I'(A' ⊗_A M)  =  (A'/I') ⊗_{A/I} (M/IM).
```

Together these say that flatness of `M/IM` over `A/I` is insensitive to the base change: it holds
if and only if the corresponding statement holds upstairs.

This is the commutative algebra behind the base-change invariance of condition (1) of
Stacks 05WY, and so of clauses (1) and (2) of Stacks 0CZS: in the application `R`, `A`, `R'`, `A'`
are the étale local rings of the four corners of a cartesian square of algebraic spaces at a
geometric point of the upper-left corner, flatness of `A'` over the pushout is
`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat`, and `M` is the geometric stalk of the
module being pulled back.

## Main results

* `Stacks.isPushout_quotient_maximalIdeal`: the fibre `A/𝔪_R A` is the base change `A ⊗_R κ_R` of
  the residue field — the quotient square is a pushout.
* `Stacks.flat_fibreQuotient_tensorFibre`: `A ⊗_R R'` modulo `𝔪_{R'}` is flat over `A/I`, being
  `(A/I) ⊗_{κ_R} κ_{R'}` and `κ_{R'}` a field extension of `κ_R`.
* `Stacks.faithfullyFlat_fibreQuotient`: `A'/I'` is faithfully flat over `A/I`.
* `Stacks.fibreQuotientBaseChangeEquiv`: `(A' ⊗_A M)/I'(A' ⊗_A M) = (A'/I') ⊗_{A/I} (M/IM)`.
* `Stacks.flat_fibreQuotient_iff`: flatness of the fibre of the module over the fibre of the base
  is the same condition upstairs and downstairs.

## Implementation notes

The one step that is not formal is the identification `T/𝔪_{R'} T = (A/I) ⊗_{κ_R} κ_{R'}`, and the
difficulty there is not the identification itself but its *linearity*: the two obvious routes
through `TensorProduct.AlgebraTensorModule.cancelBaseChange` are linear over `κ_{R'}`, whereas what
is needed is linearity over `A`, or rather over `A/I`.  `Algebra.IsPushout.cancelBaseChange` is the
cancellation on the other side and is linear over exactly the right ring: applied to the pushout
`T = A ⊗_R R'` it gives `T ⊗_{R'} κ_{R'} ≃ₗ[A] A ⊗_R κ_{R'}`, and applied to the pushout
`A/I = A ⊗_R κ_R` of `Stacks.isPushout_quotient_maximalIdeal` it gives
`(A/I) ⊗_{κ_R} κ_{R'} ≃ₗ[A] A ⊗_R κ_{R'}`.  Composing them and extending the scalars along the
surjection `A → A/I` gives the identification in the form the flatness argument consumes.

Faithful flatness is then flatness plus locality: both fibre rings are local, being quotients of
local rings by proper ideals, and the homomorphism between them is local because `A → A'` is.

## References

* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public section

open scoped TensorProduct
open IsLocalRing

universe u v

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Stacks

/-! ### The fibre of a ring is the base change of the residue field -/

/-- **The quotient square of a local ring is a pushout.**  For a local ring `R` and an
`R`-algebra `A`, the fibre `A / 𝔪_R A` is the base change `A ⊗_R κ_R` of the residue field.

This is `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` read as a pushout square. -/
@[ega "0 19.7.1" "partial", ega "IV 2.5.8.8" "special case", sga "1 III 1.7"]
theorem isPushout_quotient_maximalIdeal (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [IsLocalRing R] [Algebra R A] :
    letI : Algebra (R ⧸ maximalIdeal R) (A ⧸ (maximalIdeal R).map (algebraMap R A)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    Algebra.IsPushout R A (R ⧸ maximalIdeal R)
      (A ⧸ (maximalIdeal R).map (algebraMap R A)) := by
  let : Algebra (R ⧸ maximalIdeal R) (A ⧸ (maximalIdeal R).map (algebraMap R A)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R (R ⧸ maximalIdeal R)
      (A ⧸ (maximalIdeal R).map (algebraMap R A)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.IsPushout.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (maximalIdeal R)).symm
    (RingHom.ext fun z => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (maximalIdeal R)).symm
          ((1 : A) ⊗ₜ[R] Ideal.Quotient.mk (maximalIdeal R) r) =
        algebraMap R (A ⧸ (maximalIdeal R).map (algebraMap R A)) r
      change Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)) (r • (1 : A)) = _
      rw [Algebra.smul_def, mul_one]
      rfl)

/-! ### The two fibre ideals -/

section Ideals

variable (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [IsLocalRing R] [IsLocalRing R'] [Algebra R A] [Algebra R R'] [Algebra A A'] [Algebra R' A']
  [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [IsLocalHom (algebraMap R R')]

/-- **The fibre ideal downstairs generates less than the fibre ideal upstairs.**  The ideal
`𝔪_R A` generates, in a ring `A'` receiving both `A` and `R'` compatibly over `R`, an ideal
contained in `𝔪_{R'} A'`: it is generated by the image of `𝔪_R`, which lands inside `𝔪_{R'}`
because `R → R'` is a local homomorphism. -/
theorem fibreIdeal_map_le :
    ((maximalIdeal R).map (algebraMap R A)).map (algebraMap A A') ≤
      (maximalIdeal R').map (algebraMap R' A') := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R A A', IsScalarTower.algebraMap_eq R R' A',
    ← Ideal.map_map]
  exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le _)

/-- The fibre of `A'` is an algebra over the fibre of `A`, by
`Stacks.fibreIdeal_map_le`. -/
abbrev fibreAlgebra :
    Algebra (A ⧸ (maximalIdeal R).map (algebraMap R A))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.1 (fibreIdeal_map_le R A R' A'))

/-- The fibre of `A'` is a tower over the fibre of `A` and `A`. -/
theorem isScalarTower_fibreAlgebra :
    letI := fibreAlgebra R A R' A'
    IsScalarTower A (A ⧸ (maximalIdeal R).map (algebraMap R A))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) :=
  let := fibreAlgebra R A R' A'
  IsScalarTower.of_algebraMap_eq fun _ => rfl

end Ideals

/-! ### Flatness of the fibre of the pushout over the fibre of the base -/

section Flat

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [IsLocalRing R] [IsLocalRing R'] [Algebra R A] [Algebra R R']
  [IsLocalHom (algebraMap R R')]

/-- **The fibre of the pushout is flat over the fibre of the base.**  For `R` and `R'` local with
`R → R'` local, the pushout `T = A ⊗_R R'` modulo `𝔪_{R'} T` is a flat `A/𝔪_R A`-algebra.

Indeed `T/𝔪_{R'} T` is `(A/𝔪_R A) ⊗_{κ_R} κ_{R'}`, and `κ_{R'}` is a field extension of `κ_R`,
hence flat.  The identification is `Algebra.IsPushout.cancelBaseChange` twice, at the pushout
`T = A ⊗_R R'` and at the pushout `A/𝔪_R A = A ⊗_R κ_R` of
`Stacks.isPushout_quotient_maximalIdeal`; both readings are linear over `A`, and the scalars are
extended to `A/𝔪_R A` along the surjection `A → A/𝔪_R A`. -/
theorem flat_fibre_tensorProduct :
    letI := fibreAlgebra R A R' (A ⊗[R] R')
    Module.Flat (A ⧸ (maximalIdeal R).map (algebraMap R A))
      ((A ⊗[R] R') ⧸ (maximalIdeal R').map (algebraMap R' (A ⊗[R] R'))) := by
  let := fibreAlgebra R A R' (A ⊗[R] R')
  have := isScalarTower_fibreAlgebra R A R' (A ⊗[R] R')
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let : Field (R' ⧸ maximalIdeal R') := Ideal.Quotient.field _
  let : Algebra (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R') :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.1 (IsLocalRing.map_maximalIdeal_le (algebraMap R R')))
  have : IsScalarTower R (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra (R ⧸ maximalIdeal R) (A ⧸ (maximalIdeal R).map (algebraMap R A)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R (R ⧸ maximalIdeal R) (A ⧸ (maximalIdeal R).map (algebraMap R A)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := isPushout_quotient_maximalIdeal R A
  have e1 := Algebra.IsPushout.cancelBaseChange R A R' (A ⊗[R] R') (R' ⧸ maximalIdeal R')
  have e2 := Algebra.IsPushout.cancelBaseChange R A (R ⧸ maximalIdeal R)
    (A ⧸ (maximalIdeal R).map (algebraMap R A)) (R' ⧸ maximalIdeal R')
  have e3 := LinearEquiv.restrictScalars A
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⊗[R] R')
      (maximalIdeal R')).toLinearEquiv
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.extendScalarsOfSurjective (R := A)
      (S := A ⧸ (maximalIdeal R).map (algebraMap R A)) Ideal.Quotient.mk_surjective
      (e3 ≪≫ₗ e1 ≪≫ₗ e2.symm))

end Flat

/-- **Flatness passes to the fibres.**  For a flat `C`-algebra `D` and an ideal `J` of `C`, the
quotient `D / J D` is flat over `C / J`, being the base change `(C/J) ⊗_C D`. -/
theorem flat_quotient_map (C D : Type u) [CommRing C] [CommRing D] [Algebra C D]
    [Module.Flat C D] (J : Ideal C) :
    Module.Flat (C ⧸ J) (D ⧸ J.map (algebraMap C D)) :=
  Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor D J).toLinearEquiv

/-- **Flatness of the fibre of a module over a fibre of its base ring depends only on the
isomorphism class of the module.** -/
theorem flat_quotSMul_iff_of_linearEquiv {C : Type u} [CommRing C] (P : Ideal C)
    {N N' : Type v} [AddCommGroup N] [Module C N] [AddCommGroup N'] [Module C N']
    (e : N ≃ₗ[C] N') :
    Module.Flat (C ⧸ P) (N ⧸ P • (⊤ : Submodule C N)) ↔
      Module.Flat (C ⧸ P) (N' ⧸ P • (⊤ : Submodule C N')) := by
  have eq : (N ⧸ P • (⊤ : Submodule C N)) ≃ₗ[C ⧸ P] (N' ⧸ P • (⊤ : Submodule C N')) :=
    LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      (Submodule.Quotient.equiv _ _ e (by
        rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]))
  exact ⟨fun h => have := h; Module.Flat.of_linearEquiv eq.symm,
    fun h => have := h; Module.Flat.of_linearEquiv eq⟩

/-! ### Faithful flatness of the fibre of a flat base change -/

section BaseChange

variable (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [IsLocalRing R] [IsLocalRing R'] [IsLocalRing A] [IsLocalRing A']
  [Algebra R A] [Algebra R R'] [Algebra A A'] [Algebra R' A'] [Algebra R A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [IsLocalHom (algebraMap R R')] [IsLocalHom (algebraMap R A)]
  [IsLocalHom (algebraMap R' A')] [IsLocalHom (algebraMap A A')]
  [Algebra (A ⊗[R] R') A']
  [IsScalarTower A (A ⊗[R] R') A'] [IsScalarTower R' (A ⊗[R] R') A']

omit [IsLocalRing R] [IsLocalRing A] [IsLocalRing A'] [Algebra A A'] [Algebra R A']
  [IsScalarTower R A A'] [IsScalarTower R R' A'] [IsLocalHom (algebraMap R R')]
  [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap R' A')] [IsLocalHom (algebraMap A A')]
  [IsScalarTower A (A ⊗[R] R') A'] in
/-- The fibre ideal of `A'` is generated by the fibre ideal of the pushout `A ⊗_R R'`. -/
theorem fibreIdeal_eq_map_tensorProduct :
    (maximalIdeal R').map (algebraMap R' A') =
      ((maximalIdeal R').map (algebraMap R' (A ⊗[R] R'))).map
        (algebraMap (A ⊗[R] R') A') := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R' (A ⊗[R] R') A']

/-- The fibre of a local ring map is a local ring: the fibre ideal is contained in the maximal
ideal, so the quotient is a nontrivial quotient of a local ring. -/
theorem isLocalRing_fibre :
    IsLocalRing (A ⧸ (maximalIdeal R).map (algebraMap R A)) :=
  have : Nontrivial (A ⧸ (maximalIdeal R).map (algebraMap R A)) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
        (IsLocalRing.map_maximalIdeal_le (algebraMap R A)))
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- Reduction modulo the fibre ideal is a local homomorphism, the fibre ideal being contained in
the maximal ideal. -/
theorem isLocalHom_mk_fibreIdeal :
    IsLocalHom (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A))) :=
  isLocalHom_of_le_jacobson_bot _
    ((IsLocalRing.map_maximalIdeal_le (algebraMap R A)).trans
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal (R := A) ⊥ bot_ne_top).symm))

/-- **The fibre of a flat base change is faithfully flat over the fibre of the base.**

Flatness is the composite of two steps: the fibre of the pushout `A ⊗_R R'` is flat over the
fibre of `A` (`Stacks.flat_fibre_tensorProduct`), and the fibre of `A'` is flat over the fibre of
the pushout, because `A'` is flat over the pushout and the fibre ideal of `A'` is generated by
that of the pushout (`Stacks.flat_quotient_map`).  Faithfulness is then locality: both fibre rings
are local and the homomorphism between them is local, because `A → A'` is. -/
theorem faithfullyFlat_fibre [Module.Flat (A ⊗[R] R') A'] :
    letI := fibreAlgebra R A R' A'
    Module.FaithfullyFlat (A ⧸ (maximalIdeal R).map (algebraMap R A))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) := by
  let := fibreAlgebra R A R' A'
  have := isScalarTower_fibreAlgebra R A R' A'
  let := fibreAlgebra R A R' (A ⊗[R] R')
  have := isScalarTower_fibreAlgebra R A R' (A ⊗[R] R')
  have := flat_fibre_tensorProduct R A R'
  let : Algebra ((A ⊗[R] R') ⧸ (maximalIdeal R').map (algebraMap R' (A ⊗[R] R')))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.map_le_iff_le_comap.1
        (le_of_eq (fibreIdeal_eq_map_tensorProduct R A R' A').symm))
  have : IsScalarTower (A ⊗[R] R')
      ((A ⊗[R] R') ⧸ (maximalIdeal R').map (algebraMap R' (A ⊗[R] R')))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (A ⊗[R] R')
      ((A ⊗[R] R') ⧸ (maximalIdeal R').map (algebraMap R' (A ⊗[R] R')))
      (A' ⧸ ((maximalIdeal R').map (algebraMap R' (A ⊗[R] R'))).map
        (algebraMap (A ⊗[R] R') A')) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (A ⧸ (maximalIdeal R).map (algebraMap R A))
      ((A ⊗[R] R') ⧸ (maximalIdeal R').map (algebraMap R' (A ⊗[R] R')))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) :=
    IsScalarTower.of_algebraMap_eq fun z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact congrArg (Ideal.Quotient.mk _) (IsScalarTower.algebraMap_apply A (A ⊗[R] R') A' a)
  have : Module.Flat ((A ⊗[R] R') ⧸ (maximalIdeal R').map (algebraMap R' (A ⊗[R] R')))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) :=
    have := flat_quotient_map (A ⊗[R] R') A'
      ((maximalIdeal R').map (algebraMap R' (A ⊗[R] R')))
    Module.Flat.of_linearEquiv
      (LinearEquiv.extendScalarsOfSurjective (R := A ⊗[R] R') Ideal.Quotient.mk_surjective
        (LinearEquiv.restrictScalars (A ⊗[R] R')
          (Submodule.quotEquivOfEq _ _ (fibreIdeal_eq_map_tensorProduct R A R' A'))))
  have : Module.Flat (A ⧸ (maximalIdeal R).map (algebraMap R A))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) :=
    Module.Flat.trans _
      ((A ⊗[R] R') ⧸ (maximalIdeal R').map (algebraMap R' (A ⊗[R] R'))) _
  have := isLocalRing_fibre R A
  have := isLocalRing_fibre R' A'
  have := isLocalHom_mk_fibreIdeal R' A'
  have : IsLocalHom (algebraMap (A ⧸ (maximalIdeal R).map (algebraMap R A))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A'))) := by
    constructor
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact (isUnit_of_map_unit (algebraMap A A') a
      (isUnit_of_map_unit (Ideal.Quotient.mk _) _ hz)).map (Ideal.Quotient.mk _)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- **The fibre of a base change of modules is the base change of the fibre.**  For an
`A`-module `M`,

```
(A' ⊗_A M) / 𝔪_{R'}(A' ⊗_A M)  =  (A'/𝔪_{R'} A') ⊗_{A/𝔪_R A} (M/𝔪_R M).
```

Both sides are `(A'/𝔪_{R'} A') ⊗_A M`: on the left because `𝔪_R M` already dies in the base
change, on the right by cancelling the base change along `A → A'`.  This is the shape of
`TensorProduct.quotSMulBaseChangeEquiv` with the two fibre ideals in place of an ideal and its
extension. -/
noncomputable def fibreBaseChangeEquiv (M : Type v) [AddCommGroup M] [Module A M] :
    letI := fibreAlgebra R A R' A'
    (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) ⊗[
        A ⧸ (maximalIdeal R).map (algebraMap R A)]
        (M ⧸ (maximalIdeal R).map (algebraMap R A) • (⊤ : Submodule A M)) ≃ₗ[
      A' ⧸ (maximalIdeal R').map (algebraMap R' A')]
      (A' ⊗[A] M) ⧸ ((maximalIdeal R').map (algebraMap R' A')) •
        (⊤ : Submodule A' (A' ⊗[A] M)) :=
  letI := fibreAlgebra R A R' A'
  haveI := isScalarTower_fibreAlgebra R A R' A'
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (TensorProduct.quotTensorEquivQuotSMulOverQuotient
          ((maximalIdeal R).map (algebraMap R A)) M)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange A
      (A ⧸ (maximalIdeal R).map (algebraMap R A))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A'))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) M ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A A'
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A'))
      (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) M).symm ≪≫ₗ
    TensorProduct.quotTensorEquivQuotSMulOverQuotient
      ((maximalIdeal R').map (algebraMap R' A')) (A' ⊗[A] M)

/-- **Flatness of the fibre of a module over the fibre of the base is insensitive to a flat base
change.**  For an `A`-module `M`, the fibre `M/𝔪_R M` is flat over the fibre `A/𝔪_R A` if and only
if the fibre `(A' ⊗_A M)/𝔪_{R'}(A' ⊗_A M)` of the base change is flat over the fibre
`A'/𝔪_{R'} A'`.

The fibre of the base change is the base change of the fibre along the faithfully flat map of
fibre rings (`Stacks.fibreBaseChangeEquiv` and `Stacks.faithfullyFlat_fibre`); flatness then
ascends by base change and descends by Stacks 0584 (2). -/
theorem flat_fibre_iff [Module.Flat (A ⊗[R] R') A']
    (M : Type v) [AddCommGroup M] [Module A M] :
    letI := fibreAlgebra R A R' A'
    (Module.Flat (A' ⧸ (maximalIdeal R').map (algebraMap R' A'))
        ((A' ⊗[A] M) ⧸ ((maximalIdeal R').map (algebraMap R' A')) •
          (⊤ : Submodule A' (A' ⊗[A] M))) ↔
      Module.Flat (A ⧸ (maximalIdeal R).map (algebraMap R A))
        (M ⧸ (maximalIdeal R).map (algebraMap R A) • (⊤ : Submodule A M))) := by
  let := fibreAlgebra R A R' A'
  have := isScalarTower_fibreAlgebra R A R' A'
  have := faithfullyFlat_fibre R A R' A'
  have e := fibreBaseChangeEquiv R A R' A' M
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : Module.Flat (A' ⧸ (maximalIdeal R').map (algebraMap R' A'))
        ((A' ⧸ (maximalIdeal R').map (algebraMap R' A')) ⊗[
          A ⧸ (maximalIdeal R).map (algebraMap R A)]
          (M ⧸ (maximalIdeal R).map (algebraMap R A) • (⊤ : Submodule A M))) :=
      Module.Flat.of_linearEquiv e
    have : Module.Flat (A ⧸ (maximalIdeal R).map (algebraMap R A))
        ((A' ⧸ (maximalIdeal R').map (algebraMap R' A')) ⊗[
          A ⧸ (maximalIdeal R).map (algebraMap R A)]
          (M ⧸ (maximalIdeal R).map (algebraMap R A) • (⊤ : Submodule A M))) :=
      Module.Flat.trans _ (A' ⧸ (maximalIdeal R').map (algebraMap R' A')) _
    exact (Module.Flat.tensorProduct_iff_of_faithfullyFlat
      (R := A ⧸ (maximalIdeal R).map (algebraMap R A))
      (S := A ⧸ (maximalIdeal R).map (algebraMap R A))
      (S' := A' ⧸ (maximalIdeal R').map (algebraMap R' A'))
      (M := M ⧸ (maximalIdeal R).map (algebraMap R A) • (⊤ : Submodule A M))).1 inferInstance
  · have := h
    exact Module.Flat.of_linearEquiv e.symm

end BaseChange

end Stacks
