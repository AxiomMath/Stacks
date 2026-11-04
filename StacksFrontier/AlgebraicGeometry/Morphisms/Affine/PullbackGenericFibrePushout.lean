module

public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.PullbackTensorProduct
public import StacksFrontier.RingTheory.TensorProduct.GenericFibreComponents

/-!
# The generic fibre of an affine base change as a pushout of fields

Let
```
U --snd--> X
|fst       |q
V --b-->   Y
```
be a cartesian square of schemes with `X`, `V` and `Y` affine, let `Y` and `X` be integral with
`q` dominant and integral, and let `V` be integral. Write `A = Γ(Y)`, `O = Γ(V)`, `B = Γ(X)` and
`C = Γ(U)`, let `K`, `F` and `L` be the function fields of `Y`, `V` and `X`, and let `T` be the
localization of `C` at the nonzero elements of `O` — the ring of the fibre of `U → V` over the
generic point of `V`. This file proves

`T = F ⊗_K L`,

that is `Algebra.IsPushout K F L T`: **the generic fibre of `U → V` is the base change of the
generic fibre `L` of `X → Y` along `K → F`.**

This is the hypothesis `Algebra.IsPushout K F L T` of
`Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout`, discharged whenever the base
is an affine scheme.

## Main results

* `AlgebraicGeometry.algebraIsPushout_appTop_of_isPullback`: **the square of global sections of a
  cartesian square of schemes with three affine corners is a pushout of algebras.** This is
  Mathlib's `AlgebraicGeometry.isPushout_appTop_of_isPullback`, which states the pushout in
  `CommRingCat`, transported to `Algebra.IsPushout` by
  `CommRingCat.isPushout_iff_isPushout`.
* `Stacks.GenericFibre.isPushout_of_localization`: **the generic fibre of `U → V` is the base
  change of `C` along `O → F`.** Inverting the nonzero elements of `O` in `C` is the base change
  of `C` along the localization `O → F`.
* `Stacks.GenericFibre.isPushout_fractionRing_of_isIntegral`: **the generic fibre of an integral
  dominant morphism of integral affine schemes is `Spec L`.** For `B` a domain integral over the
  domain `A` with `A → B` injective, the fraction field `L` of `B` is the base change of `B`
  along `A → K`.
* `Stacks.GenericFibre.isPushout_fractionRing_of_isPushout`: **the identification, for a base
  which is an affine scheme.** Given `C` presented as the base change `O ⊗_A B` — which
  `AlgebraicGeometry.algebraIsPushout_appTop_of_isPullback` supplies for a cartesian square of
  affine schemes — and `T` a localization of `C` at the nonzero elements of `O`, the ring `T` is
  the base change of `L` along `K → F`.

## Implementation notes

**The shape of the proof is two applications of `Algebra.IsPushout.comp_iff`** to the two
diagrams
```
  A  →  O  →  F            A  →  K  →  F
  ↓     ↓     ↓            ↓     ↓     ↓
  B  →  C  →  T            B  →  L  →  T
```
In the first, the left square is the hypothesis `Algebra.IsPushout A O B C` — the cartesian
square of affine schemes — and the right square is
`Stacks.GenericFibre.isPushout_of_localization`, so the big rectangle `Algebra.IsPushout A F B T`
holds. In the second, the left square is
`Stacks.GenericFibre.isPushout_fractionRing_of_isIntegral` and the big rectangle is what the
first gave, so the right square `Algebra.IsPushout K F L T` holds. Geometrically the two
rectangles are the single identification `Spec T = X ×_Y Spec F`, read once as a fibre of
`U → V` and once as a fibre of `X → Y`.

**`C` is presented by a pushout rather than as a literal tensor product.** The statements of
`StacksFrontier.RingTheory.TensorProduct.GenericFibreComponents` are made for `C = O ⊗[A] B`, which
a consumer that obtains `U` as an affine scheme *representing* a fibre product does not have on
the nose; and `T` is an arbitrary localization rather than `F ⊗[K] L`, so that a consumer may use
whichever presentation of the generic fibre it has. Both choices are the ones of
`StacksFrontier.RingTheory.Localization.GenericFibreComponents`.

**What this does not supply: the same statement with `Y` an algebraic space.** In the proof of
Stacks 0EQ4 for algebraic spaces, `Y` is an algebraic space and has no affine open, so there is
no ring `A` with `Spec A ⊆ Y` and the chain above has no first column. The geometric input which
would replace it is the identification of the generic fibre of `X → Y` itself — that
`Spec R(X) = X ×_Y Spec R(Y)`, the space-level form of
`Stacks.GenericFibre.isPushout_fractionRing_of_isIntegral` — after which the single application
of `AlgebraicGeometry.algebraIsPushout_appTop_of_isPullback` to the cartesian square
```
Spec T  -->  Spec L
  |            |
Spec F  -->  Spec K
```
gives `Algebra.IsPushout R(Y) R(V_j) R(X) T`. That square is not available here: nothing in this
repository presents a fibre of a morphism of algebraic spaces over a point as the spectrum of a
ring. Note that `Spec R(Y)` *is* an object of the site — the residue field
`AlgebraicGeometry.Space.residueField` at the generic point lives in `Type u`, and
`AlgebraicGeometry.Space.residueFieldMorphism` is the monomorphism `Spec R(Y) ⟶ Y` — so the
obstruction is not a universe one; it is the missing identification of the ring of the fibre.

No Stacks tag is claimed. The source asserts the identification implicitly, in the proof of
Stacks 0EQ4, where it says that the `Mᵢ` of the field-theoretic lemma are the function fields of
the components of `V ×_Y X` dominating `V_j`, and omits its proof; there is no tag stating it.

## References

* [Stacks Project, Tag 01JO](https://stacks.math.columbia.edu/tag/01JO)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped nonZeroDivisors TensorProduct

universe u

namespace AlgebraicGeometry

variable {U X V Y : Scheme.{u}} {fst : U ⟶ V} {snd : U ⟶ X} {b : V ⟶ Y} {q : X ⟶ Y}
  [IsAffine X] [IsAffine V] [IsAffine Y]

/-- **The global sections of a cartesian square of schemes form a pushout of algebras.** For a
cartesian square `fst ≫ b = snd ≫ q` of schemes with `X`, `V` and `Y` affine, the ring
`Γ(U, 𝒪_U)` is the base change of `Γ(X, 𝒪_X)` along `Γ(Y, 𝒪_Y) → Γ(V, 𝒪_V)`.

This is Mathlib's `AlgebraicGeometry.isPushout_appTop_of_isPullback`, which states the same
square to be a pushout in `CommRingCat`, read as a pushout of algebras through
`CommRingCat.isPushout_iff_isPushout`. The content is the same as that of
`AlgebraicGeometry.tensorProductΓEquivOfIsPullback`; this form is the one a consumer needs when
it has to compose the square with another one, since `Algebra.IsPushout.comp_iff` is stated for
`Algebra.IsPushout`. -/
theorem algebraIsPushout_appTop_of_isPullback (h : IsPullback fst snd b q) :
    letI : Algebra Γ(Y, ⊤) Γ(V, ⊤) := b.appTop.hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := q.appTop.hom.toAlgebra
    letI : Algebra Γ(V, ⊤) Γ(U, ⊤) := fst.appTop.hom.toAlgebra
    letI : Algebra Γ(X, ⊤) Γ(U, ⊤) := snd.appTop.hom.toAlgebra
    letI : Algebra Γ(Y, ⊤) Γ(U, ⊤) := (fst ≫ b).appTop.hom.toAlgebra
    haveI : IsScalarTower Γ(Y, ⊤) Γ(V, ⊤) Γ(U, ⊤) :=
      .of_algebraMap_eq'
        (show (fst ≫ b).appTop.hom = fst.appTop.hom.comp b.appTop.hom by
          rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp])
    haveI : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) Γ(U, ⊤) :=
      .of_algebraMap_eq'
        (show (fst ≫ b).appTop.hom = snd.appTop.hom.comp q.appTop.hom by
          rw [h.w, Scheme.Hom.comp_appTop, CommRingCat.hom_comp])
    Algebra.IsPushout Γ(Y, ⊤) Γ(V, ⊤) Γ(X, ⊤) Γ(U, ⊤) := by
  algebraize [b.appTop.hom, q.appTop.hom, fst.appTop.hom, snd.appTop.hom, (fst ≫ b).appTop.hom]
  have : IsScalarTower Γ(Y, ⊤) Γ(V, ⊤) Γ(U, ⊤) :=
    .of_algebraMap_eq'
      (show (fst ≫ b).appTop.hom = fst.appTop.hom.comp b.appTop.hom by
        rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp])
  have : IsScalarTower Γ(Y, ⊤) Γ(X, ⊤) Γ(U, ⊤) :=
    .of_algebraMap_eq'
      (show (fst ≫ b).appTop.hom = snd.appTop.hom.comp q.appTop.hom by
        rw [h.w, Scheme.Hom.comp_appTop, CommRingCat.hom_comp])
  exact CommRingCat.isPushout_iff_isPushout.mp (isPushout_appTop_of_isPullback h)

end AlgebraicGeometry

namespace Stacks.GenericFibre

/-! ### The generic fibre of a localization -/

/-- **The generic fibre of `U → V` is the base change of `Γ(U)` along `Γ(V) → R(V)`.** Let `O`
be a commutative ring, `F` a localization of `O` at its nonzero elements, `C` an `O`-algebra and
`T` a localization of `C` at the image of the nonzero elements of `O`. Then `T = F ⊗_O C`.

Geometrically, with `V = Spec O` integral and `U = Spec C` a `V`-scheme: the fibre of `U → V`
over the generic point of `V` is the base change of `U` along `Spec R(V) → V`. This is
Mathlib's `Algebra.isPushout_of_isLocalization`, which is the statement that a localization is a
base change. -/
theorem isPushout_of_localization (O C T : Type*) [CommRing O] [CommRing C] [CommRing T]
    [Algebra O C] [Algebra C T] [IsLocalization (Algebra.algebraMapSubmonoid C O⁰) T]
    (F : Type*) [CommRing F] [Algebra O F] [IsFractionRing O F] [Algebra O T] [Algebra F T]
    [IsScalarTower O C T] [IsScalarTower O F T] :
    Algebra.IsPushout O F C T :=
  (Algebra.isPushout_of_isLocalization O⁰ F C T).symm

/-! ### The generic fibre of an integral dominant morphism of integral affine schemes -/

/-- **The generic fibre of an integral dominant morphism of integral affine schemes is the
spectrum of the function field of the source.** Let `A` be a domain with fraction field `K` and
let `B` be a domain integral over `A` with `A → B` injective and with fraction field `L`. Then
`L = K ⊗_A B`.

This is `IsLocalization.algebraMapSubmonoid_nonZeroDivisors_of_isIntegral` — the fraction field
of `B` is already the localization of `B` at the image of the nonzero elements of `A` — read as
a base change through Mathlib's `Algebra.isPushout_of_isLocalization`. Integrality is what makes
it true: for a merely affine dominant `X → Y` the ring of the generic fibre is a proper subring
of `R(X)`, already for `𝔸¹_K → Spec K`, where it is `K[t]` and not `K(t)`. -/
theorem isPushout_fractionRing_of_isIntegral (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.IsIntegral A B] (K : Type*) [Field K]
    [Algebra A K] [IsFractionRing A K] (L : Type*) [CommRing L] [Algebra B L]
    [IsFractionRing B L] [Algebra A L] [Algebra K L] [IsScalarTower A B L]
    [IsScalarTower A K L] :
    Algebra.IsPushout A K B L :=
  have := IsLocalization.algebraMapSubmonoid_nonZeroDivisors_of_isIntegral A B K L
  (Algebra.isPushout_of_isLocalization A⁰ K B L).symm

/-! ### The generic fibre of the base change as a pushout of function fields -/

section Pushout

variable (A O B C K F L T : Type*) [CommRing A] [IsDomain A] [CommRing O] [CommRing B]
  [IsDomain B] [CommRing C] [Field K] [CommRing F] [CommRing L] [CommRing T]
  [Algebra A O] [Algebra A B] [Algebra A C] [Algebra A F] [Algebra A T] [Algebra A K]
  [Algebra A L] [Algebra O C] [Algebra O F] [Algebra O T] [Algebra B C] [Algebra B L]
  [Algebra B T] [Algebra C T] [Algebra F T] [Algebra K F] [Algebra K L] [Algebra K T]
  [Algebra L T]
  [IsScalarTower A O C] [IsScalarTower A B C] [IsScalarTower A O F] [IsScalarTower A K F]
  [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A C T] [IsScalarTower A F T]
  [IsScalarTower A B T] [IsScalarTower A L T] [IsScalarTower O C T] [IsScalarTower O F T]
  [IsScalarTower B C T] [IsScalarTower B L T] [IsScalarTower K F T] [IsScalarTower K L T]
  [FaithfulSMul A B] [Algebra.IsIntegral A B] [IsFractionRing A K] [IsFractionRing O F]
  [IsFractionRing B L] [IsLocalization (Algebra.algebraMapSubmonoid C O⁰) T]

/-- **The generic fibre of the base change is the base change of the generic fibre.** Let
`A` be a domain with fraction field `K`, let `B` be a domain integral over `A` with `A → B`
injective and with fraction field `L`, let `O` be an `A`-algebra with fraction field `F`, let
`C` be the base change `O ⊗_A B`, and let `T` be a localization of `C` at the nonzero elements
of `O`. Then `T = F ⊗_K L`, that is `Algebra.IsPushout K F L T`.

Geometrically, with `Y = Spec A` and `X = Spec B` integral and `q : X → Y` integral and
dominant, `V = Spec O` an integral `Y`-scheme and `U = V ×_Y X = Spec C`: the fibre of `U → V`
over the generic point of `V` is `Spec (R(V) ⊗_{R(Y)} R(X))`. The hypothesis
`Algebra.IsPushout A O B C` is what
`AlgebraicGeometry.algebraIsPushout_appTop_of_isPullback` supplies for a cartesian square of
affine schemes, so a consumer which obtains `U` as an affine scheme representing a fibre product
— rather than as `Spec (O ⊗_A B)` on the nose — can use this.

This discharges the hypothesis `Algebra.IsPushout K F L T` of
`Stacks.GenericFibre.norm_eq_finprod_norm_quotient_of_isPushout` whenever the base is an affine
scheme.

The proof chains the two rectangles `A → O → F` over `B → C → T` and `A → K → F` over
`B → L → T` with `Algebra.IsPushout.comp_iff`: the first gives `Algebra.IsPushout A F B T` from
the hypothesis and `Stacks.GenericFibre.isPushout_of_localization`, and the second then turns it
into the conclusion, its left square being
`Stacks.GenericFibre.isPushout_fractionRing_of_isIntegral`. -/
theorem isPushout_fractionRing_of_isPushout [Algebra.IsPushout A O B C] :
    Algebra.IsPushout K F L T :=
  have : Algebra.IsPushout O F C T := isPushout_of_localization O C T F
  have : Algebra.IsPushout A F B T :=
    (Algebra.IsPushout.comp_iff A O B C (T := F) (T' := T)).mpr ‹_›
  have : Algebra.IsPushout A K B L := isPushout_fractionRing_of_isIntegral A B K L
  (Algebra.IsPushout.comp_iff A K B L (T := F) (T' := T)).mp ‹_›

end Pushout

end Stacks.GenericFibre

end
