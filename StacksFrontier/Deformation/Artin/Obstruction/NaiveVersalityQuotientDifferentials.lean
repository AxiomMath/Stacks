module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityEssentialSurjection
public import StacksFrontier.Deformation.BaseCategory.AugmentedPowQuotient
public import StacksFrontier.RingTheory.NaiveCotangent.DerivedSquareZeroExtension

/-!
# The base-change map of differentials along a square of quotients

Stacks 07YL produces a square-zero extension `A' → A` of `Λ`-algebras which "does not change
differentials modulo `𝔭`", that is for which `Deformation.Artin.differentialsBaseChangeMap`
`k ⊗_{A'} Ω_{A'/Λ} ⟶ k ⊗_A Ω_{A/Λ}` is bijective. Stacks 06H0, as read through
`Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_differentialsBaseChangeMap`,
needs the same bijectivity for the induced map of the *Artinian* quotients
`A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n`. This file makes that step.

The square

```
A' ───→ A
 │       │
 ↓       ↓
B' ───→ B
```

of `Λ`-algebras, with both vertical maps surjective with kernel inside the square of the kernel
of the augmentation onto `k`, has four base-change maps of differentials. Functoriality in the
tower (`Deformation.Artin.differentialsBaseChangeMap_comp`) factors the diagonal in two ways,
and the two vertical maps are bijective by
`Deformation.Artin.differentialsBaseChangeMap_bijective_of_ker_le_ker_sq`; so the bottom
horizontal map is bijective as soon as the top one is.

## Main results

* `Deformation.Artin.differentialsBaseChangeMap_bijective_of_square` — the abstract step: for a
  commuting square of `Λ`-algebras over `k` whose two vertical maps are surjective with kernel
  inside the square of the augmentation ideal, bijectivity of the top base-change map of
  differentials gives bijectivity of the bottom one.
* `Deformation.Artin.differentialsBaseChangeMap_bijective_powQuotient` — **the instance
  [Stacks, Tag 07YM] uses**: the square with vertical maps `A' → A' ⧸ (𝔭') ^ n` and
  `A → A ⧸ 𝔭 ^ n`, for `n ≥ 2` and `𝔭`, `𝔭'` the two augmentation ideals.

## Implementation notes

The abstract step takes the whole square's worth of algebra structures and scalar towers as
instance arguments — fourteen algebras and sixteen towers — rather than building them with
`letI` inside its own statement. That keeps the statement free of `letI` and lets the
instantiation choose them; it is the instantiation
`Deformation.Artin.differentialsBaseChangeMap_bijective_powQuotient` that carries the `letI`
block, exactly as
`Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_differentialsBaseChangeMap`
does, because the structures there depend on the algebra homomorphisms and so cannot be
instances.

The two factorisations of the diagonal `k ⊗_{A'} Ω_{A'/Λ} ⟶ k ⊗_B Ω_{B/Λ}` require one and the
same `Algebra A' B`, with *both* `IsScalarTower A' A B` and `IsScalarTower A' B' B`; that is
the commutativity of the square, and it is what the single instance argument `Algebra A' B`
together with those two towers expresses. In the instantiation that structure is therefore
*not* introduced by hand: instance synthesis already builds `Algebra A' (A ⧸ 𝔭 ^ n)` from
`Ideal.Quotient.algebra` and the `Algebra A' A` of `φ`, and a second copy built from the
composite algebra homomorphism, though equal to it, is not found by the searches that
elaborate the two towers.

The hypothesis `n ≥ 2` enters only through `Ideal.pow_le_pow_right`: the kernel of
`A' → A' ⧸ (𝔭') ^ n` is `(𝔭') ^ n`, which lies in `(𝔭') ^ 2`, and `𝔭'` is the kernel of the
augmentation of `A'` onto `k`. The instance argument `NeZero n` is implied by `n ≥ 2`; it is
taken as an instance because every declaration of
`StacksFrontier.Deformation.BaseCategory.AugmentedPowQuotient` that the conclusion mentions
already requires it.

## References

* [Stacks Project, Tag 06H0](https://stacks.math.columbia.edu/tag/06H0)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

universe u

namespace Deformation.Artin

/-! ### The abstract step -/

section Square

variable (Λ A' A B' B k : Type u) [CommRing Λ] [CommRing A'] [CommRing A] [CommRing B']
  [CommRing B] [CommRing k]
  [Algebra Λ A'] [Algebra Λ A] [Algebra Λ B'] [Algebra Λ B] [Algebra Λ k]
  [Algebra A' A] [Algebra A' B'] [Algebra A B] [Algebra B' B] [Algebra A' B]
  [Algebra A' k] [Algebra A k] [Algebra B' k] [Algebra B k]
  [IsScalarTower Λ A' A] [IsScalarTower Λ A' B'] [IsScalarTower Λ A B]
  [IsScalarTower Λ B' B] [IsScalarTower Λ A' B]
  [IsScalarTower A' B' B] [IsScalarTower A' A B]
  [IsScalarTower Λ A' k] [IsScalarTower Λ A k] [IsScalarTower Λ B' k] [IsScalarTower Λ B k]
  [IsScalarTower A' A k] [IsScalarTower A' B' k] [IsScalarTower A' B k]
  [IsScalarTower A B k] [IsScalarTower B' B k]

/-- **The base-change map of differentials along a square of quotients.** Let

```
A' ───→ A
 │       │
 ↓       ↓
B' ───→ B
```

be a commuting square of `Λ`-algebras over `k` in which the two vertical maps are surjective
with kernel contained in the square of the kernel of the augmentation onto `k`. If the top
horizontal map does not change differentials modulo `k`, neither does the bottom one.

The two vertical base-change maps are bijective by
`Deformation.Artin.differentialsBaseChangeMap_bijective_of_ker_le_ker_sq`, and
`Deformation.Artin.differentialsBaseChangeMap_comp` factors the diagonal both as
`A' → B' → B` and as `A' → A → B`; the second factorisation exhibits the diagonal as a
composite of two bijections, and cancelling the bijective `A' → B'` from the first leaves
`B' → B`. -/
public theorem differentialsBaseChangeMap_bijective_of_square
    (hA'B' : Function.Surjective (algebraMap A' B'))
    (hkerA' : RingHom.ker (algebraMap A' B') ≤ RingHom.ker (algebraMap A' k) ^ 2)
    (hAB : Function.Surjective (algebraMap A B))
    (hkerA : RingHom.ker (algebraMap A B) ≤ RingHom.ker (algebraMap A k) ^ 2)
    (htop : Function.Bijective (differentialsBaseChangeMap Λ A' A k)) :
    Function.Bijective (differentialsBaseChangeMap Λ B' B k) := by
  refine (Function.Bijective.of_comp_iff _
    (differentialsBaseChangeMap_bijective_of_ker_le_ker_sq Λ A' B' k hA'B' hkerA')).mp ?_
  rw [← LinearMap.coe_comp, differentialsBaseChangeMap_comp Λ A' B' B k,
    ← differentialsBaseChangeMap_comp Λ A' A B k, LinearMap.coe_comp]
  exact (differentialsBaseChangeMap_bijective_of_ker_le_ker_sq Λ A B k hAB hkerA).comp htop

end Square

/-! ### The instance of Stacks 07YM -/

section PowQuotient

open Deformation.ArtinianLocalAlgCat

variable {Λ k A' A : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  [CommRing A'] [CommRing A] [Algebra Λ A'] [Algebra Λ A]

/-- **The quotient transfer of [Stacks, Tag 07YL]'s bijectivity.** Let `A' → A` be a map of
`Λ`-algebras with compatible surjective augmentations onto a field `k`, let `𝔭 = Ker ε` and
`𝔭' = Ker ε'`, and let `n ≥ 2`. If `A' → A` does not change differentials modulo `k`, neither
does the induced map `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n`.

This is `Deformation.Artin.differentialsBaseChangeMap_bijective_of_square` at the square whose
vertical maps are the two quotient maps: each is surjective, and the kernel of
`A' → A' ⧸ (𝔭') ^ n` is `(𝔭') ^ n ≤ (𝔭') ^ 2`, the augmentation ideal being the kernel of
`A' ⟶ k`. Composed with
`Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_differentialsBaseChangeMap`
it says that `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` is an essential surjection of `𝒞_Λ`, which is the
contradiction the direction `(1) ⇒ (2)` of [Stacks, Tag 07YM] drives at. -/
@[stacks 07YM "A'/(𝔭') ^ n ⟶ A/𝔭 ^ n does not change differentials either"]
public theorem differentialsBaseChangeMap_bijective_powQuotient
    {ε' : A' →ₐ[Λ] k} {ε : A →ₐ[Λ] k} {φ : A' →ₐ[Λ] A} (hφ : ε.comp φ = ε')
    (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    letI : Algebra A' A := φ.toRingHom.toAlgebra
    letI : Algebra A' k := ε'.toRingHom.toAlgebra
    letI : Algebra A k := ε.toRingHom.toAlgebra
    letI : IsScalarTower Λ A' A := .of_algebraMap_eq fun l => (φ.commutes l).symm
    letI : IsScalarTower Λ A' k := .of_algebraMap_eq fun l => (ε'.commutes l).symm
    letI : IsScalarTower Λ A k := .of_algebraMap_eq fun l => (ε.commutes l).symm
    letI : IsScalarTower A' A k :=
      .of_algebraMap_eq fun a => (DFunLike.congr_fun hφ a).symm
    letI : Algebra (A' ⧸ RingHom.ker ε'.toRingHom ^ n) (A ⧸ RingHom.ker ε.toRingHom ^ n) :=
      (powQuotientMapAlgHom hφ n).toRingHom.toAlgebra
    letI : Algebra (A' ⧸ RingHom.ker ε'.toRingHom ^ n) k :=
      (powQuotientAug ε' n).toRingHom.toAlgebra
    letI : Algebra (A ⧸ RingHom.ker ε.toRingHom ^ n) k :=
      (powQuotientAug ε n).toRingHom.toAlgebra
    letI : IsScalarTower Λ (A' ⧸ RingHom.ker ε'.toRingHom ^ n)
        (A ⧸ RingHom.ker ε.toRingHom ^ n) :=
      .of_algebraMap_eq fun l => ((powQuotientMapAlgHom hφ n).commutes l).symm
    letI : IsScalarTower Λ (A' ⧸ RingHom.ker ε'.toRingHom ^ n) k :=
      .of_algebraMap_eq fun l => ((powQuotientAug ε' n).commutes l).symm
    letI : IsScalarTower Λ (A ⧸ RingHom.ker ε.toRingHom ^ n) k :=
      .of_algebraMap_eq fun l => ((powQuotientAug ε n).commutes l).symm
    letI : IsScalarTower (A' ⧸ RingHom.ker ε'.toRingHom ^ n)
        (A ⧸ RingHom.ker ε.toRingHom ^ n) k :=
      .of_algebraMap_eq fun b => (powQuotientAug_powQuotientMapAlgHom hφ n b).symm
    Function.Bijective (differentialsBaseChangeMap Λ A' A k) →
      Function.Bijective (differentialsBaseChangeMap Λ
        (A' ⧸ RingHom.ker ε'.toRingHom ^ n) (A ⧸ RingHom.ker ε.toRingHom ^ n) k) := by
  let : Algebra A' A := φ.toRingHom.toAlgebra
  let : Algebra A' k := ε'.toRingHom.toAlgebra
  let : Algebra A k := ε.toRingHom.toAlgebra
  let : IsScalarTower Λ A' A := .of_algebraMap_eq fun l => (φ.commutes l).symm
  let : IsScalarTower Λ A' k := .of_algebraMap_eq fun l => (ε'.commutes l).symm
  let : IsScalarTower Λ A k := .of_algebraMap_eq fun l => (ε.commutes l).symm
  let : IsScalarTower A' A k := .of_algebraMap_eq fun a => (DFunLike.congr_fun hφ a).symm
  let : Algebra (A' ⧸ RingHom.ker ε'.toRingHom ^ n) (A ⧸ RingHom.ker ε.toRingHom ^ n) :=
    (powQuotientMapAlgHom hφ n).toRingHom.toAlgebra
  let : Algebra (A' ⧸ RingHom.ker ε'.toRingHom ^ n) k :=
    (powQuotientAug ε' n).toRingHom.toAlgebra
  let : Algebra (A ⧸ RingHom.ker ε.toRingHom ^ n) k :=
    (powQuotientAug ε n).toRingHom.toAlgebra
  let : IsScalarTower Λ (A' ⧸ RingHom.ker ε'.toRingHom ^ n)
      (A ⧸ RingHom.ker ε.toRingHom ^ n) :=
    .of_algebraMap_eq fun l => ((powQuotientMapAlgHom hφ n).commutes l).symm
  let : IsScalarTower Λ (A' ⧸ RingHom.ker ε'.toRingHom ^ n) k :=
    .of_algebraMap_eq fun l => ((powQuotientAug ε' n).commutes l).symm
  let : IsScalarTower Λ (A ⧸ RingHom.ker ε.toRingHom ^ n) k :=
    .of_algebraMap_eq fun l => ((powQuotientAug ε n).commutes l).symm
  let : IsScalarTower (A' ⧸ RingHom.ker ε'.toRingHom ^ n)
      (A ⧸ RingHom.ker ε.toRingHom ^ n) k :=
    .of_algebraMap_eq fun b => (powQuotientAug_powQuotientMapAlgHom hφ n b).symm
  -- The remaining structures of the square.  `Algebra A' (A ⧸ 𝔭 ^ n)` is NOT introduced here:
  -- instance synthesis already produces it from `Ideal.Quotient.algebra` and the `Algebra A' A`
  -- above, and a second copy built from the composite algebra homomorphism, though equal to it,
  -- is not found by the search that elaborates the scalar towers below.
  let : IsScalarTower Λ A' (A' ⧸ RingHom.ker ε'.toRingHom ^ n) :=
    .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Λ A (A ⧸ RingHom.ker ε.toRingHom ^ n) :=
    .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower Λ A' (A ⧸ RingHom.ker ε.toRingHom ^ n) :=
    .of_algebraMap_eq fun l => by
      show Ideal.Quotient.mk _ (algebraMap Λ A l) =
        Ideal.Quotient.mk _ (φ (algebraMap Λ A' l))
      rw [φ.commutes]
  let : IsScalarTower A' (A' ⧸ RingHom.ker ε'.toRingHom ^ n)
      (A ⧸ RingHom.ker ε.toRingHom ^ n) := .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A' A (A ⧸ RingHom.ker ε.toRingHom ^ n) :=
    .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A' (A' ⧸ RingHom.ker ε'.toRingHom ^ n) k :=
    .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A (A ⧸ RingHom.ker ε.toRingHom ^ n) k :=
    .of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A' (A ⧸ RingHom.ker ε.toRingHom ^ n) k :=
    .of_algebraMap_eq fun a => (DFunLike.congr_fun hφ a).symm
  intro htop
  have hker : ∀ {R : Type u} [CommRing R] (I : Ideal R),
      RingHom.ker (Ideal.Quotient.mk (I ^ n)) ≤ I ^ 2 := fun I =>
    Ideal.mk_ker.le.trans (Ideal.pow_le_pow_right hn)
  exact differentialsBaseChangeMap_bijective_of_square Λ A' A
    (A' ⧸ RingHom.ker ε'.toRingHom ^ n) (A ⧸ RingHom.ker ε.toRingHom ^ n) k
    Ideal.Quotient.mk_surjective (hker _) Ideal.Quotient.mk_surjective (hker _) htop

end PowQuotient

end Deformation.Artin
