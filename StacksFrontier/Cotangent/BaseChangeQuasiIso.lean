module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.ResolutionTorBaseChange
public import StacksFrontier.Cotangent.StandardResolutionSquareFunctoriality
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Base change of the cotangent complex along a derived pushout square

Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings which induces a quasi-isomorphism `B ⊗_A^L A' = B'`. Tag 08QQ
asserts that the functoriality map of cotangent complexes then induces an isomorphism

`L_{B/A} ⊗_B^L B' ⟶ L_{B'/A'}`.

The arrow is not left arbitrary: it is the `B`-linear map `L_{B/A} ⟶ L_{B'/A'}` which Tag 08PN
attaches to the square, read through extension of scalars along `B → B'`. Its `B'`-linear adjoint
is `CommAlgCat.cotangentExtendScalarsComplexMap`, and it is that map which is shown below to be a
quasi-isomorphism, hence an isomorphism in `D(B')`. Every term of `L_{B/A}` is a free `B`-module,
because the differentials of a polynomial algebra are free
(`CommAlgCat.free_kaehlerDifferential_standardResolution`), so the degreewise extension of scalars
appearing here computes the derived tensor product `L_{B/A} ⊗_B^L B'`.

The mathematical content supplied is the step the source performs by inspection:

`B' ⊗_{A' ⊗_A P} Ω[A' ⊗_A P⁄A'] = B' ⊗_B (B ⊗_P Ω[P⁄A])`,

naturally in the `A`-algebra `P` augmented to `B`. Applied degreewise to the standard resolution
`P_•` of `B` over `A`, it identifies `L_{B/A} ⊗_B B'` with the complex `Ω[Q_•⁄A'] ⊗_{Q_•} B'` of
the base-changed simplicial algebra `Q_• = A' ⊗_A P_•`, compatibly with the functoriality map; and
the hypothesis `B ⊗_A^L A' = B'` makes the base-changed augmentation `Q_• ⟶ B'` a resolution of
`B'` over `A'`, which is the first half of Tag 08QP.

## The one carried hypothesis

Comparing the complex attached to `Q_•` with the one attached to the *standard* resolution of `B'`
over `A'` is Remark 08QI, the assertion that every simplicial polynomial resolution computes the
cotangent complex. That remark is not available here — see the implementation note
on Remark 08QI in `StacksFrontier/Cotangent/ResolutionComplex.lean`, which records that
resolution-independence is unproved — so it is carried as the explicit hypothesis
`CommAlgCat.CotangentComputedByEveryResolution A' B'`: for every simplicial polynomial resolution
of `B'` over `A'` and every morphism from it to the standard resolution, the induced map of the
complexes `Ω[−⁄A'] ⊗ B'` is a quasi-isomorphism. It is the only hypothesis beyond the source's
own, and Tag 08QI is what discharges it.

## Main definitions

* `CommAlgCat.tensorKaehlerBaseChangeEquiv`: base change of a module of Kähler differentials,
  pushed along an augmentation.
* `CommAlgCat.overDifferentialsBaseChange` and
  `CommAlgCat.overDifferentialsBaseChangeNatIso`: the identification
  `B' ⊗_B (B ⊗_P Ω[P⁄A]) = B' ⊗_{A' ⊗_A P} Ω[A' ⊗_A P⁄A']`, for one augmented algebra and
  naturally in it.
* `CommAlgCat.algebraSquareOfAlgHom`: the commutative square of ring maps attached to a scalar
  tower `A → A' → B'` together with an `A`-algebra map `B → B'`.
* `CommAlgCat.standardResolutionBaseChangeMap` and
  `CommAlgCat.resolutionOverStandardBaseChangeMap`: the canonical morphism
  `A' ⊗_A P_• ⟶ P'_•` of augmented simplicial `A'`-algebras over `B'`.
* `CommAlgCat.cotangentExtendScalarsMooreMap` and
  `CommAlgCat.cotangentExtendScalarsComplexMap`: the functoriality map
  `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}`, on the alternating-face-map complexes and on the cotangent
  complexes.
* `CommAlgCat.cotangentBaseChangeComparisonIso`: the identification of `L_{B/A} ⊗_B B'` with the
  complex of the base-changed simplicial algebra.
* `CommAlgCat.CotangentComputedByEveryResolution`: Remark 08QI, in the form carried here.
* `CommAlgCat.cotangentBaseChangeIso`: the base-change isomorphism in `D(B')`, as data.

## Main results

* `CommAlgCat.cotangentExtendScalarsMooreMap_f_mk`: the functoriality map carries the pure
  differential `1 ⊗ (1 ⊗ d p)` to `1 ⊗ d (u p)`, which is the formula pinning the map of
  Tag 08PN.
* `CommAlgCat.cotangentExtendScalarsMooreMap_eq`: the functoriality map factors as the
  identification of `L_{B/A} ⊗_B B'` with the complex of `Q_• = A' ⊗_A P_•` followed by the map
  induced by `Q_• ⟶ P'_•`.
* `CommAlgCat.quasiIso_cotangentExtendScalarsMooreMap` and
  `CommAlgCat.quasiIso_cotangentExtendScalarsComplexMap`: **Tag 08QQ** — the functoriality map is
  a quasi-isomorphism.
* `CommAlgCat.isIso_Q_map_cotangentExtendScalarsComplexMap`: the same read in `D(B')`.

## Implementation notes

**Why the identification is built from `LinearEquiv`s.** The two `B'`-modules being compared are
scalar extensions, so a map between them is pinned by its values on the pure differentials
`1 ⊗ (1 ⊗ d p)`; but invertibility is not. The identification is therefore assembled from
Mathlib's `KaehlerDifferential.tensorKaehlerEquiv` and two cancellations of base change, each an
isomorphism, and the value on a pure differential is read off afterwards. Naturality in the
augmented algebra is then a computation on those generators.

**The base-changed resolution, and why no second cardinal appears.** Extension of scalars carries
`A[S]` to `A'[S]` on the same set `S` of variables, so the terms of `A' ⊗_A P_•` are again
polynomial algebras; nothing here restricts the sets of variables, because the comparison used is
the chain-level one and not the criterion of Tag 08Q9.

**One universe.** The two base rings and the two algebras all live in a single universe `u`, the
convention of `StacksFrontier/Cotangent/PolynomialAlgebraSiteBaseChange.lean` and of
`StacksFrontier/Cotangent/ResolutionBaseChange.lean`, which is where the base-changed augmentation
and its properties are available. The square of ring maps is therefore
`CommAlgCat.AlgebraSquare.{u, u, u}`.

## References

* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08QM](https://stacks.math.columbia.edu/tag/08QM)
* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
* [Stacks Project, Tag 08QP](https://stacks.math.columbia.edu/tag/08QP)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open scoped ChangeOfRings TensorProduct

universe u

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

/-! ### Base change of the differentials of an algebra -/

/-- **`B' ⊗_{Bb} (Bb ⊗_P Ω[P⁄A]) = B' ⊗_{A' ⊗_A P} Ω[A' ⊗_A P⁄A']`.** Base change of Kähler
differentials along `A → A'` presents `Ω[A' ⊗_A P⁄A']` as `(A' ⊗_A P) ⊗_P Ω[P⁄A]`, and cancelling
base change on either side identifies the two `B'`-modules of differentials. -/
def tensorKaehlerBaseChangeEquiv (A A' P Bb B' : Type u) [CommRing A] [CommRing A'] [CommRing P]
    [CommRing Bb] [CommRing B'] [Algebra A A'] [Algebra A P] [Algebra P Bb] [Algebra Bb B']
    [Algebra P B'] [IsScalarTower P Bb B'] [Algebra A' B']
    [Algebra (A' ⊗[A] P) B'] [IsScalarTower A' (A' ⊗[A] P) B']
    [IsScalarTower P (A' ⊗[A] P) B'] :
    (B' ⊗[Bb] (Bb ⊗[P] Ω[P⁄A])) ≃ₗ[B'] (B' ⊗[A' ⊗[A] P] Ω[(A' ⊗[A] P)⁄A']) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange P Bb B' B' (Ω[P⁄A]) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P (A' ⊗[A] P) B' B' (Ω[P⁄A])).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B' B')
        (KaehlerDifferential.tensorKaehlerEquiv A A' P (A' ⊗[A] P))

/-- The identification carries the pure differential `1 ⊗ (1 ⊗ d p)` to `1 ⊗ d (1 ⊗ p)`, the
image of `p` in `A' ⊗_A P`. -/
theorem tensorKaehlerBaseChangeEquiv_tmul
    (A A' P Bb B' : Type u) [CommRing A] [CommRing A'] [CommRing P]
    [CommRing Bb] [CommRing B'] [Algebra A A'] [Algebra A P] [Algebra P Bb] [Algebra Bb B']
    [Algebra P B'] [IsScalarTower P Bb B'] [Algebra A' B']
    [Algebra (A' ⊗[A] P) B'] [IsScalarTower A' (A' ⊗[A] P) B']
    [IsScalarTower P (A' ⊗[A] P) B'] (p : P) :
    tensorKaehlerBaseChangeEquiv A A' P Bb B'
        ((1 : B') ⊗ₜ[Bb] ((1 : Bb) ⊗ₜ[P] KaehlerDifferential.D A P p)) =
      (1 : B') ⊗ₜ[A' ⊗[A] P] KaehlerDifferential.D A' (A' ⊗[A] P)
        (algebraMap P (A' ⊗[A] P) p) := by
  simp [tensorKaehlerBaseChangeEquiv, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

section Functoriality

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}

/-- The functor `P ↦ B ⊗_P Ω[P⁄A]` sends a morphism of `A`-algebras over `B` to the map carrying
the pure differential `1 ⊗ d p` to `1 ⊗ d (f p)`. -/
theorem overDifferentialsFunctor_map_mk {X Y : Over B} (f : X ⟶ Y) (p : (X.left : Type u)) :
    overDifferentialsFunctor.map f (overDifferentialsMk X p) =
      overDifferentialsMk Y (f.left.hom p) :=
  overDifferentialsPush_mk f.left (augmentationRingHom_comp f) p

end Functoriality

section Square

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
  [Algebra A (B' : Type u)] [IsScalarTower A A' (B' : Type u)]
  (b : (B : Type u) →ₐ[A] (B' : Type u))

/-- **Base change of the differentials of one augmented algebra.** For an `A`-algebra `P`
augmented to `B`, extension of scalars along `B → B'` of the `B`-module `B ⊗_P Ω[P⁄A]` is the
`B'`-module `B' ⊗_{A' ⊗_A P} Ω[A' ⊗_A P⁄A']` attached to `A' ⊗_A P` augmented to `B'`. -/
def overDifferentialsBaseChange (X : Over B) :
    (ModuleCat.extendScalars b.toRingHom).obj (overDifferentials X) ≅
      overDifferentials ((baseChangeOver b).obj X) :=
  letI : Algebra (X.left : Type u) (B : Type u) := (augmentationRingHom X).toAlgebra
  letI : Algebra (B : Type u) (B' : Type u) := b.toRingHom.toAlgebra
  letI : Algebra (X.left : Type u) (B' : Type u) :=
    (b.toRingHom.comp (augmentationRingHom X)).toAlgebra
  letI : IsScalarTower (X.left : Type u) (B : Type u) (B' : Type u) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra (A' ⊗[A] (X.left : Type u)) (B' : Type u) :=
    (baseChangeAugmentation b X).toRingHom.toAlgebra
  letI : IsScalarTower A' (A' ⊗[A] (X.left : Type u)) (B' : Type u) :=
    IsScalarTower.of_algebraMap_eq fun a' => by
      change (algebraMap A' (B' : Type u)) a' =
        baseChangeAugmentation b X (algebraMap A' (A' ⊗[A] (X.left : Type u)) a')
      rw [AlgHom.commutes]
  letI : IsScalarTower (X.left : Type u) (A' ⊗[A] (X.left : Type u)) (B' : Type u) :=
    IsScalarTower.of_algebraMap_eq fun q => by
      change b (X.hom.hom q) = baseChangeAugmentation b X ((1 : A') ⊗ₜ[A] q)
      rw [baseChangeAugmentation_tmul]
      simp
  let e := tensorKaehlerBaseChangeEquiv A A' (X.left : Type u) (B : Type u) (B' : Type u)
  { hom := ModuleCat.ofHom
      (X := (((ModuleCat.extendScalars b.toRingHom).obj (overDifferentials X)) : Type u))
      (Y := ((overDifferentials ((baseChangeOver b).obj X)) : Type u)) e.toLinearMap
    inv := ModuleCat.ofHom
      (X := ((overDifferentials ((baseChangeOver b).obj X)) : Type u))
      (Y := (((ModuleCat.extendScalars b.toRingHom).obj (overDifferentials X)) : Type u))
      e.symm.toLinearMap
    hom_inv_id := ModuleCat.hom_ext (LinearMap.ext fun x => e.symm_apply_apply x)
    inv_hom_id := ModuleCat.hom_ext (LinearMap.ext fun x => e.apply_symm_apply x) }

/-- The identification carries `1 ⊗ (1 ⊗ d p)` to the pure differential `1 ⊗ d (1 ⊗ p)` of the
base-changed algebra. These elements generate, so this formula pins it down. -/
theorem overDifferentialsBaseChange_hom_mk (X : Over B) (p : (X.left : Type u)) :
    (overDifferentialsBaseChange b X).hom
        ((1 : (B' : Type u)) ⊗ₜ[(B : Type u), b.toRingHom] overDifferentialsMk X p) =
      overDifferentialsMk ((baseChangeOver b).obj X) ((1 : A') ⊗ₜ[A] p) := by
  let : Algebra (X.left : Type u) (B : Type u) := (augmentationRingHom X).toAlgebra
  let : Algebra (B : Type u) (B' : Type u) := b.toRingHom.toAlgebra
  let : Algebra (X.left : Type u) (B' : Type u) :=
    (b.toRingHom.comp (augmentationRingHom X)).toAlgebra
  have : IsScalarTower (X.left : Type u) (B : Type u) (B' : Type u) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (A' ⊗[A] (X.left : Type u)) (B' : Type u) :=
    (baseChangeAugmentation b X).toRingHom.toAlgebra
  have : IsScalarTower A' (A' ⊗[A] (X.left : Type u)) (B' : Type u) :=
    IsScalarTower.of_algebraMap_eq fun a' => by
      change (algebraMap A' (B' : Type u)) a' =
        baseChangeAugmentation b X (algebraMap A' (A' ⊗[A] (X.left : Type u)) a')
      rw [AlgHom.commutes]
  have : IsScalarTower (X.left : Type u) (A' ⊗[A] (X.left : Type u)) (B' : Type u) :=
    IsScalarTower.of_algebraMap_eq fun q => by
      change b (X.hom.hom q) = baseChangeAugmentation b X ((1 : A') ⊗ₜ[A] q)
      rw [baseChangeAugmentation_tmul]
      simp
  exact tensorKaehlerBaseChangeEquiv_tmul A A' (X.left : Type u) (B : Type u) (B' : Type u) p

/-- **`i^*Ω_{𝒪/A} ⊗_B B' = g^{-1}(i^*Ω_{𝒪'/A'})`, the step the source performs by inspection.**
Extension of scalars along `B → B'` of the `B`-module of differentials `B ⊗_P Ω[P⁄A]` is the
`B'`-module of differentials of the base-changed algebra `A' ⊗_A P`, naturally in the `A`-algebra
`P` augmented to `B`. -/
@[stacks 08QQ "the step of the proof the source performs by inspection: extension of scalars \
  along B → B' of i^*Ω_{𝒪/A} is the restriction of i^*Ω_{𝒪'/A'} along the base-change functor \
  of sites of Tag 08QN"]
def overDifferentialsBaseChangeNatIso :
    overDifferentialsFunctor (A := A) (B := B) ⋙ ModuleCat.extendScalars b.toRingHom ≅
      baseChangeOver b ⋙ overDifferentialsFunctor (A := A') (B := B') :=
  NatIso.ofComponents (fun X => overDifferentialsBaseChange b X) (by
    intro X Y f
    let : Algebra (X.left : Type u) (B : Type u) := (augmentationRingHom X).toAlgebra
    refine ModuleCat.extendScalars_baseChange_kaehlerDifferential_hom_ext
      (A := A) (P := (X.left : Type u)) b.toRingHom _ _ fun p => ?_
    change (overDifferentialsBaseChange b Y).hom
        ((ModuleCat.extendScalars b.toRingHom).map
          (overDifferentialsPush f.left (augmentationRingHom_comp f))
            ((1 : (B' : Type u)) ⊗ₜ[(B : Type u), b.toRingHom] overDifferentialsMk X p)) =
      overDifferentialsPush ((baseChangeOver b).map f).left
          (augmentationRingHom_comp ((baseChangeOver b).map f))
        ((overDifferentialsBaseChange b X).hom
          ((1 : (B' : Type u)) ⊗ₜ[(B : Type u), b.toRingHom] overDifferentialsMk X p))
    rw [ModuleCat.ExtendScalars.map_tmul, overDifferentialsPush_mk]
    refine (overDifferentialsBaseChange_hom_mk b Y (f.left.hom p)).trans ?_
    have h1 : overDifferentialsPush ((baseChangeOver b).map f).left
          (augmentationRingHom_comp ((baseChangeOver b).map f))
          (overDifferentialsMk ((baseChangeOver b).obj X) ((1 : A') ⊗ₜ[A] p)) =
        overDifferentialsMk ((baseChangeOver b).obj Y)
          (baseChangeMap f ((1 : A') ⊗ₜ[A] p)) :=
      overDifferentialsPush_mk _ _ _
    have h2 : overDifferentialsMk ((baseChangeOver b).obj Y)
          (baseChangeMap f ((1 : A') ⊗ₜ[A] p)) =
        overDifferentialsMk ((baseChangeOver b).obj Y) ((1 : A') ⊗ₜ[A] f.left.hom p) :=
      congrArg (fun q : A' ⊗[A] (Y.left : Type u) =>
        overDifferentialsMk ((baseChangeOver b).obj Y) q) (baseChangeMap_tmul f 1 p)
    have h3 : (overDifferentialsPush ((baseChangeOver b).map f).left
          (augmentationRingHom_comp ((baseChangeOver b).map f)))
          ((overDifferentialsBaseChange b X).hom
            ((1 : (B' : Type u)) ⊗ₜ[(B : Type u), b.toRingHom] overDifferentialsMk X p)) =
        (overDifferentialsPush ((baseChangeOver b).map f).left
          (augmentationRingHom_comp ((baseChangeOver b).map f)))
          (overDifferentialsMk ((baseChangeOver b).obj X) ((1 : A') ⊗ₜ[A] p)) :=
      congrArg _ (overDifferentialsBaseChange_hom_mk b X p)
    exact (h3.trans (h1.trans h2)).symm)

/-! ### The commutative square and the base-changed standard resolution -/

/-- The commutative square of ring maps `A → B`, `A → A'`, `B → B'`, `A' → B'` determined by a
scalar tower `A → A' → B'` together with an `A`-algebra map `b : B → B'`. -/
def algebraSquareOfAlgHom : AlgebraSquare.{u, u, u} A A' B B' where
  base := algebraMap A A'
  map := b.toRingHom
  map_algebraMap a := by
    rw [show b.toRingHom (algebraMap A (B : Type u) a) = b (algebraMap A (B : Type u) a) from rfl,
      b.commutes a]
    exact IsScalarTower.algebraMap_apply A A' (B' : Type u) a

/-- The `A'`-algebra map `A' ⊗_A P_n → P'_n` extending the canonical map `u : P_n → P'_n` of
standard resolutions attached to the square: it sends `a' ⊗ p` to `a' · u(p)`. -/
def standardResolutionBaseChangeMap (n : SimplexCategoryᵒᵖ) :
    (A' ⊗[A] ((standardResolution.{u, u} A B).left.obj n : Type u)) →ₐ[A']
      ((standardResolution.{u, u} A' B').left.obj n : Type u) :=
  letI : Algebra A ((standardResolution.{u, u} A' B').left.obj n : Type u) :=
    ((algebraMap A' ((standardResolution.{u, u} A' B').left.obj n : Type u)).comp
      (algebraMap A A')).toAlgebra
  letI : IsScalarTower A A' ((standardResolution.{u, u} A' B').left.obj n : Type u) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId A' ((standardResolution.{u, u} A' B').left.obj n : Type u))
    (AlgHom.mk (standardResolutionSquareMap.{u, u, u} (algebraSquareOfAlgHom b) n)
      (standardResolutionSquareMap_algebraMap.{u, u, u} (algebraSquareOfAlgHom b) n))

/-- The map on a pure tensor: `a' ⊗ p ↦ a' · u(p)`. -/
@[simp]
theorem standardResolutionBaseChangeMap_tmul (n : SimplexCategoryᵒᵖ) (a' : A')
    (p : (standardResolution.{u, u} A B).left.obj n) :
    standardResolutionBaseChangeMap b n (a' ⊗ₜ[A] p) =
      algebraMap A' ((standardResolution.{u, u} A' B').left.obj n : Type u) a' *
        standardResolutionSquareMap.{u, u, u} (algebraSquareOfAlgHom b) n p := by
  simp only [standardResolutionBaseChangeMap, Algebra.TensorProduct.productLeftAlgHom,
    Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]
  rfl

/-- On `1 ⊗ p` the map is the canonical map `u` of the two standard resolutions. -/
theorem standardResolutionBaseChangeMap_one_tmul (n : SimplexCategoryᵒᵖ)
    (p : (standardResolution.{u, u} A B).left.obj n) :
    standardResolutionBaseChangeMap b n ((1 : A') ⊗ₜ[A] p) =
      standardResolutionSquareMap.{u, u, u} (algebraSquareOfAlgHom b) n p := by
  rw [standardResolutionBaseChangeMap_tmul, map_one, one_mul]

/-- Two additive maps out of a tensor product which agree on pure tensors agree everywhere. -/
private theorem apply_eq_of_tmul_eq {R S P M F G : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [AddCommMonoid P] [Module R P] [AddCommMonoid M]
    [FunLike F (S ⊗[R] P) M] [AddMonoidHomClass F (S ⊗[R] P) M]
    [FunLike G (S ⊗[R] P) M] [AddMonoidHomClass G (S ⊗[R] P) M] (f : F) (g : G)
    (h : ∀ (s : S) (p : P), f (s ⊗ₜ[R] p) = g (s ⊗ₜ[R] p)) (x : S ⊗[R] P) : f x = g x := by
  induction x using TensorProduct.inductionOn with
  | tmul s p => exact h s p
  | add x y hx hy => simp [hx, hy]

/-- The map lies over `B'`: composing it with the augmentation of `P'_n` gives the base-changed
augmentation `a' ⊗ p ↦ a' · b(ε_n(p))`. -/
theorem standardResolutionBaseChangeMap_augmentation (n : SimplexCategoryᵒᵖ)
    (x : A' ⊗[A] ((standardResolution.{u, u} A B).left.obj n : Type u)) :
    ((standardResolution.{u, u} A' B').hom.app n).hom
        (standardResolutionBaseChangeMap b n x) =
      ((augmentationBaseChange b (standardResolution.{u, u} A B).hom).app n).hom x := by
  refine apply_eq_of_tmul_eq (((standardResolution.{u, u} A' B').hom.app n).hom.comp
    (standardResolutionBaseChangeMap b n)) ((augmentationBaseChange b
      (standardResolution.{u, u} A B).hom).app n).hom (fun a' p => ?_) x
  refine Eq.trans ?_
    (augmentationBaseChange_app_tmul b (standardResolution.{u, u} A B).hom n a' p).symm
  rw [AlgHom.comp_apply, standardResolutionBaseChangeMap_tmul, map_mul]
  congr 1
  · exact AlgHom.commutes _ a'
  · exact standardResolutionSquareMap_augmentation_app.{u, u, u} (algebraSquareOfAlgHom b) n p

/-- The maps commute with every simplicial operator, so they form a morphism of simplicial
`A'`-algebras. -/
theorem standardResolutionBaseChangeMap_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j)
    (x : A' ⊗[A] ((standardResolution.{u, u} A B).left.obj i : Type u)) :
    standardResolutionBaseChangeMap b j
        (((simplicialBaseChange b (standardResolution.{u, u} A B).hom).map g).hom x) =
      ((standardResolution.{u, u} A' B').left.map g).hom
        (standardResolutionBaseChangeMap b i x) := by
  refine apply_eq_of_tmul_eq ((standardResolutionBaseChangeMap b j).comp
    ((simplicialBaseChange b (standardResolution.{u, u} A B).hom).map g).hom)
    (((standardResolution.{u, u} A' B').left.map g).hom.comp (standardResolutionBaseChangeMap b i))
    (fun a' p => ?_) x
  refine Eq.trans (congrArg (standardResolutionBaseChangeMap b j)
    (simplicialBaseChange_map_tmul b (standardResolution.{u, u} A B).hom g a' p)) ?_
  rw [standardResolutionBaseChangeMap_tmul, AlgHom.comp_apply,
    standardResolutionBaseChangeMap_tmul, map_mul]
  congr 1
  · exact (((standardResolution.{u, u} A' B').left.map g).hom.commutes a').symm
  · exact standardResolutionSquareMap_naturality.{u, u, u} (algebraSquareOfAlgHom b) g p

/-- **The canonical morphism `A' ⊗_A P_• ⟶ P'_•` of augmented simplicial `A'`-algebras over
`B'`**, from the base change of the standard resolution of `B` over `A` to the standard resolution
of `B'` over `A'`. -/
def resolutionOverStandardBaseChangeMap :
    resolutionOver (augmentationBaseChange b (standardResolution.{u, u} A B).hom) ⟶
      resolutionOver (standardResolution.{u, u} A' B').hom where
  app n := Over.homMk (CommAlgCat.ofHom (standardResolutionBaseChangeMap b n))
    (CommAlgCat.hom_ext (AlgHom.ext (standardResolutionBaseChangeMap_augmentation b n)))
  naturality i j g := by
    apply Over.OverMorphism.ext
    exact CommAlgCat.hom_ext (AlgHom.ext (standardResolutionBaseChangeMap_naturality b g))

/-! ### The functoriality map after extension of scalars -/

/-- **The functoriality map of the square after extension of scalars**, on the
alternating-face-map complexes: the `B'`-linear adjoint of the `B`-linear map
`L_{B/A} ⟶ L_{B'/A'}` of Tag 08PN. -/
def cotangentExtendScalarsMooreMap :
    ((ModuleCat.extendScalars b.toRingHom).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
          (cotangentSimplicialModule.{u, u} A B).object) ⟶
      (alternatingFaceMapComplex (ModuleCat.{u} B')).obj
        (cotangentSimplicialModule.{u, u} A' B').object where
  f n := ((ModuleCat.extendRestrictScalarsAdj b.toRingHom).homEquiv _ _).symm
    ((squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b)).f n)
  comm' i j _ := by
    have h := (squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b)).comm i j
    simp only [Functor.mapHomologicalComplex_obj_d] at h
    have e1 := Adjunction.homEquiv_naturality_right_symm
      (ModuleCat.extendRestrictScalarsAdj b.toRingHom)
      ((squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b)).f i)
      (((alternatingFaceMapComplex (ModuleCat.{u} B')).obj
        (cotangentSimplicialModule.{u, u} A' B').object).d i j)
    have e2 := Adjunction.homEquiv_naturality_left_symm
      (ModuleCat.extendRestrictScalarsAdj b.toRingHom)
      (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (cotangentSimplicialModule.{u, u} A B).object).d i j)
      ((squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b)).f j)
    exact e1.symm.trans ((congrArg
      (fun z => ((ModuleCat.extendRestrictScalarsAdj b.toRingHom).homEquiv _ _).symm z) h).trans e2)

/-- In each degree the map is, by construction, the adjoint of the degreewise functoriality map
of Tag 08PN. -/
theorem cotangentExtendScalarsMooreMap_f (n : ℕ) :
    (cotangentExtendScalarsMooreMap b).f n =
      ((ModuleCat.extendRestrictScalarsAdj b.toRingHom).homEquiv _ _).symm
        ((squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b)).f n) :=
  rfl

/-- The functoriality map carries the pure differential `1 ⊗ (1 ⊗ d p)` to `1 ⊗ d (u p)`, where
`u : P_n → P'_n` is the canonical map of standard resolutions. This is the formula which pins
down the map of Tag 08PN. -/
theorem cotangentExtendScalarsMooreMap_f_mk (n : ℕ)
    (p : (standardResolution.{u, u} A B).left.obj (op ⦋n⦌)) :
    (cotangentExtendScalarsMooreMap b).f n
        ((1 : (B' : Type u)) ⊗ₜ[(B : Type u), b.toRingHom]
          cotangentTermDifferential.{u, u} A B (op ⦋n⦌) p) =
      cotangentTermDifferential.{u, u} A' B' (op ⦋n⦌)
        (standardResolutionSquareMap.{u, u, u} (algebraSquareOfAlgHom b) (op ⦋n⦌) p) := by
  refine Eq.trans (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
    b.toRingHom ((squareCotangentMooreMap.{u, u, u} (algebraSquareOfAlgHom b)).f n) 1 _) ?_
  rw [one_smul]
  refine Eq.trans (congrArg (fun φ => φ (cotangentTermDifferential.{u, u} A B (op ⦋n⦌) p))
    (squareCotangentMooreMap_f.{u, u, u} (algebraSquareOfAlgHom b) n)) ?_
  exact squareCotangentTermMap_D.{u, u, u} (algebraSquareOfAlgHom b) (op ⦋n⦌) p

/-- **`L_{B/A} ⊗_B B'` is the complex of the base-changed simplicial algebra.** Extension of
scalars along `B → B'` of the alternating-face-map complex of `B ⊗_{P_•} Ω[P_•⁄A]` is the
alternating-face-map complex of `B' ⊗_{Q_•} Ω[Q_•⁄A']` for `Q_• = A' ⊗_A P_•`. -/
def cotangentBaseChangeComparisonIso :
    ((ModuleCat.extendScalars b.toRingHom).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
          (cotangentSimplicialModule.{u, u} A B).object) ≅
      (alternatingFaceMapComplex (ModuleCat.{u} B')).obj
        (resolutionOver (augmentationBaseChange b (standardResolution.{u, u} A B).hom) ⋙
          overDifferentialsFunctor) :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
        (ModuleCat.extendScalars b.toRingHom)).app
      (cotangentSimplicialModule.{u, u} A B).object ≪≫
    (alternatingFaceMapComplex (ModuleCat.{u} B')).mapIso
      (Functor.isoWhiskerLeft (resolutionOver (standardResolution.{u, u} A B).hom)
        (overDifferentialsBaseChangeNatIso b))

/-- In each degree the comparison carries `1 ⊗ (1 ⊗ d p)` to the pure differential
`1 ⊗ d (1 ⊗ p)` of the base-changed term. -/
theorem cotangentBaseChangeComparisonIso_hom_f_mk (n : ℕ)
    (p : (standardResolution.{u, u} A B).left.obj (op ⦋n⦌)) :
    (cotangentBaseChangeComparisonIso b).hom.f n
        ((1 : (B' : Type u)) ⊗ₜ[(B : Type u), b.toRingHom]
          cotangentTermDifferential.{u, u} A B (op ⦋n⦌) p) =
      overDifferentialsMk
        ((baseChangeOver b).obj
          ((resolutionOver (standardResolution.{u, u} A B).hom).obj (op ⦋n⦌)))
        ((1 : A') ⊗ₜ[A] p) := by
  have h : (cotangentBaseChangeComparisonIso b).hom.f n =
      (overDifferentialsBaseChange b
        ((resolutionOver (standardResolution.{u, u} A B).hom).obj (op ⦋n⦌))).hom := by
    simp only [cotangentBaseChangeComparisonIso, Iso.trans_hom, HomologicalComplex.comp_f]
    exact Category.id_comp _
  rw [h]
  exact overDifferentialsBaseChange_hom_mk b
    ((resolutionOver (standardResolution.{u, u} A B).hom).obj (op ⦋n⦌)) p

/-! ### Remark 08QI, carried as a hypothesis -/

/-- **Remark 08QI, in the form in which it is used here:** for every simplicial polynomial
resolution `δ : Q_• ⟶ B'` of `B'` over `A'` and every morphism from it to the standard resolution,
the induced map of the complexes `Ω[−⁄A'] ⊗ B'` is a quasi-isomorphism. That is: the cotangent
complex of `B'` over `A'` is computed by any resolution, compatibly with the comparison maps. -/
def CotangentComputedByEveryResolution (A' : Type u) [CommRing A'] (B' : CommAlgCat.{u} A') :
    Prop :=
  ∀ (Q : SimplicialObject (CommAlgCat.{u} A'))
    (δ : Q ⟶ (SimplicialObject.const (CommAlgCat.{u} A')).obj B'),
    (∀ n, IsPolynomialAlgebra A' (Q.obj n)) → IsResolution A' (B' : Type u) Q δ →
    ∀ ψ : resolutionOver δ ⟶ resolutionOver (standardResolution.{u, u} A' B').hom,
      QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} B')).map
        (Functor.whiskerRight ψ (overDifferentialsFunctor (A := A') (B := B'))))

/-- **The functoriality map factors through the base-changed resolution.** Under the
identification of `L_{B/A} ⊗_B B'` with the complex of `Q_• = A' ⊗_A P_•`, the functoriality map
of the square is the map induced by the canonical morphism `Q_• ⟶ P'_•`: both carry the pure
differential `1 ⊗ (1 ⊗ d p)` to `1 ⊗ d (u p)`, and a map out of a scalar extension of a module of
differentials is determined by its values there. -/
theorem cotangentExtendScalarsMooreMap_eq :
    cotangentExtendScalarsMooreMap b =
      (cotangentBaseChangeComparisonIso b).hom ≫
        (alternatingFaceMapComplex (ModuleCat.{u} B')).map
          (Functor.whiskerRight (resolutionOverStandardBaseChangeMap b)
            (overDifferentialsFunctor (A := A') (B := B'))) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  let : Algebra ((standardResolution.{u, u} A B).left.obj (op ⦋n⦌) : Type u) (B : Type u) :=
    (standardResolutionAugmentationHom.{u, u} A B (op ⦋n⦌)).toAlgebra
  refine ModuleCat.extendScalars_baseChange_kaehlerDifferential_hom_ext
    (A := A) (P := ((standardResolution.{u, u} A B).left.obj (op ⦋n⦌) : Type u))
    b.toRingHom _ _ fun p => ?_
  refine Eq.trans (cotangentExtendScalarsMooreMap_f_mk b n p) ?_
  have hcomp : ((cotangentBaseChangeComparisonIso b).hom ≫
      (alternatingFaceMapComplex (ModuleCat.{u} B')).map
        (Functor.whiskerRight (resolutionOverStandardBaseChangeMap b)
          (overDifferentialsFunctor (A := A') (B := B')))).f n =
      (cotangentBaseChangeComparisonIso b).hom.f n ≫
        overDifferentialsFunctor.map
          ((resolutionOverStandardBaseChangeMap b).app (op ⦋n⦌)) := by
    simp only [HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f,
      Functor.whiskerRight_app]
  refine Eq.symm ?_
  refine Eq.trans (congrArg (fun φ => φ ((1 : (B' : Type u)) ⊗ₜ[(B : Type u), b.toRingHom]
    cotangentTermDifferential.{u, u} A B (op ⦋n⦌) p)) hcomp) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg _ (cotangentBaseChangeComparisonIso_hom_f_mk b n p)) ?_
  refine Eq.trans (overDifferentialsFunctor_map_mk
    ((resolutionOverStandardBaseChangeMap b).app (op ⦋n⦌)) ((1 : A') ⊗ₜ[A] p)) ?_
  exact congrArg
    (fun q : ((standardResolution.{u, u} A' B').left.obj (op ⦋n⦌) : Type u) =>
      cotangentTermDifferential.{u, u} A' B' (op ⦋n⦌) q)
    (standardResolutionBaseChangeMap_one_tmul b (op ⦋n⦌) p)

/-! ### Tag 08QQ -/

/-- The differentials of each term of the standard resolution are free over that term, the terms
being polynomial algebras over `A`. This is why the degreewise extension of scalars of `L_{B/A}`
computes the derived tensor product `L_{B/A} ⊗_B^L B'`. -/
theorem free_kaehlerDifferential_standardResolution (A : Type u) [CommRing A]
    (B : CommAlgCat.{u} A) (n : SimplexCategoryᵒᵖ) :
    Module.Free ((standardResolution.{u, u} A B).left.obj n : Type u)
      Ω[((standardResolution.{u, u} A B).left.obj n : Type u)⁄A] :=
  free_kaehlerDifferential_of_isPolynomialAlgebra A
    ((standardResolution_isResolution.{u, u} A B).isPolynomialAlgebra n)

/-- **Stacks 08QQ, on the alternating-face-map complexes.** If the commutative square `A → B`,
`A → A'`, `B → B'`, `A' → B'` induces a quasi-isomorphism `B ⊗_A^L A' = B'` — that is, `A'` and
`B` are Tor-independent over `A` and `A' ⊗_A B → B'` is bijective — then the functoriality map
`L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of Tag 08PN is a quasi-isomorphism.

The hypothesis `B ⊗_A^L A' = B'` makes the base change `A' ⊗_A P_• ⟶ B'` of the standard
resolution a resolution of `B'` over `A'`, and the functoriality map is the map induced by
`A' ⊗_A P_• ⟶ P'_•` read through the identification of `L_{B/A} ⊗_B B'` with the complex of
`A' ⊗_A P_•`; Remark 08QI, carried as `CommAlgCat.CotangentComputedByEveryResolution`, inverts
that map. -/
@[stacks 08QQ "on the alternating-face-map complexes, under ONE carried hypothesis: Remark 08QI \
  as CommAlgCat.CotangentComputedByEveryResolution, which Tag 08QI discharges; the source's own \
  hypothesis and its conclusion on THE functoriality map of Tag 08PN are kept"]
theorem quasiIso_cotangentExtendScalarsMooreMap
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hpush : Function.Bijective (baseChangeUnit b))
    (hQI : CotangentComputedByEveryResolution A' B') :
    QuasiIso (cotangentExtendScalarsMooreMap b) := by
  have hres : IsResolution A' (B' : Type u)
      (simplicialBaseChange b (standardResolution.{u, u} A B).hom)
      (augmentationBaseChange b (standardResolution.{u, u} A B).hom) :=
    isResolution_augmentationBaseChange b (standardResolution.{u, u} A B).hom
      (standardResolution_isResolution.{u, u} A B) hTor hpush
  have hpoly : ∀ n, IsPolynomialAlgebra A'
      ((simplicialBaseChange b (standardResolution.{u, u} A B).hom).obj n) :=
    isPolynomialAlgebra_simplicialBaseChange b (standardResolution.{u, u} A B).hom
      (standardResolution_isResolution.{u, u} A B).isPolynomialAlgebra
  have hq : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} B')).map
      (Functor.whiskerRight (resolutionOverStandardBaseChangeMap b)
        (overDifferentialsFunctor (A := A') (B := B')))) :=
    hQI _ (augmentationBaseChange b (standardResolution.{u, u} A B).hom) hpoly hres
      (resolutionOverStandardBaseChangeMap b)
  rw [cotangentExtendScalarsMooreMap_eq]
  exact quasiIso_comp _ _ (hφ' := hq)

/-- **The functoriality map `L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` on the cotangent complexes.** It is
`CommAlgCat.cotangentExtendScalarsMooreMap` reindexed so that simplicial degree `n` sits in
cohomological degree `-n`, exactly as `CommAlgCat.squareCotangentComplexMap` reindexes the
`B`-linear functoriality map of Tag 08PN. -/
def cotangentExtendScalarsComplexMap :
    ((ModuleCat.extendScalars b.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, u} A B) ⟶ cotangentComplex.{u, u} A' B' :=
  (HomologicalComplex.mapHomologicalComplexExtendIso (ModuleCat.extendScalars b.toRingHom)
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (cotangentSimplicialModule.{u, u} A B).object)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).inv ≫
    HomologicalComplex.extendMap (cotangentExtendScalarsMooreMap b)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))

/-- **Stacks 08QQ.** If the commutative square `A → B`, `A → A'`, `B → B'`, `A' → B'` induces a
quasi-isomorphism `B ⊗_A^L A' = B'`, then the functoriality map
`L_{B/A} ⊗_B B' ⟶ L_{B'/A'}` of Tag 08PN is a quasi-isomorphism of cotangent complexes. The terms
of `L_{B/A}` are free `B`-modules, so the left-hand side computes `L_{B/A} ⊗_B^L B'`. -/
@[stacks 08QQ "on the cotangent complexes, under ONE carried hypothesis: Remark 08QI as \
  CommAlgCat.CotangentComputedByEveryResolution, which Tag 08QI discharges; the source's own \
  hypothesis B ⊗_A^L A' = B' and its conclusion on THE functoriality map of 08PN are kept"]
theorem quasiIso_cotangentExtendScalarsComplexMap
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hpush : Function.Bijective (baseChangeUnit b))
    (hQI : CotangentComputedByEveryResolution A' B') :
    QuasiIso (cotangentExtendScalarsComplexMap b) := by
  have h := quasiIso_cotangentExtendScalarsMooreMap b hTor hpush hQI
  have h2 : QuasiIso (HomologicalComplex.extendMap (cotangentExtendScalarsMooreMap b)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).2 h
  have h3 : QuasiIso (HomologicalComplex.mapHomologicalComplexExtendIso
      (ModuleCat.extendScalars b.toRingHom)
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        (cotangentSimplicialModule.{u, u} A B).object)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).inv := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := h3) (hφ' := h2)

/-- **Stacks 08QQ in the derived category.** Under the hypothesis `B ⊗_A^L A' = B'` the
functoriality map becomes an isomorphism `L_{B/A} ⊗_B^L B' ⟶ L_{B'/A'}` in `D(B')`. -/
@[stacks 08QQ "the lemma as an isomorphism in D(B'): the image of the functoriality map of \
  Tag 08PN under the localization D(B') is invertible. Carries the same single hypothesis, \
  Remark 08QI as CommAlgCat.CotangentComputedByEveryResolution, discharged by Tag 08QI"]
theorem isIso_Q_map_cotangentExtendScalarsComplexMap
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hpush : Function.Bijective (baseChangeUnit b))
    (hQI : CotangentComputedByEveryResolution A' B') :
    IsIso (DerivedCategory.Q.map (cotangentExtendScalarsComplexMap b)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} (B' : Type u))
      (cotangentExtendScalarsComplexMap b)).2
    (quasiIso_cotangentExtendScalarsComplexMap b hTor hpush hQI)

/-- **Stacks 08QQ, the base-change isomorphism.** The isomorphism
`L_{B/A} ⊗_B^L B' ≅ L_{B'/A'}` in `D(B')` whose underlying morphism is the functoriality map of
the square. -/
@[stacks 08QQ "the base-change isomorphism itself, as data: an isomorphism in D(B') whose \
  underlying morphism is the functoriality map of Tag 08PN. Carries the same single hypothesis, \
  Remark 08QI as CommAlgCat.CotangentComputedByEveryResolution, discharged by Tag 08QI"]
def cotangentBaseChangeIso
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hpush : Function.Bijective (baseChangeUnit b))
    (hQI : CotangentComputedByEveryResolution A' B') :
    DerivedCategory.Q.obj
        (((ModuleCat.extendScalars b.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) ≅
      DerivedCategory.Q.obj (cotangentComplex.{u, u} A' B') :=
  have := isIso_Q_map_cotangentExtendScalarsComplexMap b hTor hpush hQI
  asIso (DerivedCategory.Q.map (cotangentExtendScalarsComplexMap b))

end Square

end CommAlgCat

end
