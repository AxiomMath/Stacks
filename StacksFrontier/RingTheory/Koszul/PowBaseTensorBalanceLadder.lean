module

public import StacksFrontier.RingTheory.Koszul.OppositeBaseChangeBalance
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlip
public import StacksFrontier.RingTheory.Koszul.PowBaseTensorTransition

/-!
# The ladder of the two plain Koszul towers

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_n = R⟨ξ₁, …, ξ_r⟩` be the Koszul
differential graded algebra with `d ξᵢ = fᵢ ^ n`, let `(B, d)` be a differential graded
`R`-algebra and let `P_k` be a family of differential graded `(K_{b+k}, B)`-bimodules with
semilinear transition homomorphisms `P_{k+1} ⟶ P_k|_τ` along the transition homomorphisms `τ` of
the Koszul algebras. There are two towers of differential graded `B`-modules in play:

* `k ↦ P_k ⊗_{K_{b+k}} (K_{b+k} ⊗_R K_t)`, the plain tower of the tower of derived tensor
  products `Koszul.powBaseTensorDerivedTensorTower`, and
* `k ↦ P_k ⊗_R K_t`, the plain tower over the base ring placed in degree zero, in which only the
  bimodule varies and the module `K_t` is constant.

`Koszul.oppTensorObjIso_powBaseTensorRestrictedModule` identifies the `k`-th terms, one `k` at a
time, and claims nothing about the transition maps. This file supplies that compatibility: the
squares formed by those identifications and the two transition homomorphisms commute. This is the
commuting ladder of homomorphisms of differential graded `B`-modules that
`DifferentialGraded.Bimodule.DerivedTensorTower.towerNatIso` asks for, so the two towers of
derived tensor products are isomorphic as functors `ℕᵒᵖ ⥤ D(B, d)` and not merely termwise.

The content of a square is small, and it is checked on pure tensors. Read in the direction out of
the tensor product over the base ring, where no Koszul sign appears, the identification sends the
pure tensor `c ⊗ y` of `K_t ⊗_R P_k` to the pure tensor `(1 ⊗ c) ⊗ y` of
`P_k ⊗_{K_{b+k}} (K_{b+k} ⊗_R K_t)`. Both transition homomorphisms act on the bimodule factor
through the same map, so the square reduces to the identity `(τ ⊗ id)(1 ⊗ c) = 1 ⊗ c`.

## Main definitions

* `DifferentialGradedAlgebra.Hom.id`: the identity homomorphism of a differential graded algebra,
  which is the transition homomorphism of a constant tower of algebras.
* `DifferentialGraded.Bimodule.restrictLeftHomOfSquare`: **the functoriality of the left
  restriction of a differential graded bimodule for a semilinear homomorphism**, along a
  commuting square of homomorphisms of the acting algebras.
* `DifferentialGraded.absBaseBimoduleHom`: its specialisation to
  `DifferentialGraded.absBaseBimodule`, a differential graded bimodule read over the base ring
  placed in degree zero.
* `DifferentialGraded.absBaseIdTransitionHom`: the identity of `C`, as a transition homomorphism
  of the constant tower over the base ring in degree zero.
* `DifferentialGraded.oppBaseBalanceIso`: the comparison of plain tensor products of
  `Koszul.oppTensorObjIso_oppTensorModule_baseModule`, over abstract differential graded
  algebras.
* `Koszul.powBaseDegreeZeroDerivedTensorTower`: **the tower of derived tensor products
  `P_k ⊗_R^𝐋 K_t` over the base ring placed in degree zero**, whose plain tower is the second one
  above.
* `Koszul.powBaseTensorBalanceObjIso`: the identification of the `k`-th terms of the two plain
  towers.

## Main results

* `DifferentialGraded.oppBaseBalanceIso_inv_pure`: **the comparison of plain tensor products on
  pure tensors**, in the direction out of the tensor product over the base ring.
* `DifferentialGraded.oppBaseBalance_ladder`: **the commuting square**, over abstract
  differential graded algebras, for any transition homomorphism of the modules that fixes
  `1 ⊗ c`.
* `DifferentialGraded.oppHom_tensorHomLeft_oppLeftBridgeEquiv_one_tmul`: the homomorphism
  `σ ⊗ id` fixes `1 ⊗ c`, read on the graded opposite algebras. This is the hypothesis of the
  square at the Koszul transition homomorphisms.
* `Koszul.powBaseTensorBalanceObjIso_ladder`: **the ladder at the Koszul towers.**

## Implementation notes

*Only one direction of the comparison is computed.* The comparison of plain tensor products is
`DifferentialGraded.tensorObjIsoOfBaseChange` transported along
`DifferentialGraded.oppLeftBridgeIso`, and on pure tensors its forward direction carries the
Koszul sign of `DifferentialGraded.absLeftUnbalance` and moves a scalar from one factor to the
other. Its inverse carries no sign and changes nothing but the first factor, by
`DifferentialGraded.absLeftBalanceInverseLinear_tmul`; so the square is proved for the inverses,
where both sides are homomorphisms out of the relative tensor product over the base ring and
`DifferentialGraded.Bimodule.tensorObj_hom_ext` applies, and is then transported by
`DifferentialGraded.hom_square_of_inv_square`.

*The transition homomorphism of the modules is a hypothesis.* The square needs exactly one
property of the transition homomorphism of the modules `K_N ⊗_R K_t`, namely that it fixes the
elements `1 ⊗ c`; the general statement therefore takes an arbitrary homomorphism with that
property, and the homomorphism of algebras it is semilinear over is arbitrary too. At the Koszul
towers the hypothesis is discharged by
`DifferentialGraded.oppHom_tensorHomLeft_oppLeftBridgeEquiv_one_tmul`, whose proof is `τ(1) = 1`
pushed across the two identifications of underlying graded modules through which the graded
opposite algebras are reached.

*The constant tower.* The second tower is a tower over the single algebra `R` placed in degree
zero, so its transition homomorphisms of algebras are identities. Restriction of scalars along
the identity is not the identity functor on the nose — the right action is composed with the
identity rather than left alone — so the transition homomorphism of the constant module `K_t` is
`DifferentialGraded.absBaseIdTransitionHom`, built from
`DifferentialGradedModule.restrictedRegularHomRestrict` rather than taken to be `𝟙`, and the
transition homomorphism of the bimodules lands in a left restriction along the identity as well.

## References

* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) is where the two towers
  are compared.
* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the relative tensor
  product with a bimodule, [Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ) differential
  graded bimodules, [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX) restriction of scalars,
  [Tag 065W](https://stacks.math.columbia.edu/tag/065W) the tensor product of differential graded
  algebras and [Tag 09JG](https://stacks.math.columbia.edu/tag/09JG) the graded opposite algebra.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct DirectSum

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- **The identity homomorphism of a differential graded algebra.** This is the transition
homomorphism of a constant tower of differential graded algebras; it is the companion of
`DifferentialGradedAlgebra.Hom.comp`. -/
def Hom.id (A : DifferentialGradedAlgebra.{u, u} R) : A.Hom A where
  toAlgebraHom := AlgHom.id R A.A
  map_grading _ _ ha := ha
  map_d _ := rfl

/-- The underlying algebra homomorphism of `DifferentialGradedAlgebra.Hom.id A` is the identity
`AlgHom.id R A.A`. -/
@[simp] theorem Hom.id_toAlgebraHom (A : DifferentialGradedAlgebra.{u, u} R) :
    (Hom.id A).toAlgebraHom = AlgHom.id R A.A := rfl

end DifferentialGradedAlgebra

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R]

/-! ### Functoriality of the left restriction -/

/-- **A commuting square of homomorphisms of differential graded algebras carries a semilinear
homomorphism of bimodules to a semilinear homomorphism of their left restrictions.** Let
`σ : A₂ → A₁`, `δ : D₂ → D₁`, `ρ₁ : D₁ → A₁` and `ρ₂ : D₂ → A₂` be homomorphisms of differential
graded algebras with `σ ∘ ρ₂ = ρ₁ ∘ δ`, and let `g : P₂ ⟶ P₁|_σ` be a `σ`-semilinear homomorphism
of differential graded bimodules with right algebra `B`. Then the same underlying homomorphism of
right `B`-modules is a `δ`-semilinear homomorphism `P₂|_{ρ₂} ⟶ P₁|_{ρ₁}`.

The only thing to check is compatibility with the left action, and nothing is computed: the
degree-`n` part of `D₂` acts on `P₂|_{ρ₂}` through `ρ₂` and on `P₁|_{ρ₁}|_δ` through `ρ₁ ∘ δ`, so
the compatibility of `g` at `ρ₂(a)` is the assertion, once the two images of `a` in the degree-`n`
part of `A₁` are identified by the commuting square.

This is the companion, for the left action of a bimodule, of
`DifferentialGradedModule.restrictedRegularHomRestrict`, and stating it with the target presented
as a restriction of a restriction is what lets it be the transition homomorphism of a tower whose
algebras do not vary. -/
def Bimodule.restrictLeftHomOfSquare {A₁ A₂ D₁ D₂ B : DifferentialGradedAlgebra.{u, u} R}
    (σ : A₂.Hom A₁) (δ : D₂.Hom D₁) (ρ₁ : D₁.Hom A₁) (ρ₂ : D₂.Hom A₂)
    (hsq : ∀ a, σ.toAlgebraHom (ρ₂.toAlgebraHom a) = ρ₁.toAlgebraHom (δ.toAlgebraHom a))
    {P₁ : Bimodule A₁ B} {P₂ : Bimodule A₂ B}
    (g : P₂ ⟶ Bimodule.restrictLeft σ P₁) :
    Bimodule.restrictLeft ρ₂ P₂ ⟶ Bimodule.restrictLeft δ (Bimodule.restrictLeft ρ₁ P₁) where
  rightHom := g.rightHom
  map_left n p a x := by
    have hact : σ.gradingMap n (ρ₂.gradingMap n a) = ρ₁.gradingMap n (δ.gradingMap n a) :=
      Subtype.ext (hsq a)
    have h := g.map_left n p (ρ₂.gradingMap n a) x
    rw [Bimodule.restrictLeft_action σ P₁ n (ρ₂.gradingMap n a), hact] at h
    exact h

/-- The underlying homomorphism of right differential graded modules is unchanged. -/
@[simp] theorem Bimodule.restrictLeftHomOfSquare_rightHom
    {A₁ A₂ D₁ D₂ B : DifferentialGradedAlgebra.{u, u} R}
    (σ : A₂.Hom A₁) (δ : D₂.Hom D₁) (ρ₁ : D₁.Hom A₁) (ρ₂ : D₂.Hom A₂)
    (hsq : ∀ a, σ.toAlgebraHom (ρ₂.toAlgebraHom a) = ρ₁.toAlgebraHom (δ.toAlgebraHom a))
    {P₁ : Bimodule A₁ B} {P₂ : Bimodule A₂ B} (g : P₂ ⟶ Bimodule.restrictLeft σ P₁) :
    (Bimodule.restrictLeftHomOfSquare σ δ ρ₁ ρ₂ hsq g).rightHom = g.rightHom := rfl

variable (A B C : DifferentialGradedAlgebra.{u, u} R)

/-- **A semilinear homomorphism of differential graded bimodules, read over the base ring placed
in degree zero.** A `σ`-semilinear homomorphism `g : P₂ ⟶ P₁|_σ`, where `σ : A₂ → A₁` is a
homomorphism of differential graded algebras, becomes a homomorphism of the differential graded
`(R, B)`-bimodules `DifferentialGraded.absBaseBimodule` with `R` placed in degree zero,
semilinear over the identity of `R` in degree zero.

This is `DifferentialGraded.Bimodule.restrictLeftHomOfSquare` for the square formed by `σ` and
the two structure maps `DifferentialGradedAlgebra.baseHom`, which commutes because a
homomorphism of differential graded algebras is in particular a homomorphism of `R`-algebras. -/
def absBaseBimoduleHom {A₁ A₂ : DifferentialGradedAlgebra.{u, u} R} (σ : A₂.Hom A₁)
    {P₁ : Bimodule A₁ B} {P₂ : Bimodule A₂ B} (g : P₂ ⟶ Bimodule.restrictLeft σ P₁) :
    absBaseBimodule A₂ B P₂ ⟶
      Bimodule.restrictLeft (Hom.id (degreeZero R R)) (absBaseBimodule A₁ B P₁) :=
  Bimodule.restrictLeftHomOfSquare σ (Hom.id (degreeZero R R)) (baseHom A₁)
    (baseHom A₂) (fun s => σ.toAlgebraHom.commutes s) g

/-- Reading a semilinear homomorphism over the base ring in degree zero does not change its
underlying homomorphism of right differential graded modules. -/
@[simp] theorem absBaseBimoduleHom_rightHom {A₁ A₂ : DifferentialGradedAlgebra.{u, u} R}
    (σ : A₂.Hom A₁) {P₁ : Bimodule A₁ B} {P₂ : Bimodule A₂ B}
    (g : P₂ ⟶ Bimodule.restrictLeft σ P₁) :
    (absBaseBimoduleHom B σ g).rightHom = g.rightHom := rfl

/-- **The identity of `C`, as the transition homomorphism of the constant tower of right
differential graded modules over the base ring placed in degree zero.** Restriction of scalars
along the identity of `R` in degree zero composes the right action with the identity instead of
leaving it alone, so this homomorphism is not `𝟙`; it is
`DifferentialGradedModule.restrictedRegularHomRestrict` for the square in which every side is an
identity or the structure map `DifferentialGradedAlgebra.baseHom`. -/
def absBaseIdTransitionHom :
    absBaseSource C ⟶ restrictScalars (Hom.id (degreeZero R R)) (absBaseSource C) :=
  restrictedRegularHomRestrict (baseHom C) (Hom.id (degreeZero R R))
    (baseHom C) (Hom.id C) fun _ => rfl

/-- The transition homomorphism of the constant tower is the identity on elements. -/
theorem absBaseIdTransitionHom_apply (c : C.A) : (absBaseIdTransitionHom C).toFun c = c := rfl

/-! ### The comparison of the two plain tensor products, on pure tensors -/

/-- **The comparison of the two plain tensor products**, over abstract differential graded
algebras: for a differential graded `(A^opp, B)`-bimodule `P`, the relative tensor product over
`A^opp` of `P` with `A ⊗_R C` read over `A^opp` is the relative tensor product over `R` placed in
degree zero of `P` with `C`.

This is `Koszul.oppTensorObjIso_oppTensorModule_baseModule` with the Koszul algebra replaced by an
arbitrary differential graded algebra `C`: the comparison
`DifferentialGraded.tensorObjIsoOfBaseChange` of the two plain tensor products, transported along
the comparison `DifferentialGraded.oppLeftBridgeIso` of the two presentations of `A ⊗_R C` as a
right differential graded `A^opp`-module. -/
def oppBaseBalanceIso (P : Bimodule (oppAlgebra A) B) :
    Bimodule.tensorObj P (oppLeftSource A C) ≅
      Bimodule.tensorObj (absBaseBimodule (oppAlgebra A) B P) (absBaseSource C) :=
  (tensorCompFunctor P).mapIso (oppLeftBridgeIso A C).symm ≪≫
    tensorObjIsoOfBaseChange (oppAlgebra A) B C P

/-- **The comparison of the two plain tensor products, read backwards on pure tensors:** the pure
tensor `c ⊗ y` of `C ⊗_R P` goes to the pure tensor `(1 ⊗ c) ⊗ y` of `(A ⊗_R C) ⊗_{A^opp} P`.

No sign appears in this direction. The comparison is the composite of
`DifferentialGraded.absBaseBalanceForward`, which identifies the relative tensor product over `R`
in degree zero with the absolute one, of `DifferentialGraded.absLeftBalanceInverse`, which sends
`c ⊗ y` to the pure tensor at `1 ⊗ c`, and of the comparison of the two presentations, which is
the identification `DifferentialGraded.oppLeftBridgeEquiv` of underlying graded modules. -/
theorem oppBaseBalanceIso_inv_pure (P : Bimodule (oppAlgebra A) B) (c : C.A)
    (y : P.rightModule.M) :
    (oppBaseBalanceIso A B C P).inv.toFun
        (((tensorDGFunctor (absBaseBimodule (oppAlgebra A) B P)).pure
          (absBaseSource C)).toLinearMap c y) =
      ((tensorDGFunctor P).pure (oppLeftSource A C)).toLinearMap
        (oppLeftBridgeEquiv A C
          (((1 : (oppAlgebra A).A) ᵍ⊗ₜ[R] c : (oppAlgebra A).grading ᵍ⊗[R] C.grading))) y := by
  have h2 : (absBaseBalanceForward (oppAlgebra A) B C P).toFun
      (absBasePureBilinear (oppAlgebra A) B C P c y) =
      (c ⊗ₜ[R] y : C.A ⊗[R] P.rightModule.M) :=
    absBaseBalanceForward_pure (oppAlgebra A) B C P c y
  have h3 : (absLeftBalanceInverse (oppAlgebra A) B C P).toFun
      (c ⊗ₜ[R] y : C.A ⊗[R] P.rightModule.M) =
      ((tensorDGFunctor P).pure (absLeftSource (oppAlgebra A) C)).toLinearMap
        (((1 : (oppAlgebra A).A) ᵍ⊗ₜ[R] c : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) y := rfl
  have h4 := tensorCompFunctor_map_pure' P (oppLeftBridgeHom A C)
    (((1 : (oppAlgebra A).A) ᵍ⊗ₜ[R] c : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) y
  change ((tensorCompFunctor P).map (oppLeftBridgeHom A C)).toFun
      ((absLeftBalanceInverse (oppAlgebra A) B C P).toFun
        ((absBaseBalanceForward (oppAlgebra A) B C P).toFun
          (absBasePureBilinear (oppAlgebra A) B C P c y))) = _
  rw [h2, h3]
  exact h4

/-! ### The commuting square -/

variable {A₁ A₂ : DifferentialGradedAlgebra.{u, u} R}

/-- A commuting square of the inverses of two isomorphisms is a commuting square of the
isomorphisms themselves, read in the other direction. -/
theorem hom_square_of_inv_square {D : Type*} [Category D] {X₂ Y₂ X₁ Y₁ : D}
    (e₂ : X₂ ≅ Y₂) (e₁ : X₁ ≅ Y₁) {F : X₂ ⟶ X₁} {G : Y₂ ⟶ Y₁}
    (h : e₂.inv ≫ F = G ≫ e₁.inv) : F ≫ e₁.hom = e₂.hom ≫ G := by
  have h2 : e₂.hom ≫ e₂.inv ≫ F = e₂.hom ≫ G ≫ e₁.inv := by rw [h]
  rw [Iso.hom_inv_id_assoc] at h2
  rw [h2]
  simp

/-- **The comparison of the two plain tensor products is compatible with the transition
homomorphisms.** Let `σ : A₂^opp → A₁^opp` be a homomorphism of differential graded algebras, let
`g : P₂ ⟶ P₁|_σ` be a `σ`-semilinear homomorphism of differential graded bimodules with right
algebra `B`, and let `u : A₂ ⊗_R C ⟶ (A₁ ⊗_R C)|_σ` be a `σ`-semilinear homomorphism of the
presentations `DifferentialGraded.oppLeftSource` which fixes the elements `1 ⊗ c`. Then the square
formed by

* the transition homomorphism
  `P₂ ⊗_{A₂^opp} (A₂ ⊗_R C) ⟶ P₁ ⊗_{A₁^opp} (A₁ ⊗_R C)` built from `u` and `g`,
* the transition homomorphism `P₂ ⊗_R C ⟶ P₁ ⊗_R C` over the base ring placed in degree zero
  built from `DifferentialGraded.absBaseIdTransitionHom` and
  `DifferentialGraded.absBaseBimoduleHom`, and
* the two comparisons `DifferentialGraded.oppBaseBalanceIso`

commutes. Both sides are homomorphisms out of a relative tensor product, so the square is checked
on pure tensors: the comparisons contribute `c ↦ 1 ⊗ c` by
`DifferentialGraded.oppBaseBalanceIso_inv_pure`, the two transition homomorphisms contribute `g`
on the bimodule factor, and what is left is the hypothesis on `u`. -/
theorem oppBaseBalance_ladder (B C : DifferentialGradedAlgebra.{u, u} R)
    (σ : (oppAlgebra A₂).Hom (oppAlgebra A₁))
    (P₂ : Bimodule (oppAlgebra A₂) B) (P₁ : Bimodule (oppAlgebra A₁) B)
    (g : P₂ ⟶ Bimodule.restrictLeft σ P₁)
    (u : oppLeftSource A₂ C ⟶ restrictScalars σ (oppLeftSource A₁ C))
    (hu : ∀ c : C.A,
      u.toFun (oppLeftBridgeEquiv A₂ C
          (((1 : (oppAlgebra A₂).A) ᵍ⊗ₜ[R] c : (oppAlgebra A₂).grading ᵍ⊗[R] C.grading))) =
        oppLeftBridgeEquiv A₁ C
          (((1 : (oppAlgebra A₁).A) ᵍ⊗ₜ[R] c : (oppAlgebra A₁).grading ᵍ⊗[R] C.grading))) :
    ((tensorCompFunctor P₂).map u ≫
          (tensorCompNatTransOfSemilinear σ P₂ P₁ g).app (oppLeftSource A₁ C)) ≫
        (oppBaseBalanceIso A₁ B C P₁).hom =
      (oppBaseBalanceIso A₂ B C P₂).hom ≫
        ((tensorCompFunctor (absBaseBimodule (oppAlgebra A₂) B P₂)).map
              (absBaseIdTransitionHom C) ≫
            (tensorCompNatTransOfSemilinear (Hom.id (degreeZero R R))
                (absBaseBimodule (oppAlgebra A₂) B P₂) (absBaseBimodule (oppAlgebra A₁) B P₁)
                (absBaseBimoduleHom B σ g)).app (absBaseSource C)) := by
  have key : (oppBaseBalanceIso A₂ B C P₂).inv ≫
        ((tensorCompFunctor P₂).map u ≫
          (tensorCompNatTransOfSemilinear σ P₂ P₁ g).app (oppLeftSource A₁ C)) =
      ((tensorCompFunctor (absBaseBimodule (oppAlgebra A₂) B P₂)).map
            (absBaseIdTransitionHom C) ≫
          (tensorCompNatTransOfSemilinear (Hom.id (degreeZero R R))
              (absBaseBimodule (oppAlgebra A₂) B P₂) (absBaseBimodule (oppAlgebra A₁) B P₁)
              (absBaseBimoduleHom B σ g)).app (absBaseSource C)) ≫
        (oppBaseBalanceIso A₁ B C P₁).inv := by
    refine Bimodule.tensorObj_hom_ext (absBaseBimodule (oppAlgebra A₂) B P₂) (absBaseSource C)
      _ _ fun c y => ?_
    have hLa := oppBaseBalanceIso_inv_pure A₂ B C P₂ c y
    have hLb := tensorCompFunctor_map_pure' P₂ u
      (oppLeftBridgeEquiv A₂ C
        (((1 : (oppAlgebra A₂).A) ᵍ⊗ₜ[R] c : (oppAlgebra A₂).grading ᵍ⊗[R] C.grading))) y
    have hLc := tensorCompNatTransOfSemilinear_app_pure σ P₂ P₁ g (oppLeftSource A₁ C)
      (u.toFun (oppLeftBridgeEquiv A₂ C
        (((1 : (oppAlgebra A₂).A) ᵍ⊗ₜ[R] c : (oppAlgebra A₂).grading ᵍ⊗[R] C.grading)))) y
    have hRa := tensorCompFunctor_map_pure' (absBaseBimodule (oppAlgebra A₂) B P₂)
      (absBaseIdTransitionHom C) c y
    have hRb := tensorCompNatTransOfSemilinear_app_pure (Hom.id (degreeZero R R))
      (absBaseBimodule (oppAlgebra A₂) B P₂) (absBaseBimodule (oppAlgebra A₁) B P₁)
      (absBaseBimoduleHom B σ g) (absBaseSource C) c y
    have hRc := oppBaseBalanceIso_inv_pure A₁ B C P₁ c (g.rightHom.toFun y)
    have hL : ((oppBaseBalanceIso A₂ B C P₂).inv ≫
          ((tensorCompFunctor P₂).map u ≫
            (tensorCompNatTransOfSemilinear σ P₂ P₁ g).app (oppLeftSource A₁ C))).toFun
          (((tensorDGFunctor (absBaseBimodule (oppAlgebra A₂) B P₂)).pure
            (absBaseSource C)).toLinearMap c y) =
        ((tensorDGFunctor P₁).pure (oppLeftSource A₁ C)).toLinearMap
          (u.toFun (oppLeftBridgeEquiv A₂ C
            (((1 : (oppAlgebra A₂).A) ᵍ⊗ₜ[R] c : (oppAlgebra A₂).grading ᵍ⊗[R] C.grading))))
          (g.rightHom.toFun y) :=
      Eq.trans (congrArg
        (fun z => ((tensorCompNatTransOfSemilinear σ P₂ P₁ g).app
            (oppLeftSource A₁ C)).toFun (((tensorCompFunctor P₂).map u).toFun z)) hLa)
        (Eq.trans (congrArg
          (fun z => ((tensorCompNatTransOfSemilinear σ P₂ P₁ g).app
            (oppLeftSource A₁ C)).toFun z) hLb) hLc)
    have hR : (((tensorCompFunctor (absBaseBimodule (oppAlgebra A₂) B P₂)).map
            (absBaseIdTransitionHom C) ≫
          (tensorCompNatTransOfSemilinear (Hom.id (degreeZero R R))
              (absBaseBimodule (oppAlgebra A₂) B P₂) (absBaseBimodule (oppAlgebra A₁) B P₁)
              (absBaseBimoduleHom B σ g)).app (absBaseSource C)) ≫
          (oppBaseBalanceIso A₁ B C P₁).inv).toFun
          (((tensorDGFunctor (absBaseBimodule (oppAlgebra A₂) B P₂)).pure
            (absBaseSource C)).toLinearMap c y) =
        ((tensorDGFunctor P₁).pure (oppLeftSource A₁ C)).toLinearMap
          (oppLeftBridgeEquiv A₁ C
            (((1 : (oppAlgebra A₁).A) ᵍ⊗ₜ[R] c : (oppAlgebra A₁).grading ᵍ⊗[R] C.grading)))
          (g.rightHom.toFun y) :=
      Eq.trans (congrArg (oppBaseBalanceIso A₁ B C P₁).inv.toFun
        (Eq.trans (congrArg
          (fun z => ((tensorCompNatTransOfSemilinear (Hom.id (degreeZero R R))
            (absBaseBimodule (oppAlgebra A₂) B P₂) (absBaseBimodule (oppAlgebra A₁) B P₁)
            (absBaseBimoduleHom B σ g)).app (absBaseSource C)).toFun z) hRa) hRb)) hRc
    refine hL.trans (Eq.trans (congrArg
      (fun z => ((tensorDGFunctor P₁).pure (oppLeftSource A₁ C)).toLinearMap z
        (g.rightHom.toFun y)) (hu c)) hR.symm)
  exact hom_square_of_inv_square _ _ key

/-! ### The transition homomorphism fixes `1 ⊗ c` -/

/-- **The homomorphism `σ ⊗ id : A₂ ⊗_R C → A₁ ⊗_R C` fixes the elements `1 ⊗ c`**, read on the
graded opposite algebras through the identification `DifferentialGraded.oppLeftBridgeEquiv` of
underlying graded modules. This is `σ(1) = 1` pushed across the identifications of the underlying
graded modules of the graded opposite algebras, and it is the hypothesis that
`DifferentialGraded.oppBaseBalance_ladder` makes on the transition homomorphism of the
modules. -/
theorem oppHom_tensorHomLeft_oppLeftBridgeEquiv_one_tmul (σ : A₂.Hom A₁)
    (C : DifferentialGradedAlgebra.{u, u} R) (c : C.A) :
    (oppHom (tensorHomLeft σ C)).toAlgebraHom
        (oppLeftBridgeEquiv A₂ C
          (((1 : (oppAlgebra A₂).A) ᵍ⊗ₜ[R] c : (oppAlgebra A₂).grading ᵍ⊗[R] C.grading))) =
      oppLeftBridgeEquiv A₁ C
        (((1 : (oppAlgebra A₁).A) ᵍ⊗ₜ[R] c : (oppAlgebra A₁).grading ᵍ⊗[R] C.grading)) := by
  have h (A : DifferentialGradedAlgebra.{u, u} R) : oppLeftEquiv A C
      (((1 : (oppAlgebra A).A) ᵍ⊗ₜ[R] c : (oppAlgebra A).grading ᵍ⊗[R] C.grading)) =
      (((1 : A.A) ᵍ⊗ₜ[R] c : A.grading ᵍ⊗[R] C.grading)) := by
    rw [oppLeftEquiv_tmul, (opposite R A).map_one]
  rw [oppLeftBridgeEquiv_apply, oppLeftBridgeEquiv_apply, h, h, oppHom_apply,
    LinearEquiv.apply_symm_apply, tensorHomLeft_tmul, map_one]

end DifferentialGraded

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule
  DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] {r : ℕ} {B : DifferentialGradedAlgebra.{u, u} R}
  (f : Fin r → R) (t : ℕ) {b : ℕ} (hb : 1 ≤ b)
  (bimod : ∀ k : ℕ, Bimodule (oppAlgebra (powAlgebra f (b + k))) B)
  (bimodTrans : ∀ k : ℕ,
    bimod (k + 1) ⟶ Bimodule.restrictLeft (powSuccTransition f hb k) (bimod k))

/-- **The tower of derived tensor products `P_k ⊗_R^𝐋 K_t` over the base ring placed in degree
zero.** The algebras of the tower are the single algebra `R` in degree zero, the modules are the
single module `Koszul.baseModule`, which is `K_t` read over `R` in degree zero, and only the
bimodules vary: they are the bimodules `P_k` of `Koszul.powBaseTensorDerivedTensorTower` read over
`R` in degree zero, with the transition homomorphisms of
`DifferentialGraded.absBaseBimoduleHom`. The left orthogonality of the module to the acyclic
modules, which makes each term computed by the plain tensor product, is
`Koszul.leftOrthogonal_acyclic_baseModule`.

This is the tower that `Koszul.powBaseTensorDerivedTensorTower` is compared to in Tag 0GZJ: its
plain tower is `k ↦ P_k ⊗_R K_t`, with the module `K_t` constant. -/
def powBaseDegreeZeroDerivedTensorTower : DerivedTensorTower B :=
  DerivedTensorTower.ofSemilinear (fun _ => degreeZero R R)
    (fun _ => Hom.id (degreeZero R R))
    (fun k => absBaseBimodule (oppAlgebra (powAlgebra f (b + k))) B (bimod k))
    (fun k => absBaseBimoduleHom B (powSuccTransition f hb k) (bimodTrans k))
    (fun _ => baseModule (seqDual fun i => f i ^ t))
    (fun _ => absBaseIdTransitionHom
      (cohomologicalDifferentialGradedAlgebra R (Fin r → R) (seqDual fun i => f i ^ t)))
    (fun _ => leftOrthogonal_acyclic_baseModule (seqDual fun i => f i ^ t))

/-- The `k`-th algebra of the tower over the base ring in degree zero is `R` in degree zero. -/
@[simp] theorem powBaseDegreeZeroDerivedTensorTower_alg (k : ℕ) :
    (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).alg k = degreeZero R R := rfl

/-- The `k`-th module of the tower over the base ring in degree zero is `K_t`. -/
@[simp] theorem powBaseDegreeZeroDerivedTensorTower_mod (k : ℕ) :
    (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).mod k =
      baseModule (seqDual fun i => f i ^ t) := rfl

/-- The `k`-th bimodule of the tower over the base ring in degree zero is `P_k`, read over the
base ring in degree zero. -/
@[simp] theorem powBaseDegreeZeroDerivedTensorTower_bimod (k : ℕ) :
    (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).bimod k =
      absBaseBimodule (oppAlgebra (powAlgebra f (b + k))) B (bimod k) := rfl

/-- **The identification of the `k`-th terms of the two plain towers of Tag 0GZJ:**
`P_k ⊗_{K_{b+k}} (K_{b+k} ⊗_R K_t) ≅ P_k ⊗_R K_t`. This is
`Koszul.oppTensorObjIso_powBaseTensorRestrictedModule`, read as a comparison of the plain towers
of `Koszul.powBaseTensorDerivedTensorTower` and
`Koszul.powBaseDegreeZeroDerivedTensorTower`. -/
def powBaseTensorBalanceObjIso (k : ℕ) :
    (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).plainObj k ≅
      (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).plainObj k :=
  oppTensorObjIso_powBaseTensorRestrictedModule B f t (b + k) (bimod k)

/-- **The ladder of the two plain towers of Tag 0GZJ.** The identifications
`Koszul.powBaseTensorBalanceObjIso` of the `k`-th terms commute with the transition homomorphisms
of the two plain towers, so together they are an isomorphism of towers of differential graded
`B`-modules and not merely a family of isomorphisms of the terms.

This is the commuting ladder of homomorphisms of differential graded `B`-modules that
`DifferentialGraded.Bimodule.DerivedTensorTower.towerNatIso` and
`DifferentialGraded.Bimodule.DerivedTensorTower.nonempty_iso_of_isDerivedLimit` ask for; nothing
in the derived category is involved. It is `DifferentialGraded.oppBaseBalance_ladder` at the
Koszul algebras, whose hypothesis on the transition homomorphism `τ ⊗ id` of the modules is
`DifferentialGraded.oppHom_tensorHomLeft_oppLeftBridgeEquiv_one_tmul`. -/
theorem powBaseTensorBalanceObjIso_ladder (k : ℕ) :
    (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).plainMap k ≫
        (powBaseTensorBalanceObjIso f t hb bimod bimodTrans k).hom =
      (powBaseTensorBalanceObjIso f t hb bimod bimodTrans (k + 1)).hom ≫
        (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).plainMap k :=
  oppBaseBalance_ladder B (powAlgebra f t) (powSuccTransition f hb k) (bimod (k + 1))
    (bimod k) (bimodTrans k)
    (powBaseTensorTransitionHom f t (hb.trans (Nat.le_add_right b k))
      (Nat.add_le_add_left (Nat.le_succ k) b))
    fun c => oppHom_tensorHomLeft_oppLeftBridgeEquiv_one_tmul
      (powTransition f (hb.trans (Nat.le_add_right b k))
        (Nat.add_le_add_left (Nat.le_succ k) b)) (powAlgebra f t) c

end Koszul

end
