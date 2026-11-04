module

public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.AlgebraCocycle

/-!
# Algebra descent data presented by two pushout squares of rings

Effective descent for algebras along a faithfully flat ring map `R → A`
(`ModuleCat.bijective_productMap_descentInvariants`, the algebra step of Stacks 0245) consumes a
transition isomorphism of `A ⊗[R] A`-algebras `τ : B ⊗[R] A ≃ₐ[R] A ⊗[R] B`.  Geometry does not
hand that over.  What geometry produces — in the proof of Stacks 0APK this is the pair of
instances of Stacks 0APJ, `AlgebraicGeometry.isPushout_sectionsRingOnSubset_of_flat` — is a pair
of **pushout squares of commutative rings**
```
  R ----→ A            R ----→ C
  |       |            |       |
  ↓       ↓            ↓       ↓
  C ----→ P            A ----→ Q
```
together with an isomorphism `Φ : P ≅ Q` of the two apexes, coming from the transition
isomorphism of the descent datum.  Neither `P` nor `Q` is literally a tensor product, and the
isomorphism is given only through the two squares.

This file converts that data into the `≃ₐ` the algebra descent asks for, and records the one
compatibility it needs.  The two conditions on `Φ` are exactly the statement that `Φ` lies over
`A ⊗[R] A`: on the `C`-leg of `P` it becomes, after `A → C`, the `A`-leg of `Q`, and on the
`A`-leg of `P` it becomes the `C`-leg of `Q` composed with `A → C`.

## Main definitions

* `CommRingCat.tensorProductIsoOfIsPushout` : the comparison of the apex of a pushout square of
  rings with the tensor product of its two legs.
* `ModuleCat.algebraTransitionOfPushout` : the transition isomorphism
  `C ⊗[R] A ≃ₐ[R] A ⊗[R] C` of an algebra descent datum presented by two pushout squares and an
  isomorphism of their apexes.

## Main results

* `CommRingCat.tensorProductIsoOfIsPushout_hom_tmul_one`,
  `CommRingCat.tensorProductIsoOfIsPushout_hom_one_tmul`,
  `CommRingCat.tensorProductIsoOfIsPushout_inv_left` and
  `CommRingCat.tensorProductIsoOfIsPushout_inv_right` : the comparison carries the two inclusions
  of the tensor product to the two legs of the square.
* `ModuleCat.algebraTransitionOfPushout_tmul` : the transition sends `c ⊗ a` to the image under
  `Φ` of the product of the two legs, read back in `A ⊗[R] C`.  This is the characterisation a
  consumer verifies the cocycle condition against.
* `ModuleCat.algebraTransitionOfPushout_algebraMap_tmul` : the transition lies over `A ⊗[R] A`.
* `ModuleCat.bijective_productMap_descentInvariants_of_isPushout` : **the algebraic half of step 4
  of the proof of Stacks 0APK.**  For `R → A` faithfully flat, and with the cocycle condition
  supplied as coassociativity of the unit, the canonical map `A ⊗[R] C₀ → C` out of the invariant
  `R`-subalgebra `C₀` is bijective.

## Implementation notes

The comparison `CommRingCat.tensorProductIsoOfIsPushout` is
`CategoryTheory.IsPushout.isoIsPushout` against `CommRingCat.isPushout_tensorProduct`; the four
element-level lemmas are the four `inl`/`inr` equations of that comparison, pushed through
`CommRingCat.Hom.hom`.  They are stated element-wise rather than as equalities of morphisms in
`CommRingCat` because every consumer multiplies two of them together inside the apex.

`ModuleCat.algebraTransitionOfPushout` is built as a `RingEquiv` first and promoted to an
`AlgEquiv` afterwards: its `R`-linearity is a *consequence* of the compatibility with
`A ⊗[R] A`, read at `a = algebraMap R A r` and `b = 1`, and so is not available before that
compatibility has been proved.

*How the output of Stacks 0APJ is read in this shape.*
`AlgebraicGeometry.isPushout_sectionsRingOnSubset_of_flat` names the **base** ring `A` and the
**flat** ring `R`, which is the opposite of the convention here: in the notation of this file its
base is `R`, its flat extension is `A`, and its apex is `C`.  Its two legs are arbitrary
morphisms of `CommRingCat`, not `algebraMap`s, so a consumer installs the algebra structures and
rewrites, which takes six lines:
```
letI : Algebra R A := ρ.hom.toAlgebra
letI : Algebra A C := γ.hom.toAlgebra
letI : Algebra R C := (ρ ≫ γ).hom.toAlgebra
have : IsScalarTower R A C :=
  IsScalarTower.of_algebraMap_eq' (by simp [RingHom.algebraMap_toAlgebra])
have hRC : CommRingCat.ofHom (algebraMap R C) = ρ ≫ γ := by
  rw [RingHom.algebraMap_toAlgebra]; exact CommRingCat.ofHom_hom (ρ ≫ γ)
```
and likewise for the other two legs; the pushout squares then transport by `rw`.  Here `ρ` is the
leg `Γ(Spec R, ⊤) ⟶ Γ(Spec A, ⊤)` of the base change and `γ` the structure morphism
`Γ(Spec A, ⊤) ⟶ Γ(E, 𝒪_V|_E)`.  That `CommRingCat.of ↥X` and `X` agree for an object `X` of
`CommRingCat` is definitional, so no further comparison is needed.

The cocycle condition is not derived here.  It enters
`ModuleCat.bijective_productMap_descentInvariants_of_isPushout` in the form
`ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc` asks for, namely
coassociativity of the unit `σ c = τ (c ⊗ 1)`; in the geometric application that is the cocycle
condition for the transition isomorphism of the descent datum, which the source of Stacks 0APK
transports with "details omitted".

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 023G](https://stacks.math.columbia.edu/tag/023G)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace CommRingCat

/-- Applying an equation `f ≫ g = k` of morphisms in `CommRingCat` to an element. -/
private lemma comp_apply_of_comp_eq {X Y Z : CommRingCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    (h : f ≫ g = k) (x : X) : g.hom (f.hom x) = k.hom x := by
  rw [← h]; rfl

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {P : CommRingCat.{u}} {iA : CommRingCat.of A ⟶ P} {iB : CommRingCat.of B ⟶ P}

/-- The apex of a pushout square of commutative rings with legs `A` and `B` over `R` is the
tensor product `A ⊗[R] B`.  This is the comparison isomorphism, obtained from
`CommRingCat.isPushout_tensorProduct`. -/
def tensorProductIsoOfIsPushout
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R B)) iA iB) :
    CommRingCat.of (A ⊗[R] B) ≅ P :=
  (CommRingCat.isPushout_tensorProduct R A B).isoIsPushout _ _ h

/-- The comparison isomorphism carries `a ⊗ 1` to the image of `a` under the first leg. -/
lemma tensorProductIsoOfIsPushout_hom_tmul_one
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R B)) iA iB) (a : A) :
    (tensorProductIsoOfIsPushout h).hom.hom (a ⊗ₜ[R] (1 : B)) = iA.hom a :=
  comp_apply_of_comp_eq
    ((CommRingCat.isPushout_tensorProduct R A B).inl_isoIsPushout_hom _ _ h) a

/-- The comparison isomorphism carries `1 ⊗ b` to the image of `b` under the second leg. -/
lemma tensorProductIsoOfIsPushout_hom_one_tmul
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R B)) iA iB) (b : B) :
    (tensorProductIsoOfIsPushout h).hom.hom ((1 : A) ⊗ₜ[R] b) = iB.hom b :=
  comp_apply_of_comp_eq
    ((CommRingCat.isPushout_tensorProduct R A B).inr_isoIsPushout_hom _ _ h) b

/-- The inverse of the comparison isomorphism carries the first leg to `a ⊗ 1`. -/
lemma tensorProductIsoOfIsPushout_inv_left
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R B)) iA iB) (a : A) :
    (tensorProductIsoOfIsPushout h).inv.hom (iA.hom a) = a ⊗ₜ[R] (1 : B) :=
  comp_apply_of_comp_eq
    ((CommRingCat.isPushout_tensorProduct R A B).inl_isoIsPushout_inv _ _ h) a

/-- The inverse of the comparison isomorphism carries the second leg to `1 ⊗ b`. -/
lemma tensorProductIsoOfIsPushout_inv_right
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R B)) iA iB) (b : B) :
    (tensorProductIsoOfIsPushout h).inv.hom (iB.hom b) = (1 : A) ⊗ₜ[R] b :=
  comp_apply_of_comp_eq
    ((CommRingCat.isPushout_tensorProduct R A B).inr_isoIsPushout_inv _ _ h) b

end CommRingCat

namespace ModuleCat

variable {R A C : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra A C]
    [Algebra R C] [IsScalarTower R A C] {P Q : CommRingCat.{u}}
    {iC : CommRingCat.of C ⟶ P} {iA : CommRingCat.of A ⟶ P}
    {kA : CommRingCat.of A ⟶ Q} {kC : CommRingCat.of C ⟶ Q}

variable (hP : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R A)) iC iA)
    (hQ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R C)) kA kC)
    (Φ : P ≅ Q)

/-- An elementary tensor is the product of its two one-sided factors. -/
private lemma tmul_eq_tmul_one_mul_one_tmul {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (a : A) (b : B) :
    a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The transition map of an algebra descent datum presented by two pushout squares and an
isomorphism of their apexes, as a ring isomorphism.  Its `R`-linearity needs the compatibility
of `Φ` with `A ⊗[R] A` and so is proved afterwards, in
`ModuleCat.algebraTransitionOfPushout`. -/
def ringTransitionOfPushout : (C ⊗[R] A) ≃+* (A ⊗[R] C) :=
  (CommRingCat.tensorProductIsoOfIsPushout hP ≪≫ Φ ≪≫
      (CommRingCat.tensorProductIsoOfIsPushout hQ).symm).commRingCatIsoToRingEquiv

omit [Algebra A C] [IsScalarTower R A C] in
/-- The transition is, on elements, the composite of the two comparison isomorphisms with
`Φ`. -/
lemma ringTransitionOfPushout_apply (x : C ⊗[R] A) :
    ringTransitionOfPushout hP hQ Φ x =
      (CommRingCat.tensorProductIsoOfIsPushout hQ).inv.hom
        (Φ.hom.hom ((CommRingCat.tensorProductIsoOfIsPushout hP).hom.hom x)) := rfl

omit [Algebra A C] [IsScalarTower R A C] in
/-- The transition sends `c ⊗ a` to the image under `Φ` of the product of the two legs of the
first square, read back in `A ⊗[R] C` through the second square.  This pins the transition down
completely, and is the form in which a geometric consumer verifies the cocycle condition. -/
lemma ringTransitionOfPushout_tmul (c : C) (a : A) :
    ringTransitionOfPushout hP hQ Φ (c ⊗ₜ[R] a) =
      (CommRingCat.tensorProductIsoOfIsPushout hQ).inv.hom
        (Φ.hom.hom (iC.hom c * iA.hom a)) := by
  rw [tmul_eq_tmul_one_mul_one_tmul, map_mul, ringTransitionOfPushout_apply,
    ringTransitionOfPushout_apply,
    CommRingCat.tensorProductIsoOfIsPushout_hom_tmul_one,
    CommRingCat.tensorProductIsoOfIsPushout_hom_one_tmul, ← map_mul, ← map_mul]

variable (h1 : CommRingCat.ofHom (algebraMap A C) ≫ iC ≫ Φ.hom = kA)
    (h2 : iA ≫ Φ.hom = CommRingCat.ofHom (algebraMap A C) ≫ kC)

omit [IsScalarTower R A C] in
include h1 h2 in
/-- **The transition lies over `A ⊗[R] A`.**  The two hypotheses on `Φ` say that it carries the
`C`-leg of the first square, precomposed with `A → C`, to the `A`-leg of the second, and the
`A`-leg of the first to the `C`-leg of the second, postcomposed with `A → C`.  Together with
multiplicativity that is exactly the equation
`τ (algebraMap A C a ⊗ b) = a ⊗ algebraMap A C b` of
`ModuleCat.bijective_productMap_descentInvariants`. -/
lemma ringTransitionOfPushout_algebraMap_tmul (a b : A) :
    ringTransitionOfPushout hP hQ Φ (algebraMap A C a ⊗ₜ[R] b) =
      a ⊗ₜ[R] algebraMap A C b := by
  have e1 : Φ.hom.hom (iC.hom (algebraMap A C a)) = kA.hom a := by
    exact CommRingCat.comp_apply_of_comp_eq h1 a
  have e2 : Φ.hom.hom (iA.hom b) = kC.hom (algebraMap A C b) := by
    exact CommRingCat.comp_apply_of_comp_eq h2 b
  rw [tmul_eq_tmul_one_mul_one_tmul, map_mul, ringTransitionOfPushout_apply,
    ringTransitionOfPushout_apply,
    CommRingCat.tensorProductIsoOfIsPushout_hom_tmul_one,
    CommRingCat.tensorProductIsoOfIsPushout_hom_one_tmul, e1, e2,
    CommRingCat.tensorProductIsoOfIsPushout_inv_left,
    CommRingCat.tensorProductIsoOfIsPushout_inv_right,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

include h1 h2 in
/-- **The transition isomorphism of an algebra descent datum presented by two pushout squares.**
Given pushout squares exhibiting `P` as `C ⊗[R] A` and `Q` as `A ⊗[R] C`, and an isomorphism
`Φ : P ≅ Q` over `A ⊗[R] A`, this is the transition isomorphism
`C ⊗[R] A ≃ₐ[R] A ⊗[R] C` that `ModuleCat.bijective_productMap_descentInvariants` consumes. -/
def algebraTransitionOfPushout : (C ⊗[R] A) ≃ₐ[R] (A ⊗[R] C) :=
  { ringTransitionOfPushout hP hQ Φ with
    commutes' := fun r => by
      have := ringTransitionOfPushout_algebraMap_tmul hP hQ Φ h1 h2 (algebraMap R A r) 1
      rw [← IsScalarTower.algebraMap_apply, map_one] at this
      exact this }

/-- On elements, `ModuleCat.algebraTransitionOfPushout` agrees with the ring isomorphism
`ModuleCat.ringTransitionOfPushout`. -/
lemma algebraTransitionOfPushout_apply (x : C ⊗[R] A) :
    algebraTransitionOfPushout hP hQ Φ h1 h2 x = ringTransitionOfPushout hP hQ Φ x := rfl

/-- `ModuleCat.algebraTransitionOfPushout` sends `c ⊗ a` to the image under `Φ` of the product of
the two legs of the first square, read back in `A ⊗[R] C`. -/
lemma algebraTransitionOfPushout_tmul (c : C) (a : A) :
    algebraTransitionOfPushout hP hQ Φ h1 h2 (c ⊗ₜ[R] a) =
      (CommRingCat.tensorProductIsoOfIsPushout hQ).inv.hom
        (Φ.hom.hom (iC.hom c * iA.hom a)) :=
  ringTransitionOfPushout_tmul hP hQ Φ c a

/-- `ModuleCat.algebraTransitionOfPushout` lies over `A ⊗[R] A`. -/
lemma algebraTransitionOfPushout_algebraMap_tmul (a b : A) :
    algebraTransitionOfPushout hP hQ Φ h1 h2 (algebraMap A C a ⊗ₜ[R] b) =
      a ⊗ₜ[R] algebraMap A C b :=
  ringTransitionOfPushout_algebraMap_tmul hP hQ Φ h1 h2 a b

/-- The unit of `ModuleCat.algebraTransitionOfPushout` is the `C`-leg of the first square,
transported by `Φ` and read back in `A ⊗[R] C`. -/
lemma algebraUnitTransition_algebraTransitionOfPushout (c : C) :
    algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2) c =
      (CommRingCat.tensorProductIsoOfIsPushout hQ).inv.hom (Φ.hom.hom (iC.hom c)) := by
  rw [algebraUnitTransition_apply, algebraTransitionOfPushout_tmul, map_one, mul_one]

include h1 h2 in
/-- **The algebraic half of step 4 of the proof of Stacks 0APK.**  Let `R → A` be faithfully
flat, let `C` be an `A`-algebra, and suppose given pushout squares of commutative rings
exhibiting `P` as `C ⊗[R] A` and `Q` as `A ⊗[R] C`, together with an isomorphism `Φ : P ≅ Q` of
their apexes lying over `A ⊗[R] A`.  If the unit `σ c = Φ(c)`, read in `A ⊗[R] C`, is
coassociative, then the canonical map `A ⊗[R] C₀ → C` out of the `R`-subalgebra `C₀` of
invariants is bijective.

In the proof of Stacks 0APK the two squares are the two instances of Stacks 0APJ for the
subsets `E ×_S X ⊆ V ×_S X` and `X ×_S E ⊆ X ×_S V`, `Φ` is induced by the transition
isomorphism of the descent datum, and `C₀` is the ring called `R'` there. -/
theorem bijective_productMap_descentInvariants_of_isPushout [Module.FaithfullyFlat R A]
    (hkey : ∀ c : C,
      LinearMap.lTensor A (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2))
          (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2) c) =
        LinearMap.lTensor A (TensorProduct.mk R A C 1)
          (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2) c)) :
    Function.Bijective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R A C)
      (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)).val) :=
  bijective_productMap_descentInvariants_of_unitCoassoc R A C _
    (algebraTransitionOfPushout_algebraMap_tmul hP hQ Φ h1 h2) hkey

end ModuleCat

end

end
