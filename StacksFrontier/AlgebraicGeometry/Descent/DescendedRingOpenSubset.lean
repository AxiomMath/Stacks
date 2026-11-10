module

public import StacksFrontier.AlgebraicGeometry.Descent.Modules.AlgebraDescentFromPushout
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFaithfullyFlatBaseChange

/-!
# The descended ring of an algebra descent datum, and the opens of its spectrum

This file joins the two halves of steps 4 and 5 of the proof of Stacks 0APK over an affine base.

Step 4 produces, from the two pushout squares of Stacks 0APJ and the transition isomorphism of a
descent datum, an `R`-algebra `R'` and an identification `R' ⊗_R A = Γ(E, 𝒪_V|_E)` of
`A`-algebras.  `ModuleCat.bijective_productMap_descentInvariants` delivers that identification as
the *bijectivity* of the canonical map out of the invariant subalgebra; what step 5 consumes is
the identification itself, in the form `Algebra.IsPushout R A R' Γ(E, 𝒪_V|_E)`.  The first result
below converts the one into the other, and the second states step 4's conclusion in that form.

Step 5 then descends an open subset of `Spec Γ(E, 𝒪_V|_E)` to one of `Spec R'`, which is
`AlgebraicGeometry.existsUnique_opens_preimage_eq_of_isPushout`.  The last result below is the
two chained.

## Main results

* `Algebra.IsPushout.of_bijective_productMap` : if the canonical map `A ⊗[R] C₀ → C` out of an
  `R`-subalgebra `C₀` of an `A`-algebra `C` is bijective, then `C` is the base change of `A`
  along `R → C₀`.
* `ModuleCat.isPushout_descentInvariants_of_isPushout` : **step 4 of the proof of Stacks 0APK,
  over an affine base.**  The ring of invariants of the transition isomorphism is an `R`-algebra
  whose base change to `A` is `C`.
* `ModuleCat.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq` : **steps 4 and 5
  chained.**  There is an `R`-subalgebra `C₀ ⊆ C` with `C = A ⊗[R] C₀`, and every open subscheme
  of `Spec C` whose two preimages in `Spec C ×_{Spec C₀} Spec C` agree is the preimage of a
  unique open subscheme of `Spec C₀`.

## Implementation notes

`Algebra.IsPushout.of_bijective_productMap` goes through `Algebra.IsPushout.of_equiv` applied to
the tautological pushout square `Algebra.IsPushout R A C₀ (A ⊗[R] C₀)`, which needs the
`C₀`-algebra structure on `A ⊗[R] C₀`.  That structure is
`Algebra.TensorProduct.rightAlgebra`, which Mathlib does not make a global instance; it is
enabled locally here, exactly as `CommRingCat.isPushout_iff_isPushout` does in Mathlib.

The comparison isomorphism is built from `Algebra.TensorProduct.productLeftAlgHom` rather than
from `Algebra.TensorProduct.productMap`, because `Algebra.IsPushout.of_equiv` asks for an
`A`-algebra isomorphism while `productMap` is only `R`-linear.  The two have the same underlying
function, so the bijectivity hypothesis transfers without an argument.

Nothing here derives the cocycle condition: it is carried through as the coassociativity
hypothesis `hkey` of `ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc`.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 023N](https://stacks.math.columbia.edu/tag/023N)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **A bijective canonical map out of a subalgebra exhibits a base change.**  Let `C` be an
`A`-algebra, let `A` be an `R`-algebra and let `C₀` be an `R`-subalgebra of `C`.  If the
canonical map `A ⊗[R] C₀ → C`, `a ⊗ c ↦ a · c`, is bijective, then `C` is the base change of `A`
along `R → C₀`.

This is the step which turns the conclusion of
`ModuleCat.bijective_productMap_descentInvariants` into the identification
`χ : R' ⊗_R A → Γ(E, 𝒪_V|_E)` that the proof of Stacks 0APK goes on to use. -/
theorem Algebra.IsPushout.of_bijective_productMap (R A C : Type u) [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    (C₀ : Subalgebra R C)
    (h : Function.Bijective
      (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R A C) C₀.val)) :
    Algebra.IsPushout R A C₀ C := by
  have hb : Function.Bijective
      (Algebra.TensorProduct.productLeftAlgHom (R := R) (Algebra.ofId A C) C₀.val) := h
  refine Algebra.IsPushout.of_equiv (AlgEquiv.ofBijective _ hb) ?_
  ext x
  change Algebra.TensorProduct.productLeftAlgHom (R := R) (Algebra.ofId A C) C₀.val
      ((1 : A) ⊗ₜ[R] x) = (x : C)
  simp

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
    (h1 : CommRingCat.ofHom (algebraMap A C) ≫ iC ≫ Φ.hom = kA)
    (h2 : iA ≫ Φ.hom = CommRingCat.ofHom (algebraMap A C) ≫ kC)

include h1 h2 in
/-- **Step 4 of the proof of Stacks 0APK, over an affine base.**  Let `R → A` be faithfully flat,
let `C` be an `A`-algebra, and suppose given pushout squares of commutative rings exhibiting `P`
as `C ⊗[R] A` and `Q` as `A ⊗[R] C`, an isomorphism `Φ : P ≅ Q` of their apexes lying over
`A ⊗[R] A`, and coassociativity of the unit of the resulting transition isomorphism.  Then `C` is
the base change to `A` of the `R`-subalgebra of invariants.

In the proof of Stacks 0APK the subalgebra is the ring called `R'`, and the pushout property is
the isomorphism `χ : R' ⊗_R A → Γ(E, 𝒪_V|_E)` of `A`-algebras. -/
theorem isPushout_descentInvariants_of_isPushout [Module.FaithfullyFlat R A]
    (hkey : ∀ c : C,
      LinearMap.lTensor A (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2))
          (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2) c) =
        LinearMap.lTensor A (TensorProduct.mk R A C 1)
          (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2) c)) :
    Algebra.IsPushout R A
      (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C :=
  Algebra.IsPushout.of_bijective_productMap R A C _
    (bijective_productMap_descentInvariants_of_isPushout hP hQ Φ h1 h2 hkey)

include h1 h2 in
/-- **Steps 4 and 5 of the proof of Stacks 0APK, over an affine base, chained.**  Under the
hypotheses of `ModuleCat.isPushout_descentInvariants_of_isPushout` there is an `R`-subalgebra
`C₀ ⊆ C` such that `C` is the base change of `A` along `R → C₀`, and such that every open
subscheme of `Spec C` whose two preimages in `Spec C ×_{Spec C₀} Spec C` agree is the preimage of
a unique open subscheme of `Spec C₀`.

The subalgebra is `ModuleCat.descentInvariants`; it is produced existentially here only so that
the statement of the open-descent clause can refer to it. -/
theorem exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq
    [Module.FaithfullyFlat R A]
    (hkey : ∀ c : C,
      LinearMap.lTensor A (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2))
          (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2) c) =
        LinearMap.lTensor A (TensorProduct.mk R A C 1)
          (algebraUnitTransition R A C (algebraTransitionOfPushout hP hQ Φ h1 h2) c)) :
    ∃ C₀ : Subalgebra R C, Algebra.IsPushout R A C₀ C ∧
      ∀ W' : (Spec (CommRingCat.of C)).Opens,
        (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))
              (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))).base ⁻¹'
            (W' : Set (Spec (CommRingCat.of C))) =
          (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))
              (Spec.map (CommRingCat.ofHom (algebraMap C₀ C)))).base ⁻¹'
            (W' : Set (Spec (CommRingCat.of C))) →
        ∃! W : (Spec (CommRingCat.of C₀)).Opens,
          Spec.map (CommRingCat.ofHom (algebraMap C₀ C)) ⁻¹ᵁ W = W' := by
  have := isPushout_descentInvariants_of_isPushout hP hQ Φ h1 h2 hkey
  exact ⟨_, this, fun W' hcompat => existsUnique_opens_preimage_eq_of_isPushout R A _ C W' hcompat⟩

end ModuleCat

end

end
