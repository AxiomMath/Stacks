module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamDoubleComplex

/-!
# A horizontal map of pairs read on the completed de Rham complexes

Let `p` be a prime, `D` a commutative ring, `Ω^*` a graded family of `D`-modules with a wedge
product and a de Rham differential, and let `(M, ∇_M)` and `(N, ∇_N)` be two modules over `D`
carrying completed connections with values in `Ω^1`. A `D`-linear map `e : M → N` is
*horizontal* when `∇_N (e m) = (e ⊗ 1)_* (∇_M m)`; that is the field
`Crystalline.PairHom.horizontal` of a morphism in the category
`Crystalline.Pair` of [Stacks, Tag 07JG].

This module reads such a map on the complexes `M ⊗^∧_D Ω^*_D` of
`Crystalline.CompletedDeRham.complex`: a horizontal map induces a morphism of complexes, and a
horizontal **isomorphism** induces an isomorphism of complexes.

## Main definitions

* `Crystalline.CompletedDeRham.horizontalTerm` — the degree-`i` component `(e ⊗ 1)^` of the map
  of completed de Rham complexes induced by a `D`-linear map `e : M → N`.
* `Crystalline.CompletedDeRham.horizontalComplexHom` — the morphism of complexes induced by a
  horizontal map.
* `Crystalline.CompletedDeRham.horizontalComplexIso` — the isomorphism of complexes induced by a
  horizontal `D`-linear equivalence.
* `Crystalline.CompletedDeRham.pairComplexIso` — the same for an isomorphism in the category
  `Crystalline.Pair` of [Stacks, Tag 07JG].

## Main results

* `Crystalline.CompletedDeRham.horizontalTerm_comm` — the chain-map square.
* `Crystalline.CompletedDeRham.horizontalTerm_bijective` — the degreewise component of the map
  induced by a `D`-linear equivalence is bijective.
* `Crystalline.CompletedDeRham.isSquareZero_of_horizontalEquiv` — the square-zero condition
  transports along a horizontal `D`-linear equivalence.
* `Crystalline.CompletedDeRham.isIso_horizontalComplexHom` — the induced morphism is an
  isomorphism.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers
open scoped TensorProduct

universe uD uM uO uI

namespace Crystalline

namespace CompletedDeRham

section Horizontal

variable (p : ℕ) (D : Type uD) [CommRing D] (M : Type uM) [AddCommGroup M] [Module D M]
  (N : Type uM) [AddCommGroup N] [Module D N] (Om : ℕ → Type uO) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (e : M →ₗ[D] N)

/-- **The degree-`i` component of the map of completed de Rham complexes induced by a
`D`-linear map `e : M → N`**: the completion of `e ⊗ 1 : M ⊗_D Ω^i_D → N ⊗_D Ω^i_D`. -/
def horizontalTerm (i : ℕ) :
    CompletedTensor p D (Om i) M →+ CompletedTensor p D (Om i) N :=
  (AdicCompletion.map (pAdicIdeal (A := D) p)
    (TensorProduct.map e (LinearMap.id (R := D) (M := Om i)))).toAddMonoidHom

/-- The degree-`i` component on the image of an uncompleted pure tensor: `m ⊗ ω ↦ e m ⊗ ω`. -/
@[simp] theorem horizontalTerm_of_tmul (i : ℕ) (m : M) (ω : Om i) :
    horizontalTerm p D M N Om e i (toCompletedTensor p D (Om i) M (m ⊗ₜ[D] ω)) =
      toCompletedTensor p D (Om i) N (e m ⊗ₜ[D] ω) :=
  rfl

/-- The degree-`i` component is the semilinear comparison of
`Crystalline.CompletedDeRham.comparisonValues` for the identity ring map and the identity
comparison of forms. -/
theorem horizontalTerm_eq_comparisonValues (i : ℕ) (x : CompletedTensor p D (Om i) M) :
    horizontalTerm p D M N Om e i x =
      comparisonValues p D D (RingHom.id D) M N e Om Om (fun _ ↦ LinearMap.id) i x :=
  adicCompletionMap_eq_mapₛₗ _ _ x

variable (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1)) (deRham : ∀ i, Om i →+ Om (i + 1))
  {dmap : D → Om 1} (nablaM : CompletedConnection p D (Om 1) dmap M)
  (nablaN : CompletedConnection p D (Om 1) dmap N)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)
  (hnabla : ∀ m : M, nablaN (e m) =
    AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map e (LinearMap.id (R := D) (M := Om 1))) (nablaM m))

include hnabla in
/-- **The chain-map square of a horizontal map**: the degree-`i` component commutes with the two
de Rham differentials. -/
theorem horizontalTerm_comm (i : ℕ) (x : CompletedTensor p D (Om i) M) :
    differential p D Om wedge deRham N nablaN hleib i (horizontalTerm p D M N Om e i x) =
      horizontalTerm p D M N Om e (i + 1)
        (differential p D Om wedge deRham M nablaM hleib i x) := by
  rw [horizontalTerm_eq_comparisonValues, horizontalTerm_eq_comparisonValues]
  refine differential_comparisonValues p D D (RingHom.id D) M N e Om Om
    (fun _ ↦ LinearMap.id) wedge wedge deRham deRham nablaM nablaN hleib hleib
    (fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun m ↦ ?_) i x
  rw [hnabla m]
  exact horizontalTerm_eq_comparisonValues p D M N Om e 1 (nablaM m)

include hnabla in
/-- **The morphism of completed de Rham complexes induced by a horizontal map**
`M ⊗^∧_D Ω^*_D ⟶ N ⊗^∧_D Ω^*_D`, whose degree-`i` component is
`Crystalline.CompletedDeRham.horizontalTerm`. -/
def horizontalComplexHom (hsqM : IsSquareZero p D Om wedge deRham M nablaM hleib)
    (hsqN : IsSquareZero p D Om wedge deRham N nablaN hleib) :
    complex p D Om wedge deRham M nablaM hleib hsqM ⟶
      complex p D Om wedge deRham N nablaN hleib hsqN :=
  CochainComplex.ofHom (fun i ↦ AddCommGrpCat.ofHom (horizontalTerm p D M N Om e i))
    (fun i ↦ by
      rw [complex_d, complex_d]
      exact AddCommGrpCat.ext fun x ↦ horizontalTerm_comm p D M N Om e wedge deRham nablaM
        nablaN hleib hnabla i x)

/-- The degree-`i` component of the induced morphism of complexes. -/
@[simp] theorem horizontalComplexHom_f
    (hsqM : IsSquareZero p D Om wedge deRham M nablaM hleib)
    (hsqN : IsSquareZero p D Om wedge deRham N nablaN hleib) (i : ℕ) :
    (horizontalComplexHom p D M N Om e wedge deRham nablaM nablaN hleib hnabla hsqM hsqN).f i =
      AddCommGrpCat.ofHom (horizontalTerm p D M N Om e i) :=
  rfl

end Horizontal

section HorizontalEquiv

variable (p : ℕ) (D : Type uD) [CommRing D] (M : Type uM) [AddCommGroup M] [Module D M]
  (N : Type uM) [AddCommGroup N] [Module D N] (Om : ℕ → Type uO) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] (e : M ≃ₗ[D] N)

/-- The degree-`i` component of the map induced by a `D`-linear equivalence is bijective. -/
theorem horizontalTerm_bijective (i : ℕ) :
    Function.Bijective (horizontalTerm p D M N Om (e : M →ₗ[D] N) i) :=
  (AdicCompletion.congr (pAdicIdeal (A := D) p)
    (TensorProduct.congr e (LinearEquiv.refl D (Om i)))).bijective

variable (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1)) (deRham : ∀ i, Om i →+ Om (i + 1))
  {dmap : D → Om 1} (nablaM : CompletedConnection p D (Om 1) dmap M)
  (nablaN : CompletedConnection p D (Om 1) dmap N)
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)
  (hnabla : ∀ m : M, nablaN (e m) =
    AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map (e : M →ₗ[D] N) (LinearMap.id (R := D) (M := Om 1))) (nablaM m))

include hnabla in
/-- **The square-zero condition transports along a horizontal `D`-linear equivalence.** -/
theorem isSquareZero_of_horizontalEquiv
    (hsqM : IsSquareZero p D Om wedge deRham M nablaM hleib) :
    IsSquareZero p D Om wedge deRham N nablaN hleib := by
  intro i
  refine AddMonoidHom.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (horizontalTerm_bijective p D M N Om e i).2 y
  change differential p D Om wedge deRham N nablaN hleib (i + 1)
      (differential p D Om wedge deRham N nablaN hleib i
        (horizontalTerm p D M N Om (e : M →ₗ[D] N) i x)) = 0
  rw [horizontalTerm_comm p D M N Om (e : M →ₗ[D] N) wedge deRham nablaM nablaN hleib hnabla,
    horizontalTerm_comm p D M N Om (e : M →ₗ[D] N) wedge deRham nablaM nablaN hleib hnabla,
    show differential p D Om wedge deRham M nablaM hleib (i + 1)
        (differential p D Om wedge deRham M nablaM hleib i x) = 0 from
      DFunLike.congr_fun (hsqM i) x, map_zero]

include hnabla in
/-- **The morphism of complexes induced by a horizontal `D`-linear equivalence is an
isomorphism.** -/
theorem isIso_horizontalComplexHom (hsqM : IsSquareZero p D Om wedge deRham M nablaM hleib)
    (hsqN : IsSquareZero p D Om wedge deRham N nablaN hleib) :
    IsIso (horizontalComplexHom p D M N Om (e : M →ₗ[D] N) wedge deRham nablaM nablaN hleib
      hnabla hsqM hsqN) := by
  have : ∀ i : ℕ, IsIso ((horizontalComplexHom p D M N Om (e : M →ₗ[D] N) wedge deRham nablaM
      nablaN hleib hnabla hsqM hsqN).f i) := fun i ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (horizontalTerm_bijective p D M N Om e i)
  exact HomologicalComplex.Hom.isIso_of_components _

include hnabla in
/-- **The isomorphism of completed de Rham complexes induced by a horizontal `D`-linear
equivalence**, `M ⊗^∧_D Ω^*_D ≅ N ⊗^∧_D Ω^*_D`. -/
def horizontalComplexIso (hsqM : IsSquareZero p D Om wedge deRham M nablaM hleib)
    (hsqN : IsSquareZero p D Om wedge deRham N nablaN hleib) :
    complex p D Om wedge deRham M nablaM hleib hsqM ≅
      complex p D Om wedge deRham N nablaN hleib hsqN :=
  haveI := isIso_horizontalComplexHom p D M N Om e wedge deRham nablaM nablaN hleib hnabla
    hsqM hsqN
  asIso (horizontalComplexHom p D M N Om (e : M →ₗ[D] N) wedge deRham nablaM nablaN hleib
    hnabla hsqM hsqN)

end HorizontalEquiv

section PairIso

variable (p : ℕ) (D : Type uD) [CommRing D] (Om : ℕ → Type uO) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module D (Om i)] {ι : Type uI} (dx : ι → Om 1) {dmap : D → Om 1}
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1)) (deRham : ∀ i, Om i →+ Om (i + 1))
  (hleib : IsGradedLeibniz D Om wedge deRham dmap)

/-- The `D`-linear equivalence underlying an isomorphism of pairs. -/
def pairIsoLinearEquiv {P Q : Pair.{uD, uO, uI, uM} p D (Om 1) dx dmap} (f : P ≅ Q) :
    P.carrier ≃ₗ[D] Q.carrier :=
  LinearEquiv.ofLinearMap f.hom.toLinearMap f.inv.toLinearMap
    (congrArg PairHom.toLinearMap f.inv_hom_id) (congrArg PairHom.toLinearMap f.hom_inv_id)

/-- **An isomorphism of pairs gives an isomorphism of their completed de Rham complexes.** -/
def pairComplexIso {P Q : Pair.{uD, uO, uI, uM} p D (Om 1) dx dmap} (f : P ≅ Q)
    (hsqP : IsSquareZero p D Om wedge deRham P.carrier P.nabla hleib) :
    complex p D Om wedge deRham P.carrier P.nabla hleib hsqP ≅
      complex p D Om wedge deRham Q.carrier Q.nabla hleib
        (isSquareZero_of_horizontalEquiv p D P.carrier Q.carrier Om
          (pairIsoLinearEquiv p D Om dx f) wedge deRham P.nabla Q.nabla hleib
          f.hom.horizontal hsqP) :=
  horizontalComplexIso p D P.carrier Q.carrier Om (pairIsoLinearEquiv p D Om dx f) wedge deRham
    P.nabla Q.nabla hleib f.hom.horizontal hsqP _

end PairIso

end CompletedDeRham

end Crystalline

end
