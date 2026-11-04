module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedEquivalenceBimodule
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorLinear
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact

/-! # A quasi-isomorphism of differential graded algebras gives a derived equivalence

Let `φ : (A, d) → (B, d)` be a homomorphism of differential graded algebras over a commutative
ring `R` which induces an isomorphism on cohomology algebras. [Stacks, Tag 09S6] says that
$$- \otimes_A^{\mathbf L} B : D(A, \text{d}) \longrightarrow D(B, \text{d})$$
is an equivalence of triangulated categories, with quasi-inverse the restriction functor
`N ↦ N_A`.

The route is the one the source takes. Extension of scalars is tensoring with the regular
differential graded `(A, B)`-bimodule `B` of Tag 0BYX, and for that bimodule the three
hypotheses of Tag 09S7 read as follows.

1. *Compactness.* The class of `B` in `D(B, d)` is compact — this is
   `DifferentialGradedModule.isCompactObject_q_regularModule`, a global instance, and needs no
   hypothesis.
2. *Generation.* The class of `B` is a weak generator of `D(B, d)` — this is
   `DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule`, again
   hypothesis-free.
3. *Endomorphisms.* The canonical map `H^k(A) → Hom_{D(B,d)}(B, B[k])` is bijective. This is the
   only place the hypothesis on `φ` enters, and identifying that map is the work done here: for
   the regular bimodule a degree-`k` cocycle of `A` acts on `B` by multiplication by its image
   under `φ`, so the comparison map factors as
   `H^k(A) → H^k(B) ≅ Hom_{D(B,d)}(B, B[k])`, the second map being the representability
   isomorphism of `DifferentialGradedModule.cohomologyEquivDerivedHom`. Hence the comparison is
   bijective in degree `k` exactly when `H^k(φ)` is.

So the equivalence is `DifferentialGraded.Bimodule.derivedTensorEquivalence` (Tag 09S7) for the
regular bimodule. Its quasi-inverse is derived Hom `RHom(B, -)`, which Example 22.33.2 of
Tag 0BYX identifies with derived restriction of scalars — this is
`DifferentialGradedModule.DerivedHomData.functorIsoDerivedRestriction` — and transporting the
equivalence along that isomorphism makes the quasi-inverse the restriction functor on the nose.

## Main definitions

* `DifferentialGradedAlgebra.Hom.cohomologyMap`: the map `H^k(A) → H^k(B)` induced by a
  homomorphism of differential graded algebras.
* `DifferentialGraded.Bimodule.derivedExtensionEquivalence`: **Stacks 09S6**, the equivalence
  `D(A, d) ≌ D(B, d)` given by `- ⊗_A^𝐋 B`, with derived restriction of scalars as its
  quasi-inverse.

## Main results

* `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison_regular`: for the regular
  bimodule, the endomorphism comparison of Tag 09R9 is `H^k(φ)` followed by the representability
  isomorphism `H^k(B) ≅ Hom_{D(B,d)}(B, B[k])`.
* `DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_regular_iff`:
  consequently that comparison is bijective exactly when `H^k(φ)` is.
* `DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor_regular`: **Stacks 09S6** in
  the form "`- ⊗_A^𝐋 B` is an equivalence".
* `DifferentialGraded.Bimodule.derivedExtensionEquivalence_functor` and
  `DifferentialGraded.Bimodule.derivedExtensionEquivalence_inverse`: the two halves of the
  equivalence are extension and restriction of scalars.
* `DifferentialGraded.Bimodule.derivedExtensionEquivalence_linear`: **Stacks 09S6**, the
  `R`-linearity of the equivalence — both halves are `R`-linear, so it is an equivalence of
  `R`-linear triangulated categories as the source states.

## Implementation notes

*How the hypothesis "isomorphism on cohomology algebras" is spelled.* The hypothesis below is
that `DifferentialGradedAlgebra.Hom.cohomologyMap φ k` is bijective for every `k : ℤ`. That is
the source's hypothesis and not a weakening of it: the map induced on cohomology by an algebra
homomorphism is automatically a homomorphism of graded algebras, so "`φ` induces an isomorphism
on cohomology algebras" says exactly that this induced map is bijective in every degree. The
multiplicative half is recorded explicitly, on representatives, by
`DifferentialGradedAlgebra.Hom.cohomologyMap_cocycleMul` and
`DifferentialGradedAlgebra.Hom.cohomologyMap_cocycleOne`: the induced map carries the class of a
product of cocycles to the product of the classes, and the class of `1` to the class of `1`. It
is not stated as a morphism of graded `R`-algebras because this development equips
`DifferentialGradedAlgebra.Cohomology` with no algebra structure — it is a bare quotient of the
cocycles, with no additive structure either.

*What "`R`-linear equivalence of triangulated categories" amounts to.* The functor
`- ⊗_A^𝐋 B` is exact before any hypothesis: it commutes with the translation by
`DifferentialGraded.Bimodule.derivedTensorFunctor_commShift` and preserves distinguished
triangles by `DifferentialGraded.Bimodule.derivedTensorFunctor_isTriangulated` (Tags 09LR and
09LS), and its quasi-inverse is then exact as the right adjoint of an exact functor
(`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`, Tag 0A8D). It is `R`-linear before any
hypothesis as well: the derived categories are `R`-linear
(`DifferentialGradedModule.instLinearDerivedCategory`) and
`DifferentialGraded.Bimodule.derivedTensorFunctor_linear` (Tag 09S7) is a global instance giving
`(- ⊗_A^𝐋 N).Linear R` for every bimodule `N`. The quasi-inverse of an `R`-linear equivalence is
`R`-linear (`CategoryTheory.Equivalence.inverseLinear`), so both halves of the equivalence below
are `R`-linear; that is
`DifferentialGraded.Bimodule.derivedExtensionEquivalence_linear`.

*Why the regular bimodule has to be made locally reducible.* The bimodule
`DifferentialGraded.Bimodule.regular φ` has `DifferentialGradedModule.regularModule B` as its
underlying right module by definitional unfolding only, and the elaborator's `implicit`
transparency level — at which the rewriting tactics check their results — does not unfold a
plain `def`. Without the local `implicit_reducible` attribute below, a rewrite with a lemma about
`regularModule B` fails inside a goal about `(Bimodule.regular φ).rightModule` even though the
two are the same module.

As everywhere in this chapter's differential graded interface, the base ring, the algebras and
the modules all live in a single universe `u`, following Tag 09JJ.

## References

* [Stacks Project, Tag 09S6](https://stacks.math.columbia.edu/tag/09S6), the result proved here.
* [Stacks Project, Tag 09R9](https://stacks.math.columbia.edu/tag/09R9) for full faithfulness,
  [Tag 09S7](https://stacks.math.columbia.edu/tag/09S7) for the criterion of equivalence,
  [Tag 09LT](https://stacks.math.columbia.edu/tag/09LT) for the adjunction,
  [Tag 09J1](https://stacks.math.columbia.edu/tag/09J1) for the underlying triangulated
  criterion, and [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), Example 22.33.2, for the
  regular bimodule and the identification of `RHom(B, -)` with restriction of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DifferentialGradedModule

universe u

attribute [local implicit_reducible] DifferentialGradedModule.toCochainComplex
  DifferentialGraded.Bimodule.regular

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-! ### The map induced on cohomology -/

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- The image under a homomorphism of differential graded algebras of a degree-`k` cocycle: it is
again homogeneous of degree `k`, and killed by the differential because the homomorphism commutes
with the differentials. -/
def Hom.cocycleMap (φ : A.Hom B) (k : ℤ) (a : A.Cocycle k) : B.Cocycle k :=
  ⟨⟨φ.toAlgebraHom a.1, φ.map_grading k a.1 a.1.property⟩, by
    change B.d (φ.toAlgebraHom (a.1 : A.A)) = 0
    rw [← φ.map_d, show A.d (a.1 : A.A) = 0 from a.2, map_zero]⟩

@[simp] theorem Hom.cocycleMap_val (φ : A.Hom B) (k : ℤ) (a : A.Cocycle k) :
    ((φ.cocycleMap k a).1 : B.A) = φ.toAlgebraHom a.1 :=
  rfl

/-- **The map induced on cohomology by a homomorphism of differential graded algebras.** A
homomorphism carries cocycles to cocycles and coboundaries to coboundaries, so it descends to
`H^k(A) → H^k(B)`. -/
def Hom.cohomologyMap (φ : A.Hom B) (k : ℤ) : A.Cohomology k → B.Cohomology k :=
  Quotient.map (φ.cocycleMap k) (by
    rintro a b ⟨c, hc⟩
    refine ⟨⟨φ.toAlgebraHom c, φ.map_grading (k - 1) c c.property⟩, ?_⟩
    change φ.toAlgebraHom (a.1 : A.A) - φ.toAlgebraHom (b.1 : A.A) =
      B.d (φ.toAlgebraHom (c : A.A))
    rw [← map_sub, ← φ.map_d, hc])

@[simp] theorem Hom.cohomologyMap_mk (φ : A.Hom B) (k : ℤ) (a : A.Cocycle k) :
    φ.cohomologyMap k (Quotient.mk _ a) = Quotient.mk _ (φ.cocycleMap k a) :=
  rfl

/-- The unit of a differential graded algebra, as a degree-zero cocycle. -/
def cocycleOne (A : DifferentialGradedAlgebra R) : A.Cocycle 0 :=
  ⟨⟨1, SetLike.one_mem_graded A.grading⟩, A.d_one⟩

/-- The product of a degree-`k` cocycle and a degree-`l` cocycle, a cocycle of degree `k + l`:
the product is homogeneous of degree `k + l` because the grading is multiplicative, and is killed
by the differential by the Leibniz rule. -/
def cocycleMul {A : DifferentialGradedAlgebra R} {k l : ℤ} (a : A.Cocycle k) (b : A.Cocycle l) :
    A.Cocycle (k + l) :=
  ⟨⟨(a.1 : A.A) * b.1, SetLike.mul_mem_graded a.1.property b.1.property⟩, by
    change A.d ((a.1 : A.A) * (b.1 : A.A)) = 0
    rw [A.leibniz k l _ _ a.1.property b.1.property,
      show A.d (a.1 : A.A) = 0 from a.2, show A.d (b.1 : A.A) = 0 from b.2]
    simp⟩

/-- A homomorphism of differential graded algebras carries the product of two cocycles to the
product of their images: its underlying map is multiplicative. -/
theorem Hom.cocycleMap_cocycleMul (φ : A.Hom B) {k l : ℤ} (a : A.Cocycle k) (b : A.Cocycle l) :
    φ.cocycleMap (k + l) (cocycleMul a b) =
      cocycleMul (φ.cocycleMap k a) (φ.cocycleMap l b) := by
  refine Subtype.ext (Subtype.ext ?_)
  change φ.toAlgebraHom ((a.1 : A.A) * (b.1 : A.A)) =
    φ.toAlgebraHom (a.1 : A.A) * φ.toAlgebraHom (b.1 : A.A)
  exact map_mul _ _ _

/-- A homomorphism of differential graded algebras carries the unit cocycle to the unit
cocycle. -/
theorem Hom.cocycleMap_cocycleOne (φ : A.Hom B) :
    φ.cocycleMap 0 A.cocycleOne = B.cocycleOne := by
  refine Subtype.ext (Subtype.ext ?_)
  change φ.toAlgebraHom (1 : A.A) = (1 : B.A)
  exact map_one _

/-- **The induced map on cohomology is multiplicative.** On classes of cocycles, the map
`H^{k+l}(A) → H^{k+l}(B)` carries the class of a product to the product of the classes. Together
with `DifferentialGradedAlgebra.Hom.cohomologyMap_cocycleOne` this is the statement that the
induced map is a homomorphism of cohomology algebras, which is why the bijectivity of
`DifferentialGradedAlgebra.Hom.cohomologyMap` in every degree is exactly the hypothesis of
[Stacks, Tag 09S6] that `φ` induces an isomorphism on cohomology *algebras*. -/
theorem Hom.cohomologyMap_cocycleMul (φ : A.Hom B) {k l : ℤ}
    (a : A.Cocycle k) (b : A.Cocycle l) :
    φ.cohomologyMap (k + l) (Quotient.mk _ (cocycleMul a b)) =
      Quotient.mk _ (cocycleMul (φ.cocycleMap k a) (φ.cocycleMap l b)) := by
  rw [Hom.cohomologyMap_mk, Hom.cocycleMap_cocycleMul]

/-- **The induced map on cohomology is unital.** -/
theorem Hom.cohomologyMap_cocycleOne (φ : A.Hom B) :
    φ.cohomologyMap 0 (Quotient.mk _ A.cocycleOne) = Quotient.mk _ B.cocycleOne := by
  rw [Hom.cohomologyMap_mk, Hom.cocycleMap_cocycleOne]

end DifferentialGradedAlgebra

/-! ### The endomorphism comparison of the regular bimodule -/

namespace DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- **The left action of the regular bimodule is multiplication by the image element.** For the
regular differential graded `(A, B)`-bimodule of `φ : A → B`, left multiplication by a
homogeneous element `a` of `A` is left multiplication by `φ a` on the regular `B`-module. -/
theorem leftMultiplication_regular (φ : A.Hom B) (k : ℤ) (a : A.grading k) :
    (Bimodule.regular φ).leftMultiplication k a =
      regularHomogeneousMul B k ⟨φ.toAlgebraHom a, φ.map_grading k a a.property⟩ := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  induction x using DirectSum.Decomposition.inductionOn (regularModule B).grading with
  | zero => simp only [map_zero]
  | @homogeneous p x =>
    rw [leftMultiplication_apply (Bimodule.regular φ) k p a x,
      regularHomogeneousMul_val_apply]
    exact regularBimoduleStructure_action φ k p a x
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **A cocycle acts on the regular bimodule through its image.** The homomorphism
`B ⟶ B[k]` by which a degree-`k` cocycle `a` of `A` acts on the regular bimodule of `φ` is the
one attached by `DifferentialGradedModule.regularCocycleHom` to the cocycle `φ a` of `B`; both
are left multiplication by `φ a`. -/
theorem cocycleAction_regular (φ : A.Hom B) (k : ℤ) (a : A.Cocycle k) :
    (Bimodule.regular φ).cocycleAction k a = regularCocycleHom B k (φ.cocycleMap k a) := by
  refine DifferentialGradedModule.Hom.ext ?_
  rw [cocycleAction_toFun, regularCocycleHom_toFun, leftMultiplication_regular]
  rfl

/-- **The endomorphism comparison of the regular bimodule is the map induced on cohomology.** For
`N = B` the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` of
`DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` — hypothesis (2) of
[Stacks, Tag 09R9] and hypothesis (3) of [Stacks, Tag 09S7] — is the map `H^k(φ)` of
`DifferentialGradedAlgebra.Hom.cohomologyMap` followed by the representability map
`H^k(B) → Hom_{D(B,d)}(B, B[k])` of
`DifferentialGradedModule.cohomologyToDerivedCategory`.

Both sides are defined by lifting through the quotient by coboundaries, so this is
`DifferentialGraded.Bimodule.cocycleAction_regular` on representatives. -/
theorem cohomologyEndomorphismComparison_regular (φ : A.Hom B) (k : ℤ) :
    (Bimodule.regular φ).cohomologyEndomorphismComparison k =
      cohomologyToDerivedCategory B k ∘ φ.cohomologyMap k := by
  funext x
  refine Quotient.inductionOn x fun a => ?_
  rw [cohomologyEndomorphismComparison_mk, cocycleAction_regular]
  rfl

/-- **For the regular bimodule, hypothesis (2) of Tag 09R9 is the hypothesis of Tag 09S6.** The
canonical map `H^k(A) → Hom_{D(B,d)}(B, B[k])` is bijective exactly when the map `H^k(φ)` induced
by `φ` on degree-`k` cohomology is, the representability map `H^k(B) → Hom_{D(B,d)}(B, B[k])`
being bijective by `DifferentialGradedModule.cohomologyToDerivedCategory_bijective`. -/
theorem bijective_cohomologyEndomorphismComparison_regular_iff (φ : A.Hom B) (k : ℤ) :
    Function.Bijective ((Bimodule.regular φ).cohomologyEndomorphismComparison k) ↔
      Function.Bijective (φ.cohomologyMap k) := by
  rw [cohomologyEndomorphismComparison_regular]
  exact (cohomologyToDerivedCategory_bijective B k).of_comp_iff' _

/-! ### Tag 09S6 -/

/-- The class of the regular bimodule of `φ` in `D(B, d)` is a compact object: it is the class of
the regular `B`-module, and `DifferentialGradedModule.isCompactObject_q_regularModule` is a
global instance. Recorded as an instance here so that the hypothesis of Tag 09S7 is found for
`N = B`, whose underlying right module is `regularModule B` by unfolding only. -/
instance isCompactObject_q_regular (φ : A.Hom B) :
    IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
      (Bimodule.regular φ).rightModule) :=
  isCompactObject_q_regularModule B

/-- **Stacks 09S6**, in the form "`- ⊗_A^𝐋 B` is an equivalence". Let `φ : (A, d) → (B, d)` be a
homomorphism of differential graded algebras over a commutative ring `R` which induces an
isomorphism on cohomology algebras — that is, `H^k(φ) : H^k(A) → H^k(B)` is bijective for every
`k : ℤ`. Then extension of scalars `- ⊗_A^𝐋 B : D(A, d) ⥤ D(B, d)`, the derived tensor product
with the regular differential graded `(A, B)`-bimodule of Tag 0BYX, is an equivalence of
categories.

The functor is exact and `R`-linear before any hypothesis (Tags 09LR, 09LS and 09S7, all
instances), so this is the source's `R`-linear equivalence of triangulated categories; the
`R`-linearity is recorded separately at
`DifferentialGraded.Bimodule.derivedExtensionEquivalence_linear`.

This is Tag 09S7 for `N = B`. Its hypothesis (1) is
`DifferentialGraded.Bimodule.isCompactObject_q_regular`, its hypothesis (2) is
`DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule` verbatim, and its
hypothesis (3) is the hypothesis on `φ` through
`DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_regular_iff`. -/
@[stacks 09S6 "the equivalence of triangulated categories"]
theorem isEquivalence_derivedTensorFunctor_regular (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedTensorFunctor (Bimodule.regular φ)).IsEquivalence :=
  isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator (Bimodule.regular φ)
    (isWeakTriangulatedGenerator_q_regularModule B)
    fun k => (bijective_cohomologyEndomorphismComparison_regular_iff φ k).2 (hφ k)

/-- **Stacks 09S6.** Let `φ : (A, d) → (B, d)` be a homomorphism of differential graded algebras
over a commutative ring `R` inducing an isomorphism on cohomology algebras. Then extension of
scalars `- ⊗_A^𝐋 B` is one half of an equivalence `D(A, d) ≌ D(B, d)` whose other half is
derived restriction of scalars `N ↦ N_A`.

The equivalence is `DifferentialGraded.Bimodule.derivedTensorEquivalence` (Tag 09S7) for the
regular bimodule, whose quasi-inverse is derived Hom `RHom(B, -)`, transported along the
identification of `RHom(B, -)` with derived restriction of scalars
(`DifferentialGradedModule.DerivedHomData.functorIsoDerivedRestriction`, Example 22.33.2 of
Tag 0BYX). `CategoryTheory.Equivalence.changeInverse` leaves the functor untouched and replaces
the inverse by the isomorphic one, so both halves are what the source names:
`DifferentialGraded.Bimodule.derivedExtensionEquivalence_functor` and
`DifferentialGraded.Bimodule.derivedExtensionEquivalence_inverse` are both true by
`rfl`.

Both functors are exact: extension of scalars by Tags 09LR and 09LS, restriction of scalars as
the right adjoint of an exact functor (Tag 0A8D). Both are `R`-linear by
`DifferentialGraded.Bimodule.derivedExtensionEquivalence_linear`, so this is the source's
`R`-linear equivalence of triangulated categories. -/
@[stacks 09S6 "the equivalence of triangulated categories with restriction of scalars as \
quasi-inverse"]
def derivedExtensionEquivalence (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    derivedCategory' A ≌ derivedCategory' B :=
  (derivedTensorEquivalence (Bimodule.regular φ)
      ((ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero _).1
        (isWeakTriangulatedGenerator_q_regularModule B))
      fun k => (bijective_cohomologyEndomorphismComparison_regular_iff φ k).2
        (hφ k)).changeInverse
    (DerivedHomData.functorIsoDerivedRestriction φ
      (derivedHomData A B (regularModule B) (regularBimoduleStructure φ)))

/-- **The equivalence of Tag 09S6 goes by extension of scalars.** -/
@[stacks 09S6 "the functor of the equivalence is extension of scalars"]
theorem derivedExtensionEquivalence_functor (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).functor = derivedTensorFunctor (Bimodule.regular φ) :=
  rfl

/-- **The quasi-inverse of Tag 09S6 is restriction of scalars.** This is the half of the
conclusion of Tag 09S6 that names the quasi-inverse: `N ↦ N_A`. -/
@[stacks 09S6 "the quasi-inverse of the equivalence is restriction of scalars"]
theorem derivedExtensionEquivalence_inverse (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).inverse = derivedRestriction φ :=
  rfl

/-- **The equivalence of Tag 09S6 is `R`-linear.** This is the remaining half of the source's
conclusion that `- ⊗_A^𝐋 B : D(A, d) → D(B, d)` is an *`R`-linear* equivalence of triangulated
categories: both the functor and its quasi-inverse are `R`-linear.

The functor is `- ⊗_A^𝐋 B` by `DifferentialGraded.Bimodule.derivedExtensionEquivalence_functor`,
and `DifferentialGraded.Bimodule.derivedTensorFunctor_linear` (Tag 09S7) gives the `R`-linearity
of the derived tensor product with any bimodule, with no hypotheses; the quasi-inverse of an
`R`-linear equivalence is `R`-linear by `CategoryTheory.Equivalence.inverseLinear`. -/
@[stacks 09S6 "the R-linearity of the equivalence and of its quasi-inverse"]
theorem derivedExtensionEquivalence_linear (φ : A.Hom B)
    (hφ : ∀ k : ℤ, Function.Bijective (φ.cohomologyMap k)) :
    (derivedExtensionEquivalence φ hφ).functor.Linear R ∧
      (derivedExtensionEquivalence φ hφ).inverse.Linear R := by
  have hfun : (derivedExtensionEquivalence φ hφ).functor.Linear R :=
    derivedTensorFunctor_linear (Bimodule.regular φ)
  exact ⟨hfun, Equivalence.inverseLinear R _⟩

end DifferentialGraded.Bimodule

end
