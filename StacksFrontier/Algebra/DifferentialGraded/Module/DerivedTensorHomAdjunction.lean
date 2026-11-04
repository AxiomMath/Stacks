module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.CategoryTheory.Functor.Derived.Absolute
public import StacksCore.Tactic.StacksAttribute

/-! # The derived tensor–Hom adjunction for differential graded bimodules

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. Stacks 09LT says that the derived tensor product
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of Tag 09LS is left adjoint to derived Hom
`RHom(N, -) : D(B, d) ⥤ D(A, d)` of Tag 09LI, and the Stacks proof is Tag 0FND applied to the
adjunction between ordinary tensoring and internal Hom on the homotopy categories, which is
Tag 09LN.

This file carries out that deduction. The two derived functors are the library's
`DifferentialGraded.Bimodule.derivedTensorFunctor` (Tag 09LS) and the functor of an arbitrary
`DifferentialGradedModule.DerivedHomData` (Tag 09LI), so the conclusion is the adjunction for
*any* choice of derived Hom data, and in particular the adjunction does not depend on which
construction produced `RHom(N, -)`.

**The deduction is carried out twice, conditionally and then unconditionally.**
`DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHom` has two hypotheses, each the
statement of a different tag and neither of them Tag 09LT itself, so it carries no tag:

* `hadj`, the adjunction between ordinary tensoring with `N` and internal Hom out of `N` on the
  homotopy categories, is Tag 09LN. It is
  `DifferentialGraded.Bimodule.tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor`
  (`StacksFrontier/Algebra/DifferentialGraded/Module/BimoduleTensorHom.lean`). Note that the
  Tag 09LN of `StacksFrontier/Algebra/Category/ModuleCat/Bimod/TensorHom.lean` is instead the
  ordinary, non-graded tensor–Hom adjunction for bimodules over rings, a different statement.
* `hres`, the existence of resolutions by modules with property (I), is Tag 09KU, which is
  `DifferentialGradedModule.exists_propertyI_resolution`. It is the same hypothesis
  `DifferentialGradedModule.DerivedHomData.ofPropertyIResolutions` takes, so it also pins the
  `DerivedHomData` argument to `DifferentialGradedModule.derivedHomData` (Tag 09LI).

Supplying both gives `DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHomFunctor`,
which assumes nothing and is where `@[stacks 09LT]` sits.

The mirror hypothesis on the left is *not* needed: resolutions by modules with property (P)
exist unconditionally, by `DifferentialGradedModule.exists_quasiIso_leftOrthogonal_acyclic`.

## Main definitions

* `DifferentialGradedModule.exists_resolution_map_bijective`: the resolution supply on the left
  in the form the absoluteness criterion consumes — every object of `K(A, d)` receives a
  quasi-isomorphism from an object out of which the localization functor is bijective on
  morphisms. Unconditional.
* `DifferentialGradedModule.exists_coresolution_map_bijective_of_propertyI_resolutions`: the same
  on the right, from Tag 09KU.

## Main results

* `DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHomFunctor`: **Stacks 09LT**,
  unconditionally.
* `DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHomFunctor_homEquiv`: the
  resulting bifunctorial identification
  `Hom_{D(B,d)}(M ⊗_A^𝐋 N, P) ≃ Hom_{D(A,d)}(M, RHom(N, P))`, which is the form in which
  Stacks 09LT is used (Example 22.33.2, Tag 0BYX).
* `DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHom`: the same adjunction for an
  arbitrary derived Hom datum, with Tag 09LN and Tag 09KU as hypotheses rather than as
  references; untagged, and with its own `homEquiv` form.
* `DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction`: **Stacks 0BYX,
  Example 22.33.2**, the specialisation to the regular bimodule, where the right adjoint is
  restriction of scalars.
* `DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction_homEquiv`: the
  displayed formula of that example,
  `Hom_{D(A,d)}(M, N_A) = Hom_{D(B,d)}(M ⊗_A^𝐋 B, N)`.

## Implementation notes

*Where the work is.* Mathlib's `CategoryTheory.Adjunction.derived` produces the adjunction
between the derived functors, but asks the two derived functors to be **absolute**: the
composites `G' ⋙ F'` and `F' ⋙ G'` must again be derived functors, of the composites of the
undercategory functors with the localizations. That is supplied by
`CategoryTheory.Functor.isLeftDerivedFunctor_comp_of_resolutions` and
`CategoryTheory.Functor.isRightDerivedFunctor_comp_of_coresolutions`
(`StacksFrontier/CategoryTheory/Functor/Derived/Absolute.lean`), whose hypothesis is exactly the
resolution supply that Tag 06XN already consumes here. The two statements below turn the
resolutions into the form those take, by
`DifferentialGradedModule.bijective_q_map_of_leftOrthogonal` and
`DifferentialGradedModule.bijective_q_map_of_rightOrthogonal`: the localization functor is
bijective on the morphisms out of an object of the left orthogonal of the acyclic modules, and
dually.

*Why the adjunction is stated for an arbitrary `DerivedHomData`.* `RHom(N, -)` is determined only
up to the canonical isomorphism `DifferentialGradedModule.DerivedHomData.functorIso`, so pinning
one construction would make the statement weaker than the source's. Proving it for every datum
costs nothing, since the only thing used is the comparison map it carries.

*Universes.* The differential graded algebras and their modules are taken at main's
single-universe encoding of `DifferentialGradedAlgebra`, in which
`DifferentialGradedAlgebra : Type u → Type u` and a module over it again lies in `Type u`. The
Stacks source is universe-polymorphic in the base ring, each algebra and each module separately;
widening the encoding is an addition of universe parameters rather than a change of content, and
nothing below depends on the universes being equal.

## References

* [Stacks Project, Tag 09LT](https://stacks.math.columbia.edu/tag/09LT); its proof is
  [Tag 0FND](https://stacks.math.columbia.edu/tag/0FND) applied to
  [Tag 09LN](https://stacks.math.columbia.edu/tag/09LN), the two derived functors are
  [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) and
  [Tag 09LI](https://stacks.math.columbia.edu/tag/09LI), and the resolutions on the right are
  [Tag 09KU](https://stacks.math.columbia.edu/tag/09KU).
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), Example 22.33.2, for the
  specialisation to the regular bimodule of a homomorphism of differential graded algebras, where
  the right adjoint is restriction of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-! ### The resolutions, in the form the absoluteness criterion consumes -/

/-- Every object of `K(A, d)` receives a quasi-isomorphism from an object out of which the
localization functor is bijective on morphisms.

This is `DifferentialGradedModule.exists_quasiIso_leftOrthogonal_acyclic` — Tag 09KP followed by
Tag 09KM — read on the homotopy category, and it is unconditional. -/
theorem exists_resolution_map_bijective (A : DifferentialGradedAlgebra R)
    (X : HomotopyCategory A) :
    ∃ (P : HomotopyCategory A) (s : P ⟶ X), quasiIsomorphisms' A s ∧
      ∀ Y : HomotopyCategory A,
        Function.Bijective ((quasiIsomorphisms' A).Q.map : (P ⟶ Y) →
          ((quasiIsomorphisms' A).Q.obj P ⟶ (quasiIsomorphisms' A).Q.obj Y)) := by
  obtain ⟨P, s, hs, hP⟩ := exists_trW_leftOrthogonal_of_exists_quasiIso_leftOrthogonal A
    (exists_quasiIso_leftOrthogonal_acyclic A) X
  refine ⟨P, s, ?_, bijective_q_map_of_leftOrthogonal hP⟩
  rwa [← acyclic_trW_eq_quasiIsomorphisms']

/-- Every object of `K(B, d)` admits a quasi-isomorphism into an object into which the
localization functor is bijective on morphisms, as soon as every differential graded `B`-module
admits a quasi-isomorphism into a module with property (I).

The hypothesis is Tag 09KU; the orthogonality it is combined with is Tag 09KS. -/
theorem exists_coresolution_map_bijective_of_propertyI_resolutions
    (B : DifferentialGradedAlgebra R)
    (hres : ∀ M : DifferentialGradedModule B, ∃ (I : DifferentialGradedModule B) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex B).map f) ∧ Nonempty (PropertyIFiltration I))
    (X : HomotopyCategory B) :
    ∃ (I : HomotopyCategory B) (s : X ⟶ I), quasiIsomorphisms' B s ∧
      ∀ Y : HomotopyCategory B,
        Function.Bijective ((quasiIsomorphisms' B).Q.map : (Y ⟶ I) →
          ((quasiIsomorphisms' B).Q.obj Y ⟶ (quasiIsomorphisms' B).Q.obj I)) := by
  obtain ⟨I, s, hs, hI⟩ := exists_trW_rightOrthogonal_of_exists_quasiIso_rightOrthogonal B
    (exists_quasiIso_rightOrthogonal_acyclic_of_propertyI_resolutions B hres) X
  refine ⟨I, s, ?_, bijective_q_map_of_rightOrthogonal hI⟩
  rwa [← acyclic_trW_eq_quasiIsomorphisms']

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- **Stacks 09LT from Tag 09LN and Tag 09KU.** The derived tensor product
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is left adjoint to `RHom(N, -) : D(B, d) ⥤ D(A, d)`, for any
right derived functor `D` of internal Hom out of `N`.

The hypotheses are the adjunction between ordinary tensoring and internal Hom on the homotopy
categories (Tag 09LN, `hadj`) and the existence of resolutions by modules with property (I)
(Tag 09KU, `hres`); neither is Tag 09LT, which is the conclusion. The deduction is Tag 0FND, in
the form of Mathlib's `CategoryTheory.Adjunction.derived`, whose absoluteness hypotheses are
discharged from the resolutions.

Note that the mirror resolution hypothesis on the left is not among the arguments: resolutions by
modules with property (P) are available unconditionally. -/
def derivedTensorFunctor_adj_derivedHom (N : Bimodule A B)
    (D : DerivedHomData A B N.rightModule N.leftAction)
    (hres : ∀ M : DifferentialGradedModule B, ∃ (I : DifferentialGradedModule B) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex B).map f) ∧ Nonempty (PropertyIFiltration I))
    (hadj : tensorHomotopyFunctor N ⊣
      homHomotopyCategoryFunctor A B N.rightModule N.leftAction) :
    derivedTensorFunctor N ⊣ D.functor := by
  -- `D.comparison` is stated over `DifferentialGradedModule.homToDerivedCategory`, which is a
  -- plain `def` and therefore invisible to instance search; `Adjunction.derived` asks for it at
  -- the unfolded spelling. Ascribing the term — which is checked at default transparency —
  -- records the two instances at the spelling the final application needs.
  have hβ : D.functor.IsRightDerivedFunctor
      (show homHomotopyCategoryFunctor A B N.rightModule N.leftAction ⋙ (quasiIsomorphisms' A).Q ⟶
        (quasiIsomorphisms' B).Q ⋙ D.functor from D.comparison) (quasiIsomorphisms' B) :=
    D.isRightDerived
  have hleft := Functor.isLeftDerivedFunctor_comp_of_resolutions (quasiIsomorphisms' A)
    (derivedTensorFunctorCounit N) D.functor (exists_resolution_map_bijective A)
  have hright := Functor.isRightDerivedFunctor_comp_of_coresolutions (quasiIsomorphisms' B)
    (show homHomotopyCategoryFunctor A B N.rightModule N.leftAction ⋙ (quasiIsomorphisms' A).Q ⟶
      (quasiIsomorphisms' B).Q ⋙ D.functor from D.comparison) (derivedTensorFunctor N)
    (exists_coresolution_map_bijective_of_propertyI_resolutions B hres)
  exact hadj.derived (quasiIsomorphisms' A) (quasiIsomorphisms' B)
    (derivedTensorFunctorCounit N) D.comparison

/-- **Stacks 09LT**, as the bifunctorial identification of morphism groups
`Hom_{D(B,d)}(M ⊗_A^𝐋 N, P) ≃ Hom_{D(A,d)}(M, RHom(N, P))` that Stacks 0BYX, Example 22.33.2
uses. The hypotheses are those of
`DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHom`. -/
def derivedTensorFunctor_adj_derivedHom_homEquiv (N : Bimodule A B)
    (D : DerivedHomData A B N.rightModule N.leftAction)
    (hres : ∀ M : DifferentialGradedModule B, ∃ (I : DifferentialGradedModule B) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex B).map f) ∧ Nonempty (PropertyIFiltration I))
    (hadj : tensorHomotopyFunctor N ⊣
      homHomotopyCategoryFunctor A B N.rightModule N.leftAction)
    (M : derivedCategory' A) (P : derivedCategory' B) :
    ((derivedTensorFunctor N).obj M ⟶ P) ≃ (M ⟶ D.functor.obj P) :=
  (derivedTensorFunctor_adj_derivedHom N D hres hadj).homEquiv M P

/-! ### Tag 09LT, unconditionally -/

/-- **Stacks 09LT.** The derived tensor product `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of Tag 09LS is a
left adjoint to derived Hom `RHom(N, -) : D(B, d) ⥤ D(A, d)` of Tag 09LI, for a differential
graded `(A, B)`-bimodule `N`. Nothing is assumed.

This is `DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHom` with both of its
hypotheses supplied: Tag 09LN by
`DifferentialGraded.Bimodule.tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor`, and Tag 09KU
by `DifferentialGradedModule.exists_propertyI_resolution`, which also pins the derived Hom
functor to that of `DifferentialGradedModule.derivedHomData`.

*The degree-zero scope of the Tag 09LN input does not limit this.* What is proved of Tag 09LN
for differential graded modules is the bijection of the morphism groups of the two categories,
not the isomorphism of Hom *complexes* in all degrees that the source also states there. But
Tag 09LT asserts an adjunction of functors between the derived categories — a bijection of
morphism groups, natural in both variables — and it is deduced from an adjunction of functors
between the homotopy categories, which is again a bijection of morphism groups. The all-degrees
half of Tag 09LN is neither used nor needed, so this is Tag 09LT in full and the tag is bare. -/
@[stacks 09LT, sga "5 IIIB 5.2" "5.2.3"]
def derivedTensorFunctor_adj_derivedHomFunctor (N : Bimodule A B) :
    derivedTensorFunctor N ⊣ (derivedHomData A B N.rightModule N.leftAction).functor :=
  derivedTensorFunctor_adj_derivedHom N (derivedHomData A B N.rightModule N.leftAction)
    (exists_propertyI_resolution B) (tensorHomotopyFunctor_adj_homHomotopyCategoryFunctor N)

/-- **Stacks 09LT**, as the bifunctorial identification of morphism groups
`Hom_{D(B,d)}(M ⊗_A^𝐋 N, P) ≃ Hom_{D(A,d)}(M, RHom(N, P))` that Stacks 0BYX, Example 22.33.2
uses. Nothing is assumed: it is the hom-set bijection of
`DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHomFunctor`. -/
@[stacks 09LT "as a bijection of morphism groups"]
def derivedTensorFunctor_adj_derivedHomFunctor_homEquiv (N : Bimodule A B)
    (M : derivedCategory' A) (P : derivedCategory' B) :
    ((derivedTensorFunctor N).obj M ⟶ P) ≃
      (M ⟶ (derivedHomData A B N.rightModule N.leftAction).functor.obj P) :=
  (derivedTensorFunctor_adj_derivedHomFunctor N).homEquiv M P

/-! ### Tag 0BYX: extension of scalars is left adjoint to restriction of scalars -/

/-- **Stacks 0BYX, Example 22.33.2.** For a homomorphism `φ : (A, d) → (B, d)` of differential
graded algebras, derived extension of scalars `- ⊗_A^𝐋 B : D(A, d) ⥤ D(B, d)` — tensoring with
the regular bimodule, `DifferentialGraded.Bimodule.regular` — is left adjoint to derived
restriction of scalars `(-)_A : D(B, d) ⥤ D(A, d)`. Nothing is assumed.

This is the displayed formula of the example,
`Hom_{D(A,d)}(M, N_A) = Hom_{D(B,d)}(M ⊗_A^𝐋 B, N)`, *bifunctorially in `M` and `N`*: an
`CategoryTheory.Adjunction` is exactly a bijection of the two morphism groups together with its
naturality in both variables, so the bifunctoriality the source asserts is carried by this
statement and needs no separate lemma. The bijection on its own is
`DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction_homEquiv`.

The two inputs are the two steps the example takes. The adjunction with derived Hom out of the
regular bimodule on the right is Tag 09LT,
`DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedHomFunctor`; and
`DifferentialGradedModule.DerivedHomData.functorIsoDerivedRestriction` is the example's
identification `RHom(B, -) = (-)_A`, which comes from `Hom_{Mod^{dg}_B}(B, N) ≅ N_A`, `f ↦ f(1)`,
naturally in `N`. Transporting the right adjoint along that isomorphism replaces `RHom(B, -)` by
restriction of scalars, which is the example's conclusion. -/
@[stacks 0BYX "the adjunction Hom_{D(A,d)}(M, N_A) = Hom_{D(B,d)}(M ⊗_A^𝐋 B, N), bifunctorially",
  sga "5 IIIB 5.2" "5.2.3 for F = B"]
def derivedTensorFunctor_adj_derivedRestriction (φ : A.Hom B) :
    derivedTensorFunctor (Bimodule.regular φ) ⊣ derivedRestriction φ :=
  Adjunction.ofNatIsoRight (derivedTensorFunctor_adj_derivedHomFunctor (Bimodule.regular φ))
    (DerivedHomData.functorIsoDerivedRestriction φ
      (derivedHomData A B (regularModule B) (regularBimoduleStructure φ)))

/-- **Stacks 0BYX, Example 22.33.2**, the displayed formula itself:
`Hom_{D(A,d)}(M, N_A) = Hom_{D(B,d)}(M ⊗_A^𝐋 B, N)`.

It is the hom-set bijection of
`DifferentialGraded.Bimodule.derivedTensorFunctor_adj_derivedRestriction`, so the
bifunctoriality in `M` and `N` that the source asserts is the naturality carried by that
adjunction; it is not restated here. -/
@[stacks 0BYX "the displayed formula Hom_{D(A,d)}(M, N_A) = Hom_{D(B,d)}(M ⊗_A^𝐋 B, N)"]
def derivedTensorFunctor_adj_derivedRestriction_homEquiv (φ : A.Hom B)
    (M : derivedCategory' A) (N : derivedCategory' B) :
    (M ⟶ (derivedRestriction φ).obj N) ≃
      ((derivedTensorFunctor (Bimodule.regular φ)).obj M ⟶ N) :=
  ((derivedTensorFunctor_adj_derivedRestriction φ).homEquiv M N).symm

end DifferentialGraded.Bimodule

end
