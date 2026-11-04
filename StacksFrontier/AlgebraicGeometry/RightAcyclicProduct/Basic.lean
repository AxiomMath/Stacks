module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# Right acyclicity is closed under finite products

Let `F : 𝒜 ⥤ ℬ` be an additive, left exact functor between abelian categories, with `𝒜` having
enough injectives, so that the right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is everywhere defined
and right acyclicity ([Stacks, Tag 0157], `CategoryTheory.Functor.rightAcyclic`) is the
invertibility of the comparison `F(A) ⟶ RF(A[0])`.  This file proves that the objects right
acyclic for `F` are closed under finite products, and records the consequence for the terms of a
Čech complex.

## Main results

* `Stacks.RightAcyclicProduct.rightAcyclic_of_injective` and `rightAcyclic_of_isZero`: an
  injective object, in particular a zero object, is right acyclic.
* `Stacks.RightAcyclicProduct.rightAcyclic_biprod` and `rightAcyclic_prod`: a binary
  (bi)product of right acyclic objects is right acyclic.
* `Stacks.RightAcyclicProduct.rightAcyclic_pi`: **the headline.** `∏ᶜ G` is right acyclic for `F`
  whenever `G : ι → 𝒜` is a family of right acyclic objects indexed by a finite type.
* `Stacks.RightAcyclicProduct.rightAcyclic_of_isLimit_fan`: the same with the product presented by
  an arbitrary limit fan rather than by `∏ᶜ`, which is how a Čech term presents it.
* `Stacks.RightAcyclicProduct.rightAcyclic_cechComplex_X`: therefore every term of the Čech
  complex of a finite family `U : ι → 𝒞` with coefficients in a presheaf `P : 𝒞ᵒᵖ ⥤ 𝒜` is right
  acyclic for `F`, as soon as each of its factors `P(U_{x₀} × ⋯ × U_{xₙ})` is.  This is the
  hypothesis `∀ n, F.rightAcyclic (K.X n)` of Leray's acyclicity lemma
  ([Stacks, Tag 015E], `CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic`)
  for `K` a Čech complex, reduced to a statement about a single factor.

The three closure statements are also registered as `ObjectProperty` instances on
`F.rightAcyclic` — `IsClosedUnderIsomorphisms`, `ContainsZero`, `IsClosedUnderBinaryProducts` and
`IsClosedUnderFiniteProducts` — so that Mathlib's `ObjectProperty.prop_product`,
`ObjectProperty.prop_of_isLimit_fan` and friends apply to right acyclicity directly.

## Implementation notes

**The route never commutes the derived functor past the product, and so avoids two genuine
absences.** Pinned Mathlib declares no `CategoryTheory.Functor.Additive` instance for
`Functor.rightDerived`, and no lemma deducing `IsZero (∏ᶜ G)` from `∀ i, IsZero (G i)`; the usual
argument — commute `R ⁱ F` past the biproduct and observe that a product of zero objects is zero
— needs both.  The first absence is sharp enough to be visible here: even
`(F.rightDerivedPlus i).PreservesZeroMorphisms`, which is weaker than additivity and is all that
is needed to see that `R ⁱ F` kills a zero object, fails to synthesize, which is why
`rightAcyclic_of_isZero` below goes through injectivity instead.

Neither absence is used.  Instead a *binary* product of right acyclic objects is handled by
[Stacks, Tag 015D] (`Functor.rightAcyclic_and_shortExact_map_of_shortExact`) applied to the split
short exact sequence `0 ⟶ A ⟶ A ⊞ B ⟶ B ⟶ 0`, whose splitting is
`CategoryTheory.ShortComplex.Splitting.ofHasBinaryBiproduct`; and the passage from binary to
arbitrary finite products is Mathlib's
`CategoryTheory.ObjectProperty.IsClosedUnderFiniteProducts.mk'`, which needs exactly the binary
case, the zero object, and closure under isomorphism.  `F.rightAcyclic` is an `ObjectProperty 𝒜`
by construction, so that machinery applies with no transport.

`PreservesFiniteLimits F` is a hypothesis of the route and not an artefact: it is what
[Stacks, Tag 015D] assumes, and it is also what makes right acyclicity equivalent to the plain
vanishing of `R ⁱ F` in positive degrees ([Stacks, Tag 015C] part (2)), which is how the zero
object is handled below.  It holds for the intended consumer, `Scheme.Modules.pushforward f`,
which is a right adjoint.

`rightAcyclic_of_iso` and `rightAcyclic_of_isZero` restate two `private` lemmas of
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective.lean`; they are needed
as `ObjectProperty` instance fields and are not reachable from outside that file.  The proof of
`rightAcyclic_of_iso` is the same one-liner.  The proof of `rightAcyclic_of_isZero` is not: the
private route is the private `isIso_app_of_isZero`, which needs `PreservesZeroMorphisms` for the
derived functor, so instead a zero object is treated as what it is — an injective object
(`CategoryTheory.Injective.zero_injective`) — and killed by the public
`Functor.isZero_rightDerivedPlus_obj_injective` together with [Stacks, Tag 015C] part (2).

The Čech corollary is proved by handing `rightAcyclic_pi` the family
`x ↦ P(inter U x)` and letting the ascribed type do the rest: as recorded in
`StacksFrontier/CategoryTheory/Sites/CechComplex.lean`, the degree `n` term of the Čech complex
*is* `∏ᶜ (fun x : Fin (n + 1) → ι ↦ P.obj (op (inter U x)))` definitionally, because `ToType ⦋n⦌`
reduces to `Fin (n + 1)` and `FormalCoproduct.power` is that formula.  Going instead through
`Stacks.CategoryTheory.CechComplex.isLimitFan` and `rightAcyclic_of_isLimit_fan` does *not* work
directly: the fan's index type is inferred as
`(unop ((Functor.rightOp (FormalCoproduct.cech ⟨ι, U⟩)).obj ⦋n⦌)).I` rather than as
`Fin (n + 1) → ι`, and `Finite` is then not found for it even though the two are defeq.

## References

* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace Stacks.RightAcyclicProduct

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
  [EnoughInjectives C]

/-! ### Closure under isomorphism and the zero object -/

/-- **Right acyclicity is invariant under isomorphism.** Right acyclicity of `A` is the
invertibility of the unit of `RF` at the one-term complex `A[0]`, and `A ≅ B` makes
`A[0] ≅ B[0]`. -/
public theorem rightAcyclic_of_iso {A B : C} (e : A ≅ B) (hA : F.rightAcyclic A) :
    F.rightAcyclic B :=
  (NatTrans.isIso_app_iff_of_iso _ ((HomotopyCategory.Plus.singleFunctor C 0).mapIso e)).1 hA

/-- The objects right acyclic for `F` are closed under isomorphism, by `rightAcyclic_of_iso`. -/
public instance isClosedUnderIsomorphisms_rightAcyclic :
    (F.rightAcyclic).IsClosedUnderIsomorphisms where
  of_iso e hA := rightAcyclic_of_iso F e hA

variable [PreservesFiniteLimits F]

/-- **An injective object is right acyclic.** For a left exact `F` right acyclicity is the
vanishing of `R ⁱ F` in positive degrees ([Stacks, Tag 015C] part (2)), and `R ⁱ F` kills an
injective object for `i ≠ 0`. -/
public theorem rightAcyclic_of_injective (A : C) [Injective A] : F.rightAcyclic A :=
  ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F A).2
    ‹PreservesFiniteLimits F›).2 fun i hi ↦
      Functor.isZero_rightDerivedPlus_obj_injective F i hi.ne' A

/-- **A zero object is right acyclic**, being injective. -/
public theorem rightAcyclic_of_isZero {A : C} (hA : IsZero A) : F.rightAcyclic A :=
  rightAcyclic_of_iso F (hA.iso (isZero_zero C)).symm (rightAcyclic_of_injective F 0)

/-- The objects right acyclic for `F` contain a zero object, by `rightAcyclic_of_isZero`. -/
public instance containsZero_rightAcyclic : (F.rightAcyclic).ContainsZero :=
  ⟨0, isZero_zero C, rightAcyclic_of_isZero F (isZero_zero C)⟩

/-! ### Binary products -/

/-- **A biproduct of two right acyclic objects is right acyclic.** The split short exact sequence
`0 ⟶ A ⟶ A ⊞ B ⟶ B ⟶ 0` has right acyclic outer terms, so [Stacks, Tag 015D] part (1) makes its
middle term right acyclic. -/
public theorem rightAcyclic_biprod {A B : C} (hA : F.rightAcyclic A) (hB : F.rightAcyclic B) :
    F.rightAcyclic (A ⊞ B) :=
  ((Functor.rightAcyclic_and_shortExact_map_of_shortExact F _
    (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact).1 hA hB).1

/-- **A product of two right acyclic objects is right acyclic**, the product being isomorphic to
the biproduct. -/
public theorem rightAcyclic_prod {A B : C} (hA : F.rightAcyclic A) (hB : F.rightAcyclic B) :
    F.rightAcyclic (A ⨯ B) :=
  rightAcyclic_of_iso F (biprod.isoProd A B) (rightAcyclic_biprod F hA hB)

/-- The objects right acyclic for `F` are closed under binary products, by `rightAcyclic_prod`
applied to the two values of a pair diagram. -/
public instance isClosedUnderBinaryProducts_rightAcyclic :
    (F.rightAcyclic).IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨G, hG⟩
    exact rightAcyclic_of_iso F (HasLimit.isoOfNatIso (diagramIsoPair G)).symm
      (rightAcyclic_prod F (hG ⟨WalkingPair.left⟩) (hG ⟨WalkingPair.right⟩)))

/-! ### Finite products -/

/-- The objects right acyclic for `F` are closed under finite products: Mathlib's
`ObjectProperty.IsClosedUnderFiniteProducts.mk'` deduces this from the binary case, the zero
object and closure under isomorphism. -/
public instance isClosedUnderFiniteProducts_rightAcyclic :
    (F.rightAcyclic).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- **Right acyclicity is closed under finite products.** If every `G i` is right acyclic for the
additive left exact functor `F`, and the index type is finite, then `∏ᶜ G` is right acyclic
for `F`. -/
public theorem rightAcyclic_pi {ι : Type*} [Finite ι] (G : ι → C) [HasProduct G]
    (hG : ∀ i, F.rightAcyclic (G i)) : F.rightAcyclic (∏ᶜ G) :=
  ObjectProperty.prop_product _ hG

/-- **The same, for a product presented by an arbitrary limit fan.** This is the form a Čech term
takes: it is a product of the values of the coefficient presheaf, but it is not syntactically
`∏ᶜ`. -/
public theorem rightAcyclic_of_isLimit_fan {ι : Type*} [Finite ι] {G : ι → C} {c : Fan G}
    (hc : IsLimit c) (hG : ∀ i, F.rightAcyclic (G i)) : F.rightAcyclic c.pt :=
  ObjectProperty.prop_of_isLimit_fan _ hc hG

/-! ### The terms of a Čech complex -/

/-- **Every term of a Čech complex over a finite family is right acyclic as soon as each of its
factors is.** The degree `n` term of the Čech complex of `U : ι → 𝒞` with coefficients in
`P : 𝒞ᵒᵖ ⥤ 𝒜` is the product, over the tuples `x : Fin (n + 1) → ι`, of the sections of `P` over
`inter U x`; the index type is finite because `ι` is, so `rightAcyclic_of_isLimit_fan` applies to
`Stacks.CategoryTheory.CechComplex.isLimitFan`.

This is exactly the gap between acyclicity of a single factor and the hypothesis
`∀ n, F.rightAcyclic (K.X n)` that Leray's acyclicity lemma [Stacks, Tag 015E] consumes. -/
public theorem rightAcyclic_cechComplex_X {E : Type*} [Category* E] [HasFiniteProducts E]
    [HasProducts C] {ι : Type*} [Finite ι] (U : ι → E) (P : Eᵒᵖ ⥤ C) (n : ℕ)
    (hP : ∀ x : Fin (n + 1) → ι,
      F.rightAcyclic (P.obj (op (Stacks.CategoryTheory.CechComplex.inter U x)))) :
    F.rightAcyclic (((cechComplexFunctor U).obj P).X n) :=
  rightAcyclic_pi F (fun x : Fin (n + 1) → ι ↦
    P.obj (op (Stacks.CategoryTheory.CechComplex.inter U x))) hP

end Stacks.RightAcyclicProduct

end
