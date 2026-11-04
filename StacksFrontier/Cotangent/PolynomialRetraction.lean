module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SelfDerivedTensorVanishing
public import StacksFrontier.Cotangent.SurjectionSingleDegree
public import StacksFrontier.Cotangent.TensorProduct
public import StacksFrontier.RingTheory.Kaehler.PolynomialAlgebra

/-!
# The cotangent complex of the augmentation of a polynomial algebra

Let `A` be a commutative ring, let `B` be a polynomial algebra over `A`, and let `B → A` be a
retraction of `A → B`, that is, an augmentation. Write `I = ker(B → A)`. Then `L_{A/B}` is
quasi-isomorphic to `I/I²[1]`. For `A = ℤ`, `B = ℤ[x₁, …, xₙ]` and the augmentation sending
every variable to zero this is [Stacks, Tag 08SI], whose ideal `I = (x₁, …, xₙ)` is exactly the
kernel of that augmentation.

The proof is the one the source gives. The fundamental triangle of `A → B → A`,

`L_{B/A} ⊗^𝐋_B A ⟶ L_{A/A} ⟶ L_{A/B} ⟶ (L_{B/A} ⊗^𝐋_B A)[1]`,

has zero middle vertex, because `L_{A/A} = 0`; so its connecting morphism identifies `L_{A/B}`
with `(L_{B/A} ⊗^𝐋_B A)[1]`. The first vertex lies in cohomological degree `0`: by
[Stacks, Tag 08QH] the complex `L_{B/A}` is quasi-isomorphic to `Ω[B⁄A]`, which is a free, hence
projective, `B`-module, and a bounded-above complex of projectives computes derived extension of
scalars. Shifting, `L_{A/B}` has no cohomology in the degrees `≤ -2`, and that single vanishing
is all that `StacksFrontier.Cotangent.SurjectionSingleDegree` needs in order to conclude
`L_{A/B} ≅ I/I²[1]`.

## Main definitions

* `CommAlgCat.HasFundamentalTriangleAt`: Proposition 08QX for one tower `A → B → C`, as a
  `Prop` — the existence of a distinguished triangle on the three vertices
  `L_{B/A} ⊗^𝐋_B C`, `L_{C/A}` and `L_{C/B}` of the display of Tag 08QS.

## Main results

* `CommAlgCat.isGE_cotangentComplexDerivedBaseChange_of_isPolynomialAlgebra`: for `B` a
  polynomial algebra over `A`, the derived base change `L_{B/A} ⊗^𝐋_B C` lies in `D^{≥0}(C)`.
* `CommAlgCat.isGE_cotangentComplexDerived_retraction`: `L_{A/B}` lies in `D^{≥ -1}(B)`.
* `CommAlgCat.isZero_homology_cotangentComplex_retraction`: `H^i(L_{A/B}) = 0` for `i ≤ -2`.
* `CommAlgCat.nonempty_cotangentComplex_retraction_iso_single`: **Tag 08SI**, in the general
  form — `L_{A/B}` is isomorphic in `D(A)` to `I/I²` placed in cohomological degree `-1`.

## The carried hypothesis

Proposition 08QX — that the three vertices of the display of Tag 08QS form a distinguished
triangle for *arbitrary* ring maps `A → B → C` — is not proved in this library; see the
`No @[stacks 08QX]` section of `StacksFrontier/Cotangent/Triangle/Distinguished.lean`. What the
library carries is the triangle of Tag 08SD, `CommAlgCat.cotangentTriangle_distinguished`, which
assumes the middle map `B → C` *injective*. The map this file needs it for is the augmentation
`B → A`, which is surjective and far from injective, so Tag 08SD does not apply and 08QX is
carried as the explicit hypothesis `h08QX : HasFundamentalTriangleAt A B A`.

Carrying it does not turn the statement into a restatement of its own conclusion. `h08QX`
asserts only that a distinguished triangle exists on the three named vertices, for the tower
`A → B → A`; it says nothing about where the cohomology of `L_{A/B}` sits, nor that `L_{A/B}` is
a single module, nor what that module is. The three further inputs — the vanishing of `L_{A/A}`,
the concentration of `L_{B/A} ⊗^𝐋_B A` in degree `0`, and the identification of `H^{-1}(L_{A/B})`
with `I/I²` — are proved here and in `StacksFrontier.Cotangent.Surjection`. The same shape of
hypothesis is carried by `CommAlgCat.exists_tensorProduct_nine_diagram` of
`StacksFrontier/Cotangent/TensorProduct.lean`, which takes two instances of 08QX as hypotheses
`h₁` and `h₂`.

## Implementation notes

The tower is `A → B → A`: the target of the augmentation is the base ring itself, bound as a
`B`-algebra together with `IsScalarTower A B A`. That scalar tower *is* the statement that
`B → A` is a retraction of `A → B`, and it already forces `B → A` to be surjective
(`CommAlgCat.surjective_algebraMap_of_isScalarTower_self`), which is what the results of
`StacksFrontier.Cotangent.Surjection` consume.

The three rings lie in one universe, as they must: the derived tensor product of
`StacksFrontier.Homology.Tor.DerivedExtensionScalars` is formed in a single module universe, and
the tower has only two distinct rings anyway.

That the first vertex is concentrated in degree `0` is proved by moving along the quasi-isomorphism
of Tag 08QH to the single complex on `Ω[B⁄A]` and applying
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison_isIso_of_projective`
to *that* complex, whose terms are `Ω[B⁄A]` and zero. Applying it to `L_{B/A}` itself would need
the projectivity of every term of the standard resolution's differentials; the single complex
needs only `KaehlerDifferential.projective_of_isPolynomialAlgebra`.

`StacksFrontier/Cotangent/StandardResolutionOverPolynomialBase.lean` runs the same argument for the
*bounded-above* derived functor
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral`, in its private
`derivedExtensionScalarsSingleIsoOfProjective` and in
`CommAlgCat.nonempty_derivedExtensionScalars_cotangentComplex_iso_of_isPolynomialAlgebra`.
Neither is reusable here: the first is private to that module, and both are about a different
functor from the unbounded
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` out of which
`CommAlgCat.cotangentComplexDerivedBaseChange` — the first vertex of the display of Tag 08QS,
and so the first vertex of `CommAlgCat.HasFundamentalTriangleAt` — is built.

## References

* [Stacks Project, Tag 08SI](https://stacks.math.columbia.edu/tag/08SI)
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS), the displayed triangle.
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), that it is distinguished.
* [Stacks Project, Tag 08QH](https://stacks.math.columbia.edu/tag/08QH)
* [Stacks Project, Tag 08R2](https://stacks.math.columbia.edu/tag/08R2)
* [Stacks Project, Tag 08RA](https://stacks.math.columbia.edu/tag/08RA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/-- **Proposition 08QX for a single tower, as a carried hypothesis.** For ring maps
`A → B → C`, the assertion that the three vertices

`L_{B/A} ⊗^𝐋_B C`, `L_{C/A}`, `L_{C/B}`

of the display of Tag 08QS fit into a distinguished triangle in `D(C)`. The triangle is asked
for existentially, as the source states it, and no hypothesis beyond the two algebra structures
and the scalar tower is imposed: this is 08QX for a *general*, not necessarily injective,
map `B → C`.

This is the predicate at one tower, which is why it is named `…At`.
`CommAlgCat.HasFundamentalTriangle` of `StacksFrontier.Cotangent.SmoothVanishing` is the
`∀`-quantified form of the same proposition, over every tower of rings in the universe, and so
implies this one at each individual tower. The pointwise form is the one carried here: the
results below need the triangle only for the single tower `A → B → A`, and assuming it there
alone keeps the hypothesis weaker, hence the conclusions stronger. -/
def HasFundamentalTriangleAt (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C] : Prop :=
  ∃ (α : cotangentComplexDerivedBaseChange A (CommAlgCat.of A B) C ⟶
            cotangentComplexDerived A (CommAlgCat.of A C))
    (β : cotangentComplexDerived A (CommAlgCat.of A C) ⟶
            cotangentComplexDerived B (CommAlgCat.of B C))
    (δ : cotangentComplexDerived B (CommAlgCat.of B C) ⟶
            (cotangentComplexDerivedBaseChange A (CommAlgCat.of A B) C)⟦(1 : ℤ)⟧),
    Triangle.mk α β δ ∈ distTriang (DerivedCategory (ModuleCat.{u} C))

/-- A retraction is surjective: if `A → B → A` is a scalar tower, then `B → A` hits every
element of `A`, namely `a = algebraMap B A (algebraMap A B a)`. -/
theorem surjective_algebraMap_of_isScalarTower_self (A : Type u) [CommRing A] (B : Type u)
    [CommRing B] [Algebra A B] [Algebra B A] [IsScalarTower A B A] :
    Function.Surjective (algebraMap B A) := fun a =>
  ⟨algebraMap A B a, by
    rw [← IsScalarTower.algebraMap_apply A B A, Algebra.algebraMap_self_apply]⟩

/-- **Derived extension of scalars carries a single projective module in degree `0` to an object
of `D^{≥0}`.** A single complex on a projective module is a bounded-above complex of projectives,
so it computes the derived functor; and termwise extension of scalars leaves a complex
concentrated in degree `0` concentrated in degree `0`. -/
private theorem isGE_totalDerivedExtensionScalars_singleFunctor_obj
    {R : Type u} {C : Type u} [CommRing R] [CommRing C] (f : R →+* C)
    (M : ModuleCat.{u} R) [Projective M] :
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsGE 0 := by
  let _ : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
    CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
      (by change PreservesFiniteColimits _; infer_instance)
  have hproj : ∀ i, Projective
      (((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M).X i) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      exact Projective.of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi).projective
  have hstrict : CochainComplex.IsStrictlyGE
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M)) 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (ModuleCat.extendScalars.{u, u, u} f).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M) 0 i hi)
  have hGE : DerivedCategory.IsGE
      ((CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{u, u, u} f).obj
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M)) 0 := by
    have h : (CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{u, u, u}
          f).obj ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M) =
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M)) := rfl
    rw [h]
    infer_instance
  have hcmp :=
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      f).comparison_isIso_of_projective
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M) 0
  exact DerivedCategory.TStructure.t.isGE_of_iso (@asIso _ _ _ _ _ hcmp).symm 0

/-- **The derived base change of the cotangent complex of a polynomial algebra sits in degree
`0`.** If `B` is a polynomial algebra over `A` and `C` is a `B`-algebra, then
`L_{B/A} ⊗^𝐋_B C` lies in `D^{≥0}(C)`.

By Tag 08QH the complex `L_{B/A}` is quasi-isomorphic to the single complex on `Ω[B⁄A]`, which is
a free and hence projective `B`-module, and a bounded-above complex of projectives computes
derived extension of scalars. -/
theorem isGE_cotangentComplexDerivedBaseChange_of_isPolynomialAlgebra
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (C : Type u) [CommRing C] [Algebra B C]
    (hB : Algebra.IsPolynomialAlgebra A B) :
    (cotangentComplexDerivedBaseChange A (CommAlgCat.of A B) C).IsGE 0 := by
  have : Module.Projective ↥(CommAlgCat.of A B)
      (KaehlerDifferential A ↥(CommAlgCat.of A B)) :=
    KaehlerDifferential.projective_of_isPolynomialAlgebra hB
  obtain ⟨e⟩ := cotangentComplex_iso_kaehlerDifferential A (CommAlgCat.of A B) hB
  have := isGE_totalDerivedExtensionScalars_singleFunctor_obj
    (algebraMap ↥(CommAlgCat.of A B) C)
    (ModuleCat.of ↥(CommAlgCat.of A B) (KaehlerDifferential A ↥(CommAlgCat.of A B)))
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
      (algebraMap ↥(CommAlgCat.of A B) C)).functor.mapIso e).symm 0

section Retraction

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Algebra B A]
  [IsScalarTower A B A]

/-- **`L_{A/B}` lies in `D^{≥ -1}(A)` for the augmentation of a polynomial algebra.** The
fundamental triangle of `A → B → A` has zero middle vertex, since `L_{A/A} = 0`, so its
connecting morphism identifies `L_{A/B}` with the shift of the first vertex
`L_{B/A} ⊗^𝐋_B A`, which lies in degree `0`. -/
theorem isGE_cotangentComplexDerived_retraction
    (hB : Algebra.IsPolynomialAlgebra A B) (h08QX : HasFundamentalTriangleAt A B A) :
    (cotangentComplexDerived B (CommAlgCat.of B A)).IsGE (-1) := by
  obtain ⟨α, β, δ, hT⟩ := h08QX
  have h₂ : IsZero (cotangentComplexDerived A (CommAlgCat.of A A)) :=
    isZero_cotangentComplex_self A
  have hiso : IsIso δ := (Triangle.isZero₂_iff_isIso₃ (Triangle.mk α β δ) hT).1 h₂
  have h₁ : (cotangentComplexDerivedBaseChange A (CommAlgCat.of A B) A).IsGE 0 :=
    isGE_cotangentComplexDerivedBaseChange_of_isPolynomialAlgebra A B A hB
  have h₁' : ((cotangentComplexDerivedBaseChange A (CommAlgCat.of A B) A)⟦(1 : ℤ)⟧).IsGE (-1) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 1 (-1) (by omega)
  exact DerivedCategory.TStructure.t.isGE_of_iso (@asIso _ _ _ _ _ hiso).symm (-1)

/-- **`H^i(L_{A/B}) = 0` for `i ≤ -2`**, for the augmentation `B → A` of a polynomial algebra
`B` over `A`. This is the one vanishing that
`CommAlgCat.nonempty_cotangentComplex_iso_single_of_isZero_homology_le_negTwo` needs. -/
theorem isZero_homology_cotangentComplex_retraction
    (hB : Algebra.IsPolynomialAlgebra A B) (h08QX : HasFundamentalTriangleAt A B A)
    (i : ℤ) (hi : i ≤ -2) :
    IsZero ((cotangentComplex B (CommAlgCat.of B A)).homology i) := by
  have := isGE_cotangentComplexDerived_retraction A B hB h08QX
  refine (DerivedCategory.isZero_of_isGE
    (cotangentComplexDerived B (CommAlgCat.of B A)) (-1) i (by omega)).of_iso ?_
  exact ((DerivedCategory.homologyFunctorFactors
    (ModuleCat.{u} ↥(CommAlgCat.of B A)) i).app (cotangentComplex B (CommAlgCat.of B A))).symm

/-- **Stacks Project, Tag 08SI.** Let `A` be a commutative ring, let `B` be a polynomial algebra
over `A`, and let `B → A` be a retraction of `A → B` — an augmentation. Let `I = ker(B → A)`.
Then `L_{A/B}` is quasi-isomorphic to `I/I²[1]`, that is, isomorphic in `D(A)` to the conormal
module `I/I²` placed in cohomological degree `-1`.

The source states this for `A = ℤ`, `B = ℤ[x₁, …, xₙ]` and the augmentation sending every
variable to `0`, whose kernel is the ideal `I = (x₁, …, xₙ)`; the statement here is that case
with the base ring and the set of variables left general. -/
@[stacks 08SI "the lemma for a general base ring A and a general polynomial algebra B over it \
  with an augmentation B → A, of which the source's A = Z[x_1,...,x_n] -> B = Z sending every \
  x_i to 0 is the case A = Z; the source's ideal I = (x_1,...,x_n) is the kernel of the \
  augmentation, and I/I^2 is its conormal module. ONE carried hypothesis: h08QX, Proposition \
  08QX for the tower A -> B -> A, which is the triangle the source's proof invokes and which is \
  not proved in this library — the triangle the library carries, Tag 08SD, needs the middle map \
  injective, whereas the augmentation B → A is surjective. The hypothesis is 08QX itself, for a \
  general not-necessarily-injective map, and not the conclusion proved here"]
theorem nonempty_cotangentComplex_retraction_iso_single
    (hB : Algebra.IsPolynomialAlgebra A B) (h08QX : HasFundamentalTriangleAt A B A) :
    Nonempty (DerivedCategory.Q.obj (cotangentComplex B (CommAlgCat.of B A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} ↥(CommAlgCat.of B A)) (-1)).obj
        (ModuleCat.of ↥(CommAlgCat.of B A)
          (surjectionExtension B (CommAlgCat.of B A)
            (surjective_algebraMap_of_isScalarTower_self A B)).Cotangent)) :=
  nonempty_cotangentComplex_iso_single_of_isZero_homology_le_negTwo B (CommAlgCat.of B A)
    (surjective_algebraMap_of_isScalarTower_self A B)
    (isZero_homology_cotangentComplex_retraction A B hB h08QX)

end Retraction

end CommAlgCat

end
