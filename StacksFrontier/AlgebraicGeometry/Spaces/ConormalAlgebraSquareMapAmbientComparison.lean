module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePullbackEpi
public import StacksFrontier.CategoryTheory.Functor.IsIsoMapOfHypothesis

/-!
# The canonical map of conormal algebras of a square as an inverse image of one ambient map

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
so `i ≫ g = f ≫ i'`.  Write `𝓘 = Ker(i^♯) ⊆ 𝒪_X`, `𝓘' = Ker((i')^♯) ⊆ 𝒪_{X'}` and
`𝓙 = Ker((f ≫ i')^♯) ⊆ 𝒪_{X'}` for the kernel ideal sheaf of the diagonal.
`AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom`, which carries the
`@[stacks 09RS]` attribute, is the canonical map

`f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X,*}`

of sheaves of graded `𝒪_Z`-algebras, built from an ambient homomorphism
`Ψ : g^*(⨁_{n ≥ 0} 𝓙ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ` of sheaves of graded `𝒪_X`-algebras which it takes as an
explicit hypothesis.

This file reduces the canonical map to a *single* morphism upstairs on the ambient space `X`.
Out of the square and `Ψ` it assembles

`χ : g^*(⨁_{n ≥ 0} (𝓘')ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ`,

the inverse image along `g` of the inclusion `⨁ (𝓘')ⁿ ⟶ ⨁ 𝓙ⁿ` followed by `Ψ`, and proves the
factorisation

`f^*𝒞_{Z'/X',*} ≅ (f ≫ i')^*(⨁ (𝓘')ⁿ) ≅ i^*(g^*(⨁ (𝓘')ⁿ)) --i^*χ--> i^*(⨁ 𝓘ⁿ) = 𝒞_{Z/X,*}`,

whose two leading arrows are isomorphisms.  Surjectivity and invertibility of the canonical map
in a degree are therefore surjectivity and invertibility of `i^*χ` in that degree, and the
inverse image of `𝒪`-modules preserves both.

## Main definitions

* `AlgebraicGeometry.Space.conormalAlgebraSquareAmbientComparison`: the ambient comparison
  `χ : g^*(⨁_{n ≥ 0} (𝓘')ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ` of sheaves of graded `𝒪_X`-algebras which a
  commutative square and an ambient homomorphism induce.

## Main results

* `AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom_eq_ambientComparison` and
  `AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom_app_eq_ambientComparison`:
  **the canonical map is the inverse image along `i` of the ambient comparison**, up to the two
  composition comparisons, and the same degreewise.
* `epi_conormalAlgebraSquareMapOfPullbackHom_app_of_epi_ambientComparison` and
  `isIso_conormalAlgebraSquareMapOfPullbackHom_app_of_isIso_ambientComparison`, both in
  `AlgebraicGeometry.Space`: the canonical map is surjective, resp. invertible, in a degree in
  which the ambient comparison is.
* `SheafOfModules.GradedAlgebra.isIso_app_of_isIso`: the degree-`n` component of an isomorphism
  of sheaves of graded algebras is an isomorphism of sheaves of modules.

## Relation to [Stacks Project, Tag 09RT], which is not proved here

Stacks 09RT asserts that the canonical map of Stacks 09RS is surjective when the square is
cartesian and `i`, `i'` are immersions, and an isomorphism when moreover `g` is flat.  **Nothing
in this file carries a Stacks 09RT tag attribute, and neither assertion is proved here**: the
two results above take surjectivity, resp. invertibility, of the ambient comparison as a
hypothesis, and that is precisely where the source's cartesian and flatness hypotheses would
act.  A conditional statement of that shape is not the tag's content, so it is not labelled with
it.  What this file contributes to Stacks 09RT is the reduction: it isolates the one morphism
upstairs on the ambient space about which the whole tag is a statement, and discharges the
passage from that morphism down to `Z`.

The reduction is not optional.  The first of the two factors of the canonical map is the inverse
image of the inclusion `⨁ (𝓘')ⁿ ⟶ ⨁ 𝓙ⁿ` of the powers of two genuinely different ideal sheaves
on `X'` — `𝓙` is the ideal sheaf of `Z` in `X'` and `𝓘'` that of `Z'` in `X'`, and they differ as
soon as `g` is not an isomorphism — so that factor is not surjective and no factorwise hypothesis
would do.  Only the composite is the inverse image of one morphism on `X`.

### What the two assertions are still waiting for

The hypotheses above cannot be discharged for the map as Stacks 09RS is available here, because
`AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom` takes `Ψ` as an *arbitrary*
parameter with no canonicity constraint: at `Ψ = 0` the canonical map is zero, so no
unconditional statement about it can hold.  The missing input is therefore a canonical `Ψ`, and
the following is what its construction needs.

* **The degreewise family is available**:
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap : g^*(𝓙ⁿ) ⟶ 𝓘ⁿ`, with its value on
  the unit sections of a chart diagram
  (`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_app_modulePullbackUnitSection`) and
  its multiplicativity there
  (`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_mul_modulePullbackUnitSection`).
  What is missing is that the family is a morphism in `SheafOfModules.GradedAlgebra`.
* **The criterion route is blocked.**
  `Stacks.Sheaves.GradedAlgebraPullback.homOfMulUnitGeneratorSectionOfLocal` tests the family on
  the generator sections `1 ⊗ x` of the pullback of graded algebras, and the
  `What is not proved` section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientUnitSection.lean` records what
  reading the unit-section formula in that form still needs: a chart-level description of a
  section of an inverse image on the small étale site, which
  `AlgebraicGeometry.Space.smallToposMorphism_inverseImage_obj_obj` supplies only for an étale
  `g`.  That gap is geometric, not a matter of reduction.
* **The adjunction route is open and is the one to try.**
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedAdj` is an adjunction
  `gradedPull g ⊣ gradedPush g` of sheaves of graded algebras, built by
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.adjunctionOfGradedUnitCounit` from a unit and a
  counit whose degreewise components are those of the Stacks 03D7 adjunction for sheaves of
  modules — and at
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedAlgebraPullbackPushforwardAdjunction`
  those two degreewise descriptions hold by reflexivity, with the right adjoint literally
  `pushFunctor`.  So a `Ψ` may be obtained as the transpose of a homomorphism
  `⨁ 𝓙ⁿ ⟶ g_*(⨁ 𝓘ⁿ)` of sheaves of graded algebras *on `X'`*, whose degreewise components are
  the single transposes that `kernelIdealSheafZPowPullbackMap` was built from, and whose
  degree-`n` component of the transpose is then the module-level transpose, hence
  `kernelIdealSheafZPowPullbackMap` itself.  The work this leaves is the multiplicativity of
  that homomorphism, which is a statement about local sections of a *direct* image and so is
  within reach of `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushedSectionEquiv` and the
  multiplication `transposedMultiplicationAt`, in the shape in which
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pushforwardGradedAlgebraHom` proves its own.
* **Surjectivity of the ambient comparison in degree one is available, for the cartesian
  square**: `AlgebraicGeometry.Space.epi_idealSheafMap`, and its flat invertibility is
  `AlgebraicGeometry.Space.isIso_idealSheafMap_of_isFlat`, both at
  `AlgebraicGeometry.Space.preimageSubspace`, which is the cartesian square; degree zero is
  `AlgebraicGeometry.Space.isIso_structureSheafMap`.  Three bridges were owed; **the two
  identifications are now in**: from `AlgebraicGeometry.Space.kernelIdealSheaf` of the vertical
  arrow of a cartesian square to `AlgebraicGeometry.Space.idealSheaf` of that preimage subspace,
  which is
  `AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf_preimageSubspace_of_isPullback`
  of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeCartesian.lean`, and from
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` in degree one to
  `AlgebraicGeometry.Space.idealSheafMap`, which is
  `AlgebraicGeometry.Space.kernelIdealSquareMap_one_eq_idealSheafMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMapDegreeOne.lean`, stated for
  `AlgebraicGeometry.Space.kernelIdealSquareMap`, of which the ambient map is the second factor.
  The third, a reduction, is the one still owed, and was already the widest gap of the three:
  those two degree-one results are stated for the *canonical* preimage square of a
  **closed** subspace — `AlgebraicGeometry.Space.preimageProjection` together with
  `AlgebraicGeometry.Space.conormalEtaleRestrictionSquare` — whereas Stacks 09RT has an abstract
  cartesian square whose vertical arrows are **immersions**.  Base carries no passage from an
  abstract `CategoryTheory.IsPullback` square to that canonical one outside the étale case
  (`AlgebraicGeometry.Space.conormalAlgebraEtaleRestriction` and its neighbours all assume
  `AlgebraicGeometry.Space.IsEtale` of the transverse arrow), and an immersion is handled here
  by the factorisation `AlgebraicGeometry.Space.immersionClosedFactorization`, whose conormal
  algebra `AlgebraicGeometry.Space.conormalAlgebraOfImmersion` is a different object from the
  `AlgebraicGeometry.Space.conormalAlgebra` the canonical map of Stacks 09RS is stated for.
* **Unitality, and the multiplication hypothesis, are extra inputs for the degree induction.**
  `Stacks.SheafOfModules.epi_unitalHom_app_add` takes a
  `SheafOfModules.GradedAlgebra.UnitalHom`, so the ambient comparison has to be shown to carry
  the unit — `SheafOfModules.GradedAlgebra.UnitalHom.ofHom` reduces this to one equation between
  global sections in degree zero — and it takes as a hypothesis that the multiplication of the
  *target* in the two degrees is locally surjective, as a morphism out of the objectwise tensor
  product of presheaves of modules.  For `⨁ 𝓘ⁿ` that is the statement that `𝓘^{i + j}` is
  locally generated by products of sections of `𝓘ⁱ` and `𝓘ʲ`.  It is true, and provable from the
  definition of `SheafOfModules.idealSheafPow` by the covering sieve `SheafOfModules.powSieve`
  together with `Ideal.pow_add`, but **no such local surjectivity result for the multiplication
  of `SheafOfModules.reesGradedAlgebra` is in the library**, and the induction needs it at every
  pair of degrees.
* **Degree propagation separates the two clauses of Stacks 09RT, and only the flat one has a
  tool.**  `Stacks.SheafOfModules.epi_unitalHom_app_add` concludes epimorphy in degree `i + j`
  from **invertibility** in the degrees `i` and `j`, not from epimorphy; the worked precedent
  `Stacks.LineBundle.Situation.isIso_symmetricToLaurent_app_natCast` accordingly carries
  invertibility through its induction and upgrades each epimorphism to an isomorphism using that
  both sides are invertible modules.

  For the **flat clause** the degree-one case is an isomorphism, so that lemma is the right
  shape: invertibility in the degrees `i` and `j` gives epimorphy in `i + j`, and the step is
  closed by monomorphy in `i + j` from flatness — the shape of
  `AlgebraicGeometry.Space.mono_idealSheafMap_of_isFlat` in degree one, which composes the map
  with the embedding of the ideal sheaf into the structure sheaf and uses exactness of flat
  pullback — followed by `CategoryTheory.isIso_of_mono_of_epi` in the balanced category of
  sheaves of modules.  Induction then runs from degrees zero and one.  That monomorphy at the
  `n`-th power is itself owed: it needs the composite of
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` with the embedding of `𝓘ⁿ` into
  `𝒪_X` to be identified with the inverse image along `g` of the embedding of `(𝓘')ⁿ` into
  `𝒪_{X'}` followed by the comparison of structure sheaves, which is the `n`-th power
  analogue of `AlgebraicGeometry.Space.idealSheafMap_comp_ι`.  **That analogue is now proved**,
  as `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_comp_ι` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbientStructureSheaf.lean`, with the
  comparison spelled `AlgebraicGeometry.Space.structureModulePullbackMap`; its injectivity
  consequence is `AlgebraicGeometry.Space.mono_kernelIdealSheafZPowPullbackMap_of_mono_comp`
  there.  The proof is the one `idealSheafMap_comp_definingIdealSheaf_ι` uses, because the two
  morphisms are built the same way — both chartwise maps are
  `AlgebraicGeometry.Space.chartDiagramPullback`.

  For the **surjectivity clause** the degree-one case is only an epimorphism, so the induction
  needs an epimorphy-only form of `Stacks.SheafOfModules.epi_unitalHom_app_add`, which in turn
  needs that the objectwise tensor product of two locally surjective morphisms of presheaves of
  modules is locally surjective.  No such lemma is in the library, and that clause is therefore
  the further of the two.

## Implementation notes

**Why the category-theoretic steps are stated in an arbitrary category.**  The types of the
sheaves of graded algebras here are large enough that `rw` on them exhausts the elaborator's
reduction budget, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMap.lean` record for related
statements.  The four `private` lemmas below are the whole shape of the argument — associativity
across a naturality square, and the stability of epimorphy and invertibility under composition —
stated where the terms are small; what remains at the concrete types is one reflexivity step and
one application.

**Why the statements are for arbitrary morphisms and not for immersions.**  As in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraSquareMap.lean`, nothing below uses any
property of `i` or `i'`, so the statements are strictly more general than the situation of
Stacks 09RS and Stacks 09RT, which take both vertical arrows to be immersions; they specialise
to them.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RT](https://stacks.math.columbia.edu/tag/09RT)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe t a v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- **The degree-`n` component of an isomorphism of sheaves of graded algebras is an isomorphism
of sheaves of modules.**  Composition and the identity of sheaves of graded algebras are
degreewise, so the degree-`n` component of the inverse is an inverse of the degree-`n`
component. -/
theorem isIso_app_of_isIso {A D : GradedAlgebra.{t, a} R} (φ : A ⟶ D) (hφ : IsIso φ) (n : ℤ) :
    IsIso (φ.app n) :=
  have := hφ
  ⟨⟨(inv φ).app n,
    by rw [← categoryStruct_comp_app, IsIso.hom_inv_id, categoryStruct_id_app],
    by rw [← categoryStruct_comp_app, IsIso.inv_hom_id, categoryStruct_id_app]⟩⟩

end SheafOfModules.GradedAlgebra

namespace AlgebraicGeometry.Space

/-! ### The category-theoretic steps, at a readable size -/

/-- Two isomorphisms followed by an epimorphism compose to an epimorphism. -/
private theorem epi_comp₃_of_isIso {C : Type*} [Category C] {W Y₁ Y₂ Y₃ : C} (a : W ⟶ Y₁)
    (b : Y₁ ⟶ Y₂) (c : Y₂ ⟶ Y₃) [IsIso a] [IsIso b] [Epi c] : Epi (a ≫ b ≫ c) :=
  inferInstance

/-- Three isomorphisms compose to an isomorphism. -/
private theorem isIso_comp₃ {C : Type*} [Category C] {W Y₁ Y₂ Y₃ : C} (a : W ⟶ Y₁)
    (b : Y₁ ⟶ Y₂) (c : Y₂ ⟶ Y₃) [IsIso a] [IsIso b] [IsIso c] : IsIso (a ≫ b ≫ c) :=
  inferInstance

/-- Moving a morphism across a naturality square inside a composite of four arrows: given
`b ≫ c = e ≫ k` and `k ≫ d = m`, the composite `(a ≫ b) ≫ c ≫ d` is `a ≫ e ≫ m`. -/
private theorem comp_fac {C : Type*} [Category C] {W Y₁ Y₂ Y₃ Y₄ Y₅ : C}
    (a : W ⟶ Y₁) (b : Y₁ ⟶ Y₂) (c : Y₂ ⟶ Y₃) (d : Y₃ ⟶ Y₄) (e : Y₁ ⟶ Y₅) (k : Y₅ ⟶ Y₃)
    (m : Y₅ ⟶ Y₄) (h : b ≫ c = e ≫ k) (hm : k ≫ d = m) :
    (a ≫ b) ≫ c ≫ d = a ≫ e ≫ m := by
  rw [← hm, Category.assoc, ← Category.assoc b, h, Category.assoc]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X X' Z' : AlgebraicSpaces B S hS}

/-! ### The ambient comparison of a square -/

/-- **The ambient comparison `g^*(⨁_{n ≥ 0} (𝓘')ⁿ) ⟶ ⨁_{n ≥ 0} 𝓘ⁿ` of a commutative square**,
given an ambient homomorphism as in [Stacks Project, Tag 09RS].  Here `𝓘' = Ker((i')^♯)`,
`𝓙 = Ker((f ≫ i')^♯)` and `𝓘 = Ker(i^♯)`, and the comparison is the inverse image along `g` of
the inclusion `⨁ (𝓘')ⁿ ⟶ ⨁ 𝓙ⁿ` of
`AlgebraicGeometry.Space.kernelIdealGradedAlgebraCompHom`, followed by the given `Ψ`.

This is the one morphism on the ambient space `X` of which the canonical map of Stacks 09RS is
the inverse image along `i`, up to the two composition comparisons; the module documentation
records why both factors of that map are needed to produce it, and that it is the morphism about
which Stacks 09RT is a statement. -/
noncomputable def conormalAlgebraSquareAmbientComparison (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i) :
    (gradedPull (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposHom B S hS g)).obj (kernelIdealGradedAlgebra B S hS i') ⟶
      kernelIdealGradedAlgebra B S hS i :=
  (gradedPull (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).map
      (kernelIdealGradedAlgebraCompHom B S hS f i' f i' rfl) ≫ Ψ

/-- The degree-`n` component of the ambient comparison is the inverse image along `g` of the
inclusion of the `n`-th powers of the two kernel ideal sheaves on `X'`, followed by the
degree-`n` component of `Ψ`. -/
theorem conormalAlgebraSquareAmbientComparison_app (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i)
    (n : ℤ) :
    (conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n =
      (modulePullback B S hS g).map
          ((kernelIdealGradedAlgebraCompHom B S hS f i' f i' rfl).app n) ≫ Ψ.app n :=
  rfl

/-! ### The canonical map as an inverse image of the ambient comparison -/

/-- The canonical map of Stacks 09RS written out as the composite of the four arrows its two
factors are built from: the composition comparison of the first factor, the inverse image along
the diagonal `f ≫ i'` of the inclusion of the powers of the two kernel ideal sheaves, the
composition comparison of the ambient factor, and the inverse image along `i` of `Ψ`. -/
private theorem conormalAlgebraSquareMapOfPullbackHom_eq_four (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i) :
    conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq Ψ =
      (((gradedAlgebraPullbackCompIso B S hS f i').app
            (kernelIdealGradedAlgebra B S hS i')).inv ≫
        (gradedPull (X := smallEtaleRingedTopos B S hS Z)
            (Y := smallEtaleRingedTopos B S hS X')
            (smallEtaleRingedToposHom B S hS (f ≫ i'))).map
          (kernelIdealGradedAlgebraCompHom B S hS f i' f i' rfl)) ≫
        (((gradedAlgebraPullbackCompIsoOfEq B S hS i g (f ≫ i') hsq.symm).app
            (kernelIdealGradedAlgebra B S hS (f ≫ i'))).hom ≫
          (gradedPull (X := smallEtaleRingedTopos B S hS Z)
              (Y := smallEtaleRingedTopos B S hS X)
              (smallEtaleRingedToposHom B S hS i)).map Ψ) :=
  rfl

/-- **The canonical map of [Stacks Project, Tag 09RS] is the inverse image along `i` of the
ambient comparison, up to the two composition comparisons.**  Both leading arrows are
isomorphisms, so surjectivity and invertibility of the canonical map are surjectivity and
invertibility of `i^*χ`.

The proof is naturality of the multiplicative Stacks 03LU comparison
`AlgebraicGeometry.Space.gradedAlgebraPullbackCompIsoOfEq` in the graded algebra: it carries the
inverse image along the diagonal `f ≫ i'` of the inclusion of the powers of the two kernel ideal
sheaves to the inverse image along `i` of the inverse image along `g` of that inclusion, which
is the first factor of the ambient comparison. -/
theorem conormalAlgebraSquareMapOfPullbackHom_eq_ambientComparison (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i) :
    conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq Ψ =
      ((gradedAlgebraPullbackCompIso B S hS f i').app
            (kernelIdealGradedAlgebra B S hS i')).inv ≫
        ((gradedAlgebraPullbackCompIsoOfEq B S hS i g (f ≫ i') hsq.symm).app
            (kernelIdealGradedAlgebra B S hS i')).hom ≫
          (gradedPull (X := smallEtaleRingedTopos B S hS Z)
              (Y := smallEtaleRingedTopos B S hS X)
              (smallEtaleRingedToposHom B S hS i)).map
            (conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ) :=
  (conormalAlgebraSquareMapOfPullbackHom_eq_four B S hS i i' f g hsq Ψ).trans
    (comp_fac _ _ _ _ _ _ _
      ((gradedAlgebraPullbackCompIsoOfEq B S hS i g (f ≫ i') hsq.symm).hom.naturality
        (kernelIdealGradedAlgebraCompHom B S hS f i' f i' rfl))
      ((gradedPull (X := smallEtaleRingedTopos B S hS Z)
          (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS i)).map_comp
        ((gradedPull (X := smallEtaleRingedTopos B S hS X)
            (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).map
          (kernelIdealGradedAlgebraCompHom B S hS f i' f i' rfl)) Ψ).symm)

/-- **The degree-`n` component of the canonical map of [Stacks Project, Tag 09RS] is the inverse
image along `i` of the degree-`n` component of the ambient comparison**, up to the degree-`n`
components of the two composition comparisons, which are isomorphisms of sheaves of modules. -/
theorem conormalAlgebraSquareMapOfPullbackHom_app_eq_ambientComparison (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i)
    (n : ℤ) :
    (conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq Ψ).app n =
      ((gradedAlgebraPullbackCompIso B S hS f i').app
              (kernelIdealGradedAlgebra B S hS i')).inv.app n ≫
        ((gradedAlgebraPullbackCompIsoOfEq B S hS i g (f ≫ i') hsq.symm).app
              (kernelIdealGradedAlgebra B S hS i')).hom.app n ≫
          (modulePullback B S hS i).map
            ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n) := by
  rw [conormalAlgebraSquareMapOfPullbackHom_eq_ambientComparison]
  simp only [SheafOfModules.GradedAlgebra.categoryStruct_comp_app]
  rfl

/-! ### Passing surjectivity and invertibility down from the ambient space

Neither statement below is [Stacks Project, Tag 09RT]: each takes as a hypothesis the property
of the ambient comparison that Stacks 09RT's cartesian and flatness hypotheses would supply, and
the module documentation records what the construction of a canonical ambient homomorphism — the
one input that would let those hypotheses be discharged — is still waiting for. -/

/-- **The canonical map of [Stacks Project, Tag 09RS] is surjective in a degree in which the
ambient comparison is.**  By
`AlgebraicGeometry.Space.conormalAlgebraSquareMapOfPullbackHom_app_eq_ambientComparison` the
canonical map is in degree `n` the inverse image along `i` of the ambient comparison in degree
`n` preceded by two isomorphisms, and the inverse image of `𝒪`-modules preserves surjections,
being a left adjoint: `AlgebraicGeometry.Space.preservesEpimorphisms_modulePullback`.

This is the descent half of the surjectivity assertion of [Stacks Project, Tag 09RT], not that
assertion: the source deduces surjectivity from the square being cartesian, which is what makes
the ambient comparison surjective — for a cartesian square `𝓘 = 𝓘'·𝒪_X`, so `𝓘ⁿ` is generated
by the image of `g^*((𝓘')ⁿ)` — and that step is upstairs on the ambient space and is the
hypothesis here. -/
theorem epi_conormalAlgebraSquareMapOfPullbackHom_app_of_epi_ambientComparison (i : Z ⟶ X)
    (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i)
    (n : ℤ)
    (hχ : Epi ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n)) :
    Epi ((conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq Ψ).app n) := by
  have h₃ : Epi ((modulePullback B S hS i).map
      ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n)) :=
    @Functor.PreservesEpimorphisms.preserves _ _ _ _ _
      (preservesEpimorphisms_modulePullback B S hS i) _ _ _ hχ
  rw [conormalAlgebraSquareMapOfPullbackHom_app_eq_ambientComparison]
  exact @epi_comp₃_of_isIso _ _ _ _ _ _ _ _ _
    (SheafOfModules.GradedAlgebra.isIso_app_of_isIso _ inferInstance n)
    (SheafOfModules.GradedAlgebra.isIso_app_of_isIso _ inferInstance n) h₃

/-- **The canonical map of [Stacks Project, Tag 09RS] is an isomorphism in a degree in which the
ambient comparison is**: the canonical map is in that degree the inverse image along `i` of the
ambient comparison in that degree preceded by two isomorphisms, and a functor preserves
isomorphisms.

This is the descent half of the isomorphism assertion of [Stacks Project, Tag 09RT], not that
assertion: in the source the hypothesis of that half is that `g` be flat, which is what makes
the ambient comparison an isomorphism — for a cartesian square with `g` flat,
`g^*((𝓘')ⁿ) ⟶ 𝓘ⁿ` is bijective — and that step is upstairs on the ambient space and is the
hypothesis here, so flatness does not appear below. -/
theorem isIso_conormalAlgebraSquareMapOfPullbackHom_app_of_isIso_ambientComparison (i : Z ⟶ X)
    (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X') (hsq : i ≫ g = f ≫ i')
    (Ψ : (gradedPull (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS X') (smallEtaleRingedToposHom B S hS g)).obj
        (kernelIdealGradedAlgebra B S hS (f ≫ i')) ⟶ kernelIdealGradedAlgebra B S hS i)
    (n : ℤ)
    (hχ : IsIso ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n)) :
    IsIso ((conormalAlgebraSquareMapOfPullbackHom B S hS i i' f g hsq Ψ).app n) := by
  have h₃ : IsIso ((modulePullback B S hS i).map
      ((conormalAlgebraSquareAmbientComparison B S hS i i' f g Ψ).app n)) :=
    CategoryTheory.Functor.isIso_map_of_isIso (modulePullback B S hS i) _ hχ
  rw [conormalAlgebraSquareMapOfPullbackHom_app_eq_ambientComparison]
  exact @isIso_comp₃ _ _ _ _ _ _ _ _ _
    (SheafOfModules.GradedAlgebra.isIso_app_of_isIso _ inferInstance n)
    (SheafOfModules.GradedAlgebra.isIso_app_of_isIso _ inferInstance n) h₃

end AlgebraicGeometry.Space

end
