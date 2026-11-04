module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.Independence

/-!
# Inverse systems of distinguished triangles computing compactly supported cohomology

Let `f : X ⟶ Y` be a morphism of `FTS_S` and let `K ⟶ L ⟶ M ⟶ K[1]` be a distinguished
triangle of `D^b_{Coh}(𝒪_X)`. [Stacks, Tag 0G52] produces an inverse system of distinguished
triangles

`K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]`

of `D^b_{Coh}(𝒪_Y)` whose three vertex systems give the pro-objects `Rf_! K`, `Rf_! L` and
`Rf_! M`.

The source's proof is two steps. Choose a compactification `j : X ⟶ X̄` over `Y`, with structure
morphism `f̄ : X̄ ⟶ Y`, so that `Rf_! = Rf̄_* ∘ Rj_!`. First apply [Stacks, Tag 0G4M] to `j` and
the given triangle: it produces an inverse system of distinguished triangles
`K̄_n ⟶ L̄_n ⟶ M̄_n ⟶ K̄_n[1]` of `D^b_{Coh}(𝒪_{X̄})` whose vertex systems give `Rj_! K`, `Rj_! L`
and `Rj_! M`. Then put `K_n = Rf̄_* K̄_n`, and likewise for `L_n` and `M_n`. That these give
`Rf_! K`, `Rf_! L` and `Rf_! M` is, as the source puts it, the very definition of `Rf_!`: the
pro-object of a termwise pushed-forward inverse sequence is the pushforward of the pro-object of
the sequence, which is `CategoryTheory.ProSeq.pushforwardOfIso`.

This file carries out the second step, for a compactification in the sense of
`CategoryTheory.Compactification` — the data one compactification contributes to the construction
of `Rf_!`, as in [Stacks, Tag 0G50]. The first step is the hypothesis
`CategoryTheory.Compactification.TriangleExtension`, which is the conclusion of
[Stacks, Tag 0G4M] for the open immersion of the compactification, stated for every distinguished
triangle of `D^b_{Coh}(𝒪_X)`.

## Main definitions

* `CategoryTheory.Compactification.pushforwardTriangleSystem`: the inverse system
  `(Rf̄_* K̄_n ⟶ Rf̄_* L̄_n ⟶ Rf̄_* M̄_n ⟶ Rf̄_* K̄_n[1])` of triangles of `D^b_{Coh}(𝒪_Y)`.
* `CategoryTheory.Compactification.TriangleExtension`: the conclusion of [Stacks, Tag 0G4M] for
  the open immersion of the compactification.

## Main results

* `CategoryTheory.Compactification.shriekImageProIso`: an inverse sequence over `X̄` whose
  pro-object is `Rj_! K` has termwise pushforward whose pro-object is `Rf_! K`.

## Implementation notes

**What is assumed.** The compactification `j : X ⟶ X̄` over `Y` is a
`CategoryTheory.Compactification`, so `Rf_!` is `CategoryTheory.Compactification.shriekImage`;
by [Stacks, Tag 0G50] the result does not depend on that choice. The exactness of `Rf̄_*` is the
three instance hypotheses on `CategoryTheory.Compactification.direct`, which hold because `f̄` is
proper. Nothing else is assumed beyond [Stacks, Tag 0G4M] for `j`, whose scheme-theoretic form is
`AlgebraicGeometry.DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent`.

**Why the vertex systems need no comparison.** The system of triangles produced is the termwise
image `TM ⋙ Rf̄_*.mapTriangle`, and the first vertex of the image of a triangle under
`CategoryTheory.Functor.mapTriangle` is the image of its first vertex; so the vertex systems of
the image system are the termwise images of the vertex systems, on the nose rather than up to
isomorphism. This is what makes `CategoryTheory.ProSeq.pushforwardOfIso` directly applicable.

## References

* [Stacks Project, Tag 0G52](https://stacks.math.columbia.edu/tag/0G52)
* [Stacks Project, Tag 0G4M](https://stacks.math.columbia.edu/tag/0G4M)
* [Stacks Project, Tag 0G50](https://stacks.math.columbia.edu/tag/0G50)
* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u₁ u₂ u₃

namespace CategoryTheory.Compactification

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v} 𝒟]
  {ℳ : Type u₃} [Category.{v} ℳ] [HasShift ℳ ℤ] [HasShift 𝒟 ℤ]

/-- The termwise image under the proper pushforward `Rf̄_*` of an inverse system of triangles of
`D^b_{Coh}(𝒪_{X̄})`: the inverse system `(Rf̄_* K̄_n ⟶ Rf̄_* L̄_n ⟶ Rf̄_* M̄_n ⟶ Rf̄_* K̄_n[1])` of
triangles of `D^b_{Coh}(𝒪_Y)`. -/
public def pushforwardTriangleSystem (C : Compactification 𝒞 𝒟 ℳ) [C.direct.CommShift ℤ]
    (TM : ℕᵒᵖ ⥤ Triangle ℳ) : ℕᵒᵖ ⥤ Triangle 𝒟 :=
  TM ⋙ C.direct.mapTriangle

/-- The first vertex system of the pushed-forward system of triangles is the termwise pushforward
of the first vertex system. -/
public lemma pushforwardTriangleSystem_comp_π₁ (C : Compactification 𝒞 𝒟 ℳ)
    [C.direct.CommShift ℤ] (TM : ℕᵒᵖ ⥤ Triangle ℳ) :
    pushforwardTriangleSystem C TM ⋙ Triangle.π₁ = (TM ⋙ Triangle.π₁) ⋙ C.direct :=
  rfl

/-- The second vertex system of the pushed-forward system of triangles is the termwise pushforward
of the second vertex system. -/
public lemma pushforwardTriangleSystem_comp_π₂ (C : Compactification 𝒞 𝒟 ℳ)
    [C.direct.CommShift ℤ] (TM : ℕᵒᵖ ⥤ Triangle ℳ) :
    pushforwardTriangleSystem C TM ⋙ Triangle.π₂ = (TM ⋙ Triangle.π₂) ⋙ C.direct :=
  rfl

/-- The third vertex system of the pushed-forward system of triangles is the termwise pushforward
of the third vertex system. -/
public lemma pushforwardTriangleSystem_comp_π₃ (C : Compactification 𝒞 𝒟 ℳ)
    [C.direct.CommShift ℤ] (TM : ℕᵒᵖ ⥤ Triangle ℳ) :
    pushforwardTriangleSystem C TM ⋙ Triangle.π₃ = (TM ⋙ Triangle.π₃) ⋙ C.direct :=
  rfl

/-- **An inverse sequence giving `Rj_! K` has termwise pushforward giving `Rf_! K`.** This is the
"very definition of `Rf_!`" of [Stacks, Tag 0G52]: the functor `Rf_! = Rf̄_* ∘ Rj_!` applies
`Rf̄_*` to pro-objects, and on the pro-object of an inverse sequence that is the pro-object of the
termwise image sequence, `CategoryTheory.ProSeq.pushforwardOfIso`. -/
public def shriekImageProIso (C : Compactification 𝒞 𝒟 ℳ) {MM : ℕᵒᵖ ⥤ ℳ} {K : 𝒞}
    (e : ProSeq.of MM ≅ (extensionByZero C.restrict C.assignment).obj K) :
    ProSeq.of (MM ⋙ C.direct) ≅ C.shriekImage.obj K :=
  (ProSeq.pushforwardOfIso C.adj MM).symm ≪≫ (ProSeq.pushforward C.adj).mapIso e

variable [HasZeroObject ℳ] [Preadditive ℳ] [∀ n : ℤ, (shiftFunctor ℳ n).Additive]
  [Pretriangulated ℳ] [HasZeroObject 𝒟] [Preadditive 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]

/-- Every triangle of the pushed-forward system is distinguished, because `Rf̄_*` is an exact
functor of triangulated categories. -/
public lemma pushforwardTriangleSystem_distinguished (C : Compactification 𝒞 𝒟 ℳ)
    [C.direct.Additive] [C.direct.CommShift ℤ] [C.direct.IsTriangulated]
    {TM : ℕᵒᵖ ⥤ Triangle ℳ} (hTM : ∀ n, TM.obj n ∈ distTriang ℳ) (n : ℕᵒᵖ) :
    (pushforwardTriangleSystem C TM).obj n ∈ distTriang 𝒟 :=
  C.direct.map_distinguished _ (hTM n)

variable [HasZeroObject 𝒞] [Preadditive 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

/-- **The conclusion of [Stacks, Tag 0G4M] for the open immersion `j : X ⟶ X̄` of a
compactification**: every distinguished triangle `K ⟶ L ⟶ M ⟶ K[1]` of `D^b_{Coh}(𝒪_X)` is given
by an inverse system of distinguished triangles of `D^b_{Coh}(𝒪_{X̄})` whose three vertex systems
give the pro-objects `Rj_! K`, `Rj_! L` and `Rj_! M`.

In the source these systems are the Deligne systems of the three objects; the scheme-theoretic
construction is
`AlgebraicGeometry.DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent`. -/
public def TriangleExtension (C : Compactification 𝒞 𝒟 ℳ) : Prop :=
  ∀ T : Triangle 𝒞, T ∈ distTriang 𝒞 →
    ∃ TM : ℕᵒᵖ ⥤ Triangle ℳ, (∀ n, TM.obj n ∈ distTriang ℳ) ∧
      Nonempty (ProSeq.of (TM ⋙ Triangle.π₁) ≅
        (extensionByZero C.restrict C.assignment).obj T.obj₁) ∧
      Nonempty (ProSeq.of (TM ⋙ Triangle.π₂) ≅
        (extensionByZero C.restrict C.assignment).obj T.obj₂) ∧
      Nonempty (ProSeq.of (TM ⋙ Triangle.π₃) ≅
        (extensionByZero C.restrict C.assignment).obj T.obj₃)

end CategoryTheory.Compactification

end
