module

public import StacksFrontier.Deformation.ClassicalCase
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebraTangentRecord
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebrasRimSchlessinger
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClassesHull
public import StacksFrontier.Deformation.TangentSpace.LiftedComparison

/-!
# A hull for the deformations of a graded algebra

This file proves Stacks 0ET3: in the situation of Stacks Example 0D3L, if `P` is a finitely
generated graded `k`-algebra and `Λ` is a complete local ring with residue field `k` (the
classical case), then the functor of isomorphism classes of deformations of `P` has a hull.

## The standing condition of Example 0D3L

The section variable `[∀ d, Module.Finite k (grading d)]` is not a hypothesis added to 0ET3. It
is part of the definition of the deformation category `Def_P` that 0ET3 is about. Example 0D3L
reads: "Given a graded `k`-algebra `P` with `dim_k(P_d) < ∞` for all `d ≥ 0`, let `x_0 = (k, P)`
be the corresponding object of `F(k)`. We set `Def_P = F_{x_0}`", where an object `(A, P)` of
`F` must have every `P_d` a finite projective `A`-module. So `x_0 = (k, P)` exists only when
every graded piece of `P` is finite dimensional, and 0ET3 begins "In Example 0D3L". In Lean the
same condition is an argument of `specialFiber`, which builds `x_0`, and of
`deformationCategory`. A finitely generated graded algebra with an infinite-dimensional graded
piece, such as one with `P_0 = k[x]`, has no `Def_P` in the source.

The other conditions also come from the source. The grading is by `ℕ` ("for all `d ≥ 0`"), and
`P` is commutative, because Section 0DVX considers commutative graded algebras. `IsClassical Λ k`
is the classical case of Stacks 06GC: `Λ` is a Noetherian complete local ring and `k`, as a
`Λ`-algebra, is its residue field. The chapter fixes a Noetherian `Λ` in any case (Section 0DVM,
Step I). The conclusion is the definition of a hull in Stacks 06IY: a versal formal object of the
functor of isomorphism classes whose differential is bijective.

## The two hull theorems

The deformations of `P` form a deformation category (Stacks 0DVY), so the functor of fibrewise
isomorphism classes satisfies Schlessinger's conditions (S1) and (S2). The first hull theorem,
`exists_hull_isomorphismClasses_gradedAlgebra`, derives the hull from Stacks 06IZ. It assumes
that the tangent space is finite dimensional, and so it needs no finite generation of `P`. The
second theorem, `exists_hull_isomorphismClasses_gradedAlgebra_of_finiteType`, is Stacks 0ET3
itself. It assumes `P` of finite type over `k` and proves the tangent space finite dimensional
with `Deformation.Examples.ProjectiveGradedAlgebra.finiteDimensional_tangentSpace`, which is the
tangent-space clause of Stacks 0DVZ.

The two results use different models of the tangent space. The hull theorem of Stacks 06IZ asks
for finite dimensionality in the `Deformation.tangentSpaceArtinian` model, whose rank-one module
is `ULift k`. Stacks 0DVZ is stated in the `Deformation.artinianTangentSpace` model, whose
rank-one module is `k`.
`Deformation.finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace` is the linear
comparison between them.

## Main results

All of them live in the namespace `Deformation.Examples.ProjectiveGradedAlgebra`.

* `deformationProjection`: the structure functor of the deformation category of `P`.
* `isPredeformationCategory_deformationProjection` and `satisfiesRS_deformationProjection`:
  it is a deformation category, read off from Stacks 0DVY.
* `schlessingerConditionS1_deformationProjection` and
  `schlessingerConditionS2_deformationProjection`: Schlessinger's conditions for it.
* `schlessingerConditionS2_isomorphismClasses`: condition (S2) for the associated functor of
  isomorphism classes.
* `exists_hull_isomorphismClasses_gradedAlgebra`: the functor of isomorphism classes of
  deformations of `P` has a hull, given that its tangent space is finite dimensional.
* `exists_hull_isomorphismClasses_gradedAlgebra_of_finiteType`: **Stacks 0ET3**, the same for
  `P` of finite type over `k`, with no hypothesis on the tangent space.

## Implementation notes

The vector space structure on the tangent space is the canonical one of Stacks 06IH, which
instance search reads off two `Fact` instances. They are derivable — the first from the
predeformation structure and the second from condition (S2) through Stacks 06I0 — but the
finite-dimensionality hypothesis cannot even be stated before they are in scope, so they are
introduced by `letI` inside the hypothesis. This is the shape in which Stacks 06IW, 06IX and
06IZ state the same hypothesis.

## References

* [Stacks Project, Tag 0ET3](https://stacks.math.columbia.edu/tag/0ET3)
* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples.ProjectiveGradedAlgebra

universe u w m

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable (P : Type (max w m)) [CommRing P] [Algebra k P]
variable (grading : ℕ → Submodule k P) [GradedAlgebra grading]
variable [∀ d, Module.Finite k (grading d)]

/-- The structure functor of the deformation category of the graded algebra `P`: it sends a
deformation to its coefficient algebra, and is the slice projection of the category of graded
algebras with finite projective graded pieces at the special-fibre object. -/
public noncomputable abbrev deformationProjection :
    deformationCategory (Λ := Λ) P grading ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k :=
  objectsOverFunctor (projection.{u, w, w, max w m} (Λ := Λ) (k := k))
    (specialFiber (Λ := Λ) P grading)

/-- **Stacks 0DVY.** The deformations of a graded algebra with finite-dimensional graded pieces
form a deformation category. -/
public theorem isDeformationCategory_deformationProjection :
    IsDeformationCategory (deformationProjection (Λ := Λ) P grading) :=
  isDeformationCategory_deformationCategory (Λ := Λ) P grading

/-- The deformations of a graded algebra form a predeformation category. -/
public theorem isPredeformationCategory_deformationProjection :
    IsPredeformationCategory (deformationProjection (Λ := Λ) P grading) :=
  (isDeformationCategory_deformationProjection (Λ := Λ) P grading).predeformation

/-- The deformations of a graded algebra satisfy condition (RS). -/
public theorem satisfiesRS_deformationProjection :
    SatisfiesRS (deformationProjection (Λ := Λ) P grading) :=
  (isDeformationCategory_deformationProjection (Λ := Λ) P grading).satisfiesRS

/-- **Stacks 06J7.** The deformations of a graded algebra satisfy Schlessinger's condition
(S1). -/
public theorem schlessingerConditionS1_deformationProjection :
    SchlessingerConditionS1 (deformationProjection (Λ := Λ) P grading) :=
  schlessingerConditionS1_of_satisfiesRS (satisfiesRS_deformationProjection (Λ := Λ) P grading)

/-- **Stacks 06J7.** The deformations of a graded algebra satisfy Schlessinger's condition
(S2). -/
public theorem schlessingerConditionS2_deformationProjection :
    SchlessingerConditionS2 (deformationProjection (Λ := Λ) P grading) :=
  schlessingerConditionS2_of_satisfiesRS (satisfiesRS_deformationProjection (Λ := Λ) P grading)

/-- **Stacks 06I0.** The functor of isomorphism classes of deformations of a graded algebra
satisfies Schlessinger's condition (S2). -/
public theorem schlessingerConditionS2_isomorphismClasses :
    SchlessingerConditionS2 (CategoryOfElements.π (Deformation.isomorphismClasses
      (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
      (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered)) :=
  schlessingerConditionS2_of_isIsomorphismClasses _
    (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered
    (schlessingerConditionS2_deformationProjection (Λ := Λ) P grading)
    (Or.inl (isPredeformationCategory_deformationProjection (Λ := Λ) P grading))

/-- The functor of isomorphism classes of deformations of a graded `k`-algebra `P` over a
classical base has a hull, that is, a versal formal object with bijective differential, provided
its tangent space is finite dimensional.

The finite dimensionality of the graded pieces of `P` is the standing condition of Stacks
Example 0D3L, which defines `Def_P`: it is what makes `x_0 = (k, P)` an object of `F(k)`. It is
not an added hypothesis. This theorem assumes that the tangent space is finite dimensional
instead of assuming `P` finitely generated, so it is more general than Stacks 0ET3. In 0ET3 that
hypothesis is the tangent-space clause of Stacks 0DVZ, and
`exists_hull_isomorphismClasses_gradedAlgebra_of_finiteType` below proves it from finite
generation of `P`. That theorem carries the tag. -/
public theorem exists_hull_isomorphismClasses_gradedAlgebra (hΛ : IsClassical Λ k)
    (hfinite :
      letI : Fact (IsPredeformationCategory.{u, w, w}
          (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading)).p) :=
        ⟨isPredeformationCategory_deformationProjection (Λ := Λ) P grading⟩
      letI : Fact (SchlessingerConditionS2 (CategoryOfElements.π
          (Deformation.isomorphismClasses
            (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
            (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered))) :=
        ⟨schlessingerConditionS2_isomorphismClasses (Λ := Λ) P grading⟩
      FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k (Deformation.isomorphismClasses
        (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
        (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered))) :
    ∃ ξ : FormalObject (CategoryOfElements.π (Deformation.isomorphismClasses
        (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
        (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered)),
      IsVersal (categoryOfElements_projection_isCofibered (Deformation.isomorphismClasses
          (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
          (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered)) ξ ∧
        HasBijectiveDifferential
          (categoryOfElements_projection_isCofibered (Deformation.isomorphismClasses
            (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
            (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered))
          ξ := by
  let : IsNoetherianRing Λ := hΛ.isNoetherianRing
  let : Module.Finite Λ k := hΛ.moduleFinite
  let : Algebra.IsSeparable (residueImageField Λ k) k := hΛ.isSeparable
  let : Fact (IsPredeformationCategory.{u, w, w}
      (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading)).p) :=
    ⟨isPredeformationCategory_deformationProjection (Λ := Λ) P grading⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π (Deformation.isomorphismClasses
      (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
      (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered))) :=
    ⟨schlessingerConditionS2_isomorphismClasses (Λ := Λ) P grading⟩
  let : FiniteDimensional k (tangentSpaceArtinian.{u, w, w} Λ k (Deformation.isomorphismClasses
      (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
      (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered)) :=
    hfinite
  obtain ⟨ξ, -, hversal, hbijective⟩ :=
    exists_hull_isomorphismClasses.{u, w, w} Λ k
      (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
      (isPredeformationCategory_deformationProjection (Λ := Λ) P grading)
      (schlessingerConditionS1_deformationProjection (Λ := Λ) P grading)
      (schlessingerConditionS2_deformationProjection (Λ := Λ) P grading) inferInstance
  exact ⟨imageInIsomorphismClasses _
    (isPredeformationCategory_deformationProjection (Λ := Λ) P grading) ξ,
    hversal, hbijective⟩

/-- **Stacks 0ET3.** In Example 0D3L, assume `P` is a finitely generated graded `k`-algebra
and `Λ → k` is the classical case (`Λ` a Noetherian complete local ring with residue field `k`).
Then the functor `A ↦ Ob(Def_P(A))/≅` of isomorphism classes has a hull: a versal formal object
with bijective differential.

The section variable `[∀ d, Module.Finite k (grading d)]` is Example 0D3L's standing condition
defining `Def_P`. The source requires `dim_k(P_d) < ∞` for all `d ≥ 0` before it forms
`x_0 = (k, P)` and sets `Def_P = F_{x_0}`, and `specialFiber` requires the same condition to
build `x_0`. It is not a hypothesis added to 0ET3. The only hypotheses that 0ET3 adds to
Example 0D3L are finite generation, which is `[Algebra.FiniteType k P]`, and the classical case,
which is `hΛ`.

The proof applies `exists_hull_isomorphismClasses_gradedAlgebra`. Its hypothesis on the tangent
space comes from `finiteDimensional_tangentSpace`, the tangent-space clause of Stacks 0DVZ,
through the comparison of the two tangent-space models. -/
@[stacks 0ET3 "Def_P of 0D3L: finite-dimensional graded pieces define it, not an extra hypothesis"]
public theorem exists_hull_isomorphismClasses_gradedAlgebra_of_finiteType
    [Algebra.FiniteType k P] (hΛ : IsClassical Λ k) :
    ∃ ξ : FormalObject (CategoryOfElements.π (Deformation.isomorphismClasses
        (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
        (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered)),
      IsVersal (categoryOfElements_projection_isCofibered (Deformation.isomorphismClasses
          (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
          (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered)) ξ ∧
        HasBijectiveDifferential
          (categoryOfElements_projection_isCofibered (Deformation.isomorphismClasses
            (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
            (isPredeformationCategory_deformationProjection (Λ := Λ) P grading).cofibered))
          ξ :=
  exists_hull_isomorphismClasses_gradedAlgebra P grading hΛ
    (Deformation.finiteDimensional_tangentSpaceArtinian_of_artinianTangentSpace
      (BasedCategory.ofFunctor (deformationProjection (Λ := Λ) P grading))
      (isPredeformationCategory_deformationProjection (Λ := Λ) P grading)
      (schlessingerConditionS2_isomorphismClasses (Λ := Λ) P grading)
      (finiteDimensional_tangentSpace (Λ := Λ) P grading))

end Deformation.Examples.ProjectiveGradedAlgebra

end
