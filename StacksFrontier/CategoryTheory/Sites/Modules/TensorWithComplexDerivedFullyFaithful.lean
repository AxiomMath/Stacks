module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFullyFaithful
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerived
public import StacksCore.Tactic.StacksAttribute

/-!
# Full faithfulness of the derived tensor product with a complex on a ringed site

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. [Stacks,
Tag 09LZ] says that if

1. `K` represents a compact object of `D(O)`, and
2. `E` computes the ext groups of `K` in `D(O)`,

then the derived tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived` (Tag 09LX) is fully faithful.

The argument is the one of [Stacks, Tag 09R9], the same statement for a differential graded
bimodule, `DifferentialGraded.Bimodule.derivedTensorFunctor_fullyFaithful`: the functor has a
right adjoint `RHom(K, -)` by Tag 09LY, a left adjoint is fully faithful exactly when the unit
of the adjunction is invertible (Tag 07RB), and the objects of `D(E, d)` at which the unit is
invertible are all of them by the dévissage of Tag 0FQE — the class is closed under direct sums
because `RHom(K, -)` commutes with direct sums, which is hypothesis (1); it satisfies
two-out-of-three in a distinguished triangle because both functors are exact; and it contains
every shift `E[k]` of the regular module, which is hypothesis (2).

## Main definitions

* `CategoryTheory.Adjunction.fullyFaithfulL_of_devissage`: the criterion above, abstractly — a
  left adjoint between pretriangulated categories whose right adjoint commutes with direct sums
  is fully faithful as soon as the source admits a dévissage down to the shifts of a weak
  generator on which the left adjoint is bijective on morphisms.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_fullyFaithful`: the same statement for
  the functor of Tag 09LX, with the right adjoint, the adjunction, the weak generation and the
  dévissage of `D(E, d)` as arguments.

## Main results

* `CategoryTheory.Adjunction.isIso_unit_of_devissage`: under the same hypotheses the unit of the
  adjunction is an isomorphism.

## Implementation notes

*How the source's two hypotheses are read.* Hypothesis (1), compactness of `K` in `D(O)`, is used
in the source only through its consequence that `RHom(K, -)` commutes with direct sums, and that
consequence is what is assumed: `PreservesColimitsOfShape (Discrete ι) G` for every index type
`ι` in the section universe. Deriving it from compactness needs compactness of the regular module
in `D(E, d)`, which this library does not have, so it survives into Tag 09LZ as stated here.
Hypothesis (2), that `E` computes the ext groups of `K`, is read as `hExt`: the functor
`- ⊗_E^𝐋 K` is bijective from `Hom_{D(E, d)}(E, E[n])` onto its image for every `n`. This is
the same shape as hypothesis (2) of Tag 09R9 in
`DifferentialGraded.Bimodule.derivedTensorFunctor_fullyFaithful`, and it is the source's
hypothesis read through the two identifications `H^n(E) = Hom_{D(E, d)}(E, E[n])` (the regular
module represents cohomology) and `E ⊗_E^𝐋 K = K`, which are built into the reading of (2)
rather than proved.

*The abstract criterion.* `CategoryTheory.Adjunction.fullyFaithfulL_of_devissage` assembles the
three dévissage clauses `CategoryTheory.Adjunction.isIso_unit_app_sigma`,
`CategoryTheory.Adjunction.isIso_unit_app_of_mem_distTriang` and
`CategoryTheory.Adjunction.isIso_unit_app_shift_of_bijective_map` into one statement, with the
dévissage principle of the source category as a hypothesis instead of the particular one of
Tag 0FQE.

## References

* [Stacks Project, Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ), the result stated here.
* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX) for the functor,
  [Tag 09LY](https://stacks.math.columbia.edu/tag/09LY) for the adjunction,
  [Tag 09R9](https://stacks.math.columbia.edu/tag/09R9) for the same statement over a
  differential graded algebra, [Tag 07RB](https://stacks.math.columbia.edu/tag/07RB) for the
  criterion of full faithfulness and [Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE) for
  the dévissage.
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace CategoryTheory.Adjunction

universe w v₁ v₂ u₁ u₂

section Devissage

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated C] [Pretriangulated D]
  [HasCoproducts.{w} D] {F : D ⥤ C} {G : C ⥤ D}

/-- **The unit of an adjunction is invertible when the source admits a dévissage to the shifts of
a weak generator on which the left adjoint is bijective on morphisms.** Let `F ⊣ G` be an
adjunction of exact functors compatible with the translation between pretriangulated categories,
let `E` be a weak generator of the source of `F`, and assume

* `G` preserves the direct sums indexed by types in the universe `w`;
* `F` is bijective from `Hom(E, E[n])` onto `Hom(F E, F (E[n]))` for every `n : ℤ`;
* every property of objects of the source which holds of the shifts of `E`, passes to direct
  sums indexed by types in the universe `w`, and satisfies two-out-of-three in a distinguished
  triangle, holds of every object.

Then the unit of the adjunction is an isomorphism. -/
theorem isIso_unit_of_devissage (adj : F ⊣ G)
    [F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ ι : Type w, PreservesColimitsOfShape (Discrete ι) G]
    {E : D} (hgen : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hbij : ∀ n : ℤ, Function.Bijective (fun f : E ⟶ E⟦n⟧ => F.map f))
    (hdev : ∀ T : D → Prop,
      (∀ {ι : Type w} (Z : ι → D), (∀ i, T (Z i)) → T (∐ Z)) →
      (∀ Δ : Triangle D, Δ ∈ distTriang D →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ k : ℤ, T (E⟦k⟧)) → ∀ M : D, T M) :
    IsIso adj.unit := by
  have key : ∀ M : D, IsIso (adj.unit.app M) :=
    hdev (fun M => IsIso (adj.unit.app M)) (fun {_} Z hZ => adj.isIso_unit_app_sigma Z hZ)
      (fun Δ hΔ => adj.isIso_unit_app_of_mem_distTriang Δ hΔ)
      (fun k => adj.isIso_unit_app_shift_of_bijective_map hgen hbij k)
  exact NatIso.isIso_of_isIso_app _

/-- **A left adjoint is fully faithful when the source admits a dévissage to the shifts of a weak
generator on which it is bijective on morphisms.** Under the hypotheses of
`CategoryTheory.Adjunction.isIso_unit_of_devissage`, the left adjoint `F` is fully faithful. -/
def fullyFaithfulL_of_devissage (adj : F ⊣ G)
    [F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ ι : Type w, PreservesColimitsOfShape (Discrete ι) G]
    {E : D} (hgen : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (hbij : ∀ n : ℤ, Function.Bijective (fun f : E ⟶ E⟦n⟧ => F.map f))
    (hdev : ∀ T : D → Prop,
      (∀ {ι : Type w} (Z : ι → D), (∀ i, T (Z i)) → T (∐ Z)) →
      (∀ Δ : Triangle D, Δ ∈ distTriang D →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ k : ℤ, T (E⟦k⟧)) → ∀ M : D, T M) :
    F.FullyFaithful :=
  haveI := adj.isIso_unit_of_devissage hgen hbij hdev
  adj.fullyFaithfulLOfIsIsoUnit

end Devissage

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.RingedSite

universe u v w t s

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-- The object `E` of `D(E, d)`: the class of the endomorphism differential graded algebra of `K`
regarded as a right module over itself, whose cohomology is `H^*(E)`. -/
abbrev repRegularDerived :
    DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra :=
  (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
    ((toHomotopyCategory _).obj (regularModule (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))

/-- **Full faithfulness of `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)`**, with the right adjoint, the
adjunction, the weak generation and the dévissage of `D(E, d)` as arguments.

The functor is the one Tag 09LX constructs,
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived`. The source's hypothesis (2) is `hExt`,
the bijectivity of that functor on the morphism groups `Hom_{D(E, d)}(E, E[n])`; the source's
hypothesis (1) enters through `PreservesColimitsOfShape (Discrete ι) G`, the commutation of the
right adjoint with direct sums, which is the only use the source's proof makes of compactness.
Exactness of `- ⊗_E^𝐋 K` is not assumed; it follows from exactness of `G`. -/
def tensorWithComplexDerived_fullyFaithful
    {G : DerivedCategory (TensorModO.{u, v, w, t, s} X) ⥤
        DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, 0} X ℤ K).algebra}
    [HasCoproducts.{max u v w t s}
      (DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)]
    [G.CommShift ℤ] [G.IsTriangulated]
    (adj : tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⊣ G) [adj.CommShift ℤ]
    [∀ ι : Type (max u v w t s), PreservesColimitsOfShape (Discrete ι) G]
    (hgen : (ObjectProperty.singleton
      (repRegularDerived.{u, v, w, t, s} X K)).IsWeakTriangulatedGenerator)
    (hExt : ∀ n : ℤ, Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶
          (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).map f))
    (hdev : ∀ T : DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra → Prop,
      (∀ {ι : Type (max u v w t s)}
        (Z : ι → DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, 0} X ℤ K).algebra), (∀ i, T (Z i)) → T (∐ Z)) →
      (∀ Δ : Triangle (DifferentialGradedModule.derivedCategory.{0, max u v w t s,
          max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra),
        Δ ∈ distTriang (DifferentialGradedModule.derivedCategory.{0, max u v w t s,
          max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) →
        (T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃) ∧ (T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂) ∧
          (T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)) →
      (∀ k : ℤ, T ((repRegularDerived.{u, v, w, t, s} X K)⟦k⟧)) →
      ∀ M, T M) :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).FullyFaithful :=
  haveI := adj.isTriangulated_leftAdjoint
  adj.fullyFaithfulL_of_devissage hgen hExt hdev

end AlgebraicGeometry.RingedSite

end
