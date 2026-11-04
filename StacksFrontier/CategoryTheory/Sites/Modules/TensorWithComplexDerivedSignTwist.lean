module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.ConeSignTransfer
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexQuasicoherent

/-!
# The derived tensor product with a complex is exact, through the sign twist

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. The derived
tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of Tag 09LX is **not** an exact functor for the
pretriangulated structure `D(E, d)` carries in this library — the one induced from the cone
triangles of `K(Mod_(E, d))` — because the exactness Tag 09LW supplies is for the other of the
two sign conventions for the third arrow of a triangle. That is why
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_isTriangulated` has an unsatisfiable
hypothesis.

This file supplies the repair, and it is unconditional. The sign-twisted identity
`CategoryTheory.signTwist` — the identity functor carrying the shift comparison
`ε(n) = (-1)^n` — absorbs the discrepancy, and `- ⊗_E^𝐋 K ⋙ signTwist _` *is* exact. Nothing is
redefined: `signTwist` is the identity on objects and on morphisms, so
`- ⊗_E^𝐋 K ⋙ signTwist _` is the functor `- ⊗_E^𝐋 K` of Tag 09LX with a different comparison
with the translation, and any statement not mentioning that comparison — full faithfulness,
preservation of colimits, the maps on `Ext` of Tag 0CS6 — is literally the same statement about
either.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_mapTriangle_mem_distTriang`:
  **Tag 09LW** in the form the transfer consumes — tensoring with `K` followed by the
  localization carries the triangle of an admissible short exact sequence to a distinguished
  triangle. The statement names no pretriangulated structure on `K(Mod_(E, d))`, so it can be
  proved with the admissible one in force and used with the cone one in force.
* `AlgebraicGeometry.RingedSite.signTwist_tensorWithComplexToDerivedCategory_isTriangulated` and
  `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_signTwist_isTriangulated`:
  that functor is exact for the cone structure after the twist, taken on `K(Mod_(E, d))` and
  taken on `D(O)` respectively — the two agree, by
  `CategoryTheory.comp_signTwist_mapTriangle_obj_eq`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated`:
  **`- ⊗_E^𝐋 K` is exact, through the twist**, with no hypothesis at all.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_additive` and
  `AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_additive`: the additivity of
  the two functors, which Mathlib derives from their exactness.
* `AlgebraicGeometry.RingedSite.exists_distTriang_isIso_tensorWithComplexDerivedCounit`, with
  `AlgebraicGeometry.RingedSite.exists_quasiIso_leftOrthogonal_acyclic_rep` and
  `AlgebraicGeometry.RingedSite.quasiIsomorphismsRepHasRightCalculusOfFractions`: the resolution
  clause `CategoryTheory.Functor.isTriangulated_of_rightExtension` asks for. It mentions the
  functor being derived only through the comparison
  `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedCounit`, which the twist leaves alone, so
  the twisted and untwisted exactness statements consume the same clause.

## Implementation notes

*Which structure is in force where, and why the file is split in two.* The two pretriangulated
structures on `K(Mod_(E, d))` are instances on the same category, so a statement cannot be made
with both in scope. The first section pins
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, the admissible-sequence
structure of Tag 09KH, which is the one in which Tag 09LW is proved; it proves one statement, and
that statement mentions the class of admissible triangles directly, as
`DifferentialGradedModule.IsDistinguishedTriangle`, rather than through the instance, so it is
independent of the pinning. Everything after it pins
`DifferentialGradedModule.instPretriangulatedHomotopyCategory`, the cone structure, which is the
one that induces the triangulation of `D(E, d)` and therefore the one in which the dévissage of
Tag 0FQE, the weak generation of `D(E, d)` by the regular module and Tag 09LZ itself are all
read. Both sections pin the matching `Preadditive` instance as well, so that the instances
appearing in the types here are the ones the consumers synthesize.

*What the twist costs.* Two lemmas of `StacksFrontier.CategoryTheory.Shift.SignTwist` do the whole
of the bookkeeping: `CategoryTheory.comp_comp_signTwist_commShiftIso_hom_app` and
`CategoryTheory.comp_signTwist_commShiftIso_hom_app` say that the twist multiplies a shift
comparison by `ε(n)`, and `CategoryTheory.NatTrans.commShift_signTwist'` concludes that the
comparison `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedCounit` of the right extension
stays compatible with the shift after the twist, the factor `ε(n)` appearing on both sides of the
compatibility equation and cancelling. The rest of
`CategoryTheory.Functor.isTriangulated_of_rightExtension` is unchanged, the resolution of a
morphism of `D(E, d)` being
`AlgebraicGeometry.RingedSite.exists_distTriang_isIso_tensorWithComplexDerivedCounit`, which
mentions the functor only through that comparison.

*Why the twist is taken on `D(O)` and not on `D(E, d)`.* The two are interchangeable for the
*conclusion* — `CategoryTheory.comp_signTwist_mapTriangle_obj_eq` — but not for the *proof*. On
`D(O)` the twist is outermost in both `Q ⋙ (- ⊗_E^𝐋 K ⋙ signTwist _)` and
`- ⊗_E K ⋙ Qh ⋙ signTwist _`, so its comparison with the translation is never carried through
another functor and no additivity is needed; on `D(E, d)` it sits in the middle of the first
composite, and pulling the sign out through `- ⊗_E^𝐋 K` would need the additivity of
`- ⊗_E^𝐋 K`, which is what is being established. Taking the twist on the target is therefore
what makes the chain non-circular: the exactness here is unconditional, and the additivity of
both functors follows from it, Mathlib deriving additivity from exactness and `signTwist` being
the identity on morphisms.

*Two pitfalls in composing a twisted adjunction.*

First, `show T from e` does **not** produce `e`: it produces `have this := e; this`, and when it
appears in the *statement* of a lemma that wrapper is baked in, so instance search will never
match a goal whose subject is the plain term. That is why the twisted adjunction has names of its
own, `CategoryTheory.Adjunction.signTwistComp` and `CategoryTheory.Adjunction.compSignTwist`,
rather than being written as an ascription of the untwisted one at the point of use.

Second, because `signTwist` is the identity, `F ⋙ signTwist _` and `F` are definitionally equal,
and the *expected type* will then decide which of the two a metavariable is assigned. Applying
`CategoryTheory.Adjunction.fullyFaithfulL_of_devissage` against an expected type naming the
untwisted functor assigns the untwisted functor to its `F` and only afterwards matches the
twisted adjunction up to definitional equality, producing an `Adjunction.CommShift` goal with an
untwisted `F` and a twisted `G` that nothing can discharge. The fix is to ascribe the twisted
conclusion at the point of application and let the definitional equality be used once, at the
end; Tag 09LZ in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithfulDerivedHom` does
exactly that.

## References

* [Stacks Project, Tag 09LX](https://stacks.math.columbia.edu/tag/09LX), the functor.
* [Stacks Project, Tag 09LW](https://stacks.math.columbia.edu/tag/09LW), its underived form.
* [Stacks Project, Tag 09KH](https://stacks.math.columbia.edu/tag/09KH), the pretriangulated
  structure on `K(Mod_(E, d))` whose distinguished triangles come from admissible short exact
  sequences.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

attribute [local instance] HasDerivedCategory.standard

/-! ### Tag 09LW, read in the admissible structure -/

section Admissible

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

/-- **Tag 09LW in the form the sign transfer consumes.** Tensoring with `K`, followed by the
localization of `K(O)`, carries the triangle of an admissible short exact sequence of
differential graded `E`-modules to a distinguished triangle of `D(O)`.

The class of admissible triangles is named directly, as
`DifferentialGradedModule.IsDistinguishedTriangle`, and not through a `Pretriangulated`
instance, so this statement does not depend on which of the two structures on `K(Mod_(E, d))` is
in force; it is proved here with the admissible one pinned, because that is the one in which
Tag 09LW is proved, and consumed below with the cone one pinned. -/
theorem tensorWithComplexToDerivedCategory_mapTriangle_mem_distTriang
    (T : Triangle (DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))
    (hT : IsDistinguishedTriangle (Rep.{u, v, w, t, s, 0} X ℤ K).algebra T) :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).mapTriangle.obj T ∈
      distTriang (DerivedCategory (TensorModO.{u, v, w, t, s} X)) := by
  let : (tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K).IsTriangulated :=
    tensorWithComplexHomotopy_isTriangulated.{u, v, w, t, s, 0} X ℤ K
  let : (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).IsTriangulated :=
    show (tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K ⋙
      DerivedCategory.Qh (C := TensorModO.{u, v, w, t, s} X)).IsTriangulated from inferInstance
  exact mapTriangle_mem_distTriang_of_isTriangulated _
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K) T hT

end Admissible

/-! ### The twist, in the cone structure -/

section Cone

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory
  DifferentialGradedModule.instPreadditiveHomotopyCategory

/-- The quasi-isomorphisms of `K(Mod_(E, d))` admit a right calculus of fractions: they are the
morphisms whose cone is acyclic, and the acyclic modules form a triangulated subcategory. -/
instance quasiIsomorphismsRepHasRightCalculusOfFractions :
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).HasRightCalculusOfFractions := by
  rw [← acyclic_trW_eq_quasiIsomorphisms]
  infer_instance

/-- Every object of `K(Mod_(E, d))` receives a quasi-isomorphism from an object orthogonal on the
left to the acyclic modules, in the shape the resolution machinery consumes. -/
theorem exists_quasiIso_leftOrthogonal_acyclic_rep
    (Y : DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :
    ∃ (P : DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      (_ : (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal P) (f : P ⟶ Y),
      quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra f := by
  obtain ⟨P, f, hf, hP⟩ := exists_trW_leftOrthogonal_acyclic_rep.{u, v, w, t, s, 0} X ℤ K Y
  exact ⟨P, hP, f, by rwa [← acyclic_trW_eq_quasiIsomorphisms]⟩

/-- **Every morphism of `D(E, d)` is resolved by a distinguished triangle of `K(Mod_(E, d))` on
which the comparison with the underived functor is invertible.** This is the clause that
`CategoryTheory.Functor.isTriangulated_of_rightExtension` asks for, stated once because it is
what both the untwisted exactness statement below and its sign-twisted repair in
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedSignTwist` consume; it mentions
the functor being derived only through the comparison
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedCounit`, which the twist leaves alone.

Every morphism of `D(E, d)` is, up to isomorphism of arrows, the image of a morphism between
objects of `K(Mod_(E, d))` orthogonal on the left to the acyclic modules: those objects resolve
every object, so their inclusion is a localized equivalence and the induced functor is
essentially surjective on arrows. Completing such a morphism to a distinguished triangle leaves
all three vertices in the left orthogonal, the third because the left orthogonal of a
triangulated subcategory is a triangulated subcategory, and the comparison with ordinary
tensoring is invertible at each of them. -/
theorem exists_distTriang_isIso_tensorWithComplexDerivedCounit
    {Y Z : DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra} (g : Y ⟶ Z) :
    ∃ (T : Pretriangulated.Triangle
        (DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))
      (_ : T ∈ distTriang
        (DifferentialGradedModule.HomotopyCategory.{0, max u v w t s, max u v w t s}
          (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))
      (_ : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app T.obj₁))
      (_ : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app T.obj₂))
      (_ : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app T.obj₃)),
      Nonempty (Arrow.mk ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.map T.mor₁) ≅
        Arrow.mk g) := by
  have hres : (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal).HasLeftResolutions :=
    fun Y => by
      obtain ⟨P, hP, f, hf⟩ := exists_quasiIso_leftOrthogonal_acyclic_rep.{u, v, w, t, s} X K Y
      exact ⟨{ X₁ := ⟨P, hP⟩, w := f, hw := hf }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
    (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal
  have : ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).IsLocalization
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).inverseImage
        (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
        (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal)
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q)
    ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).inverseImage
      (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι)
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι ⋙
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).mapArrow) (Arrow.mk g)
  obtain ⟨W, p, q, hT⟩ := distinguished_cocone_triangle
    ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι.map a.hom)
  have h₁ : (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal
    (Triangle.mk ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι.map a.hom)
      p q).obj₁ := a.left.property
  have h₂ : (acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal
    (Triangle.mk ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι.map a.hom)
      p q).obj₂ := a.right.property
  exact ⟨Triangle.mk ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ι.map a.hom)
      p q, hT,
    isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K _ h₁,
    isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K _ h₂,
    isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K _
      ((acyclic (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).leftOrthogonal.ext_of_isTriangulatedClosed₃
        _ hT h₁ h₂), ⟨ea⟩⟩

/-- **Tag 09LW, transferred to the cone structure.** Tensoring with `K` followed by the
localization of `K(O)` is, after precomposition with the sign-twisted identity of
`K(Mod_(E, d))`, an exact functor for the pretriangulated structure whose distinguished triangles
are the cone triangles.

Without the twist this is false, by the witness in the docstring of
`AlgebraicGeometry.RingedSite.tensorWithComplexToDerivedCategory_isTriangulated'`. -/
theorem signTwist_tensorWithComplexToDerivedCategory_isTriangulated :
    (DifferentialGradedModule.signTwist (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
      tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).IsTriangulated :=
  isTriangulated_signTwist_comp (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K)
    (tensorWithComplexToDerivedCategory_mapTriangle_mem_distTriang.{u, v, w, t, s} X K)

/-- Tensoring with `K` followed by the localization of `K(O)` is additive. Mathlib derives
additivity from exactness, and `signTwist` is the identity on morphisms, so this is the
exactness above read through a definitional equality. -/
instance tensorWithComplexToDerivedCategory_additive :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).Additive :=
  let := signTwist_tensorWithComplexToDerivedCategory_isTriangulated.{u, v, w, t, s} X K
  inferInstanceAs ((DifferentialGradedModule.signTwist (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
    tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).Additive)

/-- **Tag 09LW, transferred with the twist on the target.** The same exactness as
`AlgebraicGeometry.RingedSite.signTwist_tensorWithComplexToDerivedCategory_isTriangulated`, with
the sign-twisted identity applied to `D(O)` instead of to `K(Mod_(E, d))`: by
`CategoryTheory.comp_signTwist_mapTriangle_obj_eq` the two composites act identically on
triangles. This is the side the right extension below needs, because there the twist is
outermost and its comparison with the translation is never carried through another functor. -/
theorem tensorWithComplexToDerivedCategory_signTwist_isTriangulated :
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).IsTriangulated where
  map_distinguished T hT := by
    let := signTwist_tensorWithComplexToDerivedCategory_isTriangulated.{u, v, w, t, s} X K
    rw [CategoryTheory.comp_signTwist_mapTriangle_obj_eq]
    exact (DifferentialGradedModule.signTwist (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
      tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K).map_distinguished T hT

/-- **The derived tensor product is exact, through the twist**: the functor `- ⊗_E^𝐋 K` of
Tag 09LX, composed with the sign-twisted identity of `D(O)`, carries distinguished triangles of
`D(E, d)` to distinguished triangles of `D(O)` — the pretriangulated structure on `D(E, d)`
being the one induced from the cone triangles of `K(Mod_(E, d))`, which is the structure in
which every other statement about `D(E, d)` in this library is read.

Unlike `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_isTriangulated` this is
**unconditional**: the exactness of the underived functor that the right extension needs is the
transferred form above, which is Tag 09LW.

`- ⊗_E^𝐋 K ⋙ signTwist _` is the functor `- ⊗_E^𝐋 K` itself — `signTwist` is the identity on
objects and on morphisms — carrying a different comparison with the translation. Exactness of a
*functor* is a statement about that comparison, which is why the twist is needed and why it is
not vacuous; a statement that does not mention the comparison holds of one exactly when it holds
of the other, by definitional equality. -/
theorem tensorWithComplexDerived_signTwist_isTriangulated :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).IsTriangulated := by
  let := tensorWithComplexToDerivedCategory_signTwist_isTriangulated.{u, v, w, t, s} X K
  let := CategoryTheory.NatTrans.commShift_signTwist'
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K)
    (tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K)
    (tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K)
  exact Functor.isTriangulated_of_rightExtension _
    (show (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⋙
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
          CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))) ⟶
      tensorWithComplexToDerivedCategory.{u, v, w, t, s, 0} X ℤ K ⋙
        CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) from
      tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K)
    (fun {_ _} g => exists_distTriang_isIso_tensorWithComplexDerivedCounit.{u, v, w, t, s} X K g)

/-- **`- ⊗_E^𝐋 K` is additive.** Mathlib derives additivity from exactness, and `signTwist` is
the identity on morphisms, so this is the exactness above read through a definitional equality.
It is what the additivity of the right adjoint `RHom(K, -)` is obtained from, through
`CategoryTheory.Adjunction.right_adjoint_additive`. -/
instance tensorWithComplexDerived_additive :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).Additive :=
  let := tensorWithComplexDerived_signTwist_isTriangulated.{u, v, w, t, s} X K
  inferInstanceAs ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
    CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))).Additive)

end Cone

end AlgebraicGeometry.RingedSite

end
