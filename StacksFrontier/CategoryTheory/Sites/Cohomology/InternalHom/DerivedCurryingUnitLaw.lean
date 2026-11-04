module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingUnitLaw
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality

/-!
# The unit law of the derived currying isomorphism, at representatives

Let `(C, O)` be a ringed site. The derived currying isomorphism of **Stacks 08J9**

`RSheafHom(K, RSheafHom(L, M)) ≅ RSheafHom(K ⊗^L_O L, M)`

is read here at `K = O[0]`. Its source then collapses by
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso`, the derived form of "internal Hom
out of the structure sheaf is the identity", and this file proves that what survives is the map
induced by the left unit collapse `λ_ L` of Tag 0FNG — the derived unit coherence of Tag 08J9,
stated at a K-flat `L` and a K-injective `I`, where both sides of Tag 08J9 are the classes of
internal Hom complexes.

This is the chain-level unit law
`AlgebraicGeometry.RingedSite.structureSheafHomIso_inv_comp_sheafHomTensorCurryIso` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingUnitLaw` transported into
`D(O)`, and the transport is pure bookkeeping: the comparison of Tag 08J9 with Tag 0A90 at
representatives (`AlgebraicGeometry.RingedSite.derivedCurryIso_comparison`) turns the derived
currying isomorphism into the class of the complex-level one, and the K-injective model of the
source identification (`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_model`) turns
the derived collapse into the class of evaluation at the unit section. The inner comparison of
the iterated internal Hom then cancels against itself and the chain-level law finishes it.

## Main results

* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_derivedCurryIso`: the unit
  law, with the collapse spelled `λ_ L`.
* `AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso_inv_comp_derivedCurryIso'`: the same
  at the `Stacks.SheafOfModules.Tensor.tensorComplex` spelling of the collapse.

## What this is for

The unit law (UL) of the derived-duality cluster — the compatibility of Stacks 08JA with
Stacks 08J8 recorded as the `hunit` hypothesis of
`Stacks.SheafOfModules.derivedDualCoevaluation_triangle` and
`Stacks.SheafOfModules.exactPairingDerivedDualOfApplicationLaws` in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectCoevaluation` — reduces, through
the two naturalities of Tag 08JA, to the `H⁰Γ` image of the derived unit coherence proved here.
What still separates the two is the passage from the representatives of this statement to
arbitrary objects of `D(O)`, and the identification of `DerivedCategory.Q.map (λ_ L).hom` with
the left unitor of the monoidal structure of `D(O)`, which is
`CochainComplex.KFlatMonoidal.leftUnitor_derivedTensorIso` re-seated by
`CategoryTheory.MonoidalCategory.reseat_leftUnitor_comp_of_unitality`. (UL) itself is not proved
here, and neither is (E1).

## Implementation notes

The statement is deliberately phrased with the representative isomorphisms
`AlgebraicGeometry.RingedSite.iteratedHomRepresentativeIso` — in its unfolded form, the inner
comparison followed by the outer one — and
`AlgebraicGeometry.RingedSite.tensorHomRepresentativeIso` rather than with the left unitor of
`D(O)`, so that it needs none of the instance pinning that the monoidal structure of `D(O)`
asks for at this cluster's diagonal `u`.

The cancellation of the inner comparison is done by `exact` against `inv_hom_comp_assoc`, a
lemma over an arbitrary category with every object and morphism a variable. The reason is the
one its docstring gives: after rewriting with the unfolded form of the iterated representative
isomorphism the goal carries that isomorphism's source at two definitionally equal spellings —
`(iteratedHomFunctor X).obj (modelTriple X _ _ _)` in the types and the explicit bifunctor
application in the terms — so the goal is not type-correct at the `implicit` transparency level,
and `Category.assoc` is then found neither by `rw` nor by `simp only`.

## References

* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- A retraction cancels, with the composite it is applied to left as it stands. Stated over an
arbitrary category with every object and morphism a variable: the goal it is used on below
mentions the source of the iterated representative isomorphism at two definitionally equal
spellings, so it is not type-correct at the `implicit` transparency level and no rewriting
tactic acts on it; one `exact` against this pays the crossing once instead. -/
private lemma inv_hom_comp_assoc {D : Type*} [Category* D] {a b c e : D}
    (u : a ⟶ b) (v : b ⟶ a) (huv : u ≫ v = 𝟙 a) (p : a ⟶ c) (q : c ⟶ e) :
    u ≫ (v ≫ p) ≫ q = p ≫ q := by
  rw [← Category.assoc u, ← Category.assoc, huv, Category.id_comp]

variable (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **The unit law of the derived currying isomorphism of Stacks 08J9, at a K-flat middle
complex and a K-injective target.** -/
theorem derivedStructureSheafHomIso_inv_comp_derivedCurryIso'
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (derivedStructureSheafHomIso X
          (DerivedCategory.Q.obj (sheafHomComplex X L I).obj)).inv ≫
        ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
            (derivedSheafHomComparison X L I).inv ≫
          (derivedCurryIso X (derivedStructureSheaf X) (DerivedCategory.Q.obj L)
              (DerivedCategory.Q.obj I)).hom ≫
            (tensorHomRepresentativeIso X (structureSheafComplex X) L I hL).hom =
      DerivedCategory.Q.map (homMap X (structureSheafComplexTensorLeftIso X L).hom (𝟙 I)) := by
  have := isKInjective_sheafHomComplex_of_isKFlat X L I hL
  -- the iterated representative isomorphism is the inner comparison followed by the outer one
  have hiterhom : (iteratedHomRepresentativeIso X (structureSheafComplex X) L I hL).hom =
      ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
          (derivedSheafHomComparison X L I).hom ≫
        (derivedSheafHomComparison X (structureSheafComplex X)
          (sheafHomComplex X L I).obj).hom := rfl
  -- the chain-level unit law, read against evaluation at the unit section
  have hcurry : structureSheafHomEvaluation X (sheafHomComplex X L I).obj ≫
      homMap X (structureSheafComplexTensorLeftIso X L).hom (𝟙 I) =
        (sheafHomTensorCurryIso X (structureSheafComplex X) L I).hom := by
    rw [← structureSheafHomIso_inv_comp_sheafHomTensorCurryIso' X L I, ← Category.assoc,
      show structureSheafHomEvaluation X (sheafHomComplex X L I).obj =
        (structureSheafHomIso X (sheafHomComplex X L I).obj).hom from rfl,
      Iso.hom_inv_id, Category.id_comp]
  refine (Iso.inv_comp_eq _).2 ?_
  rw [derivedCurryIso_comparison X (structureSheafComplex X) L I hL, hiterhom]
  refine Eq.trans (inv_hom_comp_assoc _ _
    ((derivedSheafHomComparison X L I).map_inv_hom_id
      ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X)))) _ _) ?_
  rw [derivedStructureSheafHomIso_model X (sheafHomComplex X L I).obj, Category.assoc,
    ← CategoryTheory.Functor.map_comp, hcurry]

/-- **The unit law of the derived currying isomorphism of Stacks 08J9, at a K-flat middle
complex and a K-injective target.** Identifying both `RSheafHom(O[0], RSheafHom(L, I))` and
`RSheafHom(O[0] ⊗^L_O L, I)` with the classes of internal Hom complexes, the derived currying
isomorphism of Tag 08J9 is the map induced by the left unit collapse `λ_ L` of Tag 0FNG.

This is `derivedStructureSheafHomIso_inv_comp_derivedCurryIso'` with the collapse spelled
`λ_ L` rather than `AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso`; the two
are `rfl`. -/
theorem derivedStructureSheafHomIso_inv_comp_derivedCurryIso
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) [I.IsKInjective] :
    (derivedStructureSheafHomIso X
          (DerivedCategory.Q.obj (sheafHomComplex X L I).obj)).inv ≫
        ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map
            (derivedSheafHomComparison X L I).inv ≫
          (derivedCurryIso X (derivedStructureSheaf X) (DerivedCategory.Q.obj L)
              (DerivedCategory.Q.obj I)).hom ≫
            (tensorHomRepresentativeIso X (structureSheafComplex X) L I hL).hom =
      DerivedCategory.Q.map (homMap X (λ_ L).hom (𝟙 I)) :=
  derivedStructureSheafHomIso_inv_comp_derivedCurryIso' X L I hL

end AlgebraicGeometry.RingedSite

end
