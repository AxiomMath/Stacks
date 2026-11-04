module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingHomEquivNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.ProjectionFormulaInternalHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor–internal-Hom adjunction of a ringed site

Let `(C, O)` be a ringed site. The bijection of [Stacks, Tag 08J8]

`Hom_{D(O)}(A, R𝓗om_O(B, M)) ≃ Hom_{D(O)}(A ⊗^L_O B, M)`

is natural in `A`, in `B` and in `M`. This file packages it, at the derived tensor product the
relative cup product of [Stacks, Tag 0B68] lands in, as a
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction`: the datum from
which the trace map of [Stacks, Tag 0B6H] is built.

## Main definitions

* `Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomBijection.NaturalInSource`,
  `NaturalInMiddle` and `NaturalInTarget` — the three naturality conditions on a
  tensor–internal-Hom bijection, as propositions.
* `Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction.ofNatural` —
  a bijection satisfying the three conditions is an adjunction.
* `Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction` —
  **the tensor–internal-Hom adjunction of [Stacks, Tag 08J8]** on a ringed site.

## Main results

* `naturalInSource_derivedTensorHomBijection`, `naturalInMiddle_derivedTensorHomBijection` and
  `naturalInTarget_derivedTensorHomBijection`, in the same namespace — the bijection
  `derivedTensorHomBijection` is natural in its three objects.

## Implementation notes

The three naturality conditions are named propositions about a bijection `D`, rather than being
stated afresh for `derivedTensorHomBijection`, so that each is proved against exactly the
statement the structure field asks for. The derived categories of the ringed site carry two
spellings of the ring sheaf and two abelian structures on its modules, which agree only after
unfolding far enough that a direct comparison exceeds the elaborator's recursion limit; the named
propositions keep the comparison syntactic.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

/-! ### Naturality of a tensor–internal-Hom bijection -/

section Abstract

variable {C : Type*} [Category C] {T : C ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ C}

/-- A tensor–internal-Hom bijection is **natural in the source**: precomposing with `u : A' ⟶ A`
corresponds to precomposing with `u ⊗ 1`. -/
def TensorHomBijection.NaturalInSource (D : TensorHomBijection T H) : Prop :=
  ∀ {A A' B M : C} (u : A' ⟶ A) (h : A ⟶ (H.obj (op B)).obj M),
    D.homEquiv A' B M (u ≫ h) = (T.map u).app B ≫ D.homEquiv A B M h

/-- A tensor–internal-Hom bijection is **natural in the object tensored with**: postcomposing with
`H(g, M)` for `g : B' ⟶ B` corresponds to precomposing with `1 ⊗ g`. -/
def TensorHomBijection.NaturalInMiddle (D : TensorHomBijection T H) : Prop :=
  ∀ {A B B' M : C} (g : B' ⟶ B) (h : A ⟶ (H.obj (op B)).obj M),
    D.homEquiv A B' M (h ≫ (H.map g.op).app M) = (T.obj A).map g ≫ D.homEquiv A B M h

/-- A tensor–internal-Hom bijection is **natural in the target**: postcomposing with `H(B, m)`
for `m : M ⟶ M'` corresponds to postcomposing with `m`. -/
def TensorHomBijection.NaturalInTarget (D : TensorHomBijection T H) : Prop :=
  ∀ {A B M M' : C} (h : A ⟶ (H.obj (op B)).obj M) (m : M ⟶ M'),
    D.homEquiv A B M' (h ≫ (H.obj (op B)).map m) = D.homEquiv A B M h ≫ m

/-- A tensor–internal-Hom bijection natural in its three objects is a tensor–internal-Hom
adjunction. -/
def TensorHomAdjunction.ofNatural (D : TensorHomBijection T H) (hs : D.NaturalInSource)
    (hm : D.NaturalInMiddle) (ht : D.NaturalInTarget) : TensorHomAdjunction T H :=
  ⟨D, hs, hm, ht⟩

/-- The bijection of `TensorHomAdjunction.ofNatural` is the given one. -/
theorem TensorHomAdjunction.ofNatural_homEquiv (D : TensorHomBijection T H)
    (hs : D.NaturalInSource) (hm : D.NaturalInMiddle) (ht : D.NaturalInTarget) :
    (TensorHomAdjunction.ofNatural D hs hm ht).homEquiv = D.homEquiv :=
  rfl

end Abstract

/-! ### The adjunction of [Stacks, Tag 08J8] on a ringed site -/

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (Z : RingedSite.{u, u, u})
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]

/-- **The bijection of [Stacks, Tag 08J8] is natural in the source**: this is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, read across the natural
comparison `AlgebraicGeometry.RingedSite.derivedTensorFunctorIso` of the two derived tensor
products. -/
theorem naturalInSource_derivedTensorHomBijection :
    (derivedTensorHomBijection Z).NaturalInSource := by
  intro A A' B M u h
  rw [derivedTensorHomBijection_homEquiv, derivedTensorCurryHomEquiv_apply,
    derivedTensorCurryHomEquiv_apply, RingedSite.derivedCurryHomEquiv_naturality_source,
    ← Category.assoc, ← Category.assoc]
  congr 1
  exact (NatTrans.congr_app ((RingedSite.derivedTensorFunctorIso Z).inv.naturality u) B).symm

/-- **The bijection of [Stacks, Tag 08J8] is natural in the object tensored with**: the
three-variable naturality `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality` at
identities in the source and the target, read across
`AlgebraicGeometry.RingedSite.derivedTensorFunctorIso`. -/
theorem naturalInMiddle_derivedTensorHomBijection :
    (derivedTensorHomBijection Z).NaturalInMiddle := by
  intro A B B' M g h
  have key := RingedSite.derivedCurryHomEquiv_naturality Z (𝟙 A) g (𝟙 M) h
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, NatTrans.id_app,
    Category.id_comp] at key
  rw [derivedTensorHomBijection_homEquiv, derivedTensorCurryHomEquiv_apply,
    derivedTensorCurryHomEquiv_apply, key, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (((RingedSite.derivedTensorFunctorIso Z).inv.app A).naturality g).symm

/-- **The bijection of [Stacks, Tag 08J8] is natural in the target**: this is
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_target`. -/
theorem naturalInTarget_derivedTensorHomBijection :
    (derivedTensorHomBijection Z).NaturalInTarget := by
  intro A B M M' h m
  rw [derivedTensorHomBijection_homEquiv, derivedTensorCurryHomEquiv_apply,
    derivedTensorCurryHomEquiv_apply, RingedSite.derivedCurryHomEquiv_naturality_target,
    Category.assoc]

/-- **The tensor–internal-Hom adjunction of [Stacks, Tag 08J8]** on a ringed site, at the derived
tensor product the relative cup product of [Stacks, Tag 0B68] lands in: the bijection
`Hom(A, R𝓗om(B, M)) ≃ Hom(A ⊗^L B, M)` of `derivedTensorHomBijection` with its naturality in
the three objects. -/
@[sga "4½ Etat_0 6.2" "more general",
  sga "5 IIIB 5.2" "special case",
  sga "7 VIII 1.1" "more general"]
def derivedTensorHomAdjunction :
    TensorHomAdjunction (derivedTensorProductFunctor Z.O) (RingedSite.derivedSheafHomBifunctor Z) :=
  TensorHomAdjunction.ofNatural (derivedTensorHomBijection Z)
    (naturalInSource_derivedTensorHomBijection Z) (naturalInMiddle_derivedTensorHomBijection Z)
    (naturalInTarget_derivedTensorHomBijection Z)

/-- The bijection of `derivedTensorHomAdjunction` is `derivedTensorCurryHomEquiv`. -/
theorem derivedTensorHomAdjunction_homEquiv :
    (derivedTensorHomAdjunction Z).homEquiv = derivedTensorCurryHomEquiv Z :=
  rfl

end Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

end
