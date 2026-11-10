module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.TricomplexRotation
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The alternating Čech complex as a functor, and the total alternating Čech complex

Let `X` be a topological space and let `U : I → Opens X` be a family of open subsets. A
morphism of abelian presheaves on `X` acts on Čech cochains by applying it to every section,
and this action preserves the alternating condition, so the alternating Čech complex of
Stacks 01FH is a functor of the coefficient presheaf. Extending that functor by zero from `ℕ`
to `ℤ` and applying it degreewise to a complex of abelian presheaves gives a double complex,
the *alternating Čech bicomplex*, whose total complex is the complex `Tot(Č_alt(U, F^•))` that
the unbounded Čech theory of Stacks 08C0 and 08C1 compares with global sections.

## Main definitions

* `Stacks.Cech.cochainMap`: a morphism of abelian presheaves acting on Čech cochains.
* `Stacks.Cech.alternatingCochainMap` and `Stacks.Cech.alternatingCechMap`: the same action on
  alternating cochains, and the resulting morphism of alternating Čech complexes.
* `Stacks.Cech.alternatingCechComplexFunctor`: the alternating Čech complex as a functor of
  the coefficient presheaf.
* `Stacks.Cech.alternatingCechComplexFunctorInt`: the same, extended by zero to a
  `ℤ`-indexed complex.
* `Stacks.Cech.alternatingCechBicomplexFunctor`: the alternating Čech bicomplex of a complex
  of abelian presheaves, with the Čech degree placed first.
* `Stacks.Cech.alternatingCechTotalComplexFunctor`: its total complex.

## Main results

* `Stacks.Cech.cochainMap_cechD`: the action on cochains commutes with the Čech differential.
* `Stacks.Cech.cochainMap_isAlternating`: it preserves the alternating condition.
* `Stacks.Cech.restr_app`: restriction of sections commutes with a morphism of presheaves.

## Implementation notes

Coefficients are written out as `(Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}` rather than as
`TopCat.Presheaf Ab.{w} X`. The two are the same type and `TopCat.Presheaf` is
implicit-reducible, so the explicit functor category is accepted wherever the alternating
complex of Stacks 01FH expects a presheaf; but only the functor-category spelling carries the
`Preadditive` instance that a complex of presheaves and the degreewise extension of a functor
to complexes require, and introducing a second, parallel instance on the same category would
force every identification across it to be made by hand. This is the same convention as the
non-alternating total Čech complex uses.

The zero object of `AddCommGrpCat` used by the extension by zero is the one coming from the
abelian structure, which is also the one used to build the non-alternating total Čech complex
with which the alternating one is compared.

The space and the coefficient universes are independent, and so is the index universe; Čech
cochains for a family indexed by `I : Type v` and coefficients in `AddCommGrpCat.{w}` live in
`AddCommGrpCat.{max v w}`.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u v w

namespace Stacks.Cech

open CechCochains

variable {X : TopCat.{u}} {I : Type v} (U : I → Opens X)

section Functoriality

variable {F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- Restriction of sections commutes with a morphism of abelian presheaves. -/
lemma restr_app (a : F ⟶ G) {V W : Opens X} (h : W ≤ V) (x : (F.obj (op V) : Type w)) :
    restr G h (a.app (op V) x) = a.app (op W) (restr F h x) :=
  (ConcreteCategory.congr_hom (a.naturality (homOfLE h).op) x).symm

/-- A morphism of abelian presheaves acts on Čech cochains by applying it to every section. -/
def cochainMap (a : F ⟶ G) (p : ℕ) : Cochain U F p →+ Cochain U G p where
  toFun s := fun i ↦ a.app (op (inter U i)) (s i)
  map_zero' := by funext i; exact map_zero _
  map_add' s t := by funext i; exact map_add _ _ _

/-- The action of a morphism of presheaves on a cochain, evaluated at a tuple of indices. -/
@[simp]
lemma cochainMap_apply (a : F ⟶ G) (p : ℕ) (s : Cochain U F p) (i : Fin (p + 1) → I) :
    cochainMap U a p s i = a.app (op (inter U i)) (s i) := rfl

/-- The action of a morphism of presheaves on Čech cochains commutes with the Čech
differential. -/
lemma cochainMap_cechD (a : F ⟶ G) (p : ℕ) (s : Cochain U F p) :
    cochainMap U a (p + 1) (cechD U F p s) = cechD U G p (cochainMap U a p s) := by
  funext i
  change a.app (op (inter U i)) (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      restr F (inter_le_omit U i j) (s (i ∘ j.succAbove))) =
    ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      restr G (inter_le_omit U i j) (a.app _ (s (i ∘ j.succAbove)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, ← restr_app a (inter_le_omit U i j)]

/-- The action of a morphism of presheaves on Čech cochains preserves the alternating
condition. -/
lemma cochainMap_isAlternating (a : F ⟶ G) (p : ℕ) {s : Cochain U F p}
    (hs : IsAlternating U F s) : IsAlternating U G (cochainMap U a p s) := by
  refine ⟨fun i hi ↦ ?_, fun i j k hjk ↦ ?_⟩
  · change a.app (op (inter U i)) (s i) = 0
    rw [hs.1 i hi, map_zero]
  · change a.app (op (inter U (i ∘ Equiv.swap j k))) (s (i ∘ Equiv.swap j k)) = _
    rw [hs.2 i j k hjk, map_neg]
    congr 1
    exact ConcreteCategory.congr_hom (a.naturality _) (s i)

/-- A morphism of abelian presheaves acting on the groups of alternating Čech cochains. -/
def alternatingCochainMap (a : F ⟶ G) (p : ℕ) :
    AddCommGrpCat.of (alternatingSubgroup U F p) ⟶
      AddCommGrpCat.of (alternatingSubgroup U G p) :=
  AddCommGrpCat.ofHom <|
    ((cochainMap U a p).comp (alternatingSubgroup U F p).subtype).codRestrict
      (alternatingSubgroup U G p) (fun s ↦ cochainMap_isAlternating U a p s.2)

/-- The morphism of alternating Čech complexes induced by a morphism of abelian presheaves. -/
noncomputable def alternatingCechMap (a : F ⟶ G) :
    alternatingCechComplex U F ⟶ alternatingCechComplex U G :=
  CochainComplex.ofHom (alternatingCochainMap U a) (fun p ↦ by
    rw [alternatingCechComplex_d, alternatingCechComplex_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply Subtype.ext
    exact (cochainMap_cechD U a p s.1).symm)

/-- The degree `p` component of `alternatingCechMap U a` is `alternatingCochainMap U a p`. -/
@[simp]
lemma alternatingCechMap_f (a : F ⟶ G) (p : ℕ) :
    (alternatingCechMap U a).f p = alternatingCochainMap U a p := rfl

end Functoriality

/-- **Stacks 01FH**, functorially in the coefficient presheaf: the alternating Čech complex of
a family of opens, as a functor of the abelian presheaf of coefficients. -/
@[simps obj]
noncomputable def alternatingCechComplexFunctor :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ CochainComplex AddCommGrpCat.{max v w} ℕ where
  obj F := alternatingCechComplex U F
  map a := alternatingCechMap U a
  map_id F := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact Subtype.ext rfl
  map_comp a b := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact Subtype.ext rfl

/-- The alternating Čech complex functor preserves zero morphisms. -/
instance alternatingCechComplexFunctor_preservesZeroMorphisms :
    (alternatingCechComplexFunctor.{u, v, w} U).PreservesZeroMorphisms where
  map_zero _ _ := HomologicalComplex.Hom.ext <| funext fun _ ↦
    AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun _ ↦ Subtype.ext rfl

/-- The alternating Čech complex is an additive functor of the coefficient presheaf. -/
instance alternatingCechComplexFunctor_additive :
    (alternatingCechComplexFunctor.{u, v, w} U).Additive where
  map_add := HomologicalComplex.Hom.ext <| funext fun _ ↦
    AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun _ ↦ Subtype.ext rfl

/-- The alternating Čech complex extended by zero to a `ℤ`-indexed complex, functorially in
the coefficient presheaf. -/
noncomputable def alternatingCechComplexFunctorInt :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ CochainComplex AddCommGrpCat.{max v w} ℤ :=
  alternatingCechComplexFunctor U ⋙ embeddingUpNat.extendFunctor AddCommGrpCat.{max v w}

/-- The `ℤ`-indexed alternating Čech complex functor preserves zero morphisms. -/
instance alternatingCechComplexFunctorInt_preservesZeroMorphisms :
    (alternatingCechComplexFunctorInt.{u, v, w} U).PreservesZeroMorphisms :=
  inferInstanceAs (alternatingCechComplexFunctor U ⋙
    embeddingUpNat.extendFunctor AddCommGrpCat.{max v w}).PreservesZeroMorphisms

/-- The `ℤ`-indexed alternating Čech complex is an additive functor of the coefficient
presheaf. -/
instance alternatingCechComplexFunctorInt_additive :
    (alternatingCechComplexFunctorInt.{u, v, w} U).Additive :=
  inferInstanceAs (alternatingCechComplexFunctor U ⋙
    embeddingUpNat.extendFunctor AddCommGrpCat.{max v w}).Additive

/-- Applying the integer-indexed alternating Čech complex degreewise to a complex of abelian
presheaves, with the Čech degree placed first. -/
@[ega "0 12.4.5", ega "III 6.6.1" "The bicomplex C^•(U"]
noncomputable def alternatingCechBicomplexFunctor :
    CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max v w} (up ℤ) (up ℤ) :=
  (alternatingCechComplexFunctorInt U).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor AddCommGrpCat.{max v w} (up ℤ) (up ℤ)

/-- The functor sending a complex of abelian presheaves to the total complex of its
alternating Čech bicomplex, that is, to `Tot(Č_alt(U, F^•))`. -/
noncomputable def alternatingCechTotalComplexFunctor :
    CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ ⥤
      CochainComplex AddCommGrpCat.{max v w} ℤ :=
  alternatingCechBicomplexFunctor U ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{max v w} (up ℤ) (up ℤ) (up ℤ)

/-- The alternating Čech bicomplex is an additive functor of the complex of presheaves. -/
instance alternatingCechBicomplexFunctor_additive :
    (alternatingCechBicomplexFunctor.{u, v, w} U).Additive :=
  inferInstanceAs ((alternatingCechComplexFunctorInt U).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor AddCommGrpCat.{max v w} (up ℤ) (up ℤ)).Additive

/-- The total alternating Čech complex is an additive functor of the complex of presheaves. -/
instance alternatingCechTotalComplexFunctor_additive :
    (alternatingCechTotalComplexFunctor.{u, v, w} U).Additive :=
  inferInstanceAs (alternatingCechBicomplexFunctor U ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{max v w} (up ℤ) (up ℤ) (up ℤ)).Additive

end Stacks.Cech

end
