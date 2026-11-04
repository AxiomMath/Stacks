module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheafification of a presheaf with values in a type of algebraic structure

Let `X` be a topological space and let `(C, F)` be a *type of algebraic structure*
(`AlgebraicStructureType`, Stacks Tag 007M): a category `C` with a faithful functor
`F : C ⥤ Type` preserving limits and filtered colimits and reflecting isomorphisms.
Every `C`-valued presheaf on `X` then has a sheafification, and taking underlying sets
commutes with it.

The two hypotheses on `F` are exactly what is needed to turn `C` into a concrete category
whose forgetful functor is `F` (`AlgebraicStructureType.concreteCategory`), after which
Mathlib's `HasSheafify` and `GrothendieckTopology.PreservesSheafification` are available
and the lemma reduces to `sheafifyComposeIso` and the sheafification adjunction.

## Main results

* `AlgebraicStructureType.exists_sheafification`: Stacks Tag 0087, both clauses — the
  underlying sheaf of sets of `F^#` is the sheafification of the underlying presheaf of
  sets of `F`, and every map from `F` to a `C`-valued sheaf factors uniquely through `F^#`.

Supporting constructions:

* `AlgebraicStructureType.homFunLike`, `AlgebraicStructureType.concreteCategory`: a
  faithful functor to `Type` concretises its source category, with `forget C = F` on
  the nose.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicStructureType

variable (A : AlgebraicStructureType.{u, u})

/-- Morphisms of `A.C` act as functions on the underlying sets, injectively because `A.F`
is faithful.  This is the `FunLike` structure underlying `concreteCategory`. -/
@[reducible] def homFunLike : ∀ (Z W : A.C), FunLike (Z ⟶ W) (A.F.obj Z) (A.F.obj W) := fun _ _ =>
  { coe := fun g => A.F.map g
    coe_injective := fun {_ _} h => A.F.map_injective (by ext z; exact congrFun h z) }

/-- A type of algebraic structure `(C, F)` makes `C` a concrete category, with the bundled
functions between objects being the morphisms of `C` themselves.  This is set up so that
`forget A.C = A.F` holds by `rfl`, which is how the instances required by Mathlib's
sheafification machinery are transported from `A.F`. -/
@[reducible] def concreteCategory :
    letI := homFunLike A; ConcreteCategory.{u} A.C (fun Z W => Z ⟶ W) :=
  letI := homFunLike A
  { hom := fun g => g
    ofHom := fun g => g
    hom_ofHom := fun _ => rfl
    ofHom_hom := fun _ => rfl
    id_apply := fun {Z} z => show A.F.map (𝟙 Z) z = z by rw [A.F.map_id]; rfl
    comp_apply := fun {Z W V} g h z =>
      show A.F.map (g ≫ h) z = A.F.map h (A.F.map g z) by rw [A.F.map_comp]; rfl }

/-- **Stacks Tag 0087.**

Let `X` be a topological space, `(C, F)` a type of algebraic structure and `P` a presheaf
on `X` with values in `C`.  There is a sheaf `P^#` with values in `C` and a morphism
`η : P ⟶ P^#` of `C`-valued presheaves such that

1. `η` identifies the underlying presheaf of sets of `P^#` with the sheafification of the
   underlying presheaf of sets of `P`: there is an isomorphism `e` from
   `sheafify J (P ⋙ F)` to `P^# ⋙ F` under `P ⋙ F`, i.e. one satisfying
   `toSheafify J (P ⋙ F) ≫ e.hom = whiskerRight η F`;
2. every morphism `ψ : P ⟶ G` into a `C`-valued sheaf `G` factors uniquely as
   `P ⟶ P^# ⟶ G`. -/
@[stacks 0087, ega "0 3.5.6" "algebraic structures", sga "4 II 6.4" "topological space site"]
theorem exists_sheafification (X : TopCat.{u}) (P : (Opens X)ᵒᵖ ⥤ A.C) :
    ∃ (Psharp : Sheaf (Opens.grothendieckTopology X) A.C) (η : P ⟶ Psharp.obj),
      (∃ e : sheafify (Opens.grothendieckTopology X) (P ⋙ A.F) ≅ Psharp.obj ⋙ A.F,
          toSheafify (Opens.grothendieckTopology X) (P ⋙ A.F) ≫ e.hom =
            Functor.whiskerRight η A.F) ∧
      ∀ (G : Sheaf (Opens.grothendieckTopology X) A.C) (ψ : P ⟶ G.obj),
        ∃! χ : Psharp ⟶ G, η ≫ χ.hom = ψ := by
  let := homFunLike A
  let := concreteCategory A
  -- `forget A.C` is `A.F` on the nose, so the hypotheses on `A.F` are hypotheses on it.
  have h1 : PreservesLimits (forget A.C) := inferInstanceAs (PreservesLimits A.F)
  have h2 : (forget A.C).ReflectsIsomorphisms := inferInstanceAs A.F.ReflectsIsomorphisms
  have h3 : PreservesFilteredColimits (forget A.C) :=
    inferInstanceAs (PreservesFilteredColimits A.F)
  set J := Opens.grothendieckTopology X with hJ
  -- The limits and filtered colimits used by the sheafification construction.
  have a1 : ∀ (j : MulticospanShape.{u, u}), HasLimitsOfShape (WalkingMulticospan j) A.C :=
    fun _ => inferInstance
  have a2 : ∀ (j : MulticospanShape.{u, u}), HasLimitsOfShape (WalkingMulticospan j) (Type u) :=
    fun _ => inferInstance
  have a3 : ∀ U : Opens X, HasColimitsOfShape (J.Cover U)ᵒᵖ A.C := fun _ => inferInstance
  have a4 : ∀ U : Opens X, HasColimitsOfShape (J.Cover U)ᵒᵖ (Type u) := fun _ => inferInstance
  have a5 : ∀ U : Opens X, PreservesColimitsOfShape (J.Cover U)ᵒᵖ A.F := fun _ => inferInstance
  have a6 : ∀ (U : Opens X) (W : J.Cover U) (Q : (Opens X)ᵒᵖ ⥤ A.C),
      PreservesLimit (W.index Q).multicospan A.F := fun _ _ _ => inferInstance
  have a7 : ∀ U : Opens X, PreservesColimitsOfShape (J.Cover U)ᵒᵖ (forget A.C) :=
    fun _ => inferInstance
  have a8 : PreservesLimitsOfSize.{u, u} (forget A.C) := inferInstance
  have hsf : HasSheafify J A.C := inferInstance
  have hsc : J.HasSheafCompose A.F := inferInstance
  have hps : J.PreservesSheafification A.F := GrothendieckTopology.instPreservesSheafification J A.F
  refine ⟨(presheafToSheaf J A.C).obj P, toSheafify J P,
    ⟨sheafifyComposeIso J A.F P, sheafComposeIso_hom_fac J A.F P⟩, fun G ψ => ?_⟩
  -- Clause (2) is the bijectivity of the sheafification adjunction's `homEquiv`, whose
  -- forward direction is composition with `η = toSheafify J P`.
  exact ((sheafificationAdjunction J A.C).homEquiv P G).bijective.existsUnique ψ

end AlgebraicStructureType
