module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeOfSimplicialModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModulesAbelian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The complex `s(F_•)` of a simplicial presheaf of modules on a site

Let `(C, J)` be a small site. A presheaf on `SimplexCategory × C` is the same thing as a
simplicial object in presheaves on `C`, and the prose preceding [Stacks, Tag 09D2] attaches to a
simplicial module `F` the cochain complex of abelian sheaves

`s(F_•)`,

obtained by passing to the underlying simplicial abelian presheaf of `F`, taking the Moore
(alternating face map) complex of that simplicial object, and sheafifying in each degree. This
module writes down that complex and the two elementary facts about it that the proof of Tag 09D2
uses: that it is natural in the structure ring, and that whether a map of simplicial modules
becomes a quasi-isomorphism may be tested before sheafifying, object by object in `C`.

## The three stages

The identification of presheaves on `Δ × C` with simplicial presheaves on `C` is currying along
`CategoryTheory.prodOpEquiv`, and is recorded here as an equivalence of categories
(`Stacks.SimplicialModules.simplicialCurryEquiv`) together with the functor it is used through
(`Stacks.SimplicialModules.simplicialCurry`). The only computation needed about it is that
evaluating the resulting simplicial presheaf at an object `V` of `C` restricts the original
presheaf to the slice `Δ × {V}`
(`Stacks.SimplicialModules.simplicialCurry_obj_comp_evaluation`); this is what lets a statement
about the simplicial object be checked one object of `C` at a time.

On top of it sit the Moore complex of presheaves
(`Stacks.SimplicialModules.moorePresheafCochain`) and its degreewise sheafification
(`Stacks.SimplicialModules.mooreSheafCochain`). Sheafification is exact — it preserves finite
limits because it is left exact by `CategoryTheory.HasSheafify.isLeftExact`, and all colimits
because it is a left adjoint — so it preserves homology, and the passage from the presheaf complex
to the sheaf complex creates no quasi-isomorphism questions of its own
(`Stacks.SimplicialModules.quasiIso_mooreSheafCochain_of_quasiIso_moorePresheafCochain`).

## Main definitions

* `Stacks.SimplicialModules.simplicialCurryEquiv` and
  `Stacks.SimplicialModules.simplicialCurry`: a presheaf on `Δ × C` read as a simplicial presheaf
  on `C`.
* `Stacks.SimplicialModules.moorePresheafCochain`: the Moore complex of the underlying simplicial
  abelian presheaf of a presheaf of modules on `Δ × C`.
* `Stacks.SimplicialModules.mooreSheafCochain`: **the complex `s(F_•)`**, the previous one
  sheafified in each degree.
* `Stacks.SimplicialModules.moorePresheafBaseChange` and
  `Stacks.SimplicialModules.mooreSheafBaseChange`: the base-change unit along a homomorphism of
  structure rings, on the two complexes.

## Main results

* `Stacks.SimplicialModules.simplicialCurry_obj_comp_evaluation`: evaluating the curried
  simplicial presheaf at `V` is restriction to the slice `Δ × {V}`.
* `Stacks.SimplicialModules.quasiIso_mapHomologicalComplex_presheafToSheaf`: degreewise
  sheafification takes a quasi-isomorphism of complexes of abelian presheaves to one of complexes
  of abelian sheaves.
* `Stacks.SimplicialModules.quasiIso_mooreSheafCochain_of_quasiIso_moorePresheafCochain`: hence
  the same for the two Moore complexes of a map of simplicial modules.
* `Stacks.SimplicialModules.quasiIso_moorePresheafCochain_map_of_forall`: the presheaf-level
  question is a question about each object of `C` separately.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

universe u

namespace Stacks.SimplicialModules

open Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-! ### Presheaves on `Δ × C` as simplicial presheaves on `C` -/

/-- **A presheaf on `Δ × C` is a simplicial presheaf on `C`.** The equivalence is the composite of
`CategoryTheory.prodOpEquiv`, which splits the opposite of the product site into the product of
the opposites, with currying `CategoryTheory.Functor.currying`. This is the identification under
which the simplicial modules of [Stacks, Tag 09D1] — modules over a ring on `Δ × C` — are
simplicial objects in modules on `C`. -/
@[sga "4 Vbis 1.2.7" "more general"]
def simplicialCurryEquiv (A : Type*) [Category* A] :
    ((SimplexCategory × C)ᵒᵖ ⥤ A) ≌ SimplicialObject (Cᵒᵖ ⥤ A) :=
  (prodOpEquiv SimplexCategory (D := C)).congrLeft.trans Functor.currying.symm

/-- **The underlying simplicial presheaf on `C` of a presheaf on `Δ × C`**, the functor of
`Stacks.SimplicialModules.simplicialCurryEquiv`: precomposition with the inverse of
`CategoryTheory.prodOpEquiv` followed by `CategoryTheory.Functor.curry`. -/
@[sga "4 Vbis 1.2.7"]
def simplicialCurry (A : Type*) [Category* A] :
    ((SimplexCategory × C)ᵒᵖ ⥤ A) ⥤ SimplicialObject (Cᵒᵖ ⥤ A) :=
  (simplicialCurryEquiv (C := C) A).functor

/-- `Stacks.SimplicialModules.simplicialCurry` is an equivalence of categories. -/
instance isEquivalence_simplicialCurry (A : Type*) [Category* A] :
    (simplicialCurry (C := C) A).IsEquivalence :=
  inferInstanceAs (simplicialCurryEquiv (C := C) A).functor.IsEquivalence

/-- `Stacks.SimplicialModules.simplicialCurry` is additive: both stages act componentwise and
addition of natural transformations is componentwise. Mathlib has no instance making an
equivalence or `CategoryTheory.Functor.curry` additive, so this is stated here, beside
`simplicialCurry` itself, for the several modules that need it. -/
instance additive_simplicialCurry (A : Type*) [Category* A] [Preadditive A] :
    (simplicialCurry (C := C) A).Additive where
  map_add := by intros; rfl

/-- **Evaluating the curried simplicial presheaf at an object `V` of `C` is restriction to the
slice `Δ × {V}`.** This is the lemma that lets a statement about the simplicial presheaf
associated with a presheaf on `Δ × C` be verified one object of `C` at a time. -/
lemma simplicialCurry_obj_comp_evaluation (A : Type*) [Category* A]
    (F : (SimplexCategory × C)ᵒᵖ ⥤ A) (V : Cᵒᵖ) :
    (simplicialCurry A).obj F ⋙ (evaluation Cᵒᵖ A).obj V =
      (Functor.prodSectionFst V.unop).op ⋙ F :=
  rfl

/-! ### The Moore complex of a simplicial abelian presheaf and its sheafification -/

/-- **The Moore complex of an abelian presheaf on `Δ × C`**, a cochain complex of abelian
presheaves on `C` with simplicial degree `n` in cohomological degree `-n`. The structure sheaf of
rings plays no part in it, so this is the form in which the hypothesis of [Stacks, Tag 09D2] —
that `L π_! A_• ⟶ L π_! B_•` be invertible — is read. -/
abbrev mooreAbPresheafCochain :
    ((SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
  simplicialCurry AddCommGrpCat.{u} ⋙ alternatingFaceMapCochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})

/-- **The complex `s(F_•)` of an abelian presheaf on `Δ × C`**: its Moore complex, sheafified in
each degree. The hypothesis of [Stacks, Tag 09D2] is that this invert the homomorphism of
structure rings; that is the sheaf-level, not the fibrewise, condition. -/
abbrev mooreAbSheafCochain :
    ((SimplexCategory × C)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
      CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ :=
  mooreAbPresheafCochain ⋙
    (presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)

/-! ### The Moore complex of a simplicial module and its sheafification -/

section

variable (O : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u})

/-- **The Moore complex of the underlying simplicial abelian presheaf of a presheaf of modules on
`Δ × C`**, a cochain complex of presheaves of abelian groups on `C` with simplicial degree `n` in
cohomological degree `-n`. This is `s(F_•)` of the prose preceding [Stacks, Tag 09D2], before
sheafification. -/
abbrev moorePresheafCochain :
    PresheafOfModules.{u} (ringPresheaf O) ⥤ CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
  PresheafOfModules.toPresheaf (ringPresheaf O) ⋙ simplicialCurry AddCommGrpCat.{u} ⋙
    alternatingFaceMapCochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u})

/-- **The complex `s(F_•)` of the prose preceding [Stacks, Tag 09D2]**: the Moore complex of the
underlying simplicial abelian presheaf of a simplicial module, sheafified in each degree. -/
abbrev mooreSheafCochain :
    PresheafOfModules.{u} (ringPresheaf O) ⥤ CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ :=
  moorePresheafCochain O ⋙
    (presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The Moore complex of a simplicial module is that of its underlying abelian presheaf. -/
lemma moorePresheafCochain_eq :
    moorePresheafCochain O =
      PresheafOfModules.toPresheaf (ringPresheaf O) ⋙ mooreAbPresheafCochain (C := C) :=
  rfl

/-- The complex `s(F_•)` of a simplicial module is that of its underlying abelian presheaf. -/
lemma mooreSheafCochain_eq :
    mooreSheafCochain J O =
      PresheafOfModules.toPresheaf (ringPresheaf O) ⋙ mooreAbSheafCochain J :=
  rfl

/-- **Degreewise sheafification takes quasi-isomorphisms to quasi-isomorphisms.** Sheafification
preserves finite limits (`CategoryTheory.HasSheafify.isLeftExact`) and all colimits, being a left
adjoint, hence preserves homology; so this is
`HomologicalComplex.quasiIso_map_of_preservesHomology`. -/
theorem quasiIso_mapHomologicalComplex_presheafToSheaf
    {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso (((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  have := hf
  have : (presheafToSheaf J AddCommGrpCat.{u}).PreservesHomology := inferInstance
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f _

/-- **A morphism of simplicial modules which is a quasi-isomorphism on presheaf-level Moore
complexes is one on the complexes `s(F_•)`.** Sheafification is exact, so the question for
`Stacks.SimplicialModules.mooreSheafCochain` is the question for
`Stacks.SimplicialModules.moorePresheafCochain`. -/
theorem quasiIso_mooreSheafCochain_of_quasiIso_moorePresheafCochain
    {M N : PresheafOfModules.{u} (ringPresheaf O)} (f : M ⟶ N)
    (hf : QuasiIso ((moorePresheafCochain O).map f)) :
    QuasiIso ((mooreSheafCochain J O).map f) :=
  quasiIso_mapHomologicalComplex_presheafToSheaf J _ hf

/-- **The presheaf-level question is a question about each object of `C` separately.** Evaluation
at an object of a functor category is exact, so it preserves homology, and a natural
transformation is invertible as soon as all of its components are; this is Mathlib's
`HomologicalComplex.quasiIso_iff_evaluation` for the complexes at hand. -/
theorem quasiIso_moorePresheafCochain_map_of_forall
    {M N : PresheafOfModules.{u} (ringPresheaf O)} (f : M ⟶ N)
    (hf : ∀ V : C, QuasiIso ((((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op V)
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map ((moorePresheafCochain O).map f))) :
    QuasiIso ((moorePresheafCochain O).map f) :=
  (HomologicalComplex.quasiIso_iff_evaluation _).2 fun V => hf V.unop

end

/-! ### Base change along a homomorphism of structure rings -/

section BaseChange

variable {O O' : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u}} (θ : O ⟶ O')

/-- **The base-change unit on presheaf-level Moore complexes**, `s(F_•) ⟶ s(F_• ⊗_O O')` before
sheafification: the unit of `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`
whiskered onto underlying presheaves of abelian groups and then onto Moore complexes. -/
def moorePresheafBaseChange :
    moorePresheafCochain O ⟶ changeOfRings θ ⋙ moorePresheafCochain O' :=
  Functor.whiskerRight
    (Functor.whiskerRight (changeOfRingsAdjunction θ).unit
      (PresheafOfModules.toPresheaf (ringPresheaf O)))
    (simplicialCurry AddCommGrpCat.{u} ⋙
      alternatingFaceMapCochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}))

/-- **The base-change unit on the complexes `s(F_•)`**, the previous morphism sheafified in each
degree, written as the same whiskering of the unit of
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`. -/
def mooreSheafBaseChange :
    mooreSheafCochain J O ⟶ changeOfRings θ ⋙ mooreSheafCochain J O' :=
  Functor.whiskerRight
    (Functor.whiskerRight (changeOfRingsAdjunction θ).unit
      (PresheafOfModules.toPresheaf (ringPresheaf O)))
    (simplicialCurry AddCommGrpCat.{u} ⋙
      alternatingFaceMapCochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⋙
      (presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ))

/-- The sheaf-level base-change unit is the presheaf-level one sheafified in each degree. -/
lemma mooreSheafBaseChange_eq_whiskerRight :
    mooreSheafBaseChange J θ = Functor.whiskerRight (moorePresheafBaseChange θ)
      ((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)) :=
  rfl

end BaseChange

end Stacks.SimplicialModules

end
