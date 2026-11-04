module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Inclusion
public import StacksFrontier.AlgebraicGeometry.DerivedTildeCounit

/-!
# The essential image of `D(QCoh(𝒪_X)) ⥤ D(𝒪_X)` on an affine scheme

Stacks 06Z0 asserts that for `X = Spec A` the functor `(06VT)`, which is
`Stacks.DerivedQCoh.derivedQCohι`, is an equivalence of `D(QCoh(𝒪_X))` onto
`D_QCoh(𝒪_X)`. `StacksFrontier/AlgebraicGeometry/DerivedQCoh/Inclusion.lean` packages the three
clauses of that assertion — fullness, faithfulness, and "the essential image is exactly the
objects satisfying `Stacks.DerivedQCoh.IsDQCoh`" — as
`Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`, proves the easy half of the third
(`Stacks.DerivedQCoh.isDQCoh_of_essImage_derivedQCohι`) and takes the other half as a hypothesis.

This file discharges that hypothesis. The content is the counit clause of Stacks 06Z0,
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso`: the counit of the derived
sheafification–sections adjunction `derivedTilde A ⋙ ι ⊣ RΓ(Spec A, -)` is invertible at every
object of `D_QCoh(𝒪_{Spec A})`. An object `E` with quasi-coherent cohomology is therefore
`(derivedTilde A ⋙ ι)(RΓ(Spec A, E))`, and derived sheafification followed by the inclusion is
`derivedQCohι` precomposed with the `~` edge
`Stacks.DerivedQCoh.derivedTildeEquiv`, because degreewise sheafification `M ↦ M̃` *is* the
equivalence `AlgebraicGeometry.tildeEquiv` onto the quasi-coherent modules followed by their
inclusion. So `E` is in the essential image of `derivedQCohι`.

Carrying that argument out means crossing between the two spellings
`AlgebraicGeometry.SheafOfModules X.ringCatSheaf` and `AlgebraicGeometry.Scheme.Modules X`, and
the first section of this file supplies the crossing.

## Main results

* `Stacks.DerivedQCoh.essImage_derivedQCohι_of_isDQCoh` — **Stacks 06Z0**, the
  essential-surjectivity clause of `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`: every object of
  `D(𝒪_{Spec A})` with quasi-coherent cohomology lies in the essential image of
  `Stacks.DerivedQCoh.derivedQCohι`. This is the clause that
  `Stacks.DerivedQCoh.exists_iso_derivedTilde_of_isDQCoh` assumes.
* `Stacks.DerivedQCoh.essImage_derivedQCohι_iff_isDQCoh` — **Stacks 06Z0**, the whole
  essential-image clause of `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`, unconditionally.
* `Stacks.DerivedQCoh.exists_iso_derivedTildeEquiv_obj_of_isDQCoh` and
  `Stacks.DerivedQCoh.isDQCoh_iff_exists_iso_derivedTildeEquiv_obj` — the hypothesis-free forms
  of `Stacks.DerivedQCoh.exists_iso_derivedTilde_of_isDQCoh` and
  `Stacks.DerivedQCoh.isDQCoh_iff_exists_iso_derivedTilde`: an object of `D(𝒪_{Spec A})` has
  quasi-coherent cohomology exactly when it is the complex of quasi-coherent sheaves attached to
  an object of `D(A)`. This is the identification the proof of Stacks 09VF uses on an affine
  open.
* `Stacks.DerivedQCoh.hasDerivedCategorySchemeModules`,
  `Stacks.DerivedQCoh.hasDerivedCategoryRingCatSheaf`,
  `Stacks.DerivedQCoh.derivedCategoryB_isQuasicoherent_eq_isDQCoh` and their companions — the
  crossing between the two spellings of the category of `𝒪_X`-modules.

## Implementation notes

**The two spellings.** `AlgebraicGeometry.Scheme.Modules X` is a plain `def` for
`AlgebraicGeometry.SheafOfModules X.ringCatSheaf` with *separately declared* `Category`,
`Abelian`, `HasLimits`, `HasColimits` and `IsGrothendieckAbelian` instances. The two are the same
type and those instances are definitionally equal, but a `def` is semireducible and instance
search unfolds only at reducible transparency, so an instance found for one spelling is not found
for the other. The symptom is a missing `(tilde.functor A).Additive`, or a missing
`Mono`.

A lemma cannot repair this, since instance search cannot consult a lemma. What does is to move
the instance across as a *term*, where the ascription is checked at default transparency:
`hasDerivedCategorySchemeModules` and `hasDerivedCategoryRingCatSheaf` are that move for
`HasDerivedCategory`, in the idiom of `Stacks.DerivedQCoh.hasDerivedCategoryOxMod` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/StructureSheafSpelling.lean`, which does the same for
the third spelling `Stacks.StrictlyPerfect.OXMod`. The remaining lemmas record that nothing is
lost in the crossing: the derived categories are the same type, the cohomology functors are the
same functor, and `Stacks.DerivedQCoh.IsDQCoh` and
`DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent _)` are the same object
property — each by `rfl`. `modulesEquivSheafOfModules` is the identity equivalence; it is the
reading of the crossing as an equivalence of categories, and it is weaker than the `rfl` lemmas
beside it, which is why those are what the proofs below use.

**The model of the derived category.** `CategoryTheory.HasDerivedCategory` carries the localized
category as data, so the statements here are tied to the model their input is proved at. The
counit clause of Stacks 06Z0 is stated at `CategoryTheory.HasDerivedCategory.standard` for the
`𝒪_{Spec A}`-modules — forced there by the upper half of Stacks 08D4, whose input Stacks 08D3 is
available at that model alone — so the results below are too, and they write that instance into
their statements through a `let`, exactly as
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso` does. The derived category
of quasi-coherent modules is left at a free `[HasDerivedCategory.{w'} _]` binder, and so is
`D(A)`, whose morphism universe is forced to agree with the `𝒪_{Spec A}` side by the binders of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/Inclusion.lean`. Re-binding the whole 06Z0 cluster at
a free model, which is what would let these results compose with the locally small model that
`Stacks.DerivedQCoh.derivedTildeEquivCompComparisonIso` is baked at, is a library-wide change
and is not made here.

**`mapDerivedCategoryObjCompIso`.** Only the object-level isomorphism
`D(G)(D(F) K) ≅ D(F ⋙ G)(K)` is needed, not the natural one, so it is derived inline from the
localisation property: both sides agree on `Q(P)` for a complex `P`, and every object of the
derived category is such a `Q(P)` up to isomorphism. The repository holds the natural version in
`private` copies in
`StacksFrontier/Homology/DerivedComplete/CompleteRestrictScalarsEquivalence.lean` and
`StacksFrontier/Homology/PseudoCoherent/Relative/Tower.lean`, and the natural iso
`Stacks.DerivedQCoh.derivedTildeEquivCompComparisonIso` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/TildeFactorization.lean` is exactly this
comparison, but baked at the locally small model and so unusable here. Lifting one general public
copy out and deleting the rest is the right repository-tier fix.

## References

* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [The Stacks Project, Section 36.3 (06VT)](https://stacks.math.columbia.edu/tag/06VT)
* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry

universe w w' w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.DerivedQCoh

/-! ### The two spellings of the category of modules on a scheme -/

section Spelling

variable (X : Scheme.{u})

/-- `AlgebraicGeometry.Scheme.Modules X` and `AlgebraicGeometry.SheafOfModules X.ringCatSheaf`
are the same type: the former is a `def` for the latter.

This is the barrier that the statements of Stacks 06Z0 have to cross, since Mathlib's `tilde` API
is stated for the first spelling and `Stacks.DerivedQCoh.derivedQCohι` for the second. -/
theorem modules_eq_sheafOfModules : X.Modules = SheafOfModules.{u} X.ringCatSheaf := rfl

/-- The crossing of `Stacks.DerivedQCoh.modules_eq_sheafOfModules` read as an equivalence of
categories: it is the identity functor in both directions, the two categories of `𝒪_X`-modules
being the same category with definitionally equal `Category` and `Abelian` instances.

This is the shape in which a statement about `D(𝒪_X)` for one spelling becomes one for the other
when an equivalence is what a consumer wants; the `rfl` lemmas beside it are stronger and are
what the proofs for Stacks 06Z0 below use. -/
def modulesEquivSheafOfModules : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf :=
  CategoryTheory.Equivalence.refl

/-- A chosen derived category for `AlgebraicGeometry.SheafOfModules X.ringCatSheaf` is one for
`AlgebraicGeometry.Scheme.Modules X`. Instance search does not make this step, because
`AlgebraicGeometry.Scheme.Modules` is a semireducible `def`; the term-level ascription does,
because it is checked at default transparency. Used to carry the inputs of Stacks 06Z0 that are
stated for `X.Modules` over to the spelling of `Stacks.DerivedQCoh.derivedQCohι`. -/
@[instance_reducible]
def hasDerivedCategorySchemeModules
    (h : HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)) :
    HasDerivedCategory.{w} X.Modules := h

/-- A chosen derived category for `AlgebraicGeometry.Scheme.Modules X` is one for
`AlgebraicGeometry.SheafOfModules X.ringCatSheaf`; the converse crossing to
`Stacks.DerivedQCoh.hasDerivedCategorySchemeModules`, and the one that makes the standard model
of `D(𝒪_{Spec A})` used by Stacks 06Z0 available at the second spelling. -/
@[instance_reducible]
def hasDerivedCategoryRingCatSheaf (h : HasDerivedCategory.{w} X.Modules) :
    HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf) := h

variable [hX : HasDerivedCategory.{w} X.Modules]

/-- Transported along `Stacks.DerivedQCoh.hasDerivedCategoryRingCatSheaf`, the two derived
categories of `𝒪_X`-modules are the same type, so an object of one is an object of the other
with no transport. This is why the statements of Stacks 06Z0 can be read at either spelling. -/
theorem derivedCategory_modules_eq :
    DerivedCategory X.Modules = @DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) _ _
      (hasDerivedCategoryRingCatSheaf X hX) := rfl

/-- The cohomology functors of the two derived categories of `𝒪_X`-modules agree. This is what
makes the quasi-coherence conditions on the two sides the same condition, and hence what makes
`Stacks.DerivedQCoh.derivedCategoryB_isQuasicoherent_eq_isDQCoh` hold; it serves Stacks 06Z0. -/
theorem homologyFunctor_modules_eq (n : ℤ) :
    DerivedCategory.homologyFunctor X.Modules n =
      @DerivedCategory.homologyFunctor (SheafOfModules.{u} X.ringCatSheaf) _ _
        (hasDerivedCategoryRingCatSheaf X hX) n := rfl

/-- **`D_QCoh(𝒪_X)` is the same subcategory in both spellings.** The object property
`DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf)` on
`D(X.Modules)`, in which the counit clause of Stacks 06Z0 is stated, and
`Stacks.DerivedQCoh.IsDQCoh`, in which `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh` is stated,
are equal. Both say that every cohomology sheaf is quasi-coherent. -/
theorem derivedCategoryB_isQuasicoherent_eq_isDQCoh :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf) =
      @IsDQCoh _ _ _ X.ringCatSheaf _ _ _ _ (hasDerivedCategoryRingCatSheaf X hX) := rfl

end Spelling

/-! ### Composing derived functors of exact functors -/

section Exact

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory.{w₁} C₁] [HasDerivedCategory.{w₂} C₂] [HasDerivedCategory.{w₃} C₃]

/-- For exact functors `F : C₁ ⥤ C₂` and `G : C₂ ⥤ C₃`, the derived functor of `F ⋙ G` agrees
with the composite of the derived functors on each object: `D(G)(D(F) K) ≅ D(F ⋙ G)(K)`.

Both sides are computed from a complex `P` with `Q(P) ≅ K`, which exists because
`CategoryTheory.DerivedCategory.Q` is essentially surjective, and there they agree by
`CategoryTheory.Functor.mapHomologicalComplexCompIso`. Only the object-level statement is needed
below; see the implementation notes of this file for the `private` natural versions the
repository already holds. -/
private def mapDerivedCategoryObjCompIso (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory C₁) :
    G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ≅
      (F ⋙ G).mapDerivedCategory.obj K :=
  let P := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso eK.symm) ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).app P) ≪≫
    ((F ⋙ G).mapDerivedCategoryFactors.app P).symm ≪≫
    (F ⋙ G).mapDerivedCategory.mapIso eK

end Exact

/-! ### The essential image of the functor (06VT) on an affine scheme -/

section Affine

variable (A : CommRingCat.{u})
  [HasDerivedCategory.{w'}
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory]

/-- The standard derived category of `𝒪_{Spec A}`-modules, read at the
`AlgebraicGeometry.SheafOfModules` spelling by
`Stacks.DerivedQCoh.hasDerivedCategoryRingCatSheaf`.

This is the model the counit clause of Stacks 06Z0,
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso`, is stated at, and
therefore the one the results below are stated at; see the implementation notes of this file. -/
@[instance_reducible]
def standardHasDerivedCategorySpecModules :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} (Spec A).ringCatSheaf) :=
  hasDerivedCategoryRingCatSheaf (Spec A) (HasDerivedCategory.standard _)

/-- **Stacks 06Z0: the functor (06VT) hits every object of `D_QCoh(𝒪_X)`.** For `X = Spec A`, an
object of `D(𝒪_X)` all of whose cohomology sheaves are quasi-coherent lies in the essential image
of `Stacks.DerivedQCoh.derivedQCohι`.

This is the essential-surjectivity clause of `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`, and the
hypothesis of `Stacks.DerivedQCoh.exists_iso_derivedTilde_of_isDQCoh`. The proof is the counit
clause of Stacks 06Z0, `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso`:
the counit at `E` exhibits `E` as `(derivedTilde A ⋙ ι)(RΓ(X, E))`, and derived sheafification
followed by the inclusion is `Stacks.DerivedQCoh.derivedQCohι` after the `~` edge
`Stacks.DerivedQCoh.derivedTildeEquiv`, because `M ↦ M̃` is `AlgebraicGeometry.tildeEquiv`
followed by the inclusion of the quasi-coherent modules. Neither fullness nor faithfulness of
`derivedQCohι` is used. -/
theorem essImage_derivedQCohι_of_isDQCoh :
    let _inst : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (Spec A).ringCatSheaf) :=
      standardHasDerivedCategorySpecModules A
    ∀ E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf),
      IsDQCoh (R := (Spec A).ringCatSheaf) E → (derivedQCohι A).essImage E := by
  intro _inst E hE
  let _instSpec : HasDerivedCategory.{u + 1} (Spec A).Modules := HasDerivedCategory.standard _
  have hiso : IsIso ((derivedTildeGlobalSectionsAdjunction A).val.counit.app E) :=
    AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction_counit_isIso A ⟨E, hE⟩
  refine ⟨(derivedTildeEquiv A).functor.obj
    ((derivedGlobalSectionsOver (𝟙 (Spec A))).obj E), ⟨?_⟩⟩
  exact mapDerivedCategoryObjCompIso (tildeEquiv (R := A)).functor
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf))
      ((derivedGlobalSectionsOver (𝟙 (Spec A))).obj E) ≪≫
    ((AlgebraicGeometry.derivedTildeCompι A).app
      ((derivedGlobalSectionsOver (𝟙 (Spec A))).obj E)).symm ≪≫
    @asIso _ _ _ _ _ hiso

/-- **Stacks 06Z0: the essential image of the functor (06VT) is exactly `D_QCoh(𝒪_X)`.** For
`X = Spec A`, an object of `D(𝒪_X)` is isomorphic to one in the image of
`Stacks.DerivedQCoh.derivedQCohι` precisely when all of its cohomology sheaves are quasi-coherent.

This is the essential-image clause of `Stacks.DerivedQCoh.IsEquivalenceOntoDQCoh`, proved
unconditionally: the forward implication is
`Stacks.DerivedQCoh.isDQCoh_of_essImage_derivedQCohι` and the reverse is
`Stacks.DerivedQCoh.essImage_derivedQCohι_of_isDQCoh`. The fullness and faithfulness clauses of
`IsEquivalenceOntoDQCoh` are not touched. -/
theorem essImage_derivedQCohι_iff_isDQCoh :
    let _inst : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (Spec A).ringCatSheaf) :=
      standardHasDerivedCategorySpecModules A
    ∀ E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf),
      (derivedQCohι A).essImage E ↔ IsDQCoh (R := (Spec A).ringCatSheaf) E := by
  intro _inst E
  exact ⟨isDQCoh_of_essImage_derivedQCohι A, essImage_derivedQCohι_of_isDQCoh A E⟩

variable [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]

/-- **Stacks 06Z0: every object of `D_QCoh(𝒪_{Spec A})` comes from `D(A)`.** An object of
`D(𝒪_{Spec A})` all of whose cohomology sheaves are quasi-coherent is isomorphic to the complex
of quasi-coherent sheaves attached to an object `M` of `D(A)` by the `~` edge
`Stacks.DerivedQCoh.derivedTildeEquiv`.

This is `Stacks.DerivedQCoh.exists_iso_derivedTilde_of_isDQCoh` with its hypothesis discharged by
`Stacks.DerivedQCoh.essImage_derivedQCohι_of_isDQCoh`, and it is the identification the proof of
Stacks 09VF uses on an affine open. That `M` may be taken to be `RΓ(Spec A, E)` is a further
clause of Stacks 06Z0 and is not asserted here. -/
theorem exists_iso_derivedTildeEquiv_obj_of_isDQCoh :
    let _inst : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (Spec A).ringCatSheaf) :=
      standardHasDerivedCategorySpecModules A
    ∀ E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf),
      IsDQCoh (R := (Spec A).ringCatSheaf) E →
        ∃ M : DerivedCategory (ModuleCat.{u} A),
          Nonempty ((derivedQCohι A).obj ((derivedTildeEquiv A).functor.obj M) ≅ E) := by
  intro _inst E hE
  exact exists_iso_derivedTilde_of_isDQCoh A (essImage_derivedQCohι_of_isDQCoh A) hE

/-- **Stacks 06Z0: `D_QCoh(𝒪_{Spec A})` consists of the complexes attached to objects of
`D(A)`.** An object of `D(𝒪_{Spec A})` has all its cohomology sheaves quasi-coherent exactly when
it is isomorphic to the complex of quasi-coherent sheaves attached to an object of `D(A)` by the
`~` edge of Stacks 06Z0.

This is `Stacks.DerivedQCoh.isDQCoh_iff_exists_iso_derivedTilde` with its hypothesis discharged
by `Stacks.DerivedQCoh.essImage_derivedQCohι_of_isDQCoh`. -/
theorem isDQCoh_iff_exists_iso_derivedTildeEquiv_obj :
    let _inst : HasDerivedCategory.{u + 1} (SheafOfModules.{u} (Spec A).ringCatSheaf) :=
      standardHasDerivedCategorySpecModules A
    ∀ E : DerivedCategory (SheafOfModules.{u} (Spec A).ringCatSheaf),
      IsDQCoh (R := (Spec A).ringCatSheaf) E ↔
        ∃ M : DerivedCategory (ModuleCat.{u} A),
          Nonempty ((derivedQCohι A).obj ((derivedTildeEquiv A).functor.obj M) ≅ E) := by
  intro _inst E
  exact isDQCoh_iff_exists_iso_derivedTilde A (essImage_derivedQCohι_of_isDQCoh A) E

end Affine

end Stacks.DerivedQCoh

end
