module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentChaoticSite
public import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-coherent objects of the derived category of a sheaf of differential graded algebras

Let `C` be a category, viewed as a site with the chaotic topology — the bottom Grothendieck
topology, in which every presheaf is a sheaf — let `O` be a sheaf of rings on it and let
`(A, d)` be a sheaf of differential graded `O`-algebras. Because the topology is chaotic,
evaluation at an object of `C` is exact, so for an object `U` of `C` the derived sections
`RΓ(U, M)` of an object of `D(A, d)` are computed by taking the sections over `U` of any right
differential graded `A`-module representing it: no replacement is needed. Those sections are a
differential graded module over the section algebra `A(U)`, restriction along a morphism
`a : V ⟶ U` of `Cᵒᵖ` is a homomorphism `M(V) ⟶ M(U)` of differential graded `A(V)`-modules, and
its adjoint transpose under the adjunction of Tag 0BYX is the canonical map

`RΓ(V, M) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, M)`

of `D(A(U), d)`. This file cuts out the full subcategory `QC(A, d)` of `D(A, d)` on which all of
these maps are isomorphisms.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.Chaotic.QC`: **the full subcategory `QC(A, d)` of
  `D(A, d)`**, as the property of an object of the derived category that every right
  differential graded module computing it satisfies the quasi-coherence condition.
* `SheafOfModules.DifferentialGradedModule.Chaotic.QCFullSubcategory` and
  `SheafOfModules.DifferentialGradedModule.Chaotic.QCι`: that full subcategory as a
  category, and its inclusion into `D(A, d)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.Chaotic.exists_module_eq`: every object of `D(A, d)` is
  computed by a right differential graded module, so the condition defining `QC(A, d)` is a
  condition on a non-empty family.
* `SheafOfModules.DifferentialGradedModule.Chaotic.derivedSectionsIsoOfEq`: **the derived
  sections `RΓ(U, X)` are the sections `M(U)` of any right differential graded module `M`
  computing `X`**, so the condition below is a condition on the object of `D(A, d)`.
* `SheafOfModules.DifferentialGradedModule.Chaotic.qc_of_module`: a right differential graded
  module satisfying the quasi-coherence condition and computing an object all of whose
  computing modules satisfy it.

## Implementation notes

Nothing in this file, and nothing in the three files it rests on, is a hypothesis standing for
an unproved result: the section algebras `A(U)`, the section modules `M(U)`, restriction of
sections, derived extension of scalars along the restriction homomorphisms and its adjunction
to derived restriction of scalars are all constructed, the last two by the ambient library's
Tag 0BYX. The derived category `D(A, d)` is
`SheafOfModules.DifferentialGradedModule.derivedCategory`, the localization of the homotopy
category at the quasi-isomorphisms of Tag 0FT5.

The derived sections `RΓ(U, X)` of an object `X` of `D(A, d)` are read off a right differential
graded module computing `X`, which is what the chaotic topology buys and what the source's proof
of Lemma 24.33.2 uses; the condition is therefore quantified over all such modules. The
quantification is not vacuous: `exists_toDerivedCategory_obj_eq` produces one, with an equality
rather than an isomorphism, and
`SheafOfModules.DifferentialGradedModule.Chaotic.derivedSectionsIsoOfEq` identifies the sections
of such a module with the value at `X` of the derived sections functor.

`SheafOfModules.DifferentialGradedModule.IsQC` and
`SheafOfModules.DifferentialGradedModule.QC` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedQuasiCoherent.lean` cut out the
same subcategory from a *carried* derived category: there the derived sections functor, the
derived base changes and their adjunctions are fields of
`SheafOfModules.DifferentialGradedModule.SectionData`, which is what the functoriality results
of Tags 0GZC and 0GZE are stated over. Those are the versions with a parameter; the ones here
are built from `A` itself, which is why Tag 0GZ9 is registered on `QC` below. The two are
matched as soon as a `SheafOfModules.DifferentialGradedModule.GoodModuleData` for the chaotic
site is available, which needs the existence of good resolutions of Tag 0FSH.

The chaotic topology is written `⊥` rather than carried as a hypothesis `J = ⊥`, so that the
sheafification and local-bijectivity instances which the abelian structure on sheaves of modules
needs are found by instance search rather than transported.

## References

* [Stacks Project, Definition 24.33.1 (Tag 0GZ9)](https://stacks.math.columbia.edu/tag/0GZ9)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

namespace Chaotic

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}}
  (A : DifferentialGradedAlgebra.{t, a} R)

/-- The object of `D(A, d)` computed by a right differential graded `A`-module: its class in the
localization of the homotopy category at the quasi-isomorphisms. -/
abbrev derivedClass (M : DifferentialGradedModule.{t, a, a} A) : derivedCategory.{t, a, a} A :=
  (toDerivedCategory.{t, a, a} A).obj ((HomotopyCategory.quotient A).obj M)

/-- Every object of `D(A, d)` is computed by a right differential graded `A`-module. -/
theorem exists_module_eq (X : derivedCategory.{t, a, a} A) :
    ∃ M : DifferentialGradedModule.{t, a, a} A, derivedClass A M = X :=
  exists_toDerivedCategory_obj_eq A X

/-- **The full subcategory `QC(A, d)` of `D(A, d)`**: an object `X` lies in it when, for every
right differential graded `A`-module `M` computing `X` and every morphism `U → V` of the chaotic
site `C`, the canonical map

`RΓ(V, X) ⊗^𝐋_{A(V)} A(U) ⟶ RΓ(U, X)`

is an isomorphism of `D(A(U), d)`. The derived sections `RΓ(U, X)` are the sections `M(U)` over
`U` of such a module, which is what they are on a chaotic site, and the canonical map is the
adjoint transpose of restriction of sections under the adjunction between derived extension of
scalars along `A(V) ⟶ A(U)` and derived restriction of scalars. -/
@[stacks 0GZ9 "the full subcategory QC(A, d) of D(A, d)"]
def QC : ObjectProperty (derivedCategory.{t, a, a} A) :=
  fun X ↦ ∀ M : DifferentialGradedModule.{t, a, a} A, derivedClass A M = X →
    ∀ ⦃U V : Cᵒᵖ⦄ (a : V ⟶ U), IsIso (sectionComparison M a)

/-- An object `X` of `D(A, d)` lies in `QC(A, d)` if and only if every right differential graded
`A`-module computing `X` satisfies the quasi-coherence condition. -/
theorem qc_iff {X : derivedCategory.{t, a, a} A} :
    QC A X ↔ ∀ M : DifferentialGradedModule.{t, a, a} A, derivedClass A M = X → IsQCModule M :=
  Iff.rfl

/-- A right differential graded module computing an object of `QC(A, d)` satisfies the
quasi-coherence condition. -/
theorem isQCModule_of_qc {X : derivedCategory.{t, a, a} A} (hX : QC A X)
    (M : DifferentialGradedModule.{t, a, a} A) (hM : derivedClass A M = X) : IsQCModule M :=
  hX M hM

/-- An object of `D(A, d)` computed by a single module all of whose fellow representatives
satisfy the quasi-coherence condition lies in `QC(A, d)`. -/
theorem qc_of_module {X : derivedCategory.{t, a, a} A}
    (h : ∀ M : DifferentialGradedModule.{t, a, a} A, derivedClass A M = X → IsQCModule M) :
    QC A X :=
  h

/-- **The derived sections of `X` are the sections of any right differential graded module
computing `X`.** For a right differential graded `A`-module `M` computing `X` and an object `U`
of `Cᵒᵖ`, the value at `X` of the derived sections functor `RΓ(U, -) : D(A, d) ⥤ D(A(U), d)` is
isomorphic to the class of the sections `M(U)` in `D(A(U), d)`. -/
def derivedSectionsIsoOfEq {X : derivedCategory.{t, a, a} A}
    (M : DifferentialGradedModule.{t, a, a} A) (hM : derivedClass A M = X) (U : Cᵒᵖ) :
    (derivedSections A U).obj X ≅ sectionClass M U :=
  hM ▸ derivedSectionsIsoSectionClass A U M

/-- The full subcategory `QC(A, d)` of `D(A, d)`, as a category. -/
abbrev QCFullSubcategory : Type _ := ObjectProperty.FullSubcategory (QC A)

/-- The inclusion of `QC(A, d)` into `D(A, d)`. -/
abbrev QCι : QCFullSubcategory A ⥤ derivedCategory.{t, a, a} A :=
  ObjectProperty.ι _

end Chaotic

end DifferentialGradedModule

end SheafOfModules

end
