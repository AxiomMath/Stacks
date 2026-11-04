module

public import StacksFrontier.CategoryTheory.Sites.AbelianSheafSectionwiseAcyclic
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.CohomologyPresheafResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.VanishingCohomology

/-!
# Acyclicity detected by the free abelian sheaves on the representables

`CochainComplex.acyclic_of_acyclic_coyonedaComplex` detects acyclicity of a complex in an
abelian category by the Hom complexes out of *every* object. For a complex of abelian sheaves
far fewer objects suffice: the free abelian sheaves `ℤ_V^♯` on the representable presheaves,
one for each object `V` of the site. Indeed `Hom(ℤ_V^♯, ℱ)` is `ℱ(V)`, so the Hom complex out of
`ℤ_V^♯` is the complex of sections over `V`, and a complex of abelian sheaves with acyclic
sections is acyclic by `CategoryTheory.Sheaf.acyclic_of_sectionwise`.

This is what cuts a "for every abelian sheaf `𝒢`" hypothesis down to a "for every object `V` of
the site" one.

## Main definitions

* `Stacks.Cohomology.CohomologyPresheaf.coyonedaFreeYonedaSheafIso`: the functor
  `Hom(ℤ_V^♯, -)` on abelian sheaves is the sections functor over `V`.

## Main results

* `CategoryTheory.Sheaf.acyclic_of_acyclic_coyonedaComplex_freeYoneda`: **a complex of abelian
  sheaves is acyclic as soon as the Hom complex out of `ℤ_V^♯` is acyclic for every object `V`
  of the site.**
* `Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf_eq_freeAbelianSheaf_yoneda`: the two
  spellings of `ℤ_V^♯` agree.

## Implementation notes

`ℤ_V^♯` is spelled `Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf`, the sheafification of
the free abelian presheaf on `yoneda.obj V`, because that spelling comes with the additive
identification `Hom(ℤ_V^♯, ℱ) ≅ ℱ(V)` and its naturality in `ℱ`
(`Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheafHomAddEquiv` and
`.freeYonedaSheafHomAddEquiv_naturality`), which is exactly what assembling an isomorphism of
complexes needs. It agrees with `CategoryTheory.Presheaf.freeAbelianSheaf` applied to
`yoneda.obj V` — the spelling in which Stacks 01GE is stated — on the nose, and
`freeYonedaSheaf_eq_freeAbelianSheaf_yoneda` records that.

Only one implication is available and it is the useful one: the converse fails, sheaf cohomology
not being sectionwise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.CohomologyPresheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]

/-- **Maps out of the free abelian sheaf on `h_V` are the sections over `V`**, as functors of the
abelian sheaf: `Hom(ℤ_V^♯, -)` is the sections functor over `V`. -/
def coyonedaFreeYonedaSheafIso (V : C) :
    preadditiveCoyoneda.obj (op (freeYonedaSheaf J V)) ≅
      sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op V) :=
  NatIso.ofComponents (fun F => (freeYonedaSheafHomAddEquiv V F).toAddCommGrpIso)
    (fun {F G} p => by ext φ; exact freeYonedaSheafHomAddEquiv_naturality V p φ)

/-- The free abelian sheaf on `h_V` is the one `CategoryTheory.Presheaf.freeAbelianSheaf`
produces from `yoneda.obj V`, the spelling in which Stacks 01GE is stated. -/
lemma freeYonedaSheaf_eq_freeAbelianSheaf_yoneda (V : C) :
    freeYonedaSheaf J V = (Presheaf.freeAbelianSheaf J).obj (yoneda.obj V) :=
  rfl

end Stacks.Cohomology.CohomologyPresheaf

namespace CategoryTheory.Sheaf

open Stacks.Cohomology.CohomologyPresheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}]

/-- **A complex of abelian sheaves is acyclic as soon as the Hom complex out of the free abelian
sheaf on each representable is acyclic.** The Hom complex out of `ℤ_V^♯` is the complex of
sections over `V`, and a complex of abelian sheaves with acyclic sections is acyclic.

This is the form of `CochainComplex.acyclic_of_acyclic_coyonedaComplex` which needs only the
objects of the site, not every abelian sheaf. -/
theorem acyclic_of_acyclic_coyonedaComplex_freeYoneda
    (X : CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ)
    (h : ∀ V : C, (CochainComplex.coyonedaComplex (freeYonedaSheaf J V) X).Acyclic) :
    X.Acyclic :=
  acyclic_of_sectionwise J X fun U n =>
    (h U.unop n).of_iso ((NatIso.mapHomologicalComplex
      (coyonedaFreeYonedaSheafIso J U.unop) (ComplexShape.up ℤ)).app X)

end CategoryTheory.Sheaf

end
