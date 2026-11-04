module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheaf

/-!
# Base change of a polynomial presentation, and the conormal map it induces

Let `u : 𝒜₁ ⟶ 𝒜₂` be a morphism of sheaves of commutative rings on a site, let `ℰ` be a
presheaf of sets and let `α : ℰ ⟶ ℬ` be a family of generators of a sheaf of rings `ℬ` over
`𝒜₂`. The same family presents `ℬ` over `𝒜₁` as well, by restricting coefficients along `u`,
and the two polynomial presentations are compared by a morphism of sheaves of rings

`𝒜₁[ℰ] ⟶ 𝒜₂[ℰ]`

which is the identity on the variables. Writing `ℐ' = Ker(𝒜₁[ℰ] ⟶ ℬ)` and
`ℐ = Ker(𝒜₂[ℰ] ⟶ ℬ)`, it carries `ℐ'` into `ℐ` and hence induces a map of conormal sheaves

`ℐ'/(ℐ')² ⟶ ℐ/ℐ²`.

This is the map used in the proofs of [Stacks 08U8] and [Stacks 08UC], where `𝒜₁ = f⁻¹𝒪_{S'}`
and `𝒜₂ = f⁻¹𝒪_S` for a first order thickening `t : S ⟶ S'`, `ℬ = 𝒪_X`, and `ℰ` is the sheaf of
sets of the source's Step 1.

## Main definitions

* `Stacks.Sites.FreeAlgebra.baseChange`: the morphism `𝒜₁[ℰ] ⟶ 𝒜₂[ℰ]` induced by `u`.
* `Stacks.Sites.Conormal.basePresentation` and
  `Stacks.Sites.Conormal.restrictedPresentation`: the presentation `𝒜₂[ℰ] ⟶ ℬ` of a family of
  generators and the presentation `𝒜₁[ℰ] ⟶ ℬ` of the same family with coefficients restricted
  along `u`.
* `Stacks.Sites.Conormal.restrictedPresentationIdeal` and
  `Stacks.Sites.Conormal.basePresentationIdeal`: the ideals `ℐ'` and `ℐ`, objectwise.
* `Stacks.Sites.Conormal.presentationConormalMap`: the induced map `ℐ'/(ℐ')² ⟶ ℐ/ℐ²` of
  conormal sheaves.

## Main results

* `Stacks.Sites.FreeAlgebra.baseChange_comp_desc`: the base change morphism factors the
  restricted presentation through the base one, `𝒜₁[ℰ] ⟶ 𝒜₂[ℰ] ⟶ ℬ`. This is the
  factorisation that `Stacks.Sites.Conormal.conormalSheafMapOfFac` consumes.
* `Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_baseChange` and
  `Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_baseChange`: the base change morphism
  is `u` on coefficients and the identity on variables. Together with
  `Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext` these two determine it.
* `Stacks.Sites.FreeAlgebra.baseChange_id` and `Stacks.Sites.FreeAlgebra.baseChange_comp`: base
  change is functorial in the coefficient sheaf.
* `Stacks.Sites.Conormal.baseChange_mem_basePresentationIdeal`: the base change morphism carries
  `ℐ'` into `ℐ`.
* `Stacks.Sites.Conormal.isLocallySurjective_basePresentation`: local surjectivity of the
  restricted presentation implies it for the base presentation.
* `Stacks.Sites.Conormal.presentationConormalMap_conormalClass`: the induced map sends the
  conormal class of a local section `g` of `ℐ'` to the conormal class of its image in `ℐ`. This
  formula pins the map down.

## Implementation notes

Nothing here is new mathematics on top of
`StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence`, which already builds the conormal
sheaf of a locally surjective morphism of sheaves of rings and the map
`Stacks.Sites.Conormal.conormalSheafMapOfFac` induced by a factorisation of one presentation
through another. The only missing input was the factorisation itself in the case at hand, where
the two presentations have the *same* variables and differ in their coefficients; that is
`baseChange_comp_desc`, and it is proved from the universal property of the free algebra sheaf
rather than by inspecting polynomials.

Local surjectivity of the two presentations is carried as instance arguments, because both are
needed to *state* the conormal map: each is a hypothesis of the conormal sheaf it appears in.
This is the source's own hypothesis on a family of generators ("`α : ℰ → ℬ` such that
`𝒜[ℰ] → ℬ` is surjective", see [Stacks 08TL]). Only one of the two is an independent
assumption: `isLocallySurjective_basePresentation` derives the base presentation's from the
restricted presentation's, the factorisation going that way. The reverse implication is not
available — it would need `𝒜₁[ℰ] ⟶ 𝒜₂[ℰ]` to be locally surjective, which holds when `u` is,
as it is for a thickening, but is not proved here because no consumer has needed it.

## References

* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public section

open CategoryTheory

universe v u w z

namespace Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]

/-- The morphism of sheaves of rings `𝒜₁[ℰ] ⟶ 𝒜₂[ℰ]` induced by a morphism `u : 𝒜₁ ⟶ 𝒜₂` of
coefficient sheaves: it is `u` on coefficients and the identity on the variables. -/
noncomputable def baseChange {A₁ A₂ : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂)
    (E : Functor Cᵒᵖ (Type w)) :
    freeAlgebraSheaf J A₁ E ⟶ freeAlgebraSheaf J A₂ E :=
  freeAlgebraSheafDesc J A₁ (freeAlgebraSheaf J A₂ E) E
    (u ≫ freeAlgebraSheafCoefficientMap J A₂ E) (freeAlgebraSheafVariable J A₂ E)

/-- Base change is `u` on coefficients. -/
theorem freeAlgebraSheafCoefficientMap_comp_baseChange {A₁ A₂ : Sheaf J CommRingCat.{w}}
    (u : A₁ ⟶ A₂) (E : Functor Cᵒᵖ (Type w)) :
    freeAlgebraSheafCoefficientMap J A₁ E ≫ baseChange J u E =
      u ≫ freeAlgebraSheafCoefficientMap J A₂ E :=
  freeAlgebraSheafCoefficientMap_comp_desc J A₁ (freeAlgebraSheaf J A₂ E) E _ _

/-- Base change is the identity on the variables. -/
theorem freeAlgebraSheafVariable_comp_baseChange {A₁ A₂ : Sheaf J CommRingCat.{w}}
    (u : A₁ ⟶ A₂) (E : Functor Cᵒᵖ (Type w)) :
    freeAlgebraSheafVariable J A₁ E ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{w}).map (baseChange J u E)) (forget CommRingCat.{w}) =
      freeAlgebraSheafVariable J A₂ E :=
  freeAlgebraSheafVariable_comp_desc J A₁ (freeAlgebraSheaf J A₂ E) E _ _

/-- Base change along `u` factors the presentation of a family of generators with coefficients
restricted along `u` through the presentation over `𝒜₂`. -/
theorem baseChange_comp_desc {A₁ A₂ B : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂)
    (E : Functor Cᵒᵖ (Type w)) (a₂ : A₂ ⟶ B) (e : E ⟶ underlyingPresheaf J B) :
    baseChange J u E ≫ freeAlgebraSheafDesc J A₂ B E a₂ e =
      freeAlgebraSheafDesc J A₁ B E (u ≫ a₂) e := by
  refine freeAlgebraSheaf_hom_ext J A₁ B E ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_baseChange, Category.assoc,
      freeAlgebraSheafCoefficientMap_comp_desc, freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_baseChange, freeAlgebraSheafVariable_comp_desc,
      freeAlgebraSheafVariable_comp_desc]

/-- Base change along the identity is the identity. -/
theorem baseChange_id (A : Sheaf J CommRingCat.{w}) (E : Functor Cᵒᵖ (Type w)) :
    baseChange J (𝟙 A) E = 𝟙 (freeAlgebraSheaf J A E) := by
  refine freeAlgebraSheaf_hom_ext J A (freeAlgebraSheaf J A E) E ?_ ?_
  · rw [freeAlgebraSheafCoefficientMap_comp_baseChange, Category.id_comp, Category.comp_id]
  · rw [freeAlgebraSheafVariable_comp_baseChange, CategoryTheory.Functor.map_id,
      Functor.whiskerRight_id']
    exact (Category.comp_id _).symm

/-- Base change is compatible with composition of coefficient morphisms. -/
theorem baseChange_comp {A₁ A₂ A₃ : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂) (v : A₂ ⟶ A₃)
    (E : Functor Cᵒᵖ (Type w)) :
    baseChange J (u ≫ v) E = baseChange J u E ≫ baseChange J v E := by
  have h := baseChange_comp_desc J u E (v ≫ freeAlgebraSheafCoefficientMap J A₃ E)
    (freeAlgebraSheafVariable J A₃ E)
  rw [← Category.assoc] at h
  exact h.symm

end Stacks.Sites.FreeAlgebra

namespace Stacks.Sites.Conormal

open Stacks.Sites.FreeAlgebra

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A₁ A₂ B : Sheaf J CommRingCat.{w}} (u : A₁ ⟶ A₂) (E : Functor Cᵒᵖ (Type w))
  (a₂ : A₂ ⟶ B) (e : E ⟶ underlyingPresheaf J B)

/-- The presentation `𝒜₂[ℰ] ⟶ ℬ` of the family of generators `e` over `𝒜₂`. In the application
to [Stacks 08UC] this is `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`. -/
noncomputable abbrev basePresentation : freeAlgebraSheaf J A₂ E ⟶ B :=
  freeAlgebraSheafDesc J A₂ B E a₂ e

/-- The presentation `𝒜₁[ℰ] ⟶ ℬ` of the *same* family of generators, with coefficients
restricted along `u`. In the application to [Stacks 08UC] this is `f⁻¹𝒪_{S'}[ℰ] ⟶ 𝒪_X`. -/
noncomputable abbrev restrictedPresentation : freeAlgebraSheaf J A₁ E ⟶ B :=
  freeAlgebraSheafDesc J A₁ B E (u ≫ a₂) e

/-- The ideal `ℐ' = Ker(𝒜₁[ℰ] ⟶ ℬ)` of the restricted presentation, objectwise. -/
noncomputable abbrev restrictedPresentationIdeal (X : Cᵒᵖ) :
    Ideal ((freeAlgebraSheaf J A₁ E).obj.obj X) :=
  kernelIdeal (restrictedPresentation J u E a₂ e).hom X

/-- The ideal `ℐ = Ker(𝒜₂[ℰ] ⟶ ℬ)` of the base presentation, objectwise. -/
noncomputable abbrev basePresentationIdeal (X : Cᵒᵖ) :
    Ideal ((freeAlgebraSheaf J A₂ E).obj.obj X) :=
  kernelIdeal (basePresentation J E a₂ e).hom X

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Base change carries `ℐ'` into `ℐ`: a local section of `𝒜₁[ℰ]` killed by the restricted
presentation has image killed by the base presentation, because the latter factors the former. -/
theorem baseChange_mem_basePresentationIdeal (X : Cᵒᵖ)
    (g : restrictedPresentationIdeal J u E a₂ e X) :
    (baseChange J u E).hom.app X g ∈ basePresentationIdeal J E a₂ e X :=
  kernelIdeal_le_comap _ _ _ (hom_of_comp_eq (baseChange_comp_desc J u E a₂ e)) X g.2

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- If the restricted presentation `𝒜₁[ℰ] ⟶ ℬ` is locally surjective then so is the base
presentation `𝒜₂[ℰ] ⟶ ℬ`, since the former factors through the latter. The converse direction
is not available: the factorisation runs the wrong way, and `𝒜₁[ℰ] ⟶ 𝒜₂[ℰ]` need not be
locally surjective unless `u` is. -/
theorem isLocallySurjective_basePresentation
    [Presheaf.IsLocallySurjective J (restrictedPresentation J u E a₂ e).hom] :
    Presheaf.IsLocallySurjective J (basePresentation J E a₂ e).hom :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
    (hom_of_comp_eq (baseChange_comp_desc J u E a₂ e))

variable [Presheaf.IsLocallySurjective J (restrictedPresentation J u E a₂ e).hom]
  [Presheaf.IsLocallySurjective J (basePresentation J E a₂ e).hom]

/-- The map `ℐ'/(ℐ')² ⟶ ℐ/ℐ²` of conormal sheaves induced by base change of the coefficients of
a polynomial presentation. This is the map `ℐ' ⟶ ℐ'/(ℐ')² ⟶ ℐ/ℐ²` of the proof of
[Stacks 08UC]. -/
noncomputable def presentationConormalMap :
    conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A₁ E) B
        (restrictedPresentation J u E a₂ e) ⟶
      conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A₂ E) B
        (basePresentation J E a₂ e) :=
  conormalSheafMapOfFac.{v, u, w, z} J B _ _ _ _ (baseChange J u E)
    (baseChange_comp_desc J u E a₂ e)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The induced map on conormal sheaves sends the conormal class of a local section `g` of `ℐ'`
to the conormal class of its image in `ℐ`. This formula determines the map, by
`Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass` and
`Stacks.Sites.Conormal.sheafifyLiftDesc`. -/
theorem presentationConormalMap_conormalClass (X : Cᵒᵖ)
    (g : restrictedPresentationIdeal J u E a₂ e X) :
    ((presentationConormalMap J u E a₂ e).val.app X)
        (conormalClass.{v, u, w, z} J A₁ (freeAlgebraSheaf J A₁ E) B
          (freeAlgebraSheafCoefficientMap J A₁ E) (restrictedPresentation J u E a₂ e) X g) =
      conormalClass.{v, u, w, z} J A₁ (freeAlgebraSheaf J A₂ E) B
        (u ≫ freeAlgebraSheafCoefficientMap J A₂ E) (basePresentation J E a₂ e) X
        ⟨(baseChange J u E).hom.app X g, baseChange_mem_basePresentationIdeal J u E a₂ e X g⟩ :=
  conormalSheafMapOfFac_conormalClass.{v, u, w, z} J A₁ B _ _
    (freeAlgebraSheafCoefficientMap J A₁ E) (u ≫ freeAlgebraSheafCoefficientMap J A₂ E) _ _
    (baseChange J u E) (baseChange_comp_desc J u E a₂ e) X g

end Stacks.Sites.Conormal

end
