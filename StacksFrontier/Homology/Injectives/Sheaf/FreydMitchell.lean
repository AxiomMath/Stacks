module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.Opposite
public import StacksFrontier.Homology.Injectives.Sheaf.EpiTopologyEmbedding
import StacksCore.Tactic.StacksAttribute

/-!
# The Freyd--Mitchell embedding theorem from the epimorphism site

Let `A` be an abelian category with a set of objects. Tag 05PR explains how to deduce the
Freyd--Mitchell embedding theorem from the Yoneda embedding of Tag 05PN into abelian sheaves on
the epimorphism site. This file carries out that deduction.

Write `B = Ab(C)` for the abelian sheaves on the epimorphism site of `Aᵒᵖ` (Tag 05PM) and
`D = Bᵒᵖ`. The steps are:

* `B` is a Grothendieck abelian category, so it has enough injectives and — this is the step for
  which Tag 05PR omits the details — an injective cogenerator. Dually `D` has enough projectives
  and a generator, hence a projective generator.
* Tag 05PN applied to `Aᵒᵖ` gives a fully faithful exact functor `Aᵒᵖ ⥤ B`, i.e. a fully faithful
  exact `i : A ⥤ D`.
* For a projective generator `P` of `D`, the functor `Hom_D(P, -) : D ⥤ Mod_{Mor_D(P,P)}` is
  faithful (because `P` is a generator) and exact (left exactness because it is a hom functor,
  right exactness because `P` is projective), and `i ⋙ Hom_D(P, -)` is full. Fullness needs more
  than the bare existence of a projective generator: every object in the image of `i` must be a
  quotient of `P`. The generator is therefore enlarged to
  `P = ∐_{X : A} ∐_{P₀ ⟶ i.obj X} P₀` for a projective generator `P₀`, which is still a
  projective generator and does cover the image of `i`.

The result is `Stacks.Injectives.exists_projectiveSeparator_hom_fullyFaithful_exact`, which
states the whole of the last display of Tag 05PR, and
`Stacks.Injectives.exists_ring_moduleEmbedding`, the Freyd--Mitchell statement for an arbitrary
abelian category obtained from it by replacing `A` with an equivalent small category.

## Main definitions

* `Stacks.Injectives.oppEpiSheaf`: the category `B = Ab(C)` of abelian sheaves on the
  epimorphism site of `Aᵒᵖ`.
* `Stacks.Injectives.oppEpiEmbedding`: the functor `i : A ⥤ D = Bᵒᵖ` of Tag 05PN applied to
  `Aᵒᵖ`.

## Main results

* `Stacks.Injectives.oppEpiSheaf_enoughInjectives` and
  `Stacks.Injectives.oppEpiSheaf_exists_injective_coseparator`: `B` has enough injectives and an
  injective cogenerator.
* `Stacks.Injectives.oppEpiSheafOp_enoughProjectives` and
  `Stacks.Injectives.oppEpiSheafOp_exists_projective_separator`: `D` has enough projectives and a
  projective generator.
* `Stacks.Injectives.oppEpiEmbedding_full`, `_faithful`, `_preservesFiniteLimits` and
  `_preservesFiniteColimits`: `i` is a fully faithful exact embedding.
* `Stacks.Injectives.exists_projectiveSeparator_hom_fullyFaithful_exact`: there is a projective
  generator `P` of `D` for which `X ↦ Hom_D(P, X)` is a fully faithful exact functor
  `A ⥤ Mod_{Mor_D(P,P)}`.
* `Stacks.Injectives.exists_ring_moduleEmbedding`: the Freyd--Mitchell embedding theorem.

## Implementation notes

The source says `Mod_R` for `R = Mor_D(P, P)`; the Lean functor `preadditiveCoyonedaObj P` lands
in modules over `(End P)ᵐᵒᵖ`, because `Hom_D(P, X)` is naturally a *right* module over the
endomorphism ring under composition.

Smallness of `A` is a genuine hypothesis of Tag 05PN (see Tag 05PQ) and is carried here as
`SmallCategory A`. The last theorem removes it in the only way available, by enlarging the ring:
an arbitrary abelian category `A : Type u` with `Category.{v} A` is replaced by the equivalent
small category `AsSmall.{max u v} A`, so the modules live over a ring in `Type (max u v)`.

## References

* [Stacks Project, Tag 05PR](https://stacks.math.columbia.edu/tag/05PR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe v u

namespace Stacks.Injectives

section Small

variable (A : Type v) [SmallCategory A] [Abelian A]

/-- The category `B = Ab(C)` of abelian sheaves on the epimorphism site of `Aᵒᵖ`, i.e. the target
of the embedding of Tag 05PN applied to `Aᵒᵖ`. -/
abbrev oppEpiSheaf := Sheaf (epiPretopology Aᵒᵖ).toGrothendieck AddCommGrpCat.{v}

/-- **Stacks 05PR**, first clause. `Ab(C)` has enough injectives. -/
@[stacks 05PR "Ab(C) has enough injectives"]
theorem oppEpiSheaf_enoughInjectives : EnoughInjectives (oppEpiSheaf A) := inferInstance

/-- **Stacks 05PR**, second clause: `Ab(C)` has a cogenerator. The source omits the details; here
it comes from `Ab(C)` being a Grothendieck abelian category, which moreover makes the cogenerator
injective. -/
@[stacks 05PR "Ab(C) has a cogenerator"]
theorem oppEpiSheaf_exists_injective_coseparator :
    ∃ G : oppEpiSheaf A, Injective G ∧ IsCoseparator G :=
  Abelian.has_injective_coseparator (separator (oppEpiSheaf A)) (isSeparator_separator _)

/-- The functor `i : A ⥤ D = Bᵒᵖ` of Tag 05PR, namely the Yoneda embedding of Tag 05PN applied to
`Aᵒᵖ`. -/
noncomputable def oppEpiEmbedding : A ⥤ (oppEpiSheaf A)ᵒᵖ := (yonedaSheaf Aᵒᵖ).rightOp

/-- **Stacks 05PR**, third clause. The functor `i : A ⥤ D` is full. -/
@[stacks 05PR "the embedding i : A ⥤ D"]
theorem oppEpiEmbedding_full : (oppEpiEmbedding A).Full := by
  have : (yonedaSheaf Aᵒᵖ).Full := yonedaSheaf_full Aᵒᵖ
  dsimp only [oppEpiEmbedding]
  infer_instance

/-- **Stacks 05PR**, third clause. The functor `i : A ⥤ D` is faithful. -/
@[stacks 05PR "the embedding i : A ⥤ D"]
theorem oppEpiEmbedding_faithful : (oppEpiEmbedding A).Faithful := by
  have : (yonedaSheaf Aᵒᵖ).Faithful := yonedaSheaf_faithful Aᵒᵖ
  dsimp only [oppEpiEmbedding]
  infer_instance

/-- **Stacks 05PR**, third clause. The functor `i : A ⥤ D` is left exact. -/
@[stacks 05PR "the embedding i : A ⥤ D"]
theorem oppEpiEmbedding_preservesFiniteLimits :
    PreservesFiniteLimits (oppEpiEmbedding A) := by
  have := yonedaSheaf_preservesFiniteColimits Aᵒᵖ
  exact preservesFiniteLimits_rightOp _

/-- **Stacks 05PR**, third clause. The functor `i : A ⥤ D` is right exact. -/
@[stacks 05PR "the embedding i : A ⥤ D"]
theorem oppEpiEmbedding_preservesFiniteColimits :
    PreservesFiniteColimits (oppEpiEmbedding A) := by
  have := yonedaSheaf_preservesFiniteLimits Aᵒᵖ
  exact preservesFiniteColimits_rightOp _

/-- **Stacks 05PR**, fourth clause. `D = Bᵒᵖ` has enough projectives. -/
@[stacks 05PR "D has enough projectives"]
theorem oppEpiSheafOp_enoughProjectives : EnoughProjectives (oppEpiSheaf A)ᵒᵖ := inferInstance

/-- **Stacks 05PR**, fourth clause. `D = Bᵒᵖ` has a generator, hence a projective generator. -/
@[stacks 05PR "D has a projective generator"]
theorem oppEpiSheafOp_exists_projective_separator :
    ∃ P : (oppEpiSheaf A)ᵒᵖ, Projective P ∧ IsSeparator P :=
  Abelian.has_projective_separator (op (separator (oppEpiSheaf A)))
    ((isCoseparator_op_iff _).2 (isSeparator_separator _))

/-- **Stacks 05PR**, last clause. There is a projective generator `P` of `D = Bᵒᵖ` such that

`A ⟶ Mod_R, X ↦ Hom_D(P, X)` with `R = Mor_D(P, P)`

is a fully faithful exact functor. This is the Freyd--Mitchell embedding theorem for a small
abelian category, obtained along the route of Tag 05PR. -/
@[stacks 05PR "the embedding into `Hom_D(P, -)` for a projective generator `P`"]
theorem exists_projectiveSeparator_hom_fullyFaithful_exact :
    ∃ P : (oppEpiSheaf A)ᵒᵖ, Projective P ∧ IsSeparator P ∧
      (oppEpiEmbedding A ⋙ preadditiveCoyonedaObj P).Full ∧
      (oppEpiEmbedding A ⋙ preadditiveCoyonedaObj P).Faithful ∧
      PreservesFiniteLimits (oppEpiEmbedding A ⋙ preadditiveCoyonedaObj P) ∧
      PreservesFiniteColimits (oppEpiEmbedding A ⋙ preadditiveCoyonedaObj P) := by
  classical
  have : Nonempty A := ⟨0⟩
  obtain ⟨P₀, hproj, hsep⟩ := oppEpiSheafOp_exists_projective_separator A
  have := oppEpiEmbedding_full A
  have := oppEpiEmbedding_faithful A
  have := oppEpiEmbedding_preservesFiniteLimits A
  have := oppEpiEmbedding_preservesFiniteColimits A
  set i := oppEpiEmbedding A
  -- Enlarge `P₀` so that every object in the image of `i` is a quotient of it.
  set g : A → (oppEpiSheaf A)ᵒᵖ := fun X => ∐ fun _ : P₀ ⟶ i.obj X => P₀
  have hgsep : IsSeparator (∐ g) := by
    refine isSeparator_sigma_of_isSeparator g (Classical.ofNonempty : A) ?_
    exact isSeparator_sigma_of_isSeparator _ (0 : P₀ ⟶ i.obj Classical.ofNonempty) hsep
  have hgepi : ∀ X : A, ∃ p : (∐ g) ⟶ i.obj X, Epi p := by
    intro X
    refine ⟨Sigma.desc (Pi.single X (𝟙 (g X))) ≫ Sigma.desc fun f : P₀ ⟶ i.obj X => f, ?_⟩
    have h := (isSeparator_iff_epi P₀).1 hsep (i.obj X)
    suffices Epi (Sigma.desc (Pi.single X (𝟙 (g X)))) from epi_comp' this h
    exact SplitEpi.epi ⟨Sigma.ι g X, by simp⟩
  have hfaith : (preadditiveCoyonedaObj (∐ g)).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj _).1 hgsep
  refine ⟨∐ g, inferInstance, hgsep,
    Abelian.full_comp_preadditiveCoyonedaObj i hgsep hgepi, inferInstance, ?_, ?_⟩
  · exact comp_preservesFiniteLimits _ _
  · have : PreservesFiniteColimits (preadditiveCoyonedaObj (∐ g)) :=
      preservesFiniteColimits_preadditiveCoyonedaObj_of_projective _
    exact comp_preservesFiniteColimits _ _

end Small

/-- **The Freyd--Mitchell embedding theorem**, in the form Tag 05PR retrieves it: for every
abelian category `A` there are a ring `R` and a fully faithful exact functor `A ⥤ Mod_R`.

The functor produced here is `X ↦ Hom_D(P, X)` for a projective generator `P` of the opposite of
the category of abelian sheaves on the epimorphism site of `Aᵒᵖ`, as in Tag 05PR. The conclusion
is the same as Mathlib's `CategoryTheory.Abelian.freyd_mitchell`, which carries Tag 05PP and is
proved instead through Gabriel--Popescu; what Tag 05PR asserts, and what this declaration
records, is that the theorem is retrieved from Tag 05PN by the route above. -/
@[stacks 05PR]
theorem exists_ring_moduleEmbedding (A : Type u) [Category.{v} A] [Abelian A] :
    ∃ (R : Type (max u v)) (_ : Ring R) (F : A ⥤ ModuleCat.{max u v} R),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := by
  obtain ⟨P, _, _, hfull, hfaith, hlim, hcolim⟩ :=
    exists_projectiveSeparator_hom_fullyFaithful_exact (AsSmall.{max u v} A)
  exact ⟨(End P)ᵐᵒᵖ, inferInstance,
    AsSmall.equiv.functor ⋙ oppEpiEmbedding (AsSmall.{max u v} A) ⋙ preadditiveCoyonedaObj P,
    inferInstance, inferInstance, comp_preservesFiniteLimits _ _,
    comp_preservesFiniteColimits _ _⟩

end Stacks.Injectives
