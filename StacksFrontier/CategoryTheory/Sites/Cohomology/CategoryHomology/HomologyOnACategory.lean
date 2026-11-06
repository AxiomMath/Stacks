module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Generator.Presheaf
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import StacksCore.Tactic.StacksAttribute

/-!
# Homology on a category

Let `C` be a small category and let `F` be an abelian-group-valued presheaf on `C`. For the
chaotic topology on `C`, the lower shriek functor along the morphism to the point is the
colimit over `Cᵒᵖ`, so the homology groups `H_n(C, F)` of Stacks 08PF are the values at `F`
of the left derived functors of `colim`.

The content of this file is that those left derived functors exist: the category of
abelian-group-valued presheaves on a small category has enough projectives. A projective
presentation is produced from the free presheaves `freeYoneda X P` on representables with
projective coefficients `P`, whose coproduct over all objects of `C` is a projective
separator; the canonical epimorphism out of a coproduct of copies of a projective separator
is then the required projective cover.

## Main definitions

* `Stacks.CategoryHomology.presheafProjectiveSeparator`: the coproduct of the free presheaves
  on representables with coefficients a projective cover of a separator of abelian groups.
* `Stacks.CategoryHomology.categoryHomology`: the `n`th homology group `H_n(C, F)`, the value
  at `F` of the `n`th left derived functor of `colim`.

## Main results

* `Stacks.CategoryHomology.presheafEnoughProjectives`: the category of abelian-group-valued
  presheaves on a small category has enough projectives; this is what supplies the projective
  resolutions used to form the left derived functors.

## Implementation notes

That abelian groups have enough projectives is transported along the equivalence with
`ℤ`-modules. A free diagram `freeYoneda X P` is projective as soon as `P` is, because
`freeYonedaHomEquiv` turns a lifting problem for it into a lifting problem for `P` against
the component of the epimorphism at `X`; that argument uses nothing about abelian groups, so
`Stacks.CategoryHomology.freeYonedaProjective` is stated for an arbitrary target in which the
free diagrams exist and epimorphisms of diagrams are epimorphisms componentwise. The source
writes `H_n(C, F) = L_nπ_!(F)` and then
identifies `π_!` with `colim`; the identification itself (Stacks 08PE) is not formalized
here, so `categoryHomology` is defined directly as the left derived functor of `colim`.

Tag 08PF is split over three modules of this section, this one carrying the clause
`homology_of_a_category`. The others are
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/PointMorphism.lean` (the clauses
`chaotic_site` and `point_morphism`: presheaves and sheaves agree for the chaotic topology,
and the point functor induces a morphism of topoi) and
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/RingedPoint.lean` (the
clause `ringed_point`, which equips the point with a ring `B` and `C` with `O_C = π⁻¹B`).

## References

* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uD vD vC u v

namespace Stacks.CategoryHomology

/-- The category of abelian groups has enough projectives, transported from the equivalent
category of `ℤ`-modules. -/
noncomputable instance abEnoughProjectives :
    EnoughProjectives AddCommGrpCat.{v} :=
  (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.enoughProjectives_iff.mp
    ModuleCat.enoughProjectives

/-- **A free diagram on a representable is projective when its coefficient object is.** This
holds in any target in which the free diagrams are defined and epimorphisms of diagrams are
epimorphisms componentwise, in particular in any abelian target: `freeYonedaHomEquiv` turns a
lifting problem for `freeYoneda X P` into a lifting problem for `P` against the component at `X`
of the epimorphism. -/
noncomputable instance freeYonedaProjective
    {C : Type u} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    [HasCoproducts.{vC} D] [HasPushouts D] (X : C) (P : D) [Projective P] :
    Projective (Presheaf.freeYoneda X P) where
  factors {E Y} f e _ :=
    ⟨Presheaf.freeYonedaHomEquiv.symm
        (Projective.factorThru (Presheaf.freeYonedaHomEquiv f) (e.app (.op X))), by
      apply Presheaf.freeYonedaHomEquiv.injective
      rw [Presheaf.freeYonedaHomEquiv_comp, Equiv.apply_symm_apply,
        Projective.factorThru_comp]⟩

/-- A projective separator of the category of abelian-group-valued presheaves. -/
noncomputable def presheafProjectiveSeparator
    (C : Type u) [SmallCategory C] : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  ∐ fun i : C × Unit ↦ match i with
    | (X, _) => Presheaf.freeYoneda X (Projective.over (separator AddCommGrpCat.{max u v}))

/-- A projective cover of the chosen separator of abelian groups is still a separator. -/
lemma projectiveOverSeparator_isSeparator :
    IsSeparator (Projective.over (separator AddCommGrpCat.{v})) := by
  refine (isSeparator_def _).2 fun X Y f g h ↦
    (isSeparator_separator AddCommGrpCat.{v}).def f g fun k ↦ ?_
  rw [← cancel_epi (Projective.π (separator AddCommGrpCat.{v}))]
  simpa only [Category.assoc] using
    h (Projective.π (separator AddCommGrpCat.{v}) ≫ k)

/-- The coproduct of the free presheaves on the representables is a separator. -/
lemma presheafProjectiveSeparator_isSeparator
    (C : Type u) [SmallCategory C] :
    IsSeparator (presheafProjectiveSeparator.{u, v} C) :=
  Presheaf.isSeparator C
    (S := fun _ : Unit ↦ Projective.over (separator AddCommGrpCat.{max u v}))
    (ObjectProperty.IsSeparating.of_le projectiveOverSeparator_isSeparator.{max u v}
      (by simp))

/-- Every abelian-group-valued presheaf on a small category is a quotient of a projective
presheaf. -/
noncomputable instance presheafEnoughProjectives
    (C : Type u) [SmallCategory C] : EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) := by
  let P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} := presheafProjectiveSeparator.{u, v} C
  let _ : ∀ i : C × Unit,
      Projective (match i with
        | (X, _) => Presheaf.freeYoneda X
          (Projective.over (separator AddCommGrpCat.{max u v}))) := by
    rintro ⟨X, _⟩
    exact freeYonedaProjective X _
  let _ : Projective P := by
    dsimp only [P, presheafProjectiveSeparator]
    exact ⟨fun f e _ ↦ ⟨Sigma.desc fun i ↦ Projective.factorThru
      (Sigma.ι (fun i : C × Unit ↦ match i with
        | (X, _) => Presheaf.freeYoneda X
          (Projective.over (separator AddCommGrpCat.{max u v}))) i ≫ f) e, by cat_disch⟩⟩
  exact ⟨fun F ↦ ⟨{
    p := ∐ fun _ : P ⟶ F ↦ P
    f := Sigma.desc fun f ↦ f
    epi := (isSeparator_iff_epi P).mp (presheafProjectiveSeparator_isSeparator.{u, v} C) F }⟩⟩

/-- **Stacks 08PF.** The `n`th homology group of an abelian-group-valued presheaf on a small
category is the value of the `n`th left derived functor of `colim`. -/
@[stacks 08PF "homology_of_a_category"]
noncomputable abbrev categoryHomology {C : Type u} [SmallCategory C]
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) : AddCommGrpCat.{max u v} :=
  ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v}).leftDerived n).obj F

end Stacks.CategoryHomology
