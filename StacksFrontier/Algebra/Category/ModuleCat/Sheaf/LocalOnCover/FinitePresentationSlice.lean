module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentation

/-!
# Finite presentation on a slice of a site

Restriction along the projection from a slice of a site preserves finite presentation of a
sheaf of modules, as `Stacks.SheafOfModules.Site.isFiniteType_over_of_isFiniteType` does for
finite type.

## Main results

* `Stacks.SheafOfModules.isFinitePresentation_over`: restriction to a slice of the site
  preserves finite presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)
  [∀ (U : C), HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ (U : C), (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ (U : C) (V : Over U), HasSheafify ((J.over U).over V) AddCommGrpCat.{w}]
  [∀ (U : C) (V : Over U), ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A finite presentation of `M` over `Z.left` is a finite presentation of the restriction of
`M.over U` to `Z`, read through `Stacks.SheafOfModules.Site.overOverEquivalence`. -/
theorem exists_finitePresentation_overOver (M : _root_.SheafOfModules.{w} R) (U : C)
    (Z : Over U) (P : (M.over Z.left).Presentation) [P.IsFinite] :
    ∃ Q : ((M.over U).over Z).Presentation, Q.IsFinite := by
  let F := (Site.overOverEquivalence (R := R) U Z).functor
  have hfin : (LocalCokernel.mapFinitePresentation P F (Iso.refl _)).IsFinite :=
    LocalCokernel.mapFinitePresentation_isFinite P F (Iso.refl _)
  exact ⟨(LocalCokernel.mapFinitePresentation P F (Iso.refl _)).ofIsIso
    (F.mapIso (Site.overOverIso M U Z).symm ≪≫
      (Site.overOverEquivalence (R := R) U Z).counitIso.app ((M.over U).over Z)).hom,
    inferInstance⟩

/-- Restriction to a slice of the site preserves finite presentation: if `M` is of finite
presentation, then so is its restriction `M.over U` to the slice over `U`. -/
theorem isFinitePresentation_over (M : _root_.SheafOfModules.{w} R)
    (hM : M.IsFinitePresentation) (U : C) : (M.over U).IsFinitePresentation := by
  classical
  have _ := hM
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hcover : (J.over U).CoversTop (Subtype.val :
      { Z : Over U // ∃ P : ((M.over U).over Z).Presentation, P.IsFinite } → Over U) := by
    intro Y
    refine (J.over U).superset_covering ?_
      ((Over.forget U).cover_lift (J.over U) J (q.coversTop Y.left))
    intro Z g hg
    obtain ⟨i, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff _ ((Over.forget U).map g)).1 hg
    have : (q.presentation i).IsFinite := hq.isFinite_presentation i
    obtain ⟨P, hP⟩ := LocalCokernel.exists_finitePresentation_overMap M c (q.presentation i)
    have _ := hP
    exact (Sieve.mem_ofObjects_iff _ g).2
      ⟨⟨Z, exists_finitePresentation_overOver M U Z P⟩, ⟨𝟙 Z⟩⟩
  refine { exists_quasicoherentData := ?_ }
  refine ⟨({ I := { Z : Over U // ∃ P : ((M.over U).over Z).Presentation, P.IsFinite }
             X := Subtype.val
             coversTop := hcover
             presentation := fun i => i.2.choose } :
            (M.over U).QuasicoherentData).shrink, ?_⟩
  exact ⟨fun j => j.2.choose.2.choose_spec⟩

end Stacks.SheafOfModules

end
