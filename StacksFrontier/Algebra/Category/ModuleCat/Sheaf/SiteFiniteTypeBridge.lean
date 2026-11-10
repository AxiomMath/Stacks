module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceKernels
import StacksCore.Tactic.EgaSgaAttribute

/-!
# From categorical to sectionwise finite type for sheaves of modules on a site

Mathlib's `SheafOfModules.IsFiniteType` is categorical: it records a covering family of the
site together with, on each member, finitely many global sections whose associated map from the
sheafified free sheaf of modules is an epimorphism. The sectionwise
`PresheafOfModules.IsFiniteType` asks instead that every section be locally a linear combination
of finitely many fixed ones. This file proves that the categorical condition implies the
sectionwise one.

## Main results

* `Stacks.SheafOfModules.exists_eval_comb`: the image of a section of a free sheaf of modules on
  a finite type under a morphism `π` is a linear combination of the images under `π` of the
  tautological sections.
* `Stacks.SheafOfModules.exists_generators_of_generatingSections`: finitely many generating
  global sections of a sheaf of modules generate it sectionwise over every object of the site.
* `Stacks.SheafOfModules.isFiniteType_presheaf_of_generatingSections`: a sheaf of modules with
  finitely many generating global sections has a presheaf of modules of finite type.
* `Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteType`: `SheafOfModules.IsFiniteType`
  implies `PresheafOfModules.IsFiniteType` of the underlying presheaf of modules.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w

section Free

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A section of the sheaf of rings read as a section of the unit sheaf of modules. -/
private abbrev unitElt (X : Cᵒᵖ) (b : R.obj.obj X) : (SheafOfModules.unit R).val.obj X := b

private noncomputable def freeSummandProj {I : Type w} [DecidableEq I] (j : I) :
    SheafOfModules.free (R := R) I ⟶ SheafOfModules.unit R :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan I)
    (fun i ↦ if i = j then 𝟙 (SheafOfModules.unit R) else 0)

private theorem ιFree_freeSummandProj {I : Type w} [DecidableEq I] (i j : I) :
    SheafOfModules.ιFree (R := R) i ≫ freeSummandProj j =
      if i = j then 𝟙 (SheafOfModules.unit R) else 0 :=
  Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan I) _ i

private theorem freeSummandProj_total {I : Type w} [DecidableEq I] [Fintype I] :
    (∑ j : I, freeSummandProj (R := R) j ≫ SheafOfModules.ιFree j) =
      𝟙 (SheafOfModules.free (R := R) I) := by
  have key : ∀ i : I, SheafOfModules.ιFree (R := R) i ≫
      (∑ j : I, freeSummandProj (R := R) j ≫ SheafOfModules.ιFree j) =
      SheafOfModules.ιFree (R := R) i ≫ 𝟙 (SheafOfModules.free (R := R) I) := by
    intro i
    rw [Category.comp_id, Preadditive.comp_sum, Finset.sum_eq_single i]
    · rw [← Category.assoc, ιFree_freeSummandProj]
      simp
    · intro j _ hj
      rw [← Category.assoc, ιFree_freeSummandProj]
      simp [Ne.symm hj]
    · simp
  exact Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) _ _ key

private theorem free_eval_eq_sum {I : Type w} [DecidableEq I] [Fintype I] {X : Cᵒᵖ}
    (y : (SheafOfModules.free (R := R) I).val.obj X) :
    y = ∑ j : I, (SheafOfModules.ιFree (R := R) j).val.app X
      ((freeSummandProj (R := R) j).val.app X y) := by
  let ev : (SheafOfModules.free (R := R) I ⟶ SheafOfModules.free (R := R) I) →+
      (SheafOfModules.free (R := R) I).val.obj X :=
    { toFun := fun f ↦ f.val.app X y
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have h := map_sum ev
    (fun j : I ↦ freeSummandProj (R := R) j ≫ SheafOfModules.ιFree j) Finset.univ
  rwa [freeSummandProj_total] at h

/-- Let `π` be a morphism out of the free sheaf of modules on a finite type `I`. Every section
`y` of the free sheaf over an object `X` of the site has image under `π` a linear combination,
with coefficients in the sections of the sheaf of rings over `X`, of the sections over `X` of the
family that `π` corresponds to under `SheafOfModules.freeHomEquiv`. -/
theorem exists_eval_comb {I : Type w} [Fintype I] {N : SheafOfModules.{w} R}
    (π : SheafOfModules.free (R := R) I ⟶ N) {X : Cᵒᵖ}
    (y : (SheafOfModules.free (R := R) I).val.obj X) :
    ∃ b : I → R.obj.obj X,
      π.val.app X y = ∑ j, b j • (N.freeHomEquiv π j).eval X := by
  classical
  refine ⟨fun j ↦ ((freeSummandProj (R := R) j).val.app X y : R.obj.obj X), ?_⟩
  have h1 := congrArg (fun z ↦ π.val.app X z) (free_eval_eq_sum (R := R) (I := I) y)
  rw [map_sum] at h1
  refine h1.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
  change (SheafOfModules.ιFree (R := R) j ≫ π).val.app X _ = _
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply π j]
  rfl

end Free

section Bridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]

/-- A section of a presheaf of modules read as a section of the underlying presheaf of abelian
groups. -/
private abbrev groupElt {N : PresheafOfModules.{w} R.obj} (X : Cᵒᵖ) (t : N.obj X) :
    ((PresheafOfModules.toPresheaf R.obj).obj N).obj X := t

/-- If a sheaf of modules on a site has a finite family of generating global sections, then over
every object of the site their values form a finite family generating the module in the sense of
`PresheafOfModules.Generates`. -/
@[ega "0 5.1.1" "partial"]
theorem exists_generators_of_generatingSections {N : SheafOfModules.{w} R}
    (G : N.GeneratingSections) [Finite G.I] (U : C) :
    ∃ (n : ℕ) (s : Fin n → N.val.obj (op U)), PresheafOfModules.Generates J N.val s := by
  classical
  have : Fintype G.I := Fintype.ofFinite G.I
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G.I
  refine ⟨n, fun j ↦ (G.s (e.symm j)).eval (op U), ?_⟩
  intro V f t
  have hls : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map G.π.val) :=
    Stacks.SheafOfModules.LocalCokernel.locallySurjective_of_epi G.π
  refine ⟨Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map G.π.val)
    (groupElt (op V) t), Presheaf.imageSieve_mem J _ _, ?_⟩
  intro W g hg
  obtain ⟨y, hy⟩ := hg
  obtain ⟨b, hb⟩ := exists_eval_comb G.π (X := op W) y
  refine ⟨fun i ↦ b (e.symm i), ?_⟩
  have hπ : ∀ j : G.I, N.freeHomEquiv G.π j = G.s j := fun j ↦
    congrFun (N.freeHomEquiv.apply_symm_apply G.s) j
  have hb' : G.π.val.app (op W) y = ∑ j : G.I, b j • (G.s j).eval (op W) :=
    hb.trans (Finset.sum_congr rfl fun j _ ↦ by rw [hπ j])
  have hval : N.val.restrictₛₗ g.op t = ∑ j : G.I, b j • (G.s j).eval (op W) :=
    (hy.symm : N.val.restrictₛₗ g.op t = G.π.val.app (op W) y).trans hb'
  have hreindex : (∑ j : G.I, b j • (G.s j).eval (op W)) =
      ∑ i : Fin n, b (e.symm i) • (G.s (e.symm i)).eval (op W) :=
    (Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl).symm
  have hsec : ∀ i : Fin n, N.val.restrictₛₗ (g ≫ f).op ((G.s (e.symm i)).eval (op U)) =
      (G.s (e.symm i)).eval (op W) := fun i ↦ (G.s (e.symm i)).2 (g ≫ f).op
  rw [hval, hreindex]
  exact (Finset.sum_congr rfl fun i _ ↦ by rw [hsec i]).symm

/-- A sheaf of modules with finitely many generating global sections has a presheaf of modules
of finite type. -/
theorem isFiniteType_presheaf_of_generatingSections {N : SheafOfModules.{w} R}
    (G : N.GeneratingSections) [Finite G.I] :
    PresheafOfModules.IsFiniteType J N.val :=
  isFiniteType_presheaf_of_coversTop (id : C → C)
    (fun _ ↦ J.covering_of_eq_top (Sieve.ext fun Y _ ↦ ⟨fun _ ↦ trivial, fun _ ↦ ⟨Y, ⟨𝟙 Y⟩⟩⟩))
    (fun X ↦ exists_generators_of_generatingSections G X)

end Bridge

section Descent

/-- Mathlib's categorical finite type condition `SheafOfModules.IsFiniteType` on a sheaf of
modules implies the sectionwise condition `PresheafOfModules.IsFiniteType` on the underlying
presheaf of modules. -/
@[ega "0 5.2.1" "partial", sga "6 I 1.3" "partial"]
theorem presheaf_isFiniteType_of_isFiniteType
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
    (M : SheafOfModules.{w} R) (h : M.IsFiniteType) :
    PresheafOfModules.IsFiniteType J M.val := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  refine isFiniteType_of_over M σ.X σ.coversTop fun i ↦ ?_
  have := hσ.isFiniteType i
  exact isFiniteType_presheaf_of_generatingSections (σ.generators i)

end Descent

end Stacks.SheafOfModules

end
