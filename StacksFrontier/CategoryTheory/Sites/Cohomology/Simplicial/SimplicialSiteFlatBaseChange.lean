module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeRows
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialSiteBaseChangeStep

/-!
# Flat base change of simplicial modules on the simplicial site `Δ × C`

Let `(C, J)` be a small site, let `Δ × C` be the simplicial site of [Stacks, Tag 09D0] and let
`θ : O ⟶ O'` be a homomorphism of presheaves of commutative rings on it. Write `s(-)` for the
complex of abelian sheaves on `C` attached to a presheaf of `O`-modules by
`Stacks.SimplicialModules.mooreSheafCochain`. This module proves the instance of
[Stacks, Tag 08RX] on `Δ × C`: if the base-change unit

`s(O) ⟶ s(O')`

is a quasi-isomorphism — which is the hypothesis of [Stacks, Tag 09D2], read through the
identification of `L π_!` on simplicial modules with `s(-)` — then for every presheaf of
`O`-modules `F` whose sections over each object of `Δ × C` are a flat module, the base-change
unit

`s(F) ⟶ s(F ⊗_O O')`

is a quasi-isomorphism.

That is the statement the proof of [Stacks, Tag 09D2] reduces the lemma to in its second step:
"thus it suffices to prove the lemma for a flat `A_•`-module `F`". It is *not* Tag 09D2, and
carries no tag; see the section below.

## What was missing and is supplied here

`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialSiteMooreBicomplex.lean` builds
the double complex of a resolution and compares the two filtrations, leaving the row filtration on
the base-changed side as the hypothesis `hrow` of
`Stacks.SimplicialModules.quasiIso_totalSingleColumn_baseChangedMooreSheafCochain`; that is where
the flatness of `F` is consumed, and it was the one thing between that module and the statement
above. It is discharged here, and the route is the one the Δ-instance of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/FlatBaseChangeRows.lean` takes, with no
K-flatness of sheaves or presheaves of modules needed anywhere:

* the row `q = -n` of the base-changed double complex is base change followed by four exact
  functors — the underlying abelian presheaf, the currying which reads it as a simplicial abelian
  presheaf on `C`, evaluation at `⦋n⦌`, and sheafification — so the question is the question for
  base change alone, read on underlying abelian presheaves on `Δ × C`
  (`Stacks.PresheafOfModules.ChangeOfRings.quasiIso_changeOfRings_toPresheaf_map`);
* a quasi-isomorphism of complexes of abelian presheaves is a quasi-isomorphism over each object
  separately, and over an object `X` of `Δ × C` base change is extension of scalars along
  `θ_X : O(X) ⟶ O'(X)` on honest modules;
* a bounded above complex of flat modules is K-flat ([Stacks, Tag 064K],
  `CochainComplex.KFlat.kFlat_of_flat`) and extension of scalars preserves quasi-isomorphisms
  between K-flat complexes
  (`CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat`).

The flatness that the terms of the resolution supply is `PresheafOfModules.flat_stdCover_obj`: a
standard cover is a coproduct of free presheaves of modules on universe-lifted representables, and
the sections of those are free. The three flatness lemmas and the base-change step are stated over
an arbitrary small base category, nothing in them being special to `Δ × C`; at `C = Δ` they are
`Stacks.SimplicialModules.flat_stdCover_obj` and
`Stacks.SimplicialModules.quasiIso_eval_extendScalars_map`.

## Main results

* `PresheafOfModules.flat_free_obj`, `PresheafOfModules.flat_stdCover_obj`,
  `PresheafOfModules.flat_obj_of_isStdCover` and `PresheafOfModules.flat_single_obj`: the sections
  of the objects a resolution by standard covers is built from are flat modules.
* `Stacks.PresheafOfModules.ChangeOfRings.quasiIso_eval_extendScalars_map`: base change at one
  object of the base category, the flat base-change step.
* `Stacks.PresheafOfModules.ChangeOfRings.quasiIso_changeOfRings_toPresheaf_map`: **base change
  preserves quasi-isomorphisms between bounded above complexes of presheaves of modules with flat
  sections**, read on underlying abelian presheaves.
* `Stacks.SimplicialModules.quasiIso_total_map_baseChangedMooreSheafBicomplex`: **the row
  filtration on the base-changed side**, the hypothesis `hrow` discharged.
* `Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_quasiIso_total_row`: the passage
  from the two filtrations to the base-change unit at `F`.
* `Stacks.SimplicialModules.quasiIso_mooreSheafBaseChange_app_of_flat`: **the instance of
  [Stacks, Tag 08RX] on `Δ × C`** — `s(F) ⟶ s(F ⊗_O O')` is a quasi-isomorphism for every
  sectionwise flat `F`, under the hypothesis of [Stacks, Tag 09D2] and nothing else. No hypothesis
  about the fibres `Δ × U` is made or needed.

## Why this is not [Stacks, Tag 09D2], and carries no tag

Tag 09D2 reads: for a homomorphism `A_• ⟶ B_•` of simplicial sheaves of rings on a site `C` such
that `L π_! A_• ⟶ L π_! B_•` is an isomorphism in `D(C)`,

`L π_!(K) = L π_!(K ⊗^𝐋_{A_•} B_•)` for **all** `K` in `D(A_•)`.

The statement proved here is the one the source's proof reduces that to after two of its four
steps: a single sectionwise flat module, for which the derived tensor product is the ordinary one.
It is therefore a special case of the lemma's conclusion, and registering the tag on it would
report the lemma as covered while no declaration states it — exactly the defect that the five
former `@[stacks 09D2]` attributes on the four proof steps constituted. Three things are still
owed, and are listed in the module docstring of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/SimplicialSiteBaseChangeStep.lean`:
an identification of `L π_!` with `s(-)` on a *complex* (the available [Stacks, Tag 09D0],
`Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplex`, covers a single abelian
sheaf in degree `0`); the derived tensor product in the category the Moore machinery works in; and
the reduction of an arbitrary object of `D(A_•)` to bounded above complexes.

## Implementation notes

Simplicial modules are taken here as presheaves of modules on `Δ × C`, not as sheaves of modules;
since `s(-)` sheafifies in each degree this loses nothing and assumes less, a sheaf of modules
having an underlying presheaf of modules with the same `s(-)`. For the same reason the flatness
hypothesis is sectionwise flatness of the underlying presheaf of modules, which is what
[Stacks, Tag 03ET] shows implies flatness of the associated sheaf of modules.

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open StacksDraft.TotalComplexQuasiIso
open Stacks.PresheafOfModules.ChangeOfRings (ringPresheaf)

universe u

/-! ### Flatness of the sections of a resolution by standard covers -/

namespace PresheafOfModules

variable {D : Type u} [SmallCategory D] {R : Dᵒᵖ ⥤ CommRingCat.{u}}

/-- The commutative ring structure on a section ring of the presheaf of rings underlying a
presheaf of *commutative* rings, which instance search does not see through
`AlgebraicGeometry.SheafOfModules.ringPresheaf`. -/
instance commRing_ringPresheaf_obj (X : Dᵒᵖ) : CommRing ↥((ringPresheaf R).obj X) :=
  inferInstanceAs (CommRing ↥(R.obj X))

/-- **The sections of a free presheaf of modules are a free module**, hence flat. -/
lemma flat_free_obj (F : Dᵒᵖ ⥤ Type u) (X : Dᵒᵖ) :
    Module.Flat ↥((ringPresheaf R).obj X)
      ↥(((PresheafOfModules.free (ringPresheaf R)).obj F).obj X) :=
  inferInstanceAs (Module.Flat ↥((ringPresheaf R).obj X)
    (F.obj X →₀ ↥((ringPresheaf R).obj X)))

/-- **The sections of a standard cover are a flat module.** The cover is a coproduct of free
presheaves of modules on universe-lifted representables, evaluation at an object preserves that
coproduct, and the sections of a free presheaf of modules are a free module. This is the flatness
that the row direction of [Stacks, Tag 08RX] consumes on the terms of a resolution. -/
lemma flat_stdCover_obj (N : PresheafOfModules.{u} (ringPresheaf R)) (X : Dᵒᵖ) :
    Module.Flat ↥((ringPresheaf R).obj X) ↥((N.stdCover').obj X) := by
  classical
  have e := Limits.PreservesCoproduct.iso (PresheafOfModules.evaluation (ringPresheaf R) X)
    (fun m : N.Elements => (PresheafOfModules.free (ringPresheaf R)).obj
      (uliftYoneda.{u}.obj m.1.unop))
  have hflat : Module.Flat ↥((ringPresheaf R).obj X)
      ↥(∐ fun m : N.Elements => (PresheafOfModules.evaluation (ringPresheaf R) X).obj
        ((PresheafOfModules.free (ringPresheaf R)).obj (uliftYoneda.{u}.obj m.1.unop))) :=
    Stacks.SimplicialModules.flat_sigma _
      (fun m => flat_free_obj (uliftYoneda.{u}.obj m.1.unop) X)
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- **An object of a resolution by standard covers has flat sections.** A zero object has
subsingleton sections, and a standard cover has flat ones
(`PresheafOfModules.flat_stdCover_obj`). -/
lemma flat_obj_of_isStdCover {N : PresheafOfModules.{u} (ringPresheaf R)}
    (hN : PresheafOfModules.IsStdCover N) (X : Dᵒᵖ) :
    Module.Flat ↥((ringPresheaf R).obj X) ↥(N.obj X) := by
  obtain hz | ⟨N', ⟨e⟩⟩ := hN
  · have : Subsingleton ↥(N.obj X) :=
      ModuleCat.isZero_iff_subsingleton.1
        (Functor.map_isZero (PresheafOfModules.evaluation (ringPresheaf R) X) hz)
    infer_instance
  · have : Module.Flat ↥((ringPresheaf R).obj X)
        ↥((PresheafOfModules.evaluation (ringPresheaf R) X).obj N'.stdCover') :=
      flat_stdCover_obj N' X
    exact Module.Flat.of_linearEquiv
      ((PresheafOfModules.evaluation (ringPresheaf R) X).mapIso e).toLinearEquiv

/-- **A presheaf of modules with flat sections, placed in degree zero, has flat sections in every
degree of the resulting complex**: in degree `0` they are its own, and elsewhere they are a
subsingleton. -/
lemma flat_single_obj {M : PresheafOfModules.{u} (ringPresheaf R)}
    (hM : ∀ X, Module.Flat ↥((ringPresheaf R).obj X) ↥(M.obj X)) (p : ℤ) (X : Dᵒᵖ) :
    Module.Flat ↥((ringPresheaf R).obj X)
      ↥((((HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf R))
        (ComplexShape.up ℤ) 0).obj M).X p).obj X) := by
  by_cases hp : p = 0
  · subst hp
    have : Module.Flat ↥((ringPresheaf R).obj X)
        ↥((PresheafOfModules.evaluation (ringPresheaf R) X).obj M) := hM X
    exact Module.Flat.of_linearEquiv
      ((PresheafOfModules.evaluation (ringPresheaf R) X).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).toLinearEquiv
  · have : Subsingleton
        ↥((((HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf R))
          (ComplexShape.up ℤ) 0).obj M).X p).obj X) :=
      ModuleCat.isZero_iff_subsingleton.1
        (Functor.map_isZero (PresheafOfModules.evaluation (ringPresheaf R) X)
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M p hp))
    infer_instance

end PresheafOfModules

/-! ### Flat base change of presheaves of modules -/

namespace Stacks.PresheafOfModules.ChangeOfRings

variable {D : Type u} [SmallCategory D] {O O' : Dᵒᵖ ⥤ CommRingCat.{u}} (θ : O ⟶ O')

/-- **The flat base-change step at one object of the base category.** A quasi-isomorphism of
complexes of presheaves of `O`-modules, both bounded above by `0` and both with flat sections over
`X`, stays a quasi-isomorphism after evaluation at `X` and extension of scalars along `θ_X`.

Both evaluated complexes are K-flat ([Stacks, Tag 064K],
`CochainComplex.KFlat.kFlat_of_flat`), so this is
`CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat`; evaluation is
exact, which is what makes the evaluated map a quasi-isomorphism to begin with. -/
theorem quasiIso_eval_extendScalars_map (X : Dᵒᵖ)
    {K L : CochainComplex (_root_.PresheafOfModules.{u} (ringPresheaf O)) ℤ} (f : K ⟶ L)
    [QuasiIso f] [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (hK : ∀ p : ℤ, Module.Flat ↥((ringPresheaf O).obj X) ↥((K.X p).obj X))
    (hL : ∀ p : ℤ, Module.Flat ↥((ringPresheaf O).obj X) ↥((L.X p).obj X)) :
    QuasiIso (((_root_.PresheafOfModules.evaluation (ringPresheaf O) X ⋙
      ModuleCat.extendScalars (θ.app X).hom ⋙
        forget₂ (ModuleCat.{u} ↥(O'.obj X)) AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) := by
  have hKi : ∀ p : ℤ, Module.Flat ↥((ringPresheaf O).obj X)
      ↥((((_root_.PresheafOfModules.evaluation (ringPresheaf O) X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).X p) := hK
  have hLi : ∀ p : ℤ, Module.Flat ↥((ringPresheaf O).obj X)
      ↥((((_root_.PresheafOfModules.evaluation (ringPresheaf O) X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).X p) := hL
  have hev : QuasiIso (((_root_.PresheafOfModules.evaluation (ringPresheaf O)
      X).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology f _
  have hKf : CochainComplex.KFlat
      (((_root_.PresheafOfModules.evaluation (ringPresheaf O) X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
    CochainComplex.KFlat.kFlat_of_flat _ 0
  have hLf : CochainComplex.KFlat
      (((_root_.PresheafOfModules.evaluation (ringPresheaf O) X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) :=
    CochainComplex.KFlat.kFlat_of_flat _ 0
  have hext := CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat
    (θ.app X).hom
    (((_root_.PresheafOfModules.evaluation (ringPresheaf O) X).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) hKf hLf
  have hext' : QuasiIso
      (((ModuleCat.extendScalars (θ.app X).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((_root_.PresheafOfModules.evaluation (ringPresheaf O) X).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)) :=
    hext
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (((ModuleCat.extendScalars (θ.app X).hom).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((_root_.PresheafOfModules.evaluation (ringPresheaf O) X).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f))
    (forget₂ (ModuleCat.{u} ↥(O'.obj X)) AddCommGrpCat.{u})

/-- **Base change preserves quasi-isomorphisms between bounded above complexes of presheaves of
modules with flat sections**, read on underlying presheaves of abelian groups.

A quasi-isomorphism of complexes of abelian presheaves is one over each object of the base
category separately (`HomologicalComplex.quasiIso_iff_evaluation`), and over an object `X` base
change is extension of scalars along `θ_X` on the sections, which is
`Stacks.PresheafOfModules.ChangeOfRings.quasiIso_eval_extendScalars_map`. No K-flatness of
presheaves or sheaves of modules is involved: the flatness is spent on honest modules, one object
at a time. -/
theorem quasiIso_changeOfRings_toPresheaf_map
    {K L : CochainComplex (_root_.PresheafOfModules.{u} (ringPresheaf O)) ℤ} (f : K ⟶ L)
    [QuasiIso f] [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (hK : ∀ (p : ℤ) (X : Dᵒᵖ), Module.Flat ↥((ringPresheaf O).obj X) ↥((K.X p).obj X))
    (hL : ∀ (p : ℤ) (X : Dᵒᵖ), Module.Flat ↥((ringPresheaf O).obj X) ↥((L.X p).obj X)) :
    QuasiIso (((changeOfRings θ ⋙
      _root_.PresheafOfModules.toPresheaf (ringPresheaf O')).mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) :=
  (HomologicalComplex.quasiIso_iff_evaluation _).2 fun X =>
    quasiIso_eval_extendScalars_map θ X f (fun p => hK p X) (fun p => hL p X)

end Stacks.PresheafOfModules.ChangeOfRings

/-! ### The row filtration on `Δ × C` and the instance of Tag 08RX -/

namespace Stacks.SimplicialModules

open Stacks.PresheafOfModules.ChangeOfRings

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {O O' : (SimplexCategory × C)ᵒᵖ ⥤ CommRingCat.{u}} (θ : O ⟶ O')

/-- **The row `q = -n` of the base-changed double complex on `Δ × C`**: base change, followed by
the underlying abelian presheaf, the currying which reads it as a simplicial abelian presheaf on
`C`, evaluation at `⦋n⦌`, and sheafification. The reindexing of the Moore complex along
`ComplexShape.embeddingUpIntLE 0` is what
`AlgebraicTopology.alternatingFaceMapCochainComplexCompEvalIso` undoes; everything else is an
equality of functors. -/
def baseChangedMooreSheafCochainCompEvalIso (n : ℕ) :
    (changeOfRings θ ⋙ mooreSheafCochain J O') ⋙
        HomologicalComplex.eval (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)
          ((ComplexShape.embeddingUpIntLE (0 : ℤ)).f n) ≅
      (changeOfRings θ ⋙ PresheafOfModules.toPresheaf (ringPresheaf O')) ⋙
        simplicialCurry AddCommGrpCat.{u} ⋙
          ((evaluation SimplexCategoryᵒᵖ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
            (op (SimplexCategory.mk n)) ⋙ presheafToSheaf J AddCommGrpCat.{u}) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft
      (changeOfRings θ ⋙ PresheafOfModules.toPresheaf (ringPresheaf O') ⋙
        simplicialCurry AddCommGrpCat.{u})
      (alternatingFaceMapCochainComplexCompEvalIso (Cᵒᵖ ⥤ AddCommGrpCat.{u}) n))
    (presheafToSheaf J AddCommGrpCat.{u})

/-- The row `q` of the base-changed double complex of a map of complexes of presheaves of modules
on `Δ × C` is that map under the row functor. Both sides are degreewise constructions, so this is
`rfl`. -/
lemma flipHom_baseChangedMooreSheaf_f (q : ℤ)
    {K L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ} (f : K ⟶ L) :
    (flipHom (((changeOfRings θ ⋙ mooreSheafCochain J O').mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)).f q =
      (((changeOfRings θ ⋙ mooreSheafCochain J O') ⋙
        HomologicalComplex.eval (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)
          q).mapHomologicalComplex (ComplexShape.up ℤ)).map f := rfl

/-- **The row filtration of the double complex on the base-changed side.** A quasi-isomorphism of
complexes of presheaves of modules on `Δ × C`, both bounded above by `0` and both with flat
sections, stays a quasi-isomorphism on the total complexes of the base-changed double complexes.

This is [Stacks, Tag 0133] on the rows; the row `q = -n` is base change followed by exact
functors, so it is `Stacks.PresheafOfModules.ChangeOfRings.quasiIso_changeOfRings_toPresheaf_map`
transported along `Stacks.SimplicialModules.baseChangedMooreSheafCochainCompEvalIso`, and the rows
with `q > 0` vanish. This is the hypothesis `hrow` of
`Stacks.SimplicialModules.quasiIso_totalSingleColumn_baseChangedMooreSheafCochain`. -/
theorem quasiIso_total_map_baseChangedMooreSheafBicomplex
    {K L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ} (f : K ⟶ L) [QuasiIso f]
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (hK : ∀ (p : ℤ) (X : (SimplexCategory × C)ᵒᵖ),
      Module.Flat ↥((ringPresheaf O).obj X) ↥((K.X p).obj X))
    (hL : ∀ (p : ℤ) (X : (SimplexCategory × C)ᵒᵖ),
      Module.Flat ↥((ringPresheaf O).obj X) ↥((L.X p).obj X)) :
    QuasiIso (HomologicalComplex₂.total.map
      (((changeOfRings θ ⋙ mooreSheafCochain J O').mapHomologicalComplex
        (ComplexShape.up ℤ)).map f) (ComplexShape.up ℤ)) := by
  have hzero (M : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) [M.IsStrictlyLE 0]
      (p q : ℤ) (hpq : 0 < p ∨ 0 < q) :
      IsZero (((((changeOfRings θ ⋙ mooreSheafCochain J O').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).X p).X q) := by
    rcases hpq with hp | hq
    · exact Functor.map_isZero
        (HomologicalComplex.eval (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ) q)
        (isZero_baseChangedMooreSheafBicomplex_X J θ M p
          (CochainComplex.isZero_of_isStrictlyLE M 0 p hp))
    · exact isZero_baseChangedMooreSheafBicomplex_X_X J θ M p q hq
  refine quasiIso_total_map_of_upperBound_flip _ 0 0 (fun p q hpq => hzero K p q hpq)
    (fun p q hpq => hzero L p q hpq) (fun q => ?_)
  · rcases le_or_gt q 0 with hq | hq
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
        ⟨(-q).toNat, by simp; omega⟩
      subst hn
      rw [flipHom_baseChangedMooreSheaf_f J θ _ f]
      have hbase : QuasiIso (((changeOfRings θ ⋙
          PresheafOfModules.toPresheaf (ringPresheaf O')).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f) :=
        quasiIso_changeOfRings_toPresheaf_map θ f hK hL
      have hrow : QuasiIso ((((changeOfRings θ ⋙
          PresheafOfModules.toPresheaf (ringPresheaf O')) ⋙
            simplicialCurry AddCommGrpCat.{u} ⋙
              ((evaluation SimplexCategoryᵒᵖ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
                (op (SimplexCategory.mk n)) ⋙
                  presheafToSheaf J AddCommGrpCat.{u})).mapHomologicalComplex
                    (ComplexShape.up ℤ)).map f) :=
        HomologicalComplex.quasiIso_map_of_preservesHomology
          (((changeOfRings θ ⋙ PresheafOfModules.toPresheaf
            (ringPresheaf O')).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
          (simplicialCurry AddCommGrpCat.{u} ⋙
            ((evaluation SimplexCategoryᵒᵖ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).obj
              (op (SimplexCategory.mk n)) ⋙ presheafToSheaf J AddCommGrpCat.{u}))
      have hE := Functor.mapHomologicalComplexIso (ComplexShape.up ℤ)
        (baseChangedMooreSheafCochainCompEvalIso J θ n)
      have hcomp : QuasiIso ((((changeOfRings θ ⋙ mooreSheafCochain J O') ⋙
          HomologicalComplex.eval (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)
            ((ComplexShape.embeddingUpIntLE (0 : ℤ)).f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f ≫ hE.hom.app L) := by
        rw [hE.hom.naturality f]
        exact quasiIso_comp _ _
      exact quasiIso_of_comp_right ((((changeOfRings θ ⋙ mooreSheafCochain J O') ⋙
        HomologicalComplex.eval (Sheaf J AddCommGrpCat.{u}) (ComplexShape.up ℤ)
          ((ComplexShape.embeddingUpIntLE (0 : ℤ)).f n)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map f) (hE.hom.app L)
    · have hiso : ∀ p : ℤ, IsIso (((flipHom (((changeOfRings θ ⋙
          mooreSheafCochain J O').mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)).f q).f p) := fun p =>
        ⟨0, (isZero_baseChangedMooreSheafBicomplex_X_X J θ K p q hq).eq_of_src _ _,
          (isZero_baseChangedMooreSheafBicomplex_X_X J θ L p q hq).eq_of_src _ _⟩
      have : IsIso ((flipHom (((changeOfRings θ ⋙
          mooreSheafCochain J O').mapHomologicalComplex
            (ComplexShape.up ℤ)).map f)).f q) := HomologicalComplex.Hom.isIso_of_components _
      infer_instance

/-- **The instance of [Stacks, Tag 08RX] on `Δ × C` from the two filtrations.** Let
`L^• ⟶ F[0]` be a resolution of a presheaf of `O`-modules on `Δ × C` by standard covers. If the
base-change unit is a quasi-isomorphism at the structure module — the hypothesis `hθ`, which is
`s(O) ⟶ s(O')` and is the hypothesis of [Stacks, Tag 09D2] — and if base change takes the
resolution to a quasi-isomorphism on total complexes — the hypothesis `hrow`, which is where the
flatness of `F` is consumed — then the base-change unit is a quasi-isomorphism at `F`.

The proof is two applications of two out of three. The square

`Tot(Z) ⟶ Tot(Z')`, `Tot(Z) ⟶ Tot(W)`, `Tot(Z') ⟶ Tot(W')`

commutes by naturality of the unit, its top edge is the column filtration
(`Stacks.SimplicialModules.quasiIso_total_mooreSheafBicomplexBaseChangeMap_of_isStdCover`) and its
left edge the row filtration
(`Stacks.SimplicialModules.quasiIso_total_map_mooreSheafBicomplex`), so its bottom edge is a
quasi-isomorphism; and the bottom edge is the unit at `F`, read through the identification of the
total complex of a double complex concentrated in column zero with that column
(`StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit`) and Mathlib's comparison
`single ⋙ G.mapHomologicalComplex ≅ G ⋙ single`, which is natural in `G`
(`HomologicalComplex.singleMapHomologicalComplex_hom_naturality`). -/
theorem quasiIso_mooreSheafBaseChange_app_of_quasiIso_total_row
    (F : PresheafOfModules.{u} (ringPresheaf O))
    (L : CochainComplex (PresheafOfModules.{u} (ringPresheaf O)) ℤ) [L.IsStrictlyLE 0]
    (hL : ∀ p, PresheafOfModules.IsStdCover (L.X p))
    (π : L ⟶ (HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf O))
      (ComplexShape.up ℤ) 0).obj F) [QuasiIso π]
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' θ)))
    (hrow : QuasiIso (HomologicalComplex₂.total.map
      (((changeOfRings θ ⋙ mooreSheafCochain J O').mapHomologicalComplex
        (ComplexShape.up ℤ)).map π) (ComplexShape.up ℤ))) :
    QuasiIso ((mooreSheafBaseChange J θ).app F) := by
  let := hasTotal_singleColumn ((mooreSheafCochain J O).obj F) (0 : ℤ)
  let := hasTotal_singleColumn ((changeOfRings θ ⋙ mooreSheafCochain J O').obj F) (0 : ℤ)
  have hsq := (NatTrans.mapHomologicalComplex (mooreSheafBaseChange J θ)
    (ComplexShape.up ℤ)).naturality π
  have hcol : QuasiIso (HomologicalComplex₂.total.map
      (mooreSheafBicomplexBaseChangeMap J θ L) (ComplexShape.up ℤ)) :=
    quasiIso_total_mooreSheafBicomplexBaseChangeMap_of_isStdCover J θ hθ L hL
  have hrowL : QuasiIso (HomologicalComplex₂.total.map
      (((mooreSheafCochain J O).mapHomologicalComplex (ComplexShape.up ℤ)).map π)
      (ComplexShape.up ℤ)) := quasiIso_total_map_mooreSheafBicomplex J π
  have hbot : QuasiIso (HomologicalComplex₂.total.map
      ((NatTrans.mapHomologicalComplex (mooreSheafBaseChange J θ) (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single (PresheafOfModules.{u} (ringPresheaf O))
          (ComplexShape.up ℤ) 0).obj F))
      (ComplexShape.up ℤ)) := by
    refine (quasiIso_iff_comp_left (HomologicalComplex₂.total.map
      (((mooreSheafCochain J O).mapHomologicalComplex (ComplexShape.up ℤ)).map π)
      (ComplexShape.up ℤ)) _).1 ?_
    rw [← HomologicalComplex₂.total.map_comp, hsq, HomologicalComplex₂.total.map_comp]
    have := hrow
    exact quasiIso_comp _ _
  have hnat := HomologicalComplex.singleMapHomologicalComplex_hom_naturality
    (ComplexShape.up ℤ) 0 (mooreSheafBaseChange J θ) F
  have hiso₂ : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (changeOfRings θ ⋙ mooreSheafCochain J O') (ComplexShape.up ℤ) 0).hom.app F)
      (ComplexShape.up ℤ)) :=
    Stacks.ChaoticSite.ModuleValued.isIso_total_map_of_isIso _
  have hiso₁ : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreSheafCochain J O)
        (ComplexShape.up ℤ) 0).hom.app F) (ComplexShape.up ℤ)) :=
    Stacks.ChaoticSite.ModuleValued.isIso_total_map_of_isIso _
  have hsingle : QuasiIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.single (CochainComplex (Sheaf J AddCommGrpCat.{u}) ℤ)
        (ComplexShape.up ℤ) 0).map ((mooreSheafBaseChange J θ).app F))
      (ComplexShape.up ℤ)) := by
    refine (quasiIso_iff_comp_left (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreSheafCochain J O)
        (ComplexShape.up ℤ) 0).hom.app F) (ComplexShape.up ℤ)) _).1 ?_
    rw [← HomologicalComplex₂.total.map_comp, ← hnat, HomologicalComplex₂.total.map_comp]
    have := hbot
    exact quasiIso_comp _ _
  have hfin := Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso_hom_naturality
    ((mooreSheafBaseChange J θ).app F)
  refine (quasiIso_iff_comp_right ((mooreSheafBaseChange J θ).app F)
    (Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso
      ((changeOfRings θ ⋙ mooreSheafCochain J O').obj F)).hom).1 ?_
  rw [hfin]
  have := hsingle
  exact quasiIso_comp _ _

/-- **The instance of [Stacks, Tag 08RX] on the simplicial site `Δ × C` of [Stacks, Tag 09D0].**
Let `(C, J)` be a small site, let `θ : O ⟶ O'` be a homomorphism of presheaves of commutative
rings on `Δ × C` and suppose that `s(O) ⟶ s(O')` is a quasi-isomorphism of complexes of abelian
sheaves on `C` — the hypothesis of [Stacks, Tag 09D2], which is a sheaf-level condition and not a
fibrewise one. Then for every presheaf of `O`-modules `F` whose sections over each object of
`Δ × C` are a flat module, the base-change unit

`s(F) ⟶ s(F ⊗_O O')`

is a quasi-isomorphism.

The proof resolves `F` by standard covers
(`PresheafOfModules.exists_isStdCover_resolution`) and compares the two filtrations of the
resulting double complex: the columns are the base-change unit at a standard cover
(`Stacks.SimplicialModules.quasiIso_total_mooreSheafBicomplexBaseChangeMap_of_isStdCover`), the
rows on the unchanged side are exact functors
(`Stacks.SimplicialModules.quasiIso_total_map_mooreSheafBicomplex`) and the rows on the
base-changed side are flat base change
(`Stacks.SimplicialModules.quasiIso_total_map_baseChangedMooreSheafBicomplex`), which is where the
flatness of `F` is consumed. Nothing about the fibres of `O` or `O'` over an object of `C` is
assumed or used.

This is the statement the proof of [Stacks, Tag 09D2] reduces that lemma to after its first two
steps. It is **not** [Stacks, Tag 09D2] and carries no tag: 09D2 concludes for every object of
`D(A_•)`, not for a single flat module, and mentions `L π_!` and the derived tensor product. See
the module docstring. -/
theorem quasiIso_mooreSheafBaseChange_app_of_flat
    (F : PresheafOfModules.{u} (ringPresheaf O))
    (hF : ∀ X : (SimplexCategory × C)ᵒᵖ,
      Module.Flat ↥((ringPresheaf O).obj X) ↥(F.obj X))
    (hθ : QuasiIso ((mooreAbSheafCochain J).map (unitMap' θ))) :
    QuasiIso ((mooreSheafBaseChange J θ).app F) := by
  obtain ⟨L, π, hq, hP, hLE⟩ := PresheafOfModules.exists_isStdCover_resolution F
  have := hq
  have := hLE
  exact quasiIso_mooreSheafBaseChange_app_of_quasiIso_total_row J θ F L hP π hθ
    (quasiIso_total_map_baseChangedMooreSheafBicomplex J θ π
      (fun p X => PresheafOfModules.flat_obj_of_isStdCover (hP p) X)
      (fun p X => PresheafOfModules.flat_single_obj hF p X))

end Stacks.SimplicialModules

end
