module

public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Local freeness of a sheaf of modules is local on a covering family

Stacks 03DN asserts that each of the local conditions of Stacks 03DL may be tested on the
members of any family covering the final object.  This file proves the clause for local
freeness: a sheaf of modules on a ringed site is locally free exactly when its restrictions to
the members of some covering family are locally free on the localized ringed sites, and exactly
when those restrictions can be taken free.

Freeness here is `SheafOfModules.IsFree`, Stacks 03DE(1): the module is a coproduct of copies of
the structure sheaf indexed by an *arbitrary* type.  That is the only difference from the
companion file `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree`,
and it changes one step of the argument.  The comparison of the two readings of a module on an
iterated slice site is index free already: `Stacks.SheafOfModules.isColimitCofanTransport`
carries a cofan of copies of the structure sheaf along an equivalence of categories of sheaves
of modules at any index type.  The descent step is not: a *finite* coproduct of copies of the
structure sheaf is a biproduct and is therefore preserved by restriction for formal reasons,
whereas an arbitrary coproduct of sheaves of modules is a sheafification of the objectwise
coproduct, and its preservation by restriction is
`Stacks.SheafOfModules.overMap_preservesColimits`.

## Main results

* `Stacks.SheafOfModules.isLocallyFreeOnSite_iff_exists_cover_isLocallyFreeOnSite`: local
  freeness is equivalent to local freeness of the restrictions to the members of some covering
  family.  This is the equivalence of conditions (a) and (b) of Stacks 03DN for local freeness.
* `Stacks.SheafOfModules.isLocallyFreeOnSite_iff_exists_cover_isFree`: local freeness is
  equivalent to freeness of those restrictions.  This is the equivalence of conditions (a)
  and (c).
* `Stacks.SheafOfModules.isFree_over_of_le`: freeness of a sheaf of modules on a slice site is
  inherited by every smaller slice site, which is the descent step both equivalences rest on.

## Implementation notes

Local freeness is `SheafOfModules.IsLocallyFreeOnSite`, which is Stacks 03DL(1), freeness is
`SheafOfModules.IsFree`, which is Stacks 03DE(1), and the localized ringed site is
`AlgebraicGeometry.RingedSite.over`, which is Stacks 04IX; no notion is introduced here.

The statements carry the sheafification hypotheses of
`Stacks.SheafOfModules.overMap_preservesColimits`, in the form in which the clauses of
Stacks 03DN for local generation carry them: sheafification of presheaves of abelian groups on
each slice of the site, at the universe of the module sections, and the identification of its
equivalences with the local bijections.  They hold on every site whose objects and morphisms lie
below that universe, and are the hypotheses of that colimit-preservation statement rather than
restrictions on the module: Mathlib knows `SheafOfModules.overMap` to be a left adjoint only when
the site has pullbacks, so arbitrary coproducts travel along it only through sheafification.  The
companion clause for finite local freeness needs none of them, finite coproducts being
biproducts.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u v w t

section IteratedSlice

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Freeness of the restriction of `M` to `V.left` gives freeness of its restriction to the
iterated slice over `V`. -/
private theorem isFree_overOver (M : SheafOfModules.{w} R) (U : C) (V : Over U)
    (h : SheafOfModules.IsFree (M.over V.left)) :
    SheafOfModules.IsFree ((M.over U).over V) := by
  obtain ⟨B, ι, ⟨hc⟩⟩ := h
  exact ⟨B, _, ⟨isColimitCofanTransport (sliceEquiv R U V) (sliceEquivUnitIso R U V)
    (sliceEquivObjIso M U V) ι hc⟩⟩

/-- Freeness of the restriction of `M` to the iterated slice over `V` gives freeness of its
restriction to `V.left`. -/
private theorem isFree_overOver_symm (M : SheafOfModules.{w} R) (U : C) (V : Over U)
    (h : SheafOfModules.IsFree ((M.over U).over V)) :
    SheafOfModules.IsFree (M.over V.left) := by
  obtain ⟨B, ι, ⟨hc⟩⟩ := h
  let e := sliceEquiv R U V
  let η : e.symm.functor.obj (SheafOfModules.unit ((R.over U).over V)) ≅
      SheafOfModules.unit (R.over V.left) :=
    e.inverse.mapIso (sliceEquivUnitIso R U V).symm ≪≫
      (e.unitIso.app (SheafOfModules.unit (R.over V.left))).symm
  let ρ : e.symm.functor.obj ((M.over U).over V) ≅ M.over V.left :=
    e.inverse.mapIso (sliceEquivObjIso M U V).symm ≪≫ (e.unitIso.app (M.over V.left)).symm
  exact ⟨B, _, ⟨isColimitCofanTransport e.symm η ρ ι hc⟩⟩

end IteratedSlice

section Descent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction along `h : Z ⟶ Y` of a cofan exhibiting `F.over Y` as a coproduct of copies of
the structure sheaf, as a cofan exhibiting `F.over Z` as a coproduct of copies of the structure
sheaf indexed by the same type.

The index type is arbitrary, so the cofan is carried by colimit preservation of restriction
between slice sites and not, as in the finite case, by additivity. -/
noncomputable def isColimitCofanOverMap (F : SheafOfModules.{w} R) {Z Y : C} (h : Z ⟶ Y)
    {B : Type w} (ι : B → (SheafOfModules.unit (R.over Y) ⟶ F.over Y))
    (hc : IsColimit (Cofan.mk (F.over Y) ι)) :
    IsColimit (Cofan.mk (F.over Z)
      (fun b => (SheafOfModules.overMap R h).map (ι b) ≫
        ((SheafOfModules.overFunctorMap R h).app F).hom)) := by
  have : PreservesColimitsOfSize.{w, w} (SheafOfModules.overMap.{w} R h) :=
    overMap_preservesColimits R h
  refine IsColimit.ofIsoColimit
    (isColimitOfPreserves (SheafOfModules.overMap.{w} R h) hc)
    (Cocone.ext ((SheafOfModules.overFunctorMap R h).app F) ?_)
  rintro ⟨j⟩
  rfl

/-- **Freeness of a sheaf of modules on a slice site is inherited by every smaller slice
site.** -/
theorem isFree_over_of_le (F : SheafOfModules.{w} R) {Z Y : C} (h : Z ⟶ Y)
    (hF : SheafOfModules.IsFree (F.over Y)) : SheafOfModules.IsFree (F.over Z) := by
  obtain ⟨B, ι, ⟨hc⟩⟩ := hF
  exact ⟨B, _, ⟨isColimitCofanOverMap F h ι hc⟩⟩

/-- **Freeness on a family covering the final object gives freeness on a covering family of
every object.** If a family of objects `Y` covers the final object and the restriction of `F` to
each `Y i` is free, then every object `W` carries a covering family of arrows on whose sources
the restriction of `F` is free.

The sieve produced is `Sieve.ofArrows V f`, and it is covering because it contains
`Sieve.ofObjects Y W`. -/
theorem exists_cover_isFree_of_coversTop {I : Type t} (Y : I → C) (hY : J.CoversTop Y)
    (F : SheafOfModules.{w} R) (hF : ∀ i, SheafOfModules.IsFree (F.over (Y i))) (W : C) :
    ∃ (I' : Type (max u v)) (V : I' → C) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ J W ∧ ∀ i, SheafOfModules.IsFree (F.over (V i)) := by
  refine ⟨Σ Z : C, { g : Z ⟶ W // (Sieve.ofObjects Y W).arrows g }, fun x => x.1,
    fun x => x.2.1, ?_, ?_⟩
  · refine J.superset_covering ?_ (hY W)
    intro Z g hg
    exact Sieve.ofArrows_mk _ _ (⟨Z, g, hg⟩ : Σ Z : C, { g : Z ⟶ W // _ })
  · rintro ⟨Z, g, i, ⟨h⟩⟩
    exact isFree_over_of_le F h (hF i)

end Descent

section RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03DN, local freeness.** A sheaf of modules on a ringed site is locally free if and
only if its restriction to each member of some covering family of the final object is locally
free on the corresponding localized ringed site. -/
@[stacks 03DN "locally_free"]
theorem isLocallyFreeOnSite_iff_exists_cover_isLocallyFreeOnSite :
    SheafOfModules.IsLocallyFreeOnSite F ↔
      ∃ (I : Type (max u v)) (U : I → X.C), X.J.CoversTop U ∧
        ∀ i : I, SheafOfModules.IsLocallyFreeOnSite
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (X.over (U i)).O) (F.over (U i)) := by
  constructor
  · intro hF
    rw [SheafOfModules.isLocallyFreeOnSite_iff_isFree] at hF
    refine ⟨ULift.{max u v} X.C, fun i => i.down, coversTop_ulift_self X.J,
      fun i => (SheafOfModules.isLocallyFreeOnSite_iff_isFree _).mpr fun W => ?_⟩
    obtain ⟨I, V, f, hcov, hfree⟩ := hF W.left
    refine ⟨I, (fun j => Over.mk (f j ≫ W.hom)), (fun j => Over.homMk (f j) (by simp)), ?_,
      fun j => isFree_overOver F _ (Over.mk (f j ≫ W.hom)) (hfree j)⟩
    show Sieve.ofArrows (fun j => Over.mk (f j ≫ W.hom))
      (fun j => Over.homMk (f j) (by simp)) ∈ (X.J.over i.down) W
    rw [GrothendieckTopology.mem_over_iff]
    simpa [Sieve.overEquiv, Sieve.functorPushforward_ofArrows] using hcov
  · rintro ⟨I, U, hU, hlocal⟩
    choose I' V f hcov hfree using fun i : I =>
      (SheafOfModules.isLocallyFreeOnSite_iff_isFree _).mp (hlocal i) (Over.mk (𝟙 (U i)))
    have hcovBase : ∀ i, Sieve.ofArrows (fun j => (V i j).left)
        (fun j => (V i j).hom) ∈ X.J (U i) := by
      intro i
      have heq : ∀ j, (f i j).left = (V i j).hom := fun j => by simpa using Over.w (f i j)
      simpa [Sieve.overEquiv, Sieve.functorPushforward_ofArrows, heq] using
        (GrothendieckTopology.mem_over_iff (J := X.J) (S := Sieve.ofArrows (V i) (f i))).mp
          (hcov i)
    have hW : X.J.CoversTop (fun ij : (Σ i, I' i) => (V ij.1 ij.2).left) :=
      hU.over fun i => coversTop_over_of_ofArrows_mem X.J (U i) (fun j => (V i j).left)
        (fun j => (V i j).hom) (hcovBase i)
    exact (SheafOfModules.isLocallyFreeOnSite_iff_isFree F).mpr fun W =>
      exists_cover_isFree_of_coversTop _ hW F
        (fun ij => isFree_overOver_symm F (U ij.1) (V ij.1 ij.2) (hfree ij.1 ij.2)) W

/-- **Stacks 03DN, local freeness.** A sheaf of modules on a ringed site is locally free if and
only if its restriction to each member of some covering family of the final object is free. -/
@[stacks 03DN "locally_free"]
theorem isLocallyFreeOnSite_iff_exists_cover_isFree :
    SheafOfModules.IsLocallyFreeOnSite F ↔
      ∃ (I : Type (max u v)) (U : I → X.C), X.J.CoversTop U ∧
        ∀ i : I, SheafOfModules.IsFree (F.over (U i)) := by
  refine ⟨fun hF => ?_, fun ⟨I, U, hU, hfree⟩ =>
    (SheafOfModules.isLocallyFreeOnSite_iff_isFree F).mpr fun W =>
      exists_cover_isFree_of_coversTop U hU F hfree W⟩
  rw [SheafOfModules.isLocallyFreeOnSite_iff_isFree] at hF
  choose I V f hcov hfree using fun i : ULift.{max u v} X.C => hF i.down
  have hslice : ∀ i : ULift.{max u v} X.C,
      (X.J.over i.down).CoversTop (fun j => Over.mk (f i j)) := fun i =>
    coversTop_over_of_ofArrows_mem X.J i.down (V i) (f i) (hcov i)
  exact ⟨(Σ i, I i), fun ij => V ij.1 ij.2, (coversTop_ulift_self X.J).over hslice,
    fun ij => hfree ij.1 ij.2⟩

end RingedSite

end Stacks.SheafOfModules

end
