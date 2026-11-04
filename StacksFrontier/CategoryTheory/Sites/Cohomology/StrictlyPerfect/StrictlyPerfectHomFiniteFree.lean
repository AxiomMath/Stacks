module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08JH at the hypothesis of Stacks 08FL

`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso` — Stacks 08JH — is stated with
strict perfectness spelled as boundedness together with
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand` on every term: being a retract of
`O^{⊕r} = unitPower X r`. That spelling is chosen because it is the one the comparison's proof
uses; `IsStrictlyPerfect`, the predicate which carries the Stacks 08FL tag, asks instead that
every term be a direct summand of a finite free module.

This file closes that gap, so that the generalisation is *checked* rather than asserted. It
proves `O^{⊕r}` agrees with the direct sum over `Fin r`, that a retract of
`SheafOfModules.free I` for a finite `I` is an `IsFiniteFreeSummand`, and Stacks 08JH under the
hypothesis `IsStrictlyPerfect X.ringSheaf E` itself, at the diagonal `RingedSite.{u, u, u}`
where the internal Hom complex of Stacks 0A8Z lives.

Nothing in the library depends on this file; it is a certificate.

## Main definitions

* `AlgebraicGeometry.RingedSite.finSuccBicone`: the bicone exhibiting `A^{⊕r} ⊞ A` as the
  biproduct of `r + 1` copies of `A`.
* `AlgebraicGeometry.RingedSite.biproductFinSuccIso`: `A^{⊕(r+1)} ≅ A^{⊕r} ⊞ A`.
* `AlgebraicGeometry.RingedSite.unitPowerIsoBiproduct`: the iterated binary biproduct
  `unitPower X r` agrees with `⨁ (fun _ : Fin r => O)`.

## Main results

* `AlgebraicGeometry.RingedSite.isFiniteFreeSummand_iff_retract_biproduct`.
* `AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_retract_free`: the bridge to the
  free-module spelling of Stacks 08FL.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_isStrictlyPerfect`:
  Stacks 08JH from `IsStrictlyPerfect`.
* `AlgebraicGeometry.RingedSite.IsDirectSummandOfFiniteFree.isFiniteFreeSummand`: the termwise
  half of the comparison.

## Implementation notes

Mathlib has no reindexing of a `Fin (r + 1)`-indexed biproduct as a binary biproduct, so
`finSuccBicone` builds the bicone by hand and `Limits.isBilimitOfTotal` checks it; the total
condition splits by `Fin.sum_univ_castSucc` into `biproduct.total` and `biprod.total`. The one
transparency configuration in this file, `rw (transparency := .default)` on
`Preadditive.comp_sum` and `Preadditive.sum_comp`, is there because the ambient type of the sum
is `(finSuccBicone A r).pt`, which is only definitionally the binary biproduct, so `rw` at
`reducible` transparency builds an ill-typed motive.

The free-module comparison is uniqueness of coproducts: `SheafOfModules.isColimitFreeCofan`
says `SheafOfModules.free I` is the coproduct of `I` copies of `SheafOfModules.unit`, and
`Limits.biproduct.isColimit` says the biproduct is too.

`strictlyPerfectHomComparison_isIso_of_isStrictlyPerfect` is at the diagonal
`RingedSite.{u, u, u}`, free in `u`: `strictlyPerfectHomComparison` ties all three universes of
the ringed site together, and `IsStrictlyPerfect X.ringSheaf` ties the sections of the modules
to those of the structure sheaf, so the diagonal is forced but its value is not. An earlier
version of this file stated it at the value `0` and recorded that as forced; that was wrong —
`IsStrictlyPerfect` is defined at `RingedSite.{u, v, w}` with modules in `SheafOfModules.{m}`
(`StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism`) and is used at
the free diagonal elsewhere in this chapter. The statement carries no `@[stacks 08JH]`
attribute — the tag belongs on the universe-polymorphic `strictlyPerfectHomComparison_isIso`, of
which this is an instance.

The `RingedSite.{0, 0, 0}` form of the termwise half that used to live in the
`StrictPerfectness` section below has been retired: once the section is universe-general it is
`IsDirectSummandOfFiniteFree.isFiniteFreeSummand` verbatim, and nothing outside this file used
it.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe u d

namespace AlgebraicGeometry.RingedSite
section Bicone

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] (A : C) (r : ℕ)

/-- The bicone exhibiting `(⨁_{Fin r} A) ⊞ A` as the biproduct of `r + 1` copies of `A`. -/
def finSuccBicone : Bicone (fun _ : Fin (r + 1) => A) :=
  { pt := (⨁ fun _ : Fin r => A) ⊞ A
    π := Fin.lastCases biprod.snd (fun a => biprod.fst ≫ biproduct.π (fun _ : Fin r => A) a)
    ι := Fin.lastCases biprod.inr (fun a => biproduct.ι (fun _ : Fin r => A) a ≫ biprod.inl)
    ι_π := by
      intro j j'
      induction j using Fin.lastCases with
      | last =>
        induction j' using Fin.lastCases with
        | last => simp
        | cast b =>
          have hne : Fin.last r ≠ b.castSucc := (Fin.castSucc_lt_last b).ne'
          simp [hne]
      | cast a =>
        induction j' using Fin.lastCases with
        | last =>
          have hne : a.castSucc ≠ Fin.last r := (Fin.castSucc_lt_last a).ne
          simp [hne]
        | cast b =>
          rcases eq_or_ne a b with rfl | h
          · simp
          · simp [(Fin.castSucc_injective r).ne h, biproduct.ι_π_ne _ h] }

/-- The projection of `finSuccBicone A r` at `a.castSucc` is `biprod.fst` followed by the `a`-th
projection of `⨁_{Fin r} A`. -/
@[simp] lemma finSuccBicone_π_castSucc (a : Fin r) :
    (finSuccBicone A r).π a.castSucc = biprod.fst ≫ biproduct.π (fun _ : Fin r => A) a := by
  simp [finSuccBicone]

/-- The projection of `finSuccBicone A r` at `Fin.last r` is `biprod.snd`. -/
@[simp] lemma finSuccBicone_π_last :
    (finSuccBicone A r).π (Fin.last r) = biprod.snd := by
  simp [finSuccBicone]

/-- The inclusion of `finSuccBicone A r` at `a.castSucc` is the `a`-th inclusion into `⨁_{Fin r} A`
followed by `biprod.inl`. -/
@[simp] lemma finSuccBicone_ι_castSucc (a : Fin r) :
    (finSuccBicone A r).ι a.castSucc = biproduct.ι (fun _ : Fin r => A) a ≫ biprod.inl := by
  simp [finSuccBicone]

/-- The inclusion of `finSuccBicone A r` at `Fin.last r` is `biprod.inr`. -/
@[simp] lemma finSuccBicone_ι_last :
    (finSuccBicone A r).ι (Fin.last r) = biprod.inr := by
  simp [finSuccBicone]

/-- The bicone of `finSuccBicone` is a biproduct. -/
def finSuccBiconeIsBilimit : (finSuccBicone A r).IsBilimit := by
  apply isBilimitOfTotal
  rw [Fin.sum_univ_castSucc, finSuccBicone_π_last, finSuccBicone_ι_last]
  have h : ∀ a : Fin r, (finSuccBicone A r).π a.castSucc ≫ (finSuccBicone A r).ι a.castSucc =
      biprod.fst ≫ (biproduct.π (fun _ : Fin r => A) a ≫
        biproduct.ι (fun _ : Fin r => A) a) ≫ biprod.inl := by
    intro a
    rw [finSuccBicone_π_castSucc, finSuccBicone_ι_castSucc]
    exact (Category.assoc _ _ _).trans
      (congrArg (fun z => biprod.fst ≫ z) (Category.assoc _ _ _)).symm
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  rw (transparency := .default) [← Preadditive.comp_sum, ← Preadditive.sum_comp]
  rw [biproduct.total, Category.id_comp]
  exact biprod.total

/-- `A^{⊕(r+1)} ≅ A^{⊕r} ⊞ A`. -/
def biproductFinSuccIso :
    (⨁ fun _ : Fin (r + 1) => A) ≅ (⨁ fun _ : Fin r => A) ⊞ A :=
  (biproduct.uniqueUpToIso _ (finSuccBiconeIsBilimit A r)).symm

omit [HasBinaryBiproducts C] in
/-- `A^{⊕0}` is zero. -/
lemma isZero_biproduct_fin_zero : IsZero (⨁ fun _ : Fin 0 => A) :=
  (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun i => i.elim0)

end Bicone

section Compare

variable (X : RingedSite.{u, u, u})

attribute [local instance] hasFiniteBiproducts_sheafOfModules

/-- `O^{⊕r}` written as an iterated binary biproduct agrees with the direct sum over `Fin r`. -/
def unitPowerIsoBiproduct (r : ℕ) :
    unitPower X r ≅
      ⨁ fun _ : Fin r => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := by
  induction r with
  | zero =>
    exact (isZero_zero _).iso
      (isZero_biproduct_fin_zero (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  | succ r e =>
    exact (biprod.mapIso e (Iso.refl _)).trans
      (biproductFinSuccIso
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) r).symm

/-- Being a direct summand of a finite free `O`-module can equivalently be tested against the
direct sum `O^{⊕r}` over `Fin r`. -/
theorem isFiniteFreeSummand_iff_retract_biproduct
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsFiniteFreeSummand X M ↔ ∃ r : ℕ, Nonempty (Retract M
      (⨁ fun _ : Fin r => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  ⟨fun ⟨r, ⟨ρ⟩⟩ => ⟨r, ⟨ρ.trans (unitPowerIsoBiproduct X r).retract⟩⟩,
    fun ⟨r, ⟨ρ⟩⟩ => ⟨r, ⟨ρ.trans (unitPowerIsoBiproduct X r).symm.retract⟩⟩⟩

/-- A retract of a finite free `O`-module `SheafOfModules.free I` is a direct summand of a
finite free `O`-module in the sense of `IsFiniteFreeSummand`.

This is the bridge to the Stacks 08FL condition: `IsDirectSummandOfFiniteFree R M` is, by
`isDirectSummandOfFiniteFree_iff_free`, the existence of maps
`M ⟶ SheafOfModules.free (ULift (Fin n))` and back composing to the identity, which is exactly a
`Retract M (SheafOfModules.free (ULift (Fin n)))`. -/
theorem isFiniteFreeSummand_of_retract_free
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (I : Type u) [Finite I]
    (ρ : Retract M (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I)) :
    IsFiniteFreeSummand X M := by
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfree : SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I ≅
      ⨁ fun _ : Fin r => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    (IsColimit.coconePointUniqueUpToIso
        (SheafOfModules.isColimitFreeCofan (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) I)
        (biproduct.isColimit fun _ : I =>
          SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).trans
      (biproduct.whiskerEquiv
        (f := fun _ : I => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (g := fun _ : Fin r => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        e fun _ => Iso.refl _)
  exact (isFiniteFreeSummand_iff_retract_biproduct X M).2 ⟨r, ⟨ρ.trans hfree.retract⟩⟩

/-- **The Stacks 08FL termwise condition implies `IsFiniteFreeSummand`, at an arbitrary
universe.** This is the `RingedSite.{u, u, u}` form of
`AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_isDirectSummandOfFiniteFree`, which is
stated at `RingedSite.{0, 0, 0}` because the whole of `IsStrictlyPerfect` is written there.
Nothing of the universe restriction is needed for the termwise condition: the substance is
`AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_retract_free`, which is general, and
`isDirectSummandOfFiniteFree_iff_free` holds whenever the sections of the modules and of the
structure sheaf lie in the same universe, as they do here. -/
theorem IsDirectSummandOfFiniteFree.isFiniteFreeSummand (X : RingedSite.{u, u, u})
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [X.J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    {M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hM : IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) :
    IsFiniteFreeSummand X M := by
  obtain ⟨n, i, r, hir⟩ :=
    (isDirectSummandOfFiniteFree_iff_free (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M).1 hM
  exact isFiniteFreeSummand_of_retract_free X (ULift.{u} (Fin n)) ⟨i, r, hir⟩

end Compare

section StrictPerfectness

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 08JH under the hypothesis `IsStrictlyPerfect` itself**, at an arbitrary universe of
the sections.  The termwise half is `IsDirectSummandOfFiniteFree.isFiniteFreeSummand`. -/
theorem strictlyPerfectHomComparison_isIso_of_isStrictlyPerfect
    [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (D : DerivedInternalHom.{u, d} X)
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) E) :
    IsIso (strictlyPerfectHomComparison X D E F) :=
  strictlyPerfectHomComparison_isIso X D E F hE.bounded
    (fun i => IsDirectSummandOfFiniteFree.isFiniteFreeSummand X (hE.termDirectSummand i))

end StrictPerfectness

end AlgebraicGeometry.RingedSite

end
