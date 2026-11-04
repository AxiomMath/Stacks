module

public import StacksFrontier.AlgebraicGeometry.DenominatorIdealQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealSupport.Basic

/-!
# The denominator ideal as affine-local ideal-sheaf data

`AlgebraicGeometry.Scheme.IdealSheafData` presents an ideal sheaf by its ideals on the affine
opens, subject to compatibility with passage to a basic open, and
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals` is the largest ideal sheaf contained in a
given family of ideals.  This file shows that for a **quasi-coherent** submodule of the structure
sheaf, `ofIdeals` applied to the family of its sections does not shrink it — the family already
satisfies the compatibility condition, because quasi-coherence says exactly that the sections
over a basic open are the localization of the sections over the affine open.

Applied to the denominator ideal of a meromorphic section of an invertible sheaf, whose
quasi-coherence is `Stacks.DenominatorIdealQcoh.denominatorIdeal_isQuasicoherent`, this gives the
two remaining assertions of Stacks Tag 02P0 about the ideal-sheaf presentation: that the ideal on
each affine open is the denominator ideal there, and that its support is nowhere dense.

## Main results

* `Stacks.DenominatorIdealQcoh.map_rangeFamily_basicOpen`: for quasi-coherent `N`, the family of
  images of its sections on the affine opens is compatible with passage to a basic open.
* `Stacks.DenominatorIdealQcoh.ideal_ofIdeals_rangeFamily`: hence `ofIdeals` recovers that family
  exactly.
* `Stacks.DenominatorIdealQcoh.isNowhereDense_support_of_nhds`: an ideal sheaf whose ideal
  contains a nonzerodivisor on *some* affine open around every point of every open set has
  nowhere dense support.
* `Stacks.DenominatorIdealQcoh.denominatorIdealData_ideal`: **on each affine open the
  ideal-sheaf data of the denominator ideal are exactly the denominators.**
* `Stacks.DenominatorIdealQcoh.denominatorIdealData_support_isNowhereDense`: **its support is
  nowhere dense.**

## Implementation notes

`Stacks.IdealSheafSupport.isNowhereDense_support` asks for a nonzerodivisor in the ideal at
*every* affine open, and a meromorphic section does not supply one there: `Γ(K_X, U)` is a
sheafification and need not consist of single fractions even for affine `U`, so there is no
global denominator over an arbitrary affine open.  What
`Stacks.DenominatorLocalRatio.exists_affineOpen_denominator` supplies is a denominator on
*arbitrarily small* affine opens, and that is enough: the nowhere-density argument chooses the
affine open it runs on, inside the interior of the support.  `isNowhereDense_support_of_nhds` is
that argument with the hypothesis weakened accordingly; its two ingredients,
`Stacks.IdealSheafSupport.eq_bot_of_subset_zeroLocus` and
`AlgebraicGeometry.Scheme.IdealSheafData.supportSet_subset_zeroLocus`, are unchanged.

The compatibility proof uses only one direction of quasi-coherence non-trivially: a section over
the basic open becomes, after multiplication by an element of the denominator submonoid, the
restriction of a section over the affine open, and that element is a unit downstairs, so the
section lies in the image ideal.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorColonIdeal Stacks.DenominatorLocalRatio
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.DenominatorIdealQcoh

variable (X : Scheme.{u})

/-! ### Ideal-sheaf data from a quasi-coherent submodule of the structure sheaf -/

/-- The family of ideals cut out on the affine opens by a module equipped with a map to the
structure sheaf: the image of its sections there. -/
def rangeFamily (N : X.Modules) (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.affineOpens) : Ideal Γ(X, U.1) :=
  LinearMap.range (inclₗ X N ι U.1)

/-- The ideal `rangeFamily X N ι U` is the range of the ring-level map on sections of `ι` over
`U`. -/
lemma rangeFamily_eq_hom_range (N : X.Modules) (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.affineOpens) :
    rangeFamily X N ι U = ((ι.val.app (op U.1)).hom.range : Ideal Γ(X, U.1)) := rfl

/-- **For a quasi-coherent `N`, the family of ideals cut out on the affine opens is compatible
with passage to a basic open.**  This is the one condition `Scheme.IdealSheafData` asks of a
family of ideals, and it is exactly the statement that the sections of `N` over `X.basicOpen f`
are the localization of its sections over the affine open away from `f`, which quasi-coherence
supplies. -/
theorem map_rangeFamily_basicOpen (N : X.Modules) (hqc : N.IsQuasicoherent)
    (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.affineOpens) (f : Γ(X, U.1)) :
    (rangeFamily X N ι U).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      rangeFamily X N ι (X.affineBasicOpen f) := by
  have := hqc
  let := moduleOfLE N (X.basicOpen_le f)
  have hloc : IsLocalizedModule.Away f (restrictₗ N (X.basicOpen_le f)) :=
    isLocalizedModule_restrictₗ N U.2 f rfl (X.basicOpen_le f)
  have halg : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) := rfl
  rw [halg]
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr ?_) ?_
  · rintro y ⟨d, rfl⟩
    exact ⟨restrictₗ N (X.basicOpen_le f) d, inclBasicOpenₗ_restrictₗ X N ι f d⟩
  · intro y hy
    obtain ⟨e, rfl⟩ : ∃ e : Γ(N, X.basicOpen f), inclₗ X N ι (X.basicOpen f) e = y :=
      LinearMap.mem_range.mp hy
    obtain ⟨⟨d, c⟩, hd⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (restrictₗ N (X.basicOpen_le f)) e
    have hd' : (c : Γ(X, U.1)) • e = restrictₗ N (X.basicOpen_le f) d := hd
    have h1 : inclBasicOpenₗ X N ι f ((c : Γ(X, U.1)) • e) =
        (c : Γ(X, U.1)) • inclBasicOpenₗ X N ι f e :=
      map_smul (inclBasicOpenₗ X N ι f) (c : Γ(X, U.1)) e
    have h2 : inclBasicOpenₗ X N ι f (restrictₗ N (X.basicOpen_le f) d) =
        algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (inclₗ X N ι U.1 d) :=
      inclBasicOpenₗ_restrictₗ X N ι f d
    have key : (c : Γ(X, U.1)) • inclBasicOpenₗ X N ι f e =
        algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (inclₗ X N ι U.1 d) := by
      rw [← h1, hd', h2]
    have hu : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (c : Γ(X, U.1))) := by
      have := U.2.isLocalization_basicOpen f
      exact IsLocalization.map_units (M := Submonoid.powers f) _ c
    obtain ⟨w, hw⟩ := hu
    have hy : inclBasicOpenₗ X N ι f e = ((w⁻¹ : Γ(X, X.basicOpen f)ˣ) : Γ(X, X.basicOpen f)) *
        algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (inclₗ X N ι U.1 d) := by
      rw [← key, Algebra.smul_def, ← hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [show inclₗ X N ι (X.basicOpen f) e = inclBasicOpenₗ X N ι f e from rfl, hy]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ⟨d, rfl⟩)

/-- The ideal-sheaf data of a quasi-coherent submodule of the structure sheaf: its sections on
each affine open. -/
def rangeIdealSheafData (N : X.Modules) (hqc : N.IsQuasicoherent)
    (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf) : X.IdealSheafData where
  ideal := rangeFamily X N ι
  map_ideal_basicOpen := map_rangeFamily_basicOpen X N hqc ι

/-- **The largest ideal sheaf contained in the ideals of a quasi-coherent submodule of the
structure sheaf has exactly those ideals.**  `Scheme.IdealSheafData.ofIdeals` is a supremum and
in general shrinks the family it is applied to; here it does not, because the family is already
an ideal sheaf. -/
theorem ideal_ofIdeals_rangeFamily (N : X.Modules) (hqc : N.IsQuasicoherent)
    (ι : N ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.IdealSheafData.ofIdeals (rangeFamily X N ι)).ideal = rangeFamily X N ι := by
  have h : Scheme.IdealSheafData.ofIdeals (rangeFamily X N ι) = rangeIdealSheafData X N hqc ι :=
    Scheme.IdealSheafData.ofIdeals_ideal (rangeIdealSheafData X N hqc ι)
  rw [h]
  rfl

/-! ### Nowhere density from arbitrarily small affine opens -/

/-- **An ideal sheaf whose ideal contains a nonzerodivisor on some affine open around every point
of every open set has nowhere dense support.**  This weakens the hypothesis of
`Stacks.IdealSheafSupport.isNowhereDense_support` from *every* affine open to *arbitrarily small*
affine opens, which is all its argument uses: the affine open it runs on is produced inside the
interior of the support and may be shrunk freely.  That is the form in which a meromorphic
section supplies a denominator — only near each point. -/
theorem isNowhereDense_support_of_nhds (I : X.IdealSheafData)
    (h : ∀ (W : Opens X) (x : X), x ∈ W → ∃ V : Opens X, V ≤ W ∧ x ∈ V ∧
      ∃ hV : IsAffineOpen V, ∃ b ∈ I.ideal ⟨V, hV⟩, b ∈ nonZeroDivisors Γ(X, V)) :
    IsNowhereDense (I.support : Set X) := by
  have hcl : IsClosed (I.support : Set X) := I.isClosed_supportSet
  rw [hcl.isNowhereDense_iff, Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨V, hVsub, hxV, hV, b, hbI, hb⟩ :=
    h ⟨interior (I.support : Set X), isOpen_interior⟩ x hx
  have hsub : ((⟨V, hV⟩ : X.affineOpens).1 : Set X) ⊆
      X.zeroLocus (U := (⟨V, hV⟩ : X.affineOpens).1) (I.ideal ⟨V, hV⟩) := fun y hy =>
    I.supportSet_subset_zeroLocus ⟨V, hV⟩ (interior_subset (hVsub hy))
  have hVbot : V = ⊥ :=
    Stacks.IdealSheafSupport.eq_bot_of_subset_zeroLocus ⟨V, hV⟩ hbI hb hsub
  simp only [hVbot] at hxV
  exact hxV

/-! ### The denominator ideal -/

variable (L : SheafOfModules.{u} (O X)) (s : MeromorphicSection.{u, u} X.sheaf L)

/-- **The denominator ideal as affine-local ideal-sheaf data, usable for blowups.**  This is the
largest ideal sheaf whose ideal on each affine open is contained in the denominators there. -/
def denominatorIdealData : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U : X.affineOpens =>
    ((denominatorIdealι X L s).val.app (op U.1)).hom.range

/-- **On each affine open the ideal-sheaf data are exactly the denominators.**

`Scheme.IdealSheafData.ofIdeals` is a supremum and in general shrinks the family of ideals it is
applied to; it does not here, because quasi-coherence of the denominator ideal makes that family
compatible with passage to a basic open, so it is already an ideal sheaf. -/
@[stacks 02P0 "affine denominator ideal"]
theorem denominatorIdealData_ideal
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L)
    (U : X.affineOpens) :
    (denominatorIdealData X L s).ideal U =
      ((denominatorIdealι X L s).val.app (op U.1)).hom.range :=
  congrFun (ideal_ofIdeals_rangeFamily X (denominatorIdeal X L s)
    (denominatorIdeal_isQuasicoherent X L s hL) (denominatorIdealι X L s)) U

/-- **The closed support of the denominator ideal is nowhere dense.**

Around every point of every open set there is an affine open carrying a nonzerodivisor `b` which
is a denominator of `s`, so `(b) ⊆ I` there and the support is contained in `V(b)`, which has
empty interior.  Shrinking freely is legitimate because the nowhere-density argument runs on an
affine open of its own choosing inside the interior of the support. -/
@[stacks 02P0 "support of the denominator ideal"]
theorem denominatorIdealData_support_isNowhereDense
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf (O X).property L) :
    IsNowhereDense ((denominatorIdealData X L s).support : Set X) := by
  refine isNowhereDense_support_of_nhds X _ fun W x hx => ?_
  obtain ⟨V, hVW, hxV, hVaff, -, b, hb, t, hbt⟩ :=
    Stacks.DenominatorLocalRatio.exists_affineOpen_denominator X L s hL W x hx
  refine ⟨V, hVW, hxV, hVaff, b, ?_, hb⟩
  rw [denominatorIdealData_ideal X L s hL ⟨V, hVaff⟩]
  exact (denominatorIdeal_sections X L s V b).mpr ⟨t, hbt.symm⟩

end Stacks.DenominatorIdealQcoh

end
