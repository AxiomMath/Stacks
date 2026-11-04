module

public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.DenominatorIdealQcoh.IdealData
public import StacksFrontier.AlgebraicGeometry.IdealSheafFiniteType.Basic

/-!
# The blowup in the ideal of denominators is admissible

Let `X` be a locally Noetherian scheme, `L` an invertible `𝒪_X`-module and `s` a regular
meromorphic section of `L`.  Let `U ⊆ X` be the maximal open subscheme such that `s` corresponds
to a section of `L` over `U`.  The blowup of `X` in the ideal of denominators of `s` is then
`U`-admissible.

## Main definitions

* `Stacks.DenominatorBlowup.IsSectionOver`: the predicate "`s` corresponds to a section of `L`
  over `V`", i.e. the restriction of `s` to `V` lies in the image of `L(V) ⟶ K_X(L)(V)`.
* `Stacks.DenominatorBlowup.sectionOpens`: the open subscheme `U` of the source, defined as the
  supremum of the open sets over which `s` corresponds to a section of `L`.

## Main results

* `Stacks.DenominatorBlowup.isSectionOver_iff_one_mem_range`: `s` corresponds to a section of
  `L` over `V` exactly when `1` is a denominator of `s` on `V`.
* `Stacks.DenominatorBlowup.ideal_denominatorIdealData_eq_top_iff`: on an affine open the ideal
  of denominators is the unit ideal exactly when `s` corresponds to a section of `L` there.
* `Stacks.DenominatorBlowup.sectionOpens_eq_compl_support`: `U` is the complement of the support
  of the ideal of denominators.
* `Stacks.DenominatorBlowup.sectionOpens_eq_top_iff`: `U` is the whole scheme exactly when the
  centre of the blowup has empty support.
* `Stacks.DenominatorBlowup.isAdmissibleBlowup_denominatorIdealData`: **the blowup in the ideal
  of denominators is `U`-admissible**, the first assertion of Stacks Tag 0ESL.
* `Stacks.DenominatorBlowup.isAdmissibleBlowup_denominatorIdealData'`: the same for an arbitrary
  meromorphic section `s`.

## Implementation notes

The ideal of denominators is `Stacks.DenominatorIdealQcoh.denominatorIdealData`, the sheaf of
denominators of Stacks Tag 02P1 presented as `AlgebraicGeometry.Scheme.IdealSheafData`, which is
the form the blowup consumes.

`U` is *defined* here as the supremum of the open sets on which `s` is a section. That it is a
maximum, i.e. that `s` is itself a section of `L` over `U`, is
`Stacks.DenominatorBlowup.isSectionOver_sectionOpens`.

## References

* [Stacks Project, Tag 0ESL](https://stacks.math.columbia.edu/tag/0ESL)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P1](https://stacks.math.columbia.edu/tag/02P1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.DenominatorIdeal Stacks.DenominatorIdealQcoh

universe u

namespace Stacks.DenominatorBlowup

variable {X : Scheme.{u}} (L : SheafOfModules.{u} (Stacks.DenominatorIdeal.O X))
  (s : MeromorphicSection.{u, u} X.sheaf L)

/-- **`s` corresponds to a section of `L` over `V`.**  The restriction of the meromorphic
section `s` to `V` lies in the image of the canonical map `L(V) ⟶ K_X(L)(V)`. -/
def IsSectionOver (V : Opens X) : Prop :=
  ∃ t : L.val.obj (op V), (toK X L).val.app (op V) t = s.val (op V)

/-- If `s` corresponds to a section of `L` over `V`, it does so over any smaller open set. -/
theorem IsSectionOver.mono {V W : Opens X} (h : W ≤ V) (hV : IsSectionOver L s V) :
    IsSectionOver L s W := by
  obtain ⟨t, ht⟩ := hV
  refine ⟨L.val.map (homOfLE h).op t, ?_⟩
  rw [PresheafOfModules.naturality_apply (toK X L).val (homOfLE h).op t, ht]
  exact s.2 (homOfLE h).op

/-- **The maximal open subscheme over which `s` corresponds to a section of `L`,** defined as the
supremum of the open sets with that property.  By
`Stacks.DenominatorBlowup.sectionOpens_eq_compl_support` it is the complement of the support of
the ideal of denominators of `s`. -/
def sectionOpens : Opens X := sSup {V | IsSectionOver L s V}

/-- Every open set over which `s` corresponds to a section of `L` is contained in
`Stacks.DenominatorBlowup.sectionOpens`. -/
theorem le_sectionOpens {V : Opens X} (hV : IsSectionOver L s V) : V ≤ sectionOpens L s :=
  le_sSup hV

/-- Multiplication by `s`, applied to the section `1` of the structure sheaf over `V`, is the
restriction of `s` to `V`. -/
theorem sectionMap_app_one (V : Opens X) :
    (sectionMap X L s).val.app (op V)
        (1 : (Stacks.DenominatorIdeal.O X).obj.obj (op V)) = s.val (op V) :=
  congrArg (fun σ : (kAsOModule X L).sections => σ.val (op V))
    ((kAsOModule X L).unitHomEquiv.apply_symm_apply s)

/-- **`s` corresponds to a section of `L` over `V` exactly when `1` is a denominator of `s` on
`V`.** -/
theorem isSectionOver_iff_one_mem_range (V : Opens X) :
    IsSectionOver L s V ↔
      ∃ d : (denominatorIdeal X L s).val.obj (op V),
        (denominatorIdealι X L s).val.app (op V) d =
          (1 : (Stacks.DenominatorIdeal.O X).obj.obj (op V)) := by
  rw [denominatorIdeal_sections X L s V (1 : (Stacks.DenominatorIdeal.O X).obj.obj (op V)),
    sectionMap_app_one]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, ht.symm⟩, fun ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

/-- A point of an affine open on which the ideal of denominators is the unit ideal is not in the
support of the ideal of denominators. -/
theorem notMem_support_of_ideal_eq_top {W : X.affineOpens} {x : X} (hx : x ∈ W.1)
    (hW : (denominatorIdealData X L s).ideal W = ⊤) :
    x ∉ (denominatorIdealData X L s).support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, Scheme.mem_zeroLocus_iff]
  intro h
  exact h 1 (by rw [hW]; exact Submodule.mem_top) (by rwa [X.basicOpen_one])

variable (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
  (Stacks.DenominatorIdeal.O X).property L)

include hL

/-- **On an affine open the ideal of denominators is the unit ideal exactly when `s` corresponds
to a section of `L` there.** -/
theorem ideal_denominatorIdealData_eq_top_iff (W : X.affineOpens) :
    (denominatorIdealData X L s).ideal W = ⊤ ↔ IsSectionOver L s W.1 := by
  rw [isSectionOver_iff_one_mem_range L s W.1, Ideal.eq_top_iff_one,
    denominatorIdealData_ideal X L s hL W]
  exact Iff.rfl

/-- An open set over which `s` corresponds to a section of `L` is disjoint from the support of
the ideal of denominators of `s`. -/
theorem disjoint_support_of_isSectionOver {V : Opens X} (hV : IsSectionOver L s V) :
    Disjoint (V : Set X) ((denominatorIdealData X L s).support : Set X) := by
  rw [Set.disjoint_left]
  intro x hxV
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V from hxV) V.isOpen
  exact notMem_support_of_ideal_eq_top L s hxW
    ((ideal_denominatorIdealData_eq_top_iff L s hL ⟨W, hW⟩).mpr
      (IsSectionOver.mono L s hWV hV))

/-- Every point outside the support of the ideal of denominators has an open neighbourhood over
which `s` corresponds to a section of `L`. -/
theorem exists_isSectionOver_of_notMem_support {x : X}
    (hx : x ∉ (denominatorIdealData X L s).support) :
    ∃ V : Opens X, x ∈ V ∧ IsSectionOver L s V := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hxW,
    Scheme.mem_zeroLocus_iff] at hx
  simp only [not_forall] at hx
  obtain ⟨f, hf, hxf⟩ := hx
  rw [not_not] at hxf
  refine ⟨X.basicOpen f, hxf, ?_⟩
  refine (ideal_denominatorIdealData_eq_top_iff L s hL
    (X.affineBasicOpen (U := ⟨W, hW⟩) f)).mp ?_
  rw [← (denominatorIdealData X L s).map_ideal_basicOpen ⟨W, hW⟩ f]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
    (X.toRingedSpace.isUnit_res_basicOpen f)

/-- **The maximal open subscheme over which `s` corresponds to a section of `L` is the complement
of the support of the ideal of denominators of `s`.** -/
theorem sectionOpens_eq_compl_support :
    sectionOpens L s = (denominatorIdealData X L s).support.compl := by
  refine le_antisymm (sSup_le fun V hV x hxV => ?_) fun x hx => ?_
  · exact Set.disjoint_left.mp (disjoint_support_of_isSectionOver L s hL hV) hxV
  · obtain ⟨V, hxV, hV⟩ := exists_isSectionOver_of_notMem_support L s hL hx
    exact le_sectionOpens L s hV hxV

/-- `U` is the whole scheme exactly when the ideal of denominators has empty support. -/
theorem sectionOpens_eq_top_iff :
    sectionOpens L s = ⊤ ↔ (denominatorIdealData X L s).support = ⊥ := by
  rw [sectionOpens_eq_compl_support L s hL]
  refine ⟨fun h => TopologicalSpace.Closeds.ext ?_, fun h => TopologicalSpace.Opens.ext ?_⟩
  · have h' : ((denominatorIdealData X L s).support : Set X)ᶜ = Set.univ :=
      congrArg (fun V : Opens X => (V : Set X)) h
    rw [← Set.top_eq_univ] at h'
    simpa only [compl_eq_top, Set.bot_eq_empty, TopologicalSpace.Closeds.coe_bot] using h'
  · have h' : ((denominatorIdealData X L s).support : Set X) = ∅ :=
      congrArg (fun K : Closeds X => (K : Set X)) h
    simp [TopologicalSpace.Closeds.compl, h']

/-- The maximal open subscheme over which `s` corresponds to a section of `L` is disjoint from
the support of the ideal of denominators of `s`. -/
theorem disjoint_sectionOpens_support :
    Disjoint ((sectionOpens L s : Opens X) : Set X)
      ((denominatorIdealData X L s).support : Set X) := by
  rw [sectionOpens_eq_compl_support L s hL]
  exact disjoint_compl_left

/-- **The blowup in the ideal of denominators is `U`-admissible, for an arbitrary meromorphic
section.**  For a locally Noetherian `X`, an invertible `L` and an arbitrary meromorphic section
`s` of `L`, the blowup of `X` in the ideal of denominators of `s` is `U`-admissible, where `U` is
the maximal open subscheme over which `s` corresponds to a section of `L`. -/
theorem isAdmissibleBlowup_denominatorIdealData' [IsLocallyNoetherian X] :
    Stacks.Blowup.IsAdmissibleBlowup (sectionOpens L s)
      (Stacks.Blowup.blowUpToBase (denominatorIdealData X L s)) :=
  Stacks.Blowup.isAdmissibleBlowup_blowUpToBase
    (AlgebraicGeometry.finitePresentation_subschemeι_of_isLocallyNoetherian _)
    (disjoint_sectionOpens_support L s hL)

/-- Let `X` be a locally Noetherian scheme, `L` an invertible `𝒪_X`-module and `s` a regular
meromorphic section of `L`.  Let `U ⊆ X` be the maximal open subscheme such that `s` corresponds
to a section of `L` over `U`.  Then the blowup `b : X' ⟶ X` of `X` in the ideal of denominators
of `s` is `U`-admissible. -/
@[stacks 0ESL "the blowup in the ideal of denominators is U-admissible"]
theorem isAdmissibleBlowup_denominatorIdealData [IsLocallyNoetherian X]
    (_hs : IsRegularMeromorphicSection X.sheaf L s) :
    Stacks.Blowup.IsAdmissibleBlowup (sectionOpens L s)
      (Stacks.Blowup.blowUpToBase (denominatorIdealData X L s)) :=
  isAdmissibleBlowup_denominatorIdealData' L s hL

end Stacks.DenominatorBlowup

end
