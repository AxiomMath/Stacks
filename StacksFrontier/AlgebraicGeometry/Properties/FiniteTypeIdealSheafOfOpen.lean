module

public import StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Restriction
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Sheaves.SectionsWithSupport.QuasiCompactOpenIdealSheaf

/-!
# Cutting out a quasi-compact open by an ideal sheaf of finite type

On a quasi-compact and quasi-separated scheme every quasi-compact open subscheme is the
complement of the support of a quasi-coherent sheaf of ideals of finite type. This is the
implication (2) ⟹ (4) of [Stacks, Tag 01PH]; the converse implication, (4) ⟹ (2), is
`AlgebraicGeometry.isCompact_of_isFiniteType_of_support_eq_compl`.

The vanishing ideal of the closed complement already has the right support, but it is not of
finite type. It is everything on each affine open inside the quasi-compact open
(`AlgebraicGeometry.Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support`), so
`Stacks.IdealSheaf.exists_fg_le_of_mem` — Stacks tag 01PF for sheaves of ideals — shrinks it,
one member of a finite affine cover of the open at a time, to a finite type subsheaf which is
still everything on each of them. Being a subsheaf its support can only grow, and being
everything on a cover of the open its support still misses the open; so the support is exactly
the closed complement.

## Main results

* `AlgebraicGeometry.exists_isFiniteType_support_eq_compl`: a quasi-compact open of a
  quasi-compact and quasi-separated scheme is the complement of the support of a quasi-coherent
  sheaf of ideals of finite type.

## Implementation notes

No `@[stacks 01PH]` attribute is attached. That tag asserts the equivalence of four conditions
on an open subscheme, of which only two are formalized here and in
`StacksFrontier/AlgebraicGeometry/Sheaves/SectionsWithSupport/QuasiCompactOpenIdealSheaf.lean`; the
two implications between them are tracked by the `add_to_stacks` entries in that file.

`AlgebraicGeometry.Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support` is imported from
`StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Restriction`, which states it in the ambient
`Scheme.IdealSheafData` namespace and sits far lower in the import graph. The three statements
of it that used to sit in the blowup development are gone: `ideal_eq_top_of_disjoint_support` of
`Blowup/AdmissibleSeparation.lean` and `ideal_eq_top_of_subset_compl_support_reesData` of
`Blowup/AdmissibleDominating.lean` now call this one, and
`ideal_eq_top_of_le_compl_support` of `Blowup/IsoOffCentre.lean` calls the equivalent public
statement in `Cohomology/InjectiveQcoh/Basic.lean`.

## References

* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A quasi-coherent sheaf of ideals which is the unit ideal on each member of a finite family of
affine opens has a finite type quasi-coherent subsheaf of ideals with the same property. The
single-affine-open step is Stacks tag 01PF for sheaves of ideals,
`Stacks.IdealSheaf.exists_fg_le_of_mem`, applied to the unit section. -/
theorem exists_isFiniteType_forall_ideal_eq_top [CompactSpace X] [QuasiSeparatedSpace X]
    (K : X.IdealSheafData) {s : Set X.affineOpens} (hs : s.Finite)
    (hK : ∀ W ∈ s, K.ideal W = ⊤) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ J.IsFiniteType ∧ ∀ W ∈ s, J.ideal W = ⊤ := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨⊥, bot_le, fun _ ↦ Submodule.fg_bot, by simp⟩
  | @insert W s hW hs ih =>
    obtain ⟨J, hJK, hJft, hJtop⟩ := ih fun V hV ↦ hK V (Set.mem_insert_of_mem _ hV)
    obtain ⟨J', hJ'K, hJ'fg, hJ'one⟩ :=
      Stacks.IdealSheaf.exists_fg_le_of_mem K W.2 (a := 1)
        (by rw [hK W (Set.mem_insert _ _)]; exact Submodule.mem_top)
    refine ⟨J ⊔ J', sup_le hJK hJ'K, fun V ↦ Submodule.FG.sup (hJft V) (hJ'fg V),
      fun V hV ↦ ?_⟩
    have hsup : (J ⊔ J').ideal V = J.ideal V ⊔ J'.ideal V := rfl
    rw [hsup]
    rcases Set.mem_insert_iff.mp hV with rfl | hV
    · exact (Ideal.eq_top_iff_one _).mpr (Submodule.mem_sup_right hJ'one)
    · rw [hJtop V hV, top_sup_eq]

/-- **The implication (2) ⟹ (4) of [Stacks, Tag 01PH].** A quasi-compact open subscheme of a
quasi-compact and quasi-separated scheme is the complement of the support of a quasi-coherent
sheaf of ideals of finite type.

The vanishing ideal of the closed complement has the right support but need not be of finite
type; `AlgebraicGeometry.exists_isFiniteType_forall_ideal_eq_top` shrinks it to a finite type
subsheaf which is still the unit ideal on a finite affine cover of the open, and that is enough
to keep the support from meeting the open. -/
theorem exists_isFiniteType_support_eq_compl (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∃ I : X.IdealSheafData, I.IsFiniteType ∧ (I.support : Set X) = (U : Set X)ᶜ := by
  obtain ⟨s, hs, hcover⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  set Z : Closeds X := ⟨(U : Set X)ᶜ, U.2.isClosed_compl⟩ with hZ
  have hsub : ∀ W ∈ s, (W : X.Opens) ≤ U := fun W hW ↦
    (le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) ↦ (i : X.Opens)) W hW).trans hcover.ge
  have hKtop : ∀ W ∈ s, (vanishingIdeal Z).ideal W = ⊤ := fun W hW ↦
    Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support (vanishingIdeal Z) W
      (by
        rw [show (((vanishingIdeal Z).support : Closeds X) : Set X) = (U : Set X)ᶜ from rfl]
        exact Set.disjoint_compl_right_iff_subset.mpr (hsub W hW))
  obtain ⟨I, hIK, hIft, hItop⟩ :=
    exists_isFiniteType_forall_ideal_eq_top (vanishingIdeal Z) hs hKtop
  refine ⟨I, hIft, Set.Subset.antisymm (fun x hx hxU ↦ ?_) ?_⟩
  · rw [hcover] at hxU
    obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp hxU
    obtain ⟨hW, hxW⟩ := Opens.mem_iSup.mp hxW
    replace hx : x ∈ I.support := hx
    rw [mem_support_iff_of_mem (U := W) hxW, hItop W hW, Submodule.top_coe,
      X.zeroLocus_univ] at hx
    exact hx hxW
  · exact le_support_iff_le_vanishingIdeal.mpr hIK

end AlgebraicGeometry

end
