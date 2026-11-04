module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation

/-!
# A finite-type ideal sheaf below a directed supremum lies below a member

On a quasi-compact scheme, an ideal sheaf of finite type contained in the supremum of a directed
family of ideal sheaves is contained in one member of the family.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_le_of_le_iSup_of_directed`: an ideal sheaf of
  finite type below the supremum of a nonempty directed family lies below one member.
* `AlgebraicGeometry.exists_lift_of_ker_le_iSup_of_directed`: if a closed immersion `Z ⟶ X` locally
  of finite presentation has ideal sheaf below the supremum of a nonempty directed family of
  kernels of morphisms `H a ⟶ X`, then one of these morphisms factors through `Z`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- On a quasi-compact scheme, an ideal sheaf of finite type contained in the supremum of a
nonempty directed family of ideal sheaves is contained in one member of the family. -/
theorem exists_le_of_le_iSup_of_directed {X : Scheme.{u}} [CompactSpace X]
    (K : X.IdealSheafData) (hK : ∀ U : X.affineOpens, (K.ideal U).FG) {ι : Type*} [Nonempty ι]
    (J : ι → X.IdealSheafData) (hJ : Directed (· ≤ ·) J) (hle : K ≤ ⨆ i, J i) :
    ∃ i, K ≤ J i := by
  classical
  have hloc : ∀ U : X.affineOpens, ∃ i, K.ideal U ≤ (J i).ideal U := by
    intro U
    have hc := (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le
      (α := Ideal Γ(X, U.1)) (K.ideal U)).mp
      ((Submodule.fg_iff_compact _).mp (hK U))
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hc (Set.range fun i => (J i).ideal U) (Set.range_nonempty _)
      (by
        rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
        obtain ⟨l, hil, hjl⟩ := hJ i j
        exact ⟨_, ⟨l, rfl⟩, hil U, hjl U⟩)
      (by
        rw [← iSup, ← iSup_apply (f := fun i => (J i).ideal) (a := U), ← ideal_iSup]
        exact hle U)
    exact ⟨i, hi⟩
  choose iU hiU using hloc
  obtain ⟨s, hs, hcov⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := ⊤)).mp
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  obtain ⟨z, hz⟩ := hJ.finset_le (hs.toFinset.image iU)
  refine ⟨z, le_of_iSup_eq_top (fun V : s => V.1) ?_ fun V => ?_⟩
  · rw [hcov, iSup_subtype']
  · exact (hiU V.1).trans
      (hz (iU V.1) (Finset.mem_image_of_mem _ (hs.mem_toFinset.mpr V.2)) V.1)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

universe u

/-- On a quasi-compact scheme `X`, let `i : Z ⟶ X` be a closed immersion locally of finite
presentation and `j a : H a ⟶ X` a family of morphisms whose kernels form a nonempty directed
family with supremum containing the ideal sheaf of `Z`. Then some `j a` factors through `Z`. -/
theorem exists_lift_of_ker_le_iSup_of_directed {X Z : Scheme.{u}} [CompactSpace X] (i : Z ⟶ X)
    [IsClosedImmersion i] [LocallyOfFinitePresentation i] {ι : Type*} [Nonempty ι]
    {H : ι → Scheme.{u}} (j : ∀ a, H a ⟶ X) (hdir : Directed (· ≤ ·) fun a => (j a).ker)
    (hle : i.ker ≤ ⨆ a, (j a).ker) : ∃ (a : ι) (t : H a ⟶ Z), t ≫ i = j a := by
  have hfg : ∀ U : X.affineOpens, (i.ker.ideal U).FG := by
    let e : Z ⟶ i.ker.subscheme := IsClosedImmersion.lift i.ker.subschemeι i
      (by rw [Scheme.IdealSheafData.ker_subschemeι])
    have he : e ≫ i.ker.subschemeι = i := IsClosedImmersion.lift_fac _ _ _
    have : IsIso e := IsClosedImmersion.isIso_of_ker_eq i i.ker.subschemeι e he
      (by rw [Scheme.IdealSheafData.ker_subschemeι])
    have : LocallyOfFinitePresentation i.ker.subschemeι := by
      rw [← Category.id_comp i.ker.subschemeι, ← IsIso.inv_hom_id e, Category.assoc, he]
      infer_instance
    exact (Stacks.Flatness.locallyOfFinitePresentation_subschemeι_iff _).mp this
  obtain ⟨a, ha⟩ := i.ker.exists_le_of_le_iSup_of_directed hfg _ hdir hle
  exact ⟨a, IsClosedImmersion.lift i (j a) ha, IsClosedImmersion.lift_fac _ _ _⟩

end AlgebraicGeometry

end
