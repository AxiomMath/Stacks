module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.FinitePresentationOpenImmersion

/-!
# Closed immersion into a finitely presented scheme

A morphism locally of finite type from a quasi-compact, quasi-separated scheme to a
quasi-separated scheme factors as a closed immersion followed by a morphism of finite
presentation.

This upgrades the immersion of [Stacks, Tag 01ZE] to a closed immersion.

## Main results

* `AlgebraicGeometry.exists_finite_affineOpens_cover_of_isCompact`: a compact subset of an open
  subscheme is covered by finitely many affine opens contained in it.
* `AlgebraicGeometry.exists_finitePresentation_closedImmersion`: the closed immersion of `X`
  into a scheme of finite presentation over `S`.

## References

* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- A compact subset of an open subscheme is covered by finitely many affine opens contained
in that open subscheme. -/
theorem exists_finite_affineOpens_cover_of_isCompact {Y : Scheme.{u}} (K : Set Y)
    (hK : IsCompact K) (W : Y.Opens) (hKW : K ⊆ (W : Set Y)) :
    ∃ (n : ℕ) (A : Fin n → Y.affineOpens),
      (∀ j, (A j).1 ≤ W) ∧ K ⊆ ⋃ j : Fin n, ((A j).1 : Set Y) := by
  classical
  have hcov : K ⊆ ⋃ A ∈ {A : Y.affineOpens | A.1 ≤ W}, (A.1 : Set Y) := fun x hx => by
    obtain ⟨s, ⟨A, hAaff, rfl⟩, hxs, hsW⟩ :=
      (Scheme.isBasis_affineOpens Y).mem_nhds_iff.mp (W.isOpen.mem_nhds (hKW hx))
    exact Set.mem_biUnion (x := (⟨A, hAaff⟩ : Y.affineOpens)) hsW hxs
  obtain ⟨B, hBW, hBfin, hBcov⟩ := hK.elim_finite_subcover_image (fun A _ => A.1.isOpen) hcov
  refine ⟨hBfin.toFinset.card, fun i => hBfin.toFinset.equivFin.symm i,
    fun j => hBW (hBfin.mem_toFinset.mp (hBfin.toFinset.equivFin.symm j).2), fun x hx => ?_⟩
  obtain ⟨A, hAB, hxA⟩ := Set.mem_iUnion₂.mp (hBcov hx)
  exact Set.mem_iUnion.mpr
    ⟨hBfin.toFinset.equivFin ⟨A, hBfin.mem_toFinset.mpr hAB⟩, by simpa using hxA⟩

/-- **Stacks Project, Tag 01ZG.**  A morphism locally of finite type from a quasi-compact,
quasi-separated scheme to a quasi-separated scheme factors as a closed immersion into a scheme
of finite presentation over the target. -/
@[stacks 01ZG]
theorem exists_finitePresentation_closedImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ S) (i : X ⟶ X'),
      FinitePresentation p ∧ IsClosedImmersion i ∧ i ≫ p = f := by
  obtain ⟨Y, g, i, hg, hi, hif⟩ := exists_finitePresentation_isImmersion f
  obtain ⟨Z, h, j, hh, hj, hij⟩ := IsImmersion.isImmersion_iff_exists.mp hi
  have hK : IsCompact (Set.range i.base) := by
    simpa only [Set.image_univ] using isCompact_univ.image i.continuous
  have hKj : Set.range i.base ⊆ (j.opensRange : Set Y) := by
    rintro y ⟨x, rfl⟩
    rw [← hij]
    exact ⟨h.base x, rfl⟩
  obtain ⟨n, A, hAW, hKA⟩ :=
    exists_finite_affineOpens_cover_of_isCompact (Set.range i.base) hK j.opensRange hKj
  set V : Y.Opens := ⨆ k : Fin n, (A k).1 with hV
  have hKV : Set.range i.base ⊆ (V : Set Y) := by
    intro y hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hKA hy)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩
  have hVj : V ≤ j.opensRange := iSup_le hAW
  have : CompactSpace V.toScheme :=
    isCompact_iff_compactSpace.mp (by
      simpa [hV] using isCompact_iUnion fun k => (A k).2.isCompact)
  have : QuasiSeparatedSpace Y :=
    (quasiSeparated_iff_quasiSeparatedSpace g).mp (FinitePresentation.quasiSeparated hg)
  have hVrange : Set.range (Scheme.Opens.ι V).base ⊆ Set.range j.base := by
    rintro y ⟨v, rfl⟩
    exact Scheme.Hom.mem_opensRange.mp (hVj v.2)
  have hiVrange : Set.range i.base ⊆ Set.range (Scheme.Opens.ι V).base := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨i.base x, hKV ⟨x, rfl⟩⟩, rfl⟩
  let k : V.toScheme ⟶ Z := IsOpenImmersion.lift j (Scheme.Opens.ι V) hVrange
  let t : X ⟶ V.toScheme := IsOpenImmersion.lift (Scheme.Opens.ι V) i hiVrange
  have htFac : t ≫ Scheme.Opens.ι V = i :=
    IsOpenImmersion.lift_fac (f := Scheme.Opens.ι V) (g := i) hiVrange
  have htk : t ≫ k = h := (cancel_mono j).1 <| by
    rw [Category.assoc, IsOpenImmersion.lift_fac, htFac, hij]
  have : IsClosedImmersion (t ≫ k) := htk ▸ hh
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t k
  obtain ⟨_, _, _⟩ := hg
  obtain ⟨_, _, _⟩ :=
    (finitePresentation_iff_quasiCompact_of_isOpenImmersion (Scheme.Opens.ι V)).2 inferInstance
  exact ⟨V.toScheme, Scheme.Opens.ι V ≫ g, t, ⟨inferInstance, inferInstance, inferInstance⟩,
    inferInstance, by rw [← Category.assoc, htFac, hif]⟩

end AlgebraicGeometry

end
