module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibrePointFreeness

/-!
# Freeness of a fixed rank near a point travels along pullbacks

`AlgebraicGeometry.FreeAtPointOfRank F x r` says that a module is finite locally free of rank `r`
on some open neighbourhood of `x`. This file records that the condition is carried by pullback
along an arbitrary morphism and is detected by pullback along an isomorphism or along an open
immersion.

## Main results

* `AlgebraicGeometry.freeAtPointOfRank_of_moduleIso`: the condition depends on the module only up
  to isomorphism.
* `AlgebraicGeometry.freeAtPointOfRank_of_restrict_iso_free`: a trivialisation of the restriction
  to an open exhibits the condition at every point of that open.
* `AlgebraicGeometry.freeAtPointOfRank_pullback`: freeness of rank `r` near the image of a point
  gives freeness of rank `r` of the pullback near that point.
* `AlgebraicGeometry.freeAtPointOfRank_of_pullback_isIso` and
  `AlgebraicGeometry.freeAtPointOfRank_of_isOpenImmersion`: the converse along an isomorphism and
  along an open immersion. The second is the form needed when the neighbourhood produced by a
  comparison isomorphism lives on a scheme presented as the source of an open immersion rather
  than as the inclusion of an open, which is how a base change of an open immersion arrives.

## Implementation notes

The witness neighbourhood for the pullback along `h` is the inverse image of the witness
neighbourhood downstairs; the comparison between the two restrictions is pseudofunctoriality of
pullback applied to the square `(h ∣_ U) ≫ U.ι = (h ⁻¹ᵁ U).ι ≫ h`, which is
`AlgebraicGeometry.morphismRestrict_ι`. The transport lemmas of
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/FreeRankLocus.lean` —
`AlgebraicGeometry.invertibleRank_pullback_comp` and
`AlgebraicGeometry.invertibleRank_of_moduleIso` — do the rest.

For an open immersion the image open is reached through `AlgebraicGeometry.Scheme.Hom.opensRange`
and `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`, after which
`AlgebraicGeometry.freeAtPointOfRank_of_opens` applies.

## References

* [Stacks Project, Tag 05MP](https://stacks.math.columbia.edu/tag/05MP)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Freeness of a fixed rank near a point depends on the module only up to isomorphism.** -/
theorem freeAtPointOfRank_of_moduleIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) {x : X}
    {r : ℕ} (hM : FreeAtPointOfRank M x r) : FreeAtPointOfRank N x r := by
  obtain ⟨U, hU, hdata⟩ := hM
  exact ⟨U, hU, invertibleRank_of_moduleIso ((Scheme.Modules.pullback U.ι).mapIso e) r hdata⟩

/-- **A trivialisation on an open neighbourhood, stated after restriction along the inclusion of
that open, exhibits a module as free of that rank near every point of the open.** This is the
companion of `AlgebraicGeometry.freeAtPointOfRank_of_over_iso_free` for the other of the two
spellings of "restrict a module to an open". -/
theorem freeAtPointOfRank_of_restrict_iso_free {X : Scheme.{u}} (M : X.Modules) {x : X}
    {W : X.Opens} (hx : x ∈ W) (n : ℕ)
    (e : M.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :
    FreeAtPointOfRank M x n := by
  have h2 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (M.restrict W.ι) n :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e.symm
      (SheafOfModules.isFiniteLocallyFreeOfRank_free.{u, u, u} n)
  have h3 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback W.ι).obj M) n :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M) h2
  exact ⟨W, hx, { exists_isFiniteLocallyFreeOfRankData :=
    h3.exists_isFiniteLocallyFreeOfRankData }⟩

/-- **Freeness of a fixed rank near a point is carried by pullback.** If `M` is finite locally
free of rank `r` near the image of `y`, then its pullback is finite locally free of rank `r`
near `y`. -/
theorem freeAtPointOfRank_pullback {Y Z : Scheme.{u}} (h : Y ⟶ Z) (M : Z.Modules) (y : Y)
    (r : ℕ) (hM : FreeAtPointOfRank M (h.base y) r) :
    FreeAtPointOfRank ((Scheme.Modules.pullback h).obj M) y r := by
  obtain ⟨U, hU, hdata⟩ := hM
  refine ⟨h ⁻¹ᵁ U, hU, ?_⟩
  have h1 : Stacks.SheafOfModules.Invertible.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback ((h ⁻¹ᵁ U).ι ≫ h)).obj M) r :=
    invertibleRank_pullback_comp M r (morphismRestrict_ι h U) hdata
  exact invertibleRank_of_moduleIso
    ((Scheme.Modules.pullbackComp (h ⁻¹ᵁ U).ι h).app M).symm r h1

/-- **Freeness of a fixed rank near a point is detected by pullback along an isomorphism.** -/
theorem freeAtPointOfRank_of_pullback_isIso {Y Z : Scheme.{u}} (h : Y ⟶ Z) [IsIso h]
    (M : Z.Modules) (y : Y) (r : ℕ)
    (hM : FreeAtPointOfRank ((Scheme.Modules.pullback h).obj M) y r) :
    FreeAtPointOfRank M (h.base y) r := by
  have hy : (inv h).base (h.base y) = y := by
    change (h ≫ inv h).base y = y
    rw [IsIso.hom_inv_id]
    rfl
  refine freeAtPointOfRank_of_moduleIso
    ((Scheme.Modules.pullbackComp (inv h) h).app M ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id h)).app M ≪≫
      (Scheme.Modules.pullbackId Z).app M) ?_
  exact freeAtPointOfRank_pullback (inv h) _ (h.base y) r (by rw [hy]; exact hM)

/-- **Freeness of a fixed rank near a point is detected by pullback along an open immersion.** -/
theorem freeAtPointOfRank_of_isOpenImmersion {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (M : Z.Modules) (y : Y) (r : ℕ)
    (hM : FreeAtPointOfRank ((Scheme.Modules.pullback j).obj M) y r) :
    FreeAtPointOfRank M (j.base y) r := by
  have hrange : Set.range j.base = Set.range j.opensRange.ι.base := by
    rw [Scheme.Opens.range_ι]
    rfl
  set e : Y ≅ j.opensRange.toScheme := IsOpenImmersion.isoOfRangeEq j j.opensRange.ι hrange
    with he
  have hfac : e.hom ≫ j.opensRange.ι = j :=
    IsOpenImmersion.isoOfRangeEq_hom_fac j j.opensRange.ι hrange
  have h1 : FreeAtPointOfRank
      ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback j.opensRange.ι).obj M)) y r := by
    refine freeAtPointOfRank_of_moduleIso
      ((Scheme.Modules.pullbackComp e.hom j.opensRange.ι).app M ≪≫
        (Scheme.Modules.pullbackCongr hfac).app M).symm hM
  have h2 := freeAtPointOfRank_of_pullback_isIso e.hom
    ((Scheme.Modules.pullback j.opensRange.ι).obj M) y r h1
  have h3 := freeAtPointOfRank_of_opens M j.opensRange (e.hom.base y) r h2
  have h4 : j.opensRange.ι.base (e.hom.base y) = j.base y :=
    congrArg (fun k : Y ⟶ Z ↦ k.base y) hfac
  rwa [h4] at h3

end AlgebraicGeometry

end
