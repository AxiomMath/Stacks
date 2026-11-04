module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Transporting an open immersion from a union of standard opens to a scheme covering it

Let `g : V ⟶ Spec R` be an open immersion and let `r` be a family of elements of `R` whose
standard opens pull back to a cover of `V`.  If the union `⨆ l, D(r l)` maps by an open
immersion to a further scheme, then so does `V`.

This is the last step of the paragraph of the Stacks proof of
[Stacks, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN) that ends "We conclude that the
morphism `W_i ⟶ Spec(R_i) ⟶ Spec(B_i)` is an open immersion".  The result quoted there,
[Stacks, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9), is formalized as
`AlgebraicGeometry.isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback`, whose source is
the union of the standard opens itself; the source proof instead names the scheme `W_i`, and
reaches it by invoking Tag 01Z4 a second time to identify the union with `W_i` on the nose.

**That second shrinking step is unnecessary.**  Only the inclusion `W_i ⊆ ⨆ l, D(g_{l,i})` is
needed, never the equality: an open immersion whose range lies inside an open `U` factors
through `U` (`AlgebraicGeometry.IsOpenImmersion.lift`), so the conclusion for `U` transports to
it by composition.  Correspondingly none of the hypotheses below mention affineness of the
basic opens, which is what an identification of the two opens would have required (through
[Stacks, Tag 01P8]).

## Main results

* `AlgebraicGeometry.isOpenImmersion_comp_of_opensRange_le`: an open immersion whose range lies
  in an open `U` composes to an open immersion with anything `U` does.
* `AlgebraicGeometry.isOpenImmersion_comp_of_iSup_preimage_basicOpen_eq_top`: the same with the
  containment supplied by a family of standard opens covering the source.
* `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp'`: the quasi-affine case, where the open
  immersion is the canonical morphism `V ⟶ Spec Γ(V, ⊤)` and the cover is by basic opens of
  global sections.  This is the shape the Stacks proof uses, `W_i` being quasi-affine.  It is
  the primed form of `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp`, which asks in addition
  that each basic open of the cover be affine; no affineness is needed here.
* `AlgebraicGeometry.exists_stage_iSup_basicOpen_eq_top`: the cover itself descends to a stage.
  If the basic opens of the global sections `r l` of a stage `D i` of a cofiltered system of
  compact schemes with affine transition morphisms cover the limit after restriction, then
  already some stage below `i` is covered by the basic opens of the restricted sections.  This
  is the hypothesis the three results above take, and it is what the source's second
  "after shrinking `I`" step supplies -- but with no affineness and no identification of opens,
  so it is [Stacks, Tag 01Z4]'s `exists_map_eq_top` ingredient alone rather than Tag 01Z4.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An open immersion whose range is contained in an open `U` composes to an open immersion
with any morphism that `U` composes to an open immersion with: it factors through `U`. -/
theorem isOpenImmersion_comp_of_opensRange_le {V Z Y : Scheme.{u}} (g : V ⟶ Z)
    [IsOpenImmersion g] (U : Z.Opens) (hU : g.opensRange ≤ U) (h : Z ⟶ Y)
    (hoi : IsOpenImmersion (U.ι ≫ h)) :
    IsOpenImmersion (g ≫ h) := by
  have hr : Set.range g.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hU
  have hfac : g ≫ h = IsOpenImmersion.lift U.ι g hr ≫ U.ι ≫ h := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
  rw [hfac]
  infer_instance

/-- **The union of standard opens may be larger than the scheme it comes from.** If `g` is an
open immersion into `Spec R` and the preimages of the standard opens `D(r l)` cover its source,
then `g` composes to an open immersion with anything `⨆ l, D(r l)` does. -/
theorem isOpenImmersion_comp_of_iSup_preimage_basicOpen_eq_top {V Y : Scheme.{u}}
    {R : CommRingCat.{u}} (g : V ⟶ Spec R) [IsOpenImmersion g] {ι : Type*} (r : ι → R)
    (hcov : ⨆ l, g ⁻¹ᵁ (PrimeSpectrum.basicOpen (r l) : (Spec R).Opens) = ⊤)
    (h : Spec R ⟶ Y)
    (hoi : IsOpenImmersion
      ((⨆ l, PrimeSpectrum.basicOpen (r l) : (Spec R).Opens).ι ≫ h)) :
    IsOpenImmersion (g ≫ h) := by
  refine isOpenImmersion_comp_of_opensRange_le g _ ?_ h hoi
  rintro x ⟨y, rfl⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show y ∈ ⨆ l, g ⁻¹ᵁ (PrimeSpectrum.basicOpen (r l) : (Spec R).Opens) from by
      rw [hcov]; trivial)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, hl⟩

/-- **The quasi-affine case**, which is the one the Stacks proof of Tag 07RN uses: if the basic
opens of a family of global sections of a quasi-affine scheme `V` cover `V`, then the canonical
morphism `V ⟶ Spec Γ(V, ⊤)` composes to an open immersion with anything the union of the
corresponding standard opens does.

This is the primed form of `AlgebraicGeometry.isOpenImmersion_toSpecΓ_comp`: that one asks in
addition that every `V.basicOpen (r l)` be affine, and the containment argument above makes
that hypothesis unnecessary. -/
theorem isOpenImmersion_toSpecΓ_comp' {V Y : Scheme.{u}} [V.IsQuasiAffine]
    {ι : Type*} (r : ι → Γ(V, ⊤)) (hcov : ⨆ l, V.basicOpen (r l) = ⊤)
    (h : Spec Γ(V, ⊤) ⟶ Y)
    (hoi : IsOpenImmersion
      ((⨆ l, PrimeSpectrum.basicOpen (r l) : (Spec Γ(V, ⊤)).Opens).ι ≫ h)) :
    IsOpenImmersion (V.toSpecΓ ≫ h) := by
  refine isOpenImmersion_comp_of_iSup_preimage_basicOpen_eq_top V.toSpecΓ r ?_ h hoi
  simpa only [Scheme.toSpecΓ_preimage_basicOpen] using hcov

/-- **A cover of the limit by basic opens of global sections of a stage already covers a
stage.** For a cofiltered system of compact schemes with affine transition morphisms, if the
basic opens of the restrictions to the limit of global sections `r l` of the stage `D i` cover
the limit, then the basic opens of the restrictions of the `r l` cover some stage below `i`.

This is what the second "after shrinking `I`" step of the Stacks proof of Tag 07RN needs.  The
source states that step as a second application of [Stacks, Tag 01Z4] identifying the standard
opens `D(g_{l, i})` with `W_i`; only this covering statement is used, and it is the single
ingredient `AlgebraicGeometry.exists_map_eq_top` of Tag 01Z4's proof, not Tag 01Z4 itself. -/
theorem exists_stage_iSup_basicOpen_eq_top {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] (c : Cone D) (hc : IsLimit c) {i : I}
    {ι : Type*} (r : ι → Γ(D.obj i, ⊤))
    (hcov : ⨆ l, c.pt.basicOpen ((c.π.app i).appTop (r l)) = ⊤) :
    ∃ (j : I) (fji : j ⟶ i),
      ⨆ l, (D.obj j).basicOpen ((D.map fji).appTop (r l)) = ⊤ := by
  obtain ⟨j, fji, hj⟩ := exists_map_eq_top D c hc (⨆ l, (D.obj i).basicOpen (r l))
    (by simp only [Scheme.Hom.preimage_iSup, Scheme.preimage_basicOpen_top]; exact hcov)
  exact ⟨j, fji, by simpa only [Scheme.Hom.preimage_iSup, Scheme.preimage_basicOpen_top] using hj⟩

end AlgebraicGeometry

end
