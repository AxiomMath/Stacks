module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Invariance
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Locus
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Cohen–Macaulay locus in the base of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a flat morphism of algebraic spaces over a scheme `S` which is locally of
finite presentation. The points of `Y` all of whose preimages in `X` are Cohen–Macaulay points
of `f` form a set which is open as soon as `f` is closed on points, and which is compatible
with arbitrary base change.

## Main definitions

* `AlgebraicGeometry.Space.cohenMacaulayBaseLocus`: the locus in the target over which `f` is
  Cohen–Macaulay.

## Main results

* `AlgebraicGeometry.Space.isOpen_cohenMacaulayBaseLocus`: the locus is open for a flat
  morphism locally of finite presentation which is closed on points.
* `AlgebraicGeometry.Space.setOf_isCohenMacaulayAt_of_isPullback`: the Cohen–Macaulay locus in
  the source along an arbitrary cartesian square.
* `AlgebraicGeometry.Space.preimage_cohenMacaulayBaseLocus_of_isPullback`: the locus in the
  base commutes with arbitrary base change.
* `AlgebraicGeometry.Space.isCohenMacaulay_of_range_subset_cohenMacaulayBaseLocus`: the base
  change over anything mapping into the locus is Cohen–Macaulay.
* `AlgebraicGeometry.Space.isCohenMacaulay_of_isPullback`: a base change of a Cohen–Macaulay
  flat morphism locally of finite presentation is Cohen–Macaulay.

## References

* [Stacks Project, Tag 0E10](https://stacks.math.columbia.edu/tag/0E10)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The locus in the target of a morphism of algebraic spaces over `S` over which the morphism
is Cohen–Macaulay: the points of the target every preimage of which is a Cohen–Macaulay point
of the morphism in the sense of Tag 0E0V. -/
def cohenMacaulayBaseLocus {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Set (points B S hS Y) :=
  {y | ∀ x : points B S hS X, pointsMap B S hS X f x = y → IsCohenMacaulayAt B S hS f x}

/-- The complement of the Cohen–Macaulay locus in the target is the image of the complement of
the Cohen–Macaulay locus in the source. -/
theorem compl_cohenMacaulayBaseLocus {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    (cohenMacaulayBaseLocus B S hS f)ᶜ =
      pointsMap B S hS X f '' {x : points B S hS X | IsCohenMacaulayAt B S hS f x}ᶜ := by
  ext y
  simp only [cohenMacaulayBaseLocus, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_image,
    not_forall]
  exact ⟨fun ⟨x, hx, hcm⟩ ↦ ⟨x, hcm, hx⟩, fun ⟨x, hcm, hx⟩ ↦ ⟨x, hx, hcm⟩⟩

/-- **The open locus in the base.** For a flat morphism of algebraic spaces over `S` which is
locally of finite presentation and closed on points, the locus in the target over which the
morphism is Cohen–Macaulay is open. -/
theorem isOpen_cohenMacaulayBaseLocus {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf_flat : IsFlat B S hS f) (hf_lfp : IsLocallyOfFinitePresentation B S hS f)
    (hf_closed : IsClosedMorphism B S hS f) :
    IsOpen (cohenMacaulayBaseLocus B S hS f) := by
  rw [← isClosed_compl_iff, compl_cohenMacaulayBaseLocus]
  exact hf_closed _
    (isOpen_setOf_isCohenMacaulayAt B S hS hX hY f hf_flat hf_lfp).isClosed_compl

/-- The Cohen–Macaulay locus in the base of a proper, flat morphism of algebraic spaces over
`S` which is locally of finite presentation is open. -/
theorem isOpen_cohenMacaulayBaseLocus_of_isProper
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf_flat : IsFlat B S hS f) (hf_lfp : IsLocallyOfFinitePresentation B S hS f)
    (hf_proper : IsProper B S hS f) :
    IsOpen (cohenMacaulayBaseLocus B S hS f) :=
  isOpen_cohenMacaulayBaseLocus B S hS hX hY f hf_flat hf_lfp
    (isClosed_of_universallyClosed B S hS hY f hf_proper.universallyClosed)

/-- **The Cohen–Macaulay locus along an arbitrary cartesian square.** For a flat morphism
`f : X ⟶ Y` of algebraic spaces over `S` which is locally of finite presentation and any
cartesian square over it, the Cohen–Macaulay locus of the second projection is the inverse image
of the Cohen–Macaulay locus of `f` under the first projection. -/
theorem setOf_isCohenMacaulayAt_of_isPullback {X Y Y' : AlgebraicSpaces B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ X.1} {q : W ⟶ Y'.1} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback p q f.hom g.hom) (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    {w : points B S hS W | IsCohenMacaulayAt B S hS q w} =
      pointsMap B S hS W p ⁻¹' {x : points B S hS X.1 | IsCohenMacaulayAt B S hS f.hom x} := by
  have hcomm : sq.isoPullback.hom ≫ pullback.snd f.hom g.hom = q ≫ (Iso.refl Y'.1).hom := by
    rw [sq.isoPullback_hom_snd, Iso.refl_hom, Category.comp_id]
  ext w
  rw [Set.mem_ofPred_eq, isCohenMacaulayAt_iso_iff B S hS sq.isoPullback (Iso.refl Y'.1) q
    (pullback.snd f.hom g.hom) hcomm w]
  refine (Set.ext_iff.mp (isCohenMacaulayAt_pullback_locus B S hS f g hf_flat hf_lfp) _).trans ?_
  rw [Set.mem_preimage, ← pointsMap_comp_apply, sq.isoPullback_hom_fst, Set.mem_preimage]

/-- **The open locus in the base commutes with arbitrary base change.** For a flat morphism
`f : X ⟶ Y` of algebraic spaces over `S` which is locally of finite presentation and any
cartesian square over it, the Cohen–Macaulay locus in `Y'` of the second projection is the
inverse image under `g : Y' ⟶ Y` of the Cohen–Macaulay locus in `Y` of `f`. -/
@[ega "IV 6.8.2" "partial"]
theorem preimage_cohenMacaulayBaseLocus_of_isPullback {X Y Y' : AlgebraicSpaces B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ X.1} {q : W ⟶ Y'.1} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback p q f.hom g.hom) (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    pointsMap B S hS Y'.1 g.hom ⁻¹' cohenMacaulayBaseLocus B S hS f.hom =
      cohenMacaulayBaseLocus B S hS q := by
  have hlocus := Set.ext_iff.mp
    (setOf_isCohenMacaulayAt_of_isPullback B S hS f g sq hf_flat hf_lfp)
  ext y'
  simp only [cohenMacaulayBaseLocus, Set.mem_preimage, Set.mem_ofPred_eq]
  refine ⟨fun hy' w hw ↦ (hlocus w).2 (hy' _ ?_), fun hy' x hx ↦ ?_⟩
  · rw [pointsMap_apply_comm B S hS sq.w w, hw]
  · obtain ⟨w, rfl, hq⟩ := exists_points_of_isPullback B S hS sq x y' hx
    exact (hlocus w).1 (hy' w hq)

/-- The Cohen–Macaulay locus in the base of a flat morphism locally of finite presentation
commutes with the canonical base change. -/
@[ega "IV 6.8.2" "partial"]
theorem preimage_cohenMacaulayBaseLocus {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    pointsMap B S hS Y'.1 g.hom ⁻¹' cohenMacaulayBaseLocus B S hS f.hom =
      cohenMacaulayBaseLocus B S hS (pullback.snd f.hom g.hom) :=
  preimage_cohenMacaulayBaseLocus_of_isPullback B S hS f g
    (IsPullback.of_hasPullback f.hom g.hom) hf_flat hf_lfp

/-- **The base change over the open locus is Cohen–Macaulay.** For a flat morphism
`f : X ⟶ Y` of algebraic spaces over `S` which is locally of finite presentation, the base
change of `f` along any morphism whose image on points lies in the Cohen–Macaulay locus of `f`
in `Y` is Cohen–Macaulay. -/
@[ega "IV 6.8.2" "partial"]
theorem isCohenMacaulay_of_range_subset_cohenMacaulayBaseLocus
    {X Y Y' : AlgebraicSpaces B S hS} {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ X.1}
    {q : W ⟶ Y'.1} (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p q f.hom g.hom)
    (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (hg : Set.range (pointsMap B S hS Y'.1 g.hom) ⊆ cohenMacaulayBaseLocus B S hS f.hom) :
    IsCohenMacaulay B S hS q := fun w ↦
  (Set.ext_iff.mp (setOf_isCohenMacaulayAt_of_isPullback B S hS f g sq hf_flat hf_lfp) w).2
    (hg ⟨pointsMap B S hS W q w, rfl⟩ _ (pointsMap_apply_comm B S hS sq.w w))

/-- A base change of a Cohen–Macaulay flat morphism of algebraic spaces over `S` which is
locally of finite presentation is Cohen–Macaulay. -/
@[ega "IV 6.8.2" "partial"]
theorem isCohenMacaulay_of_isPullback {X Y Y' : AlgebraicSpaces B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ X.1} {q : W ⟶ Y'.1} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback p q f.hom g.hom) (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (hf : IsCohenMacaulay B S hS f.hom) :
    IsCohenMacaulay B S hS q :=
  isCohenMacaulay_of_range_subset_cohenMacaulayBaseLocus B S hS f g sq hf_flat hf_lfp
    fun _ _ x _ ↦ hf x

end AlgebraicGeometry.Space

end
