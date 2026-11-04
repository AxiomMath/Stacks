module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.Invariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.Locus
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The Gorenstein locus in the base of a morphism of algebraic spaces

For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, the points of `Y` all of whose
preimages in `X` are Gorenstein points of `f` (Tag 0E14) form the locus in the base over which
`f` is Gorenstein. The morphism is Gorenstein exactly when this locus is all of `Y`, and the
complement of the locus is the image of the set of non-Gorenstein points of `X`.

When `f` is flat and locally of finite presentation, the Gorenstein locus of the source is open
and its formation commutes with arbitrary base change (Tag 0E19). Consequently the locus in the
base is open as soon as `f` is closed on points (for instance when `f` is proper), and its
formation commutes with arbitrary base change as well.

## Main definitions

* `AlgebraicGeometry.Space.gorensteinBaseLocus`: the locus in the target over which `f` is
  Gorenstein.

## Main results

* `AlgebraicGeometry.Space.compl_gorensteinBaseLocus`: the complement of the locus is the image
  of the complement of the Gorenstein locus of the source.
* `AlgebraicGeometry.Space.isGorenstein_iff_gorensteinBaseLocus_eq_univ`: a morphism is
  Gorenstein exactly when its locus in the base is everything.
* `AlgebraicGeometry.Space.isOpen_gorensteinBaseLocus`: the locus is open for a flat morphism
  locally of finite presentation which is closed on points.
* `AlgebraicGeometry.Space.setOf_isGorensteinAt_of_isPullback`: the Gorenstein locus of the
  source along an arbitrary cartesian square.
* `AlgebraicGeometry.Space.preimage_gorensteinBaseLocus_of_isPullback`: the locus in the base
  commutes with arbitrary base change.
* `AlgebraicGeometry.Space.isGorenstein_of_isPullback`: a base change of a Gorenstein flat
  morphism locally of finite presentation is Gorenstein.

## Implementation notes

As in the source's proof of Tag 0E1M, openness is openness of the Gorenstein locus of the source
(`AlgebraicGeometry.Space.isOpen_setOf_isGorensteinAt`) pushed through the complement identity by
a closed map, and compatibility with base change is the same identity read along a cartesian
square: the preimage of an image is the image of the preimage
(`AlgebraicGeometry.Space.exists_points_of_isPullback`), and the preimage of the Gorenstein locus
is the Gorenstein locus of the base change
(`AlgebraicGeometry.Space.isGorensteinAt_pullback_locus`).

## References

* [Stacks Project, Tag 0E14](https://stacks.math.columbia.edu/tag/0E14)
* [Stacks Project, Tag 0E19](https://stacks.math.columbia.edu/tag/0E19)
* [Stacks Project, Tag 0E1M](https://stacks.math.columbia.edu/tag/0E1M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The locus in the target of a morphism of algebraic spaces over `S` over which the morphism
is Gorenstein: the points of the target every preimage of which is a Gorenstein point of the
morphism in the sense of Tag 0E14. -/
def gorensteinBaseLocus {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Set (points B S hS Y) :=
  {y | ∀ x : points B S hS X, pointsMap B S hS X f x = y → IsGorensteinAt B S hS f x}

/-- The complement of the Gorenstein locus in the target is the image of the complement of the
Gorenstein locus in the source. -/
theorem compl_gorensteinBaseLocus {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    (gorensteinBaseLocus B S hS f)ᶜ =
      pointsMap B S hS X f '' {x : points B S hS X | IsGorensteinAt B S hS f x}ᶜ := by
  ext y
  simp only [gorensteinBaseLocus, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_image,
    not_forall]
  exact ⟨fun ⟨x, hx, hg⟩ => ⟨x, hg, hx⟩, fun ⟨x, hg, hx⟩ => ⟨x, hx, hg⟩⟩

/-- A morphism of algebraic spaces is Gorenstein exactly when its Gorenstein locus in the
target is the whole point space of the target. -/
theorem isGorenstein_iff_gorensteinBaseLocus_eq_univ
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsGorenstein B S hS f ↔ gorensteinBaseLocus B S hS f = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact ⟨fun hf _ x _ => hf x, fun hf x => hf _ x rfl⟩

/-- **The open locus in the base.** For a flat morphism of algebraic spaces over `S` which is
locally of finite presentation and closed on points, the locus in the target over which the
morphism is Gorenstein is open: its complement is the image of the complement of the Gorenstein
locus of the source, which is open by Tag 0E19. -/
theorem isOpen_gorensteinBaseLocus {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf_flat : IsFlat B S hS f) (hf_lfp : IsLocallyOfFinitePresentation B S hS f)
    (hf_closed : IsClosedMorphism B S hS f) :
    IsOpen (gorensteinBaseLocus B S hS f) := by
  rw [← isClosed_compl_iff, compl_gorensteinBaseLocus]
  exact hf_closed _ (isOpen_setOf_isGorensteinAt B S hS hX hY f hf_flat hf_lfp).isClosed_compl

/-- The Gorenstein locus in the base of a proper, flat morphism of algebraic spaces over `S`
which is locally of finite presentation is open: a proper morphism is closed on points. -/
theorem isOpen_gorensteinBaseLocus_of_isProper {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf_flat : IsFlat B S hS f) (hf_lfp : IsLocallyOfFinitePresentation B S hS f)
    (hf_proper : IsProper B S hS f) :
    IsOpen (gorensteinBaseLocus B S hS f) :=
  isOpen_gorensteinBaseLocus B S hS hX hY f hf_flat hf_lfp
    (isClosed_of_universallyClosed B S hS hY f hf_proper.universallyClosed)

/-- **Tag 0E19 along an arbitrary cartesian square.** For a flat morphism `f : X ⟶ Y` of
algebraic spaces over `S` which is locally of finite presentation and any cartesian square over
it, the Gorenstein locus of the second projection is the inverse image of the Gorenstein locus
of `f` under the first projection. -/
theorem setOf_isGorensteinAt_of_isPullback {X Y Y' : AlgebraicSpaces B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ X.1} {q : W ⟶ Y'.1} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback p q f.hom g.hom) (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    {w : points B S hS W | IsGorensteinAt B S hS q w} =
      pointsMap B S hS W p ⁻¹' {x : points B S hS X.1 | IsGorensteinAt B S hS f.hom x} := by
  have hcomm : sq.isoPullback.hom ≫ pullback.snd f.hom g.hom = q ≫ (Iso.refl Y'.1).hom := by
    rw [sq.isoPullback_hom_snd, Iso.refl_hom, Category.comp_id]
  ext w
  rw [Set.mem_ofPred_eq, isGorensteinAt_iso_iff B S hS sq.isoPullback (Iso.refl Y'.1) q
    (pullback.snd f.hom g.hom) hcomm w]
  have hmem : pointsMap B S hS W sq.isoPullback.hom w ∈
      {x' : points B S hS (pullback f.hom g.hom) |
        IsGorensteinAt B S hS (pullback.snd f.hom g.hom) x'} ↔
      pointsMap B S hS W sq.isoPullback.hom w ∈
        pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom) ⁻¹'
          {x : points B S hS X.1 | IsGorensteinAt B S hS f.hom x} := by
    rw [isGorensteinAt_pullback_locus B S hS f g hf_flat hf_lfp]
  rw [Set.mem_ofPred_eq] at hmem
  rw [hmem, Set.mem_preimage, ← pointsMap_comp_apply, sq.isoPullback_hom_fst, Set.mem_preimage]

/-- **The open locus in the base commutes with arbitrary base change.** For a flat morphism
`f : X ⟶ Y` of algebraic spaces over `S` which is locally of finite presentation and any
cartesian square over it, the Gorenstein locus in `Y'` of the second projection is the inverse
image under `g : Y' ⟶ Y` of the Gorenstein locus in `Y` of `f`. -/
theorem preimage_gorensteinBaseLocus_of_isPullback {X Y Y' : AlgebraicSpaces B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ X.1} {q : W ⟶ Y'.1} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback p q f.hom g.hom) (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    pointsMap B S hS Y'.1 g.hom ⁻¹' gorensteinBaseLocus B S hS f.hom =
      gorensteinBaseLocus B S hS q := by
  have hlocus := setOf_isGorensteinAt_of_isPullback B S hS f g sq hf_flat hf_lfp
  ext y'
  simp only [gorensteinBaseLocus, Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · intro hy' w hw
    exact (Set.ext_iff.mp hlocus w).mpr (hy' _ (by rw [pointsMap_apply_comm B S hS sq.w w, hw]))
  · intro hy' x hx
    obtain ⟨w, hp, hq⟩ := exists_points_of_isPullback B S hS sq x y' hx
    rw [← hp]
    exact (Set.ext_iff.mp hlocus w).mp (hy' w hq)

/-- A base change of a Gorenstein flat morphism of algebraic spaces over `S` which is locally of
finite presentation is Gorenstein. -/
theorem isGorenstein_of_isPullback {X Y Y' : AlgebraicSpaces B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ X.1} {q : W ⟶ Y'.1} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (sq : IsPullback p q f.hom g.hom) (hf_flat : IsFlat B S hS f.hom)
    (hf_lfp : IsLocallyOfFinitePresentation B S hS f.hom) (hf : IsGorenstein B S hS f.hom) :
    IsGorenstein B S hS q := fun w =>
  (Set.ext_iff.mp (setOf_isGorensteinAt_of_isPullback B S hS f g sq hf_flat hf_lfp) w).mpr (hf _)

end AlgebraicGeometry.Space

end
