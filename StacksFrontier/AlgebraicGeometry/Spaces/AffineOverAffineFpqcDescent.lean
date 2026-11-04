module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverFpqcSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsTerminalIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Affineness of an algebraic space from an affine base change along a morphism of affine schemes

Let `X ⟶ Spec A` be a morphism of algebraic spaces over `S` whose target is the presheaf
represented by an affine object of the big fppf site, let `Spec B ⟶ Spec A` be a quasi-compact
flat surjective morphism of affine objects of the site, and suppose the fibre product
`X ×_{Spec A} Spec B` is an affine algebraic space. Then `X` is an affine algebraic space.

This is the concluding step of the proof of Stacks 07SQ. Affineness of a morphism of algebraic
spaces is local on the base for the fpqc topology by Stacks 041Z, so affineness of
`X ⟶ Spec A` may be tested on the base change along the one-member fpqc covering
`{Spec B ⟶ Spec A}`; the base change there is the morphism `X ×_{Spec A} Spec B ⟶ Spec B`,
which is a morphism from an affine object of the site into a separated algebraic space and
therefore affine by Stacks 08GB, part (4). Affineness of `X` itself then follows from
affineness of `Spec A`.

## Main definitions

* `AlgebraicGeometry.Space.siteHomOfTerminal`: a morphism of two schemes contained in the site,
  read as a morphism of the site when the base scheme is terminal.

## Main results

* `AlgebraicGeometry.Space.schemePointsUnit_comp_schemePointsMap_siteHom`: over a terminal base
  the functor of points of a morphism of contained schemes is, up to the comparison of the two
  functors of points, the Yoneda image of a morphism of the site.
* `AlgebraicGeometry.Space.isAffineHom_of_isAffineSpace_source_of_isAffineSpace_target`: a
  morphism between two affine algebraic spaces is affine.
* `AlgebraicGeometry.Space.isAffineSpace_of_isAffineSpace_pullback_of_fpqcSingleton`: the descent
  step described above.

## Implementation notes

*Why the covering is taken between objects of the site rather than between spectra.* The
one-member covering of Stacks 041Z is tested by
`AlgebraicGeometry.Space.isAffineHom_of_isAffineHom_pullback_of_isFpqcSingleton`, whose
hypotheses are quasi-compactness, flatness and surjectivity of a morphism of algebraic spaces
over `S`. For the Yoneda image of a morphism of the site all three are read off the underlying
morphism of schemes, by `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map_of_isAffineHom`,
`AlgebraicGeometry.Space.isFlat_yoneda_map` and
`AlgebraicGeometry.Space.isSurjective_yoneda_map`. The statement is therefore phrased for
objects of the big *affine* fppf category, and
`AlgebraicGeometry.Space.schemePointsUnit_comp_schemePointsMap_siteHom` is what moves a
morphism given between functors of points of schemes into that form, over a terminal base.

*The affineness of the base change.* It is used only through
`AlgebraicGeometry.Space.isAffineHom_of_affine_source_of_isAbsolutelySeparated`, which needs the
*target* to be separated; an affine algebraic space is separated by
`AlgebraicGeometry.Space.isAbsolutelySeparated_of_isAffineSpace`, so no hypothesis beyond
affineness of `Spec B` is needed.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-! ### A morphism of contained schemes as a morphism of the site -/

section Terminal

variable (hterminal : IsTerminal S) {T T' : Scheme.{u}}
  (hT : B.Contains T) (hT' : B.Contains T') (f : T ⟶ T')

/-- A morphism of two schemes contained in the site, read as a morphism of the site over a
terminal base: the structure morphisms to a terminal scheme leave nothing to commute with. -/
noncomputable def siteHomOfTerminal : terminalSiteObject B S hS hterminal hT ⟶
    terminalSiteObject B S hS hterminal hT' :=
  BigFppfOver.homOfCompEq B S hS f (hterminal.hom_ext _ _)

/-- The morphism of schemes underlying
`AlgebraicGeometry.Space.siteHomOfTerminal` is the given one. -/
@[simp]
theorem toScheme_map_siteHomOfTerminal :
    (BigFppfOver.toScheme B S hS).map (siteHomOfTerminal B S hS hterminal hT hT' f) = f :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS
    (T := terminalSiteObject B S hS hterminal hT) (W := terminalSiteObject B S hS hterminal hT')
    f (hterminal.hom_ext _ _)

/-- **The functor of points of a morphism of contained schemes is the Yoneda image of a morphism
of the site**, over a terminal base and up to the comparison of the two functors of points. -/
theorem schemePointsUnit_comp_schemePointsMap_siteHom :
    schemePointsUnit B S hS (terminalSiteObject B S hS hterminal hT) ≫
        schemePointsMap B S hS f =
      yoneda.map (siteHomOfTerminal B S hS hterminal hT hT' f) ≫
        schemePointsUnit B S hS (terminalSiteObject B S hS hterminal hT') := by
  have hsq := commSq_schemePointsUnit B S hS (siteHomOfTerminal B S hS hterminal hT hT' f)
  rw [toScheme_map_siteHomOfTerminal] at hsq
  exact hsq

end Terminal

/-! ### Affineness of a morphism of affine algebraic spaces -/

include hZ

/-- **A morphism between two affine algebraic spaces is affine.** The source is the presheaf
represented by an affine object of the site, and the target, being affine, is separated, so
Stacks 08GB part (4) applies to the morphism read on that representing object. -/
theorem isAffineHom_of_isAffineSpace_source_of_isAffineSpace_target
    {P G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : P ⟶ G)
    (hP : IsAffineSpace B S hS P) (hG : IsAffineSpace B S hS G) :
    IsAffineHom B S hS b := by
  obtain ⟨TP, hTP, ⟨e⟩⟩ := hP
  have hb : IsAffineHom B S hS (e.inv ≫ b) :=
    isAffineHom_of_affine_source_of_isAbsolutelySeparated B S hS hZ ⟨TP, hTP⟩ (e.inv ≫ b)
      (isAbsolutelySeparated_of_isAffineSpace B S hS hZ hG)
  have := isAffineHom_comp B S hS e.hom (e.inv ≫ b) (isAffineHom_of_isIso e.hom) hb
  rwa [Iso.hom_inv_id_assoc] at this

/-! ### The concluding descent step of Stacks 07SQ -/

/-- **The concluding descent step of Stacks 07SQ.** Let `X` be an algebraic space over `S` with a
morphism `pk` to the presheaf represented by an affine object `WA` of the site, let
`π : WB ⟶ WA` be a morphism of affine objects of the site whose underlying morphism of schemes
is affine, flat and surjective, and suppose the fibre product of `pk` and the Yoneda image of
`π` is an affine algebraic space. Then `X` is an affine algebraic space.

The one-member family of `yoneda π` is an fpqc covering of `yoneda WA` by Stacks 03MQ, and
affineness of a morphism of algebraic spaces is fpqc local on the base by Stacks 041Z, so it is
enough that the second projection of the fibre product be affine; that projection is a morphism
between two affine algebraic spaces. -/
theorem isAffineSpace_of_isAffineSpace_pullback_of_fpqcSingleton
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {WA WB : BigAffineFppf B S hS}
    (pk : F ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj WA))
    (π : (BigAffineFppf.inclusion B S hS).obj WB ⟶
      (BigAffineFppf.inclusion B S hS).obj WA)
    (hqc : AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map π))
    (hflat : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map π))
    (hsurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map π))
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : P ⟶ F}
    {b : P ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj WB)}
    (hpb : IsPullback a b pk (yoneda.map π))
    (hP : IsAffineSpace B S hS P) :
    IsAffineSpace B S hS F := by
  set YA : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj ((BigAffineFppf.inclusion B S hS).obj WA),
      isAlgebraicSpace_yoneda B S hS _⟩ with hYA
  set YB : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj ((BigAffineFppf.inclusion B S hS).obj WB),
      isAlgebraicSpace_yoneda B S hS _⟩ with hYB
  set FF : AlgebraicSpaces B S hS := ⟨F, hF⟩ with hFF
  set gg : FF ⟶ YA := ObjectProperty.homMk pk with hgg
  set ff : YB ⟶ YA := ObjectProperty.homMk (yoneda.map π) with hff
  have hpb2 : IsPullback (pullback.fst gg ff).hom (pullback.snd gg ff).hom pk (yoneda.map π) :=
    AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback gg ff)
  set e := hpb.isoIsPullback _ _ hpb2 with he
  have hsnd : e.hom ≫ (pullback.snd gg ff).hom = b :=
    hpb.isoIsPullback_hom_snd _ _ hpb2
  have hb : IsAffineHom B S hS b :=
    isAffineHom_of_isAffineSpace_source_of_isAffineSpace_target B S hS hZ b hP
      (isAffineSpace_yoneda B S hS _ WB.property)
  have hsnd' : IsAffineHom B S hS (pullback.snd gg ff).hom := by
    have hrw : (pullback.snd gg ff).hom = e.inv ≫ b := by
      rw [← hsnd, Iso.inv_hom_id_assoc]
    rw [hrw]
    exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso e.inv) hb
  have hpk : IsAffineHom B S hS pk :=
    isAffineHom_of_isAffineHom_pullback_of_isFpqcSingleton B S hS gg ff
      (isQuasiCompact_yoneda_map_of_isAffineHom B S hS π hqc)
      (isFlat_yoneda_map B S hS π hflat)
      (isSurjective_yoneda_map B S hS π hsurj) hsnd'
  exact hpk.isAffineSpace_source (isAffineSpace_yoneda B S hS _ WA.property)

end AlgebraicGeometry.Space

end
