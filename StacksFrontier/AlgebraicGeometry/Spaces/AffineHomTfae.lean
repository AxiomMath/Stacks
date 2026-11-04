module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Local criteria for an affine morphism of algebraic spaces

Affineness of a morphism of algebraic spaces over a scheme `S` (Stacks 03WF) is the
affine-base-change pattern `AlgebraicGeometry.Space.HoldsOnAffineBaseChange` at Mathlib's
`AlgebraicGeometry.IsAffineHom`: over an affine test object the representing object is affine
exactly when its projection is an affine morphism of schemes. This file proves that
identification and several of the implications between the conditions of Stacks 03WG.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_iff_holdsOnAffineBaseChange`: affineness of a
  morphism of algebraic spaces is the affine-base-change pattern at Mathlib's
  `AlgebraicGeometry.IsAffineHom`.
* `AlgebraicGeometry.Space.IsAffineHom.of_isPullback`: affineness of a morphism of algebraic
  spaces is stable under arbitrary base change.
* `AlgebraicGeometry.Space.isAffineHom_of_presheaf`: a representable morphism all of whose
  represented base changes are affine morphisms of schemes is affine. This is the
  implication (1) ⇒ (2) of Stacks 03WG.
* `AlgebraicGeometry.Space.IsAffineHom.exists_affine_isPullback_of_isEtale`: the base change
  of an affine morphism along an étale morphism from an affine object is represented by an
  affine object. This is the implication (2) ⇒ (3) of Stacks 03WG.
* `AlgebraicGeometry.Space.IsAffineHom.exists_etaleChart`: an affine morphism stays affine
  after base change along a surjective étale scheme chart of its target. This is the
  implication (2) ⇒ (4) of Stacks 03WG.
* `AlgebraicGeometry.Space.IsAffineHom.exists_zariskiCover`: an affine morphism is affine
  over the members of a Zariski covering of its target. This is the implication (2) ⇒ (5) of
  Stacks 03WG.
* `AlgebraicGeometry.Space.presheaf_isAffineHom_of_surjectiveEtaleChart`: assuming effective
  descent of affine morphisms along surjective étale morphisms of the site, a morphism whose
  base change along a surjective étale scheme chart of its target is representable with
  affine represented base changes is itself representable with affine represented base
  changes.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03WI](https://stacks.math.columbia.edu/tag/03WI)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Affineness of a morphism of algebraic spaces over `S` is the general
affine-base-change pattern of `AlgebraicGeometry.Space.HoldsOnAffineBaseChange` at Mathlib's
`AlgebraicGeometry.IsAffineHom`. -/
theorem isAffineHom_iff_holdsOnAffineBaseChange (f : X ⟶ Y) :
    IsAffineHom B S hS f ↔
      HoldsOnAffineBaseChange B S hS @_root_.AlgebraicGeometry.IsAffineHom f := by
  refine ⟨fun h Z hZ g ↦ ?_, fun h Z g ↦ ?_⟩
  · obtain ⟨W, p, q, hpb⟩ := h ⟨Z, hZ⟩ g
    have := W.property
    exact ⟨W.obj, q, p, hpb, W.property, isAffineHom_of_isAffine _⟩
  · obtain ⟨W, p, q, hpb, hW, -⟩ := h Z.obj Z.property g
    exact ⟨⟨W, hW⟩, q, p, hpb⟩

/-- Affineness of a morphism of algebraic spaces over `S` is stable under base change: if `f'`
sits in a Cartesian square over `f`, then `f'` is affine as soon as `f` is. -/
@[stacks 03WI]
theorem IsAffineHom.of_isPullback {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {k : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback k f' f g)
    (hf : IsAffineHom B S hS f) : IsAffineHom B S hS f' :=
  (isAffineHom_iff_holdsOnAffineBaseChange f').2
    (((isAffineHom_iff_holdsOnAffineBaseChange f).1 hf).of_isPullback sq)

/-- A representable morphism of algebraic spaces over `S` all of whose represented base changes
are affine morphisms of schemes is affine. -/
theorem isAffineHom_of_presheaf {f : X ⟶ Y}
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsAffineHom B S hS f :=
  (isAffineHom_iff_holdsOnAffineBaseChange f).2
    (HoldsOnAffineBaseChange.of_presheaf
      (fun p hp hZ ↦ by
        have := hp
        have := hZ
        exact isAffine_of_isAffineHom p) hf)

/-- The base change of an affine morphism of algebraic spaces over `S` along an étale morphism
from an affine object of the site is represented by an affine object of the site. -/
theorem IsAffineHom.exists_affine_isPullback_of_isEtale {f : X ⟶ Y}
    (hf : IsAffineHom B S hS f) (V : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ Y)
    (_hg : IsEtale B S hS g) :
    ∃ (W : BigAffineFppf B S hS)
      (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ X)
      (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
        (BigAffineFppf.inclusion B S hS).obj V),
      IsPullback p (yoneda.map q) f g :=
  hf V g

/-- An affine morphism of algebraic spaces over `S` stays affine after base change along some
surjective étale morphism from a representable presheaf onto its target. -/
theorem IsAffineHom.exists_etaleChart {f : X ⟶ Y} (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsAffineHom B S hS f) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
      IsSurjective B S hS g ∧ IsEtale B S hS g ∧
        IsAffineHom B S hS (pullback.snd f g) := by
  obtain ⟨V, g, hsurj, hetale⟩ := hY.exists_atlas
  exact ⟨V, g, isSurjective_of_presheafSurjective B S hS g hsurj,
    isEtale_of_presheaf_etale B S hS hetale,
    hf.of_isPullback (IsPullback.of_hasPullback f g)⟩

/-- An affine morphism of algebraic spaces over `S` is affine over the members of some Zariski
covering of its target. -/
theorem IsAffineHom.exists_zariskiCover {f : X ⟶ Y} (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsAffineHom B S hS f) :
    ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
      ∀ i, IsAffineHom B S hS (pullback.snd f (U i).ι) :=
  ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top hY,
    fun _ ↦ hf.of_isPullback (IsPullback.of_hasPullback _ _)⟩

/-- Let `g` be a surjective étale morphism from a representable presheaf onto `Y`. If affine
morphisms of schemes satisfy effective descent along the surjective étale morphisms of the site
and the base change of `f` along `g` is representable with affine represented base changes,
then `f` is representable with affine represented base changes. -/
theorem presheaf_isAffineHom_of_surjectiveEtaleChart
    (hdesc : IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}))
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hs : IsSurjective B S hS g) (he : IsEtale B S hS g)
    (hV : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f := by
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hf := presheaf_of_surjectiveEtaleChart hdesc hX.isSheaf hY.isSheaf
    (presheafSurjective_of_isSurjective B S hS g
      (hY.diagonal_representable.of_diag g) hs)
    (presheaf_etale_of_isEtale B S hS he) hV
  exact ⟨hf.rep, hf⟩

end AlgebraicGeometry.Space

end
