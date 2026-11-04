module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableProperty

/-!
# Representability criteria for morphisms of presheaves on a big fppf site

Let `S` be a scheme contained in a big fppf site `B`. A morphism of presheaves on the big
fppf site of `S` is *representable by algebraic spaces*
(`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces`) when every base change of it along
a morphism from a representable presheaf is an algebraic space, and such a morphism *has* a
property of morphisms of algebraic spaces (`AlgebraicGeometry.Space.HasProperty`) when every one
of those base changes, viewed as a morphism of algebraic spaces onto the representable presheaf,
has that property.

This file proves basic stability properties of these notions, and shows that quasi-affineness of
morphisms of algebraic spaces over `S` is fpqc local on the base, given effective descent for
quasi-affine morphisms along finite fpqc coverings of affine objects of the site.

## Main definitions

* `AlgebraicGeometry.Space.IsEffectiveQuasiAffineDescentAlongFpqc`: effective descent for
  quasi-affine morphisms along a finite fpqc covering of an affine object of the site.

## Main results

* `AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable`: a
  morphism representable by objects of the site is representable by algebraic spaces.
* `AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces.of_isPullback`: representability by
  algebraic spaces is stable under base change.
* `AlgebraicGeometry.Space.HasProperty.mono`: an implication between properties of morphisms of
  algebraic spaces over `S` passes to morphisms of presheaves representable by algebraic spaces.
* `AlgebraicGeometry.Space.respectsIso_isQuasiAffineHom`: quasi-affineness of morphisms of
  algebraic spaces over `S` respects isomorphisms.
* `AlgebraicGeometry.Space.isQuasiAffineHom_isLocalAtTarget_fpqc`: quasi-affineness of
  morphisms of algebraic spaces over `S` is fpqc local on the base, given
  `AlgebraicGeometry.Space.IsEffectiveQuasiAffineDescentAlongFpqc`.

## References

* [Stacks Project, Tag 02YQ](https://stacks.math.columbia.edu/tag/02YQ)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 0AM1](https://stacks.math.columbia.edu/tag/0AM1)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 02L7](https://stacks.math.columbia.edu/tag/02L7)
* [Stacks Project, Tag 0423](https://stacks.math.columbia.edu/tag/0423)
* [Stacks Project, Tag 041J](https://stacks.math.columbia.edu/tag/041J)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-! ### Morphisms representable by algebraic spaces -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of presheaves on the big fppf site of `S` which is representable by objects of
the site is representable by algebraic spaces. -/
theorem IsRepresentableByAlgebraicSpaces.of_relativelyRepresentable
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : yoneda.relativelyRepresentable a) :
    IsRepresentableByAlgebraicSpaces B S hS a := fun _ ξ ↦
  (isAlgebraicSpace_yoneda B S hS (ha.pullback ξ)).of_iso
    (ha.isPullback ξ).flip.isoPullback

/-- Representability by algebraic spaces is stable under base change: in a Cartesian square of
presheaves on the big fppf site of `S` whose right-hand column is representable by algebraic
spaces, the left-hand column is too. -/
theorem IsRepresentableByAlgebraicSpaces.of_isPullback
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G} {g : G' ⟶ G} {k : F' ⟶ F}
    {a' : F' ⟶ G'} (sq : IsPullback k a' a g)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a) :
    IsRepresentableByAlgebraicSpaces B S hS a' := fun U ξ ↦
  (ha U (ξ ≫ g)).of_iso
    (((IsPullback.of_hasPullback ξ a').flip.paste_horiz sq).flip.isoPullback).symm

/-- A presheaf on the big fppf site of `S` admitting a morphism to a representable presheaf
which is representable by algebraic spaces is itself an algebraic space. -/
theorem isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} {a : F ⟶ yoneda.obj U}
    (ha : IsRepresentableByAlgebraicSpaces B S hS a) : IsAlgebraicSpace B S hS F :=
  (ha U (𝟙 (yoneda.obj U))).of_iso
    (IsPullback.of_horiz_isIso (fst := 𝟙 F) (snd := a) ⟨by simp⟩).flip.isoPullback.symm

/-- The property tested by `AlgebraicGeometry.Space.HasProperty` may be enlarged: if `P` implies
`Q` for every morphism of algebraic spaces over `S`, then a morphism of presheaves representable
by algebraic spaces having `P` also has `Q`. -/
@[stacks 0AM1]
theorem HasProperty.mono {P Q : MorphismProperty (AlgebraicSpaces B S hS)} (hPQ : P ≤ Q)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    {ha : IsRepresentableByAlgebraicSpaces B S hS a}
    (h : HasProperty B S hS P a ha) : HasProperty B S hS Q a ha :=
  fun U ξ ↦ hPQ _ (h U ξ)

/-! ### Quasi-affineness respects isomorphisms -/

/-- Quasi-affineness of a morphism of presheaves on the big fppf site of `S` is unchanged by
precomposition with an isomorphism. -/
theorem IsQuasiAffineHom.iso_comp {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F' ⟶ F)
    [IsIso e] {f : F ⟶ G} (hf : IsQuasiAffineHom B S hS f) :
    IsQuasiAffineHom B S hS (e ≫ f) :=
  IsQuasiAffineHom.of_isPullback (g := 𝟙 G)
    (IsPullback.of_horiz_isIso (fst := e) (snd := e ≫ f) ⟨by simp⟩) hf

/-- Quasi-affineness of a morphism of presheaves on the big fppf site of `S` is unchanged by
postcomposition with an isomorphism. -/
theorem IsQuasiAffineHom.comp_iso {F G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (e : G ⟶ G') [IsIso e] (hf : IsQuasiAffineHom B S hS f) :
    IsQuasiAffineHom B S hS (f ≫ e) :=
  IsQuasiAffineHom.of_isPullback (g := inv e)
    (IsPullback.of_horiz_isIso (fst := 𝟙 F) (snd := f ≫ e) ⟨by simp⟩) hf

/-- Quasi-affineness of a morphism of algebraic spaces over `S` is stable under base change
in the category of algebraic spaces. -/
theorem IsQuasiAffineHom.hom_of_isPullback {F G H K : AlgebraicSpaces B S hS}
    {f : F ⟶ H} {g : G ⟶ H} {p : K ⟶ F} {q : K ⟶ G} (h : IsPullback p q f g)
    (hf : IsQuasiAffineHom B S hS f.hom) : IsQuasiAffineHom B S hS q.hom :=
  IsQuasiAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ h) hf

/-- Quasi-affineness of morphisms of algebraic spaces over `S` respects isomorphisms. -/
instance respectsIso_isQuasiAffineHom :
    MorphismProperty.RespectsIso
      (fun {X Y} (f : X ⟶ Y) => IsQuasiAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS)) :=
  MorphismProperty.RespectsIso.mk _
    (fun e _ hf => IsQuasiAffineHom.iso_comp e.hom.hom hf)
    (fun e _ hf => IsQuasiAffineHom.comp_iso e.hom.hom hf)

/-! ### Effective descent for quasi-affine morphisms along an fpqc covering -/

variable (B S hS) in
/-- *Effective descent for quasi-affine morphisms along an fpqc covering of an affine object
of the site.* Let `Z` be an affine object of the big fppf site of `S` and let `{Zⱼ → Z}` be a
finite fpqc covering of `Z` by affine objects of the site. Let `f : F ⟶ G` be a morphism of
algebraic spaces over `S` and let `k : h_Z ⟶ G`. If the base change of `f` along each
composite `h_{Zⱼ} → h_Z → G` is represented by an object of the site with quasi-affine
underlying scheme, then so is the base change of `f` along `k`. -/
def IsEffectiveQuasiAffineDescentAlongFpqc : Prop :=
  ∀ (Z : BigAffineFppf B S hS) (𝒰 : PreZeroHypercover.{u + 1} Z), Finite 𝒰.I₀ →
    Presieve.map (BigAffineFppf.toScheme B S hS) 𝒰.presieve₀ ∈
      Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj Z) →
    ∀ ⦃F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄, IsAlgebraicSpace B S hS F →
      IsAlgebraicSpace B S hS G → ∀ (f : F ⟶ G)
        (k : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ G),
        (∀ j : 𝒰.I₀, ∃ (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ F)
            (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj (𝒰.X j)),
            Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
              IsPullback p (yoneda.map q) f
                (yoneda.map ((BigAffineFppf.inclusion B S hS).map (𝒰.f j)) ≫ k)) →
        ∃ (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ F)
          (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj Z),
          Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
            IsPullback p (yoneda.map q) f k

/-! ### Quasi-affineness is fpqc local on the base -/

/-- Given effective descent for quasi-affine morphisms along finite fpqc coverings of affine
objects of the site, quasi-affineness of morphisms of algebraic spaces over `S` is fpqc local on
the base: a morphism of algebraic spaces is quasi-affine exactly when its base change to every
member of some fpqc covering of its target is quasi-affine. -/
theorem isQuasiAffineHom_isLocalAtTarget_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hdesc : IsEffectiveQuasiAffineDescentAlongFpqc B S hS) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsQuasiAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, v} B S hS) where
  pullbackSnd _ _ hf :=
    IsQuasiAffineHom.hom_of_isPullback (IsPullback.of_hasPullback _ _) hf
  of_forall_pullbackSnd := by
    rintro T A f R ⟨I, Yi, gi, rfl, -, -, -, hfpqc⟩ hbc Z k
    obtain ⟨𝒰, hfin, hmem, href⟩ := hfpqc Z k
    have hloc : ∀ j : 𝒰.I₀, ∃ (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ A.obj)
        (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj (𝒰.X j)),
        Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
          IsPullback p (yoneda.map q) f.hom
            (yoneda.map ((BigAffineFppf.inclusion B S hS).map (𝒰.f j)) ≫ k) := by
      intro j
      obtain ⟨i, a, ha⟩ := href j
      obtain ⟨W₀, hW₀, ⟨e⟩⟩ := hbc (g := gi i) (Presieve.ofArrows.mk i) (𝒰.X j) a
      have sq := (isPullback_of_iso_pullback a (pullback.snd f (gi i)).hom e).flip
      refine ⟨W₀, (e.hom ≫ pullback.snd a (pullback.snd f (gi i)).hom) ≫
        (pullback.fst f (gi i)).hom,
        yoneda.preimage (e.hom ≫ pullback.fst a (pullback.snd f (gi i)).hom), hW₀, ?_⟩
      rw [Functor.map_preimage, ← ha]
      exact sq.paste_horiz
        (AlgebraicSpaces.isPullback_hom _ _ _ (IsPullback.of_hasPullback f (gi i)))
    obtain ⟨W, p, q, hW, hpb⟩ :=
      hdesc Z 𝒰 hfin hmem A.property T.property f.hom k hloc
    exact ⟨W, hW, ⟨hpb.flip.isoPullback⟩⟩

end AlgebraicGeometry.Space

end
