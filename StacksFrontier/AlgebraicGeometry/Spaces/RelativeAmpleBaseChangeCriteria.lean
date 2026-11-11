module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# Testing relative ampleness on the scheme base changes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`L` be an invertible `𝒪_X`-module. Stacks 0D36 lists four ways of saying that `L` is ample on
`X/Y`: the definition of Stacks 0D31; that for every scheme `Z ⟶ Y` the algebraic space
`X_Z = Z ×_Y X` is a scheme and `L_Z` is ample on `X_Z/Z`; the same for affine `Z` only; and
the same for a single surjective étale `V ⟶ Y` from a scheme.

## Main definitions

* `AlgebraicGeometry.Space.IsAmpleOnBaseChange`: the clause shared by parts (2), (3) and (4) of
  Stacks 0D36 — over a morphism `g : yoneda.obj T ⟶ Y` from a scheme of the site, the base
  change of `f` is represented by a scheme of the site and the pullback of `L` to it is
  invertible and ample relative to that scheme over `T` in the sense of Stacks 01VH.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_isAmpleOnBaseChange`: **Stacks 0D36,
  parts (1) and (2).** Relative ampleness is exactly the condition that every base change of
  `f` along a scheme of the site is a scheme carrying a relatively ample pullback of `L`.
* `AlgebraicGeometry.Space.isAmpleOnBaseChange_of_isRelativelyAmple`: **Stacks 0D36, part (1)
  implies part (3).** The condition on one base change, from relative ampleness; restricting it
  to affine test objects is part (3).
* `AlgebraicGeometry.Space.exists_etaleChart_isAmpleOnBaseChange_of_isRelativelyAmple`:
  **Stacks 0D36, part (1) implies part (4).** A relatively ample module admits a surjective
  étale chart of `Y` on which the condition holds.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_forall_affine_isAmpleOnBaseChange`:
  **Stacks 0D36, the schematic half of part (3) implies part (2).** If every affine base change
  of `f` is a scheme then so is every scheme base change.

## Implementation notes

**The clauses are stated at the cartesian squares of Stacks 0D31.** A morphism `T ⟶ Y` from a
scheme of the site carries no chosen fibre product, so `X_Z` is spelled, exactly as in
`AlgebraicGeometry.Space.IsRelativelyAmple`, as a cartesian square whose two left-hand corners
are representable. "`X_Z` is a scheme" is then the existence of such a square, which is what
`CategoryTheory.Functor.relativelyRepresentable` asks of `f` at `g`, and the ampleness clause is
imposed on every such square; any two of them are isomorphic, so this is the source's condition.
Parts (1) and (2) are therefore equivalent by unfolding, as in the source.

**The full equivalence.** Two implications of Stacks 0D36 are not proved in this file: the
ampleness half of part (3) implies part (2), and part (4) implies part (3). They need Stacks 01VJ
(relative ampleness is local on the base) and Stacks 0D35 (descent of relative ampleness along a
surjective étale morphism of affine schemes, proved unconditionally as
`AlgebraicGeometry.Space.isRelativelyAmple_iff_isRelativelyAmple_baseChange_etale`), and are
proved for an invertible module in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeAmpleBaseChangeCriteriaComplete.lean`, which
assembles the four parts into `AlgebraicGeometry.Space.isRelativelyAmple_tfae_of_isInvertible`.

**Surjectivity and étaleness in part (4)** are spelled by `CategoryTheory.MorphismProperty.presheaf`
of the inverse images of `AlgebraicGeometry.Surjective` and `AlgebraicGeometry.Etale`, which is
the spelling of the atlas of `AlgebraicGeometry.IsAlgebraicSpace` and of part (3) of
`AlgebraicGeometry.Space.isQuasiAffineHom_tfae_of_isAlgebraicSpace`; no affineness is asked of
the chart, matching the source.

## References

* [Stacks Project, Tag 0D36](https://stacks.math.columbia.edu/tag/0D36)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The condition on one scheme base change shared by parts (2), (3) and (4) of Stacks 0D36:
for a morphism `g` to `Y` from the algebraic space represented by a scheme `T` of the site, the
base change of `f : X ⟶ Y` along `g` is represented by a scheme of the site, and on every
cartesian square realising it the pullback of `L` is invertible and ample relative to that
scheme over `T` in the sense of Stacks 01VH. -/
def IsAmpleOnBaseChange {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (L : Modules.{u, u} B S hS X.1 X.2) (T : BigFppfOver B S hS)
    (g : yoneda.obj T ⟶ Y.1) : Prop :=
  (∃ (U : BigFppfOver B S hS) (q : U ⟶ T) (p : yoneda.obj U ⟶ X.1),
      IsPullback p (yoneda.map q) f.hom g) ∧
    ∀ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ T),
      IsPullback p (yoneda.map q) f.hom g →
        ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
            (baseChangeModule B S hS L U p),
          @Stacks.RelativeAmple.IsRelativelyAmple _ _ ((BigFppfOver.toScheme B S hS).map q)
            (baseChangeModule B S hS L U p) hL

variable {B S hS}

/-- **Stacks 0D36, parts (1) and (2).** A module is ample relative to `f : X ⟶ Y` precisely when
every base change of `f` along a scheme of the site is represented by a scheme carrying a
relatively ample pullback of the module.

The two conditions are the same after unfolding: relative representability of `f` is the
existence of the cartesian squares, and the ampleness clause is imposed on the same squares by
both sides. -/
@[stacks 0D36 "parts (1) and (2), which the source calls equivalent by definition and which
the library's Tag 0D31 predicate makes so here too"]
theorem isRelativelyAmple_iff_forall_isAmpleOnBaseChange {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (L : Modules.{u, u} B S hS X.1 X.2) :
    IsRelativelyAmple B S hS f L ↔
      ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y.1),
        IsAmpleOnBaseChange B S hS f L T g := by
  constructor
  · intro h T g
    exact ⟨h.1 g, fun U p q hsq => h.2 T U g p q hsq⟩
  · intro h
    refine ⟨?_, fun T U g p q hsq => (h T g).2 U p q hsq⟩
    intro T g
    exact (h T g).1

/-- **Stacks 0D36, part (1) implies part (3).** For a relatively ample module the base change of
`f` along any scheme of the site is a scheme carrying a relatively ample pullback; part (3) of
Stacks 0D36 is this restricted to the affine objects of the site. -/
@[stacks 0D36 "part (1) implies part (2) at a single base change, hence part (1) implies part
(3) by restriction to affine Z"]
theorem isAmpleOnBaseChange_of_isRelativelyAmple {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2} (h : IsRelativelyAmple B S hS f L)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y.1) :
    IsAmpleOnBaseChange B S hS f L T g :=
  (isRelativelyAmple_iff_forall_isAmpleOnBaseChange f L).mp h T g

/-- **Stacks 0D36, part (1) implies part (4).** A module ample relative to `f : X ⟶ Y` admits a
scheme `V` of the site and a surjective étale morphism `yoneda.obj V ⟶ Y` over which the base
change of `f` is a scheme carrying a relatively ample pullback of the module: any atlas of `Y`
(Stacks 025Y) will do. -/
@[stacks 0D36 "part (1) implies part (4): a surjective etale chart of the base over which the
pullback is a scheme with ample pullback"]
theorem exists_etaleChart_isAmpleOnBaseChange_of_isRelativelyAmple
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {L : Modules.{u, u} B S hS X.1 X.2}
    (h : IsRelativelyAmple B S hS f L) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      IsAmpleOnBaseChange B S hS f L V g := by
  obtain ⟨V, g, hsurj, hetale⟩ := Y.2.exists_atlas
  exact ⟨V, g, hsurj, hetale, isAmpleOnBaseChange_of_isRelativelyAmple h V g⟩

/-- **Stacks 0D36, the schematic half of part (3) implies part (2).** If the base change of
`f : X ⟶ Y` along every affine object of the site is a scheme, then the base change of `f` along
every object of the site is a scheme.

Relative representability may be tested on the affine objects of the site, by
`AlgebraicGeometry.Space.presheaf_of_affineBaseChange` for the property `⊤` of morphisms of
schemes; this is the half of the implication that the source takes from Stacks 03JH. -/
@[stacks 0D36 "part (3) implies the REPRESENTABILITY clause of part (2) — every base change
to a scheme is a scheme — unconditionally. The ampleness clause of that implication is not
proved here; see `isRelativelyAmple_tfae_of_isInvertible`"]
theorem relativelyRepresentable_of_forall_affine_isAmpleOnBaseChange
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (L : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ g : yoneda.obj T ⟶ Y.1, IsAmpleOnBaseChange B S hS f L T g) :
    yoneda.relativelyRepresentable f.hom := by
  have key := presheaf_of_affineBaseChange B S hS
    (P := (⊤ : MorphismProperty Scheme.{u})) inferInstance X.2 Y.2
    (f := f.hom) fun T hT g => by
      obtain ⟨U, q, p, hsq⟩ := (h T hT g).1
      exact ⟨U, q, p, hsq, trivial⟩
  exact key.rep

end AlgebraicGeometry.Space

end
