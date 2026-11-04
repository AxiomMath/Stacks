module

public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatSurjectiveMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affineness over a one-member fpqc covering

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of algebraic spaces
over `S` which is quasi-compact (**Stacks 03H2**), flat (**Stacks 03ML**) and surjective
(**Stacks 03ME**) is, all by itself, an fpqc covering family of `Y` in the sense of
**Stacks 03MQ**. Presented as a covering family of the fpqc precoverage of **Stacks 03YH**, that
is what lets a property of morphisms of algebraic spaces which is local on the base for the fpqc
topology be tested on the single base change along `f`.

The property this file is written for is affineness, which is fpqc local on the base by
**Stacks 041Z**: a morphism `g : Z ⟶ Y` is affine as soon as its base change `Z ×_Y X ⟶ X` is.
That is the concluding step of **Stacks 07SQ**, where `Y` is an affine scheme `Spec A`, the
covering is a single flat morphism `Spec B ⟶ Spec A` of affine schemes, and the base change of
the morphism under study is already known to be affine.

## Main results

* `AlgebraicGeometry.Space.ofArrows_singleton_mem_fpqc_precoverage`: the one-member family of a
  quasi-compact flat surjective morphism, as a covering of
  `AlgebraicGeometry.Space.Topology.fpqc.precoverage`.
* `AlgebraicGeometry.Space.prop_iff_pullbackSnd_of_fpqc`: a property local on the base for the
  fpqc topology may be tested on the base change along such a morphism.
* `AlgebraicGeometry.Space.isAffineHom_iff_isAffineHom_pullbackSnd_of_isFpqcSingleton` and
  `AlgebraicGeometry.Space.isAffineHom_of_isAffineHom_pullback_of_isFpqcSingleton`: the
  specialisation of that test to affineness, which is the usable form of **Stacks 041Z**.
* `AlgebraicGeometry.Space.isAffineHom_of_isAffineHom_pullback_of_isEtale_of_isSurjective`: the
  same test for a quasi-compact surjective étale covering morphism, which is flat by
  **Stacks 0467**.

## Implementation notes

The fpqc covering condition for the one-member family is
`AlgebraicGeometry.Space.isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective`, which holds
for a family indexed by any nonempty type; here the index type is `PUnit` in the universe the
precoverage quantifies over, which is independent of the universe of the site. Since
`AlgebraicGeometry.Space.Topology.precoverage` takes that universe as a parameter, it is written
out at every use.

Unlike the fppf analogue of
`AlgebraicGeometry.Space.ofArrows_singleton_mem_fppf_precoverage`, no finiteness condition on the
morphism is needed, but quasi-compactness is: the refinement of the pulled-back family by a
finite affine family demanded by Stacks 03MQ is produced from a single affine étale cover of the
fibre product, which exists because quasi-compactness makes that fibre product quasi-compact.

The affineness statements instantiate the precoverage universe at the universe of the site, which
is the instantiation in which `AlgebraicGeometry.Space.isLocalAtTarget_isAffineHom_fpqc` is
consumed elsewhere; nothing in the argument depends on the choice.

## References

* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
* [Stacks Project, Tag 0467](https://stacks.math.columbia.edu/tag/0467)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The one-member presieve of a quasi-compact flat surjective morphism of algebraic spaces over
`S` is a covering family of the fpqc precoverage of **Stacks 03YH**.

The two algebraicity clauses of a covering family are the bundling data of the two objects, and
the fpqc condition of **Stacks 03MQ** for the one-member family is
`AlgebraicGeometry.Space.isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective`. -/
theorem ofArrows_singleton_mem_fpqc_precoverage {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    Presieve.ofArrows (fun _ : PUnit.{v + 1} => X) (fun _ => f) ∈
      (Topology.fpqc.precoverage.{u, v} B S hS).coverings Y :=
  ⟨PUnit.{v + 1}, fun _ => X, fun _ => f, rfl, Y.property, fun _ => X.property,
    isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective.{u, v} B S hS f hqc hflat hsurj⟩

/-- **A property of morphisms of algebraic spaces over `S` local on the base for the fpqc
topology may be tested on the base change along one quasi-compact flat surjective morphism.**
This is the form in which fpqc descent of such a property is consumed: the hypotheses on `f` are
exactly those which make its one-member family an fpqc covering of `Y` in the sense of
**Stacks 03MQ**. -/
theorem prop_iff_pullbackSnd_of_fpqc (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.fpqc.precoverage.{u, v} B S hS)]
    {X Y Z : AlgebraicSpaces B S hS} (g : Z ⟶ Y) (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    P g ↔ P (pullback.snd g f) := by
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd
    (ofArrows_singleton_mem_fpqc_precoverage.{u, v} B S hS f hqc hflat hsurj) (f := g)).trans
    ⟨fun h => h f (Presieve.ofArrows.mk PUnit.unit), ?_⟩
  intro h U k hpb hk
  cases hk
  exact h

/-- **Affineness of a morphism of algebraic spaces over `S` may be checked after base change
along a single quasi-compact flat surjective morphism.** This is the usable form of
**Stacks 041Z**, affineness being local on the base for the fpqc topology, applied to the
one-member fpqc covering of **Stacks 03MQ** given by `f`. -/
theorem isAffineHom_iff_isAffineHom_pullbackSnd_of_isFpqcSingleton
    {X Y Z : AlgebraicSpaces B S hS} (g : Z ⟶ Y) (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    IsAffineHom B S hS g.hom ↔ IsAffineHom B S hS (pullback.snd g f).hom := by
  have hP : MorphismProperty.IsLocalAtTarget
      (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom :
        MorphismProperty (AlgebraicSpaces B S hS))
      (Topology.fpqc.precoverage.{u, u} B S hS) :=
    isLocalAtTarget_isAffineHom_fpqc.{u, u} B S hS
  exact prop_iff_pullbackSnd_of_fpqc.{u, u} B S hS
    (fun {X Y} (f : X ⟶ Y) => IsAffineHom B S hS f.hom) g f hqc hflat hsurj

/-- **The descent direction of
`AlgebraicGeometry.Space.isAffineHom_iff_isAffineHom_pullbackSnd_of_isFpqcSingleton`.** A
morphism `g : Z ⟶ Y` of algebraic spaces over `S` is affine as soon as its base change along one
quasi-compact flat surjective morphism `f : X ⟶ Y` is affine.

This is the concluding step of **Stacks 07SQ**: there `Y` is an affine scheme, `f` is a flat
morphism of affine schemes which is surjective, and affineness of the base change is already
known. -/
@[ega "IV 2.7.1" "(xiii)"]
theorem isAffineHom_of_isAffineHom_pullback_of_isFpqcSingleton
    {X Y Z : AlgebraicSpaces B S hS} (g : Z ⟶ Y) (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom)
    (h : IsAffineHom B S hS (pullback.snd g f).hom) :
    IsAffineHom B S hS g.hom :=
  (isAffineHom_iff_isAffineHom_pullbackSnd_of_isFpqcSingleton B S hS g f hqc hflat hsurj).mpr h

/-- **Affineness of a morphism of algebraic spaces over `S` may be checked after base change
along a quasi-compact surjective étale morphism.** An étale morphism is flat by **Stacks 0467**,
so such an `f` satisfies the hypotheses of
`AlgebraicGeometry.Space.isAffineHom_of_isAffineHom_pullback_of_isFpqcSingleton`. -/
theorem isAffineHom_of_isAffineHom_pullback_of_isEtale_of_isSurjective
    {X Y Z : AlgebraicSpaces B S hS} (g : Z ⟶ Y) (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) (hetale : IsEtale B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) (h : IsAffineHom B S hS (pullback.snd g f).hom) :
    IsAffineHom B S hS g.hom :=
  isAffineHom_of_isAffineHom_pullback_of_isFpqcSingleton B S hS g f hqc
    (isFlat_of_isEtale B S hS hetale) hsurj h

end AlgebraicGeometry.Space

end
