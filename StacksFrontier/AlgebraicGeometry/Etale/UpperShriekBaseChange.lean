module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekQuasiFinite

import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the upper shriek of a locally quasi-finite morphism

Consider a cartesian square of a big étale site with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'`, with `f` locally
quasi-finite. The upper shriek `f^!` of Stacks 0F59 is the right adjoint of the direct image
with compact support `f_!`, and the direct image `g_*` of abelian étale sheaves is the right
adjoint of the inverse image `g⁻¹`. Hence `f^! g_*` is right adjoint to `g⁻¹ f_!` and
`p_* f'^!` is right adjoint to `f'_! p⁻¹`, so the base-change isomorphism
`g⁻¹ f_! ≅ f'_! p⁻¹` of Stacks 0F5J transposes to `p_* f'^! ≅ f^! g_*` by uniqueness of right
adjoints. This is Stacks 0F6U.

## Main definitions

* `AlgebraicGeometry.SmallEtale.abPushforward` — the direct image of abelian sheaves on the
  small étale sites along a morphism of the big étale site.
* `AlgebraicGeometry.SmallEtale.fShriekAbPullbackAdjunction` and
  `AlgebraicGeometry.SmallEtale.abPullbackFShriekAdjunction` — the two composite adjunctions
  `f_! ⋙ g⁻¹ ⊣ g_* ⋙ f^!` and `p⁻¹ ⋙ f'_! ⊣ f'^! ⋙ p_*`.
* `AlgebraicGeometry.SmallEtale.FShriekBaseChangeIso` — the type of the base-change isomorphism
  `g⁻¹ f_! ≅ f'_! p⁻¹` of Stacks 0F5J, the input of the proof.
* `AlgebraicGeometry.SmallEtale.transposeFShriekBaseChangeIso` — the transposition step: a
  base-change isomorphism `g⁻¹ f_! ≅ f'_! p⁻¹` transposed to `p_* f'^! ≅ f^! g_*`.
* `AlgebraicGeometry.SmallEtale.fUpperShriekBaseChangeIso` — **Stacks 0F6U**, the base-change
  isomorphism `(g')_* (f')^! ≅ f^! g_*` of functors on abelian sheaves of `Y'_étale`, with
  `AlgebraicGeometry.SmallEtale.fUpperShriekBaseChangeObjIso` its value at a single sheaf.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekFunctor_map_fUpperShriekBaseChangeIso_inv_app_comp_counit`
  — the base-change isomorphism is the transpose of the one of Stacks 0F5J under the two
  composite adjunctions, which is what pins it down.

## Implementation notes

The source writes the conclusion as an equality `(g')_* (f')^! ℱ = f^! g_* ℱ` of abelian
sheaves. Here it is a natural isomorphism of functors. Equality is not available: `f^!` is the
chosen right adjoint `CategoryTheory.Functor.rightAdjoint` of `f_!`, so it is pinned down only
up to canonical isomorphism, and the two sides are built from different adjunctions. A natural
isomorphism of functors is also strictly stronger than a family of isomorphisms indexed by `ℱ`,
since it carries naturality in `ℱ`; uniqueness of adjoints, which is the source's proof,
produces exactly that.

The input of the source's proof, the base-change isomorphism `g⁻¹ f_! ≅ f'_! p⁻¹` for the direct
image with compact support of Stacks 0F5J, is
`AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatIso`, so nothing is assumed here. The
transposition is factored out as
`AlgebraicGeometry.SmallEtale.transposeFShriekBaseChangeIso`, which takes any such isomorphism:
it is the only step of the argument and is available for every pair of sheaf universes, whereas
Stacks 0F5J is proved for the abelian sheaves of values in `AddCommGrpCat.{u + 1}`, i.e. for the
second universe parameter equal to `u + 1`. The unconditional statements of Stacks 0F6U below are
therefore the specialisations of the transposition at that universe.

The upper shriek `f^!` needs `f` locally of finite type and locally quasi-finite, these being
the hypotheses of Stacks 0F59. For `f'` they are not assumed: they are read off the cartesian
square by `AlgebraicGeometry.SmallEtale.locallyOfFiniteType_of_isPullback` and
`AlgebraicGeometry.SmallEtale.locallyQuasiFinite_of_isPullback`, so the statements below assume
exactly what the source does.

## References

* [Stacks Project, Tag 0F6U](https://stacks.math.columbia.edu/tag/0F6U)
* [Stacks Project, Tag 0F5J](https://stacks.math.columbia.edu/tag/0F5J)
* [Stacks Project, Tag 0F59](https://stacks.math.columbia.edu/tag/0F59)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The direct image of abelian sheaves on small étale sites along a morphism of the big étale
site, right adjoint to `AlgebraicGeometry.SmallEtale.abPullback`. -/
public abbrev abPushforward {S T : B.Scheme} (q : T ⟶ S) :
    Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v} :=
  (smallEtaleBaseChange B q).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

/-- The inverse-image–direct-image adjunction `q⁻¹ ⊣ q_*` for abelian sheaves on the small étale
sites. -/
public def abPullbackAdjunction {S T : B.Scheme} (q : T ⟶ S) :
    abPullback.{u, v} B q ⊣ abPushforward.{u, v} B q :=
  (smallEtaleBaseChange B q).sheafAdjunctionContinuous AddCommGrpCat.{max (u + 1) v}
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)

section Adjunctions

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]

/-- The composite adjunction `g⁻¹ f_! ⊣ f^! g_*`, from `f_! ⊣ f^!` of Stacks 0F59 and the
inverse-image–direct-image adjunction along `g`. -/
public def fShriekAbPullbackAdjunction :
    fShriekFunctor.{u, v} B f ⋙ abPullback.{u, v} B g ⊣
      abPushforward.{u, v} B g ⋙ fUpperShriekFunctor.{u, v} B f :=
  (fShriekAdjunction.{u, v} B f).comp (abPullbackAdjunction.{u, v} B g)

/-- The composite adjunction `f'_! p⁻¹ ⊣ p_* f'^!`, from the inverse-image–direct-image
adjunction along `p` and `f'_! ⊣ f'^!` of Stacks 0F59. -/
public def abPullbackFShriekAdjunction :
    abPullback.{u, v} B p ⋙ fShriekFunctor.{u, v} B f' ⊣
      fUpperShriekFunctor.{u, v} B f' ⋙ abPushforward.{u, v} B p :=
  (abPullbackAdjunction.{u, v} B p).comp (fShriekAdjunction.{u, v} B f')

end Adjunctions

section BaseChange

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- The base-change isomorphism `g⁻¹ f_! ≅ f'_! p⁻¹` of Stacks 0F5J for the direct image with
compact support, for a cartesian square whose vertical morphism `f` is locally quasi-finite: the
input the proof of Stacks 0F6U transposes. It is supplied by
`AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatIso` when the second universe parameter is
`u + 1`. The base change `f'` inherits the finite-type and quasi-finiteness hypotheses from the
square. -/
public abbrev FShriekBaseChangeIso (sq : IsPullback p f' f g) :=
  letI := locallyOfFiniteType_of_isPullback B p f' f g sq
  letI := locallyQuasiFinite_of_isPullback B p f' f g sq
  fShriekFunctor.{u, v} B f ⋙ abPullback.{u, v} B g ≅
    abPullback.{u, v} B p ⋙ fShriekFunctor.{u, v} B f'

/-- The transposition step of the proof of Stacks 0F6U: a base-change isomorphism
`bc : g⁻¹ f_! ≅ f'_! p⁻¹` for the direct image with compact support transposes to
`p_* f'^! ≅ f^! g_*`, both sides being right adjoint to the two sides of `bc`, so that they
agree by uniqueness of right adjoints. -/
public def transposeFShriekBaseChangeIso (sq : IsPullback p f' f g)
    (bc : FShriekBaseChangeIso.{u, v} B p f' f g sq) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    fUpperShriekFunctor.{u, v} B f' ⋙ abPushforward.{u, v} B p ≅
      abPushforward.{u, v} B g ⋙ fUpperShriekFunctor.{u, v} B f :=
  letI := locallyOfFiniteType_of_isPullback B p f' f g sq
  letI := locallyQuasiFinite_of_isPullback B p f' f g sq
  (Adjunction.rightAdjointUniq ((fShriekAbPullbackAdjunction.{u, v} B f g).ofNatIsoLeft bc)
    (abPullbackFShriekAdjunction.{u, v} B p f')).symm

/-- The transposed isomorphism is the transpose of `bc`: its inverse is the natural
transformation whose image under `f'_! p⁻¹`, followed by the counit of `f'_! p⁻¹ ⊣ p_* f'^!`,
equals `bc` followed by the counit of `g⁻¹ f_! ⊣ f^! g_*`. This property determines it. -/
public theorem fShriekFunctor_map_transposeFShriekBaseChangeIso_inv_app_comp_counit
    (sq : IsPullback p f' f g) (bc : FShriekBaseChangeIso.{u, v} B p f' f g sq)
    (ℱ : Sheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{max (u + 1) v}) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    (abPullback.{u, v} B p ⋙ fShriekFunctor.{u, v} B f').map
          ((transposeFShriekBaseChangeIso.{u, v} B p f' f g sq bc).inv.app ℱ) ≫
        (abPullbackFShriekAdjunction.{u, v} B p f').counit.app ℱ =
      bc.inv.app ((abPushforward.{u, v} B g ⋙ fUpperShriekFunctor.{u, v} B f).obj ℱ) ≫
        (fShriekAbPullbackAdjunction.{u, v} B f g).counit.app ℱ :=
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  let := locallyQuasiFinite_of_isPullback B p f' f g sq
  Adjunction.rightAdjointUniq_hom_app_counit
    ((fShriekAbPullbackAdjunction.{u, v} B f g).ofNatIsoLeft bc)
    (abPullbackFShriekAdjunction.{u, v} B p f') ℱ

/-- **Stacks 0F6U.** For a cartesian square with horizontal morphisms `p : X' ⟶ X`,
`g : Y' ⟶ Y`, vertical morphisms `f : X ⟶ Y`, `f' : X' ⟶ Y'` and `f` locally quasi-finite, the
upper shriek commutes with direct image: `p_* f'^! ≅ f^! g_*` as functors on abelian sheaves of
`Y'_étale`. Both sides are right adjoint to the two sides of the base-change isomorphism
`g⁻¹ f_! ≅ f'_! p⁻¹` of Stacks 0F5J, so they agree by uniqueness of right adjoints. -/
@[stacks 0F6U]
public def fUpperShriekBaseChangeIso (sq : IsPullback p f' f g) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    fUpperShriekFunctor.{u, u + 1} B f' ⋙ abPushforward.{u, u + 1} B p ≅
      abPushforward.{u, u + 1} B g ⋙ fUpperShriekFunctor.{u, u + 1} B f :=
  letI := locallyOfFiniteType_of_isPullback B p f' f g sq
  letI := locallyQuasiFinite_of_isPullback B p f' f g sq
  transposeFShriekBaseChangeIso.{u, u + 1} B p f' f g sq
    (fShriekBaseChangeNatIso.{u} B p f' f g sq)

/-- **Stacks 0F6U.** For an abelian sheaf `ℱ` on `Y'_étale` the base-change isomorphism of
Stacks 0F6U reads `p_* (f'^! ℱ) ≅ f^! (g_* ℱ)`, which is the identification the source states
sheaf by sheaf. -/
@[stacks 0F6U "the identification at a single abelian sheaf"]
public def fUpperShriekBaseChangeObjIso (sq : IsPullback p f' f g)
    (ℱ : Sheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{u + 1}) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    (abPushforward.{u, u + 1} B p).obj ((fUpperShriekFunctor.{u, u + 1} B f').obj ℱ) ≅
      (fUpperShriekFunctor.{u, u + 1} B f).obj ((abPushforward.{u, u + 1} B g).obj ℱ) :=
  (fUpperShriekBaseChangeIso.{u} B p f' f g sq).app ℱ

/-- The base-change isomorphism of Stacks 0F6U is the transpose of the one of Stacks 0F5J: its
inverse is the natural transformation whose image under `f'_! p⁻¹`, followed by the counit of
`f'_! p⁻¹ ⊣ p_* f'^!`, equals `fShriekBaseChangeNatIso` followed by the counit of
`g⁻¹ f_! ⊣ f^! g_*`. This property determines it. -/
public theorem fShriekFunctor_map_fUpperShriekBaseChangeIso_inv_app_comp_counit
    (sq : IsPullback p f' f g)
    (ℱ : Sheaf (SmallEtale.topology B Y'.obj Y'.property) AddCommGrpCat.{u + 1}) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    letI := locallyQuasiFinite_of_isPullback B p f' f g sq
    (abPullback.{u, u + 1} B p ⋙ fShriekFunctor.{u, u + 1} B f').map
          ((fUpperShriekBaseChangeIso.{u} B p f' f g sq).inv.app ℱ) ≫
        (abPullbackFShriekAdjunction.{u, u + 1} B p f').counit.app ℱ =
      (fShriekBaseChangeNatIso.{u} B p f' f g sq).inv.app
          ((abPushforward.{u, u + 1} B g ⋙ fUpperShriekFunctor.{u, u + 1} B f).obj ℱ) ≫
        (fShriekAbPullbackAdjunction.{u, u + 1} B f g).counit.app ℱ :=
  let := locallyOfFiniteType_of_isPullback B p f' f g sq
  let := locallyQuasiFinite_of_isPullback B p f' f g sq
  fShriekFunctor_map_transposeFShriekBaseChangeIso_inv_app_comp_counit.{u, u + 1}
    B p f' f g sq (fShriekBaseChangeNatIso.{u} B p f' f g sq) ℱ

end BaseChange

end AlgebraicGeometry.SmallEtale

end
