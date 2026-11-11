module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme

/-!
# Relative ampleness and surjective étale base change of the base, on carried hypotheses

Let `h : V ⟶ U` be a surjective étale morphism of schemes over the base, let `X` be an algebraic
space over `U`, let `L` be an invertible `𝒪_X`-module, let `Y = V ×_U X` and let `N` be the
pullback of `L` to `Y`. [Stacks, Tag 0D35] says (for affine `U` and `V`) that `L` is ample on
`X/U` if and only if `N` is ample on `Y/V`, both in the sense of [Stacks, Tag 0D31].

**This file does not prove that tag.** The complete, unconditional statement of
[Stacks, Tag 0D35] is
`AlgebraicGeometry.Space.isRelativelyAmple_iff_isRelativelyAmple_baseChange_etale` in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeAmpleEtaleSourceScheme.lean`, which proves that `X`
is a scheme and descends the ampleness, with no hypothesis beyond the source's. The two theorems
below are an earlier, conditional version, kept because they allow arbitrary (not necessarily
affine) schemes `U` and `V`; they rest on two hypotheses that the source does not make.

## Main definitions

* `AlgebraicGeometry.Space.RelativeAmpleEtaleDescentOfSchemes`: a statement about **schemes
  only**, not proved here: invertibility and relative ampleness of a module on a scheme descend
  along a surjective étale base change of the base.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_of_baseChange_etale`: the implication (2) ⇒ (1) of
  [Stacks, Tag 0D35] for arbitrary schemes `U`, `V`, assuming
  `AlgebraicGeometry.Space.RelativeAmpleEtaleDescentOfSchemes` and that `X` is a scheme.
* `AlgebraicGeometry.Space.isRelativelyAmple_iff_baseChange_etale`: the equivalence on the same
  hypotheses. Its forward implication, [Stacks, Tag 0D33], uses none of them.

## The hypotheses

**`hdesc : AlgebraicGeometry.Space.RelativeAmpleEtaleDescentOfSchemes`.** For a cartesian square
of schemes with `a : T' ⟶ T` surjective étale, an invertible module on `W'` that is ample on
`W'/T'` and is the pullback of a module `M` on `W` forces `M` to be invertible and ample on
`W/T`. It is not proved in the library in this generality (invertibility of `M` is part of its
conclusion). The affine case needed by the tag, with `M` already invertible, is
[Stacks, Tag 0D2P], `Stacks.Descent.isRelativelyAmple_of_forall_of_fpqcCover`, which is what the
unconditional proof uses.

**`hX : X.1.IsRepresentable`**, that `X` is a scheme. In the source this is a *conclusion* of
(2) ⇒ (1); it is proved for affine `U`, `V` by
`AlgebraicGeometry.Space.isRepresentable_of_isRelativelyAmple_baseChange_etale`.

## The route

Both clauses are read on the base by [Stacks, Tag 0D32],
`AlgebraicGeometry.Space.isRelativelyAmple_iff_exists_scheme`; the square of schemes
`Y₀ ⟶ V₀`, `X₀ ⟶ U₀` is cartesian because the Yoneda embedding is fully faithful and reflects
limits, the module on `Y₀` is identified with the pullback of the module on `X₀` by
`AlgebraicGeometry.Space.nonempty_baseChangeModule_baseChange_of_isInvertible`, and `hdesc` is
applied once.

## References

* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0D33](https://stacks.math.columbia.edu/tag/0D33)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry.Space

/-- **Étale descent of invertibility and of relative ampleness, for schemes.** Let

  `W' ⟶ W`, `W' ⟶ T'`, `W ⟶ T`, `T' ⟶ T`

be a cartesian square of schemes whose bottom edge `a : T' ⟶ T` is surjective and étale, let `M`
be a module on `W`, and let `M'` be an invertible module on `W'` isomorphic to the pullback of
`M` along `W' ⟶ W`. If `M'` is ample relative to `W' ⟶ T'` in the sense of [Stacks, Tag 01VH],
then `M` is invertible and ample relative to `W ⟶ T`.

Invertibility of `M` is part of the conclusion: the scheme-level notion of relative ampleness is
defined only for an invertible module, and invertibility has to descend along `W' ⟶ W` together
with ampleness. The conclusion is therefore spelled in the same existential shape as the clause
of `AlgebraicGeometry.Space.IsRelativelyAmple`, which asserts the invertibility of each base
change rather than deducing it.

This is a statement about schemes alone, quantified over every cartesian square and every pair
of modules; it is a hypothesis of the conditional theorems of this file and is not proved here.
The unconditional [Stacks, Tag 0D35],
`AlgebraicGeometry.Space.isRelativelyAmple_iff_isRelativelyAmple_baseChange_etale`, does not use
it. -/
def RelativeAmpleEtaleDescentOfSchemes : Prop :=
  ∀ {W T W' T' : Scheme.{u}} {c : W' ⟶ W} {q' : W' ⟶ T'} {q : W ⟶ T} {a : T' ⟶ T},
    IsPullback c q' q a → Surjective a → Etale a →
    ∀ (M : W.Modules) (M' : W'.Modules) (hM' : Stacks.Ample.IsInvertibleModule W' M'),
      (M' ≅ pullbackModule c M) →
      @Stacks.RelativeAmple.IsRelativelyAmple _ _ q' M' hM' →
        ∃ hM : Stacks.Ample.IsInvertibleModule W M,
          @Stacks.RelativeAmple.IsRelativelyAmple _ _ q M hM

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
private instance (priority := high) hasPullbacks_presheaf_relativeAmpleEtaleBaseChange :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

private instance (priority := high) hasPullback_presheaf_relativeAmpleEtaleBaseChange
    {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W) (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

/-- **The implication (2) ⇒ (1) of Stacks 0D35, conditionally, over arbitrary schemes.** Let
`g : V ⟶ U` be a morphism of algebraic spaces which are
the schemes `V₀` and `U₀`, induced by a surjective étale `h₀ : V₀ ⟶ U₀`, let `f : X ⟶ U` be a
morphism of algebraic spaces, let `L` be an invertible `𝒪_X`-module, and let `pr : Y ⟶ X`,
`f' : Y ⟶ V` present `Y` as `V ×_U X`. If the pullback of `L` to `Y` is ample on `Y/V` and `X` is
a scheme, then `L` is ample on `X/U`.

Both clauses are read on the base by [Stacks, Tag 0D32]: clause (2) gives a scheme `Y₀` with `N`
ample on `Y₀/V₀`, the square of schemes `Y₀ ⟶ V₀` over `X₀ ⟶ U₀` is cartesian because `yoneda` is
fully faithful and reflects limits while the passage to schemes preserves fibre products, and the
module on `Y₀` is the pullback of the module on `X₀` by
`AlgebraicGeometry.Space.nonempty_baseChangeModule_baseChange_of_isInvertible`. One application
of `AlgebraicGeometry.Space.RelativeAmpleEtaleDescentOfSchemes` at that single square
finishes.

The hypotheses `hdesc` and `hX` (that `X` is a scheme) are not hypotheses of the source; `hX`
is a conclusion there. This is not the tag: the unconditional (2) ⇒ (1), for affine `U` and `V`,
is `AlgebraicGeometry.Space.isRelativelyAmple_of_isRelativelyAmple_baseChange_etale`. -/
theorem isRelativelyAmple_of_baseChange_etale
    (hdesc : RelativeAmpleEtaleDescentOfSchemes.{u})
    {U V X Y : AlgebraicSpaces B S hS} {f : X ⟶ U} {g : V ⟶ U} {f' : Y ⟶ V} {pr : Y ⟶ X}
    (hsq : IsPullback pr f' f g) (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (U₀ V₀ : BigFppfOver B S hS) (eU : U.1 ≅ yoneda.obj U₀) (eV : V.1 ≅ yoneda.obj V₀)
    (h₀ : V₀ ⟶ U₀) (hg : g.hom ≫ eU.hom = eV.hom ≫ yoneda.map h₀)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map h₀))
    (hetale : Etale ((BigFppfOver.toScheme B S hS).map h₀))
    (hX : X.1.IsRepresentable)
    (hN : IsRelativelyAmple B S hS f' ((modulePullback B S hS pr).obj L)) :
    IsRelativelyAmple B S hS f L := by
  obtain ⟨Y₀, eY, hNinv, hNamp⟩ := hN.exists_scheme V₀ eV
  have := hX
  refine isRelativelyAmple_of_exists_scheme f L hLinv U₀ eU
    ⟨X.1.reprX, X.1.reprW, ?_⟩
  have hpr : yoneda.map (yoneda.preimage (eY.hom ≫ pr.hom ≫ X.1.reprW.inv)) ≫
      X.1.reprW.hom = eY.hom ≫ pr.hom := by simp
  -- the given square, read on the underlying presheaves
  have hpre : IsPullback pr.hom f'.hom f.hom g.hom := by
    have hcan := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
    exact IsPullback.of_iso_pullback ⟨congrArg InducedCategory.Hom.hom hsq.w⟩
      ((ObjectProperty.ι _).mapIso (hsq.isoIsPullback _ _ hcan))
      (congrArg InducedCategory.Hom.hom (hsq.isoIsPullback_hom_fst _ _ hcan))
      (congrArg InducedCategory.Hom.hom (hsq.isoIsPullback_hom_snd _ _ hcan))
  have hsq₁ : IsPullback (yoneda.map (yoneda.preimage (eY.hom ≫ pr.hom ≫ X.1.reprW.inv)))
      (yoneda.map (yoneda.preimage (eY.hom ≫ f'.hom ≫ eV.hom)))
      (yoneda.map (yoneda.preimage (X.1.reprW.hom ≫ f.hom ≫ eU.hom))) (yoneda.map h₀) :=
    hpre.of_iso eY.symm X.1.reprW.symm eV eU
      (by simp) (by simp) (by simp) hg
  have hsq₂ := IsPullback.of_map yoneda
    (yoneda.map_injective (by simpa only [Functor.map_comp] using hsq₁.w)) hsq₁
  obtain ⟨e⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L hLinv X.1.reprX Y₀
    X.1.reprW.hom (yoneda.preimage (eY.hom ≫ pr.hom ≫ X.1.reprW.inv))
  rw [hpr] at e
  exact hdesc (hsq₂.map (BigFppfOver.toScheme B S hS)) hsurj hetale _ _ hNinv
    ((baseChangeModuleCompIso B S hS pr L Y₀ eY.hom).symm ≪≫ e) hNamp

/-- **Stacks 0D35, conditionally, over arbitrary schemes.** Let `g : V ⟶ U` be a morphism of
algebraic spaces which are the schemes `V₀`
and `U₀`, induced by a surjective étale morphism `h₀ : V₀ ⟶ U₀`, let `f : X ⟶ U` be a morphism of
algebraic spaces, let `L` be an invertible `𝒪_X`-module and let `pr : Y ⟶ X`, `f' : Y ⟶ V`
present `Y` as `V ×_U X`. The following are equivalent:

1. `L` is ample on `X/U`;
2. the pullback of `L` to `Y` is ample on `Y/V`.

Clause (1) implies clause (2) by [Stacks, Tag 0D33],
`AlgebraicGeometry.Space.isRelativelyAmple_baseChange`, and uses neither the hypothesis `hdesc`
nor `hX`, nor the surjectivity or étaleness of `h₀`. The converse is
`AlgebraicGeometry.Space.isRelativelyAmple_of_baseChange_etale`, which rests on all of them.
This is not the tag: its unconditional statement, for affine `U` and `V` as in the source, is
`AlgebraicGeometry.Space.isRelativelyAmple_iff_isRelativelyAmple_baseChange_etale`. -/
theorem isRelativelyAmple_iff_baseChange_etale
    (hdesc : RelativeAmpleEtaleDescentOfSchemes.{u})
    {U V X Y : AlgebraicSpaces B S hS} {f : X ⟶ U} {g : V ⟶ U} {f' : Y ⟶ V} {pr : Y ⟶ X}
    (hsq : IsPullback pr f' f g) (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (U₀ V₀ : BigFppfOver B S hS) (eU : U.1 ≅ yoneda.obj U₀) (eV : V.1 ≅ yoneda.obj V₀)
    (h₀ : V₀ ⟶ U₀) (hg : g.hom ≫ eU.hom = eV.hom ≫ yoneda.map h₀)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map h₀))
    (hetale : Etale ((BigFppfOver.toScheme B S hS).map h₀))
    (hX : X.1.IsRepresentable) :
    IsRelativelyAmple B S hS f L ↔
      IsRelativelyAmple B S hS f' ((modulePullback B S hS pr).obj L) :=
  ⟨fun hL => isRelativelyAmple_baseChange hsq L hL,
    isRelativelyAmple_of_baseChange_etale hdesc hsq L hLinv U₀ V₀ eU eV h₀ hg hsurj hetale hX⟩

end AlgebraicGeometry.Space

end
