module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme

/-!
# Relative ampleness and surjective étale base change of the base

Let `h : V ⟶ U` be a surjective étale morphism of schemes over the base, let `X` be an algebraic
space over `U`, let `L` be an invertible `𝒪_X`-module, let `Y = V ×_U X` and let `N` be the
pullback of `L` to `Y`. [Stacks, Tag 0D35] says that `L` is ample on `X/U` if and only if `N` is
ample on `Y/V`, both in the sense of [Stacks, Tag 0D31].

The forward implication is [Stacks, Tag 0D33] — relative ampleness is stable under arbitrary base
change — specialised to this square, and is available with nothing assumed:
`AlgebraicGeometry.Space.isRelativelyAmple_baseChange` applied to the cartesian square is already
the statement. The converse is the content of the tag, and is the direction that is *not* closed
here; see "What is carried" below.

## Main definitions

* `AlgebraicGeometry.Space.RelativeAmpleEtaleDescentOfSchemes`: the single fact carried here, a
  statement about **schemes only**: invertibility and relative ampleness of an invertible module
  on a scheme descend along a surjective étale base change of the base.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_of_baseChange_etale`: **Stacks 0D35, (2) implies
  (1)**, on the two carried hypotheses and on the representability of `f`.
* `AlgebraicGeometry.Space.isRelativelyAmple_iff_baseChange_etale`: **Stacks 0D35**, the
  equivalence. Its forward implication uses none of those hypotheses.

## The route

Both clauses are read on the base by [Stacks, Tag 0D32],
`AlgebraicGeometry.Space.isRelativelyAmple_iff_exists_scheme`: since the targets `U` and `V` are
schemes, relative ampleness of an invertible module in the sense of algebraic spaces is
equivalent to the source being a scheme carrying an invertible module relatively ample in the
sense of schemes, [Stacks, Tag 01VH]. So clause (2) says that `Y` is a scheme `Y₀` and that `N`
read on `Y₀` is ample on `Y₀/V₀`, and clause (1) says that `X` is a scheme `X₀` and that `L` read
on `X₀` is ample on `X₀/U₀`; the square of schemes `Y₀ ⟶ V₀`, `X₀ ⟶ U₀` is cartesian because the
Yoneda embedding is fully faithful and reflects limits and the passage to schemes preserves fibre
products, and `V₀ ⟶ U₀` is the given surjective étale morphism. The whole implication is
therefore one application of the carried descent statement, at the *single* square over the base
— no quantification over test schemes survives — after the module on `Y₀` has been identified
with the pullback of the module on `X₀` by
`AlgebraicGeometry.Space.nonempty_baseChangeModule_baseChange_of_isInvertible`.

The source's own proof is different: it forms `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}`, the adjunction map
`ψ : f^* 𝒜 ⟶ ⨁_{d ≥ 0} L^{⊗ d}`, and the morphism `r_{L,ψ} : U(ψ) ⟶ Proj_U(𝒜)` of
[Stacks, Tag 0D2Z], and concludes from clause (5) of [Stacks, Tag 01VJ] that `r_{L,ψ}` is an open
immersion, whence `X` is a scheme and `L` is ample on `X/U`. That route is not open here: neither
the tensor powers of an invertible module on the small étale site of an algebraic space nor the
pullback of a quasi-coherent graded algebra along a morphism of algebraic spaces is available, so
`ψ` cannot even be written — this is what the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjInvertibleMorphismSpaces.lean` record about
[Stacks, Tag 0D2Z], whose own `ψ` is carried as a family of restrictions — and clause (5) of
[Stacks, Tag 01VJ] is among the clauses that
`StacksFrontier/AlgebraicGeometry/RelativeAmple/LocalOnBase.lean` records as not proved, every
clause about the relative `Proj` being out of reach.

## What is carried

**`AlgebraicGeometry.Space.RelativeAmpleEtaleDescentOfSchemes`.** Étale descent of relative
ampleness for schemes: for a cartesian square of schemes with `a : T' ⟶ T` surjective étale, an
invertible module on `W'` that is ample on `W'/T'` and is the pullback of a module `M` on `W`
forces `M` to be invertible and ample on `W/T`. This is the mathematical content of the
direction, and nothing in the library approaches it: ampleness does not descend along a
surjective morphism by any formal manipulation, and the library's only descent of ampleness,
`StacksFrontier/AlgebraicGeometry/RelativeAmple/LocalOnBase.lean`, is Zariski-local on the base.
Invertibility of `M` is part of the conclusion rather than a hypothesis because it too has to
descend: the scheme-level [Stacks, Tag 01VH] is only defined for an invertible module, and
`AlgebraicGeometry.Space.IsRelativelyAmple` accordingly asserts the invertibility of each base
change existentially rather than deducing it, as its implementation notes record. The statement
is quantified over every cartesian square and every module, so it is a statement about schemes
and not about the algebraic spaces of this tag; in particular it says nothing about when an
algebraic space is a scheme, which is the other half of the tag's conclusion.

No quasi-compactness is asked of `a`. It is not needed: an étale morphism is open, so a surjective
étale `a` refines to one with affine source over each affine open of `T`, and relative ampleness
is local on the base by [Stacks, Tag 01VJ],
`Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover`.

## What is assumed, and is a conclusion in the source

**Representability of `f`, that is, that `X` is a scheme.** In the source this is *proved*, at the
very end of the argument, from `r_{L,ψ}` being an open immersion into the scheme `Proj_U(𝒜)`; it
does not follow from clause (2) by any formal step, since `Y ⟶ X` is a surjective étale morphism
from a scheme and every algebraic space admits one of those. With the `Proj` route unavailable it
is taken as the hypothesis `hX` of
`AlgebraicGeometry.Space.isRelativelyAmple_of_baseChange_etale`. It is deliberately a hypothesis
of the theorem and not a field of the carried datum: it is half of the tag's own conclusion, and
carrying a tag's conclusion would make the statement circular.

So the equivalence below is: one direction unconditional, the other on one carried statement
about schemes and the hypothesis that `X` is a scheme.

## Generality

The source takes `V ⟶ U` to be a surjective étale morphism of *affine* schemes. Affineness is
used nowhere below — the route reads both clauses on the base and applies the descent once — so
the statements are given for a surjective étale morphism of arbitrary schemes over the base,
which contains the tag.

## References

* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 0D33](https://stacks.math.columbia.edu/tag/0D33)
* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
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

This is the one fact carried in this file, and it is a statement about schemes alone: it is
quantified over every cartesian square and every pair of modules, and it says nothing about
algebraic spaces. It is the mathematical content of the hard direction of
[Stacks, Tag 0D35] that the library cannot reach; see the "What is carried" section of the module
documentation. -/
def RelativeAmpleEtaleDescentOfSchemes : Prop :=
  ∀ {W T W' T' : Scheme.{u}} {c : W' ⟶ W} {q' : W' ⟶ T'} {q : W ⟶ T} {a : T' ⟶ T},
    IsPullback c q' q a → Surjective a → Etale a →
    ∀ (M : W.Modules) (M' : W'.Modules) (hM' : Stacks.Ample.IsInvertibleModule W' M'),
      (M' ≅ pullbackModule c M) →
      @Stacks.RelativeAmple.IsRelativelyAmple _ _ q' M' hM' →
        ∃ hM : Stacks.Ample.IsInvertibleModule W M,
          @Stacks.RelativeAmple.IsRelativelyAmple _ _ q M hM

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0D35, (2) implies (1).** Let `g : V ⟶ U` be a morphism of algebraic spaces which are
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

The hypothesis `hX` that `X` is a scheme is a *conclusion* of the source's proof, which obtains
it from the relative `Proj`; that route is unavailable here. See the module documentation. -/
@[stacks 0D35 "(2) implies (1), on RelativeAmpleEtaleDescentOfSchemes and with the source's \
conclusion that X is a scheme assumed"]
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
  have hsq₂ := IsPullback.of_map yoneda (yoneda.map_injective (by simpa using hsq₁.w)) hsq₁
  obtain ⟨e⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L hLinv X.1.reprX Y₀
    X.1.reprW.hom (yoneda.preimage (eY.hom ≫ pr.hom ≫ X.1.reprW.inv))
  rw [hpr] at e
  exact hdesc (hsq₂.map (BigFppfOver.toScheme B S hS)) hsurj hetale _ _ hNinv
    ((baseChangeModuleCompIso B S hS pr L Y₀ eY.hom).symm ≪≫ e) hNamp

/-- **Stacks 0D35.** Let `g : V ⟶ U` be a morphism of algebraic spaces which are the schemes `V₀`
and `U₀`, induced by a surjective étale morphism `h₀ : V₀ ⟶ U₀`, let `f : X ⟶ U` be a morphism of
algebraic spaces, let `L` be an invertible `𝒪_X`-module and let `pr : Y ⟶ X`, `f' : Y ⟶ V`
present `Y` as `V ×_U X`. The following are equivalent:

1. `L` is ample on `X/U`;
2. the pullback of `L` to `Y` is ample on `Y/V`.

Clause (1) implies clause (2) by [Stacks, Tag 0D33],
`AlgebraicGeometry.Space.isRelativelyAmple_baseChange`, and uses neither the hypothesis `hdesc`
nor `hX`, nor the surjectivity or étaleness of `h₀`. The converse is
`AlgebraicGeometry.Space.isRelativelyAmple_of_baseChange_etale`, which rests on all of them. -/
@[stacks 0D35 "the equivalence; (1) implies (2) is unconditional, (2) implies (1) rests on the \
carried statement about schemes and on the source's conclusion that X is a scheme"]
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
