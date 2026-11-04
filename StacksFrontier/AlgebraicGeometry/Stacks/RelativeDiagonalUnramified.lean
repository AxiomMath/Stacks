module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UnramifiedLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalQuasiFinite

/-!
# The relative diagonal of a representable 1-morphism of stacks is unramified

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over the big fppf site of `S` which is representable by algebraic spaces. Its
relative diagonal

`Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`

is representable by algebraic spaces (Stacks 04XS, part (1)), a monomorphism (**Stacks 04YQ**,
part (3)) and locally of finite type (part (2) of that tag for a representable 1-morphism). A
monomorphism of algebraic spaces which is locally of finite type is unramified, which is the
implication (3) ⇒ (1) of **Stacks 05W6**. So `Δ_f` is unramified — and unramifiedness of the
relative diagonal is exactly the Deligne–Mumford condition of **Stacks 04YW**.

This is the unramified counterpart of
`Stack.isLocallyQuasiFinite_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`, which is part
(5) of Stacks 04YQ and goes through the locally-quasi-finite half of Stacks 0463 instead. The two
proofs are the same argument at two properties of morphisms of schemes.

## Main results

* `AlgebraicGeometry.Space.isUnramified_of_mono`: the unramified half of the implication
  (3) ⇒ (1) of **Stacks 05W6**: a monomorphism of algebraic spaces over `S` whose represented
  base changes are locally of finite type is unramified.
* `AlgebraicGeometry.Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`:
  **Stacks 050E**, part (3) — a 1-morphism of algebraic stacks over `S` which is representable by
  algebraic spaces is Deligne–Mumford.

## Implementation notes

`AlgebraicGeometry.Space.isUnramified_of_mono` is one implication of Stacks 05W6, which is in
`chapter-076-spaces-more-morphisms`. Stacks 05W6 is a four-way equivalence which
additionally concludes representability, separatedness and local quasi-finiteness, so one
implication is not its covering set, and the lemma is left untagged. The same holds for
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono` and
`AlgebraicGeometry.Space.isSeparated_of_mono`, the two halves of Stacks 0463 stated
untagged beside the quasi-finite sibling of this file, and for
`AlgebraicGeometry.Space.isUnramified_of_comp`, the untagged Stacks 06G6 helper of the
same chapter 76.

The second declaration carries the part (3) key of **Stacks 050E** and no part key of Stacks
04YQ, because Stacks 04YQ has no unramified part: its five parts are representability, local
finite type, monomorphy, separatedness and local quasi-finiteness. What is proved here is
Stacks 05W6 applied at the relative diagonal, and its conclusion is stated as
`AlgebraicGeometry.Stack.IsDM` because that abbreviation *is* the every-chart unramifiedness of
the relative diagonal, so no second notion is coined — which is exactly the conclusion Stacks
050E, part (3) draws for a representable 1-morphism, so that part needs no further declaration.

The quantifier of `AlgebraicGeometry.Stack.IsDM` is not reached through
`AlgebraicGeometry.Stack.HasRelativeProperty`, for the reason recorded in the quasi-finite
sibling: that abbreviation carries two instance arguments on the tested property which its body
does not use, and they are unavailable here.

`AlgebraicGeometry.Space.isUnramified_of_mono` takes local finite type in the
represented-base-change form `CategoryTheory.MorphismProperty.presheaf`, because that is the form
in which `AlgebraicGeometry.Stack.presheaf_locallyOfFiniteType_relativeDiagonal` supplies it, and
concludes in the every-étale-chart form, because that is
`AlgebraicGeometry.Space.IsUnramified`. The passage between the two is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative` (**Stacks 03MJ** for a
representable morphism) at `AlgebraicGeometry.Unramified`, which is étale local on the source and
target by **Stacks 04R3** and stable under base change by instance synthesis. Its
`CategoryTheory.MorphismProperty.IsLocalAtTarget` hypothesis for the fppf precoverage of schemes
does **not** synthesize and is supplied by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` from the fpqc form, exactly as in the
quasi-finite sibling. At a represented base change the scheme-level implication is then instance
synthesis: a monomorphism of schemes has an isomorphism as diagonal, hence an open immersion,
and `AlgebraicGeometry.Unramified.of_isOpenImmersion_diagonal` applies to a morphism which is
moreover locally of finite type.

Two of the six imports this file was first written with were removable at exit 0 with the two
signatures **byte-identical at 1,641 bytes individually and jointly** under `pp.universes` *and*
`pp.fullNames` in one scope, so nothing was narrowed by removing them.
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism` is **retained and disclosed as
cosmetic**: it declares `AlgebraicGeometry.Stack.IsDM`, the notion the second statement concludes,
and reaches this file transitively through
`StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalQuasiFinite` only. Of the four load-bearing
imports, two fail on removal with a real diagnostic and are therefore **necessary** —
`...Descent.UnramifiedFpqcLocalAtTarget` and `...Morphisms.Unramified.Diagonal`, each
`failed to synthesize` — while `...Descent.EtaleLocal.UnramifiedLocalAtSource` and
`...Stacks.RelativeDiagonalQuasiFinite` fail only as `Unknown constant`/`Unknown identifier`,
which establishes **use** and not necessity.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Space

/-- **The implication (3) ⇒ (1) of Stacks 05W6, the unramified half.** A monomorphism of
algebraic spaces over `S` all of whose represented base changes are locally of finite type is
unramified.

Untagged: Stacks 05W6 is a four-way equivalence which additionally concludes representability,
separatedness and local quasi-finiteness, so one implication is not its covering set. It is
proved here because the Deligne–Mumford
condition on the relative diagonal of a representable 1-morphism consumes it, as for
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono` and
`AlgebraicGeometry.Space.isUnramified_of_comp`. -/
theorem isUnramified_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (g : F ⟶ G) (hmono : Mono g)
    (hft : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    IsUnramified B S hS g := by
  have _ : MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have := hmono
  refine (holdsOnEveryEtaleChart_iff_relative B S hS
    (@AlgebraicGeometry.Unramified.{u} : MorphismProperty Scheme.{u})
    AlgebraicGeometry.Unramified.isEtaleLocalOnSourceAndTarget hF hG g hft.1).2 ⟨hft.1, ?_⟩
  intro a b h fst snd hpb
  have _ : AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map snd) := hft.2 h fst snd hpb
  have _ : Mono snd := yoneda.mono_of_mono_map hpb.mono_snd_of_mono
  have _ : Mono ((BigFppfOver.toScheme B S hS).map snd) := inferInstance
  exact (inferInstance :
    AlgebraicGeometry.Unramified ((BigFppfOver.toScheme B S hS).map snd))

end Space

namespace Stack

universe t

variable {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)

include hf

/-- **Stacks 050E, part (3).** A 1-morphism of algebraic stacks which is representable by
algebraic spaces is Deligne–Mumford: its relative diagonal is representable by algebraic spaces
(Stacks 04XS, part (1)), a monomorphism by part (3) of Stacks 04YQ and locally of finite type by
part (2) of that tag, so Stacks 05W6 makes it unramified — which is the Deligne–Mumford
condition of Stacks 04YW.

**No part key of Stacks 04YQ is claimed**: that tag's five parts are representability, local
finite type, monomorphy, separatedness and local quasi-finiteness, and unramifiedness is none of
them. -/
@[stacks 050E "representable_implies_dm"]
theorem isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces : IsDM B S hS f := by
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, ?_⟩
  intro U y hy F hF hE
  exact Space.isUnramified_of_mono B S hS
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
    (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) _
    (mono_hom_algebraicSpaceMap_of_subsingleton B S hS U F hF
      (subsingleton_representing_of_relativeDiagonal B S hS 𝒳.val 𝒴.val f.hom hf U y hy F hE))
    (presheaf_locallyOfFiniteType_relativeDiagonal B S hS f hf U y hy F hF hE)

end Stack

end AlgebraicGeometry

end
