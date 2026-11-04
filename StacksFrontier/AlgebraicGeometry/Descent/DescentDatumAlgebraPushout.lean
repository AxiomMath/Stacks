module

public import StacksFrontier.AlgebraicGeometry.Descent.DescendedRingOpenSubset
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDatumSectionsPushout

/-!
# The geometric input of step 4 of Stacks 0APK, in the shape algebra descent consumes

`AlgebraicGeometry.ModuleCat.isPushout_descentInvariants_of_isPushout` — the algebraic
core of step 4 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) —
asks for two pushout squares of commutative rings whose four outer legs are `algebraMap`s, an
isomorphism `Φ` of their apexes, and two equations saying that `Φ` lies over `A ⊗[R] A`.
`StacksFrontier.AlgebraicGeometry.Descent.DescentDatumSectionsPushout` produces all of that from a
descent datum, but with the legs the plain `appTop` and restriction morphisms of geometry rather
than `algebraMap`s. This file performs the translation.

The algebra structures cannot be instances: `Algebra Γ(S, ⊤) Γ(X, ⊤)` holds only through the
particular ring map `f.appTop`. They are therefore taken as hypotheses, together with the
equations identifying each `algebraMap` with the geometric morphism it is meant to be — which is
what `RingHom.toAlgebra` gives a consumer, as recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.Modules.AlgebraDescentFromPushout`.

## Main results

* `AlgebraicGeometry.DescentDatum.isPushout_algebraMap_transitionSource` : the square `hP` of
  `AlgebraicGeometry.ModuleCat.isPushout_descentInvariants_of_isPushout`, exhibiting
  `Γ(E ×_S X, 𝒪)` as `Γ(E, 𝒪_V|_E) ⊗_{Γ(S, ⊤)} Γ(X, ⊤)`.
* `AlgebraicGeometry.DescentDatum.isPushout_algebraMap_transitionTarget` : the square `hQ`,
  exhibiting `Γ(X ×_S E, 𝒪)` as `Γ(X, ⊤) ⊗_{Γ(S, ⊤)} Γ(E, 𝒪_V|_E)`.
* `AlgebraicGeometry.DescentDatum.algebraMap_comp_transitionSectionsIso_hom` and
  `AlgebraicGeometry.DescentDatum.transitionSectionsIso_hom_eq_algebraMap_comp` : the hypotheses
  `h1` and `h2` of `AlgebraicGeometry.ModuleCat.algebraTransitionOfPushout`.

Together these four are the complete geometric input of step 4; what remains before
`AlgebraicGeometry.ModuleCat.isPushout_descentInvariants_of_isPushout` can be applied is its
faithful-flatness instance — in the situation of Tag 0APK the hypothesis that `Γ(S, ⊤) ⟶ Γ(X, ⊤)`
is faithfully flat — and its coassociativity hypothesis `hkey`, which is the cocycle condition
that the source of Tag 0APK transports with "details omitted".

## Implementation notes

Each result is one `rw` with the identification equations followed by the corresponding statement
of `StacksFrontier.AlgebraicGeometry.Descent.DescentDatumSectionsPushout`. The second square is the
*flip* of the one proved there, because `AlgebraicGeometry.ModuleCat.algebraTransitionOfPushout`
reads its second square with the `Γ(X, ⊤)`-leg first, so that its apex is `A ⊗[R] C` rather than
`C ⊗[R] A`.

No tag is placed: Tag 0APJ is carried by
`AlgebraicGeometry.isPushout_sectionsRingOnSubset_of_flat`, Tag 023N is module-only mathematics
and must not be placed on an algebra statement, and Tag 0APK is for arbitrary fpqc covering
families while this is the affine single-morphism case.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (E : Set D.over.left)

/-! ### The two pushout squares with `algebraMap` legs -/

section Squares

variable [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)]
    [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)
    [IsAffine S] [IsAffine X] [Flat f] [QuasiSeparatedSpace D.over.left]

include hRA hRC in
/-- **The square `hP` of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK).**  With `R = Γ(S, ⊤)`,
`A = Γ(X, ⊤)` and `C = Γ(E, 𝒪_V|_E)`, the ring of functions on `E ×_S X` is `C ⊗[R] A`.

This is `AlgebraicGeometry.DescentDatum.isPushout_sectionsRingOnSubset_transitionSource` with its
two outer legs rewritten as `algebraMap`s. -/
theorem isPushout_algebraMap_transitionSource {I : Type u} [Nonempty I]
    (U : I → D.over.left.Opens) (hU : ∀ i, IsCompact (U i : Set D.over.left))
    (hE : E = ⋂ i, (U i : Set D.over.left)) :
    IsPushout (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)))
      (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)))
      (Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
        (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _))
      ((pullback.snd (D.over.hom ≫ f) f).appTop ≫
        (pullback (D.over.hom ≫ f) f).topToSubset
          (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) := by
  rw [hRA, hRC]
  exact D.isPushout_sectionsRingOnSubset_transitionSource U hU E hE

include hRA hRC in
/-- **The square `hQ` of step 4 of the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK).**  With the same notation, the ring
of functions on `X ×_S E` is `A ⊗[R] C`.

This is `AlgebraicGeometry.DescentDatum.isPushout_sectionsRingOnSubset_transitionTarget`,
flipped so that the `Γ(X, ⊤)`-leg comes first, with its two outer legs rewritten as
`algebraMap`s. -/
theorem isPushout_algebraMap_transitionTarget {I : Type u} [Nonempty I]
    (U : I → D.over.left.Opens) (hU : ∀ i, IsCompact (U i : Set D.over.left))
    (hE : E = ⋂ i, (U i : Set D.over.left)) :
    IsPushout (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)))
      ((pullback.fst f (D.over.hom ≫ f)).appTop ≫
        (pullback f (D.over.hom ≫ f)).topToSubset
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
      (Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
        (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _)) := by
  rw [hRA, hRC]
  exact (D.isPushout_sectionsRingOnSubset_transitionTarget U hU E hE).flip

end Squares

/-! ### `Φ` lies over `A ⊗[R] A`, with `algebraMap` legs -/

section Compatibility

variable [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    (hAC : CommRingCat.ofHom
        (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E)
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))

include hAC in
/-- **The hypothesis `h1` of `AlgebraicGeometry.ModuleCat.algebraTransitionOfPushout`.**  The
`C`-leg of the first square, precomposed with `A ⟶ C` and followed by `Φ`, is the `A`-leg of the
second square. -/
theorem algebraMap_comp_transitionSectionsIso_hom :
    CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) ≫
        Scheme.sectionsRingOnSubsetMap (pullback.fst (D.over.hom ≫ f) f) E
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) (Set.Subset.refl _) ≫
          (D.transitionSectionsIso E h₁ h₂).hom =
      (pullback.fst f (D.over.hom ≫ f)).appTop ≫
        (pullback f (D.over.hom ≫ f)).topToSubset
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) := by
  rw [hAC]
  exact D.structureMap_comp_transitionSectionsIso_hom E h₁ h₂

include hAC in
/-- **The hypothesis `h2` of `AlgebraicGeometry.ModuleCat.algebraTransitionOfPushout`.**  The
`A`-leg of the first square followed by `Φ` is the `C`-leg of the second square, precomposed with
`A ⟶ C`. -/
theorem transitionSectionsIso_hom_eq_algebraMap_comp :
    ((pullback.snd (D.over.hom ≫ f) f).appTop ≫
          (pullback (D.over.hom ≫ f) f).topToSubset
            (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E)) ≫
        (D.transitionSectionsIso E h₁ h₂).hom =
      CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) ≫
        Scheme.sectionsRingOnSubsetMap (pullback.snd f (D.over.hom ≫ f)) E
          (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) (Set.Subset.refl _) := by
  rw [hAC]
  exact D.base_comp_transitionSectionsIso_hom E h₁ h₂

end Compatibility

end DescentDatum

end AlgebraicGeometry

end

end
