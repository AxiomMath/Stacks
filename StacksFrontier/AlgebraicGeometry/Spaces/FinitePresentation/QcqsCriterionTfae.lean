module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingIff
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSiteLimitCone
import all StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion

/-!
# Local finite presentation through limits of quasi-compact quasi-separated spaces

For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, Stacks 0CP4 adds to the two
equivalent conditions of Stacks 04AK, (1) `f` is locally of finite presentation and (2) `f` is
relatively limit preserving, a third: (3) for every directed inverse limit `T = lim T_i` of
quasi-compact and quasi-separated algebraic spaces with affine transition morphisms, the square
of morphism sets

    colim_i Mor(T_i, X) → Mor(T, X)
          ↓                    ↓
    colim_i Mor(T_i, Y) → Mor(T, Y)

is cartesian. This file proves the three conditions equivalent.

## Main results

* `AlgebraicGeometry.Space.relativelyLimitPreserving_of_qcqsLimitSquare_of_convention`: the
  implication (3) ⇒ (2).
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_tfae_qcqsLimitSquare`: Stacks 0CP4,
  the equivalence of (1), (2) and (3).

## Implementation notes

The limits in (3) are read under the chapter's standing convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`: the limits of the affine charts of the
system lie in the site. Nothing is asked of the index beyond being cofiltered in the universe
of the schemes, the index universe at which (2) is read. Without the convention the limit of
the system, computed in presheaves on the size-bounded site, need not be the limit of algebraic
spaces of the source (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentation/QcqsCriterion.lean`).

The implication (2) ⇒ (3) is
`AlgebraicGeometry.Space.isPullback_qcqsLimitSquare_of_siteContainsBaseChangeLimits`, the
source's proof through two systems of affine étale charts of a stage.

The implication (3) ⇒ (2) is the source's "it is clear": a cofiltered system of affine objects
of the site whose limit of schemes lies in the site is, through the Yoneda embedding, a system
of quasi-compact and quasi-separated algebraic spaces with affine transition morphisms which
satisfies the convention (`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_affineYoneda`),
and the square of (3) for it is, by the Yoneda lemma, the affine-limit comparison square which
characterises relative limit preservation by Tag 06BC
(`AlgebraicGeometry.relativelyLimitPreserving_iff_affineLimit_isPullback`). No bound on the size
of the index is needed for this, which is why (3) is read under the convention rather than for
systems smaller than the cofinality of the cutoff, as in
`AlgebraicGeometry.Space.QcqsLimitSquare`: the affine systems of that bounded form do not reach
the systems of finitely presented algebras which detect local finite presentation.

## References

* [Stacks Project, Tag 0CP4](https://stacks.math.columbia.edu/tag/0CP4)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 06BC](https://stacks.math.columbia.edu/tag/06BC)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0CP4, the implication (3) ⇒ (2).** A morphism `f : X ⟶ Y` of presheaves on the big
fppf site over `S` is relatively limit preserving as soon as the comparison square of morphism
sets is cartesian for every cofiltered inverse system of quasi-compact and quasi-separated
algebraic spaces with affine transition morphisms satisfying the chapter's convention (tag
07SD).

A cofiltered system of affine objects of the site whose limit of schemes lies in the site is,
through the Yoneda embedding, such a system, and the square for it is the affine-limit
comparison square of Tag 06BC. -/
theorem relativelyLimitPreserving_of_qcqsLimitSquare_of_convention (f : X ⟶ Y)
    (h : ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D),
      SiteContainsBaseChangeLimits B S hS D →
      (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
      (∀ i, IsQuasiCompactSpace B S hS (D.obj i)) →
      (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) →
      (∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a)) →
      IsLimit c →
      IsPullback
        (colimit.desc (D.op ⋙ yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1})
          ((yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))
        (colimMap (Functor.whiskerLeft D.op
          (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u + 1})))
        (uliftFunctor.{u + 1, u + 1}.map ((yoneda.map f).app (op c.pt)))
        (colimit.desc (D.op ⋙ yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1})
          ((yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))) :
    RelativelyLimitPreserving.{u, u, u, u} B S hS f := by
  refine (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, u, u, u} B S hS f).mpr
    fun I _ _ D c hsl hAff hAffpt => ?_
  have _ : IsConnected I := IsCofiltered.isConnected I
  have hc : IsLimit c := BigFppfOver.isLimit_of_isLimit_toScheme B S hS hsl
  let D' : I ⥤ BigAffineFppf B S hS := ObjectProperty.lift _ D hAff
  let c' : Cone D' :=
    { pt := ⟨c.pt, hAffpt⟩
      π := { app := fun i => ObjectProperty.homMk (c.π.app i)
             naturality := fun i j g => by
               ext1
               exact c.π.naturality g } }
  have hconv : SiteContainsBaseChangeLimits B S hS (D ⋙ yoneda) :=
    siteContainsBaseChangeLimits_affineYoneda (D := D') c' hsl
  have hB := h I (D ⋙ yoneda) (yoneda.mapCone c) hconv
    (fun i => isAlgebraicSpace_yoneda B S hS (D.obj i))
    (fun i => isQuasiCompactSpace_yoneda_of_isAffine B S hS (D.obj i) (hAff i))
    (fun i => isAbsolutelyQuasiSeparated_yoneda_of_isAffine B S hS hZ (D.obj i) (hAff i))
    (fun {i j} a => isAffineHom_yoneda_map B S hS (D.map a) (hAff i) (hAff j))
    (isLimitOfPreserves yoneda hc)
  have hB' := (isPullback_colim_iff (D ⋙ yoneda) (yoneda.mapCone c)
    (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u + 1})).mp hB
  exact (isPullback_colim_iff D c (Functor.whiskerRight f uliftFunctor.{u, u})).mpr
    ⟨(colimInj_uliftFunctor_iff f).mpr
        ((colimInj_yoneda_iff B S hS D c f).mp
          ((colimInj_uliftFunctor_iff (yoneda.map f)).mp hB'.1)),
      (colimSurj_uliftFunctor_iff f).mpr
        ((colimSurj_yoneda_iff B S hS D c f).mp
          ((colimSurj_uliftFunctor_iff (yoneda.map f)).mp hB'.2))⟩

/-- **Stacks 0CP4.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S`, the following are
equivalent:

1. `f` is locally of finite presentation;
2. `f` is relatively limit preserving (the two equivalent conditions of Stacks 04AK);
3. for every cofiltered inverse system `D` of quasi-compact and quasi-separated algebraic spaces
   over `S` with affine transition morphisms and every limit `c` of it, the square of morphism
   sets `colim_i Mor(D_i, X) → Mor(c, X)` over `colim_i Mor(D_i, Y) → Mor(c, Y)` is cartesian.

The limits in (3) are those of the chapter's standing convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`; relative limit preservation and the
systems of (3) are read at index categories in the universe of the schemes. -/
@[stacks 0CP4 "condition (3) is read for systems satisfying the chapter's standing convention
(tag 07SD), at index categories in the universe of the schemes"]
theorem isLocallyOfFinitePresentation_tfae_qcqsLimitSquare (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    List.TFAE
      [IsLocallyOfFinitePresentation B S hS f,
        RelativelyLimitPreserving.{u, u, u, u} B S hS f,
        ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
          (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D),
          SiteContainsBaseChangeLimits B S hS D →
          (∀ i, IsAlgebraicSpace B S hS (D.obj i)) →
          (∀ i, IsQuasiCompactSpace B S hS (D.obj i)) →
          (∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i)) →
          (∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a)) →
          IsLimit c →
          IsPullback
            (colimit.desc (D.op ⋙ yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1})
              ((yoneda.obj X ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))
            (colimMap (Functor.whiskerLeft D.op
              (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1, u + 1})))
            (uliftFunctor.{u + 1, u + 1}.map ((yoneda.map f).app (op c.pt)))
            (colimit.desc (D.op ⋙ yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1})
              ((yoneda.obj Y ⋙ uliftFunctor.{u + 1, u + 1}).mapCocone c.op))] := by
  tfae_have 1 ↔ 2 := isLocallyOfFinitePresentation_iff_relativelyLimitPreserving B S hS hX hY f
  tfae_have 2 → 3 := fun hrlp I _ _ D c hconv hD hqc hqs hAffine hc =>
    isPullback_qcqsLimitSquare_of_siteContainsBaseChangeLimits B S hS hZ f hX hY hrlp D c hconv
      hD hqc hqs hAffine hc
  tfae_have 3 → 2 := relativelyLimitPreserving_of_qcqsLimitSquare_of_convention B S hS hZ f
  tfae_finish

end AlgebraicGeometry.Space

end
