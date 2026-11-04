module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypeAtLocally
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Local complete intersection morphisms are perfect

A local complete intersection morphism of schemes is perfect, hence pseudo-coherent, hence
locally of finite presentation: this is **Stacks 069H**.

## Main results

* `AlgebraicGeometry.perfect_of_isLocalCompleteIntersectionMorphism`: part (3) of Stacks 069H.
* `AlgebraicGeometry.pseudoCoherent_of_isLocalCompleteIntersectionMorphism`: part (2).
* `AlgebraicGeometry.locallyOfFinitePresentation_of_isLocalCompleteIntersectionMorphism`:
  part (1).

Three auxiliary results of independent interest are proved on the way:

* `AlgebraicGeometry.locallyOfFiniteType_of_isLocalCompleteIntersectionMorphism`: a local
  complete intersection morphism is locally of finite type.
* `AlgebraicGeometry.perfect_of_forall_exists_open`: perfectness of a morphism locally of finite
  type may be checked on an open neighbourhood of each point of the source.
* `AlgebraicGeometry.appLE_opens_ι_comp`: restricting a morphism to an open subscheme of its
  source does not change the map on sections over an open of that subscheme.

## Implementation notes

The source proves part (3) first and deduces (2) and (1) from it, through the implications
"perfect `⇒` pseudo-coherent `⇒` locally of finite presentation"; those two implications are
`AlgebraicGeometry.pseudoCoherent_of_perfect` (the first conjunct of Stacks 067H) and Stacks
0682, so the deduction is reproduced verbatim here.

Part (3) is local on the source, because a local complete intersection morphism only factors as
a Koszul-regular immersion followed by a smooth morphism on a neighbourhood of each point. The
source appeals to Stacks 069D, which says that perfectness is fppf-local on the source; only the
Zariski case of that is needed, and it is `AlgebraicGeometry.perfect_of_forall_exists_open`. Its
proof runs the affine-local criterion of Stacks 0686 against the cover of the
source by those affine opens that sit inside some open on which the morphism is already known to
be perfect.

The index type in that proof is a subtype of `(U : X.Opens) × U.toScheme.Opens`, so that the
affine open of `X` is presented as `U.ι ''ᵁ W` for an affine open `W` of the open subscheme
`U.toScheme`. That is what makes `AlgebraicGeometry.appLE_opens_ι_comp` an equation between two
maps on sections rather than an equation modulo an `eqToHom`: the rings `Γ(U.toScheme, W)` and
`Γ(X, U.ι ''ᵁ W)` are the same by definition, whereas `Γ(U.toScheme, U.ι ⁻¹ᵁ W')` and
`Γ(X, W')` for an affine open `W'` of `X` inside `U` are only canonically isomorphic. For the
same reason the identity morphism produced by `AlgebraicGeometry.Scheme.Opens.ι_appLE` is
cancelled against a hypothesis written out at the one inequality it is applied to, rather than
by a general simp lemma: `CategoryTheory.homOfLE_refl` is stated for the abbreviation
`LE.le.hom` and so does not rewrite an occurrence of `CategoryTheory.homOfLE`.

The hypothesis of Stacks 069H is `AlgebraicGeometry.IsLocalCompleteIntersectionMorphism`, which
is Stacks 069F and is a plain predicate rather than a class, so the three results below take it
as an explicit argument and are not instances.

## References

* [The Stacks Project, Lemma 37.62.4 (069H)](https://stacks.math.columbia.edu/tag/069H)
* [The Stacks Project, Definition 37.62.2 (069F)](https://stacks.math.columbia.edu/tag/069F)
* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Lemma 37.61.5 (068A)](https://stacks.math.columbia.edu/tag/068A)
* [The Stacks Project, Lemma 37.61.7 (068C)](https://stacks.math.columbia.edu/tag/068C)
* [The Stacks Project, Lemma 37.61.4 (0689)](https://stacks.math.columbia.edu/tag/0689)
* [The Stacks Project, Lemma 37.61.14 (069D)](https://stacks.math.columbia.edu/tag/069D)
* [The Stacks Project, Lemma 37.60.3 (0682)](https://stacks.math.columbia.edu/tag/0682)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

universe u

/-- A local complete intersection morphism of schemes is locally of finite type, being of finite
type at every point of its source by part (1) of Stacks 069F. -/
theorem locallyOfFiniteType_of_isLocalCompleteIntersectionMorphism {X S : Scheme.{u}}
    {f : X ⟶ S} (hf : IsLocalCompleteIntersectionMorphism f) : LocallyOfFiniteType f :=
  LocallyOfFiniteType.of_forall_finiteTypeAt f fun x ↦ (hf x).finiteTypeAt

/-- Restricting a morphism of schemes to an open subscheme `U` of its source does not change the
map on sections over an open `W` of `U`, viewed as the open `U.ι ''ᵁ W` of the source. -/
theorem appLE_opens_ι_comp {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (V : S.Opens) (W : U.toScheme.Opens) (e : W ≤ (U.ι ≫ f) ⁻¹ᵁ V)
    (e' : U.ι ''ᵁ W ≤ f ⁻¹ᵁ V) :
    (U.ι ≫ f).appLE V W e = f.appLE V (U.ι ''ᵁ W) e' := by
  rw [← Scheme.Hom.appLE_comp_appLE U.ι f V (U.ι ''ᵁ W) W e'
    (by exact (U.ι.preimage_image_eq W).ge)]
  have key : ∀ (h : U.ι ''ᵁ W ≤ U.ι ''ᵁ W),
      f.appLE V (U.ι ''ᵁ W) e' ≫ X.presheaf.map (homOfLE h).op
        = f.appLE V (U.ι ''ᵁ W) e' := by
    intro h
    rw [show homOfLE h = 𝟙 (U.ι ''ᵁ W) from rfl]
    simp
  simp only [Scheme.Opens.ι_appLE]
  exact key _

/-- Perfectness of a morphism of schemes locally of finite type is Zariski-local on the source:
if every point of the source has an open neighbourhood on which the restriction of the morphism
is perfect, then the morphism is perfect.

This is the Zariski case of Stacks 069D, which states the same for the fppf topology. It is
proved from the affine-local criterion of Stacks 0686, applied to the cover of the source by the
affine opens contained in such a neighbourhood. -/
theorem perfect_of_forall_exists_open {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ Perfect (U.ι ≫ f)) : Perfect f := by
  rw [perfect_iff_exists_affine_openCover f]
  refine ⟨S.affineOpens, fun V ↦ V.1, iSup_affineOpens_eq_top S, fun V ↦ V.2, fun V ↦ ?_⟩
  refine ⟨{ p : (U : X.Opens) × U.toScheme.Opens //
      IsAffineOpen p.2 ∧ Perfect (p.1.ι ≫ f) ∧ p.1.ι ''ᵁ p.2 ≤ f ⁻¹ᵁ V.1 },
    fun p ↦ p.1.1.ι ''ᵁ p.1.2, ?_, ?_, ?_⟩
  · refine le_antisymm (iSup_le fun p ↦ p.2.2.2) fun x hx ↦ ?_
    obtain ⟨U, hxU, hU⟩ := h x
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWle⟩ :=
      U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
        (show (⟨x, hxU⟩ : U.toScheme) ∈ (U.ι ⁻¹ᵁ (f ⁻¹ᵁ V.1) : U.toScheme.Opens) from hx)
        (U.ι ⁻¹ᵁ (f ⁻¹ᵁ V.1)).2
    exact Opens.mem_iSup.mpr
      ⟨⟨⟨U, W⟩, hW, hU, (U.ι.image_mono hWle).trans (U.ι.image_preimage_le _)⟩,
        (Scheme.Opens.mem_ι_image_iff U).mpr hxW⟩
  · exact fun p ↦ p.2.1.image_of_isOpenImmersion p.1.1.ι
  · rintro ⟨⟨U, W⟩, hW, hU, hle⟩
    have e : W ≤ (U.ι ≫ f) ⁻¹ᵁ V.1 := fun y hy ↦
      hle ((Scheme.Opens.mem_ι_image_iff U).mpr hy)
    have hmap := Perfect.perfect_appLE (U.ι ≫ f) W hW V.1 V.2 e
    rw [appLE_opens_ι_comp f U V.1 W e hle] at hmap
    exact hmap

/-- **Stacks 069H, part (3).** A local complete intersection morphism of schemes is perfect.

Perfectness is Zariski-local on the source, and on a neighbourhood of each point the morphism
factors as a Koszul-regular immersion followed by a smooth morphism; the first is perfect by
Stacks 068C, the second is flat and locally of finite presentation and hence perfect by
Stacks 068A, and perfectness is stable under composition by Stacks 0689. -/
@[stacks 069H "part (3): perfect", sga "6 III 4.1.1", sga "6 VIII 1.7", sga "6 X 7.1" "partial"]
theorem perfect_of_isLocalCompleteIntersectionMorphism {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsLocalCompleteIntersectionMorphism f) : Perfect f := by
  have hft : LocallyOfFiniteType f :=
    locallyOfFiniteType_of_isLocalCompleteIntersectionMorphism hf
  refine perfect_of_forall_exists_open f fun x ↦ ?_
  obtain ⟨-, U, hxU, P, i, π, hi, hik, hπ, hfac⟩ := hf x
  let _ : IsImmersion i := hi
  let _ : Smooth π := hπ
  exact ⟨U, hxU, hfac ▸ @perfect_comp _ _ _ i π (perfect_of_isKoszulRegularImmersion i hik)
    ((flat_and_perfect_iff_flat_and_locallyOfFinitePresentation π).mpr
      ⟨inferInstance, inferInstance⟩).2⟩

/-- **Stacks 069H, part (2).** A local complete intersection morphism of schemes is
pseudo-coherent, because it is perfect and a perfect morphism is pseudo-coherent. -/
@[stacks 069H "part (2): pseudo-coherent", sga "6 VIII 1.7" "partial"]
theorem pseudoCoherent_of_isLocalCompleteIntersectionMorphism {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsLocalCompleteIntersectionMorphism f) : PseudoCoherent f :=
  have : Perfect f := perfect_of_isLocalCompleteIntersectionMorphism hf
  pseudoCoherent_of_perfect f

/-- **Stacks 069H, part (1).** A local complete intersection morphism of schemes is locally of
finite presentation, because it is pseudo-coherent and a pseudo-coherent morphism is locally of
finite presentation by Stacks 0682. -/
@[stacks 069H "part (1): locally of finite presentation"]
theorem locallyOfFinitePresentation_of_isLocalCompleteIntersectionMorphism
    {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : IsLocalCompleteIntersectionMorphism f) : LocallyOfFinitePresentation f :=
  have : PseudoCoherent f := pseudoCoherent_of_isLocalCompleteIntersectionMorphism hf
  locallyOfFinitePresentation_of_pseudoCoherent f

end AlgebraicGeometry

end
