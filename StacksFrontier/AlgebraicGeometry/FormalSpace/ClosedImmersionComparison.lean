module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillanCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianCharacterization
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Closed immersions into a formal algebraic space: comparing the sheaf and presheaf notions

Let `S` be a scheme contained in a big fppf site `B`. Two conditions on a morphism of fppf
sheaves over `S` are called "being a closed immersion" in the Stacks Project, and they are
phrased against two different Yoneda embeddings.

* Stacks 0ANP, `AlgebraicGeometry.FormalSpace.IsClosedImmersion`, tests the morphism of
  *underlying presheaves* against the universe-lifted Yoneda embedding
  `CategoryTheory.uliftYoneda`: the morphism is representable by algebraic spaces, and each
  represented base change of it is a closed immersion in the relative sense of Stacks 03XZ.
* Stacks 0AIC, `AlgebraicGeometry.FormalSpace.IsClosedImmersionInto`, tests the morphism of
  *sheaves* against the sheafified Yoneda embedding `CategoryTheory.Sheaf.sheafifiedYoneda`:
  it is the relative morphism property, along that embedding, of being a closed immersion of
  schemes.

This file proves that the first implies the second, which is the comparison the proof of
Stacks 0AKM needs, and then uses it to close the last open implication of Stacks 0AKM, namely
(1) ⇒ (2): a Noetherian affine formal algebraic space has Noetherian closed subschemes.

The comparison has nothing to do with formal algebraic spaces: it is the observation that the
big fppf site of `S` is subcanonical, so that a sheafified representable is already the
universe-lifted Yoneda presheaf, and that a square of sheaves is cartesian as soon as its
square of underlying presheaves is, the inclusion of sheaves into presheaves being fully
faithful. The 0ANP hypothesis is used in the shape of a single cartesian square per
scheme-valued point of the target — produced by testing the relative representability of a
base change against an identity — and the closed-immersion property of its represented leg;
`CategoryTheory.MorphismProperty.relative.of_exists` upgrades one such square per point to
the property for *every* represented cartesian square.

Granted the comparison, Stacks 0AKM (1) ⇒ (2) is a composition of results in the library.
`AlgebraicGeometry.FormalSpace.isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian`
turns Noetherianness of `X` into a presentation `X = colim X_λ` by Noetherian affine schemes;
`AlgebraicGeometry.FormalSpace.exists_stage_isClosedImmersion_of_isClosedImmersionInto`
factors a closed immersion `T ⟶ X` of a scheme of the site through a stage `X_λ` by a closed
immersion of schemes; and a scheme closed-immersed in a Noetherian scheme is Noetherian,
being of finite type over it and a closed subspace of a compact space.

## Main results

* `AlgebraicGeometry.FormalSpace.isClosedImmersionInto_of_isClosedImmersion`: a closed
  immersion of fppf sheaves in the sense of Stacks 0ANP is a closed immersion in the sense of
  Stacks 0AIC.
* `AlgebraicGeometry.FormalSpace.hasNoetherianClosedSubschemes_of_isNoetherian`:
  **Stacks 0AKM, (1) ⇒ (2)**, every scheme of the site closed-immersed in a Noetherian affine
  formal algebraic space is Noetherian.
* `AlgebraicGeometry.FormalSpace.isNoetherian_tfae'`: **Stacks 0AKM**, the full equivalence of
  all four conditions of the tag.

## Implementation notes

The private `AlgebraicGeometry.FormalSpace.sheafifiedYonedaCompToPresheaf` is the comparison
isomorphism identifying the underlying presheaf of a sheafified representable with the
universe-lifted Yoneda presheaf; it is the composite of
`CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'`, which is where subcanonicality of the
topology enters, with Mathlib's
`CategoryTheory.GrothendieckTopology.uliftYonedaCompSheafToPresheaf`. All the bookkeeping of
the comparison lemma is the transport of one cartesian square along that isomorphism.

The comparison is stated for an arbitrary morphism of fppf sheaves, not only for one out of a
sheafified representable, since neither hypothesis constrains the source. Its converse is
proved, as a private helper, in
`StacksFrontier.AlgebraicGeometry.FormalSpace.NoetherianCharacterization`; together the two say
that the notions of Stacks 0ANP and of Stacks 0AIC agree, but the converse is not restated
here.

Noetherianness of a scheme closed-immersed in a Noetherian scheme is assembled from Mathlib:
a closed immersion is an immersion, hence locally of finite type, so
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` gives the local half, and a closed
embedding into a compact space has compact source.

`AlgebraicGeometry.FormalSpace.isNoetherian_tfae'` is the primed form of
`AlgebraicGeometry.FormalSpace.isNoetherian_tfae`, which states the same equivalence for the
three conditions (1), (3) and (4) that were available before condition (2) could be reached.

## References

* [Stacks Project, Tag 0AKM](https://stacks.math.columbia.edu/tag/0AKM)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Noetherian schemes and closed immersions -/

/-- A scheme admitting a closed immersion into a Noetherian scheme is Noetherian: a closed
immersion is locally of finite type, which carries the locally Noetherian condition, and a
closed embedding into a compact space has compact source. -/
@[ega "IV 1.3.3" "special case"]
private theorem isNoetherian_of_isClosedImmersion {T Y : Scheme.{u}} (g : T ⟶ Y)
    [AlgebraicGeometry.IsClosedImmersion g] (hY : AlgebraicGeometry.IsNoetherian Y) :
    AlgebraicGeometry.IsNoetherian T := by
  have : AlgebraicGeometry.IsNoetherian Y := hY
  have : IsLocallyNoetherian T := AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace T := g.isClosedEmbedding.compactSpace
  exact AlgebraicGeometry.IsNoetherian.mk

/-! ### From Stacks 0ANP to Stacks 0AIC -/

/-- The inclusion of the fppf sheaves over `S` into the presheaves on the big fppf site of
`S`. Stacks 0ANP is a condition on the image of a morphism under this functor, while
Stacks 0AIC is a condition on the morphism itself. -/
private abbrev toPresheaf :
    FppfSheaf B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))

/-- The underlying presheaf of a sheafified representable on the big fppf site of `S` is the
universe-lifted Yoneda presheaf. The topology is subcanonical, so sheafifying a representable
changes nothing. -/
private noncomputable def sheafifiedYonedaCompToPresheaf :
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS) ⋙ toPresheaf B S hS ≅
      uliftYoneda.{u + 1} :=
  Functor.isoWhiskerRight
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' (BigFppfOver.topology B S hS))
      (toPresheaf B S hS) ≪≫
    GrothendieckTopology.uliftYonedaCompSheafToPresheaf.{u + 1} (BigFppfOver.topology B S hS)

/-- The property of a morphism of the big fppf site of `S` that the underlying morphism of
schemes is a closed immersion. Both Stacks 0ANP and Stacks 0AIC are the relative form of this
property, the first along the universe-lifted Yoneda embedding of presheaves and the second
along the sheafified Yoneda embedding. -/
private abbrev closedImmersionOfSite : MorphismProperty (BigFppfOver B S hS) :=
  MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)

/-- The second half of Stacks 0ANP in the shape of a relative morphism property: a closed
immersion of fppf sheaves has all the represented base changes of its underlying morphism of
presheaves closed immersions of the site.

Stacks 0ANP provides, for a scheme-valued point `ξ` of the target, that the base change of
the morphism along `ξ` is *itself* relatively a closed immersion; testing that against the
identity of the represented point produces one cartesian square over `ξ` whose represented
leg is a closed immersion, and that is enough because the universe-lifted Yoneda embedding is
fully faithful. -/
private theorem relative_closedImmersionOfSite_of_isClosedImmersion
    {Y Z : FppfSheaf B S hS} (f : Y ⟶ Z) (hf : IsClosedImmersion B S hS f) :
    (closedImmersionOfSite B S hS).relative (uliftYoneda.{u + 1}) f.hom := by
  obtain ⟨hrep, hprop⟩ := hf
  apply MorphismProperty.relative.of_exists
  intro U ξ
  have hq : (closedImmersionOfSite B S hS).relative (uliftYoneda.{u + 1})
      (pullback.fst ξ f.hom) := hprop U ξ
  obtain ⟨V, t, s, hpb⟩ := hq.rep (𝟙 ((uliftYoneda.{u + 1}).obj U))
  have ht : closedImmersionOfSite B S hS t := hq.property (g := 𝟙 _) s t hpb
  have _ : IsIso s := hpb.isIso_fst_of_isIso
  have hV : IsPullback ((uliftYoneda.{u + 1}).map t) (s ≫ pullback.snd ξ f.hom) ξ f.hom := by
    apply (IsPullback.of_hasPullback ξ f.hom).of_iso'
      (asIso s) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simpa using hpb.w
    all_goals simp
  exact ⟨V, s ≫ pullback.snd ξ f.hom, t, hV.flip, ht⟩

/-- **A closed immersion of fppf sheaves in the sense of Stacks 0ANP is one in the sense of
Stacks 0AIC.** The first notion is a condition on the underlying morphism of presheaves,
tested against the universe-lifted Yoneda embedding; the second is the relative
closed-immersion property of the morphism of sheaves, tested against the sheafified Yoneda
embedding.

The two agree because the big fppf site of `S` is subcanonical, so the underlying presheaf of
a sheafified representable is the universe-lifted Yoneda presheaf
(`AlgebraicGeometry.FormalSpace.sheafifiedYonedaCompToPresheaf`), and because the inclusion of
sheaves into presheaves is fully faithful, hence reflects cartesian squares: a scheme-valued
point of the target in the sheaf category becomes one in the presheaf category, the
hypothesis supplies a cartesian square over it whose represented leg is a closed immersion of
schemes, and that square descends to the sheaf category. -/
theorem isClosedImmersionInto_of_isClosedImmersion {Y Z : FppfSheaf B S hS} (f : Y ⟶ Z)
    (hf : IsClosedImmersion B S hS f) : IsClosedImmersionInto B S hS f := by
  have hQ := relative_closedImmersionOfSite_of_isClosedImmersion B S hS f hf
  set γ := sheafifiedYonedaCompToPresheaf B S hS
  apply MorphismProperty.relative.of_exists
  intro U ξ
  obtain ⟨V, t, p, hpb⟩ := hQ.rep ((γ.app U).inv ≫ (toPresheaf B S hS).map ξ)
  refine ⟨V, (toPresheaf B S hS).preimage ((γ.app V).hom ≫ p), t, ?_,
    hQ.property _ p t hpb⟩
  apply IsPullback.of_map_of_faithful (toPresheaf B S hS)
  rw [Functor.map_preimage]
  refine hpb.of_iso' (γ.app V) (Iso.refl _) (γ.app U) (Iso.refl _) (by simp) ?_ (by simp) ?_
  · simpa using (γ.hom.naturality t).symm
  · rw [Iso.hom_inv_id_assoc]
    simp

/-! ### Stacks 0AKM, condition (1) implies condition (2) -/

/-- **Stacks 0AKM, (1) ⇒ (2).** Every scheme of the site admitting a closed immersion into a
Noetherian affine formal algebraic space `X` is a Noetherian scheme.

By the implication (1) ⇒ (3) of the same tag, `X` has a presentation by Noetherian affine
schemes. A closed immersion `T ⟶ X` in the sense of Stacks 0ANP is one in the sense of
Stacks 0AIC, so the geometric step of Stacks 0AIC factors it through a stage of that
presentation by a closed immersion of schemes `T ⟶ X_λ`. As `X_λ` is Noetherian, so is `T`. -/
@[stacks 0AKM "(1) ⇒ (2)"]
theorem hasNoetherianClosedSubschemes_of_isNoetherian {X : FppfSheaf B S hS}
    (hX : IsNoetherian B S hS X) : HasNoetherianClosedSubschemes B S hS X := by
  obtain ⟨-, hpres⟩ :=
    isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian B S hS hX
  obtain ⟨I, pre, hne, hdir, D, hD, ⟨e⟩, hstage⟩ := hpres
  let _ : Preorder I := pre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  intro T g hg
  obtain ⟨i, h, hci, -⟩ := exists_stage_isClosedImmersion_of_isClosedImmersionInto B S hS D hD
    e g (isClosedImmersionInto_of_isClosedImmersion B S hS g hg)
  have _ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map h) := hci
  exact isNoetherian_of_isClosedImmersion ((BigFppfOver.toScheme B S hS).map h) (hstage i)

/-! ### The equivalence of all four conditions of Stacks 0AKM -/

/-- **Stacks 0AKM.** For an fppf sheaf `X` on the big fppf site of `S` the following are
equivalent:

1. `X` is a Noetherian affine formal algebraic space;
2. `X` is adic\* and every scheme of the site closed-immersed in `X` is Noetherian;
3. `X` is adic\* and some presentation of it by affine thickenings has Noetherian stages;
4. `X` is weakly adic and some presentation of it by affine thickenings has Noetherian stages.

Each condition already contains the requirement that `X` be a McQuillan affine formal
algebraic space. This is the primed form of
`AlgebraicGeometry.FormalSpace.isNoetherian_tfae`, which records the equivalence of
conditions (1), (3) and (4) alone. -/
@[stacks 0AKM]
theorem isNoetherian_tfae' (X : FppfSheaf B S hS) :
    List.TFAE
      [IsNoetherian B S hS X,
        IsAdicStar B S hS X ∧ HasNoetherianClosedSubschemes B S hS X,
        IsAdicStar B S hS X ∧ HasNoetherianAffinePresentation B S hS X,
        IsWeaklyAdic B S hS X ∧ HasNoetherianAffinePresentation B S hS X] := by
  tfae_have 1 → 2 := fun h ↦
    ⟨(isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian B S hS h).1,
      hasNoetherianClosedSubschemes_of_isNoetherian B S hS h⟩
  tfae_have 2 → 1 := fun h ↦ isNoetherian_of_hasNoetherianClosedSubschemes B S hS h.1 h.2
  tfae_have 1 → 3 := isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian B S hS
  tfae_have 3 → 4 := fun h ↦ ⟨isWeaklyAdic_of_isAdicStar B S hS h.1, h.2⟩
  tfae_have 4 → 3 := fun h ↦ ⟨isAdicStar_of_isWeaklyAdic B S hS h.1 h.2, h.2⟩
  tfae_have 3 → 1 := fun h ↦ isNoetherian_of_isAdicStar B S hS h.1 h.2
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
