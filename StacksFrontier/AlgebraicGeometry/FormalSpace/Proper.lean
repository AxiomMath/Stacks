module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProper
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProperLocality

/-!
# Proper morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of formal
algebraic spaces over `S` is *proper* (**Stacks 0AM6**) when it is representable by algebraic
spaces and proper in the Bootstrap sense of Stacks 03XZ: every base change of `f` along a
scheme-valued point of `Y` is a morphism of algebraic spaces which is proper, that is,
separated, of finite type and universally closed.

Properness is the first of the four conditions defining a *formal modification*
(**Stacks 0GDK**): a morphism of locally Noetherian formal algebraic spaces over `S` which is
proper, rig-étale and rig-surjective and whose relative diagonal is again rig-surjective.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsProper`: **Stacks 0AM6**.
* `AlgebraicGeometry.FormalSpace.IsFormalModification`: **Stacks 0GDK**.

## Main results

* `AlgebraicGeometry.FormalSpace.IsProper.isBootstrapFiniteType`: a proper morphism of formal
  algebraic spaces satisfies condition (2) of **Stacks 0AJJ**, which Stacks 0AJJ identifies
  with being of finite type.
* `AlgebraicGeometry.FormalSpace.IsProper.isRepresentable`: a proper morphism of formal
  algebraic spaces is representable by algebraic spaces.
* `AlgebraicGeometry.FormalSpace.IsProper.of_isPullback`: a base change of a proper morphism of
  formal algebraic spaces is proper.
* `AlgebraicGeometry.FormalSpace.isProper_iff_isProperOnSchemeBaseChanges`: clauses (1) and (2)
  of **Stacks 0ART** are equivalent.
* `AlgebraicGeometry.FormalSpace.IsProper.isProperOnSchemeBaseChanges`,
  `AlgebraicGeometry.FormalSpace.isProper_of_isProperOnSchemeBaseChanges`,
  `AlgebraicGeometry.FormalSpace.IsProperOnSchemeBaseChanges.isProperOnAffineBaseChanges`,
  `AlgebraicGeometry.FormalSpace.IsProperOnAffineBaseChanges.isAlgebraicAndProper`,
  `AlgebraicGeometry.FormalSpace.IsProper.hasProperFormalAtlas`: the implications
  (1) ⇒ (2), (2) ⇒ (1), (2) ⇒ (3), (3) ⇒ (4) and (1) ⇒ (5) of **Stacks 0ART**. In the same
  namespace, the reverse implication (4) ⇒ (3) is
  `IsAlgebraicAndProperOnAffineBaseChanges.isProperOnAffineBaseChanges`, the implication
  (3) ⇒ (1) is `IsProperOnAffineBaseChanges.isProper` and the implication (5) ⇒ (1) is
  `HasProperFormalAtlas.isProper`; `isProper_tfae` assembles the first four conditions.

## Implementation notes

The condition does not use the witnesses that the source and the target are formal algebraic
spaces, so it is stated for an arbitrary morphism of fppf sheaves, as the source's Tag 03XZ
condition is, and exactly as `AlgebraicGeometry.FormalSpace.IsBootstrapFiniteType` and
`AlgebraicGeometry.FormalSpace.IsClosedImmersion` are. Representability is
`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpacesULift`, since the sheaves carrying formal
algebraic spaces take values in `Type (u + 1)` rather than in `Type u`; the representability
witness is bundled with the property because it is what makes those base changes algebraic
spaces, so the definition is an existential over that witness rather than a conjunction.

The property tested on the base changes is `AlgebraicGeometry.Space.properPropertyULift`, the
universe-lifted form of the properness of morphisms of algebraic spaces of Stacks 03ZM — separated,
of finite type and universally closed — packaged as a property of morphisms of the category
`AlgebraicGeometry.Space.AlgebraicSpacesULift`. Properness is not representable by schemes, so
unlike the closed immersions of Stacks 0ANP it cannot be tested by handing
`AlgebraicGeometry.Space.HasPropertyULift` a property of morphisms of schemes made relative along
`CategoryTheory.uliftYoneda`; the three conjuncts of Stacks 03ZM are assembled instead.

Since properness is of finite type by definition, a proper morphism of formal algebraic spaces
is of finite type in the sense of Stacks 0AM4 part (2) with the same representability witness,
which is the monotonicity of Stacks 0AM1 for the universe-lifted Bootstrap condition.

The formal modification condition of Stacks 0GDK is a conjunction of conditions on one morphism, so
it is recorded as a structure whose fields are those conditions. The hypothesis of Stacks 0GDK that
the source and the target be locally Noetherian formal algebraic spaces is carried as two further
fields, `AlgebraicGeometry.FormalSpace.IsLocallyNoetherian` of Tag 0AKY, rather than as hypotheses,
so that the predicate applies to an arbitrary morphism of fppf sheaves and names exactly the
source's class of morphisms. Those two fields are the only ones that use the Tag 0AKY predicate,
which is condition (2) of Tag 0AKX rather than its chart-by-chart condition (1). Rig-étaleness and
rig-surjectivity are the predicates of Tags 0AQM and 0AQQ, which carry their own standing
hypotheses in the same way, and the relative diagonal is the categorical diagonal
`CategoryTheory.Limits.pullback.diagonal` of the sheaf category, which has fibre products, so
`X ×_Y X` need not be built by hand.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 0AM6](https://stacks.math.columbia.edu/tag/0AM6)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AM6.** A morphism of formal algebraic spaces over `S` is *proper* when it is
representable by algebraic spaces and every base change of it along a scheme-valued point of
its target is a morphism of algebraic spaces which is proper, that is, separated, of finite
type and universally closed. The condition makes sense, and is stated, for an arbitrary
morphism of fppf sheaves on the big fppf site of `S`. -/
@[stacks 0AM6]
abbrev IsProper {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom,
    Space.HasPropertyULift.{u + 1} B S hS
      (Space.properPropertyULift.{u + 1} B S hS) f.hom hrep

/-- A proper morphism of formal algebraic spaces over `S` is representable by algebraic
spaces. -/
theorem IsProper.isRepresentable {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsProper B S hS f) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom :=
  h.choose

/-- A proper morphism of formal algebraic spaces over `S` is of finite type: properness of a
morphism of algebraic spaces includes being of finite type, so the same representability
witness serves. -/
theorem IsProper.isFiniteType {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsProper B S hS f) : IsFiniteType B S hS f := by
  obtain ⟨hrep, hprop⟩ := h
  exact ⟨hrep, fun U ξ => (hprop U ξ).2.1⟩

/-- A proper morphism of formal algebraic spaces over `S` satisfies condition (2) of
Stacks 0AJJ: properness of a morphism of algebraic spaces includes being of finite type, so
the same representability witness serves. Stacks 0AJJ identifies that condition with being of
finite type in the sense of Definition 0AM4, part (2), which is the source's remark following
Definition 0AM6; that identification is
`AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`. -/
theorem IsProper.isBootstrapFiniteType {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsProper B S hS f) : IsBootstrapFiniteType B S hS f :=
  h.isFiniteType

/-- **Stacks 0GBT.** A base change of a proper morphism of formal algebraic spaces over `S` is
proper: representability by algebraic spaces is stable under base change, and so is the Bootstrap
condition of Stacks 03XZ, properness of morphisms of algebraic spaces being invariant under
isomorphism. -/
@[stacks 0GBT]
theorem IsProper.of_isPullback {W X Z Y : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsProper B S hS f) : IsProper B S hS p := by
  obtain ⟨hrep, hprop⟩ := hf
  have sq' := isPullback_hom_of_isPullback B S hS sq
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS q.hom p.hom f.hom
      g.hom sq' hrep,
    Space.hasPropertyULift_of_isPullback B S hS sq' hrep hprop⟩

/-! ### Schemes of the site as fppf sheaves -/

/-- A scheme over `S` belonging to the big fppf site of `S`, regarded as an fppf sheaf: its
universe-lifted Yoneda presheaf is a sheaf, the topology being subcanonical. -/
abbrev schemeSheaf (Z : BigFppfOver B S hS) : FppfSheaf B S hS :=
  ⟨(uliftYoneda.{u + 1}).obj Z,
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Z).isSheaf⟩

/-! ### The four base change conditions -/

/-- **Stacks 0ART, condition (2).** Every base change of a morphism of formal algebraic spaces
over `S` along a scheme over `S` in the site mapping to its target is proper. -/
abbrev IsProperOnSchemeBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (Z : BigFppfOver B S hS) (g : schemeSheaf B S hS Z ⟶ Y) (W : FppfSheaf B S hS)
      (p : W ⟶ schemeSheaf B S hS Z) (q : W ⟶ X), IsPullback p q g f → IsProper B S hS p

/-- **Stacks 0ART, condition (3).** Every base change of a morphism of formal algebraic spaces
over `S` along an affine scheme over `S` in the site mapping to its target is proper. -/
abbrev IsProperOnAffineBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
    ∀ (g : schemeSheaf B S hS Z ⟶ Y) (W : FppfSheaf B S hS)
      (p : W ⟶ schemeSheaf B S hS Z) (q : W ⟶ X), IsPullback p q g f → IsProper B S hS p

/-- **Stacks 0ART, condition (4).** Every base change of a morphism of formal algebraic spaces
over `S` along an affine scheme `Z` over `S` in the site mapping to its target is an algebraic
space over `S`, and its projection to `Z` is proper as a morphism of algebraic spaces. -/
abbrev IsAlgebraicAndProperOnAffineBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (Z : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
    ∀ (g : schemeSheaf B S hS Z ⟶ Y) (W : FppfSheaf B S hS)
      (p : W ⟶ schemeSheaf B S hS Z) (q : W ⟶ X), IsPullback p q g f →
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS W.obj ∧
        Space.IsProperULift.{u + 1} B S hS p.hom

/-- **Stacks 0ART, condition (5).** There is a covering of the target of a morphism of formal
algebraic spaces over `S` as in Definition 0AIM — by affine formal algebraic spaces, along
morphisms representable by algebraic spaces and étale, jointly surjective as a map of sheaves
— each of whose base changes of the morphism is proper. -/
abbrev HasProperFormalAtlas {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∃ (I : Type (u + 1)) (Yi : I → FppfSheaf B S hS) (c : ∀ i, Yi i ⟶ Y),
    (∀ i, IsAffineFormalAlgebraicSpace B S hS (Yi i)) ∧
    (∀ i, ∃ hci : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (c i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (c i).hom hci) ∧
    Sheaf.IsLocallySurjective (Sigma.desc c) ∧
    ∀ (i : I) (W : FppfSheaf B S hS) (p : W ⟶ Yi i) (q : W ⟶ X),
      IsPullback p q (c i) f → IsProper B S hS p

/-! ### Reading a base change at the identity point of its target -/

/-- The two halves of **Stacks 0ART, condition (4)** for a proper morphism of fppf sheaves on
the big fppf site of `S` whose target is a scheme in the site: the source is an algebraic space
and the morphism is proper as a morphism of algebraic spaces, by reading properness at the
identity point of the target. -/
private theorem isAlgebraicSpaceULift_and_isProperULift_of_isProper_schemeSheaf
    {W : FppfSheaf B S hS} {Z : BigFppfOver B S hS} {p : W ⟶ schemeSheaf B S hS Z}
    (hp : IsProper B S hS p) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS W.obj ∧
      Space.IsProperULift.{u + 1} B S hS p.hom := by
  obtain ⟨hrep, hprop⟩ := hp
  have hW : Space.IsAlgebraicSpaceULift.{u + 1} B S hS W.obj :=
    Space.isAlgebraicSpaceULift_of_isRepresentable_uliftYoneda.{u + 1} B S hS p.hom
      (Iso.refl _) hrep
  refine ⟨hW, ?_⟩
  have hcomp : (IsPullback.of_id_snd (f := p.hom)).isoPullback.hom ≫
      pullback.fst (𝟙 _) p.hom = p.hom :=
    IsPullback.isoPullback_hom_fst _
  rw [← hcomp]
  exact Space.isProperULift_precomp.{u + 1} B S hS _ _ hW (hrep Z (𝟙 _))
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS Z) (hprop Z (𝟙 _))

/-- The two halves of **Stacks 0ART, condition (4)** for the chosen base change of a morphism
of fppf sheaves on the big fppf site of `S` along a scheme-valued point of its target, read off
from properness of that base change as a morphism of formal algebraic spaces. -/
private theorem isAlgebraicSpaceULift_and_isProperULift_of_isProper
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (U : BigFppfOver B S hS)
    (g : schemeSheaf B S hS U ⟶ Y) (hp : IsProper B S hS (pullback.fst g f)) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback g.hom f.hom) ∧
      Space.IsProperULift.{u + 1} B S hS (pullback.fst g.hom f.hom) := by
  obtain ⟨hsrc, hproper⟩ :=
    isAlgebraicSpaceULift_and_isProperULift_of_isProper_schemeSheaf B S hS hp
  have hsq : IsPullback (pullback.fst g f).hom (pullback.snd g f).hom g.hom f.hom :=
    (IsPullback.of_hasPullback g f).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have htgt : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback g.hom f.hom) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS hsq.isoPullback hsrc
  refine ⟨htgt, ?_⟩
  have hcomp : hsq.isoPullback.symm.hom ≫ (pullback.fst g f).hom = pullback.fst g.hom f.hom := by
    rw [Iso.symm_hom, Iso.inv_comp_eq, hsq.isoPullback_hom_fst]
  rw [← hcomp]
  exact Space.isProperULift_precomp.{u + 1} B S hS _ _ htgt hsrc
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U) hproper

/-! ### The implications -/

/-- **Stacks 0ART, (1) implies (2).** A base change of a proper morphism of formal algebraic
spaces over `S` along a scheme over `S` in the site is proper. This is the base change
stability of properness, which needs no hypothesis on the base. -/
@[stacks 0ART "(1) implies (2)"]
theorem IsProper.isProperOnSchemeBaseChanges {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hf : IsProper B S hS f) : IsProperOnSchemeBaseChanges B S hS f :=
  fun _ _ _ _ _ sq => IsProper.of_isPullback B S hS sq hf

/-- **Stacks 0ART, (2) implies (1).** A morphism of formal algebraic spaces over `S` all of
whose base changes along schemes over `S` in the site are proper is proper: the base change
along a scheme-valued point of the target, read at the identity point of its own target, is
that base change itself. -/
@[stacks 0ART "(2) implies (1)"]
theorem isProper_of_isProperOnSchemeBaseChanges {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsProperOnSchemeBaseChanges B S hS f) : IsProper B S hS f := by
  have key (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ Y.obj) :
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ f.hom) ∧
        Space.IsProperULift.{u + 1} B S hS (pullback.fst ξ f.hom) :=
    isAlgebraicSpaceULift_and_isProperULift_of_isProper B S hS f U (ObjectProperty.homMk ξ)
      (h U (ObjectProperty.homMk ξ) _ _ _ (IsPullback.of_hasPullback _ f))
  exact ⟨fun U ξ => (key U ξ).1, fun U ξ => (key U ξ).2⟩

/-- **Stacks 0ART, (1) is equivalent to (2).** A morphism of formal algebraic spaces over `S`
is proper exactly when each of its base changes along a scheme over `S` in the site is
proper. -/
@[stacks 0ART "(1) is equivalent to (2)"]
theorem isProper_iff_isProperOnSchemeBaseChanges {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    IsProper B S hS f ↔ IsProperOnSchemeBaseChanges B S hS f :=
  ⟨fun hf => hf.isProperOnSchemeBaseChanges B S hS,
    isProper_of_isProperOnSchemeBaseChanges B S hS⟩

/-- **Stacks 0ART, (2) implies (3).** The base change condition over all schemes over `S` in
the site restricts to the affine ones. -/
@[stacks 0ART "(2) implies (3)"]
theorem IsProperOnSchemeBaseChanges.isProperOnAffineBaseChanges {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (h : IsProperOnSchemeBaseChanges B S hS f) :
    IsProperOnAffineBaseChanges B S hS f :=
  fun Z _ g W p q sq => h Z g W p q sq

/-- **Stacks 0ART, (3) implies (4).** If every base change of a morphism of formal algebraic
spaces over `S` along an affine scheme `Z` over `S` in the site is proper, then every such
base change is an algebraic space over `S` and its projection to `Z` is proper as a morphism of
algebraic spaces: both are the content of properness of that base change read at the identity
point of `Z`. -/
@[stacks 0ART "(3) implies (4)"]
theorem IsProperOnAffineBaseChanges.isAlgebraicAndProper {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsProperOnAffineBaseChanges B S hS f) :
    IsAlgebraicAndProperOnAffineBaseChanges B S hS f := by
  intro Z hZ g W p q sq
  exact isAlgebraicSpaceULift_and_isProperULift_of_isProper_schemeSheaf B S hS
    (h Z hZ g W p q sq)

/-- **Stacks 0ART, (1) implies (5).** A proper morphism of formal algebraic spaces over `S`
has a covering of its target as in Definition 0AIM all of whose base changes of the morphism
are proper: any atlas of the target witnessing that it is a formal algebraic space will do,
properness being stable under base change. -/
@[stacks 0ART "(1) implies (5)"]
theorem IsProper.hasProperFormalAtlas {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hY : IsFormalAlgebraicSpace B S hS Y) (hf : IsProper B S hS f) :
    HasProperFormalAtlas B S hS f := by
  obtain ⟨-, I, Yi, c, haff, hetale, hsurj⟩ := hY
  exact ⟨I, Yi, c, haff, hetale, hsurj,
    fun _ _ _ _ sq => IsProper.of_isPullback B S hS sq hf⟩

/-! ### Formal modifications -/

/-- **Stacks 0GDK.** A morphism `f : X ⟶ Y` of locally Noetherian formal algebraic spaces over
`S` is a *formal modification* when (1) `f` is proper, (2) `f` is rig-étale, (3) `f` is
rig-surjective, and (4) the relative diagonal `Δ_f : X ⟶ X ×_Y X` is rig-surjective. The
hypothesis that `X` and `Y` be locally Noetherian formal algebraic spaces is recorded in the
first two fields, so the condition is stated for an arbitrary morphism of fppf sheaves on the
big fppf site of `S`. -/
@[stacks 0GDK]
structure IsFormalModification {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop where
  /-- The source is a locally Noetherian formal algebraic space over `S`: the standing
  hypothesis of Stacks 0GDK on `X`. -/
  isLocallyNoetherian_source : IsLocallyNoetherian B S hS X
  /-- The target is a locally Noetherian formal algebraic space over `S`: the standing
  hypothesis of Stacks 0GDK on `Y`. -/
  isLocallyNoetherian_target : IsLocallyNoetherian B S hS Y
  /-- **Condition (1)** of Stacks 0GDK: `f` is a proper morphism. -/
  isProper : IsProper B S hS f
  /-- **Condition (2)** of Stacks 0GDK: `f` is rig-étale. -/
  isRigEtale : IsRigEtale B S hS f
  /-- **Condition (3)** of Stacks 0GDK: `f` is rig-surjective. -/
  isRigSurjective : IsRigSurjective B S hS f
  /-- **Condition (4)** of Stacks 0GDK: the relative diagonal `Δ_f : X ⟶ X ×_Y X` of `f` is
  rig-surjective. -/
  isRigSurjective_diagonal : IsRigSurjective B S hS (pullback.diagonal f)

end AlgebraicGeometry.FormalSpace

end
