module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical

/-!
# Schemes closed-immersed in an affine formal algebraic space (Stacks 0AIC)

Let `X` be an affine formal algebraic space over a scheme `S`, presented as the colimit of a
directed diagram `D` of affine schemes over `S` whose transition morphisms are thickenings, and
let `T` be a scheme of the site admitting a closed immersion `T ⟶ X`. This file proves that `T`
is then *affine*, and more precisely that `T ⟶ X` factors through a single stage of the
presentation by a closed immersion of schemes `T ⟶ X_i`.

This is the geometric step in the proof of **Stacks 0AIC**: the source deduces the implication
(4) ⇒ (3) from it, and the same step turns the quantifier over affine schemes in condition (2)
into the quantifier over all schemes in condition (3). The latter is proved here, so that
conditions (2) and (3) of Stacks 0AIC are equivalent — the converse (3) ⇒ (2) is
`AlgebraicGeometry.FormalSpace.HasSchemeClosedImmersionCriterion.hasAffineClosedImmersionCriterion`
in `StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan`.

The argument is the source's, with its appeal to [Stacks Project, Tag 06AD] replaced by one to
Stacks 0AIA. Pick any stage `X_i`. The base change `P = X_i ×_X T` is a closed subscheme of
`X_i`, because `T ⟶ X` is a closed immersion, hence affine; and `P ⟶ T` is a thickening, because
`X_i ⟶ X` is one (**Stacks 0AI9**). A thickening is a homeomorphism on points, so `T` is
quasi-compact. Therefore `T ⟶ X` factors through some stage `X_i` (**Stacks 0AIA**), and the
resulting morphism `T ⟶ X_i` splits the thickening `X_i ×_X T ⟶ T`; a split retraction of a
monomorphism is an isomorphism, so `T` *is* that base change, and `T ⟶ X_i` is a closed immersion
of schemes with affine target.

The source instead concludes affineness of `T` from the affineness of the base change by
[Stacks Project, Tag 06AD], a thickening of an affine scheme being affine. That tag is not
available in this development — `StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine`
reduces it to a first-cohomology vanishing which is still open — and the detour above needs only
quasi-compactness of a thickening, which is elementary.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_stage_isClosedImmersion_of_isClosedImmersionInto`: a
  closed immersion of a scheme of the site into a presented affine formal algebraic space
  factors through a stage of the presentation by a closed immersion of schemes.
* `AlgebraicGeometry.FormalSpace.isAffine_of_isClosedImmersionInto`: a scheme of the site
  closed-immersed in an affine formal algebraic space is affine.
* `AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterion`'s
  `hasSchemeClosedImmersionCriterion`: **Stacks 0AIC**, condition (2) implies condition (3).
* `AlgebraicGeometry.FormalSpace.HasAffineClosedImmersionCriterion`'s
  `hasAllSurjectivePresentations`, `hasSomeSurjectivePresentation`: **Stacks 0AIC**, condition
  (2) implies conditions (5) and (4).
* `AlgebraicGeometry.FormalSpace.HasSchemeClosedImmersionCriterion`'s
  `hasSomeSurjectivePresentation`: **Stacks 0AIC**, condition (3) implies condition (4).

## Implementation notes

A closed immersion into a sheaf is the relative morphism property
`AlgebraicGeometry.FormalSpace.IsClosedImmersionInto` of Stacks 0AIC, not the notion of
Stacks 0ANP: the former is what conditions (2) and (3) are phrased with, and it is the one the
argument consumes, since the stage maps of a presentation are representable by *objects of the
site* (**Stacks 0AI9**) and the base changes used here are therefore schemes rather than merely
algebraic spaces.

Both halves of the first step read off the *same* cartesian square, the one supplied by
representability of the stage map `X_i ⟶ X`: the thickening property of that map applies to it as
it stands, and the closed-immersion property of `T ⟶ X` applies to its transpose. That is why the
square is produced once, by the private `exists_pullback_stage`, and the two properties are
extracted from it rather than from two independently chosen pullbacks.

The factorization through a stage is **Stacks 0AIA**,
`AlgebraicGeometry.exists_factor_through_thickening`, which is stated for a quasi-compact
algebraic space over `S`; the sheaf represented by a quasi-compact object of the site is one, by
`AlgebraicGeometry.isAlgebraicSpace_yoneda` and
`AlgebraicGeometry.Space.isQuasiCompactSpace_yoneda_obj`, and its sheafification is the
sheafified representable on the nose.

Descending a morphism of sheafified representables to the site uses that sheafified Yoneda is
fully faithful, which holds because the big fppf topology over `S` is subcanonical
(`AlgebraicGeometry.bigFppfOver_subcanonical` and
`CategoryTheory.Sheaf.fullyFaithfulSheafifiedYoneda`); and recognising a retraction as an
isomorphism uses that the structure functor to schemes is faithful, so that a closed immersion of
the site is a monomorphism there.

**What this makes dischargeable downstream.** The two tags whose only open implication is
Stacks 0AIC need more than this file proves, and it is worth recording exactly how much.

* Stacks 0AKM's implication (1) ⇒ (2),
  `AlgebraicGeometry.FormalSpace.HasNoetherianClosedSubschemes` for a Noetherian `X`, follows
  from `exists_stage_isClosedImmersion_of_isClosedImmersionInto` applied to the presentation with
  Noetherian stages that `isAdicStar_and_hasNoetherianAffinePresentation_of_isNoetherian`
  supplies, since a scheme closed-immersed in a Noetherian scheme is Noetherian; what is still
  missing is only the comparison of the two closed-immersion notions, namely that a closed
  immersion in the sense of Stacks 0ANP is an
  `AlgebraicGeometry.FormalSpace.IsClosedImmersionInto`. Only the *property* half of that
  hypothesis is consumed here — that every cartesian square over `T ⟶ X` with represented
  corners has its opposite leg a closed immersion of schemes — and not the representability
  half, representability of the base changes coming from the stage map instead; so the
  comparison is needed in that weaker form only.
* The passage from condition (4) to condition (1) asks for a *weakly admissible ring* together
  with a presentation of `X` by the spectra of its quotients, the ring being the limit of the
  section rings of the presentation. For a presentation indexed by `ℕ` that limit again lives
  in `Type u` and the construction is carried out in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.SectionLimitPresentation`. For a general index in
  `Type (u + 1)` it needs a smallness argument on the presentation, which this file does not
  supply.

Conditions (2) and (3) ask for an affine scheme *over* `S`, whereas the associated ring of a
presentation carries structure morphisms only on its quotients, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum` explain; so the route from
condition (4) into conditions (2) and (3) is not taken. What is recorded here is the clause
(2) ⇒ (3).

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- The cartesian square exhibiting the base change of a stage map `X_i ⟶ X` along a closed
immersion `T ⟶ X`, together with both properties it carries: the projection to `T` is a
thickening because the stage map is one (**Stacks 0AI9**), and the projection to the stage is a
closed immersion because `T ⟶ X` is one. -/
private theorem exists_pullback_stage (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : FppfSheaf B S hS)
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    {T : BigFppfOver B S hS}
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hg : IsClosedImmersionInto B S hS g) (i : I) :
    ∃ (P : BigFppfOver B S hS) (p : P ⟶ T)
      (c : P ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map p) ∧
        IsClosedImmersion ((BigFppfOver.toScheme B S hS).map c) ∧
        IsPullback ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map c)
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map p)
          (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv) g := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  let _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  have hthick := isThickening_colimitι B S hS D hD X e.symm i
  have hrep := hthick.rep
  have hpb := hrep.isPullback' g
  refine ⟨hrep.pullback g, hrep.snd g, hrep.fst' g, ?_, ?_, hpb⟩
  · exact hthick.property g _ _ hpb
  · exact hg.property _ _ _ hpb.flip

/-- If a morphism of the site is a closed immersion of schemes into an affine scheme, its source
is affine. -/
private theorem isAffine_of_isClosedImmersion_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {T T' : BigFppfOver B S hS} (h : T ⟶ T')
    (hh : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map h))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine ((BigFppfOver.toScheme B S hS).map h)).1

/-- A closed immersion of a scheme of the site into an affine formal algebraic space factors
through a single stage of any presentation of it by affine thickenings, by a closed immersion of
schemes. This is the geometric content of the implication (4) ⇒ (3) of **Stacks 0AIC**. -/
theorem exists_stage_isClosedImmersion_of_isClosedImmersionInto (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {I : Type (u + 1)} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    {X : FppfSheaf B S hS}
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    {T : BigFppfOver B S hS}
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hg : IsClosedImmersionInto B S hS g) :
    ∃ (i : I) (h : T ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i)),
      IsClosedImmersion ((BigFppfOver.toScheme B S hS).map h) ∧
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map h ≫
          (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
            Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.inv) = g := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let q := BigFppfOver.toScheme B S hS
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  -- Any stage exhibits `T` as a thickening of an affine scheme, hence makes `T` quasi-compact.
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨P₀, p₀, c₀, hth₀, hci₀, -⟩ := exists_pullback_stage B S hS D hD X e g hg i₀
  have : IsAffine (q.obj P₀) :=
    isAffine_of_isClosedImmersion_map B S hS c₀ hci₀ (D.obj i₀).property
  have hTc : CompactSpace (q.obj T) :=
    Stacks.Thickenings.IsThickening.compactSpace hth₀
  -- So it factors through a stage, by Stacks 0AIA.
  have hfac : ∃ (i : I)
      (g' : F.obj T ⟶ F.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))),
      g' ≫ (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i ≫ e.inv) = g := by
    obtain ⟨i, g₁, hg₁⟩ := exists_factor_through_thickening B S hS I D hD X e
      (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
      (Space.isQuasiCompactSpace_yoneda_obj B S hS hTc) g
    exact ⟨i, g₁, hg₁⟩
  obtain ⟨i, g', hg'⟩ := hfac
  -- The factorization splits the thickening at that stage, so it is an isomorphism.
  obtain ⟨P, p, c, hth, hci, hpb⟩ := exists_pullback_stage B S hS D hD X e g hg i
  have hw : g' ≫ (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i ≫ e.inv) =
      𝟙 (F.obj T) ≫ g := by
    rw [Category.id_comp]
    exact hg'
  let s : T ⟶ P := F.preimage (hpb.lift g' (𝟙 (F.obj T)) hw)
  have hmaps : F.map s = hpb.lift g' (𝟙 (F.obj T)) hw := F.map_preimage _
  have hsp : s ≫ p = 𝟙 T := by
    refine F.map_injective ?_
    rw [F.map_comp, hmaps, F.map_id]
    exact hpb.lift_snd _ _ _
  have hsc : F.map (s ≫ c) = g' := by
    rw [F.map_comp, hmaps]
    exact hpb.lift_fst _ _ _
  have : IsClosedImmersion (q.map p) := hth.1
  have : Mono p := q.mono_of_mono_map (f := p) inferInstance
  have hps : p ≫ s = 𝟙 P := by
    rw [← cancel_mono p, Category.assoc, hsp, Category.comp_id, Category.id_comp]
  have : IsIso s := ⟨⟨p, hsp, hps⟩⟩
  have : IsIso (q.map s) := inferInstance
  have : IsClosedImmersion (q.map c) := hci
  have hcih : IsClosedImmersion (q.map (s ≫ c)) := by
    rw [q.map_comp]
    infer_instance
  refine ⟨i, s ≫ c, hcih, ?_⟩
  rw [hsc]
  exact hg'

/-- **A scheme of the site closed-immersed in an affine formal algebraic space is affine.** It
is a closed subscheme of a stage of any presentation of the space by affine thickenings. -/
theorem isAffine_of_isClosedImmersionInto (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X : FppfSheaf B S hS} (hX : IsAffineFormalAlgebraicSpace B S hS X)
    {T : BigFppfOver B S hS}
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj T ⟶ X)
    (hg : IsClosedImmersionInto B S hS g) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj T) := by
  obtain ⟨-, I, pre, hne, hdir, D, hD, ⟨e⟩⟩ := id hX
  let _ : Preorder I := pre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  obtain ⟨i, h, hci, -⟩ :=
    exists_stage_isClosedImmersion_of_isClosedImmersionInto B S hS D hD e g hg
  exact isAffine_of_isClosedImmersion_map B S hS h hci (D.obj i).property

/-- **Stacks 0AIC, condition (2) implies condition (3).** If some morphism from `X` to an affine
scheme over `S` turns every closed immersion of an *affine* scheme into `X` into a closed
immersion of schemes, then it does so for every *scheme* of the site: a scheme closed-immersed in
an affine formal algebraic space is already affine. -/
@[stacks 0AIC "part (2) implies part (3)"]
theorem HasAffineClosedImmersionCriterion.hasSchemeClosedImmersionCriterion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : FppfSheaf B S hS}
    (hX : HasAffineClosedImmersionCriterion B S hS X) :
    HasSchemeClosedImmersionCriterion B S hS X := by
  obtain ⟨hA, A, f, hf⟩ := hX
  refine ⟨hA, A, f, fun T g hg ↦ ?_⟩
  exact hf ⟨T, isAffine_of_isClosedImmersionInto B S hS hA g hg⟩ g hg

/-- A closed immersion of fppf sheaves between sheaves represented by objects of the site is a
closed immersion of the underlying schemes: the identity square exhibits the morphism as one of
its own represented base changes. -/
theorem isClosedImmersion_of_isClosedImmersionInto_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {T T' : BigFppfOver B S hS} (h : T ⟶ T')
    (hh : IsClosedImmersionInto B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map h)) :
    IsClosedImmersion ((BigFppfOver.toScheme B S hS).map h) :=
  MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) hh

/-- The engine of the implications (2) ⇒ (5) and (2) ⇒ (4) of **Stacks 0AIC**. If some morphism
`f : X ⟶ Spec A` to an affine scheme over `S` turns every closed immersion of an affine scheme
into `X` into a closed immersion of schemes, then *any* presentation of `X` by affine thickenings
has surjective section-ring projections.

The argument is the source's. Each stage map `X_i ⟶ X` is a thickening (**Stacks 0AI9**), hence a
closed immersion into `X`, so the criterion makes the composite `X_i ⟶ Spec A` a closed immersion
of affine schemes and `Γ(A) ⟶ Γ(X_i)` surjective. These surjections are compatible along the
diagram, because the factorizations `X_i ⟶ Spec A` are, so the image in the inverse system of a
preimage in `Γ(A)` is a compatible family projecting onto the given section. -/
theorem HasAffineClosedImmersionCriterion.hasSurjectiveSectionProjections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : FppfSheaf B S hS}
    (hX : HasAffineClosedImmersionCriterion B S hS X)
    {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (g : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map g)))
    (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :
    HasSurjectiveSectionProjections B S hS D := by
  classical
  obtain ⟨-, A, f, hf⟩ := hX
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let F' := BigAffineFppf.inclusion B S hS ⋙ F
  have _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have _ : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have _ : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  have _ : F'.Full := inferInstanceAs (Functor.Full (_ ⋙ _))
  have _ : F'.Faithful := inferInstanceAs (Functor.Faithful (_ ⋙ _))
  -- Each stage maps to `X` by a closed immersion, the stage map being a thickening.
  have hstage : ∀ i : I, IsClosedImmersionInto B S hS (colimit.ι (D ⋙ F') i ≫ e.inv) := by
    intro i
    refine ⟨(isThickening_colimitι B S hS D hD X e.symm i).rep, ?_⟩
    intro a b g fst snd hpb
    exact ((isThickening_colimitι B S hS D hD X e.symm i).property g fst snd hpb).1
  -- So each stage factors through `A` by a closed immersion of affine schemes.
  let c : ∀ i : I, D.obj i ⟶ A := fun i => F'.preimage (colimit.ι (D ⋙ F') i ≫ e.inv ≫ f)
  have hc : ∀ i : I, F'.map (c i) = colimit.ι (D ⋙ F') i ≫ e.inv ≫ f :=
    fun i => F'.map_preimage _
  have hci : ∀ i : I, IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (c i)) := by
    intro i
    refine isClosedImmersion_of_isClosedImmersionInto_map B S hS
      ((BigAffineFppf.inclusion B S hS).map (c i)) ?_
    have hmap : F.map ((BigAffineFppf.inclusion B S hS).map (c i)) =
        (colimit.ι (D ⋙ F') i ≫ e.inv) ≫ f := by
      rw [Category.assoc]; exact hc i
    rw [hmap]
    exact hf (D.obj i) _ (hstage i)
  -- The factorizations are compatible along the diagram.
  have hw : ∀ ⦃i j : I⦄ (φ : i ⟶ j), c i = D.map φ ≫ c j := by
    intro i j φ
    apply F'.map_injective
    rw [F'.map_comp, hc i, hc j]
    have hwι := colimit.w (D ⋙ F') φ
    simp only [Functor.comp_map] at hwι
    rw [← hwι, Category.assoc]
  -- A preimage in `Γ(A)` of a given section spreads out to a compatible family.
  intro i₀ a
  have hAaff : IsAffine ((BigAffineFppf.toScheme B S hS).obj A) := A.property
  have _ : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (c i₀)) := hci i₀
  obtain ⟨b, hb⟩ :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigAffineFppf.toScheme B S hS).map (c i₀))).2 a
  refine ⟨⟨fun jo => ((BigAffineFppf.toScheme B S hS).map (c jo.unop)).appTop b, ?_⟩, hb⟩
  intro jo ko ψ
  change Scheme.Γ.map ((BigAffineFppf.toScheme B S hS).map (D.map ψ.unop)).op
      (((BigAffineFppf.toScheme B S hS).map (c jo.unop)).appTop b) =
    ((BigAffineFppf.toScheme B S hS).map (c ko.unop)).appTop b
  rw [Scheme.Γ_map_op, hw ψ.unop, Functor.map_comp, Scheme.Hom.comp_appTop]
  rfl

/-- **Stacks 0AIC, condition (2) implies condition (5).** Condition (2) is read on every
presentation of `X` by affine thickenings at once, which is condition (5). -/
@[stacks 0AIC "part (2) implies part (5), and with it part (2) implies part (4). No hypothesis \
beyond condition (2) is carried. What remains open in this tag is the implication (4) implies \
(1) for a presentation indexed by an arbitrary directed type in Type (u + 1): the ring it asks \
for is the limit of the section rings of the presentation, which then lies in Type (u + 1) \
rather than Type u, so a smallness argument on the index is needed that this development does \
not have. The sequential case is exists_quotientSystem_formalSpectrum_iso and the countably \
indexed case is isPresentingRing_of_isCountablyIndexed. The implication (1) implies (2) is open \
for the reason recorded in the implementation notes above: conditions (2) and (3) ask for an \
affine scheme over S, and the ring of a presentation carries structure morphisms only on its \
quotients"]
theorem HasAffineClosedImmersionCriterion.hasAllSurjectivePresentations
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : FppfSheaf B S hS}
    (hX : HasAffineClosedImmersionCriterion B S hS X) :
    HasAllSurjectivePresentations B S hS X := by
  refine ⟨hX.1, ?_⟩
  intro I pre hne hdir D hD he
  let _ : Preorder I := pre
  obtain ⟨e⟩ := he
  exact hX.hasSurjectiveSectionProjections B S hS D hD e

/-- **Stacks 0AIC, condition (2) implies condition (4).** The presentation by affine thickenings
that affineness of `X` supplies has surjective section-ring projections. -/
@[stacks 0AIC "part (2) implies part (4)"]
theorem HasAffineClosedImmersionCriterion.hasSomeSurjectivePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : FppfSheaf B S hS}
    (hX : HasAffineClosedImmersionCriterion B S hS X) :
    HasSomeSurjectivePresentation B S hS X :=
  (hX.hasAllSurjectivePresentations B S hS).hasSomeSurjectivePresentation B S hS

/-- **Stacks 0AIC, condition (3) implies condition (4).** The criterion for all schemes
of the site restricts to the affine ones, which is already enough. -/
@[stacks 0AIC "part (3) implies part (4)"]
theorem HasSchemeClosedImmersionCriterion.hasSomeSurjectivePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : FppfSheaf B S hS}
    (hX : HasSchemeClosedImmersionCriterion B S hS X) :
    HasSomeSurjectivePresentation B S hS X :=
  (hX.hasAffineClosedImmersionCriterion B S hS).hasSomeSurjectivePresentation B S hS

end AlgebraicGeometry.FormalSpace

end
