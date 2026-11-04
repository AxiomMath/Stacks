module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidPullbackDiagram
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksCore.Tactic.StacksAttribute

/-!
# Open loci on the source of a groupoid presentation

Let `G` be a groupoid scheme over `S` and let `g : U' ⟶ U` be a morphism to its object scheme.
If a property `P` of morphisms of schemes has maximal open `P`-loci for `Q`-morphisms, and if
those loci commute with base change along `R`-morphisms, then the maximal `P`-locus of the map
`U' ×_{g, U, t} R ⟶ U` is pulled back from an open of `U'`.  The reason is that the two
pullbacks of the locus to `(U' ×_U R) ×_{U'} (U' ×_U R)` agree — one square is a base change
along the target map, the other along the source map, and both carry the locus to the same open
because the comparison of the two descriptions of a pair of arrows with a common target is an
isomorphism — and the locus therefore descends along the first projection, which admits the
section coming from the identity of the groupoid.

## Main results

* `AlgebraicGeometry.exists_open_with_preimage_maximal_locus` constructs the open of `U'` whose
  inverse image is the maximal locus on the pullback.

## Implementation notes

An open `V` of the source of `f` is a locus on which `f` has `P` when the composite `V.ι ≫ f`
has `P`.  Maximality is expressed by `IsGreatest`.  Consequently the equality of open
subschemes in the source is expressed as the assertion that the inverse-image open is the
greatest such locus.  The base-change hypothesis is stated for arbitrary pullback squares, so it
does not depend on the chosen implementation of a fibre product.

## References

* [Stacks Project, Tag 04LH](https://stacks.math.columbia.edu/tag/04LH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- An open of the source of a morphism admitting a section is the inverse image of an open of
the target as soon as its two pullbacks to the fibre square of the morphism agree. -/
private theorem open_eq_pullback_of_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (V : X.Opens)
    (hV : (pullback.fst f f) ⁻¹ᵁ V = (pullback.snd f f) ⁻¹ᵁ V) :
    V = f ⁻¹ᵁ (s ⁻¹ᵁ V) := by
  let j : X ⟶ pullback f f :=
    pullback.lift (𝟙 X) (f ≫ s) (by simp [Category.assoc, hs])
  have h := congrArg (fun W : (pullback f f).Opens => j ⁻¹ᵁ W) hV
  change (j ≫ pullback.fst f f) ⁻¹ᵁ V =
    (j ≫ pullback.snd f f) ⁻¹ᵁ V at h
  simpa only [j, pullback.lift_fst, pullback.lift_snd,
    Scheme.Hom.id_preimage, Scheme.Hom.comp_preimage] using h

/-- The two projections of the fibre square of `pullback.fst g t` have the same composite with
the second projection of `pullback g t`, up to the common value of `t`. -/
private theorem pairComparison_condition {A B C : Scheme.{u}} (g : A ⟶ C) (t : B ⟶ C) :
    (pullback.fst (pullback.fst g t) (pullback.fst g t) ≫ pullback.snd g t) ≫ t =
      (pullback.snd (pullback.fst g t) (pullback.fst g t) ≫ pullback.snd g t) ≫ t := by
  rw [Category.assoc, Category.assoc, ← pullback.condition, pullback.condition_assoc]

/-- The comparison map from the fibre square of `pullback.fst g t` to the fibre square of `t`:
it sends a pair of points of `A ×_C B` with the same `A`-component to the pair of their
`B`-components, which have the same image under `t`. -/
private noncomputable def pairComparison {A B C : Scheme.{u}} (g : A ⟶ C) (t : B ⟶ C) :
    pullback (pullback.fst g t) (pullback.fst g t) ⟶ pullback t t :=
  pullback.lift
    (pullback.fst (pullback.fst g t) (pullback.fst g t) ≫ pullback.snd g t)
    (pullback.snd (pullback.fst g t) (pullback.fst g t) ≫ pullback.snd g t)
    (pairComparison_condition g t)

/-- The first component of `pairComparison`. -/
private theorem pairComparison_fst {A B C : Scheme.{u}} (g : A ⟶ C) (t : B ⟶ C) :
    pairComparison g t ≫ pullback.fst t t =
      pullback.fst (pullback.fst g t) (pullback.fst g t) ≫ pullback.snd g t :=
  pullback.lift_fst _ _ _

/-- The second component of `pairComparison`. -/
private theorem pairComparison_snd {A B C : Scheme.{u}} (g : A ⟶ C) (t : B ⟶ C) :
    pairComparison g t ≫ pullback.snd t t =
      pullback.snd (pullback.fst g t) (pullback.fst g t) ≫ pullback.snd g t :=
  pullback.lift_snd _ _ _

/-- The square formed by `pairComparison`, the first projection of the fibre square of
`pullback.fst g t`, the first projection of the fibre square of `t`, and `pullback.snd g t` is
cartesian. -/
private theorem pairComparison_isPullback_fst {A B C : Scheme.{u}} (g : A ⟶ C) (t : B ⟶ C) :
    IsPullback (pairComparison g t)
      (pullback.fst (pullback.fst g t) (pullback.fst g t))
      (pullback.fst t t) (pullback.snd g t) := by
  refine IsPullback.of_right ?_ (pairComparison_fst g t) (IsPullback.of_hasPullback t t).flip
  rw [pairComparison_snd]
  simpa only [pullback.condition] using
    (IsPullback.of_hasPullback (pullback.fst g t) (pullback.fst g t)).flip.paste_horiz
      (IsPullback.of_hasPullback g t).flip

/-- The companion of `pairComparison_isPullback_fst` for the second projections. -/
private theorem pairComparison_isPullback_snd {A B C : Scheme.{u}} (g : A ⟶ C) (t : B ⟶ C) :
    IsPullback (pairComparison g t)
      (pullback.snd (pullback.fst g t) (pullback.fst g t))
      (pullback.snd t t) (pullback.snd g t) := by
  refine IsPullback.of_right ?_ (pairComparison_snd g t) (IsPullback.of_hasPullback t t)
  rw [pairComparison_fst]
  simpa only [pullback.condition] using
    (IsPullback.of_hasPullback (pullback.fst g t) (pullback.fst g t)).paste_horiz
      (IsPullback.of_hasPullback g t).flip

/-- Precomposing a cartesian square with an isomorphism keeps it cartesian. -/
private theorem isPullback_precomp_iso {A B X Y Z : Scheme.{u}}
    (i : A ⟶ B) [IsIso i] {f : B ⟶ X} {g : B ⟶ Y}
    {h : X ⟶ Z} {k : Y ⟶ Z} (sq : IsPullback f g h k) :
    IsPullback (i ≫ f) (i ≫ g) h k :=
  sq.of_iso (asIso i).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- **Stacks Project, Tag 04LH.** Suppose `P`, `Q`, and `R` are properties of morphisms of
schemes, `R` implies `Q`, `Q` is stable under composition and base change, and maximal open
`P`-loci exist for `Q`-morphisms and commute with base change by `R`-morphisms.  For a groupoid
scheme whose source and target have `R`, the maximal `P`-locus of the indicated map from the
pullback of its arrow scheme is the inverse image of an open of `U'`. -/
@[stacks 04LH]
public theorem exists_open_with_preimage_maximal_locus
    (P Q R : MorphismProperty Scheme.{u})
    (hRQ : R ≤ Q) [Q.IsStableUnderComposition] [Q.IsStableUnderBaseChange]
    (hmax : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Q f →
      ∃ V : X.Opens, IsGreatest {W : X.Opens | P (W.ι ≫ f)} V)
    (hbase : ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {p : X' ⟶ X} {q : Y' ⟶ Y}, Q f → R q → IsPullback p f' f q →
      ∀ {V : X.Opens}, IsGreatest {W : X.Opens | P (W.ι ≫ f)} V →
        IsGreatest {W' : X'.Opens | P (W'.ι ≫ f')} (p ⁻¹ᵁ V))
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Scheme.{u}}
    (g : U' ⟶ G.objects.left) (hs : R G.source.left) (ht : R G.target.left) (hg : Q g) :
    ∃ W : U'.Opens,
      IsGreatest
        {V : (pullback g G.target.left).Opens |
          P (V.ι ≫ pullback.snd g G.target.left ≫ G.source.left)}
        ((pullback.fst g G.target.left) ⁻¹ᵁ W) := by
  let X := pullback g G.target.left
  let p : X ⟶ U' := pullback.fst g G.target.left
  let r : X ⟶ G.arrows.left := pullback.snd g G.target.left
  let h : X ⟶ G.objects.left := r ≫ G.source.left
  have hr : Q r :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g G.target.left) hg
  have hh : Q h := Q.comp_mem r G.source.left hr (hRQ _ hs)
  obtain ⟨V, hV⟩ := hmax h hh
  have he : G.identity.left ≫ G.target.left = 𝟙 G.objects.left := by
    simpa only [Over.comp_left, Over.id_left] using congrArg Over.Hom.left G.target_identity
  let σ : U' ⟶ X := pullback.lift (𝟙 U') (g ≫ G.identity.left) (by
    simp only [Category.assoc, he, Category.comp_id, Category.id_comp])
  have hσ : σ ≫ p = 𝟙 U' := by
    simp only [σ, p, pullback.lift_fst]
  let eT := PreservesPullback.iso (Over.forget S) G.target G.target
  let eST := PreservesPullback.iso (Over.forget S) G.source G.target
  let aG : pullback G.target.left G.target.left ⟶
      pullback G.source.left G.target.left :=
    eT.inv ≫ (GroupoidScheme.targetPullbackToComposable G).left ≫ eST.hom
  let kG : pullback G.target.left G.target.left ⟶ G.arrows.left :=
    eT.inv ≫ (GroupoidScheme.inverseCompSnd G).left
  have hcompIso : IsIso (GroupoidScheme.targetPullbackToComposable G) :=
    GroupoidScheme.targetPullbackToComposable_isIso G
  have hcompLeftIso : IsIso (GroupoidScheme.targetPullbackToComposable G).left := by
    change IsIso ((Over.forget S).map (GroupoidScheme.targetPullbackToComposable G))
    infer_instance
  have haGIso : IsIso aG := by
    dsimp [aG]
    infer_instance
  have hleft : ∀ {A B C : Over S} {f : A ⟶ B} {g : B ⟶ C} {k : A ⟶ C},
      f ≫ g = k → f.left ≫ g.left = k.left := fun h => by
    simpa only [Over.comp_left] using congrArg Over.Hom.left h
  have hcompSnd := hleft (f := GroupoidScheme.targetPullbackToComposable G)
    (g := pullback.snd G.source G.target) (k := GroupoidScheme.inverseCompSnd G)
    (by
      simp only [GroupoidScheme.targetPullbackToComposable, pullback.lift_snd])
  have haGSnd : aG ≫ pullback.snd G.source.left G.target.left = kG := by
    dsimp [aG, kG]
    have heST : eST.hom ≫ pullback.snd G.source.left G.target.left =
        (pullback.snd G.source G.target).left :=
      PreservesPullback.iso_hom_snd (Over.forget S) G.source G.target
    simp only [Category.assoc, heST, ← hcompSnd]
  have hcompFst := hleft (GroupoidScheme.targetPullbackToComposable_fst G)
  have haGFst : aG ≫ pullback.fst G.source.left G.target.left =
      pullback.fst G.target.left G.target.left := by
    have heST : eST.hom ≫ pullback.fst G.source.left G.target.left =
        (pullback.fst G.source G.target).left :=
      PreservesPullback.iso_hom_fst (Over.forget S) G.source G.target
    have heT : eT.inv ≫ (pullback.fst G.target G.target).left =
        pullback.fst G.target.left G.target.left :=
      PreservesPullback.iso_inv_fst (Over.forget S) G.target G.target
    simp only [aG, Category.assoc, heST, hcompFst, heT]
  let compS : pullback G.source.left G.target.left ⟶ G.arrows.left :=
    eST.inv ≫ G.comp.left
  have hcompComp := hleft (GroupoidScheme.targetPullbackToComposable_comp G)
  have haGComp : aG ≫ compS = pullback.snd G.target.left G.target.left := by
    have heT : eT.inv ≫ (pullback.snd G.target G.target).left =
        pullback.snd G.target.left G.target.left :=
      PreservesPullback.iso_inv_snd (Over.forget S) G.target G.target
    simp only [aG, compS, Category.assoc, Iso.hom_inv_id_assoc, hcompComp, heT]
  have sqTargetA : IsPullback kG (pullback.fst G.target.left G.target.left)
      G.target.left G.source.left := by
    have sq := isPullback_precomp_iso aG
      (IsPullback.of_hasPullback G.source.left G.target.left).flip
    simpa only [haGSnd, haGFst] using sq
  have sqCompRaw : IsPullback G.comp.left
      (pullback.snd G.source G.target).left G.source.left G.source.left :=
    Functor.map_isPullback (Over.forget S) (GroupoidScheme.comp_source_isPullback G)
  have sqCompS : IsPullback compS
      (pullback.snd G.source.left G.target.left) G.source.left G.source.left := by
    have sq := isPullback_precomp_iso eST.inv sqCompRaw
    have heST : eST.inv ≫ (pullback.snd G.source G.target).left =
        pullback.snd G.source.left G.target.left :=
      PreservesPullback.iso_inv_snd (Over.forget S) G.source G.target
    simpa only [compS, heST] using sq
  have sqSourceA : IsPullback kG (pullback.snd G.target.left G.target.left)
      G.source.left G.source.left := by
    have sq := (isPullback_precomp_iso aG sqCompS).flip
    simpa only [haGSnd, haGComp] using sq
  let z₁ := pullback.fst p p
  let z₂ := pullback.snd p p
  let pairMap : pullback p p ⟶ pullback G.target.left G.target.left :=
    pairComparison g G.target.left
  have sqPairLeft : IsPullback pairMap z₁
      (pullback.fst G.target.left G.target.left) r :=
    pairComparison_isPullback_fst g G.target.left
  have sqPairRight : IsPullback pairMap z₂
      (pullback.snd G.target.left G.target.left) r :=
    pairComparison_isPullback_snd g G.target.left
  have sq₁ : IsPullback z₁ (pairMap ≫ kG) h G.target.left :=
    (sqPairLeft.paste_horiz sqTargetA).flip
  have sq₂ : IsPullback z₂ (pairMap ≫ kG) h G.source.left :=
    (sqPairRight.paste_horiz sqSourceA).flip
  have h₁ := hbase hh ht sq₁ hV
  have h₂ := hbase hh hs sq₂ hV
  have heq : z₁ ⁻¹ᵁ V = z₂ ⁻¹ᵁ V := h₁.unique h₂
  have hdesc : V = p ⁻¹ᵁ (σ ⁻¹ᵁ V) :=
    open_eq_pullback_of_section p σ hσ V heq
  refine ⟨σ ⁻¹ᵁ V, ?_⟩
  rw [← hdesc]
  simpa only [h, r] using hV

end AlgebraicGeometry
