module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelLocal
public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.NodalAwayFromAttaching
public import StacksFrontier.AlgebraicGeometry.Morphisms.UnitPushforwardFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.HigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange

/-!
# Stable contractions on arbitrary presentations of a base change

The conditions of [Stacks, Tag 0E7Q] on a morphism `c : X ⟶ Y` over a field are invariant under
isomorphisms of `X` and `Y` over the field, and they are preserved by extension of the ground
field (`Stacks.Curves.StableModel.IsStableContraction.baseChange`). Together: for an extension
`K/k` and any cartesian presentations `X'`, `Y'` of the base changes of `X` and `Y`, the induced
morphism `c' : X' ⟶ Y'` satisfies the conditions over `K`. This is the form in which the fibres of
a deformed contraction are read at every field-valued point (the output of [Stacks, Tag 0E7C] as
consumed by [Stacks, Tag 0E8A]).

## Main results

* `AlgebraicGeometry.C1590Private.isStableContraction_of_iso`: invariance under isomorphisms.
* `AlgebraicGeometry.C1590Private.isStableContraction_of_isPullback_baseChange`: base change to
  arbitrary cartesian presentations.

## References

* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Curves.StableModel

namespace AlgebraicGeometry.C1590Private

universe u

/-- The global functions of the target of a stable contraction are those of the source. -/
theorem isIso_globalSections_target_of_isStableContraction {k : Type u} [Field k]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
    (h : IsStableContraction f gY c) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop) := by
  have hc : IsIso c.appTop :=
    Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c
      h.isIso_unitToPushforwardObjUnit ⊤
  have : IsIso (((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop) ≫ c.appTop) := by
    rw [Category.assoc, ← Scheme.Hom.comp_appTop, h.comp_eq]; infer_instance
  exact IsIso.of_isIso_comp_right _ c.appTop

/-- **The conditions of [Stacks, Tag 0E7Q] are invariant under isomorphisms over the field.** -/
theorem isStableContraction_of_iso {k : Type u} [Field k] {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y} {f' : X' ⟶ Spec (.of k)}
    {gY' : Y' ⟶ Spec (.of k)} {c' : X' ⟶ Y'} (αX : X' ⟶ X) [IsIso αX] (αY : Y' ⟶ Y) [IsIso αY]
    (hf : αX ≫ f = f') (hg : αY ≫ gY = gY') (hc : c' ≫ αY = αX ≫ c) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (h : IsStableContraction f gY c) :
    IsStableContraction f' gY' c' := by
  have : IsProper gY := h.isProper
  have : IsProper c := by
    have : IsProper (c ≫ gY) := by rw [h.comp_eq]; infer_instance
    exact IsProper.of_comp c gY
  have : IsProper gY' := by rw [← hg]; infer_instance
  have := isIso_globalSections_target_of_isStableContraction h
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY'.appTop) := by
    have : IsIso αY.appTop := inferInstanceAs (IsIso (αY.app ⊤))
    rw [← hg, Scheme.Hom.comp_appTop, ← Category.assoc]
    infer_instance
  have H : IsPullback αX c' c αY := IsPullback.of_horiz_isIso ⟨hc.symm⟩
  have hdim' : topologicalKrullDim Y' = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso αY)).isHomeomorph).trans
      h.topologicalKrullDim_eq
  have hnodal : letI : Y'.Over (Spec (.of k)) := ⟨gY'⟩
      Stacks.Curves.HasAtWorstNodalSingularities k Y' := by
    let : Y'.Over (Spec (.of k)) := ⟨gY'⟩
    intro y hy
    have hcl : IsClosed ({αY y} : Set Y) := by
      have := (Scheme.homeoOfIso (asIso αY)).isClosedMap _ hy
      rwa [Set.image_singleton] at this
    have := Stacks.Curves.smoothAt_or_isNode_of_etale_of_comm k gY gY' h.topologicalKrullDim_eq
      hdim' αY (𝟙 Y') (by rw [Category.id_comp, hg]) y
      (let : Y.Over (Spec (.of k)) := ⟨gY⟩; h.hasAtWorstNodalSingularities _ hcl)
    exact this
  exact
    { comp_eq := by rw [← hg, reassoc_of% hc, h.comp_eq, hf]
      isProper := inferInstance
      topologicalKrullDim_eq := hdim'
      hasAtWorstNodalSingularities := hnodal
      isIso_unitToPushforwardObjUnit :=
        c.isIso_unitToPushforwardObjUnit_of_isPullback H h.isIso_unitToPushforwardObjUnit
      isZero_rightDerived_one := by
        open Stacks.AlgebraicGeometry.FlatBaseChangeDerived in
        exact isZero_rightDerived_pushforward_unit_of_isPullback H 1 h.isZero_rightDerived_one
      isAmple := isAmple_dualizingSheafOverField_of_iso gY' gY hdim' hnodal (asIso αY) hg
        h.isAmple }

/-- **Stable contractions on arbitrary presentations of a base change.** Let `c : X ⟶ Y` satisfy
the conditions of [Stacks, Tag 0E7Q] over `k`, with `X` proper and `H⁰(X, 𝒪_X) = k`, and let
`K/k` be a field extension. For cartesian presentations `X' ⟶ X`, `Y' ⟶ Y` of the base changes
along `Spec K ⟶ Spec k` and `c' : X' ⟶ Y'` over `K` compatible with `c`, `c'` satisfies the
conditions over `K`. -/
theorem isStableContraction_of_isPullback_baseChange {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)}
    {c : X ⟶ Y} {f' : X' ⟶ Spec (.of K)} {gY' : Y' ⟶ Spec (.of K)} {c' : X' ⟶ Y'}
    (pX : X' ⟶ X) (pY : Y' ⟶ Y)
    (hX : IsPullback pX f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hY : IsPullback pY gY' gY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hc' : c' ≫ gY' = f') (hcp : c' ≫ pY = pX ≫ c) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (h : IsStableContraction f gY c) :
    IsStableContraction f' gY' c' := by
  let gK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hb := h.baseChange K
  have sqX : IsPullback (pullback.fst f gK) (pullback.snd f gK) f gK :=
    IsPullback.of_hasPullback f gK
  have : IsProper (pullback.snd f gK) := MorphismProperty.of_isPullback sqX inferInstance
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (pullback.snd f gK).appTop) :=
    isIso_globalSections_baseChange k K _ _ f sqX
  have hcY : c ≫ gY = f := h.comp_eq
  refine isStableContraction_of_iso hX.isoPullback.hom hY.isoPullback.hom
    (IsPullback.isoPullback_hom_snd _) (IsPullback.isoPullback_hom_snd _) ?_ hb
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, Category.assoc, pullback.lift_fst,
      IsPullback.isoPullback_hom_fst_assoc, hcp]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc, pullback.lift_snd,
      Category.comp_id, IsPullback.isoPullback_hom_snd, hc']

end AlgebraicGeometry.C1590Private

end
