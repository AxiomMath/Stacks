module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModelCharacterization
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.TerminalBaseChange
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.HigherDirectImageVanishing

/-!
# The stable model commutes with extension of the ground field

Let `X` be a proper scheme over a field `k` with `H⁰(X, 𝒪_X) = k`, and let `c : X ⟶ Y` be a
morphism over `k` satisfying the three conditions of [Stacks, Tag 0E7Q]:

1. `Y` is proper over `k`, of dimension one, with at-worst-nodal singularities;
2. `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`;
3. `ω_Y` is ample.

For a field extension `K/k` the base change `c_K : X_K ⟶ Y_K` satisfies the same three
conditions over `K`. Properness, dimension and nodality pass to `Y_K` (the last one because `Y`
is equidimensional, `H⁰(Y, 𝒪_Y) = H⁰(X, 𝒪_X) = k`); both halves of (2) survive the flat base
change `Spec K ⟶ Spec k` ([Stacks, Tag 02KH]); and `ω_{Y_K}` is the pullback of `ω_Y`
([Stacks, Tag 0E32]), the pullback of an ample invertible module along the affine morphism
`Y_K ⟶ Y` being ample.

When moreover `X` has dimension one, genus at least two and at-worst-nodal singularities, so that
`c` is the stable model of `X` — the contraction of rational tails and bridges of
[Stacks, Section 0E7N] — the uniqueness in [Stacks, Tag 0E7Q] then shows that `c_K` is the stable
model of `X_K`: every morphism `d : X_K ⟶ Z` satisfying the three conditions over `K` is `c_K`
followed by a unique isomorphism `Y_K ≅ Z`. This is the compatibility with ground field
extensions in the proof of [Stacks, Tag 0E8B]: the conditions characterizing the contraction on
the fibres of a family are preserved under extension of the ground field, so the fibrewise
property of the stable model of a prestable family is stable under base change.

## Main results

* `Stacks.Curves.StableModel.IsStableContraction.baseChange`: the conditions of
  [Stacks, Tag 0E7Q] pass to the base change along a field extension.
* `Stacks.Curves.StableModel.existsUnique_iso_baseChange_of_isStableContraction`: the stable
  model of `X_K` is the base change of the stable model of `X`, up to unique isomorphism.

## References

* [Stacks Project, Tag 0E8B](https://stacks.math.columbia.edu/tag/0E8B)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Curves.StableModel

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- **The conditions of [Stacks, Tag 0E7Q] are preserved under extension of the ground field.**
Let `X` be proper over `k` with `H⁰(X, 𝒪_X) = k` and let `c : X ⟶ Y` satisfy the conditions of
[Stacks, Tag 0E7Q]. For a field extension `K/k`, the base change `c_K : X_K ⟶ Y_K` satisfies them
over `K`. -/
theorem IsStableContraction.baseChange {f : X ⟶ Spec (.of k)} {gY : Y ⟶ Spec (.of k)}
    {c : X ⟶ Y} [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (h : IsStableContraction f gY c) (K : Type u) [Field K] [Algebra k K] :
    IsStableContraction (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.snd gY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k K))) gY
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) c (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, h.comp_eq]) (by simp)) := by
  let gK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let cK := pullback.map f gK gY gK c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h.comp_eq])
    (by simp)
  let pX := pullback.fst f gK
  let pY := pullback.fst gY gK
  let fXK := pullback.snd f gK
  let fYK := pullback.snd gY gK
  have : IsProper gY := h.isProper
  have : Flat gK := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have hYsq : IsPullback pY fYK gY gK := IsPullback.of_hasPullback gY gK
  have hcfY : cK ≫ fYK = fXK := by simp [cK, fXK, fYK]
  have hcp : cK ≫ pY = pX ≫ c := by simp [cK, pX, pY]
  have hcsq : IsPullback pX cK c pY := by
    refine IsPullback.of_bot ?_ hcp.symm hYsq
    rw [hcfY, h.comp_eq]
    exact IsPullback.of_hasPullback f gK
  have : IsProper (c ≫ gY) := by rw [h.comp_eq]; infer_instance
  have : IsProper c := IsProper.of_comp c gY
  -- `H⁰(Y, 𝒪_Y) = H⁰(X, 𝒪_X) = k`
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop) := by
    have hc : IsIso c.appTop :=
      Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c
        h.isIso_unitToPushforwardObjUnit ⊤
    have : IsIso (((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop) ≫ c.appTop) := by
      rw [Category.assoc, ← Scheme.Hom.comp_appTop, h.comp_eq]
      infer_instance
    exact IsIso.of_isIso_comp_right _ c.appTop
  have : IsProper fYK := isProper_of_isPullback_specMapAlgebraMap k K pY fYK gY hYsq
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fYK.appTop) :=
    isIso_globalSections_baseChange k K pY fYK gY hYsq
  obtain ⟨hYKdim, hYKnodal⟩ :=
    Stacks.Curves.topologicalKrullDim_eq_one_and_hasAtWorstNodalSingularities_baseChange K gY
      h.topologicalKrullDim_eq h.hasAtWorstNodalSingularities
  refine
    { comp_eq := hcfY
      isProper := inferInstance
      topologicalKrullDim_eq := hYKdim
      hasAtWorstNodalSingularities := hYKnodal
      isIso_unitToPushforwardObjUnit :=
        c.isIso_unitToPushforwardObjUnit_of_isPullback hcsq h.isIso_unitToPushforwardObjUnit
      isZero_rightDerived_one :=
        AlgebraicGeometry.FlatBaseChangeDerived.isZero_rightDerived_pushforward_unit_of_isPullback
          hcsq 1 h.isZero_rightDerived_one
      isAmple := ?_ }
  -- `ω_{Y_K} = (ω_Y)_K` is ample
  obtain ⟨hωY, hωYample⟩ := h.isAmple
  have hωYK := Stacks.Curves.isInvertible_dualizingSheafOverField_of_isIso_globalSections fYK
    hYKdim hYKnodal
  exact ⟨hωYK, Stacks.Curves.isAmple_dualizingSheafOverField_of_isPullback hYsq hωYample⟩

/-- **The stable model commutes with extension of the ground field.** Let `X` be a proper scheme
over `k` of dimension one with `H⁰(X, 𝒪_X) = k`, genus at least two and at-worst-nodal
singularities, and let `c : X ⟶ Y` be its stable model, i.e. a morphism satisfying the conditions
of [Stacks, Tag 0E7Q]. For a field extension `K/k` and any morphism `d : X_K ⟶ Z` satisfying the
conditions of [Stacks, Tag 0E7Q] over `K`, there is a unique isomorphism `e : Y_K ≅ Z` with
`c_K ≫ e = d`: the base change `c_K` satisfies these conditions
(`Stacks.Curves.StableModel.IsStableContraction.baseChange`), and `X_K` satisfies the hypotheses
of [Stacks, Tag 0E7Q], under which such a morphism is unique up to unique isomorphism. -/
theorem existsUnique_iso_baseChange_of_isStableContraction {f : X ⟶ Spec (.of k)}
    {gY : Y ⟶ Spec (.of k)} {c : X ⟶ Y} [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X = 1)
    (hgenus : 2 ≤ genus f)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    (h : IsStableContraction f gY c) (K : Type u) [Field K] [Algebra k K] {Z : Scheme.{u}}
    {gZ : Z ⟶ Spec (.of K)}
    {d : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Z}
    (hd : IsStableContraction (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      gZ d) :
    ∃! e : pullback gY (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅ Z,
      pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k K))) gY
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) c (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, h.comp_eq]) (by simp) ≫ e.hom = d := by
  let gK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hXsq : IsPullback (pullback.fst f gK) (pullback.snd f gK) f gK :=
    IsPullback.of_hasPullback f gK
  have : IsProper (pullback.snd f gK) :=
    isProper_of_isPullback_specMapAlgebraMap k K _ _ f hXsq
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (pullback.snd f gK).appTop) :=
    isIso_globalSections_baseChange k K _ _ f hXsq
  obtain ⟨hXKdim, hXKnodal⟩ :=
    Stacks.Curves.topologicalKrullDim_eq_one_and_hasAtWorstNodalSingularities_baseChange K f hdim
      hnodal
  exact existsUnique_iso_of_isStableContraction (pullback.snd f gK) hXKdim
    ((genus_baseChange k K _ _ f hXsq).symm ▸ hgenus) hXKnodal (h.baseChange K) hd

end Stacks.Curves.StableModel

end
