module

public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Terminal
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.UnitPushforwardFlatBaseChange

/-!
# Contracting rational bridges commutes with extension of the ground field

Let `k` be a field and `X` a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`, genus
`g ≥ 2`, at-worst-nodal singularities and no rational tails, and let `c : X ⟶ X'` be the composite
of a sequence of contractions of rational bridges until none are left. For a field extension `K/k`
the base change `c_K : X_K ⟶ X'_K` is, up to a unique isomorphism under `X_K`, the morphism the
same construction produces for `X_K` ([Stacks, Tag 0E3Q]).

The curve `X_K` again satisfies the hypotheses: properness, dimension, `H⁰`, genus and nodality
pass to it, and it has no rational tails because `c_K^* ω_{X'_K} ≅ ω_{X_K}` with `ω_{X'_K}` ample
(`Stacks.Curves.forall_not_isRationalTail_of_pullback_iso_of_isAmple`). Here
`ω_{X'_K} ≅ (ω_{X'})_K` and `ω_{X_K} ≅ (ω_X)_K` ([Stacks, Tag 0E32]) and `c^* ω_{X'} ≅ ω_X`
(Tag 0E3N along the chain). So a chain `d : X_K ⟶ Z` for `X_K` is a stable contraction, `c_K`
satisfies `𝒪_{X'_K} = c_{K,*} 𝒪_{X_K}` by flat base change ([Stacks, Tag 02KH]), and both pull the
ample dualizing sheaves of their targets back to `ω_{X_K}`; such contractions are isomorphic
under `X_K` (`Stacks.ContractionComparison.exists_iso_comp_eq_of_isAmple`).

## Main results

* `Stacks.Curves.forall_not_isRationalTail_of_pullback_iso_of_isAmple`: a nodal curve whose
  dualizing sheaf is the pullback of an ample invertible module along a proper morphism has no
  rational tail.
* `AlgebraicGeometry.IsIteratedContractionOfRationalBridges.existsUnique_iso_baseChange`:
  [Stacks, Tag 0E3Q], formation of `X ⟶ X'` commutes with base field extensions.

## References

* [Stacks Project, Tag 0E3Q](https://stacks.math.columbia.edu/tag/0E3Q)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **A curve whose dualizing sheaf is pulled back from an ample module has no rational tail.**
Let `X` be a proper one-dimensional nodal curve over `k` with `H⁰ = k`, and let `f : X ⟶ Y` be
proper with `f^* L ≅ ω_X` for an ample invertible `𝒪_Y`-module `L`. On a rational tail `C`,
`deg(ω_X|_C) < 0` (Tag 0E63); but `deg((f^* L)|_C)` is `0` if `f` contracts `C` to a point and
positive otherwise, `L` being ample. -/
theorem forall_not_isRationalTail_of_pullback_iso_of_isAmple
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    {Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (hL : Scheme.Modules.IsAmple Y L)
    (e : (Scheme.Modules.pullback f).obj L ≅
      Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))
    (C : X.IdealSheafData) : ¬ IsRationalTail k X C := by
  intro hC
  have : IsIntegral C.subscheme := hC.isIntegral
  have hCdim := topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC
  have hneg := invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail
    hdim hnodal C hC
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have hωX := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
    hnodal
  let := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι
    (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) hωX
  let : AlgebraicGeometry.SheafOfModules.IsInvertible C.subscheme.presheaf
      C.subscheme.ringCatSheaf.2 ((Scheme.Modules.pullback (C.subschemeι ≫ f)).obj L) :=
    Stacks.Modules.isInvertible_pullback _ _
  rw [invertibleCurveDegree_eq_of_iso k _ _
    ((Scheme.Modules.pullback C.subschemeι).mapIso e.symm ≪≫
      (Scheme.Modules.pullbackComp C.subschemeι f).app L)] at hneg
  by_cases hsub : (Set.range (C.subschemeι ≫ f).base).Subsingleton
  · obtain ⟨z⟩ : Nonempty C.subscheme := inferInstance
    exact hneg.ne (invertibleCurveDegree_pullback_eq_zero_of_forall_eq k
      (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim.le (C.subschemeι ≫ f) L
      ((C.subschemeι ≫ f).base z) fun w => hsub ⟨w, rfl⟩ ⟨z, rfl⟩)
  · have := Stacks.AlgebraicGeometry.ComponentDegrees.isNoetherian_of_isProper_over_field k
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
    exact lt_asymm hneg (invertibleCurveDegree_pos_of_isAmple_of_not_subsingleton_range k
      (C.subschemeι ≫ (X ↘ Spec (.of k))) hCdim (C.subschemeι ≫ f) hsub L hL)

end Stacks.Curves

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- The base change `X_K` of a proper one-dimensional nodal curve `X` over `k` with
`H⁰(X, 𝒪_X) = k` is again a one-dimensional nodal curve over `K`. -/
theorem topologicalKrullDim_eq_one_and_hasAtWorstNodalSingularities_baseChange (K : Type u)
    [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      HasAtWorstNodalSingularities k X) :
    topologicalKrullDim
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) = 1 ∧
      letI : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).Over
          (Spec (.of K)) := ⟨pullback.snd f _⟩
      HasAtWorstNodalSingularities K
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType f)
  exact ⟨(topologicalKrullDim_baseChange k K _ _ f (IsPullback.of_hasPullback _ _)).trans hdim,
    hasAtWorstNodalSingularities_baseChange k K X
      (equidimensional_of_isIso_globalSections_of_dimension_one k f hdim) hdim hnodal⟩

/-- The dualizing sheaf of a proper one-dimensional nodal curve with `H⁰(X, 𝒪_X) = k` is
invertible. -/
theorem isInvertible_dualizingSheafOverField_of_isIso_globalSections {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      HasAtWorstNodalSingularities k X) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k f
  exact isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal

variable {K : Type u} [Field K] [Algebra k K]

/-- Ampleness of the dualizing sheaf of a proper scheme over `k` passes to its base change along a
field extension `K/k`, since `ω_{Y_K} ≅ (ω_Y)_K` ([Stacks, Tag 0E32]). -/
theorem isAmple_dualizingSheafOverField_of_isPullback {Y Y' : Scheme.{u}}
    {fY : Y ⟶ Spec (.of k)} [IsProper fY] {pY : Y' ⟶ Y} {fY' : Y' ⟶ Spec (.of K)} [IsProper fY']
    (h : IsPullback pY fY' fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField fY)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y'.toRingedSpace.presheaf
      (structureSheafRing Y'.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField fY')]
    (hY : Scheme.Modules.IsAmple Y (Stacks.Duality.dualizingSheafOverField fY)) :
    Scheme.Modules.IsAmple Y' (Stacks.Duality.dualizingSheafOverField fY') := by
  let : AlgebraicGeometry.SheafOfModules.IsInvertible Y'.presheaf Y'.ringCatSheaf.2
      ((Scheme.Modules.pullback pY).obj (Stacks.Duality.dualizingSheafOverField fY)) :=
    Stacks.Modules.isInvertible_pullback _ _
  have : IsAffineHom pY := MorphismProperty.of_isPullback h.flip inferInstance
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace fY'
  exact Scheme.Modules.isAmple_of_iso
    (Stacks.Duality.dualizingSheafOverFieldBaseChangeIso fY pY fY' h)
    (Scheme.Modules.isAmple_pullback_of_isAffineHom pY _ hY)

/-- If `c : X ⟶ Y` over `k` satisfies `c^* ω_Y ≅ ω_X`, then so does any morphism
`c' : X_K ⟶ Y_K` lying over it between the base changes along a field extension `K/k`. -/
theorem nonempty_pullback_dualizingSheafOverField_iso_of_isPullback {X Y X' Y' : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} [IsProper fX] [IsProper fY]
    {pX : X' ⟶ X} {fX' : X' ⟶ Spec (.of K)} {pY : Y' ⟶ Y} {fY' : Y' ⟶ Spec (.of K)}
    [IsProper fX'] [IsProper fY']
    (hX : IsPullback pX fX' fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hY : IsPullback pY fY' fY (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {c : X ⟶ Y} {c' : X' ⟶ Y'} (hc : c' ≫ pY = pX ≫ c)
    (e : (Scheme.Modules.pullback c).obj (Stacks.Duality.dualizingSheafOverField fY) ≅
      Stacks.Duality.dualizingSheafOverField fX) :
    Nonempty ((Scheme.Modules.pullback c').obj (Stacks.Duality.dualizingSheafOverField fY') ≅
      Stacks.Duality.dualizingSheafOverField fX') :=
  ⟨(Scheme.Modules.pullback c').mapIso
      (Stacks.Duality.dualizingSheafOverFieldBaseChangeIso fY pY fY' hY).symm ≪≫
    (Scheme.Modules.pullbackComp c' pY).app _ ≪≫ (Scheme.Modules.pullbackCongr hc).app _ ≪≫
    ((Scheme.Modules.pullbackComp pX c).app _).symm ≪≫ (Scheme.Modules.pullback pX).mapIso e ≪≫
    Stacks.Duality.dualizingSheafOverFieldBaseChangeIso fX pX fX' hX⟩

/-- A morphism `c : X ⟶ Y` is proper if `c ≫ g = f` with `f` and `g` proper. -/
private theorem isProper_of_comp_eq {X Y S : Scheme.{u}} (c : X ⟶ Y) (g : Y ⟶ S) {f : X ⟶ S}
    (h : c ≫ g = f) [IsProper f] [IsProper g] : IsProper c := by
  subst h
  exact IsProper.of_comp c g

/-- A morphism `c : X ⟶ Y` over `k` with `𝒪_Y = c_* 𝒪_X` onto a nodal curve with ample dualizing
sheaf is related to every stable contraction `d : X ⟶ Z` with `c^* ω_Y ≅ d^* ω_Z` by a unique
isomorphism `e : Y ≅ Z` under `X`. -/
theorem existsUnique_iso_of_isStableContraction_of_isAmple {X Y Z : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {fZ : Z ⟶ Spec (.of k)} [IsProper fX]
    [IsProper fY] {c : X ⟶ Y} {d : X ⟶ Z} (hc : c ≫ fY = fX)
    (hO : IsIso (SheafOfModules.unitToPushforwardObjUnit c.toRingCatSheafHom))
    (hnodal : letI : Y.Over (Spec (.of k)) := ⟨fY⟩
      HasAtWorstNodalSingularities k Y)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property (Stacks.Duality.dualizingSheafOverField fY)]
    (hY : Scheme.Modules.IsAmple Y (Stacks.Duality.dualizingSheafOverField fY))
    (hd : StableModel.IsStableContraction fX fZ d)
    (φ : haveI := hd.isProper
      (Scheme.Modules.pullback c).obj (Stacks.Duality.dualizingSheafOverField fY) ≅
        (Scheme.Modules.pullback d).obj (Stacks.Duality.dualizingSheafOverField fZ)) :
    ∃! e : Y ≅ Z, c ≫ e.hom = d := by
  have : IsProper fZ := hd.isProper
  have : IsProper c := isProper_of_comp_eq c fY hc
  have : IsProper d := isProper_of_comp_eq d fZ hd.comp_eq
  have : Surjective c := c.surjective_of_isIso_app
    (DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c hO)
  have : Surjective d := d.surjective_of_isIso_app
    (DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit d
      hd.isIso_unitToPushforwardObjUnit)
  let : Y.Over (Spec (.of k)) := ⟨fY⟩
  have : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType fY)
  have := isReduced_of_hasAtWorstNodalSingularities k Y hnodal
  have := hd.isReduced
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from fY]; infer_instance⟩
  have : Z.IsSeparated := ⟨by rw [← terminal.comp_from fZ]; infer_instance⟩
  obtain ⟨hωZ, hωZample⟩ := hd.isAmple
  obtain ⟨e, he⟩ := Stacks.ContractionComparison.exists_iso_comp_eq_of_isAmple c d hO
    hd.isIso_unitToPushforwardObjUnit _ _ φ hY hωZample
  refine ⟨e, he, fun e' he' => Iso.ext ?_⟩
  have : IsDominant c := c.isDominant_of_isIso_unitToPushforwardObjUnit hO
  exact ext_of_isDominant c (he'.trans he.symm)

end Stacks.Curves

namespace AlgebraicGeometry.IsIteratedContractionOfRationalBridges

variable {k : Type u} [Field k]
variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
  (hseq : IsIteratedContractionOfRationalBridges k fX fY c) [IsProper fX]
  (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
  (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
    Stacks.Curves.HasAtWorstNodalSingularities k X)

include hseq hdim hnodal

/-- Formation of the contraction `c : X ⟶ Y` commutes with base field extensions: under the
hypotheses of `AlgebraicGeometry.IsIteratedContractionOfRationalBridges.isStableContraction`, let
`K/k` be a field extension, `X_K = X ×_k K` and `Y_K = Y ×_k K` over `K`, and `c_K : X_K ⟶ Y_K` the
base change of `c`. For every sequence `d : X_K ⟶ Z` of contractions of rational bridges of `X_K`
over `K` such that `Z` has no rational bridge, there is a unique isomorphism `e : Y_K ≅ Z` with
`c_K ≫ e.hom = d`: the morphism the construction produces for `X_K` is the base change of the one
for `X`. -/
@[stacks 0E3Q "formation of the morphism X ⟶ X' commutes with base field extensions"]
theorem existsUnique_iso_baseChange
    (htail : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hg : 2 ≤ genus fX)
    (hterminal : ∀ C : Y.IdealSheafData,
      letI : Y.Over (Spec (.of k)) := ⟨fY⟩
      ∀ _ : IsProper (Y ↘ Spec (.of k)), ¬ IsRationalBridge k Y C)
    (K : Type u) [Field K] [Algebra k K] {Z : Scheme.{u}} {fZ : Z ⟶ Spec (.of K)}
    {d : pullback fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ Z}
    (hd : IsIteratedContractionOfRationalBridges K
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k K)))) fZ d)
    (hdterminal : ∀ C : Z.IdealSheafData,
      letI : Z.Over (Spec (.of K)) := ⟨fZ⟩
      ∀ _ : IsProper (Z ↘ Spec (.of K)), ¬ IsRationalBridge K Z C) :
    ∃! e : pullback fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅ Z,
      pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) c (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, hseq.comp_structureMorphism]) (by simp) ≫ e.hom = d := by
  let gK : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let cK := pullback.map fX gK fY gK c (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hseq.comp_structureMorphism]) (by simp)
  let pX := pullback.fst fX gK
  let pY := pullback.fst fY gK
  let fXK := pullback.snd fX gK
  let fYK := pullback.snd fY gK
  obtain ⟨hYp, hYdim, hYglob, hYnodal, -, hO, -⟩ :=
    hseq.standing_target inferInstance hdim inferInstance hnodal
  have : IsProper fY := hYp
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fY.appTop) := hYglob
  obtain ⟨eX⟩ := hseq.nonempty_pullback_dualizingSheafOverField_iso hdim hnodal
  obtain ⟨hωY, hωYample⟩ := (hseq.isStableContraction hdim hnodal htail hg hterminal).isAmple
  have hXsq : IsPullback pX fXK fX gK := IsPullback.of_hasPullback fX gK
  have hYsq : IsPullback pY fYK fY gK := IsPullback.of_hasPullback fY gK
  have hcfY : cK ≫ fYK = fXK := by simp [cK, fXK, fYK]
  have hcp : cK ≫ pY = pX ≫ c := by simp [cK, pX, pY]
  have : IsProper fXK := isProper_of_isPullback_specMapAlgebraMap k K pX fXK fX hXsq
  have : IsProper fYK := isProper_of_isPullback_specMapAlgebraMap k K pY fYK fY hYsq
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fXK.appTop) :=
    isIso_globalSections_baseChange k K pX fXK fX hXsq
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fYK.appTop) :=
    isIso_globalSections_baseChange k K pY fYK fY hYsq
  obtain ⟨hXKdim, hXKnodal⟩ :=
    Stacks.Curves.topologicalKrullDim_eq_one_and_hasAtWorstNodalSingularities_baseChange K fX hdim
      hnodal
  obtain ⟨hYKdim, hYKnodal⟩ :=
    Stacks.Curves.topologicalKrullDim_eq_one_and_hasAtWorstNodalSingularities_baseChange K fY
      hYdim hYnodal
  have := Stacks.Curves.isInvertible_dualizingSheafOverField_of_isIso_globalSections fYK hYKdim
    hYKnodal
  have hωYKample := Stacks.Curves.isAmple_dualizingSheafOverField_of_isPullback hYsq hωYample
  obtain ⟨φ⟩ := Stacks.Curves.nonempty_pullback_dualizingSheafOverField_iso_of_isPullback hXsq hYsq
    hcp eX
  have : IsProper cK := Stacks.Curves.isProper_of_comp_eq cK fYK hcfY
  let : (pullback fX gK : Scheme.{u}).Over (Spec (.of K)) := ⟨fXK⟩
  have : IsProper ((pullback fX gK : Scheme.{u}) ↘ Spec (.of K)) := inferInstanceAs (IsProper fXK)
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      ((pullback fX gK : Scheme.{u}) ↘ Spec (.of K)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fXK.appTop))
  have hdstab := hd.isStableContraction hXKdim hXKnodal
    (Stacks.Curves.forall_not_isRationalTail_of_pullback_iso_of_isAmple hXKdim hXKnodal cK _
      hωYKample φ) (genus_baseChange k K pX fXK fX hXsq ▸ hg) hdterminal
  obtain ⟨eZ⟩ := hd.nonempty_pullback_dualizingSheafOverField_iso hXKdim hXKnodal
  have : Flat pY := MorphismProperty.of_isPullback hYsq.flip inferInstance
  have : IsProper c := Stacks.Curves.isProper_of_comp_eq c fY hseq.comp_structureMorphism
  exact Stacks.Curves.existsUnique_iso_of_isStableContraction_of_isAmple hcfY
    (c.isIso_unitToPushforwardObjUnit_of_isPullback
      (IsPullback.of_bot (by rwa [hcfY, hseq.comp_structureMorphism]) hcp.symm hYsq) hO)
    hYKnodal hωYKample hdstab (φ ≪≫ eZ.symm)

end AlgebraicGeometry.IsIteratedContractionOfRationalBridges
