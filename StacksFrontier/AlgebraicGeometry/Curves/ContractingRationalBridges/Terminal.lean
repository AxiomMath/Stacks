module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingAmple
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.DualizingSheafPullback
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Iterated
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.DualizingSheafDegree
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# Contracting rational bridges until none are left

Let `k` be a field and `X` a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`, genus
`g ≥ 2`, at-worst-nodal singularities and no rational tails. Contract rational bridges
(Tag 0E3M) until none are left: `X = X₀ → X₁ → ⋯ → Xₙ = X'`. Then `ω_{X'}` is ample, and the
morphism `X ⟶ X'` is independent of the choices made ([Stacks, Tag 0E3Q]).

Along the chain `c^* ω_{X'} ≅ ω_X` (Tag 0E3N and induction). This identification shows that `X'`
has no rational tails: a rational tail `D ⊆ X'` has `deg(ω_{X'}|_D) < 0` (Tag 0E63), a component
`C` of `X` mapping onto `D` then has `deg(ω_X|_C) = [R(C) : R(D)] · deg(ω_{X'}|_D) < 0`, while
`deg(ω_X|_C) ≥ 0` because `X` has no rational tails (Tag 0E3J). So Tag 0E3P applies to `X'`. Two
such chains are then two stable contractions of `X` (in the sense of Tag 0E7Q) pulling the
dualizing sheaves back to `ω_X`, so they are related by a unique isomorphism.

## Main results

* `Stacks.Curves.forall_not_isRationalTail_of_pullback_dualizingSheafOverField_iso`: a surjection
  `f : X ⟶ Y` of nodal curves with `f^* ω_Y ≅ ω_X` and `X` without rational tails of genus at
  least two has a target without rational tails.
* `IsIteratedContractionOfRationalBridges.nonempty_pullback_dualizingSheafOverField_iso`
  (namespace `AlgebraicGeometry`): Tag 0E3N along a chain.
* `AlgebraicGeometry.IsIteratedContractionOfRationalBridges.isStableContraction`:
  [Stacks, Tag 0E3Q], `ω_{X'}` is ample; the composite satisfies the conditions of Tag 0E7Q.
* `AlgebraicGeometry.IsIteratedContractionOfRationalBridges.existsUnique_iso`:
  [Stacks, Tag 0E3Q], the morphism `X ⟶ X'` is independent of choices.

## References

* [Stacks Project, Tag 0E3Q](https://stacks.math.columbia.edu/tag/0E3Q)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop)]

/-- **A curve dominated by a curve without rational tails has none.** Let `X` and `Y` be proper
one-dimensional nodal curves over `k` with `H⁰ = k`, `X` of genus at least two without rational
tails, and let `f : X ⟶ Y` be a surjection over `k` with `f^* ω_Y ≅ ω_X`. Then `Y` has no rational
tail. A rational tail `D` has `deg(ω_Y|_D) < 0` (Tag 0E63); a point over its generic point spans an
integral curve `C ⊆ X` mapping onto `D`, so `deg(ω_X|_C) = [R(C) : R(D)] · deg(ω_Y|_D) < 0`, which
contradicts `deg(ω_X|_C) ≥ dim H¹(C, 𝒪_C) ≥ 0` (Tag 0E3J; `deg(ω_X) = 2g - 2 > 0` if `C = X`). -/
theorem forall_not_isRationalTail_of_pullback_dualizingSheafOverField_iso
    (hdimX : topologicalKrullDim X = 1) (hnodalX : HasAtWorstNodalSingularities k X)
    (hdimY : topologicalKrullDim Y = 1) (hnodalY : HasAtWorstNodalSingularities k Y)
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (f : X ⟶ Y) (hf : f ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k))
    (hsurj : Function.Surjective f.base)
    (e : (Scheme.Modules.pullback f).obj
        (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) ≅
      Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))
    (D : Y.IdealSheafData) : ¬ IsRationalTail k Y D := by
  intro hD
  have : IsIntegral D.subscheme := hD.isIntegral
  have hDdim := topologicalKrullDim_subscheme_eq_one_of_isRationalTail k Y hdimY D hD
  have hneg := invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail
    hdimY hnodalY D hD
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have : ConnectedSpace Y := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
  have hωX := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdimX
    hnodalX
  have hωY := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdimY
    hnodalY
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodalX
  have : IsProper f := by
    have : IsProper (f ≫ (Y ↘ Spec (.of k))) := by rw [hf]; infer_instance
    exact IsProper.of_comp f (Y ↘ Spec (.of k))
  -- the generic point `η` of `D` is not closed
  let η : Y := D.subschemeι (genericPoint D.subscheme)
  have hηcl : closure ({η} : Set Y) = D.support := by
    rw [← Set.image_singleton, D.subschemeι.isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ, D.range_subschemeι]
  have hηnc : ¬ IsClosed ({η} : Set Y) := by
    intro h
    have hs : (D.support : Set Y) = {η} := hηcl.symm.trans h.closure_eq
    have : Subsingleton D.subscheme := by
      refine ⟨fun a b => D.subschemeι.isClosedEmbedding.injective ?_⟩
      have ha : D.subschemeι a ∈ (D.support : Set Y) := D.range_subschemeι ▸ ⟨a, rfl⟩
      have hb : D.subschemeι b ∈ (D.support : Set Y) := D.range_subschemeι ▸ ⟨b, rfl⟩
      rw [hs] at ha hb
      exact ha.trans hb.symm
    have h0 : topologicalKrullDim D.subscheme ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology D.subscheme
    rw [hDdim] at h0
    exact absurd h0 (by decide)
  -- a point `ζ` over `η` spans an integral curve `C ⊆ X` mapping onto `D`
  obtain ⟨ζ, hζ⟩ := hsurj η
  let Z : TopologicalSpace.Closeds X := ⟨closure ({ζ} : Set X), isClosed_closure⟩
  let C := Scheme.IdealSheafData.vanishingIdeal Z
  have hCrange : Set.range C.subschemeι = closure ({ζ} : Set X) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal Z
  have : IrreducibleSpace C.subscheme := Scheme.IdealSheafData.irreducibleSpace_subscheme X C
    (by rw [hCrange]; exact isIrreducible_singleton.closure)
  have : IsIntegral C.subscheme := isIntegral_of_irreducibleSpace_of_isReduced C.subscheme
  have hfC : f.base '' closure ({ζ} : Set X) = D.support := by
    refine subset_antisymm ?_ ?_
    · refine (image_closure_subset_closure_image f.continuous).trans ?_
      rw [Set.image_singleton, hζ, hηcl]
    · rw [← hηcl]
      refine closure_minimal ?_ (f.isClosedMap _ isClosed_closure)
      rw [Set.singleton_subset_iff, ← hζ]
      exact Set.mem_image_of_mem _ (subset_closure rfl)
  have hrange : Set.range (C.subschemeι ≫ f).base = D.support := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hCrange, hfC]
  -- if `C` is mapped to a single point, then `η` is closed
  have hcollapse : (∃ y : Y, ∀ a : C.subscheme, (C.subschemeι ≫ f).base a = y) →
      IsClosed ({η} : Set Y) := by
    rintro ⟨y, hy⟩
    obtain ⟨b, hb⟩ : ζ ∈ Set.range C.subschemeι := hCrange ▸ subset_closure rfl
    have hyη : y = η := by rw [← hy b, Scheme.Hom.comp_base, TopCat.comp_app, hb, hζ]
    have hs : (D.support : Set Y) = {η} := by
      refine subset_antisymm ?_ (Set.singleton_subset_iff.2 (hηcl ▸ subset_closure rfl))
      rw [← hrange]
      rintro _ ⟨a, rfl⟩
      rw [hy a, hyη]
      rfl
    rw [← hs]
    exact D.support.isClosed
  have hCdim : topologicalKrullDim C.subscheme = 1 := by
    rcases Stacks.AlgebraicGeometry.ComponentDegrees.topologicalKrullDim_le_zero_or_eq_one
      C.subschemeι hdimX.le with h | h
    · exfalso
      have hpt : ∀ a b : C.subscheme, a = b := fun a b =>
        (Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero h
          (genericPoint_specializes a)).symm.trans
          (Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero h
            (genericPoint_specializes b))
      exact hηnc (hcollapse ⟨_, fun a => congrArg (C.subschemeι ≫ f).base (hpt a (genericPoint _))⟩)
    · exact h
  -- the morphism `h : C ⟶ D` induced by `f`
  have hker : D.subschemeι.ker ≤ (C.subschemeι ≫ f).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    show closure (Set.range (C.subschemeι ≫ f).base) ⊆ (D.support : Set Y)
    rw [hrange]
    exact D.support.isClosed.closure_subset
  let h : C.subscheme ⟶ D.subscheme := IsClosedImmersion.lift D.subschemeι (C.subschemeι ≫ f) hker
  have hh : h ≫ D.subschemeι = C.subschemeι ≫ f := IsClosedImmersion.lift_fac _ _ _
  have hnc : ¬ ∃ y : D.subscheme, ∀ x : C.subscheme, h.base x = y := by
    rintro ⟨y, hy⟩
    apply hηnc
    refine hcollapse ⟨D.subschemeι y, fun a => ?_⟩
    rw [← hh, Scheme.Hom.comp_base, TopCat.comp_app, hy a]
  have : IsCurve k (C.subschemeι ≫ (X ↘ Spec (.of k))) := { topologicalKrullDim_eq_one := hCdim }
  have : IsCurve k (D.subschemeι ≫ (Y ↘ Spec (.of k))) := { topologicalKrullDim_eq_one := hDdim }
  have hcomp : h ≫ D.subschemeι ≫ (Y ↘ Spec (.of k)) = C.subschemeι ≫ (X ↘ Spec (.of k)) := by
    rw [← Category.assoc, hh, Category.assoc, hf]
  let hL := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback D.subschemeι
    (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) hωY
  let hLC := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback C.subschemeι
    (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) hωX
  have key := (invertibleCurveDegree_neg_iff_of_not_constant k _ _ h hcomp hnc
    ((Scheme.Modules.pullback D.subschemeι).obj
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))))).2 hneg
  let φ : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback D.subschemeι).obj
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k)))) ≅
      (Scheme.Modules.pullback C.subschemeι).obj
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) :=
    (Scheme.Modules.pullbackComp h D.subschemeι).app _ ≪≫
      (Scheme.Modules.pullbackCongr hh).app _ ≪≫
      ((Scheme.Modules.pullbackComp C.subschemeι f).app _).symm ≪≫
      (Scheme.Modules.pullback C.subschemeι).mapIso e
  rw [invertibleCurveDegree_eq_of_iso k _ _ φ] at key
  -- but `deg(ω_X|_C) ≥ 0`
  by_cases hCbot : C = ⊥
  · have hZ : (Z : Set X) = Set.univ := by
      have h1 : (C.support : Set X) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
      rw [← h1, hCbot, Scheme.IdealSheafData.support_bot]
      rfl
    have hpos := invertibleCurveDegree_pullback_dualizingSheafOverField_pos_of_eq_univ k
      (X ↘ Spec (.of k)) hdimX.le hg Z hZ hCdim.le
    exact absurd key (not_lt.2 hpos.le)
  · have hJ :=
      finrank_cohomologyOverField_one_le_invertibleCurveDegree_of_forall_not_isRationalTail
        hdimX hnodalX htail C hCdim hCbot
    exact absurd key (not_lt.2 ((Nat.cast_nonneg _).trans hJ))

end Stacks.Curves

namespace AlgebraicGeometry.IsIteratedContractionOfRationalBridges

variable {k : Type u} [Field k]

/-- Tag 0E3N along a chain, with the standing hypotheses as explicit arguments. -/
private theorem nonempty_pullback_dualizingSheafOverField_iso_aux {X Y : Scheme.{u}}
    {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
    (hseq : IsIteratedContractionOfRationalBridges k fX fY c)
    (hproper : IsProper fX) (hdim : topologicalKrullDim X = 1)
    (hglobal : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    haveI := hproper
    haveI := (hseq.standing_target hproper hdim hglobal hnodal).1
    Nonempty ((Scheme.Modules.pullback c).obj (Stacks.Duality.dualizingSheafOverField fY) ≅
      Stacks.Duality.dualizingSheafOverField fX) := by
  induction hseq with
  | identity X fX => exact ⟨(Scheme.Modules.pullbackId X).app _⟩
  | @step X Y Z fX fY fZ c d C hC hbase hd ih =>
    let : X.Over (Spec (.of k)) := ⟨fX⟩
    have : IsProper (X ↘ Spec (.of k)) := hproper
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) := hglobal
    obtain ⟨hCb, hc⟩ := hC hproper
    obtain ⟨g, hcg, hgp, hgdim, hgglob, -⟩ :=
      Stacks.Curves.exists_isProper_structureMorphism_and_genus_eq_contraction_bridge k X hdim
        hnodal C hCb c hc
    have hfY : fY = g := Stacks.Curves.structureMorphism_eq_of_isContractionOfRationalBridge
      hdim hnodal hc (hbase.trans hcg.symm)
    subst hfY
    have hYnodal := Stacks.Curves.hasAtWorstNodalSingularities_of_isContractionOfRationalBridge
      hdim hnodal hc hcg
    have : IsProper fY := hgp
    have := (hd.standing_target hgp hgdim hgglob hYnodal).1
    obtain ⟨ed⟩ := ih hgp hgdim hgglob hYnodal
    obtain ⟨ec⟩ := Stacks.Curves.nonempty_pullback_dualizingSheafOverField_iso_contraction_bridge
      hdim hnodal hc fY hbase
    exact ⟨((Scheme.Modules.pullbackComp c d).app _).symm ≪≫
      (Scheme.Modules.pullback c).mapIso ed ≪≫ ec⟩

variable {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of k)} {c : X ⟶ Y}
  (hseq : IsIteratedContractionOfRationalBridges k fX fY c) [IsProper fX]
  (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop)]
  (hnodal : letI : X.Over (Spec (.of k)) := ⟨fX⟩
    Stacks.Curves.HasAtWorstNodalSingularities k X)

include hseq hdim hnodal

/-- **Tag 0E3N along a chain of contractions of rational bridges**: the composite
`c : X ⟶ Y` of the chain satisfies `c^* ω_Y ≅ ω_X`. Each contraction does
(`Stacks.Curves.nonempty_pullback_dualizingSheafOverField_iso_contraction_bridge`), and the
hypotheses of Tag 0E3M pass along the chain (`standing_target`). -/
theorem nonempty_pullback_dualizingSheafOverField_iso :
    haveI := (hseq.standing_target inferInstance hdim inferInstance hnodal).1
    Nonempty ((Scheme.Modules.pullback c).obj (Stacks.Duality.dualizingSheafOverField fY) ≅
      Stacks.Duality.dualizingSheafOverField fX) :=
  nonempty_pullback_dualizingSheafOverField_iso_aux hseq inferInstance hdim inferInstance hnodal

/-- **Stacks Project, Tag 0E3Q: `ω_{X'}` is ample.** Let `X` be a proper scheme over a field `k`
of dimension one with `H⁰(X, 𝒪_X) = k`, genus `g ≥ 2`, at-worst-nodal singularities and no
rational tails, and let `c : X ⟶ X'` be the composite of a sequence of contractions of rational
bridges (Tag 0E3M) such that `X'` has no rational bridge. Then `ω_{X'}` is invertible and ample;
more precisely `c` satisfies the conditions of Tag 0E7Q: `X'` is proper of dimension one with
at-worst-nodal singularities, `𝒪_{X'} = c_* 𝒪_X`, `R¹ c_* 𝒪_X = 0`, and `ω_{X'}` is ample.

The target has no rational tails
(`Stacks.Curves.forall_not_isRationalTail_of_pullback_dualizingSheafOverField_iso`, from
`c^* ω_{X'} ≅ ω_X`), so Tag 0E3P applies to it. -/
@[stacks 0E3Q "ω_{X'} is ample"]
theorem isStableContraction
    (htail : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hg : 2 ≤ genus fX)
    (hterminal : ∀ C : Y.IdealSheafData,
      letI : Y.Over (Spec (.of k)) := ⟨fY⟩
      ∀ _ : IsProper (Y ↘ Spec (.of k)), ¬ IsRationalBridge k Y C) :
    Stacks.Curves.StableModel.IsStableContraction fX fY c := by
  obtain ⟨hYp, hYdim, hYglob, hYnodal, hYgenus, hO, hR⟩ :=
    hseq.standing_target inferInstance hdim inferInstance hnodal
  let : X.Over (Spec (.of k)) := ⟨fX⟩
  let : Y.Over (Spec (.of k)) := ⟨fY⟩
  have : IsProper (Y ↘ Spec (.of k)) := hYp
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop) := hYglob
  have : IsProper (X ↘ Spec (.of k)) := inferInstanceAs (IsProper fX)
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ fX.appTop))
  have hcomp := hseq.comp_structureMorphism
  obtain ⟨e⟩ := hseq.nonempty_pullback_dualizingSheafOverField_iso hdim hnodal
  have : IsProper c := by
    have : IsProper (c ≫ fY) := by rw [hcomp]; infer_instance
    exact IsProper.of_comp c fY
  have hsurj : Function.Surjective c.base :=
    (c.surjective_of_isIso_app fun U =>
      Stacks.Curves.DualizingPullback.isIso_app_of_isIso_unitToPushforwardObjUnit c hO U).surj
  have hYtail := Stacks.Curves.forall_not_isRationalTail_of_pullback_dualizingSheafOverField_iso
    hdim hnodal hYdim hYnodal htail hg c hcomp hsurj e
  refine ⟨hcomp, hYp, hYdim, hYnodal, hO, hR 1 one_pos, ?_⟩
  exact isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hYdim hYnodal hYtail
    (fun C => hterminal C hYp) (hYgenus ▸ hg)

/-- **Stacks Project, Tag 0E3Q: the morphism `X ⟶ X'` is independent of choices.** Under the
hypotheses of `AlgebraicGeometry.IsIteratedContractionOfRationalBridges.isStableContraction`, if
`c₂ : X ⟶ X'₂` is the composite of a second sequence of contractions of rational bridges such that
`X'₂` has no rational bridge, then there is a unique isomorphism `e : X' ≅ X'₂` with
`c ≫ e.hom = c₂`. Both composites are stable contractions pulling the dualizing sheaves back to
`ω_X` (Tag 0E3N along each chain), so
`Stacks.Curves.StableModel.existsUnique_iso_of_pullback_dualizingSheafOverField_iso` applies. -/
@[stacks 0E3Q "the morphism X ⟶ X' is independent of choices"]
theorem existsUnique_iso
    (htail : letI : X.Over (Spec (.of k)) := ⟨fX⟩
      ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hg : 2 ≤ genus fX)
    (hterminal : ∀ C : Y.IdealSheafData,
      letI : Y.Over (Spec (.of k)) := ⟨fY⟩
      ∀ _ : IsProper (Y ↘ Spec (.of k)), ¬ IsRationalBridge k Y C)
    {Y₂ : Scheme.{u}} {fY₂ : Y₂ ⟶ Spec (.of k)} {c₂ : X ⟶ Y₂}
    (hseq₂ : IsIteratedContractionOfRationalBridges k fX fY₂ c₂)
    (hterminal₂ : ∀ C : Y₂.IdealSheafData,
      letI : Y₂.Over (Spec (.of k)) := ⟨fY₂⟩
      ∀ _ : IsProper (Y₂ ↘ Spec (.of k)), ¬ IsRationalBridge k Y₂ C) :
    ∃! e : Y ≅ Y₂, c ≫ e.hom = c₂ := by
  have h₁ := hseq.isStableContraction hdim hnodal htail hg hterminal
  have h₂ := hseq₂.isStableContraction hdim hnodal htail hg hterminal₂
  obtain ⟨e₁⟩ := hseq.nonempty_pullback_dualizingSheafOverField_iso hdim hnodal
  obtain ⟨e₂⟩ := hseq₂.nonempty_pullback_dualizingSheafOverField_iso hdim hnodal
  exact Stacks.Curves.StableModel.existsUnique_iso_of_pullback_dualizingSheafOverField_iso h₁ h₂
    (e₁ ≪≫ e₂.symm)

end AlgebraicGeometry.IsIteratedContractionOfRationalBridges
