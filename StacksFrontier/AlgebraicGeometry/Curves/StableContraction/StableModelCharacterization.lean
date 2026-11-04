module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModelUniqueness
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Terminal

/-!
# The stable model of a nodal curve of genus at least two

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, genus
`g ≥ 2` and at-worst-nodal singularities. There is a morphism `c : X ⟶ Y` over `k`, unique up to
unique isomorphism, with `Y` proper of dimension one and at-worst-nodal, `𝒪_Y = c_*𝒪_X`,
`R¹c_*𝒪_X = 0` and `ω_Y` ample ([Stacks, Tag 0E7Q]).

## Main results

* `Stacks.Curves.StableModel.exists_isStableContraction`: existence, by contracting rational
  tails ([Stacks, Tag 0E3L]) and then rational bridges ([Stacks, Tag 0E3Q]).
* `Stacks.Curves.StableModel.existsUnique_isStableContraction`: [Stacks, Tag 0E7Q].
* `Stacks.Curves.StableModel.exists_isStableContraction_comp_tails_bridges`: [Stacks, Tag 0E7N],
  the composite of the two contractions, with `H⁰(Y, 𝒪_Y) = k`, the genus preserved, and its
  characterization by the conditions of [Stacks, Tag 0E7Q].

## References

* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E7N](https://stacks.math.columbia.edu/tag/0E7N)
* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
* [Stacks Project, Tag 0E3Q](https://stacks.math.columbia.edu/tag/0E3Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Curves.StableModel

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Existence in [Stacks, Tag 0E7Q]**: a proper nodal curve over `k` with `H⁰ = k` and genus
`g ≥ 2` has a stable contraction. Contract rational tails until none is left
(`IsIteratedContractionOfRationalTails.exists_forall_not_isRationalTail`), then rational bridges
until none is left (`IsIteratedContractionOfRationalBridges.exists_forall_not_isRationalBridge`);
the second chain is a stable contraction of the tail-free curve ([Stacks, Tag 0E3Q]) and the
first is acyclic for the structure sheaf, so the composite is a stable contraction of `X`. -/
theorem exists_isStableContraction (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hgenus : 2 ≤ genus f)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    ∃ (Y : Scheme.{u}) (gY : Y ⟶ Spec (.of k)) (c : X ⟶ Y), IsStableContraction f gY c := by
  obtain ⟨X₁, f₁, t, hseq, htail⟩ :=
    IsIteratedContractionOfRationalTails.exists_forall_not_isRationalTail k f hdim hnodal
  have : IsProper f₁ := hseq.isProper_target hdim hnodal
  have hdim₁ := hseq.topologicalKrullDim_target hdim hnodal
  have := hseq.isIso_globalSections_target hdim hnodal
  have hnodal₁ := hseq.hasAtWorstNodalSingularities_target hdim hnodal
  have hg₁ : 2 ≤ genus f₁ := (hseq.genus_target hdim hnodal).symm ▸ hgenus
  obtain ⟨Y, gY, d, hbr, -, hterm⟩ :=
    IsIteratedContractionOfRationalBridges.exists_forall_not_isRationalBridge hdim₁ hnodal₁
  have hst := hbr.isStableContraction hdim₁ hnodal₁ htail hg₁ hterm
  have ht := hseq.comp_structureMap
  have : IsProper (t ≫ f₁) := by rw [ht]; infer_instance
  have : IsProper t := IsProper.of_comp t f₁
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  exact ⟨Y, gY, t ≫ d, IsStableContraction.comp t d ht
    (hseq.isIso_unitToPushforwardObjUnit hdim hnodal)
    (fun i hi => hseq.isZero_rightDerived hdim hnodal i hi) hst⟩

/-- **Stacks Project, Tag 0E7Q.** Let `X` be a proper scheme over a field `k` of dimension one
with `H⁰(X, 𝒪_X) = k`, genus `g ≥ 2` and at-worst-nodal singularities. There is a morphism
`c : X ⟶ Y` of schemes over `k` such that
1. `Y` is proper over `k`, `dim Y = 1`, and `Y` has at-worst-nodal singularities,
2. `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, and
3. `ω_Y` is ample on `Y`

(`IsStableContraction f gY c`), and it is unique up to unique isomorphism: any two such
`c : X ⟶ Y`, `c' : X ⟶ Y'` are related by exactly one isomorphism `e : Y ≅ Y'` with
`c ≫ e = c'`. -/
@[stacks 0E7Q "Condition (3) includes that `ω_Y` is invertible, as ampleness is defined for \
invertible modules. Uniqueness up to unique isomorphism: any two such morphisms are related by \
exactly one isomorphism of targets under `X`."]
theorem existsUnique_isStableContraction (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hgenus : 2 ≤ genus f)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    (∃ (Y : Scheme.{u}) (gY : Y ⟶ Spec (.of k)) (c : X ⟶ Y), IsStableContraction f gY c) ∧
      ∀ (Y Y' : Scheme.{u}) (gY : Y ⟶ Spec (.of k)) (gY' : Y' ⟶ Spec (.of k)) (c : X ⟶ Y)
        (c' : X ⟶ Y'), IsStableContraction f gY c → IsStableContraction f gY' c' →
        ∃! e : Y ≅ Y', c ≫ e.hom = c' :=
  ⟨exists_isStableContraction f hdim hgenus hnodal, fun _ _ _ _ _ _ h h' =>
    existsUnique_iso_of_isStableContraction f hdim hgenus hnodal h h'⟩

/-- **Stacks Project, Tag 0E7N: contracting to a stable curve.** Let `X` be a proper scheme over a
field `k` of dimension one with `H⁰(X, 𝒪_X) = k`, genus `g ≥ 2` and at-worst-nodal singularities.
Contract rational tails until none are left, `t : X ⟶ X₁` ([Stacks, Tag 0E3L]), and then rational
bridges until none are left, `d : X₁ ⟶ Y` ([Stacks, Tag 0E3Q]). The composite `c = t ≫ d` is a
morphism over `k` such that `Y` is proper over `k` of dimension one with at-worst-nodal
singularities, `H⁰(Y, 𝒪_Y) = k`, `Y` has genus `g`, `𝒪_Y = c_*𝒪_X`, `R¹c_*𝒪_X = 0`, and `ω_Y` is
ample. These conditions characterize `c` ([Stacks, Tag 0E7Q]): any `c' : X ⟶ Y'` satisfying the
conditions of `IsStableContraction` is related to `c` by exactly one isomorphism `e : Y ≅ Y'` with
`c ≫ e.hom = c'`. -/
@[stacks 0E7N]
theorem exists_isStableContraction_comp_tails_bridges (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X = 1) [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hgenus : 2 ≤ genus f)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    ∃ (X₁ : Scheme.{u}) (f₁ : X₁ ⟶ Spec (.of k)) (t : X ⟶ X₁) (Y : Scheme.{u})
      (gY : Y ⟶ Spec (.of k)) (d : X₁ ⟶ Y),
      IsIteratedContractionOfRationalTails k f f₁ t ∧
      (∀ C : X₁.IdealSheafData, ¬ @IsRationalTail k _ X₁ ⟨f₁⟩ C) ∧
      IsIteratedContractionOfRationalBridges k f₁ gY d ∧
      (∀ C : Y.IdealSheafData,
        letI : Y.Over (Spec (.of k)) := ⟨gY⟩
        ∀ _ : IsProper (Y ↘ Spec (.of k)), ¬ IsRationalBridge k Y C) ∧
      IsStableContraction f gY (t ≫ d) ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ gY.appTop) ∧
      genus gY = genus f ∧
      ∀ (Y' : Scheme.{u}) (gY' : Y' ⟶ Spec (.of k)) (c' : X ⟶ Y'),
        IsStableContraction f gY' c' → ∃! e : Y ≅ Y', (t ≫ d) ≫ e.hom = c' := by
  obtain ⟨X₁, f₁, t, hseq, htail⟩ :=
    IsIteratedContractionOfRationalTails.exists_forall_not_isRationalTail k f hdim hnodal
  have : IsProper f₁ := hseq.isProper_target hdim hnodal
  have hdim₁ := hseq.topologicalKrullDim_target hdim hnodal
  have := hseq.isIso_globalSections_target hdim hnodal
  have hnodal₁ := hseq.hasAtWorstNodalSingularities_target hdim hnodal
  have hg₁ : genus f₁ = genus f := hseq.genus_target hdim hnodal
  obtain ⟨Y, gY, d, hbr, -, hterm⟩ :=
    IsIteratedContractionOfRationalBridges.exists_forall_not_isRationalBridge hdim₁ hnodal₁
  have hst := hbr.isStableContraction hdim₁ hnodal₁ htail (hg₁.symm ▸ hgenus) hterm
  obtain ⟨-, -, hglob, -, hgY, -, -⟩ :=
    hbr.standing_target inferInstance hdim₁ inferInstance hnodal₁
  have : IsProper (t ≫ f₁) := by rw [hseq.comp_structureMap]; infer_instance
  have : IsProper t := IsProper.of_comp t f₁
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have hc : IsStableContraction f gY (t ≫ d) := IsStableContraction.comp t d
    hseq.comp_structureMap (hseq.isIso_unitToPushforwardObjUnit hdim hnodal)
    (fun i hi => hseq.isZero_rightDerived hdim hnodal i hi) hst
  exact ⟨X₁, f₁, t, Y, gY, d, hseq, htail, hbr, hterm, hc, hglob, hgY.trans hg₁,
    fun _ _ _ h' => existsUnique_iso_of_isStableContraction f hdim hgenus hnodal hc h'⟩

end Stacks.Curves.StableModel
