module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProductRegular
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ProjectiveLineDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSmooth
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData

/-!
# The projective line `𝐏¹_k` as a smooth projective scheme

The projective line `𝐏¹_k = Stacks.Chow.relativeProjectiveLine (Spec k)` over a field `k`, the
base change of the projective line over the integers, as an object of the category of smooth
projective schemes over `k`: it has Krull dimension one, its structure morphism is smooth,
proper and H-projective, and it is nonempty and equidimensional of dimension one.

## Main definitions

* `Stacks.WeilCohomology.projectiveLineObj`: `𝐏¹_k` as a smooth projective scheme over `k`.

## Main results

* `Stacks.WeilCohomology.topologicalKrullDim_relativeProjectiveLine_spec`: `dim 𝐏¹_k = 1`.
* `Stacks.WeilCohomology.isProjectiveMorphism_relativeProjectiveLine_spec`: `𝐏¹_k` is
  H-projective over `k`.
* `Stacks.WeilCohomology.relativeDimension_relativeProjectiveLine_spec`: `𝐏¹_k` has relative
  dimension one over `k`.
* `Stacks.WeilCohomology.isNonemptyEquidimensional_projectiveLineObj`: `𝐏¹_k` is nonempty and
  equidimensional of dimension one.

## References

* [Stacks Project, Tag 0FHI](https://stacks.math.columbia.edu/tag/0FHI)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-- The projective line over a field has Krull dimension one. -/
theorem topologicalKrullDim_relativeProjectiveLine_spec :
    topologicalKrullDim (relativeProjectiveLine (Spec (.of k))) = 1 := by
  have : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of k)))
  rw [topologicalKrullDim_eq_relativeDimension_toNat (fieldChowSituation k)
    (fun _ _ => rfl) (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
    (𝟙 _) (genericPoint (relativeProjectiveLine (Spec (.of k))))
    ((genericPoint_spec (relativeProjectiveLine (Spec (.of k)))).trans (by simp))]
  change ((relativeDimension (fieldChowSituation k).dimensionFunction
    (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
    (genericPoint (relativeProjectiveLine (Spec (.of k))))).toNat : WithBot ℕ∞) = 1
  rw [relativeDimension_relativeProjectiveLine_genericPoint (CommRingCat.of k)
      (fieldChowSituation k).dimensionFunction]
  change (((fieldChowSituation k).dimensionFunction (genericPoint (Spec (.of k))) + 1).toNat :
    WithBot ℕ∞) = 1
  rw [fieldChowSituation_dimensionFunction k (genericPoint (Spec (.of k)))]
  rfl

/-- The structure morphism of the projective line over a field is H-projective. -/
theorem isProjectiveMorphism_relativeProjectiveLine_spec :
    IsProjectiveMorphism (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) :=
  Stacks.HQuasiProjectiveDimensionOne.isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
    _ (topologicalKrullDim_relativeProjectiveLine_spec k).le

/-- The projective line `𝐏¹_k` as a smooth projective scheme over `k`. -/
abbrev projectiveLineObj : (SmoothProjectiveScheme k).FullSubcategory :=
  ⟨Over.mk (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)),
    smooth_relativeProjectiveLine_over (Spec (.of k)),
    (isProjectiveMorphism_relativeProjectiveLine_spec k).isProjective⟩

/-- The structure morphism of `𝐏¹_k` is smooth. -/
instance smooth_projectiveLineObj : Smooth (projectiveLineObj k).obj.hom :=
  smooth_relativeProjectiveLine_over (Spec (.of k))

/-- The structure morphism of `𝐏¹_k` is proper. -/
instance isProper_projectiveLineObj : IsProper (projectiveLineObj k).obj.hom :=
  isProper_relativeProjectiveLine_over (Spec (.of k))

/-- The projective line over a field has relative dimension one. -/
theorem relativeDimension_relativeProjectiveLine_spec :
    AlgebraicGeometry.RelativeDimension
      (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) 1 := by
  intro s _
  have : IsIso ((Spec (CommRingCat.of k)).fromSpecResidueField s) :=
    isIso_fromSpecResidueField_spec_field k s
  have hiso : IsIso ((relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).fiberι s) := by
    change IsIso (pullback.fst (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))
      ((Spec (CommRingCat.of k)).fromSpecResidueField s))
    infer_instance
  let e := Scheme.homeoOfIso
    (asIso ((relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)).fiberι s))
  refine ⟨TopologicalSpace.Equidimensional.of_homeomorph e
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace _), ?_⟩
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
  exact topologicalKrullDim_relativeProjectiveLine_spec k

/-- `𝐏¹_k` is nonempty and equidimensional of dimension one. -/
theorem isNonemptyEquidimensional_projectiveLineObj :
    IsNonemptyEquidimensional (projectiveLineObj k) 1 where
  nonempty := show Nonempty (relativeProjectiveLine (Spec (.of k))) from inferInstance
  relativeDimension := relativeDimension_relativeProjectiveLine_spec k

end Stacks.WeilCohomology

end
