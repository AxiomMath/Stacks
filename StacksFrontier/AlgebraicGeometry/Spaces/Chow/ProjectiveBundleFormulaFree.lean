module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaIsoBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveCompletionBundleFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankNotionBridge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UnitTorsorsOfInvertibleModules

/-!
# The projective bundle formula for the free modules

On an algebraic space `X` let `F_0 = 𝒪_X` and `F_{n+1} = F_n ⊕ 𝒪_X`
(`AlgebraicGeometry.Space.freeTower`), the free module of rank `n + 1` presented as an iterated
projective completion: `𝐏(F_{n+1})` is the projective completion of `F_n`. Both halves of the
projective bundle formula hold for `𝐏(F_n)`, by induction on `n`: for `n = 0` the projection
`𝐏(𝒪_X) → X` is an isomorphism, and the inductive step is the projective completion step
(`AlgebraicGeometry.Space.bundleTopPowerIdentity_projectiveCompletion`,
`AlgebraicGeometry.Space.bundleFormulaSurjective_projectiveCompletion`).

The two geometric inputs, the comparison `i^*𝒪_{𝐏(F ⊕ 𝒪)}(1) ≅ 𝒪_{𝐏(F)}(1)` along the hyperplane at
infinity and the isomorphism `𝐏(𝒪_X) ≅ X`, are explicit arguments.

## Main definitions

* `AlgebraicGeometry.Space.freeTower`: `F_n = 𝒪_X^{⊕(n+1)}` as an iterated `- ⊕ 𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_unit_smallEtale`: `𝒪_X` has rank `1`.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_freeTower`: `F_n` has rank `n + 1`.
* `AlgebraicGeometry.Space.projectiveBundleFormula_freeTower`: both halves of the formula for
  `𝐏(F_n)`.

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

section Tower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X : AlgebraicSpaces B S hS)

/-- **The structure sheaf has rank `1`** on the small étale site (Stacks 0409). -/
theorem isFiniteLocallyFreeOfRank_unit_smallEtale :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      (SheafOfModules.unit _) 1 := by
  intro U
  refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ?_⟩
  · refine (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering ?_
      ((smallEtaleRingedSite B S hS X.1 X.2).J.top_mem U)
    intro Y g _
    exact ⟨U, g, 𝟙 U, Presieve.ofArrows.mk PUnit.unit, Category.comp_id g⟩
  · let N := SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over U)
    have hN : IsColimit (Cofan.mk N (fun _ : Fin 1 => 𝟙 N)) :=
      Stacks.Cohomology.Torsors.Generators.cofanFinOneIsColimitOfIso (Iso.refl N)
    exact ⟨fun _ => 𝟙 N, ⟨hN⟩⟩

/-- **The free module `F_n = 𝒪_X^{⊕(n+1)}`**, as `F_0 = 𝒪_X` and `F_{n+1} = F_n ⊕ 𝒪_X`. -/
def freeTower : ℕ → Modules.{u, u} B S hS X.1 X.2
  | 0 => SheafOfModules.unit _
  | n + 1 => addUnit X.2 (freeTower n)

/-- `F_n` has rank `n + 1`. -/
theorem isFiniteLocallyFreeOfRank_freeTower : ∀ n : ℕ,
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) (freeTower X n)
      (n + 1)
  | 0 => isFiniteLocallyFreeOfRank_unit_smallEtale X
  | n + 1 => isFiniteLocallyFreeOfRank_addUnit (isFiniteLocallyFreeOfRank_freeTower n)

end Tower

section Formula

variable (D : BaseSpaceDimensionSituation.{u})
    {X : AlgebraicSpaces D.site D.base D.base_mem} (sX : X.1 ⟶ D.space) (hX : D.IsGood sX)

/-- **Both halves of the projective bundle formula for `𝐏(E)`**, `E` of rank `n + 1`: the top power
of Stacks 0ERU and the surjectivity half of Stacks 0ERV. -/
def ProjectiveBundleFormulaHolds (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (n + 1)) : Prop :=
  BundleTopPowerIdentity D sX hX _ (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).hom rfl n
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@isProper_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite) ∧
    BundleFormulaSurjective D sX hX _ (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
      (@projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).hom rfl n
      (@isFlat_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@hasRelativeDimension_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) n hr
        hr.isFiniteLocallyFreeOnSite)
      (@projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).obj
      (@isInvertibleModule_projectiveBundleTwist D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite)

/-- **The projective bundle formula for the free modules `F_n`**, by induction on `n` through the
projective completions, granted the two geometric inputs: `𝐏(𝒪_X) → X` is an isomorphism, and the
twist comparison along the hyperplane at infinity of each `𝐏(F_n ⊕ 𝒪_X)`. -/
theorem projectiveBundleFormula_freeTower
    (hbase : IsIso (@projectiveBundleProj D.site D.base D.base_mem X (freeTower X 0)
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2
        (isFiniteLocallyFreeOfRank_freeTower X 0))
      (isFiniteLocallyFreeOfRank_freeTower X 0).isFiniteLocallyFreeOnSite).hom)
    (htw : ∀ n : ℕ, Nonempty ((modulePullback D.site D.base D.base_mem
        (projectiveCompletionInfinityImmersion (freeTower X n)
          (isFiniteLocallyFreeOfRank_freeTower X n))).obj
        (projectiveCompletionTwist (freeTower X n) (isFiniteLocallyFreeOfRank_freeTower X n)).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem X (freeTower X n)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2
          (isFiniteLocallyFreeOfRank_freeTower X n))
        (isFiniteLocallyFreeOfRank_freeTower X n).isFiniteLocallyFreeOnSite).obj)) :
    ∀ n : ℕ, ProjectiveBundleFormulaHolds D sX hX (freeTower X n) n
      (isFiniteLocallyFreeOfRank_freeTower X n)
  | 0 => by
    have := hbase
    exact ⟨bundleTopPowerIdentity_of_isIso D sX hX _ _ _ rfl _ _ _ _ _,
      bundleFormulaSurjective_of_isIso D sX hX _ _ _ rfl _ _ _ _⟩
  | n + 1 => by
    obtain ⟨ih₁, ih₂⟩ := projectiveBundleFormula_freeTower hbase htw n
    obtain ⟨e⟩ := htw n
    have := isFiniteLocallyFree_sheafOfModules_of_isFiniteLocallyFreeOfRank (freeTower X n)
      (isFiniteLocallyFreeOfRank_freeTower X n)
    have := isFiniteLocallyFreeOfRank_sheafOfModules (freeTower X n)
      (isFiniteLocallyFreeOfRank_freeTower X n)
    exact ⟨bundleTopPowerIdentity_projectiveCompletion D sX hX (freeTower X n) n
        (isFiniteLocallyFreeOfRank_freeTower X n) e ih₁,
      bundleFormulaSurjective_projectiveCompletion D sX hX (freeTower X n) n
        (isFiniteLocallyFreeOfRank_freeTower X n) e ih₂⟩

/-- **The projective bundle formula passes along an isomorphism of projective bundles over `X`**
matching the twists: if `φ : 𝐏(E') ≅ 𝐏(E)` lies over `X` and `φ^*𝒪_{𝐏(E)}(1) ≅ 𝒪_{𝐏(E')}(1)`, the
formula for `𝐏(E)` gives the one for `𝐏(E')`. -/
theorem ProjectiveBundleFormulaHolds.of_iso {E E' : Modules.{u, u} D.site D.base D.base_mem X.1 X.2}
    {n : ℕ}
    {hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (n + 1)}
    {hr' : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E' (n + 1)}
    (φ : (@projectiveBundle D.site D.base D.base_mem X E'
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr')
        hr'.isFiniteLocallyFreeOnSite).1 ⟶
      (@projectiveBundle D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).1) [IsIso φ]
    (hφπ : φ ≫ (@projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite).hom =
      (@projectiveBundleProj D.site D.base D.base_mem X E'
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr')
        hr'.isFiniteLocallyFreeOnSite).hom)
    (e : (modulePullback D.site D.base D.base_mem
      (ObjectProperty.homMk φ :
        (⟨_, (isGood_projectiveBundleProj_comp_of_rank D sX hX E' n hr').1⟩ :
        AlgebraicSpaces D.site D.base D.base_mem) ⟶
        ⟨_, (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr).1⟩)).obj
        (@projectiveBundleTwist D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem X E'
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr')
        hr'.isFiniteLocallyFreeOnSite).obj)
    (h : ProjectiveBundleFormulaHolds D sX hX E n hr) :
    ProjectiveBundleFormulaHolds D sX hX E' n hr' :=
  ⟨BundleTopPowerIdentity.of_iso D sX hX _ _ _ _ _ rfl _ rfl n _ _ _ _ _ _ _ _ _ _ φ
      (by rw [← Category.assoc, hφπ]) hφπ e h.1,
    BundleFormulaSurjective.of_iso D sX hX _ _ _ _ _ rfl _ rfl n _ _
      (@isProper_projectiveBundleProj D.site D.base D.base_mem X E
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite) _ _
      (@isProper_projectiveBundleProj D.site D.base D.base_mem X E'
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr') hr'.isFiniteLocallyFreeOnSite)
      _ _ _ _ φ
      (by rw [← Category.assoc, hφπ]) hφπ e h.2⟩

end Formula

end AlgebraicGeometry.Space

end
