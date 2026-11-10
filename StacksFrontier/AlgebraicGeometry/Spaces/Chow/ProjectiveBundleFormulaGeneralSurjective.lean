module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaNoetherianInduction

/-!
# The surjectivity half of the projective bundle formula for every finite locally free module

Let `ℰ` be a finite locally free module of rank `n + 1` on a good algebraic space `X`, with
projective bundle `(π : 𝐏(ℰ) → X, 𝒪(1))`. This file proves the surjectivity half of Stacks 0ERV
for `𝐏(ℰ)`.

## Main results

* `AlgebraicGeometry.Space.hasGenericallySurjectiveBundleFormula_projectiveBundle`: the
  hypothesis of the noetherian induction for `𝐏(ℰ)`.
* `AlgebraicGeometry.Space.bundleFormulaSurjective_projectiveBundle_of_forall`: the surjectivity
  half of Stacks 0ERV for `𝐏(ℰ)`, from the freeness of finite locally free modules on nonempty
  opens, the invariance of the formula under isomorphisms of modules, and the formula for `F_n`.
* `AlgebraicGeometry.Space.bundleFormulaSurjective_projectiveBundle_of_freeTower`: the same with
  the formula for `F_n` from its two geometric inputs.

## References

* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section ProjectiveBundle

variable (D : BaseSpaceDimensionSituation.{u})
    {X : AlgebraicSpaces D.site D.base D.base_mem} (sX : X.1 ⟶ D.space) (hX : D.IsGood sX)
    (E : Modules.{u, u} D.site D.base D.base_mem X.1 X.2) (n : ℕ)
    (hr : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X.1 X.2) E (n + 1))

/-- **The hypothesis of the noetherian induction for a projective bundle.** Over every integral
good space `g : T → X` the projective bundle formula for `𝐏(ℰ)` holds on a nonempty open
`j : U → T`. -/
theorem hasGenericallySurjectiveBundleFormula_projectiveBundle
    (hfreeOpen : ∀ (Y : AlgebraicSpaces D.site D.base D.base_mem) (sY : Y.1 ⟶ D.space),
      D.IsGood sY → points D.site D.base D.base_mem Y.1 →
      ∀ F : Modules.{u, u} D.site D.base D.base_mem Y.1 Y.2,
        RingedSite.IsFiniteLocallyFreeOfRank
          (smallEtaleRingedSite D.site D.base D.base_mem Y.1 Y.2) F (n + 1) →
        ∃ (U : AlgebraicSpaces D.site D.base D.base_mem) (j : U ⟶ Y),
          IsOpenImmersion D.site D.base D.base_mem j.hom ∧
            Nonempty (points D.site D.base D.base_mem U.1) ∧
            Nonempty ((modulePullback D.site D.base D.base_mem j).obj F ≅ freeTower U n))
    (hmod : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU) (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2)
      (hF : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F (n + 1))
      (hF' : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F' (n + 1)),
      (F ≅ F') → ProjectiveBundleFormulaHolds D sU hU F n hF →
        ProjectiveBundleFormulaHolds D sU hU F' n hF')
    (hfreeHolds : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU),
      ProjectiveBundleFormulaHolds D sU hU (freeTower U n) n
        (isFiniteLocallyFreeOfRank_freeTower U n)) :
    HasGenericallySurjectiveBundleFormula D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
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
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite) := by
  intro T sT hT g hgB hint
  let T' : AlgebraicSpaces D.site D.base D.base_mem := ⟨T, hT.1⟩
  let g' : T' ⟶ X := ObjectProperty.homMk g
  obtain ⟨U, jU, hj, ⟨u₀⟩, ⟨eU⟩⟩ := hfreeOpen T' sT hT hint.2.2.toNonempty.some
    ((modulePullback D.site D.base D.base_mem g').obj E)
    (isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem g' E (n + 1) hr)
  have hU : D.IsGood (jU.hom ≫ sT) := isGood_comp_of_isOpenImmersion D sT hT U.2 hj
  have hrU := isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem (jU ≫ g') E
    (n + 1) hr
  have hQ : ProjectiveBundleFormulaHolds D (jU.hom ≫ sT) hU
      ((modulePullback D.site D.base D.base_mem (jU ≫ g')).obj E) n hrU :=
    hmod U _ hU (freeTower U n) _ (isFiniteLocallyFreeOfRank_freeTower U n) _
      (eU.symm ≪≫ (modulePullbackCompIsoOfEq D.site D.base D.base_mem jU g' rfl).app E)
      (hfreeHolds U _ hU)
  have hθ := isPullback_projectiveBundlePullbackIso_hom_comp_fst D E n hr (jU ≫ g')
  have hPU := isGood_projectiveBundleProj_comp_of_rank D (jU.hom ≫ sT) hU
    ((modulePullback D.site D.base D.base_mem (jU ≫ g')).obj E) n hrU
  have hθB : ((projectiveBundlePullbackIso
        (hE := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) (jU ≫ g') E
        hr.isFiniteLocallyFreeOnSite).hom ≫
      projectiveBundleFiberProductFst
        (hE := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) (jU ≫ g') E
        hr.isFiniteLocallyFreeOnSite).hom ≫
        (@projectiveBundleProj D.site D.base D.base_mem X E
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
          hr.isFiniteLocallyFreeOnSite).hom ≫ sX =
      (@projectiveBundleProj D.site D.base D.base_mem U
          ((modulePullback D.site D.base D.base_mem (jU ≫ g')).obj E)
          (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2 hrU)
          hrU.isFiniteLocallyFreeOnSite).hom ≫ jU.hom ≫ sT := by
    rw [← Category.assoc, hθ.w, Category.assoc]
    change _ ≫ (jU.hom ≫ g) ≫ sX = _
    rw [Category.assoc, hgB]
  refine ⟨U.1, _, jU.hom ≫ sT, hU, _, hPU, jU.hom, hj, rfl, ⟨u₀⟩, _, _, hθB, rfl, hθ, ?_⟩
  have eTw := ((modulePullbackCompIsoOfEq D.site D.base D.base_mem
      (projectiveBundlePullbackIso (hE := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        (jU ≫ g') E hr.isFiniteLocallyFreeOnSite).hom
      (projectiveBundleFiberProductFst
        (hE := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) (jU ≫ g') E
        hr.isFiniteLocallyFreeOnSite) rfl).app _).symm ≪≫
    projectiveBundleTwistFiberProductIso
      (hE := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) (jU ≫ g') E
      hr.isFiniteLocallyFreeOnSite
  exact BundleFormulaSurjective.of_iso D _ hU _ hPU _ hPU _ rfl _ rfl n _ _ _ _ _ _ _ _
    (𝟙 _) (Category.id_comp _) (Category.id_comp _)
    ((modulePullbackIdIso D.site D.base D.base_mem _).app _ ≪≫ eTw.symm) hQ.2

/-- **The surjectivity half of Stacks 0ERV** for the projective bundle `𝐏(ℰ)` of a finite locally
free module of rank `n + 1` on a good algebraic space, from three inputs on good algebraic spaces
over the base: a finite locally free module of rank `n + 1` is isomorphic to `F_n` on a nonempty
open subspace of any good space with a point; the projective bundle formula is invariant under
isomorphisms of modules; and it holds for `F_n`. -/
theorem bundleFormulaSurjective_projectiveBundle_of_forall
    (hfreeOpen : ∀ (Y : AlgebraicSpaces D.site D.base D.base_mem) (sY : Y.1 ⟶ D.space),
      D.IsGood sY → points D.site D.base D.base_mem Y.1 →
      ∀ F : Modules.{u, u} D.site D.base D.base_mem Y.1 Y.2,
        RingedSite.IsFiniteLocallyFreeOfRank
          (smallEtaleRingedSite D.site D.base D.base_mem Y.1 Y.2) F (n + 1) →
        ∃ (U : AlgebraicSpaces D.site D.base D.base_mem) (j : U ⟶ Y),
          IsOpenImmersion D.site D.base D.base_mem j.hom ∧
            Nonempty (points D.site D.base D.base_mem U.1) ∧
            Nonempty ((modulePullback D.site D.base D.base_mem j).obj F ≅ freeTower U n))
    (hmod : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU) (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2)
      (hF : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F (n + 1))
      (hF' : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F' (n + 1)),
      (F ≅ F') → ProjectiveBundleFormulaHolds D sU hU F n hF →
        ProjectiveBundleFormulaHolds D sU hU F' n hF')
    (hfreeHolds : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU),
      ProjectiveBundleFormulaHolds D sU hU (freeTower U n) n
        (isFiniteLocallyFreeOfRank_freeTower U n)) :
    BundleFormulaSurjective D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
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
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite) :=
  bundleFormulaSurjective_of_hasGenericallySurjectiveBundleFormula D sX hX _ _ _ rfl n _ _
    (@isProper_projectiveBundleProj D.site D.base D.base_mem X E
      (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr) hr.isFiniteLocallyFreeOnSite)
    _ _ (hasGenericallySurjectiveBundleFormula_projectiveBundle D sX hX E n hr hfreeOpen hmod
      hfreeHolds)

/-- **The surjectivity half of Stacks 0ERV** for `𝐏(ℰ)`, from the freeness of a finite locally
free module on a nonempty open subspace, the invariance of the projective bundle formula under
isomorphisms of modules, and the two geometric inputs of the free case: `𝐏(𝒪_U) → U` is an
isomorphism and `i^*𝒪_{𝐏(F_m ⊕ 𝒪)}(1) ≅ 𝒪_{𝐏(F_m)}(1)` along the hyperplane at infinity. -/
theorem bundleFormulaSurjective_projectiveBundle_of_freeTower
    (hfreeOpen : ∀ (Y : AlgebraicSpaces D.site D.base D.base_mem) (sY : Y.1 ⟶ D.space),
      D.IsGood sY → points D.site D.base D.base_mem Y.1 →
      ∀ F : Modules.{u, u} D.site D.base D.base_mem Y.1 Y.2,
        RingedSite.IsFiniteLocallyFreeOfRank
          (smallEtaleRingedSite D.site D.base D.base_mem Y.1 Y.2) F (n + 1) →
        ∃ (U : AlgebraicSpaces D.site D.base D.base_mem) (j : U ⟶ Y),
          IsOpenImmersion D.site D.base D.base_mem j.hom ∧
            Nonempty (points D.site D.base D.base_mem U.1) ∧
            Nonempty ((modulePullback D.site D.base D.base_mem j).obj F ≅ freeTower U n))
    (hmod : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (sU : U.1 ⟶ D.space)
      (hU : D.IsGood sU) (F F' : Modules.{u, u} D.site D.base D.base_mem U.1 U.2)
      (hF : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F (n + 1))
      (hF' : RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem U.1 U.2) F' (n + 1)),
      (F ≅ F') → ProjectiveBundleFormulaHolds D sU hU F n hF →
        ProjectiveBundleFormulaHolds D sU hU F' n hF')
    (hbase : ∀ U : AlgebraicSpaces D.site D.base D.base_mem,
      IsIso (@projectiveBundleProj D.site D.base D.base_mem U (freeTower U 0)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2
          (isFiniteLocallyFreeOfRank_freeTower U 0))
        (isFiniteLocallyFreeOfRank_freeTower U 0).isFiniteLocallyFreeOnSite).hom)
    (htw : ∀ (U : AlgebraicSpaces D.site D.base D.base_mem) (m : ℕ),
      Nonempty ((modulePullback D.site D.base D.base_mem
        (projectiveCompletionInfinityImmersion (freeTower U m)
          (isFiniteLocallyFreeOfRank_freeTower U m))).obj
        (projectiveCompletionTwist (freeTower U m) (isFiniteLocallyFreeOfRank_freeTower U m)).obj ≅
      (@projectiveBundleTwist D.site D.base D.base_mem U (freeTower U m)
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank U.2
          (isFiniteLocallyFreeOfRank_freeTower U m))
        (isFiniteLocallyFreeOfRank_freeTower U m).isFiniteLocallyFreeOnSite).obj)) :
    BundleFormulaSurjective D sX hX _
      (isGood_projectiveBundleProj_comp_of_rank D sX hX E n hr)
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
        (isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank X.2 hr)
        hr.isFiniteLocallyFreeOnSite) :=
  bundleFormulaSurjective_projectiveBundle_of_forall D sX hX E n hr hfreeOpen hmod
    (fun U sU hU => projectiveBundleFormula_freeTower D sU hU (hbase U) (htw U) n)

end ProjectiveBundle

end AlgebraicGeometry.Space

end
