module
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.Topology.Maps.Proper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineReduction
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineReduction

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeZariskiLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCancellationUnconditional
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveLineTowerCover

/-!
# ProjectiveLineReductionGeneral

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProjectiveLineReduction`, stated
as separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u v

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

/-- Cohomology commutes with base change for `h` if `h = f ≫ g` with `f` finite and `g` proper
satisfying the condition. -/
private theorem cohomologyCommutesWithBaseChange_of_isFinite_comp_eq {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] {g : Y ⟶ Z} [IsProper g] {h : X ⟶ Z} (hfg : f ≫ g = h)
    (hg : CohomologyCommutesWithBaseChange.{u, v} g) :
    CohomologyCommutesWithBaseChange.{u, v} h :=
  CohomologyCommutesWithBaseChange.of_eq hfg
    (CohomologyCommutesWithBaseChange.comp
      (cohomologyCommutesWithBaseChange_of_isFinite_general f) hg)

/-- An immersion `i` followed by a proper `q` with `i ≫ q` proper is finite. -/
private theorem isFinite_of_isImmersion_of_isProper_comp {X Y Z : Scheme.{u}} (i : X ⟶ Y)
    (q : Y ⟶ Z) [IsImmersion i] [IsProper q] [IsProper (i ≫ q)] : IsFinite i := by
  have : IsProper i := .of_comp i q
  have : IsClosedImmersion i := .of_isPreimmersion i i.isClosedMap.isClosed_range
  infer_instance

/-- **Cohomology commutes with base change for every base change of `ℙ¹_T ⟶ T`.** The second
projection `ℙ¹_T ×_T B ⟶ B` is `ℙ¹_B ⟶ B` up to the isomorphism
`AlgebraicGeometry.ProjectiveSpace.baseChangeIso`, which is finite. -/
public theorem cohomologyCommutesWithBaseChange_pullback_snd_projectiveLine
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    {T B : Scheme.{u}} (k : B ⟶ T) :
    CohomologyCommutesWithBaseChange.{u, v} (pullback.snd (ProjectiveSpace 1 T ↘ T) k) :=
  cohomologyCommutesWithBaseChange_of_isFinite_comp_eq (ProjectiveSpace.baseChangeIso 1 k).hom
    (ProjectiveSpace.baseChangeIso_hom_over 1 k) (hline B)

/-- **Cohomology commutes with base change for every base change of the projection of the
`n`-fold power of the projective line.** Induction on `n`: the projection of the `(n+1)`-st stage
is the projective line over the `n`-th stage followed by the projection of the `n`-th stage, and a
base change of that composite is, up to the pasting isomorphism of pullbacks, a base change of the
projective line followed by a base change of the `n`-th projection. -/
public theorem cohomologyCommutesWithBaseChange_pullback_snd_projectiveLineTowerHom
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    (S : Scheme.{u}) (n : ℕ) {B : Scheme.{u}} (h : B ⟶ S) :
    CohomologyCommutesWithBaseChange.{u, v} (pullback.snd (projectiveLineTowerHom S n) h) := by
  induction n generalizing B with
  | zero =>
      have : IsIso (pullback.snd (projectiveLineTowerHom S 0) h) :=
        inferInstanceAs (IsIso (pullback.snd (𝟙 S) h))
      exact cohomologyCommutesWithBaseChange_of_isFinite_general _
  | succ n ih =>
      let π := ProjectiveSpace 1 (projectiveLineTower S n) ↘ projectiveLineTower S n
      let t := projectiveLineTowerHom S n
      let e := pullbackRightPullbackFstIso t h π
      exact cohomologyCommutesWithBaseChange_of_isFinite_comp_eq e.inv
        (pullbackRightPullbackFstIso_inv_snd_snd t h π)
        (CohomologyCommutesWithBaseChange.comp
          (cohomologyCommutesWithBaseChange_pullback_snd_projectiveLine hline _) (ih h))

/-- **Cohomology commutes with base change for the projection of the `n`-fold power of the
projective line**, the base change of that projection along the identity. -/
public theorem cohomologyCommutesWithBaseChange_projectiveLineTowerHom_unconditional
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    (S : Scheme.{u}) (n : ℕ) :
    CohomologyCommutesWithBaseChange.{u, v} (projectiveLineTowerHom S n) := by
  have hiso : IsIso (pullback.fst (projectiveLineTowerHom S n) (𝟙 S)) := inferInstance
  have hw : pullback.fst (projectiveLineTowerHom S n) (𝟙 S) ≫ projectiveLineTowerHom S n =
      pullback.snd (projectiveLineTowerHom S n) (𝟙 S) := by
    rw [pullback.condition, Category.comp_id]
  exact cohomologyCommutesWithBaseChange_of_isFinite_comp_eq
    (inv (pullback.fst (projectiveLineTowerHom S n) (𝟙 S)))
    (by rw [← hw, IsIso.inv_hom_id_assoc])
    (cohomologyCommutesWithBaseChange_pullback_snd_projectiveLineTowerHom hline S n _)

/-- **Cohomology commutes with base change for a surjective `S`-morphism from the tower of
projective lines to `ℙⁿ_S`.** Its graph `T ⟶ T ×_S ℙⁿ_S` is a closed immersion, being a section of
the separated projection to `T`, and the second projection `T ×_S ℙⁿ_S ⟶ ℙⁿ_S` is a base change of
the projection of the tower. -/
public theorem cohomologyCommutesWithBaseChange_of_comp_eq_projectiveLineTowerHom
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    (S : Scheme.{u}) (n : ℕ) (c : projectiveLineTower S n ⟶ ProjectiveSpace n S)
    (hc : c ≫ (ProjectiveSpace n S ↘ S) = projectiveLineTowerHom S n) :
    CohomologyCommutesWithBaseChange.{u, v} c := by
  let t := projectiveLineTowerHom S n
  let p := ProjectiveSpace n S ↘ S
  let γ : projectiveLineTower S n ⟶ pullback t p :=
    pullback.lift (𝟙 _) c (by rw [Category.id_comp, hc])
  have hγfst : γ ≫ pullback.fst t p = 𝟙 _ := pullback.lift_fst _ _ _
  have hγsnd : γ ≫ pullback.snd t p = c := pullback.lift_snd _ _ _
  have : IsClosedImmersion (γ ≫ pullback.fst t p) := hγfst ▸ inferInstance
  have : IsClosedImmersion γ := IsClosedImmersion.of_comp γ (pullback.fst t p)
  exact cohomologyCommutesWithBaseChange_of_isFinite_comp_eq γ hγsnd
    (cohomologyCommutesWithBaseChange_pullback_snd_projectiveLineTowerHom hline S n p)

/-- **Cohomology commutes with base change for `ℙⁿ_S ⟶ S`.** The `n`-fold power of the
projective line covers `ℙⁿ_S` by a surjective morphism over `S`, so the condition for the
projection of that power descends to `ℙⁿ_S ⟶ S`. -/
public theorem cohomologyCommutesWithBaseChange_projectiveSpace_unconditional
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    (n : ℕ) (S : Scheme.{u}) :
    CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace n S ↘ S) := by
  obtain ⟨c, hcsurj, hctri⟩ := exists_surjective_projectiveLineTower S n
  have : IsProper (c ≫ (ProjectiveSpace n S ↘ S)) := hctri ▸ inferInstance
  have : IsProper c := IsProper.of_comp c (ProjectiveSpace n S ↘ S)
  have : Surjective c := hcsurj
  refine CohomologyCommutesWithBaseChange.of_comp_of_surjective c _
    (cohomologyCommutesWithBaseChange_of_comp_eq_projectiveLineTowerHom hline S n c hctri) ?_
  exact CohomologyCommutesWithBaseChange.of_eq hctri.symm
    (cohomologyCommutesWithBaseChange_projectiveLineTowerHom_unconditional hline S n)

/-- **Cohomology commutes with base change for a proper morphism to an affine scheme.** Chow's
lemma provides `π : X' ⟶ X` proper and surjective together with an immersion of `X'` into
`ℙⁿ_Y` over `Y`. Both `X' ⟶ ℙⁿ_Y` and the induced `X' ⟶ ℙⁿ_X` are proper, by Morphisms, Lemma
29.42.7, hence closed immersions and so finite; each therefore composes with a projection of a
projective space to give the condition for `X' ⟶ Y` and for `π`, and the condition for `f`
follows by descent along `π`. -/
public theorem cohomologyCommutesWithBaseChange_of_isAffine_unconditional
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [IsProper f] :
    CohomologyCommutesWithBaseChange.{u, v} f := by
  obtain ⟨n, X', π, i, hπ, hπsurj, hi, hcomm⟩ :=
    hasChowModification_of_compactSpace_quasiSeparatedSpace f
  have : IsProper π := hπ
  have : IsImmersion i := hi
  -- `X' ⟶ ℙⁿ_Y` is proper, hence a closed immersion, hence finite.
  have : IsProper (i ≫ (ProjectiveSpace n Y ↘ Y)) := hcomm ▸ inferInstance
  have : IsFinite i := isFinite_of_isImmersion_of_isProper_comp i (ProjectiveSpace n Y ↘ Y)
  -- hence cohomology commutes with base change for `X' ⟶ Y`.
  have hXY : CohomologyCommutesWithBaseChange.{u, v} (π ≫ f) :=
    cohomologyCommutesWithBaseChange_of_isFinite_comp_eq i hcomm.symm
      (cohomologyCommutesWithBaseChange_projectiveSpace_unconditional hline n Y)
  -- the induced morphism `X' ⟶ ℙⁿ_X = X ×_Y ℙⁿ_Y` is proper, hence finite by the same route.
  set j : X' ⟶ pullback (ProjectiveSpace n Y ↘ Y) f := pullback.lift i π hcomm.symm with hj
  have hjfst : j ≫ pullback.fst (ProjectiveSpace n Y ↘ Y) f = i := pullback.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd (ProjectiveSpace n Y ↘ Y) f = π := pullback.lift_snd _ _ _
  have : IsImmersion (j ≫ pullback.fst (ProjectiveSpace n Y ↘ Y) f) := hjfst ▸ ‹IsImmersion i›
  have : IsImmersion j := IsImmersion.of_comp j (pullback.fst _ _)
  have : IsProper (j ≫ pullback.snd (ProjectiveSpace n Y ↘ Y) f) := hjsnd ▸ ‹IsProper π›
  have : IsFinite j := isFinite_of_isImmersion_of_isProper_comp j (pullback.snd _ _)
  -- the second projection of that pullback is `ℙⁿ_X ⟶ X` up to the canonical isomorphism.
  have hsnd : CohomologyCommutesWithBaseChange.{u, v}
      (pullback.snd (ProjectiveSpace n Y ↘ Y) f) :=
    cohomologyCommutesWithBaseChange_of_isFinite_comp_eq (ProjectiveSpace.baseChangeIso n f).hom
      (ProjectiveSpace.baseChangeIso_hom_over n f)
      (cohomologyCommutesWithBaseChange_projectiveSpace_unconditional hline n X)
  have hπbc : CohomologyCommutesWithBaseChange.{u, v} π :=
    cohomologyCommutesWithBaseChange_of_isFinite_comp_eq j hjsnd hsnd
  have : Surjective π := hπsurj
  exact CohomologyCommutesWithBaseChange.of_comp_of_surjective π f hπbc hXY

/-- **[Stacks, Tag 0A4F].** To prove that cohomology commutes with base change for every proper
morphism of schemes it suffices to prove it for the morphism `ℙ¹_S ⟶ S` for every scheme `S`:
if cohomology commutes with base change for every `ℙ¹_S ⟶ S`, then it does for every proper
`f`. -/
@[stacks 0A4F]
public theorem cohomologyCommutesWithBaseChange_of_projectiveLine_unconditional
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, v} (ProjectiveSpace 1 S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsProper f) :
    CohomologyCommutesWithBaseChange.{u, v} f := by
  have := hf
  refine cohomologyCommutesWithBaseChange_of_affineOpens f fun V ↦ ?_
  have : IsAffine V.1.toScheme := V.2
  exact cohomologyCommutesWithBaseChange_of_isAffine_unconditional hline _

end Stacks.EtaleCohomology

end
