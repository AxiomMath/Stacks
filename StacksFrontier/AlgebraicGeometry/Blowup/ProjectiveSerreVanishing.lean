module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSpaceEmbedding
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoherentSerreVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneIsProjectiveSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre vanishing on the blowup of an affine Noetherian scheme

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec A`
in `I`. The positive-degree cohomology of the twists of the structure sheaf of `X` vanishes once
the twist is large:
$$ H^i(X, \mathcal{O}_X(d)) = 0 \qquad (i > 0,\ d \gg 0). $$

## Main results

* `Stacks.Blowup.exists_isZero_Hgroup_twistingSheaf_reesGrading_of_span`: the vanishing, for a
  blowup presented by a finite generating family of `I`.
* `Stacks.Blowup.exists_isZero_Hgroup_twistingSheaf_reesGrading`: the vanishing over a
  Noetherian ring, where such a family always exists.

## References

* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.ProjectiveCohomology (polyGrading)

universe u

namespace Stacks.Blowup

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The sheaves of modules on a scheme with the sheafified tensor product of [Stacks, Tag 01CA]. -/
local instance modulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

/-- The sheafified tensor product of [Stacks, Tag 01CA] on `SheafOfModules X.ringCatSheaf`. -/
local instance modulesMonoidal' (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} X.ringCatSheaf) :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace

section Descent

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Vanishing of cohomology descends along a closed immersion**: if `Hⁱ(Y, f_*ℱ)` vanishes
then so does `Hⁱ(X, ℱ)`. -/
theorem isZero_Hgroup_of_isZero_Hgroup_pushforward [IsClosedImmersion f] (F : X.Modules)
    (hF : F.IsQuasicoherent) (i : ℕ)
    (h : IsZero (Hgroup Y.ringCatSheaf ⊤ i ((Scheme.Modules.pushforward f).obj F))) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i F) := by
  have := hF
  refine (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    X.ringCatSheaf ⊤ i F).1 ?_
  have h' := (Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward f F i).isZero_iff.2
    ((Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      Y.ringCatSheaf ⊤ i ((Scheme.Modules.pushforward f).obj F)).2 h)
  rw [ModuleCat.isZero_iff_subsingleton] at h' ⊢
  exact h'

/-- **The twist of the direct image of the structure sheaf along a closed immersion is the
direct image of the twist**, for any identification of the inverse image of the twisting module
with a module on the source. -/
def pushforwardUnitTensorIso [IsClosedImmersion f] (E : Y.Modules) (G : X.Modules)
    (e : (Scheme.Modules.pullback f).obj E ≅ G) :
    (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⊗ E ≅
      (Scheme.Modules.pushforward f).obj G :=
  Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso f
      (SheafOfModules.unit X.ringCatSheaf) E ≪≫
    (Scheme.Modules.pushforward f).mapIso (whiskerLeftIso _ e ≪≫ λ_ G)

end Descent

/-- **Serre vanishing on the blowup of an affine scheme in an ideal with a given finite
generating family**: for `i > 0` the cohomology `Hⁱ(X, 𝒪_X(d))` of the `d`-th twist of the
structure sheaf of the blowup vanishes once `d` is large. -/
@[sga "6 VII 3.5" "partial"]
theorem exists_isZero_Hgroup_twistingSheaf_reesGrading_of_span {A : Type u} [CommRing A]
    [IsNoetherianRing A] {I : Ideal A} {n : ℕ} (x : Fin (n + 1) → A) (hx : ∀ j, x j ∈ I)
    (hspan : I = Ideal.span (Set.range x)) (i : ℕ) (hi : 0 < i) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (blowUpSpec I).ringCatSheaf ⊤ i (twistingSheaf (reesGrading I) d)) := by
  set f := blowUpSpecToProjSpace I x hx hspan
  have : IsLocallyNoetherian (blowUpSpec I) := isLocallyNoetherian_of_isClosedImmersion f
  have : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit (blowUpSpec I).ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit (blowUpSpec I)
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.ProjectiveSpace.SerreVanishing.exists_isZero_Hgroup_twist_of_isCoherent A n i hi
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit (blowUpSpec I).ringCatSheaf))
      (isCoherent_pushforward_of_isClosedImmersion f
        (SheafOfModules.unit (blowUpSpec I).ringCatSheaf))
  refine ⟨d₀, fun d hd => isZero_Hgroup_of_isZero_Hgroup_pushforward f
    (twistingSheaf (reesGrading I) d)
    (Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistingSheaf
      (reesGrading I) d) i ?_⟩
  obtain ⟨e⟩ := Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap (polyGrading A n)
    (reesGrading I) (reesPresentation I x hx) _ (surjective_reesPresentation I x hx hspan)
    (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A n) d
  exact (hd₀ d hd).of_iso
    ((Hfunctor (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf ⊤ i).mapIso
      (pushforwardUnitTensorIso f (twistingSheaf (polyGrading A n) d) _ e).symm)

/-- **Serre vanishing on the blowup of an affine Noetherian scheme**: for `i > 0` the cohomology
`Hⁱ(X, 𝒪_X(d))` of the `d`-th twist of the structure sheaf of the blowup of `Spec A` in `I`
vanishes once `d` is large. -/
theorem exists_isZero_Hgroup_twistingSheaf_reesGrading {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (i : ℕ) (hi : 0 < i) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (blowUpSpec I).ringCatSheaf ⊤ i (twistingSheaf (reesGrading I) d)) := by
  classical
  obtain ⟨m, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  have hspan : Ideal.span (Set.range (Fin.snoc y (0 : A))) = I := by
    refine le_antisymm (Ideal.span_le.2 ?_) (hy ▸ Ideal.span_mono ?_)
    · rintro a ⟨j, rfl⟩
      refine Fin.lastCases ?_ ?_ j
      · simp
      · intro j
        simpa using hy ▸ Ideal.subset_span (Set.mem_range_self (f := y) j)
    · rintro a ⟨j, rfl⟩
      exact ⟨j.castSucc, by simp⟩
  exact exists_isZero_Hgroup_twistingSheaf_reesGrading_of_span (I := I) (Fin.snoc y 0)
    (fun j => hspan ▸ Ideal.subset_span (Set.mem_range_self (f := Fin.snoc y (0 : A)) j))
    hspan.symm i hi

end Stacks.Blowup

end
