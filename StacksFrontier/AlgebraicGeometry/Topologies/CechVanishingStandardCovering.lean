module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AssociatedModuleOnCoarserTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSliceCoveringObject
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnTheSlice
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleSlicePowerSections
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.OverSliceContinuity
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingOnAffineSlice
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringSingletonReduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfASingletonUpToIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech vanishing for a standard covering, with quasi-coherent coefficients

For a standard `τ`-covering of an affine object of `Over S`, the higher Čech cohomology of the
presheaf `Fᵃ` of [Stacks, Tag 03DS] vanishes.

## Main results

* `AlgebraicGeometry.grothendieckTopology_coveringMorphismProperty_le_fpqcTopology`: each of the
  five topologies is coarser than the fpqc topology, uniformly in `τ`.
* `AlgebraicGeometry.isSheaf_over_quasiCoherentPresheafFunctor`: `Fᵃ` is a sheaf on the big
  `τ`-site of `S`, uniformly in `τ`.
* `AlgebraicGeometry.isAffine_cechNerveTerminalFrom_overAffineAlgSpec`: the fibre powers over
  `U` of the spectrum of an algebra over the coordinate ring of `U.left` have affine total
  space.
* `AlgebraicGeometry.isZero_cechCohomology_singleton_succ_quasiCoherentPresheaf_of_powerSections`:
  positive-degree Čech vanishing for a one-member covering of an affine object of `Over S` by an
  affine object, given an identification of the power sections of the slice module with the
  Amitsur coefficients.
* `AlgebraicGeometry.isZero_cechCohomology_singleton_succ_quasiCoherentPresheaf`: positive-degree
  Čech vanishing for a one-member covering of an affine object of `Over S` by an affine object
  whose coordinate ring is faithfully flat over that of the target.
* `AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf_of_singleton`:
  positive-degree Čech vanishing for a standard `τ`-covering follows from that for the
  one-member covering by its disjoint union.
* `AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf`: positive-degree Čech
  vanishing for a standard `τ`-covering of an affine object of `Over S`, uniformly in the five
  topologies.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03OZ](https://stacks.math.columbia.edu/tag/03OZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology Stacks.CechSite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### The big `τ`-site is coarser than the fpqc site -/

/-- Each of the five topologies is coarser than the fpqc topology. -/
@[sga "4 VII 4.2" "partial"]
public theorem grothendieckTopology_coveringMorphismProperty_le_fpqcTopology
    (τ : CoveringTopology) :
    Scheme.grothendieckTopology (coveringMorphismProperty τ) ≤ Scheme.fpqcTopology.{u} :=
  le_trans (Scheme.grothendieckTopology_monotone
      (coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation τ))
    Scheme.fppfTopology_le_fpqcTopology

/-- The presheaf `Fᵃ` is a sheaf on the big `τ`-site of `S`, for each of the five topologies. -/
public theorem isSheaf_over_quasiCoherentPresheafFunctor (τ : CoveringTopology) (S : Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf ((Scheme.grothendieckTopology (coveringMorphismProperty τ)).over S)
      (quasiCoherentPresheafFunctor S F) :=
  Stacks.EtaleCohomology.isSheaf_associatedPresheaf_of_le S F
    (grothendieckTopology_coveringMorphismProperty_le_fpqcTopology τ)

/-! ### The fibre powers of an affine object of the slice are affine -/

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left]

/-- The fibre powers over `U` of the spectrum of an algebra over the coordinate ring of `U.left`
have affine total space. -/
public theorem isAffine_cechNerveTerminalFrom_overAffineAlgSpec
    (a : CommAlgCat.{u} (ULift.{u} (Γ(U.left, ⊤) : Type u))) (n : SimplexCategory) :
    IsAffine ((cechNerveTerminalFrom ((overAffineAlgSpec U).obj (op a))).obj (op n)).left.left :=
  (essImage_overAffineAlgSpec U).mp
    ⟨∏ᶜ (fun _ : Fin (n.len + 1) ↦ (op a : (CommAlgCat.{u}
        (ULift.{u} (Γ(U.left, ⊤) : Type u)))ᵒᵖ)),
      ⟨PreservesProduct.iso (overAffineAlgSpec U)
        (fun _ : Fin (n.len + 1) ↦ (op a : (CommAlgCat.{u}
          (ULift.{u} (Γ(U.left, ⊤) : Type u)))ᵒᵖ))⟩⟩

/-! ### The one-member covering by an affine object -/

/-- Čech vanishing in positive degrees for the one-member covering of an affine object of
`Over S` by an affine object whose coordinate ring is faithfully flat over that of the target,
with the presheaf `Fᵃ` of [Stacks, Tag 03DS] as coefficients, given an identification `hpow` of
the power sections of the slice module with the Amitsur coefficients. -/
public theorem isZero_cechCohomology_singleton_succ_quasiCoherentPresheaf_of_powerSections
    (F : S.Modules) [F.IsQuasicoherent] {W : Over S} (f : W ⟶ U) [IsAffine W.left]
    (hff : letI := overAffineSliceAlgebra U f
      Module.FaithfullyFlat (Γ(U.left, ⊤) : Type u) (Γ(W.left, ⊤) : Type u))
    (hpow : letI := overAffineSliceAlgebra U f
      Stacks.CechSite.powerSections
          ((overAffineAlgSpec U).obj (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))))
          (Stacks.Sites.sliceAssociatedModuleCat F U) ≅
        Stacks.CechSite.powerSections
            ((overAffineAlgSpec U).obj (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))))
            (overAffineAlgΓ U).leftOp ⋙
          Stacks.Descent.amitsurCoefficients.{u, u, u} (Γ(U.left, ⊤) : Type u)
            (Stacks.Sites.coeffModule S F (𝟭 (Over S)) U))
    (p : ℕ) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{u} f)
      (quasiCoherentPresheafFunctor S F) (p + 1)) := by
  let _ := overAffineSliceAlgebra U f
  have := hff
  exact Stacks.CechSite.isZero_cechCohomology_singleton_of_iso.{u} f
    ((overAffineAlgSpec U).obj (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)))).hom
    (mkIsoMkSpecOverAffineAlgObj U f) (quasiCoherentPresheafFunctor S F) (p + 1)
    (isZero_cechCohomology_singleton_succ_overAffine U (Γ(W.left, ⊤) : Type u)
      (Stacks.Sites.coeffModule S F (𝟭 (Over S)) U) (quasiCoherentPresheafFunctor S F)
      (Stacks.Sites.sliceAssociatedModuleCat F U)
      (Stacks.Sites.sliceAssociatedModuleCatForget₂Iso F U)
      (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)) hpow
      (sectionsTerminalArrowIsoAlgebraMapArrow U (Γ(W.left, ⊤) : Type u)) p)

/-- Čech vanishing in positive degrees for the one-member covering of an affine object of
`Over S` by an affine object whose coordinate ring is faithfully flat over that of the target,
with the presheaf `Fᵃ` of [Stacks, Tag 03DS] as coefficients. -/
@[stacks 03FJ "the `Cech^p = 0 for p >= 1` clause, for the one-member covering 03FI reduces \
to; unconditional -- hcoeff, harrow and hcolim are all three discharged"]
public theorem isZero_cechCohomology_singleton_succ_quasiCoherentPresheaf
    (F : S.Modules) [F.IsQuasicoherent] {W : Over S} (f : W ⟶ U) [IsAffine W.left]
    (hff : letI := overAffineSliceAlgebra U f
      Module.FaithfullyFlat (Γ(U.left, ⊤) : Type u) (Γ(W.left, ⊤) : Type u))
    (p : ℕ) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{u} f)
      (quasiCoherentPresheafFunctor S F) (p + 1)) :=
  let _halg := overAffineSliceAlgebra U f
  isZero_cechCohomology_singleton_succ_quasiCoherentPresheaf_of_powerSections U F f hff
    (powerSectionsSliceAssociatedModuleIso S F U
      ((overAffineAlgSpec U).obj (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))))
      (isAffine_cechNerveTerminalFrom_overAffineAlgSpec U
        (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)))) p

/-! ### The standard covering -/

/-- If the one-member covering by the disjoint union of a standard `τ`-covering has vanishing
positive-degree Čech cohomology with coefficients in `Fᵃ`, then so does the covering itself. -/
public theorem isZero_cechCohomology_succ_quasiCoherentPresheaf_of_singleton
    (τ : CoveringTopology) (F : S.Modules) [F.IsQuasicoherent] (𝒱 : PreZeroHypercover.{u} U)
    (h : IsStandardCovering τ (fun i ↦ (𝒱.X i).left) (fun i ↦ (𝒱.f i).left))
    (hone : letI : Finite 𝒱.I₀ := h.finite_index
      ∀ q : ℕ, IsZero (cechCohomology (PreZeroHypercover.singleton.{u} (Sigma.desc 𝒱.f))
        (quasiCoherentPresheafFunctor S F) (q + 1)))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology 𝒱 (quasiCoherentPresheafFunctor S F) p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  have : Finite 𝒱.I₀ := h.finite_index
  exact IsStandardCovering.isZero_cechCohomology_of_isZero_singleton_bigSite τ S 𝒱 h
    (quasiCoherentPresheafFunctor S F) (isSheaf_over_quasiCoherentPresheafFunctor τ S F) (q + 1)
    (hone q)

/-- Čech vanishing in positive degrees for a standard `τ`-covering of an affine object of
`Over S`, with the presheaf `Fᵃ` of [Stacks, Tag 03DS] as coefficients, for each of the five
topologies. -/
@[stacks 03FJ "the `Cech^p = 0 for p >= 1` clause, for an arbitrary standard covering; \
unconditional -- hcoeff, harrow and hcolim are all three discharged"]
public theorem isZero_cechCohomology_succ_quasiCoherentPresheaf (τ : CoveringTopology)
    (F : S.Modules) [F.IsQuasicoherent] (𝒱 : PreZeroHypercover.{u} U)
    (h : IsStandardCovering τ (fun i ↦ (𝒱.X i).left) (fun i ↦ (𝒱.f i).left))
    (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology 𝒱 (quasiCoherentPresheafFunctor S F) p) := by
  have : Finite 𝒱.I₀ := h.finite_index
  have : IsAffine (∐ 𝒱.X).left := h.isAffine_left_sigmaObj τ S 𝒱
  exact isZero_cechCohomology_succ_quasiCoherentPresheaf_of_singleton U τ F 𝒱 h
    (isZero_cechCohomology_singleton_succ_quasiCoherentPresheaf U F (Sigma.desc 𝒱.f)
      (h.faithfullyFlat_left_sigmaDesc τ S 𝒱)) p hp

end AlgebraicGeometry

end
