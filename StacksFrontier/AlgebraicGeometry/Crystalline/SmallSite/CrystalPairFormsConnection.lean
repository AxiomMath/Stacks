module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamSquareZeroLevelwise
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedFormsUnitZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPoincareCurvature
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairEquivalence07JH
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFormsEquiv
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceCoordinates

/-!
# The connection of the pair of a crystal, in the completed forms of `D`

The pair `(M, ∇)` of [Stacks, Lemma 60.17.3, Tag 07JG] attached to a crystal `ℱ`
(`...SmallSite.crystalPair`) has its connection with values in `Ω_D`
(`...SmallSite.pairForms`), and the completed de Rham complex of
[Stacks, Proposition 60.21.3, Tag 07LG] is built from the completed forms
`Ω̂^*_D = (...SmallSite.wholeSpaceDPAlgebra hp).forms S.p · 0`.  The two agree in degree one by
`...SmallSite.crystalPairFormsEquiv`, which carries `d : D → Ω_D` to the universal differential.
This module reads the connection through that identification and proves what the de Rham complex
needs of it.

## Main definitions

* `Crystalline.CompletedConnection.mapForms` — a completed connection pushed along a linear map
  of the modules of forms compatible with the differentials.
* `...SmallSite.crystalPairFormsConnection` — **the connection `∇ : M → M ⊗̂_D Ω̂¹_D`**.

## Main results

* `...SmallSite.crystalPairFormsConnection_eq` — it is the connection of the pair, composed with
  the identification of the forms.
* `...SmallSite.isCoordinateExpansion_crystalPairFormsConnection` — **its coordinate expansion**
  `∇ m = ∑_c (-θ_c m) ⊗ d x_c`, with `θ_c` the first-order Taylor operators of the crystal.
* `...SmallSite.isSquareZero_crystalPairFormsConnection` — **the de Rham differentials of
  `M ⊗^∧_D Ω̂^*_D` compose to zero.**
* `...SmallSite.hasIntegrableConnection_crystalPairFormsConnection` — **the connection is
  integrable** in the sense of [Stacks, Remark 60.5.4, Tag 07I0]: its curvature vanishes.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Remark 60.5.4, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u v v' w

/-! ### Changing the module of forms of a completed connection -/

namespace Crystalline.CompletedConnection

variable {p : ℕ} {D : Type u} [CommRing D] {Omega : Type v} [AddCommGroup Omega] [Module D Omega]
  {Omega' : Type v'} [AddCommGroup Omega'] [Module D Omega'] {d : D → Omega} {d' : D → Omega'}
  {M : Type w} [AddCommGroup M] [Module D M]

/-- The map `M ⊗̂_D Ω → M ⊗̂_D Ω'` induced by a linear map `Ω → Ω'`, as a `D`-linear map. -/
noncomputable abbrev completedTensorFormsMap (φ : Omega →ₗ[D] Omega') :
    CompletedTensor p D Omega M →ₗ[D] CompletedTensor p D Omega' M :=
  (AdicCompletion.map (DividedPowers.pAdicIdeal (A := D) p)
    (LinearMap.lTensor M φ)).restrictScalars D

/-- **A completed connection pushed along a linear map of the modules of forms** carrying `d` to
`d'`: the connection `M → M ⊗̂_D Ω → M ⊗̂_D Ω'`. -/
noncomputable def mapForms (nabla : CompletedConnection p D Omega d M) (φ : Omega →ₗ[D] Omega')
    (hφ : ∀ a, φ (d a) = d' a) : CompletedConnection p D Omega' d' M where
  toFun m := completedTensorFormsMap φ (nabla m)
  map_add' m n := by rw [nabla.map_add, _root_.map_add]
  leibniz' a m := by
    rw [nabla.leibniz, _root_.map_add, _root_.map_smul]
    congr 1
    change AdicCompletion.map _ _ (AdicCompletion.of _ _ _) = _
    rw [AdicCompletion.map_of, LinearMap.lTensor_tmul, hφ]

/-- The pushed connection on an element. -/
theorem mapForms_apply (nabla : CompletedConnection p D Omega d M) (φ : Omega →ₗ[D] Omega')
    (hφ : ∀ a, φ (d a) = d' a) (m : M) :
    nabla.mapForms φ hφ m = completedTensorFormsMap φ (nabla m) :=
  rfl

/-- **A coordinate expansion of a connection pushes to a coordinate expansion** of the pushed
connection, along the pushed coordinate forms. -/
theorem _root_.Crystalline.IsCoordinateExpansion.mapForms {ι : Type*} {dx : ι → Omega}
    {theta : ι → (M → M)}
    {nabla : CompletedConnection p D Omega d M} (h : IsCoordinateExpansion p D Omega dx nabla theta)
    (φ : Omega →ₗ[D] Omega') (hφ : ∀ a, φ (d a) = d' a) :
    IsCoordinateExpansion p D Omega' (fun i ↦ φ (dx i)) (nabla.mapForms φ hφ) theta := by
  intro m
  let := completedTensorTopology p D Omega M
  let := completedTensorTopology p D Omega' M
  have hmap := (h m).map (completedTensorFormsMap (M := M) (p := p) φ)
    (continuous_linearMap_adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p)
      (completedTensorFormsMap (M := M) (p := p) φ))
  convert hmap using 1
  · funext i
    simp only [Function.comp_apply, toCompletedTensor, LinearMap.restrictScalars_apply,
      AdicCompletion.map_of, LinearMap.lTensor_tmul]
  · rfl

end Crystalline.CompletedConnection

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AlgebraicGeometry Crystalline Simplicial

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp] (Fc : QuasiCoherentCrystal S)

/-- `M = lim_e Γ(T_e, ℱ)` is a module over the completed ring `D̂(0)` of the cosimplicial degree
zero, which is the ring `D` of the pair; this is the module structure of the degree zero of
`...SmallSite.wholeSpaceCosimplicialModule`. -/
instance crystalPairCompletedModule :
    Module ((wholeSpaceDPAlgebra hp).completedRing S.p 0) (wholeSpaceSections hp Fc ⦋0⦌) :=
  pairSectionsModule hp Fc

/-- The connection of the pair of a crystal with values in the completed one-forms of `D`, over
the ring `...SmallSite.pairRing` of the pair; `...SmallSite.crystalPairFormsConnection` is the same
connection over the completed ring of the cosimplicial degree zero. -/
def crystalPairFormsConnectionAux :
    CompletedConnection S.p (pairRing hp) ((wholeSpaceDPAlgebra hp).forms S.p 1 0)
      ((wholeSpaceDPAlgebra hp).differential S.p 0) (wholeSpaceSections hp Fc ⦋0⦌) :=
  (pairConnection hp Fc).mapForms (crystalPairFormsEquiv hp).toLinearMap
    (crystalPairFormsEquiv_pairDerivation hp)

/-- **The connection of the pair of a crystal, with values in the completed one-forms of `D`**:
the connection `...SmallSite.pairConnection` of [Stacks, Tag 07JG] followed by the identification
`Ω_D ≃ Ω̂¹_D` of `...SmallSite.crystalPairFormsEquiv`, over the completed ring `D̂(0)` of the
cosimplicial degree zero, which is the ring `D` of the pair. -/
def crystalPairFormsConnection :
    CompletedConnection S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
      ((wholeSpaceDPAlgebra hp).forms S.p 1 0) ((wholeSpaceDPAlgebra hp).differential S.p 0)
      (wholeSpaceSections hp Fc ⦋0⦌) :=
  crystalPairFormsConnectionAux hp Fc

/-- The connection in the completed forms is the connection of the pair, composed with the
identification of the forms. -/
theorem crystalPairFormsConnection_eq (m : wholeSpaceSections hp Fc ⦋0⦌) :
    crystalPairFormsConnection hp Fc m =
      CompletedConnection.completedTensorFormsMap (crystalPairFormsEquiv hp).toLinearMap
        (pairConnection hp Fc m) :=
  rfl

/-- The coordinate one-forms `d x_c` of the completed forms of `D`. -/
abbrev crystalPairFormsDx (c : wholeSpaceIndex S hp) :
    (wholeSpaceDPAlgebra hp).forms S.p 1 0 :=
  (wholeSpaceDPAlgebra hp).differential S.p 0
    (AdicCompletion.of (pAdicIdeal (A := (wholeSpaceDPAlgebra hp).carrier 0) S.p)
      ((wholeSpaceDPAlgebra hp).carrier 0) (wsCoordinate hp c))

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- The identification of the forms carries `d x_c` of the pair to `d x_c`. -/
theorem crystalPairFormsEquiv_pairDx (c : wholeSpaceIndex S hp) :
    crystalPairFormsEquiv hp (pairDx hp c) = crystalPairFormsDx hp c :=
  crystalPairFormsEquiv_pairDerivation hp _

/-- **The coordinate expansion of the connection**: `∇ m = ∑_c (-θ_c m) ⊗ d x_c`, the sum
converging `p`-adically, with `θ_c` the first-order Taylor operators of the crystal. -/
theorem isCoordinateExpansion_crystalPairFormsConnection :
    IsCoordinateExpansion S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
      ((wholeSpaceDPAlgebra hp).forms S.p 1 0) (crystalPairFormsDx hp)
      (crystalPairFormsConnection hp Fc)
      (fun c m ↦ -crystalTheta hp Fc (Finsupp.single c 1) m) := by
  have h := (isCoordinateExpansion_pairConnection hp Fc).mapForms
    (crystalPairFormsEquiv hp).toLinearMap (crystalPairFormsEquiv_pairDerivation hp)
  have hdx : (fun c ↦ (crystalPairFormsEquiv hp).toLinearMap (pairDx hp c)) =
      crystalPairFormsDx hp := funext fun c ↦ crystalPairFormsEquiv_pairDx hp c
  rw [hdx] at h
  exact h

/-- At each level only finitely many first-order Taylor operators do not land in `pⁿ M`. -/
theorem finite_crystalTheta_single_notMem (m : wholeSpaceSections hp Fc ⦋0⦌) (n : ℕ) :
    (setOf fun c : (wholeSpaceIndex S hp) ↦ -crystalTheta hp Fc (Finsupp.single c 1) m ∉
      pPowSmul S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
        (wholeSpaceSections hp Fc ⦋0⦌) n).Finite := by
  refine ((finite_crystalTheta_ne_zero hp Fc m n).preimage
    (Finsupp.single_left_injective one_ne_zero).injOn).subset fun c hc ↦ ?_
  intro h0
  apply hc
  have hmem : crystalTheta hp Fc (Finsupp.single c 1) m ∈
      LinearMap.ker (pairComponent hp Fc n) := h0
  rw [ker_pairComponent] at hmem
  have hle : pAdicIdeal (A := (pairRing hp : Type u)) S.p ^
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + n) •
        (⊤ : Submodule (pairRing hp) (wholeSpaceSections hp Fc ⦋0⦌)) ≤
      pPowSmul S.p (pairRing hp) (wholeSpaceSections hp Fc ⦋0⦌) n :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left _ _))
  exact Submodule.neg_mem _ (hle hmem)

/-- **The de Rham differentials of `M ⊗^∧_D Ω̂^*_D` compose to zero.**  The coordinate
expansion is finite at each level, the coordinate one-forms are closed and the Taylor operators
commute. -/
theorem isSquareZero_crystalPairFormsConnection :
    CompletedDeRham.IsSquareZero S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
      (fun a ↦ (wholeSpaceDPAlgebra hp).forms S.p a 0) ((wholeSpaceDPAlgebra hp).wedge S.p 0)
      ((wholeSpaceDPAlgebra hp).deRham S.p 0) (wholeSpaceSections hp Fc ⦋0⦌)
      (crystalPairFormsConnection hp Fc) ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p 0) :=
  CompletedDeRham.isSquareZero_of_commute_of_isLevelwiseCoordinateExpansion _ _ _ _ _ _ _ _
    (crystalPairFormsDx hp) (fun c m ↦ -crystalTheta hp Fc (Finsupp.single c 1) m)
    ((wholeSpaceDPAlgebra hp).isGradedExterior S.p 0)
    (isLevelwiseCoordinateExpansion_of_finite_support _ _ _ _
      (isCoordinateExpansion_crystalPairFormsConnection hp Fc)
      (finite_crystalTheta_single_notMem hp Fc)
      (fun _ c _ hx ↦ map_mem_pPowSmul _ _ _
        (f := fun y ↦ -crystalTheta hp Fc (Finsupp.single c 1) y)
        (fun y z ↦ by rw [map_add, neg_add]) hx))
    (fun _ ↦ deRham_completedFormsDifferential _ _ _ _)
    (fun c d ↦ funext fun m ↦ by
      simp only [Function.comp_apply, map_neg, neg_neg, crystalTheta_crystalTheta, add_comm])

/-- **The connection is integrable** in the sense of [Stacks, Remark 60.5.4, Tag 07I0]: the
composite `M → M ⊗̂_D Ω̂¹_D → M ⊗̂_D Ω̂²_D` vanishes. -/
theorem hasIntegrableConnection_crystalPairFormsConnection :
    CompletedDeRham.HasIntegrableConnection S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
      (fun a ↦ (wholeSpaceDPAlgebra hp).forms S.p a 0) ((wholeSpaceDPAlgebra hp).wedge S.p 0)
      ((wholeSpaceDPAlgebra hp).deRham S.p 0) (wholeSpaceSections hp Fc ⦋0⦌)
      (crystalPairFormsConnection hp Fc) ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p 0) :=
  CompletedDeRham.hasIntegrableConnection_of_isSquareZero _ _ _ _ _ _ _ _
    (completedUnitZeroForm S.p _ ((wholeSpaceDPAlgebra hp).dividedPowers 0))
    (completedDividedPowerDeRham_completedUnitZeroForm S.p _ _)
    (fun η ↦ completedDividedPowerWedge_completedUnitZeroForm S.p _ _ η)
    (isSquareZero_crystalPairFormsConnection hp Fc)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
