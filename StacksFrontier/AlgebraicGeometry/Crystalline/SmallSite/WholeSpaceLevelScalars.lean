module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelReductionFaithful
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemLevelRings

/-!
# Whole-space level scalars and the comparison datum at `𝒪_{X/S}`

Let `X` and `S` be affine with `p` nilpotent on `Γ(X, 𝒪_X)`, and fix a presentation. This file
constructs the level scalars whose system of levels is the degree-`n` member `e ↦ T(n)_e` of
`wholeSpaceSystem`, with the `p`-adically completed divided power envelope `D(n)` identified with
`lim_e Γ(T(n)_e, 𝒪)` by `envelopeLevelRingLimitEquiv`. In degree zero a level reduction datum
over these scalars is a reduction datum.

For an arbitrary system of levels it also identifies the module `lim_e Γ(T_e, 𝒪_{X/S})` with `D`
and transports `Crystalline.structureComparison` along this identification, giving a first-order
comparison datum at `𝒪_{X/S}` whose connection is the divided power derivation.

Unless stated otherwise, declarations are in `Crystalline.GlobalCrystallineSituation.SmallSite`.

## Main definitions

* `Crystalline.FirstOrderComparison.ofLinearEquiv`: a first-order comparison datum transported
  along a `D`-linear equivalence of the module.
* `wholeSpaceLevelScalars`: the level scalars at the degree-`n` member of `wholeSpaceSystem`.
* `LevelReduction07JG.toReduction07JGWholeSpace`: a level reduction datum over
  `wholeSpaceLevelScalars hp 0` as a reduction datum.
* `levelSectionsUnitRingLimitEquiv`: the limit of the modules of sections of `𝒪_{X/S}` over a
  system of levels is the limit of their section rings.
* `LevelScalars07JG.sectionsUnitAddEquiv`, `LevelScalars07JG.sectionsUnitEquiv`: the module
  `lim_e Γ(T_e, 𝒪_{X/S})` is `D`, additively and `D`-linearly.
* `LevelScalars07JG.comparisonUnit`: the first-order comparison datum at `𝒪_{X/S}`.

## Main results

* `Crystalline.lTensor_smul_firstOrderExtension`: a `D`-linear map of the module induces a
  `D ⊕ Ω`-linear map of the base changes.
* `Crystalline.FirstOrderComparison.ofLinearEquiv_connection`: the connection of the transported
  datum is the original connection carried across.
* `levelSectionsUnitRingLimitEquiv_smul`: the limit of the section rings acts on the limit of the
  sections of `𝒪_{X/S}` by multiplication.
* `LevelScalars07JG.comparisonUnit_connection`: the connection of the datum at `𝒪_{X/S}` is
  `s ↦ d s ⊗ 1`, read through the identification of the module with `D`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI w

noncomputable section

namespace Crystalline

/-! ### Transporting a first-order comparison datum along a linear equivalence -/

section Transport

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega}
  {M : Type w} [AddCommGroup M] [Module (D : Type u) M]
  {N : Type w} [AddCommGroup N] [Module (D : Type u) N]

/-- A `D`-linear map of the module induces a `D ⊕ Ω`-linear map of the base changes: the action
of `D ⊕ Ω` is on the left factor and the map is on the right one. -/
theorem lTensor_smul_firstOrderExtension (phi : M →ₗ[(D : Type u)] N)
    (b : firstOrderExtension D Omega) (z : firstOrderExtension D Omega ⊗[D] M) :
    LinearMap.lTensor (firstOrderExtension D Omega) phi (b • z) =
      b • LinearMap.lTensor (firstOrderExtension D Omega) phi z := by
  induction z using TensorProduct.inductionOn with
  | tmul a m => rw [TensorProduct.smul_tmul', LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, _root_.map_add, _root_.map_add, smul_add, hx, hy]

/-- The transport of a first-order comparison datum along a `D`-linear equivalence `e : M ≃ N`:
its comparison map sends `n` to the base change of `e` applied to the comparison map of `c` at
`e.symm n`. -/
def FirstOrderComparison.ofLinearEquiv (e : M ≃ₗ[(D : Type u)] N)
    (c : FirstOrderComparison A D g Omega d M) : FirstOrderComparison A D g Omega d N where
  toFun n :=
    LinearMap.lTensor (firstOrderExtension D Omega) (e : M →ₗ[(D : Type u)] N) (c (e.symm n))
  map_add' m n := by
    rw [_root_.map_add e.symm, c.map_add', _root_.map_add]
  reduction' n := by
    rw [firstOrderReduction_lTensor, c.reduction', LinearEquiv.coe_coe, e.apply_symm_apply]
  semilinear' f n := by
    rw [_root_.map_smul e.symm, c.semilinear', lTensor_smul_firstOrderExtension]

/-- The connection of `FirstOrderComparison.ofLinearEquiv e c` at `n` is the base change of `e`
applied to the connection of `c` at `e.symm n`. -/
theorem FirstOrderComparison.ofLinearEquiv_connection (e : M ≃ₗ[(D : Type u)] N)
    (c : FirstOrderComparison A D g Omega d M) (n : N) :
    (FirstOrderComparison.ofLinearEquiv e c).connection n =
      LinearMap.lTensor Omega (e : M →ₗ[(D : Type u)] N) (c.connection (e.symm n)) :=
  firstOrderDifferentialPart_lTensor D Omega M N (e : M →ₗ[(D : Type u)] N) (c (e.symm n))

end Transport

namespace GlobalCrystallineSituation.SmallSite

/-! ### The level scalars at the whole-space system -/

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]

section Presentation

variable [WholeSpacePresentation S hp]

/-- The level scalars whose system of levels is the degree-`n` member `e ↦ (X, T(n)_e, δ(n))` of
`wholeSpaceSystem`, with the `p`-adically completed divided power envelope `D(n)` of the
tautological presentation identified with `lim_e Γ(T(n)_e, 𝒪)` by
`envelopeLevelRingLimitEquiv`. -/
def wholeSpaceLevelScalars (n : ℕ) :
    LevelScalars07JG S (wholeSpaceSystemEnvelope hp n).ring where
  levelSystem := (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n))
  ringEquiv := envelopeLevelRingLimitEquiv hp n

/-- The system of levels of `wholeSpaceLevelScalars hp n` is the degree-`n` member of
`wholeSpaceSystem S hp`. -/
@[simp] theorem wholeSpaceLevelScalars_levelSystem (n : ℕ) :
    (wholeSpaceLevelScalars hp n).levelSystem =
      (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk n)) :=
  rfl

/-- The ring identification of `wholeSpaceLevelScalars hp n` is
`envelopeLevelRingLimitEquiv hp n`. -/
@[simp] theorem wholeSpaceLevelScalars_ringEquiv (n : ℕ) :
    (wholeSpaceLevelScalars hp n).ringEquiv = envelopeLevelRingLimitEquiv hp n :=
  rfl

end Presentation

/-! ### Reduction data in degree zero -/

section Reduction

variable {A : Type u} [CommRing A] {g : A →+* (wholeSpaceSystemEnvelope hp 0).ring}
  {Omega : Type u} [AddCommGroup Omega]
  [Module (wholeSpaceSystemEnvelope hp 0).ring Omega]
  [Module ((wholeSpaceSystemEnvelope hp 0).ring)ᵐᵒᵖ Omega]
  [IsCentralScalar (wholeSpaceSystemEnvelope hp 0).ring Omega]
  {d : DividedPowerDerivation A (wholeSpaceSystemEnvelope hp 0).ring g Omega} {p : ℕ}
  {ι : Type uI} {dx : ι → Omega}

/-- A level reduction datum over `wholeSpaceLevelScalars hp 0` is a reduction datum: its system
of levels is the degree-zero member of `wholeSpaceSystem`. -/
def LevelReduction07JG.toReduction07JGWholeSpace
    (R : LevelReduction07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d p dx
      (wholeSpaceLevelScalars hp 0)) :
    Reduction07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d p dx hp :=
  R.toReduction07JG rfl

end Reduction

/-! ### The datum at the coefficient sheaf `𝒪_{X/S}` -/

section Unit

omit [IsAffine S.X] [IsAffine S.S.scheme]

/-- The limit of the modules of sections of `quasiCoherentCrystalUnit S` over a system of levels
`T` is the limit of the section rings of `T`; the two are the same subtype of the same product,
and the identification is the identity. -/
def levelSectionsUnitRingLimitEquiv (T : ℕ ⥤ CrystallineThickening S) :
    ↥(levelSectionsLimit S T (quasiCoherentCrystalUnit S)) ≃+ ↥(levelRingLimit S T) :=
  AddEquiv.refl _

/-- The limit of the section rings acts on the limit of the sections of the structure sheaf by
its own multiplication: `levelSectionsUnitRingLimitEquiv T (a • s)` is
`a * levelSectionsUnitRingLimitEquiv T s`. -/
theorem levelSectionsUnitRingLimitEquiv_smul (T : ℕ ⥤ CrystallineThickening S)
    (a : ↑(levelRingLimit S T))
    (s : ↑(levelSectionsLimit S T (quasiCoherentCrystalUnit S))) :
    levelSectionsUnitRingLimitEquiv T (a • s) = a * levelSectionsUnitRingLimitEquiv T s :=
  rfl

variable {D : DividedPowerRing.{u}} (L : LevelScalars07JG S D)

/-- The module `M = lim_e Γ(T_e, ℱ)` at `ℱ = 𝒪_{X/S}` is additively `D`: it is the limit of the
section rings of the levels, which `ringEquiv` identifies with `D`. -/
def LevelScalars07JG.sectionsUnitAddEquiv :
    L.sections (quasiCoherentCrystalUnit S) ≃+ (D : Type u) :=
  (L.sectionsEquiv (quasiCoherentCrystalUnit S)).trans
    ((levelSectionsUnitRingLimitEquiv L.levelSystem).trans L.ringEquiv.symm.toAddEquiv)

/-- Applying `ringEquiv` to `L.sectionsUnitAddEquiv s` gives the compatible family of sections
underlying `s`. -/
theorem LevelScalars07JG.ringEquiv_sectionsUnitAddEquiv
    (s : L.sections (quasiCoherentCrystalUnit S)) :
    L.ringEquiv (L.sectionsUnitAddEquiv s) =
      levelSectionsUnitRingLimitEquiv L.levelSystem
        (L.sectionsEquiv (quasiCoherentCrystalUnit S) s) :=
  L.ringEquiv.apply_symm_apply _

/-- The module `M = lim_e Γ(T_e, ℱ)` at `ℱ = 𝒪_{X/S}` is `D`, as `D`-modules. -/
def LevelScalars07JG.sectionsUnitEquiv :
    L.sections (quasiCoherentCrystalUnit S) ≃ₗ[(D : Type u)] (D : Type u) :=
  { L.sectionsUnitAddEquiv with
    map_smul' := fun a s ↦ L.ringEquiv.injective (by
      change L.ringEquiv (L.sectionsUnitAddEquiv (a • s)) =
        L.ringEquiv (a * L.sectionsUnitAddEquiv s)
      rw [map_mul, L.ringEquiv_sectionsUnitAddEquiv, L.ringEquiv_sectionsUnitAddEquiv]
      exact levelSectionsUnitRingLimitEquiv_smul L.levelSystem (L.ringEquiv a)
        (L.sectionsEquiv (quasiCoherentCrystalUnit S) s)) }

/-- The linear equivalence `L.sectionsUnitEquiv` agrees with `L.sectionsUnitAddEquiv` on
elements. -/
@[simp] theorem LevelScalars07JG.sectionsUnitEquiv_apply
    (s : L.sections (quasiCoherentCrystalUnit S)) :
    L.sectionsUnitEquiv s = L.sectionsUnitAddEquiv s :=
  rfl

variable {A : Type u} [CommRing A] {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  (d : DividedPowerDerivation A D g Omega)

/-- The first-order comparison datum on the module of sections at `𝒪_{X/S}`:
`Crystalline.structureComparison` transported along `L.sectionsUnitEquiv.symm`. -/
def LevelScalars07JG.comparisonUnit :
    FirstOrderComparison A D g Omega d (L.sections (quasiCoherentCrystalUnit S)) :=
  FirstOrderComparison.ofLinearEquiv L.sectionsUnitEquiv.symm (structureComparison A D g Omega d)

/-- The connection of `L.comparisonUnit d` is the divided power derivation: read through the
identification of the module with `D`, it sends `s` to `d s ⊗ 1`. -/
theorem LevelScalars07JG.comparisonUnit_connection
    (s : L.sections (quasiCoherentCrystalUnit S)) :
    (L.comparisonUnit d).connection s =
      LinearMap.lTensor Omega (L.sectionsUnitEquiv.symm : (D : Type u) →ₗ[(D : Type u)]
          L.sections (quasiCoherentCrystalUnit S))
        (d (L.sectionsUnitEquiv s) ⊗ₜ[D] (1 : (D : Type u))) := by
  rw [LevelScalars07JG.comparisonUnit, FirstOrderComparison.ofLinearEquiv_connection,
    structureComparison_connection]
  rfl

end Unit

end GlobalCrystallineSituation.SmallSite

end Crystalline

end

end
