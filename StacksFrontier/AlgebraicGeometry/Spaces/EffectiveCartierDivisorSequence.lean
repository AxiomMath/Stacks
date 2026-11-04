module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionTensorPushforwardIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The exact sequence of an effective Cartier divisor on a closed subspace

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces, let `D ⊆ Z` be an effective Cartier
divisor with inclusion `ι : D ⟶ Z`, and let `L` be an invertible `𝒪_X`-module with
`i^*L ≅ 𝒪_Z(D)`.  This file builds the short exact sequence of `𝒪_X`-modules

`0 ⟶ i_*𝒪_Z ⊗ L^{⊗ -1} ⟶ i_*𝒪_Z ⊗ L^{⊗ 0} ⟶ (ι ≫ i)_*𝒪_D ⟶ 0`

which is the sequence `0 ⟶ L^{⊗ -1} ⟶ 𝒪 ⟶ 𝒪_D ⟶ 0` of the proof of Stacks 0EDK, read on `X`,
and proves that `D` has dimension at most `d` when `Z` has dimension `d + 1`.

## Main definitions

* `tensorStructureSheafPushforwardIso`: the projection formula `i_*𝒪_Z ⊗ N ≅ i_*(i^*N)` along a
  closed immersion, the case `𝓖 = 𝒪_Z` of Stacks 04G0.
* `modulePullbackInvertibleTensorPowerNegOneIso`: `i^*(L^{⊗ -1}) ≅ 𝓘_D` when `i^*L ≅ 𝒪_Z(D)`.
* `effectiveCartierDivisorShortComplex`: the sequence displayed above.

## Main results

* `effectiveCartierDivisorShortComplex_shortExact`: it is short exact.
* `twistedModule_cons`: a twist by `L₁, …, L_{d+1}` is the twist by `L₂, …, L_{d+1}` of the first
  twisting step.
* `dimension_le_of_isEffectiveCartierDivisor`: an effective Cartier divisor of an algebraic space
  of dimension `d + 1` has dimension at most `d`.

## Implementation notes

The sequence is the direct image along `i` of the defining sequence
`0 ⟶ 𝓘_D ⟶ 𝒪_Z ⟶ ι_*𝒪_D ⟶ 0` of `D`
(`AlgebraicGeometry.Space.definingIdealShortComplex_shortExact`). Its first term is identified
with `i_*𝒪_Z ⊗ L^{⊗ -1}` by the projection formula and by `i^*(L^{⊗ -1}) ≅ 𝓘_D`, and its third
term with the direct image along the composite by the composition comparison of Stacks 03LU,
`AlgebraicGeometry.Space.modulePushforwardPushforwardStructureSheafIso`.

## References

* [Stacks Project, Tag 0EDK](https://stacks.math.columbia.edu/tag/0EDK)
* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 083T](https://stacks.math.columbia.edu/tag/083T)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space

section Aux

variable {C : Type*} [Category* C]

private theorem comp_comp_inv_comp_hom_comp_eq_zero [HasZeroMorphisms C] {P Q R T U V : C}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : T ≅ R) (d : R ⟶ U) (f : U ⟶ V) (h : b ≫ d = 0) :
    (a ≫ b ≫ c.inv) ≫ c.hom ≫ d ≫ f = 0 := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% h, zero_comp, comp_zero]

private theorem symm_hom_comp_hom_comp_comp_inv {P Q R T : C} (a : P ≅ Q) (b : Q ⟶ R)
    (c : T ≅ R) : a.symm.hom ≫ a.hom ≫ b ≫ c.inv = b ≫ c.symm.hom := by
  simp

private theorem symm_hom_comp_hom_comp_comp_hom {P Q R T : C} (a : P ≅ Q) (b : Q ⟶ R)
    (c : R ≅ T) : a.symm.hom ≫ a.hom ≫ b ≫ c.hom = b ≫ c.hom := by
  simp

end Aux

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Z : AlgebraicSpaces B S hS}

/-- **The projection formula for the structure sheaf of a closed subspace.**  For a closed
immersion `i : Z ⟶ X` and an `𝒪_X`-module `N`, `i_*𝒪_Z ⊗ N ≅ i_*(i^*N)`.  This is Stacks 04G0
(`AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isClosedImmersion`) at `𝓖 = 𝒪_Z`, with
the two factors interchanged and `i^*N ⊗ 𝒪_Z` identified with `i^*N`. -/
def tensorStructureSheafPushforwardIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
        (structureSheafPushforward B S hS i)).obj N ≅
      (modulePushforward B S hS i).obj ((modulePullback B S hS i).obj N) :=
  @Stacks.SheafOfModules.Invertible.tensorProductBraiding.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ _ _ ≪≫
    @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ _ _ _ _ (Iso.refl N)
      ((modulePushforwardIso B S hS i).app
        (SheafOfModules.unit (structureRingSheaf B S hS Z))).symm ≪≫
    @asIso _ _ _ _ (tensorPushforwardMap B S hS i (structureSharpCommRing B S hS i) N
      (SheafOfModules.unit (structureRingSheaf B S hS Z)))
      (isIso_tensorPushforwardMap_of_isClosedImmersion B S hS i hi
        (structureSharpCommRing B S hS i) N
        (SheafOfModules.unit (structureRingSheaf B S hS Z))) ≪≫
    (modulePushforwardIso B S hS i).app _ ≪≫
    (modulePushforward B S hS i).mapIso
      (@Stacks.SheafOfModules.Invertible.tensorProductRightUnitor.{u, u + 1, u}
        (smallEtaleRingedSite B S hS Z.1 Z.2).C _ (smallEtaleRingedSite B S hS Z.1 Z.2).J
        (structurePresheaf B S hS Z.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O).property
        _ _ ((modulePullback B S hS i).obj N))

section Divisor

open Stacks.SheafOfModules.Invertible

/-- **The inverse image of `L^{⊗ -1}` is the ideal sheaf of `D`.**  If `i^*L ≅ 𝒪_Z(D)` for an
effective Cartier divisor `D ⊆ Z`, then `i^*(L^{⊗ -1}) ≅ 𝓘_D`. -/
def modulePullbackInvertibleTensorPowerNegOneIso (i : Z ⟶ X) (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (Dv : ClosedSubspaces B S hS Z.1) (hDv : IsEffectiveCartierDivisor B S hS Z Dv)
    (e : (modulePullback B S hS i).obj L ≅ associatedInvertibleSheaf B S hS Z Dv hDv) :
    (modulePullback B S hS i).obj
      (@Stacks.SheafOfModules.Invertible.tensorPower.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) (-1)) ≅
      idealSheafOfModules B S hS Z Dv := by
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Z)
      (structureRingSheaf B S hS Z).property (idealSheafOfModules B S hS Z Dv) := hDv
  haveI := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL
  set O := structureCommRings B S hS Z
  set hO := (structureRingSheaf B S hS Z).property
  set G := idealSheafOfModules B S hS Z Dv
  set M := associatedInvertibleSheaf B S hS Z Dv hDv
  set Linv := (@Stacks.SheafOfModules.Invertible.tensorPower.{u, u + 1, u}
    (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
    (structurePresheaf B S hS X.1)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) (-1)) with hLinv
  set N := (modulePullback B S hS i).obj Linv
  have eM : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj M).obj G) ≅
      SheafOfModules.unit (structureRingSheaf B S hS Z) :=
    tensorPowerSuccIso O hO G (-1)
  have eL : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS X.1 X.2).O).obj
        Linv).obj L) ≅
      SheafOfModules.unit (structureRingSheaf B S hS X) :=
    @tensorPowerSuccIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
      _ _ L (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) (-1)
  have eN : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj N).obj M) ≅
      SheafOfModules.unit (structureRingSheaf B S hS Z) :=
    tensorProductIso O hO (Iso.refl N) e.symm ≪≫
      ((Stacks.SheafOfModules.pullbackTensorIso (smallEtaleRingedToposModulesHom B S hS i)).app
        (Linv, L)).symm ≪≫
      (modulePullback B S hS i).mapIso eL ≪≫ modulePullbackUnitIso B S hS i
  exact (tensorProductRightUnitor O hO N).symm ≪≫ tensorProductIso O hO (Iso.refl N) eM.symm ≪≫
    (tensorProductAssociator O hO N M G).symm ≪≫ tensorProductIso O hO eN (Iso.refl G) ≪≫
    tensorProductLeftUnitor O hO G

/-- The twist `i_*𝒪_Z ⊗ L^{⊗ -1}` is the direct image `i_*𝓘_D` of the ideal sheaf of `D`, when
`i^*L ≅ 𝒪_Z(D)`. -/
def twistStepNegOneStructureSheafPushforwardIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (Dv : ClosedSubspaces B S hS Z.1) (hDv : IsEffectiveCartierDivisor B S hS Z Dv)
    (e : (modulePullback B S hS i).obj L ≅ associatedInvertibleSheaf B S hS Z Dv hDv) :
    twistStep B S hS X.1 X.2 L (-1) (structureSheafPushforward B S hS i) ≅
      (modulePushforward B S hS i).obj (idealSheafOfModules B S hS Z Dv) :=
  tensorStructureSheafPushforwardIso B S hS i hi _ ≪≫
    (modulePushforward B S hS i).mapIso
      (modulePullbackInvertibleTensorPowerNegOneIso B S hS i L Dv hDv e)

/-- The direct image along `i : Z ⟶ X` of the defining sequence `𝓘_D ⟶ 𝒪_Z ⟶ ι_*𝒪_D` of a closed
subspace `D ⊆ Z` is a complex. -/
theorem modulePushforward_map_ι_comp_map_structureProjection (i : Z ⟶ X)
    (Dv : ClosedSubspaces B S hS Z.1) :
    (modulePushforward B S hS i).map (definingIdealSheaf B S hS Z Dv).ι ≫
      (modulePushforward B S hS i).map (structureProjection B S hS Z Dv) = 0 :=
  ((definingIdealShortComplex B S hS Z Dv).map (modulePushforward B S hS i)).zero


/-- The direct image along `i : Z ⟶ X` of `ι_*𝒪_D`, for the inclusion `ι` of a closed subspace
`D ⊆ Z`, is the direct image `(ι ≫ i)_*𝒪_D` along the composite. -/
def modulePushforwardPushforwardStructureSheafIso (i : Z ⟶ X) (Dv : ClosedSubspaces B S hS Z.1) :
    (modulePushforward B S hS i).obj (pushforwardStructureSheaf B S hS Z Dv) ≅
      structureSheafPushforward B S hS (subspaceInclusion B S hS Z Dv ≫ i) :=
  (modulePushforwardCompIso B S hS (subspaceInclusion B S hS Z Dv) i).app
    (SheafOfModules.unit (structureRingSheaf B S hS ⟨Dv.1.toFunctor, Dv.2.1⟩))

/-- The two maps of `AlgebraicGeometry.Space.effectiveCartierDivisorShortComplex` compose to
zero. -/
theorem effectiveCartierDivisorShortComplex_zero (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (Dv : ClosedSubspaces B S hS Z.1) (hDv : IsEffectiveCartierDivisor B S hS Z Dv)
    (e : (modulePullback B S hS i).obj L ≅ associatedInvertibleSheaf B S hS Z Dv hDv) :
    ((twistStepNegOneStructureSheafPushforwardIso B S hS i hi L Dv hDv e).hom ≫
      (modulePushforward B S hS i).map (definingIdealSheaf B S hS Z Dv).ι ≫
      (twistStepZeroIso B S hS X.1 X.2 L (structureSheafPushforward B S hS i)).inv) ≫
    ((twistStepZeroIso B S hS X.1 X.2 L (structureSheafPushforward B S hS i)).hom ≫
      (modulePushforward B S hS i).map (structureProjection B S hS Z Dv) ≫
      (modulePushforwardPushforwardStructureSheafIso B S hS i Dv).hom) = 0 :=
  comp_comp_inv_comp_hom_comp_eq_zero _ _ _ _ _
    (modulePushforward_map_ι_comp_map_structureProjection B S hS i Dv)

/-- **The divisor sequence** `i_*𝒪_Z ⊗ L^{⊗ -1} ⟶ i_*𝒪_Z ⊗ L^{⊗ 0} ⟶ (ι ≫ i)_*𝒪_D` on `X`, for a
closed immersion `i : Z ⟶ X`, an effective Cartier divisor `ι : D ⟶ Z` and an invertible
`𝒪_X`-module `L` with `i^*L ≅ 𝒪_Z(D)`: the direct image along `i` of the defining sequence
`𝓘_D ⟶ 𝒪_Z ⟶ ι_*𝒪_D` of `D`, with its terms identified as in the implementation notes. -/
def effectiveCartierDivisorShortComplex (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (Dv : ClosedSubspaces B S hS Z.1) (hDv : IsEffectiveCartierDivisor B S hS Z Dv)
    (e : (modulePullback B S hS i).obj L ≅ associatedInvertibleSheaf B S hS Z Dv hDv) :
    ShortComplex (Modules.{u, u} B S hS X.1 X.2) :=
  ShortComplex.mk
    ((twistStepNegOneStructureSheafPushforwardIso B S hS i hi L Dv hDv e).hom ≫
      (modulePushforward B S hS i).map (definingIdealSheaf B S hS Z Dv).ι ≫
      (twistStepZeroIso B S hS X.1 X.2 L (structureSheafPushforward B S hS i)).inv)
    ((twistStepZeroIso B S hS X.1 X.2 L (structureSheafPushforward B S hS i)).hom ≫
      (modulePushforward B S hS i).map (structureProjection B S hS Z Dv) ≫
      (modulePushforwardPushforwardStructureSheafIso B S hS i Dv).hom)
    (effectiveCartierDivisorShortComplex_zero B S hS i hi L Dv hDv e)

/-- **The divisor sequence is short exact**:
`0 ⟶ i_*𝒪_Z ⊗ L^{⊗ -1} ⟶ i_*𝒪_Z ⊗ L^{⊗ 0} ⟶ (ι ≫ i)_*𝒪_D ⟶ 0`. -/
theorem effectiveCartierDivisorShortComplex_shortExact (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (Dv : ClosedSubspaces B S hS Z.1) (hDv : IsEffectiveCartierDivisor B S hS Z Dv)
    (e : (modulePullback B S hS i).obj L ≅ associatedInvertibleSheaf B S hS Z Dv hDv) :
    (effectiveCartierDivisorShortComplex B S hS i hi L Dv hDv e).ShortExact := by
  have hex := exactFunctor_modulePushforward_of_isClosedImmersion_viaAlmostCocontinuity B S hS i hi
  rw [exactFunctor_iff] at hex
  obtain ⟨_, _⟩ := hex
  refine ShortComplex.shortExact_of_iso ?_
    ((definingIdealShortComplex_shortExact B S hS Z Dv).map_of_exact (modulePushforward B S hS i))
  exact ShortComplex.isoMk (twistStepNegOneStructureSheafPushforwardIso B S hS i hi L Dv hDv e).symm
    (twistStepZeroIso B S hS X.1 X.2 L (structureSheafPushforward B S hS i)).symm
    (modulePushforwardPushforwardStructureSheafIso B S hS i Dv)
    (symm_hom_comp_hom_comp_comp_inv _ _ _) (symm_hom_comp_hom_comp_comp_hom _ _ _)

/-- **Peeling off the first twist.**  The twist of `M` by `L₁^{⊗ a} ⊗ L₂^{⊗ n₂} ⊗ ⋯` is the twist
of `M ⊗ L₁^{⊗ a}` by the remaining modules. -/
theorem twistedModule_cons {d : ℕ} (M : Modules.{u, u} B S hS X.1 X.2)
    (L : Fin (d + 1) → Modules.{u, u} B S hS X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property
        (L j)]
    (a : ℤ) (n : Fin d → ℤ) :
    twistedModule B S hS X.1 X.2 M L (Fin.cons a n) =
      twistedModule B S hS X.1 X.2 (twistStep B S hS X.1 X.2 (L 0) a M) (fun j => L j.succ) n := by
  rw [twistedModule, List.finRange_succ, List.foldl_cons, List.foldl_map]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rfl

/-- **An effective Cartier divisor of a space of dimension `d + 1` has dimension at most `d`.** -/
theorem dimension_le_of_isEffectiveCartierDivisor (Z : AlgebraicSpaces B S hS)
    (Dv : ClosedSubspaces B S hS Z.1) (hDv : IsEffectiveCartierDivisor B S hS Z Dv) (d : ℕ)
    (hd : dimension B S hS Z.1 Z.2 = d + 1) :
    dimension B S hS Dv.1.toFunctor Dv.2.1 ≤ d := by
  refine iSup_le fun x => ?_
  have hle : dimensionAtPoint B S hS Z.1 Z.2 (pointsMap B S hS Dv.1.toFunctor Dv.1.ι x) ≤
      (d : WithBot ℕ∞) + 1 :=
    hd ▸ le_iSup (dimensionAtPoint B S hS Z.1 Z.2) _
  have hcast : (d : WithBot ℕ∞) + 1 = (((d : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) := by push_cast; rfl
  have htop : (d : WithBot ℕ∞) + 1 < ⊤ :=
    hcast ▸ (WithBot.coe_lt_coe.2 (show (d : ℕ∞) + 1 < ⊤ by simp)).trans_le le_top
  have hlt := lt_of_lt_of_le
    (dimensionAtPoint_lt_of_isEffectiveCartierDivisor B S hS Z Dv hDv x (hle.trans_lt htop)) hle
  generalize dimensionAtPoint B S hS Dv.1.toFunctor Dv.2.1 x = a at hlt ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    rw [hcast, WithBot.coe_lt_coe] at hlt
    exact WithBot.coe_le_coe.2 (Order.le_of_lt_add_one hlt)

end Divisor

end AlgebraicGeometry.Space

end
