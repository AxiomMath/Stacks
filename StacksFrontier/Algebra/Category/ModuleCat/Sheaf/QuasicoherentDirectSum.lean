module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.BiproductQuasicoherent
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Direct sums of quasi-coherent modules on a ringed space

The direct sum of two quasi-coherent `𝒪_X`-modules on a ringed space is quasi-coherent. This is
the ringed-space form of `AlgebraicGeometry.directSum_isQuasicoherent`, which holds for any sheaf
of rings on a topological space.

## Main results

* `directSum_isQuasicoherent`: Stacks Tag 01BF on a ringed space.

## References

* [Stacks Project, Tag 01BF](https://stacks.math.columbia.edu/tag/01BF)
-/

open CategoryTheory Limits

/-- A sheaf of `O_X`-modules on a ringed space is quasi-coherent (Stacks Tag 01BE)
when `X` is covered by opens `U` on which `M` admits a presentation
`⨁ O_U → ⨁ O_U → M|_U → 0`; this is Mathlib's `SheafOfModules.IsQuasicoherent`. -/
@[ega "0 5.1.3",
  sga "3 VIB 11.8.0" "partial",
  sga "4 Vbis 4.2.0" "partial",
  sga "6 II 2.2.1" "special case"]
abbrev IsQuasicoherentModule {X : AlgebraicGeometry.RingedSpace}
    (M : SheafOfModules (ringCatSheaf X)) : Prop :=
  M.IsQuasicoherent

universe uOver

open SheafOfModules in
/-- (Step 3) Restriction to an open `U` commutes with the binary biproduct of
two sheaves of modules: `(M ⊞ N).over U ≅ (M.over U) ⊞ (N.over U)`.

Restriction is `overFunctor R U = pushforward (𝟙 (R.over U))`, a left adjoint,
hence additive and biproduct-preserving. -/
@[ega "0 4.3.2" "special case"]
noncomputable def biprod_over_iso
    {X : AlgebraicGeometry.RingedSpace.{uOver}}
    (M N : SheafOfModules.{uOver} (ringCatSheaf X))
    (U : (TopologicalSpace.Opens (X : TopCat))) :
    letI : HasFiniteLimits (SheafOfModules.{uOver} ((ringCatSheaf X).over U)) :=
      SheafOfModules.Finite.hasFiniteLimits ((ringCatSheaf X).over U)
    letI : HasBinaryBiproducts (SheafOfModules.{uOver} ((ringCatSheaf X).over U)) :=
      HasBinaryBiproducts.of_hasBinaryProducts
    (M ⊞ N).over U ≅
      Limits.biprod (C := SheafOfModules.{uOver} ((ringCatSheaf X).over U))
        (M.over U) (N.over U) := by
  letI : HasFiniteLimits (SheafOfModules.{uOver} ((ringCatSheaf X).over U)) :=
    SheafOfModules.Finite.hasFiniteLimits ((ringCatSheaf X).over U)
  letI : HasBinaryBiproducts (SheafOfModules.{uOver} ((ringCatSheaf X).over U)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  let F := SheafOfModules.overFunctor.{uOver} (ringCatSheaf X) U
  letI : F.IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := ringCatSheaf X) U).isLeftAdjoint
  letI : F.Additive := ⟨by intros; rfl⟩
  have hpc : PreservesColimitsOfSize.{0,0} F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
  have : PreservesColimit (pair M N) F := inferInstance
  have : PreservesBinaryBiproduct M N F :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct F
  exact F.mapBiprod M N

/-- Stacks Tag 01BF (Lemma 17.10.2): the direct sum of two quasi-coherent
`O_X`-modules on a ringed space is quasi-coherent. -/
@[stacks 01BF, ega "0 5.1.3" "direct sum remark", ega "I 4.1.1" "direct sums (binary)"]
theorem directSum_isQuasicoherent
    (X : AlgebraicGeometry.RingedSpace)
    (M N : SheafOfModules (ringCatSheaf X))
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (M ⊞ N).IsQuasicoherent :=
  AlgebraicGeometry.directSum_isQuasicoherent _ M N

end
