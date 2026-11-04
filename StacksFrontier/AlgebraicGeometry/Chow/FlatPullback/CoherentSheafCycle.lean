module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Flat pullback of the cycle of a coherent sheaf

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
locally of finite type over `S` and let `f : X ⟶ Y` be flat of relative dimension `r`. If `F` is
a coherent sheaf on `Y` whose support has delta-dimension at most `k`, then the flat pullback of
its cycle is the cycle of its pullback:

`f^*[F]_k = [f^*F]_{k+r}`.

This is the cycle identity of Stacks 02RE, part (2). The dimension bounds of that tag, which
make both sides well formed, are `Stacks.Chow.schemeDeltaDimension_pullback_le` and
`Stacks.Chow.schemeDeltaDimension_support_pullback_le`.

## Main results

* `Stacks.Chow.sheafMultiplicity_pullback` — the multiplicity of `f^*F` at `x` is the
  multiplicity of `F` at `f x` times the colength of `𝔪_{Y,f x} 𝒪_{X,x}`, which is Stacks 02M1
  applied to the stalks.
* `Stacks.Chow.flatPullback_cycleAssociatedToCoherentSheaf` — **Stacks 02RE, part (2)**, the
  cycle identity `f^*[F]_k = [f^*F]_{k+r}`.

## References

* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The multiplicity of a pullback sheaf -/

/-- The stalk of the pullback of a sheaf of modules has the same length over the local ring
upstairs as the base change of the stalk along the map of local rings. -/
private theorem length_stalk_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) (x : X) :
    let A := Y.presheaf.stalk (f.base x)
    let B := X.presheaf.stalk x
    let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f.base x)
    let N := TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pullback f).obj F).val.presheaf x
    let : Algebra A B := (f.stalkMap x).hom.toAlgebra
    let : Module A M :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) F.val (f.base x)
    let : Module B N :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) ((Scheme.Modules.pullback f).obj F).val x
    Module.length B N = Module.length B (TensorProduct A B M) := by
  let A := Y.presheaf.stalk (f.base x)
  let B := X.presheaf.stalk x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f.base x)
  let P' : PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) :=
    ((RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom).obj F).val
  let N := TopCat.Presheaf.stalk P'.presheaf x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) F.val (f.base x)
  let : Module B N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) ((Scheme.Modules.pullback f).obj F).val x
  obtain ⟨e, _⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    f.toLRSHom.toShHom F x
  exact e.length_eq

/-- **Stacks 02M1 on the stalks.** For `f` flat the length of the stalk of `f^*F` over the local
ring upstairs is the length of the stalk of `F` downstairs times the colength of the extended
maximal ideal. -/
private theorem length_stalk_pullback_eq_mul {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (F : Y.Modules) (x : X) :
    let A := Y.presheaf.stalk (f.base x)
    let B := X.presheaf.stalk x
    let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f.base x)
    let N := TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pullback f).obj F).val.presheaf x
    let : Algebra A B := (f.stalkMap x).hom.toAlgebra
    let : Module A M :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) F.val (f.base x)
    let : Module B N :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) ((Scheme.Modules.pullback f).obj F).val x
    Module.length B N =
      Module.length A M * Module.length B (B ⧸ extendedMaximalIdeal A B) := by
  let A := Y.presheaf.stalk (f.base x)
  let B := X.presheaf.stalk x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f.base x)
  let N := TopCat.Presheaf.stalk (C := Ab.{u})
    ((Scheme.Modules.pullback f).obj F).val.presheaf x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap A B) :=
    LocallyRingedSpace.isLocalHomStalkMap f.toLRSHom x
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) F.val (f.base x)
  let : Module B N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) ((Scheme.Modules.pullback f).obj F).val x
  let : Module.Flat A B := Flat.stalkMap f x
  calc
    Module.length B N = Module.length B (TensorProduct A B M) :=
      length_stalk_pullback f F x
    _ = Module.length A M * Module.length B (B ⧸ extendedMaximalIdeal A B) :=
      (length_baseChange_eq_length_mul_length_quotient A B M).symm

/-- **Stacks 02M1 for sheaf multiplicities.** The multiplicity of the pullback of a sheaf of
modules along a flat morphism at a point `x` is the multiplicity of the sheaf at `f x` times the
colength in `𝒪_{X, x}` of the ideal generated by the maximal ideal of `𝒪_{Y, f x}`. -/
theorem sheafMultiplicity_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (F : Y.Modules)
    (x : X) :
    sheafMultiplicity ((Scheme.Modules.pullback f).obj F) x =
      sheafMultiplicity F (f.base x) *
        ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
          Ideal.map (f.stalkMap x).hom
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))))).toNat : ℤ) := by
  let A := Y.presheaf.stalk (f.base x)
  let B := X.presheaf.stalk x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (f.base x)
  let N := TopCat.Presheaf.stalk (C := Ab.{u})
    ((Scheme.Modules.pullback f).obj F).val.presheaf x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) F.val (f.base x)
  let : Module B N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) ((Scheme.Modules.pullback f).obj F).val x
  have hlen := length_stalk_pullback_eq_mul f F x
  change Module.length B N =
    Module.length A M * Module.length B (B ⧸ extendedMaximalIdeal A B) at hlen
  show ((Module.length B N).toNat : ℤ) =
    ((Module.length A M).toNat : ℤ) *
      ((Module.length B (B ⧸ extendedMaximalIdeal A B)).toNat : ℤ)
  rw [hlen, ENat.toNat_mul]
  norm_cast

/-! ### The cycle identity of Stacks 02RE -/

/-- For `f : X ⟶ Y` flat of relative dimension `r` between schemes locally of finite type over
the base of chapter 42, and `F` a coherent sheaf on `Y` whose support has delta-dimension at most
`k`, the flat pullback of the cycle of `F` is the cycle of the pullback of `F`:

`f^*[F]_k = [f^*F]_{k+r}`. -/
@[stacks 02RE "part (2): cycle identity"]
theorem flatPullback_cycleAssociatedToCoherentSheaf (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sY = sX) (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (F : Y.Modules) [hF : F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sY) ≤ (k : EInt)) :
    flatPullback C sX sY f hbase r hf k (cycleAssociatedToCoherentSheaf C sY F k hFk) =
      @cycleAssociatedToCoherentSheaf X C sX inferInstance
        ((Scheme.Modules.pullback f).obj F)
        (@AlgebraicGeometry.isCoherent_pullback X Y
          (LocallyOfFiniteType.isLocallyNoetherian sX) f F hF)
        (k + (r : ℤ))
        (schemeDeltaDimension_support_pullback_le C sX sY f hbase r hf F k hFk) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let hFp : ((Scheme.Modules.pullback f).obj F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback f F
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  have hFpk : schemeDeltaDimension C
      ((reducedSupport ((Scheme.Modules.pullback f).obj F)).subschemeι ≫ sX) ≤
      ((k + (r : ℤ) : ℤ) : EInt) :=
    schemeDeltaDimension_support_pullback_le C sX sY f hbase r hf F k hFk
  have hsupp : SheafOfModules.supp ((Scheme.Modules.pullback f).obj F) =
      f.base ⁻¹' SheafOfModules.supp F := Stacks.Modules.supp_pullback f F
  suffices hmain : flatPullback C sX sY f hbase r hf k
      (cycleAssociatedToCoherentSheaf C sY F k hFk) =
      cycleAssociatedToCoherentSheaf C sX ((Scheme.Modules.pullback f).obj F) (k + (r : ℤ))
        hFpk by exact hmain
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [flatPullback_apply]
  by_cases hrelX : relativeDimension C.dimensionFunction sX x = k + (r : ℤ)
  · by_cases hx : x ∈ SheafOfModules.supp ((Scheme.Modules.pullback f).obj F)
    · have hfx : f.base x ∈ SheafOfModules.supp F := by
        rwa [hsupp] at hx
      have hleY : relativeDimension C.dimensionFunction sY (f.base x) ≤ k :=
        relativeDimension_le_of_mem_supp C sY F hFk hfx
      have htr : Cardinal.toNat (residueTrdeg f x) ≤ r :=
        toNat_residueTrdeg_le_of_relativeDimension f r hf x
      have hadd := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f x
      rw [hbase] at hadd
      have hrelY : relativeDimension C.dimensionFunction sY (f.base x) = k := by omega
      have hdim' : relativeDimension C.dimensionFunction sX x =
          relativeDimension C.dimensionFunction sY (f.base x) + (r : ℤ) := by omega
      have hex := exists_genericPoints_comap_integralComponentAt C sX sY f hbase r hf x hdim'
      rw [flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sX f (k + (r : ℤ)) x
          hex hrelX,
        cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C sY F k hFk hrelY,
        cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C sX
          ((Scheme.Modules.pullback f).obj F) (k + (r : ℤ)) hFpk hrelX]
      exact (sheafMultiplicity_pullback f F x).symm
    · have hfx : f.base x ∉ SheafOfModules.supp F := by
        rwa [hsupp] at hx
      rw [cycleAssociatedToCoherentSheaf_apply C sY F k hFk,
        cycleAssociatedToCoherentSheaf_apply C sX ((Scheme.Modules.pullback f).obj F)
          (k + (r : ℤ)) hFpk]
      simp [hfx, hx]
  · have hw : flatPullbackWeight C sX f (k + (r : ℤ)) x = 0 := by
      unfold flatPullbackWeight closedSubschemeCycleCoeff
      split
      · rename_i h
        exact absurd (Classical.choose_spec h).2 hrelX
      · rfl
    rw [hw, mul_zero]
    exact (cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C sX
      ((Scheme.Modules.pullback f).obj F) (k + (r : ℤ)) hFpk hrelX).symm

end Stacks.Chow

end
