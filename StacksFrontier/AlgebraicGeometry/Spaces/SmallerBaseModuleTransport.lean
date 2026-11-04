module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafOverSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# Modules on an algebraic space over a smaller base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site, `Y` an algebraic space over `S` with a morphism
`φ : Y ⟶ W`, and `Y'` the corresponding algebraic space over `W` (Stacks 04SG,
`AlgebraicGeometry.Space.spaceOverSmallerBase`). The equivalence
`AlgebraicGeometry.Space.smallerBaseModulesEquivalence` between the modules on `Y` and on `Y'` is
restriction along an equivalence of ringed sites; this file records that it is compatible with
the module structure the twisted Euler characteristics use: it commutes with tensor products and
integer tensor powers, and preserves invertibility, quasi-coherence and finite type, hence
coherence.

## Main definitions

* `AlgebraicGeometry.Space.smallerBaseModulesTensorIso`: `(M ⊗ N)' ≅ M' ⊗ N'`.
* `AlgebraicGeometry.Space.smallerBaseModulesTensorPowerIso`: `(L^{⊗ n})' ≅ (L')^{⊗ n}` for an
  invertible `L`.

## Main results

* `AlgebraicGeometry.Space.isInvertible_smallerBaseModules`: invertibility is preserved.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallerBaseModules` and
  `AlgebraicGeometry.Space.isFiniteType_smallerBaseModules`: quasi-coherence and finite type are
  preserved.
* `AlgebraicGeometry.Space.isCoherent_smallerBaseModules`: so is coherence, on a locally
  Noetherian space.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) (Y : AlgebraicSpaces B S hS) (φ : Y.1 ⟶ yoneda.obj (Over.mk h))

/-- The continuity of `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalence`, at the spelling
of the topologies as projections of the small étale ringed sites, which instance search does not
unfold. -/
instance smallerBaseSmallEtaleEquivalence_functor_isContinuous_ringedSite :
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).functor.IsContinuous
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).J
      (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  smallerBaseSmallEtaleEquivalence_functor_isContinuous B W S hW hS h Y φ

/-- The continuity of the inverse of
`AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalence`, at the spelling of the topologies as
projections of the small étale ringed sites. -/
instance smallerBaseSmallEtaleEquivalence_inverse_isContinuous_ringedSite :
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).inverse.IsContinuous
      (smallEtaleRingedSite B S hS Y.1 Y.2).J
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).J :=
  smallerBaseSmallEtaleEquivalence_inverse_isContinuous B W S hW hS h Y φ

/-- `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalence_functor_isContinuous` with the
categories spelled through the small étale ringed sites, as the tensor-product and
quasi-coherence API consumes it. -/
instance smallerBaseSmallEtaleEquivalence_functor_isContinuous_ringedSite' :
    @Functor.IsContinuous
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).C
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).category
      (smallEtaleRingedSite B S hS Y.1 Y.2).C (smallEtaleRingedSite B S hS Y.1 Y.2).category
      (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).functor
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).J
      (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  smallerBaseSmallEtaleEquivalence_functor_isContinuous B W S hW hS h Y φ

/-- `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalence_inverse_isContinuous` with the
categories spelled through the small étale ringed sites. -/
instance smallerBaseSmallEtaleEquivalence_inverse_isContinuous_ringedSite' :
    @Functor.IsContinuous
      (smallEtaleRingedSite B S hS Y.1 Y.2).C (smallEtaleRingedSite B S hS Y.1 Y.2).category
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).C
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).category
      (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).inverse
      (smallEtaleRingedSite B S hS Y.1 Y.2).J
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).J :=
  smallerBaseSmallEtaleEquivalence_inverse_isContinuous B W S hW hS h Y φ

/-- The equivalence of small étale sites of `Y'` and `Y` is cocontinuous, its inverse being
continuous. -/
instance smallerBaseSmallEtaleEquivalence_functor_isCocontinuous :
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).functor.IsCocontinuous
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).J
      (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  let adj := (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).toAdjunction
  (adj.isCocontinuous_iff_coverPreserving _ _).2 (CoverPreserving.of_isContinuous _ _ _)

/-- **The module equivalence of Stacks 04SG commutes with tensor products**:
`(M ⊗ N)' ≅ M' ⊗ N'`. -/
def smallerBaseModulesTensorIso (M N : Modules.{u, u} B S hS Y.1 Y.2) :
    (smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
          (spaceOverSmallerBase B W S hW hS h Y φ).2).O).obj
          ((smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj M)).obj
        ((smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj N) :=
  letI : @Functor.IsCocontinuous
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).C
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).category
      (smallEtaleRingedSite B S hS Y.1 Y.2).C (smallEtaleRingedSite B S hS Y.1 Y.2).category
      (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).functor
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).J
      (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
    smallerBaseSmallEtaleEquivalence_functor_isCocontinuous B W S hW hS h Y φ
  Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso
    (J' := (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
      (spaceOverSmallerBase B W S hW hS h Y φ).2).J)
    (smallEtaleRingedSite B S hS Y.1 Y.2).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).property
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ).functor M N

/-- **The module equivalence of Stacks 04SG preserves invertibility**: a tensor inverse `N` of
`L` gives the tensor inverse `N'` of `L'`, the equivalence commuting with tensor products and
carrying the structure sheaf to the structure sheaf. -/
theorem isInvertible_smallerBaseModules (L : Modules.{u, u} B S hS Y.1 Y.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).property
      L] :
    Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
          (spaceOverSmallerBase B W S hW hS h Y φ).2).O)).property
      ((smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj L) := by
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (C := (smallEtaleRingedSite B S hS Y.1 Y.2).C) (J := (smallEtaleRingedSite B S hS Y.1 Y.2).J)
    L).mp hL
  exact (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (C := (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
      (spaceOverSmallerBase B W S hW hS h Y φ).2).C)
    (J := (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
      (spaceOverSmallerBase B W S hW hS h Y φ).2).J)
    (O := structurePresheaf B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1) _).mpr
    ⟨(smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj N,
      ⟨(smallerBaseModulesTensorIso B W S hW hS h Y φ L N).symm ≪≫
        (smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.mapIso e⟩⟩

/-- **The module equivalence of Stacks 04SG commutes with integer tensor powers**:
`(L^{⊗ n})' ≅ (L')^{⊗ n}` for an invertible `L` and `n : ℤ`. -/
def smallerBaseModulesTensorPowerIso (L : Modules.{u, u} B S hS Y.1 Y.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).property
      L] (n : ℤ) :
    letI := isInvertible_smallerBaseModules B W S hW hS h Y φ L
    (smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj
        (invertibleTensorPower B S hS Y.1 Y.2 L n) ≅
      invertibleTensorPower B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2
        ((smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj L) n :=
  letI := isInvertible_smallerBaseModules B W S hW hS h Y φ L
  haveI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible _ _ L
    (hL := hL)
  haveI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_stacksIsInvertible _ _
    ((smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj L)
    (hL := isInvertible_smallerBaseModules B W S hW hS h Y φ L)
  Stacks.SheafOfModules.TensorPower.mapTensorPowerIso _ _ _ _
    (smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor L
    (fun M => smallerBaseModulesTensorIso B W S hW hS h Y φ M L) (Iso.refl _) n

/-- **The module equivalence of Stacks 04SG preserves quasi-coherence** (Stacks 03DM). -/
theorem isQuasicoherentOnSite_smallerBaseModules (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : M.IsQuasicoherentOnSite) :
    ((smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj
      M).IsQuasicoherentOnSite :=
  @Stacks.SheafOfModules.isQuasicoherentOnSite_reindex _ _ _ _ _ _
    (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ) _
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))
    (Stacks.SheafOfModules.isDenseSubsite_inverse_of_isContinuous
      (J := (smallEtaleRingedSite B S hS Y.1 Y.2).J)
      (J' := (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).J) _) M hM

/-- **The module equivalence of Stacks 04SG preserves finite type.** -/
theorem isFiniteType_smallerBaseModules (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS Y.1 Y.2).J M.val) :
    PresheafOfModules.IsFiniteType
      (smallEtaleRingedSite B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
        (spaceOverSmallerBase B W S hW hS h Y φ).2).J
      ((smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj M).val :=
  Stacks.SheafOfModules.isFiniteType_reindex (smallerBaseSmallEtaleEquivalence B W S hW hS h Y φ)
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) M hM

/-- **The module equivalence of Stacks 04SG carries quasi-coherent modules of finite type to
coherent modules** when `Y'` is locally Noetherian (Stacks 07UB). -/
theorem isCoherent_smallerBaseModules
    [Fact (HasEtaleLocalProperty B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    (hft : PresheafOfModules.IsFiniteType (smallEtaleRingedSite B S hS Y.1 Y.2).J M.val) :
    IsCoherent B W hW (spaceOverSmallerBase B W S hW hS h Y φ).1
      (spaceOverSmallerBase B W S hW hS h Y φ).2
      ((smallerBaseModulesEquivalence.{u, u} B W S hW hS h Y φ).functor.obj M) :=
  (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B W hW _ _ _).2
    ⟨isQuasicoherentOnSite_smallerBaseModules B W S hW hS h Y φ M hM,
      isFiniteType_smallerBaseModules B W S hW hS h Y φ M hft⟩

end AlgebraicGeometry.Space

end
