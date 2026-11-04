module

public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleInvertibility
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatAlgebraBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.PairingIndependence
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.QuasiFiniteGorenstein
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparisonPushout
public import StacksFrontier.AlgebraicGeometry.Discriminant.FlatOverBase
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleData0BVG
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.RingTheory.Flat.FlatAtPointCriteria
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus

/-!
# Further results

Results complementing `StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleInvertibility`.
-/

@[expose] public section

universe u v w z

namespace Stacks.Discriminant

open scoped TensorProduct

/-- **Local criterion at a prime.** A finite module over the target which is flat over the base
becomes free after localizing at a prime `q` as soon as its fibre `T ⊗ M_q` over
`T = B_q / 𝔭 B_q`, `𝔭 = q ∩ A`, is free. This is the local criterion for flatness over `A_𝔭`. -/
theorem free_localizedModule_of_free_quotient
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] [Module.Flat A M] (q : Ideal B) [q.IsPrime]
    (hfree : Module.Free (Localization.AtPrime q ⧸ (q.under A).map
        (algebraMap A (Localization.AtPrime q)))
      ((Localization.AtPrime q ⧸ (q.under A).map (algebraMap A (Localization.AtPrime q)))
        ⊗[Localization.AtPrime q] LocalizedModule.AtPrime q M)) :
    Module.Free (Localization.AtPrime q) (LocalizedModule.AtPrime q M) := by
  let p := q.under A
  let S := Localization.AtPrime q
  let N := LocalizedModule.AtPrime q M
  let J := p.map (algebraMap A S)
  let T := S ⧸ J
  let : Algebra (Localization.AtPrime p) S := Ideal.algebraLocalizationAtPrimeUnder q
  let : IsScalarTower A (Localization.AtPrime p) S :=
    Ideal.isScalarTower_localizationAtPrimeUnder q
  let : IsLocalHom (algebraMap (Localization.AtPrime p) S) :=
    Ideal.isLocalHom_algebraMap_localizationAtPrimeUnder q
  let : Module (Localization.AtPrime p) N :=
    Module.compHom N (algebraMap (Localization.AtPrime p) S)
  let : IsScalarTower (Localization.AtPrime p) S N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A (Localization.AtPrime p) N :=
    IsScalarTower.of_algebraMap_smul fun a n => by
      show algebraMap (Localization.AtPrime p) S
        (algebraMap A (Localization.AtPrime p) a) • n = a • n
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_smul]
  have : Module.Flat A N := Module.Flat.of_isLocalizedModule_of_tower q.primeCompl
    (LocalizedModule.mkLinearMap q.primeCompl M)
  have : Module.Flat (Localization.AtPrime p) N :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl N).mpr
      inferInstance
  have : Module.Free T (T ⊗[S] N) := hfree
  rcases subsingleton_or_nontrivial N with _ | _
  · exact Module.Free.of_subsingleton _ _
  refine (Module.Flat.free_and_flat_of_free_maximalIdeal
    (R := Localization.AtPrime p) ?_).1
  rw [Ideal.map_maximalIdeal_eq_map_under q]
  exact Module.Free.of_equiv (LinearEquiv.extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective (TensorProduct.quotTensorEquivQuotSMul N J))

section Schemes

open _root_.AlgebraicGeometry _root_.CategoryTheory
open scoped _root_.AlgebraicGeometry

noncomputable section

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-! ### Invertibility along a semilinear equivalence -/

/-! ### Moving a finite-open factorization along an isomorphism of the target -/

/-! ### The relative dualizing module of a cocartesian chart -/

/-! ### The residue field of a point of an affine chart -/

/-! ### The scheme version -/

section Fibres

variable {X Y : Scheme.{u}} (f : Y ⟶ X)
  [IsNoetherian X] [IsNoetherian Y]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f]

end Fibres

end

end Schemes

end Stacks.Discriminant

end
