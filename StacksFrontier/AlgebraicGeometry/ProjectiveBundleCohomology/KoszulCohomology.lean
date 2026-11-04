module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.KoszulFiltration
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.DegreeZero
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.DirectImageDelta
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula

/-!
# Higher direct images along the Koszul filtration of a projective bundle

Let `E` be finite locally free of constant rank `n + 1 ≥ 2` on a scheme `S`, `π : 𝐏(E) ⟶ S` its
projective bundle and `K` the kernel of the tautological surjection `π^* E ⟶ 𝒪(1)`. The middle
terms `⋀ⁱ π^* E ⊗ 𝒪(-i)`, `1 ≤ i ≤ n`, of the twisted Koszul filtration have no higher direct
images at all, so the connecting morphisms identify `π_* 𝒪` with `Rⁿ π_* (⋀ⁿ K ⊗ 𝒪(-n))`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_rightDerivedPlus_twist_neg`:
  `R^q π_* 𝒪(-i) = 0` for all `q` and `1 ≤ i ≤ n`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.isZero_rightDerivedPlus_tensor_pullback`:
  the projection formula transports vanishing.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.SheafOfModules.TopWedge Stacks.SheafOfModules.WedgeQuotient

open Stacks.AlgebraicGeometry.LerayAffineBase (pushDelta)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section ProjectionFormula

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]

/-- **The projection formula for the higher direct images**, in the indexing
`CategoryTheory.Functor.rightDerived` by injective resolutions:
`R^q f_*(F ⊗ f^* G) ≅ R^q f_* F ⊗ G` for a finite locally free `G`. -/
public def rightDerivedProjectionFormulaIso (F : X.Modules) (q : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived q).obj
        ((Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback f).obj G)).obj
          F) ≅
      (Stacks.ProjectionFormula.tensorRightInvertible Y G).obj
        (((Scheme.Modules.pushforward f).rightDerived q).obj F) :=
  (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app _ ≪≫
    (Stacks.ProjectionFormula.higherDirectImageTensorRightFiniteLocallyFreeIso f G q).app F ≪≫
    (Stacks.ProjectionFormula.tensorRightInvertible Y G).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app F).symm

/-- **Vanishing passes along the projection formula**: if `R^q f_* F = 0` then
`R^q f_*(F ⊗ f^* G) = 0` for every finite locally free `G`. -/
public theorem isZero_rightDerived_tensor_pullback (F : X.Modules) (q : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj F)) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj
      ((Stacks.ProjectionFormula.tensorRightInvertible X ((Scheme.Modules.pullback f).obj G)).obj
        F)) :=
  ((Stacks.ProjectionFormula.tensorRightInvertible Y G).map_isZero h).of_iso
    (rightDerivedProjectionFormulaIso f G F q)

end ProjectionFormula

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))

/-- **`R^q π_* 𝒪(-i) = 0` for every integer `q` and `1 ≤ i ≤ n`.** -/
public theorem isZero_rightDerivedPlus_twist_neg {n : ℕ} (hn : 1 ≤ n)
    (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1)) {i : ℕ} (hi1 : 1 ≤ i)
    (hin : i ≤ n) (q : ℤ) :
    IsZero (((Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).rightDerivedPlus
      q).obj (D.algebra.piece (-(i : ℤ)))) := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · exact Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ q hq _
  · exact isZero_rightDerivedPlus_zero_of_neg E hqc D (by omega) hfree (by omega)
  · by_cases hqn : q = n
    · subst hqn
      exact isZero_rightDerivedPlus_pushforward_twist_top E hqc hn hfree D _ (by omega)
    · exact isZero_rightDerivedPlus_pushforward_twist_of_ne E hqc n hfree D _ q hq.ne' hqn

/-- The twist `𝒪(-k)` on the projective bundle. -/
public abbrev negTwist (k : ℕ) : (bundle E hqc).Modules := D.algebra.piece (-(k : ℤ))

/-- Tensoring with `𝒪(-k)` on the right. -/
public abbrev negTwistFunctor (k : ℕ) : (bundle E hqc).Modules ⥤ (bundle E hqc).Modules :=
  Stacks.ProjectionFormula.tensorRightInvertible (bundle E hqc) (negTwist E hqc D k)

/-- The twists on the projective bundle are invertible. -/
public instance isInvertible_piece (d : ℤ) :
    Stacks.SheafOfModules.IsInvertible (bundle E hqc).presheaf (bundle E hqc).ringCatSheaf.2
      (D.algebra.piece d) :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_stacksIsInvertible D
    (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E hqc) d

/-- The associativity isomorphism `(⋀ᵖ K ⊗ 𝒪(1)) ⊗ 𝒪(-p-1) ≅ ⋀ᵖ K ⊗ (𝒪(1) ⊗ 𝒪(-p-1))`. -/
public def koszulAssoc (p : ℕ) :
    (negTwistFunctor E hqc D (p + 1)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj
            ((kernelAlgebras E hqc D).exteriorPower p)).obj
          (D.algebra.piece ((1 : ℕ) : ℤ))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj
          ((kernelAlgebras E hqc D).exteriorPower p)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj
            (D.algebra.piece ((1 : ℕ) : ℤ))).obj (negTwist E hqc D (p + 1))) :=
  Stacks.SheafOfModules.tensorSheafAssociator (bundle E hqc).sheaf.obj
    (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (bundle E hqc))
      (bundle E hqc).sheaf).property ((kernelAlgebras E hqc D).exteriorPower p)
    (D.algebra.piece ((1 : ℕ) : ℤ)) (negTwist E hqc D (p + 1))

/-- `⋀ᵖ K ⊗ (𝒪(1) ⊗ 𝒪(-p-1)) ≅ ⋀ᵖ K ⊗ 𝒪(-p)`, by the multiplication of the twists. -/
public def koszulTwistMulIso (p : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj
          ((kernelAlgebras E hqc D).exteriorPower p)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj
            (D.algebra.piece ((1 : ℕ) : ℤ))).obj (negTwist E hqc D (p + 1))) ≅
      (negTwistFunctor E hqc D p).obj ((kernelAlgebras E hqc D).exteriorPower p) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj
      ((kernelAlgebras E hqc D).exteriorPower p)).mapIso
    (@asIso _ _ _ _ (twistMul D ((1 : ℕ) : ℤ) (-((p + 1 : ℕ) : ℤ)))
        (isIso_twistMul D (Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra
          E hqc) _ _) ≪≫
      eqToIso (congrArg D.algebra.piece (by push_cast; ring)))

/-- `koszulTwistMulIso` is the tensor product of the identity of `⋀ᵖ K` with the multiplication of
the twists. -/
public theorem koszulTwistMulIso_hom (p : ℕ) :
    (koszulTwistMulIso E hqc D p).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩)).map
        (X := ((kernelAlgebras E hqc D).exteriorPower p, _))
        (Y := ((kernelAlgebras E hqc D).exteriorPower p, negTwist E hqc D p))
        (𝟙 ((kernelAlgebras E hqc D).exteriorPower p),
          twistMul D ((1 : ℕ) : ℤ) (-((p + 1 : ℕ) : ℤ)) ≫
            eqToHom (congrArg D.algebra.piece (by push_cast; ring))) :=
  (Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(bundle E hqc).toRingedSpace.presheaf, (bundle E hqc).toRingedSpace.IsSheaf⟩)
    ((kernelAlgebras E hqc D).exteriorPower p)
    (twistMul D ((1 : ℕ) : ℤ) (-((p + 1 : ℕ) : ℤ)) ≫
      eqToHom (congrArg D.algebra.piece (by push_cast; ring) : _ = negTwist E hqc D p))).symm

/-- **`(⋀ᵖ K ⊗ 𝒪(1)) ⊗ 𝒪(-p-1) ≅ ⋀ᵖ K ⊗ 𝒪(-p)`**, by the associativity of the tensor product and
the multiplication of the twists. -/
public def koszulTwistIso (p : ℕ) :
    (negTwistFunctor E hqc D (p + 1)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj
            ((kernelAlgebras E hqc D).exteriorPower p)).obj
          (D.algebra.piece ((1 : ℕ) : ℤ))) ≅
      (negTwistFunctor E hqc D p).obj ((kernelAlgebras E hqc D).exteriorPower p) :=
  koszulAssoc E hqc D p ≪≫ koszulTwistMulIso E hqc D p

/-- Tensoring with a twist preserves zero morphisms. -/
public instance preservesZeroMorphisms_negTwistFunctor (k : ℕ) :
    (negTwistFunctor E hqc D k).PreservesZeroMorphisms :=
  haveI := isInvertible_piece E hqc D (-(k : ℤ))
  inferInstance

/-- Tensoring with a twist preserves finite limits. -/
public instance preservesFiniteLimits_negTwistFunctor (k : ℕ) :
    PreservesFiniteLimits (negTwistFunctor E hqc D k) :=
  haveI := isInvertible_piece E hqc D (-(k : ℤ))
  inferInstance

/-- Tensoring with a twist preserves finite colimits. -/
public instance preservesFiniteColimits_negTwistFunctor (k : ℕ) :
    PreservesFiniteColimits (negTwistFunctor E hqc D k) :=
  haveI := isInvertible_piece E hqc D (-(k : ℤ))
  inferInstance

/-- The Koszul filtration twisted by `𝒪(-p-1)`. -/
public abbrev koszulTwistSequence (p : ℕ) : ShortComplex (bundle E hqc).Modules :=
  (koszulSequence E hqc D p).map (negTwistFunctor E hqc D (p + 1))

/-- **The twisted Koszul filtration
`0 → ⋀ᵖ⁺¹ K ⊗ 𝒪(-p-1) → ⋀ᵖ⁺¹ π^* E ⊗ 𝒪(-p-1) → (⋀ᵖ K ⊗ 𝒪(1)) ⊗ 𝒪(-p-1) → 0` is short
exact.** -/
public theorem shortExact_koszulTwistSequence (p : ℕ) :
    (koszulTwistSequence E hqc D p).ShortExact :=
  (shortExact_koszul E hqc D p).map_of_exact _

/-- A finite locally free module of constant rank in the pointwise sense is finite locally
free. -/
public theorem isFiniteLocallyFree_of_rank {X : Scheme.{u}} (F : X.Modules) {r : ℕ}
    (hF : Scheme.Modules.IsFiniteLocallyFreeOfRank F r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
  have := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff F r).mp hF
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r

/-- The swap `⋀ᵖ π^* E ⊗ 𝒪(-k) ≅ 𝒪(-k) ⊗ ⋀ᵖ π^* E`. -/
public def koszulMiddleSwap (p k : ℕ) :
    (negTwistFunctor E hqc D k).obj ((pullbackAlgebras E hqc).exteriorPower p) ≅
      (Stacks.ProjectionFormula.tensorRightInvertible (bundle E hqc)
        ((pullbackAlgebras E hqc).exteriorPower p)).obj (negTwist E hqc D k) :=
  Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap (bundle E hqc).toRingedSpace
    ((pullbackAlgebras E hqc).exteriorPower p) (negTwist E hqc D k)

/-- The middle term `⋀ᵖ π^* E ⊗ 𝒪(-k)` of the twisted Koszul filtration is
`𝒪(-k) ⊗ π^* (⋀ᵖ E)`. -/
public def koszulMiddleIso (p k : ℕ) :
    (negTwistFunctor E hqc D k).obj ((pullbackAlgebras E hqc).exteriorPower p) ≅
      (Stacks.ProjectionFormula.tensorRightInvertible (bundle E hqc)
        ((Scheme.Modules.pullback
          (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj
          (Scheme.Modules.exteriorPower E (p : ℤ)))).obj (negTwist E hqc D k) :=
  koszulMiddleSwap E hqc D p k ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor (bundle E hqc).sheaf).obj
        (negTwist E hqc D k)).mapIso
      (Scheme.Modules.exteriorPowerPullbackIso
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase E p).symm

/-- The direct image functor of the projective bundle. -/
public abbrev bundlePushforward : (bundle E hqc).Modules ⥤ S.Modules :=
  Scheme.Modules.pushforward (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase

/-- The `r`-th term `⋀ʳ K ⊗ 𝒪(-r)` of the dimension shifting. -/
public abbrev koszulTerm (r : ℕ) : (bundle E hqc).Modules :=
  (negTwistFunctor E hqc D r).obj ((kernelAlgebras E hqc D).exteriorPower r)

variable {n : ℕ} (hn : 1 ≤ n) (hfree : Scheme.Modules.IsFiniteLocallyFreeOfRank E (n + 1))
include hn hfree

/-- **The middle term `⋀ᵖ⁺¹ π^* E ⊗ 𝒪(-p-1)` of the twisted Koszul filtration has no higher
direct images**, for `p + 1 ≤ n`. -/
public theorem isZero_rightDerived_koszulMiddle {p : ℕ} (hp : p + 1 ≤ n) (q : ℕ) :
    IsZero (((bundlePushforward E hqc).rightDerived q).obj (koszulTwistSequence E hqc D p).X₂) := by
  have := isFiniteLocallyFree_of_rank E hfree
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E (p + 1)
  have h : IsZero (((bundlePushforward E hqc).rightDerived q).obj (negTwist E hqc D (p + 1))) :=
    (isZero_rightDerivedPlus_twist_neg E hqc D hn hfree (i := p + 1) (by omega) hp q).of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso (bundlePushforward E hqc) q).app _)
  exact (isZero_rightDerived_tensor_pullback _ _ _ q h).of_iso
    (((bundlePushforward E hqc).rightDerived q).mapIso (koszulMiddleIso E hqc D (p + 1) (p + 1)))

/-- **The connecting morphism of the twisted Koszul filtration is an isomorphism**
`R^q π_*(⋀ᵖ K ⊗ 𝒪(-p)) ≅ R^{q+1} π_*(⋀ᵖ⁺¹ K ⊗ 𝒪(-p-1))`, for `p + 1 ≤ n`. -/
public def koszulShiftIso {p : ℕ} (hp : p + 1 ≤ n) (q : ℕ) :
    ((bundlePushforward E hqc).rightDerived q).obj (koszulTerm E hqc D p) ≅
      ((bundlePushforward E hqc).rightDerived (q + 1)).obj (koszulTerm E hqc D (p + 1)) :=
  ((bundlePushforward E hqc).rightDerived q).mapIso (koszulTwistIso E hqc D p).symm ≪≫
    @asIso _ _ _ _ ((pushDelta _).δ (shortExact_koszulTwistSequence E hqc D p) q)
      (DeltaFunctor.isIso_δ_of_isZero _ (shortExact_koszulTwistSequence E hqc D p) q
        (isZero_rightDerived_koszulMiddle E hqc D hn hfree hp q)
        (isZero_rightDerived_koszulMiddle E hqc D hn hfree hp (q + 1)))

/-- **Dimension shifting along the Koszul filtration**:
`π_*(⋀⁰ K ⊗ 𝒪(0)) ≅ R^p π_*(⋀ᵖ K ⊗ 𝒪(-p))` for `p ≤ n`. -/
public def koszulChainIso : ∀ (p : ℕ), p ≤ n →
    (((bundlePushforward E hqc).rightDerived 0).obj (koszulTerm E hqc D 0) ≅
      ((bundlePushforward E hqc).rightDerived p).obj (koszulTerm E hqc D p))
  | 0, _ => Iso.refl _
  | p + 1, hp => koszulChainIso p (by omega) ≪≫ koszulShiftIso E hqc D hn hfree hp p

omit hn [E.IsQuasicoherent] in
/-- The stalks of `π^* E` are free of rank `n + 1`. -/
public theorem nonempty_basis_stalk_bundlePullback (x : bundle E hqc) :
    Nonempty (Module.Basis (Fin (n + 1)) ↑(TopCat.Presheaf.stalk (bundle E hqc).presheaf x)
      ↑(TopCat.Presheaf.stalk (bundlePullback E hqc).val.presheaf x)) := by
  have := (Scheme.Modules.isFiniteLocallyFreeOfRank_iff E (n + 1)).mp hfree
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (bundle E hqc))
        (bundle E hqc).sheaf) (bundlePullback E hqc) (n + 1) :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase E (n + 1)
  exact ⟨Stacks.SheafOfModules.TopWedge.stalkBasis (bundlePullback E hqc) (n + 1) x⟩

omit hn in
/-- **`⋀ⁿ⁺¹ K = 0`**, `K` being of rank `n`. -/
public theorem isZero_kernelExteriorPower_succ :
    IsZero ((kernelAlgebras E hqc D).exteriorPower (n + 1)) :=
  @isZero_exteriorPower_of_rank _ _ _ _ _ (kernelAlgebras E hqc D)
    (tautologicalSequence E hqc D).f (tautologicalSequence E hqc D).g
    (tautologicalSequence E hqc D).zero (exact_tautological E hqc D)
    (mono_tautologicalSequence_f E hqc D) (epi_tautologicalMap E hqc D)
    (fun x => nonempty_basis_stalk_twistOne E hqc D x) n
    (fun x => nonempty_basis_stalk_bundlePullback E hqc hfree x)

omit hn in
/-- At `p = n` the second arrow of the twisted Koszul filtration is an isomorphism
`⋀ⁿ⁺¹ π^* E ⊗ 𝒪(-n-1) ≅ (⋀ⁿ K ⊗ 𝒪(1)) ⊗ 𝒪(-n-1)`. -/
public theorem isIso_koszulTwistSequence_g :
    IsIso (koszulTwistSequence E hqc D n).g :=
  (shortExact_koszulTwistSequence E hqc D n).isIso_g_iff.mpr
    ((negTwistFunctor E hqc D (n + 1)).map_isZero (isZero_kernelExteriorPower_succ E hqc D hfree))

/-- **The trace isomorphism of the Koszul filtration**:
`π_*(⋀⁰ K ⊗ 𝒪(0)) ≅ Rⁿ π_* 𝒪(-n-1) ⊗ ⋀ⁿ⁺¹ E`. -/
public def koszulTopIso :
    ((bundlePushforward E hqc).rightDerived 0).obj (koszulTerm E hqc D 0) ≅
      (Stacks.ProjectionFormula.tensorRightInvertible S
        (Scheme.Modules.exteriorPower E ((n + 1 : ℕ) : ℤ))).obj
        (((bundlePushforward E hqc).rightDerived n).obj (negTwist E hqc D (n + 1))) :=
  haveI := isFiniteLocallyFree_of_rank E hfree
  haveI := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower_scheme E (n + 1)
  koszulChainIso E hqc D hn hfree n le_rfl ≪≫
    ((bundlePushforward E hqc).rightDerived n).mapIso
      ((koszulTwistIso E hqc D n).symm ≪≫
        (@asIso _ _ _ _ (koszulTwistSequence E hqc D n).g
          (isIso_koszulTwistSequence_g E hqc D hfree)).symm ≪≫
        koszulMiddleIso E hqc D (n + 1) (n + 1)) ≪≫
    projectionFormulaDeltaApp _ _ _ n

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
