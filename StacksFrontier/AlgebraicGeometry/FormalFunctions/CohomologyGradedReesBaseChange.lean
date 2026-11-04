module

public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModuleDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFiniteType
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheafFiniteType
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraTotalModule
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.RelativeSpecQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FiniteTypeDominating.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFinite
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness
public import StacksCore.Tactic.StacksAttribute

/-!
# The two index sets of the graded cohomology, and Tag 0897 part (1) for the Rees algebra

For a graded module `M` over `⨁ₙ ℐⁿ` on a scheme `X` over `Spec A`, the `ℕ`-indexed sum
`⨁_{n : ℕ} Hᵖ(X, Mₙ)` and the `ℤ`-indexed sum
`Stacks.AlgebraicGeometry.GradedProperCohomology.gradedCohomologySum M p = ⨁_{n : ℤ} Hᵖ(X, Mₙ)`
agree when the negative pieces of `M` vanish. Through this comparison, finiteness of
`⨁_{n : ℕ} Hᵖ(X, Mₙ)` over `B = ⨁_{n : ℕ} Iⁿ` ([Stacks, Tag 02O8]'s hypothesis) follows from
[Stacks, Tag 0897] part (1), given a proper `f' : X' ⟶ Spec B`, a coherent `𝒪_{X'}`-module `F'`
and a `B`-linear comparison of `⨁ₙ Hᵖ(X, Mₙ)` with `Hᵖ(X', F')`.

The file also constructs the relative spectrum `X' = Spec_X(⨁ₙ ℐⁿ)` and the quasi-coherent
`𝒪_{X'}`-module `F'` with `π_* F' ≅ ⨁ₙ Mₙ`.

## Main definitions

* `Stacks.Cohomology.FormalFunctions.natToIntSum`: the comparison
  `⨁_{n : ℕ} Hᵖ(X, Mₙ) ⟶ ⨁_{n : ℤ} Hᵖ(X, Mₙ)`, an additive map.
* `Stacks.Cohomology.FormalFunctions.intToNatSum`: its retraction, restriction of a `ℤ`-indexed
  family along `ℕ ↪ ℤ` (`DFinsupp.comapDomain`).
* `Stacks.Cohomology.FormalFunctions.natIntSumEquiv`: the two sums agree when the negative
  pieces of `M` are zero objects.
* `Stacks.Cohomology.FormalFunctions.moduleOfAddEquiv`: a module structure transported along an
  additive equivalence.
* `Stacks.Cohomology.FormalFunctions.isQuasicoherent_reesAlgebraSheaf`: `⨁ₙ ℐⁿ` is
  quasi-coherent as a sheaf of commutative `𝒪_X`-algebras.
* `Stacks.Cohomology.FormalFunctions.reesRelativeSpec`: `X' = Spec_X(⨁ₙ ℐⁿ)`, with its affine
  structure morphism and the identification `π_* 𝒪_{X'} ≅ ⨁ₙ ℐⁿ` (`reesRelativeSpecIso`).
* `Stacks.Cohomology.FormalFunctions.reesBaseChangeModule`: `F'`, the quasi-coherent
  `𝒪_{X'}`-module with `π_* F' ≅ ⨁ₙ Mₙ` (`reesBaseChangeModuleIso`).
* `Stacks.Cohomology.FormalFunctions.reesSpecToBase`: the structure morphism
  `Spec(B) ⟶ Spec(A)` of the Rees algebra.

## Main results

* `Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_baseChange`:
  [Stacks, Tag 02O8]'s hypothesis at one graded module, from a proper `f' : X' ⟶ Spec B`, a
  coherent `F'` on `X'` and a `B`-linear comparison of `⨁ₙ Hᵖ(X, Mₙ)` with `Hᵖ(X', F')`.
* `Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_closedImmersion`:
  the same, with the proper morphism `f'` replaced by a closed immersion
  `j : X' ⟶ Spec(B) ×_{Spec A} X`.
* `Stacks.Cohomology.FormalFunctions.isProper_comp_pullbackFst_of_isClosedImmersion`: a closed
  subscheme of a base change along a proper morphism is proper over the new base.
* `Stacks.Cohomology.FormalFunctions.isQuasicoherent_ungradedSheaf` and
  `Stacks.Cohomology.FormalFunctions.isFiniteType_ungradedSheaf`: the total module `⨁ₙ Mₙ` is
  quasi-coherent, and of finite type, over `⨁ₙ ℐⁿ`.
* `Stacks.Cohomology.FormalFunctions.isLocallyNoetherian_of_isProper` and
  `Stacks.Cohomology.FormalFunctions.isLocallyNoetherian_reesRelativeSpec`: `X` and `X'` are
  locally Noetherian when `X` is proper over a Noetherian ring.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Blowup Stacks.AlgebraicGeometry.GradedProperCohomology
open scoped DirectSum

universe u

namespace Stacks.Cohomology.FormalFunctions

/-! ### Transport of a module structure along an additive equivalence -/

section Transport

variable {R : Type*} [Semiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module R M]

/-- Scalars act on `N` through an additive equivalence `e : M ≃+ N`, by `e ∘ (r • ·) ∘ e.symm`. -/
@[instance_reducible]
def smulOfAddEquiv (e : M ≃+ N) : SMul R N where
  smul r n := e (r • e.symm n)

/-- The `R`-module structure on `N` obtained from one on `M` by transport along an additive
equivalence `e : M ≃+ N`. -/
@[instance_reducible]
def moduleOfAddEquiv (e : M ≃+ N) : Module R N :=
  letI := smulOfAddEquiv (R := R) e
  { one_smul := fun n =>
      show e ((1 : R) • e.symm n) = n by rw [one_smul, e.apply_symm_apply]
    mul_smul := fun r s n =>
      show e ((r * s) • e.symm n) = e (r • e.symm (e (s • e.symm n))) by
        rw [e.symm_apply_apply, mul_smul]
    smul_zero := fun r =>
      show e (r • e.symm 0) = 0 by rw [map_zero, smul_zero, map_zero]
    smul_add := fun r n n' =>
      show e (r • e.symm (n + n')) = e (r • e.symm n) + e (r • e.symm n') by
        rw [map_add, smul_add, map_add]
    add_smul := fun r s n =>
      show e ((r + s) • e.symm n) = e (r • e.symm n) + e (s • e.symm n) by
        rw [add_smul, map_add]
    zero_smul := fun n =>
      show e ((0 : R) • e.symm n) = 0 by rw [zero_smul, map_zero] }

/-- Under `moduleOfAddEquiv`, the inverse of `e` is `R`-linear. -/
theorem moduleOfAddEquiv_symm_smul (e : M ≃+ N) (r : R) (n : N) :
    letI := moduleOfAddEquiv (R := R) e
    e.symm (r • n) = r • e.symm n :=
  e.symm_apply_apply _

end Transport

/-! ### The two index sets of the graded cohomology -/

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))
  (M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X)) (p : ℕ)

/-- The inclusion of the naturals in the integers is injective. -/
theorem natCast_injective_int : Function.Injective (Nat.cast : ℕ → ℤ) :=
  fun _ _ h => Int.natCast_inj.mp h

/-- Every element of a zero object of `ModuleCat R` vanishes. -/
theorem eq_zero_of_isZero {R : Type u} [Ring R] {N : ModuleCat.{u} R} (h : IsZero N) (x : N) :
    x = 0 :=
  calc x = (𝟙 N : N ⟶ N).hom x := rfl
    _ = (0 : N ⟶ N).hom x := by rw [(IsZero.iff_id_eq_zero N).mp h]
    _ = 0 := rfl

/-- The cohomology `Hᵖ(X, Mₙ)` in an integer degree `n`. -/
abbrev intCohomologyPiece (n : ℤ) : Type u := ↥(cohomologyOf X.left p (pieceModule M n))

/-- The comparison `⨁_{n : ℕ} Hᵖ(X, Mₙ) ⟶ ⨁_{n : ℤ} Hᵖ(X, Mₙ)`, placing the degree-`n` piece
in integer degree `n`. -/
def natToIntSum :
    (⨁ n : ℕ, gradedCohomologyPiece I X M p n) →+ gradedCohomologySum M p :=
  DirectSum.toAddMonoid fun n : ℕ =>
    DirectSum.of (intCohomologyPiece I X M p) (n : ℤ)

/-- The comparison on a homogeneous element. -/
theorem natToIntSum_of (n : ℕ) (x : gradedCohomologyPiece I X M p n) :
    natToIntSum I X M p (DirectSum.of (gradedCohomologyPiece I X M p) n x) =
      DirectSum.of (intCohomologyPiece I X M p) (n : ℤ) x :=
  DirectSum.toAddMonoid_of _ n x

/-- The retraction of the comparison: restriction of a `ℤ`-indexed family along the injection
`ℕ ↪ ℤ`. -/
def intToNatSum :
    gradedCohomologySum M p →+ (⨁ n : ℕ, gradedCohomologyPiece I X M p n) where
  toFun z :=
    DFinsupp.comapDomain (β := intCohomologyPiece I X M p)
      (Nat.cast : ℕ → ℤ) natCast_injective_int z
  map_zero' :=
    DFinsupp.ext fun n =>
      (DFinsupp.comapDomain_apply (β := intCohomologyPiece I X M p)
        (Nat.cast : ℕ → ℤ) natCast_injective_int 0 n).trans (DFinsupp.zero_apply _)
  map_add' x y :=
    DFinsupp.comapDomain_add (β := intCohomologyPiece I X M p)
      (Nat.cast : ℕ → ℤ) natCast_injective_int x y

/-- The retraction, read on a single component. -/
theorem intToNatSum_apply (z : gradedCohomologySum M p) (n : ℕ) :
    intToNatSum I X M p z n = z (n : ℤ) :=
  DFinsupp.comapDomain_apply (β := intCohomologyPiece I X M p)
    (Nat.cast : ℕ → ℤ) natCast_injective_int z n

/-- `intToNatSum` is a left inverse of `natToIntSum`. -/
theorem intToNatSum_natToIntSum (y : ⨁ n : ℕ, gradedCohomologyPiece I X M p n) :
    intToNatSum I X M p (natToIntSum I X M p y) = y := by
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n x =>
      refine DFinsupp.ext fun m => ?_
      rw [intToNatSum_apply, natToIntSum_of]
      rcases eq_or_ne n m with rfl | hnm <;> simp [DirectSum.of_apply, DirectSum.of_eq_same, *]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']

/-- The comparison is surjective when the negative pieces of `M` are zero objects. -/
theorem natToIntSum_surjective
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    Function.Surjective (natToIntSum I X M p) := by
  intro z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of n x =>
      rcases le_or_gt 0 n with hn | hn
      · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
        exact ⟨DirectSum.of (gradedCohomologyPiece I X M p) m x, natToIntSum_of I X M p m x⟩
      · refine ⟨0, ?_⟩
        have hx : x = 0 :=
          eq_zero_of_isZero (Functor.map_isZero (cohomologyFunctor X p) (hneg n hn)) x
        rw [map_zero, hx, map_zero]
  | add z z' hz hz' =>
      obtain ⟨y, hy⟩ := hz
      obtain ⟨y', hy'⟩ := hz'
      exact ⟨y + y', by rw [map_add, hy, hy']⟩

/-- The `ℕ`-indexed and `ℤ`-indexed sums agree when the negative pieces of `M` are zero
objects. -/
def natIntSumEquiv (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    (⨁ n : ℕ, gradedCohomologyPiece I X M p n) ≃+ gradedCohomologySum M p :=
  AddEquiv.ofBijective (natToIntSum I X M p)
    ⟨Function.LeftInverse.injective (intToNatSum_natToIntSum I X M p),
      natToIntSum_surjective I X M p hneg⟩

/-! ### The relative spectrum `Spec_X(⨁ₙ ℐⁿ)` -/

section RelativeSpec

open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
  Stacks.AlgebraicGeometry.FiniteTypeDominating

/-- A coproduct of quasi-coherent modules indexed by a `u`-small type is quasi-coherent. -/
theorem isQuasicoherent_coprod_of_small {Y : Scheme.{u}} {ι : Type*} [Small.{u} ι]
    (N : ι → SheafOfModules.{u} Y.ringCatSheaf) [HasCoproduct N]
    (h : ∀ j, (N j).IsQuasicoherent) :
    (∐ N).IsQuasicoherent :=
  have (j : Shrink.{u} ι) : (N ((equivShrink ι).symm j)).IsQuasicoherent := h _
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso SheafOfModules.sigmaShrinkIso
    (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_sigma
      fun j : Shrink.{u} ι => N ((equivShrink ι).symm j))

/-- The Rees algebra sheaf `⨁ₙ ℐⁿ` (`Stacks.Blowup.reesAlgebraSheaf`) is quasi-coherent as a
sheaf of algebras. -/
instance isQuasicoherent_reesAlgebraSheaf {Y : Scheme.{u}} (J : Y.IdealSheafData) :
    AlgebraSheaf.IsQuasicoherent (Stacks.Blowup.reesAlgebraSheaf J) :=
  isQuasicoherent_gradedAlgebraSheaf Y (reesGradedAlgebra J) _
    (reesPiece_negative_isZero J)
    (isQuasicoherent_coprod_of_small
      (fun n : ℕ => (reesGradedAlgebra J).piece (n : ℤ))
      fun n => reesPiece_isQuasicoherent J (n : ℤ))

/-- `X' = Spec_X(⨁_{n ≥ 0} ℐⁿ)`, the relative spectrum of the Rees algebra of `ℐ = I · 𝒪_X`,
as a scheme over `X`. -/
@[sga "2 XII 4.2" "partial"]
def reesRelativeSpec : Over X.left :=
  relativeSpecOver (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom))

/-- The structure morphism `π : X' ⟶ X` is affine. -/
instance isAffineHom_reesRelativeSpec : IsAffineHom (reesRelativeSpec I X).hom :=
  isAffineHom_relativeSpecOver _

/-- The identification `π_* 𝒪_{X'} ≅ ⨁_{n ≥ 0} ℐⁿ` ([Stacks, Tag 01LX]). -/
def reesRelativeSpecIso :
    pushforwardAlgebra (reesRelativeSpec I X).hom ≅
      Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom) :=
  relativeSpecOverIso _

/-- `X` is locally Noetherian when it is proper over a Noetherian ring. -/
theorem isLocallyNoetherian_of_isProper [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom) : IsLocallyNoetherian X.left :=
  let := hX
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- `X' = Spec_X(⨁ₙ ℐⁿ)` is locally Noetherian when `X` is proper over the Noetherian ring
`A`. -/
theorem isLocallyNoetherian_reesRelativeSpec [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom) :
    IsLocallyNoetherian (reesRelativeSpec I X).left :=
  have : IsLocallyNoetherian X.left := isLocallyNoetherian_of_isProper X hX
  @AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian _ _
    (relativeSpecOver (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom))).hom
    (locallyOfFiniteType_relativeSpecOver _
      (Stacks.Blowup.isFiniteType_reesAlgebraSheaf_of_isLocallyNoetherian _))
    (isLocallyNoetherian_of_isProper X hX)

/-! #### The total module `⨁ₙ Mₙ` and the module `F'` on `X'` -/

/-- The total module `⨁ₙ Mₙ` of a graded `𝓑 = ⨁ₙ ℐⁿ`-module is quasi-coherent over `⨁ₙ ℐⁿ`
when its homogeneous pieces are quasi-coherent and its negative pieces vanish. -/
theorem isQuasicoherent_ungradedSheaf
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    (SheafOfModules.GradedModule.ungradedSheaf M).IsQuasicoherent := by
  have hcop : (∐ fun n : ℕ => M.piece (n : ℤ)).IsQuasicoherent :=
    isQuasicoherent_coprod_of_small (fun n : ℕ => M.piece (n : ℤ)) fun n => hqc _
  have hres : ((SheafOfModules.restrictScalars
      (baseReesAlgebra I X).ungradedStructureMap).obj
        (SheafOfModules.GradedModule.ungradedSheaf M)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).prop_of_iso
      (SheafOfModules.GradedModule.coprodIsoUngradedSheaf M hneg) hcop
  exact Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_of_isQuasicoherent_restrictScalars
    (baseReesAlgebra I X).ungradedStructureMap
    (isQuasicoherent_reesAlgebraSheaf (baseIdealSheaf A I X.hom))
    (SheafOfModules.GradedModule.ungradedSheaf M) hres

/-- The total module `⨁ₙ Mₙ` is of finite type over `⨁ₙ ℐⁿ` when the graded module `M` is of
finite type. -/
theorem isFiniteType_ungradedSheaf (hft : M.IsFiniteType) :
    (SheafOfModules.GradedModule.ungradedSheaf M).IsFiniteType :=
  SheafOfModules.GradedModule.isFiniteType_ungradedSheaf M hft

/-- The total module `⨁ₙ Mₙ` as a quasi-coherent module over
`⨁ₙ ℐⁿ = AlgebraSheaf.ringSheaf (Stacks.Blowup.reesAlgebraSheaf ℐ)`. -/
def reesTotalQcoh (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    (SheafOfModules.isQuasicoherent
      (AlgebraSheaf.ringSheaf
        (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom)))).FullSubcategory :=
  ⟨SheafOfModules.GradedModule.ungradedSheaf M, isQuasicoherent_ungradedSheaf I X M hqc hneg⟩

/-- `F'`, the quasi-coherent `𝒪_{X'}`-module on `X' = Spec_X(⨁ₙ ℐⁿ)` whose direct image is the
total module `⨁ₙ Mₙ`, obtained from the equivalence
`Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence` ([Stacks, Tag 01SB]). -/
def reesBaseChangeModule (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    (reesRelativeSpec I X).left.Modules :=
  ((relativeSpecQcohEquivalence
    (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inverse.obj
      (reesTotalQcoh I X M hqc hneg)).obj

/-- `F'` is quasi-coherent. -/
theorem isQuasicoherent_reesBaseChangeModule
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    (reesBaseChangeModule I X M hqc hneg).IsQuasicoherent :=
  ((relativeSpecQcohEquivalence
    (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inverse.obj
      (reesTotalQcoh I X M hqc hneg)).property

/-- The identification `π_* F' ≅ ⨁ₙ Mₙ`. -/
def reesBaseChangeModuleIso (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    (relativeSpecQcohEquivalence
        (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom))).functor.obj
      ((relativeSpecQcohEquivalence
        (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inverse.obj
          (reesTotalQcoh I X M hqc hneg)) ≅
      reesTotalQcoh I X M hqc hneg :=
  (relativeSpecQcohEquivalence
    (Stacks.Blowup.reesAlgebraSheaf (baseIdealSheaf A I X.hom))).counitIso.app _

end RelativeSpec

/-! ### The honest base change `Spec(B) ×_{Spec A} X`, and properness over `Spec B` -/

section BaseChange

/-- The structure morphism `Spec(B) ⟶ Spec(A)` of the Rees algebra `B` of `I`. -/
abbrev reesSpecToBase : Spec (.of ↥(reesAlgebra I)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A ↥(reesAlgebra I)))

/-- If `q : Y ⟶ S` is proper and `j : Z ⟶ T ×_S Y` is a closed immersion, then the composite
`Z ⟶ T ×_S Y ⟶ T` is proper. -/
@[ega "III 4.3.4" "more general"]
theorem isProper_comp_pullbackFst_of_isClosedImmersion {S T Y Z : Scheme.{u}} (g : T ⟶ S)
    {q : Y ⟶ S} (hq : AlgebraicGeometry.IsProper q) (j : Z ⟶ pullback g q)
    (hj : AlgebraicGeometry.IsClosedImmersion j) :
    AlgebraicGeometry.IsProper (j ≫ pullback.fst g q) :=
  let := hq
  let := hj
  inferInstance

end BaseChange

/-! ### Tag 0897 part (1) for the Rees algebra, from the base change -/

attribute [local instance] cohomologyGradedModule

/-- The Rees algebra of `I` is of finite type over `A` when `A` is Noetherian, because `I` is then
finitely generated. -/
instance finiteType_reesAlgebra [IsNoetherianRing A] :
    Algebra.FiniteType A ↥(reesAlgebra I) :=
  finiteType_reesAlgebra_of_fg I (IsNoetherian.noetherian I)

/-- The graded action of `B = ⨁ₙ Iⁿ` on the `ℤ`-indexed sum `⨁_{n : ℤ} Hᵖ(X, Mₙ)`, transported
from the action on the `ℕ`-indexed sum along `natIntSumEquiv`. -/
@[instance_reducible]
def gradedCohomologySumModule
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    Module (⨁ n, ↥(reesGrading I n)) (gradedCohomologySum M p) :=
  moduleOfAddEquiv (natIntSumEquiv I X M p hneg)

/-- The action of the Rees algebra `reesAlgebra I` on `⨁_{n : ℤ} Hᵖ(X, Mₙ)`, obtained from the
graded action by restriction along `DirectSum.decomposeRingEquiv`. -/
@[instance_reducible, ega "III 3.3.2" "more general"]
def gradedCohomologySumModuleRees
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules)) :
    Module ↥(reesAlgebra I) (gradedCohomologySum M p) :=
  letI := gradedCohomologySumModule I X M p hneg
  Module.compHom _ (DirectSum.decomposeRingEquiv (reesGrading I)).toRingHom

/-- Let `A` be Noetherian, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper, and `M` a quasi-coherent
graded `𝓑 = ⨁ₙ ℐⁿ`-module of finite type whose negative pieces are zero objects. Given a proper
`f' : X' ⟶ Spec B`, a coherent `𝒪_{X'}`-module `F'` and a `B`-linear isomorphism of
`⨁_{n : ℤ} Hᵖ(X, Mₙ)` with `Hᵖ(X', F')`, the sum `⨁_{n : ℕ} Hᵖ(X, Mₙ)` is a finite module over
`B = ⨁_{n : ℕ} Iⁿ`. -/
theorem isCohomologyReesFiniteOfGradedModule_of_baseChange [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom)
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hft : M.IsFiniteType)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules))
    {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of ↥(reesAlgebra I))) [IsProper f']
    (F' : X'.Modules) [F'.IsCoherent]
    (cmp :
      letI := gradedCohomologySumModuleRees I X M p hneg
      gradedCohomologySum M p ≃ₗ[↥(reesAlgebra I)]
        ↥((ModuleCat.restrictScalars (specAlgebraRingHom ↥(reesAlgebra I) f')).obj
          (cohomologyOf X' p F'))) :
    IsCohomologyReesFiniteOfGradedModule I X M p := by
  let := hX
  let := gradedCohomologySumModule I X M p hneg
  let := gradedCohomologySumModuleRees I X M p hneg
  have hfinB : Module.Finite ↥(reesAlgebra I) (gradedCohomologySum M p) :=
    moduleFinite_gradedCohomologySum A (reesGrading I) X.hom M hqc hft p f' F' cmp
  show Module.Finite (⨁ n, ↥(reesGrading I n))
    (⨁ n, gradedCohomologyPiece I X M p n)
  exact Module.Finite.of_surjective
    (σ := (DirectSum.decomposeRingEquiv (reesGrading I)).toRingHom)
    { toFun := (natIntSumEquiv I X M p hneg).symm
      map_add' := map_add _
      map_smul' := fun r z => moduleOfAddEquiv_symm_smul (natIntSumEquiv I X M p hneg) _ z }
    (natIntSumEquiv I X M p hneg).symm.surjective

/-- `Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule_of_baseChange`
with the proper morphism `f' : X' ⟶ Spec B` replaced by a closed immersion
`j : X' ⟶ Spec(B) ×_{Spec A} X`, with `f' = j ≫ pr₁`. -/
theorem isCohomologyReesFiniteOfGradedModule_of_closedImmersion [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom)
    (hqc : ∀ n : ℤ, (pieceModule M n).IsQuasicoherent)
    (hft : M.IsFiniteType)
    (hneg : ∀ n : ℤ, n < 0 → IsZero (M.piece n : X.left.Modules))
    {X' : Scheme.{u}} (j : X' ⟶ pullback (reesSpecToBase I) X.hom)
    (hj : AlgebraicGeometry.IsClosedImmersion j)
    (F' : X'.Modules) [F'.IsCoherent]
    (cmp :
      letI := gradedCohomologySumModuleRees I X M p hneg
      gradedCohomologySum M p ≃ₗ[↥(reesAlgebra I)]
        ↥((ModuleCat.restrictScalars (specAlgebraRingHom ↥(reesAlgebra I)
            (j ≫ pullback.fst (reesSpecToBase I) X.hom))).obj
          (cohomologyOf X' p F'))) :
    IsCohomologyReesFiniteOfGradedModule I X M p :=
  let := isProper_comp_pullbackFst_of_isClosedImmersion (reesSpecToBase I) hX j hj
  isCohomologyReesFiniteOfGradedModule_of_baseChange I X M p hX hqc hft hneg
    (j ≫ pullback.fst (reesSpecToBase I) X.hom) F' cmp

end Stacks.Cohomology.FormalFunctions

end
