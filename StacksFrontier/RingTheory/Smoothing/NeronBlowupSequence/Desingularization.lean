module

public import StacksFrontier.RingTheory.Smoothing.NeronBlowupSequence.TorsionLength
import all StacksFrontier.RingTheory.Smoothing.NeronBlowupSequence.TorsionLength
public import StacksFrontier.RingTheory.Smoothing.NeronBlowupSequence.DifferentialRelations
import all StacksFrontier.RingTheory.Smoothing.NeronBlowupSequence.DifferentialRelations

/-!
# Néron's desingularization by a finite sequence of affine blowups

Fix an extension `R → Λ` of discrete valuation rings of ramification index one together with a
factorization `R → A → Λ` in which `A` is flat and of finite type over `R`, and write
`𝔮 = Ker(A → Λ)` and `𝔭 = (A → Λ)^{-1}(𝔪_Λ)`. If `A` is smooth over `R` at `𝔮` and the
residue-field extension `κ(R) → κ(Λ)` is separable, then finitely many affine Néron blowups
turn `A` into an algebra that is smooth over `R` at its distinguished prime.

Each blowup replaces a stage `A'` by the affine blowup `A'[𝔭'/π]` at a uniformizer `π` of `R`,
with `𝔭'` the preimage of `𝔪_Λ`. Smoothness at the generic prime and the separability
hypothesis persist along the sequence, and the torsion length

`defect(A') = length_Λ (torsion of Λ ⊗_{A'} Ω_{A'/R})`

drops strictly at every blowup as long as it is non-zero. When it reaches zero the module
`Λ ⊗_{A'} Ω_{A'/R}` is free, and the conormal criterion for smoothness applies.

## Main definitions

* `Stacks.Smoothing.NeronStage`: an intermediate algebra `R → A' → Λ` of a blowup sequence.
* `Stacks.Smoothing.NeronStage.kernelIdeal`,
  `Stacks.Smoothing.NeronStage.maximalIdealPreimage`: the ideals `𝔮'` and `𝔭'` of a stage.
* `Stacks.Smoothing.IsAffineNeronBlowup`: the one-step relation "`Y` is an affine Néron blowup
  of `X`".
* `Stacks.Smoothing.NeronStage.blowup`: the affine Néron blowup of a stage at a uniformizer.
* `Stacks.Smoothing.NeronSituation.withIntermediate`,
  `Stacks.Smoothing.NeronStage.toNeronSituation`: changing the intermediate algebra of a Néron
  situation, and the Néron situation attached to a stage.

## Main results

* `Stacks.Smoothing.exists_finite_affineNeronBlowup_smoothAt`: Néron's desingularization — some
  stage reachable from `A` by finitely many affine Néron blowups is smooth over `R` at its
  distinguished prime.

## Implementation notes

A finite sequence of blowups is the reflexive transitive closure of the one-step relation
`IsAffineNeronBlowup`. That relation identifies the next stage, as an `R`-algebra, with the
canonical `affineBlowupAlgebra` of `𝔭'` at the image of a uniformizer, and requires its map to
`Λ` to extend the map of the current stage; `NeronStage.blowup` is the canonical witness, built
from `canonicalNeronBlowupMap`.

## References

* [Stacks Project, Tag 0BJ6](https://stacks.math.columbia.edu/tag/0BJ6)
-/

@[expose] public section

namespace Stacks.Smoothing

open CategoryTheory
open scoped TensorProduct

universe uV u v w w'

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## Stages of a blowup sequence -/

/-- An intermediate algebra of a Néron blowup sequence: a factorization `R → A' → Λ` of the
extension through an algebra `A'` reached from `A` by affine blowups. -/
structure NeronStage (S : NeronSituation.{u, v, w}) where
  /-- The underlying algebra of the stage. -/
  A : Type w
  /-- The commutative-ring structure on the stage. -/
  [commRing : CommRing A]
  /-- The structure map from `R`. -/
  [algebraRA : Algebra S.R A]
  /-- The structure map to `Λ`. -/
  [algebraAΛ : Algebra A S.Λ]
  /-- The displayed maps factor the extension `R → Λ`. -/
  [tower : IsScalarTower S.R A S.Λ]

attribute [instance] NeronStage.commRing NeronStage.algebraRA NeronStage.algebraAΛ
  NeronStage.tower

/-- The kernel ideal `𝔮' = Ker(A' → Λ)` of a stage. -/
def NeronStage.kernelIdeal {S : NeronSituation.{u, v, w}} (X : NeronStage S) : Ideal X.A :=
  RingHom.ker (algebraMap X.A S.Λ)

/-- The kernel ideal of a stage is prime, since `Λ` is a domain. -/
instance NeronStage.isPrime_kernelIdeal {S : NeronSituation.{u, v, w}}
    (X : NeronStage S) : X.kernelIdeal.IsPrime :=
  RingHom.ker_isPrime (algebraMap X.A S.Λ)

/-- The distinguished prime `𝔭' = (A' → Λ)^{-1}(𝔪_Λ)` of a stage. -/
def NeronStage.maximalIdealPreimage {S : NeronSituation.{u, v, w}} (X : NeronStage S) :
    Ideal X.A :=
  Ideal.comap (algebraMap X.A S.Λ) (IsLocalRing.maximalIdeal S.Λ)

/-- The distinguished prime of a stage is prime. -/
instance NeronStage.isPrime_maximalIdealPreimage {S : NeronSituation.{u, v, w}}
    (X : NeronStage S) : X.maximalIdealPreimage.IsPrime := by
  let : (IsLocalRing.maximalIdeal S.Λ).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal S.Λ).isPrime
  exact Ideal.comap_isPrime _ _

/-- The initial stage of a blowup sequence, namely `A` itself. -/
def NeronStage.initial (S : NeronSituation.{u, v, w}) : NeronStage S where
  A := S.A
  commRing := inferInstance
  algebraRA := inferInstance
  algebraAΛ := inferInstance
  tower := inferInstance

/-- `Y` is an affine Néron blowup of `X`: for some uniformizer `π` of `R`, the algebra `Y` is
`R`-isomorphic to the affine blowup `X[𝔭'/π]`, compatibly with a map to `Λ` extending the one
of `X`. -/
def IsAffineNeronBlowup (S : NeronSituation.{u, v, w}) (X Y : NeronStage S) : Prop :=
  ∃ π : S.R, IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R) ∧
    ∃ (φ : affineBlowupAlgebra X.maximalIdealPreimage (algebraMap S.R X.A π)
        (Localization.Away (algebraMap S.R X.A π)) →+* S.Λ)
      (e : affineBlowupAlgebra X.maximalIdealPreimage (algebraMap S.R X.A π)
        (Localization.Away (algebraMap S.R X.A π)) ≃ₐ[S.R] Y.A),
      φ.comp (algebraMap X.A _) = algebraMap X.A S.Λ ∧
      ∀ x, algebraMap Y.A S.Λ (e x) = φ x

/-- The Néron situation obtained by replacing the intermediate algebra by another flat
finite-type factorization `R → B → Λ` of the same extension of discrete valuation rings. -/
@[reducible]
def NeronSituation.withIntermediate (S : NeronSituation.{u, v, w}) (B : Type w')
    [CommRing B] [Algebra S.R B] [Algebra B S.Λ] [IsScalarTower S.R B S.Λ]
    [Module.Flat S.R B] [Algebra.FiniteType S.R B] : NeronSituation.{u, v, w'} where
  R := S.R
  Λ := S.Λ
  A := B
  commRingR := S.commRingR
  isDomainR := S.isDomainR
  isDiscreteValuationRingR := S.isDiscreteValuationRingR
  commRingΛ := S.commRingΛ
  isDomainΛ := S.isDomainΛ
  isDiscreteValuationRingΛ := S.isDiscreteValuationRingΛ
  commRingA := inferInstance
  algebraRΛ := S.algebraRΛ
  extension := S.extension
  ramificationIndex_one := S.ramificationIndex_one
  algebraRA := inferInstance
  algebraAΛ := inferInstance
  isScalarTower := inferInstance
  flat := inferInstance
  finiteType := inferInstance

/-- A flat finite-type stage is itself the intermediate algebra of a Néron situation, with the
same extension `R → Λ`. -/
def NeronStage.toNeronSituation
    (S : NeronSituation.{u, v, w}) (X : NeronStage S)
    [Module.Flat S.R X.A] [Algebra.FiniteType S.R X.A] :
    NeronSituation.{u, v, w} :=
  S.withIntermediate X.A

/-- The affine Néron blowup of a stage at a uniformizer `π`: the affine blowup algebra
`X[𝔭'/π]`, with the canonical extension of `X → Λ` as its map to `Λ`. -/
noncomputable def NeronStage.blowup
    (S : NeronSituation.{u, v, w}) (X : NeronStage S)
    [Module.Flat S.R X.A] [Algebra.FiniteType S.R X.A]
    (π : S.R) (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    NeronStage S := by
  letI : CommRing X.A := X.commRing
  letI : Algebra S.R X.A := X.algebraRA
  letI : Algebra X.A S.Λ := X.algebraAΛ
  let SX := NeronStage.toNeronSituation S X
  let B := affineBlowupAlgebra X.maximalIdealPreimage (algebraMap S.R X.A π)
    (Localization.Away (algebraMap S.R X.A π))
  let φ : {f : B →+* S.Λ // f.comp (algebraMap X.A B) = algebraMap X.A S.Λ} :=
    canonicalNeronBlowupMap SX π hπ
  letI : Algebra B S.Λ := φ.1.toAlgebra
  have hcomp : (algebraMap B S.Λ).comp (algebraMap X.A B) = algebraMap X.A S.Λ := φ.2
  letI : IsScalarTower S.R B S.Λ := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply S.R X.A S.Λ,
      IsScalarTower.algebraMap_apply S.R X.A B]
    exact (RingHom.congr_fun hcomp (algebraMap S.R X.A r)).symm
  exact ⟨B⟩

/-- The canonical blowup of a stage is an affine Néron blowup of it. -/
private lemma isAffineNeronBlowup_blowup
    (S : NeronSituation.{u, v, w}) (X : NeronStage S)
    [Module.Flat S.R X.A] [Algebra.FiniteType S.R X.A]
    (π : S.R) (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    IsAffineNeronBlowup S X (NeronStage.blowup S X π hπ) := by
  let SX := NeronStage.toNeronSituation S X
  let φ := canonicalNeronBlowupMap SX π hπ
  exact ⟨π, hπ, φ.1, AlgEquiv.refl, φ.2, fun _ => rfl⟩

/-- Flatness over `R` is inherited by the blowup of a stage. -/
private lemma flat_neronStage_blowup
    (S : NeronSituation.{u, v, w}) (X : NeronStage S)
    [Module.Flat S.R X.A] [Algebra.FiniteType S.R X.A]
    (π : S.R) (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    Module.Flat S.R (NeronStage.blowup S X π hπ).A := by
  exact flat_affineBlowupAlgebra (R := S.R) (A := X.A) _ _

/-- Being of finite type over `R` is inherited by the blowup of a stage. -/
private lemma finiteType_neronStage_blowup
    (S : NeronSituation.{u, v, w}) (X : NeronStage S)
    [Module.Flat S.R X.A] [Algebra.FiniteType S.R X.A]
    (π : S.R) (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    Algebra.FiniteType S.R (NeronStage.blowup S X π hπ).A := by
  let : CommRing X.A := X.commRing
  let : Algebra S.R X.A := X.algebraRA
  let : IsNoetherianRing X.A := Algebra.FiniteType.isNoetherianRing S.R X.A
  let I := X.maximalIdealPreimage
  let B := affineBlowupAlgebra I (algebraMap S.R X.A π)
    (Localization.Away (algebraMap S.R X.A π))
  let : Algebra.FiniteType X.A B :=
    finiteType_affineBlowupAlgebra I _ (IsNoetherian.noetherian I)
  change Algebra.FiniteType S.R B
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType S.R X.A) inferInstance

/-- The image of a uniformizer of `R` in `Λ` is non-zero. -/
private lemma algebraMap_uniformizer_ne_zero (S : NeronSituation.{u, v, w}) {π : S.R}
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) :
    algebraMap S.R S.Λ π ≠ 0 := by
  simpa only [map_zero] using S.extension.1.ne (uniformizer_ne_zero hπ)

/-- Smoothness at the generic prime `𝔮'` is inherited by the blowup of a stage: the blowup is a
subalgebra of a localization of `X` away from the image of `π`, which is a unit in `Λ`. -/
private lemma smoothAt_kernelIdeal_neronStage_blowup
    (S : NeronSituation.{u, v, w}) (X : NeronStage S)
    [Module.Flat S.R X.A] [Algebra.FiniteType S.R X.A]
    (π : S.R) (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsm : Algebra.SmoothAt S.R X.A X.kernelIdeal) :
    Algebra.SmoothAt S.R (NeronStage.blowup S X π hπ).A
      (NeronStage.blowup S X π hπ).kernelIdeal := by
  let SX := NeronStage.toNeronSituation S X
  let a := algebraMap S.R X.A π
  let B := affineBlowupAlgebra X.maximalIdealPreimage a (Localization.Away a)
  let φ : {f : B →+* S.Λ // f.comp (algebraMap X.A B) = algebraMap X.A S.Λ} :=
    canonicalNeronBlowupMap SX π hπ
  have : (RingHom.ker φ.1).IsPrime := RingHom.ker_isPrime _
  change Algebra.SmoothAt S.R B (RingHom.ker φ.1)
  have hker : (RingHom.ker φ.1).comap (algebraMap X.A B) =
      RingHom.ker (algebraMap X.A S.Λ) := by
    rw [RingHom.comap_ker, φ.2]
  apply smoothAt_subalgebra_localization a B (RingHom.ker φ.1)
  · intro h
    have he : φ.1 (algebraMap X.A B a) = algebraMap X.A S.Λ a :=
      RingHom.congr_fun φ.2 a
    refine algebraMap_uniformizer_ne_zero S hπ ?_
    rw [IsScalarTower.algebraMap_apply S.R X.A S.Λ, ← he]
    exact h
  · simpa only [Algebra.SmoothAt, NeronStage.kernelIdeal, hker] using hsm

/-- A Néron situation whose intermediate algebra is smooth over `R` is smooth over `R` at the
distinguished prime `𝔭`. -/
private lemma smoothAt_maximalIdealPreimage_of_smooth (S : NeronSituation.{u, v, w})
    [Algebra.Smooth S.R S.A] :
    Algebra.SmoothAt S.R S.A S.maximalIdealPreimage := by
  refine ⟨1, fun h => (NeronSituation.isPrime_maximalIdealPreimage S).ne_top
    (Ideal.eq_top_of_isUnit_mem _ h isUnit_one), ?_⟩
  have : Algebra.Smooth S.A (Localization.Away (1 : S.A)) :=
    Algebra.Smooth.of_isLocalization_Away (R := S.A) 1
  exact Algebra.Smooth.comp S.R S.A _

/-- If `Λ ⊗_A Ω_{A/R}` is free and `A` is smooth over `R` at `𝔮`, then `A` is smooth over `R`
at `𝔭`: a polynomial presentation of `A` has free conormal cokernel, so Stacks 0BJ5 applies. -/
private lemma smoothAt_of_free_differentials
    (S : NeronSituation.{u, v, w})
    (hsm : Algebra.SmoothAt S.R S.A S.kernelIdeal)
    (hfree : Module.Free S.Λ (S.Λ ⊗[S.A] Ω[S.A⁄S.R])) :
    Algebra.SmoothAt S.R S.A S.maximalIdealPreimage := by
  let : CommRing S.A := S.commRingA
  let : Algebra S.R S.A := S.algebraRA
  obtain ⟨n, f, hf, hB⟩ := exists_smooth_polynomial_presentation
    (R := S.R) (A := S.A) S.maximalIdealPreimage
  let P := MvPolynomial (Fin n) S.R
  let : Algebra P S.A := f.toRingHom.toAlgebra
  let : IsScalarTower S.R P S.A :=
    IsScalarTower.of_algebraMap_eq (R := S.R) (S := P) (A := S.A)
      fun r => (f.commutes r).symm
  let : Algebra P S.Λ := ((algebraMap S.A S.Λ).comp (algebraMap P S.A)).toAlgebra
  let : IsScalarTower P S.A S.Λ :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := S.A) (A := S.Λ) fun _ => rfl
  have hsurj : Function.Surjective (algebraMap P S.A) := hf
  let : RingHomSurjective f.toRingHom := ⟨hsurj⟩
  let := ConormalSeq.cotangentModule hsurj
  let Q := (S.Λ ⊗[S.A] (S.A ⊗[P] Ω[P⁄S.R])) ⧸
    LinearMap.range (LinearMap.baseChange S.Λ (ConormalSeq.conormalMap S.R hsurj))
  have : Module.Free S.Λ (S.Λ ⊗[S.A] Ω[S.A⁄S.R]) := hfree
  have hQ : Module.Free S.Λ Q :=
    Module.Free.of_equiv (quotConormalRangeEquivDifferentials hsurj).symm
  exact smoothAt_of_conormal_cokernel_free S P hsurj hsm hB hQ

/-! ## The strict drop of the torsion length -/

/-- From a short exact sequence `0 → L ⊗_P Ω_{P/R} → L ⊗_{P'} Ω_{P'/R} → N → 0` of `L`-modules
whose third term is killed by `π`, the base change to `Λ` of the first map is injective and
admits a section up to the factor `π`. -/
private lemma exists_differential_section_of_exact
    {R P P' L Λ N : Type*} [CommRing R] [CommRing P] [CommRing P'] [CommRing L]
    [CommRing Λ] [IsDomain Λ] [Algebra R P] [Algebra R P'] [Algebra P P']
    [IsScalarTower R P P'] [Algebra P L] [Algebra P' L] [IsScalarTower P P' L]
    [Algebra R L] [IsScalarTower R P' L] [Algebra L Λ] [Algebra P Λ] [Algebra P' Λ]
    [Algebra R Λ] [IsScalarTower P P' Λ] [IsScalarTower P L Λ] [IsScalarTower P' L Λ]
    [IsScalarTower R L Λ] [AddCommGroup N] [Module L N]
    [Module.IsTorsionFree Λ (Λ ⊗[L] (L ⊗[P] Ω[P⁄R]))]
    (π : R) (hπ : algebraMap L Λ (algebraMap R L π) ≠ 0)
    (f : (L ⊗[P] Ω[P⁄R]) →ₗ[L] (L ⊗[P'] Ω[P'⁄R]))
    (hf : ∀ (a : L) (x : Ω[P⁄R]),
      f (a ⊗ₜ[P] x) = a ⊗ₜ[P'] KaehlerDifferential.map R R P P' x)
    (g : (L ⊗[P'] Ω[P'⁄R]) →ₗ[L] N) (hex : Function.Exact f g)
    (hinj : Function.Injective f)
    (hN : ∀ z : N, algebraMap R L π • z = 0) :
    Function.Injective (differentialBaseChangeMap R P P' Λ) ∧
      ∃ v : (Λ ⊗[P'] Ω[P'⁄R]) →ₗ[Λ] (Λ ⊗[P] Ω[P⁄R]),
        ∀ x, differentialBaseChangeMap R P P' Λ (v x) = algebraMap R Λ π • x := by
  obtain ⟨vloc, huloc, huvloc⟩ :=
    exists_baseChange_mul_inverse_of_exact f g hex hinj (algebraMap R L π) hπ hN
  let eP := TensorProduct.AlgebraTensorModule.cancelBaseChange P L Λ Λ Ω[P⁄R]
  let eP' := TensorProduct.AlgebraTensorModule.cancelBaseChange P' L Λ Λ Ω[P'⁄R]
  let uLoc : (Λ ⊗[P] Ω[P⁄R]) →ₗ[Λ] (Λ ⊗[P'] Ω[P'⁄R]) :=
    eP'.toLinearMap.comp ((LinearMap.baseChange Λ f).comp eP.symm.toLinearMap)
  have huLoc_tmul (a : Λ) (x : Ω[P⁄R]) :
      uLoc (a ⊗ₜ[P] x) = a ⊗ₜ[P'] KaehlerDifferential.map R R P P' x := by
    change eP' ((LinearMap.baseChange Λ f) (eP.symm (a ⊗ₜ[P] x))) = _
    rw [show eP.symm (a ⊗ₜ[P] x) = a ⊗ₜ[L] ((1 : L) ⊗ₜ[P] x) from
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul P L Λ a x]
    change eP' (a ⊗ₜ[L] f ((1 : L) ⊗ₜ[P] x)) = _
    rw [hf 1 x]
    change ((1 : L) • a) ⊗ₜ[P'] KaehlerDifferential.map R R P P' x = _
    rw [one_smul]
  have huLoc : uLoc = differentialBaseChangeMap R P P' Λ := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => rw [huLoc_tmul, differentialBaseChangeMap_tmul]
  refine ⟨?_, eP.toLinearMap.comp (vloc.comp eP'.symm.toLinearMap), ?_⟩
  · rw [← huLoc]
    exact eP'.injective.comp (huloc.comp eP.symm.injective)
  · intro x
    rw [← huLoc]
    change eP' ((LinearMap.baseChange Λ f) (eP.symm (eP (vloc (eP'.symm x))))) = _
    rw [eP.symm_apply_apply, huvloc, map_smul, eP'.apply_symm_apply,
      ← IsScalarTower.algebraMap_apply R L Λ]

/-- Transitivity of factorizations: if `A → B → C`, `B → C → D` and `A → B → D` are towers,
then so is `A → C → D`. -/
private lemma isScalarTower_of_trans {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra A B] [Algebra B C] [Algebra A C] [Algebra B D]
    [Algebra C D] [Algebra A D] [IsScalarTower A B C] [IsScalarTower B C D]
    [IsScalarTower A B D] : IsScalarTower A C D :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A B C x, ← IsScalarTower.algebraMap_apply B C D,
      ← IsScalarTower.algebraMap_apply A B D]

/-- A finite tuple of elements of `L ⧸ (a)` is killed by `a`. -/
private lemma smul_pi_quotient_span_singleton_eq_zero {L : Type*} [CommRing L] (a : L)
    (c : ℕ) (z : Fin c → L ⧸ Ideal.span ({a} : Set L)) : a • z = 0 := by
  funext i
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (z i)
  change a • z i = 0
  rw [← hb]
  change Ideal.Quotient.mk _ (a * b) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _)))

/-- In a Néron situation with uniformizer `π`, smoothness of `A` over `R` at `𝔭` together with
separability of the residue-field extension makes the Krull dimension of the closed fibre of the
local ring at `𝔭` a natural number, namely the number of local parameters. -/
private lemma exists_closedFibre_ringKrullDim_eq
    (S : NeronSituation.{u, v, w}) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) :
    ∃ c : ℕ, ringKrullDim ((Localization.AtPrime S.maximalIdealPreimage) ⧸
      Ideal.span ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} :
        Set (Localization.AtPrime S.maximalIdealPreimage))) = c := by
  obtain ⟨_, _, _, c, _, hc, _, _, _, _, _, _, _, _, _⟩ :=
    exists_local_parameters_of_smoothAt S π hπ hsep hsm
  exact ⟨c, hc⟩

/-- The affine Néron blowup chart `A[𝔭/π]` at a uniformizer `π` of `R`, formed inside the
localization of `A` away from the image of `π`. -/
private abbrev neronChart (S : NeronSituation.{u, v, w}) (π : S.R) : Type w :=
  ↥(affineBlowupAlgebra S.maximalIdealPreimage (algebraMap S.R S.A π)
    (Localization.Away (algebraMap S.R S.A π)))

/-- In a Néron situation with uniformizer `π`, assume `A` is smooth over `R` at `𝔭` and the
residue-field extension is separable. Over the local ring `L` of the chart `A[𝔭/π]` at the prime
induced by `Λ`, the relative differentials of `A` inject into those of the chart, with cokernel
a free module over `L/πL` of rank the dimension `c` of the closed fibre (Stacks 0BJ4). -/
private lemma exists_exact_differentials_localization
    (S : NeronSituation.{u, v, w}) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage)
    (q : Ideal (neronChart S π)) [q.IsPrime]
    (hq : q = Ideal.comap (canonicalNeronBlowupMap S π hπ).1 (IsLocalRing.maximalIdeal S.Λ))
    (L : Type w) [CommRing L] [Algebra (neronChart S π) L]
    [IsLocalization.AtPrime L q] [Algebra S.A L]
    [IsScalarTower S.A (neronChart S π) L] :
    ∃ (c : ℕ) (f : (L ⊗[S.A] Ω[S.A⁄S.R]) →ₗ[L]
        (L ⊗[neronChart S π] Ω[neronChart S π⁄S.R])),
      (∀ (a : L) (x : Ω[S.A⁄S.R]), f (a ⊗ₜ[S.A] x) =
          a ⊗ₜ[neronChart S π] KaehlerDifferential.map S.R S.R S.A (neronChart S π) x) ∧
        Function.Injective f ∧
        ∃ _g : (L ⊗[neronChart S π] Ω[neronChart S π⁄S.R]) →ₗ[L] (Fin c →
            L ⧸ Ideal.span
              ({algebraMap (neronChart S π) L (algebraMap S.R (neronChart S π) π)} : Set L)),
          Function.Exact f _g := by
  obtain ⟨c, hc⟩ := exists_closedFibre_ringKrullDim_eq S π hπ hsep hsm
  obtain ⟨f, hf, g, hzero, hex⟩ :=
    @affineBlowup_differentials_shortExact S π hπ hsep hsm c hc q inferInstance hq L
      (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance)
  have hExact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) hzero)).mp hex.exact
  have hInjective := (ModuleCat.mono_iff_injective (ModuleCat.ofHom f)).mp hex.mono_f
  simp only [ModuleCat.hom_ofHom] at hExact hInjective
  exact ⟨c, f, hf, hInjective, g, hExact⟩

/-- The canonical map `A[𝔭/π] → Λ` is the only ring map out of the chart extending `A → Λ`:
the image of `π` is a non-zero-divisor in `Λ`, and every element of the chart is a fraction with
a power of it as denominator. -/
private lemma eq_canonicalNeronBlowupMap (S : NeronSituation.{u, v, w}) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (ξ : neronChart S π →+* S.Λ)
    (hξ : ∀ x : S.A, ξ (algebraMap S.A (neronChart S π) x) = algebraMap S.A S.Λ x) :
    ξ = (canonicalNeronBlowupMap S π hπ).1 := by
  have hcanon (x : S.A) :
      (canonicalNeronBlowupMap S π hπ).1 (algebraMap S.A (neronChart S π) x) =
        algebraMap S.A S.Λ x :=
    congrArg (fun h : S.A →+* S.Λ => h x) (canonicalNeronBlowupMap S π hπ).2
  symm
  apply ringHom_ext_subalgebra_localization (algebraMap S.R S.A π) _
    (canonicalNeronBlowupMap S π hπ).1 ξ
  · apply IsRegular.of_ne_zero
    rw [hcanon, ← IsScalarTower.algebraMap_apply S.R S.A S.Λ]
    exact algebraMap_uniformizer_ne_zero S hπ
  · intro x
    rw [hcanon, hξ]

/-- In a Néron situation with uniformizer `π`, suppose `A` is smooth over `R` at `𝔭`, the
residue-field extension is separable and `Ω_{A/R}` is free, and let `L` be the local ring of the
chart `A[𝔭/π]` at the prime induced by `Λ`, with `L → Λ` extending `A[𝔭/π] → Λ`. Then the
base-change map `Λ ⊗_A Ω_{A/R} → Λ ⊗_{A[𝔭/π]} Ω_{A[𝔭/π]/R}` is injective and admits a section up
to the factor `π`, because the differential sequence over `L` has cokernel killed by `π`. -/
private lemma exists_differential_section_of_lift
    (S : NeronSituation.{u, v, w}) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage)
    [Module.Free S.A Ω[S.A⁄S.R]]
    [Algebra (neronChart S π) S.Λ] [IsScalarTower S.A (neronChart S π) S.Λ]
    [IsScalarTower S.R (neronChart S π) S.Λ]
    (q : Ideal (neronChart S π)) [q.IsPrime]
    (hq : q = Ideal.comap (canonicalNeronBlowupMap S π hπ).1 (IsLocalRing.maximalIdeal S.Λ))
    (L : Type w) [CommRing L] [Algebra (neronChart S π) L]
    [IsLocalization.AtPrime L q] [Algebra S.A L] [Algebra S.R L] [Algebra L S.Λ]
    [IsScalarTower S.A (neronChart S π) L] [IsScalarTower S.R (neronChart S π) L]
    [IsScalarTower (neronChart S π) L S.Λ] :
    Function.Injective (differentialBaseChangeMap S.R S.A (neronChart S π) S.Λ) ∧
      ∃ v : (S.Λ ⊗[neronChart S π] Ω[neronChart S π⁄S.R]) →ₗ[S.Λ]
          (S.Λ ⊗[S.A] Ω[S.A⁄S.R]),
        ∀ x, differentialBaseChangeMap S.R S.A (neronChart S π) S.Λ (v x) =
          algebraMap S.R S.Λ π • x := by
  have hπΛ := algebraMap_uniformizer_ne_zero S hπ
  obtain ⟨c, floc, hfloc, hInjective, gloc, hExact⟩ :=
    exists_exact_differentials_localization S π hπ hsep hsm q hq L
  have : IsScalarTower S.A L S.Λ := isScalarTower_of_trans (B := neronChart S π)
  have : IsScalarTower S.R L S.Λ := isScalarTower_of_trans (B := neronChart S π)
  have hQ : ∀ z : Fin c → L ⧸ Ideal.span
      ({algebraMap (neronChart S π) L (algebraMap S.R (neronChart S π) π)} : Set L),
      algebraMap S.R L π • z = 0 := by
    rw [show algebraMap S.R L π =
      algebraMap (neronChart S π) L (algebraMap S.R (neronChart S π) π) from
      IsScalarTower.algebraMap_apply S.R (neronChart S π) L π]
    exact smul_pi_quotient_span_singleton_eq_zero _ c
  have hπLΛ : algebraMap L S.Λ (algebraMap S.R L π) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply S.R L S.Λ]
    exact hπΛ
  exact exists_differential_section_of_exact π hπLΛ floc hfloc gloc hExact hInjective hQ

/-- In a Néron situation with uniformizer `π`, suppose `A` is smooth over `R` at `𝔭`, the
residue-field extension is separable, `Ω_{A/R}` is free, and the chart `A[𝔭/π]` carries the
canonical map to `Λ`. Then the base-change map `Λ ⊗_A Ω_{A/R} → Λ ⊗_{A[𝔭/π]} Ω_{A[𝔭/π]/R}` is
injective and admits a section up to the factor `π`. -/
private lemma exists_differential_section_affineBlowup
    (S : NeronSituation.{u, v, w}) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage)
    [Module.Free S.A Ω[S.A⁄S.R]]
    [Algebra (neronChart S π) S.Λ] [IsScalarTower S.A (neronChart S π) S.Λ]
    [IsScalarTower S.R (neronChart S π) S.Λ]
    (halg : algebraMap (neronChart S π) S.Λ = (canonicalNeronBlowupMap S π hπ).1) :
    Function.Injective (differentialBaseChangeMap S.R S.A (neronChart S π) S.Λ) ∧
      ∃ v : (S.Λ ⊗[neronChart S π] Ω[neronChart S π⁄S.R]) →ₗ[S.Λ]
          (S.Λ ⊗[S.A] Ω[S.A⁄S.R]),
        ∀ x, differentialBaseChangeMap S.R S.A (neronChart S π) S.Λ (v x) =
          algebraMap S.R S.Λ π • x := by
  let A' := neronChart S π
  let ψ : A' →+* S.Λ := (canonicalNeronBlowupMap S π hπ).1
  let q : Ideal A' := Ideal.comap ψ (IsLocalRing.maximalIdeal S.Λ)
  have hq : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨ψloc, hψloc⟩ := exists_map_localizationAtPrime_to_local ψ
  let L := Localization.AtPrime q
  let : Algebra L S.Λ := ψloc.toAlgebra
  let : IsScalarTower A' L S.Λ := IsScalarTower.of_algebraMap_eq fun z => by
    change algebraMap A' S.Λ z = ψloc (algebraMap A' L z)
    rw [hψloc z, halg]
  exact @exists_differential_section_of_lift S π hπ hsep hsm _ _ _ _ q hq rfl L
    (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance)
    (inferInstance) (inferInstance) (inferInstance) (inferInstance)

/-- In a Néron situation with uniformizer `π` and separable residue-field extension, if `A` is
smooth over `R` at `𝔭` then the differentials of the chart `A[𝔭/π]` become free after base
change to `Λ`: the chart is smooth over `R` at the prime induced by `Λ` (Stacks 0BJ4), and the
element witnessing that smoothness is a unit in `Λ`. -/
private lemma free_baseChange_differentials_affineBlowup
    (S : NeronSituation.{u, v, w}) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage)
    [Algebra (neronChart S π) S.Λ]
    (halg : algebraMap (neronChart S π) S.Λ = (canonicalNeronBlowupMap S π hπ).1) :
    Module.Free S.Λ (S.Λ ⊗[neronChart S π] Ω[neronChart S π⁄S.R]) := by
  have : FaithfulSMul S.R S.Λ :=
    (faithfulSMul_iff_algebraMap_injective S.R S.Λ).mpr S.extension.1
  obtain ⟨s, hs, hsmLocal⟩ := affineBlowup_smoothAt S π hπ hsep hsm
  have hsunit : IsUnit (algebraMap (neronChart S π) S.Λ s) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    rw [halg]
    exact hs
  exact @free_baseChange_differentials_of_smooth_localization S.R (neronChart S π) S.Λ
    _ _ _ _ _ _ s hsunit hsmLocal

/-- In a Néron situation with uniformizer `π`, let `φ : B' → C` be a ring map out of an
`A`-algebra `B'` over `Λ` under which the image of `π` is regular and the image of `𝔭` is
divisible by `π`, and let `u`, `v` compare the relative differentials of `A` and `B'` with
`u ∘ v` multiplication by `π`. Then an element of an ideal `I ⊆ Ker(A → Λ)` that dies under `φ`
and whose differential vanishes over the residue field at `𝔭` has its differential in `π` times
the image under `v` of the differential relations of `Ker φ`. -/
private lemma exists_relation_of_smul_mem_differentialRelations
    (S : NeronSituation.{u, v, w}) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage)
    {B' C : Type*} [CommRing B'] [CommRing C] [Algebra S.R B'] [Algebra S.A B']
    [IsScalarTower S.R S.A B'] [Algebra B' S.Λ] [IsScalarTower S.A B' S.Λ]
    [IsScalarTower S.R B' S.Λ]
    (φ : B' →+* C) (hφ : IsRegular (φ (algebraMap S.R B' π)))
    (hpmap : Ideal.map (algebraMap S.A B') S.maximalIdealPreimage ≤
      Ideal.span {algebraMap S.R B' π})
    (u : (S.Λ ⊗[S.A] Ω[S.A⁄S.R]) →ₗ[S.Λ] (S.Λ ⊗[B'] Ω[B'⁄S.R]))
    (v : (S.Λ ⊗[B'] Ω[B'⁄S.R]) →ₗ[S.Λ] (S.Λ ⊗[S.A] Ω[S.A⁄S.R]))
    (huinj : Function.Injective u)
    (hu : ∀ x : S.A, u ((1 : S.Λ) ⊗ₜ[S.A] KaehlerDifferential.D S.R S.A x) =
      (1 : S.Λ) ⊗ₜ[B'] KaehlerDifferential.D S.R B' (algebraMap S.A B' x))
    (huv : ∀ x, u (v x) = algebraMap S.R S.Λ π • x)
    (I : Ideal S.A) (hIΛ : ∀ z ∈ I, algebraMap S.A S.Λ z = 0)
    (hIφ : ∀ z ∈ I, φ (algebraMap S.A B' z) = 0)
    (hle : differentialRelations S.R S.A S.Λ I ≤
      (differentialRelations S.R B' S.Λ (RingHom.ker φ)).map v)
    [Module.Finite S.A Ω[S.A⁄S.R]] [Module.Free S.A Ω[S.A⁄S.R]] :
    ∀ x : S.Λ ⊗[S.A] Ω[S.A⁄S.R],
      algebraMap S.R S.Λ π • x ∈ differentialRelations S.R S.A S.Λ I →
      ∃ y ∈ differentialRelations S.R B' S.Λ (RingHom.ker φ),
        u x = algebraMap S.R S.Λ π • y := by
  have hπΛ := algebraMap_uniformizer_ne_zero S hπ
  have hπmax : IsLocalRing.maximalIdeal S.Λ =
      Ideal.span ({algebraMap S.R S.Λ π} : Set S.Λ) :=
    maximalIdeal_eq_span_algebraMap S π hπ
  have hp : S.maximalIdealPreimage =
      Ideal.comap (algebraMap S.A S.Λ) (Ideal.span {algebraMap S.R S.Λ π}) := by
    rw [← hπmax]
    rfl
  obtain ⟨fchart, hfchart, -, c, gchart, hc, hidealchart, _, _, _, nchart, bchart,
      ech, hechart, hbchart⟩ :=
    exists_local_parameters_of_smoothAt S π hπ hsep hsm
  have hzeroRel : ∀ z ∈ I, (1 : S.maximalIdealPreimage.ResidueField) ⊗ₜ[S.A]
        KaehlerDifferential.D S.R S.A z = 0 →
      (1 : S.Λ) ⊗ₜ[S.A] KaehlerDifferential.D S.R S.A z ∈
        ((differentialRelations S.R B' S.Λ (RingHom.ker φ)).map v).map
          (algebraMap S.R S.Λ π • LinearMap.id) := by
    intro z hz hdz
    obtain ⟨t, ht, htz⟩ := exists_mul_mem_sq_of_residue_differential_eq_zero
      π hπΛ S.maximalIdealPreimage hp hπmax fchart hfchart gchart hidealchart bchart ech
      hechart hbchart (hIΛ z hz) hdz
    exact differential_mem_smul_relations_of_mul_mem_sq φ S.maximalIdealPreimage rfl π hφ
      hpmap u v huinj hu huv z (hIΛ z hz) (hIφ z hz) t ht htz
  intro x hx
  obtain ⟨y, hy, rfl⟩ := differentialRelations_saturated_of_residue_kernel
    S.maximalIdealPreimage I rfl (fun z hz => hIΛ z hz) (algebraMap S.R S.Λ π) hπmax
    (smul_right_injective _ hπΛ)
    (((differentialRelations S.R B' S.Λ (RingHom.ker φ))).map v) hle hzeroRel x hx
  exact ⟨y, hy, huv y⟩

/-- The torsion length of `Λ ⊗_{A'} Ω_{A'/R}` drops strictly at an affine Néron blowup, as long
as it is non-zero: the differential relations of two polynomial presentations, one for the stage
and one for its blowup, are compared through the short exact sequence of Stacks 0BJ4. -/
private lemma torsion_length_blowup_lt
    (S : NeronSituation.{u, v, w}) (X : NeronStage S)
    [Module.Flat S.R X.A] [Algebra.FiniteType S.R X.A]
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (π : S.R) (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hpos :
      (Module.length S.Λ (Submodule.torsion S.Λ (S.Λ ⊗[X.A] Ω[X.A⁄S.R]))).toNat ≠ 0) :
    (Module.length S.Λ (Submodule.torsion S.Λ
        (S.Λ ⊗[(NeronStage.blowup S X π hπ).A]
          Ω[(NeronStage.blowup S X π hπ).A⁄S.R]))).toNat <
      (Module.length S.Λ (Submodule.torsion S.Λ (S.Λ ⊗[X.A] Ω[X.A⁄S.R]))).toNat := by
  let Y := NeronStage.blowup S X π hπ
  have hπ0 : π ≠ 0 := uniformizer_ne_zero hπ
  have : Module.Flat S.R Y.A := flat_neronStage_blowup S X π hπ
  have : Algebra.FiniteType S.R Y.A := finiteType_neronStage_blowup S X π hπ
  obtain ⟨m, f, hf⟩ := exists_finite_polynomial_presentation (R := S.R) (A := X.A)
  let P := MvPolynomial (Fin m) S.R
  let : Algebra P X.A := f.toRingHom.toAlgebra
  let : IsScalarTower S.R P X.A :=
    IsScalarTower.of_algebraMap_eq (R := S.R) (S := P) (A := X.A)
      fun r => (f.commutes r).symm
  let : Algebra P S.Λ := ((algebraMap X.A S.Λ).comp f.toRingHom).toAlgebra
  let : IsScalarTower P X.A S.Λ := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower S.R P S.Λ := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap S.R S.Λ r = algebraMap X.A S.Λ (f (algebraMap S.R P r))
    rw [f.commutes r]
    exact IsScalarTower.algebraMap_apply S.R X.A S.Λ r
  let SP : NeronSituation.{u, v, u} := S.withIntermediate P
  have : SP.maximalIdealPreimage.IsPrime := NeronSituation.isPrime_maximalIdealPreimage SP
  let pX : Ideal X.A := X.maximalIdealPreimage
  let pP : Ideal P := SP.maximalIdealPreimage
  have hpP : pP = pX.comap f := by
    ext z
    change algebraMap P S.Λ z ∈ IsLocalRing.maximalIdeal S.Λ ↔ f z ∈ pX
    rfl
  obtain ⟨F, hF, hFcomp, hkernelDivision, hclear⟩ :=
    exists_surjective_affineBlowup_map_kernel_division f hf pX pP hpP π hπ0
  let P' := affineBlowupAlgebra pP (algebraMap S.R P π)
    (Localization.Away (algebraMap S.R P π))
  let j : X.A →+* Y.A := algebraMap X.A
    (affineBlowupAlgebra pX (algebraMap S.R X.A π)
      (Localization.Away (algebraMap S.R X.A π)))
  let : Algebra P' Y.A := F.toRingHom.toAlgebra
  let : IsScalarTower S.R P' Y.A :=
    IsScalarTower.of_algebraMap_eq fun r => (F.commutes r).symm
  have hsurjF : Function.Surjective (algebraMap P' Y.A) := hF
  have hregularπ : IsRegular (algebraMap S.R Y.A π) :=
    isRegular_algebraMap_of_isTorsionFree hπ0
  have hFregular : IsRegular (F (algebraMap S.R P' π)) := by
    rw [show F (algebraMap S.R P' π) = algebraMap S.R Y.A π from F.commutes π]
    exact hregularπ
  let : Algebra P' S.Λ := ((algebraMap Y.A S.Λ).comp F.toRingHom).toAlgebra
  let : IsScalarTower P' Y.A S.Λ := IsScalarTower.of_algebraMap_eq' rfl
  let φ := canonicalNeronBlowupMap (NeronStage.toNeronSituation S X) π hπ
  have hjΛ (z : X.A) : algebraMap Y.A S.Λ (j z) = algebraMap X.A S.Λ z :=
    congrArg (fun q : X.A →+* S.Λ => q z) φ.2
  let : IsScalarTower P P' S.Λ := IsScalarTower.of_algebraMap_eq fun z => by
    change algebraMap X.A S.Λ (f z) = algebraMap Y.A S.Λ (F (algebraMap P P' z))
    rw [show F (algebraMap P P' z) = j (f z) from hFcomp z, hjΛ]
  let : IsScalarTower S.R P' S.Λ := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap S.R S.Λ r = algebraMap Y.A S.Λ (F (algebraMap S.R P' r))
    rw [F.commutes r]
    exact IsScalarTower.algebraMap_apply S.R Y.A S.Λ r
  have hπΛ := algebraMap_uniformizer_ne_zero S hπ
  let u : (S.Λ ⊗[P] Ω[P⁄S.R]) →ₗ[S.Λ] (S.Λ ⊗[P'] Ω[P'⁄S.R]) :=
    differentialBaseChangeMap S.R P P' S.Λ
  have hu (z : P) : u ((1 : S.Λ) ⊗ₜ[P] KaehlerDifferential.D S.R P z) =
      (1 : S.Λ) ⊗ₜ[P'] KaehlerDifferential.D S.R P' (algebraMap P P' z) := by
    rw [differentialBaseChangeMap_tmul, KaehlerDifferential.map_D]
  have hgen : differentialRelations S.R P' S.Λ (RingHom.ker (algebraMap P' Y.A)) ≤
      torsionSaturation ((differentialRelations S.R P S.Λ
        (RingHom.ker (algebraMap P X.A))).map u) :=
    differentialRelations_le_torsionSaturation_map
      (RingHom.ker (algebraMap P X.A)) (RingHom.ker (algebraMap P' Y.A)) π hπΛ u hu
      hclear
  have hsmP : Algebra.SmoothAt S.R P SP.maximalIdealPreimage := by
    have : Algebra.Smooth S.R P := ⟨inferInstance, inferInstance⟩
    exact smoothAt_maximalIdealPreimage_of_smooth SP
  have hsepSP : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ SP.residueFieldExtension := hsep
  have hψeq : algebraMap P' S.Λ = (canonicalNeronBlowupMap SP π hπ).1 :=
    eq_canonicalNeronBlowupMap SP π hπ (algebraMap P' S.Λ)
      fun z => (IsScalarTower.algebraMap_apply P P' S.Λ z).symm
  obtain ⟨huinj, v, huv⟩ :=
    exists_differential_section_affineBlowup SP π hπ hsepSP hsmP hψeq
  have hle : differentialRelations S.R P S.Λ (RingHom.ker (algebraMap P X.A)) ≤
      (differentialRelations S.R P' S.Λ
        (RingHom.ker (algebraMap P' Y.A))).map v :=
    differentialRelations_le_map_of_division
      (RingHom.ker (algebraMap P X.A)) (RingHom.ker (algebraMap P' Y.A)) π u v
      huinj hu huv hkernelDivision
  have : Module.Free S.Λ (S.Λ ⊗[P'] Ω[P'⁄S.R]) :=
    free_baseChange_differentials_affineBlowup SP π hπ hsepSP hsmP hψeq
  have : Module.Flat S.Λ (S.Λ ⊗[P'] Ω[P'⁄S.R]) := Module.Flat.of_free
  have : Module.IsTorsionFree S.Λ (S.Λ ⊗[P'] Ω[P'⁄S.R]) := Module.Flat.isTorsionFree
  have hπmax : IsLocalRing.maximalIdeal S.Λ =
      Ideal.span ({algebraMap S.R S.Λ π} : Set S.Λ) :=
    maximalIdeal_eq_span_algebraMap S π hπ
  have hIΛ : RingHom.ker (algebraMap P X.A) ≤
      RingHom.ker (algebraMap P S.Λ) := by
    intro z hz
    change f z = 0 at hz
    change algebraMap X.A S.Λ (f z) = 0
    rw [hz, map_zero]
  have hpmap : Ideal.map (algebraMap P P') SP.maximalIdealPreimage ≤
      Ideal.span {algebraMap S.R P' π} := by
    rw [IsScalarTower.algebraMap_apply S.R P P' π]
    exact map_ideal_le_span_affineBlowup pP (algebraMap S.R P π)
  have hdiv := exists_relation_of_smul_mem_differentialRelations SP π hπ hsepSP hsmP
    F.toRingHom hFregular hpmap u v huinj hu huv (RingHom.ker (algebraMap P X.A))
    (fun z hz => hIΛ hz) (fun z hz => by
      change F (algebraMap P P' z) = 0
      rw [hFcomp, show f z = 0 from hz, map_zero]) hle
  exact torsion_length_differentials_lt_of_comparison hf hsurjF
    (algebraMap S.R S.Λ π) hπmax hπΛ u v huinj huv hle hgen hdiv hpos

/-! ## Néron's desingularization -/

/-- **Stacks 0BJ6.** In a Néron situation, if `A` is smooth over `R` at the generic prime
`𝔮 = Ker(A → Λ)` and the residue-field extension `κ(R) → κ(Λ)` is separable, then finitely many
affine Néron blowups produce a stage that is smooth over `R` at its distinguished prime
`𝔭 = (· → Λ)^{-1}(𝔪_Λ)`. -/
@[stacks 0BJ6]
theorem exists_finite_affineNeronBlowup_smoothAt
    (S : NeronSituation.{u, v, w})
    (hsm : Algebra.SmoothAt S.R S.A S.kernelIdeal)
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension) :
    ∃ T : NeronStage S,
      Relation.ReflTransGen (IsAffineNeronBlowup S) (NeronStage.initial S) T ∧
        Algebra.SmoothAt S.R T.A T.maximalIdealPreimage := by
  let defect (X : NeronStage S) : ℕ :=
    (Module.length S.Λ (Submodule.torsion S.Λ (S.Λ ⊗[X.A] Ω[X.A⁄S.R]))).toNat
  have H (n : ℕ) : ∀ X : NeronStage S, defect X = n →
      Module.Flat S.R X.A → Algebra.FiniteType S.R X.A →
      Algebra.SmoothAt S.R X.A X.kernelIdeal →
      ∃ T : NeronStage S, Relation.ReflTransGen (IsAffineNeronBlowup S) X T ∧
        Algebra.SmoothAt S.R T.A T.maximalIdealPreimage := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hn hflat hft hgeneric
      by_cases hz : defect X = 0
      · have : Module.Finite S.Λ (S.Λ ⊗[X.A] Ω[X.A⁄S.R]) := inferInstance
        have hfree : Module.Free S.Λ (S.Λ ⊗[X.A] Ω[X.A⁄S.R]) :=
          torsion_length_toNat_eq_zero_iff_free.mp hz
        exact ⟨X, Relation.ReflTransGen.refl,
          smoothAt_of_free_differentials (NeronStage.toNeronSituation S X) hgeneric hfree⟩
      · obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible S.R
        have hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R) :=
          hπirr.maximalIdeal_eq
        let Y := NeronStage.blowup S X π hπ
        have hstep : IsAffineNeronBlowup S X Y := isAffineNeronBlowup_blowup S X π hπ
        have : Module.Flat S.R Y.A := flat_neronStage_blowup S X π hπ
        have : Algebra.FiniteType S.R Y.A := finiteType_neronStage_blowup S X π hπ
        have hgenericY : Algebra.SmoothAt S.R Y.A Y.kernelIdeal :=
          smoothAt_kernelIdeal_neronStage_blowup S X π hπ hgeneric
        have hdec : defect Y < defect X := torsion_length_blowup_lt S X hsep π hπ hz
        obtain ⟨T, hYT, hT⟩ := ih (defect Y) (by omega) Y rfl
          inferInstance inferInstance hgenericY
        exact ⟨T, Relation.ReflTransGen.head hstep hYT, hT⟩
  exact H (defect (NeronStage.initial S)) (NeronStage.initial S) rfl S.flat
    S.finiteType hsm

end Stacks.Smoothing

end
