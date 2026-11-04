module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.RingTheory.Polynomial.Ideal
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Homology.PseudoCoherent.Module

@[expose] public section

/-!
# Pseudo-coherence over a polynomial ring and its evaluation at zero

Evaluating a polynomial ring at zero does not change whether a complex is `m`-pseudo-coherent:
an object of `D(R)` is `m`-pseudo-coherent over `R` exactly when its restriction of scalars along
`R[x] → R`, `x ↦ 0`, is `m`-pseudo-coherent over `R[x]`.

## Main results

* `PseudoCoherence.isPseudoCoherentFrom_iff_restrictScalars_polynomial_evalZero` (Stacks 065G).

## Implementation notes

The hypothesis that tag 064Z needs of the ring map is that `R`, as a module over `R[x]` via
evaluation at zero, is pseudo-coherent. That is supplied here by an explicit resolution: `R` sits
in a two-term free resolution `R[x] --·x--> R[x] ↠ R`, whose terms are finite free, so tag 064T's
fourth condition applies. The rest is tag 064Z together with transport along the isomorphism
between the derived image of a termwise restriction and the restriction of the derived image.

Tags 064T and 064Z belong to Chapter 15 section 65; this module cites
`StacksFrontier/Homology/PseudoCoherent/Module.lean` and
`StacksFrontier/Homology/PseudoCoherent/ChangeOfRings.lean` rather than restating either.

## References

* [The Stacks Project, Lemma 15.82.2 (065G)](https://stacks.math.columbia.edu/tag/065G)
-/

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u v

attribute [local instance] HasDerivedCategory.standard

noncomputable section

namespace EvalZeroResolution

variable (R : Type u) [CommRing R]

private abbrev A := Polynomial R

private def ev : A R →+* R :=
  Polynomial.eval₂RingHom (RingHom.id R) 0

private local instance : Module (A R) R := (ev R).toAlgebra.toModule

private abbrev M : ModuleCat.{u} (A R) := ModuleCat.of (A R) R

private def term : ℕ → ModuleCat.{u} (A R)
  | 0 => ModuleCat.of (A R) (A R)
  | 1 => ModuleCat.of (A R) (A R)
  | _ + 2 => ModuleCat.of (A R) (Fin 0 → A R)

private def mulX : A R →ₗ[A R] A R :=
  LinearMap.mulLeft (A R) Polynomial.X

private def differential : (n : ℕ) → term R (n + 1) ⟶ term R n
  | 0 => ModuleCat.ofHom (mulX R)
  | _ + 1 => 0

private lemma differential_sq (n : ℕ) :
    differential R (n + 1) ≫ differential R n = 0 := by
  simp [differential]

private def complex : ChainComplex (ModuleCat.{u} (A R)) ℕ :=
  ChainComplex.of (term R) (differential R) (differential_sq R)

private def augmentationLinear : A R →ₗ[A R] M R where
  toFun := Polynomial.constantCoeff
  map_add' := map_add _
  map_smul' p q := by
    change Polynomial.constantCoeff (p * q) = (ev R p) * Polynomial.constantCoeff q
    simp [ev]

private def augmentation : (complex R).X 0 ⟶ M R :=
  ModuleCat.ofHom (augmentationLinear R)

private lemma constantCoeff_mulX (p : A R) :
    Polynomial.constantCoeff (mulX R p) = 0 := by
  simp [mulX]

private lemma augmentation_condition :
    (complex R).d 1 0 ≫ augmentation R = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun p => constantCoeff_mulX R p)

private def pi : complex R ⟶ (ChainComplex.single₀ (ModuleCat (A R))).obj (M R) :=
  (ChainComplex.toSingle₀Equiv (complex R) (M R)).symm
    ⟨augmentation R, augmentation_condition R⟩

private lemma mulX_injective : Function.Injective (mulX R) := by
  intro p q h
  ext n
  simpa [mulX, Polynomial.coeff_X_mul] using congrArg (fun z : A R ↦ z.coeff (n + 1)) h

private lemma exactAt_one : (complex R).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' (complex R) 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro p hp
  refine ⟨0, ?_⟩
  have hp' : mulX R p = mulX R 0 := by
    change mulX R p = 0 at hp
    simpa using hp
  have : p = 0 := mulX_injective R hp'
  subst p
  simp

private lemma exactAt_succ_succ (n : ℕ) : (complex R).ExactAt (n + 2) := by
  rw [HomologicalComplex.exactAt_iff' (complex R) (n + 3) (n + 2) (n + 1)
    (by simp) (by simp), ShortComplex.moduleCat_exact_iff]
  intro x _
  refine ⟨0, ?_⟩
  funext i
  exact i.elim0

private lemma X_mul_divX_of_constantCoeff_eq_zero (p : A R)
    (hp : Polynomial.constantCoeff p = 0) :
    Polynomial.X * Polynomial.divX p = p := by
  have hp0 : Polynomial.coeff p 0 = 0 := by
    simpa only [Polynomial.constantCoeff_apply] using hp
  simpa only [hp0, Polynomial.C_0, add_zero] using Polynomial.X_mul_divX_add p

private lemma augmentation_exact :
    (ShortComplex.mk ((complex R).d 1 0) (augmentation R)
      (augmentation_condition R)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro p hp
  exact ⟨Polynomial.divX p, X_mul_divX_of_constantCoeff_eq_zero R p hp⟩

private lemma augmentation_epi : Epi (augmentation R) := by
  rw [ModuleCat.epi_iff_surjective]
  intro r
  exact ⟨Polynomial.C r, by change Polynomial.constantCoeff (Polynomial.C r) = r; simp⟩

private lemma quasiIsoAt_zero : QuasiIsoAt (pi R) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff,
    ShortComplex.quasiIso_iff_of_zeros' _ ((complex R).shape 0 0 (by simp))
      (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 (M R) 1 0)
      (HomologicalComplex.single_obj_d (ComplexShape.down ℕ) 0 (M R) 0 0)]
  exact ⟨augmentation_exact R, augmentation_epi R⟩

private instance pi_quasiIso : QuasiIso (pi R) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero => exact quasiIsoAt_zero R
  | succ n =>
      rw [quasiIsoAt_iff_exactAt' (pi R) (n + 1)
        (ChainComplex.exactAt_succ_single_obj (M R) n)]
      cases n with
      | zero => exact exactAt_one R
      | succ n => simpa [Nat.add_assoc] using exactAt_succ_succ R n

private lemma finite_free (n : ℕ) :
    Module.Finite (A R) ((complex R).X n) ∧
      Module.Free (A R) ((complex R).X n) := by
  rcases n with _ | _ | n
  iterate 2
    · change Module.Finite (A R) (A R) ∧ Module.Free (A R) (A R)
      exact ⟨inferInstance, inferInstance⟩
  · change Module.Finite (A R) (Fin 0 → A R) ∧ Module.Free (A R) (Fin 0 → A R)
    exact ⟨inferInstance, inferInstance⟩

private def resolution : FiniteFreeModuleResolution (A R) (M R) where
  complex := complex R
  hasHomology := fun _ => inferInstance
  π := pi R
  quasiIso := inferInstance
  free := fun n => (finite_free R n).2
  finite := fun n => (finite_free R n).1

private lemma modulePseudoCoherent : IsModulePseudoCoherent (R := A R) (M R) :=
  (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small (M R)).2.2.2.mpr ⟨resolution R⟩

end EvalZeroResolution

private lemma pseudoCoherentFrom_of_iso
    {R : Type u} [Ring R] {X Y : DerivedCategory (ModuleCat.{v} R)} {m : ℤ}
    (e : X ≅ Y) (hX : IsPseudoCoherentFrom X m) : IsPseudoCoherentFrom Y m := by
  obtain ⟨E, hE, α, hα, hαm⟩ := hX
  refine ⟨E, hE, α ≫ e.hom, fun i hi => ?_, ?_⟩
  · have := hα i hi
    rw [Functor.map_comp]
    exact IsIso.comp_isIso
  · rw [Functor.map_comp]
    have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map e.hom) :=
      IsIso.epi_of_iso _
    exact epi_comp _ _

/-- **Stacks 065G.** An object of `D(R)` is `m`-pseudo-coherent over `R` if and only if,
after letting `X` act by zero, it is `m`-pseudo-coherent over `R[X]`.

For an object represented by a complex, `Functor.mapDerivedCategoryFactors` identifies the
right-hand object with the localization of that complex after restriction of scalars. -/
@[stacks 065G]
public theorem isPseudoCoherentFrom_iff_restrictScalars_polynomial_evalZero
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (m : ℤ) :
    let ev : Polynomial R →+* R := Polynomial.eval₂RingHom (RingHom.id R) (0 : R)
    IsPseudoCoherentFrom K m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{max u v} ev).mapDerivedCategory.obj K) m := by
  dsimp
  let ev : Polynomial R →+* R := Polynomial.eval₂RingHom (RingHom.id R) 0
  let L := DerivedCategory.Q.objPreimage K
  let e := DerivedCategory.Q.objObjPreimageIso K
  let L' := ((ModuleCat.restrictScalars.{max u v} ev).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L
  have h := (pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars
    ev (EvalZeroResolution.modulePseudoCoherent R) L m).1
  have e' : DerivedCategory.Q.obj L' ≅
      (ModuleCat.restrictScalars.{max u v} ev).mapDerivedCategory.obj K :=
    ((ModuleCat.restrictScalars.{max u v} ev).mapDerivedCategoryFactors.app L).symm ≪≫
      (ModuleCat.restrictScalars.{max u v} ev).mapDerivedCategory.mapIso e
  exact ⟨fun hK => pseudoCoherentFrom_of_iso e' (h.mp (pseudoCoherentFrom_of_iso e.symm hK)),
    fun hK => pseudoCoherentFrom_of_iso e (h.mpr (pseudoCoherentFrom_of_iso e'.symm hK))⟩

end

end PseudoCoherence
