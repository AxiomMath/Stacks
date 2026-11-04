module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppConstantNumeratorFamily
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedResidueAbsorption
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationTower

open Stacks.DegreePExtensionLevel
open Stacks.DiscreteValuationRing.EppLevelInduction

/-!
# Prime-degree input: conjugate factors and reduced-factor packages

Weak unramifiedness of conjugate factors over a perfect-residue integral model, the re-entered
constant-Laurent branch, and the Artin-Schreier and cyclotomic factor packages obtained from
matching reduced factors.
-/

@[expose] public section

open IsLocalRing
open IsDiscreteValuationRing
open scoped TensorProduct

namespace Stacks.EppTheorem

universe u v w uΩ

/-- **A weakly-unramified lower layer remains weakly unramified at every conjugate factor.**

The base DVR `R` is an arbitrary integral model of the finite field extension `K₁ / K`, not
definitionally `integralClosure A K₁`.  The canonical base change of `A → B` is a weak solution
because `ResidueField A` is perfect.  Its factor criterion gives weak unramifiedness over
`integralClosure A K₁`; the final step transports that statement across the canonical
integral-closure equivalence `integralClosure A K₁ ≃ R`.

This is the lower-ring input required when the constant Laurent branch is re-entered in every
conjugate factor after shared residue absorption. -/
theorem isWeaklyUnramified_integralClosure_factor_of_perfectResidue
    (A B K L K₁ R : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [HenselianLocalRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsDiscreteValuationRing.IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R] [IsDiscreteValuationRing.IsExtension A R]
    [Algebra R K₁] [IsFractionRing R K₁] [IsScalarTower A R K₁]
    [IsAdicComplete (maximalIdeal A) A]
    [IsAdicComplete (maximalIdeal B) B]
    [PerfectField (ResidueField A)]
    (hweak : IsDiscreteValuationRing.IsWeaklyUnramified A B)
    {n : ℕ} (E : Fin n → Type u)
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Algebra L (E i)]
    [∀ i, Algebra K₁ (E i)] [∀ i, IsScalarTower K L (E i)]
    [∀ i, IsScalarTower K K₁ (E i)] [∀ i, Module.Finite L (E i)]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
      algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x) :
    letI : ∀ i, Algebra B (E i) := fun i =>
      ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
    letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra A (E i) := fun i =>
      ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
    letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra R (E i) := fun i =>
      ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
    letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, FaithfulSMul R (E i) := fun i =>
      (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
        ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
    letI : ∀ i, IsScalarTower A R (E i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun a =>
        (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E
          decomp hleft hright i a).trans
          (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
    letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
      isDiscreteValuationRing_integralClosure_factor B L (E i)
    letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
      algebraIntegralClosureBase A B R (E i)
    letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
      isExtension_base_integralClosure_factor A B R L (E i)
    ∀ i, IsDiscreteValuationRing.IsWeaklyUnramified R (integralClosure B (E i)) := by
  let : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, FaithfulSMul R (E i) := fun i =>
    (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
      ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
  let : ∀ i, IsScalarTower A R (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a =>
      (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E
        decomp hleft hright i a).trans
        (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
  let : ∀ i, IsScalarTower A K₁ (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a =>
      algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E
        decomp hleft hright i a
  let : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (E i)
  let : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
    algebraIntegralClosureBase A B R (E i)
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (E i)
  let D := IsDiscreteValuationRing.canonicalBaseChange A B K L K₁
  have hD : D.IsWeakSolution :=
    IsDiscreteValuationRing.isWeakSolution_of_isWeaklyUnramified_of_perfect_residueField
      A B K L K₁ D hweak
  let := D.commRingL₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  let e : D.L₁ ≃ₐ[L] ∀ i, E i :=
    { __ := (D.eL₁.trans decomp).toRingEquiv
      commutes' l := by
        ext i
        show decomp (D.eL₁ (algebraMap L D.L₁ l)) i = algebraMap L (E i) l
        rw [D.eL₁_left, hleft] }
  have he : ∀ i x, e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x := by
    intro i x
    show decomp (D.eL₁ (algebraMap K₁ D.L₁ x)) i = algebraMap K₁ (E i) x
    rw [D.eL₁_right, hright]
  let R₀ := integralClosure A K₁
  obtain ⟨hR₀, hAR₀, hR₀fin, hR₀complete, hR₀frac⟩ :=
    IsDiscreteValuationRing.integralClosure_isCompleteDVR A K K₁
  let := hR₀
  let := hAR₀
  let := hR₀fin
  let := hR₀complete
  let := hR₀frac
  let : IsIntegralClosure R A K₁ :=
    IsDiscreteValuationRing.isIntegralClosure_of_isAdicComplete A R K K₁
  let eR : R₀ ≃ₐ[A] R := IsIntegralClosure.equiv A R₀ K₁ R
  intro i
  let S := integralClosure B (E i)
  let : IsDiscreteValuationRing S := isDiscreteValuationRing_integralClosure_factor B L (E i)
  let : Algebra R₀ S := (mapIntegralClosureOfTower A B K₁ (E i)).toRingHom.toAlgebra
  let : Algebra R S := algebraIntegralClosureBase A B R (E i)
  let : IsDiscreteValuationRing.IsExtension R₀ S :=
    (integralClosure_factor_isExtension A B K L K₁ (E i)).choose_spec.choose_spec.1
  let : IsDiscreteValuationRing.IsExtension R S :=
    isExtension_base_integralClosure_factor A B R L (E i)
  have hweak₀ : IsDiscreteValuationRing.IsWeaklyUnramified R₀ S :=
    (IsDiscreteValuationRing.isWeaklyUnramified_iff_ramificationIdx_eq_one R₀ S).mpr
      (IsDiscreteValuationRing.isWeakSolution_factor A B K L K₁ D E e he hD i
        (IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal.isMaximal S))
  apply IsDiscreteValuationRing.isWeaklyUnramified_of_equiv R₀ S R S
    eR.toRingEquiv (RingEquiv.refl S)
  · intro r
    apply Subtype.ext
    show algebraMap K₁ (E i) (r : K₁) =
      algebraMap K₁ (E i) (algebraMap R K₁ (eR r))
    rw [IsIntegralClosure.algebraMap_equiv]
    show algebraMap K₁ (E i) (r : K₁) =
      algebraMap K₁ (E i) ((integralClosure A K₁).subtype r)
    rfl
  · exact hweak₀

/-- **The constant-Laurent endgame for one re-entered conjugate factor.**

The original Laurent presentation lives over `B \subset L`.  After a finite weakly-unramified
extension `A \to R`, a lower conjugate factor has valuation ring `S` and fraction field `E`; its
upper Artin--Schreier factor has valuation ring `T` and fraction field `F`.  The hypotheses
`hrootBase` say that the finitely many perfect-core roots absorbed into the residue field of `R`
have the expected images in the residue field of `S`.

`exists_transported_constant_laurent_data` transports the section, its truncated ring map, and
the Laurent identity from `B` to `S`.  The all-conjugate constant-numerator theorem then produces
a finite extension of `K` solving `R \to T`.  This theorem is deliberately factorwise: the
perfect-residue combiner amalgamates the resulting extension fields only after every factor has
been solved. -/
theorem exists_finite_extension_isWeakSolution_of_reentered_constant_laurent
    (p : ℕ) [Fact p.Prime]
    (A B R S T K L E F : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsLocalRing B]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Field L] [Field E] [Field F]
    [Algebra A B] [Algebra A R] [Algebra A S]
    [Algebra B S] [Algebra B L] [Algebra B E] [Algebra L E]
    [Algebra R S] [Algebra R K] [Algebra S E] [Algebra T F]
    [Algebra K E] [Algebra E F] [Algebra K F]
    [Algebra R E] [Algebra S F] [Algebra R T] [Algebra R F]
    [algST : Algebra S T]
    [IsScalarTower A B S] [IsScalarTower A R S]
    [IsScalarTower B S E] [IsScalarTower B L E]
    [IsScalarTower R S E] [IsScalarTower R K E]
    [IsScalarTower R S T]
    [hSTF : IsScalarTower S T F] [hSEF : IsScalarTower S E F]
    [IsScalarTower R T F] [IsScalarTower R K F]
    [IsScalarTower K E F]
    [IsLocalHom (algebraMap B S)]
    [IsDiscreteValuationRing.IsExtension A R]
    [IsDiscreteValuationRing.IsExtension R S]
    [IsDiscreteValuationRing.IsExtension S T]
    [IsDiscreteValuationRing.IsExtension R T]
    [IsFractionRing R K] [IsFractionRing S E] [IsFractionRing T F]
    [IsAdicComplete (maximalIdeal R) R]
    [IsAdicComplete (maximalIdeal S) S]
    [PerfectField (ResidueField R)]
    [Module.Finite E F]
    [CharP K p]
    (hweakAR : IsDiscreteValuationRing.IsWeaklyUnramified A R)
    (hweakRS : IsDiscreteValuationRing.IsWeaklyUnramified R S)
    (hB : ∀ x : B, algebraMap L E (algebraMap B L x) =
      algebraMap S E (algebraMap B S x))
    (pi : A) (hpi : Irreducible pi) (N : ℕ)
    (lift : ResidueField B → B)
    (hlift : ∀ x, residue B (lift x) = x)
    (liftMod : ResidueField B →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ N)
    (hliftMod : ∀ x, Ideal.Quotient.mk _ (lift x) = liftMod x)
    (coeff rootCoeff : ℕ → ResidueField B)
    (hrootCoeff : ∀ k, k ∈ Finset.range N →
      rootCoeff k ^ (p ^ N) = coeff k)
    (rootBase : ℕ → ResidueField R)
    (hrootBase : ∀ k, k ∈ Finset.range N →
      algebraMap (ResidueField R) (ResidueField S) (rootBase k) =
        IsLocalRing.ResidueField.map (algebraMap B S) (rootCoeff k))
    (xi : L) (b : B)
    (hexp : xi = (∑ k ∈ Finset.range N,
      algebraMap B L (lift (coeff k)) *
        (algebraMap B L (algebraMap A B pi))⁻¹ ^ (N - k)) + algebraMap B L b)
    (zF : F)
    (hzF : zF ^ p - zF = algebraMap E F (algebraMap L E xi))
    (hgenF : Algebra.adjoin E {zF} = ⊤) :
    ∃ (K₂ : Type u) (_ : Field K₂) (_ : Algebra K K₂) (_ : Algebra R K₂)
      (_ : IsScalarTower R K K₂) (_ : Module.Finite K K₂),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} R T K F K₂,
        D.IsWeakSolution := by
  classical
  let : IsLocalHom (algebraMap R S) := inferInstance
  have ht : algebraMap B S (algebraMap A B pi) = algebraMap R S (algebraMap A R pi) := by
    rw [← IsScalarTower.algebraMap_apply A B S, ← IsScalarTower.algebraMap_apply A R S]
  obtain ⟨fS, sigmaS, sqS, hsigmaS, hsqS, hrootCoeffS, hrootBaseS, hexpS⟩ :=
    exists_transported_constant_laurent_data hB p N (algebraMap A R pi)
      (algebraMap A B pi) ht (RingHom.id (ResidueField B)) lift hlift liftMod hliftMod
      coeff rootCoeff hrootCoeff rootBase hrootBase xi b hexp
  let : CharP E p := charP_of_injective_algebraMap (algebraMap K E).injective p
  let : CharP S p := (algebraMap S E).charP (IsFractionRing.injective S E) p
  have hpiR : Irreducible (algebraMap A R pi) :=
    irreducible_algebraMap_of_isWeaklyUnramified hweakAR hpi
  obtain ⟨K₂, hK₂, hKK₂, hRK₂, hRK₂tower, hK₂fin, hsol⟩ :=
    exists_finite_extension_forall_isWeakSolution_of_constant_laurent p (ULift.{u} Unit) R K
      (fun _ => ResidueField B) (fun _ => S) (fun _ => T) (fun _ => E) (fun _ => F)
      (fun _ => hweakRS) N (algebraMap A R pi) hpiR
      (fun _ => fS) (fun _ => sigmaS) (fun _ => hsigmaS)
      (fun _ => sqS) (fun _ => hsqS)
      (fun _ => coeff) (fun _ => rootCoeff) (fun _ => hrootCoeffS)
      (fun _ => rootBase) (fun _ => hrootBaseS)
      (fun _ => algebraMap L E xi) (fun _ => algebraMap B S b) (fun _ => hexpS)
      (fun _ => zF) (fun _ => hzF) (fun _ => hgenF)
  exact ⟨K₂, hK₂, hKK₂, hRK₂, hRK₂tower, hK₂fin, hsol (ULift.up ())⟩

/-- The canonical map `E ⊗[L] M → F` is surjective when `M ⊗[K₀] K → F` is. -/
private theorem surjective_tensorProduct_lift_of_surjective
    {K₀ : Type u} (L E M F K : Type u)
    [Field K₀] [Field L] [Field M] [Field K] [Field E] [Field F]
    [Algebra K₀ M] [Algebra K₀ K] [Algebra M F] [Algebra K F]
    [Algebra L M] [Algebra L E] [Algebra K E] [Algebra E F] [Algebra L F]
    [IsScalarTower L E F] [IsScalarTower L M F] [IsScalarTower K E F]
    (phi : (M ⊗[K₀] K) →+* F)
    (hphi : ∀ m k, phi (m ⊗ₜ[K₀] k) = algebraMap M F m * algebraMap K F k)
    (hphisurj : Function.Surjective phi) :
    Function.Surjective (Algebra.TensorProduct.lift (Algebra.ofId E F)
      (IsScalarTower.toAlgHom L M F) (fun _ _ => .all _ _) : (E ⊗[L] M) →ₐ[E] F) := by
  intro x
  obtain ⟨t, rfl⟩ := hphisurj x
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul m k =>
      refine ⟨algebraMap K E k ⊗ₜ[L] m, ?_⟩
      simp [mul_comm, hphi]
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩

/-- Mapping the defining equation `P(z) = ξ` of a generator along `B → S` and `M → F`. -/
private theorem aeval_map_eq_of_eval₂_eq
    {B S L M E F : Type u}
    [CommRing B] [CommRing S] [Field L] [Field M] [Field E] [Field F]
    [Algebra B L] [Algebra B S] [Algebra S E] [Algebra S F]
    [Algebra L M] [Algebra M F] [Algebra L E] [Algebra E F] [Algebra L F]
    [IsScalarTower S E F] [IsScalarTower L E F] [IsScalarTower L M F]
    (P : Polynomial B) (xi : L) (z : M)
    (hz : Polynomial.eval₂ ((algebraMap L M).comp (algebraMap B L)) z P = algebraMap L M xi)
    (hB : ∀ b : B, algebraMap L E (algebraMap B L b) =
      algebraMap S E (algebraMap B S b)) :
    Polynomial.aeval (algebraMap M F z) (P.map (algebraMap B S)) =
      algebraMap E F (algebraMap L E xi) := by
  have hcoeff :
      ((algebraMap E F).comp (algebraMap S E)).comp (algebraMap B S) =
        ((algebraMap M F).comp (algebraMap L M)).comp (algebraMap B L) := by
    ext b
    change algebraMap E F (algebraMap S E (algebraMap B S b)) =
      algebraMap M F (algebraMap L M (algebraMap B L b))
    rw [← hB]
    exact (IsScalarTower.algebraMap_apply L E F (algebraMap B L b)).symm.trans
      (IsScalarTower.algebraMap_apply L M F (algebraMap B L b))
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, IsScalarTower.algebraMap_eq S E F]
  change Polynomial.eval₂
    (((algebraMap E F).comp (algebraMap S E)).comp (algebraMap B S)) (algebraMap M F z) P = _
  rw [hcoeff]
  have hz' := congrArg (algebraMap M F) hz
  rw [Polynomial.hom_eval₂] at hz'
  exact hz'.trans ((IsScalarTower.algebraMap_apply L M F xi).symm.trans
    (IsScalarTower.algebraMap_apply L E F xi))

/-- **An upper reduced factor inherits the Artin--Schreier presentation.**

The lower factor `E` is already embedded in the upper factor `F`.  Surjectivity of the upper
factor map from `M ⊗[K₀] K` implies surjectivity of `E ⊗[L] M → F`: on a pure tensor, the latter
map contains the image of `M` and the image of `K` through `E`.  The standard
Artin--Schreier factor package can therefore be applied without choosing a new presentation. -/
theorem artinSchreierFactorPackage_of_matching_reducedFactors
    (K₀ L M K E F : Type u)
    [Field K₀] [Field L] [Field M] [Field K] [Field E] [Field F]
    [Algebra K₀ L] [Algebra L M] [Algebra K₀ M]
    [Algebra K₀ K] [Algebra K₀ E] [Algebra K₀ F] [Algebra M F] [Algebra K F]
    [Algebra L E] [Algebra K E] [Algebra E F] [Algebra L F]
    [IsScalarTower K₀ L M] [IsScalarTower K₀ M F]
    [IsScalarTower K₀ K F] [IsScalarTower K₀ K E]
    [IsScalarTower L E F] [IsScalarTower L M F]
    [IsScalarTower K E F]
    (p : ℕ) (hp : p.Prime) [CharP L p]
    (xi : L) (z : M)
    (hz : z ^ p - z = algebraMap L M xi)
    (hgen : Algebra.adjoin L {z} = ⊤)
    (phi : (M ⊗[K₀] K) →+* F)
    (hphi : ∀ m k, phi (m ⊗ₜ[K₀] k) = algebraMap M F m * algebraMap K F k)
    (hphisurj : Function.Surjective phi) :
    let zF := (Algebra.TensorProduct.lift (Algebra.ofId E F)
      (IsScalarTower.toAlgHom L M F) (fun _ _ => .all _ _)) (1 ⊗ₜ[L] z)
    zF ^ p - zF = algebraMap E F (algebraMap L E xi) ∧
      Algebra.adjoin E {zF} = ⊤ ∧
      ∃ hfin : Module.Finite E F,
        letI := hfin
        (Module.finrank E F = 1 ∧ Function.Surjective (algebraMap E F)) ∨
          (Module.finrank E F = p ∧ IsGalois E F) := by
  let q : (E ⊗[L] M) →ₐ[E] F :=
    Algebra.TensorProduct.lift (Algebra.ofId E F)
      (IsScalarTower.toAlgHom L M F) (fun _ _ => .all _ _)
  have hqsurj : Function.Surjective q :=
    surjective_tensorProduct_lift_of_surjective L E M F K phi hphi hphisurj
  exact artinSchreierFactorPackage_of_surjective_tensorProduct L M E F p hp xi z hz hgen q hqsurj

/-- **A matching upper factor inherits a mixed-characteristic finite-level presentation.**

The upper factor is generated by the image of the original cyclotomic generator.  Hence its
degree divides `p`: it is either trivial, or it again has degree `p` and carries the mapped
finite-level presentation.  The latter is the re-entry datum needed by the mixed-characteristic
all-conjugates recursion after a finite residue-field absorption. -/
theorem cyclotomicFiniteLevelFactorPackage_of_matching_reducedFactors
    (K₀ B S L M K E F : Type u)
    [Field K₀] [CommRing B] [CommRing S] [IsDomain B] [IsDomain S]
    [IsDiscreteValuationRing B] [IsDiscreteValuationRing S]
    [Field L] [Field M] [Field K] [Field E] [Field F]
    [Algebra B L] [Algebra B S] [Algebra S E]
    [Algebra K₀ L] [Algebra L M] [Algebra K₀ M]
    [Algebra K₀ K] [Algebra K₀ E] [Algebra K₀ F] [Algebra M F] [Algebra K F]
    [Algebra L E] [Algebra K E] [Algebra E F] [Algebra L F]
    [IsScalarTower K₀ L M] [IsScalarTower K₀ M F]
    [IsScalarTower K₀ K F] [IsScalarTower K₀ K E]
    [IsScalarTower L E F] [IsScalarTower L M F] [IsScalarTower K E F]
    [IsLocalHom (algebraMap B S)]
    [IsFractionRing B L] [IsFractionRing S E]
    [CharZero L]
    (p : ℕ) (hp : p.Prime) [Fact p.Prime]
    [CharP (ResidueField S) p]
    (f : CyclotomicRing p ℤ ℚ →+* B) (P : Polynomial B)
    (hP : intProp f P ∧ quotChar f P ∧ shapeProp f P ∧ funcEq f P)
    [Module.Finite L M]
    (hfinite : Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel B L M p f P)
    (hB : ∀ b : B, algebraMap L E (algebraMap B L b) =
      algebraMap S E (algebraMap B S b))
    (phi : (M ⊗[K₀] K) →+* F)
    (hphi : ∀ m k, phi (m ⊗ₜ[K₀] k) = algebraMap M F m * algebraMap K F k)
    (hphisurj : Function.Surjective phi) :
    let fS := (algebraMap B S).comp f
    let PS := P.map (algebraMap B S)
    ∃ hfin : Module.Finite E F,
      letI := hfin
      (Module.finrank E F = 1 ∧ Function.Surjective (algebraMap E F)) ∨
        (Module.finrank E F = p ∧ IsGalois E F ∧
          Stacks.DegreePExtensionLevel.IsDegreePExtensionOfFiniteLevel S E F p fS PS) := by
  classical
  let q : (E ⊗[L] M) →ₐ[E] F :=
    Algebra.TensorProduct.lift (Algebra.ofId E F)
      (IsScalarTower.toAlgHom L M F) (fun _ _ => .all _ _)
  have hqsurj : Function.Surjective q :=
    surjective_tensorProduct_lift_of_surjective L E M F K phi hphi hphisurj
  rcases hfinite with ⟨_, xi, z, hgen, hz, a, ha, haeq⟩
  let zF : F := q (1 ⊗ₜ[L] z)
  have hzFdef : zF = algebraMap M F z := by simp [zF, q]
  have hgenF : Algebra.adjoin E {zF} = ⊤ :=
    adjoin_eq_top_of_surjective_tensorProduct_factor L E M F z hgen q hqsurj
  let fS := (algebraMap B S).comp f
  let PS := P.map (algebraMap B S)
  have hPS : intProp fS PS ∧ quotChar fS PS ∧ shapeProp fS PS ∧ funcEq fS PS :=
    Stacks.DiscreteValuationRing.EppLevelInduction.cyclotomic_properties_map f P hP (algebraMap B S)
  let : Algebra S F := ((algebraMap E F).comp (algebraMap S E)).toAlgebra
  let : IsScalarTower S E F := IsScalarTower.of_algebraMap_eq' rfl
  have hzF : Polynomial.aeval zF PS = algebraMap E F (algebraMap L E xi) := by
    rw [hzFdef]
    exact aeval_map_eq_of_eval₂_eq P xi z hz hB
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap L E).injective
  obtain ⟨hfinEF, hgalEF, hdiv⟩ :=
    cyclotomic_galois_and_degree S E F p fS PS hPS.1 (algebraMap L E xi) zF hzF hgenF
  let := hfinEF
  rcases (Nat.dvd_prime hp).mp hdiv with hdegreeOne | hdegreeP
  · exact ⟨hfinEF, Or.inl ⟨hdegreeOne,
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdegreeOne).2⟩⟩
  · refine ⟨hfinEF, Or.inr ⟨hdegreeP, hgalEF, hdegreeP, algebraMap L E xi, zF,
      hgenF, hzF, algebraMap B S a, ?_, ?_⟩⟩
    · exact map_nonunit (algebraMap B S) a ha
    · show algebraMap S E (algebraMap B S a) =
        algebraMap S E (wElt fS) ^ p * algebraMap L E xi
      have hw : wElt fS = algebraMap B S (wElt f) := by
        simp only [fS, wElt, zetaA, RingHom.comp_apply, map_sub, map_one]
      have haeq' := congrArg (algebraMap L E) haeq
      rw [hw]
      simpa only [map_mul, map_pow, hB] using haeq'

/-- **A matching reduced factor carries the mapped prepared cyclotomic presentation.**

This is the generator-level companion to
`cyclotomicFiniteLevelFactorPackage_of_matching_reducedFactors`.  It retains the particular
generator and parameter occurring in a prepared level step, rather than merely returning some
witnesses to finite level.  The all-conjugates mixed recursion needs these exact mapped witnesses
to transport the scaled preparation equation into every factor. -/
theorem cyclotomicPresentation_of_matching_reducedFactors
    (K0 B S L M K E F : Type u)
    [Field K0] [CommRing B] [CommRing S] [IsDomain B] [IsDomain S]
    [Field L] [Field M] [Field K] [Field E] [Field F]
    [Algebra B L] [Algebra B M] [Algebra B S] [Algebra S E] [Algebra S F]
    [Algebra K0 L] [Algebra L M] [Algebra K0 M]
    [Algebra K0 K] [Algebra K0 E] [Algebra K0 F] [Algebra M F] [Algebra K F]
    [Algebra L E] [Algebra K E] [Algebra E F] [Algebra L F]
    [IsScalarTower K0 L M] [IsScalarTower K0 M F]
    [IsScalarTower K0 K F] [IsScalarTower K0 K E]
    [IsScalarTower B L M] [IsScalarTower S E F]
    [IsScalarTower L E F] [IsScalarTower L M F] [IsScalarTower K E F]
    (P : Polynomial B) (xi : L) (z : M)
    (hz : Polynomial.aeval z P = algebraMap L M xi)
    (hgen : Algebra.adjoin L {z} = ⊤)
    (hB : ∀ b : B, algebraMap L E (algebraMap B L b) =
      algebraMap S E (algebraMap B S b))
    (phi : (M ⊗[K0] K) →+* F)
    (hphi : ∀ m k, phi (m ⊗ₜ[K0] k) = algebraMap M F m * algebraMap K F k)
    (hphisurj : Function.Surjective phi) :
    let PS := P.map (algebraMap B S)
    let zF := (Algebra.TensorProduct.lift (Algebra.ofId E F)
      (IsScalarTower.toAlgHom L M F) (fun _ _ => .all _ _)) (1 ⊗ₜ[L] z)
    Algebra.adjoin E {zF} = ⊤ ∧
      Polynomial.aeval zF PS = algebraMap E F (algebraMap L E xi) := by
  let q : (E ⊗[L] M) →ₐ[E] F :=
    Algebra.TensorProduct.lift (Algebra.ofId E F)
      (IsScalarTower.toAlgHom L M F) (fun _ _ => .all _ _)
  have hqsurj : Function.Surjective q :=
    surjective_tensorProduct_lift_of_surjective L E M F K phi hphi hphisurj
  let PS := P.map (algebraMap B S)
  let zF : F := q (1 ⊗ₜ[L] z)
  have hzFdef : zF = algebraMap M F z := by simp [zF, q]
  have hgenF : Algebra.adjoin E {zF} = ⊤ :=
    adjoin_eq_top_of_surjective_tensorProduct_factor L E M F z hgen q hqsurj
  refine ⟨hgenF, ?_⟩
  change Polynomial.aeval zF PS = _
  rw [hzFdef]
  refine aeval_map_eq_of_eval₂_eq P xi z ?_ hB
  rwa [Polynomial.aeval_def, IsScalarTower.algebraMap_eq B L M] at hz

end Stacks.EppTheorem

end
