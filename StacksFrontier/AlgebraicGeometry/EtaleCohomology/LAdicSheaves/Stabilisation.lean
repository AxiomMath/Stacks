module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.UnderlyingTower

/-!
# Stabilisation of the Verschiebung kernels, and divisibility of torsion

The transition maps of the underlying tower of an ℓ-adic sheaf exhibit each level as the
quotient of any higher level by `ℓⁿ⁺¹`, and the Verschiebung goes back the other way with both
composites equal to multiplication by `ℓ`. Iterating the Verschiebung out of level `0` gives an
ascending chain of kernels, which must stabilise because the levels are Noetherian objects. The
level at which it stabilises is a uniform bound beyond which a map into a level killed by `ℓᵐ` is
divisible: `ℓⁿ · g` already lands in `ℓⁿ⁺¹` times the level.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.underlyingTransitionLE`: the transition map of the
  underlying tower between two arbitrary levels.
* `Stacks.EtaleCohomology.LAdicSheaf.initialVerschiebung`: the iterated Verschiebung out of
  level `0`.
* `Stacks.EtaleCohomology.LAdicSheaf.underlyingRawKernelι`: the underlying inclusion of a
  levelwise kernel.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.underlyingTransitionLE_isCokernel`: every transition map of
  the underlying tower exhibits the lower level as the quotient by `ℓⁿ⁺¹`.
* `Stacks.EtaleCohomology.LAdicSheaf.initialVerschiebung_kernel_stabilizes`: the kernels of the
  iterated Verschiebung stabilise.
* `Stacks.EtaleCohomology.LAdicSheaf.underlyingLAdic_torsion_divisibility`: beyond that level,
  `ℓⁿ` times a map killed by `ℓᵐ` is divisible by `ℓⁿ⁺¹`.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
* [Stacks Project, Tag 09YV](https://stacks.math.columbia.edu/tag/09YV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

attribute [local instance] underlyingLevelFunctor_additive
  underlyingLevelFunctor_preservesMonomorphisms underlyingLevelFunctor_isLeftAdjoint
  underlyingLevelFunctor_preservesKernels underlyingLevelFunctor_full

/-- The underlying sheaf of abelian groups of a finite level is killed by `ℓⁿ⁺¹`. -/
public theorem underlyingLevelFunctor_annihilated (n : ℕ)
    (P : FiniteLevelSheaf.{u, u + 1} B X ℓ n) :
    (ℓ ^ (n + 1)) • (𝟙 ((underlyingLevelFunctor B X ℓ n).obj P)) = 0 := by
  have h := (underlyingLevelFunctor B X ℓ n).congr_map
    (zmodSheaf_nsmul_id (SmallEtale.topology B X.1 X.property) (ℓ ^ (n + 1)) P)
  simpa only [Functor.map_nsmul, Functor.map_zero,
    (underlyingLevelFunctor B X ℓ n).map_id] using h

variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

attribute [local instance] underlyingLAdicLevel_noetherian

/-- The Verschiebung of the underlying tower, iterated `k` times out of level `n`. -/
public def iteratedUnderlyingVerschiebung (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (k : ℕ) → underlyingLAdicLevel B X ℓ F n ⟶ underlyingLAdicLevel B X ℓ F (n + k)
  | 0 => 𝟙 _
  | k + 1 => iteratedUnderlyingVerschiebung F n k ≫
      underlyingLAdicVerschiebung B X ℓ F (n + k)

/-- The transition map of the underlying tower, iterated `k` times down to level `n`. -/
public def iteratedUnderlyingTransition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (k : ℕ) → underlyingLAdicLevel B X ℓ F (n + k) ⟶ underlyingLAdicLevel B X ℓ F n
  | 0 => 𝟙 _
  | k + 1 => underlyingLAdicTransition B X ℓ F (n + k) ≫
      iteratedUnderlyingTransition F n k

/-- Descending `k` levels and coming back up by the Verschiebung is multiplication by `ℓᵏ`. -/
public theorem iteratedUnderlyingTransition_verschiebung (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (n k : ℕ) :
    iteratedUnderlyingTransition B X ℓ F n k ≫ iteratedUnderlyingVerschiebung B X ℓ F n k =
      (ℓ ^ k) • (𝟙 (underlyingLAdicLevel B X ℓ F (n + k))) := by
  induction k with
  | zero => simp [iteratedUnderlyingTransition, iteratedUnderlyingVerschiebung]
  | succ k hk =>
    show (underlyingLAdicTransition B X ℓ F (n + k) ≫
        iteratedUnderlyingTransition B X ℓ F n k) ≫
      (iteratedUnderlyingVerschiebung B X ℓ F n k ≫
        underlyingLAdicVerschiebung B X ℓ F (n + k)) = _
    rw [Category.assoc, ← Category.assoc (iteratedUnderlyingTransition B X ℓ F n k), hk,
      Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
      underlyingLAdicTransition_verschiebung, smul_smul, pow_succ]
    rfl

/-- Going up `k` levels by the Verschiebung and coming back down is multiplication by `ℓᵏ`. -/
public theorem iteratedUnderlyingVerschiebung_transition (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (n k : ℕ) :
    iteratedUnderlyingVerschiebung B X ℓ F n k ≫ iteratedUnderlyingTransition B X ℓ F n k =
      (ℓ ^ k) • (𝟙 (underlyingLAdicLevel B X ℓ F n)) := by
  induction k with
  | zero => simp [iteratedUnderlyingTransition, iteratedUnderlyingVerschiebung]
  | succ k hk =>
    show (iteratedUnderlyingVerschiebung B X ℓ F n k ≫
        underlyingLAdicVerschiebung B X ℓ F (n + k)) ≫
      (underlyingLAdicTransition B X ℓ F (n + k) ≫
        iteratedUnderlyingTransition B X ℓ F n k) = _
    rw [Category.assoc, ← Category.assoc (underlyingLAdicVerschiebung B X ℓ F (n + k)),
      underlyingLAdicVerschiebung_transition, Preadditive.nsmul_comp, Category.id_comp,
      Preadditive.comp_nsmul, hk, smul_smul, pow_succ']

/-- The kernels of the iterated Verschiebung increase with the number of iterations. -/
public theorem verschiebungKernel_monotone (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    Monotone (fun k => kernelSubobject (iteratedUnderlyingVerschiebung B X ℓ F n k)) :=
  monotone_nat_of_le_succ fun _ => kernelSubobject_comp_le _ _

/-- The kernels of the iterated Verschiebung out of level `n` stabilise. -/
public theorem verschiebungKernel_stabilizes (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    ∃ c : ℕ, ∀ k : ℕ, c ≤ k →
      kernelSubobject (iteratedUnderlyingVerschiebung B X ℓ F n c) =
        kernelSubobject (iteratedUnderlyingVerschiebung B X ℓ F n k) :=
  monotone_chain_condition_of_isNoetherianObject ⟨_, verschiebungKernel_monotone B X ℓ F n⟩

/-- Each level of the underlying tower is killed by `ℓⁿ⁺¹`. -/
public theorem underlyingLAdicLevel_annihilated (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (ℓ ^ (n + 1)) • (𝟙 (underlyingLAdicLevel B X ℓ F n)) = 0 :=
  underlyingLevelFunctor_annihilated B X ℓ n (F.level n)

/-- A map out of an object into level `n` of the underlying tower kills `ℓⁿ⁺¹` when
precomposed with multiplication by `ℓⁿ⁺¹`. -/
private theorem nsmul_id_comp_eq_zero (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ)
    {A : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1}}
    (t : A ⟶ underlyingLAdicLevel B X ℓ F n) :
    ((ℓ ^ (n + 1)) • (𝟙 A)) ≫ t = 0 := by
  simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp, Category.comp_id, comp_zero] using
    congrArg (fun q => t ≫ q) (underlyingLAdicLevel_annihilated B X ℓ F n)

/-- The transition map of the underlying tower kills `ℓⁿ⁺¹`. -/
public theorem underlyingTransition_condition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    ((ℓ ^ (n + 1)) • (𝟙 (underlyingLAdicLevel B X ℓ F (n + 1)))) ≫
      underlyingLAdicTransition B X ℓ F n = 0 := by
  exact nsmul_id_comp_eq_zero B X ℓ F n _

/-- The transition map of the underlying tower exhibits level `n` as the quotient of level
`n + 1` by `ℓⁿ⁺¹`. -/
public def underlyingTransition_isCokernel (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (underlyingLAdicTransition B X ℓ F n)
      (underlyingTransition_condition B X ℓ F n)) :=
  mapNsmulCokernel (underlyingLevelFunctor B X ℓ (n + 1))
    (ℓ ^ (n + 1)) (F.transition n) (transition_condition F n) (transition_isCokernel F n)

/-- The iterated transition map kills `ℓⁿ⁺¹`. -/
public theorem iteratedUnderlyingTransition_condition (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (n k : ℕ) :
    ((ℓ ^ (n + 1)) • (𝟙 (underlyingLAdicLevel B X ℓ F (n + k)))) ≫
      iteratedUnderlyingTransition B X ℓ F n k = 0 := by
  exact nsmul_id_comp_eq_zero B X ℓ F n _

/-- The iterated transition map exhibits level `n` as the quotient of level `n + k` by
`ℓⁿ⁺¹`. -/
public def iteratedUnderlyingTransition_isCokernel (F : LAdicSheaf.{u, u + 1} B X ℓ) (n k : ℕ) :
    IsColimit (CokernelCofork.ofπ (iteratedUnderlyingTransition B X ℓ F n k)
      (iteratedUnderlyingTransition_condition B X ℓ F n k)) := by
  induction k with
  | zero =>
    exact CokernelCofork.IsColimit.ofId _ (underlyingLAdicLevel_annihilated B X ℓ F n)
  | succ k hk =>
    exact nsmulCokernel_comp (underlyingLAdicTransition B X ℓ F (n + k))
      (iteratedUnderlyingTransition B X ℓ F n k)
      (ℓ ^ (n + k + 1)) (ℓ ^ (n + 1)) (pow_dvd_pow ℓ (by omega))
      (underlyingTransition_condition B X ℓ F (n + k))
      (iteratedUnderlyingTransition_condition B X ℓ F n k)
      (underlyingTransition_isCokernel B X ℓ F (n + k)) hk

/-- The transition map of the underlying tower between two arbitrary levels. -/
public def underlyingTransitionLE (F : LAdicSheaf.{u, u + 1} B X ℓ) {n m : ℕ} (h : n ≤ m) :
    underlyingLAdicLevel B X ℓ F m ⟶ underlyingLAdicLevel B X ℓ F n :=
  (underlyingLAdicTower B X ℓ F).map (homOfLE h).op

/-- Transition maps of the underlying tower compose. -/
public theorem underlyingTransitionLE_comp (F : LAdicSheaf.{u, u + 1} B X ℓ) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    underlyingTransitionLE B X ℓ F hjk ≫ underlyingTransitionLE B X ℓ F hij =
      underlyingTransitionLE B X ℓ F (hij.trans hjk) :=
  towerMap_comp (underlyingLAdicTower B X ℓ F) hij hjk

/-- The one-step transition map of the underlying tower. -/
public theorem underlyingTransitionLE_succ (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    underlyingTransitionLE B X ℓ F (Nat.le_succ n) = underlyingLAdicTransition B X ℓ F n :=
  Functor.ofOpSequence_map_homOfLE_succ _ _

/-- The iterated transition map is the transition map of the tower. -/
public theorem iteratedUnderlyingTransition_eq (F : LAdicSheaf.{u, u + 1} B X ℓ) (n k : ℕ) :
    iteratedUnderlyingTransition B X ℓ F n k =
      underlyingTransitionLE B X ℓ F (Nat.le_add_right n k) := by
  induction k with
  | zero =>
    show 𝟙 _ = (underlyingLAdicTower B X ℓ F).map (𝟙 _)
    exact ((underlyingLAdicTower B X ℓ F).map_id _).symm
  | succ k hk =>
    show underlyingLAdicTransition B X ℓ F (n + k) ≫
      iteratedUnderlyingTransition B X ℓ F n k = _
    rw [hk, ← underlyingTransitionLE_succ, underlyingTransitionLE_comp]

/-- Every transition map of the underlying tower kills `ℓⁿ⁺¹`. -/
public theorem underlyingTransitionLE_condition (F : LAdicSheaf.{u, u + 1} B X ℓ) {n m : ℕ}
    (h : n ≤ m) :
    ((ℓ ^ (n + 1)) • (𝟙 (underlyingLAdicLevel B X ℓ F m))) ≫
      underlyingTransitionLE B X ℓ F h = 0 := by
  exact nsmul_id_comp_eq_zero B X ℓ F n _

/-- Every transition map of the underlying tower exhibits the lower level as the quotient of the
higher one by `ℓⁿ⁺¹`. -/
public def underlyingTransitionLE_isCokernel (F : LAdicSheaf.{u, u + 1} B X ℓ) {n m : ℕ}
    (h : n ≤ m) :
    IsColimit (CokernelCofork.ofπ (underlyingTransitionLE B X ℓ F h)
      (underlyingTransitionLE_condition B X ℓ F h)) :=
  Classical.choice <| by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨(iteratedUnderlyingTransition_isCokernel B X ℓ F n k).ofIsoColimit <|
      Cofork.ext (Iso.refl _) <|
        (Category.comp_id _).trans (iteratedUnderlyingTransition_eq B X ℓ F n k)⟩

/-- Every transition map of the underlying tower is an epimorphism. -/
public theorem underlyingTransitionLE_epi (F : LAdicSheaf.{u, u + 1} B X ℓ) {n m : ℕ}
    (h : n ≤ m) : Epi (underlyingTransitionLE B X ℓ F h) :=
  Cofork.IsColimit.epi (underlyingTransitionLE_isCokernel B X ℓ F h)

attribute [local instance] underlyingTransitionLE_epi

/-- The Verschiebung iterated out of level `0`. -/
public def initialVerschiebung (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    (n : ℕ) → underlyingLAdicLevel B X ℓ F 0 ⟶ underlyingLAdicLevel B X ℓ F n
  | 0 => 𝟙 _
  | n + 1 => initialVerschiebung F n ≫ underlyingLAdicVerschiebung B X ℓ F n

/-- Descending to level `0` and coming back up by the iterated Verschiebung is multiplication by
`ℓⁿ`. -/
public theorem initialVerschiebung_scalar (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    underlyingTransitionLE B X ℓ F (Nat.zero_le n) ≫ initialVerschiebung B X ℓ F n =
      (ℓ ^ n) • (𝟙 (underlyingLAdicLevel B X ℓ F n)) := by
  induction n with
  | zero =>
    simp [initialVerschiebung, underlyingTransitionLE]
    rfl
  | succ n hn =>
    rw [← underlyingTransitionLE_comp B X ℓ F (Nat.zero_le n) (Nat.le_succ n),
      underlyingTransitionLE_succ]
    show (underlyingLAdicTransition B X ℓ F n ≫
      underlyingTransitionLE B X ℓ F (Nat.zero_le n)) ≫
      (initialVerschiebung B X ℓ F n ≫ underlyingLAdicVerschiebung B X ℓ F n) = _
    rw [Category.assoc, ← Category.assoc (underlyingTransitionLE B X ℓ F (Nat.zero_le n)),
      hn, Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
      underlyingLAdicTransition_verschiebung, smul_smul, pow_succ]

/-- The kernels of the Verschiebung iterated out of level `0` stabilise. -/
public theorem initialVerschiebung_kernel_stabilizes (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    ∃ c : ℕ, ∀ k : ℕ, c ≤ k →
      kernelSubobject (initialVerschiebung B X ℓ F c) =
        kernelSubobject (initialVerschiebung B X ℓ F k) :=
  monotone_chain_condition_of_isNoetherianObject
    ⟨_, monotone_nat_of_le_succ fun _ => kernelSubobject_comp_le _ _⟩

/-- Where the Verschiebung kernels have stopped growing between levels `n` and `m`, a map into
level `m` killed by `ℓᵐ` becomes divisible by `ℓⁿ⁺¹` after multiplication by `ℓⁿ`. -/
public theorem torsion_divisibility_of_verschiebung_kernel_eq
    (F : LAdicSheaf.{u, u + 1} B X ℓ) {n m : ℕ} (hnm : n ≤ m)
    (hker : kernelSubobject (initialVerschiebung B X ℓ F n) =
      kernelSubobject (initialVerschiebung B X ℓ F m))
    (A : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
    (g : A ⟶ underlyingLAdicLevel B X ℓ F m) (hg : (ℓ ^ m) • g = 0) :
    ((ℓ ^ n) • g) ≫ cokernel.π ((ℓ ^ (n + 1)) • (𝟙 (underlyingLAdicLevel B X ℓ F m))) = 0 := by
  let g₀ := g ≫ underlyingTransitionLE B X ℓ F (Nat.zero_le m)
  have hg₀m : g₀ ≫ initialVerschiebung B X ℓ F m = 0 := by
    dsimp only [g₀]
    rw [Category.assoc, initialVerschiebung_scalar, Preadditive.comp_nsmul, Category.comp_id, hg]
  have hg₀n : g₀ ≫ initialVerschiebung B X ℓ F n = 0 :=
    (kernelSubobject_factors_iff _ _).1 (hker ▸ kernelSubobject_factors _ _ hg₀m)
  have ht : ((ℓ ^ n) • g) ≫ underlyingTransitionLE B X ℓ F hnm = 0 := by
    dsimp only [g₀] at hg₀n
    rwa [← underlyingTransitionLE_comp B X ℓ F (Nat.zero_le n) hnm, Category.assoc,
      Category.assoc, initialVerschiebung_scalar, Preadditive.comp_nsmul, Category.comp_id,
      Preadditive.comp_nsmul, ← Preadditive.nsmul_comp] at hg₀n
  obtain ⟨d, hd : underlyingTransitionLE B X ℓ F hnm ≫ d = _⟩ :=
    CokernelCofork.IsColimit.desc' (underlyingTransitionLE_isCokernel B X ℓ F hnm)
      (cokernel.π ((ℓ ^ (n + 1)) • (𝟙 (underlyingLAdicLevel B X ℓ F m)))) (cokernel.condition _)
  rw [← hd, ← Category.assoc, ht, zero_comp]

/-- **The divisibility of torsion in the underlying tower.** Beyond a level depending only on
the ℓ-adic sheaf, a map into level `m` killed by `ℓᵐ` becomes divisible by `ℓⁿ⁺¹` after
multiplication by `ℓⁿ`. -/
public theorem underlyingLAdic_torsion_divisibility (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    ∃ c : ℕ, ∀ (n m : ℕ), c ≤ n → (hnm : n ≤ m) →
      ∀ (A : Sheaf (SmallEtale.topology B X.1 X.property) AddCommGrpCat.{u + 1})
        (g : A ⟶ underlyingLAdicLevel B X ℓ F m), (ℓ ^ m) • g = 0 →
        ((ℓ ^ n) • g) ≫
          cokernel.π ((ℓ ^ (n + 1)) • (𝟙 (underlyingLAdicLevel B X ℓ F m))) = 0 := by
  obtain ⟨c, hc⟩ := initialVerschiebung_kernel_stabilizes B X ℓ F
  exact ⟨c, fun n m hn hnm A g hg =>
    torsion_divisibility_of_verschiebung_kernel_eq B X ℓ F hnm
      ((hc n hn).symm.trans (hc m (hn.trans hnm))) A g hg⟩

/-- The underlying sheaf of abelian groups of a levelwise kernel. -/
public abbrev underlyingRawKernelLevel {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :=
  (underlyingLevelFunctor B X ℓ n).obj (kernel (f.app n))

/-- The underlying inclusion of a levelwise kernel. -/
public def underlyingRawKernelι {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) (n : ℕ) :
    underlyingRawKernelLevel B X ℓ f n ⟶ underlyingLAdicLevel B X ℓ F n :=
  (underlyingLevelFunctor B X ℓ n).map (kernel.ι (f.app n))

/-- The underlying inclusion of a levelwise kernel is a monomorphism. -/
public theorem underlyingRawKernelι_mono {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) : Mono (underlyingRawKernelι B X ℓ f n) :=
  (underlyingLevelFunctor B X ℓ n).map_mono _

attribute [local instance] underlyingRawKernelι_mono

/-- The underlying inclusion of a levelwise kernel is killed by the morphism. -/
public theorem underlyingRawKernelι_condition {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) :
    underlyingRawKernelι B X ℓ f n ≫ (underlyingLevelFunctor B X ℓ n).map (f.app n) = 0 := by
  rw [underlyingRawKernelι, ← Functor.map_comp, kernel.condition, Functor.map_zero]

/-- The underlying inclusion of a levelwise kernel is a kernel of the underlying morphism. -/
public def underlyingRawKernel_isKernel {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) :
    IsLimit (KernelFork.ofι (underlyingRawKernelι B X ℓ f n)
      (underlyingRawKernelι_condition B X ℓ f n)) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (f.app n)) (underlyingLevelFunctor B X ℓ n)

/-- The transition map of the tower of underlying levelwise kernels. -/
public def underlyingRawKernelTransition {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) :
    underlyingRawKernelLevel B X ℓ f (n + 1) ⟶ underlyingRawKernelLevel B X ℓ f n :=
  (underlyingLevelFunctor B X ℓ (n + 1)).map (rawKernelTransition f n)

/-- The transition map of underlying levelwise kernels lies over that of the source. -/
public theorem underlyingRawKernelTransition_fac {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    (n : ℕ) :
    underlyingRawKernelTransition B X ℓ f n ≫ underlyingRawKernelι B X ℓ f n =
      underlyingRawKernelι B X ℓ f (n + 1) ≫ underlyingLAdicTransition B X ℓ F n := by
  show (underlyingLevelFunctor B X ℓ (n + 1)).map (rawKernelTransition f n) ≫
      (underlyingLevelFunctor B X ℓ (n + 1)).map
        ((restrictScalarsFunctor B X ℓ n).map (kernel.ι (f.app n))) = _
  rw [← Functor.map_comp, rawKernelTransition_fac, Functor.map_comp]
  rfl

/-- For an epimorphism, the transition maps of the underlying levelwise kernels are
epimorphisms. -/
public theorem underlyingRawKernelTransition_epi {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    [Epi f] (n : ℕ) : Epi (underlyingRawKernelTransition B X ℓ f n) := by
  have := rawKernelTransition_epi f n
  exact (underlyingLevelFunctor B X ℓ (n + 1)).map_epi _

end LAdicSheaf

end Stacks.EtaleCohomology

end
