module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedLevelData

/-!
# The completed reverse map and homotopy of Tag 07N1 along `B → B'`

The level data of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PthRootCompletedLevelData.lean`
— the reverse maps `e_n` and the integrating homotopies `h_n` of the levels `M_n = M / pⁿ M`, which
are compatible with the transition maps — assemble into maps of the completed complexes
`M' ⊗̂_{B'} Ω^•_{B'} → M ⊗̂_B Ω^•_B` and `M' ⊗̂_{B'} Ω^{•+1}_{B'} → M' ⊗̂_{B'} Ω^•_{B'}`. Every
identity of [Stacks, Lemma 60.25.3, Tag 07N1] holds at every level, hence on the completions: `ê`
is a map of complexes, `ê ∘ ĉ = p`, `ĥ ∘ ĉ = 0`, `ĥ d = p - ĉ ê` in degree zero and
`d ĥ + ĥ d = p - ĉ ê` in positive degree.

## Main definitions

* `Crystalline.PthRootExtension.completedReverse` — the completed reverse map `ê`.
* `Crystalline.PthRootExtension.completedHomotopy` — the completed homotopy `ĥ`.

## Main results

* `Crystalline.PthRootExtension.completedReverse_differential`,
  `Crystalline.PthRootExtension.completedReverse_comparison`,
  `Crystalline.PthRootExtension.completedHomotopy_comparison`,
  `Crystalline.PthRootExtension.completedHomotopy_zero`,
  `Crystalline.PthRootExtension.completedHomotopy_succ` — the identities.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u w

namespace Crystalline

namespace PthRootExtension

open CompletedLevels

/-! ### The level identifications of the two completed complexes -/

section LevelEquivs

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0) (M : Type u) [AddCommGroup M] [Module (B : Type u) M]

/-- The level `pⁿ` of the source term `M ⊗̂_B Ω^q_B` is the term of `M_n`. -/
abbrev baseLevelEquiv (q n : ℕ) :=
  formsLevelEquiv p A (B : Type u) B.dividedPowers M q n

/-- **The level `pⁿ` of the target term `M' ⊗̂_{B'} Ω^q_{B'}` is the term
`(B' ⊗_B M_n) ⊗_{B'} Ω^q_{B'/A,γ'}` of the base change of `M_n`.** -/
abbrev primeLevelEquiv (q n : ℕ) :
    ((primeCarrier B p lam M ⊗[primeRing B p lam]
        completedDividedPowerForms p A (primeDividedPowers B p lam hp) q) ⧸
      (pAdicIdeal (A := primeRing B p lam) p ^ n • ⊤ : Submodule (primeRing B p lam)
        (primeCarrier B p lam M ⊗[primeRing B p lam]
          completedDividedPowerForms p A (primeDividedPowers B p lam hp) q))) ≃ₗ[primeRing B p lam]
      primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M n) q :=
  (formsLevelEquiv p A (primeRing B p lam) (primeDividedPowers B p lam hp)
    (primeCarrier B p lam M) q n).trans
    (TensorProduct.congr (primeLevelModuleEquiv B p lam M n) (LinearEquiv.refl _ _))

/-- The target level identification as a formula. -/
theorem primeLevelEquiv_apply (q n : ℕ) (y) :
    primeLevelEquiv A B p lam hp M q n y =
      TensorProduct.map (primeLevelModuleEquiv B p lam M n).toLinearMap LinearMap.id
        (formsLevelEquiv p A (primeRing B p lam) (primeDividedPowers B p lam hp)
          (primeCarrier B p lam M) q n y) := rfl

variable {m k : ℕ} (hmk : m ≤ k)

/-- The source level identifications are compatible with the transition maps. -/
theorem baseLevelEquiv_transition (q : ℕ) (x) :
    baseLevelEquiv A B p M q m (AdicCompletion.transitionMap _ _ hmk x) =
      baseTermMap A B (levelTransition B p M hmk) q (baseLevelEquiv A B p M q k x) :=
  levelTensorEquiv_transitionMap _ M _ _ hmk x

/-- The identification `M'_n ≃ B' ⊗_B M_n` is compatible with the transition maps. -/
theorem primeLevelModuleEquiv_transition (x : levelModule p (primeRing B p lam)
    (primeCarrier B p lam M) k) :
    primeLevelModuleEquiv B p lam M m (AdicCompletion.transitionMap _ _ hmk x) =
      (levelTransition B p M hmk).baseChange (primeRing B p lam)
        (primeLevelModuleEquiv B p lam M k x) := by
  have key := tensor_addMonoidHom_ext
    (F := ((primeLevelModuleEquiv B p lam M m).toLinearMap.toAddMonoidHom.comp
      (AdicCompletion.transitionMap (pAdicIdeal (A := primeRing B p lam) p)
        (primeCarrier B p lam M) hmk).toAddMonoidHom).comp
        ((Submodule.mkQ _).toAddMonoidHom.comp
          (AdicCompletion.of (pAdicIdeal (A := primeRing B p lam) p)
            (primeRing B p lam ⊗[(B : Type u)] M)).toAddMonoidHom))
    (G := (((levelTransition B p M hmk).baseChange (primeRing B p lam)).toAddMonoidHom.comp
      (primeLevelModuleEquiv B p lam M k).toLinearMap.toAddMonoidHom).comp
        ((Submodule.mkQ _).toAddMonoidHom.comp
          (AdicCompletion.of (pAdicIdeal (A := primeRing B p lam) p)
            (primeRing B p lam ⊗[(B : Type u)] M)).toAddMonoidHom))
    (fun b' y ↦ by
      show primeLevelModuleEquiv B p lam M m (AdicCompletion.transitionMap _ _ hmk
          (Submodule.Quotient.mk (AdicCompletion.of _ _ (b' ⊗ₜ y)))) =
        (levelTransition B p M hmk).baseChange (primeRing B p lam) (b' ⊗ₜ Submodule.Quotient.mk y)
      rw [transitionMap_mk_eq, LinearMap.baseChange_tmul, transitionMap_mk_eq]
      rfl)
  have := quotientAdicCompletion_addMonoidHom_ext (pAdicIdeal (A := primeRing B p lam) p) k
    (primeRing B p lam ⊗[(B : Type u)] M) (CompletedConnection.pAdicIdeal_fg p _)
    (F := (primeLevelModuleEquiv B p lam M m).toLinearMap.toAddMonoidHom.comp
      (AdicCompletion.transitionMap (pAdicIdeal (A := primeRing B p lam) p)
        (primeCarrier B p lam M) hmk).toAddMonoidHom)
    (G := ((levelTransition B p M hmk).baseChange (primeRing B p lam)).toAddMonoidHom.comp
      (primeLevelModuleEquiv B p lam M k).toLinearMap.toAddMonoidHom)
    (fun t ↦ DFunLike.congr_fun key t)
  exact DFunLike.congr_fun this x

/-- The target level identifications are compatible with the transition maps. -/
theorem primeLevelEquiv_transition (q : ℕ) (y) :
    primeLevelEquiv A B p lam hp M q m (AdicCompletion.transitionMap _ _ hmk y) =
      primeTermMap A B p lam hp (levelTransition B p M hmk) q
        (primeLevelEquiv A B p lam hp M q k y) := by
  have h1 := levelTensorEquiv_transitionMap (pAdicIdeal (A := primeRing B p lam) p)
    (primeCarrier B p lam M) (dividedPowerDifferentialForms (A := A) (primeDividedPowers B p lam hp)
        q)
    (pAdicIdeal_fg_ring p (primeRing B p lam)) hmk y
  refine (congrArg (TensorProduct.map (primeLevelModuleEquiv B p lam M m).toLinearMap
    LinearMap.id) h1).trans ?_
  refine (?_ : ∀ t, TensorProduct.map (primeLevelModuleEquiv B p lam M m).toLinearMap LinearMap.id
      (TensorProduct.map (AdicCompletion.transitionMap _ _ hmk) LinearMap.id t) =
    primeTermMap A B p lam hp (levelTransition B p M hmk) q
      (TensorProduct.map (primeLevelModuleEquiv B p lam M k).toLinearMap LinearMap.id t)) _
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a w =>
    exact congrArg (· ⊗ₜ[primeRing B p lam] w) (primeLevelModuleEquiv_transition B p lam M hmk a)

end LevelEquivs

/-! ### The completed reverse map and homotopy -/

section Completed

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0) [Nontrivial (XiAlg B)] [Fact p.Prime]
  [Algebra (IntegersAtPrime p) (B : Type u)] (M : Type u) [AddCommGroup M] [Module (B : Type u) M]
  (nabla : CompletedConnection p (B : Type u) (completedDividedPowerForms p A B.dividedPowers 1)
    (completedDividedPowerDifferentialOnRing p A B.dividedPowers) M)
  (hint : IsCompletedIntegrable p A (B : Type u) B.dividedPowers M nabla)
  (S : SourceDeRham A (B : Type u)) (S' : SourceDeRham A (primeRing B p lam))

/-- The degree-`q` term `M ⊗̂_B Ω^q_B` of the source complex. -/
abbrev baseCompletedTerm (q : ℕ) : Type u :=
  CompletedTensor p (B : Type u) (completedDividedPowerForms p A B.dividedPowers q) M

/-- The integrating homotopy kills the image of the canonical map. -/
theorem pthRootHomotopy_comparison {N : Type u} [AddCommGroup N] [Module (B : Type u) N] (q : ℕ)
    (c : RestrictScalars A (B : Type u) (baseDeRhamTerm A B N (q + 1)) →ₗ[A]
      RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp N (q + 1)))
    (hc : ∀ (m : N) (omega : Fin (q + 1) → baseForms A B),
      c (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) (q + 1) omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) (q + 1)
            ((primeFormsComparison A B p lam hp) ∘ omega))
    (x : baseDeRhamTerm A B N (q + 1)) :
    pthRootHomotopy A B p lam hp N q (c x) = 0 := by
  have := tensorExteriorPower_addMonoidHom_ext
    (F := ((pthRootHomotopy A B p lam hp N q).toAddMonoidHom.comp c.toAddMonoidHom))
    (G := 0) (fun m v ↦ by
      show pthRootHomotopy A B p lam hp N q (c (m ⊗ₜ exteriorPower.ιMulti _ _ v)) = 0
      rw [hc]
      exact integratingHomotopyMap_base (A := A) (primeFormsProjection A B p lam hp)
        (primeFormsComparison A B p lam hp) (zElt B p lam) (pthRootDzDecomposition A B p lam hp)
        (theta B p lam hp) N q 1 m v)
  exact DFunLike.congr_fun this x

/-- The level maps of the completed reverse map. -/
abbrev reverseLevel (q k : ℕ) :=
  (baseLevelEquiv A B p M q k).toAddEquiv.symm.toAddMonoidHom.comp
    ((restrictScalarsUnderlyingAddHom (levelReverse A B p lam hp M nabla hint S S' k q)).comp
      (primeLevelEquiv A B p lam hp M q k).toAddEquiv.toAddMonoidHom)

/-- The level maps of the completed reverse map are compatible. -/
theorem reverseLevel_compat (q : ℕ) {m k : ℕ} (hmk : m ≤ k) (y) :
    AdicCompletion.transitionMap _ _ hmk (reverseLevel A B p lam hp M nabla hint S S' q k y) =
      reverseLevel A B p lam hp M nabla hint S S' q m (AdicCompletion.transitionMap _ _ hmk y) :=
  conj_compat (baseLevelEquiv A B p M q k).toAddEquiv (baseLevelEquiv A B p M q m).toAddEquiv
    (primeLevelEquiv A B p lam hp M q k).toAddEquiv (primeLevelEquiv A B p lam hp M q m).toAddEquiv
    (AdicCompletion.transitionMap _ _ hmk).toAddMonoidHom
    (AdicCompletion.transitionMap _ _ hmk).toAddMonoidHom
    (baseTermMap A B (levelTransition B p M hmk) q).toAddMonoidHom
    (primeTermMap A B p lam hp (levelTransition B p M hmk) q).toAddMonoidHom
    (restrictScalarsUnderlyingAddHom (levelReverse A B p lam hp M nabla hint S S' k q))
    (restrictScalarsUnderlyingAddHom (levelReverse A B p lam hp M nabla hint S S' m q))
    (baseLevelEquiv_transition A B p M hmk q) (primeLevelEquiv_transition A B p lam hp M hmk q)
    (levelReverse_transition A B p lam hp M nabla hint S S' hmk q) y

/-- **The completed reverse map `ê : M' ⊗̂_{B'} Ω^q_{B'} → M ⊗̂_B Ω^q_B`**, assembled from the
reverse maps `e_n` of the levels. -/
def completedReverse (q : ℕ) :
    primeCompletedTerm A B p lam hp M q →+ baseCompletedTerm A B p M q :=
  levelwiseAddHom _ _ (reverseLevel A B p lam hp M nabla hint S S' q)
    (fun hmk y ↦ reverseLevel_compat A B p lam hp M nabla hint S S' q hmk y)

/-- The level maps of the completed homotopy. -/
abbrev homotopyLevel (q k : ℕ) :=
  (primeLevelEquiv A B p lam hp M q k).toAddEquiv.symm.toAddMonoidHom.comp
    ((restrictScalarsUnderlyingAddHom
        (pthRootHomotopy A B p lam hp (levelModule p (B : Type u) M k) q)).comp
      (primeLevelEquiv A B p lam hp M (q + 1) k).toAddEquiv.toAddMonoidHom)

/-- The level maps of the completed homotopy are compatible. -/
theorem homotopyLevel_compat (q : ℕ) {m k : ℕ} (hmk : m ≤ k) (y) :
    AdicCompletion.transitionMap _ _ hmk (homotopyLevel A B p lam hp M q k y) =
      homotopyLevel A B p lam hp M q m (AdicCompletion.transitionMap _ _ hmk y) :=
  conj_compat (primeLevelEquiv A B p lam hp M q k).toAddEquiv
    (primeLevelEquiv A B p lam hp M q m).toAddEquiv
    (primeLevelEquiv A B p lam hp M (q + 1) k).toAddEquiv
    (primeLevelEquiv A B p lam hp M (q + 1) m).toAddEquiv
    (AdicCompletion.transitionMap _ _ hmk).toAddMonoidHom
    (AdicCompletion.transitionMap _ _ hmk).toAddMonoidHom
    (primeTermMap A B p lam hp (levelTransition B p M hmk) q).toAddMonoidHom
    (primeTermMap A B p lam hp (levelTransition B p M hmk) (q + 1)).toAddMonoidHom
    (restrictScalarsUnderlyingAddHom
      (pthRootHomotopy A B p lam hp (levelModule p (B : Type u) M k) q))
    (restrictScalarsUnderlyingAddHom
      (pthRootHomotopy A B p lam hp (levelModule p (B : Type u) M m) q))
    (primeLevelEquiv_transition A B p lam hp M hmk q)
    (primeLevelEquiv_transition A B p lam hp M hmk (q + 1))
    (fun t ↦ (pthRootHomotopy_naturality A B p lam hp (levelTransition B p M hmk) q t).symm) y

/-- **The completed homotopy `ĥ : M' ⊗̂_{B'} Ω^{q+1}_{B'} → M' ⊗̂_{B'} Ω^q_{B'}`**, assembled from
the integrating homotopies of the levels. -/
def completedHomotopy (q : ℕ) :
    primeCompletedTerm A B p lam hp M (q + 1) →+ primeCompletedTerm A B p lam hp M q :=
  levelwiseAddHom _ _ (homotopyLevel A B p lam hp M q)
    (fun hmk y ↦ homotopyLevel_compat A B p lam hp M q hmk y)

/-! #### The level maps as additive maps -/

/-- The level de Rham differential of the source, as an additive map. -/
abbrev dXn (n q : ℕ) :=
  restrictScalarsUnderlyingAddHom ((baseExtended A B (levelModule p (B : Type u) M n) S
    (levelNabla A B p M nabla n)).toLinearMap q)

/-- The level de Rham differential of the target, as an additive map. -/
abbrev dYn (n q : ℕ) :=
  restrictScalarsUnderlyingAddHom ((primeExtended A B p lam hp (levelModule p (B : Type u) M n) S'
    (levelNabla A B p M nabla n)).toLinearMap q)

/-- The level canonical map, as an additive map. -/
abbrev cn (n q : ℕ) :=
  restrictScalarsUnderlyingAddHom (levelComparison A B p lam hp M nabla hint S S' n q)

/-- The level reverse map, as an additive map. -/
abbrev en (n q : ℕ) :=
  restrictScalarsUnderlyingAddHom (levelReverse A B p lam hp M nabla hint S S' n q)

/-- The level homotopy, as an additive map. -/
abbrev hn (n q : ℕ) :=
  restrictScalarsUnderlyingAddHom (pthRootHomotopy A B p lam hp (levelModule p (B : Type u) M n) q)

/-- The level reverse map is a map of complexes. -/
theorem en_dYn (n q : ℕ) (y : primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M n) q) :
    en A B p lam hp M nabla hint S S' n (q + 1) (dYn A B p lam hp M nabla S' n q y) =
      dXn A B p M nabla S n q (en A B p lam hp M nabla hint S S' n q y) :=
  levelReverse_comm A B p lam hp M nabla hint S S' n q y

/-- `e_n ∘ c_n = p`. -/
theorem en_cn (n q : ℕ) (x : baseDeRhamTerm A B (levelModule p (B : Type u) M n) q) :
    en A B p lam hp M nabla hint S S' n q (cn A B p lam hp M nabla hint S S' n q x) = p • x :=
  (levelReverse_comparison A B p lam hp M nabla hint S S' n q x).trans
    (restrictScalars_lsmul_natCast A (B : Type u)
      (X := baseDeRhamTerm A B (levelModule p (B : Type u) M n) q) p x)

/-- `h_n d = p - c_n e_n` in degree zero. -/
theorem hn_dYn_zero (n : ℕ) (y : primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M n) 0) :
    hn A B p lam hp M n 0 (dYn A B p lam hp M nabla S' n 0 y) =
      p • y - cn A B p lam hp M nabla hint S S' n 0 (en A B p lam hp M nabla hint S S' n 0 y) :=
  (levelReverse_homotopy_zero A B p lam hp M nabla hint S S' n y).trans
    (congrArg (· - _) (restrictScalars_lsmul_algebraMap_natCast A (B : Type u) (primeRing B p lam)
      (X := primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M n) 0) p y))

/-- `d h_n + h_n d = p - c_n e_n` in positive degree. -/
theorem hn_dYn_succ (n q : ℕ)
    (y : primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M n) (q + 1)) :
    dYn A B p lam hp M nabla S' n q (hn A B p lam hp M n q y) +
        hn A B p lam hp M n (q + 1) (dYn A B p lam hp M nabla S' n (q + 1) y) =
      p • y - cn A B p lam hp M nabla hint S S' n (q + 1)
        (en A B p lam hp M nabla hint S S' n (q + 1) y) :=
  (levelReverse_homotopy_succ A B p lam hp M nabla hint S S' n q y).trans
    (congrArg (· - _) (restrictScalars_lsmul_algebraMap_natCast A (B : Type u) (primeRing B p lam)
      (X := primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M n) (q + 1)) p y))

/-- `h_n ∘ c_n = 0`. -/
theorem hn_cn (n q : ℕ) (x : baseDeRhamTerm A B (levelModule p (B : Type u) M n) (q + 1)) :
    hn A B p lam hp M n q (cn A B p lam hp M nabla hint S S' n (q + 1) x) = 0 :=
  pthRootHomotopy_comparison A B p lam hp q (levelComparison A B p lam hp M nabla hint S S' n
      (q + 1))
    (levelComparison_wedge A B p lam hp M nabla hint S S' n (q + 1)) x

/-! #### The completed differentials and the completed canonical map -/

/-- The differential of the source complex `M ⊗̂_B Ω^•_B`. -/
abbrev baseCompletedDifferential (q : ℕ) :
    baseCompletedTerm A B p M q →+ baseCompletedTerm A B p M (q + 1) :=
  CompletedDeRham.differential p (B : Type u) (completedDividedPowerForms p A B.dividedPowers)
    (completedDividedPowerWedgeOnRing p A B.dividedPowers)
    (completedDividedPowerDeRham p A B.dividedPowers) M nabla
    (isGradedLeibniz_completedDividedPowerOnRing p A B.dividedPowers) q

/-- The differential of the target complex `M' ⊗̂_{B'} Ω^•_{B'}`. -/
abbrev primeCompletedDifferential (q : ℕ) :
    primeCompletedTerm A B p lam hp M q →+ primeCompletedTerm A B p lam hp M (q + 1) :=
  CompletedDeRham.differential p (primeRing B p lam)
    (completedDividedPowerForms p A (primeDividedPowers B p lam hp))
    (completedDividedPowerWedgeOnRing p A (primeDividedPowers B p lam hp))
    (completedDividedPowerDeRham p A (primeDividedPowers B p lam hp)) (primeCarrier B p lam M)
    (primeCompletedConnection A B p lam hp M nabla)
    (isGradedLeibniz_completedDividedPowerOnRing p A (primeDividedPowers B p lam hp)) q

/-- The completed canonical map `ĉ` of [Stacks, Tag 07PY] along `B → B'`. -/
abbrev primeCompletedComparison (q : ℕ) :
    baseCompletedTerm A B p M q →+ primeCompletedTerm A B p lam hp M q :=
  CompletedDeRham.baseChangeTerm p (B : Type u) (primeRing B p lam) M
    (completedDividedPowerForms p A B.dividedPowers)
    (completedDividedPowerForms p A (primeDividedPowers B p lam hp))
    (primeCompletedFormsMap A B p lam hp) q

/-- The level of the source differential is the extended level connection. -/
theorem baseLevel_differential (n q : ℕ) (x : baseCompletedTerm A B p M q) :
    baseLevelEquiv A B p M (q + 1) n ((baseCompletedDifferential A B p M nabla q x).val n) =
      dXn A B p M nabla S n q (baseLevelEquiv A B p M q n (x.val n)) :=
  formsLevelEquiv_levelDifferential p A (B : Type u) B.dividedPowers M nabla S q n (x.val n)

/-- The level of the target differential is the extended level connection. -/
theorem primeLevel_differential (n q : ℕ) (y : primeCompletedTerm A B p lam hp M q) :
    primeLevelEquiv A B p lam hp M (q + 1) n
        ((primeCompletedDifferential A B p lam hp M nabla q y).val n) =
      dYn A B p lam hp M nabla S' n q (primeLevelEquiv A B p lam hp M q n (y.val n)) :=
  primeLevel_levelDifferential A B p lam hp M nabla S' q n (y.val n)

/-- The level of the completed canonical map is the level canonical map. -/
theorem primeLevel_comparison (n q : ℕ) (x : baseCompletedTerm A B p M q) :
    primeLevelEquiv A B p lam hp M q n ((primeCompletedComparison A B p lam hp M q x).val n) =
      cn A B p lam hp M nabla hint S S' n q (baseLevelEquiv A B p M q n (x.val n)) :=
  primeLevel_baseChangeTerm A B p lam hp M n (levelComparison A B p lam hp M nabla hint S S' n)
    (levelComparison_wedge A B p lam hp M nabla hint S S' n) q x

/-- The levels of the completed reverse map. -/
theorem completedReverse_val (n q : ℕ) (y : primeCompletedTerm A B p lam hp M q) :
    (completedReverse A B p lam hp M nabla hint S S' q y).val n =
      (baseLevelEquiv A B p M q n).symm
        (en A B p lam hp M nabla hint S S' n q (primeLevelEquiv A B p lam hp M q n (y.val n))) :=
  rfl

/-- The levels of the completed homotopy. -/
theorem completedHomotopy_val (n q : ℕ) (y : primeCompletedTerm A B p lam hp M (q + 1)) :
    (completedHomotopy A B p lam hp M q y).val n =
      (primeLevelEquiv A B p lam hp M q n).symm
        (hn A B p lam hp M n q (primeLevelEquiv A B p lam hp M (q + 1) n (y.val n))) :=
  rfl

/-- **`ê` is a map of complexes.** -/
theorem completedReverse_differential (q : ℕ) (y : primeCompletedTerm A B p lam hp M q) :
    completedReverse A B p lam hp M nabla hint S S' (q + 1) (primeCompletedDifferential A B p lam hp
        M nabla q y) = baseCompletedDifferential A B p M nabla q (completedReverse A B p lam hp M
        nabla hint S S' q y) := by
  refine AdicCompletion.ext fun n ↦ (baseLevelEquiv A B p M (q + 1) n).injective ?_
  have h1 := completedReverse_val A B p lam hp M nabla hint S S' n (q + 1)
      (primeCompletedDifferential A B p lam hp M nabla q y)
  have h2 := completedReverse_val A B p lam hp M nabla hint S S' n q y
  refine (congrArg (baseLevelEquiv A B p M (q + 1) n) h1).trans ?_
  refine ((baseLevelEquiv A B p M (q + 1) n).apply_symm_apply _).trans ?_
  refine (congrArg (en A B p lam hp M nabla hint S S' n (q + 1)) (primeLevel_differential A B p lam
      hp M nabla S' n q y)).trans ?_
  refine (en_dYn A B p lam hp M nabla hint S S' n q _).trans ?_
  refine Eq.trans ?_ (baseLevel_differential A B p M nabla S n q (completedReverse A B p lam hp M
      nabla hint S S' q y)).symm
  refine congrArg (dXn A B p M nabla S n q) ?_
  exact ((baseLevelEquiv A B p M q n).apply_symm_apply _).symm.trans (congrArg (baseLevelEquiv A B p
      M q n) h2).symm

/-- **`ê ∘ ĉ = p` on the nose.** -/
theorem completedReverse_comparison (q : ℕ) (x : baseCompletedTerm A B p M q) :
    completedReverse A B p lam hp M nabla hint S S' q (primeCompletedComparison A B p lam hp M q
        x) = p • x := by
  refine AdicCompletion.ext fun n ↦ (baseLevelEquiv A B p M q n).injective ?_
  have h1 := completedReverse_val A B p lam hp M nabla hint S S' n q (primeCompletedComparison A B p
      lam hp M q x)
  refine (congrArg (baseLevelEquiv A B p M q n) h1).trans ?_
  refine ((baseLevelEquiv A B p M q n).apply_symm_apply _).trans ?_
  refine (congrArg (en A B p lam hp M nabla hint S S' n q) (primeLevel_comparison A B p lam hp M
      nabla hint S S' n q x)).trans ?_
  refine (en_cn A B p lam hp M nabla hint S S' n q _).trans ?_
  refine Eq.trans ?_ (congrArg (baseLevelEquiv A B p M q n)
    (map_nsmul (AdicCompletion.eval _ _ n) p x)).symm
  exact (map_nsmul (baseLevelEquiv A B p M q n) p (x.val n)).symm

/-- The level `pⁿ` of the completed canonical map, as the map `ψ_*` of the levels. -/
theorem primeLevel_comparison_values (n q : ℕ) (x : baseCompletedTerm A B p M q) :
    primeLevelEquiv A B p lam hp M q n ((primeCompletedComparison A B p lam hp M q x).val n) =
      Connection.baseChangeValues (primeFormsMapₛₗ A B p lam hp q)
        (baseLevelEquiv A B p M q n (x.val n)) :=
  levelTensorEquiv_adicQuotientMap_baseChangeTensor p n M
    (dividedPowerDifferentialForms (A := A) B.dividedPowers q)
    (dividedPowerDifferentialForms (A := A) (primeDividedPowers B p lam hp) q)
    (primeFormsMapₛₗ A B p lam hp q) (x.val n)

/-- The integrating homotopy kills the image of `ψ_*`. -/
theorem hn_baseChangeValues (n q : ℕ)
    (t : baseDeRhamTerm A B (levelModule p (B : Type u) M n) (q + 1)) :
    hn A B p lam hp M n q (Connection.baseChangeValues (primeFormsMapₛₗ A B p lam hp (q + 1)) t) =
      0 := by
  have := tensorExteriorPower_addMonoidHom_ext
    (F := (hn A B p lam hp M n q).comp
      (Connection.baseChangeValues (primeFormsMapₛₗ A B p lam hp (q + 1))))
    (G := 0) (fun m v ↦ by
      show hn A B p lam hp M n q (Connection.baseChangeValues (primeFormsMapₛₗ A B p lam hp
          (q + 1))
        (m ⊗ₜ exteriorPower.ιMulti _ _ v)) = 0
      rw [Connection.baseChangeValues_tmul, primeFormsMapₛₗ_ιMulti]
      exact integratingHomotopyMap_base (A := A) (primeFormsProjection A B p lam hp)
        (primeFormsComparison A B p lam hp) (zElt B p lam) (pthRootDzDecomposition A B p lam hp)
        (theta B p lam hp) _ q 1 m v)
  exact DFunLike.congr_fun this t

/-- **`ĥ ∘ ĉ = 0`.** -/
theorem completedHomotopy_comparison (q : ℕ) (x : baseCompletedTerm A B p M (q + 1)) :
    completedHomotopy A B p lam hp M q (primeCompletedComparison A B p lam hp M (q + 1) x) = 0 := by
  refine AdicCompletion.ext fun n ↦ ?_
  refine (completedHomotopy_val A B p lam hp M n q _).trans ?_
  refine (congrArg (fun t ↦ (primeLevelEquiv A B p lam hp M q n).symm (hn A B p lam hp M n q t))
    (primeLevel_comparison_values A B p lam hp M n (q + 1) x)).trans ?_
  refine (congrArg (primeLevelEquiv A B p lam hp M q n).symm
    (hn_baseChangeValues A B p lam hp M n q _)).trans ?_
  exact map_zero _

/-- **`ĥ d = p - ĉ ê` in degree zero.** -/
theorem completedHomotopy_zero (y : primeCompletedTerm A B p lam hp M 0) :
    completedHomotopy A B p lam hp M 0 (primeCompletedDifferential A B p lam hp M nabla 0 y) =
        p • y - primeCompletedComparison A B p lam hp M 0 (completedReverse A B p lam hp M nabla
        hint S S' 0 y) := by
  refine AdicCompletion.ext fun n ↦ (primeLevelEquiv A B p lam hp M 0 n).injective ?_
  have h1 := completedHomotopy_val A B p lam hp M n 0 (primeCompletedDifferential A B p lam hp M
      nabla 0 y)
  have h2 := completedReverse_val A B p lam hp M nabla hint S S' n 0 y
  refine (congrArg (primeLevelEquiv A B p lam hp M 0 n) h1).trans ?_
  refine ((primeLevelEquiv A B p lam hp M 0 n).apply_symm_apply _).trans ?_
  refine (congrArg (hn A B p lam hp M n 0) (primeLevel_differential A B p lam hp M nabla S' n 0
      y)).trans ?_
  refine (hn_dYn_zero A B p lam hp M nabla hint S S' n _).trans ?_
  have h3 : primeLevelEquiv A B p lam hp M 0 n ((p • y - primeCompletedComparison A B p lam hp M 0
      (completedReverse A B p lam hp M nabla hint S S' 0 y)).val n) =
      p • primeLevelEquiv A B p lam hp M 0 n (y.val n) - primeLevelEquiv A B p lam hp M 0 n
          ((primeCompletedComparison A B p lam hp M 0 (completedReverse A B p lam hp M nabla hint S
          S' 0 y)).val n) :=
    (congrArg (primeLevelEquiv A B p lam hp M 0 n) (map_sub (AdicCompletion.eval _ _ n) _ _)).trans
      ((map_sub _ _ _).trans (congrArg (· - _) ((congrArg (primeLevelEquiv A B p lam hp M 0 n)
        (map_nsmul (AdicCompletion.eval _ _ n) p y)).trans (map_nsmul _ p _))))
  refine Eq.trans ?_ h3.symm
  refine congrArg (p • primeLevelEquiv A B p lam hp M 0 n (y.val n) - ·) ?_
  refine Eq.trans ?_ (primeLevel_comparison A B p lam hp M nabla hint S S' n 0 (completedReverse A B
      p lam hp M nabla hint S S' 0 y)).symm
  exact congrArg (cn A B p lam hp M nabla hint S S' n 0) (((baseLevelEquiv A B p M 0
      n).apply_symm_apply _).symm.trans (congrArg (baseLevelEquiv A B p M 0 n) h2).symm)

/-- **`d ĥ + ĥ d = p - ĉ ê` in positive degree.** -/
theorem completedHomotopy_succ (q : ℕ) (y : primeCompletedTerm A B p lam hp M (q + 1)) :
    primeCompletedDifferential A B p lam hp M nabla q (completedHomotopy A B p lam hp M q
        y) + completedHomotopy A B p lam hp M (q + 1) (primeCompletedDifferential A B p lam hp M
        nabla (q + 1) y) = p • y - primeCompletedComparison A B p lam hp M (q + 1) (completedReverse
        A B p lam hp M nabla hint S S' (q + 1) y) := by
  refine AdicCompletion.ext fun n ↦ (primeLevelEquiv A B p lam hp M (q + 1) n).injective ?_
  have h1 := completedHomotopy_val A B p lam hp M n q y
  have h1' := completedHomotopy_val A B p lam hp M n (q + 1) (primeCompletedDifferential A B p lam
      hp M nabla (q + 1) y)
  have h2 := completedReverse_val A B p lam hp M nabla hint S S' n (q + 1) y
  have h3 : primeLevelEquiv A B p lam hp M (q + 1) n ((primeCompletedDifferential A B p lam hp M
      nabla q (completedHomotopy A B p lam hp M q y) + completedHomotopy A B p lam hp M (q + 1)
      (primeCompletedDifferential A B p lam hp M nabla (q + 1) y)).val n) =
      primeLevelEquiv A B p lam hp M (q + 1) n ((primeCompletedDifferential A B p lam hp M nabla q
          (completedHomotopy A B p lam hp M q y)).val n) +
        primeLevelEquiv A B p lam hp M (q + 1) n ((completedHomotopy A B p lam hp M (q + 1)
            (primeCompletedDifferential A B p lam hp M nabla (q + 1) y)).val n) :=
    (congrArg (primeLevelEquiv A B p lam hp M (q + 1) n)
      (map_add (AdicCompletion.eval _ _ n) _ _)).trans (map_add _ _ _)
  refine h3.trans ?_
  have h4 : primeLevelEquiv A B p lam hp M (q + 1) n ((primeCompletedDifferential A B p lam hp M
      nabla q (completedHomotopy A B p lam hp M q y)).val n) = dYn A B p lam hp M nabla S' n q (hn A
      B p lam hp M n q (primeLevelEquiv A B p lam hp M (q + 1) n (y.val n))) := by
    refine (primeLevel_differential A B p lam hp M nabla S' n q (completedHomotopy A B p lam hp M q
        y)).trans ?_
    refine congrArg (dYn A B p lam hp M nabla S' n q) ?_
    exact (congrArg (primeLevelEquiv A B p lam hp M q n) h1).trans ((primeLevelEquiv A B p lam hp M
        q n).apply_symm_apply _)
  have h5 : primeLevelEquiv A B p lam hp M (q + 1) n ((completedHomotopy A B p lam hp M (q + 1)
      (primeCompletedDifferential A B p lam hp M nabla (q + 1) y)).val n) =
      hn A B p lam hp M n (q + 1) (dYn A B p lam hp M nabla S' n (q + 1) (primeLevelEquiv A B p lam
          hp M (q + 1) n (y.val n))) := by
    refine (congrArg (primeLevelEquiv A B p lam hp M (q + 1) n) h1').trans ?_
    refine ((primeLevelEquiv A B p lam hp M (q + 1) n).apply_symm_apply _).trans ?_
    exact congrArg (hn A B p lam hp M n (q + 1)) (primeLevel_differential A B p lam hp M nabla S' n
        (q + 1) y)
  refine (congrArg₂ (· + ·) h4 h5).trans ?_
  refine (hn_dYn_succ A B p lam hp M nabla hint S S' n q _).trans ?_
  have h6 : primeLevelEquiv A B p lam hp M (q + 1) n ((p • y - primeCompletedComparison A B p lam hp
      M (q + 1) (completedReverse A B p lam hp M nabla hint S S' (q + 1) y)).val n) =
      p • primeLevelEquiv A B p lam hp M (q + 1) n (y.val n) - primeLevelEquiv A B p lam hp M
          (q + 1) n ((primeCompletedComparison A B p lam hp M (q + 1) (completedReverse A B p lam hp
          M nabla hint S S' (q + 1) y)).val n) :=
    (congrArg (primeLevelEquiv A B p lam hp M (q + 1) n) (map_sub (AdicCompletion.eval _ _ n) _
        _)).trans
      ((map_sub _ _ _).trans (congrArg (· - _) ((congrArg (primeLevelEquiv A B p lam hp M (q + 1) n)
        (map_nsmul (AdicCompletion.eval _ _ n) p y)).trans (map_nsmul _ p _))))
  refine Eq.trans ?_ h6.symm
  refine congrArg (p • primeLevelEquiv A B p lam hp M (q + 1) n (y.val n) - ·) ?_
  refine Eq.trans ?_
    (primeLevel_comparison A B p lam hp M nabla hint S S' n (q + 1) (completedReverse A B p lam hp M
        nabla hint S S' (q + 1) y)).symm
  exact congrArg (cn A B p lam hp M nabla hint S S' n (q + 1))
    (((baseLevelEquiv A B p M (q + 1) n).apply_symm_apply _).symm.trans (congrArg (baseLevelEquiv A
        B p M (q + 1) n) h2).symm)


end Completed

end PthRootExtension

end Crystalline
