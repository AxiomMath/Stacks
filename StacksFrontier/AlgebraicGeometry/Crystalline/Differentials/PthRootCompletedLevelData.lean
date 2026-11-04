module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedLevels

/-!
# The reverse maps of Tag 07N1 at the levels `pⁿ`, and their compatibility

For a module `M` over a divided power ring `B` with an integrable completed connection `∇`, the
level connections `∇_n` on `M_n = M / pⁿ M` are integrable connections in the sense of
[Stacks, Tag 07I0], so the uncompleted form of [Stacks, Lemma 60.25.3, Tag 07N1] applies to each
of them: the canonical map `c_n` of de Rham complexes along `B → B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))`
has a reverse map `e_n` with `e_n ∘ c_n = p` and `c_n ∘ e_n = p - d h_n - h_n d`, where `h_n` is
the integrating homotopy of the extension. This module shows that the `e_n` and `h_n` are
compatible with the transition maps `M_k → M_m`, which is what lets them be assembled into maps of
the completed complexes.

The compatibility is not a choice: `c_m` is injective, and every term of
`c_m ∘ e_m = p - d h - h d` is natural in the module — the canonical map by its value on wedges,
the extended connections because the transition maps are horizontal, and the integrating
homotopy by `Crystalline.PthRootExtension.pthRootHomotopy_naturality`.

## Main definitions

* `Crystalline.PthRootExtension.levelComparison` — the canonical map `c_n` of [Stacks, Tag 07PY]
  for `M_n`.
* `Crystalline.PthRootExtension.levelReverse` — the reverse map `e_n`.

## Main results

* `Crystalline.PthRootExtension.levelReverse_transition` — the `e_n` are compatible with the
  transition maps.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u w

namespace Crystalline

namespace CompletedLevels

/-! ### Assembling maps of completions from compatible level maps -/

section Levelwise

variable {R R' : Type*} [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') {X Y : Type*}
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R' Y]

/-- **The additive map of completions assembled from compatible additive maps of the levels.** -/
def levelwiseAddHom (F : ∀ n : ℕ, (X ⧸ (I ^ n • ⊤ : Submodule R X)) →+
      (Y ⧸ (I' ^ n • ⊤ : Submodule R' Y)))
    (hF : ∀ {m k : ℕ} (h : m ≤ k) (x : X ⧸ (I ^ k • ⊤ : Submodule R X)),
      AdicCompletion.transitionMap I' Y h (F k x) = F m (AdicCompletion.transitionMap I X h x)) :
    AdicCompletion I X →+ AdicCompletion I' Y where
  toFun x := ⟨fun n ↦ F n (x.val n), fun {m k} h ↦
    (hF h (x.val k)).trans (congrArg (F m) (x.property h))⟩
  map_zero' := AdicCompletion.ext fun n ↦ map_zero (F n)
  map_add' x y := AdicCompletion.ext fun n ↦ map_add (F n) (x.val n) (y.val n)

/-- The levels of the assembled map are the given level maps. -/
@[simp] theorem levelwiseAddHom_val (F : ∀ n : ℕ, (X ⧸ (I ^ n • ⊤ : Submodule R X)) →+
      (Y ⧸ (I' ^ n • ⊤ : Submodule R' Y)))
    (hF : ∀ {m k : ℕ} (h : m ≤ k) (x : X ⧸ (I ^ k • ⊤ : Submodule R X)),
      AdicCompletion.transitionMap I' Y h (F k x) = F m (AdicCompletion.transitionMap I X h x))
    (x : AdicCompletion I X) (n : ℕ) :
    (levelwiseAddHom I I' F hF x).val n = F n (x.val n) := rfl

/-- **A completed complex is a complex as soon as its levels are**: if the levels of the
differentials of a family of completions are identified with the differentials of a family of
complexes, the differentials of the completions compose to zero. -/
theorem comp_eq_zero_of_levels {R : Type*} [CommRing R] (I : Ideal R) {X : ℕ → Type*}
    [∀ q, AddCommGroup (X q)] [∀ q, Module R (X q)]
    (d : ∀ q, AdicCompletion I (X q) →+ AdicCompletion I (X (q + 1)))
    {Y : ℕ → ℕ → Type*} [∀ q n, AddCommGroup (Y q n)]
    (α : ∀ q n, (X q ⧸ (I ^ n • ⊤ : Submodule R (X q))) ≃+ Y q n)
    (dY : ∀ n q, Y q n →+ Y (q + 1) n)
    (hd : ∀ n q x, α (q + 1) n ((d q x).val n) = dY n q (α q n (x.val n)))
    (hsq : ∀ n q t, dY n (q + 1) (dY n q t) = 0) (q : ℕ) :
    (d (q + 1)).comp (d q) = 0 := by
  refine AddMonoidHom.ext fun x ↦ AdicCompletion.ext fun n ↦ (α (q + 1 + 1) n).injective ?_
  refine (hd n (q + 1) (d q x)).trans ?_
  refine (congrArg (dY n (q + 1)) (hd n q x)).trans ?_
  refine (hsq n q _).trans ?_
  exact (map_zero (α (q + 1 + 1) n)).symm

/-- Conjugating compatible maps by compatible identifications gives compatible maps. -/
theorem conj_compat {Q₁ Q₂ S₁ S₂ P₁ P₂ T₁ T₂ : Type*} [AddCommGroup Q₁] [AddCommGroup Q₂]
    [AddCommGroup S₁] [AddCommGroup S₂] [AddCommGroup P₁] [AddCommGroup P₂] [AddCommGroup T₁]
    [AddCommGroup T₂] (eX₁ : Q₁ ≃+ S₁) (eX₂ : Q₂ ≃+ S₂) (eY₁ : P₁ ≃+ T₁) (eY₂ : P₂ ≃+ T₂)
    (tX : Q₁ →+ Q₂) (tY : P₁ →+ P₂) (φ : S₁ →+ S₂) (ψ : T₁ →+ T₂) (E₁ : T₁ →+ S₁)
    (E₂ : T₂ →+ S₂) (hX : ∀ x, eX₂ (tX x) = φ (eX₁ x)) (hY : ∀ y, eY₂ (tY y) = ψ (eY₁ y))
    (hE : ∀ t, φ (E₁ t) = E₂ (ψ t)) (y : P₁) :
    tX (eX₁.symm (E₁ (eY₁ y))) = eX₂.symm (E₂ (eY₂ (tY y))) := by
  apply eX₂.injective
  rw [hX, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hY, hE]

end Levelwise

end CompletedLevels

namespace PthRootExtension

open CompletedLevels

/-! ### Naturality of the uncompleted constructions -/

section Naturality

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0)

/-- **The base change of connections is natural along horizontal maps.** -/
theorem primeConnection_baseChange_map {M₁ M₂ : Type w} [AddCommGroup M₁] [Module (B : Type u) M₁]
    [AddCommGroup M₂] [Module (B : Type u) M₂]
    (nab₁ : Connection A (B : Type u) (baseFormsProjection A B) M₁)
    (nab₂ : Connection A (B : Type u) (baseFormsProjection A B) M₂) (f : M₁ →ₗ[(B : Type u)] M₂)
    (hf : ∀ m, nab₂ (f m) = TensorProduct.map f LinearMap.id (nab₁ m))
    (y : primeRing B p lam ⊗[(B : Type u)] M₁) :
    primeConnection A B p lam hp M₂ nab₂ (f.baseChange (primeRing B p lam) y) =
      TensorProduct.map (f.baseChange (primeRing B p lam)) LinearMap.id
        (primeConnection A B p lam hp M₁ nab₁ y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb =>
    rw [map_add, Connection.map_add, ha, hb, Connection.map_add, map_add]
  | tmul b' m =>
    have h1 := Connection.baseChange_tmul (primeFormsComparison A B p lam hp) nab₂
      (primeFormsComparison_dividedPowerDifferential A B p lam hp) b' (f m)
    have h2 := Connection.baseChange_tmul (primeFormsComparison A B p lam hp) nab₁
      (primeFormsComparison_dividedPowerDifferential A B p lam hp) b' m
    have key : ∀ t : M₁ ⊗[(B : Type u)] baseForms A B,
        Connection.baseChangeValues (primeFormsComparison A B p lam hp)
            (TensorProduct.map f LinearMap.id t) =
          TensorProduct.map (f.baseChange (primeRing B p lam)) LinearMap.id
            (Connection.baseChangeValues (primeFormsComparison A B p lam hp) t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a w => simp [Connection.baseChangeValues_tmul]
      | add a b ha hb => simp only [map_add, ha, hb]
    rw [LinearMap.baseChange_tmul]
    refine h1.trans ?_
    refine Eq.trans ?_ (congrArg (TensorProduct.map (f.baseChange (primeRing B p lam))
      LinearMap.id) h2).symm
    rw [hf, map_add, map_smul, key, TensorProduct.map_tmul, LinearMap.baseChange_tmul,
      LinearMap.id_apply]

/-- **The canonical map of de Rham complexes is natural in the module**: any two families with the
characterising value on wedges commute with the maps induced by a `B`-linear map. -/
theorem comparison_naturality {M₁ M₂ : Type w} [AddCommGroup M₁] [Module (B : Type u) M₁]
    [AddCommGroup M₂] [Module (B : Type u) M₂] (f : M₁ →ₗ[(B : Type u)] M₂) (q : ℕ)
    (c₁ : RestrictScalars A (B : Type u) (baseDeRhamTerm A B M₁ q) →ₗ[A]
      RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M₁ q))
    (c₂ : RestrictScalars A (B : Type u) (baseDeRhamTerm A B M₂ q) →ₗ[A]
      RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M₂ q))
    (hc₁ : ∀ (m : M₁) (omega : Fin q → baseForms A B),
      c₁ (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam hp) ∘ omega))
    (hc₂ : ∀ (m : M₂) (omega : Fin q → baseForms A B),
      c₂ (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam hp) ∘ omega))
    (x : baseDeRhamTerm A B M₁ q) :
    c₂ (baseTermMap A B f q x) = primeTermMap A B p lam hp f q (c₁ x) := by
  have := tensorExteriorPower_addMonoidHom_ext
    (F := (c₂.toAddMonoidHom.comp (baseTermMap A B f q).toAddMonoidHom))
    (G := ((primeTermMap A B p lam hp f q).toAddMonoidHom.comp c₁.toAddMonoidHom))
    (fun m v ↦ by
      show c₂ (f m ⊗ₜ exteriorPower.ιMulti (B : Type u) q v) =
        primeTermMap A B p lam hp f q (c₁ (m ⊗ₜ exteriorPower.ιMulti (B : Type u) q v))
      rw [hc₂, hc₁, TensorProduct.map_tmul, LinearMap.baseChange_tmul, LinearMap.id_apply])
  exact DFunLike.congr_fun this x

end Naturality

/-! ### The level data -/

section LevelData

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0) [Nontrivial (XiAlg B)] [Fact p.Prime]
  [Algebra (IntegersAtPrime p) (B : Type u)] (M : Type u) [AddCommGroup M] [Module (B : Type u) M]
  (nabla : CompletedConnection p (B : Type u) (completedDividedPowerForms p A B.dividedPowers 1)
    (completedDividedPowerDifferentialOnRing p A B.dividedPowers) M)
  (hint : IsCompletedIntegrable p A (B : Type u) B.dividedPowers M nabla)
  (S : SourceDeRham A (B : Type u)) (S' : SourceDeRham A (primeRing B p lam))

/-- The level connection `∇_n` on `M_n`. -/
abbrev levelNabla (n : ℕ) :=
  levelConnection p A (B : Type u) B.dividedPowers M nabla n

include hint in
/-- The level connections of an integrable completed connection are integrable. -/
theorem levelNabla_integrable (n : ℕ) :
    Connection.IsIntegrable S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
      (baseFormsGenerationHypothesis A B S) (levelNabla A B p M nabla n) :=
  isIntegrable_levelConnection p A (B : Type u) B.dividedPowers M nabla S hint n

include hint in
/-- The canonical map of [Stacks, Tag 07PY] for `M_n` exists. -/
theorem exists_levelComparison (n : ℕ) :
    ∃ c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (baseDeRhamTerm A B (levelModule p (B : Type u) M n) q) →ₗ[A]
        RestrictScalars A (primeRing B p lam)
          (primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M n) q),
      (∀ (q : ℕ) (m : levelModule p (B : Type u) M n) (omega : Fin q → baseForms A B),
        c q (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
          (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
            exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam
                hp) ∘ omega)) ∧
      (∀ (q : ℕ) (x : levelModule p (B : Type u) M n ⊗[(B : Type u)]
          (⋀[(B : Type u)]^q (baseForms A B))),
        c (q + 1) ((baseExtended A B (levelModule p (B : Type u) M n) S
          (levelNabla A B p M nabla n)).toLinearMap q x) =
          (primeExtended A B p lam hp (levelModule p (B : Type u) M n) S'
            (levelNabla A B p M nabla n)).toLinearMap q (c q x)) :=
  (existsUnique_baseChangeDeRhamMap S S' (baseFormsProjection A B)
    (primeFormsProjection A B p lam hp) (Submodule.mkQ_surjective _)
    (baseFormsGenerationHypothesis A B S) (Submodule.mkQ_surjective _)
    (primeFormsGenerationHypothesis A B p lam hp S') (primeFormsComparison A B p lam hp)
    (primeFormsComparison_dividedPowerDifferential A B p lam hp) (levelNabla A B p M nabla n)
    (levelNabla_integrable A B p M nabla hint S n)).exists

/-- **The canonical map `c_n` of [Stacks, Tag 07PY] for `M_n`.** -/
def levelComparison (n : ℕ) := Classical.choose
  (exists_levelComparison A B p lam hp M nabla hint S S' n)

/-- The level canonical map on a tensor of a wedge. -/
theorem levelComparison_wedge (n q : ℕ) (m : levelModule p (B : Type u) M n)
    (omega : Fin q → baseForms A B) :
    levelComparison A B p lam hp M nabla hint S S' n q
        (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
      (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
        exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam hp) ∘ omega) :=
  (Classical.choose_spec (exists_levelComparison A B p lam hp M nabla hint S S' n)).1 q m omega

/-- The level canonical map commutes with the extended connections. -/
theorem levelComparison_comm (n q : ℕ) (x : levelModule p (B : Type u) M n ⊗[(B : Type u)]
    (⋀[(B : Type u)]^q (baseForms A B))) :
    levelComparison A B p lam hp M nabla hint S S' n (q + 1)
        ((baseExtended A B (levelModule p (B : Type u) M n) S
          (levelNabla A B p M nabla n)).toLinearMap q x) =
      (primeExtended A B p lam hp (levelModule p (B : Type u) M n) S'
        (levelNabla A B p M nabla n)).toLinearMap q
        (levelComparison A B p lam hp M nabla hint S S' n q x) :=
  (Classical.choose_spec (exists_levelComparison A B p lam hp M nabla hint S S' n)).2 q x

/-- **The reverse map `e_n`** of Tag 07N1 for `M_n`. -/
def levelReverse (n : ℕ) := Classical.choose
  (exists_reverse_pthRootExtension A B p lam hp (levelModule p (B : Type u) M n) S S'
    (levelNabla A B p M nabla n) (levelNabla_integrable A B p M nabla hint S n)
    (levelComparison A B p lam hp M nabla hint S S' n)
    (levelComparison_wedge A B p lam hp M nabla hint S S' n)
    (levelComparison_comm A B p lam hp M nabla hint S S' n))

/-- The existence statement of the reverse map `e_n`, which `levelReverse` is chosen from. -/
private abbrev levelReverse_exists (n : ℕ) :=
  exists_reverse_pthRootExtension A B p lam hp (levelModule p (B : Type u) M n) S S'
    (levelNabla A B p M nabla n) (levelNabla_integrable A B p M nabla hint S n)
    (levelComparison A B p lam hp M nabla hint S S' n)
    (levelComparison_wedge A B p lam hp M nabla hint S S' n)
    (levelComparison_comm A B p lam hp M nabla hint S S' n)

/-- The reverse map is a map of complexes. -/
theorem levelReverse_comm (n q : ℕ)
    (x : RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp (levelModule p (B :
        Type u) M n) q)) :
    levelReverse A B p lam hp M nabla hint S S' n (q + 1) ((primeExtended A B p lam hp (levelModule
        p (B : Type u) M n) S' (levelNabla A B p M nabla n)).toLinearMap q x) = (baseExtended A B
        (levelModule p (B : Type u) M n) S (levelNabla A B p M nabla n)).toLinearMap q (levelReverse
        A B p lam hp M nabla hint S S' n q x) :=
  (Classical.choose_spec (levelReverse_exists A B p lam hp M nabla hint S S' n)).1 q x

/-- `e_n ∘ c_n = p` on the nose. -/
theorem levelReverse_comparison (n q : ℕ)
    (x : RestrictScalars A (B : Type u) (baseDeRhamTerm A B (levelModule p (B : Type u) M n) q)) :
    levelReverse A B p lam hp M nabla hint S S' n q (levelComparison A B p lam hp M nabla hint S S'
        n q x) =
      RestrictScalars.lsmul A (B : Type u) (baseDeRhamTerm A B (levelModule p (B : Type u) M n) q)
          ((p : ℕ) : (B : Type u)) x :=
  (Classical.choose_spec (levelReverse_exists A B p lam hp M nabla hint S S' n)).2.2.1 q x

/-- `c_n ∘ e_n = p - h_n d` in degree zero. -/
theorem levelReverse_homotopy_zero (n : ℕ)
    (x : RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp (levelModule p (B :
        Type u) M n) 0)) :
    pthRootHomotopy A B p lam hp (levelModule p (B : Type u) M n) 0 ((primeExtended A B p lam hp
        (levelModule p (B : Type u) M n) S' (levelNabla A B p M nabla n)).toLinearMap 0 x) =
      RestrictScalars.lsmul A (primeRing B p lam) (primeDeRhamTerm A B p lam hp (levelModule p (B :
          Type u) M n) 0)
          (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u))) x -
        levelComparison A B p lam hp M nabla hint S S' n 0 (levelReverse A B p lam hp M nabla hint S
            S' n 0 x) :=
  (Classical.choose_spec (levelReverse_exists A B p lam hp M nabla hint S S' n)).2.2.2.1 x

/-- `c_n ∘ e_n = p - d h_n - h_n d` in positive degree. -/
theorem levelReverse_homotopy_succ (n q : ℕ)
    (x : RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp (levelModule p (B :
        Type u) M n) (q + 1))) :
    (show RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp (levelModule p (B :
        Type u) M n) (q + 1)) from
        (primeExtended A B p lam hp (levelModule p (B : Type u) M n) S' (levelNabla A B p M nabla
            n)).toLinearMap q (pthRootHomotopy A B p lam hp (levelModule p (B : Type u) M n) q
            x)) + pthRootHomotopy A B p lam hp (levelModule p (B : Type u) M n) (q + 1)
            ((primeExtended A B p lam hp (levelModule p (B : Type u) M n) S' (levelNabla A B p M
            nabla n)).toLinearMap (q + 1) x) =
      RestrictScalars.lsmul A (primeRing B p lam) (primeDeRhamTerm A B p lam hp (levelModule p (B :
          Type u) M n) (q + 1))
          (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u))) x -
        levelComparison A B p lam hp M nabla hint S S' n (q + 1) (levelReverse A B p lam hp M nabla
            hint S S' n (q + 1) x) :=
  (Classical.choose_spec (levelReverse_exists A B p lam hp M nabla hint S S' n)).2.2.2.2 q x

section Transition

variable {m k : ℕ} (hmk : m ≤ k)

/-- The transition map `M_k → M_m`. -/
abbrev levelTransition : levelModule p (B : Type u) M k →ₗ[(B : Type u)] levelModule p (B : Type u)
    M m :=
  AdicCompletion.transitionMap (pAdicIdeal (A := (B : Type u)) p) M hmk

/-- The transition maps are horizontal for the level connections. -/
theorem levelNabla_transition (x : levelModule p (B : Type u) M k) :
    levelNabla A B p M nabla m (levelTransition B p M hmk x) =
      TensorProduct.map (levelTransition B p M hmk) LinearMap.id (levelNabla A B p M nabla k x) :=
  levelConnection_transitionMap p A (B : Type u) B.dividedPowers M nabla hmk x

/-- The extended level connections commute with the transition maps. -/
theorem baseExtended_transition (q : ℕ) (x : baseDeRhamTerm A B (levelModule p (B : Type u) M k) q)
    :
    (baseExtended A B (levelModule p (B : Type u) M m) S (levelNabla A B p M nabla m)).toLinearMap q
        (baseTermMap A B (levelTransition B p M hmk) q x) =
      baseTermMap A B (levelTransition B p M hmk) (q + 1)
        ((baseExtended A B (levelModule p (B : Type u) M k) S
          (levelNabla A B p M nabla k)).toLinearMap q x) :=
  extendedConnection_map S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
    (baseFormsGenerationHypothesis A B S) (levelNabla A B p M nabla k) (levelNabla A B p M nabla m)
    (levelTransition B p M hmk) (levelNabla_transition A B p M nabla hmk) q x

/-- The extended base-changed level connections commute with the transition maps. -/
theorem primeExtended_transition (q : ℕ)
    (y : primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M k) q) :
    (primeExtended A B p lam hp (levelModule p (B : Type u) M m) S'
        (levelNabla A B p M nabla m)).toLinearMap q
        (primeTermMap A B p lam hp (levelTransition B p M hmk) q y) =
      primeTermMap A B p lam hp (levelTransition B p M hmk) (q + 1)
        ((primeExtended A B p lam hp (levelModule p (B : Type u) M k) S'
          (levelNabla A B p M nabla k)).toLinearMap q y) :=
  extendedConnection_map S' (primeFormsProjection A B p lam hp) (Submodule.mkQ_surjective _)
    (primeFormsGenerationHypothesis A B p lam hp S')
    (primeConnection A B p lam hp _ (levelNabla A B p M nabla k))
    (primeConnection A B p lam hp _ (levelNabla A B p M nabla m))
    ((levelTransition B p M hmk).baseChange (primeRing B p lam))
    (primeConnection_baseChange_map A B p lam hp (levelNabla A B p M nabla k)
      (levelNabla A B p M nabla m) (levelTransition B p M hmk)
      (levelNabla_transition A B p M nabla hmk)) q y

/-- The transition maps commute with multiplication by `p`. -/
theorem primeTermMap_lsmul (q : ℕ) (y : primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M
    k) q) :
    primeTermMap A B p lam hp (levelTransition B p M hmk) q (RestrictScalars.lsmul A (primeRing B p
        lam) (primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M k) q)
        (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u))) y) =
      RestrictScalars.lsmul A (primeRing B p lam) (primeDeRhamTerm A B p lam hp (levelModule p (B :
          Type u) M m) q)
        (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u))) (primeTermMap A B p
            lam hp (levelTransition B p M hmk) q y) :=
  (primeTermMap A B p lam hp (levelTransition B p M hmk) q).map_smul _ y

/-- The transition maps carry the homotopy `h_k` of the extended differential to `h_m`. -/
private theorem primeTermMap_homotopy_extended (q : ℕ)
    (y : primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M k) q) :
    primeTermMap A B p lam hp (levelTransition B p M hmk) q (pthRootHomotopy A B p lam hp
        (levelModule p (B : Type u) M k) q ((primeExtended A B p lam hp
        (levelModule p (B : Type u) M k) S' (levelNabla A B p M nabla k)).toLinearMap q y)) =
      pthRootHomotopy A B p lam hp (levelModule p (B : Type u) M m) q ((primeExtended A B p lam hp
        (levelModule p (B : Type u) M m) S' (levelNabla A B p M nabla m)).toLinearMap q
        (primeTermMap A B p lam hp (levelTransition B p M hmk) q y)) :=
  (pthRootHomotopy_naturality A B p lam hp (levelTransition B p M hmk) q _).symm.trans
    (congrArg (pthRootHomotopy A B p lam hp (levelModule p (B : Type u) M m) q)
      (primeExtended_transition A B p lam hp M nabla S' hmk q y).symm)

/-- The Cartan remainder `c_n ∘ e_n` is compatible with the transition maps, in degree zero. -/
theorem levelComparison_reverse_transition_zero (y : primeDeRhamTerm A B p lam hp (levelModule p (B
    : Type u) M k) 0) :
    primeTermMap A B p lam hp (levelTransition B p M hmk) 0 (levelComparison A B p lam hp M nabla
        hint S S' k 0 (levelReverse A B p lam hp M nabla hint S S' k 0 y)) = levelComparison A B p
        lam hp M nabla hint S S' m 0 (levelReverse A B p lam hp M nabla hint S S' m 0 (primeTermMap
        A B p lam hp (levelTransition B p M hmk) 0 y)) := by
  have hk := eq_sub_iff_add_eq.mp (levelReverse_homotopy_zero A B p lam hp M nabla hint S S' k y)
  have hm := eq_sub_iff_add_eq.mp
    (levelReverse_homotopy_zero A B p lam hp M nabla hint S S' m (primeTermMap A B p lam hp
        (levelTransition B p M hmk) 0 y))
  have hk' := ((primeTermMap A B p lam hp (levelTransition B p M hmk) 0).map_add _ _).symm.trans
    ((congrArg (primeTermMap A B p lam hp (levelTransition B p M hmk) 0) hk).trans
      (primeTermMap_lsmul A B p lam hp M hmk 0 y))
  exact add_left_cancel ((congrArg (· + _)
    (primeTermMap_homotopy_extended A B p lam hp M nabla S' hmk 0 y)).symm.trans
      (hk'.trans hm.symm))

/-- The Cartan remainder `c_n ∘ e_n` is compatible with the transition maps, in positive
degree. -/
theorem levelComparison_reverse_transition_succ (q : ℕ)
    (y : primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M k) (q + 1)) :
    primeTermMap A B p lam hp (levelTransition B p M hmk) (q + 1) (levelComparison A B p lam hp M
        nabla hint S S' k (q + 1) (levelReverse A B p lam hp M nabla hint S S' k (q + 1) y)) =
        levelComparison A B p lam hp M nabla hint S S' m (q + 1) (levelReverse A B p lam hp M nabla
        hint S S' m (q + 1) (primeTermMap A B p lam hp (levelTransition B p M hmk) (q + 1) y)) := by
  have hk := eq_sub_iff_add_eq.mp (levelReverse_homotopy_succ A B p lam hp M nabla hint S S' k q y)
  have hm := eq_sub_iff_add_eq.mp
    (levelReverse_homotopy_succ A B p lam hp M nabla hint S S' m q (primeTermMap A B p lam hp
        (levelTransition B p M hmk) (q + 1) y))
  have na := (primeExtended_transition A B p lam hp M nabla S' hmk q (pthRootHomotopy A B p lam hp
        (levelModule p (B : Type u) M k) q y)).symm.trans
      (congrArg ((primeExtended A B p lam hp (levelModule p (B : Type u) M m) S' (levelNabla A B p M
          nabla m)).toLinearMap q)
        (pthRootHomotopy_naturality A B p lam hp (levelTransition B p M hmk) q y).symm)
  have hk' := ((primeTermMap A B p lam hp (levelTransition B p M hmk) (q + 1)).map_add _
      _).symm.trans
    ((congrArg (primeTermMap A B p lam hp (levelTransition B p M hmk) (q + 1)) hk).trans
      (primeTermMap_lsmul A B p lam hp M hmk (q + 1) y))
  have hk'' := (congrArg (· + _) ((primeTermMap A B p lam hp (levelTransition B p M hmk)
      (q + 1)).map_add _ _)).symm.trans hk'
  exact add_left_cancel ((congrArg₂
    (fun a b : primeDeRhamTerm A B p lam hp (levelModule p (B : Type u) M m) (q + 1) ↦ a + b + _) na
    (primeTermMap_homotopy_extended A B p lam hp M nabla S' hmk (q + 1) y)).symm.trans
      (hk''.trans hm.symm))

/-- **The reverse maps `e_n` are compatible with the transition maps.** -/
theorem levelReverse_transition (q : ℕ) (y : primeDeRhamTerm A B p lam hp (levelModule p (B : Type
    u) M k) q) :
    baseTermMap A B (levelTransition B p M hmk) q (levelReverse A B p lam hp M nabla hint S S' k q
        y) = levelReverse A B p lam hp M nabla hint S S' m q (primeTermMap A B p lam hp
        (levelTransition B p M hmk) q y) := by
  refine injective_pthRootComparison A B p lam hp (levelModule p (B : Type u) M m) q
      (levelComparison A B p lam hp M nabla hint S S' m q)
    (levelComparison_wedge A B p lam hp M nabla hint S S' m q)
    ((comparison_naturality A B p lam hp (levelTransition B p M hmk) q (levelComparison A B p lam hp
        M nabla hint S S' k q) (levelComparison A B p lam hp M nabla hint S S' m q)
      (levelComparison_wedge A B p lam hp M nabla hint S S' k q)
      (levelComparison_wedge A B p lam hp M nabla hint S S' m q) (levelReverse A B p lam hp M nabla
          hint S S' k q y)).trans ?_)
  cases q with
  | zero => exact levelComparison_reverse_transition_zero A B p lam hp M nabla hint S S' hmk y
  | succ q => exact levelComparison_reverse_transition_succ A B p lam hp M nabla hint S S' hmk q y

end Transition

end LevelData

end PthRootExtension

end Crystalline
