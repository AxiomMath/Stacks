module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.DirectImageEpi
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FreeDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.ExactOnAffineOpens

/-!
# `π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))` is surjective

For `K ∈ Quot^P(T)` with quotient map `q : 𝒪^{⊕ r} ⟶ 𝒬` and `m = regularityIndex n r P`, the
map `π_*(q(m)) : π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))` of modules on `T` is an epimorphism. This removes
the two fibrewise inputs of
`AlgebraicGeometry.ProjectiveQuot.epi_pushforward_twistMap_quotientπ_of_fibres`:

* the base-change morphism of `𝒪^{⊕ r}(m)` along `Spec κ(t) ⟶ T` is invertible
  (`AlgebraicGeometry.ProjectiveQuot.isIso_baseChangeNatTrans_twist_freeModule`);
* on the fibre `ℙⁿ_{κ(t)}` the map `Γ(𝒪^{⊕ r}(m)) ⟶ Γ(𝒬_t(m))` is onto, the choice of `m`
  (`AlgebraicGeometry.ProjectiveQuot.regularityIndex_spec`); on `Spec κ(t)`, whose only opens are
  `∅` and the whole space, that is an epimorphism of modules.

This is the surjection `W ⊗ 𝒪_T ⟶ π_*(𝒬(m))` of the proof of Stacks 0DPA.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.epi_pushforward_of_surjective_app_top`.
* `AlgebraicGeometry.ProjectiveQuot.epi_pushforward_pullback_fibreMap_twistMap_quotientπ`.
* `AlgebraicGeometry.ProjectiveQuot.epi_pushforward_twistMap_quotientπ`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProjectiveQuot

/-- Sections over the empty open of a sheaf of modules on a scheme form a subsingleton. -/
theorem subsingleton_sections_bot {X : Scheme.{u}} (M : X.Modules) :
    Subsingleton (M.val.obj (op ⊥)) := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
  exact AddCommGrpCat.isZero_iff_subsingleton.mp
    (IsZero.of_iso (isZero_zero AddCommGrpCat)
      ((isZero_zero AddCommGrpCat).isTerminal.uniqueUpToIso F.isTerminalOfEmpty).symm)

/-- **On the spectrum of a field a direct image is onto as soon as it is on global sections**:
the only opens of `Spec k` are `∅`, where there is nothing to hit, and `Spec k` itself. -/
theorem epi_pushforward_of_surjective_app_top (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {M N : X.Modules} (φ : M ⟶ N)
    (hφ : Function.Surjective (φ.app ⊤)) : Epi ((Scheme.Modules.pushforward f).map φ) := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  refine Scheme.epi_of_surjective_of_isAffineOpen _ fun U _ => ?_
  by_cases hU : U = ⊤
  · subst hU
    exact hφ
  · have hbot : U = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hU
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rwa [Subsingleton.elim y x]
    subst hbot
    have := subsingleton_sections_bot ((Scheme.Modules.pushforward f).obj N)
    exact fun y => ⟨0, Subsingleton.elim _ _⟩

/-- Surjectivity on sections over an open passes to a composite. -/
theorem surjective_app_comp {X : Scheme.{u}} {A B C : X.Modules} (a : A ⟶ B) (b : B ⟶ C)
    (U : X.Opens) (ha : Function.Surjective (a.app U)) (hb : Function.Surjective (b.app U)) :
    Function.Surjective ((a ≫ b).app U) := by
  intro z
  obtain ⟨y, rfl⟩ := hb z
  obtain ⟨x, rfl⟩ := ha y
  exact ⟨x, rfl⟩

/-- Surjectivity on sections over an open passes to the second factor of a composite. -/
theorem surjective_app_of_comp {X : Scheme.{u}} {A B C : X.Modules} (a : A ⟶ B) (b : B ⟶ C)
    (U : X.Opens) (h : Function.Surjective ((a ≫ b).app U)) :
    Function.Surjective (b.app U) := by
  intro z
  obtain ⟨x, rfl⟩ := h z
  exact ⟨a.app U x, rfl⟩

/-- An isomorphism of modules is bijective on sections. -/
theorem surjective_app_of_isIso {X : Scheme.{u}} {A B : X.Modules} (a : A ⟶ B) [IsIso a]
    (U : X.Opens) : Function.Surjective (a.app U) :=
  (ConcreteCategory.bijective_of_isIso (a.app U)).2

variable {n r : ℕ}

/-- The twist of a morphism is the twist functor applied to it. -/
theorem twistMap_eq_twistFunctor_map {T : Scheme.{u}} (d : ℤ)
    {F G : (projectiveSpaceOver n T).Modules} (φ : F ⟶ G) :
    twistMap d φ = (twistFunctor n T d).map φ :=
  (congrArg (fun x => ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projectiveSpaceOver n T).toSheafedSpace.presheaf,
        (projectiveSpaceOver n T).toSheafedSpace.IsSheaf⟩).map φ).app (twistingSheaf n T d) ≫ x)
    (CategoryTheory.Functor.map_id ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(projectiveSpaceOver n T).toSheafedSpace.presheaf,
        (projectiveSpaceOver n T).toSheafedSpace.IsSheaf⟩).obj G) (twistingSheaf n T d))).trans
    (Category.comp_id _)

variable {P : Polynomial ℚ}

/-- **The fibre map on sections is onto.** For `K ∈ Quot^P(T)`, `m = regularityIndex n r P`
and `t ∈ T`, the map `Γ(ℙⁿ_{κ(t)}, 𝒪^{⊕ r}(m)) ⟶ Γ(ℙⁿ_{κ(t)}, 𝒬_t(m))`, read on the pullbacks
of the twists along `ℙⁿ_{κ(t)} ⟶ ℙⁿ_T`, is onto; so is its direct image to `Spec κ(t)`. -/
theorem epi_pushforward_pullback_fibreMap_twistMap_quotientπ {T : Scheme.{u}}
    {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) (t : T) :
    Epi ((Scheme.Modules.pushforward
      (projectiveSpaceOver n (Spec (T.residueField t)) ↘ Spec (T.residueField t))).map
        ((Scheme.Modules.pullback (fibreMap n t)).map
          (twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K)))) := by
  obtain ⟨hcoh, hval⟩ := hK.2 t
  let q : freeModules (T.residueField t) n r ⟶ fibre t (quotient K) :=
    baseChangeQuotientMap (T.fromSpecResidueField t) K
  have : Epi q := inferInstanceAs (Epi (baseChangeQuotientMap (T.fromSpecResidueField t) K))
  obtain ⟨-, -, -, hsurj, -⟩ := regularityIndex_spec n r P (T.residueField t)
    (fibre t (quotient K)) q hval
  let f := projectiveSpaceOverRing n (.of (T.residueField t)) ↘ Spec (.of (T.residueField t))
  -- the pulled-back quotient map is the free-module identification followed by `q`
  have hpb : (Scheme.Modules.pullback (fibreMap n t)).map (quotientπ K) =
      (freeModulePullbackIso n r (T.fromSpecResidueField t)).hom ≫ q := by
    change _ = _ ≫ (freeModulePullbackIso n r (T.fromSpecResidueField t)).inv ≫ _
    rw [Iso.hom_inv_id_assoc]
  have h₁ : Function.Surjective
      ((twistMap (regularityIndex.{u} n r P : ℤ)
        ((Scheme.Modules.pullback (fibreMap n t)).map (quotientπ K))).app ⊤) := by
    rw [hpb, twistMap_eq_twistFunctor_map, Functor.map_comp]
    -- surjectivity of `Γ(q(m))`
    refine surjective_app_comp _ _ _ (surjective_app_of_isIso _ _) fun z => ?_
    let eQ := cohomologyOverFieldZeroLinearIso (T.residueField t) f
      ((twistFunctorModules (T.residueField t) n (regularityIndex.{u} n r P)).obj
        (fibre t (quotient K)))
    obtain ⟨a, ha⟩ := hsurj (eQ.inv z)
    refine ⟨(cohomologyOverFieldZeroLinearIso (T.residueField t) f _).hom a, ?_⟩
    have h := cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap (T.residueField t) f
      ((twistFunctorModules (T.residueField t) n (regularityIndex.{u} n r P)).map q) a
    rw [ha] at h
    exact h.symm.trans (eQ.inv_hom_id_apply z)
  refine epi_pushforward_of_surjective_app_top (T.residueField t) _ _ ?_
  refine surjective_app_of_comp (twistPullbackIso (T.fromSpecResidueField t)
    (regularityIndex.{u} n r P : ℤ) (freeModule n r T)).hom _ _ ?_
  rw [← twistPullbackIso_hom_naturality (T.fromSpecResidueField t)
    (regularityIndex.{u} n r P : ℤ) (quotientπ K)]
  exact surjective_app_comp _ _ _ h₁ (surjective_app_of_isIso _ _)

/-- **`π_*(q(m)) : π_*(𝒪^{⊕ r}(m)) ⟶ π_*(𝒬(m))` is surjective** for `K ∈ Quot^P(T)` and
`m = regularityIndex n r P`. -/
theorem epi_pushforward_twistMap_quotientπ {T : Scheme.{u}}
    {K : Subobject (freeModule n r T)} (hK : K ∈ hilbertFamilies n r P T) :
    Epi ((Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).map
      (twistMap (regularityIndex.{u} n r P : ℤ) (quotientπ K))) :=
  epi_pushforward_twistMap_quotientπ_of_fibres hK
    (fun t => isIso_baseChangeNatTrans_twist_freeModule n r (T.fromSpecResidueField t) _)
    (fun t => epi_pushforward_pullback_fibreMap_twistMap_quotientπ hK t)

end AlgebraicGeometry.ProjectiveQuot

end
