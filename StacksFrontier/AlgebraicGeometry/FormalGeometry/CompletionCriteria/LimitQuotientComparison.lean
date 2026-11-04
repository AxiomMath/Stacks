module

public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.MittagLefflerCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteModuleModel

/-!
# Coherence and injectivity of the comparison with the quotients of the limit

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X \ V(𝔞)`. Let `(F_n)` be a coherent `I`-adic system
on `U`, let `M = limₙ H⁰(U, F_n)` be its module of compatible global sections, and put
`G_n = (M/Iⁿ⁺¹M)^~`.

Assume the limit topology on `M` agrees with its `I`-adic topology. This file proves that the
restrictions `G_n|_U` are again a coherent `I`-adic system on `U`, and that the canonical
comparison `(G_n|_U) ⟶ (F_n)` is a *monomorphism* of `Coh(U, I 𝒪_U)`. It is not asserted to be
an isomorphism: surjectivity is a separate hypothesis, supplied by the Mittag-Leffler condition
in Stacks 0EHF.

The topology hypothesis is exactly what makes `(M_n)` and `(M/IⁿM)` pro-isomorphic, where
`M_n ⊆ H⁰(U, F_n)` is the image of `M`. The half of that pro-isomorphism used here — every
`I`-adic neighbourhood of `0` in `M` contains the kernel of some projection — is
`exists_projection_ker_le_adicPower`.

## Main definitions

* `Stacks.Algebraization.LimitTopologyAgrees` — the hypothesis that the limit topology on `M`
  is its `I`-adic topology.
* `Stacks.Algebraization.limitQuotientSystem` — the inverse system `n ↦ M/Iⁿ⁺¹M` of
  `A`-modules, with the canonical quotient maps as transitions.
* `Stacks.Algebraization.limitQuotientSheaves` — the inverse system `n ↦ G_n|_U` on `U`.
* `Stacks.Algebraization.coherentLimitQuotientSystem` — that system as an object of
  `Coh(U, I 𝒪_U)`.
* `Stacks.Algebraization.comparison` — the canonical comparison, as a morphism of
  `Coh(U, I 𝒪_U)`.

## Main results

* `Stacks.Algebraization.limitQuotientSheaves_isCoherentAdicSystem` — conclusion (1) of
  Stacks 0EHG: each `G_n|_U` is coherent, and the system is `I`-adic.
* `Stacks.Algebraization.comparison_hom_app_limitSection` — the comparison is the canonical
  one: on sections over `U` it sends the section induced by `m ∈ M` to the `n`-th component
  of `m`.
* `Stacks.Algebraization.mono_comparison` — conclusion (2) of Stacks 0EHG: the comparison is a
  monomorphism in `Coh(U, I 𝒪_U)`.

## Implementation notes

The system is indexed by `ℕᵒᵖ` and zero-indexed: term `n` is the source's `G_{n+1}`.

Coherence of `G_n|_U` is *not* obtained from the finite-module-model criterion Stacks 0DXT,
because `M/Iⁿ⁺¹M` need not be a finite `A`-module: `M` is a submodule of sections over the
non-proper open `U`, and finiteness of its quotients is an extra hypothesis, added only in
Stacks 0EHH. The source's own argument is followed instead. Writing `M_n` for the image of `M`
in `H⁰(U, F_n)`, the sheaf `M_n^~|_U` injects into the coherent `F_n`, hence is coherent by
Stacks 01Y1; the topology hypothesis makes `M/Iⁿ⁺¹M` a quotient of `M_m` for some `m`, so
`G_n|_U` is a quotient of a coherent module, hence coherent by Stacks 01Y1 again. Only the
annihilation and quotient-transition clauses of the adic-system predicate are taken from
`restrictedTildeSystem_idealPowerMultiple_eq_bot` and `restrictedTildeSystem_transition`, which
is why those are stated separately from the coherence clause.

Injectivity is reduced to the same pro-isomorphism. For each `n` the comparison at a
sufficiently large stage `m` factors as `G_m|_U ⟶ M_m^~|_U ⟶ F_m` with the second map a
monomorphism, and the first map composed with a further reduction is the transition
`G_m|_U ⟶ G_n|_U`. Since every transition of a coherent adic system is an epimorphism, two
morphisms into the system that agree after the comparison already agree at every stage.

## References

* [The Stacks Project, Lemma 52.17.3 (0EHG)](https://stacks.math.columbia.edu/tag/0EHG)
* [The Stacks Project, Situation 52.17.1 (0EHC)](https://stacks.math.columbia.edu/tag/0EHC)
* [The Stacks Project, Lemma 30.9.3 (01Y1)](https://stacks.math.columbia.edu/tag/01Y1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-- The hypothesis of Stacks 0EHG: the limit topology on `M = limₙ H⁰(U, F_n)`, that is the
coarsest topology making every projection to a discrete `H⁰(U, F_n)` continuous, agrees with
the `I`-adic topology on `M`. -/
public abbrev LimitTopologyAgrees : Prop :=
  (⨅ n : ℕ, TopologicalSpace.induced
    (fun x : limitGlobalSections S F =>
      (limit.π (globalSectionsSystem S F) (op n)).hom x) ⊥) =
    S.I.adicModuleTopology (limitGlobalSections S F)

/-- The transition `M/Iⁿ⁺²M ⟶ M/Iⁿ⁺¹M` of the system of quotients of `M`. -/
public abbrev limitQuotientTransition (n : ℕ) :
    quotientModule S F (n + 1) ⟶ quotientModule S F n :=
  ModuleCat.ofHom (Submodule.factorPow S.I (limitGlobalSections S F) (Nat.le_succ (n + 1)))

/-- The inverse system `n ↦ M/Iⁿ⁺¹M` of `A`-modules. -/
public def limitQuotientSystem : ℕᵒᵖ ⥤ ModuleCat.{u} S.A :=
  Functor.ofOpSequence (X := fun n => quotientModule S F n) (limitQuotientTransition S F)

/-- The inverse system `n ↦ (M/Iⁿ⁺¹M)^~|_U` of modules on the open complement `U`. -/
public abbrev limitQuotientSheaves : ℕᵒᵖ ⥤ S.U.toScheme.Modules :=
  restrictedTildeSystem S (limitQuotientSystem S F)

public theorem limitQuotientSystem_map_succ (n : ℕ) :
    (limitQuotientSystem S F).map (homOfLE (Nat.le_succ n)).op =
      limitQuotientTransition S F n :=
  Functor.ofOpSequence_map_homOfLE_succ _ _

/-! ### The module-theoretic input -/

-- `pullbackTildeFunctor` is a left adjoint, hence preserves epimorphisms.
attribute [local instance] pullbackTilde_isLeftAdjoint

/-- `Iⁿ⁺¹` annihilates `M/Iⁿ⁺¹M`. -/
private theorem quotientModule_idealPower_eq_bot (n : ℕ) :
    S.I ^ (n + 1) • (⊤ : Submodule S.A (quotientModule S F n)) = ⊥ := by
  rw [← Submodule.le_annihilator_iff]
  intro a ha
  rw [Submodule.mem_annihilator]
  intro x _
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    show (Submodule.Quotient.mk (a • x) : limitGlobalSections S F ⧸
      (S.I ^ (n + 1) • (⊤ : Submodule S.A (limitGlobalSections S F)))) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha trivial)

/-- The transition `M/Iⁿ⁺²M ⟶ M/Iⁿ⁺¹M` has kernel exactly `Iⁿ⁺¹(M/Iⁿ⁺²M)`, so the system of
quotients of `M` satisfies the reduction condition on the nose. -/
private theorem ker_factorPow (n : ℕ) :
    LinearMap.ker (Submodule.factorPow S.I (limitGlobalSections S F) (Nat.le_succ (n + 1))) =
      S.I ^ (n + 1) • (⊤ : Submodule S.A (quotientModule S F (n + 1))) := by
  rw [Submodule.factorPow, Submodule.factor, Submodule.mapQ, Submodule.ker_liftQ,
    LinearMap.comp_id, Submodule.ker_mkQ, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)]

/-- A subsingleton module is `J`-power torsion, for any ideal `J`. -/
private theorem isIPowerTorsion_of_subsingleton {R : Type u} [CommRing R] {N : Type u}
    [AddCommGroup N] [Module R N] [Subsingleton N] (J : Ideal R) : IsIPowerTorsion R N J :=
  fun _ => ⟨1, Nat.one_pos, fun _ _ => Subsingleton.elim _ _⟩

/-- The kernels of the projections `M → H⁰(U, F_n)` decrease with `n`. -/
private theorem ker_limitProjection_antitone {m n : ℕ} (hmn : m ≤ n) :
    LinearMap.ker (limit.π (globalSectionsSystem S F) (op n)).hom ≤
      LinearMap.ker (limit.π (globalSectionsSystem S F) (op m)).hom := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have hw := limit.w (globalSectionsSystem S F) (homOfLE hmn).op
  have heq := (congrArg (fun f => f.hom x) hw).symm
  rw [ModuleCat.comp_apply] at heq
  change (limit.π (globalSectionsSystem S F) (op m)).hom x =
    ((globalSectionsSystem S F).map (homOfLE hmn).op).hom
      ((limit.π (globalSectionsSystem S F) (op n)).hom x) at heq
  rw [hx, map_zero] at heq
  exact heq

/-- Every transition of the system `n ↦ M/Iⁿ⁺¹M` is the canonical quotient map. -/
private theorem limitQuotientSystem_map {m n : ℕ} (hnm : n ≤ m) :
    (limitQuotientSystem S F).map (homOfLE hnm).op =
      (ModuleCat.ofHom (Submodule.factorPow S.I (limitGlobalSections S F)
        (Nat.add_le_add_right hnm 1)) :
        quotientModule S F m ⟶ quotientModule S F n) := by
  let T := limitQuotientSystem S F
  let p : ∀ k : ℕ, limitGlobalSections S F ⟶ T.obj (op k) := fun k =>
    (ModuleCat.ofHom (Submodule.mkQ (S.I ^ (k + 1) • ⊤)) :
      limitGlobalSections S F ⟶ quotientModule S F k)
  let c : (Functor.const ℕᵒᵖ).obj (limitGlobalSections S F) ⟶ T :=
    NatTrans.ofOpSequence p (by
      intro k
      show p k = p (k + 1) ≫ T.map (homOfLE (Nat.le_add_right k 1)).op
      rw [limitQuotientSystem_map_succ]
      ext x
      rfl)
  have hepi : Epi (p m) := (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  apply (cancel_epi (p m)).1
  calc
    p m ≫ T.map (homOfLE hnm).op = p n := (c.naturality (homOfLE hnm).op).symm
    _ = _ := by
      ext x
      rfl

/-! ### The image of `M` in the sections of `F_n` -/

/-- The image `M_n` of `M` in `H⁰(U, F_n)`, presented as `M` modulo the kernel of the `n`-th
projection. -/
private abbrev projectionImage (n : ℕ) : ModuleCat.{u} S.A :=
  ModuleCat.of S.A (limitGlobalSections S F ⧸
    LinearMap.ker (limit.π (globalSectionsSystem S F) (op n)).hom)

/-- The inclusion `M_n ⊆ H⁰(U, F_n)`. -/
private def projectionImageInclusion (n : ℕ) :
    projectionImage S F n ⟶ (globalSectionsSystem S F).obj (op n) :=
  ModuleCat.ofHom (X := projectionImage S F n)
    (Y := (globalSectionsSystem S F).obj (op n))
    ((LinearMap.ker ((limit.π (globalSectionsSystem S F) (op n)).hom :
        limitGlobalSections S F →ₗ[S.A] (globalSectionsSystem S F).obj (op n))).liftQ
      ((limit.π (globalSectionsSystem S F) (op n)).hom :
        limitGlobalSections S F →ₗ[S.A] (globalSectionsSystem S F).obj (op n)) le_rfl)

private theorem mono_projectionImageInclusion (n : ℕ) :
    Mono (projectionImageInclusion S F n) :=
  (ModuleCat.mono_iff_injective _).2
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ rfl))

/-- The map `M_n^~|_U ⟶ F_n` transposing the inclusion `M_n ⊆ H⁰(U, F_n)`. -/
private def projectionImageComparison (n : ℕ) :
    (pullbackTildeFunctor S).obj (projectionImage S F n) ⟶ F.obj.obj (op n) :=
  ((pullbackTildeAdjunction S).homEquiv (projectionImage S F n) (F.obj.obj (op n))).symm
    (projectionImageInclusion S F n)

private theorem mono_projectionImageComparison (n : ℕ) :
    Mono (projectionImageComparison S F n) :=
  mono_pullbackTilde_homEquiv_symm S (F.obj.obj (op n)) (F.property.isQuasicoherent n)
    (projectionImageInclusion S F n) (mono_projectionImageInclusion S F n)

/-- **Stacks 01Y1 for `M_n`.** The sheaf `M_n^~|_U` is coherent, being a submodule of the
coherent module `F_n`. -/
private theorem isCoherent_projectionImageSheaf (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u}
      ((pullbackTildeFunctor S).obj (projectionImage S F n)) := by
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  have : (F.obj.obj (op n)).IsCoherent := F.property.isCoherent n
  have : ((pullbackTildeFunctor S).obj (projectionImage S F n)).IsQuasicoherent :=
    isQuasicoherent_pullbackTilde S (projectionImage S F n)
  have := mono_projectionImageComparison S F n
  exact Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono
    (projectionImageComparison S F n)

/-- **Stacks 01Y1 for `G_n`.** Under the topology hypothesis `M/Iⁿ⁺¹M` is a quotient of some
`M_m`, so `G_n|_U` is coherent. -/
private theorem isCoherent_limitQuotientSheaf (h : LimitTopologyAgrees S F) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} ((limitQuotientSheaves S F).obj (op n)) := by
  obtain ⟨m, hm⟩ := exists_projection_ker_le_adicPower S F h n
  have hnoeth : IsLocallyNoetherian S.U.toScheme :=
    isLocallyNoetherian_of_isOpenImmersion S.U.ι
  let q : projectionImage S F m ⟶ quotientModule S F n :=
    ModuleCat.ofHom (Submodule.factor hm)
  have hq : Epi q := (ModuleCat.epi_iff_surjective q).2 (Submodule.factor_surjective hm)
  have hcoh := isCoherent_projectionImageSheaf S F m
  have hepi : Epi ((pullbackTildeFunctor S).map q) :=
    @Functor.PreservesEpimorphisms.preserves _ _ _ _ _
      (Functor.preservesEpimorphisms_of_adjunction (pullbackTildeAdjunction S)) _ _ q hq
  have hqc : ((pullbackTildeFunctor S).obj (quotientModule S F n)).IsQuasicoherent :=
    isQuasicoherent_pullbackTilde S (quotientModule S F n)
  exact @Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi
    S.U.toScheme hnoeth _ _ hcoh hqc ((pullbackTildeFunctor S).map q) hepi

/-! ### Conclusion (1): the quotients form a coherent adic system -/

/-- **Stacks Project, Tag 0EHG (1).** If the limit topology on `M = limₙ H⁰(U, F_n)` agrees with
its `I`-adic topology, then the restrictions `G_n|_U = (M/Iⁿ⁺¹M)^~|_U` form a coherent `I`-adic
system on `U`. In particular every `G_n|_U` is a coherent `𝒪_U`-module. -/
@[stacks 0EHG "coherent inverse system"]
public theorem limitQuotientSheaves_isCoherentAdicSystem (h : LimitTopologyAgrees S F) :
    Stacks.Coherent.IsCoherentAdicSystem (idealOnOpen S) (limitQuotientSheaves S F) := by
  refine ⟨isCoherent_limitQuotientSheaf S F h, ?_, ?_⟩
  · exact restrictedTildeSystem_idealPowerMultiple_eq_bot S (limitQuotientSystem S F)
      (quotientModule_idealPower_eq_bot S F)
  · refine restrictedTildeSystem_transition S (limitQuotientSystem S F) ?_
    intro n
    refine ⟨Submodule.liftQ _ (Submodule.factorPow S.I (limitGlobalSections S F)
      (Nat.le_succ (n + 1))) (le_of_eq (ker_factorPow S F n).symm), ?_, ?_, ?_⟩
    · rw [limitQuotientSystem_map_succ]
      exact Submodule.liftQ_mkQ _ _ _
    · exact @isIPowerTorsion_of_subsingleton _ _ _ _ _
        (Submodule.subsingleton_iff_eq_bot.2
          (Submodule.ker_liftQ_eq_bot' _ _ (ker_factorPow S F n).symm)) S.a
    · refine @isIPowerTorsion_of_subsingleton _ _ _ _ _
        (Submodule.Quotient.subsingleton_iff.2 (LinearMap.range_eq_top.mpr fun z => ?_)) S.a
      obtain ⟨w, hw⟩ := Submodule.factor_surjective
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) z
      exact ⟨Submodule.Quotient.mk w, hw⟩

/-- The system `(G_n|_U)` as an object of `Coh(U, I 𝒪_U)`. -/
public def coherentLimitQuotientSystem (h : LimitTopologyAgrees S F) :
    Stacks.Coherent.CoherentAdicSystems (idealOnOpen S) :=
  ⟨limitQuotientSheaves S F, limitQuotientSheaves_isCoherentAdicSystem S F h⟩

/-! ### The comparison as a morphism of inverse systems -/

/-- The canonical comparison map is the transpose of the projection `M/Iⁿ⁺¹M ⟶ H⁰(U, F_n)`
along the composite adjunction. -/
public theorem canonicalComparisonMap_eq_transpose (n : ℕ) :
    canonicalComparisonMap S F n =
      ((pullbackTildeAdjunction S).homEquiv (quotientModule S F n) (F.obj.obj (op n))).symm
        (quotientProjection S F n) := by
  rw [canonicalComparisonMap_eq, Adjunction.comp_homEquiv]
  rfl

/-- The canonical comparison maps are compatible with the transitions of the two systems. -/
public theorem canonicalComparisonMap_naturality (n : ℕ) :
    (limitQuotientSheaves S F).map (homOfLE (n.le_add_right 1)).op ≫
        canonicalComparisonMap S F n =
      canonicalComparisonMap S F (n + 1) ≫ F.obj.map (homOfLE (n.le_add_right 1)).op := by
  rw [canonicalComparisonMap_eq_transpose, canonicalComparisonMap_eq_transpose]
  have hmap : (limitQuotientSheaves S F).map (homOfLE (n.le_add_right 1)).op =
      (pullbackTildeFunctor S).map (limitQuotientTransition S F n) :=
    congrArg (pullbackTildeFunctor S).map (limitQuotientSystem_map_succ S F n)
  rw [hmap]
  apply (pullbackTildeAdjunction S).homEquiv_naturality_right_square
  apply ModuleCat.hom_ext
  ext x
  exact (congrArg (fun q => q.hom x)
    (limit.w (globalSectionsSystem S F) (homOfLE (n.le_add_right 1)).op)).symm

/-- **Stacks Project, Tag 0EHG (the comparison).** The canonical comparison
`(G_n|_U) ⟶ (F_n)`, as a morphism of `Coh(U, I 𝒪_U)`. -/
public def comparison (h : LimitTopologyAgrees S F) :
    coherentLimitQuotientSystem S F h ⟶ F :=
  ⟨NatTrans.ofOpSequence (canonicalComparisonMap S F) (canonicalComparisonMap_naturality S F)⟩

/-- Each component of the comparison is the transpose of the projection
`M/Iⁿ⁺¹M ⟶ H⁰(U, F_n)` along the adjunction. Since the transpose is a bijection on hom-sets,
this determines the comparison uniquely. -/
public theorem comparison_hom_app (h : LimitTopologyAgrees S F) (n : ℕ) :
    (comparison S F h).hom.app (op n) =
      ((pullbackTildeAdjunction S).homEquiv (quotientModule S F n)
        (F.obj.obj (op n))).symm (quotientProjection S F n) :=
  canonicalComparisonMap_eq_transpose S F n

/-- **Stacks Project, Tag 0EHG (the comparison is the canonical one).** On sections over `U`,
the comparison sends the section of `G_n|_U` induced by an element `m` of the inverse limit
`M = limₙ H⁰(U, F_n)` to the `n`-th projection of `m`.

This pins the comparison down: it is the map induced by the limit projections, not an
arbitrary morphism of inverse systems. `comparison_hom_app` records the same fact as the
identification of each component with an adjunction transpose. -/
@[stacks 0EHG "canonical comparison"]
public theorem comparison_hom_app_limitSection (h : LimitTopologyAgrees S F) (n : ℕ)
    (m : limitGlobalSections S F) :
    (((comparison S F h).hom.app (op n)).app ⊤) (limitSection S F n m) =
      (limit.π (globalSectionsSystem S F) (op n)).hom m :=
  canonicalComparisonMap_app_limitSection S F n m

/-! ### Conclusion (2): the comparison is injective -/

/-- At every sufficiently large stage the comparison factors through `M_m^~|_U` by a
monomorphism, and the same factor also computes the transition down to stage `n`. -/
private theorem exists_mono_factorisation (h : LimitTopologyAgrees S F) (n : ℕ) :
    ∃ m : ℕ, ∃ hnm : n ≤ m, ∃ E : S.U.toScheme.Modules,
      ∃ b : (limitQuotientSheaves S F).obj (op m) ⟶ E,
      ∃ c : E ⟶ F.obj.obj (op m), ∃ d : E ⟶ (limitQuotientSheaves S F).obj (op n),
        Mono c ∧ b ≫ c = canonicalComparisonMap S F m ∧
          b ≫ d = (limitQuotientSheaves S F).map (homOfLE hnm).op := by
  obtain ⟨k, hk⟩ := exists_projection_ker_le_adicPower S F h n
  let m := max k n
  have hnm : n ≤ m := le_max_right _ _
  have hm : LinearMap.ker (limit.π (globalSectionsSystem S F) (op m)).hom ≤
      S.I ^ (n + 1) • (⊤ : Submodule S.A (limitGlobalSections S F)) :=
    (ker_limitProjection_antitone S F (le_max_left k n)).trans hk
  let b₀ : quotientModule S F m ⟶ projectionImage S F m :=
    ModuleCat.ofHom (Submodule.factor (limitProjection_kills_idealPower S F m))
  let d₀ : projectionImage S F m ⟶ quotientModule S F n :=
    ModuleCat.ofHom (Submodule.factor hm)
  refine ⟨m, hnm, (pullbackTildeFunctor S).obj (projectionImage S F m),
    (pullbackTildeFunctor S).map b₀, projectionImageComparison S F m,
    (pullbackTildeFunctor S).map d₀, mono_projectionImageComparison S F m, ?_, ?_⟩
  · rw [canonicalComparisonMap_eq_transpose]
    refine (Adjunction.homEquiv_naturality_left_symm (pullbackTildeAdjunction S) b₀
      (projectionImageInclusion S F m)).symm.trans ?_
    congr 1
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x => ?_
    exact Submodule.Quotient.induction_on _ x fun _ => rfl
  · have hmod : b₀ ≫ d₀ = (limitQuotientSystem S F).map (homOfLE hnm).op := by
      rw [limitQuotientSystem_map]
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      exact Submodule.Quotient.induction_on _ x fun _ => rfl
    exact ((pullbackTildeFunctor S).map_comp _ _).symm.trans
      (congrArg (pullbackTildeFunctor S).map hmod)

/-- **Stacks Project, Tag 0EHG (2).** The canonical comparison `(G_n|_U) ⟶ (F_n)` is a
monomorphism in the abelian category `Coh(U, I 𝒪_U)`.

It is *not* claimed to be an isomorphism: the comparison need not be surjective without a
further hypothesis such as the Mittag-Leffler condition of Stacks 0EHF. -/
@[stacks 0EHG "injective comparison"]
public theorem mono_comparison (h : LimitTopologyAgrees S F) : Mono (comparison S F h) := by
  constructor
  intro K a b hab
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext j
  obtain ⟨n, rfl⟩ := Opposite.op_surjective j
  obtain ⟨m, hnm, E, q, c, d, hc, hqc, hqd⟩ := exists_mono_factorisation S F h n
  have hcomp : a.hom.app (op m) ≫ canonicalComparisonMap S F m =
      b.hom.app (op m) ≫ canonicalComparisonMap S F m :=
    congrArg (fun f : K ⟶ F => f.hom.app (op m)) hab
  have heq : a.hom.app (op m) ≫ q = b.hom.app (op m) ≫ q := by
    rw [← cancel_mono c]
    erw [Category.assoc, Category.assoc, hqc]
    exact hcomp
  refine (@cancel_epi _ _ _ _ _ (K.obj.map (homOfLE hnm).op)
    (K.property.epi_map hnm) _ _).1 ?_
  rw [a.hom.naturality, b.hom.naturality]
  change a.hom.app (op m) ≫ (limitQuotientSheaves S F).map _ =
    b.hom.app (op m) ≫ (limitQuotientSheaves S F).map _
  rw [← hqd]
  erw [← Category.assoc, heq, Category.assoc]

end Stacks.Algebraization

end
