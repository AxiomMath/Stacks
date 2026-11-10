module

public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Reduction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.GeneratorShifts
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.LimitGlobalSectionsTopology
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplittingCharts
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientSystemNearVanishingTilde
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.RingTheory.AdicCompletion.ObstructionGeneration
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.MittagLefflerEventualLifting

/-!
# The Mittag-Leffler property of `H⁰(U, F_n)` in cohomological dimension one

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, `X = Spec(A)` and the
open complement `U = X ∖ V(𝔞)`, and let `(F_n)` be an object of `Coh(U, I𝒪_U)`. This file proves
the obstruction-theoretic core of [Stacks, Tag 0EJI]: if `cd(A, I) = 1` and the images of the
transition maps of `(H¹(U, F_n))` are eventually finite `A`-modules, then the inverse system
`(H⁰(U, F_n))` satisfies the Mittag-Leffler condition — condition (a) of [Stacks, Tag 0EHH].

## The argument

Write `F = lim F_n` and `F_n = F / I^{n+1} F` (zero-indexed, by [Stacks, Tag 0EI8]). The boundary
maps of the short exact sequences `0 → I^{n+1} F → F → F_n → 0` are maps
`δ_n : H⁰(U, F_n) → H¹(U, I^{n+1} F)`; an element whose boundary lies in `I^k H¹(U, I^{n+1} F)`
lifts to `H⁰(U, F_{k+n})`, because its image in `H¹(U, I^{n+1} F_{k+n})` is the boundary of the
finite sequence `0 → I^{n+1} F_{k+n} → F_{k+n} → F_n → 0` and is killed by `I^k`. Choosing
generators `f_1, …, f_r` of `I` and the graded splitting `Φ_F` of [Stacks, Tag 0EH6], the inclusion
`I^{(n+1)d} F → I^{n+1} F` is a sum of multiplications by monomials of degree `n + 1` composed with
maps to `F`, so the boundary of an element coming from `H⁰(U, F_{(n+1)d - 1})` lies in the sum of
the images of the maps `μ_a : H¹(U, F) → H¹(U, I^{n+1} F)` induced by multiplication by
`a ∈ I^{n+1}`. The same splitting shows that the kernel of `H¹(U, F) → H¹(U, F_{d-1})` lies in
`I · H¹(U, F)`, so `H¹(U, F)/I` is a finite `A`-module once the images in `H¹(U, F_{d-1})` are.

These are the inputs of `Stacks.AdicObstruction.exists_eventual_sum_shift_of_obstructionSpan`,
which supplies the Noetherian argument of the source over the completion of `A`, and of the
Mittag-Leffler criterion
`Stacks.Cohomology.EventualLifting.isMittagLefflerCategorical_of_eventualLifting`; the
obstruction modules are the completions `H¹(U, I^{n+1} F)^∧`, through which an element with
vanishing obstruction lifts to every level.

## Main definitions

* `Stacks.Algebraization.limKer` — the kernel `I^{n+1} F` of `F = lim F_n ⟶ F_n`.
* `Stacks.Algebraization.limBoundary` — the boundary `H⁰(U, F_n) → H¹(U, I^{n+1} F)`.
* `Stacks.Algebraization.limMu` — the maps `μ_a : H¹(U, F) → H¹(U, I^{n+1} F)`, `a ∈ I^{n+1}`.
* `Stacks.Algebraization.limRho` — multiplication by a generator
  `H¹(U, I^{n+1} F) → H¹(U, I^{n+2} F)`.

## Main results

* `Stacks.Algebraization.mem_range_tr_of_limBoundary_mem` — an element whose boundary lies in
  `I^k H¹(U, I^{n+1} F)` lifts to `H⁰(U, F_{k+n})`.
* `Stacks.Algebraization.limBoundary_tr_mem_iSup` and
  `Stacks.Algebraization.ker_cohomology_limπ_le` — the two consequences of the graded splitting
  of [Stacks, Tag 0EH6].
* `Stacks.Algebraization.isMittagLefflerCategorical_globalSectionsSystem_of_cd_one` — the
  Mittag-Leffler property of `(H⁰(U, F_n))`.

## Implementation notes

Cohomology is the right derived functor of global sections on `U`, in `Γ(U, 𝒪_U)`-modules
(`Stacks.Algebraization.topSections`) and, with scalars restricted to `A`,
`Stacks.Algebraization.openCohomologyFunctor`; its boundary maps are
`Stacks.Algebraization.boundary`, and its linearity over `Γ(U, 𝒪_U)` is
`AlgebraicGeometry.rightDerived_moduleGlobalSections_linear`. The subsheaves `I^{n+1} F` and
`I^{n+1} F_{k+n}` are taken as kernels of the projections, so that every map between the short
exact sequences is a `kernel.lift`; they meet the subsheaves `idealPowerMultiple` of the graded
splitting only through `Stacks.Algebraization.exists_kernel_lift_ιModules`. No limit of
cohomology modules is formed: the limits of the source are replaced by the `I`-adic completions
of `H¹(U, I^{n+1} F)`, into which an element of vanishing obstruction maps to zero exactly when
its finite-level obstructions vanish (`mem_range_tr_of_limBoundary_mem`).

## References

* [Stacks Project, Tag 0EJI](https://stacks.math.columbia.edu/tag/0EJI)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-! ### Generalities -/

/-- The ideal sheaf `I 𝒪_U` is of finite type. -/
theorem isFiniteType_idealOnOpen : Scheme.IdealSheafData.IsFiniteType (idealOnOpen S) := by
  have h := Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_comap S.A S.I S.U.ι
  intro V
  have hV : (idealOnOpen S).ideal V =
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι).ideal V := by
    rw [h]
  rw [hV, Stacks.Coherent.baseIdealSheaf_ideal_eq_map]
  exact Ideal.FG.map (IsNoetherian.noetherian S.I) _

/-- Multiplication by a global function, in the two spellings of the library. -/
theorem sectionSmul_eq_globalSmul (b : Γ(S.U.toScheme, ⊤)) (M : S.U.toScheme.Modules) :
    sectionSmul b M = globalSmul b M := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  rw [sectionSmul_app, globalSmul_app]
  rfl

/-- **`H^p(U, -)` carries multiplication by a global function to the scalar action.** -/
theorem rightDerived_map_sectionSmul_apply (p : ℕ) (b : Γ(S.U.toScheme, ⊤))
    (M : S.U.toScheme.Modules) (x : ((moduleGlobalSections S.U.toScheme).rightDerived p).obj M) :
    (((moduleGlobalSections S.U.toScheme).rightDerived p).map (sectionSmul b M)).hom x =
      b • x := by
  rw [sectionSmul_eq_globalSmul, globalSmul_eq_smul_id, Functor.map_smul,
    CategoryTheory.Functor.map_id]
  rfl

/-- `H^p(U, -)` over `A` carries multiplication by `a ∈ A` to multiplication by `a`. -/
theorem openCohomologyFunctor_map_sectionSmul (p : ℕ) (a : S.A) (M : S.U.toScheme.Modules)
    (x : (openCohomologyFunctor S p).obj M) :
    ((openCohomologyFunctor S p).map (sectionSmul (scalarMap S a) M)).hom x = a • x :=
  rightDerived_map_sectionSmul_apply S p (scalarMap S a) M x

/-- A module on which multiplication by every element of `I ^ k` vanishes has cohomology killed
by `I ^ k`. -/
theorem smul_openCohomology_eq_zero (p k : ℕ) (M : S.U.toScheme.Modules)
    (hM : ∀ a ∈ S.I ^ k, sectionSmul (scalarMap S a) M = 0) :
    ∀ a ∈ S.I ^ k, ∀ x : (openCohomologyFunctor S p).obj M, a • x = 0 := by
  intro a ha x
  rw [← openCohomologyFunctor_map_sectionSmul, hM a ha, Functor.map_zero]
  rfl

/-- Multiplication by an element of `I ^ (n + 1)` vanishes on `F_n`. -/
theorem sectionSmul_term_eq_zero (n : ℕ) {a : S.A} (ha : a ∈ S.I ^ (n + 1)) :
    sectionSmul (scalarMap S a) (F.obj.obj (op n)) = 0 :=
  sectionSmul_eq_zero _ (F.property.idealPowerMultiple_eq_bot n)
    (restrictMemIdealPow_scalarMap S (n + 1) ha)

/-- Multiplication by an element of `I ^ k` vanishes on a subobject of a module on which it
vanishes. -/
theorem sectionSmul_eq_zero_of_mono {M N : S.U.toScheme.Modules} (ι : M ⟶ N) [Mono ι]
    {b : Γ(S.U.toScheme, ⊤)} (hb : sectionSmul b N = 0) : sectionSmul b M = 0 := by
  rw [← cancel_mono ι, ← comp_sectionSmul, hb, comp_zero, zero_comp]

/-- The transition map of the system from level `m` down to level `n`. -/
abbrev tr {n m : ℕ} (h : n ≤ m) : F.obj.obj (op m) ⟶ F.obj.obj (op n) :=
  F.obj.map (homOfLE h).op

/-- The transition maps compose: `F_m → F_n → F_k` is the transition `F_m → F_k`. -/
theorem tr_tr {k n m : ℕ} (h₁ : k ≤ n) (h₂ : n ≤ m) :
    tr S F h₂ ≫ tr S F h₁ = tr S F (h₁.trans h₂) := by
  rw [← F.obj.map_comp]
  rfl

/-- The transition maps of the system are epimorphisms. -/
instance epi_tr {n m : ℕ} (h : n ≤ m) : Epi (tr S F h) := F.property.epi_map h

/-! ### The kernels `I^{n+1} F_{k+n}` and their boundary maps -/

/-- The kernel `I^{n+1} F_{k+n}` of the transition `F_{k+n} → F_n`. -/
abbrev kerSub (n k : ℕ) : S.U.toScheme.Modules := kernel (tr S F (Nat.le_add_left n k))

/-- The sequence `0 → I^{n+1} F_{k+n} → F_{k+n} → F_n → 0`. -/
abbrev kerShortComplex (n k : ℕ) : ShortComplex S.U.toScheme.Modules :=
  ShortComplex.mk (kernel.ι (tr S F (Nat.le_add_left n k))) (tr S F (Nat.le_add_left n k))
    (kernel.condition _)

/-- The sequence `0 → I^{n+1} F_{k+n} → F_{k+n} → F_n → 0` is short exact. -/
theorem kerShortComplex_shortExact (n k : ℕ) : (kerShortComplex S F n k).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) inferInstance (epi_tr S F _)

/-- **The boundary map** `H⁰(U, F_n) ⟶ H¹(U, I^{n+1} F_{k+n})`, in `Γ(U, 𝒪_U)`-modules. -/
def kerBoundaryHom (n k : ℕ) :
    (topSections S).obj (F.obj.obj (op n)) ⟶
      ((topSections S).rightDerived 1).obj (kerSub S F n k) :=
  (topSections S).rightDerivedZeroIsoSelf.inv.app _ ≫
    ((topSections S).rightDerived 0).map (Iso.refl (F.obj.obj (op n))).inv ≫
      boundary S (kerShortComplex_shortExact S F n k)

/-- The kernel of the boundary map is the image of `H⁰(U, F_{k+n})`. -/
theorem kerBoundaryHom_eq_zero_iff (n k : ℕ) (s : (topSections S).obj (F.obj.obj (op n))) :
    (kerBoundaryHom S F n k).hom s = 0 ↔
      s ∈ LinearMap.range ((topSections S).map (tr S F (Nat.le_add_left n k))).hom :=
  abstract_boundary_eq_zero_iff _ _ (topSections S).rightDerivedZeroIsoSelf _ _ _
    (Category.comp_id _) _ (range_eq_ker_boundary S (kerShortComplex_shortExact S F n k)) s

/-! ### The limit `F = lim F_n` -/

/-- The projection `F ⟶ F_n` from the limit. -/
abbrev limπ (n : ℕ) : limit F.obj ⟶ F.obj.obj (op n) := limit.π F.obj (op n)

/-- The projections from the limit are compatible with the transition maps. -/
theorem limπ_tr {n m : ℕ} (h : n ≤ m) : limπ S F m ≫ tr S F h = limπ S F n :=
  limit.w F.obj (homOfLE h).op

/-- The projection `F ⟶ F_n` identifies `F_n` with the quotient `F / I^{n+1} F`. -/
theorem exists_limitQuotientIso (n : ℕ) :
    ∃ e : idealPowerQuotient (idealOnOpen S) (n + 1) (limit F.obj) ≅ F.obj.obj (op n),
      cokernel.π ((idealPowerMultiple (idealOnOpen S) (n + 1) (limit F.obj)).ι) ≫ e.hom =
        limπ S F n :=
  (adicInverseSystemOnOpen S F).exists_idealPowerQuotientIso (isFiniteType_idealOnOpen S) n

/-- The projections `F ⟶ F_n` from the limit are epimorphisms. -/
instance epi_limπ (n : ℕ) : Epi (limπ S F n) :=
  (adicInverseSystemOnOpen S F).epi_limitProjection n

/-- The kernel `I^{n+1} F` of the projection `F ⟶ F_n`. -/
abbrev limKer (n : ℕ) : S.U.toScheme.Modules := kernel (limπ S F n)

/-- The sequence `0 → I^{n+1} F → F → F_n → 0`. -/
abbrev limShortComplex (n : ℕ) : ShortComplex S.U.toScheme.Modules :=
  ShortComplex.mk (kernel.ι (limπ S F n)) (limπ S F n) (kernel.condition _)

/-- The sequence `0 → I^{n+1} F → F → F_n → 0` is short exact. -/
theorem limShortComplex_shortExact (n : ℕ) : (limShortComplex S F n).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel _) inferInstance (epi_limπ S F n)

/-- **The boundary map** `H⁰(U, F_n) ⟶ H¹(U, I^{n+1} F)`, in `Γ(U, 𝒪_U)`-modules. -/
def limBoundaryHom (n : ℕ) :
    (topSections S).obj (F.obj.obj (op n)) ⟶ ((topSections S).rightDerived 1).obj (limKer S F n) :=
  (topSections S).rightDerivedZeroIsoSelf.inv.app _ ≫
    ((topSections S).rightDerived 0).map (Iso.refl (F.obj.obj (op n))).inv ≫
      boundary S (limShortComplex_shortExact S F n)

/-- The inclusion `I^{m+1} F ⟶ I^{n+1} F` for `n ≤ m`. -/
def limKerIncl {n m : ℕ} (h : n ≤ m) : limKer S F m ⟶ limKer S F n :=
  kernel.lift _ (kernel.ι _) (by rw [← limπ_tr S F h, kernel.condition_assoc, zero_comp])

/-- The inclusion `I^{m+1} F ⟶ I^{n+1} F` commutes with the inclusions into `F`. -/
theorem limKerIncl_ι {n m : ℕ} (h : n ≤ m) :
    limKerIncl S F h ≫ kernel.ι (limπ S F n) = kernel.ι (limπ S F m) :=
  kernel.lift_ι _ _ _

/-- The morphism of sequences `(0 → I^{m+1} F → F → F_m → 0) ⟶ (0 → I^{n+1} F → F → F_n → 0)`. -/
def limShortComplexIncl {n m : ℕ} (h : n ≤ m) : limShortComplex S F m ⟶ limShortComplex S F n where
  τ₁ := limKerIncl S F h
  τ₂ := 𝟙 _
  τ₃ := (Iso.refl _).hom ≫ tr S F h ≫ (Iso.refl _).inv
  comm₁₂ := by rw [Category.comp_id]; exact limKerIncl_ι S F h
  comm₂₃ := by
    change 𝟙 _ ≫ limπ S F n = limπ S F m ≫ (𝟙 _ ≫ tr S F h ≫ 𝟙 _)
    rw [Category.id_comp, Category.id_comp, Category.comp_id, limπ_tr]

/-- The boundary maps `H⁰(U, F_n) ⟶ H¹(U, -)` are natural in a morphism of short exact sequences
whose third component is `u`. -/
private theorem topSections_map_boundary_naturality
    {T T' : ShortComplex S.U.toScheme.Modules} (hT : T.ShortExact) (hT' : T'.ShortExact)
    (φ : T ⟶ T') (u : T.X₃ ⟶ T'.X₃) (hu : φ.τ₃ = (Iso.refl _).hom ≫ u ≫ (Iso.refl _).inv) :
    (topSections S).map u ≫ (topSections S).rightDerivedZeroIsoSelf.inv.app T'.X₃ ≫
        ((topSections S).rightDerived 0).map (Iso.refl T'.X₃).inv ≫ boundary S hT' =
      ((topSections S).rightDerivedZeroIsoSelf.inv.app T.X₃ ≫
        ((topSections S).rightDerived 0).map (Iso.refl T.X₃).inv ≫ boundary S hT) ≫
          ((topSections S).rightDerived 1).map φ.τ₁ :=
  abstract_boundary_naturality _ _ _ (topSections S).rightDerivedZeroIsoSelf
    (Iso.refl _) (Iso.refl _) u φ.τ₁ _ _ (hu ▸ boundary_naturality S hT hT' φ)

/-- The boundary maps of the limit are compatible with the transitions. -/
theorem limBoundaryHom_incl {n m : ℕ} (h : n ≤ m) :
    (topSections S).map (tr S F h) ≫ limBoundaryHom S F n =
      limBoundaryHom S F m ≫ ((topSections S).rightDerived 1).map (limKerIncl S F h) :=
  topSections_map_boundary_naturality S (limShortComplex_shortExact S F m)
    (limShortComplex_shortExact S F n) (limShortComplexIncl S F h) _ rfl

/-- The restriction `I^{n+1} F ⟶ I^{n+1} F_{k+n}`. -/
def limKerRestrict (n k : ℕ) : limKer S F n ⟶ kerSub S F n k :=
  kernel.map _ _ (limπ S F (k + n)) (𝟙 _) (by rw [Category.comp_id, limπ_tr])

/-- The morphism of sequences given by the projection `F ⟶ F_{k+n}`. -/
def limShortComplexRestrict (n k : ℕ) : limShortComplex S F n ⟶ kerShortComplex S F n k where
  τ₁ := limKerRestrict S F n k
  τ₂ := limπ S F (k + n)
  τ₃ := (Iso.refl _).hom ≫ 𝟙 _ ≫ (Iso.refl _).inv
  comm₁₂ := kernel.lift_ι _ _ _
  comm₂₃ := by
    change limπ S F (k + n) ≫ tr S F _ = limπ S F n ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _)
    rw [Category.id_comp, Category.id_comp, Category.comp_id, limπ_tr]

/-- The finite-level boundaries are the images of the boundary of the limit. -/
theorem kerBoundaryHom_eq_limBoundaryHom (n k : ℕ) :
    kerBoundaryHom S F n k = limBoundaryHom S F n ≫
      ((topSections S).rightDerived 1).map (limKerRestrict S F n k) := by
  have h := topSections_map_boundary_naturality S (limShortComplex_shortExact S F n)
    (kerShortComplex_shortExact S F n k) (limShortComplexRestrict S F n k) (𝟙 _) rfl
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-! ### Multiplication maps into the kernels -/

/-- Multiplication by `a ∈ I ^ (n + 1)` on `F`, as a map `F ⟶ I^{n+1} F`. -/
def limKerMul (n : ℕ) {a : S.A} (ha : a ∈ S.I ^ (n + 1)) : limit F.obj ⟶ limKer S F n :=
  kernel.lift _ (sectionSmul (scalarMap S a) (limit F.obj)) (by
    rw [← comp_sectionSmul, sectionSmul_term_eq_zero S F n ha, comp_zero])

/-- Composing `limKerMul` with the inclusion `I^{n+1} F ⟶ F` is multiplication by `a` on `F`. -/
theorem limKerMul_ι (n : ℕ) {a : S.A} (ha : a ∈ S.I ^ (n + 1)) :
    limKerMul S F n ha ≫ kernel.ι (limπ S F n) = sectionSmul (scalarMap S a) (limit F.obj) :=
  kernel.lift_ι _ _ _

variable {r : ℕ} (f : Fin r → S.A) (hfI : ∀ j, f j ∈ S.I)

/-! ### The graded splitting of [Stacks, Tag 0EH6] -/

/-- The open complement `U` is a Noetherian scheme. -/
theorem isNoetherian_complement : AlgebraicGeometry.IsNoetherian S.U.toScheme := by
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  have : CompactSpace S.U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (S.U : Set S.X))
  exact (isNoetherian_iff S.U.toScheme).2 ⟨inferInstance, inferInstance⟩

include hfI in
/-- A monomial of degree `k` in elements of `I` lies in `I ^ k`. -/
theorem prod_pow_mem_pow {k : ℕ} (σ : Fin r →₀ ℕ) (hσ : Finsupp.degree σ = k) :
    (∏ j, f j ^ σ j) ∈ S.I ^ k := by
  have hprod : (∏ j, f j ^ σ j) ∈ ∏ j, S.I ^ σ j :=
    Ideal.prod_mem_prod fun j _ => Ideal.pow_mem_pow (hfI j) _
  rwa [Finset.prod_pow_eq_pow_sum, ← Stacks.ReesAlgebra.degree_eq_sum_univ, hσ] at hprod

/-- **The graded splitting, as an identity of morphisms.** For a graded splitting `Ψ` of
[Stacks, Tag 0EH6] on `F = lim F_n`, the inclusion `I^{kd} F ⟶ F` is
`∑_{|σ| = k} Ψ_σ ≫ (f^σ · -)`. -/
theorem ιModules_eq_sum_gradedSplitting {d : ℕ}
    {Ψ : Stacks.Coherent.GradedSplittingComponents S.A S.I S.U.ι (limit F.obj) r d}
    (hΨ : ∀ n : ℕ, Stacks.Coherent.gradedSplittingEvalHom Ψ f n =
      AlgebraicGeometry.SheafOfModules.Submodule.ιModules (idealPowerMultiple
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι) (n * d) (limit F.obj)))
    (k : ℕ) :
    AlgebraicGeometry.SheafOfModules.Submodule.ιModules (idealPowerMultiple
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι) (k * d) (limit F.obj)) =
      ∑ σ ∈ (Stacks.ReesAlgebra.degreeMonomials r k).attach,
        Stacks.Coherent.gradedSplittingComponentAt Ψ
            (Stacks.ReesAlgebra.mem_degreeMonomials.1 σ.2) ≫
          sectionSmul (scalarMap S (∏ j, f j ^ (σ.1 : Fin r →₀ ℕ) j)) (limit F.obj) := by
  rw [← hΨ k]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext t
  rw [Stacks.Coherent.gradedSplittingEvalHom_app, Stacks.Coherent.gradedSplittingEval_eq]
  change _ = (∑ σ ∈ (Stacks.ReesAlgebra.degreeMonomials r k).attach,
    Stacks.Coherent.gradedSplittingComponentAt Ψ (Stacks.ReesAlgebra.mem_degreeMonomials.1 σ.2) ≫
      sectionSmul (scalarMap S (∏ j, f j ^ (σ.1 : Fin r →₀ ℕ) j)) (limit F.obj)).val.app (op V) t
  have happ : ∀ {κ : Type} {M : S.U.toScheme.Modules} (s : Finset κ)
      (q : κ → (M ⟶ limit F.obj)) (t' : Γ(M, V)), Scheme.Modules.Hom.app (∑ i ∈ s, q i) V t' =
        ∑ i ∈ s, Scheme.Modules.Hom.app (q i) V t' := by
    intro κ M s q t'
    classical
    induction s using Finset.induction with
    | empty => rfl
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, Scheme.Modules.Hom.add_app]
      rfl
  change _ = Scheme.Modules.Hom.app (∑ σ ∈ (Stacks.ReesAlgebra.degreeMonomials r k).attach,
    Stacks.Coherent.gradedSplittingComponentAt Ψ (Stacks.ReesAlgebra.mem_degreeMonomials.1 σ.2) ≫
      sectionSmul (scalarMap S (∏ j, f j ^ (σ.1 : Fin r →₀ ℕ) j)) (limit F.obj)) V t
  rw [happ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, sectionSmul_app]
  rfl

/-- In an abelian category, a map killed by the composite of a cokernel projection with an
isomorphism lifts through the monomorphism whose cokernel it is. -/
theorem exists_lift_of_cokernel_iso {C : Type*} [Category C] [Abelian C] {P M Q K : C}
    (ι : P ⟶ M) [Mono ι] (π : M ⟶ Q) (e : cokernel ι ≅ Q) (he : cokernel.π ι ≫ e.hom = π)
    (k : K ⟶ M) (hk : k ≫ π = 0) : ∃ ψ : K ⟶ P, ψ ≫ ι = k := by
  have hk' : k ≫ cokernel.π ι = 0 := by
    rw [← cancel_mono e.hom, Category.assoc, he, hk, zero_comp]
  exact ⟨(ShortComplex.exact_cokernel ι).lift k hk', (ShortComplex.exact_cokernel ι).lift_f k hk'⟩

/-- The kernel of `F ⟶ F_N` is the subsheaf `I^{N+1} F`, which `N + 1 = k d` lets us read as the
source of a component of the graded splitting. -/
theorem exists_kernel_lift_ιModules {N k d : ℕ} (hN : N + 1 = k * d) :
    ∃ ψ : limKer S F N ⟶ AlgebraicGeometry.SheafOfModules.Submodule.asModules (idealPowerMultiple
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι) (k * d) (limit F.obj)),
      ψ ≫ AlgebraicGeometry.SheafOfModules.Submodule.ιModules (idealPowerMultiple
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι) (k * d) (limit F.obj)) =
        kernel.ι (limπ S F N) := by
  have hP : idealPowerMultiple (idealOnOpen S) (N + 1) (limit F.obj) =
      idealPowerMultiple (Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι)
        (k * d) (limit F.obj) := by
    rw [hN]
    exact congrArg (fun J => idealPowerMultiple J (k * d) (limit F.obj))
      (idealOnOpen_eq_baseIdealSheaf S)
  obtain ⟨e, he⟩ := exists_limitQuotientIso S F N
  revert e
  generalize idealPowerMultiple (Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι)
    (k * d) (limit F.obj) = P at hP
  subst hP
  intro e he
  exact exists_lift_of_cokernel_iso (C := S.U.toScheme.Modules)
    (AlgebraicGeometry.SheafOfModules.Submodule.ιModules _) (limπ S F N) e he _
    (kernel.condition _)

/-- The long exact cohomology sequence of `𝒪_U`-modules, in `Γ(U, 𝒪_U)`-modules. -/
abbrev cohDelta := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
  (moduleGlobalSections S.U.toScheme)

/-! ### Lifting along an obstruction divisible by a power of `I` -/

/-- Multiplication by an element of `I ^ k` vanishes on `I^{n+1} F_{k+n}`: on `F_{k+n}` it factors
through the transition to `F_n`. -/
theorem sectionSmul_kerSub_eq_zero (n k : ℕ) {a : S.A} (ha : a ∈ S.I ^ k) :
    sectionSmul (scalarMap S a) (kerSub S F n k) = 0 := by
  obtain ⟨u, hu, -⟩ := exists_transitionSmulUp F (Nat.le_add_left n k) (by omega)
    (restrictMemIdealPow_scalarMap S k ha)
  rw [← cancel_mono (kernel.ι (tr S F (Nat.le_add_left n k))), zero_comp, ← comp_sectionSmul]
  change kernel.ι (tr S F (Nat.le_add_left n k)) ≫ sectionSmul _ _ = 0
  rw [← hu, ← Category.assoc, kernel.condition, zero_comp]

/-- **The boundary map** `H⁰(U, F_n) ⟶ H¹(U, I^{n+1} F)`, over `A`. -/
def limBoundary (n : ℕ) :
    (openSectionsFunctor S).obj (F.obj.obj (op n)) →ₗ[S.A]
      (openCohomologyFunctor S 1).obj (limKer S F n) :=
  ((ModuleCat.restrictScalars (scalarMap S)).map (limBoundaryHom S F n)).hom

/-- **An element whose boundary is divisible by `I ^ k` lifts to `F_{k+n}`.** -/
theorem mem_range_tr_of_limBoundary_mem (n k : ℕ)
    (s : (openSectionsFunctor S).obj (F.obj.obj (op n)))
    (hs : limBoundary S F n s ∈ (S.I ^ k • ⊤ : Submodule S.A _)) :
    s ∈ LinearMap.range ((openSectionsFunctor S).map (tr S F (Nat.le_add_left n k))).hom := by
  have hzero : ∀ y ∈ (S.I ^ k • ⊤ : Submodule S.A ((openCohomologyFunctor S 1).obj (limKer S F n))),
      ((openCohomologyFunctor S 1).map (limKerRestrict S F n k)).hom y = 0 := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
    · rw [map_smul, smul_openCohomology_eq_zero S 1 k (kerSub S F n k)
        (fun a ha => sectionSmul_kerSub_eq_zero S F n k ha) a ha]
    · rw [map_add, h₁, h₂, add_zero]
  have h := hzero _ hs
  have hk : (kerBoundaryHom S F n k).hom s = 0 := by
    rw [kerBoundaryHom_eq_limBoundaryHom]
    exact h
  exact (kerBoundaryHom_eq_zero_iff S F n k s).mp hk

/-! ### The up maps on the kernels of the limit -/

/-- The projection `F ⟶ F_n` carries multiplication by `f_l` on `F` to the up map
`F_n ⟶ F_{n+1}` of `f_l`. -/
theorem limπ_upMapOf (l : Fin r) (n : ℕ) :
    limπ S F n ≫ upMapOf S F f hfI l n =
      sectionSmul (scalarMap S (f l)) (limit F.obj) ≫ limπ S F (n + 1) := by
  rw [← limπ_tr S F (Nat.le_succ n), Category.assoc]
  change limπ S F (n + 1) ≫ (succTrans S F n ≫ upMapOf S F f hfI l n) = _
  rw [trans_upMapOf, comp_sectionSmul]

include hfI in
/-- Multiplication by `f_l` carries `I^{n+1} F` into the kernel `I^{n+2} F` of `F ⟶ F_{n+1}`. -/
theorem limKerUp_cond (l : Fin r) (n : ℕ) :
    (kernel.ι (limπ S F n) ≫ sectionSmul (scalarMap S (f l)) (limit F.obj)) ≫
      limπ S F (n + 1) = 0 := by
  rw [Category.assoc, ← limπ_upMapOf S F f hfI, ← Category.assoc, kernel.condition, zero_comp]

/-- The up map `I^{n+1} F ⟶ I^{n+2} F` of a generator: multiplication by `f_l`. -/
def limKerUp (l : Fin r) (n : ℕ) : limKer S F n ⟶ limKer S F (n + 1) :=
  kernel.lift _ (kernel.ι _ ≫ sectionSmul (scalarMap S (f l)) (limit F.obj))
    (limKerUp_cond S F f hfI l n)

/-- The up map `I^{n+1} F ⟶ I^{n+2} F` commutes with multiplication by `f_l` on `F`. -/
theorem limKerUp_ι (l : Fin r) (n : ℕ) :
    limKerUp S F f hfI l n ≫ kernel.ι _ =
      kernel.ι _ ≫ sectionSmul (scalarMap S (f l)) (limit F.obj) :=
  kernel.lift_ι _ _ _

/-- The up maps of two generators commute. -/
theorem limKerUp_comm (l l' : Fin r) (n : ℕ) :
    limKerUp S F f hfI l' n ≫ limKerUp S F f hfI l (n + 1) =
      limKerUp S F f hfI l n ≫ limKerUp S F f hfI l' (n + 1) := by
  rw [← cancel_mono (kernel.ι _), Category.assoc, Category.assoc, limKerUp_ι, limKerUp_ι,
    ← Category.assoc, ← Category.assoc, limKerUp_ι, limKerUp_ι, Category.assoc, Category.assoc,
    sectionSmul_comp, sectionSmul_comp, mul_comm]

/-- Multiplication by `a` followed by the up map of `f_l` is multiplication by `f_l * a`. -/
theorem limKerMul_up (l : Fin r) (n : ℕ) {a : S.A} (ha : a ∈ S.I ^ (n + 1)) :
    limKerMul S F n ha ≫ limKerUp S F f hfI l n =
      limKerMul S F (n + 1) (show f l * a ∈ S.I ^ (n + 1 + 1) by
        rw [pow_succ']; exact Ideal.mul_mem_mul (hfI l) ha) := by
  rw [← cancel_mono (kernel.ι _), Category.assoc, limKerUp_ι, ← Category.assoc, limKerMul_ι,
    limKerMul_ι, sectionSmul_comp, map_mul]

/-- The morphism of sequences given by the up maps. -/
def limShortComplexUp (l : Fin r) (n : ℕ) :
    limShortComplex S F n ⟶ limShortComplex S F (n + 1) where
  τ₁ := limKerUp S F f hfI l n
  τ₂ := sectionSmul (scalarMap S (f l)) (limit F.obj)
  τ₃ := (Iso.refl _).hom ≫ upMapOf S F f hfI l n ≫ (Iso.refl _).inv
  comm₁₂ := limKerUp_ι S F f hfI l n
  comm₂₃ := by
    change sectionSmul _ _ ≫ limπ S F (n + 1) = limπ S F n ≫ (𝟙 _ ≫ upMapOf S F f hfI l n ≫ 𝟙 _)
    rw [Category.id_comp, Category.comp_id, limπ_upMapOf]

/-- The boundary maps commute with the up maps. -/
theorem limBoundaryHom_up (l : Fin r) (n : ℕ) :
    (topSections S).map (upMapOf S F f hfI l n) ≫ limBoundaryHom S F (n + 1) =
      limBoundaryHom S F n ≫ ((topSections S).rightDerived 1).map (limKerUp S F f hfI l n) :=
  topSections_map_boundary_naturality S (limShortComplex_shortExact S F n)
    (limShortComplex_shortExact S F (n + 1)) (limShortComplexUp S F f hfI l n) _ rfl

/-! ### The multiplication maps on cohomology -/

/-- Multiplication into `I^{n+1} F` is additive in the multiplier. -/
theorem limKerMul_add (n : ℕ) {a b : S.A} (ha : a ∈ S.I ^ (n + 1)) (hb : b ∈ S.I ^ (n + 1)) :
    limKerMul S F n (add_mem ha hb) = limKerMul S F n ha + limKerMul S F n hb := by
  rw [← cancel_mono (kernel.ι _), Preadditive.add_comp, limKerMul_ι, limKerMul_ι, limKerMul_ι,
    map_add]
  exact map_add (sectionSmulHom (limit F.obj)) _ _

/-- Multiplication by `c * a` into `I^{n+1} F` is multiplication by `c` on `F` followed by
multiplication by `a`. -/
theorem limKerMul_mul (n : ℕ) (c : S.A) {a : S.A} (ha : a ∈ S.I ^ (n + 1)) :
    limKerMul S F n (Ideal.mul_mem_left _ c ha) =
      sectionSmul (scalarMap S c) (limit F.obj) ≫ limKerMul S F n ha := by
  rw [← cancel_mono (kernel.ι _), limKerMul_ι, Category.assoc, limKerMul_ι, sectionSmul_comp,
    map_mul, mul_comm]

/-- **The maps `μ_a : H¹(U, F) ⟶ H¹(U, I^{n+1} F)`**, multiplication by `a ∈ I^{n+1}`, linear in
`a`. -/
def limMu (n : ℕ) :
    ↥(S.I ^ (n + 1)) →ₗ[S.A] (openCohomologyFunctor S 1).obj (limit F.obj) →ₗ[S.A]
      (openCohomologyFunctor S 1).obj (limKer S F n) where
  toFun a := ((openCohomologyFunctor S 1).map (limKerMul S F n a.2)).hom
  map_add' a b := by
    change ((openCohomologyFunctor S 1).map (limKerMul S F n (add_mem a.2 b.2))).hom = _
    rw [limKerMul_add, Functor.map_add]
    rfl
  map_smul' c a := by
    ext x
    change ((openCohomologyFunctor S 1).map
      (limKerMul S F n (Ideal.mul_mem_left _ c a.2))).hom x = c • _
    rw [limKerMul_mul, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
      openCohomologyFunctor_map_sectionSmul, map_smul]

/-- The up map of a generator on cohomology. -/
def limRho (l : Fin r) (n : ℕ) :
    (openCohomologyFunctor S 1).obj (limKer S F n) →ₗ[S.A]
      (openCohomologyFunctor S 1).obj (limKer S F (n + 1)) :=
  ((openCohomologyFunctor S 1).map (limKerUp S F f hfI l n)).hom

/-- The up map of `f_l` on cohomology carries `μ_a` to `μ_{f_l a}`. -/
theorem limRho_comp_limMu (l : Fin r) (n : ℕ) (a : ↥(S.I ^ (n + 1))) :
    (limRho S F f hfI l n).comp (limMu S F n a) = limMu S F (n + 1) ⟨f l * a, by
      rw [pow_succ']; exact Ideal.mul_mem_mul (hfI l) a.2⟩ := by
  change ((openCohomologyFunctor S 1).map (limKerUp S F f hfI l n)).hom.comp
    ((openCohomologyFunctor S 1).map (limKerMul S F n a.2)).hom = _
  rw [← ModuleCat.hom_comp, ← Functor.map_comp, limKerMul_up]
  rfl

/-- The up maps of two generators on cohomology commute. -/
theorem limRho_comm (l l' : Fin r) (n : ℕ) :
    (limRho S F f hfI l (n + 1)).comp (limRho S F f hfI l' n) =
      (limRho S F f hfI l' (n + 1)).comp (limRho S F f hfI l n) := by
  change ((openCohomologyFunctor S 1).map _).hom.comp ((openCohomologyFunctor S 1).map _).hom =
    ((openCohomologyFunctor S 1).map _).hom.comp ((openCohomologyFunctor S 1).map _).hom
  rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp,
    limKerUp_comm]

/-- The boundary maps carry the up map of `f_l` on `H⁰` to its up map on `H¹`. -/
theorem limBoundary_up (l : Fin r) (n : ℕ) (x : (openSectionsFunctor S).obj (F.obj.obj (op n))) :
    limBoundary S F (n + 1) ((openSectionsFunctor S).map (upMapOf S F f hfI l n) x) =
      limRho S F f hfI l n (limBoundary S F n x) :=
  congrArg (fun φ => φ.hom x) (limBoundaryHom_up S F f hfI l n)

/-! ### The two consequences of the graded splitting -/

section GradedSplitting

variable {d : ℕ} (hd : 1 ≤ d)
  {Ψ : Stacks.Coherent.GradedSplittingComponents S.A S.I S.U.ι (limit F.obj) r d}
  (hΨ : ∀ n : ℕ, Stacks.Coherent.gradedSplittingEvalHom Ψ f n =
    AlgebraicGeometry.SheafOfModules.Submodule.ιModules (idealPowerMultiple
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι) (n * d) (limit F.obj)))

include hd in
/-- For `1 ≤ d`, `n ≤ (n + 1) d - 1`. -/
theorem le_pred_succ_mul (n : ℕ) : n ≤ (n + 1) * d - 1 := by
  have h : n + 1 ≤ (n + 1) * d := Nat.le_mul_of_pos_right _ hd
  omega

include hd in
/-- For `1 ≤ d`, `(n + 1) d - 1 + 1 = (n + 1) d`. -/
theorem pred_succ_mul_add_one (n : ℕ) : (n + 1) * d - 1 + 1 = (n + 1) * d := by
  have h : n + 1 ≤ (n + 1) * d := Nat.le_mul_of_pos_right _ hd
  omega

include hfI hΨ in
/-- **[Stacks, Tag 0EH6] applied to the boundaries.** The boundary of an element of `H⁰(U, F_n)`
coming from `H⁰(U, F_{(n+1)d - 1})` lies in `∑_{a ∈ I^{n+1}} μ_a(H¹(U, F))`. -/
theorem limBoundary_tr_mem_iSup (n : ℕ)
    (t : (openSectionsFunctor S).obj (F.obj.obj (op ((n + 1) * d - 1)))) :
    limBoundary S F n ((openSectionsFunctor S).map (tr S F (le_pred_succ_mul hd n)) t) ∈
      ⨆ a : ↥(S.I ^ (n + 1)), LinearMap.range (limMu S F n a) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_kernel_lift_ιModules S F (k := n + 1) (pred_succ_mul_add_one hd n)
  have hmor : limKerIncl S F (le_pred_succ_mul hd n) = ψ ≫
      ∑ σ ∈ (Stacks.ReesAlgebra.degreeMonomials r (n + 1)).attach,
        Stacks.Coherent.gradedSplittingComponentAt Ψ
            (Stacks.ReesAlgebra.mem_degreeMonomials.1 σ.2) ≫
          limKerMul S F n (prod_pow_mem_pow S f hfI σ.1
            (Stacks.ReesAlgebra.mem_degreeMonomials.1 σ.2)) := by
    rw [← cancel_mono (kernel.ι (limπ S F n)), limKerIncl_ι, Category.assoc,
      Preadditive.sum_comp]
    simp only [Category.assoc, limKerMul_ι]
    rw [← ιModules_eq_sum_gradedSplitting S F f hΨ (n + 1), hψ]
  have h : limBoundary S F n ((openSectionsFunctor S).map (tr S F (le_pred_succ_mul hd n)) t) =
      ((openCohomologyFunctor S 1).map (limKerIncl S F (le_pred_succ_mul hd n))).hom
        (limBoundary S F _ t) :=
    congrArg (fun φ => φ.hom t) (limBoundaryHom_incl S F (le_pred_succ_mul hd n))
  rw [h, hmor, Functor.map_comp, Functor.map_sum, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_sum]
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact Submodule.mem_iSup_of_mem ⟨_, prod_pow_mem_pow S f hfI σ.1
    (Stacks.ReesAlgebra.mem_degreeMonomials.1 σ.2)⟩ ⟨_, rfl⟩

include hd hfI hΨ in
/-- **[Stacks, Tag 0EH6] applied to `H¹(U, F)`.** The kernel of `H¹(U, F) → H¹(U, F_{d-1})` lies
in `I · H¹(U, F)`. -/
theorem ker_cohomology_limπ_le (x : (openCohomologyFunctor S 1).obj (limit F.obj))
    (hx : ((openCohomologyFunctor S 1).map (limπ S F (d - 1))).hom x = 0) :
    x ∈ (S.I • ⊤ : Submodule S.A ((openCohomologyFunctor S 1).obj (limit F.obj))) := by
  classical
  have hN : d - 1 + 1 = 1 * d := by omega
  obtain ⟨ψ, hψ⟩ := exists_kernel_lift_ιModules S F hN
  have hex : LinearMap.range
      ((((cohDelta S).functor 1).map (kernel.ι (limπ S F (d - 1))))).hom =
      LinearMap.ker ((((cohDelta S).functor 1).map (limπ S F (d - 1)))).hom :=
    ((cohDelta S).exact_map (limShortComplex_shortExact S F (d - 1)) 1).moduleCat_range_eq_ker
  have hxr : x ∈ LinearMap.range
      ((((cohDelta S).functor 1).map (kernel.ι (limπ S F (d - 1))))).hom := by
    rw [hex]
    exact hx
  obtain ⟨y, hy⟩ := hxr
  let y' : (openCohomologyFunctor S 1).obj (limKer S F (d - 1)) := y
  have hxy : x = ((openCohomologyFunctor S 1).map (kernel.ι (limπ S F (d - 1)))).hom y' := hy.symm
  rw [hxy, ← hψ, ιModules_eq_sum_gradedSplitting S F f hΨ 1, Preadditive.comp_sum, Functor.map_sum,
    ModuleCat.hom_sum]
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [← Category.assoc, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    openCohomologyFunctor_map_sectionSmul]
  have hσ := prod_pow_mem_pow S f hfI σ.1 (Stacks.ReesAlgebra.mem_degreeMonomials.1 σ.2)
  rw [pow_one] at hσ
  exact Submodule.smul_mem_smul hσ Submodule.mem_top

end GradedSplitting

/-! ### The Mittag-Leffler property -/

/-- **Condition (a) of [Stacks, Tag 0EHH] in cohomological dimension one.** In Situation 0EHC
with `cd(A, I) = 1`, let `(F_n)` be an object of `Coh(U, I𝒪_U)` such that every transition map
of `(H¹(U, F_n))` into a given level has, from some level on, a finite `A`-module as image. Then
the inverse system `(H⁰(U, F_n))` satisfies the Mittag-Leffler condition. -/
theorem isMittagLefflerCategorical_globalSectionsSystem_of_cd_one
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (hH1 : ∀ N : ℕ, ∃ M : ℕ, ∃ h : N ≤ M, Module.Finite S.A
      (LinearMap.range ((openCohomologyFunctor S 1).map (tr S F h)).hom)) :
    IsMittagLefflerCategorical (globalSectionsSystem S F) := by
  classical
  have := isNoetherian_complement S
  obtain ⟨r, gen, hgen⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian S.I)
  have hf : S.I = Ideal.span (Set.range gen) := hgen.symm
  have hfI : ∀ j, gen j ∈ S.I := fun j => hf ▸ Ideal.subset_span ⟨j, rfl⟩
  obtain ⟨c, hc, φ, hφ⟩ :=
    Stacks.LocalCohomology.exists_pow_linearMaps_sum_eq_self S.A S.I gen hf hcd
  have hcoh : Stacks.Coherent.IsCoherentAdicSystem
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf S.A S.I S.U.ι) F.obj :=
    idealOnOpen_eq_baseIdealSheaf S ▸ F.property
  obtain ⟨d, hcd', ψ, -, -, Ψ, ⟨-, hΨ⟩, -⟩ :=
    Stacks.Coherent.existsUnique_gradedSplitting S.A S.I gen hf hcd hc φ hφ S.U.ι F.obj hcoh
  have hd : 1 ≤ d := hc.trans hcd'
  -- `H¹(U, F) / I` is a finite `A`-module.
  have hV : Module.Finite S.A ((openCohomologyFunctor S 1).obj (limit F.obj) ⧸
      (S.I • ⊤ : Submodule S.A ((openCohomologyFunctor S 1).obj (limit F.obj)))) := by
    obtain ⟨M, hM, hfinM⟩ := hH1 (d - 1)
    refine Stacks.AdicObstruction.finite_quotient_smul_top_of_ker_le
      ((openCohomologyFunctor S 1).map (limπ S F (d - 1))).hom
      (fun x hx => ker_cohomology_limπ_le S F gen hfI hd hΨ x hx) ?_
    have hle : LinearMap.range ((openCohomologyFunctor S 1).map (limπ S F (d - 1))).hom ≤
        LinearMap.range ((openCohomologyFunctor S 1).map (tr S F hM)).hom := by
      rintro _ ⟨y, rfl⟩
      refine ⟨((openCohomologyFunctor S 1).map (limπ S F M)).hom y, ?_⟩
      rw [← ModuleCat.comp_apply, ← Functor.map_comp, limπ_tr]
    refine Module.Finite.iff_fg.mpr ?_
    have hmap := (IsNoetherian.noetherian ((LinearMap.range
      ((openCohomologyFunctor S 1).map (limπ S F (d - 1))).hom).comap
        (LinearMap.range ((openCohomologyFunctor S 1).map (tr S F hM)).hom).subtype)).map
      (LinearMap.range ((openCohomologyFunctor S 1).map (tr S F hM)).hom).subtype
    rwa [Submodule.map_comap_subtype, inf_of_le_right hle] at hmap
  refine Stacks.Cohomology.EventualLifting.isMittagLefflerCategorical_of_eventualLifting
    (globalSectionsSystem S F) gen S.I
    (fun l n => ((openSectionsFunctor S).map (upMapOf S F gen hfI l n)).hom)
    (O := fun n => AdicCompletion S.I ((openCohomologyFunctor S 1).obj (limKer S F n)))
    (fun n => (AdicCompletion.of S.I _).comp (limBoundary S F n))
    (fun l n => (AdicCompletion.map S.I (limRho S F gen hfI l n)).restrictScalars S.A) hfI
    ?_ (fun n => idealPow_smul_globalSections_eq_bot S F n) ?_ ?_
    (fun n => (Stacks.AdicObstruction.obstructionSpan (limMu S F) n).restrictScalars S.A)
    (fun l n x hx => Stacks.AdicObstruction.map_mem_obstructionSpan gen (limMu S F)
      (limRho S F gen hfI) hfI (limRho_comp_limMu S F gen hfI) l n hx)
    (fun D hDP hDμ hDann => Stacks.AdicObstruction.exists_eventual_sum_shift_of_obstructionSpan
      gen (limMu S F) (limRho S F gen hfI) hf hV (limRho_comp_limMu S F gen hfI)
      (limRho_comm S F gen hfI) D hDP hDμ hDann)
    (fun n => (n + 1) * d - 1) (le_pred_succ_mul hd) ?_
  · intro l n x
    change ((openSectionsFunctor S).map (upMapOf S F gen hfI l n) ≫
      (openSectionsFunctor S).map (succTrans S F n)).hom x = gen l • x
    rw [← Functor.map_comp, upMapOf_trans]
    exact openSectionsFunctor_map_sectionSmul S (gen l) _ x
  · intro n x hx m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
    have hmem : limBoundary S F n x ∈
        (S.I ^ k • ⊤ : Submodule S.A ((openCohomologyFunctor S 1).obj (limKer S F n))) := by
      have h0 : AdicCompletion.eval S.I _ k
          (AdicCompletion.of S.I _ (limBoundary S F n x)) = 0 := by
        change AdicCompletion.eval S.I _ k
          ((AdicCompletion.of S.I _).comp (limBoundary S F n) x) = 0
        rw [hx, map_zero]
      rwa [AdicCompletion.eval_of, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
    exact mem_range_tr_of_limBoundary_mem S F n k x hmem
  · intro l n x
    change AdicCompletion.of S.I _ (limBoundary S F (n + 1)
      ((openSectionsFunctor S).map (upMapOf S F gen hfI l n) x)) = AdicCompletion.map S.I _
        (AdicCompletion.of S.I _ (limBoundary S F n x))
    rw [limBoundary_up, AdicCompletion.map_of]
  · rintro n _ ⟨t, rfl⟩
    exact Stacks.AdicObstruction.of_mem_obstructionSpan (limMu S F) n
      (limBoundary_tr_mem_iSup S F gen hfI hd hΨ n t)

end Stacks.Algebraization

end
