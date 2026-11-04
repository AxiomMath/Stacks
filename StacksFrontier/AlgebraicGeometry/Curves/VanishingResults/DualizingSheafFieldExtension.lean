module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGenerationCoherent
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SituationBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FlatTraceNoetherian
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineFaithful
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine

/-!
# The dualizing sheaf of a proper curve under an extension of the ground field

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `K/k` be a field extension, `p : X_K ⟶ X` the projection, and let
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))` and `ω_{X_K}` be the dualizing sheaves of [Stacks, Tag 0BS2] of
`X ⟶ Spec k` and of `X_K ⟶ Spec K`. Part (2) of [Stacks, Tag 0E32] says that `p^*ω_X ≅ ω_{X_K}`.
This file proves it.

## The argument

The source deduces it from base change for the right adjoint of [Stacks, Tag 0A9E]
([Stacks, Tag 0AA8]). Here only the sheaves are compared, through the property that characterizes
them: clause (5) of [Stacks, Tag 0BS2], `Hom(𝒢, ω_{X_K}) = Hom_K(H¹(X_K, 𝒢), K)` for
quasi-coherent `𝒢`, and similarly on `X`.

* `H¹(X_K, p^*ω_X)` is one-dimensional over `K` ([Stacks, Tag 02KH]), so a nonzero `K`-linear form
  on it is, by clause (5) for `ω_{X_K}`, a morphism `θ : p^*ω_X ⟶ ω_{X_K}` with `H¹(θ)` injective.
* `θ` is a monomorphism. Its kernel `𝒩` has `H¹(𝒩) ⟶ H¹(p^*ω_X)` zero. For every `k`-linear form
  `f` on `K` let `tr_f : p_*p^*ω_X ⟶ ω_X` be its trace (`Stacks.FlatTrace.trace`); then
  `p_*𝒩 ⟶ p_*p^*ω_X ⟶ ω_X` is zero on `H¹`, hence zero by clause (5) on `X`. The traces are jointly
  faithful, so `p_*𝒩 ⟶ p_*p^*ω_X` is zero, and `p_*` is faithful on quasi-coherent modules.
* Every morphism `p^*ℰ ⟶ ω_{X_K}` from the pullback of a coherent `ℰ` factors through `θ`. Choose
  maps `φ_l : ℰ ⟶ ω_X` whose forms on `H¹(X, ℰ)` (clause (5) on `X`) are a basis of its dual. The
  forms of `p^*φ_l ≫ θ` on `H¹(X_K, p^*ℰ)` are `K`-linearly independent: a relation between them
  is, since `θ` is a monomorphism, a relation `∑ a_l • p^*φ_l = 0`, which the traces turn into the
  relations `∑ f(a_l) • φ_l = 0` on `X`, so every `f(a_l)` vanishes. As
  `dim_K H¹(X_K, p^*ℰ) = dim_k H¹(X, ℰ)` ([Stacks, Tag 02KH]) they are a basis.
* `θ` is an epimorphism: `ω_{X_K}` is a quotient of `p^*p_*ω_{X_K}` (`p` is affine), which is the
  filtered colimit of the `p^*ℰ` over the coherent submodules `ℰ ⊆ p_*ω_{X_K}`
  ([Stacks, Tag 01PG]), so a nonzero morphism out of `coker(θ)` would be nonzero on some
  `p^*ℰ ⟶ ω_{X_K}`, which factors through `θ`.

## Main results

* `AlgebraicGeometry.CohenMacaulayCurveSituation.mono_omegaComparison` and
  `AlgebraicGeometry.CohenMacaulayCurveSituation.epi_omegaComparison`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.dualizingSheafPullbackIso`: **part (2) of
  [Stacks, Tag 0E32]** at the dualizing sheaf, `p^*ω_X ≅ ω_{X_K}`, with no hypothesis.

## References

* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open Stacks.Cohomology.AffineComparison

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u}) (K : Type u) [Field K] [Algebra S.k K]

/-! ### The base change square and its standing hypotheses -/

/-- The spectrum of the extension field, spelled through the base-changed situation. -/
abbrev bcT : Scheme.{u} := Spec (.of (S.baseChange K).k)

/-- The morphism `Spec K ⟶ Spec k`. -/
abbrev bcq : S.bcT K ⟶ Spec (.of S.k) := Spec.map (CommRingCat.ofHom (algebraMap S.k K))

/-- The cartesian square of the base change `X_K ⟶ X` over `Spec K ⟶ Spec k`. -/
abbrev bcSquare : IsPullback (S.baseChangeProj K) (S.baseChange K).f S.f (S.bcq K) :=
  IsPullback.of_hasPullback _ _

/-- The ring of global functions of the spectrum of a field is a field. -/
theorem isField_Γ_Spec (k : Type u) [Field k] : IsField Γ(Spec (.of k), ⊤) :=
  MulEquiv.isField (Field.toIsField k)
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv

/-- `Γ(Spec k, ⊤) ⟶ Γ(Spec K, ⊤)` is flat. -/
theorem flat_bcSquare :
    RingHom.Flat ((S.bcq K).appLE ⊤ ⊤ (le_preimage_top (S.bcq K) ⊤)).hom :=
  flat_appLE_Spec_map (CommRingCat.ofHom (algebraMap S.k K))
    (RingHom.flat_algebraMap_iff.2 inferInstance)

/-- Every open of the curve is quasi-compact, the curve being Noetherian. -/
theorem isCompact_opens (W : S.X.Opens) : IsCompact (W : Set S.X) :=
  have := S.isNoetherian'
  NoetherianSpace.isCompact _

attribute [local instance] isAffineHom_baseChangeProj

/-- The trace `p_* p^* F ⟶ F` of a `Γ(Spec k, ⊤)`-linear functional on `Γ(Spec K, ⊤)`. -/
abbrev bcTrace (F : S.X.Modules) [F.IsQuasicoherent]
    (f : letI := baseAlgebra (S.bcq K);
      Γ(S.bcT K, ⊤) →ₗ[Γ(Spec (.of S.k), ⊤)] Γ(Spec (.of S.k), ⊤)) :
    (Scheme.Modules.pushforward (S.baseChangeProj K)).obj
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) ⟶ F :=
  Stacks.FlatTrace.trace (S.bcSquare K) (S.flat_bcSquare K) S.isCompact_opens F f

/-- Cohomology over a field acts on elements as the underlying right derived functor. -/
theorem cohomologyOverFieldMap_hom_apply {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (x : cohomologyOverField k f F n) :
    (cohomologyOverFieldMap k f φ n).hom x =
      (((moduleGlobalSections X).rightDerived n).map φ).hom x := by
  unfold cohomologyOverFieldMap
  rfl

/-- Cohomology over a field sends the zero morphism to zero. -/
theorem cohomologyOverFieldMap_zero' {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F G : X.Modules) (n : ℕ) :
    cohomologyOverFieldMap k f (0 : F ⟶ G) n = 0 := by
  ext x
  rw [cohomologyOverFieldMap_hom_apply, Functor.map_zero]
  rfl

/-! ### Notation for the two dualizing sheaves -/

/-- The dualizing sheaf `ω_X` of the curve. -/
abbrev omega : S.X.Modules := Stacks.Duality.dualizingSheafOverField S.f

/-- The pullback `p^*ω_X` of the dualizing sheaf to the base change. -/
abbrev omegaPullback : (S.baseChange K).X.Modules :=
  (Scheme.Modules.pullback (S.baseChangeProj K)).obj S.omega

/-- The dualizing sheaf `ω_X` is quasi-coherent. -/
instance isQuasicoherent_omega : S.omega.IsQuasicoherent :=
  Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f

/-- The pullback `p^*ω_X` is quasi-coherent. -/
instance isQuasicoherent_omegaPullback : (S.omegaPullback K).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _

/-- The structure morphism `X ⟶ Spec k` of the curve is proper. -/
instance isProper_f : IsProper S.f := S.proper

/-- `H¹(X_K, p^*ω_X)` is one-dimensional over `K`. -/
theorem finrank_cohomologyOverField_one_omegaPullback :
    Module.finrank (S.baseChange K).k
      (cohomologyOverField (S.baseChange K).k (S.baseChange K).f (S.omegaPullback K) 1) = 1 :=
  (finrank_cohomologyOverField_baseChange_field S.k K (S.baseChangeProj K) (S.baseChange K).f
    S.f (S.bcSquare K) S.omega 1).trans
    (finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one S)

/-- A linear map out of a one-dimensional space is injective as soon as it is nonzero. -/
theorem injective_of_ne_zero_of_finrank_eq_one {F V W : Type*} [Field F] [AddCommGroup V]
    [Module F V] [AddCommGroup W] [Module F W] (hV : Module.finrank F V = 1)
    (g : V →ₗ[F] W) (hg : g ≠ 0) : Function.Injective g := by
  have : FiniteDimensional F V := Module.finite_of_finrank_eq_succ hV
  have hsum := LinearMap.finrank_range_add_finrank_ker g
  have hrange : Module.finrank F (LinearMap.range g) ≠ 0 := by
    intro h0
    exact hg (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
  have hker : Module.finrank F (LinearMap.ker g) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

/-- A nonzero `K`-linear form on `H¹(X_K, p^*ω_X)`. -/
theorem exists_dual_ne_zero_omegaPullback :
    ∃ τ : cohomologyOverField (S.baseChange K).k (S.baseChange K).f (S.omegaPullback K) 1 →ₗ[
      (S.baseChange K).k] (S.baseChange K).k, τ ≠ 0 := by
  have hV := S.finrank_cohomologyOverField_one_omegaPullback K
  have : Nontrivial
      (cohomologyOverField (S.baseChange K).k (S.baseChange K).f (S.omegaPullback K) 1) :=
    Module.nontrivial_of_finrank_eq_succ hV
  obtain ⟨v, hv⟩ := exists_ne
    (0 : cohomologyOverField (S.baseChange K).k (S.baseChange K).f (S.omegaPullback K) 1)
  by_contra h
  push Not at h
  exact hv ((Module.forall_dual_apply_eq_zero_iff (S.baseChange K).k v).mp fun φ => by
    rw [h φ]; rfl)

/-- The chosen nonzero form on `H¹(X_K, p^*ω_X)`. -/
def omegaPullbackForm :
    cohomologyOverField (S.baseChange K).k (S.baseChange K).f (S.omegaPullback K) 1 →ₗ[
      (S.baseChange K).k] (S.baseChange K).k :=
  (S.exists_dual_ne_zero_omegaPullback K).choose

/-- The chosen form on `H¹(X_K, p^*ω_X)` is nonzero. -/
theorem omegaPullbackForm_ne_zero : S.omegaPullbackForm K ≠ 0 :=
  (S.exists_dual_ne_zero_omegaPullback K).choose_spec

/-- Clause (5) of [Stacks, Tag 0BS2] for `ω_{X_K}`. -/
abbrev dualK := firstCohomologyDuality_dualizingSheafOverField (S.baseChange K)

/-- There is a morphism `p^*ω_X ⟶ ω_{X_K}` corresponding to the chosen nonzero form on
`H¹(X_K, p^*ω_X)` under clause (5) of [Stacks, Tag 0BS2] for `ω_{X_K}`. -/
theorem exists_omegaComparison : ∃ θ : S.omegaPullback K ⟶ (S.baseChange K).omega,
    (S.dualK K).dual (S.omegaPullback K) inferInstance θ = S.omegaPullbackForm K :=
  ((S.dualK K).dual (S.omegaPullback K) inferInstance).surjective _

/-- **The comparison morphism `θ : p^*ω_X ⟶ ω_{X_K}`**, the morphism corresponding to the chosen
nonzero form on `H¹(X_K, p^*ω_X)` under clause (5) of [Stacks, Tag 0BS2] for `ω_{X_K}`. -/
def omegaComparison : S.omegaPullback K ⟶ (S.baseChange K).omega :=
  (S.exists_omegaComparison K).choose

/-- Under clause (5) of [Stacks, Tag 0BS2] for `ω_{X_K}`, `omegaComparison` corresponds to the
chosen nonzero form `omegaPullbackForm` on `H¹(X_K, p^*ω_X)`. -/
theorem dual_omegaComparison :
    (S.dualK K).dual (S.omegaPullback K) inferInstance (S.omegaComparison K) =
      S.omegaPullbackForm K :=
  (S.exists_omegaComparison K).choose_spec

/-- Clause (5) for `ω_{X_K}`, read on a morphism factoring through `θ`. -/
theorem dual_comp_omegaComparison {G : (S.baseChange K).X.Modules} (hG : G.IsQuasicoherent)
    (ψ : G ⟶ S.omegaPullback K) :
    (S.dualK K).dual G hG (ψ ≫ S.omegaComparison K) =
      (S.omegaPullbackForm K).comp
        (cohomologyOverFieldMap (S.baseChange K).k (S.baseChange K).f ψ 1).hom := by
  rw [(S.dualK K).dual_comp G (S.omegaPullback K) hG inferInstance ψ (S.omegaComparison K),
    dual_omegaComparison]

/-- `H¹(X_K, θ)` is injective. -/
theorem injective_cohomologyOverFieldMap_omegaComparison :
    Function.Injective (cohomologyOverFieldMap (S.baseChange K).k (S.baseChange K).f
      (S.omegaComparison K) 1).hom := by
  refine injective_of_ne_zero_of_finrank_eq_one (S.finrank_cohomologyOverField_one_omegaPullback K)
    _ fun h => S.omegaPullbackForm_ne_zero K ?_
  have h1 := (S.dualK K).dual_comp (S.omegaPullback K) (S.baseChange K).omega inferInstance
    (Stacks.Duality.isQuasicoherent_dualizingSheafOverField (S.baseChange K).f)
    (S.omegaComparison K) (𝟙 _)
  rwa [Category.comp_id, dual_omegaComparison, h, LinearMap.comp_zero] at h1

/-! ### The comparison is a monomorphism -/

/-- **A quasi-coherent submodule of `p^*ω_X` on which `H¹` vanishes is zero.** Its direct image
`p_*𝒩 ⟶ p_*p^*ω_X ⟶ ω_X` along every trace is killed by `t ∘ H¹(-)`, where `t` is the trace of
`X`, so it is zero by clause (5) of [Stacks, Tag 0BS2] on `X`; the traces are jointly faithful, and
`p_*` is faithful on quasi-coherent modules. -/
theorem isZero_of_mono_omegaPullback (N : (S.baseChange K).X.Modules) [N.IsQuasicoherent]
    (ι : N ⟶ S.omegaPullback K) [Mono ι]
    (h : cohomologyOverFieldMap (S.baseChange K).k (S.baseChange K).f ι 1 = 0) : IsZero N := by
  let p := S.baseChangeProj K
  have hR : ((moduleGlobalSections (S.baseChange K).X).rightDerived 1).map ι = 0 := by
    ext x
    have hx := cohomologyOverFieldMap_hom_apply (S.baseChange K).f ι 1 x
    rw [h] at hx
    exact hx.symm
  have hpush : ((moduleGlobalSections S.X).rightDerived 1).map
      ((Scheme.Modules.pushforward p).map ι) = 0 := by
    have hnat := Stacks.Tag0CKW.cohomologyIsoPushforward_hom_naturality p ι 1
    rw [hR, Functor.map_zero, zero_comp] at hnat
    exact (cancel_epi (cohomologyIsoPushforward p N 1).hom).mp (by rw [← hnat, comp_zero])
  have hNq : ((Scheme.Modules.pushforward p).obj N).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom p N inferInstance
  have hH : cohomologyOverFieldMap S.k S.f ((Scheme.Modules.pushforward p).map ι) 1 = 0 := by
    ext x
    rw [cohomologyOverFieldMap_hom_apply, hpush]
    rfl
  have htr : ∀ f, (Scheme.Modules.pushforward p).map ι ≫ S.bcTrace K S.omega f = 0 := by
    intro f
    refine ((firstCohomologyDuality_dualizingSheafOverField S).dual _ hNq).injective ?_
    rw [(firstCohomologyDuality_dualizingSheafOverField S).dual_comp _ _ hNq
      (Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom p _ inferInstance), hH,
      ModuleCat.hom_zero, LinearMap.comp_zero, map_zero]
  have hp0 : (Scheme.Modules.pushforward p).map ι = 0 :=
    Stacks.FlatTrace.eq_zero_of_forall_comp_trace_eq_zero (S.bcSquare K) (S.flat_bcSquare K)
      S.isCompact_opens S.omega (isField_Γ_Spec S.k) _ htr
  have hι0 : ι = 0 :=
    Stacks.AlgebraicGeometry.ModuleLimits.affinePushforwardFaithful p inferInstance
      inferInstance ι 0 (by rw [hp0, Functor.map_zero])
  refine (IsZero.iff_id_eq_zero N).mpr ((cancel_mono ι).mp ?_)
  rw [hι0, comp_zero, comp_zero]

/-- **`θ : p^*ω_X ⟶ ω_{X_K}` is a monomorphism.** Its kernel `𝒩` is quasi-coherent and
`H¹(X_K, 𝒩) ⟶ H¹(X_K, p^*ω_X)` vanishes, being followed by the injective `H¹(θ)`. -/
theorem mono_omegaComparison : Mono (S.omegaComparison K) := by
  refine (Preadditive.mono_iff_isZero_kernel _).mpr ?_
  refine S.isZero_of_mono_omegaPullback K _ (kernel.ι (S.omegaComparison K)) ?_
  ext x
  refine S.injective_cohomologyOverFieldMap_omegaComparison K ?_
  have h := congrArg
    (fun g => (cohomologyOverFieldMap (S.baseChange K).k (S.baseChange K).f g 1).hom x)
    (kernel.condition (S.omegaComparison K))
  simp only [cohomologyOverFieldMap_comp, cohomologyOverFieldMap_zero'] at h
  rwa [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]

/-! ### Traces against pulled back classes -/

/-- The trace of `f` on first cohomology, `H¹(X_K, p^*F) = H¹(X, p_*p^*F) ⟶ H¹(X, F)`. -/
def bcTraceCohomology (F : S.X.Modules) [F.IsQuasicoherent]
    (f : letI := baseAlgebra (S.bcq K);
      Γ(S.bcT K, ⊤) →ₗ[Γ(Spec (.of S.k), ⊤)] Γ(Spec (.of S.k), ⊤)) :
    ((moduleGlobalSections (S.baseChange K).X).rightDerived 1).obj
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) →+
      ((moduleGlobalSections S.X).rightDerived 1).obj F :=
  let ν : ((moduleGlobalSections (S.baseChange K).X).rightDerived 1).obj
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) →+
      (ModuleCat.restrictScalars (S.baseChangeProj K).appTop.hom).obj
        (((moduleGlobalSections (S.baseChange K).X).rightDerived 1).obj
          ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F)) :=
    { toFun := fun y => y, map_zero' := rfl, map_add' := fun _ _ => rfl }
  (((moduleGlobalSections S.X).rightDerived 1).map (S.bcTrace K F f)).hom.toAddMonoidHom.comp
    ((cohomologyIsoPushforward (S.baseChangeProj K)
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) 1).hom.hom.toAddMonoidHom.comp ν)

/-- **The trace of `f` against a pulled back class multiplied by `b`** is `f(b)` times the class:
`H¹(tr_f)(b • p^* x) = f(b) • x`. This is `H¹` of `u_b ≫ tr_f = f(b) • 𝟙`. -/
theorem bcTraceCohomology_smul_cohomologyPullback (F : S.X.Modules) [F.IsQuasicoherent]
    (f : letI := baseAlgebra (S.bcq K);
      Γ(S.bcT K, ⊤) →ₗ[Γ(Spec (.of S.k), ⊤)] Γ(Spec (.of S.k), ⊤))
    (b : Γ(S.bcT K, ⊤)) (x : ((moduleGlobalSections S.X).rightDerived 1).obj F) :
    S.bcTraceCohomology K F f
        (((S.baseChange K).f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom b •
          (Stacks.Tag0CKW.cohomologyPullback (S.bcSquare K) F 1).hom x :
          ((moduleGlobalSections (S.baseChange K).X).rightDerived 1).obj
            ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F)) =
      ((S.f.appLE ⊤ ⊤ (le_preimage_top S.f ⊤)).hom (f b) • x :
        ((moduleGlobalSections S.X).rightDerived 1).obj F) := by
  show (((moduleGlobalSections S.X).rightDerived 1).map (S.bcTrace K F f)).hom
      ((cohomologyIsoPushforward (S.baseChangeProj K)
        ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F) 1).hom.hom
        (Stacks.Tag0CKW.restrictScalarsMk (S.baseChangeProj K).appTop.hom
          (((S.baseChange K).f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom b •
            (Stacks.Tag0CKW.cohomologyPullback (S.bcSquare K) F 1).hom x :
            ((moduleGlobalSections (S.baseChange K).X).rightDerived 1).obj
              ((Scheme.Modules.pullback (S.baseChangeProj K)).obj F)))) = _
  rw [Stacks.Tag0CKW.smul_cohomologyPullback, Stacks.Tag0CKW.hom_restrictScalarsMk_inv,
    ← ModuleCat.comp_apply, ← Functor.map_comp, bcTrace, Stacks.FlatTrace.twistedUnit_comp_trace]
  exact Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply S.X _ 1 F x

/-- **The canonical map `Γ(Spec K) ⊗ H¹(X, F) ⟶ H¹(X_K, p^*F)` is injective.** Composed with the
trace of `f` on cohomology it is `f ⊗ 1`, and the functionals on `Γ(Spec K)` detect the elements of
its tensor products. -/
theorem injective_cohomologyBaseChangeLinearMap (F : S.X.Modules) [F.IsQuasicoherent] :
    Function.Injective (Stacks.Tag0CKW.cohomologyBaseChangeLinearMap (S.bcSquare K) F 1) := by
  let := baseAlgebra (S.bcq K)
  rw [injective_iff_map_eq_zero]
  intro z hz
  refine Stacks.FlatTrace.eq_zero_of_forall_lid_rTensor_eq_zero_of_isField (isField_Γ_Spec S.k) z
    fun f => ?_
  have key : ∀ w, S.bcTraceCohomology K F f
      (Stacks.Tag0CKW.cohomologyBaseChangeLinearMap (S.bcSquare K) F 1 w) =
      TensorProduct.lid _ _ (LinearMap.rTensor _ f w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero, map_zero]
      exact (S.bcTraceCohomology K F f).map_zero
    | tmul b x =>
      rw [Stacks.Tag0CKW.cohomologyBaseChangeLinearMap_tmul, LinearMap.rTensor_tmul,
        TensorProduct.lid_tmul]
      exact S.bcTraceCohomology_smul_cohomologyPullback K F f b x
    | add w w' hw hw' =>
      rw [map_add, map_add, map_add, ← hw, ← hw']
      exact (S.bcTraceCohomology K F f).map_add _ _
  rw [← key, hz]
  exact (S.bcTraceCohomology K F f).map_zero

/-! ### Scalars of the base acting on morphisms -/

/-- Multiplication by a function `b` on `Spec K`, on a module on `X_K`. -/
abbrev bcSmul (G : (S.baseChange K).X.Modules) (b : Γ(S.bcT K, ⊤)) : G ⟶ G :=
  (Scheme.smulEnd (S.baseChange K).X
    (((S.baseChange K).f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom b)).app G

/-- Multiplication by a function `c` on `Spec k`, on a module on `X`. -/
abbrev baseSmul (G : S.X.Modules) (c : Γ(Spec (.of S.k), ⊤)) : G ⟶ G :=
  (Scheme.smulEnd S.X ((S.f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom c)).app G

/-- Transporting a function on `Spec R` along `ΓSpecIso` and back does not change its image under
`f.appLE`. -/
private theorem ΓSpecIso_inv_comp_appLE_apply {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (r : Γ(Spec R, ⊤)) :
    ((Scheme.ΓSpecIso R).inv ≫ f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom
        ((Scheme.ΓSpecIso R).hom r) = (f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom r := by
  rw [CommRingCat.comp_apply, Iso.hom_inv_id_apply]

/-- The action of `Γ(Spec k, ⊤)` on cohomology through `f.appLE` is the action of `k`. -/
private theorem appLE_smul_eq_ΓSpecIso_smul {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (G : X.Modules) (n : ℕ) (r : Γ(Spec (.of k), ⊤))
    (v : ((moduleGlobalSections X).rightDerived n).obj G) :
    ((f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom r • v :
        ((moduleGlobalSections X).rightDerived n).obj G) =
      (Scheme.ΓSpecIso (.of k)).hom r • (show cohomologyOverField k f G n from v) := by
  change _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom
        ((Scheme.ΓSpecIso (.of k)).hom r) • v
  rw [ΓSpecIso_inv_comp_appLE_apply f r]

/-- `H¹(X, r •)` is multiplication by the corresponding element of `k`. -/
private theorem cohomologyOverFieldMap_smulEnd_apply {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (G : X.Modules) (r : Γ(Spec (.of k), ⊤))
    (x : cohomologyOverField k f G 1) :
    (cohomologyOverFieldMap k f
        ((Scheme.smulEnd X ((f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom r)).app G) 1).hom x =
      (Scheme.ΓSpecIso (.of k)).hom r • x := by
  refine (cohomologyOverFieldMap_hom_apply f _ 1 x).trans ?_
  exact (Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply X _ 1 G x).trans
    (appLE_smul_eq_ΓSpecIso_smul f G 1 r x)

/-- `H¹(X_K, b •)` is multiplication by the corresponding element of `K`. -/
theorem cohomologyOverFieldMap_bcSmul_apply (G : (S.baseChange K).X.Modules)
    (b : Γ(S.bcT K, ⊤))
    (x : cohomologyOverField (S.baseChange K).k (S.baseChange K).f G 1) :
    (cohomologyOverFieldMap (S.baseChange K).k (S.baseChange K).f (S.bcSmul K G b) 1).hom x =
      (Scheme.ΓSpecIso (.of (S.baseChange K).k)).hom b • x :=
  cohomologyOverFieldMap_smulEnd_apply (S.baseChange K).f G b x

/-- `H¹(X, c •)` is multiplication by the corresponding element of `k`. -/
theorem cohomologyOverFieldMap_baseSmul_apply (G : S.X.Modules) (c : Γ(Spec (.of S.k), ⊤))
    (x : cohomologyOverField S.k S.f G 1) :
    (cohomologyOverFieldMap S.k S.f (S.baseSmul G c) 1).hom x =
      (Scheme.ΓSpecIso (.of S.k)).hom c • x :=
  cohomologyOverFieldMap_smulEnd_apply S.f G c x

/-- Clause (5) for the dualizing sheaf of `T` turns multiplication by `r` into multiplication
by `r`. -/
private theorem dual_smulEnd_comp (T : CohenMacaulayCurveSituation.{u}) {G : T.X.Modules}
    (hG : G.IsQuasicoherent) (ψ : G ⟶ T.omega) (r : Γ(Spec (.of T.k), ⊤)) :
    (firstCohomologyDuality_dualizingSheafOverField T).dual G hG
        ((Scheme.smulEnd T.X ((T.f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom r)).app G ≫ ψ) =
      (Scheme.ΓSpecIso (.of T.k)).hom r •
        (firstCohomologyDuality_dualizingSheafOverField T).dual G hG ψ := by
  refine ((firstCohomologyDuality_dualizingSheafOverField T).dual_comp G G hG hG _ ψ).trans ?_
  ext x
  rw [LinearMap.comp_apply, cohomologyOverFieldMap_smulEnd_apply, map_smul]
  rfl

/-- Clause (5) for `ω_{X_K}` turns multiplication by `b` into multiplication by `b`. -/
theorem dualK_comp_bcSmul {G : (S.baseChange K).X.Modules} (hG : G.IsQuasicoherent)
    (ψ : G ⟶ (S.baseChange K).omega) (b : Γ(S.bcT K, ⊤)) :
    (S.dualK K).dual G hG (S.bcSmul K G b ≫ ψ) =
      (Scheme.ΓSpecIso (.of (S.baseChange K).k)).hom b • (S.dualK K).dual G hG ψ :=
  dual_smulEnd_comp (S.baseChange K) hG ψ b

/-- Clause (5) for `ω_X` turns multiplication by `c` into multiplication by `c`. -/
theorem dual_comp_baseSmul {G : S.X.Modules} (hG : G.IsQuasicoherent)
    (φ : G ⟶ S.omega) (c : Γ(Spec (.of S.k), ⊤)) :
    (firstCohomologyDuality_dualizingSheafOverField S).dual G hG (S.baseSmul G c ≫ φ) =
      (Scheme.ΓSpecIso (.of S.k)).hom c •
        (firstCohomologyDuality_dualizingSheafOverField S).dual G hG φ :=
  dual_smulEnd_comp S hG φ c

/-- A `K`-linear map out of `H¹(X_K, G)` turns multiplication by a function on `Spec K` into
multiplication by the corresponding element of `K`. -/
theorem map_appLE_smul {M : Type*} [AddCommGroup M] [Module (S.baseChange K).k M]
    (G : (S.baseChange K).X.Modules) (b : Γ(S.bcT K, ⊤))
    (μ : cohomologyOverField (S.baseChange K).k (S.baseChange K).f G 1 →ₗ[(S.baseChange K).k] M)
    (v : ((moduleGlobalSections (S.baseChange K).X).rightDerived 1).obj G) :
    μ (((S.baseChange K).f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom b • v :
        ((moduleGlobalSections (S.baseChange K).X).rightDerived 1).obj G) =
      (Scheme.ΓSpecIso (.of (S.baseChange K).k)).hom b • μ v := by
  exact (congrArg μ (appLE_smul_eq_ΓSpecIso_smul (S.baseChange K).f G 1 b v)).trans
    (map_smul μ _ _)

/-- The rank of cohomology over `Γ(Spec k, ⊤)` is its rank over `k`. -/
theorem rank_baseRestrictScalars_rightDerived (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) (n : ℕ) :
    Module.rank Γ(Spec (.of k), ⊤)
        ((baseRestrictScalars f).obj (((moduleGlobalSections X).rightDerived n).obj F)) =
      Module.rank k (cohomologyOverField k f F n) := by
  refine rank_eq_of_equiv_equiv (Scheme.ΓSpecIso (.of k)).hom (AddEquiv.refl _)
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.bijective fun r m => ?_
  exact appLE_smul_eq_ΓSpecIso_smul f F n r m

/-- `H¹(X_K, p^*ℰ)` is finite dimensional over `K` for a coherent `ℰ`. -/
private theorem finiteDimensional_cohomologyOverField_pullback (E : S.X.Modules)
    [E.IsQuasicoherent] [E.IsCoherent] :
    FiniteDimensional (S.baseChange K).k (cohomologyOverField (S.baseChange K).k
      (S.baseChange K).f ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E) 1) :=
  have := S.isCoherent_pullback_baseChangeProj K E ‹_›
  have : IsProper (S.baseChange K).f := (S.baseChange K).proper
  forall_finiteDimensional_cohomologyOverField_of_isProper _ _ _ ‹_› 1

/-- **The canonical map `Γ(Spec K) ⊗ H¹(X, ℰ) ⟶ H¹(X_K, p^*ℰ)` is surjective for a coherent
`ℰ`**: it is injective, and both sides have the same finite dimension
([Stacks, Tag 02KH]). -/
theorem surjective_cohomologyBaseChangeLinearMap (E : S.X.Modules) [E.IsQuasicoherent]
    [E.IsCoherent] :
    Function.Surjective (Stacks.Tag0CKW.cohomologyBaseChangeLinearMap (S.bcSquare K) E 1) := by
  let := baseAlgebra (S.bcq K)
  let : Field Γ(Spec (.of S.k), ⊤) := (isField_Γ_Spec S.k).toField
  let : Field Γ(S.bcT K, ⊤) := (isField_Γ_Spec _).toField
  have hfinE : FiniteDimensional S.k (cohomologyOverField S.k S.f E 1) :=
    forall_finiteDimensional_cohomologyOverField_of_isProper S.k S.f E ‹_› 1
  have hfinE' := S.finiteDimensional_cohomologyOverField_pullback K E
  have hr1 := rank_baseRestrictScalars_rightDerived S.k S.f E 1
  have hr2 := rank_baseRestrictScalars_rightDerived (S.baseChange K).k (S.baseChange K).f
    ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E) 1
  have hM : Module.Finite Γ(Spec (.of S.k), ⊤)
      ((baseRestrictScalars S.f).obj (((moduleGlobalSections S.X).rightDerived 1).obj E)) :=
    Module.rank_lt_aleph0_iff.mp (hr1 ▸ Module.rank_lt_aleph0_iff.mpr hfinE)
  have hN : Module.Finite Γ(S.bcT K, ⊤)
      ((baseRestrictScalars (S.baseChange K).f).obj
        (((moduleGlobalSections (S.baseChange K).X).rightDerived 1).obj
          ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E))) :=
    Module.rank_lt_aleph0_iff.mp (hr2 ▸ Module.rank_lt_aleph0_iff.mpr hfinE')
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (S.injective_cohomologyBaseChangeLinearMap K E)
  rw [Module.finrank_baseChange]
  have e1 := congrArg Cardinal.toNat hr1
  have e2 := congrArg Cardinal.toNat hr2
  change Module.finrank _ _ = Module.finrank _ _ at e1 e2
  rw [e1, e2]
  exact (finrank_cohomologyOverField_baseChange_field S.k K (S.baseChangeProj K)
    (S.baseChange K).f S.f (S.bcSquare K) E 1).symm

/-- **Two `K`-linear forms on `H¹(X_K, p^*ℰ)` agreeing on the pulled back classes are equal**, for
a coherent `ℰ`: the pulled back classes span. -/
theorem dual_ext_of_cohomologyPullback (E : S.X.Modules) [E.IsQuasicoherent] [E.IsCoherent]
    (μ₁ μ₂ : cohomologyOverField (S.baseChange K).k (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E) 1 →ₗ[(S.baseChange K).k]
        (S.baseChange K).k)
    (h : ∀ x : ((moduleGlobalSections S.X).rightDerived 1).obj E,
      μ₁ ((Stacks.Tag0CKW.cohomologyPullback (S.bcSquare K) E 1).hom x) =
        μ₂ ((Stacks.Tag0CKW.cohomologyPullback (S.bcSquare K) E 1).hom x)) : μ₁ = μ₂ := by
  let := baseAlgebra (S.bcq K)
  ext y
  obtain ⟨z, rfl⟩ := S.surjective_cohomologyBaseChangeLinearMap K E y
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero μ₁).trans (map_zero μ₂).symm
  | tmul b x =>
    rw [Stacks.Tag0CKW.cohomologyBaseChangeLinearMap_tmul]
    exact (S.map_appLE_smul K _ b μ₁ _).trans
      ((congrArg _ (h x)).trans (S.map_appLE_smul K _ b μ₂ _).symm)
  | add z w hz hw =>
    rw [map_add]
    exact ((map_add μ₁ _ _).trans (congrArg₂ (· + ·) hz hw)).trans (map_add μ₂ _ _).symm

/-! ### Morphisms out of pulled back coherent modules factor through `θ` -/

/-- Clause (5) for `ω_{X_K}` on a sum of pulled back morphisms twisted by functions on `Spec K`. -/
theorem dualK_sum_comp {E : S.X.Modules} {ι : Type*} (s : Finset ι) (φ : ι → (E ⟶ S.omega))
    (b : ι → Γ(S.bcT K, ⊤))
    (hq : ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E).IsQuasicoherent) :
    (S.dualK K).dual _ hq ((∑ l ∈ s, (Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) ≫
        S.bcSmul K (S.omegaPullback K) (b l)) ≫ S.omegaComparison K) =
      ∑ l ∈ s, (Scheme.ΓSpecIso (.of (S.baseChange K).k)).hom (b l) •
        (S.dualK K).dual _ hq
          ((Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) ≫ S.omegaComparison K) := by
  rw [Preadditive.sum_comp, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hnat : (Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) ≫
      S.bcSmul K (S.omegaPullback K) (b l) =
      S.bcSmul K _ (b l) ≫ (Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) :=
    (Scheme.smulEnd (S.baseChange K).X
      (((S.baseChange K).f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom (b l))).naturality
        ((Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l))
  rw [Category.assoc, ← Category.assoc _ (S.bcSmul K _ _), hnat, Category.assoc,
    S.dualK_comp_bcSmul K hq]

/-- **A vanishing sum of pulled back morphisms twisted by functions on `Spec K` gives vanishing
sums on `X` after every trace.** Push the relation forward along the unit of `p^* ⊣ p_*` and apply
the trace of `f`, which takes the twisted unit `x ↦ b • p^*x` to multiplication by `f(b)`. -/
theorem sum_baseSmul_comp_eq_zero {E : S.X.Modules} {ι : Type*} (s : Finset ι)
    (φ : ι → (E ⟶ S.omega)) (b : ι → Γ(S.bcT K, ⊤))
    (h : ∑ l ∈ s, (Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) ≫
        S.bcSmul K (S.omegaPullback K) (b l) = 0)
    (f : letI := baseAlgebra (S.bcq K);
      Γ(S.bcT K, ⊤) →ₗ[Γ(Spec (.of S.k), ⊤)] Γ(Spec (.of S.k), ⊤)) :
    ∑ l ∈ s, S.baseSmul E (f (b l)) ≫ φ l = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (S.baseChangeProj K)
  have h1 := congrArg (fun g => adj.unit.app E ≫
    (Scheme.Modules.pushforward (S.baseChangeProj K)).map g ≫ S.bcTrace K S.omega f) h
  simp only [Functor.map_sum, Functor.map_zero, zero_comp, comp_zero, Preadditive.sum_comp,
    Preadditive.comp_sum] at h1
  refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) h1
  have hu := adj.unit.naturality (φ l)
  simp only [Functor.id_map, Functor.comp_map] at hu
  have htw : adj.unit.app S.omega ≫ (Scheme.Modules.pushforward (S.baseChangeProj K)).map
      (S.bcSmul K (S.omegaPullback K) (b l)) ≫ S.bcTrace K S.omega f =
      S.baseSmul S.omega (f (b l)) := by
    rw [← Category.assoc]
    exact Stacks.FlatTrace.twistedUnit_comp_trace (S.bcSquare K) (S.flat_bcSquare K)
      S.isCompact_opens S.omega f (b l)
  have hsm : φ l ≫ S.baseSmul S.omega (f (b l)) = S.baseSmul E (f (b l)) ≫ φ l :=
    (Scheme.smulEnd S.X ((S.f.appLE ⊤ ⊤ (le_preimage_top _ ⊤)).hom (f (b l)))).naturality (φ l)
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, ← hu, Category.assoc, Category.assoc,
    htw, ← hsm]

/-- **Pulling back `k`-linearly independent forms gives `K`-linearly independent forms.** If the
forms on `H¹(X, ℰ)` given by `φ_l : ℰ ⟶ ω_X` under clause (5) of [Stacks, Tag 0BS2] are
`k`-linearly independent, then so are over `K` the forms on `H¹(X_K, p^*ℰ)` given by
`p^*φ_l ≫ θ`. -/
theorem linearIndependent_dualK_pullback_comp_omegaComparison (E : S.X.Modules)
    [E.IsQuasicoherent]
    (hq : ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E).IsQuasicoherent) {n : ℕ}
    (φ : Fin n → (E ⟶ S.omega))
    (hφ : LinearIndependent S.k fun l =>
      (firstCohomologyDuality_dualizingSheafOverField S).dual E inferInstance (φ l)) :
    LinearIndependent (S.baseChange K).k fun l => (S.dualK K).dual _ hq
      ((Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) ≫ S.omegaComparison K) := by
  let := baseAlgebra (S.bcq K)
  let : Field Γ(Spec (.of S.k), ⊤) := (isField_Γ_Spec S.k).toField
  have := S.mono_omegaComparison K
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  let b : Fin n → Γ(S.bcT K, ⊤) := fun l => (Scheme.ΓSpecIso (.of (S.baseChange K).k)).inv (a l)
  have hb : ∀ l, (Scheme.ΓSpecIso (.of (S.baseChange K).k)).hom (b l) = a l := fun l =>
    Iso.inv_hom_id_apply _ _
  have hsum : ∑ l, (Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) ≫
      S.bcSmul K (S.omegaPullback K) (b l) = 0 := by
    refine (cancel_mono (S.omegaComparison K)).mp ?_
    refine ((S.dualK K).dual _ hq).injective ?_
    rw [zero_comp, map_zero, S.dualK_sum_comp K _ φ b hq]
    refine (Finset.sum_congr rfl fun l _ => ?_).trans ha
    exact congrArg (· • (S.dualK K).dual _ hq
      ((Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) ≫ S.omegaComparison K)) (hb l)
  have hf : ∀ f : Γ(S.bcT K, ⊤) →ₗ[Γ(Spec (.of S.k), ⊤)] Γ(Spec (.of S.k), ⊤), f (b i) = 0 := by
    intro f
    have h1 := congrArg ((firstCohomologyDuality_dualizingSheafOverField S).dual E inferInstance)
      (S.sum_baseSmul_comp_eq_zero K _ φ b hsum f)
    rw [map_sum, map_zero] at h1
    have h1' : ∑ l, (Scheme.ΓSpecIso (.of S.k)).hom (f (b l)) •
        (firstCohomologyDuality_dualizingSheafOverField S).dual E inferInstance (φ l) = 0 :=
      Eq.trans (Finset.sum_congr rfl fun l _ =>
        (S.dual_comp_baseSmul inferInstance (φ l) (f (b l))).symm) h1
    exact (Scheme.ΓSpecIso (.of S.k)).commRingCatIsoToRingEquiv.injective
      ((Fintype.linearIndependent_iff.mp hφ _ h1' i).trans (map_zero _).symm)
  rw [← hb i, (Module.forall_dual_apply_eq_zero_iff _ (b i)).mp hf, map_zero]

/-- **Every `K`-linear form on `H¹(X_K, p^*ℰ)` comes from a morphism `p^*ℰ ⟶ p^*ω_X`**, for a
coherent `ℰ`: under clause (5) of [Stacks, Tag 0BS2] for `ω_{X_K}`, every morphism
`p^*ℰ ⟶ ω_{X_K}` factors through `θ`.

The forms `λ_l` of a basis of the dual of `H¹(X, ℰ)` are, by clause (5) on `X`, given by maps
`φ_l : ℰ ⟶ ω_X`. The forms `μ_l` given by `p^*φ_l ≫ θ` are `K`-linearly independent: a relation
`∑ a_l μ_l = 0` is, by clause (5) for `ω_{X_K}` and the injectivity of `θ`, the relation
`∑ a_l • p^*φ_l = 0`, and the traces of all functionals on `K` turn it into the relations
`∑ f(a_l) λ_l = 0`, so `f(a_l) = 0` for every `f`. There are `dim_k H¹(X, ℰ) = dim_K H¹(X_K, p^*ℰ)`
of them ([Stacks, Tag 02KH]), so they are a basis. -/
theorem exists_comp_omegaComparison_eq (E : S.X.Modules) [E.IsQuasicoherent] [E.IsCoherent]
    (hq : ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E).IsQuasicoherent)
    (μ : cohomologyOverField (S.baseChange K).k (S.baseChange K).f
      ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E) 1 →ₗ[(S.baseChange K).k]
        (S.baseChange K).k) :
    ∃ ψ : (Scheme.Modules.pullback (S.baseChangeProj K)).obj E ⟶ S.omegaPullback K,
      (S.dualK K).dual _ hq (ψ ≫ S.omegaComparison K) = μ := by
  classical
  let D := firstCohomologyDuality_dualizingSheafOverField S
  have hfin : FiniteDimensional S.k (cohomologyOverField S.k S.f E 1) :=
    forall_finiteDimensional_cohomologyOverField_of_isProper S.k S.f E ‹_› 1
  have hfin' := S.finiteDimensional_cohomologyOverField_pullback K E
  let n := Module.finrank S.k (Module.Dual S.k (cohomologyOverField S.k S.f E 1))
  let lam := Module.finBasis S.k (Module.Dual S.k (cohomologyOverField S.k S.f E 1))
  let φ : Fin n → (E ⟶ S.omega) := fun l => (D.dual E inferInstance).symm (lam l)
  let μv : Fin n → _ := fun l => (S.dualK K).dual _ hq
    ((Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) ≫ S.omegaComparison K)
  have hli : LinearIndependent (S.baseChange K).k μv :=
    S.linearIndependent_dualK_pullback_comp_omegaComparison K E hq φ (by
      convert lam.linearIndependent using 1
      exact funext fun l => (D.dual E inferInstance).apply_symm_apply _)
  have hcard : Fintype.card (Fin n) = Module.finrank (S.baseChange K).k
      (Module.Dual (S.baseChange K).k (cohomologyOverField (S.baseChange K).k
        (S.baseChange K).f ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E) 1)) := by
    rw [Fintype.card_fin, Subspace.dual_finrank_eq]
    show Module.finrank S.k (Module.Dual S.k _) = _
    rw [Subspace.dual_finrank_eq]
    exact (finrank_cohomologyOverField_baseChange_field S.k K (S.baseChangeProj K)
      (S.baseChange K).f S.f (S.bcSquare K) E 1).symm
  let B := basisOfLinearIndependentOfCardEqFinrank' μv hli hcard
  let b : Fin n → Γ(S.bcT K, ⊤) := fun l =>
    (Scheme.ΓSpecIso (.of (S.baseChange K).k)).inv (B.repr μ l)
  refine ⟨∑ l, (Scheme.Modules.pullback (S.baseChangeProj K)).map (φ l) ≫
    S.bcSmul K (S.omegaPullback K) (b l), ?_⟩
  rw [S.dualK_sum_comp K _ φ b hq]
  conv_rhs => rw [← B.sum_repr μ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']
  exact congrArg (· • μv l) (Iso.inv_hom_id_apply _ _)

/-! ### The comparison is an epimorphism -/

/-- **A nonzero morphism out of a quasi-coherent module on `X_K` is nonzero on the pullback of
some coherent module on `X`.** The counit `p^*p_*𝒢 ⟶ 𝒢` is an epimorphism, `p` being affine, and
`p_*𝒢` is the filtered colimit of its coherent submodules ([Stacks, Tag 01PG]), which `p^*`
preserves. -/
theorem exists_pullback_coherent_comp_ne_zero {G T : (S.baseChange K).X.Modules}
    [G.IsQuasicoherent] (φ : G ⟶ T) (hφ : φ ≠ 0) :
    ∃ (E : S.X.Modules) (_ : E.IsQuasicoherent) (_ : E.IsCoherent)
      (ψ : (Scheme.Modules.pullback (S.baseChangeProj K)).obj E ⟶ G), ψ ≫ φ ≠ 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (S.baseChangeProj K)
  have hepi : Epi (adj.counit.app G) :=
    Stacks.AlgebraicGeometry.ModuleLimits.affineCounitEpi (S.baseChangeProj K) G inferInstance
  have hne : adj.counit.app G ≫ φ ≠ 0 := fun h => hφ ((cancel_epi (adj.counit.app G)).mp
    (by rw [h, comp_zero]))
  have hq : ((Scheme.Modules.pushforward (S.baseChangeProj K)).obj G).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom _ G inferInstance
  have : CompactSpace S.X := QuasiCompact.compactSpace_of_compactSpace S.f
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have : QuasiSeparatedSpace S.X := inferInstance
  let hc := isColimit_finiteTypeQuasicoherentSubobjectCocone
    ((Scheme.Modules.pushforward (S.baseChangeProj K)).obj G)
  let hc' := isColimitOfPreserves (Scheme.Modules.pullback (S.baseChangeProj K)) hc
  by_contra hall
  push Not at hall
  refine hne ?_
  have hg : (adj.counit.app G ≫ φ : (Scheme.Modules.pullback (S.baseChangeProj K)).obj
      ((Scheme.Modules.pushforward (S.baseChangeProj K)).obj G) ⟶ T) = 0 := by
    refine hc'.hom_ext fun j => ?_
    have hj := j.property
    have : (j.obj : S.X.Modules).IsQuasicoherent := hj.1
    have : (j.obj : S.X.Modules).IsFiniteType := hj.2
    have : (j.obj : S.X.Modules).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType _
    calc _ = ((Scheme.Modules.pullback (S.baseChangeProj K)).map j.obj.arrow ≫
          adj.counit.app G) ≫ φ := (Category.assoc _ _ _).symm
      _ = 0 := hall _ inferInstance inferInstance _
      _ = _ := comp_zero.symm
  exact hg

/-- **`θ : p^*ω_X ⟶ ω_{X_K}` is an epimorphism.** A nonzero `ω_{X_K} ⟶ coker(θ)` would be nonzero
on some `p^*ℰ ⟶ ω_{X_K}` with `ℰ` coherent, and every such morphism factors through `θ`. -/
theorem epi_omegaComparison : Epi (S.omegaComparison K) := by
  refine Preadditive.epi_of_cokernel_zero ?_
  by_contra hne
  obtain ⟨E, hEq, hEc, ψ, hψ⟩ := S.exists_pullback_coherent_comp_ne_zero K
    (cokernel.π (S.omegaComparison K)) hne
  have hq : ((Scheme.Modules.pullback (S.baseChangeProj K)).obj E).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
  obtain ⟨ψ₀, hψ₀⟩ := S.exists_comp_omegaComparison_eq K E hq ((S.dualK K).dual _ hq ψ)
  have : ψ = ψ₀ ≫ S.omegaComparison K := ((S.dualK K).dual _ hq).injective hψ₀.symm
  rw [this, Category.assoc, cokernel.condition, comp_zero] at hψ
  exact hψ rfl

/-! ### Stacks Tag 0E32, part (2) -/

/-- **Part (2) of [Stacks, Tag 0E32].** For the curve of Situation [Stacks, Tag 0B5D] and a field
extension `K/k`, the inverse image of the dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` along
the projection `X_K ⟶ X` is the dualizing sheaf of `X_K ⟶ Spec K`.

The isomorphism is `θ`, the morphism corresponding to a nonzero form on the one-dimensional
`H¹(X_K, p^*ω_X)` under clause (5) of [Stacks, Tag 0BS2] for `ω_{X_K}`; it is a monomorphism and
an epimorphism, see the module documentation. -/
def dualizingSheafPullbackIso :
    (Scheme.Modules.pullback (S.baseChangeProj K)).obj
        (Stacks.Duality.dualizingSheafOverField S.f) ≅
      Stacks.Duality.dualizingSheafOverField (S.baseChange K).f :=
  have := S.mono_omegaComparison K
  have := S.epi_omegaComparison K
  have : IsIso (S.omegaComparison K) := isIso_of_mono_of_epi _
  asIso (S.omegaComparison K)

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
