module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.LerayEdge

/-!
# Injectivity of the Leray edge map

For `g₁ = v ≫ g₀` and an abelian sheaf `K` on the small étale site of the source of `v`, the
Leray edge map `𝟙⁻¹ R^r g₀_*(v_* K) ⟶ R^r g₁_* K` (`Stacks.EtaleCohomology.lerayEdge`) is
injective when `R^a v_* K = 0` for `0 < a < r`, and bijective when `R^a v_* K = 0` for all
`a > 0`. These are the consequences of the relative Leray spectral sequence
([Stacks, Tag 0734]) used in the proof of [Stacks, Tag 0F07]; they are proved by dimension
shifting along an injective hull `0 ⟶ K ⟶ I ⟶ Q ⟶ 0`, using that the base change maps commute
with the connecting morphisms of the higher direct images. In degree one no vanishing is needed
and the argument is the four lemma, with `v_*` applied to the hull only left exact.

## Main results

* `Stacks.EtaleCohomology.mono_lerayEdge_one` — injectivity in degree one.
* `Stacks.EtaleCohomology.mono_lerayEdge` — injectivity under vanishing of `R^a v_* K`,
  `0 < a < r`.
* `Stacks.EtaleCohomology.epi_lerayEdge`, `Stacks.EtaleCohomology.isIso_lerayEdge` —
  surjectivity and bijectivity when `v_*` is exact on `K`.
* `Stacks.EtaleCohomology.higherBaseChangeMapAb_comp_directImageδ` — the compatibility with the
  connecting morphisms for the square `g₁ ≫ 𝟙 = v ≫ g₀`.

## References

* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section

variable {A A' B : Scheme.{u}} (g₀ : A ⟶ B) (g₁ : A' ⟶ B) (v : A' ⟶ A)
  (w : g₁ ≫ 𝟙 B = v ≫ g₀)

/-- The pullback `f⁻¹` of abelian sheaves on small étale sites preserves epimorphisms. -/
instance smallEtalePullbackAb_preservesEpimorphisms {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtalePullbackAb f).PreservesEpimorphisms := inferInstance

/-- The pullback `f⁻¹` of abelian sheaves on small étale sites preserves monomorphisms. -/
instance smallEtalePullbackAb_preservesMonomorphisms {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtalePullbackAb f).PreservesMonomorphisms := inferInstance

/-- The short exact sequence `0 ⟶ K ⟶ I ⟶ Q ⟶ 0` of an injective hull. -/
abbrev injectiveHullSeq {X : Scheme.{u}} (K : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  ShortComplex.mk (Injective.ι K) (cokernel.π (Injective.ι K)) (cokernel.condition _)

/-- The sequence `0 ⟶ K ⟶ I ⟶ Q ⟶ 0` of an injective hull is short exact. -/
theorem injectiveHullSeq_shortExact {X : Scheme.{u}} (K : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (injectiveHullSeq K).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- The image under `v_*` of the injective hull of `K`, completed by the cokernel of
`v_* K ⟶ v_* I`. -/
abbrev pushforwardHullSeq (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    ShortComplex (Sheaf (smallEtaleTopology A) Ab.{u + 1}) :=
  ShortComplex.mk ((smallEtalePushforwardAb v).map (Injective.ι K))
    (cokernel.π ((smallEtalePushforwardAb v).map (Injective.ι K))) (cokernel.condition _)

/-- The sequence `0 ⟶ v_* K ⟶ v_* I ⟶ Coker(v_* K ⟶ v_* I) ⟶ 0` is short exact. -/
theorem pushforwardHullSeq_shortExact (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    (pushforwardHullSeq v K).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- The map from the cokernel of `v_* K ⟶ v_* I` to `v_* Q`. -/
abbrev pushforwardHullDesc (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    cokernel ((smallEtalePushforwardAb v).map (Injective.ι K)) ⟶
      (smallEtalePushforwardAb v).obj (cokernel (Injective.ι K)) :=
  cokernel.desc _ ((smallEtalePushforwardAb v).map (cokernel.π (Injective.ι K))) (by
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero])

/-- The map `Coker(v_* K ⟶ v_* I) ⟶ v_* Q` is a monomorphism. -/
instance mono_pushforwardHullDesc (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    Mono (pushforwardHullDesc v K) := by
  have hex : ((injectiveHullSeq K).map (smallEtalePushforwardAb v)).Exact :=
    (injectiveHullSeq_shortExact K).exact.map_of_mono_of_preservesKernel _ inferInstance
      inferInstance
  exact hex.mono_cokernelDesc

/-- The comparison of `v⁻¹` of `pushforwardHullSeq` with the injective hull sequence. -/
def pushforwardHullSeqCounit (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    (pushforwardHullSeq v K).map (smallEtalePullbackAb v) ⟶ injectiveHullSeq K where
  τ₁ := (smallEtaleAdjunctionAb v).counit.app K
  τ₂ := (smallEtaleAdjunctionAb v).counit.app _
  τ₃ := ((smallEtaleAdjunctionAb v).homEquiv _ _).symm (pushforwardHullDesc v K)
  comm₁₂ := ((smallEtaleAdjunctionAb v).counit.naturality _).symm
  comm₂₃ := by
    dsimp
    rw [← Adjunction.homEquiv_naturality_left_symm, cokernel.π_desc,
      Adjunction.homEquiv_counit]
    exact ((smallEtaleAdjunctionAb v).counit.naturality _).symm

/-- The connecting morphism `R^n g_* X₃ ⟶ R^{n+1} g_* X₁` of the higher direct images at a short
exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`. -/
abbrev directImageδ {X Y : Scheme.{u}} (g : X ⟶ Y)
    {S : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS : S.ShortExact) (n : ℕ) :
    ((smallEtalePushforwardAb g).rightDerived n).obj S.X₃ ⟶
      ((smallEtalePushforwardAb g).rightDerived (n + 1)).obj S.X₁ :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb g)).δ hS n

/-- The composite `R^n g_* X₂ ⟶ R^n g_* X₃ ⟶ R^{n+1} g_* X₁` vanishes. -/
theorem map_g_directImageδ {X Y : Scheme.{u}} (g : X ⟶ Y)
    {S : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS : S.ShortExact) (n : ℕ) :
    ((smallEtalePushforwardAb g).rightDerived n).map S.g ≫ directImageδ g hS n = 0 :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb g)).map_g_δ hS n

/-- The sequence `R^n g_* X₂ ⟶ R^n g_* X₃ ⟶ R^{n+1} g_* X₁` is exact. -/
theorem exact_directImageδ {X Y : Scheme.{u}} (g : X ⟶ Y)
    {S : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk _ _ (map_g_directImageδ g hS n)).Exact :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb g)).exact_δ₁ hS n

/-- The sequence `R^n g_* X₃ ⟶ R^{n+1} g_* X₁ ⟶ R^{n+1} g_* X₂` is exact. -/
theorem exact_directImageδ_map_f {X Y : Scheme.{u}} (g : X ⟶ Y)
    {S : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS : S.ShortExact) (n : ℕ) :
    (ShortComplex.mk (directImageδ g hS n) (((smallEtalePushforwardAb g).rightDerived (n + 1)).map
      S.f) ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb g)).δ_map_f hS n)).Exact :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb g)).exact_δ₂ hS n

/-- If `R^{n+1} g_* X₂ = 0`, the connecting morphism `R^n g_* X₃ ⟶ R^{n+1} g_* X₁` is an
epimorphism. -/
theorem epi_directImageδ {X Y : Scheme.{u}} (g : X ⟶ Y)
    {S : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS : S.ShortExact) (n : ℕ)
    (h : IsZero (((smallEtalePushforwardAb g).rightDerived (n + 1)).obj S.X₂)) :
    Epi (directImageδ g hS n) :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb g)).epi_δ_of_map_f_eq_zero hS n (h.eq_of_tgt _ _)

/-- If `R^n g_* X₂ = 0`, the connecting morphism `R^n g_* X₃ ⟶ R^{n+1} g_* X₁` is a
monomorphism. -/
theorem mono_directImageδ {X Y : Scheme.{u}} (g : X ⟶ Y)
    {S : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS : S.ShortExact) (n : ℕ)
    (h : IsZero (((smallEtalePushforwardAb g).rightDerived n).obj S.X₂)) :
    Mono (directImageδ g hS n) :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb g)).mono_δ_of_map_g_eq_zero hS n (h.eq_of_src _ _)

/-- For the square `g₁ ≫ 𝟙 = v ≫ g₀`, short exact sequences `S` on `A` and `S'` on `A'` and
`σ : v⁻¹S ⟶ S'`, the base change maps commute with the connecting morphisms `directImageδ`. -/
theorem higherBaseChangeMapAb_comp_directImageδ (q : ℕ)
    {S : ShortComplex (Sheaf (smallEtaleTopology A) Ab.{u + 1})} (hS : S.ShortExact)
    {S' : ShortComplex (Sheaf (smallEtaleTopology A') Ab.{u + 1})} (hS' : S'.ShortExact)
    (σ : S.map (smallEtalePullbackAb v) ⟶ S') :
    ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w q).app S.X₃ ≫
        ((smallEtalePushforwardAb g₁).rightDerived q).map σ.τ₃) ≫ directImageδ g₁ hS' q =
      (smallEtalePullbackAb (𝟙 B)).map (directImageδ g₀ hS q) ≫
        ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w (q + 1)).app S.X₁ ≫
        ((smallEtalePushforwardAb g₁).rightDerived (q + 1)).map σ.τ₁) := by
  rw [Category.assoc]
  exact higherBaseChangeMapAb_comp_δ (𝟙 B) g₀ g₁ v w q hS hS' σ

/-- **The four lemma for the Leray ladder in degree one.** Let `S'` on `A` and `S` on `A'` be
short exact and `σ : v⁻¹S' ⟶ S`. If `R¹g₀_* S'.X₂ = 0`, the degree-zero comparison at the
middle terms is an epimorphism and the one at the right-hand terms a monomorphism, then the
degree-one comparison `𝟙⁻¹R¹g₀_* S'.X₁ ⟶ R¹g₁_* S.X₁` at the left-hand terms is a
monomorphism. -/
theorem mono_higherBaseChangeMapAb_one_comp_of_ladder
    {S' : ShortComplex (Sheaf (smallEtaleTopology A) Ab.{u + 1})} (hS' : S'.ShortExact)
    {S : ShortComplex (Sheaf (smallEtaleTopology A') Ab.{u + 1})} (hS : S.ShortExact)
    (σ : S'.map (smallEtalePullbackAb v) ⟶ S)
    (hI : IsZero (((smallEtalePushforwardAb g₀).rightDerived 1).obj S'.X₂))
    (h₁ : Epi ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w 0).app S'.X₂ ≫
      ((smallEtalePushforwardAb g₁).rightDerived 0).map σ.τ₂))
    (h₂ : Mono ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w 0).app S'.X₃ ≫
      ((smallEtalePushforwardAb g₁).rightDerived 0).map σ.τ₃)) :
    Mono ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w 1).app S'.X₁ ≫
      ((smallEtalePushforwardAb g₁).rightDerived 1).map σ.τ₁) := by
  have hsq₂ := higherBaseChangeMapAb_comp_directImageδ g₀ g₁ v w 0 hS' hS σ
  have hsq₁ : ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w 0).app S'.X₂ ≫
        ((smallEtalePushforwardAb g₁).rightDerived 0).map σ.τ₂) ≫
        ((smallEtalePushforwardAb g₁).rightDerived 0).map S.g =
      (smallEtalePullbackAb (𝟙 B)).map (((smallEtalePushforwardAb g₀).rightDerived 0).map S'.g) ≫
        ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w 0).app S'.X₃ ≫
          ((smallEtalePushforwardAb g₁).rightDerived 0).map σ.τ₃) := by
    have hn := (higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w 0).naturality S'.g
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun z => _ ≫ ((smallEtalePushforwardAb g₁).rightDerived 0).map z)
      σ.comm₂₃
  have hza : (smallEtalePullbackAb (𝟙 B)).map (((smallEtalePushforwardAb g₀).rightDerived 0).map
        S'.g) ≫ (smallEtalePullbackAb (𝟙 B)).map (directImageδ g₀ hS' 0) = 0 := by
    rw [← (smallEtalePullbackAb (𝟙 B)).map_comp, map_g_directImageδ, Functor.map_zero]
  have := epi_directImageδ g₀ hS' 0 hI
  exact Stacks.Cohomology.BaseChange.mono_of_ladder hza (map_g_directImageδ g₁ hS 0) hsq₁ hsq₂
    (exact_directImageδ g₁ hS 0) inferInstance h₁ h₂

/-- **The dimension-shifting step for the Leray ladder.** Let `S'` on `A` and `S` on `A'` be
short exact and `σ : v⁻¹S' ⟶ S`, with `R^{n+2}g₀_* S'.X₂ = 0` and `R^{n+1}g₁_* S.X₂ = 0`. If the
comparison in degree `n + 1` at the right-hand terms is a monomorphism, so is the comparison in
degree `n + 2` at the left-hand terms. -/
theorem mono_higherBaseChangeMapAb_succ_comp_of_ladder (n : ℕ)
    {S' : ShortComplex (Sheaf (smallEtaleTopology A) Ab.{u + 1})} (hS' : S'.ShortExact)
    {S : ShortComplex (Sheaf (smallEtaleTopology A') Ab.{u + 1})} (hS : S.ShortExact)
    (σ : S'.map (smallEtalePullbackAb v) ⟶ S)
    (hI' : IsZero (((smallEtalePushforwardAb g₀).rightDerived (n + 2)).obj S'.X₂))
    (hI : IsZero (((smallEtalePushforwardAb g₁).rightDerived (n + 1)).obj S.X₂))
    (hm : Mono ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w (n + 1)).app S'.X₃ ≫
      ((smallEtalePushforwardAb g₁).rightDerived (n + 1)).map σ.τ₃)) :
    Mono ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w (n + 2)).app S'.X₁ ≫
      ((smallEtalePushforwardAb g₁).rightDerived (n + 2)).map σ.τ₁) := by
  have key := higherBaseChangeMapAb_comp_directImageδ g₀ g₁ v w (n + 1) hS' hS σ
  have := mono_directImageδ g₁ hS (n + 1) hI
  have := epi_directImageδ g₀ hS' (n + 1) hI'
  have hm' : Mono ((smallEtalePullbackAb (𝟙 B)).map (directImageδ g₀ hS' (n + 1)) ≫
      ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w (n + 2)).app S'.X₁ ≫
        ((smallEtalePushforwardAb g₁).rightDerived (n + 2)).map σ.τ₁)) := key ▸ mono_comp _ _
  have : Mono ((smallEtalePullbackAb (𝟙 B)).map (directImageδ g₀ hS' (n + 1))) :=
    mono_of_mono _ ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w (n + 2)).app S'.X₁ ≫
      ((smallEtalePushforwardAb g₁).rightDerived (n + 2)).map σ.τ₁)
  have : IsIso ((smallEtalePullbackAb (𝟙 B)).map (directImageδ g₀ hS' (n + 1))) :=
    isIso_of_mono_of_epi _
  have e := IsIso.inv_hom_id_assoc ((smallEtalePullbackAb (𝟙 B)).map (directImageδ g₀ hS' (n + 1)))
    ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w (n + 2)).app S'.X₁ ≫
      ((smallEtalePushforwardAb g₁).rightDerived (n + 2)).map σ.τ₁)
  rw [← e]
  exact mono_comp _ _

/-- The comparison at the right-hand terms of the ladder of an injective hull, in degree zero,
is a monomorphism: it factors as `R⁰g₀_*` of the injection `Coker(v_*K ⟶ v_*I) ⟶ v_*Q` followed by
the invertible Leray edge map. -/
theorem mono_higherBaseChangeMapAb_zero_comp_pushforwardHullSeqCounit
    (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    Mono ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w 0).app (pushforwardHullSeq v K).X₃ ≫
      ((smallEtalePushforwardAb g₁).rightDerived 0).map (pushforwardHullSeqCounit v K).τ₃) := by
  have hτ := higherBaseChangeMapAb_app_comp_map_eq g₀ g₁ v w 0 (pushforwardHullSeqCounit v K).τ₃
  have e : (smallEtaleAdjunctionAb v).homEquiv _ _ (pushforwardHullSeqCounit v K).τ₃ =
      pushforwardHullDesc v K := Equiv.apply_symm_apply _ _
  rw [e] at hτ
  have := mono_rightDerived_zero_map g₀ (pushforwardHullDesc v K)
  rw [hτ]
  infer_instance

/-- **The Leray edge map in degree one is injective**, with no hypothesis: this is the
injectivity of `R¹g₀_*(v_* K) ⟶ R¹g₁_* K` in the five-term exact sequence of the Leray spectral
sequence. -/
theorem mono_lerayEdge_one (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) :
    Mono (lerayEdge g₀ g₁ v w 1 K) :=
  mono_higherBaseChangeMapAb_one_comp_of_ladder g₀ g₁ v w (pushforwardHullSeq_shortExact v K)
    (injectiveHullSeq_shortExact K) (pushforwardHullSeqCounit v K)
    (isZero_rightDerived_succ_of_injective g₀ 0 _)
    (inferInstanceAs (Epi (lerayEdge g₀ g₁ v w 0 (Injective.under K))))
    (mono_higherBaseChangeMapAb_zero_comp_pushforwardHullSeqCounit g₀ g₁ v w K)

/-- The comparison of `v⁻¹ v_*` of a short complex with the complex itself, by the counit. -/
def pullbackPushforwardCounit (S : ShortComplex (Sheaf (smallEtaleTopology A') Ab.{u + 1})) :
    (S.map (smallEtalePushforwardAb v)).map (smallEtalePullbackAb v) ⟶ S where
  τ₁ := (smallEtaleAdjunctionAb v).counit.app _
  τ₂ := (smallEtaleAdjunctionAb v).counit.app _
  τ₃ := (smallEtaleAdjunctionAb v).counit.app _
  comm₁₂ := ((smallEtaleAdjunctionAb v).counit.naturality _).symm
  comm₂₃ := ((smallEtaleAdjunctionAb v).counit.naturality _).symm

/-- If `R¹v_* K = 0`, then `v_*` takes the injective hull sequence of `K` to a short exact
sequence. -/
theorem shortExact_map_injectiveHullSeq (K : Sheaf (smallEtaleTopology A') Ab.{u + 1})
    (hK : IsZero (((smallEtalePushforwardAb v).rightDerived 1).obj K)) :
    ((injectiveHullSeq K).map (smallEtalePushforwardAb v)).ShortExact := by
  have hepi0 : Epi (((smallEtalePushforwardAb v).rightDerived 0).map (injectiveHullSeq K).g) :=
    (exact_directImageδ v (injectiveHullSeq_shortExact K) 0).epi_f (hK.eq_of_tgt _ _)
  have hepi := epi_map_of_epi_rightDerived_zero_map v (injectiveHullSeq K).g
  have hmono : Mono ((injectiveHullSeq K).map (smallEtalePushforwardAb v)).f :=
    inferInstanceAs (Mono ((smallEtalePushforwardAb v).map (Injective.ι K)))
  exact ShortComplex.ShortExact.mk'
    ((injectiveHullSeq_shortExact K).exact.map_of_mono_of_preservesKernel
      (smallEtalePushforwardAb v) inferInstance inferInstance) hmono hepi

/-- The higher direct images of the quotient of an injective hull are those of `K`, shifted. -/
theorem isZero_rightDerived_cokernel_hull (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) (b : ℕ)
    (hK : IsZero (((smallEtalePushforwardAb v).rightDerived (b + 2)).obj K)) :
    IsZero (((smallEtalePushforwardAb v).rightDerived (b + 1)).obj (injectiveHullSeq K).X₃) :=
  (exact_directImageδ v (injectiveHullSeq_shortExact K) (b + 1)).isZero_X₂
    ((isZero_rightDerived_succ_of_injective v b _).eq_of_src _ _) (hK.eq_of_tgt _ _)

/-- The higher direct images of the quotient of an injective hull, in positive degree `a`, vanish
if `R^{a+1} v_* K` does. -/
private theorem isZero_rightDerived_cokernel_hull_of_pos
    (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}) (a : ℕ) (ha : 0 < a)
    (hK : IsZero (((smallEtalePushforwardAb v).rightDerived (a + 1)).obj K)) :
    IsZero (((smallEtalePushforwardAb v).rightDerived a).obj (injectiveHullSeq K).X₃) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  exact isZero_rightDerived_cokernel_hull v K b hK

/-- **Injectivity of the Leray edge map.** For a commutative square `g₁ ≫ 𝟙 = v ≫ g₀` and an
abelian sheaf `K` on the small étale site of the source of `v` with `R^a v_* K = 0` for
`0 < a < r`, the Leray edge map `𝟙⁻¹ R^r g₀_*(v_* K) ⟶ R^r g₁_* K` is a monomorphism. This is
the injectivity of the edge map of the relative Leray spectral sequence for `g₁ = v ≫ g₀`
([Stacks, Tag 0734]), proved by dimension shifting: degree one is the four lemma, and in higher
degree `R¹v_* K = 0` makes `v_*` exact on an injective hull `0 ⟶ K ⟶ I ⟶ Q ⟶ 0`, and `Q`
satisfies the hypothesis one degree lower. -/
theorem mono_lerayEdge : ∀ (r : ℕ) (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}),
    (∀ a, 0 < a → a < r → IsZero (((smallEtalePushforwardAb v).rightDerived a).obj K)) →
      Mono (lerayEdge g₀ g₁ v w r K)
  | 0, K, _ => inferInstance
  | 1, K, _ => mono_lerayEdge_one g₀ g₁ v w K
  | r + 2, K, hK =>
    mono_higherBaseChangeMapAb_succ_comp_of_ladder g₀ g₁ v w r
      (shortExact_map_injectiveHullSeq v K (hK 1 (by omega) (by omega)))
      (injectiveHullSeq_shortExact K)
      (pullbackPushforwardCounit v (injectiveHullSeq K))
      (isZero_rightDerived_succ_of_injective g₀ (r + 1)
        ((smallEtalePushforwardAb v).obj (Injective.under K)))
      (isZero_rightDerived_succ_of_injective g₁ r (Injective.under K))
      (mono_lerayEdge (r + 1) (injectiveHullSeq K).X₃ fun a ha har =>
        isZero_rightDerived_cokernel_hull_of_pos v K a ha (hK (a + 1) (by omega) (by omega)))

/-- The surjectivity step of the Leray ladder: if the comparison in degree `n` at the
right-hand terms is an epimorphism and `R^{n+1}g₁_* S.X₂ = 0`, the comparison in degree `n + 1`
at the left-hand terms is an epimorphism. -/
theorem epi_higherBaseChangeMapAb_succ_comp_of_ladder (n : ℕ)
    {S' : ShortComplex (Sheaf (smallEtaleTopology A) Ab.{u + 1})} (hS' : S'.ShortExact)
    {S : ShortComplex (Sheaf (smallEtaleTopology A') Ab.{u + 1})} (hS : S.ShortExact)
    (σ : S'.map (smallEtalePullbackAb v) ⟶ S)
    (hI : IsZero (((smallEtalePushforwardAb g₁).rightDerived (n + 1)).obj S.X₂))
    (he : Epi ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w n).app S'.X₃ ≫
      ((smallEtalePushforwardAb g₁).rightDerived n).map σ.τ₃)) :
    Epi ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w (n + 1)).app S'.X₁ ≫
      ((smallEtalePushforwardAb g₁).rightDerived (n + 1)).map σ.τ₁) := by
  have key := higherBaseChangeMapAb_comp_directImageδ g₀ g₁ v w n hS' hS σ
  have := epi_directImageδ g₁ hS n hI
  have : Epi ((smallEtalePullbackAb (𝟙 B)).map (directImageδ g₀ hS' n) ≫
      ((higherBaseChangeMapAb (𝟙 B) g₀ g₁ v w (n + 1)).app S'.X₁ ≫
        ((smallEtalePushforwardAb g₁).rightDerived (n + 1)).map σ.τ₁)) := key ▸ epi_comp _ _
  exact epi_of_epi ((smallEtalePullbackAb (𝟙 B)).map (directImageδ g₀ hS' n)) _

/-- **Surjectivity of the Leray edge map when `v_*` is exact on `K`.** If all positive higher
direct images `R^a v_* K` vanish, the Leray edge map `𝟙⁻¹ R^r g₀_*(v_* K) ⟶ R^r g₁_* K` is an
epimorphism in every degree; together with `mono_lerayEdge` it is then an isomorphism, the
degenerate case of the relative Leray spectral sequence. -/
theorem epi_lerayEdge : ∀ (r : ℕ) (K : Sheaf (smallEtaleTopology A') Ab.{u + 1}),
    (∀ a, 0 < a → IsZero (((smallEtalePushforwardAb v).rightDerived a).obj K)) →
      Epi (lerayEdge g₀ g₁ v w r K)
  | 0, K, _ => inferInstance
  | r + 1, K, hK =>
    epi_higherBaseChangeMapAb_succ_comp_of_ladder g₀ g₁ v w r
      (shortExact_map_injectiveHullSeq v K (hK 1 (by omega))) (injectiveHullSeq_shortExact K)
      (pullbackPushforwardCounit v (injectiveHullSeq K))
      (isZero_rightDerived_succ_of_injective g₁ r (Injective.under K))
      (epi_lerayEdge r (injectiveHullSeq K).X₃ fun a ha =>
        isZero_rightDerived_cokernel_hull_of_pos v K a ha (hK (a + 1) (by omega)))

/-- **The Leray edge map is invertible when `v_*` is exact on `K`**: if `R^a v_* K = 0` for all
`a > 0`, then `𝟙⁻¹ R^r g₀_*(v_* K) ≅ R^r g₁_* K` through the Leray edge map. -/
theorem isIso_lerayEdge (r : ℕ) (K : Sheaf (smallEtaleTopology A') Ab.{u + 1})
    (hK : ∀ a, 0 < a → IsZero (((smallEtalePushforwardAb v).rightDerived a).obj K)) :
    IsIso (lerayEdge g₀ g₁ v w r K) :=
  have := mono_lerayEdge g₀ g₁ v w r K fun a ha _ => hK a ha
  have := epi_lerayEdge g₀ g₁ v w r K hK
  isIso_of_mono_of_epi _

end

end Stacks.EtaleCohomology
