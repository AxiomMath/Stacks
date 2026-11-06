module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.InternalHomPairingDerived
public import StacksFrontier.Algebra.Homology.HomologySequenceCoeffacement

/-!
# Perfectness of a family of pairings by descending induction

Let `R` be a finite ring, `Q` a compact topological group, `S` a ring, `φ : S →+* Rᵐᵒᵖ`, and
`T` the injective resolution of `ℚ/ℤ[-d]` (`Stacks.ContinuousCohomology.traceTarget`). A pairing
`P` of complexes `A`, `E` of discrete modules into `T` gives a chain map
`Φ_P : A ⟶ Hom^•_ℤ(E, T)` (`Stacks.ContinuousCohomology.internalHomComplexOfPairing`), and
`Hⁱ(Hom^•_ℤ(E, T)) = (H^{d-i}(E))^∨`.

This file proves that `Φ_P` is a quasi-isomorphism for every member of a family of pairings
as soon as

* it is an isomorphism on `H^d`,
* `Hⁱ(A) = 0` and `H^{d-i}(E) = 0` for `i > d`, and
* for every member and every `i < d` there is a short exact sequence `0 → A₁ → A₂ → A → 0` and
  a short exact sequence `0 → E → E₂ → E₁ → 0` of members, adjoint for the pairings, such that
  `A₂ → A` is zero on `Hⁱ` and `E → E₂` is zero on `H^{d-i}` (a compatible coeffacement).

The proof is descending induction on `i`, the inductive step being
`HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃_of_homologyMap_g_eq_zero`; the sequence
`Hom^•_ℤ(E₁, T) → Hom^•_ℤ(E₂, T) → Hom^•_ℤ(E, T)` is short exact because every term of `T` is an
injective abelian group (`Stacks.ContinuousCohomology.shortExact_internalHomComplexPrecomp`).

This is the shape of the derived Poincaré duality of Tag 03VM: `A = RΓ_c(X_k̄, ℱ_M)`,
`E = RHom(ℱ_M, μ_n)`, the family is indexed by finite modules `M` (with resolutions), and the
coeffacements come from the left derived functor property of `H_c^{2-i}` and the right derived
functor property of `Ext^i(ℱ_-, μ_n)`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex Stacks.GroupHomology

universe v w

namespace Stacks.ContinuousCohomology

open InternalHomCochain

section ShortExact

variable (R : Type) [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q]

/-- The short complex `Hom^•(X₃, G) → Hom^•(X₂, G) → Hom^•(X₁, G)` of precompositions. -/
def internalHomComplexPrecompShortComplex
    (S : ShortComplex (CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} R Q) ℤ))
    (G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{w} (CompletedGroupAlgebra Rᵐᵒᵖ Q)) ℤ) :=
  ShortComplex.mk (internalHomComplexPrecomp R S.X₃ G S.g)
    (internalHomComplexPrecomp R S.X₂ G S.f) (by
      refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext <|
        LinearMap.ext fun z => ?_
      apply InternalHomCochain.ext
      refine Cochain.ext _ _ fun p q hpq => ?_
      change ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map S.f)).comp
        ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map S.g)).comp
          (toCochain z) (zero_add n)) (zero_add n)).v p q hpq = 0
      rw [Cochain.zero_cochain_comp_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
        Cochain.ofHom_v, ← Category.assoc, ← HomologicalComplex.comp_f,
        ← CategoryTheory.Functor.map_comp, S.zero, Functor.map_zero,
        HomologicalComplex.zero_f, zero_comp])

/-- **`Hom^•_ℤ(-, G)` is exact** on short exact sequences when every term of `G` is an injective
abelian group: `0 → Hom^•(X₃, G) → Hom^•(X₂, G) → Hom^•(X₁, G) → 0` is short exact. -/
theorem shortExact_internalHomComplexPrecomp
    {S : ShortComplex (CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} R Q) ℤ)}
    (hS : S.ShortExact) (G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, w} ℤ Q) ℤ)
    [∀ q, Injective ((underlyingAb ℤ G).X q)] :
    (internalHomComplexPrecompShortComplex R S G).ShortExact := by
  have hp : ∀ p, ((S.map (HomologicalComplex.eval _ _ p)).map (forgetAb R Q)).ShortExact :=
    fun p => (hS.map_of_exact (HomologicalComplex.eval _ _ p)).map_of_exact (forgetAb R Q)
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  have := fun p => (hp p).mono_f
  have := fun p => (hp p).epi_g
  have hmono : ∀ p, Mono ((forgetAb R Q).map (S.f.f p)) := fun p => (hp p).mono_f
  have hepi : ∀ p, Epi ((forgetAb R Q).map (S.g.f p)) := fun p => (hp p).epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    have hz' : ∀ p q (hpq : p + n = q),
        (forgetAb R Q).map (S.f.f p) ≫ (toCochain (R := R) (V := S.X₂) (W := G) z).v p q hpq =
          0 := by
      intro p q hpq
      have := Cochain.congr_v (congrArg (toCochain (R := R) (V := S.X₁) (W := G)) hz) p q hpq
      change ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map S.f)).comp
        (toCochain (R := R) (V := S.X₂) (W := G) z) (zero_add n)).v p q hpq =
          (0 : Cochain _ _ n).v p q hpq at this
      rwa [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at this
    refine ⟨of (Cochain.mk fun p q hpq => (hp p).exact.desc _ (hz' p q hpq)), ?_⟩
    apply InternalHomCochain.ext
    refine Cochain.ext _ _ fun p q hpq => ?_
    show ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map S.g)).comp
      (Cochain.mk fun p q hpq => (hp p).exact.desc _ (hz' p q hpq)) (zero_add n)).v p q hpq = _
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
    exact (hp p).exact.g_desc _ (hz' p q hpq)
  · rw [ModuleCat.mono_iff_injective]
    intro z z' h
    apply InternalHomCochain.ext
    refine Cochain.ext _ _ fun p q hpq => ?_
    have := Cochain.congr_v (congrArg (toCochain (R := R) (V := S.X₂) (W := G)) h) p q hpq
    change ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map S.g)).comp
        (toCochain (R := R) (V := S.X₃) (W := G) z) (zero_add n)).v p q hpq =
      ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map S.g)).comp
        (toCochain (R := R) (V := S.X₃) (W := G) z') (zero_add n)).v p q hpq at this
    rw [Cochain.zero_cochain_comp_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at this
    exact (cancel_epi ((forgetAb R Q).map (S.g.f p))).1 this
  · rw [ModuleCat.epi_iff_surjective]
    intro z
    refine ⟨of (Cochain.mk fun p q hpq => Injective.factorThru
      ((toCochain (R := R) (V := S.X₁) (W := G) z).v p q hpq) ((forgetAb R Q).map (S.f.f p))), ?_⟩
    apply InternalHomCochain.ext
    refine Cochain.ext _ _ fun p q hpq => ?_
    show ((Cochain.ofHom (((forgetAb R Q).mapHomologicalComplex _).map S.f)).comp
      (Cochain.mk fun p q hpq => Injective.factorThru
        ((toCochain (R := R) (V := S.X₁) (W := G) z).v p q hpq)
          ((forgetAb R Q).map (S.f.f p))) (zero_add n)).v p q hpq = _
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
    exact Injective.comp_factorThru (f := (forgetAb R Q).map (S.f.f p)) _

end ShortExact

section Induction

attribute [local instance] HasDerivedCategory.standard

variable {R : Type} [Ring R] [Finite R] {Q : Type v} [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [CompactSpace Q] {S : Type} [Ring S] {φ : S →+* Rᵐᵒᵖ} {d : ℤ}

/-- An exact functor carries a morphism that is zero on `Hᵐ` to a morphism that is zero on `Hᵐ`. -/
lemma homologyMap_discreteToCompletedGroupAlgebra_map_eq_zero
    {A₁ A₂ : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} S Q) ℤ}
    (f : A₁ ⟶ A₂) (m : ℤ) (hf : HomologicalComplex.homologyMap f m = 0) :
    HomologicalComplex.homologyMap
      (((discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapHomologicalComplex _).map f) m =
        0 := by
  have hn := ((discreteToCompletedGroupAlgebra.{0, v, max v w} S Q)
    |>.mapHomologicalComplexHomologyFunctorIso m).hom.naturality f
  change HomologicalComplex.homologyMap _ m ≫ _ = _ ≫
    (discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).map
      (HomologicalComplex.homologyMap f m) at hn
  rw [hf, Functor.map_zero] at hn
  exact (((discreteToCompletedGroupAlgebra.{0, v, max v w} S Q)
    |>.mapHomologicalComplexHomologyFunctorIso m).app A₂).eq_comp_inv.2 (hn.trans comp_zero)
    |>.trans zero_comp

/-- **Perfectness of a family of pairings by descending induction.** For a family of pairings
`P i` into `T = traceTarget Q d` such that

* `Φ_{P i}` is an isomorphism on `H^d`,
* `Hᵐ(A i) = 0` and `H^{d-m}(E i) = 0` for `m > d`, and
* for every `i` and every `m < d` there are members `i₁`, `i₂` with short exact sequences
  `0 → A i₁ → A i₂ → A i → 0` and `0 → E i → E i₂ → E i₁ → 0`, adjoint for the pairings, with
  `A i₂ → A i` zero on `Hᵐ` and `E i → E i₂` zero on `H^{d-m}`,

every chain map `Φ_{P i} : A i ⟶ Hom^•_ℤ(E i, T)` is a quasi-isomorphism. -/
theorem quasiIso_internalHomComplexOfPairing_of_coeffacement {ι : Type*}
    (A : ι → CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} S Q) ℤ)
    (E : ι → CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ)
    (P : ∀ i, ComplexPairing R φ (A i) (E i) (traceTarget.{v, w} Q d))
    (hbase : ∀ i, IsIso (HomologicalComplex.homologyMap (internalHomComplexOfPairing (P i)) d))
    (hA : ∀ i m, d < m → IsZero ((A i).homology m))
    (hE : ∀ i m, d < m → IsZero ((E i).homology (d - m)))
    (hstep : ∀ i m, m < d → ∃ (i₁ i₂ : ι) (f₁ : A i₁ ⟶ A i₂) (f₂ : A i₂ ⟶ A i)
      (g₁ : E i ⟶ E i₂) (g₂ : E i₂ ⟶ E i₁) (w₁ : f₁ ≫ f₂ = 0) (w₂ : g₁ ≫ g₂ = 0),
      (ShortComplex.mk f₁ f₂ w₁).ShortExact ∧ (ShortComplex.mk g₁ g₂ w₂).ShortExact ∧
      (∀ (n p q : ℤ) (hpq : p + n = q) (a : ((A i₁).X n).obj.obj.V) (e : ((E i₂).X p).obj.obj.V),
        (P i₂).pair n p q hpq ((f₁.f n).hom.hom.hom.hom a) e =
          (P i₁).pair n p q hpq a ((g₂.f p).hom.hom.hom.hom e)) ∧
      (∀ (n p q : ℤ) (hpq : p + n = q) (a : ((A i₂).X n).obj.obj.V) (e : ((E i).X p).obj.obj.V),
        (P i).pair n p q hpq ((f₂.f n).hom.hom.hom.hom a) e =
          (P i₂).pair n p q hpq a ((g₁.f p).hom.hom.hom.hom e)) ∧
      HomologicalComplex.homologyMap f₂ m = 0 ∧ HomologicalComplex.homologyMap g₁ (d - m) = 0)
    (i : ι) : QuasiIso (internalHomComplexOfPairing (P i)) := by
  suffices H : ∀ m i,
      IsIso (HomologicalComplex.homologyMap (internalHomComplexOfPairing (P i)) m) by
    exact ⟨fun m => (quasiIsoAt_iff_isIso_homologyMap _ m).2 (H m i)⟩
  intro m
  rcases lt_or_ge d m with hm | hm
  · intro i
    refine isIso_of_source_target_iso_zero _ ?_ ?_
    · exact (IsZero.of_iso ((discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).map_isZero
        (hA i m hm)) (((discreteToCompletedGroupAlgebra.{0, v, max v w} S Q)
          |>.mapHomologicalComplexHomologyFunctorIso m).app (A i))).isoZero
    · exact (isZero_homology_internalHomComplex_traceTarget.{v, w} R φ d (E i) m
        (hE i m hm)).isoZero
  · induction m, hm using Int.leInductionDown with
    | base => exact hbase
    | pred n hn ih =>
      intro i
      obtain ⟨i₁, i₂, f₁, f₂, g₁, g₂, w₁, w₂, hSA, hSE, h₁, h₂, hf, hg⟩ :=
        hstep i (n - 1) (by omega)
      have hS₁ : ((ShortComplex.mk f₁ f₂ w₁).map
          ((discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapHomologicalComplex
            _)).ShortExact :=
        HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k =>
          (hSA.map_of_exact (HomologicalComplex.eval _ _ k)).map_of_exact
            (discreteToCompletedGroupAlgebra.{0, v, max v w} S Q)
      have hE' := shortExact_internalHomComplexPrecomp R hSE (traceTarget.{v, w} Q d)
      have hS₂ : ((internalHomComplexPrecompShortComplex R (ShortComplex.mk g₁ g₂ w₂)
          (traceTarget.{v, w} Q d)).map
            ((pairingRestrict.{v, w} R φ).mapHomologicalComplex _)).ShortExact :=
        HomologicalComplex.shortExact_of_degreewise_shortExact _ fun k =>
          (hE'.map_of_exact (HomologicalComplex.eval _ _ k)).map_of_exact
            (pairingRestrict.{v, w} R φ)
      let ψ : (ShortComplex.mk f₁ f₂ w₁).map
          ((discreteToCompletedGroupAlgebra.{0, v, max v w} S Q).mapHomologicalComplex _) ⟶
          (internalHomComplexPrecompShortComplex R (ShortComplex.mk g₁ g₂ w₂)
            (traceTarget.{v, w} Q d)).map ((pairingRestrict.{v, w} R φ).mapHomologicalComplex _) :=
        { τ₁ := internalHomComplexOfPairing (P i₁)
          τ₂ := internalHomComplexOfPairing (P i₂)
          τ₃ := internalHomComplexOfPairing (P i)
          comm₁₂ := (internalHomComplexOfPairing_naturality (P i₁) (P i₂) f₁ g₂ h₁).symm
          comm₂₃ := (internalHomComplexOfPairing_naturality (P i₂) (P i) f₂ g₁ h₂).symm }
      have : IsIso (HomologicalComplex.homologyMap ψ.τ₁ n) := ih i₁
      have : Mono (HomologicalComplex.homologyMap ψ.τ₂ n) := by
        have := ih i₂
        exact inferInstanceAs
          (Mono (HomologicalComplex.homologyMap (internalHomComplexOfPairing (P i₂)) n))
      exact HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃_of_homologyMap_g_eq_zero
        ψ hS₁ hS₂ (n - 1) n (by simp)
        (homologyMap_discreteToCompletedGroupAlgebra_map_eq_zero f₂ (n - 1) hf)
        (homologyMap_internalHomComplexPrecomp_traceTarget_eq_zero d g₁ (n - 1) hg)

end Induction

end Stacks.ContinuousCohomology

end
