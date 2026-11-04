module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTwistModelFinite

/-!
# The bad points of the Fourier twist: finitely many over one field, stable under extension

For `s : T ⟶ 𝔸¹_k` (the `t`-line) say that `s` is *bad* when the twisted sheaf
`t⁻¹ M ⊗ L_ψ(x s)` on `C_s` (`Stacks.EtaleCohomology.fourierTwistSheaf`) has a constant simple
quotient. Two facts on bad points enter the Artin–Schreier half of the generic coinvariant
vanishing in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH):

* **badness goes up along surjections**
  (`Stacks.EtaleCohomology.not_hasNoConstantSimpleQuotient_comp`): for a surjective `d : T' ⟶ T`,
  the canonical `C_{d ≫ s} ⟶ C_s` is surjective (a base change of `d`), it pulls the twisted sheaf
  back to the twisted sheaf, and inverse image along a surjection keeps morphisms nonzero. In
  particular badness at a field passes to every extension field;
* **over one field `K` below the cutoff, only finitely many `K`-points `t ↦ σ` are bad**
  (`Stacks.EtaleCohomology.finite_setOf_not_hasNoConstantSimpleQuotient`): all the `C_{s_σ}` are
  the one model `Spec Γ(𝔸¹_K ×_{𝔸¹_k} V)`, a simple module over the finite ring `Λ` is `Λ/𝔪` for
  one of finitely many maximal ideals `𝔪`, and for each `𝔪` only finitely many `σ` give a nonzero
  morphism to the constant sheaf on `Λ/𝔪`
  (`Stacks.EtaleCohomology.finite_setOf_ne_zero_fourierTwistModel`).

## Main results

* `Stacks.EtaleCohomology.not_hasNoConstantSimpleQuotient_comp`.
* `Stacks.EtaleCohomology.finite_setOf_not_hasNoConstantSimpleQuotient`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier
  Polynomial

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal hasSheafify_etaleModules_fourierKernel

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- A map between two pullbacks of `f`, covering a surjection `h` on the other leg, is
surjective. -/
private theorem surjective_of_isPullback_comp {P P' X Y Y' Z : Scheme.{u}} {f : X ⟶ Z}
    {g : Y ⟶ Z} {h : Y' ⟶ Y} [Surjective h] {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {p₁' : P' ⟶ X}
    {p₂' : P' ⟶ Y'} (hP : IsPullback p₁ p₂ f g) (hP' : IsPullback p₁' p₂' f (h ≫ g))
    {m : P' ⟶ P} (h₁ : m ≫ p₁ = p₁') (h₂ : m ≫ p₂ = p₂' ≫ h) : Surjective m := by
  have : IsPullback m p₂' p₂ h := IsPullback.of_right (h₁.symm ▸ hP') h₂ hP
  exact MorphismProperty.of_isPullback (P := @Surjective) this.flip inferInstance

/-- **Badness goes up along surjections**: if `t⁻¹ M ⊗ L_ψ(x s)` on `C_s` has a constant simple
quotient, so has `t⁻¹ M ⊗ L_ψ(x (d ≫ s))` on `C_{d ≫ s}`, for `d : T' ⟶ T` surjective. -/
theorem not_hasNoConstantSimpleQuotient_comp {V : Scheme.{u}} (jV : V ⟶ Spec (.of k[X]))
    (M : EtaleModules.{u, 0} Λ V) {T T' : Scheme.{u}} (s : T ⟶ Spec (.of k[X])) (d : T' ⟶ T)
    [Surjective d] (h : ¬ HasNoConstantSimpleQuotient Λ (fourierTwistSheaf k Λ ψ B p₀ jV M s)) :
    ¬ HasNoConstantSimpleQuotient Λ (fourierTwistSheaf k Λ ψ B p₀ jV M (d ≫ s)) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let u := pullback.fst pr₂ s
  let u₂ := pullback.fst pr₂ (d ≫ s)
  let dX : pullback pr₂ (d ≫ s) ⟶ pullback pr₂ s :=
    pullback.map pr₂ (d ≫ s) pr₂ s (𝟙 _) d (𝟙 _) (by simp) (by simp)
  have hdu : dX ≫ u = u₂ := by simp [dX, u, u₂]
  have : Surjective dX :=
    surjective_of_isPullback_comp (IsPullback.of_hasPullback pr₂ s)
      (IsPullback.of_hasPullback pr₂ (d ≫ s)) hdu (pullback.lift_snd _ _ _)
  let w := u ≫ pr₁
  let w₂ := u₂ ≫ pr₁
  have hw : dX ≫ w = w₂ := by rw [← Category.assoc, hdu]
  let c : pullback w₂ jV ⟶ pullback w jV :=
    pullback.map w₂ jV w jV dX (𝟙 V) (𝟙 _) (by rw [Category.comp_id, hw]) (by simp)
  have hcs : c ≫ pullback.snd w jV = pullback.snd w₂ jV := by simp [c]
  have hcf : c ≫ pullback.fst w jV = pullback.fst w₂ jV ≫ dX := pullback.lift_fst _ _ _
  have : Surjective c :=
    surjective_of_isPullback_comp (h := dX) (IsPullback.of_hasPullback w jV).flip
      (by rw [hw]; exact (IsPullback.of_hasPullback w₂ jV).flip) hcs hcf
  have hcu : c ≫ pullback.fst w jV ≫ u = pullback.fst w₂ jV ≫ u₂ := by
    rw [reassoc_of% hcf, hdu]
  unfold HasNoConstantSimpleQuotient at h ⊢
  push Not at h ⊢
  obtain ⟨E, hE, φ, hφ⟩ := h
  refine ⟨E, hE, ?_⟩
  let I := etaleModuleInverseImage.{u, 0} Λ c
  let L := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  let a₁ : I.obj ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd w jV)).obj M) ≅
      (etaleModuleInverseImage.{u, 0} Λ (pullback.snd w₂ jV)).obj M :=
    ((etaleModuleInverseImageCompIso Λ c (pullback.snd w jV)).app M).symm ≪≫
      eqToIso (by rw [hcs])
  let a₂ : I.obj ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst w jV ≫ u)).obj L) ≅
      (etaleModuleInverseImage.{u, 0} Λ (pullback.fst w₂ jV ≫ u₂)).obj L :=
    ((etaleModuleInverseImageCompIso Λ c (pullback.fst w jV ≫ u)).app L).symm ≪≫
      eqToIso (by rw [hcu])
  let a := (Functor.Monoidal.μIso I _ _).symm ≪≫ (a₁ ⊗ᵢ a₂)
  let b := (etaleModuleInverseImageConstantIso Λ c).app E
  refine ⟨a.inv ≫ I.map φ ≫ b.hom, fun h0 => hφ
    (eq_zero_of_etaleModuleInverseImage_map_eq_zero_of_surjective Λ c φ ?_)⟩
  exact zero_of_epi_comp a.inv (zero_of_comp_mono b.hom h0)

/-- **Over one field below the cutoff only finitely many points are bad**: for a field `K` over
`k` of cardinality below the cutoff, a nonempty open `V ⊆ 𝔸¹_k` and `M` locally constant with
finite values on `V`, only finitely many `σ ∈ K` have `t⁻¹ M ⊗ L_ψ(x σ)` on `C_{s_σ}` with a
constant simple quotient, `s_σ : t ↦ σ` the `K`-point of the `t`-line. -/
theorem finite_setOf_not_hasNoConstantSimpleQuotient (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) {V : Scheme.{u}} (jV : V ⟶ Spec (.of k[X]))
    [IsOpenImmersion jV] [Nonempty V] (M : EtaleModules.{u, 0} Λ V)
    (hM : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) M)
    (K : Type u) [Field K] [Algebra k K] (hK : schemeSizeBelow B.cutoff (Spec (.of K))) :
    {σ : K | ¬ HasNoConstantSimpleQuotient Λ (fourierTwistSheaf k Λ ψ B p₀ jV M
      (Spec.map (CommRingCat.ofHom (eval₂RingHom (algebraMap k K) σ))))}.Finite := by
  have := isAffine_fourierTwistModel k K jV
  let Ec : Ideal Λ → ModuleCat.{u + 1} Λ := fun I => ModuleCat.of Λ (ULift.{u + 1} (Λ ⧸ I))
  have : Finite (Ideal Λ) :=
    Finite.of_injective (fun I : Ideal Λ => (I : Set Λ)) SetLike.coe_injective
  let S : {I : Ideal Λ // I.IsMaximal} → Set K := fun I =>
    {σ : K | ∃ φ : (etaleModuleInverseImage.{u, 0} Λ
          ((pullback (fourierTwistModelMap k K) jV).isoSpec.inv ≫
            pullback.snd (fourierTwistModelMap k K) jV)).obj M ⊗
          fourierTwistModelSheaf k K jV Λ ψ B p₀ σ ⟶
          etaleModuleConstantSheaf Λ (Ec I.1)
            (Spec Γ(pullback (fourierTwistModelMap k K) jV, ⊤)), φ ≠ 0}
  have hS : ∀ I, (S I).Finite := fun I => by
    have : IsSimpleModule Λ (Ec I.1) :=
      isSimpleModule_iff_quot_maximal.2 ⟨I.1, I.2, ⟨ULift.moduleEquiv⟩⟩
    have : Finite (Λ ⧸ I.1) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    have : Finite (Ec I.1) := inferInstanceAs (Finite (ULift.{u + 1} (Λ ⧸ I.1)))
    exact finite_setOf_ne_zero_fourierTwistModel k K jV Λ ψ B p₀ hψ hq hK M hM (Ec I.1)
  refine (Set.finite_iUnion hS).subset fun σ hσ => ?_
  obtain ⟨E, hE, φ, hφ⟩ := exists_ne_zero_fourierTwistModel k Λ ψ B p₀ K jV M σ hσ
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 hE
  let iso : E ≅ Ec I := (e.trans ULift.moduleEquiv.symm).toModuleIso
  let G := constantSheaf (Spec Γ(pullback (fourierTwistModelMap k K) jV, ⊤)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)
  refine Set.mem_iUnion.2 ⟨⟨I, hI⟩, φ ≫ G.map iso.hom, fun h0 => hφ ?_⟩
  exact zero_of_comp_mono (G.map iso.hom) h0

end Stacks.EtaleCohomology

end
