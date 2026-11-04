module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantFibreSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ArtinSchreierCoverOpenImmersion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.InverseImageSurjectiveNonzero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTripleCoordinates

/-!
# One model for the fibres `C_s` of the Fourier twist

Let `k` be a finite field, `V ⊆ 𝔸¹_k` an open, `M` a sheaf on `V`, and for a morphism
`s : T ⟶ 𝔸¹_k` (the `t`-line) let `C_s = X_s ×_{𝔸¹_k} V` be the open over `V` of the fibre `X_s`
of `pr₂ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹`, carrying `t⁻¹ M ⊗ L_ψ(x s)`
(`Stacks.EtaleCohomology.fourierTwistSheaf`), as in the Artin–Schreier half
`Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput`.

For a field `K` over `k` and the `K`-point `s_σ : t ↦ σ` of the `t`-line, the fibre `X_{s_σ}` is
`𝔸¹_K = Spec K[x]` (`Stacks.EtaleCohomology.isPullback_fourierTwistModel`), so that `C_{s_σ}` is
isomorphic to the one affine scheme `Y = Spec Γ(𝔸¹_K ×_{𝔸¹_k} V)`, independent of `σ`, through an
isomorphism carrying `t` to the projection `Y ⟶ V` and `μ ∘ (x, s_σ)` to the morphism
`Y ⟶ 𝔸¹_k`, `x ↦ σ x` (`Stacks.EtaleCohomology.exists_isIso_fourierTwistModel`). Hence a constant
simple quotient of the twisted sheaf on `C_{s_σ}` gives one of `p⁻¹ M ⊗ L_ψ(σ x)` on `Y`
(`Stacks.EtaleCohomology.exists_ne_zero_fourierTwistModel`): the family of fibres over the
`K`-points of the `t`-line becomes a family of sheaves on one scheme, the setting of the
finiteness argument in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.fourierTwistSheaf`.
* `Stacks.EtaleCohomology.fourierTwistModelRingHom`: `K[x] → Γ(Y)`.

## Main results

* `Stacks.EtaleCohomology.isPullback_fourierTwistModel`.
* `Stacks.EtaleCohomology.isAffine_fourierTwistModel`.
* `Stacks.EtaleCohomology.exists_isIso_fourierTwistModel`.
* `Stacks.EtaleCohomology.exists_ne_zero_fourierTwistModel`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier
  Stacks.Blowup Polynomial

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal hasSheafify_etaleModules_fourierKernel

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **The twisted sheaf `t⁻¹ M ⊗ L_ψ(x s)` on `C_s = X_s ×_{𝔸¹_k} V`**, for `s : T ⟶ 𝔸¹_k`, `X_s`
the fibre of `pr₂ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹` over `s`: the sheaf of
`Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput`. -/
abbrev fourierTwistSheaf {V : Scheme.{u}} (jV : V ⟶ Spec (.of k[X])) (M : EtaleModules.{u, 0} Λ V)
    {T : Scheme.{u}} (s : T ⟶ Spec (.of k[X])) :
    EtaleModules.{u, 0} Λ
      (pullback (pullback.fst (pullback.snd 𝔸f 𝔸f) s ≫ pullback.fst 𝔸f 𝔸f) jV) :=
  (etaleModuleInverseImage.{u, 0} Λ
      (pullback.snd (pullback.fst (pullback.snd 𝔸f 𝔸f) s ≫ pullback.fst 𝔸f 𝔸f) jV)).obj M ⊗
    (etaleModuleInverseImage.{u, 0} Λ
      (pullback.fst (pullback.fst (pullback.snd 𝔸f 𝔸f) s ≫ pullback.fst 𝔸f 𝔸f) jV ≫
        pullback.fst (pullback.snd 𝔸f 𝔸f) s)).obj
      ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
        (affineLineArtinSchreierSheaf k Λ ψ B p₀))

section Model

variable (K : Type u) [Field K] [Algebra k K]

/-- The base change `𝔸¹_K = Spec K[x] ⟶ 𝔸¹_k` of `Spec K ⟶ Spec k`. -/
abbrev fourierTwistModelMap : Spec (.of K[X]) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (mapRingHom (algebraMap k K)))

/-- **`𝔸¹_K` is the base change of `𝔸¹_k` along `Spec K ⟶ Spec k`.** -/
theorem isPullback_fourierTwistModel :
    IsPullback (fourierTwistModelMap k K) (Spec.map (CommRingCat.ofHom (C : K →+* K[X]))) 𝔸f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  let : Algebra k[X] K[X] := Polynomial.algebra k K
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout k K k[X] K[X])).flip

variable {V : Scheme.{u}} (jV : V ⟶ Spec (.of k[X])) [IsOpenImmersion jV]

/-- **The model `𝔸¹_K ×_{𝔸¹_k} V` is affine**: `V` is an open of `𝔸¹_k`, hence affine. -/
theorem isAffine_fourierTwistModel : IsAffine (pullback (fourierTwistModelMap k K) jV) := by
  have := isAffine_of_isOpenImmersion_polynomial k jV
  have : IsAffineHom (pullback.fst (fourierTwistModelMap k K) jV) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback (fourierTwistModelMap k K) jV).flip inferInstance
  exact isAffine_of_isAffineHom (pullback.fst (fourierTwistModelMap k K) jV)

/-- The ring map `K[x] → Γ(Y)` of the open immersion `Y = 𝔸¹_K ×_{𝔸¹_k} V ⟶ 𝔸¹_K`. -/
abbrev fourierTwistModelRingHom : K[X] →+* Γ(pullback (fourierTwistModelMap k K) jV, ⊤) :=
  specHomRingHom (pullback.fst (fourierTwistModelMap k K) jV)

/-- `Spec` of `K[x] → Γ(Y)` is the open immersion `Y ⟶ 𝔸¹_K`, read on `Spec Γ(Y) ≅ Y`. -/
theorem specMap_fourierTwistModelRingHom :
    haveI := isAffine_fourierTwistModel k K jV
    Spec.map (CommRingCat.ofHom (fourierTwistModelRingHom k K jV)) =
      (pullback (fourierTwistModelMap k K) jV).isoSpec.inv ≫
        pullback.fst (fourierTwistModelMap k K) jV := by
  have := isAffine_fourierTwistModel k K jV
  rw [Iso.eq_inv_comp, Scheme.isoSpec_hom]
  exact toSpecΓ_comp_specMap_specHomRingHom _

/-- The ring map of `h ≫ μ`, for `h : Z ⟶ 𝔸¹ ×_k 𝔸¹`: `X ↦ h^* x · h^* t`. -/
theorem specHomRingHom_comp_affineLineMul {Z : Scheme.{u}} (h : Z ⟶ pullback 𝔸f 𝔸f) :
    specHomRingHom (h ≫ affineLineMul k) = eval₂RingHom
      (specHomRingHom (h ≫ pullback.fst 𝔸f 𝔸f ≫ 𝔸f))
      (specHomRingHom (h ≫ pullback.fst 𝔸f 𝔸f) Polynomial.X *
        specHomRingHom (h ≫ pullback.snd 𝔸f 𝔸f) Polynomial.X) := by
  rw [specHomRingHom_comp, specHomRingHom_affineLineMul]
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
    rw [specHomRingHom_comp_apply h, specHomRingHom_comp_apply (pullback.fst 𝔸f 𝔸f)]
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, map_mul, affineLineCoordinate]
    rw [specHomRingHom_comp_apply, specHomRingHom_comp_apply]

/-- **`μ ∘ (x, s_σ) = σ x` on `𝔸¹_K`**: for the `K`-point `s_σ : t ↦ σ` of the `t`-line and an
identification `e : X_{s_σ} ≅ 𝔸¹_K` of its fibre, the composite of `e⁻¹` with the inclusion of
the fibre and `μ` is `Spec` of `x ↦ σ x`. -/
theorem fourierTwistModel_comp_affineLineMul (σ : K) {Xs : Scheme.{u}} {u' : Xs ⟶ _}
    {f' : Xs ⟶ Spec (.of K)}
    (hu : u' ≫ pullback.snd 𝔸f 𝔸f =
      f' ≫ Spec.map (CommRingCat.ofHom (eval₂RingHom (algebraMap k K) σ)))
    (e : Xs ≅ Spec (.of K[X])) (he₁ : e.hom ≫ fourierTwistModelMap k K = u' ≫ pullback.fst 𝔸f 𝔸f)
    (he₂ : e.hom ≫ Spec.map (CommRingCat.ofHom (C : K →+* K[X])) = f') :
    e.inv ≫ u' ≫ affineLineMul k =
      Spec.map (CommRingCat.ofHom (aeval (C σ * Polynomial.X : K[X])).toRingHom) := by
  have h₁ : (e.inv ≫ u') ≫ pullback.fst 𝔸f 𝔸f = fourierTwistModelMap k K := by
    rw [Category.assoc, ← he₁, Iso.inv_hom_id_assoc]
  have h₂ : (e.inv ≫ u') ≫ pullback.snd 𝔸f 𝔸f =
      Spec.map (CommRingCat.ofHom (C : K →+* K[X])) ≫
        Spec.map (CommRingCat.ofHom (eval₂RingHom (algebraMap k K) σ)) := by
    rw [Category.assoc, hu, ← he₂, Category.assoc, Iso.inv_hom_id_assoc]
  have h₃ : (e.inv ≫ u') ≫ pullback.fst 𝔸f 𝔸f ≫ 𝔸f =
      Spec.map (CommRingCat.ofHom (algebraMap k K[X])) := by
    rw [← Category.assoc, h₁, ← Spec.map_comp]
    congr 1
    ext c
    simp
  refine hom_ext_of_specHomRingHom ?_
  rw [← Category.assoc, specHomRingHom_comp_affineLineMul, h₁, h₂, h₃, specHomRingHom_specMap,
    specHomRingHom_specMap, specHomRingHom_comp_specMap, specHomRingHom_specMap,
    specHomRingHom_specMap]
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, coe_mapRingHom, map_X,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, map_mul]
    rw [mul_comm]

/-- **A constant simple quotient on the fibre `C_{s_σ}` gives one of `p⁻¹ M ⊗ L_ψ(σ x)` on the
model `Spec Γ(Y)`**, `Y = 𝔸¹_K ×_{𝔸¹_k} V`, `p : Spec Γ(Y) ≅ Y ⟶ V`: the fibre `X_{s_σ}` is
`𝔸¹_K`, so `C_{s_σ} ≅ Y`, the projection `t` becoming `p` and `μ ∘ (x, s_σ)` becoming `x ↦ σ x`;
inverse image along this isomorphism keeps morphisms nonzero. -/
theorem exists_ne_zero_fourierTwistModel (M : EtaleModules.{u, 0} Λ V) (σ : K)
    (h : ¬ HasNoConstantSimpleQuotient Λ (fourierTwistSheaf k Λ ψ B p₀ jV M
      (Spec.map (CommRingCat.ofHom (eval₂RingHom (algebraMap k K) σ))))) :
    haveI := isAffine_fourierTwistModel k K jV
    ∃ E : ModuleCat.{u + 1} Λ, IsSimpleModule Λ E ∧
      ∃ φ : (etaleModuleInverseImage.{u, 0} Λ
          ((pullback (fourierTwistModelMap k K) jV).isoSpec.inv ≫
            pullback.snd (fourierTwistModelMap k K) jV)).obj M ⊗
          (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom
            ((fourierTwistModelRingHom k K jV).comp
              (aeval (C σ * Polynomial.X : K[X])).toRingHom)))).obj
            (affineLineArtinSchreierSheaf k Λ ψ B p₀) ⟶
          etaleModuleConstantSheaf Λ E (Spec Γ(pullback (fourierTwistModelMap k K) jV, ⊤)),
        φ ≠ 0 := by
  have := isAffine_fourierTwistModel k K jV
  let s := Spec.map (CommRingCat.ofHom (eval₂RingHom (algebraMap k K) σ))
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let u' := pullback.fst pr₂ s
  let f' := pullback.snd pr₂ s
  let w := u' ≫ pr₁
  have hsq : IsPullback w f' 𝔸f (s ≫ 𝔸f) :=
    (IsPullback.of_hasPullback pr₂ s).paste_horiz (IsPullback.of_hasPullback 𝔸f 𝔸f)
  have hs : s ≫ 𝔸f = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [← Spec.map_comp]
    congr 1
    ext c
    simp
  rw [hs] at hsq
  let e := hsq.isoIsPullback _ _ (isPullback_fourierTwistModel k K)
  have he₁ : e.hom ≫ fourierTwistModelMap k K = w := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have he₂ : e.hom ≫ Spec.map (CommRingCat.ofHom (C : K →+* K[X])) = f' :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hμ := fourierTwistModel_comp_affineLineMul k K σ (pullback.condition (f := pr₂) (g := s))
    e he₁ he₂
  let Y := pullback (fourierTwistModelMap k K) jV
  let c : Y ⟶ pullback w jV := pullback.map _ _ _ _ e.inv (𝟙 V) (𝟙 _)
    (by rw [Category.comp_id, ← he₁, Iso.inv_hom_id_assoc]) (by simp)
  let c₀ := Y.isoSpec.inv ≫ c
  have ht : c₀ ≫ pullback.snd w jV =
      Y.isoSpec.inv ≫ pullback.snd (fourierTwistModelMap k K) jV := by
    simp [c₀, c]
  have hm : c₀ ≫ (pullback.fst w jV ≫ u') ≫ affineLineMul k =
      Spec.map (CommRingCat.ofHom ((fourierTwistModelRingHom k K jV).comp
        (aeval (C σ * Polynomial.X : K[X])).toRingHom)) := by
    have h₁ : c ≫ pullback.fst w jV = pullback.fst (fourierTwistModelMap k K) jV ≫ e.inv :=
      pullback.lift_fst _ _ _
    simp only [c₀, Category.assoc]
    rw [reassoc_of% h₁, hμ, ← Category.assoc, ← specMap_fourierTwistModelRingHom k K jV,
      ← Spec.map_comp]
    rfl
  unfold HasNoConstantSimpleQuotient at h
  push Not at h
  obtain ⟨E, hE, φ, hφ⟩ := h
  refine ⟨E, hE, ?_⟩
  let I := etaleModuleInverseImage.{u, 0} Λ c₀
  let L := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  let a₁ : I.obj ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd w jV)).obj M) ≅
      (etaleModuleInverseImage.{u, 0} Λ
        (Y.isoSpec.inv ≫ pullback.snd (fourierTwistModelMap k K) jV)).obj M :=
    ((etaleModuleInverseImageCompIso Λ c₀ (pullback.snd w jV)).app M).symm ≪≫
      eqToIso (by rw [ht])
  let a₂ : I.obj ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst w jV ≫ u')).obj L) ≅
      (etaleModuleInverseImage.{u, 0} Λ (Spec.map (CommRingCat.ofHom
        ((fourierTwistModelRingHom k K jV).comp
          (aeval (C σ * Polynomial.X : K[X])).toRingHom)))).obj
        (affineLineArtinSchreierSheaf k Λ ψ B p₀) :=
    ((etaleModuleInverseImageCompIso Λ c₀ (pullback.fst w jV ≫ u')).app L).symm ≪≫
      ((etaleModuleInverseImageCompIso Λ (c₀ ≫ pullback.fst w jV ≫ u') (affineLineMul k)).app
        (affineLineArtinSchreierSheaf k Λ ψ B p₀)).symm ≪≫
      eqToIso (by rw [← hm, Category.assoc]; rfl)
  let a := (Functor.Monoidal.μIso I _ _).symm ≪≫ (a₁ ⊗ᵢ a₂)
  let b := (etaleModuleInverseImageConstantIso Λ c₀).app E
  refine ⟨a.inv ≫ I.map φ ≫ b.hom, fun h0 => hφ ?_⟩
  refine eq_zero_of_etaleModuleInverseImage_map_eq_zero_of_surjective Λ c₀ φ ?_
  calc I.map φ = a.hom ≫ (a.inv ≫ I.map φ ≫ b.hom) ≫ b.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
    _ = 0 := by rw [h0, Limits.zero_comp, Limits.comp_zero]

end Model

end Stacks.EtaleCohomology

end
