module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AffineLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.RootExtraction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.BijectiveBaseChange
public import StacksFrontier.FieldTheory.IsAlgClosed.TranscendentalTranslation

/-!
# `π₁(𝐀¹_{k'}) → π₁(𝐀¹_k)` is not an isomorphism

Let `k ⊊ k'` be algebraically closed fields of characteristic `p > 0`. The map of étale
fundamental groups `π₁(𝐀¹_{k'}) → π₁(𝐀¹_k)` induced by `𝐀¹_{k'} ⟶ 𝐀¹_k` is not bijective
([Stacks, Tag 0A47]).

If it were, finite étale base change along `𝐀¹_{k'} ⟶ 𝐀¹_k` would be essentially surjective
(`AlgebraicGeometry.essSurj_finiteEtaleBaseChange_of_bijective_etaleFundamentalGroupMap`). Take
`μ ∈ k' ∖ k` and the Artin–Schreier cover `V : y ^ p - y = μ x` of `𝐀¹_{k'}`, so that
`V ≅ U ×_k k'` for a finite étale `U ⟶ 𝐀¹_k`. A `k`-automorphism `σ` of `k'` with `σ μ = μ + 1`
(`IsAlgClosed.exists_algEquiv_apply_eq_add_one`, `μ` being transcendental) acts on `U ×_k k'` over
its action on `𝐀¹_{k'}`, hence on `V`, and so on the ring of `V`: the root `y` goes to some `z`
with `z ^ p - z = σ(μ) x`. Now the ring of `V` maps to `k'[y]` by `x ↦ (y ^ p - y) / μ`, and there
`z ^ p - z = (σ(μ) / μ)(y ^ p - y)` forces `σ(μ) / μ ∈ 𝐅_p`
(`Polynomial.pow_eq_self_of_ringArtinSchreier_eq_C_mul`), so `1 / μ ∈ 𝐅_p` and `μ ∈ k`.

## Main results

* `Stacks.ArtinSchreier.not_bijective_etaleFundamentalGroupMap_affineLine`.

## References

* [Stacks Project, Tag 0A47](https://stacks.math.columbia.edu/tag/0A47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Stacks.EtaleCohomology

universe u

namespace Stacks.ArtinSchreier

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k']

/-- `𝐀¹_k ×_k k'` is connected, being integral: `𝐀¹_k` is geometrically integral over the
algebraically closed field `k`. -/
instance [IsAlgClosed k] : ConnectedSpace (scalarExtension k k' (affineLineStructure k)) :=
  have := isIntegral_scalarExtension k k' (affineLineStructure k)
  inferInstance

/-! ### The Artin–Schreier cover of an affine scheme -/

section Cover

variable {T : Scheme.{u}} [IsAffine T] {p : ℕ} (hp : 1 < p) (hT : (p : Γ(T, ⊤)) = 0) (a : Γ(T, ⊤))

/-- The ring `Γ(T)[y]/(y ^ p - y - a)` of the Artin–Schreier cover attached to a function `a`. -/
abbrev artinSchreierCoverRing (p : ℕ) (a : Γ(T, ⊤)) : Type u :=
  AdjoinRoot (Polynomial.X ^ p - Polynomial.X - C a)

/-- **The Artin–Schreier cover `y ^ p - y = a`** of an affine scheme `T` of characteristic `p`,
as a finite étale cover: `Spec Γ(T)[y]/(y ^ p - y - a) ⟶ Spec Γ(T) ≅ T`. -/
@[sga "1 X 1.10" "partial"]
def artinSchreierCover : FiniteEtaleOver T :=
  have := finite_adjoinRootAS a hp
  have := etale_adjoinRootAS a hp hT
  MorphismProperty.Over.mk ⊤
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (artinSchreierCoverRing p a))) ≫
      T.isoSpec.inv)
    ⟨by
      have : IsFinite (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(T, ⊤) (artinSchreierCoverRing p a)))) := by
        rw [IsFinite.SpecMap_iff]
        exact RingHom.finite_algebraMap.mpr inferInstance
      infer_instance, by
      have : Etale (Spec.map (CommRingCat.ofHom
          (algebraMap Γ(T, ⊤) (artinSchreierCoverRing p a)))) :=
        (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
      infer_instance⟩

/-- **An endomorphism of the Artin–Schreier cover over an endomorphism `τ` of `T` acts on the
ring of the cover over `τ^*`.** -/
theorem exists_ringHom_of_comp_hom_eq (τ : T ⟶ T)
    (ψ : (artinSchreierCover hp hT a).left ⟶ (artinSchreierCover hp hT a).left)
    (hψ : ψ ≫ (artinSchreierCover hp hT a).hom = (artinSchreierCover hp hT a).hom ≫ τ) :
    ∃ ψ' : artinSchreierCoverRing p a →+* artinSchreierCoverRing p a,
      ∀ s, ψ' (algebraMap Γ(T, ⊤) _ s) = algebraMap Γ(T, ⊤) _ (τ.appTop.hom s) := by
  let ι := CommRingCat.ofHom (algebraMap Γ(T, ⊤) (artinSchreierCoverRing p a))
  let ψ₀ : Spec (CommRingCat.of (artinSchreierCoverRing p a)) ⟶
      Spec (CommRingCat.of (artinSchreierCoverRing p a)) := ψ
  have hψ₂ : ψ₀ ≫ Spec.map ι ≫ T.isoSpec.inv = (Spec.map ι ≫ T.isoSpec.inv) ≫ τ := hψ
  have hn : Spec.map τ.appTop = T.isoSpec.inv ≫ τ ≫ T.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  have h : Spec.map (ι ≫ Spec.preimage ψ₀) = Spec.map (τ.appTop ≫ ι) := by
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, hn]
    calc ψ₀ ≫ Spec.map ι = (ψ₀ ≫ Spec.map ι ≫ T.isoSpec.inv) ≫ T.isoSpec.hom := by simp
      _ = Spec.map ι ≫ T.isoSpec.inv ≫ τ ≫ T.isoSpec.hom := by rw [hψ₂]; simp
  exact ⟨(Spec.preimage ψ₀).hom, fun s => congrArg (fun φ => φ.hom s) (Spec.map_injective h)⟩

end Cover

/-! ### An automorphism of the ground field acting on `𝐀¹_k ×_k k'` -/

section Translation

variable {k k'} (σ : k' →ₐ[k] k')

/-- The endomorphism of `𝐀¹_k ×_k k'` induced by a `k`-algebra endomorphism `σ` of `k'` on the
second factor. -/
def scalarExtensionAffineLineMap :
    scalarExtension k k' (affineLineStructure k) ⟶ scalarExtension k k' (affineLineStructure k) :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ.toRingHom)) (𝟙 _) (by simp) (by
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    ext c
    exact (σ.commutes c).symm)

/-- The endomorphism lies over the identity of `𝐀¹_k`. -/
theorem scalarExtensionAffineLineMap_fst :
    scalarExtensionAffineLineMap σ ≫ scalarExtensionFst k k' (affineLineStructure k) =
      scalarExtensionFst k k' (affineLineStructure k) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The endomorphism lies over `Spec σ`. -/
theorem scalarExtensionAffineLineMap_snd :
    scalarExtensionAffineLineMap σ ≫ scalarExtensionSnd k k' (affineLineStructure k) =
      scalarExtensionSnd k k' (affineLineStructure k) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  pullback.lift_snd _ _ _

/-- **On `Γ(𝐀¹_k ×_k k') ≅ k'[x]` the endomorphism acts by `σ` on the coefficients.** -/
theorem scalarExtensionAffineLineEquiv_appTop_scalarExtensionAffineLineMap
    (s : Γ(scalarExtension k k' (affineLineStructure k), ⊤)) :
    scalarExtensionAffineLineEquiv k k' ((scalarExtensionAffineLineMap σ).appTop.hom s) =
      (scalarExtensionAffineLineEquiv k k' s).map σ.toRingHom := by
  let fst := scalarExtensionFst k k' (affineLineStructure k)
  let snd := scalarExtensionSnd k k' (affineLineStructure k)
  let τ := scalarExtensionAffineLineMap σ
  have hfst : ∀ t : k[X], τ.appTop.hom (((Scheme.ΓSpecIso (.of k[X])).inv ≫ fst.appTop).hom t) =
      ((Scheme.ΓSpecIso (.of k[X])).inv ≫ fst.appTop).hom t := fun t =>
    congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of k[X])).inv.hom t))
      ((Scheme.Hom.comp_appTop _ _).symm.trans
        (congrArg Scheme.Hom.appTop (scalarExtensionAffineLineMap_fst σ)))
  have hsnd : ∀ c : k', τ.appTop.hom (((Scheme.ΓSpecIso (.of k')).inv ≫ snd.appTop).hom c) =
      ((Scheme.ΓSpecIso (.of k')).inv ≫ snd.appTop).hom (σ c) := fun c => by
    have key : (Scheme.ΓSpecIso (.of k')).inv ≫ snd.appTop ≫ τ.appTop =
        CommRingCat.ofHom σ.toRingHom ≫ (Scheme.ΓSpecIso (.of k')).inv ≫ snd.appTop := by
      rw [← Scheme.Hom.comp_appTop, scalarExtensionAffineLineMap_snd, Scheme.Hom.comp_appTop,
        ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    exact congrArg (fun φ => φ.hom c) key
  obtain ⟨n, b, c, rfl⟩ := exists_sum_of_isPushout (isPushout_scalarExtension_affineLine k k') s
  simp only [map_sum, map_mul, Polynomial.map_sum, Polynomial.map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have he₁ : ∀ f : k[X], scalarExtensionAffineLineEquiv k k'
      (((Scheme.ΓSpecIso (.of k[X])).inv ≫ fst.appTop).hom f) = f.map (algebraMap k k') :=
    scalarExtensionAffineLineEquiv_fst k k'
  have he₂ : ∀ c : k', scalarExtensionAffineLineEquiv k k'
      (((Scheme.ΓSpecIso (.of k')).inv ≫ snd.appTop).hom c) = C c :=
    scalarExtensionAffineLineEquiv_snd k k'
  rw [hfst, hsnd, he₁, he₂, he₂, Polynomial.map_C, Polynomial.map_map]
  congr 2
  ext x
  exact (σ.commutes x).symm

end Translation

/-! ### The fundamental group -/

/-- **A ring endomorphism of the ring of the Artin–Schreier cover `y ^ p - y = μ x` of
`𝐀¹_k ×_k k'` over the action of `σ`, with `σ μ = μ + 1` and `μ ≠ 0`, forces `μ ∈ k`.** -/
theorem mem_range_algebraMap_of_ringHom_artinSchreierCoverRing {p : ℕ} [hp : Fact p.Prime]
    [CharP k' p] {σ : k' ≃ₐ[k] k'} {μ : k'} (hμ0 : μ ≠ 0) (hσ : σ μ = μ + 1)
    {a : Γ(scalarExtension k k' (affineLineStructure k), ⊤)}
    (ha : a = (scalarExtensionAffineLineEquiv k k').symm (C μ * Polynomial.X))
    (ψ' : artinSchreierCoverRing p a →+* artinSchreierCoverRing p a)
    (hψ' : ∀ s : Γ(scalarExtension k k' (affineLineStructure k), ⊤),
      ψ' (algebraMap _ (artinSchreierCoverRing p a) s) =
        algebraMap _ (artinSchreierCoverRing p a)
          ((scalarExtensionAffineLineMap σ.toAlgHom).appTop.hom s)) :
    μ ∈ Set.range (algebraMap k k') := by
  let e := scalarExtensionAffineLineEquiv k k'
  let τ := scalarExtensionAffineLineMap σ.toAlgHom
  -- the image `z` of the root satisfies `z ^ p - z = σ(μ) x`
  let r := AdjoinRoot.root (Polynomial.X ^ p - Polynomial.X - C a)
  have hz : ψ' r ^ p - ψ' r = algebraMap _ (artinSchreierCoverRing p a) (τ.appTop.hom a) := by
    rw [← map_pow, ← map_sub, root_pow_sub_root, hψ']
  have he : e (τ.appTop.hom a) = C (σ μ) * Polynomial.X := by
    rw [scalarExtensionAffineLineEquiv_appTop_scalarExtensionAffineLineMap, ha,
      RingEquiv.apply_symm_apply, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    rfl
  -- the ring of `V` maps to `k'[y]`, `x ↦ (y ^ p - y) / μ`, `root ↦ y`
  let q : k'[X] := C μ⁻¹ * (Polynomial.X ^ p - Polynomial.X)
  let φ : Γ(scalarExtension k k' (affineLineStructure k), ⊤) →+* k'[X] :=
    (Polynomial.eval₂RingHom C q).comp e.toRingHom
  have hφ : ∀ c : k', φ (e.symm (C c * Polynomial.X)) =
      C (c * μ⁻¹) * (Polynomial.X ^ p - Polynomial.X) :=
    fun c => by
      simp only [φ, q, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X, C_mul, mul_assoc]
  have hφa : φ a = Polynomial.X ^ p - Polynomial.X := by
    rw [ha, hφ, mul_inv_cancel₀ hμ0, C_1, one_mul]
  let j : artinSchreierCoverRing p a →+* k'[X] := AdjoinRoot.lift φ Polynomial.X (by
    rw [eval₂_sub, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hφa, sub_self])
  have hw : j (ψ' r) ^ p - j (ψ' r) = C (σ μ * μ⁻¹) * (Polynomial.X ^ p - Polynomial.X) := by
    rw [← map_pow, ← map_sub, hz, AdjoinRoot.algebraMap_eq, AdjoinRoot.lift_of,
      ← hφ, ← he, RingEquiv.symm_apply_apply]
  -- so `σ(μ) / μ ∈ 𝐅_p`, and then `μ ∈ k`
  obtain ⟨i, -, hi⟩ := exists_castHom_eq_of_pow_eq hp.out (CharP.cast_eq_zero k' p) _
    (pow_eq_self_of_ringArtinSchreier_eq_C_mul _ _ hw)
  refine ⟨((i : k) - 1)⁻¹, ?_⟩
  rw [map_inv₀, map_sub, map_natCast, map_one, ← hi, hσ, add_mul, mul_inv_cancel₀ hμ0,
    one_mul, add_sub_cancel_left, inv_inv]

/-- **[Stacks, Tag 0A47]: `π₁(𝐀¹_{k'}) → π₁(𝐀¹_k)` is not an isomorphism.** Let `k'/k` be an
extension of algebraically closed fields of characteristic `p > 0` with `k' ≠ k`. Then for every
geometric point `x` of `𝐀¹_{k'}` the map of étale fundamental groups
`π₁(𝐀¹_{k'}, x) → π₁(𝐀¹_k, x)` induced by `𝐀¹_{k'} ⟶ 𝐀¹_k` is not bijective. -/
@[stacks 0A47 "π₁(A¹_{k'}) → π₁(A¹_k) is not an isomorphism for algebraically closed k ⊊ k'",
  sga "1 IX 6.3" "more general",
  sga "1 X 1.10" "partial",
  sga "1 XIII 2.13" "partial"]
theorem not_bijective_etaleFundamentalGroupMap_affineLine {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    [IsAlgClosed k] [IsAlgClosed k'] (hk : ¬ Function.Surjective (algebraMap k k'))
    (x : GeometricPoint (scalarExtension k k' (affineLineStructure k))) :
    ¬ Function.Bijective
      (etaleFundamentalGroupMap (scalarExtensionFst k k' (affineLineStructure k)) x) := by
  intro hbij
  have : CharP k' p := charP_of_injective_algebraMap' k p
  let g := scalarExtensionFst k k' (affineLineStructure k)
  let e := scalarExtensionAffineLineEquiv k k'
  obtain ⟨μ, hμ⟩ : ∃ μ : k', μ ∉ Set.range (algebraMap k k') := not_forall.mp hk
  have hμ0 : μ ≠ 0 := fun h => hμ ⟨0, by rw [h, map_zero]⟩
  have hμt : Transcendental k μ := fun halg => hμ (minpoly.natDegree_eq_one_iff.mp
    (natDegree_eq_of_degree_eq_some (IsAlgClosed.degree_eq_one_of_irreducible k
      (minpoly.irreducible halg.isIntegral))))
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_algEquiv_apply_eq_add_one hμt
  have hX' : (p : Γ(scalarExtension k k' (affineLineStructure k), ⊤)) = 0 :=
    natCast_eq_zero_of_hom g natCast_eq_zero_affineLine
  let a := e.symm (C μ * Polynomial.X)
  let V := artinSchreierCover hp.out.one_lt hX' a
  obtain ⟨U, ⟨α⟩⟩ :=
    (essSurj_finiteEtaleBaseChange_of_bijective_etaleFundamentalGroupMap g x hbij).mem_essImage V
  -- the action of `σ` on `U ×_k k'`, transported to `V`
  let τ := scalarExtensionAffineLineMap σ.toAlgHom
  let τU : pullback U.hom g ⟶ pullback U.hom g := pullback.map U.hom g U.hom g (𝟙 _) τ (𝟙 _)
    (by simp) (by rw [Category.comp_id, scalarExtensionAffineLineMap_fst])
  have hτU : τU ≫ pullback.snd U.hom g = pullback.snd U.hom g ≫ τ := pullback.lift_snd _ _ _
  let αh : pullback U.hom g ⟶ V.left := α.hom.left
  let αi : V.left ⟶ pullback U.hom g := α.inv.left
  have h₁ : αh ≫ V.hom = pullback.snd U.hom g := MorphismProperty.Over.w α.hom
  have h₂ : αi ≫ pullback.snd U.hom g = V.hom := MorphismProperty.Over.w α.inv
  let ψ : V.left ⟶ V.left := αi ≫ τU ≫ αh
  have hψ : ψ ≫ V.hom = V.hom ≫ τ := by
    calc ψ ≫ V.hom = αi ≫ τU ≫ αh ≫ V.hom := by simp only [ψ, Category.assoc]
      _ = V.hom ≫ τ := by rw [h₁, hτU, ← Category.assoc, h₂]
  obtain ⟨ψ', hψ'⟩ := exists_ringHom_of_comp_hom_eq hp.out.one_lt hX' a τ ψ hψ
  exact hμ (mem_range_algebraMap_of_ringHom_artinSchreierCoverRing k k' hμ0 hσ rfl ψ' hψ')

omit [Field k'] [Algebra k k'] in
/-- **[Stacks, Tag 0A47]: the étale fundamental group of the affine line depends on the
algebraically closed ground field.** For every algebraically closed field `k` of characteristic
`p > 0` there is an algebraically closed extension `k'/k` — an algebraic closure of `k(t)` — for
which `π₁(𝐀¹_{k'}, x) → π₁(𝐀¹_k, x)` is not bijective at any geometric point `x`.

The source concludes that the étale homotopy type of the affine line depends on the algebraically
closed ground field; the étale homotopy type is not available here, and this statement, with
`Stacks.ArtinSchreier.exists_not_bijective_etaleCohomologyRestrictionMap_affineLine` for `H¹`, is
the content of that conclusion for the invariants `π₁` and `H¹` of the homotopy type. -/
@[stacks 0A47 "so the étale fundamental group of A¹ depends on the algebraically closed field",
  sga "1 IX 6.3",
  sga "1 X 1.10" "partial"]
theorem exists_not_bijective_etaleFundamentalGroupMap_affineLine {p : ℕ} [Fact p.Prime]
    [CharP k p] [IsAlgClosed k] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : IsAlgClosed k'),
      ∀ x : GeometricPoint (scalarExtension k k' (affineLineStructure k)),
        ¬ Function.Bijective
          (etaleFundamentalGroupMap (scalarExtensionFst k k' (affineLineStructure k)) x) :=
  ⟨AlgebraicClosure (RatFunc k), inferInstance, inferInstance, inferInstance,
    not_bijective_etaleFundamentalGroupMap_affineLine k (AlgebraicClosure (RatFunc k)) (p := p)
      (not_surjective_algebraMap_algebraicClosure_ratFunc k)⟩

end Stacks.ArtinSchreier

end
