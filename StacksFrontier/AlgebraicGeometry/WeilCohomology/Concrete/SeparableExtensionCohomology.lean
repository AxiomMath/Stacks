module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilThreeAxioms
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FiniteEtaleSpec
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FirstChernClassSetup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectiveLineDegreePoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZeroSplitting
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Coproduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TraceDiagonal

/-!
# The cohomology of the spectrum of a finite separable extension, for Weil III data

Let `(D0)`, `(D1)`, `(D2')` be data as in Section 45.14 of the Stacks Project. This file proves two
statements about `H^*(Spec(K))` for finite separable field extensions `K/k`.

* **`H^*(Spec(K)) ≠ 0`**, from axioms (A3), (A4) and (A5). The point `Spec(K)` is a closed point of
  degree `n = [K : k]` of `𝐏¹_k = 𝐏(𝒪_k^{⊕ 2})`, an effective Cartier divisor `D` with
  `𝒪(D) ≅ 𝒪(n)` (`Stacks.WeilCohomology.exists_effectiveCartierDivisor_isoSpec_picardClassOf_eq`).
  If `H^*(Spec(K)) = 0` then `H^*(D) = 0`, so (A4) applied to `a = 1` gives
  `c₁^H(𝒪(D)) = n · c₁^H(𝒪(1)) = 0`. As `F` has characteristic zero, `c₁^H(𝒪(1)) = 0`,
  contradicting the projective bundle formula (A3) for `𝐏¹_k` over `Spec(k)`, since
  `H^*(Spec(k)) = F ≠ 0` by (A5).

* **Stacks 0FVS.** For finite separable extensions `k''/k'/k`, pullback
  `H^*(Spec(k')) ⟶ H^*(Spec(k''))` is injective. The source states it under the hypothesis
  `H^0(Spec(K)) ≠ 0` for a normal closure `K`; the source's proof of Tag 0FIS applies it without
  verifying that hypothesis, and the first statement supplies it. The proof is the source's:
  `Spec(k') × Spec(K) = ∐_σ Spec(K)` with coprojections `(Spec(σ), id)`, by (A1) and (A5), and
  every `σ : k' → K` extends to an automorphism of `K`.

## Main results

* `Stacks.WeilCohomology.FirstChernClassData.nontrivial_H_spec`: `H^*(Spec(K)) ≠ 0`.
* `Stacks.WeilCohomology.FirstChernClassData.injective_pull_specMap_of_nontrivial`: **Stacks
  0FVS**, with the source's hypothesis; `injective_pull_specMap_of_axioms`: without it.
* `Stacks.WeilCohomology.FirstChernClassData.injective_pull_specMap_family_of_axioms`: the same
  for a nonzero finite étale `A` and jointly injective maps to finitely many separable fields.
* `Stacks.WeilCohomology.FirstChernClassData.bijective_pull_of_isColimit_cofan`: axiom (A1) for a
  finite coproduct of schemes.

## References

* [Stacks Project, Tag 0FVS](https://stacks.math.columbia.edu/tag/0FVS)
* [Stacks Project, Tag 0FIS](https://stacks.math.columbia.edu/tag/0FIS)
* [Stacks Project, Section 45.14 (Tag 0FID)](https://stacks.math.columbia.edu/tag/0FID)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w

namespace Stacks.WeilCohomology.FirstChernClassData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] (𝔇 : FirstChernClassData k F)

/-- The free module `𝒪^{⊕ 2}` on the point `Spec(k)`. -/
abbrev pointFreeRankTwo (k : Type u) [Field k] :
    ((SmoothProjectiveScheme.toScheme k).obj (point k)).Modules :=
  Stacks.SymGraded.freeModule (X := Spec (CommRingCat.of k)) (Stacks.SymGraded.coordIndex.{u} 1)

/-- The free module `𝒪^{⊕ 2}` on the point `Spec(k)` is finite locally free of rank `2`. -/
instance (k : Type u) [Field k] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (pointFreeRankTwo k)
      (1 + 1) :=
  ProjectiveLineDegreePoint.isFiniteLocallyFreeOfRank_freeModule_coordIndex _ 1

/-- The free module `𝒪^{⊕ 2}` on the point `Spec(k)` is finite locally free. -/
instance (k : Type u) [Field k] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (pointFreeRankTwo k) :=
  ProjectiveLineDegreePoint.isFiniteLocallyFree_freeModule_coordIndex _ 1

/-- `Stacks.WeilCohomology.exists_effectiveCartierDivisor_isoSpec_picardClassOf_eq` on the
projective line `𝐏(𝒪^{⊕ 2})` over the point, as a smooth projective `k`-scheme. -/
theorem exists_divisor_bundle_point (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] :
    ∃ (D : ((SmoothProjectiveScheme.toScheme k).obj
        (SmoothProjectiveScheme.bundle (point k) (pointFreeRankTwo k) 1)).IdealSheafData)
      (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
      (e : D.subscheme ≅ Spec (CommRingCat.of K)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
          D.subschemeι ≫ (SmoothProjectiveScheme.bundle (point k) (pointFreeRankTwo k) 1).obj.hom ∧
        picardClassOf _ (Stacks.Divisors.divisorSheaf D) (haveI := hD; inferInstance) =
          (Module.finrank k K : ℤ) • picardClassOf _
            (Stacks.Chow.bundleTwist (pointFreeRankTwo k))
            (Stacks.Chow.isInvertible_bundleTwist (pointFreeRankTwo k)) := by
  dsimp only [SmoothProjectiveScheme.bundle, SmoothProjectiveScheme.mk, Functor.comp_obj,
    ObjectProperty.ι_obj, Over.forget_obj, Over.mk_left, Over.mk_hom, point]
  obtain ⟨D, hD, e, he, hpic⟩ := exists_effectiveCartierDivisor_isoSpec_picardClassOf_eq k K
  refine ⟨D, hD, e, ?_, hpic⟩
  rw [he]
  exact (Category.comp_id _).symm

/-- **`H^*(Spec(K)) ≠ 0`** for every finite separable extension `K/k`, under axioms (A3), (A4) and
(A5), the coefficient field `F` having characteristic zero. -/
theorem nontrivial_H_spec [CharZero F] (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom)
    (hA5 : 𝔇.KunnethAxiom) (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] : Nontrivial (𝔇.H (spec k K)) := by
  let E := pointFreeRankTwo k
  let P := SmoothProjectiveScheme.bundle (point k) E 1
  obtain ⟨D, hD, e, he, hpic⟩ := exists_divisor_bundle_point (k := k) K
  have := hD
  have := etale_specStructure k K
  let q := D.subschemeι ≫ P.obj.hom
  have hDK : e.hom ≫ specStructure k K = q := he
  have : Smooth q := by rw [← hDK]; infer_instance
  let Y : (SmoothProjectiveScheme k).FullSubcategory :=
    ⟨Over.mk q, (inferInstance : Smooth q),
      Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion _ _
        inferInstance P.property.2⟩
  let i : Y ⟶ P := SmoothProjectiveScheme.homMk D.subschemeι rfl
  let φ : Y ⟶ spec k K := SmoothProjectiveScheme.homMk e.hom hDK
  by_contra hK
  rw [not_nontrivial_iff_subsingleton] at hK
  have : Subsingleton (𝔇.H Y) := by
    refine subsingleton_of_zero_eq_one ?_
    rw [← map_zero (𝔇.pull φ), ← map_one (𝔇.pull φ), Subsingleton.elim (0 : 𝔇.H (spec k K)) 1]
  have h0 := congrArg (𝔇.κ P 1)
    (hA4 P Y i D hD (Iso.refl _) (by simp [i]) 1 (Subsingleton.elim _ _))
  rw [κ, tateTwistCoordinates_tateCupLeft, map_zero] at h0
  change 1 * 𝔇.κ P 1 (𝔇.c₁ P _) = 0 at h0
  have hc : 𝔇.c₁ P (picardClassOf _ (Stacks.Divisors.divisorSheaf D)
      (have := hD; inferInstance)) = (Module.finrank k K : ℤ) • 𝔇.bundleClass (point k) E 1 := by
    rw [hpic]
    exact map_zsmul (𝔇.c₁ P) _ _
  rw [one_mul, hc, map_zsmul] at h0
  change (Module.finrank k K : ℤ) • 𝔇.bundleClassU (point k) E 1 = 0 at h0
  have hn : (Module.finrank k K : ℤ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := k) (M := K)).ne'
  have hξ : 𝔇.bundleClassU (point k) E 1 = 0 := by
    rw [← Int.cast_smul_eq_zsmul F] at h0
    exact (smul_eq_zero.mp h0).resolve_left (by exact_mod_cast hn)
  have hinj := (𝔇.bijective_bundleFormulaU hA3 (point k) E 1).1
  have h01 := @hinj ![0, 1] 0 (by
    simp only [Pi.zero_apply, map_zero, mul_zero]
    simp [hξ])
  have h1 : (1 : 𝔇.H (point k)) = 0 := by simpa using congrFun h01 1
  have hne := hA5.1.1.ne (one_ne_zero (α := F))
  simp only [Algebra.linearMap_apply, map_one, map_zero] at hne
  exact hne h1

/-! ### Axiom (A1) for a finite coproduct of schemes -/

section FiniteCoproduct

/-- **Axiom (A1) for a finite coproduct**: if `Z` is the coproduct of finitely many `Yᵢ` as
schemes, `a ↦ (pᵢ^* a)ᵢ` identifies `H^*(Z)` with `∏ᵢ H^*(Yᵢ)`. -/
theorem bijective_pull_of_isColimit_cofan (hA1 : 𝔇.CoproductAxiom) {ι : Type u} [Finite ι]
    {Y : ι → (SmoothProjectiveScheme k).FullSubcategory}
        {Z : (SmoothProjectiveScheme k).FullSubcategory} (p : ∀ i, Y i ⟶ Z)
    (hc : Limits.IsColimit (Limits.Cofan.mk Z.obj.left fun i => (p i).hom.left)) :
    Function.Bijective fun a : 𝔇.H Z => fun i => 𝔇.pull (p i) a := by
  let G : ι → Scheme.{u} := fun i => (Y i).obj.left
  let φ := (Limits.colimit.isColimit (Discrete.functor G)).coconePointUniqueUpToIso hc
  have hφ : ∀ i, Limits.Sigma.ι G i ≫ φ.hom = (p i).hom.left := fun i =>
    (Limits.colimit.isColimit (Discrete.functor G)).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have hopen : ∀ i, IsOpenImmersion (SmoothProjectiveScheme.toScheme k |>.map (p i)) := by
    intro i
    show IsOpenImmersion (p i).hom.left
    rw [← hφ i]
    infer_instance
  have hrange : ∀ i, Set.range (p i).hom.left.base =
      φ.hom.base '' Set.range (Limits.Sigma.ι G i).base := by
    intro i
    rw [← hφ i]
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
  have hinj : Function.Injective φ.hom.base := φ.hom.homeomorph.injective
  have hsigma : ∀ i j, i ≠ j →
      Set.range (Limits.Sigma.ι G i).base ∩ Set.range (Limits.Sigma.ι G j).base = ∅ := by
    intro i j hij
    have h := disjoint_opensRange_sigmaι G i j hij
    rw [disjoint_iff, ← SetLike.coe_set_eq] at h
    simpa using h
  have hcover : ∀ w : (∐ G : Scheme.{u}), ∃ i, w ∈ Set.range (Limits.Sigma.ι G i).base := by
    intro w
    have hw := (sigmaOpenCover G).covers w
    refine ⟨(sigmaOpenCover G).idx w, ?_⟩
    have hf := sigmaOpenCover_f G ((sigmaOpenCover G).idx w)
    rw [hf] at hw
    exact hw
  let e := Finite.equivFin ι
  have h := 𝔇.bijective_pull_of_isOpenImmersion hA1 Z (fun j => Y (e.symm j))
    (fun j => p (e.symm j)) (fun j => hopen _)
    (fun j j' hjj' => by
      have := hopen (e.symm j)
      have := hopen (e.symm j')
      rw [Function.onFun, disjoint_iff, ← SetLike.coe_set_eq]
      simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_opensRange,
        TopologicalSpace.Opens.coe_bot]
      show Set.range (p (e.symm j)).hom.left.base ∩ Set.range (p (e.symm j')).hom.left.base = ∅
      rw [hrange, hrange, ← Set.image_inter hinj, hsigma _ _ (e.symm.injective.ne hjj'),
        Set.image_empty])
    (by
      rw [eq_top_iff]
      intro z _
      obtain ⟨w, rfl⟩ := φ.hom.homeomorph.surjective z
      obtain ⟨i, hi⟩ := hcover w
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e i, ?_⟩
      have := hopen (e.symm (e i))
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]
      show _ ∈ Set.range (p (e.symm (e i))).hom.left.base
      rw [e.symm_apply_apply, hrange]
      exact ⟨w, hi, rfl⟩)
  refine ⟨fun a b hab => h.1 (funext fun j => congrFun hab (e.symm j)), fun g => ?_⟩
  obtain ⟨a, ha⟩ := h.2 fun j => g (e.symm j)
  refine ⟨a, funext fun i => ?_⟩
  obtain ⟨j, rfl⟩ := e.symm.surjective i
  exact congrFun ha j

end FiniteCoproduct

/-! ### Spectra of finite separable extensions -/

section SeparableExtension

variable {K' : Type u} [CommRing K'] [Algebra k K'] [Module.Finite k K'] [Algebra.Etale k K']
  {K : Type u} [CommRing K] [Algebra k K] [Module.Finite k K] [Algebra.Etale k K]

/-- Every morphism `Spec(K) ⟶ Spec(K')` of smooth projective `k`-schemes is `Spec` of a
`k`-algebra map `K' → K`. -/
theorem exists_specMap_eq (g : spec k K ⟶ spec k K') : ∃ φ : K' →ₐ[k] K, specMap φ = g := by
  let φ₀ := Spec.preimage g.hom.left
  have hcomp : CommRingCat.ofHom (algebraMap k K') ≫ φ₀ = CommRingCat.ofHom (algebraMap k K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact Over.w g.hom
  refine ⟨⟨φ₀.hom, fun c => ?_⟩, hom_ext_left ?_⟩
  · exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of K => f.hom c) hcomp
  · show Spec.map (CommRingCat.ofHom φ₀.hom) = g.hom.left
    exact Spec.map_preimage _

/-- The `k`-algebra `Γ(Spec K', 𝒪)` is `K'`. -/
def globalSectionsSpecAlgHom : globalSections (spec k K') →ₐ[k] K' where
  toRingHom := (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
  commutes' c := by
    change ((Spec.map (CommRingCat.ofHom (algebraMap k K'))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of K')).hom).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c) = algebraMap k K' c
    rw [Scheme.ΓSpecIso_naturality]
    change (CommRingCat.ofHom (algebraMap k K')).hom
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c)
        = _
    rw [Iso.inv_hom_id]
    rfl

/-- `Spec` of a nonzero finite `k`-algebra has dimension zero. -/
theorem topologicalKrullDim_spec_field [Nontrivial K'] :
    topologicalKrullDim (spec k K').obj.left = 0 := by
  show topologicalKrullDim (PrimeSpectrum K') = 0
  have : IsArtinianRing K' := isArtinian_of_tower k inferInstance
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-- The underlying cofan of schemes of `Spec(K') × Spec(L) = ∐_σ Spec(L)` is a colimit. -/
theorem nonempty_isColimit_splitCofan_left [Nontrivial K'] (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (hsplit : ∀ a : globalSections (spec k K'), ((minpoly k a).map (algebraMap k L)).Splits) :
    Nonempty (Limits.IsColimit (Limits.Cofan.mk (prod (spec k K') (spec k L)).obj.left
      fun σ => (splitInj (topologicalKrullDim_spec_field (K' := K')) L σ).hom.left)) := by
  set hX := topologicalKrullDim_spec_field (k := k) (K' := K')
  have := finite_globalSections hX
  have := etale_globalSections hX
  let Φ := Stacks.FiniteEtaleSplitting.splitEquiv hsplit
  let R : (globalSections (spec k K') →ₐ[k] L) → CommRingCat.{u} := fun _ ↦ .of L
  have := isIso_prodMapSpec hX L
  have hdesc : Limits.Sigma.desc (splitLift hX L) ≫ prodMapSpec hX L ≫
      (pullbackSpecIso k (globalSections (spec k K')) L).hom =
        sigmaSpec R ≫ Spec.map (CommRingCat.ofHom Φ.toRingEquiv.toRingHom) := by
    refine Limits.Sigma.hom_ext _ _ fun σ ↦ ?_
    rw [Limits.Sigma.ι_desc_assoc, splitLift_prodMapSpec_pullbackSpecIso, ι_sigmaSpec_assoc,
      ← Spec.map_comp]
    congr 1
  have : IsIso (Limits.Sigma.desc (splitLift hX L) ≫ prodMapSpec hX L ≫
      (pullbackSpecIso k (globalSections (spec k K')) L).hom) := by
    rw [hdesc]
    have : IsIso (CommRingCat.ofHom Φ.toRingEquiv.toRingHom) :=
      (RingEquiv.toCommRingCatIso Φ.toRingEquiv).isIso_hom
    infer_instance
  have : IsIso (Limits.Sigma.desc (splitLift hX L)) :=
    IsIso.of_isIso_comp_right _
      (prodMapSpec hX L ≫ (pullbackSpecIso k (globalSections (spec k K')) L).hom)
  let c := Limits.Cofan.mk (prod (spec k K') (spec k L)).obj.left
    fun σ ↦ (splitInj hX L σ).hom.left
  have : IsIso (Limits.Sigma.desc c.inj) := by
    have : Limits.Sigma.desc c.inj =
        Limits.Sigma.desc (splitLift hX L) ≫ (prodLeftIso (spec k K') (spec k L)).inv :=
      Limits.Sigma.hom_ext _ _ fun σ ↦ by
        rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_desc_assoc]
        rfl
    rw [this]
    infer_instance
  exact ⟨Limits.Cofan.isColimitOfIsIsoSigmaDesc c⟩

/-- A nonzero vector `v` of an `F`-vector space makes `a ↦ a ⊗ v` injective. -/
theorem injective_tmul_right_of_ne_zero {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {w : W} (hw : w ≠ 0) :
    Function.Injective fun v : V => v ⊗ₜ[F] w := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one F hw
  intro a b hab
  simpa [hf] using congrArg ((TensorProduct.rid F V).toLinearMap ∘ₗ LinearMap.lTensor V f) hab

/-- If the minimal polynomial of every element of `B` splits in `E`, so does that of every element
of `A`, for an injective `k`-algebra map `A → B`. -/
private theorem splits_minpoly_map_of_injective {A B E : Type*} [CommRing A] [Algebra k A]
    [Ring B] [Algebra k B] [CommRing E] [Algebra k E] {f : A →ₐ[k] B} (hf : Function.Injective f)
    (h : ∀ b : B, ((minpoly k b).map (algebraMap k E)).Splits) (a : A) :
    ((minpoly k a).map (algebraMap k E)).Splits := by
  rw [← minpoly.algHom_eq f hf a]
  exact h _

/-- **Pullback to finitely many separable points is jointly injective on `H^*(Spec(A))`.** Let `A`
be a nonzero finite étale `k`-algebra, `φⱼ : A → Lⱼ` finitely many `k`-algebra maps to finite
separable field extensions, jointly injective, and `K/k` a finite normal separable extension in
which the minimal polynomial of every element of `A` splits and into which every `Lⱼ` embeds, with
`H^*(Spec(K)) ≠ 0`. Then under axioms (A1) and (A5), `a ↦ (Spec(φⱼ)^* a)ⱼ` is injective on
`H^*(Spec(A))`. This is the argument of Stacks 0FVS: `Spec(A) × Spec(K) = ∐_σ Spec(K)` with
coprojections `(Spec(σ), id)`, and every `σ : A → K` is an automorphism of `K` composed with some
`ψⱼ ∘ φⱼ`. -/
theorem injective_pull_specMap_family (hA1 : 𝔇.CoproductAxiom) (hA5 : 𝔇.KunnethAxiom)
    [Nontrivial K'] {ι : Type u} [Finite ι] {L : ι → Type u} [∀ j, Field (L j)]
    [∀ j, Algebra k (L j)] [∀ j, FiniteDimensional k (L j)] [∀ j, Algebra.IsSeparable k (L j)]
    (φ : ∀ j, K' →ₐ[k] L j) (hφ : Function.Injective fun a => fun j => φ j a)
    {E : Type u} [Field E] [Algebra k E] [FiniteDimensional k E] [Algebra.IsSeparable k E]
    [Normal k E] (ψ : ∀ j, L j →ₐ[k] E)
    (hsplit : ∀ a : K', ((minpoly k a).map (algebraMap k E)).Splits)
    (hE : Nontrivial (𝔇.H (spec k E))) :
    Function.Injective fun c : 𝔇.H (spec k K') => fun j => 𝔇.pull (specMap (φ j)) c := by
  classical
  set hX := topologicalKrullDim_spec_field (k := k) (K' := K')
  have := finite_globalSections hX
  obtain ⟨hc⟩ := nonempty_isColimit_splitCofan_left (k := k) (K' := K') E
    (splits_minpoly_map_of_injective (f := globalSectionsSpecAlgHom (k := k) (K' := K'))
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K')).hom).1 hsplit)
  have hpull := 𝔇.bijective_pull_of_isColimit_cofan hA1 (splitInj hX E) hc
  let Φ : 𝔇.H (spec k K') →ₗ[F] (∀ j, 𝔇.H (spec k (L j))) :=
    LinearMap.pi fun j => (𝔇.pull (specMap (φ j))).toLinearMap
  show Function.Injective Φ
  rw [injective_iff_map_eq_zero]
  intro c hc0
  have hσ : ∀ σ, 𝔇.pull (splitInj hX E σ ≫ fst (spec k K') (spec k E)) c = 0 := by
    intro σ
    obtain ⟨θ, hθ⟩ := exists_specMap_eq (splitInj hX E σ ≫ fst (spec k K') (spec k E))
    have : IsArtinianRing K' := isArtinian_of_tower k inferInstance
    have : Fintype ι := Fintype.ofFinite ι
    have hker : Finset.univ.inf (fun j => RingHom.ker (φ j).toRingHom) ≤
        RingHom.ker θ.toRingHom := by
      intro a ha
      have : a = 0 := hφ (funext fun j => by
        have := Finset.inf_le (f := fun j => RingHom.ker (φ j).toRingHom) (Finset.mem_univ j) ha
        simpa using this)
      rw [this]; exact zero_mem _
    have : (RingHom.ker θ.toRingHom).IsPrime := RingHom.ker_isPrime _
    obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.inf_le' inferInstance).mp hker
    have : (RingHom.ker (φ j).toRingHom).IsPrime := RingHom.ker_isPrime _
    have : (RingHom.ker (φ j).toRingHom).IsMaximal :=
      IsArtinianRing.isMaximal_of_isPrime _
    have hkereq : RingHom.ker (φ j).toRingHom = RingHom.ker θ.toRingHom :=
      Ideal.IsMaximal.eq_of_le inferInstance (RingHom.ker_ne_top _) hj
    let m := RingHom.ker (φ j).toRingHom
    let : Field (K' ⧸ m) := Ideal.Quotient.field m
    let α : K' ⧸ m →ₐ[k] E := (ψ j).comp (Ideal.Quotient.liftₐ m (φ j) fun a ha => ha)
    let β : K' ⧸ m →ₐ[k] E := Ideal.Quotient.liftₐ m θ fun a ha => by
      show a ∈ RingHom.ker θ.toRingHom; rw [← hkereq]; exact ha
    let : Algebra (K' ⧸ m) E := α.toRingHom.toAlgebra
    have : IsScalarTower k (K' ⧸ m) E :=
      IsScalarTower.of_algebraMap_eq fun c => (α.commutes c).symm
    let τ := β.liftNormal E
    have hτ : τ.comp ((ψ j).comp (φ j)) = θ := by
      ext a
      have h1 := β.liftNormal_commutes E (Ideal.Quotient.mk m a)
      have h2 : algebraMap (K' ⧸ m) E (Ideal.Quotient.mk m a) = ψ j (φ j a) := rfl
      rw [h2, Algebra.algebraMap_self, RingHom.id_apply] at h1
      exact h1
    have hcj : 𝔇.pull (specMap (φ j)) c = 0 := by simpa [Φ] using congrFun hc0 j
    rw [← hθ, ← hτ, specMap_comp, specMap_comp, 𝔇.pull_comp, 𝔇.pull_comp, AlgHom.comp_apply,
      AlgHom.comp_apply, hcj, map_zero, map_zero]
  have hκ : 𝔇.kunnethMap (spec k K') (spec k E) (c ⊗ₜ 1) = 0 := by
    apply hpull.1
    funext σ
    show 𝔇.pull (splitInj hX E σ) (𝔇.kunnethMap _ _ (c ⊗ₜ 1)) = 𝔇.pull (splitInj hX E σ) 0
    rw [map_zero, kunnethMap_tmul, map_one, mul_one, ← AlgHom.comp_apply, ← 𝔇.pull_comp]
    exact hσ σ
  have ht : c ⊗ₜ[F] (1 : 𝔇.H (spec k E)) = 0 := (hA5.2 _ _).1 (by rw [hκ, map_zero])
  exact injective_tmul_right_of_ne_zero one_ne_zero (ht.trans (TensorProduct.zero_tmul _ _).symm)

/-- For finite separable field extensions `k''/k'/k` and a finite normal separable extension `K/k`
containing `k''` (for instance a normal closure of `k''/k`) with `H^*(Spec(K)) ≠ 0`, pullback
`H^*(Spec(k')) ⟶ H^*(Spec(k''))` is injective, under axioms (A1) and (A5) (the source assumes
(A1)–(A7)); in particular it is injective on `H^0`. -/
@[stacks 0FVS "the source's statement, on the actual data (D0), (D1), (D2') over smooth projective \
  k-schemes: with H^*(Spec K) ≠ 0 for a finite normal separable K ⊇ k'' (a normal closure), \
  H^*(Spec k') ⟶ H^*(Spec k'') is injective, from (A1) and (A5)"]
theorem injective_pull_specMap_of_nontrivial (hA1 : 𝔇.CoproductAxiom) (hA5 : 𝔇.KunnethAxiom)
    {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    {k'' : Type u} [Field k''] [Algebra k k''] [FiniteDimensional k k''] [Algebra.IsSeparable k k'']
    (incl : k' →ₐ[k] k'') {E : Type u} [Field E] [Algebra k E] [FiniteDimensional k E]
    [Algebra.IsSeparable k E] [Normal k E] (ι : k'' →ₐ[k] E) (hE : Nontrivial (𝔇.H (spec k E))) :
    Function.Injective (𝔇.pull (specMap incl)) := by
  have h := 𝔇.injective_pull_specMap_family hA1 hA5 (ι := PUnit.{u + 1}) (L := fun _ => k'')
    (fun _ => incl) (fun a b hab => incl.toRingHom.injective (congrFun hab PUnit.unit))
    (fun _ => ι)
    (splits_minpoly_map_of_injective (f := ι.comp incl) (ι.comp incl).toRingHom.injective
      fun _ => Normal.splits inferInstance _) hE
  exact fun a b hab => h (funext fun _ => hab)

/-- A family of finite separable field extensions embeds into one finite Galois extension in which
the minimal polynomial of every element of the product splits. -/
theorem exists_isGalois_embeddings {ι : Type u} [Finite ι] (L : ι → Type u) [∀ j, Field (L j)]
    [∀ j, Algebra k (L j)] [∀ j, FiniteDimensional k (L j)] [∀ j, Algebra.IsSeparable k (L j)] :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : FiniteDimensional k E) (_ : IsGalois k E)
      (_ : ∀ j, L j →ₐ[k] E), ∀ a : ∀ j, L j, ((minpoly k a).map (algebraMap k E)).Splits := by
  obtain ⟨E, _, _, _, _, hE⟩ := Stacks.FiniteEtaleSplitting.exists_isGalois_splits_pi k L
  let pb (j : ι) : PowerBasis k (L j) := Field.powerBasisOfFiniteOfSeparable k (L j)
  let x : ∀ j, L j := fun j => (pb j).gen
  have hdvd (j : ι) : minpoly k (pb j).gen ∣ minpoly k x := by
    apply minpoly.dvd
    have := congrArg (Pi.evalAlgHom k L j) (minpoly.aeval k x)
    rwa [← Polynomial.aeval_algHom_apply, map_zero] at this
  have hsp (j : ι) : ((minpoly k (pb j).gen).map (algebraMap k E)).Splits :=
    (hE x).of_dvd (Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)))
      (Polynomial.map_dvd _ (hdvd j))
  have hroot (j : ι) : ∃ y : E, Polynomial.aeval y (minpoly k (pb j).gen) = 0 := by
    have hdeg : ((minpoly k (pb j).gen).map (algebraMap k E)).degree ≠ 0 := by
      rw [Polynomial.degree_map]
      exact (minpoly.degree_pos (Algebra.IsIntegral.isIntegral _)).ne'
    obtain ⟨y, hy⟩ := (hsp j).exists_eval_eq_zero hdeg
    exact ⟨y, by simpa [Polynomial.aeval_def, Polynomial.eval_map] using hy⟩
  choose y hy using hroot
  exact ⟨E, inferInstance, inferInstance, inferInstance, inferInstance,
    fun j => (pb j).lift (y j) (hy j), hE⟩

/-- **Pullback to finitely many separable points is jointly injective on `H^*(Spec(A))`**, for a
nonzero finite étale `k`-algebra `A` and jointly injective `k`-algebra maps `φⱼ : A → Lⱼ` to
finite separable field extensions, under axioms (A1), (A3), (A4) and (A5). The nonvanishing
hypothesis of `Stacks.WeilCohomology.FirstChernClassData.injective_pull_specMap_family` is
discharged by `Stacks.WeilCohomology.FirstChernClassData.nontrivial_H_spec`. -/
theorem injective_pull_specMap_family_of_axioms [CharZero F] (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA5 : 𝔇.KunnethAxiom)
    [Nontrivial K'] {ι : Type u} [Finite ι] {L : ι → Type u} [∀ j, Field (L j)]
    [∀ j, Algebra k (L j)] [∀ j, FiniteDimensional k (L j)] [∀ j, Algebra.IsSeparable k (L j)]
    (φ : ∀ j, K' →ₐ[k] L j) (hφ : Function.Injective fun a => fun j => φ j a) :
    Function.Injective fun c : 𝔇.H (spec k K') => fun j => 𝔇.pull (specMap (φ j)) c := by
  obtain ⟨E, _, _, _, _, ψ, hE⟩ := exists_isGalois_embeddings (k := k) L
  exact 𝔇.injective_pull_specMap_family hA1 hA5 φ hφ ψ
    (splits_minpoly_map_of_injective (f := Pi.algHom k L φ) hφ hE)
    (𝔇.nontrivial_H_spec hA3 hA4 hA5 E)

/-- For finite separable field extensions `k''/k'/k`, pullback `H^*(Spec(k')) ⟶ H^*(Spec(k''))` is
injective under axioms (A1), (A3), (A4) and (A5), `F` having characteristic zero: the hypothesis
`H^0(Spec(K)) ≠ 0` of the source is a consequence of the axioms
(`Stacks.WeilCohomology.FirstChernClassData.nontrivial_H_spec`). This is the form in which the
proof of Stacks 0FIS uses 0FVS. -/
@[stacks 0FVS "unconditional form: the nonvanishing hypothesis is derived from (A3), (A4), (A5)"]
theorem injective_pull_specMap_of_axioms [CharZero F] (hA1 : 𝔇.CoproductAxiom)
    (hA3 : 𝔇.ProjectiveBundleAxiom) (hA4 : 𝔇.DivisorAxiom) (hA5 : 𝔇.KunnethAxiom)
    {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']
    {k'' : Type u} [Field k''] [Algebra k k''] [FiniteDimensional k k''] [Algebra.IsSeparable k k'']
    (incl : k' →ₐ[k] k'') : Function.Injective (𝔇.pull (specMap incl)) := by
  have h := 𝔇.injective_pull_specMap_family_of_axioms hA1 hA3 hA4 hA5 (ι := PUnit.{u + 1})
    (L := fun _ => k'') (fun _ => incl)
    (fun a b hab => incl.toRingHom.injective (congrFun hab PUnit.unit))
  exact fun a b hab => h (funext fun _ => hab)

end SeparableExtension

end Stacks.WeilCohomology.FirstChernClassData

end
