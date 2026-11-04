module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociatedFieldExtension
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.PullbackOpen

/-!
# Weakly associated points after extending the ground field

Let a scheme over a field be base changed along a field extension. The image of a weakly
associated point of the pullback of a quasi-coherent module is weakly associated to the original
module.

## Main results

* `AlgebraicGeometry.isWeaklyAssociatedPoint_of_baseChange` is that descent statement.
* `AlgebraicGeometry.isWeaklyAssociatedPoint_iff_of_moduleIso`: weak association of a point is
  invariant under an isomorphism of modules, which is how the descent moves the condition along
  the comparisons of modules it builds.

## Implementation notes

The base-changed scheme is the categorical pullback of the structure morphism along
`Spec K ⟶ Spec k`, and the base-changed module is the pullback along its first projection. The
equality identifying the image of the chosen point is retained explicitly rather than being
substituted, so that the statement can be applied to any point of the pullback.

The proof is local on the source: over an affine open `U` the base change is
`Spec (Γ(X, U) ⊗[k] K)`, where the assertion is the ring-theoretic statement that a weakly
associated prime of a tensor product with a field extension contracts to a weakly associated
prime (Stacks tag 0CUB).

## References

* [Stacks Project, Tag 0CUC](https://stacks.math.columbia.edu/tag/0CUC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A weakly associated prime maps to a weakly associated prime along a semilinear bijection of
modules over a ring isomorphism. -/
private theorem isWeaklyAssociatedPrime_map_of_semilinear {R S M N : Type*} [CommRing R]
    [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (e : R ≃+* S)
    (f : M ≃+ N) (hf : ∀ r m, f (r • m) = e r • f m) {p : Ideal R}
    (h : IsWeaklyAssociatedPrime R M p) : IsWeaklyAssociatedPrime S N (p.map e.toRingHom) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨f m, ?_⟩
  have hann : (S ∙ f m).annihilator.comap e.toRingHom = (R ∙ m).annihilator := by
    ext r
    simp only [Ideal.mem_comap, Submodule.mem_annihilator_span_singleton]
    change e r • f m = 0 ↔ r • m = 0
    rw [← hf]
    exact EmbeddingLike.map_eq_zero_iff
  rw [← hann] at hm
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_comap_eq e.toRingHom p hm
  rwa [← hqp, Ideal.map_comap_of_surjective e.toRingHom e.surjective]

/-- Weak association of a prime transfers along a semilinear bijection of modules over a ring
isomorphism. -/
private theorem isWeaklyAssociatedPrime_iff_of_semilinear {R S M N : Type*} [CommRing R]
    [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (e : R ≃+* S)
    (f : M ≃+ N) (hf : ∀ r m, f (r • m) = e r • f m) {p : Ideal R} :
    IsWeaklyAssociatedPrime R M p ↔
      IsWeaklyAssociatedPrime S N (p.map e.toRingHom) := by
  refine ⟨isWeaklyAssociatedPrime_map_of_semilinear e f hf, fun h => ?_⟩
  have hf' (s : S) (n : N) : f.symm (s • n) = e.symm s • f.symm n := f.injective (by
    rw [hf, f.apply_symm_apply, f.apply_symm_apply, e.apply_symm_apply])
  have := isWeaklyAssociatedPrime_map_of_semilinear e.symm f.symm hf' h
  rwa [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Ideal.map_id] at this

/-- On an affine scheme, weak association of a point to a quasi-coherent module is weak
association of the corresponding prime to the module of global sections. -/
private theorem affineSpec_weakAssocPoint_to_module (R : Type u) [CommRing R]
    (G : (Spec (.of R)).Modules) [G.IsQuasicoherent] (x : Spec (.of R)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint G x ↔
      IsWeaklyAssociatedPrime R ((moduleSpecΓFunctor (R := .of R)).obj G) x.asIdeal := by
  let hU := isAffineOpen_top (Spec (.of R))
  let q : Ideal Γ(Spec (.of R), ⊤) := (hU.primeIdealOf ⟨x, trivial⟩).asIdeal
  let e : Γ(Spec (.of R), ⊤) ≃+* R := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let f : Γ(G, ⊤) ≃+ ↑((moduleSpecΓFunctor (R := .of R)).obj G) := AddEquiv.refl _
  have hf : ∀ r m, f (r • m) = e r • f m := fun r m => by
    change r • m = (Scheme.ΓSpecIso (.of R)).inv.hom (e r) • m
    rw [show (Scheme.ΓSpecIso (.of R)).inv.hom (e r) = r from e.symm_apply_apply r]
  have hqeq : q = PrimeSpectrum.comap e.toRingHom x := by
    dsimp [q]
    apply congrArg PrimeSpectrum.asIdeal
    change hU.isoSpec.hom ⟨x, trivial⟩ = PrimeSpectrum.comap e.toRingHom x
    rw [IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_top, ← SpecMap_ΓSpecIso_hom]
    rfl
  have hmap : q.map e.toRingHom = x.asIdeal := by
    rw [hqeq]
    exact Ideal.map_comap_of_surjective e.toRingHom e.surjective x.asIdeal
  rw [← isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint G ⊤ hU x trivial, ← hmap]
  exact isWeaklyAssociatedPrime_iff_of_semilinear e f hf

/-- A point weakly associated to an `𝒪_X`-module is weakly associated to any isomorphic one. -/
theorem isWeaklyAssociatedPoint_of_moduleIso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    {x : X} (hx : Stacks.Divisors.IsWeaklyAssociatedPoint F x) :
    Stacks.Divisors.IsWeaklyAssociatedPoint G x :=
  (isWeaklyAssociatedPoint_iff_of_iso e x).mp hx

/-- Alias of `AlgebraicGeometry.isWeaklyAssociatedPoint_iff_of_iso`. -/
alias isWeaklyAssociatedPoint_iff_of_moduleIso := isWeaklyAssociatedPoint_iff_of_iso

/-- The inverse of the stalk map of an open immersion sends a germ to the germ of its image. -/
private theorem stalkMap_inv_germ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv (X.presheaf.germ U x hx a) =
      Y.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) ((j.appIso U).inv a) := by
  apply (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv.symm.injective
  simp only [RingEquiv.symm_apply_apply]
  change X.presheaf.germ U x hx a =
    j.stalkMap x (Y.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) ((j.appIso U).inv a))
  rw [j.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
  exact (X.presheaf.germ_res_apply _ _ _ _).symm

/-- Alias of `AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion`. -/
private alias isWeaklyAssociatedPoint_pullback_open_iff :=
  isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion

open scoped TensorProduct in
/-- The affine case of the descent: a weakly associated point of the pullback of `M~` to
`Spec (A ⊗[k] K)` contracts to a weakly associated prime of `M`. -/
private theorem weaklyAssociatedPoint_fieldChange_affine {k K A : Type u} [Field k] [Field K]
    [Algebra k K] [CommRing A] [Algebra k A] (M : ModuleCat (CommRingCat.of A))
    (q : PrimeSpectrum (A ⊗[k] K)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[k] K))))).obj
          ((tilde.functor (CommRingCat.of A)).obj M)) q →
      IsWeaklyAssociatedPrime A M (Ideal.comap (algebraMap A (A ⊗[k] K)) q.asIdeal) := by
  intro hq
  let B := A ⊗[k] K
  let f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let G : (Spec (.of B)).Modules :=
    (Scheme.Modules.pullback (Spec.map f)).obj ((tilde.functor (.of A)).obj M)
  let M' : ModuleCat (CommRingCat.of B) := (ModuleCat.extendScalars f.hom).obj M
  have ePB' : G ≅ (tilde.functor (CommRingCat.of B)).obj M' := by
    simpa [f, G, M', ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj',
      ModuleCat.RestrictScalars.obj', ModuleCat.of] using
      (pullbackTildeIso (.of A) (.of B) f).app M
  have hG : G.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec (.of B)).ringCatSheaf).prop_of_iso ePB'.symm
      inferInstance
  have hq' : IsWeaklyAssociatedPrime B ((moduleSpecΓFunctor (R := .of B)).obj G) q.asIdeal :=
    (affineSpec_weakAssocPoint_to_module B G q).mp hq
  let eΓ' := (moduleSpecΓFunctor (R := .of B)).mapIso ePB' ≪≫
    (tilde.toTildeΓNatIso (R := .of B)).symm.app M'
  have hq'' : IsWeaklyAssociatedPrime B (↑M') q.asIdeal :=
    (LinearEquiv.isWeaklyAssociatedPrime_iff eΓ'.toLinearEquiv q.asIdeal).mp hq'
  let eN : (B ⊗[A] M) ≃ₗ[B] (↑M') := by
    let T := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
    let : Module B T := inferInstance
    let : IsScalarTower A B T :=
      IsScalarTower.of_algebraMap_smul (A := B) (M := ↑T) (fun _ _ => rfl)
    change (B ⊗[A] M) ≃ₗ[B] (TensorProduct A T M)
    exact TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (R := B) (M := B)) (LinearEquiv.refl (R := A) (M := M))
  exact IsWeaklyAssociatedPrime.comap_tensorProduct_field
    ((LinearEquiv.isWeaklyAssociatedPrime_iff eN.symm q.asIdeal).mp hq'')

open scoped TensorProduct in
/-- Over an affine open `U` of a `k`-scheme `X`, the preimage of `U` in the base change of `X`
to `K` is `Spec (Γ(X, U) ⊗[k] K)`, compatibly with the projections to `U`. -/
private theorem exists_specTensorIso_preimage_baseChange {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (U : X.Opens) (hU : IsAffineOpen U)
    [Algebra k Γ(X, U)]
    (hfA : Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = hU.fromSpec ≫ f) :
    ∃ e : Spec (.of (Γ(X, U) ⊗[k] K)) ≅
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ U).toScheme,
      e.hom ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⁻¹ᵁ U).ι ≫
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Γ(X, U) ⊗[k] K))) ≫
          hU.isoSpec.inv ≫ U.ι := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let π := pullback.fst f g
  let fA := Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U)))
  have hfrom : hU.fromSpec = hU.isoSpec.inv ≫ U.ι := rfl
  let ePB := pullbackSpecIso k Γ(X, U) K
  let m := pullback.map fA g (U.ι ≫ f) g hU.isoSpec.inv (𝟙 _) (𝟙 _)
    (by
      change Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = hU.isoSpec.inv ≫ U.ι ≫ f
      rw [hfA, hfrom]
      simp) (by simp)
  have : IsIso m := by
    dsimp [m]
    infer_instance
  let eAssoc := pullbackRightPullbackFstIso f g U.ι
  let eRestrict := pullbackRestrictIsoRestrict π U
  let eSymm := pullbackSymmetry U.ι (pullback.fst f g)
  let eC : pullback (U.ι ≫ f) g ≅ (π ⁻¹ᵁ U).toScheme := eAssoc.symm ≪≫ eSymm ≪≫ eRestrict
  let B := Γ(X, U) ⊗[k] K
  let j : Spec (CommRingCat.of B) ⟶ Spec Γ(X, U) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B))
  refine ⟨ePB.symm ≪≫ asIso m ≪≫ eC, ?_⟩
  dsimp [eC, ePB, eAssoc, eSymm, eRestrict, π, g]
  simp only [Category.assoc]
  rw [pullbackRestrictIsoRestrict_hom_ι_assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst]
  change (pullbackSpecIso k Γ(X, U) K).inv ≫ m ≫ pullback.fst (U.ι ≫ f) g ≫ U.ι =
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B)) ≫ hU.fromSpec
  have hm : m ≫ pullback.fst (U.ι ≫ f) g = pullback.fst fA g ≫ hU.isoSpec.inv := by
    change pullback.lift (pullback.fst fA g ≫ hU.isoSpec.inv)
      (pullback.snd fA g ≫ 𝟙 _) _ ≫ pullback.fst (U.ι ≫ f) g = _
    rw [pullback.lift_fst]
  have hspec : ePB.inv ≫ pullback.fst fA g = j := pullbackSpecIso_inv_fst' k Γ(X, U) K
  rw [reassoc_of% hm, reassoc_of% hspec]
  rfl

open scoped TensorProduct in
/-- Descent of weak association through an open `V` of a scheme over `X` identified with
`Spec (Γ(X, U) ⊗[k] K)` compatibly with an affine open `U` of `X`. -/
private theorem isWeaklyAssociatedPoint_of_specTensorIso {k K : Type u} [Field k] [Field K]
    [Algebra k K] {X Y : Scheme.{u}} (π : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) [Algebra k Γ(X, U)] (V : Y.Opens)
    (e : Spec (.of (Γ(X, U) ⊗[k] K)) ≅ V.toScheme)
    (hmap : e.hom ≫ V.ι ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Γ(X, U) ⊗[k] K))) ≫ hU.isoSpec.inv ≫ U.ι)
    (y : V.toScheme) (hy : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback π).obj F) (V.ι.base y)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint F (π.base (V.ι.base y)) := by
  let B := Γ(X, U) ⊗[k] K
  let j : Spec (CommRingCat.of B) ⟶ Spec Γ(X, U) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B))
  let q : Spec (CommRingCat.of B) := e.inv.base y
  have hq : e.hom.base q = y := by simp [q]
  let HV : V.toScheme.Modules :=
    (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback π).obj F)
  let FU : U.toScheme.Modules := (Scheme.Modules.pullback U.ι).obj F
  have hFU : FU.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion U.ι F
  let GA : (Spec Γ(X, U)).Modules := (Scheme.Modules.pullback hU.isoSpec.inv).obj FU
  have hGA : GA.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion
      hU.isoSpec.inv FU
  let M : ModuleCat Γ(X, U) := (moduleSpecΓFunctor (R := Γ(X, U))).obj GA
  let HB : (Spec (CommRingCat.of B)).Modules := (Scheme.Modules.pullback e.hom).obj HV
  have hyB : Stacks.Divisors.IsWeaklyAssociatedPoint HB q := by
    refine (isWeaklyAssociatedPoint_pullback_open_iff e.hom HV q).mpr ?_
    rw [hq]
    exact (isWeaklyAssociatedPoint_pullback_open_iff V.ι _ y).mpr hy
  have hHB : HB ≅ (Scheme.Modules.pullback j).obj ((tilde.functor (.of Γ(X, U))).obj M) := by
    let c₁ := (Scheme.Modules.pullback e.hom).mapIso ((Scheme.Modules.pullbackComp V.ι π).app F)
    let c₂ := (Scheme.Modules.pullbackComp e.hom (V.ι ≫ π)).app F
    let c₃ := (Scheme.Modules.pullbackCongr hmap).app F
    let c₄ := (Scheme.Modules.pullback j).mapIso
      ((Scheme.Modules.pullbackComp hU.isoSpec.inv U.ι).app F)
    let c₅ := (Scheme.Modules.pullbackComp j (hU.isoSpec.inv ≫ U.ι)).app F
    exact c₁ ≪≫ c₂ ≪≫ c₃ ≪≫ c₅.symm ≪≫ c₄.symm ≪≫
      (Scheme.Modules.pullback j).mapIso (asIso GA.fromTildeΓ).symm
  have hweakA : IsWeaklyAssociatedPrime Γ(X, U) M
      (Ideal.comap (algebraMap Γ(X, U) B) q.asIdeal) :=
    weaklyAssociatedPoint_fieldChange_affine M q
      ((isWeaklyAssociatedPoint_iff_of_moduleIso hHB q).mp hyB)
  have hweakF : Stacks.Divisors.IsWeaklyAssociatedPoint F
      (U.ι.base (hU.isoSpec.inv.base (j.base q))) :=
    (isWeaklyAssociatedPoint_pullback_open_iff U.ι F _).mp
      ((isWeaklyAssociatedPoint_pullback_open_iff hU.isoSpec.inv FU (j.base q)).mp
        ((affineSpec_weakAssocPoint_to_module Γ(X, U) GA (j.base q)).mpr hweakA))
  have he : π.base (V.ι.base (e.hom.base q)) = U.ι.base (hU.isoSpec.inv.base (j.base q)) :=
    congrArg (fun a : Spec (CommRingCat.of B) ⟶ X => a.base q) hmap
  rwa [← hq, he]

open scoped TensorProduct in
/-- The descent, localized on an affine open of the source. -/
private theorem weaklyAssociatedPoint_pullback_baseChange_affineOpen {k K : Type u} [Field k]
    [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules)
    [F.IsQuasicoherent]
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) (x : X)
    (hyx : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x)
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U)
    (hy : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj F) y) :
    Stacks.Divisors.IsWeaklyAssociatedPoint F x := by
  subst hyx
  have hApp : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let ψ : CommRingCat.of k ⟶ Γ(X, U) := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U hApp
  let : Algebra k Γ(X, U) := ψ.hom.toAlgebra
  have hψ : ψ = CommRingCat.ofHom (algebraMap k Γ(X, U)) := rfl
  have hfA : Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) = hU.fromSpec ≫ f := by
    rw [← hψ]
    simpa only [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of k))) hU hApp)
  obtain ⟨e, hmap⟩ := exists_specTensorIso_preimage_baseChange (K := K) f U hU hfA
  exact isWeaklyAssociatedPoint_of_specTensorIso _ F U hU _ e hmap ⟨y, hxU⟩ hy

/-- **Stacks Project, Tag 0CUC.** If a point of a field base change is weakly associated to the
pullback of a quasi-coherent module, then its image is weakly associated to the original
module. -/
@[stacks 0CUC]
lemma isWeaklyAssociatedPoint_of_baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules) [F.IsQuasicoherent]
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) (x : X)
    (hyx : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x)
    (hy : Stacks.Divisors.IsWeaklyAssociatedPoint
      ((Scheme.Modules.pullback
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj F) y) :
    Stacks.Divisors.IsWeaklyAssociatedPoint F x := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  exact weaklyAssociatedPoint_pullback_baseChange_affineOpen f F y x hyx U hU hxU hy

end AlgebraicGeometry
