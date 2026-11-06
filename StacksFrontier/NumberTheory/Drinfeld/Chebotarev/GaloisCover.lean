module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FrobeniusSplitting.QuotientCover
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
public import StacksFrontier.AlgebraicGeometry.Curves.WeilBound.FixedFieldPoints

/-!
# The Galois cover of an open normal subgroup of `π₁` and its field of constants

Let `X` be a connected scheme with a geometric point `base` and `U` an open normal subgroup of
`π₁(X, base)`. There is a connected Galois finite étale cover `Z` of `X` with a point `z₀` of its
fibre at `base` whose stabilizer in `π₁(X, base)` is exactly `U`, and on whose fibre `π₁(X, base)`
acts transitively: the fibre is `π₁ / U` as a `π₁`-set
(`AlgebraicGeometry.exists_galoisCover_stabilizer_eq`). This sharpens
`AlgebraicGeometry.exists_connected_cover_of_isOpen_normal`, which only records that `U` acts
trivially.

If `r : Y ⟶ Spec K` makes a connected reduced scheme `Y` proper over a finite extension `K` of a
field `k`, then every endomorphism `σ` of `Y` over `k` is semilinear over `K`: there is a
`k`-algebra endomorphism `θ` of `K` with `σ ≫ r = r ≫ Spec θ`
(`AlgebraicGeometry.exists_algHom_comp_specMap`). Indeed `r` and `σ ≫ r` correspond to two
`k`-embeddings of `K` into the field `Γ(Y, 𝒪_Y)`; when `K` is finite their images are the
subfield of `Γ(Y, 𝒪_Y)` of roots of `a ^ #K = a`, so the second factors through the first. When
`k` is finite with `q = p ^ e` elements, `θ` is a power `a ↦ a ^ q ^ c` with `c ≥ 1`
(`AlgebraicGeometry.exists_algHom_eq_iterateFrobenius`).

## Main results

* `AlgebraicGeometry.exists_galoisCover_stabilizer_eq`.
* `AlgebraicGeometry.exists_algHom_comp_specMap`.
* `AlgebraicGeometry.exists_algHom_eq_iterateFrobenius`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory Limits

universe u

namespace AlgebraicGeometry

section Cover

variable {X : Scheme.{u}} [ConnectedSpace X] {base : GeometricPoint X}

/-- **The Galois cover of an open normal subgroup of `π₁`.** For an open normal subgroup `U` of
`π₁(X, base)` there is a connected Galois finite étale cover `Z` of `X` and a point `z₀` of its
fibre at `base` whose stabilizer is `U`, the action of `π₁(X, base)` on the fibre being
transitive. -/
theorem exists_galoisCover_stabilizer_eq (U : Subgroup (EtaleFundamentalGroup X base))
    (hUn : U.Normal) (hUo : IsOpen (U : Set (EtaleFundamentalGroup X base))) :
    ∃ Z : FiniteEtaleOver X, ConnectedSpace Z.left ∧ PreGaloisCategory.IsGalois Z ∧
      ∃ z₀ : (finiteEtaleFiberFunctor base).obj Z,
        (∀ γ : EtaleFundamentalGroup X base, γ • z₀ = z₀ ↔ γ ∈ U) ∧
        ∀ w : (finiteEtaleFiberFunctor base).obj Z, ∃ γ : EtaleFundamentalGroup X base,
          γ • z₀ = w := by
  set F := finiteEtaleFiberFintypeFunctor X base
  set e := autMulEquivEtaleFundamentalGroup X base
  set F' : FiniteEtaleOver X ⥤ FintypeCat.{u + 1} := F ⋙ FintypeCat.uSwitch.{u, u + 1}
  have : FiberFunctor F' := FiberFunctor.comp_right _
  set φ : Aut F ≃ₜ* Aut F' :=
    autEquivAutWhiskerRight F (FintypeCat.uSwitchEquivalence.{u, u + 1}).fullyFaithfulFunctor
  set V : Subgroup (Aut F') := U.comap (e.toMonoidHom.comp φ.symm.toMonoidHom)
  have hVo : IsOpen (V : Set (Aut F')) :=
    hUo.preimage ((continuous_autMulEquivEtaleFundamentalGroup X base).comp φ.symm.continuous)
  obtain ⟨A, a, htransA, hstabA⟩ : ∃ (A : FiniteEtaleOver X) (a : F'.obj A),
      (∀ y : F'.obj A, ∃ σ : Aut F', σ • a = y) ∧ ∀ σ : Aut F', σ • a = a ↔ σ ∈ V := by
    obtain ⟨A, ⟨iso⟩⟩ := exists_lift_of_quotient_openSubgroup (F := F') ⟨V, hVo⟩
    have hinv : ∀ (σ : Aut F') (q : Aut F' ⧸ V), iso.inv.hom (σ • q) = σ • iso.inv.hom q :=
      fun σ q => congrArg (fun φ => φ q) (iso.inv.comm σ)
    have hhom : ∀ y : F'.obj A, iso.inv.hom (iso.hom.hom y) = y := fun y =>
      congrArg (fun φ => φ y) (congrArg Action.Hom.hom iso.hom_inv_id)
    have hhom' : ∀ q : Aut F' ⧸ V, iso.hom.hom (iso.inv.hom q) = q := fun q =>
      congrArg (fun φ => φ q) (congrArg Action.Hom.hom iso.inv_hom_id)
    have hq : ∀ σ : Aut F', σ • (QuotientGroup.mk 1 : Aut F' ⧸ V) = QuotientGroup.mk 1 ↔
        σ ∈ V := fun σ => by
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simp
    refine ⟨A, iso.inv.hom (QuotientGroup.mk 1 : Aut F' ⧸ V), fun y => ?_, fun σ =>
      ⟨fun h => (hq σ).1 ?_, fun h => (hinv σ _).symm.trans (congrArg _ ((hq σ).2 h))⟩⟩
    · obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (iso.hom.hom y)
      have hg' : g • (QuotientGroup.mk 1 : Aut F' ⧸ V) = iso.hom.hom y := by
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hg]
      exact ⟨g, (hinv g _).symm.trans ((congrArg _ hg').trans (hhom y))⟩
    · have h₂ := congrArg iso.hom.hom ((hinv σ _).trans h)
      rwa [hhom', hhom'] at h₂
  set ψ : F'.obj A ≃ F.obj A := (F.obj A).uSwitchEquiv
  have hψ : ∀ (σ : Aut F) (y : F'.obj A), ψ (φ σ • y) = σ • ψ y := fun σ y =>
    (FintypeCat.uSwitchEquiv_naturality (σ.asIso.hom.app A) y).symm
  have hVU : ∀ g : Aut F, φ g ∈ V ↔ e g ∈ U := fun g => by
    change e (φ.symm (φ g)) ∈ U ↔ _
    rw [ContinuousMulEquiv.symm_apply_apply]
  have htrans : ∀ y : F.obj A, ∃ σ : Aut F, σ • ψ a = y := fun y => by
    obtain ⟨g, hg⟩ := htransA (ψ.symm y)
    exact ⟨φ.symm g, by rw [← hψ, φ.apply_symm_apply, hg, ψ.apply_symm_apply]⟩
  have hstab : ∀ g : Aut F, g • ψ a = ψ a ↔ e g ∈ U := fun g => by
    rw [← hψ, ψ.injective.eq_iff, ← hVU]
    exact hstabA (φ g)
  obtain ⟨Z, i, z, hz, hconn, hmono⟩ := fiber_in_connected_component F A (ψ a)
  have hinj : Function.Injective (F.map i) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback (F.map i)).1 inferInstance
  have hequiv : ∀ (σ : Aut F) (w : F.obj Z), F.map i (σ • w) = σ • F.map i w := fun σ w =>
    (congrArg (fun φ => φ w) (σ.asIso.hom.naturality i)).symm
  have hstabZ : ∀ g : Aut F, g • z = z ↔ e g ∈ U := fun g => by
    rw [← hstab, ← hz, ← hequiv, hinj.eq_iff]
  have htransZ : ∀ w : F.obj Z, ∃ σ : Aut F, σ • z = w := fun w => by
    obtain ⟨σ, hσ⟩ := htrans (F.map i w)
    exact ⟨σ, hinj (by rw [hequiv, hz, hσ])⟩
  have hgal : PreGaloisCategory.IsGalois Z := by
    have := hconn
    refine PreGaloisCategory.isGalois_of_stabilizer_conj_mem F Z z htransZ fun g h hg => ?_
    rw [hstabZ] at hg ⊢
    rw [map_mul, map_mul, map_inv]
    simpa [mul_assoc] using hUn.conj_mem _ hg (e h)⁻¹
  refine ⟨Z, connectedSpace_left_of_isConnected Z hconn, hgal, z, fun γ => ?_, fun w => ?_⟩
  · obtain ⟨σ, rfl⟩ := e.surjective γ
    exact hstabZ σ
  · obtain ⟨σ, hσ⟩ := htransZ w
    exact ⟨e σ, hσ⟩

end Cover

section ConstantField

/-- **Endomorphisms over `k` are semilinear over a finite field of constants.** Let `r : Y ⟶
Spec K` make a connected reduced scheme `Y` proper over a finite extension `K` of `k`, `K` finite.
Then every endomorphism `σ` of `Y` over `k` satisfies `σ ≫ r = r ≫ Spec θ` for a `k`-algebra
endomorphism `θ` of `K`. -/
theorem exists_algHom_comp_specMap {k K : Type u} [Field k] [Field K] [Finite K] [Algebra k K]
    {Y : Scheme.{u}} [ConnectedSpace Y] [IsReduced Y] (r : Y ⟶ Spec (.of K))
    [IsProper (r ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)))] (σ : Y ⟶ Y)
    (hσ : σ ≫ r ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      r ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    ∃ θ : K →ₐ[k] K, σ ≫ r = r ≫ Spec.map (CommRingCat.ofHom θ.toRingHom) := by
  let := Fintype.ofFinite K
  set q := r ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : Field Γ(Y, ⊤) :=
    open Stacks.AlgebraicGeometry.ProperSectionsGeom in
    (isField_globalSections_of_connectedSpace_of_isReduced k q).toField
  have hfac : ∀ t : Y ⟶ Spec (.of K),
      Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of K)).inv ≫ t.appTop) = t := fun t => by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  set P := (Scheme.ΓSpecIso (.of K)).inv ≫ r.appTop
  set P' := (Scheme.ΓSpecIso (.of K)).inv ≫ (σ ≫ r).appTop
  have halg : ∀ t : Y ⟶ Spec (.of K), CommRingCat.ofHom (algebraMap k K) ≫
      (Scheme.ΓSpecIso (.of K)).inv ≫ t.appTop =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (t ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))).appTop :=
    fun t => by
      rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
        Scheme.Hom.comp_appTop]
  have hPP :
      CommRingCat.ofHom (algebraMap k K) ≫ P' = CommRingCat.ofHom (algebraMap k K) ≫ P := by
    rw [halg, halg, Category.assoc, hσ]
  have hmem : ∀ b : K, P'.hom b ∈ P.hom.range := fun b =>
    mem_range_of_pow_card_eq (Ω := Γ(Y, ⊤)) P.hom (a := P'.hom b)
      (by rw [← map_pow, FiniteField.pow_card])
  let eK : K ≃+* P.hom.range := RingEquiv.ofBijective P.hom.rangeRestrict
    ⟨fun a b hab => P.hom.injective (congrArg Subtype.val hab), P.hom.rangeRestrict_surjective⟩
  let θ₀ : K →+* K := eK.symm.toRingHom.comp (P'.hom.codRestrict _ hmem)
  have hθ₀ : ∀ b : K, P.hom (θ₀ b) = P'.hom b := fun b =>
    congrArg Subtype.val (eK.apply_symm_apply ⟨_, hmem b⟩)
  have hk : ∀ c : k, θ₀ (algebraMap k K c) = algebraMap k K c := fun c =>
    P.hom.injective <| (hθ₀ _).trans (congrArg (fun φ => φ.hom c) hPP)
  refine ⟨{ toRingHom := θ₀, commutes' := hk }, ?_⟩
  have hP' : P' = CommRingCat.ofHom θ₀ ≫ P := by
    ext b
    exact (hθ₀ b).symm
  conv_lhs => rw [← hfac (σ ≫ r)]
  change Y.toSpecΓ ≫ Spec.map P' = _
  rw [hP', Spec.map_comp, ← Category.assoc, hfac r]

/-- **A `k`-endomorphism of a finite extension of a finite field is a power of the Frobenius**
`a ↦ a ^ q ^ c` with `c ≥ 1`, `q = #k = p ^ e`. -/
theorem exists_algHom_eq_iterateFrobenius {k K : Type u} [Field k] [Fintype k] [Field K]
    [Finite K] [Algebra k K] (p : ℕ) [Fact p.Prime] [CharP K p] (e : ℕ)
    (hq : Fintype.card k = p ^ e) (θ : K →ₐ[k] K) :
    ∃ c : ℕ, 0 < c ∧ θ.toRingHom = iterateFrobenius K p (e * c) := by
  let := Fintype.ofFinite K
  have hbij : Function.Bijective θ := Finite.injective_iff_bijective.1 θ.injective
  set θ' : K ≃ₐ[k] K := AlgEquiv.ofBijective θ hbij
  obtain ⟨⟨a, ha⟩, hθ⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k K).2 θ'
  refine ⟨a + Module.finrank k K, by have := Module.finrank_pos (R := k) (M := K); omega, ?_⟩
  ext x
  have hcard : Fintype.card K = Fintype.card k ^ Module.finrank k K :=
    Module.card_eq_pow_finrank
  change θ' x = x ^ p ^ (e * (a + Module.finrank k K))
  rw [← hθ]
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  have hexp : p ^ (e * (a + Module.finrank k K)) = Fintype.card k ^ a * Fintype.card K := by
    rw [hcard, hq, ← pow_mul, ← pow_mul, ← pow_add]
    ring_nf
  rw [hexp, pow_mul, FiniteField.pow_card]

end ConstantField

end AlgebraicGeometry

end
