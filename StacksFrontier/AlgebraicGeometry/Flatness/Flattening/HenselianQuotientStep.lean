module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselianColimitFreeStep
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent
public import StacksFrontier.RingTheory.Flat.HenselianFlattening
public import StacksFrontier.RingTheory.Flat.LocalCriterionEssFP
public import StacksFrontier.RingTheory.Henselian.Quotient

/-!
# The flat case of Stacks 0AT3 over a quotient of the base

Fix Situation 0AT0 with `A` henselian, and an ideal `I ⊆ 𝔪_A` such that `N/IN` is flat over
`A/I`. Then the reduction `u mod I : N/IN → M/IM` is `A`-universally injective.

This is the step of the second paragraph of the proof of Stacks 0AT3 which says that "the result
of the previous paragraph shows that the lemma holds for `u mod I : N/IN → M/IM` over `A/I`". The
data `A/I → B/IB`, `M/IM`, `N/IN`, `u mod I` form Situation 0AT0 again: `A/I` is a henselian
local ring, `B/IB` is local and essentially of finite type over it, the structure map is local,
`M/IM` is flat over `A/I`, and `N/IN` is a finite `B/IB`-module whose reduction modulo the maximal
ideal of `A/I` is that of `N` modulo `𝔪_A`. Since `N/IN` is flat over `A/I`, the flat case of
Stacks 0AT3 (`AlgebraicGeometry.universallyInjective_of_henselian_of_flat`) applies over `A/I`.

## Main results

* `AlgebraicGeometry.rTensor_mapQ_injective_of_henselian_of_flat_quotient`: for every
  `A`-module `Q`, the map `(N/IN) ⊗_A Q → (M/IM) ⊗_A Q` induced by `u` is injective.

## Implementation notes

The quotient `N/IN` appears twice: as `N ⧸ (I • ⊤ : Submodule A N)`, the form of the statement,
and as `N ⧸ (IB • ⊤ : Submodule B N)`, which carries the `B/IB`-module structure that
Situation 0AT0 over `A/I` asks for. The two submodules have the same elements
(`Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top`), and the quotients are identified by
`Stacks.Flatness.FibrewiseCriterionEssFP.quotAddEquivOfCoeEq`. The `A/I`-module structure on the
second one is restricted from its `B/IB`-module structure.

Universal injectivity over `A/I` is turned into universal injectivity over `A` by
`X ⊗_{A/I} ((A/I) ⊗_A Q) ≅ X ⊗_A Q` for an `A/I`-module `X`
(`TensorProduct.AlgebraTensorModule.cancelBaseChange`), which is natural in `X`.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT3](https://stacks.math.columbia.edu/tag/0AT3)
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

/-- An element of `X` lies in `J • X` exactly when its class modulo a submodule `P ≤ J • X`
lies in `J • (X ⧸ P)`. -/
private lemma mkQ_mem_smul_top_iff {A X : Type*} [CommRing A] [AddCommGroup X] [Module A X]
    (P : Submodule A X) (J : Ideal A) (hP : P ≤ J • ⊤) (x : X) :
    P.mkQ x ∈ J • (⊤ : Submodule A (X ⧸ P)) ↔ x ∈ J • (⊤ : Submodule A X) := by
  have h : J • (⊤ : Submodule A (X ⧸ P)) = (J • (⊤ : Submodule A X)).map P.mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  rw [h, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_eq_right.mpr hP]

/-- Universal injectivity over a quotient ring gives universal injectivity over the ring: if `f`
is a map of `A ⧸ I`-modules such that `f ⊗ id` is injective for the `A ⧸ I`-module
`(A ⧸ I) ⊗_A Q`, then `f ⊗ id_Q` over `A` is injective. -/
private lemma rTensor_injective_of_quotient {A : Type*} [CommRing A] (I : Ideal A)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module A X] [Module A Y]
    [Module (A ⧸ I) X] [Module (A ⧸ I) Y] [IsScalarTower A (A ⧸ I) X] [IsScalarTower A (A ⧸ I) Y]
    (f : X →ₗ[A ⧸ I] Y) (Q : Type*) [AddCommGroup Q] [Module A Q]
    (hf : Function.Injective (f.rTensor ((A ⧸ I) ⊗[A] Q))) :
    Function.Injective ((f.restrictScalars A).rTensor Q) := by
  let eX := AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) X Q
  let eY := AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) Y Q
  have hnat : ∀ z, eY (f.rTensor ((A ⧸ I) ⊗[A] Q) z) = (f.restrictScalars A).rTensor Q (eX z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x w =>
      induction w using TensorProduct.inductionOn with
      | tmul r q =>
        simp [eX, eY, AlgebraTensorModule.cancelBaseChange_tmul]
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add, hw, hw']
    | add z z' hz hz' => simp only [map_add, hz, hz']
  intro a b hab
  obtain ⟨a, rfl⟩ := eX.surjective a
  obtain ⟨b, rfl⟩ := eX.surjective b
  rw [← hnat, ← hnat] at hab
  rw [hf (eY.injective hab)]

/-- For local rings `A → B` with a local structure map and an ideal `I` of `A` with `B ⧸ IB`
local, the induced map `A ⧸ I → B ⧸ IB` is local. -/
private theorem isLocalHom_algebraMap_quotient_map {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] (I : Ideal A)
    [IsLocalRing (B ⧸ I.map (algebraMap A B))] :
    IsLocalHom (algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B))) := by
  have hJm : I.map (algebraMap A B) ≤ maximalIdeal B :=
    le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance)
  constructor
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  by_contra hna
  have hb : algebraMap A B a ∈ maximalIdeal B :=
    Module.FlatAtPointSituation.map_maximalIdeal_le (algebraMap A B)
      (Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).mpr fun h ↦ hna (h.map _)))
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp ha
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, ← map_mul,
    ← map_one (Ideal.Quotient.mk (I.map (algebraMap A B))), Ideal.Quotient.eq] at hc
  refine (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  simpa using (maximalIdeal B).sub_mem ((maximalIdeal B).mul_mem_right c hb) (hJm hc)

/-- For a local ring `A`, a proper ideal `I` and an `A ⧸ I`-module `X`, the submodule
`𝔪_{A/I} • X` has the same elements as `𝔪_A • X`. -/
private theorem mem_maximalIdeal_quotient_smul_top_iff {A X : Type*} [CommRing A] [IsLocalRing A]
    {I : Ideal A} [IsLocalRing (A ⧸ I)] [AddCommGroup X] [Module A X] [Module (A ⧸ I) X]
    [IsScalarTower A (A ⧸ I) X] (x : X) :
    x ∈ maximalIdeal (A ⧸ I) • (⊤ : Submodule (A ⧸ I) X) ↔
      x ∈ maximalIdeal A • (⊤ : Submodule A X) := by
  have hm : (maximalIdeal A).map (algebraMap A (A ⧸ I)) = maximalIdeal (A ⧸ I) :=
    Module.FlatAtPointSituation.maximalIdeal_quotient
      (Ideal.Quotient.nontrivial_iff.mp inferInstance)
  rw [← hm, ← SetLike.mem_coe, Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top,
    SetLike.mem_coe]

/-- **The flat case of Stacks 0AT3 over `A ⧸ I`.** In Situation 0AT0 with `A` henselian, let
`I ⊆ 𝔪_A` be an ideal such that `N/IN` is flat over `A/I`. Then `u mod I : N/IN → M/IM` is
`A`-universally injective: `(N/IN) ⊗_A Q → (M/IM) ⊗_A Q` is injective for every `A`-module `Q`.

This is the step "the result of the previous paragraph shows that the lemma holds for
`u mod I : N/IN → M/IM` over `A/I`" of the proof of Stacks 0AT3: `A/I → B/IB`, `M/IM`, `N/IN`,
`u mod I` form Situation 0AT0 over the henselian local ring `A/I`, to which
`universallyInjective_of_henselian_of_flat` applies. -/
theorem rTensor_mapQ_injective_of_henselian_of_flat_quotient
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄}) [HenselianLocalRing S.A]
    (I : Ideal S.A) (hI : I ≤ maximalIdeal S.A)
    (hflat : Module.Flat (S.A ⧸ I) (S.N ⧸ (I • ⊤ : Submodule S.A S.N)))
    (Q : Type u₅) [AddCommGroup Q] [Module S.A Q] :
    Function.Injective ((Submodule.mapQ (I • ⊤ : Submodule S.A S.N)
      (I • ⊤ : Submodule S.A S.M) S.u (Submodule.smul_top_le_comap_smul_top I S.u)).rTensor Q) := by
  classical
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal S.A).ne_top hI
  set J : Ideal S.B := I.map (algebraMap S.A S.B) with hJ
  have hJm : J ≤ maximalIdeal S.B := (Ideal.map_mono hI).trans
    (Module.FlatAtPointSituation.map_maximalIdeal_le (algebraMap S.A S.B))
  have hJtop : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal S.B).ne_top hJm
  have : Nontrivial (S.A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have : Nontrivial (S.B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (S.B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have : HenselianLocalRing (S.A ⧸ I) := Stacks.Henselian.henselianLocalRing_quotient hItop
  have : IsLocalHom (algebraMap (S.A ⧸ I) (S.B ⧸ J)) := isLocalHom_algebraMap_quotient_map I
  have : Algebra.EssFiniteType (S.A ⧸ I) (S.B ⧸ J) :=
    Algebra.EssFiniteType.of_comp S.A (S.A ⧸ I) (S.B ⧸ J)
  -- The two quotient modules.
  let M' := S.M ⧸ (I • ⊤ : Submodule S.A S.M)
  let N' := S.N ⧸ (J • ⊤ : Submodule S.B S.N)
  have : Module.Flat (S.A ⧸ I) M' := Module.Flat.quotient_smul_top I
  let modN' : Module (S.A ⧸ I) N' := Module.compHom N' (algebraMap (S.A ⧸ I) (S.B ⧸ J))
  have : IsScalarTower (S.A ⧸ I) (S.B ⧸ J) N' := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hAN' : IsScalarTower S.A (S.A ⧸ I) N' := IsScalarTower.of_algebraMap_smul fun a x ↦ by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (algebraMap S.A S.B a • n) = Submodule.Quotient.mk (a • n)
    rw [algebraMap_smul]
  have hAM' : IsScalarTower S.A (S.A ⧸ I) M' := IsScalarTower.of_algebraMap_smul fun a x ↦ by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  -- The identification of `N ⧸ IB • ⊤` with `N ⧸ I • ⊤`.
  let φ : N' ≃+ S.N ⧸ (I • ⊤ : Submodule S.A S.N) :=
    Stacks.Flatness.FibrewiseCriterionEssFP.quotAddEquivOfCoeEq _ _
      (Stacks.Flatness.FibrewiseCriterionEssFP.coe_map_smul_top (R := S.A) (A := S.B)
        (M := S.N) I)
  have hφ : ∀ (a : S.A) (x : N'), φ (a • x) = a • φ x := by
    intro a x
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  let φL : N' ≃ₗ[S.A] S.N ⧸ (I • ⊤ : Submodule S.A S.N) := φ.toLinearEquiv hφ
  have : Module.Flat (S.A ⧸ I) N' :=
    Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv (RingEquiv.refl _) φ
      (by
        intro r x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        simpa only [RingEquiv.refl_apply, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
          using hφ a x)
  -- The reduction of `u`.
  let ubar := Submodule.mapQ (I • ⊤ : Submodule S.A S.N) (I • ⊤ : Submodule S.A S.M) S.u
    (Submodule.smul_top_le_comap_smul_top I S.u)
  let uA : N' →ₗ[S.A] M' := ubar ∘ₗ φL.toLinearMap
  let u' : N' →ₗ[S.A ⧸ I] M' :=
    { toFun := uA
      map_add' := uA.map_add
      map_smul' := by
        intro r x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [RingHom.id_apply, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul,
          map_smul] }
  have hinj : Function.Injective
      (Submodule.mapQ (maximalIdeal (S.A ⧸ I) • (⊤ : Submodule (S.A ⧸ I) N'))
        (maximalIdeal (S.A ⧸ I) • (⊤ : Submodule (S.A ⧸ I) M')) u'
        (Submodule.smul_top_le_comap_smul_top (maximalIdeal (S.A ⧸ I)) u')) := by
    rw [Submodule.injective_mapQ_smul_top_iff]
    intro x hx
    rw [mem_maximalIdeal_quotient_smul_top_iff] at hx
    rw [mem_maximalIdeal_quotient_smul_top_iff, ← mem_smul_top_equiv_iff φL]
    obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective _ (φL x)
    have hux : u' x = (I • ⊤ : Submodule S.A S.M).mkQ (S.u n) := by
      change ubar (φL x) = _
      rw [← hn]
      rfl
    rw [hux, mkQ_mem_smul_top_iff _ _ (Submodule.smul_mono_left hI)] at hx
    rw [← hn]
    exact (mkQ_mem_smul_top_iff _ _ (Submodule.smul_mono_left hI) n).mpr
      ((Submodule.injective_mapQ_smul_top_iff S.u _).mp S.injective_mod_maximalIdeal n hx)
  -- Situation 0AT0 over `A ⧸ I`, and its flat case.
  let T : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄} :=
    { A := S.A ⧸ I, B := S.B ⧸ J, M := M', N := N', u := u', injective_mod_maximalIdeal := hinj }
  have hUI := @universallyInjective_of_henselian_of_flat.{u₁, u₂, u₃, u₄, max u₁ u₅} T
    (inferInstanceAs (HenselianLocalRing (S.A ⧸ I))) (inferInstanceAs (Module.Flat (S.A ⧸ I) N'))
  have hfac : ubar = (u'.restrictScalars S.A) ∘ₗ φL.symm.toLinearMap := by
    refine LinearMap.ext fun y ↦ ?_
    change _ = ubar (φL (φL.symm y))
    rw [LinearEquiv.apply_symm_apply]
  change Function.Injective (ubar.rTensor Q)
  rw [hfac, LinearMap.rTensor_comp, LinearMap.coe_comp]
  exact (rTensor_injective_of_quotient I u' Q (hUI ((S.A ⧸ I) ⊗[S.A] Q))).comp
    (LinearEquiv.rTensor Q φL.symm).injective

end AlgebraicGeometry

end
