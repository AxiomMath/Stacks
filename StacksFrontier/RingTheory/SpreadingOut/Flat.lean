module

public import StacksFrontier.RingTheory.Flat.ColimitTrivialRelation
public import StacksFrontier.RingTheory.Flat.LocalCriterionVariant

@[expose] public section

/-!
# Flatness spreads out along a directed system of essentially finite type

Let `R → S` be a homomorphism of rings, `M` an `S`-module, and let `(A i → B i, N i)` be a
directed system spreading `(R → S, M)` out over `ℤ` in the sense of 00QX. If `M` is flat over
`R`, then `N j` is flat over `A j` for some index `j` — and for some `j` above any prescribed
one.

The system is given by the data and the six conditions in the conclusion of
`RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module`, together with
locality of the transition maps `A i → A j`.

## Main results

* `Module.Flat.exists_ge_flat_of_isColimit`: if `M` is flat over `R`, then for every index `i`
  there is `j ≥ i` such that `N j` is flat over `A j`.
* `CommRingCat.exists_isLocalization_tensorProduct_of_pushout`: the cartesian condition of 00QX,
  stated for the pushout in `CommRingCat`, reread for the tensor product.
-/

universe u

open CategoryTheory Limits
open scoped TensorProduct

/-- If `Sj` is a localization at a prime of the pushout of `Ri → Si` and `Ri → Rj` in
`CommRingCat`, for the algebra structure given by `pushout.desc`, then `Sj` is a localization of
`Si ⊗[Ri] Rj` at some submonoid, for the algebra structure given by
`Algebra.TensorProduct.productMap`. -/
public theorem CommRingCat.exists_isLocalization_tensorProduct_of_pushout
    {Ri Si Rj Sj : Type u} [CommRing Ri] [CommRing Si] [CommRing Rj] [CommRing Sj]
    [Algebra Ri Si] [Algebra Ri Rj] [Algebra Si Sj] [Algebra Rj Sj] [Algebra Ri Sj]
    [IsScalarTower Ri Si Sj] [IsScalarTower Ri Rj Sj] [Algebra (Si ⊗[Ri] Rj) Sj]
    (hmap : ∀ x, algebraMap (Si ⊗[Ri] Rj) Sj x
      = Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom Ri Si Sj)
          (IsScalarTower.toAlgHom Ri Rj Sj) x)
    (sq : CommRingCat.ofHom (algebraMap Ri Si) ≫ CommRingCat.ofHom (algebraMap Si Sj)
      = CommRingCat.ofHom (algebraMap Ri Rj) ≫ CommRingCat.ofHom (algebraMap Rj Sj))
    (H : letI := (pushout.desc (CommRingCat.ofHom (algebraMap Si Sj))
          (CommRingCat.ofHom (algebraMap Rj Sj)) sq).hom.toAlgebra
      ∃ (q : Ideal ↑(pushout (CommRingCat.ofHom (algebraMap Ri Si))
          (CommRingCat.ofHom (algebraMap Ri Rj)))) (_ : q.IsPrime),
        IsLocalization q.primeCompl Sj) :
    ∃ T : Submonoid (Si ⊗[Ri] Rj), IsLocalization T Sj := by
  let instP : Algebra ↑(pushout (CommRingCat.ofHom (algebraMap Ri Si))
      (CommRingCat.ofHom (algebraMap Ri Rj))) Sj :=
    (pushout.desc (CommRingCat.ofHom (algebraMap Si Sj))
      (CommRingCat.ofHom (algebraMap Rj Sj)) sq).hom.toAlgebra
  obtain ⟨q, _, hloc⟩ := H
  have := hloc
  have hpo := CommRingCat.isPushout_tensorProduct Ri Si Rj
  set can : (Si ⊗[Ri] Rj) →ₐ[Ri] Sj := Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom Ri Si Sj) (IsScalarTower.toAlgHom Ri Rj Sj) with hcan
  have key : hpo.isoPushout.inv ≫ CommRingCat.ofHom can.toRingHom
      = pushout.desc (CommRingCat.ofHom (algebraMap Si Sj))
          (CommRingCat.ofHom (algebraMap Rj Sj)) sq := by
    apply pushout.hom_ext
    · rw [← Category.assoc, hpo.inl_isoPushout_inv, pushout.inl_desc]
      ext x; simp [hcan]
    · rw [← Category.assoc, hpo.inr_isoPushout_inv, pushout.inr_desc]
      ext x; simp [hcan]
  set e : (Si ⊗[Ri] Rj) ≃+* ↑(pushout (CommRingCat.ofHom (algebraMap Ri Si))
      (CommRingCat.ofHom (algebraMap Ri Rj))) :=
    hpo.isoPushout.commRingCatIsoToRingEquiv with he
  refine ⟨Submonoid.comap (e : (Si ⊗[Ri] Rj) →+* _) q.primeCompl, ?_⟩
  refine IsLocalization.of_ringEquiv_left (M₁ := q.primeCompl) e ?_ ?_
  · exact Submonoid.map_comap_eq_of_surjective e.surjective _
  · intro x
    rw [hmap x]
    have : (pushout.desc (CommRingCat.ofHom (algebraMap Si Sj))
        (CommRingCat.ofHom (algebraMap Rj Sj)) sq).hom (e x) = can x := by
      rw [← key]
      change (CommRingCat.ofHom can.toRingHom).hom (hpo.isoPushout.inv.hom (e x)) = can x
      have : hpo.isoPushout.inv.hom (e x) = x := e.symm_apply_apply x
      rw [this]; rfl
    exact this.symm

namespace Module.Flat

/-- Let `(A i → B i, N i)` be a directed system as in 00QX, with colimits `R → S` and `M`: each
`A i` is essentially of finite type over `ℤ`, each `A i → B i` is a local homomorphism of local
rings essentially of finite type, each transition map `A i → A j` is local, each `N i` is a finite
`B i`-module, each `B j` is a localization of `B i ⊗_{A i} A j` at a prime ideal, and each `N j` is
the base change of `N i` along `B i → B j`. If `M` is flat over `R`, then for every index `i` there
is `j ≥ i` such that `N j` is flat over `A j`. -/
@[stacks 00R6 "The system \"as in Lemma 00QX\" is spelled out as the data and the six
conditions concluded by `RingHom.EssentiallyOfFinitePresentation.exists_isColimit_\
essFiniteType_module`, together with locality of the transition maps `A i → A j`, which is
the source's \"system of local homomorphisms of local rings\" read as a system in the
category of local rings and is what 00MO needs to know `(𝔪 i) A j` is proper. The
hypotheses of 00QX are not assumed, being either unused or consequences of the system. The
conclusion is the cofinal form (`∀ i, ∃ j ≥ i`), which is what the source's proof produces
and what the dependents use. See the module docstring."]
public theorem exists_ge_flat_of_isColimit
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Flat R M]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A B : Λ ⥤ CommRingCat.{u}} {φ : A ⟶ B} {N : Λ ⥤ AddCommGrpCat.{u}}
    (mod : ∀ i, Module (B.obj i) (N.obj i))
    (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (b : B.obj i) (m : N.obj i),
      N.map h (b • m) = B.map h b • N.map h m)
    {ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R)}
    {σ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S)}
    {ν : N ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M)}
    (hR : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
    (_hS : IsColimit (Cocone.mk (CommRingCat.of S) σ))
    (hM : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν))
    (hφ : ∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom (algebraMap R S))
    (hν : ∀ (i : Λ) (b : B.obj i) (m : N.obj i),
      (ν.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M) (σ.app i b) (ν.app i m))
    (hAlocal : ∀ i, IsLocalRing (A.obj i)) (hBlocal : ∀ i, IsLocalRing (B.obj i))
    (hφlocal : ∀ i, IsLocalHom (φ.app i).hom)
    (hAmaplocal : ∀ ⦃i j : Λ⦄ (h : i ⟶ j), IsLocalHom (A.map h).hom)
    (hAft : ∀ i, Algebra.EssFiniteType ℤ (A.obj i))
    (hφft : ∀ i, (φ.app i).hom.EssFiniteType)
    (hNfin : ∀ i, Module.Finite (B.obj i) (N.obj i))
    (hBloc : ∀ ⦃i j : Λ⦄ (h : i ⟶ j),
      letI := (pushout.desc (B.map h) (φ.app j) (φ.naturality h).symm).hom.toAlgebra
      ∃ (q : Ideal ↑(pushout (φ.app i) (A.map h))) (_ : q.IsPrime),
        IsLocalization q.primeCompl ↑(B.obj j))
    (hNbc : ∀ ⦃i j : Λ⦄ (h : i ⟶ j),
      letI : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map h).hom.toAlgebra
      letI : Module ↑(B.obj i) ↑(N.obj j) := Module.compHom _ (B.map h).hom
      letI : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(N.obj j) :=
        .of_algebraMap_smul fun _ _ => rfl
      IsBaseChange ↑(B.obj j)
        (⟨(N.map h).hom.toAddHom, hsmul h⟩ : ↑(N.obj i) →ₗ[↑(B.obj i)] ↑(N.obj j)))
    (i : Λ) :
    ∃ j, i ≤ j ∧
      (letI : Module ↑(A.obj j) ↑(N.obj j) := Module.compHom _ (φ.app j).hom
       Module.Flat ↑(A.obj j) ↑(N.obj j)) := by
  have hnat : ∀ ⦃k l : Λ⦄ (h : k ⟶ l) (x : ↑(A.obj k)),
      (φ.app l (A.map h x) : ↑(B.obj l)) = B.map h (φ.app k x) := by
    intro k l h x
    simp
  let modA : ∀ k : Λ, Module ↑(A.obj k) ↑(N.obj k) :=
    fun k ↦ Module.compHom _ (φ.app k).hom
  have hsmulA : ∀ ⦃k l : Λ⦄ (h : k ⟶ l) (x : ↑(A.obj k)) (m : ↑(N.obj k)),
      N.map h (x • m) = A.map h x • N.map h m := by
    intro k l h x m
    change N.map h ((φ.app k x) • m) = (φ.app l (A.map h x)) • N.map h m
    rw [hsmul h ((φ.app k) x) m, hnat h x]
  have hνA : ∀ (k : Λ) (x : ↑(A.obj k)) (m : ↑(N.obj k)),
      (ν.app k (x • m) : M) = HSMul.hSMul (α := R) (β := M) (ρ.app k x) (ν.app k m) := by
    intro k x m
    change (ν.app k ((φ.app k x) • m) : M) = _
    rw [hν k ((φ.app k) x) m]
    have h2 : (σ.app k (φ.app k x) : S) = algebraMap R S (ρ.app k x) := by
      simpa using ConcreteCategory.congr_hom (hφ k) x
    rw [h2, algebraMap_smul]
  have hAnoeth : ∀ k : Λ, IsNoetherianRing ↑(A.obj k) := fun k ↦
    Algebra.EssFiniteType.isNoetherianRing ℤ ↑(A.obj k)
  have hBnoeth : ∀ k : Λ, IsNoetherianRing ↑(B.obj k) := by
    intro k
    let : Algebra ↑(A.obj k) ↑(B.obj k) := (φ.app k).hom.toAlgebra
    have : Algebra.EssFiniteType ↑(A.obj k) ↑(B.obj k) := hφft k
    have := hAnoeth k
    exact Algebra.EssFiniteType.isNoetherianRing ↑(A.obj k) ↑(B.obj k)
  have := hAlocal i
  have := hAnoeth i
  have := hBnoeth i
  set 𝔪 : Ideal ↑(A.obj i) := IsLocalRing.maximalIdeal ↑(A.obj i) with h𝔪
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing 𝔪)
  have hgmem : ∀ k, g k ∈ 𝔪 := fun k ↦ hg ▸ Submodule.subset_span ⟨k, rfl⟩
  set a : Fin n → ↥𝔪 := fun k ↦ ⟨g k, hgmem k⟩ with ha
  have hspan : Ideal.span (Set.range fun k ↦ (a k : ↑(A.obj i))) = 𝔪 := hg
  have := hNfin i
  set Ψ : (Fin n → ↑(N.obj i)) →ₗ[↑(B.obj i)] ↑(N.obj i) :=
    ∑ k, (LinearMap.lsmul ↑(B.obj i) ↑(N.obj i) ((φ.app i) (a k))).comp
      (LinearMap.proj k) with hΨ
  have hΨapply : ∀ v : Fin n → ↑(N.obj i),
      Ψ v = ∑ k, HSMul.hSMul (α := ↑(A.obj i)) (β := ↑(N.obj i)) (a k : ↑(A.obj i)) (v k) := by
    intro v
    rw [hΨ]
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.proj_apply, LinearMap.lsmul_apply]
    rfl
  obtain ⟨p, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker Ψ))
  have hwK : ∀ q, ∑ k, HSMul.hSMul (α := ↑(A.obj i)) (β := ↑(N.obj i))
      (a k : ↑(A.obj i)) (w q k) = 0 := fun q ↦ by
    rw [← hΨapply]
    exact (hw ▸ Submodule.subset_span ⟨q, rfl⟩ : w q ∈ LinearMap.ker Ψ)
  have hwspan : ∀ v : Fin n → ↑(N.obj i),
      (∑ k, HSMul.hSMul (α := ↑(A.obj i)) (β := ↑(N.obj i)) (a k : ↑(A.obj i)) (v k) = 0) →
      ∃ b : Fin p → ↑(B.obj i), ∀ k, v k = ∑ q, b q • w q k := by
    intro v hv
    have hvK : v ∈ LinearMap.ker Ψ := by rwa [LinearMap.mem_ker, hΨapply]
    rw [← hw] at hvK
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hvK
    exact ⟨b, fun k ↦ by simpa using (congrFun hb k).symm⟩
  have hcore : ∀ q : Fin p, ∃ (jq : Λ) (hq : i ⟶ jq),
      Module.IsTrivialRelation (fun k ↦ A.map hq (a k : ↑(A.obj i)))
        (fun k ↦ N.map hq (w q k)) :=
    fun q ↦ Module.exists_hom_isTrivialRelation_of_isColimit modA hsmulA hR hM hνA
      (fun k ↦ (a k : ↑(A.obj i))) (w q) (hwK q)
  choose jq hjq htrivq using hcore
  obtain ⟨j, hjbound⟩ := Preorder.exists_forall_le_of_fintype
    (fun s : Option (Fin p) ↦ s.elim i jq)
  have hij : i ≤ j := hjbound none
  have hjqj : ∀ q, jq q ≤ j := fun q ↦ hjbound (some q)
  set hh : i ⟶ j := homOfLE hij with hhh
  have htrivj : ∀ q, Module.IsTrivialRelation (fun k ↦ A.map hh (a k : ↑(A.obj i)))
      (fun k ↦ N.map hh (w q k)) := fun q ↦
    Module.IsTrivialRelation.mapOfSystem' modA hsmulA (hjq q) (homOfLE (hjqj q)) hh (htrivq q)
  let algAiBi : Algebra ↑(A.obj i) ↑(B.obj i) := (φ.app i).hom.toAlgebra
  let algAiAj : Algebra ↑(A.obj i) ↑(A.obj j) := (A.map hh).hom.toAlgebra
  let algBiBj : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map hh).hom.toAlgebra
  let algAjBj : Algebra ↑(A.obj j) ↑(B.obj j) := (φ.app j).hom.toAlgebra
  let algAiBj : Algebra ↑(A.obj i) ↑(B.obj j) :=
    ((B.map hh).hom.comp (φ.app i).hom).toAlgebra
  have towerBi : IsScalarTower ↑(A.obj i) ↑(B.obj i) ↑(B.obj j) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have towerAj : IsScalarTower ↑(A.obj i) ↑(A.obj j) ↑(B.obj j) :=
    .of_algebraMap_eq fun x ↦ (hnat hh x).symm
  let modBiNj : Module ↑(B.obj i) ↑(N.obj j) := Module.compHom _ (B.map hh).hom
  let modAjNj : Module ↑(A.obj j) ↑(N.obj j) := Module.compHom _ (φ.app j).hom
  let modAiNj : Module ↑(A.obj i) ↑(N.obj j) :=
    Module.compHom _ ((B.map hh).hom.comp (φ.app i).hom)
  have : IsScalarTower ↑(A.obj i) ↑(B.obj i) ↑(N.obj j) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower ↑(A.obj i) ↑(A.obj j) ↑(N.obj j) :=
    .of_algebraMap_smul fun x m ↦ congrArg (fun y : ↑(B.obj j) ↦ y • m) (hnat hh x)
  have : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(N.obj j) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower ↑(A.obj j) ↑(B.obj j) ↑(N.obj j) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower ↑(A.obj i) ↑(B.obj i) ↑(N.obj i) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let algTensor : Algebra (↑(B.obj i) ⊗[↑(A.obj i)] ↑(A.obj j)) ↑(B.obj j) :=
    (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ↑(A.obj i) ↑(B.obj i) ↑(B.obj j))
      (IsScalarTower.toAlgHom ↑(A.obj i) ↑(A.obj j) ↑(B.obj j))).toRingHom.toAlgebra
  have hprod : ∀ (b : ↑(B.obj i)) (x : ↑(A.obj j)),
      algebraMap (↑(B.obj i) ⊗[↑(A.obj i)] ↑(A.obj j)) ↑(B.obj j) (b ⊗ₜ[↑(A.obj i)] x)
        = algebraMap ↑(B.obj i) ↑(B.obj j) b * algebraMap ↑(A.obj j) ↑(B.obj j) x :=
    fun b x ↦ Algebra.TensorProduct.productMap_apply_tmul _ _ b x
  have : IsScalarTower ↑(B.obj i) (↑(B.obj i) ⊗[↑(A.obj i)] ↑(A.obj j)) ↑(B.obj j) :=
    .of_algebraMap_eq fun b ↦ by simpa using (hprod b 1).symm
  have hR'eq : (algebraMap (↑(B.obj i) ⊗[↑(A.obj i)] ↑(A.obj j)) ↑(B.obj j)).comp
      (Algebra.TensorProduct.includeRight :
        ↑(A.obj j) →ₐ[↑(A.obj i)] ↑(B.obj i) ⊗[↑(A.obj i)] ↑(A.obj j)).toRingHom
      = algebraMap ↑(A.obj j) ↑(B.obj j) :=
    RingHom.ext fun x ↦ by simpa using hprod 1 x
  obtain ⟨T, hT⟩ := CommRingCat.exists_isLocalization_tensorProduct_of_pushout
    (Ri := ↑(A.obj i)) (Si := ↑(B.obj i)) (Rj := ↑(A.obj j)) (Sj := ↑(B.obj j))
    (fun _ ↦ rfl) (φ.naturality hh).symm (hBloc hh)
  have := hT
  have := hAlocal j
  have := hBlocal j
  have := hAnoeth j
  have := hBnoeth j
  have := hAmaplocal hh
  have := hφlocal j
  have := IsLocalRing.maximalIdeal.isMaximal ↑(A.obj i)
  set f : ↑(N.obj i) →ₗ[↑(B.obj i)] ↑(N.obj j) := ⟨(N.map hh).hom.toAddHom, hsmul hh⟩ with hf
  have hflat : Module.Flat (↑(A.obj i) ⧸ 𝔪)
      (↑(N.obj i) ⧸ (𝔪 • (⊤ : Submodule ↑(A.obj i) ↑(N.obj i)))) := by
    let : Field (↑(A.obj i) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    infer_instance
  set α : Fin n → ↥(𝔪.map (algebraMap ↑(A.obj i) ↑(A.obj j))) :=
    fun k ↦ ⟨algebraMap ↑(A.obj i) ↑(A.obj j) (a k), Ideal.mem_map_of_mem _ (a k).2⟩ with hα
  set L := TensorProduct.lift
      (((TensorProduct.mk ↑(A.obj j) ↥(𝔪.map (algebraMap ↑(A.obj i) ↑(A.obj j)))
        ↑(N.obj j)).restrictScalars₁₂ ↑(A.obj i) ↑(A.obj i)).compl₁₂
        ((Algebra.linearMap ↑(A.obj i) ↑(A.obj j)).restrict (p := 𝔪)
          (q := (𝔪.map (algebraMap ↑(A.obj i) ↑(A.obj j))).restrictScalars ↑(A.obj i))
          fun _ hx ↦ Ideal.mem_map_of_mem _ hx)
        (f.restrictScalars ↑(A.obj i))) with hL
  have hΦ : ∀ (k : Fin n) (m : ↑(N.obj i)),
      L.toAddMonoidHom ((a k) ⊗ₜ[↑(A.obj i)] m) = (α k) ⊗ₜ[↑(A.obj j)] (f m) := by
    intro k m
    rw [hL]
    rfl
  have htor : LinearMap.ker (𝔪.subtype.rTensor ↑(N.obj i)) ≤ LinearMap.ker L := by
    intro t ht
    rw [LinearMap.mem_ker]
    exact Module.sum_tmul_eq_zero_of_mem_ker_rTensor (S' := ↑(B.obj j)) a hspan f α
      L.toAddMonoidHom hΦ w hwspan htrivj t ht
  exact ⟨j, hij, Module.Flat.of_flat_quotient_of_tor_one_map_eq_zero hR'eq T 𝔪
    (IsLocalRing.maximalIdeal.isMaximal ↑(A.obj i)).ne_top f (hNbc hh) hflat htor⟩

end Module.Flat
