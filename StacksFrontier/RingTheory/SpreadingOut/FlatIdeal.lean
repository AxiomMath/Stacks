module

public import StacksFrontier.RingTheory.SpreadingOut.Flat

/-!
# Flatness spreads out along a directed system, for an arbitrary ideal

Let `R → S` be a homomorphism of rings, `M` an `S`-module, and let `(A i → B i, N i)` be a directed
system spreading `(R → S, M)` out over `ℤ` in the sense of 00QX. Let `I ⊆ R` be a proper ideal and
`I_λ = ρ_λ^{-1}(I)` its inverse image at the stage `λ`. If every relation `∑ₖ pₖ xₖ = 0` with
`pₖ ∈ I` and `xₖ ∈ M` has `∑ₖ pₖ ⊗ xₖ = 0` in `I ⊗_R M` — the elementwise form of the injectivity
of `I ⊗_R M → R ⊗_R M` — and `N λ / I_λ N λ` is flat over `A λ / I_λ` for cofinally many `λ`, then
`N j` is flat over `A j` for some `j` above any prescribed index.

This is the analogue of `Module.Flat.exists_ge_flat_of_isColimit` (Stacks 00R6), the case
`I = 𝔪_R`, where flatness of `M` over `R` is assumed outright and the quotient flatness is
automatic because `A i/𝔪_i` is a field. It is not a consequence of 00R6
and does not imply it: 00R6's hypothesis is flatness, which is injectivity of `J ⊗_R M → M` for
*every* ideal `J`, while here it is asked for the single ideal `I` only.

## Main results

* `Module.Flat.exists_ge_flat_of_isColimit_of_rTensor_subtype_injective`: the statement above.

## Implementation notes

The system is spelled exactly as in 00R6, as the data and the conditions concluded by
`RingHom.EssentiallyOfFinitePresentation.exists_isColimit_essFiniteType_module`, minus the ones
that play no part here. Two of 00R6's hypotheses are dropped: the colimit cocone on `B` (`hS`),
which 00R6 does not use either, and locality of the transition maps `A i → A j`, which 00R6 needs
only to know that `𝔪_i A j` is a proper ideal of `A j` — here the ideal at the stage `j` is `I_j`,
proper because `I` is.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace Module.Flat

/-- Let `(A i → B i, N i)` be a directed system as in 00QX, with
colimits `R → S` and `M`: each `A i` is essentially of finite type over `ℤ`, each `A i → B i` is a
local homomorphism of local rings essentially of finite type, each `N i` is a finite `B i`-module,
each `B j` is a localization of `B i ⊗_{A i} A j` at a prime ideal, and each `N j` is the base
change of `N i` along `B i → B j`. Let `I ≠ R` be an ideal of `R` and write
`I_k = ρ_k^{-1}(I) ⊆ A k`. If every relation `∑ₖ pₖ xₖ = 0` with `pₖ ∈ I` and `xₖ ∈ M` has
`∑ₖ pₖ ⊗ xₖ = 0` in `I ⊗_R M` and `N k / I_k N k` is flat over
`A k / I_k` for cofinally many `k`, then for every index `i` there is `j ≥ i` such that `N j` is
flat over `A j`. -/
public theorem exists_ge_flat_of_isColimit_of_rTensor_subtype_injective
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A B : Λ ⥤ CommRingCat.{u}} {φ : A ⟶ B} {N : Λ ⥤ AddCommGrpCat.{u}}
    (mod : ∀ i, Module (B.obj i) (N.obj i))
    (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (b : B.obj i) (m : N.obj i),
      N.map h (b • m) = B.map h b • N.map h m)
    {ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R)}
    {σ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S)}
    {ν : N ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M)}
    (hR : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
    (hM : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν))
    (hφ : ∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom (algebraMap R S))
    (hν : ∀ (i : Λ) (b : B.obj i) (m : N.obj i),
      (ν.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M) (σ.app i b) (ν.app i m))
    (hAlocal : ∀ i, IsLocalRing (A.obj i)) (hBlocal : ∀ i, IsLocalRing (B.obj i))
    (hφlocal : ∀ i, IsLocalHom (φ.app i).hom)
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
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : ∀ {n : ℕ} (p : Fin n → ↥I) (u : Fin n → M),
      (∑ k, HSMul.hSMul (α := R) (β := M) (p k : R) (u k) = 0) →
      ∑ k, (p k) ⊗ₜ[R] (u k) = (0 : ↥I ⊗[R] M))
    (hQflat : ∀ k : Λ, ∃ m, k ≤ m ∧
      (letI : Module ↑(A.obj m) ↑(N.obj m) := Module.compHom _ (φ.app m).hom
       Module.Flat (↑(A.obj m) ⧸ I.comap (ρ.app m).hom)
         (↑(N.obj m) ⧸ ((I.comap (ρ.app m).hom) • (⊤ : Submodule ↑(A.obj m) ↑(N.obj m))))))
    (i₀ : Λ) :
    ∃ j, i₀ ≤ j ∧
      (letI : Module ↑(A.obj j) ↑(N.obj j) := Module.compHom _ (φ.app j).hom
       Module.Flat ↑(A.obj j) ↑(N.obj j)) := by
  obtain ⟨i, hi₀i, hQi⟩ := hQflat i₀
  have hnat : ∀ ⦃k l : Λ⦄ (h : k ⟶ l) (x : ↑(A.obj k)),
      (φ.app l (A.map h x) : ↑(B.obj l)) = B.map h (φ.app k x) := fun _ _ _ _ => by simp
  have hrho : ∀ ⦃k l : Λ⦄ (h : k ⟶ l) (x : ↑(A.obj k)), (ρ.app l (A.map h x) : R) = ρ.app k x :=
    fun _ _ _ _ => by simp
  let modA : ∀ k : Λ, Module ↑(A.obj k) ↑(N.obj k) :=
    fun k => Module.compHom _ (φ.app k).hom
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
  have hAnoeth : ∀ k : Λ, IsNoetherianRing ↑(A.obj k) := fun k =>
    Algebra.EssFiniteType.isNoetherianRing ℤ ↑(A.obj k)
  have hBnoeth : ∀ k : Λ, IsNoetherianRing ↑(B.obj k) := by
    intro k
    let : Algebra ↑(A.obj k) ↑(B.obj k) := (φ.app k).hom.toAlgebra
    have : Algebra.EssFiniteType ↑(A.obj k) ↑(B.obj k) := hφft k
    have := hAnoeth k
    exact Algebra.EssFiniteType.isNoetherianRing ↑(A.obj k) ↑(B.obj k)
  have hcomap_ne_top : ∀ k : Λ, I.comap (ρ.app k).hom ≠ ⊤ := by
    intro k hk
    refine hI (Ideal.eq_top_iff_one I |>.2 ?_)
    have h1 : (1 : ↑(A.obj k)) ∈ I.comap (ρ.app k).hom := by rw [hk]; exact Submodule.mem_top
    have := Ideal.mem_comap.mp h1
    rwa [map_one] at this
  have := hAnoeth i
  have := hBnoeth i
  set Ji : Ideal ↑(A.obj i) := I.comap (ρ.app i).hom with hJi
  obtain ⟨n, gen, hgen⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing Ji)
  have hgmem : ∀ k, gen k ∈ Ji := fun k => hgen ▸ Submodule.subset_span ⟨k, rfl⟩
  set a : Fin n → ↥Ji := fun k => ⟨gen k, hgmem k⟩ with ha
  have hspan : Ideal.span (Set.range fun k => (a k : ↑(A.obj i))) = Ji := hgen
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
  have hwmem : ∀ q, w q ∈ LinearMap.ker Ψ := fun q => hw ▸ Submodule.subset_span ⟨q, rfl⟩
  have hwK : ∀ q, ∑ k, HSMul.hSMul (α := ↑(A.obj i)) (β := ↑(N.obj i))
      (a k : ↑(A.obj i)) (w q k) = 0 := fun q => by rw [← hΨapply]; exact hwmem q
  have hwspan : ∀ v : Fin n → ↑(N.obj i),
      (∑ k, HSMul.hSMul (α := ↑(A.obj i)) (β := ↑(N.obj i)) (a k : ↑(A.obj i)) (v k) = 0) →
      ∃ b : Fin p → ↑(B.obj i), ∀ k, v k = ∑ q, b q • w q k := by
    intro v hv
    have hvK : v ∈ LinearMap.ker Ψ := by rw [LinearMap.mem_ker, hΨapply]; exact hv
    rw [← hw] at hvK
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hvK
    exact ⟨b, fun k => by simpa using (congrFun hb k).symm⟩
  have hmemI : ∀ k, ((ρ.app i (a k : ↑(A.obj i)) : R)) ∈ I := fun k => Ideal.mem_comap.mp (a k).2
  set P : Fin n → ↥I := fun k => ⟨(ρ.app i (a k : ↑(A.obj i)) : R), hmemI k⟩ with hP
  have hcore : ∀ q : Fin p, ∃ (jq : Λ) (hq : i ⟶ jq)
      (hmemq : ∀ k, A.map hq (a k : ↑(A.obj i)) ∈ I.comap (ρ.app jq).hom),
      ∑ k, (⟨A.map hq (a k : ↑(A.obj i)), hmemq k⟩ : ↥(I.comap (ρ.app jq).hom))
          ⊗ₜ[↑(A.obj jq)] (N.map hq (w q k))
        = (0 : ↥(I.comap (ρ.app jq).hom) ⊗[↑(A.obj jq)] ↑(N.obj jq)) := by
    intro q
    set U : Fin n → M := fun k => (ν.app i (w q k) : M) with hU
    have hrel : ∑ k, HSMul.hSMul (α := R) (β := M) ((P k : R)) (U k) = 0 := by
      have h0 : ∑ k, (ν.app i ((a k : ↑(A.obj i)) • w q k) : M) = 0 := by
        rw [← map_sum (ν.app i).hom, hwK q]
        exact map_zero (ν.app i).hom
      simpa only [hνA] using h0
    have hz0 : ∑ k, (P k) ⊗ₜ[R] (U k) = (0 : ↥I ⊗[R] M) := hTor P U hrel
    exact Ideal.exists_hom_tmul_eq_zero_of_isColimit modA hsmulA hR hM hνA I
      (fun k => (a k : ↑(A.obj i))) (w q) P (fun _ => rfl) U (fun _ => rfl) hz0
  choose jq hjq hmemq hvanq using hcore
  obtain ⟨j₀, hjbound⟩ := Preorder.exists_forall_le_of_fintype
    (fun s : Option (Fin p) => s.elim i jq)
  obtain ⟨j, hj₀j, hQj⟩ := hQflat j₀
  have hij : i ≤ j := (hjbound none).trans hj₀j
  have hjqj : ∀ q, jq q ≤ j := fun q => (hjbound (some q)).trans hj₀j
  set hh : i ⟶ j := homOfLE hij with hhh
  set Jj : Ideal ↑(A.obj j) := I.comap (ρ.app j).hom with hJj
  have hJ : ∀ x ∈ Ji, A.map hh x ∈ Jj := by
    intro x hx
    refine Ideal.mem_comap.mpr ?_
    rw [show ((ρ.app j).hom (A.map hh x)) = (ρ.app j (A.map hh x) : R) from rfl, hrho]
    exact Ideal.mem_comap.mp hx
  have hmemj : ∀ k, A.map hh (a k : ↑(A.obj i)) ∈ Jj := fun k => hJ _ (a k).2
  have hvanj : ∀ q, ∑ k, (⟨A.map hh (a k : ↑(A.obj i)), hmemj k⟩ : ↥Jj)
      ⊗ₜ[↑(A.obj j)] (N.map hh (w q k)) = (0 : ↥Jj ⊗[↑(A.obj j)] ↑(N.obj j)) := fun q =>
    Ideal.tmul_eq_zero_of_mapOfSystem modA hsmulA I (hjq q) (homOfLE (hjqj q)) hh
      (fun k => (a k : ↑(A.obj i))) (w q) (hmemq q) hmemj (hvanq q)
  let algAiBi : Algebra ↑(A.obj i) ↑(B.obj i) := (φ.app i).hom.toAlgebra
  let algAiAj : Algebra ↑(A.obj i) ↑(A.obj j) := (A.map hh).hom.toAlgebra
  let algBiBj : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map hh).hom.toAlgebra
  let algAjBj : Algebra ↑(A.obj j) ↑(B.obj j) := (φ.app j).hom.toAlgebra
  let algAiBj : Algebra ↑(A.obj i) ↑(B.obj j) :=
    ((B.map hh).hom.comp (φ.app i).hom).toAlgebra
  have towerBi : IsScalarTower ↑(A.obj i) ↑(B.obj i) ↑(B.obj j) :=
    .of_algebraMap_eq fun _ => rfl
  have towerAj : IsScalarTower ↑(A.obj i) ↑(A.obj j) ↑(B.obj j) :=
    .of_algebraMap_eq fun x => (hnat hh x).symm
  let modBiNj : Module ↑(B.obj i) ↑(N.obj j) := Module.compHom _ (B.map hh).hom
  let modAjNj : Module ↑(A.obj j) ↑(N.obj j) := Module.compHom _ (φ.app j).hom
  let modAiNj : Module ↑(A.obj i) ↑(N.obj j) :=
    Module.compHom _ ((B.map hh).hom.comp (φ.app i).hom)
  have : IsScalarTower ↑(A.obj i) ↑(B.obj i) ↑(N.obj j) :=
    .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower ↑(A.obj i) ↑(A.obj j) ↑(N.obj j) :=
    .of_algebraMap_smul fun x m => congrArg (fun y : ↑(B.obj j) => y • m) (hnat hh x)
  have : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(N.obj j) :=
    .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower ↑(A.obj j) ↑(B.obj j) ↑(N.obj j) :=
    .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower ↑(A.obj i) ↑(B.obj i) ↑(N.obj i) :=
    .of_algebraMap_smul fun _ _ => rfl
  let algTensor : Algebra (↑(B.obj i) ⊗[↑(A.obj i)] ↑(A.obj j)) ↑(B.obj j) :=
    (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ↑(A.obj i) ↑(B.obj i) ↑(B.obj j))
      (IsScalarTower.toAlgHom ↑(A.obj i) ↑(A.obj j) ↑(B.obj j))).toRingHom.toAlgebra
  have : IsScalarTower ↑(B.obj i) (↑(B.obj i) ⊗[↑(A.obj i)] ↑(A.obj j)) ↑(B.obj j) :=
    .of_algebraMap_eq fun b =>
      (Algebra.TensorProduct.productMap_left_apply
        (IsScalarTower.toAlgHom ↑(A.obj i) ↑(B.obj i) ↑(B.obj j))
        (IsScalarTower.toAlgHom ↑(A.obj i) ↑(A.obj j) ↑(B.obj j)) b).symm
  have hR'eq : (algebraMap (↑(B.obj i) ⊗[↑(A.obj i)] ↑(A.obj j)) ↑(B.obj j)).comp
      (Algebra.TensorProduct.includeRight :
        ↑(A.obj j) →ₐ[↑(A.obj i)] ↑(B.obj i) ⊗[↑(A.obj i)] ↑(A.obj j)).toRingHom
      = algebraMap ↑(A.obj j) ↑(B.obj j) :=
    RingHom.ext fun x =>
      Algebra.TensorProduct.productMap_right_apply
        (IsScalarTower.toAlgHom ↑(A.obj i) ↑(B.obj i) ↑(B.obj j))
        (IsScalarTower.toAlgHom ↑(A.obj i) ↑(A.obj j) ↑(B.obj j)) x
  obtain ⟨T, hT⟩ := CommRingCat.exists_isLocalization_tensorProduct_of_pushout
    (Ri := ↑(A.obj i)) (Si := ↑(B.obj i)) (Rj := ↑(A.obj j)) (Sj := ↑(B.obj j))
    (fun _ => rfl) (φ.naturality hh).symm (hBloc hh)
  have := hT
  have := hAlocal j
  have := hBlocal j
  have := hAnoeth j
  have := hBnoeth j
  have := hφlocal j
  set f : ↑(N.obj i) →ₗ[↑(B.obj i)] ↑(N.obj j) := ⟨(N.map hh).hom.toAddHom, hsmul hh⟩ with hf
  set α : Fin n → ↥Jj := fun k => ⟨A.map hh (a k : ↑(A.obj i)), hmemj k⟩ with hα
  set L := TensorProduct.lift
      (((TensorProduct.mk ↑(A.obj j) ↥Jj ↑(N.obj j)).restrictScalars₁₂ ↑(A.obj i)
        ↑(A.obj i)).compl₁₂
        ((Algebra.linearMap ↑(A.obj i) ↑(A.obj j)).restrict (p := Ji)
          (q := Jj.restrictScalars ↑(A.obj i)) hJ)
        (f.restrictScalars ↑(A.obj i))) with hL
  have hΦ : ∀ (k : Fin n) (m : ↑(N.obj i)),
      L.toAddMonoidHom ((a k) ⊗ₜ[↑(A.obj i)] m) = (α k) ⊗ₜ[↑(A.obj j)] (f m) := by
    intro k m
    rw [hL]
    rfl
  have htor : LinearMap.ker (Ji.subtype.rTensor ↑(N.obj i)) ≤ LinearMap.ker L := by
    intro t ht
    rw [LinearMap.mem_ker]
    exact Module.sum_tmul_eq_zero_of_mem_ker_rTensor' (S' := ↑(B.obj j)) a hspan f α
      L.toAddMonoidHom hΦ w hwspan (fun q => hvanj q) t ht
  exact ⟨j, hi₀i.trans hij, Module.Flat.of_flat_quotient_of_tor_one_map_eq_zero_of_mem hR'eq T Ji
    Jj hJ (hcomap_ne_top j) f (hNbc hh) hQi hQj htor⟩

end Module.Flat
