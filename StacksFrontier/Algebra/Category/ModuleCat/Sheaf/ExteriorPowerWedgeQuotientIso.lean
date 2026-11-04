module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerWedgeQuotient
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The wedge-quotient comparison for an invertible quotient is an isomorphism

Let `0 → E' → E → E'' → 0` be a short exact sequence of sheaves of modules on a ringed space
whose third term has stalks free of rank one. Then for every `r`

* `⋀ʳ⁺¹ E' ⟶ ⋀ʳ⁺¹ E` is a monomorphism, and
* the comparison `⋀ʳ E' ⊗ E'' ⟶ ⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'` of
  `Stacks.SheafOfModules.WedgeQuotient.wedgeQuotient` is an isomorphism,

so that `0 → ⋀ʳ⁺¹ E' → ⋀ʳ⁺¹ E → ⋀ʳ E' ⊗ E'' → 0` is short exact.

## Main results

* `Stacks.SheafOfModules.WedgeQuotient.mono_extPowMap`
* `Stacks.SheafOfModules.WedgeQuotient.isIso_wedgeQuotient`
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits CategoryTheory.Sheaf
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules.WedgeQuotient

/-! ### Module algebra -/

section Algebra

variable {R : Type u} [CommRing R] {M N P : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- A short exact sequence of modules whose third term is free of rank one splits, compatibly
with the inclusion of the first term and with the coordinate of the third. -/
theorem exists_prodEquiv_of_exact (ι : M →ₗ[R] N) (σ : N →ₗ[R] P) (hι : Function.Injective ι)
    (hσ : Function.Surjective σ) (hσι : ∀ m, σ (ι m) = 0) (hex : ∀ n, σ n = 0 → ∃ m, ι m = n)
    (b : Module.Basis (Fin 1) R P) :
    ∃ e : N ≃ₗ[R] M × R, (∀ m, e (ι m) = (m, 0)) ∧ ∀ n, (e n).2 = b.coord 0 (σ n) := by
  obtain ⟨t, ht⟩ := hσ (b 0)
  let φ : M × R →ₗ[R] N := ι.coprod (LinearMap.toSpanSingleton R N t)
  have hφ : ∀ p : M × R, φ p = ι p.1 + p.2 • t := fun p => rfl
  have hσφ : ∀ p : M × R, σ (φ p) = p.2 • b 0 := fun p => by
    rw [hφ, map_add, hσι, map_smul, ht, zero_add]
  have hcoord : ∀ p : M × R, b.coord 0 (σ (φ p)) = p.2 := fun p => by
    rw [hσφ, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul,
      Finsupp.single_eq_same, mul_one]
  have hinj : Function.Injective φ := by
    intro p q hpq
    have h2 : p.2 = q.2 := by rw [← hcoord p, ← hcoord q, hpq]
    rw [hφ, hφ, h2] at hpq
    exact Prod.ext (hι (add_right_cancel hpq)) h2
  have hsurj : Function.Surjective φ := by
    intro n
    obtain ⟨m, hm⟩ := hex (n - b.coord 0 (σ n) • t) (by
      rw [map_sub, map_smul, ht]
      have hb : σ n = b.coord 0 (σ n) • b 0 := by
        conv_lhs => rw [← b.sum_repr (σ n)]
        rw [Fin.sum_univ_one, Module.Basis.coord_apply]
      rw [← hb, sub_self])
    exact ⟨(m, b.coord 0 (σ n)), by rw [hφ, hm, sub_add_cancel]⟩
  let e := (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm
  have he : ∀ n, φ (e n) = n := fun n =>
    (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).apply_symm_apply n
  refine ⟨e, fun m => hinj ?_, fun n => ?_⟩
  · rw [he, hφ, zero_smul, add_zero]
  · conv_rhs => rw [← he n]
    rw [hcoord]

variable (e : N ≃ₗ[R] M × R)

/-- The second component of the splitting `⋀ʳ⁺¹ N ≅ ⋀ʳ⁺¹ M × ⋀ʳ M` induced by
`e : N ≅ M × R`. -/
noncomputable def wedgeSnd (r : ℕ) : ⋀[R]^(r + 1) N →ₗ[R] ⋀[R]^r M :=
  LinearMap.snd R _ _ ∘ₗ (exteriorPower.prodRightEquiv R M r).toLinearMap ∘ₗ
    (exteriorPowerCongr (r + 1) e).toLinearMap

variable {e} (ι : M →ₗ[R] N) (hιe : ∀ m, e (ι m) = (m, 0))
include hιe

/-- If `e ∘ ι` is the inclusion `M → M × R`, then the map induced by `e` on `⋀ᵏ` sends the image
of `z` under `⋀ᵏ ι` to its image under `⋀ᵏ` of the inclusion. -/
theorem exteriorPowerCongr_map (k : ℕ) (z : ⋀[R]^k M) :
    exteriorPowerCongr k e (exteriorPower.map k ι z) =
      exteriorPower.map k (LinearMap.inl R M R) z := by
  have hc : (e : N →ₗ[R] M × R) ∘ₗ ι = LinearMap.inl R M R := LinearMap.ext fun m => hιe m
  show exteriorPower.map k (e : N →ₗ[R] M × R) (exteriorPower.map k ι z) = _
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hc]

/-- The splitting `⋀ʳ⁺¹ N ≅ ⋀ʳ⁺¹ M × ⋀ʳ M` carries the image of `⋀ʳ⁺¹ ι` onto the first factor. -/
private theorem prodRightEquiv_exteriorPowerCongr_map (r : ℕ) (z : ⋀[R]^(r + 1) M) :
    exteriorPower.prodRightEquiv R M r
      (exteriorPowerCongr (r + 1) e (exteriorPower.map (r + 1) ι z)) = (z, 0) := by
  rw [exteriorPowerCongr_map ι hιe, exteriorPower.prodRightEquiv_map_inl]

/-- `wedgeSnd e r` vanishes on the image of `⋀ʳ⁺¹ ι`. -/
theorem wedgeSnd_map (r : ℕ) (z : ⋀[R]^(r + 1) M) :
    wedgeSnd e r (exteriorPower.map (r + 1) ι z) = 0 :=
  congrArg Prod.snd (prodRightEquiv_exteriorPowerCongr_map ι hιe r z)

/-- An element of `⋀ʳ⁺¹ N` in the kernel of `wedgeSnd e r` lies in the image of `⋀ʳ⁺¹ ι`. -/
theorem exists_map_of_wedgeSnd_eq_zero (r : ℕ) (w : ⋀[R]^(r + 1) N)
    (hw : wedgeSnd e r w = 0) : ∃ z, exteriorPower.map (r + 1) ι z = w := by
  refine ⟨(exteriorPower.prodRightEquiv R M r (exteriorPowerCongr (r + 1) e w)).1,
    (exteriorPowerCongr (r + 1) e).injective ((exteriorPower.prodRightEquiv R M r).injective ?_)⟩
  rw [prodRightEquiv_exteriorPowerCongr_map ι hιe]
  exact Prod.ext rfl hw.symm

/-- `wedgeSnd e r` sends `ι v₀ ∧ ⋯ ∧ ι vᵣ₋₁ ∧ n` to `(-1)ʳ` times the second coordinate of
`e n` times `v₀ ∧ ⋯ ∧ vᵣ₋₁`. -/
theorem wedgeSnd_ιMulti_snoc (r : ℕ) (v : Fin r → M) (n : N) :
    wedgeSnd e r (exteriorPower.ιMulti R (r + 1) (Fin.snoc (fun i => ι (v i)) n)) =
      (-1 : ℤ) ^ r • (e n).2 • exteriorPower.ιMulti R r v := by
  show exteriorPower.map r (LinearMap.fst R M R)
      (exteriorPower.contraction (LinearMap.snd R M R) r
        (exteriorPower.map (r + 1) (e : N →ₗ[R] M × R)
          (exteriorPower.ιMulti R (r + 1) (Fin.snoc (fun i => ι (v i)) n)))) = _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.contraction_ιMulti, map_sum,
    Finset.sum_eq_single (Fin.last r)]
  · have hrem : (Fin.last r).removeNth ((e : N →ₗ[R] M × R) ∘ Fin.snoc (fun i => ι (v i)) n) =
        fun i => (v i, (0 : R)) := by
      funext i
      rw [Fin.removeNth_last]
      simp [Fin.init, hιe]
    rw [hrem, map_zsmul, map_smul, exteriorPower.map_apply_ιMulti]
    simp only [Function.comp_apply, Fin.snoc_last, Fin.val_last, LinearMap.snd_apply]
    rfl
  · intro i _ hi
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
    simp [hιe]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Algebra

section Abstract

variable {R : Type u} [CommRing R] {T₁ T₂ Q C V Z : Type u} [AddCommGroup T₁] [Module R T₁]
  [AddCommGroup T₂] [Module R T₂] [AddCommGroup Q] [Module R Q] [AddCommGroup C] [Module R C]
  [AddCommGroup V] [Module R V] [AddCommGroup Z] [Module R Z]

/-- A map `Φ : T₂ → C` out of the target of a surjection `G : T₁ → T₂` is bijective when
`Φ ∘ G = π ∘ W` for a surjection `π : Q → C` whose kernel is the image of `I`, and the composite
of `W` with a map `P : Q → V` whose kernel is also the image of `I` is a unit multiple of an
isomorphism `τ : T₂ ≅ V` composed with `G`. -/
theorem bijective_of_comp_eq (G : T₁ →ₗ[R] T₂) (W : T₁ →ₗ[R] Q) (π : Q →ₗ[R] C)
    (Φ : T₂ →ₗ[R] C) (I : Z →ₗ[R] Q) (P : Q →ₗ[R] V) (τ : T₂ ≃ₗ[R] V) (c : ℤ) (hc : c * c = 1)
    (hcomm : ∀ t, Φ (G t) = π (W t)) (hπ : Function.Surjective π)
    (hπker : ∀ w, π w = 0 → ∃ z, I z = w) (hπI : ∀ z, π (I z) = 0)
    (hPI : ∀ z, P (I z) = 0) (hPker : ∀ w, P w = 0 → ∃ z, I z = w)
    (hPW : ∀ t, P (W t) = c • τ (G t)) (hG : Function.Surjective G) :
    Function.Bijective Φ := by
  have hcc : ∀ v : V, c • c • v = v := fun v => by rw [smul_smul, hc, one_smul]
  refine ⟨?_, fun y => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ξ hξ
    obtain ⟨η, rfl⟩ := hG ξ
    obtain ⟨z, hz⟩ := hπker (W η) (by rw [← hcomm, hξ])
    have h0 : c • τ (G η) = 0 := by rw [← hPW, ← hz, hPI]
    have h1 : τ (G η) = 0 := by rw [← hcc (τ (G η)), h0, smul_zero]
    exact τ.injective (h1.trans τ.map_zero.symm)
  · obtain ⟨w, rfl⟩ := hπ y
    obtain ⟨η, hη⟩ := hG (τ.symm (c • P w))
    obtain ⟨z, hz⟩ := hPker (W η - w) (by
      rw [map_sub, hPW, hη, LinearEquiv.apply_symm_apply, hcc, sub_self])
    refine ⟨τ.symm (c • P w), ?_⟩
    rw [← hη, hcomm]
    have := congrArg π hz
    rw [hπI, map_sub] at this
    exact (sub_eq_zero.mp this.symm)

end Abstract

/-! ### The sheaf statements -/

section Sheaf

open Stacks.SheafOfModules.TopWedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0) (hS : (ShortComplex.mk f g hfg).Exact)
  [Mono f] [Epi g]
  (hb : ∀ x : ↥X, Nonempty (Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
    ↑(TopCat.Presheaf.stalk E''.val.presheaf x)))

include hS hb in
/-- At every point the stalk of `E` splits as the stalk of `E'` times the stalk ring, compatibly
with the stalk of `f` and with the coordinate of the stalk of `g`. -/
theorem exists_stalkProdEquiv (x : ↥X) :
    ∃ (b : Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E''.val.presheaf x))
      (e : ↑(TopCat.Presheaf.stalk E.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
        ↑(TopCat.Presheaf.stalk E'.val.presheaf x) × ↑(TopCat.Presheaf.stalk Osharp.obj x)),
      (∀ m, e (PresheafOfModules.stalkMapL x f.val m) = (m, 0)) ∧
        ∀ n, (e n).2 = b.coord 0 (PresheafOfModules.stalkMapL x g.val n) := by
  obtain ⟨b⟩ := hb x
  obtain ⟨hinj, hsurj, hex⟩ := stalkMapL_shortExact f g hfg hS x
  obtain ⟨e, he1, he2⟩ := exists_prodEquiv_of_exact (PresheafOfModules.stalkMapL x f.val)
    (PresheafOfModules.stalkMapL x g.val) hinj hsurj
    (fun m => LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self _ m))
    (fun n hn => LinearMap.mem_range.mp (hex.symm ▸ LinearMap.mem_ker.mpr hn)) b
  exact ⟨b, e, he1, he2⟩

include hS hb in
/-- **`⋀ʳ E' ⟶ ⋀ʳ E` is a monomorphism**, the stalk of `f` being split injective. -/
theorem mono_extPowMap (r : ℕ) : Mono (extPowMap A' A f r) := by
  refine _root_.SheafOfModules.mono_pieceMap_of_stalkMapL_retraction A'.exteriorGenerator
    A.exteriorGenerator A'.exterior_isExteriorAlgebra A.exterior_isExteriorAlgebra f r
    fun x => ?_
  obtain ⟨_, e, he1, _⟩ := exists_stalkProdEquiv f g hfg hS hb x
  exact ⟨LinearMap.fst _ _ _ ∘ₗ e.toLinearMap, LinearMap.ext fun m => by
    simp [he1]⟩

omit [Mono f] [Epi g] in
/-- Two linear maps out of the stalk of `⋀ʳ E' ⊗ M` agree as soon as they agree on the germs of
the pure tensors of a wedge of local sections of `E'` with a local section of `M`. -/
theorem stalk_tensor_ext (r : ℕ) (x : ↥X)
    {M : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    {V : Type u} [AddCommGroup V] [Module ↑(TopCat.Presheaf.stalk Osharp.obj x) V]
    (φ ψ : ↑(TopCat.Presheaf.stalk
        (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r) M).presheaf x)
      →ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)] V)
    (h : ∀ (U : Opens ↥X) (hx : x ∈ U) (s : Fin r → E'.val.obj (op U)) (m : M.val.obj (op U)),
      φ (PresheafOfModules.tensorSheafGerm Osharp (A'.exteriorPower r) M x U hx
          (A'.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) r
            fun i => A'.exteriorGenerator.val.app (op U) (s i)) m) =
        ψ (PresheafOfModules.tensorSheafGerm Osharp (A'.exteriorPower r) M x U hx
          (A'.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) r
            fun i => A'.exteriorGenerator.val.app (op U) (s i)) m)) :
    φ = ψ := by
  set eT := PresheafOfModules.tensorSheafStalkEquiv Osharp (A'.exteriorPower r) M x
  have key : φ ∘ₗ eT.symm.toLinearMap = ψ ∘ₗ eT.symm.toLinearMap := by
    refine TensorProduct.linearMap_ext_of_span₂
      (_root_.SheafOfModules.span_germWedgeSet_eq_top A' r x) Submodule.span_univ _ _ ?_
    rintro _ ⟨U, hxU, s, rfl⟩ n -
    obtain ⟨V', hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf n
    have hxW : x ∈ U ⊓ V' := ⟨hxU, hxV⟩
    rw [_root_.SheafOfModules.germ_homogeneousProd_res A' r x (inf_le_left : U ⊓ V' ≤ U) hxU hxW s,
      ← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE (inf_le_right : U ⊓ V' ≤ V')) x
        hxW m]
    have key2 := PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp
      (A'.exteriorPower r) M x (U ⊓ V') hxW
      (A'.exterior.toPresheafGradedAlgebra.homogeneousProd (op (U ⊓ V')) r fun i =>
        A'.exteriorGenerator.val.app (op (U ⊓ V'))
          (E'.val.map (homOfLE (inf_le_left : U ⊓ V' ≤ U)).op (s i)))
      (M.val.presheaf.map (homOfLE (inf_le_right : U ⊓ V' ≤ V')).op m)
    refine (congrArg (φ ∘ₗ eT.symm.toLinearMap) key2.symm).trans ?_
    refine Eq.trans ?_ (congrArg (ψ ∘ₗ eT.symm.toLinearMap) key2)
    exact (congrArg φ (eT.symm_apply_apply _)).trans
      ((h _ hxW _ _).trans (congrArg ψ (eT.symm_apply_apply _)).symm)
  ext z
  simpa using LinearMap.congr_fun key (eT z)

omit [Mono f] [Epi g] in
/-- The stalk of `⋀ʳ E' ⊗ h` on the germ of a pure tensor. -/
theorem stalkMapL_tensorLeftMap_germ (r : ℕ) (x : ↥X)
    {M M' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (h : M ⟶ M') (U : Opens ↥X) (hx : x ∈ U) (ω : (A'.exteriorPower r).val.obj (op U))
    (m : M.val.obj (op U)) :
    PresheafOfModules.stalkMapL x (((Tensor.sheafTensor Osharp).obj (A'.exteriorPower r)).map h).val
        (PresheafOfModules.tensorSheafGerm Osharp (A'.exteriorPower r) M x U hx ω m) =
      PresheafOfModules.tensorSheafGerm Osharp (A'.exteriorPower r) M' x U hx ω
        (h.val.app (op U) m) := by
  refine (PresheafOfModules.stalkMapL_germ x (((Tensor.sheafTensor Osharp).obj
      (A'.exteriorPower r)).map h).val U hx _).trans ?_
  have mapUnit :=
    Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit Osharp _ _
      (𝟙 (A'.exteriorPower r)) h (op U) ω m
  have hid : ((Tensor.sheafTensor Osharp).map (𝟙 (A'.exteriorPower r))).app M = 𝟙 _ :=
    NatTrans.congr_app ((Tensor.sheafTensor Osharp).map_id _) _
  rw [hid, Category.id_comp] at mapUnit
  exact congrArg (fun y => TopCat.Presheaf.germ
      (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r) M').presheaf U x hx y)
    mapUnit

omit [Mono f] [Epi g] in
/-- The stalk of the wedge map `⋀ʳ E' ⊗ E ⟶ ⋀ʳ⁺¹ E` on the germ of a pure tensor of a wedge of
local sections with a local section, read through `exteriorPowerStalkEquiv`. -/
theorem exteriorPowerStalkEquiv_stalkMapL_wedge_germ (r : ℕ) (x : ↥X) (U : Opens ↥X)
    (hx : x ∈ U) (s : Fin r → E'.val.obj (op U)) (m : E.val.obj (op U)) :
    A.exteriorPowerStalkEquiv (r + 1) x
        (PresheafOfModules.stalkMapL x
          (((Tensor.sheafTensor Osharp).obj
              (A'.exteriorPower r)).map A.exteriorGenerator ≫ wedgeHom A' A f r 1).val
          (PresheafOfModules.tensorSheafGerm Osharp (A'.exteriorPower r) E x U hx
            (A'.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) r
              fun i => A'.exteriorGenerator.val.app (op U) (s i)) m)) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r + 1)
        (Fin.snoc (α := fun _ : Fin (r + 1) => ↑(TopCat.Presheaf.stalk E.val.presheaf x))
          (fun i => PresheafOfModules.stalkMapL x f.val
          (TopCat.Presheaf.germ E'.val.presheaf U x hx (s i)))
          (TopCat.Presheaf.germ E.val.presheaf U x hx m)) := by
  set ω := A'.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) r
    fun i => A'.exteriorGenerator.val.app (op U) (s i) with hω
  have ha := (LinearMap.congr_fun (_root_.SheafOfModules.stalkMapL_comp_of_comp_eq_comp x
    (((Tensor.sheafTensor Osharp).obj
        (A'.exteriorPower r)).map A.exteriorGenerator) (wedgeHom A' A f r 1) _ rfl)
    (PresheafOfModules.tensorSheafGerm Osharp (A'.exteriorPower r) E x U hx ω m)).symm
  have hb := stalkMapL_tensorLeftMap_germ A' r x A.exteriorGenerator U hx ω m
  have hc := PresheafOfModules.stalkMapL_germ x (wedgeHom A' A f r 1).val U hx
    ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r) (A.exteriorPower 1)).app (op U)
      (ω ⊗ₜ A.exteriorGenerator.val.app (op U) m))
  have hd := wedgeHom_unit A' A f r 1 (op U) ω (A.exteriorGenerator.val.app (op U) m)
  have he := SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd_comp (extHom A' A f) f
    (A'.exterior_isExteriorAlgebra.map_app_one A.exterior_isExteriorAlgebra f) (op U) r s
  have hprod : (A.exterior.mul (r : ℤ) 1).app (op U)
      (A.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) r
        fun i => A.exteriorGenerator.val.app (op U) (f.val.app (op U) (s i)))
      (A.exteriorGenerator.val.app (op U) m) =
      A.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) (r + 1)
        fun i => A.exteriorGenerator.val.app (op U)
          (Fin.snoc (α := fun _ : Fin (r + 1) => ↑(E.val.obj (op U)))
            (fun j => f.val.app (op U) (s j)) m i) := by
    show _ = (A.exterior.mul (r : ℤ) 1).app (op U)
      (A.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) r fun i =>
        A.exteriorGenerator.val.app (op U)
          (Fin.snoc (α := fun _ : Fin (r + 1) => ↑(E.val.obj (op U)))
            (fun j => f.val.app (op U) (s j)) m i.castSucc))
      (A.exteriorGenerator.val.app (op U)
        (Fin.snoc (α := fun _ : Fin (r + 1) => ↑(E.val.obj (op U)))
          (fun j => f.val.app (op U) (s j)) m (Fin.last r)))
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hg := _root_.SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd A.exterior
    A.exteriorGenerator A.exterior_isExteriorAlgebra (r + 1) x U hx
    (Fin.snoc (α := fun _ : Fin (r + 1) => ↑(E.val.obj (op U))) (fun j => f.val.app (op U) (s j)) m)
  refine (congrArg (A.exteriorPowerStalkEquiv (r + 1) x)
    (ha.trans ((congrArg (PresheafOfModules.stalkMapL x (wedgeHom A' A f r 1).val) hb).trans
      (hc.trans (congrArg (TopCat.Presheaf.germ (A.exteriorPower (r + 1)).val.presheaf U x hx)
        (hd.trans ((congrArg (fun y => (A.exterior.mul (r : ℤ) 1).app (op U) y
          (A.exteriorGenerator.val.app (op U) m)) he).trans hprod))))))).trans ?_
  refine hg.trans ?_
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]
    exact (PresheafOfModules.stalkMapL_germ x f.val U hx (s j)).symm

omit [Mono f] [Epi g] in
/-- The stalk of `⋀ʳ E' ⊗ E''` is `⋀ʳ` of the stalk of `E'`, through a basis of the stalk of
`E''` of cardinality one. -/
noncomputable def tensorStalkCoord (r : ℕ) (x : ↥X)
    (b : Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E''.val.presheaf x)) :
    ↑(TopCat.Presheaf.stalk
        (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r) E'').presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^r ↑(TopCat.Presheaf.stalk E'.val.presheaf x) :=
  (PresheafOfModules.tensorSheafStalkEquiv Osharp (A'.exteriorPower r) E'' x).trans
    ((TensorProduct.congr (A'.exteriorPowerStalkEquiv r x)
      (b.equivFun.trans (LinearEquiv.funUnique (Fin 1) _ _))).trans
      (TensorProduct.rid _ _))

omit [Mono f] [Epi g] in
/-- `tensorStalkCoord` sends the germ of `ω ⊗ ℓ` to the coordinate in `b` of the germ of `ℓ`
times the image of the germ of `ω` in `⋀ʳ` of the stalk of `E'`. -/
theorem tensorStalkCoord_germ (r : ℕ) (x : ↥X)
    (b : Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E''.val.presheaf x))
    (U : Opens ↥X) (hx : x ∈ U) (ω : (A'.exteriorPower r).val.obj (op U))
    (ℓ : E''.val.obj (op U)) :
    tensorStalkCoord A' r x b
        (PresheafOfModules.tensorSheafGerm Osharp (A'.exteriorPower r) E'' x U hx ω ℓ) =
      b.coord 0 (TopCat.Presheaf.germ E''.val.presheaf U x hx ℓ) •
        A'.exteriorPowerStalkEquiv r x
          (TopCat.Presheaf.germ (A'.exteriorPower r).val.presheaf U x hx ω) := by
  refine (congrArg (fun z => TensorProduct.rid _ _ (TensorProduct.congr
      (A'.exteriorPowerStalkEquiv r x) (b.equivFun.trans (LinearEquiv.funUnique (Fin 1) _ _)) z))
    (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp (A'.exteriorPower r) E'' x U
      hx ω ℓ)).trans ?_
  exact (congrArg (TensorProduct.rid _ _) (TensorProduct.congr_tmul _ _ _ _)).trans
    (TensorProduct.rid_tmul _ _)

omit [Mono f] in
/-- On stalks, `⋀ʳ E' ⊗ g` followed by `wedgeQuotient` equals the wedge map
`⋀ʳ E' ⊗ E ⟶ ⋀ʳ⁺¹ E` followed by the projection onto `⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'`. -/
theorem stalkMapL_wedgeQuotient_tensorLeftMap (r : ℕ) (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r) E).presheaf x)) :
    PresheafOfModules.stalkMapL x (wedgeQuotient A' A f g hfg hS r).val
        (PresheafOfModules.stalkMapL x (((Tensor.sheafTensor Osharp).obj
            (A'.exteriorPower r)).map g).val t) =
      PresheafOfModules.stalkMapL x (cokernel.π (extPowMap A' A f (r + 1))).val
        (PresheafOfModules.stalkMapL x
          (((Tensor.sheafTensor Osharp).obj
              (A'.exteriorPower r)).map A.exteriorGenerator ≫ wedgeHom A' A f r 1).val t) := by
  have hcomp : ((Tensor.sheafTensor Osharp).obj
      (A'.exteriorPower r)).map g ≫ wedgeQuotient A' A f g hfg hS r =
      (((Tensor.sheafTensor Osharp).obj
          (A'.exteriorPower r)).map A.exteriorGenerator ≫ wedgeHom A' A f r 1) ≫
        cokernel.π (extPowMap A' A f (r + 1)) :=
    (tensorLeftMap_comp_wedgeQuotient A' A f g hfg hS r).trans (Category.assoc _ _ _).symm
  exact (LinearMap.congr_fun (_root_.SheafOfModules.stalkMapL_comp_of_comp_eq_comp x _ _ _
    hcomp) t).trans (LinearMap.congr_fun (_root_.SheafOfModules.stalkMapL_comp_of_comp_eq_comp x
      _ _ _ rfl) t).symm

omit [Mono f] [Epi g] in
/-- On the stalk at `x`, `wedgeSnd e r` vanishes on the image of `⋀ʳ⁺¹ E' ⟶ ⋀ʳ⁺¹ E`. -/
theorem wedgeSnd_stalkMapL_extPowMap (r : ℕ) (x : ↥X)
    {e : ↑(TopCat.Presheaf.stalk E.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk E'.val.presheaf x) × ↑(TopCat.Presheaf.stalk Osharp.obj x)}
    (he1 : ∀ m, e (PresheafOfModules.stalkMapL x f.val m) = (m, 0))
    (z : ↑(TopCat.Presheaf.stalk (A'.exteriorPower (r + 1)).val.presheaf x)) :
    wedgeSnd e r (A.exteriorPowerStalkEquiv (r + 1) x
      (PresheafOfModules.stalkMapL x (extPowMap A' A f (r + 1)).val z)) = 0 := by
  have h := _root_.SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_pieceMap A'.exteriorGenerator
    A.exteriorGenerator A'.exterior_isExteriorAlgebra A.exterior_isExteriorAlgebra f (r + 1) x z
  exact (congrArg (wedgeSnd e r) h).trans (wedgeSnd_map _ he1 r _)

omit [Mono f] [Epi g] in
/-- On the stalk at `x`, an element of `⋀ʳ⁺¹ E` in the kernel of `wedgeSnd e r` lies in the image
of `⋀ʳ⁺¹ E' ⟶ ⋀ʳ⁺¹ E`. -/
theorem exists_stalkMapL_extPowMap_of_wedgeSnd (r : ℕ) (x : ↥X)
    {e : ↑(TopCat.Presheaf.stalk E.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk E'.val.presheaf x) × ↑(TopCat.Presheaf.stalk Osharp.obj x)}
    (he1 : ∀ m, e (PresheafOfModules.stalkMapL x f.val m) = (m, 0))
    (w : ↑(TopCat.Presheaf.stalk (A.exteriorPower (r + 1)).val.presheaf x))
    (hw : wedgeSnd e r (A.exteriorPowerStalkEquiv (r + 1) x w) = 0) :
    ∃ z, PresheafOfModules.stalkMapL x (extPowMap A' A f (r + 1)).val z = w := by
  obtain ⟨z₀, hz₀⟩ := exists_map_of_wedgeSnd_eq_zero _ he1 r _ hw
  exact ⟨(A'.exteriorPowerStalkEquiv (r + 1) x).symm z₀,
    (A.exteriorPowerStalkEquiv (r + 1) x).injective
      ((_root_.SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_pieceMap_symm
        A'.exteriorGenerator A.exteriorGenerator A'.exterior_isExteriorAlgebra
        A.exterior_isExteriorAlgebra f (r + 1) x z₀).trans hz₀)⟩

omit [Mono f] [Epi g] in
/-- On the stalk at `x`, `wedgeSnd e r` composed with the wedge map `⋀ʳ E' ⊗ E ⟶ ⋀ʳ⁺¹ E` is
`(-1)ʳ` times `tensorStalkCoord` composed with `⋀ʳ E' ⊗ g`. -/
theorem wedgeSnd_stalkMapL_wedge (r : ℕ) (x : ↥X)
    (b : Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E''.val.presheaf x))
    {e : ↑(TopCat.Presheaf.stalk E.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk E'.val.presheaf x) × ↑(TopCat.Presheaf.stalk Osharp.obj x)}
    (he1 : ∀ m, e (PresheafOfModules.stalkMapL x f.val m) = (m, 0))
    (he2 : ∀ n, (e n).2 = b.coord 0 (PresheafOfModules.stalkMapL x g.val n))
    (t : ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r) E).presheaf x)) :
    wedgeSnd e r (A.exteriorPowerStalkEquiv (r + 1) x (PresheafOfModules.stalkMapL x
        (((Tensor.sheafTensor Osharp).obj
            (A'.exteriorPower r)).map A.exteriorGenerator ≫ wedgeHom A' A f r 1).val t)) =
      (-1 : ℤ) ^ r • tensorStalkCoord A' r x b
        (PresheafOfModules.stalkMapL x (((Tensor.sheafTensor Osharp).obj
            (A'.exteriorPower r)).map g).val t) := by
  refine LinearMap.congr_fun (stalk_tensor_ext A' r x
    ((wedgeSnd e r ∘ₗ (A.exteriorPowerStalkEquiv (r + 1) x).toLinearMap) ∘ₗ
      PresheafOfModules.stalkMapL x
        (((Tensor.sheafTensor Osharp).obj
            (A'.exteriorPower r)).map A.exteriorGenerator ≫ wedgeHom A' A f r 1).val)
    (((-1 : ℤ) ^ r) • ((tensorStalkCoord A' r x b).toLinearMap ∘ₗ
      PresheafOfModules.stalkMapL x (((Tensor.sheafTensor Osharp).obj
          (A'.exteriorPower r)).map g).val))
    fun U hx s m => ?_) t
  have h1 := exteriorPowerStalkEquiv_stalkMapL_wedge_germ A' A f r x U hx s m
  have h2 := wedgeSnd_ιMulti_snoc (PresheafOfModules.stalkMapL x f.val)
    he1 r (fun i => TopCat.Presheaf.germ E'.val.presheaf U x hx (s i))
    (TopCat.Presheaf.germ E.val.presheaf U x hx m)
  have h3 := stalkMapL_tensorLeftMap_germ A' r x g U hx
    (A'.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) r
      fun i => A'.exteriorGenerator.val.app (op U) (s i)) m
  have h4 := tensorStalkCoord_germ A' r x b U hx
    (A'.exterior.toPresheafGradedAlgebra.homogeneousProd (op U) r
      fun i => A'.exteriorGenerator.val.app (op U) (s i)) (g.val.app (op U) m)
  have h5 := _root_.SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd A'.exterior
    A'.exteriorGenerator A'.exterior_isExteriorAlgebra r x U hx s
  have hL2 : (e (TopCat.Presheaf.germ E.val.presheaf U x hx m)).2 =
      b.coord 0 (TopCat.Presheaf.germ E''.val.presheaf U x hx (g.val.app (op U) m)) :=
    (he2 _).trans (congrArg (b.coord 0) (PresheafOfModules.stalkMapL_germ x g.val U hx m))
  have hR := congrArg (fun y => (-1 : ℤ) ^ r • y)
    ((congrArg (tensorStalkCoord A' r x b) h3).trans (h4.trans (congrArg (fun y =>
      b.coord 0 (TopCat.Presheaf.germ E''.val.presheaf U x hx (g.val.app (op U) m)) • y) h5)))
  have hL := (congrArg (wedgeSnd e r) h1).trans (h2.trans (congrArg (fun c => (-1 : ℤ) ^ r • c •
    exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) r
      (fun i => TopCat.Presheaf.germ E'.val.presheaf U x hx (s i))) hL2))
  exact hL.trans hR.symm

omit [Mono f] in
include hS in
/-- The stalk of `⋀ʳ E' ⊗ g : ⋀ʳ E' ⊗ E ⟶ ⋀ʳ E' ⊗ E''` is surjective. -/
theorem surjective_stalkMapL_tensorLeftMap (r : ℕ) (x : ↥X) :
    Function.Surjective (PresheafOfModules.stalkMapL x (((Tensor.sheafTensor Osharp).obj
        (A'.exteriorPower r)).map g).val) := by
  have hepi : Epi (((Tensor.sheafTensor Osharp).obj (A'.exteriorPower r)).map g) :=
    Limits.epi_of_isColimit_cofork (tensorCokernelIsColimit A' f g hfg hS r)
  intro y
  obtain ⟨z, hz⟩ := (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap _).mp hepi x y
  exact ⟨z, (stalkMap_hom_apply _ x z).symm.trans hz⟩

include hb in
/-- **The comparison `⋀ʳ E' ⊗ E'' ⟶ ⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'` is bijective on stalks.** -/
theorem bijective_stalkMapL_wedgeQuotient (r : ℕ) (x : ↥X) :
    Function.Bijective (PresheafOfModules.stalkMapL x (wedgeQuotient A' A f g hfg hS r).val) := by
  obtain ⟨b, e, he1, he2⟩ := exists_stalkProdEquiv f g hfg hS hb x
  have hmono := mono_extPowMap A' A f g hfg hS hb (r + 1)
  exact bijective_of_comp_eq (T₁ := ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r) E).presheaf x))
    (T₂ := ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r) E'').presheaf x))
    (PresheafOfModules.stalkMapL x (((Tensor.sheafTensor Osharp).obj
        (A'.exteriorPower r)).map g).val)
    (PresheafOfModules.stalkMapL x
      (((Tensor.sheafTensor Osharp).obj
          (A'.exteriorPower r)).map A.exteriorGenerator ≫ wedgeHom A' A f r 1).val)
    (PresheafOfModules.stalkMapL x (cokernel.π (extPowMap A' A f (r + 1))).val)
    (PresheafOfModules.stalkMapL x (wedgeQuotient A' A f g hfg hS r).val)
    (PresheafOfModules.stalkMapL x (extPowMap A' A f (r + 1)).val)
    (wedgeSnd e r ∘ₗ (A.exteriorPowerStalkEquiv (r + 1) x).toLinearMap)
    (tensorStalkCoord A' r x b) ((-1) ^ r)
    (by rw [← mul_pow, neg_one_mul, neg_neg, one_pow])
    (stalkMapL_wedgeQuotient_tensorLeftMap A' A f g hfg hS r x)
    (Stacks.AlgebraicGeometry.ProjEulerSequence.surjective_stalkMapL_cokernelπ _ x hmono)
    (fun w hw =>
      Stacks.AlgebraicGeometry.ProjEulerSequence.exists_stalkMapL_eq_of_stalkMapL_cokernelπ_eq_zero
        _ x hmono w hw)
    (fun z => Stacks.AlgebraicGeometry.ProjEulerSequence.stalkMapL_cokernelπ_stalkMapL _ x z)
    (wedgeSnd_stalkMapL_extPowMap A' A f r x he1)
    (exists_stalkMapL_extPowMap_of_wedgeSnd A' A f r x he1)
    (wedgeSnd_stalkMapL_wedge A' A f g r x b he1 he2)
    (surjective_stalkMapL_tensorLeftMap A' f g hfg hS r x)

include hb in
/-- **The comparison `⋀ʳ E' ⊗ E'' ⟶ ⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'` is an isomorphism** for a short exact
sequence `0 → E' → E → E'' → 0` of sheaves of modules whose third term has stalks free of rank
one. -/
theorem isIso_wedgeQuotient (r : ℕ) : IsIso (wedgeQuotient A' A f g hfg hS r) := by
  rw [AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap]
  intro x
  obtain ⟨hinj, hsurj⟩ := bijective_stalkMapL_wedgeQuotient A' A f g hfg hS hb r x
  refine ⟨fun a c hac => ?_, fun ζ => ?_⟩
  · exact hinj ((stalkMap_hom_apply _ x a).symm.trans (hac.trans (stalkMap_hom_apply _ x c)))
  · obtain ⟨ξ, hξ⟩ := hsurj ζ
    exact ⟨ξ, (stalkMap_hom_apply _ x ξ).trans hξ⟩

/-- **The comparison `⋀ʳ E' ⊗ E'' ≅ ⋀ʳ⁺¹ E / ⋀ʳ⁺¹ E'`**, as an isomorphism. -/
noncomputable def wedgeQuotientIso (r : ℕ) :
    ((Tensor.sheafTensor Osharp).obj (A'.exteriorPower r)).obj E'' ≅
      cokernel (extPowMap A' A f (r + 1)) :=
  @asIso _ _ _ _ (wedgeQuotient A' A f g hfg hS r) (isIso_wedgeQuotient A' A f g hfg hS hb r)

include hb in
/-- **The short exact sequence `0 → ⋀ʳ⁺¹ E' → ⋀ʳ⁺¹ E → ⋀ʳ E' ⊗ E'' → 0`** of an extension whose
third term has stalks free of rank one. -/
theorem shortExact_wedgeQuotient (r : ℕ) :
    (ShortComplex.mk (extPowMap A' A f (r + 1))
      (cokernel.π (extPowMap A' A f (r + 1)) ≫ (wedgeQuotientIso A' A f g hfg hS hb r).inv)
      ((cokernel.condition_assoc (extPowMap A' A f (r + 1)) _).trans zero_comp)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_
    (ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact
      (extPowMap A' A f (r + 1))) (mono_extPowMap A' A f g hfg hS hb (r + 1))
      (coequalizer.π_epi))
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (wedgeQuotientIso A' A f g hfg hS hb r).symm
    ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.id_comp _)

include hS hb in
/-- **The exterior power of the kernel vanishes above its rank**: if the stalks of `E` are free of
rank `r + 1` and those of `E''` free of rank one, then `⋀ʳ⁺¹ E' = 0`. -/
@[sga "6 VII 4.1" "more general"]
theorem isZero_exteriorPower_of_rank (r : ℕ)
    (hE : ∀ x : ↥X, Nonempty (Module.Basis (Fin (r + 1)) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x))) :
    IsZero (A'.exteriorPower (r + 1)) := by
  refine (IsZero.iff_id_eq_zero _).2 (id_eq_zero_of_subsingleton_stalk _ fun x => ?_)
  obtain ⟨_, e, -, -⟩ := exists_stalkProdEquiv f g hfg hS hb x
  obtain ⟨bE⟩ := hE x
  have hempty : IsEmpty (Set.powersetCard (Fin (r + 1)) (r + 2)) := ⟨fun s => by
    have h1 := Set.powersetCard.card_eq s
    have h2 := Finset.card_le_univ (s : Finset (Fin (r + 1)))
    rw [Fintype.card_fin] at h2
    omega⟩
  have hsub : Subsingleton (⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(r + 2)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x)) :=
    (bE.exteriorPower (r + 2)).repr.toEquiv.subsingleton
  have hsub' : Subsingleton (⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(r + 1)
      ↑(TopCat.Presheaf.stalk E'.val.presheaf x)) := by
    refine ⟨fun a c => ?_⟩
    let Φ := (exteriorPowerCongr (r + 2) e).trans
      (exteriorPower.prodRightEquiv (↑(TopCat.Presheaf.stalk Osharp.obj x))
        (↑(TopCat.Presheaf.stalk E'.val.presheaf x)) (r + 1))
    have hs : ((0 : ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(r + 1 + 1)
        ↑(TopCat.Presheaf.stalk E'.val.presheaf x)), a) = (0, c) :=
      Φ.symm.injective (Subsingleton.elim _ _)
    exact congrArg Prod.snd hs
  exact (A'.exteriorPowerStalkEquiv (r + 1) x).toEquiv.subsingleton

end Sheaf

end Stacks.SheafOfModules.WedgeQuotient

end
