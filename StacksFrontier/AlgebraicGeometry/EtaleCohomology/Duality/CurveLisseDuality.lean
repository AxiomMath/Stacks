module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveCoverDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.LocalPurity

/-!
# Poincaré duality for lisse `ℤ/ℓ`-sheaves on an open of a smooth proper curve

Let `Y` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible
in `k`, `Λ = ℤ/ℓ`, `t : H²(Y, Λ) → Λ` an injective trace, and `V ⊆ Y` a nonempty open whose
complement is a finite set of closed points. For every finite type locally constant sheaf `H` of
`Λ`-modules on `V`, duality holds on `Y` at `j_! H`:

`H^i_c(V, H) × Ext^{2-i}_Y(j_! H, Λ_Y) → H²(Y, Λ) → Λ` is perfect,

and `Ext^q_Y(j_! H, Λ_Y) = 0` for `q > 2`. Given local purity.

The duality is the way-out argument `CategoryTheory.Abelian.Ext.isDualityPerfect_of_resolution` on
the class of the `j_! H`: a connected finite étale cover `π : T → V` of degree prime to `ℓ` makes
`π^{-1} H` unipotent (Tag 0A3R), the trace `π_* π^{-1} H → H` is onto with lisse kernel, and
duality at `j_! π_* π^{-1} H` is
`Stacks.EtaleCohomology.isDualityPerfect_extensionByZero_directImage_of_relSeries`. The vanishing
in degree `3` follows from duality: in `0 → K → G → H → 0`, `Ext²(G, Λ_Y) → Ext²(K, Λ_Y)` is dual
to the injection `H⁰_c(K) → H⁰_c(G)`, hence onto; higher degrees by induction.

## Main results

* `isDualityPerfect_extensionByZero_of_isFiniteTypeLocallyConstant_of_curve`: duality holds on `Y`
  at `j_! H`, and `Ext^q_Y(j_! H, Λ_Y) = 0` for `q > 2`, for every finite type locally constant
  sheaf `H` of `Λ`-modules on `V`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]


/-- **Duality makes `Ext^N(-, D)` right exact on monomorphisms.** If duality holds at `A` and at
`B` and `g : A → B` is a monomorphism, then `u ↦ g ∘ u : Ext^N(B, D) → Ext^N(A, D)` is onto: a
functional on `Ext^N(A, D)` vanishing on the image is `t(x ∘ -)` for some `x ∈ Hom(O, A)`, and then
`x ∘ g` pairs to zero with `Ext^N(B, D)`, so `x ∘ g = 0` and `x = 0`. -/
theorem surjective_precomp_of_isDualityPerfect {C : Type*} [Category C] [Abelian C]
    [HasExt.{u + 1} C] [Linear (ZMod ℓ) C] {O D A B : C} {N : ℕ} (t : Ext O D N →+ ZMod ℓ)
    (g : A ⟶ B) [Mono g] (hA : Ext.IsDualityPerfect O D N t A)
    (hB : Ext.IsDualityPerfect O D N t B) :
    Function.Surjective (fun u : Ext B D N => (Ext.mk₀ g).comp u (zero_add N)) := by
  intro w
  by_contra hw
  let φ₀ : Ext B D N →+ Ext A D N := (Ext.mk₀ g).precomp D (zero_add N)
  let I : Submodule (ZMod ℓ) (Ext A D N) := AddSubgroup.toZModSubmodule ℓ φ₀.range
  have hwI : I.mkQ w ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rintro ⟨u, hu⟩
    exact hw ⟨u, hu⟩
  obtain ⟨φbar, hφbar⟩ : ∃ φbar : Module.Dual (ZMod ℓ) (Ext A D N ⧸ I), φbar (I.mkQ w) ≠ 0 :=
    not_forall.1 (mt (Module.forall_dual_apply_eq_zero_iff (ZMod ℓ) _).1 hwI)
  let φ : Ext A D N →+ ZMod ℓ := (φbar.comp I.mkQ).toAddMonoidHom
  obtain ⟨x, hx⟩ := (hA 0 N (zero_add N)).2 φ
  have hxg : Ext.dualityPairing O D N t B (zero_add N) (x.comp (Ext.mk₀ g) (add_zero 0)) = 0 := by
    ext u
    rw [Ext.dualityPairing_apply, AddMonoidHom.zero_apply, Ext.comp_assoc_of_second_deg_zero]
    have := DFunLike.congr_fun hx ((Ext.mk₀ g).comp u (zero_add N))
    rw [Ext.dualityPairing_apply] at this
    rw [this]
    show φbar (I.mkQ (φ₀ u)) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero I).2 ⟨u, rfl⟩, map_zero]
  have hx0 : x = 0 := by
    have h1 : x.comp (Ext.mk₀ g) (add_zero 0) = 0 := (hB 0 N (zero_add N)).1 (by rw [hxg, map_zero])
    obtain ⟨x', rfl⟩ := (Ext.mk₀_bijective O A).2 x
    rw [Ext.mk₀_comp_mk₀, ← Ext.mk₀_zero] at h1
    rw [(cancel_mono g).1 ((Ext.mk₀_bijective O B).1 (h1.trans (by rw [zero_comp]))), Ext.mk₀_zero]
  have := DFunLike.congr_fun hx w
  rw [hx0, map_zero, AddMonoidHom.zero_apply] at this
  exact hφbar this.symm

include f in
/-- **The resolution step.** For a finite type locally constant `G` on `V` there is a short exact
sequence `0 → j_! K → E → j_! G → 0` with `K` finite type locally constant, duality on `Y` at `E`,
and `Ext^q_Y(E, Λ_Y) = 0` for `q > 2`. -/
theorem exists_shortExact_extensionByZero_isDualityPerfect_of_curve
    (hℓ : IsUnit (ℓ : k)) (hpurity : LocalPurity ℓ k)
    (t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht : Function.Injective t)
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    (V : Y.Opens) (hV : (V : Set Y) = (↑S : Set Y)ᶜ) [Nonempty V]
    (G : EtaleModules.{u, 0} (ZMod ℓ) V)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ)
      (V : Scheme).smallEtaleTopology G) :
    ∃ (K : EtaleModules.{u, 0} (ZMod ℓ) V)
      (_ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ)
        (V : Scheme).smallEtaleTopology K) (SS : ShortComplex (EtaleModules.{u, 0} (ZMod ℓ) Y)),
      SS.ShortExact ∧ SS.X₁ = (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj K ∧
        SS.X₃ = (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj G ∧
        Ext.IsDualityPerfect (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t SS.X₂ ∧
        ∀ q, 2 < q → Subsingleton (Ext SS.X₂ (unitSheaf (X := Y) ℓ) q) := by
  have : IsIntegral Y := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  obtain ⟨T, π, d, hfin, het, hconn, -, -, Xs, hhead, hlast⟩ :=
    exists_connected_primeToEll_finiteEtale_relSeries_constantRankOneStep Fact.out G hG
  have := hfin
  have := het
  have := hconn
  have := surjective_of_finiteEtale_of_connectedSpace π
  let jS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι
  let ε := (etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).counit.app G
  have : Epi ε := epi_etaleModuleDirectImageInverseImageAdj_counit_app (ZMod ℓ) π G
  have hG₂ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ)
      (V : Scheme).smallEtaleTopology ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj G)) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_finiteEtalePushforward_modules.{u, 0, 0} π
      (ZMod ℓ) _ (isFiniteTypeLocallyConstant_etaleModuleInverseImage π G hG)
  let SV := ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε)
  have hSV : SV.ShortExact := { exact := ShortComplex.exact_kernel ε }
  obtain ⟨hd, hv⟩ := isDualityPerfect_extensionByZero_directImage_of_relSeries f hℓ hpurity t ht
    S hS V hV π _ Xs hhead hlast
  exact ⟨kernel ε,
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_kernel.{u, u + 1, 0, 0}
      (V : Scheme).smallEtaleTopology (ZMod ℓ) ε hG₂ hG, SV.map jS, hSV.map_of_exact jS, rfl, rfl,
    hd, hv⟩

include f in
/-- **Poincaré duality for lisse `ℤ/ℓ`-sheaves on an open of a smooth proper curve**, the duality
half: duality holds on `Y` at `j_! H` for every finite type locally constant `H` on `V`. -/
theorem isDualityPerfect_extensionByZero_of_isFiniteTypeLocallyConstant_of_curve'
    (hℓ : IsUnit (ℓ : k)) (hpurity : LocalPurity ℓ k)
    (t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht : Function.Injective t)
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    (V : Y.Opens) (hV : (V : Set Y) = (↑S : Set Y)ᶜ) [Nonempty V]
    (H : EtaleModules.{u, 0} (ZMod ℓ) V)
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ)
      (V : Scheme).smallEtaleTopology H) :
    Ext.IsDualityPerfect (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj H) := by
  have hdimY : topologicalKrullDim Y ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  refine Ext.isDualityPerfect_of_resolution (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t
    (fun F => ∃ (H' : EtaleModules.{u, 0} (ZMod ℓ) V)
      (_ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ)
        (V : Scheme).smallEtaleTopology H'),
      F = (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj H')
    ?_ (fun K _ => subsingleton_ext_unitSheaf_of_curve f hdimY K 3 (by omega))
    (fun M j H φ => exists_extend_zmod H φ) _ ⟨H, hH, rfl⟩
  rintro F ⟨G, hG, rfl⟩
  obtain ⟨K, hK, SS, hSS, h₁, h₃, hd₂, -⟩ :=
    exists_shortExact_extensionByZero_isDualityPerfect_of_curve f hℓ hpurity t ht S hS V hV G hG
  exact ⟨SS, hSS, h₃, ⟨K, hK, h₁⟩, hd₂⟩

include f in
/-- **Poincaré duality for lisse `ℤ/ℓ`-sheaves on an open of a smooth proper curve.** Given
local purity, for a nonempty open `V` of `Y` with finite complement of closed points, every
injective trace `t` on `H²(Y, Λ)` and every finite type locally constant `H` on `V`, duality holds
on `Y` at `j_! H` and `Ext^q_Y(j_! H, Λ_Y) = 0` for `q > 2`. -/
theorem isDualityPerfect_extensionByZero_of_isFiniteTypeLocallyConstant_of_curve
    (hℓ : IsUnit (ℓ : k)) (hpurity : LocalPurity ℓ k)
    (t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht : Function.Injective t)
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    (V : Y.Opens) (hV : (V : Set Y) = (↑S : Set Y)ᶜ) [Nonempty V]
    (H : EtaleModules.{u, 0} (ZMod ℓ) V)
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ)
      (V : Scheme).smallEtaleTopology H) :
    Ext.IsDualityPerfect (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj H) ∧
      ∀ q, 2 < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj H)
        (unitSheaf (X := Y) ℓ) q) := by
  let ΛY := unitSheaf (X := Y) ℓ
  have hPD := isDualityPerfect_extensionByZero_of_isFiniteTypeLocallyConstant_of_curve' f hℓ hpurity
    t ht S hS V hV
  refine ⟨hPD H hH, fun q hq => ?_⟩
  induction q using Nat.strong_induction_on generalizing H with
  | _ q ih =>
  obtain ⟨K, hK, SS, hSS, h₁, h₃, hd₂, hv₂⟩ :=
    exists_shortExact_extensionByZero_isDualityPerfect_of_curve f hℓ hpurity t ht S hS V hV H hH
  rw [← h₃]
  refine ⟨fun a b => ?_⟩
  suffices hz : ∀ x₃ : Ext SS.X₃ ΛY q, x₃ = 0 by rw [hz a, hz b]
  intro x₃
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have := hv₂ (q' + 1) hq
  obtain ⟨x₁, hx₁⟩ := Ext.contravariant_sequence_exact₃ hSS ΛY x₃ (Subsingleton.elim _ _)
    (add_comm 1 q')
  rw [← hx₁]
  by_cases hq' : q' = 2
  · subst hq'
    have hd₁ : Ext.IsDualityPerfect ΛY ΛY 2 t SS.X₁ := h₁ ▸ hPD K hK
    have := hSS.mono_f
    obtain ⟨x₂, rfl⟩ := surjective_precomp_of_isDualityPerfect t SS.f hd₁ hd₂ x₁
    rw [← Ext.comp_assoc_of_second_deg_zero, hSS.extClass_comp, Ext.zero_comp]
  · have : Subsingleton (Ext SS.X₁ ΛY q') := h₁ ▸ ih q' (by omega) K hK (by omega)
    rw [Subsingleton.elim x₁ 0, Ext.comp_zero]

include f in
/-- **Poincaré duality for lisse `ℤ/ℓ`-sheaves on an open of a smooth proper curve**, with local
purity discharged (`Stacks.EtaleCohomology.Purity.localPurity`): for a nonempty open `V` of `Y`
with finite complement of closed points, every injective trace `t` on `H²(Y, Λ)` and every finite
type locally constant `H` on `V`, duality holds on `Y` at `j_! H` and `Ext^q_Y(j_! H, Λ_Y) = 0` for
`q > 2`. -/
theorem isDualityPerfect_extensionByZero_lisse_of_curve (hℓ : IsUnit (ℓ : k))
    (t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ) (ht : Function.Injective t)
    (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    (V : Y.Opens) (hV : (V : Set Y) = (↑S : Set Y)ᶜ) [Nonempty V]
    (H : EtaleModules.{u, 0} (ZMod ℓ) V)
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ)
      (V : Scheme).smallEtaleTopology H) :
    Ext.IsDualityPerfect (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj H) ∧
      ∀ q, 2 < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj H)
        (unitSheaf (X := Y) ℓ) q) :=
  isDualityPerfect_extensionByZero_of_isFiniteTypeLocallyConstant_of_curve f hℓ
    (Purity.localPurity k ℓ hℓ) t ht S hS V hV H hH

end Stacks.EtaleCohomology

end
