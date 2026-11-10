module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.TopDegreePairingTransport

/-!
# Transporting a pairing along a surjection from cycles, by counting

A pairing `ψ : X → Hom(Y, Z)` which, read through `X ≃ X'` and `Z ≃ Z'`, is computed on a group
`C` mapping onto `Y` by a bijective pairing `ψ' : X' → Hom(Y', Z')` through `f : C → Y'`, is
bijective as soon as `f` and `C ↠ Y` have the same kernel and `Y`, `Y'` are finite of the same
cardinality.

## Main results

* `CochainComplex.exists_iCycles_eq`, `CochainComplex.exists_iCycles_eq_moduleCat`: an element
  of a complex of abelian groups, resp. modules, killed by the differential is a cycle.
* `Stacks.ContinuousCohomology.bijective_of_pairing_transport_of_natCard_eq`: the transport of a
  bijective pairing described above.
* `Stacks.ContinuousCohomology.ComplexPairing.d_pair_iCycles`: the pairing of two cocycles is a
  cocycle.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe v w

namespace CochainComplex

/-- **A cocycle of a complex of abelian groups with a prescribed underlying element.** -/
theorem exists_iCycles_eq (K : CochainComplex AddCommGrpCat.{w} ℤ) (i : ℤ) (x : K.X i)
    (hx : K.d i (i + 1) x = 0) : ∃ c : K.cycles i, K.iCycles i c = x := by
  let k : AddCommGrpCat.of (ULift.{w} ℤ) ⟶ K.X i :=
    AddCommGrpCat.ofHom ((zmultiplesHom (K.X i) x).comp AddEquiv.ulift.toAddMonoidHom)
  have hk : k ≫ K.d i (i + 1) = 0 := by
    ext n
    simp [k, hx]
  refine ⟨K.liftCycles k (i + 1) (by simp) hk (ULift.up 1), ?_⟩
  exact (ConcreteCategory.congr_hom (K.liftCycles_i k (i + 1) (by simp) hk) (ULift.up 1)).trans
    (one_zsmul x)

/-- **A cocycle of a complex of modules with a prescribed underlying element.** -/
theorem exists_iCycles_eq_moduleCat {R : Type} [Ring R] (K : CochainComplex (ModuleCat.{w} R) ℤ)
    (i : ℤ) (x : K.X i) (hx : (K.d i (i + 1)).hom x = 0) :
    ∃ c : K.cycles i, (K.iCycles i).hom c = x := by
  let k : ModuleCat.of R (ULift.{w} R) ⟶ K.X i :=
    ModuleCat.ofHom ((LinearMap.toSpanSingleton R (K.X i) x).comp
      (ULift.moduleEquiv : ULift.{w} R ≃ₗ[R] R).toLinearMap)
  have hk : k ≫ K.d i (i + 1) = 0 := by
    ext n
    simp [k, hx]
  refine ⟨(K.liftCycles k (i + 1) (by simp) hk).hom (ULift.up 1), ?_⟩
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ (ULift.up 1))
    (K.liftCycles_i k (i + 1) (by simp) hk)
  exact h.trans (by simp [k])

end CochainComplex

namespace Stacks.ContinuousCohomology

/-- Under a bijective pairing `ψ'` into a group `Z'` separating the points of `Y'`, an element of
`Y'` is determined by its pairings. -/
theorem eq_of_forall_pairing_eq {X' Y' Z' : Type*} [AddCommGroup Y'] [AddCommGroup Z']
    (ψ' : X' → (Y' →+ Z')) (hψ' : Function.Surjective ψ')
    (hsep : ∀ b : Y', b ≠ 0 → ∃ φ : Y' →+ Z', φ b ≠ 0) {b b' : Y'}
    (h : ∀ α, ψ' α b = ψ' α b') : b = b' := by
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨φ, hφ⟩ := hsep _ hne
  obtain ⟨α, rfl⟩ := hψ' φ
  exact hφ (by rw [map_sub, h, sub_self])

/-- **A pairing computed on a group mapping onto its domain, by counting.** Let
`ψ : X → Hom(Y, Z)`, `π : C ↠ Y`, `f : C → Y'` and a bijective pairing
`ψ' : X' → Hom(Y', Z')` with `e₃ (ψ x (π c)) = ψ' (e₁ x) (f c)`. If `Z'` separates the points
of `Y'`, `f c = 0` forces `π c = 0`, and `Y`, `Y'` are finite of the same cardinality, then `ψ`
is bijective. -/
theorem bijective_of_pairing_transport_of_natCard_eq {X X' Y' Z' C : Type*} [AddCommGroup Y']
    [AddCommGroup Z'] [AddCommGroup C] [Finite Y'] {Y Z : AddCommGrpCat.{w}}
    (ψ : X → (Y ⟶ Z)) (ψ' : X' → (Y' →+ Z')) (e₁ : X ≃ X') (e₃ : Z ≃+ Z') (π : C →+ Y)
    (hπ : Function.Surjective π) (f : C → Y')
    (h : ∀ x c, e₃ ((ψ x).hom (π c)) = ψ' (e₁ x) (f c)) (hψ' : Function.Bijective ψ')
    (hsep : ∀ b : Y', b ≠ 0 → ∃ φ : Y' →+ Z', φ b ≠ 0) (hinj : ∀ c, f c = 0 → π c = 0)
    (hcard : Nat.card Y = Nat.card Y') : Function.Bijective ψ := by
  have hpair : ∀ α c, ψ' α (f c) = e₃ ((ψ (e₁.symm α)).hom (π c)) := fun α c => by
    rw [h, e₁.apply_symm_apply]
  let fc : C →+ Y' :=
    { toFun := f
      map_zero' := eq_of_forall_pairing_eq ψ' hψ'.2 hsep fun α => by
        rw [hpair, map_zero, map_zero, map_zero, map_zero]
      map_add' := fun c c' => eq_of_forall_pairing_eq ψ' hψ'.2 hsep fun α => by
        rw [hpair, map_add, map_add, map_add, map_add, hpair, hpair] }
  have hker : π.ker = fc.ker :=
    le_antisymm (fun c hc => eq_of_forall_pairing_eq ψ' hψ'.2 hsep fun α => by
      change ψ' α (f c) = _
      rw [hpair, hc, map_zero, map_zero, map_zero]) (fun c hc => hinj c hc)
  let E₀ : Y ≃+ C ⧸ π.ker := (QuotientAddGroup.quotientKerEquivOfSurjective π hπ).symm
  let E₁ : C ⧸ π.ker ≃+ C ⧸ fc.ker := QuotientAddGroup.quotientAddEquivOfEq hker
  let E₂ : C ⧸ fc.ker ≃+ fc.range := QuotientAddGroup.quotientKerEquivRange fc
  have htop : fc.range = ⊤ := by
    rw [← AddSubgroup.card_eq_iff_eq_top, ← hcard]
    exact (Nat.card_congr (E₀.trans (E₁.trans E₂)).toEquiv).symm
  let E : Y ≃+ Y' := E₀.trans (E₁.trans (E₂.trans
    ((AddEquiv.addSubgroupCongr htop).trans AddSubgroup.topEquiv)))
  have hE : ∀ c, E (π c) = f c := by
    intro c
    have h₀ : E₀ (π c) = QuotientAddGroup.mk c :=
      (AddEquiv.symm_apply_eq _).2 rfl
    simp only [E, AddEquiv.trans_apply, h₀]
    rfl
  refine bijective_of_pairing_transport ψ ψ' e₁ E e₃ (fun x y => ?_) hψ'
  obtain ⟨c, rfl⟩ := hπ y
  rw [hE, h]

section PairCycles

variable {Q : Type v} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  {R : Type} [Ring R] [Finite R] {S : Type} [Ring S] {φ : S →+* Rᵐᵒᵖ}
  {A : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} S Q) ℤ}
  {E : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} R Q) ℤ}
  {G : CochainComplex (Stacks.Injectives.ContinuousModule.{0, v, max v w} ℤ Q) ℤ}

omit [IsTopologicalGroup Q] in
private lemma eq_zero_of_eq_add_units_smul {V : Type*} [AddCommGroup V] {a b c : V} (u : ℤˣ)
    (h : a = b + u • c) (ha : a = 0) (hc : c = 0) : b = 0 := by
  rw [hc, smul_zero, add_zero] at h
  rw [← h, ha]

omit [IsTopologicalGroup Q] [Finite R] in
/-- **The pairing of two cocycles is a cocycle**, by the Leibniz rule. -/
theorem ComplexPairing.d_pair_iCycles (P : ComplexPairing R φ A E G) (d : ℤ)
    (x : (underlyingAb S A).cycles d) (y : (underlyingAb R E).cycles 0) :
    (underlyingAb ℤ G).d d (d + 1) (P.pair d 0 d (zero_add d) ((underlyingAb S A).iCycles d x)
      ((underlyingAb R E).iCycles 0 y)) = 0 := by
  have hx : (A.d d (d + 1)).hom.hom.hom.hom ((underlyingAb S A).iCycles d x) = 0 :=
    congrArg (fun ψ => AddCommGrpCat.Hom.hom ψ x) ((underlyingAb S A).iCycles_d d (d + 1))
  have hy : (E.d 0 (0 + 1)).hom.hom.hom.hom ((underlyingAb R E).iCycles 0 y) = 0 :=
    congrArg (fun ψ => AddCommGrpCat.Hom.hom ψ y) ((underlyingAb R E).iCycles_d 0 (0 + 1))
  have h := P.leibniz d 0 d (d + 1) (zero_add d) rfl ((underlyingAb S A).iCycles d x)
    ((underlyingAb R E).iCycles 0 y)
  exact eq_zero_of_eq_add_units_smul _ h (by rw [hx, map_zero]; rfl) (by rw [hy, map_zero])

end PairCycles

end Stacks.ContinuousCohomology

end
