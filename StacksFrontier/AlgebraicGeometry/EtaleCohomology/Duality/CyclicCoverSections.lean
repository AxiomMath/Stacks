module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CyclicCoverQuotients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantModuleSheafSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapBijectiveOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections of the free sheaf on the torsor of a nonsplit extension

Let `Λ = ℤ/ℓ` with `ℓ` prime, `X` a connected scheme and `0 → Λ_X → E → Λ_X → 0` a nonsplit
extension on the small étale site of `X`, with torsor `P` and `s = Λ[τ] - 1` on `Λ[P]`. Maps
`Λ_X → F` are sections of `F` over `X`, and the sections of `Λ_Y` over a scheme `Y` are the
locally constant `ℤ/ℓ`-valued maps on `Y`; so `End(Λ_X)` has `ℓ` elements, and a scheme `Y` with
at most `ℓ` such maps is connected.

The main result is that `Λ[P]` has at most `ℓ` global sections: every `g : Λ_X → Λ[P]` has
`s g = 0`, so `g` comes from `coker s ≅ Λ_X`.

## Main results

* `Stacks.EtaleCohomology.ExtensionTorsor.natCard_hom_unitSheaf_unitSheaf`: `#End(Λ_Y)` is the
  number of locally constant `ℤ/ℓ`-valued maps on `Y`.
* `Stacks.EtaleCohomology.ExtensionTorsor.preconnectedSpace_of_natCard_locallyConstant_le`.
* `Stacks.EtaleCohomology.ExtensionTorsor.finite_and_natCard_hom_unitSheaf_freeTorsor_le`:
  `#Hom(Λ_X, Λ[P]) ≤ ℓ` for a nonsplit extension on a connected `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.ExtensionTorsor

section Constant

variable {Y : Scheme.{u}} (ℓ : ℕ)

/-- **Maps out of `Λ_Y` are global sections.** -/
def homUnitSheafEquiv (F : EtaleModules.{u, 0} (ZMod ℓ) Y) :
    (unitSheaf (X := Y) ℓ ⟶ F) ≃ F.obj.obj (op (etaleSiteTerminal Y)) :=
  ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))
      (etaleSiteTerminalIsTerminal Y)).homEquiv _ _).trans
    (Stacks.Cohomology.GlobalSections.moduleULiftHomAddEquiv.{0, u + 1} (ZMod ℓ) _).toEquiv

/-- The global sections of `Λ_Y` are the locally constant `ℤ/ℓ`-valued maps on `Y`. -/
@[sga "4½ Arcata 2.2.1" "more general"]
def unitSheafSectionsEquiv :
    (unitSheaf (X := Y) ℓ).obj.obj (op (etaleSiteTerminal Y)) ≃
      LocallyConstant Y (ULift.{u + 1} (ZMod ℓ)) :=
  (((sheafToPresheaf _ _).mapIso (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, 0}
    (ZMod ℓ) Y (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))).app
      (op (etaleSiteTerminal Y))).toLinearEquiv.toEquiv

/-- `End(Λ_Y)` is in bijection with the locally constant `ℤ/ℓ`-valued maps on `Y`. -/
private def endUnitSheafEquiv :
    (unitSheaf (X := Y) ℓ ⟶ unitSheaf ℓ) ≃ LocallyConstant Y (ZMod ℓ) :=
  (((homUnitSheafEquiv ℓ _).trans (unitSheafSectionsEquiv ℓ)).trans
    (LocallyConstant.congrRight Equiv.ulift))

/-- **`#End(Λ_Y)` is the number of locally constant `ℤ/ℓ`-valued maps on `Y`.** -/
theorem natCard_hom_unitSheaf_unitSheaf :
    Nat.card (unitSheaf (X := Y) ℓ ⟶ unitSheaf ℓ) = Nat.card (LocallyConstant Y (ZMod ℓ)) :=
  Nat.card_congr (endUnitSheafEquiv ℓ)

/-- `End(Λ_Y)` is finite if and only if there are finitely many locally constant `ℤ/ℓ`-valued
maps on `Y`. -/
theorem finite_hom_unitSheaf_unitSheaf_iff :
    Finite (unitSheaf (X := Y) ℓ ⟶ unitSheaf ℓ) ↔ Finite (LocallyConstant Y (ZMod ℓ)) :=
  Equiv.finite_iff (endUnitSheafEquiv ℓ)

/-- On a connected space the locally constant maps are the constants. -/
theorem natCard_locallyConstant_of_connectedSpace {T A : Type*} [TopologicalSpace T]
    [ConnectedSpace T] : Nat.card (LocallyConstant T A) = Nat.card A := by
  obtain ⟨t₀⟩ := ConnectedSpace.toNonempty (α := T)
  refine Nat.card_congr
    { toFun := fun f => f t₀
      invFun := fun a => LocallyConstant.const T a
      left_inv := fun f => LocallyConstant.ext fun t => (f.apply_eq_of_preconnectedSpace t t₀).symm
      right_inv := fun a => rfl }

/-- **A space with at most `#A` locally constant `A`-valued maps is preconnected**, for a finite
`A` with at least two elements. -/
theorem preconnectedSpace_of_natCard_locallyConstant_le {T A : Type*} [TopologicalSpace T]
    [Finite A] (hA : 2 ≤ Nat.card A) [Finite (LocallyConstant T A)]
    (h : Nat.card (LocallyConstant T A) ≤ Nat.card A) : PreconnectedSpace T := by
  classical
  rw [preconnectedSpace_iff_clopen]
  intro U hU
  by_contra hne
  rw [not_or] at hne
  obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.2 hne.1
  obtain ⟨v, hv⟩ : ∃ v, v ∉ U := by
    by_contra hall
    exact hne.2 (Set.eq_univ_of_forall fun x => not_not.1 fun hx => hall ⟨x, hx⟩)
  let φ : A × A → LocallyConstant T A := fun ab =>
    (LocallyConstant.ofIsClopen hU).map ![ab.1, ab.2]
  have hφ : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 := congrArg (fun f : LocallyConstant T A => f u) hab
    have h2 := congrArg (fun f : LocallyConstant T A => f v) hab
    have e1 : ∀ c d : A, (φ (c, d)) u = c := fun c d => by
      change ![c, d] (if u ∈ U then 0 else 1) = c
      rw [ite_eq_left hu]
      rfl
    have e2 : ∀ c d : A, (φ (c, d)) v = d := fun c d => by
      change ![c, d] (if v ∈ U then 0 else 1) = d
      rw [ite_eq_right hv]
      rfl
    simp only [e1, e2] at h1 h2
    rw [h1, h2]
  have h₄ := (Nat.card_le_card_of_injective φ hφ).trans h
  rw [Nat.card_prod] at h₄
  nlinarith

end Constant

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : EtaleModules.{u, 0} (ZMod ℓ) X}
  {i : unitSheaf ℓ ⟶ E} {ε : E ⟶ unitSheaf ℓ} {w : i ≫ ε = 0}
  (hS : (ShortComplex.mk i ε w).ShortExact)

/-- **`s^{ℓ-j}` identifies `coker s^j` with the kernel of `s^j` on `Λ[P]`**, for `j ≤ ℓ`. -/
theorem exists_comp_cokernelPowLift_shift_and_cancel {j : ℕ} (hj : j ≤ ℓ) :
    (∀ {A : EtaleModules.{u, 0} (ZMod ℓ) X} (k : A ⟶ freeTorsor (i := i) (ε := ε) (w := w)),
      k ≫ (shift hS ^ j).asHom = 0 →
        ∃ k', k' ≫ Stacks.Abelian.cokernelPowLift (shift hS) (shift_pow_self hS) hj = k) ∧
      ∀ {A : EtaleModules.{u, 0} (ZMod ℓ) X} (a b : A ⟶ cokernel (shift hS ^ j).asHom),
        a ≫ Stacks.Abelian.cokernelPowLift (shift hS) (shift_pow_self hS) hj =
          b ≫ Stacks.Abelian.cokernelPowLift (shift hS) (shift_pow_self hS) hj → a = b := by
  have := etaleModules_AB5OfSize.{u} (ZMod ℓ)
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1, 0} (ZMod ℓ)) :=
    ModuleCat.instHasLimitsOfSize.{u + 1, u + 1, 0}
  have : HasColimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1, 0} (ZMod ℓ)) :=
    ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} (ZMod ℓ)
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget (ModuleCat.{u + 1, 0} (ZMod ℓ))) :=
    etaleModules_preservesFilteredColimits_forget.{u} (ZMod ℓ)
  have : GrothendieckTopology.HasEnoughPoints.{u + 1} X.smallEtaleTopology :=
    Scheme.hasEnoughPoints_smallEtaleTopology.{0, u} X
  obtain ⟨P, _, hP⟩ :=
    GrothendieckTopology.HasEnoughPoints.exists_objectProperty X.smallEtaleTopology
  let Φ : P.FullSubcategory → EtaleModules.{u, 0} (ZMod ℓ) X ⥤ ModuleCat.{u + 1} (ZMod ℓ) :=
    fun q => q.obj.sheafFiber
  have hΦ := hP.jointlyFaithful (ModuleCat.{u + 1} (ZMod ℓ))
  have : ∀ q, FiniteDimensional (ZMod ℓ) ((Φ q).obj (freeTorsor (i := i) (ε := ε) (w := w))) :=
    fun q => finiteDimensional_sheafFiber_freeTorsor hS q.obj
  exact Stacks.Abelian.exists_comp_cokernelPowLift_and_cancel _ _ hj
    (Stacks.Abelian.cokernelPowLiftShortComplex_exact_and_mono Φ
    (fun f g h => hΦ.map_injective h) (shift hS)
    (fun q => finrank_sheafFiber_freeTorsor hS q.obj) (shift_pow_self hS)
    (fun q => finrank_ker_sheafFiber_map_shift hS q.obj) hj)

variable (ℓ) in
omit [Fact ℓ.Prime] in
/-- **`End(Λ_X)` has `ℓ` elements** for a connected `X`. -/
theorem natCard_end_unitSheaf [ConnectedSpace X] :
    Nat.card (unitSheaf (X := X) ℓ ⟶ unitSheaf ℓ) = ℓ := by
  rw [natCard_hom_unitSheaf_unitSheaf, natCard_locallyConstant_of_connectedSpace (T := X),
    Nat.card_zmod]

include hS in
/-- **A map `e : Λ_X → E` whose image in `Λ_X` is nonzero splits the extension**, for a connected
`X`. -/
theorem extClass_eq_zero_of_comp_ne_zero [ConnectedSpace X] (e : unitSheaf ℓ ⟶ E)
    (he : e ≫ ε ≠ 0) : hS.extClass = 0 := by
  have hp : ℓ.Prime := Fact.out
  have : Fact (Nat.card (unitSheaf (X := X) ℓ ⟶ unitSheaf ℓ)).Prime :=
    ⟨(natCard_end_unitSheaf (X := X) ℓ).symm ▸ hp⟩
  have htop : AddSubgroup.zmultiples (e ≫ ε) = ⊤ :=
    (AddSubgroup.eq_bot_or_eq_top_of_prime_card _).resolve_left
      (mt AddSubgroup.zmultiples_eq_bot.1 he)
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (htop ▸ AddSubgroup.mem_top (𝟙 _))
  exact hS.extClass_eq_zero_of_comp_eq_id (k • e) ((Preadditive.zsmul_comp _ _ _).trans hk)

include hS in
/-- **A section killed by `s²` is killed by `s`**, for a nonsplit extension on a connected
`X`. -/
theorem comp_shift_eq_zero_of_comp_shift_sq_eq_zero [ConnectedSpace X] (hne : hS.extClass ≠ 0)
    (h : unitSheaf ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w)) (hh : h ≫ (shift hS ^ 2).asHom = 0) :
    h ≫ (shift hS).asHom = 0 := by
  have hp : ℓ.Prime := Fact.out
  have h2 : 2 ≤ ℓ := hp.two_le
  obtain ⟨h', hh'⟩ := (exists_comp_cokernelPowLift_shift_and_cancel hS h2).1 h hh
  by_cases hc : (h' ≫ cokernelShiftSqDesc hS) ≫ ε = 0
  · obtain ⟨e₁, he₁⟩ : ∃ e₁, e₁ ≫ i = h' ≫ cokernelShiftSqDesc hS :=
      have := hS.mono_f
      ⟨hS.exact.lift _ hc, hS.exact.lift_f _ hc⟩
    have := isIso_cokernelShiftSqDesc hS
    have := isIso_cokernelShiftDesc hS
    have hιτ : cokernelShiftDesc hS ≫ i =
        Stacks.Abelian.cokernelPowι (shift hS) 1 ≫ cokernelShiftSqDesc hS :=
      (cokernelPowShortComplexHom hS).comm₁₂
    have hh'' :
        h' = e₁ ≫ inv (cokernelShiftDesc hS) ≫ Stacks.Abelian.cokernelPowι (shift hS) 1 := by
      rw [← cancel_mono (cokernelShiftSqDesc hS), Category.assoc, Category.assoc, ← hιτ,
        IsIso.inv_hom_id_assoc, he₁]
    have hzero : Stacks.Abelian.cokernelPowι (shift hS) 1 ≫
        Stacks.Abelian.cokernelPowLift (shift hS) (shift_pow_self hS) h2 ≫
          (shift hS).asHom = 0 := by
      rw [← cancel_epi (cokernel.π (shift hS).asHom), Stacks.Abelian.π_cokernelPowι_assoc,
        comp_zero]
      change (shift hS ^ 1).asHom ≫ cokernel.π (shift hS ^ 2).asHom ≫ _ = 0
      rw [Stacks.Abelian.π_cokernelPowLift_assoc, ← End.mul_asHom,
        ← End.mul_asHom, pow_one, ← pow_succ', ← pow_succ, show ℓ - 2 + 1 + 1 = ℓ by omega,
        shift_pow_self, End.zero_asHom]
    rw [← hh', hh'']
    simp only [Category.assoc, hzero, comp_zero]
  · exact absurd (extClass_eq_zero_of_comp_ne_zero hS _ hc) hne

include hS in
/-- **Every global section of `Λ[P]` is killed by `s`**, for a nonsplit extension on a connected
`X`. -/
theorem comp_shift_eq_zero [ConnectedSpace X] (hne : hS.extClass ≠ 0)
    (g : unitSheaf ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w)) : g ≫ (shift hS).asHom = 0 := by
  have hp : ℓ.Prime := Fact.out
  have hstep : ∀ k, 1 ≤ k → g ≫ (shift hS ^ (k + 1)).asHom = 0 → g ≫ (shift hS ^ k).asHom = 0 := by
    intro k hk hg
    have := comp_shift_eq_zero_of_comp_shift_sq_eq_zero hS hne (g ≫ (shift hS ^ (k - 1)).asHom) (by
      rw [Category.assoc, ← End.mul_asHom, ← pow_add, show 2 + (k - 1) = k + 1 by omega, hg])
    rwa [Category.assoc, ← End.mul_asHom, ← pow_succ', Nat.sub_add_cancel hk] at this
  have hdown : ∀ d, d + 1 ≤ ℓ → g ≫ (shift hS ^ (ℓ - d)).asHom = 0 := by
    intro d
    induction d with
    | zero => exact fun _ => by rw [Nat.sub_zero, shift_pow_self, End.zero_asHom, comp_zero]
    | succ d ih =>
      intro hd
      refine hstep _ (by omega) ?_
      rw [show ℓ - (d + 1) + 1 = ℓ - d by omega]
      exact ih (by omega)
  have := hdown (ℓ - 1) (by have := hp.one_le; omega)
  rwa [Nat.sub_sub_self hp.one_le, pow_one] at this

include hS in
/-- **`Λ[P]` has at most `ℓ` global sections**, for a nonsplit extension on a connected `X`. -/
theorem finite_and_natCard_hom_unitSheaf_freeTorsor_le [ConnectedSpace X] (hne : hS.extClass ≠ 0) :
    Finite (unitSheaf ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w)) ∧
      Nat.card (unitSheaf ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w)) ≤ ℓ := by
  have hp : ℓ.Prime := Fact.out
  obtain ⟨hlift, hcancel⟩ := exists_comp_cokernelPowLift_shift_and_cancel hS hp.one_le
  have := isIso_cokernelShiftDesc hS
  have hg : ∀ g : unitSheaf ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w),
      g ≫ (shift hS ^ 1).asHom = 0 :=
    fun g => by rw [pow_one]; exact comp_shift_eq_zero hS hne g
  choose ψ hψ using fun g : unitSheaf ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w) =>
    hlift g (hg g)
  let φ : (unitSheaf ℓ ⟶ freeTorsor (i := i) (ε := ε) (w := w)) →
      (unitSheaf (X := X) ℓ ⟶ unitSheaf ℓ) := fun g =>
    ψ g ≫ (cokernelIsoOfEq (congrArg End.asHom (pow_one (shift hS)))).hom ≫ cokernelShiftDesc hS
  have hφ : Function.Injective φ := by
    intro g g' hgg
    have hl : ψ g = ψ g' := by
      simpa only [φ, cancel_mono] using hgg
    rw [← hψ g, ← hψ g', hl]
  have : Finite (unitSheaf (X := X) ℓ ⟶ unitSheaf ℓ) :=
    Nat.finite_of_card_ne_zero (by rw [natCard_end_unitSheaf]; exact hp.ne_zero)
  exact ⟨Finite.of_injective φ hφ,
    (Nat.card_le_card_of_injective φ hφ).trans (natCard_end_unitSheaf ℓ).le⟩

end Stacks.EtaleCohomology.ExtensionTorsor

end
