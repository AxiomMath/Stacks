module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import StacksFrontier.Algebra.Module.Injective.ZModPrimePower
public import Mathlib.Algebra.Module.ZMod
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Perfectness of a Yoneda pairing by dévissage ("way-out" argument)

Let `C` be an abelian category, `O` and `D` objects, `N` a natural number and
`t : Ext^N(O, D) → A` an additive map to an abelian group `A`. For an object `F` and `i + j = N`
the Yoneda product followed by `t` is a pairing

`Ext^i(O, F) × Ext^j(F, D) → A,  (x, y) ↦ t (x ∘ y)`,

and we say duality holds at `F` if for all such `i, j` the induced map
`Ext^i(O, F) → Hom(Ext^j(F, D), A)` is bijective. In étale cohomology `O = Λ` is the constant
sheaf, `D = Λ` (up to a Tate twist), `N = 2 dim X` and `t` is the trace map: duality at `F` is
Poincaré duality with coefficients in `F`.

This file proves the dévissage step reducing Poincaré duality for locally constant coefficients
to the induced sheaves `π_* Λ` of finite étale covers: if every object `F` of a class `P` sits in
a short exact sequence `0 → K → G → F → 0` with `K ∈ P` and duality at `G`, if `Ext^{N+1}(O, K)`
vanishes for `K ∈ P`, and if `A` is injective with respect to the groups `Ext^j(M, D)`, then
duality holds at every object of `P`. The proof is a descending induction on the degree `i`
using the two long exact sequences of `Ext` and the four lemma.

## Main definitions

* `CategoryTheory.Abelian.Ext.dualityPairing`: the map `Ext^i(O, F) → Hom(Ext^j(F, D), A)`.
* `CategoryTheory.Abelian.Ext.IsDualityPerfect`: it is bijective in all degrees `i + j = N`.

## Main results

* `CategoryTheory.Abelian.Ext.isDualityPerfect_of_resolution`: the dévissage.
* `CategoryTheory.Abelian.Ext.isDualityPerfect_X₂`: the five lemma, duality at the outer terms of a
  short exact sequence gives duality at the middle term.
* `CategoryTheory.Abelian.Ext.isDualityPerfect_of_retract`: duality passes to retracts.
* `CategoryTheory.Abelian.Ext.isDualityPerfect_transport_iff`: invariance under isomorphisms of
  `O` and `D`, for the transported trace `transportTrace`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section

variable (O D : C) (N : ℕ) {A : Type*} [AddCommGroup A] (t : Ext O D N →+ A)

/-- The map `Ext^i(O, F) → Hom(Ext^j(F, D), A)`, `x ↦ (y ↦ t (x ∘ y))`, for `i + j = N`. -/
noncomputable def dualityPairing (F : C) {i j : ℕ} (h : i + j = N) :
    Ext O F i →+ (Ext F D j →+ A) :=
  AddMonoidHom.mk' (fun x => t.comp (bilinearComp O F D i j N h x))
    (fun x y => by ext z; simp)

/-- The value of `dualityPairing O D N t F h` at `x` and `y` is `t (x ∘ y)`. -/
@[simp]
lemma dualityPairing_apply (F : C) {i j : ℕ} (h : i + j = N) (x : Ext O F i) (y : Ext F D j) :
    dualityPairing O D N t F h x y = t (x.comp y h) :=
  rfl

/-- **Duality holds at `F`**: for all `i + j = N` the pairing `(x, y) ↦ t (x ∘ y)` identifies
`Ext^i(O, F)` with `Hom(Ext^j(F, D), A)`. -/
def IsDualityPerfect (F : C) : Prop :=
  ∀ (i j : ℕ) (h : i + j = N), Function.Bijective (dualityPairing O D N t F h)

end

/-- An additive map `φ` out of `B` vanishing on the kernel of `α : B → E` factors through `α`,
when `A` has the extension property for subgroups of `E`. -/
lemma exists_comp_eq_of_ker_le {B E A : Type*} [AddCommGroup B] [AddCommGroup E]
    [AddCommGroup A] (hA : ∀ (H : AddSubgroup E) (φ : H →+ A), ∃ ψ : E →+ A, ∀ x : H, ψ x = φ x)
    (α : B →+ E) (φ : B →+ A) (hle : α.ker ≤ φ.ker) : ∃ ψ : E →+ A, ψ.comp α = φ := by
  let φ₀ : α.range →+ A :=
    (QuotientAddGroup.lift α.ker φ hle).comp (QuotientAddGroup.quotientKerEquivRange α).symm
  obtain ⟨ψ, hψ⟩ := hA α.range φ₀
  refine ⟨ψ, AddMonoidHom.ext fun b => ?_⟩
  rw [AddMonoidHom.comp_apply, hψ ⟨α b, b, rfl⟩]
  have : (QuotientAddGroup.quotientKerEquivRange α).symm ⟨α b, b, rfl⟩ =
      (QuotientAddGroup.mk b : B ⧸ α.ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  change QuotientAddGroup.lift α.ker φ hle
    ((QuotientAddGroup.quotientKerEquivRange α).symm ⟨α b, b, rfl⟩) = φ b
  rw [this]
  rfl

/-- **`ℤ/pᵐ` has the extension property for subgroups of `ℤ/pᵐ`-modules**, because it is
self-injective (Baer's criterion, `Stacks.ZModPrimePower.baer_self`). -/
@[sga "4 XVIII 3.2.6" "special case"]
theorem exists_extend_zmodPow {p m : ℕ} [Fact p.Prime] {E : Type*} [AddCommGroup E]
    [Module (ZMod (p ^ m)) E] (H : AddSubgroup E) (φ : H →+ ZMod (p ^ m)) :
    ∃ ψ : E →+ ZMod (p ^ m), ∀ x : H, ψ x = φ x := by
  let Hs : Submodule (ZMod (p ^ m)) E :=
    { carrier := H
      add_mem' := H.add_mem
      zero_mem' := H.zero_mem
      smul_mem' := fun c x hx => by
        rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
        exact H.nsmul_mem hx _ }
  let φ' : Hs →ₗ[ZMod (p ^ m)] ZMod (p ^ m) := (φ.comp (AddMonoidHom.mk' (fun x : Hs =>
    (⟨x.1, x.2⟩ : H)) (fun _ _ => rfl))).toZModLinearMap (p ^ m)
  obtain ⟨ψ, hψ⟩ := Module.Baer.extension_property Stacks.ZModPrimePower.baer_self Hs.subtype
    Hs.injective_subtype φ'
  exact ⟨ψ.toAddMonoidHom, fun x => LinearMap.congr_fun hψ (⟨x.1, x.2⟩ : Hs)⟩

section Iso

variable {O D O' D' : C} {N : ℕ} {A : Type*} [AddCommGroup A] (t : Ext O D N →+ A)
  (eO : O ≅ O') (eD : D ≅ D')

/-- The trace on `Ext^N(O', D')` corresponding to `t` under isomorphisms `O ≅ O'`, `D ≅ D'`. -/
noncomputable def transportTrace : Ext O' D' N →+ A :=
  t.comp (AddMonoidHom.mk' (fun z => (mk₀ eO.hom).comp (z.comp (mk₀ eD.inv) (add_zero N))
    (zero_add N)) (fun z z' => by simp [Ext.add_comp, Ext.comp_add]))

/-- The transported trace `transportTrace t eO eD` takes the value `t (x ∘ y)` on the composite of
`x` and `y` transported along `eO` and `eD`. -/
lemma transportTrace_comp (F : C) {i j : ℕ} (h : i + j = N) (x : Ext O F i) (y : Ext F D j) :
    transportTrace t eO eD (((mk₀ eO.inv).comp x (zero_add i)).comp (y.comp (mk₀ eD.hom)
      (add_zero j)) h) = t (x.comp y h) := by
  simp only [transportTrace, AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply]
  congr 1
  rw [comp_assoc_of_third_deg_zero, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, eD.hom_inv_id,
    comp_mk₀_id, comp_assoc (mk₀ eO.inv) x y (zero_add i) h (by omega), mk₀_comp_mk₀_assoc,
    eO.hom_inv_id, mk₀_id_comp]

/-- **Duality is invariant under isomorphisms of `O` and `D`**, for the transported trace. -/
theorem isDualityPerfect_transport_iff (F : C) :
    IsDualityPerfect O D N t F ↔ IsDualityPerfect O' D' N (transportTrace t eO eD) F := by
  refine forall_congr' fun i => forall_congr' fun j => forall_congr' fun h => ?_
  let α : Ext O F i ≃ Ext O' F i :=
    { toFun x := (mk₀ eO.inv).comp x (zero_add i)
      invFun x := (mk₀ eO.hom).comp x (zero_add i)
      left_inv x := by simp
      right_inv x := by simp }
  let β : Ext F D j ≃+ Ext F D' j :=
    { toFun y := y.comp (mk₀ eD.hom) (add_zero j)
      invFun y := y.comp (mk₀ eD.inv) (add_zero j)
      left_inv y := by simp
      right_inv y := by simp
      map_add' y y' := by simp [Ext.add_comp] }
  let pre : (Ext F D' j →+ A) ≃ (Ext F D j →+ A) :=
    { toFun φ := φ.comp β.toAddMonoidHom
      invFun φ := φ.comp β.symm.toAddMonoidHom
      left_inv φ := by ext; simp
      right_inv φ := by ext; simp }
  have hcomp : pre ∘ (dualityPairing O' D' N (transportTrace t eO eD) F h) ∘ α =
      dualityPairing O D N t F h := funext fun x => by
    ext y
    exact transportTrace_comp t eO eD F h x y
  rw [← hcomp]
  exact ⟨fun hb => (Function.Bijective.of_comp_iff _ α.bijective).1
      ((Function.Bijective.of_comp_iff' pre.bijective _).1 hb),
    fun hb => pre.bijective.comp (hb.comp α.bijective)⟩

end Iso

/-- Precomposing with `f : F ⟶ G` on the `Ext^i(O, -)` side corresponds to precomposing the
pairing at `G` with `f` on the `Ext^j(-, D)` side. -/
private lemma dualityPairing_comp_mk₀ {O D : C} {N : ℕ} {A : Type*} [AddCommGroup A]
    (t : Ext O D N →+ A) {F G : C} (f : F ⟶ G) {i j : ℕ} (h : i + j = N) (x : Ext O F i) :
    dualityPairing O D N t G h (x.comp (mk₀ f) (add_zero i)) =
      (dualityPairing O D N t F h x).comp ((mk₀ f).precomp D (zero_add j)) := by
  ext y
  simp [comp_assoc_of_second_deg_zero]

/-- If the pairing at `G` is injective, `x ∈ Ext^i(O, F)` killed by the pairing at `F` is killed
by `f : F ⟶ G`. -/
private lemma comp_mk₀_eq_zero_of_dualityPairing_eq_zero {O D : C} {N : ℕ} {A : Type*}
    [AddCommGroup A] (t : Ext O D N →+ A) {F G : C} (f : F ⟶ G) {i j : ℕ} (h : i + j = N)
    (hG : Function.Injective (dualityPairing O D N t G h)) (x : Ext O F i)
    (hx : dualityPairing O D N t F h x = 0) : x.comp (mk₀ f) (add_zero i) = 0 := by
  apply hG
  rw [map_zero, dualityPairing_comp_mk₀, hx]
  rfl

section Devissage

variable {O D : C} {N : ℕ} {A : Type*} [AddCommGroup A] {t : Ext O D N →+ A}
  {S : ShortComplex C} (hS : S.ShortExact)

/-- A homomorphism `Ext^j(X₃, D) → A` vanishing on the kernel of `Ext^j(X₃, D) → Ext^j(X₂, D)`
is in the image of the pairing at `X₃` when the pairing at `X₂` is onto. -/
lemma mem_range_dualityPairing_X₃ {i j : ℕ} (h : i + j = N)
    (hGsurj : Function.Surjective (dualityPairing O D N t S.X₂ h))
    (hA : ∀ (H : AddSubgroup (Ext S.X₂ D j)) (φ : H →+ A), ∃ ψ : Ext S.X₂ D j →+ A,
      ∀ x : H, ψ x = φ x)
    (ψ : Ext S.X₃ D j →+ A)
    (hψ : ∀ y : Ext S.X₃ D j, (mk₀ S.g).comp y (zero_add j) = 0 → ψ y = 0) :
    ∃ x, dualityPairing O D N t S.X₃ h x = ψ := by
  obtain ⟨ψ', hψ'⟩ := exists_comp_eq_of_ker_le hA ((mk₀ S.g).precomp D (zero_add j)) ψ
    (fun y hy => hψ y hy)
  obtain ⟨g, hg⟩ := hGsurj ψ'
  refine ⟨g.comp (mk₀ S.g) (add_zero i), AddMonoidHom.ext fun y => ?_⟩
  rw [dualityPairing_comp_mk₀, hg, hψ']

include hS in
/-- The pairing at `X₃` in degrees `i + j = N` is surjective if the pairing at `X₂` is, `A` has
the extension property for subgroups of `Ext^j(X₂, D)`, and, when `j = j' + 1`, the pairing at
`X₁` is surjective and the pairing at `X₂` is injective in degrees `(i + 1, j')`. -/
lemma surjective_dualityPairing_X₃ {i j : ℕ} (h : i + j = N)
    (hGsurj : Function.Surjective (dualityPairing O D N t S.X₂ h))
    (hA : ∀ (H : AddSubgroup (Ext S.X₂ D j)) (φ : H →+ A), ∃ ψ : Ext S.X₂ D j →+ A,
      ∀ x : H, ψ x = φ x)
    (hstep : ∀ (j' : ℕ) (hj : j = j' + 1),
      Function.Surjective (dualityPairing O D N t S.X₁ (show i + 1 + j' = N by omega)) ∧
      Function.Injective (dualityPairing O D N t S.X₂ (show i + 1 + j' = N by omega))) :
    Function.Surjective (dualityPairing O D N t S.X₃ h) := by
  intro φ
  obtain ⟨x', hx'⟩ : ∃ x' : Ext O S.X₃ i, ∀ y : Ext S.X₃ D j,
      (mk₀ S.g).comp y (zero_add j) = 0 → φ y = t (x'.comp y h) := by
    rcases j with _ | j'
    · refine ⟨0, fun y hy => ?_⟩
      obtain rfl : y = 0 := by
        have := hS.epi_g
        apply precomp_mk₀_injective_of_epi D S.g
        simpa using hy
      simp
    · obtain ⟨hKs, hGi⟩ := hstep j' rfl
      obtain ⟨k, hk⟩ := hKs (φ.comp ((hS.extClass).precomp D (add_comm 1 j')))
      have hk0 : k.comp (mk₀ S.f) (add_zero _) = 0 := by
        apply hGi
        rw [map_zero]
        refine AddMonoidHom.ext fun y => ?_
        rw [dualityPairing_apply, comp_assoc_of_second_deg_zero, AddMonoidHom.zero_apply]
        have := congrArg (fun F => F ((mk₀ S.f).comp y (zero_add j'))) hk
        simp only [dualityPairing_apply, AddMonoidHom.comp_apply] at this
        rw [this]
        simp [hS.extClass_comp_assoc]
      obtain ⟨x', hx'⟩ := covariant_sequence_exact₁ O hS k hk0 rfl
      refine ⟨x', fun y hy => ?_⟩
      obtain ⟨y₁, rfl⟩ := contravariant_sequence_exact₃ hS D y hy (add_comm 1 j')
      have this' : t (k.comp y₁ (by omega)) = φ (hS.extClass.comp y₁ (add_comm 1 j')) :=
        DFunLike.congr_fun hk y₁
      rw [← this', ← hx', comp_assoc]
      omega
  obtain ⟨x₂, hx₂⟩ := mem_range_dualityPairing_X₃ h hGsurj hA
    (φ - dualityPairing O D N t S.X₃ h x') (fun y hy => by
      simp [hx' y hy])
  exact ⟨x' + x₂, by rw [map_add, hx₂, add_sub_cancel]⟩

include hS in
/-- The pairing at `X₃` in degrees `i + j = N` is injective if the pairing at `X₁` is surjective,
the pairing at `X₂` is injective, `A` has the extension property for subgroups of `Ext^j(X₁, D)`,
and every `x` in the kernel of the pairing at `X₃` has `x ∘ δ = 0` for the extension class `δ`. -/
lemma injective_dualityPairing_X₃ {i j : ℕ} (h : i + j = N)
    (hKsurj : Function.Surjective (dualityPairing O D N t S.X₁ h))
    (hGinj : Function.Injective (dualityPairing O D N t S.X₂ h))
    (hA : ∀ (H : AddSubgroup (Ext S.X₁ D j)) (φ : H →+ A), ∃ ψ : Ext S.X₁ D j →+ A,
      ∀ x : H, ψ x = φ x)
    (hδ : ∀ x : Ext O S.X₃ i, dualityPairing O D N t S.X₃ h x = 0 →
      x.comp hS.extClass rfl = 0) :
    Function.Injective (dualityPairing O D N t S.X₃ h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨g, rfl⟩ := covariant_sequence_exact₃ O hS x rfl (hδ x hx)
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_ker_le hA ((mk₀ S.f).precomp D (zero_add j))
    (dualityPairing O D N t S.X₂ h g) (fun y hy => by
      obtain ⟨y', rfl⟩ := contravariant_sequence_exact₂ hS D y hy
      have := congrArg (fun F => F y') hx
      simp only [dualityPairing_apply, AddMonoidHom.zero_apply] at this
      simp only [AddMonoidHom.mem_ker, dualityPairing_apply]
      rw [← comp_assoc_of_second_deg_zero]
      exact this)
  obtain ⟨k, hk⟩ := hKsurj ψ
  have hg : g = k.comp (mk₀ S.f) (add_zero i) := by
    apply hGinj
    rw [dualityPairing_comp_mk₀, hk, hψ]
  rw [hg, comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, S.zero, mk₀_zero, comp_zero]

end Devissage

variable (O D : C) (N : ℕ) {A : Type*} [AddCommGroup A] (t : Ext O D N →+ A)

/-- **Poincaré-type duality by dévissage.** Let `P` be a class of objects such that every
`F ∈ P` is the cokernel of a monomorphism `K → G` with `K ∈ P` and duality at `G`, and such that
`Ext^{N+1}(O, K) = 0` for `K ∈ P`. If `A` has the extension property for subgroups of the groups
`Ext^j(M, D)` (for instance `A = ℤ/n` and all `Ext` groups are `ℤ/n`-modules), duality holds at
every object of `P`. -/
theorem isDualityPerfect_of_resolution (P : C → Prop)
    (hres : ∀ F, P F → ∃ S : ShortComplex C, S.ShortExact ∧ S.X₃ = F ∧ P S.X₁ ∧
      IsDualityPerfect O D N t S.X₂)
    (hvan : ∀ K, P K → Subsingleton (Ext O K (N + 1)))
    (hA : ∀ (M : C) (j : ℕ) (H : AddSubgroup (Ext M D j)) (φ : H →+ A),
      ∃ ψ : Ext M D j →+ A, ∀ x : H, ψ x = φ x) :
    ∀ F, P F → IsDualityPerfect O D N t F := by
  suffices H : ∀ j : ℕ, ∀ F, P F → ∀ (i : ℕ) (h : i + j = N),
      Function.Bijective (dualityPairing O D N t F h) from
    fun F hF i j h => H j F hF i h
  intro j
  induction j with
  | zero =>
    have hsurj : ∀ F, P F → ∀ (i : ℕ) (h : i + 0 = N),
        Function.Surjective (dualityPairing O D N t F h) := by
      intro F hF i h
      obtain ⟨S, hS, rfl, -, hG⟩ := hres F hF
      exact surjective_dualityPairing_X₃ hS h (hG i 0 h).2 (hA _ _)
        (fun j' hj => absurd hj (by omega))
    intro F hF i h
    refine ⟨?_, hsurj F hF i h⟩
    obtain ⟨S, hS, rfl, hK, hG⟩ := hres F hF
    refine injective_dualityPairing_X₃ hS h (hsurj _ hK i h) (hG i 0 h).1 (hA _ _)
      (fun x _ => ?_)
    have : Subsingleton (Ext O S.X₁ (i + 1)) := by
      obtain rfl : i = N := by omega
      exact hvan _ hK
    exact Subsingleton.elim _ _
  | succ j ih =>
    have hsurj : ∀ F, P F → ∀ (i : ℕ) (h : i + (j + 1) = N),
        Function.Surjective (dualityPairing O D N t F h) := by
      intro F hF i h
      obtain ⟨S, hS, rfl, hK, hG⟩ := hres F hF
      exact surjective_dualityPairing_X₃ hS h (hG i _ h).2 (hA _ _)
        (fun j' hj => by
          obtain rfl : j' = j := by omega
          exact ⟨(ih _ hK (i + 1) _).2, (hG (i + 1) j' _).1⟩)
    intro F hF i h
    refine ⟨?_, hsurj F hF i h⟩
    obtain ⟨S, hS, rfl, hK, hG⟩ := hres F hF
    refine injective_dualityPairing_X₃ hS h (hsurj _ hK i h) (hG i _ h).1 (hA _ _)
      (fun x hx => ?_)
    apply (ih _ hK (i + 1) (by omega)).1
    rw [map_zero]
    refine AddMonoidHom.ext fun y => ?_
    rw [dualityPairing_apply, comp_assoc, AddMonoidHom.zero_apply]
    · simpa using DFunLike.congr_fun hx (hS.extClass.comp y (add_comm 1 j))
    · omega

section FiveLemma

variable {O D : C} {N : ℕ} {A : Type*} [AddCommGroup A] {t : Ext O D N →+ A}
  {S : ShortComplex C} (hS : S.ShortExact)

include hS in
/-- The pairing at `X₂` in degrees `i + j = N` is injective if the pairings at `X₁` and `X₃` are,
`A` has the extension property for subgroups of `Ext^{j+1}(X₃, D)`, the pairing at `X₃` is
surjective in degrees `(i', j + 1)` when `i = i' + 1`, and `Ext^{j+1}(X₃, D) = 0` when `i = 0`. -/
lemma injective_dualityPairing_X₂ {i j : ℕ} (h : i + j = N)
    (h₃ : Function.Injective (dualityPairing O D N t S.X₃ h))
    (h₁ : Function.Injective (dualityPairing O D N t S.X₁ h))
    (hA : ∀ (H : AddSubgroup (Ext S.X₃ D (j + 1))) (φ : H →+ A),
      ∃ ψ : Ext S.X₃ D (j + 1) →+ A, ∀ x : H, ψ x = φ x)
    (hstep : ∀ (i' : ℕ) (hi : i = i' + 1),
      Function.Surjective (dualityPairing O D N t S.X₃ (show i' + (j + 1) = N by omega)))
    (hvan : i = 0 → Subsingleton (Ext S.X₃ D (j + 1))) :
    Function.Injective (dualityPairing O D N t S.X₂ h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx3 := comp_mk₀_eq_zero_of_dualityPairing_eq_zero t S.g h h₃ x hx
  obtain ⟨x₁, rfl⟩ := covariant_sequence_exact₂ O hS x hx3
  obtain ⟨χ, hχ⟩ := exists_comp_eq_of_ker_le hA (hS.extClass.precomp D (add_comm 1 j))
    (dualityPairing O D N t S.X₁ h x₁) (fun y hy => by
      obtain ⟨y₂, rfl⟩ := contravariant_sequence_exact₁ hS D y (add_comm 1 j) hy
      have := DFunLike.congr_fun hx y₂
      rw [dualityPairing_apply, comp_assoc_of_second_deg_zero, AddMonoidHom.zero_apply] at this
      exact this)
  have hx₁ : x₁ = 0 ∨
      ∃ (i' : ℕ) (z : Ext O S.X₃ i') (hi : i' + 1 = i), z.comp hS.extClass hi = x₁ := by
    rcases i with _ | i'
    · left
      have := hvan rfl
      apply h₁
      rw [map_zero, ← hχ]
      ext y
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply]
      rw [Subsingleton.elim ((hS.extClass.precomp D (add_comm 1 j)) y) 0, map_zero]
    · right
      obtain ⟨z, hz⟩ := hstep i' rfl χ
      refine ⟨i', z, rfl, h₁ ?_⟩
      rw [← hχ, ← hz]
      ext y
      simp only [AddMonoidHom.comp_apply, dualityPairing_apply]
      exact congrArg t (comp_assoc z hS.extClass y rfl (add_comm 1 j) (by omega))
  rcases hx₁ with rfl | ⟨i', z, rfl, rfl⟩
  · rw [zero_comp]
  · rw [comp_assoc_of_third_deg_zero, hS.extClass_comp, comp_zero]

include hS in
/-- The pairing at `X₂` in degrees `i + j = N` is surjective if the pairings at `X₁` and `X₃` are,
`A` has the extension property for subgroups of `Ext^j(X₁, D)`, the pairing at `X₁` is injective
in degrees `(i + 1, j')` when `j = j' + 1`, and `Ext^{i+1}(O, X₁) = 0` when `j = 0`. -/
lemma surjective_dualityPairing_X₂ {i j : ℕ} (h : i + j = N)
    (h₃ : Function.Surjective (dualityPairing O D N t S.X₃ h))
    (h₁ : Function.Surjective (dualityPairing O D N t S.X₁ h))
    (hA : ∀ (H : AddSubgroup (Ext S.X₁ D j)) (φ : H →+ A),
      ∃ ψ : Ext S.X₁ D j →+ A, ∀ x : H, ψ x = φ x)
    (hstep : ∀ (j' : ℕ) (hj : j = j' + 1),
      Function.Injective (dualityPairing O D N t S.X₁ (show i + 1 + j' = N by omega)))
    (hvan : j = 0 → Subsingleton (Ext O S.X₁ (i + 1))) :
    Function.Surjective (dualityPairing O D N t S.X₂ h) := by
  intro φ
  obtain ⟨x₃, hx₃⟩ := h₃ (φ.comp ((mk₀ S.g).precomp D (zero_add j)))
  have he : x₃.comp hS.extClass rfl = 0 := by
    rcases j with _ | j'
    · have := hvan rfl
      exact Subsingleton.elim _ _
    · apply hstep j' rfl
      rw [map_zero]
      ext y
      rw [dualityPairing_apply, AddMonoidHom.zero_apply,
        comp_assoc x₃ hS.extClass y rfl (add_comm 1 j') (by omega)]
      have := DFunLike.congr_fun hx₃ (hS.extClass.comp y (add_comm 1 j'))
      rw [dualityPairing_apply] at this
      rw [this, AddMonoidHom.comp_apply]
      simp [hS.comp_extClass_assoc]
  obtain ⟨x₂, rfl⟩ := covariant_sequence_exact₃ O hS x₃ rfl he
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_ker_le hA ((mk₀ S.f).precomp D (zero_add j))
    (φ - dualityPairing O D N t S.X₂ h x₂) (fun y hy => by
      obtain ⟨y₃, rfl⟩ := contravariant_sequence_exact₂ hS D y hy
      have := DFunLike.congr_fun hx₃ y₃
      rw [dualityPairing_apply, AddMonoidHom.comp_apply, comp_assoc_of_second_deg_zero] at this
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, dualityPairing_apply]
      exact sub_eq_zero.2 this.symm)
  obtain ⟨x₁, hx₁⟩ := h₁ ψ
  refine ⟨x₂ + x₁.comp (mk₀ S.f) (add_zero i), ?_⟩
  rw [map_add]
  have : dualityPairing O D N t S.X₂ h (x₁.comp (mk₀ S.f) (add_zero i)) =
      φ - dualityPairing O D N t S.X₂ h x₂ := by
    rw [dualityPairing_comp_mk₀, hx₁, hψ]
  rw [this, add_sub_cancel]

include hS in
/-- **Duality in a short exact sequence**: duality at `X₁` and at `X₃` gives duality at `X₂`, when
`Ext^{N+1}(O, X₁) = 0` and `Ext^{N+1}(X₃, D) = 0` and `A` has the extension property. -/
theorem isDualityPerfect_X₂ (h₁ : IsDualityPerfect O D N t S.X₁)
    (h₃ : IsDualityPerfect O D N t S.X₃) (hv₁ : Subsingleton (Ext O S.X₁ (N + 1)))
    (hv₃ : Subsingleton (Ext S.X₃ D (N + 1)))
    (hA : ∀ (M : C) (j : ℕ) (H : AddSubgroup (Ext M D j)) (φ : H →+ A),
      ∃ ψ : Ext M D j →+ A, ∀ x : H, ψ x = φ x) :
    IsDualityPerfect O D N t S.X₂ := by
  intro i j h
  refine ⟨injective_dualityPairing_X₂ hS h (h₃ i j h).1 (h₁ i j h).1 (hA _ _)
    (fun i' hi => (h₃ i' (j + 1) _).2) (fun hi => by
      obtain rfl : j = N := by omega
      exact hv₃),
    surjective_dualityPairing_X₂ hS h (h₃ i j h).2 (h₁ i j h).2 (hA _ _)
    (fun j' hj => (h₁ (i + 1) j' _).1) (fun hj => by
      obtain rfl : i = N := by omega
      exact hv₁)⟩

end FiveLemma

/-- **Duality passes to retracts**: if `i ≫ r = 𝟙 F` for `i : F ⟶ G`, `r : G ⟶ F`, duality at `G`
gives duality at `F`. -/
theorem isDualityPerfect_of_retract {O D : C} {N : ℕ} {A : Type*} [AddCommGroup A]
    {t : Ext O D N →+ A} {F G : C} (i : F ⟶ G) (r : G ⟶ F) (hir : i ≫ r = 𝟙 F)
    (hG : IsDualityPerfect O D N t G) : IsDualityPerfect O D N t F := by
  intro a b h
  have hri : ∀ {n : ℕ} (x : Ext O F n), (x.comp (mk₀ i) (add_zero n)).comp (mk₀ r) (add_zero n) =
      x := fun x => by rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, hir, comp_mk₀_id]
  have hri' : ∀ {n : ℕ} (y : Ext F D n), (mk₀ i).comp ((mk₀ r).comp y (zero_add n)) (zero_add n) =
      y := fun y => by rw [mk₀_comp_mk₀_assoc, hir, mk₀_id_comp]
  refine ⟨?_, fun φ => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [← hri x, comp_mk₀_eq_zero_of_dualityPairing_eq_zero t i h (hG a b h).1 x hx, zero_comp]
  · obtain ⟨g, hg⟩ := (hG a b h).2 (φ.comp ((mk₀ i).precomp D (zero_add b)))
    refine ⟨g.comp (mk₀ r) (add_zero a), ?_⟩
    ext y
    rw [dualityPairing_comp_mk₀, hg]
    exact congrArg φ (hri' y)

end CategoryTheory.Abelian.Ext
