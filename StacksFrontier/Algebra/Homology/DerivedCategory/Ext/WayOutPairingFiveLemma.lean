module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairing
public import StacksFrontier.Order.MayerVietorisInduction

/-!
# Duality at the outer terms of a short exact sequence, and at a direct sum

For a trace `t : Ext^N(O, D) → A` and the Yoneda pairing
`Ext^i(O, F) × Ext^j(F, D) → A`, `i + j = N` (`CategoryTheory.Abelian.Ext.IsDualityPerfect`):

* in a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, duality at `X₁` and at `X₂` gives duality at
  `X₃`, when `Ext^{N+1}(O, X₁) = 0` and `A` has the extension property for subgroups of the groups
  `Ext^j(M, D)` (the five lemma at the third term; the middle term is
  `CategoryTheory.Abelian.Ext.isDualityPerfect_X₂`);
* dually, duality at `X₂` and at `X₃` gives duality at `X₁`, when `Ext^{N+1}(X₃, D) = 0`;
* duality holds at `G ⊞ H` if and only if it holds at `G` and at `H`.

These are the two inputs of the Mayer–Vietoris step of Poincaré duality: for an open cover
`U = V ∪ W` the sequence `0 → j_{V∩W!}F → j_{V!}F ⊕ j_{W!}F → j_{U!}F → 0` is exact, and of
excision: for `Z` closed in `X̄` with complement `U`, `0 → j_!Λ_U → Λ_X̄ → i_*Λ_Z → 0`.

## Main results

* `CategoryTheory.Abelian.Ext.isDualityPerfect_X₃`.
* `CategoryTheory.Abelian.Ext.isDualityPerfect_X₁`.
* `CategoryTheory.Abelian.Ext.isDualityPerfect_biprod_iff`.
* `CategoryTheory.Abelian.Ext.isDualityPerfect_sup'_of_shortExact`: Mayer–Vietoris gluing of
  duality over a finite cover, all of whose finite intersections satisfy it.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Abelian.Ext

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {O D : C} {N : ℕ} {A : Type*} [AddCommGroup A] {t : Ext O D N →+ A}

section ThirdTerm

variable {S : ShortComplex C} (hS : S.ShortExact)

include hS in
/-- **Duality at the third term of a short exact sequence**: duality at `X₁` and at `X₂` gives
duality at `X₃`, when `Ext^{N+1}(O, X₁) = 0` and `A` has the extension property for subgroups of
the groups `Ext^j(M, D)`. -/
theorem isDualityPerfect_X₃ (h₁ : IsDualityPerfect O D N t S.X₁)
    (h₂ : IsDualityPerfect O D N t S.X₂) (hv₁ : Subsingleton (Ext O S.X₁ (N + 1)))
    (hA : ∀ (M : C) (j : ℕ) (H : AddSubgroup (Ext M D j)) (φ : H →+ A),
      ∃ ψ : Ext M D j →+ A, ∀ x : H, ψ x = φ x) :
    IsDualityPerfect O D N t S.X₃ := by
  intro i j h
  refine ⟨injective_dualityPairing_X₃ hS h (h₁ i j h).2 (h₂ i j h).1 (hA _ _) (fun x hx => ?_),
    surjective_dualityPairing_X₃ hS h (h₂ i j h).2 (hA _ _)
      (fun j' hj => ⟨(h₁ (i + 1) j' _).2, (h₂ (i + 1) j' _).1⟩)⟩
  rcases j with _ | j'
  · obtain rfl : i = N := by omega
    exact Subsingleton.elim _ _
  · apply (h₁ (i + 1) j' (by omega)).1
    rw [map_zero]
    refine AddMonoidHom.ext fun y => ?_
    rw [dualityPairing_apply, comp_assoc x hS.extClass y rfl (add_comm 1 j') (by omega),
      AddMonoidHom.zero_apply]
    simpa using DFunLike.congr_fun hx (hS.extClass.comp y (add_comm 1 j'))

/-- If `x : Ext^i(O, F)` pairs to zero with every `f ≫ y`, then `x ≫ f` vanishes, provided duality
is injective at the target of `f`. -/
private theorem comp_mk₀_eq_zero_of_dualityPairing {F G : C} (f : F ⟶ G) {i j : ℕ} (h : i + j = N)
    (hG : Function.Injective (dualityPairing O D N t G h)) {x : Ext O F i}
    (hx : ∀ y : Ext G D j, dualityPairing O D N t F h x ((mk₀ f).comp y (zero_add j)) = 0) :
    x.comp (mk₀ f) (add_zero i) = 0 := by
  apply hG
  rw [map_zero]
  ext y
  rw [dualityPairing_apply, comp_assoc_of_second_deg_zero, AddMonoidHom.zero_apply]
  exact hx y

include hS in
/-- **Five lemma, injectivity at `X₁`.** -/
lemma injective_dualityPairing_X₁ {i j : ℕ} (h : i + j = N)
    (h₂ : Function.Injective (dualityPairing O D N t S.X₂ h))
    (hA : ∀ (H : AddSubgroup (Ext S.X₂ D (j + 1))) (φ : H →+ A),
      ∃ ψ : Ext S.X₂ D (j + 1) →+ A, ∀ x : H, ψ x = φ x)
    (hstep : ∀ (i' : ℕ) (hi : i = i' + 1),
      Function.Surjective (dualityPairing O D N t S.X₂ (show i' + (j + 1) = N by omega)) ∧
      Function.Injective (dualityPairing O D N t S.X₃ (show i' + (j + 1) = N by omega))) :
    Function.Injective (dualityPairing O D N t S.X₁ h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hxf : x.comp (mk₀ S.f) (add_zero i) = 0 :=
    comp_mk₀_eq_zero_of_dualityPairing S.f h h₂ fun y => DFunLike.congr_fun hx _
  rcases i with _ | i'
  · have := hS.mono_f
    obtain ⟨g', rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    rw [mk₀_comp_mk₀, ← mk₀_zero] at hxf
    have hg' : g' = 0 := by
      rw [← cancel_mono S.f, Limits.zero_comp]
      exact (Ext.mk₀_bijective _ _).1 hxf
    rw [hg', mk₀_zero]
  · obtain ⟨hs₂, hi₃⟩ := hstep i' rfl
    obtain ⟨z, rfl⟩ := covariant_sequence_exact₁ O hS x hxf rfl
    -- `P z` vanishes on the image of `δ^*`, which is the kernel of `g^*`
    obtain ⟨χ, hχ⟩ := exists_comp_eq_of_ker_le hA ((mk₀ S.g).precomp D (zero_add (j + 1)))
      (dualityPairing O D N t S.X₃ (show i' + (j + 1) = N by omega) z) (fun y hy => by
        obtain ⟨y₁, rfl⟩ := contravariant_sequence_exact₃ hS D y hy (add_comm 1 j)
        have := DFunLike.congr_fun hx y₁
        rw [dualityPairing_apply, AddMonoidHom.zero_apply] at this
        simp only [AddMonoidHom.mem_ker, dualityPairing_apply]
        rw [← comp_assoc z hS.extClass y₁ rfl (add_comm 1 j) (by omega)]
        exact this)
    obtain ⟨x₂, hx₂⟩ := hs₂ χ
    have hz : z = x₂.comp (mk₀ S.g) (add_zero i') := by
      apply hi₃
      refine AddMonoidHom.ext fun y => ?_
      have e := DFunLike.congr_fun hχ y
      rw [AddMonoidHom.comp_apply, ← hx₂, dualityPairing_apply, dualityPairing_apply] at e
      rw [dualityPairing_apply, dualityPairing_apply, comp_assoc_of_second_deg_zero]
      exact e.symm
    rw [hz, comp_assoc_of_second_deg_zero, hS.comp_extClass, comp_zero]

include hS in
/-- **Five lemma, surjectivity at `X₁`.** -/
lemma surjective_dualityPairing_X₁ {i j : ℕ} (h : i + j = N)
    (h₂ : Function.Surjective (dualityPairing O D N t S.X₂ h))
    (h₃ : Function.Injective (dualityPairing O D N t S.X₃ h))
    (_hA : ∀ (H : AddSubgroup (Ext S.X₁ D j)) (φ : H →+ A),
      ∃ ψ : Ext S.X₁ D j →+ A, ∀ x : H, ψ x = φ x)
    (hA₃ : ∀ (H : AddSubgroup (Ext S.X₃ D (j + 1))) (φ : H →+ A),
      ∃ ψ : Ext S.X₃ D (j + 1) →+ A, ∀ x : H, ψ x = φ x)
    (hstep : ∀ (i' : ℕ) (hi : i = i' + 1),
      Function.Surjective (dualityPairing O D N t S.X₃ (show i' + (j + 1) = N by omega)))
    (hvan : i = 0 → Subsingleton (Ext S.X₃ D (j + 1))) :
    Function.Surjective (dualityPairing O D N t S.X₁ h) := by
  intro φ
  obtain ⟨x₂, hx₂⟩ := h₂ (φ.comp ((mk₀ S.f).precomp D (zero_add j)))
  have hx₂g : x₂.comp (mk₀ S.g) (add_zero i) = 0 := by
    refine comp_mk₀_eq_zero_of_dualityPairing S.g h h₃ fun y => ?_
    rw [hx₂]
    simp [mk₀_comp_mk₀_assoc]
  obtain ⟨x₁, rfl⟩ := covariant_sequence_exact₂ O hS x₂ hx₂g
  -- `φ - P x₁` vanishes on the image of `f^*`, which is the kernel of `δ^*`
  obtain ⟨χ, hχ⟩ := exists_comp_eq_of_ker_le hA₃ (hS.extClass.precomp D (add_comm 1 j))
    (φ - dualityPairing O D N t S.X₁ h x₁) (fun y hy => by
      obtain ⟨y₂, rfl⟩ := contravariant_sequence_exact₁ hS D y (add_comm 1 j) hy
      have := DFunLike.congr_fun hx₂ y₂
      rw [dualityPairing_apply, AddMonoidHom.comp_apply, comp_assoc_of_second_deg_zero] at this
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, dualityPairing_apply]
      exact sub_eq_zero.2 this.symm)
  rcases i with _ | i'
  · have := hvan rfl
    refine ⟨x₁, ?_⟩
    have : φ - dualityPairing O D N t S.X₁ h x₁ = 0 := by
      rw [← hχ]
      ext y
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply]
      rw [Subsingleton.elim ((hS.extClass.precomp D (add_comm 1 j)) y) 0, map_zero]
    exact (sub_eq_zero.1 this).symm
  · obtain ⟨z, hz⟩ := hstep i' rfl χ
    refine ⟨x₁ + z.comp hS.extClass rfl, ?_⟩
    rw [map_add, add_comm, ← eq_sub_iff_add_eq, ← hχ, ← hz]
    ext y
    simp only [AddMonoidHom.comp_apply, dualityPairing_apply]
    exact congrArg t (comp_assoc z hS.extClass y rfl (add_comm 1 j) (by omega))

include hS in
/-- **Duality at the first term of a short exact sequence**: duality at `X₂` and at `X₃` gives
duality at `X₁`, when `Ext^{N+1}(X₃, D) = 0` and `A` has the extension property for subgroups of
the groups `Ext^j(M, D)`. -/
theorem isDualityPerfect_X₁ (h₂ : IsDualityPerfect O D N t S.X₂)
    (h₃ : IsDualityPerfect O D N t S.X₃) (hv₃ : Subsingleton (Ext S.X₃ D (N + 1)))
    (hA : ∀ (M : C) (j : ℕ) (H : AddSubgroup (Ext M D j)) (φ : H →+ A),
      ∃ ψ : Ext M D j →+ A, ∀ x : H, ψ x = φ x) :
    IsDualityPerfect O D N t S.X₁ := by
  intro i j h
  refine ⟨injective_dualityPairing_X₁ hS h (h₂ i j h).1 (hA _ _)
      (fun i' hi => ⟨(h₂ i' (j + 1) _).2, (h₃ i' (j + 1) _).1⟩),
    surjective_dualityPairing_X₁ hS h (h₂ i j h).2 (h₃ i j h).1 (hA _ _) (hA _ _)
      (fun i' hi => (h₃ i' (j + 1) _).2) (fun hi => by
        obtain rfl : j = N := by omega
        exact hv₃)⟩

end ThirdTerm

section Biprod

variable (G H : C)

/-- **Duality at a direct sum**: duality holds at `G ⊞ H` if and only if it holds at `G` and at
`H`. -/
theorem isDualityPerfect_biprod_iff :
    IsDualityPerfect O D N t (G ⊞ H) ↔
      IsDualityPerfect O D N t G ∧ IsDualityPerfect O D N t H := by
  refine ⟨fun hGH => ⟨isDualityPerfect_of_retract biprod.inl biprod.fst biprod.inl_fst hGH,
    isDualityPerfect_of_retract biprod.inr biprod.snd biprod.inr_snd hGH⟩, fun ⟨hG, hH⟩ => ?_⟩
  -- `𝟙 (G ⊞ H) = fst ≫ inl + snd ≫ inr`, read on both sides of the pairing
  have hl : ∀ {n : ℕ} (x : Ext O (G ⊞ H) n),
      (x.comp (mk₀ biprod.fst) (add_zero n)).comp (mk₀ biprod.inl) (add_zero n) +
        (x.comp (mk₀ biprod.snd) (add_zero n)).comp (mk₀ biprod.inr) (add_zero n) = x := by
    intro n x
    rw [comp_assoc_of_third_deg_zero, comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, mk₀_comp_mk₀,
      ← comp_add, ← mk₀_add, biprod.total, comp_mk₀_id]
  have hr : ∀ {n : ℕ} (y : Ext (G ⊞ H) D n),
      (mk₀ biprod.fst).comp ((mk₀ biprod.inl).comp y (zero_add n)) (zero_add n) +
        (mk₀ biprod.snd).comp ((mk₀ biprod.inr).comp y (zero_add n)) (zero_add n) = y := by
    intro n y
    rw [mk₀_comp_mk₀_assoc, mk₀_comp_mk₀_assoc, ← add_comp, ← mk₀_add, biprod.total, mk₀_id_comp]
  intro a b h
  refine ⟨?_, fun φ => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ∀ {F : C} (π : G ⊞ H ⟶ F), IsDualityPerfect O D N t F →
        x.comp (mk₀ π) (add_zero a) = 0 := fun π hF =>
      comp_mk₀_eq_zero_of_dualityPairing π h (hF a b h).1 fun y => DFunLike.congr_fun hx _
    rw [← hl x, h0 biprod.fst hG, h0 biprod.snd hH, zero_comp, zero_comp, add_zero]
  · obtain ⟨g, hg⟩ := (hG a b h).2 (φ.comp ((mk₀ biprod.fst).precomp D (zero_add b)))
    obtain ⟨g', hg'⟩ := (hH a b h).2 (φ.comp ((mk₀ biprod.snd).precomp D (zero_add b)))
    refine ⟨g.comp (mk₀ biprod.inl) (add_zero a) + g'.comp (mk₀ biprod.inr) (add_zero a), ?_⟩
    ext y
    have e₁ := DFunLike.congr_fun hg ((mk₀ biprod.inl).comp y (zero_add b))
    have e₂ := DFunLike.congr_fun hg' ((mk₀ biprod.inr).comp y (zero_add b))
    rw [dualityPairing_apply, AddMonoidHom.comp_apply] at e₁ e₂
    rw [map_add, AddMonoidHom.add_apply, dualityPairing_apply, dualityPairing_apply,
      comp_assoc_of_second_deg_zero, comp_assoc_of_second_deg_zero, e₁, e₂, ← map_add]
    exact congrArg φ (hr y)

end Biprod

section MayerVietoris

/-- Duality is invariant under isomorphism of the object. -/
theorem isDualityPerfect_of_iso {F G : C} (e : F ≅ G) (hF : IsDualityPerfect O D N t F) :
    IsDualityPerfect O D N t G :=
  isDualityPerfect_of_retract e.inv e.hom e.inv_hom_id hF

/-- **Mayer–Vietoris gluing of duality.** Let `X` assign objects to the elements of a
distributive lattice (to the opens `V` of a space, the extension by zero `j_{V!}F|_V`) such that
for all `a, b` there is a short exact sequence `0 → X (a ⊓ b) → X a ⊞ X b → X (a ⊔ b) → 0` (up to
isomorphism of its terms), and `Ext^{N+1}(O, X a) = 0` for all `a`. If duality holds at `X` of
every finite meet of members of a finite nonempty family, it holds at `X` of their join. -/
theorem isDualityPerfect_sup'_of_shortExact {α ι : Type*} [DistribLattice α] (X : α → C)
    (hS : ∀ a b : α, ∃ S : ShortComplex C, S.ShortExact ∧ Nonempty (S.X₁ ≅ X (a ⊓ b)) ∧
      Nonempty (S.X₂ ≅ X a ⊞ X b) ∧ Nonempty (S.X₃ ≅ X (a ⊔ b)))
    (hvan : ∀ a, Subsingleton (Ext O (X a) (N + 1)))
    (hA : ∀ (M : C) (j : ℕ) (H : AddSubgroup (Ext M D j)) (φ : H →+ A),
      ∃ ψ : Ext M D j →+ A, ∀ x : H, ψ x = φ x)
    {s : Finset ι} (hs : s.Nonempty) (U : ι → α)
    (hU : ∀ K ⊆ s, ∀ hK : K.Nonempty, IsDualityPerfect O D N t (X (K.inf' hK U))) :
    IsDualityPerfect O D N t (X (s.sup' hs U)) := by
  refine Finset.prop_sup'_of_prop_inf' (fun a => IsDualityPerfect O D N t (X a))
    (fun a b ha hb hab => ?_) hs U hU
  obtain ⟨S, hSe, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := hS a b
  refine isDualityPerfect_of_iso e₃ (isDualityPerfect_X₃ hSe (isDualityPerfect_of_iso e₁.symm hab)
    (isDualityPerfect_of_iso e₂.symm ((isDualityPerfect_biprod_iff _ _).2 ⟨ha, hb⟩)) ?_ hA)
  have := hvan (a ⊓ b)
  have h : ∀ z : Ext O S.X₁ (N + 1),
      z = (z.comp (mk₀ e₁.hom) (add_zero _)).comp (mk₀ e₁.inv) (add_zero _) := fun z => by
    rw [comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, e₁.hom_inv_id, comp_mk₀_id]
  refine ⟨fun x y => ?_⟩
  rw [h x, h y, Subsingleton.elim (x.comp (mk₀ e₁.hom) (add_zero _))
    (y.comp (mk₀ e₁.hom) (add_zero _))]

end MayerVietoris

end CategoryTheory.Abelian.Ext
