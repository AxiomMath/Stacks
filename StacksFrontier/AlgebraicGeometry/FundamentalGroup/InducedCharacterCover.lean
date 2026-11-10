module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteGSetCover

/-!
# The torsor cover induced by a character of an open subgroup

Let `Γ` be a group, `V` a subgroup and `χ : V → A` an additive map to an abelian group. The
*induced torsor* `Γ ×^V A` is the quotient of `Γ × A` by `(g v, a) ∼ (g, a + χ v)`. The group `Γ`
acts on it by left multiplication on the first factor, `A` acts by translation on the second
factor, the two actions commute, and `[g, a] ↦ g V` maps it equivariantly onto `Γ / V` with
fibres the `A`-orbits; over the base coset the `A`-torsor `{[1, a]}` carries the action of `V`
through `χ`: `v • [1, a] = [1, a + χ v]`.

For `Γ = π₁(X, x)`, `V` open and `χ` locally constant with finite values, the induced torsor is a
finite continuous `Γ`-set, hence the geometric fibre of a finite étale cover `T_χ` of `X`
(`AlgebraicGeometry.exists_inducedCharacterCover`), mapping to the cover `Y_V` with fibre
`Γ / V`, with `A` acting on `T_χ` by automorphisms over `Y_V`. Its base change to `Y_V` is the
`A`-torsor over `Y_V` attached to `χ` read as a character of `π₁(Y_V)`.

The main point for counting characters is `Stacks.LAdic.eq_of_inducedTorsor_hom`: an
`A`-equivariant map between the base-coset fibres of two induced torsors commuting with `v ∈ V`
forces `χ₁ v = χ₂ v`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace Stacks.LAdic

variable {Γ : Type*} [Group Γ] (V : Subgroup Γ) {A : Type*} [AddCommGroup A]

variable {V} in
/-- A multiplicative-to-additive map on a subgroup sends `1` to `0`. -/
theorem map_one_eq_zero_of_map_mul {χ : V → A} (hadd : ∀ a b, χ (a * b) = χ a + χ b) :
    χ 1 = 0 := by
  have := hadd 1 1
  rw [mul_one] at this
  exact left_eq_add.1 this

/-- The relation `(g, a) ∼ (g', a')` iff `g⁻¹ g' ∈ V` and `a = a' + χ (g⁻¹ g')`. -/
def inducedTorsorSetoid (χ : V → A) (hadd : ∀ a b, χ (a * b) = χ a + χ b) : Setoid (Γ × A) where
  r p q := ∃ h : p.1⁻¹ * q.1 ∈ V, p.2 = q.2 + χ ⟨_, h⟩
  iseqv := by
    have h1 := map_one_eq_zero_of_map_mul hadd
    have hinv : ∀ v : V, χ v⁻¹ = -χ v := fun v => by
      have := hadd v v⁻¹
      rw [mul_inv_cancel, h1] at this
      exact (neg_eq_of_add_eq_zero_right this.symm).symm
    refine ⟨fun p => ⟨by simp, ?_⟩, fun {p q} ⟨h, hpq⟩ => ⟨?_, ?_⟩,
      fun {p q r} ⟨h, hpq⟩ ⟨h', hqr⟩ => ⟨?_, ?_⟩⟩
    · show p.2 = p.2 + χ ⟨p.1⁻¹ * p.1, _⟩
      rw [show (⟨p.1⁻¹ * p.1, by simp⟩ : V) = 1 from Subtype.ext (inv_mul_cancel _), h1, add_zero]
    · simpa using V.inv_mem h
    · have := hinv ⟨_, h⟩
      have heq : (⟨q.1⁻¹ * p.1, by simpa using V.inv_mem h⟩ : V) = (⟨p.1⁻¹ * q.1, h⟩ : V)⁻¹ :=
        Subtype.ext (by simp)
      rw [heq, this, hpq]
      abel
    · simpa [mul_assoc] using V.mul_mem h h'
    · have heq : (⟨p.1⁻¹ * r.1, by simpa [mul_assoc] using V.mul_mem h h'⟩ : V) =
          ⟨p.1⁻¹ * q.1, h⟩ * ⟨q.1⁻¹ * r.1, h'⟩ :=
        Subtype.ext (by simp [mul_assoc])
      rw [heq, hadd, hpq, hqr]
      abel

variable (χ : V → A) (hadd : ∀ a b, χ (a * b) = χ a + χ b)

/-- **The induced torsor** `Γ ×^V A`. -/
def InducedTorsor : Type _ := Quotient (inducedTorsorSetoid V χ hadd)

variable {V χ hadd}

/-- The class of `(g, a)` in the induced torsor. -/
def InducedTorsor.mk (g : Γ) (a : A) : InducedTorsor V χ hadd :=
  Quotient.mk (inducedTorsorSetoid V χ hadd) (g, a)

/-- `[g, a] = [g', a']` iff `g⁻¹ g' ∈ V` and `a = a' + χ (g⁻¹ g')`. -/
theorem InducedTorsor.mk_eq_mk_iff (g g' : Γ) (a a' : A) :
    (InducedTorsor.mk g a : InducedTorsor V χ hadd) = InducedTorsor.mk g' a' ↔
      ∃ h : g⁻¹ * g' ∈ V, a = a' + χ ⟨_, h⟩ :=
  Quotient.eq (r := inducedTorsorSetoid V χ hadd)

/-- Every point of the induced torsor is a class `[g, a]`. -/
theorem InducedTorsor.surjective_mk (s : InducedTorsor V χ hadd) :
    ∃ g a, InducedTorsor.mk g a = s :=
  Quotient.inductionOn s fun p => ⟨p.1, p.2, rfl⟩

/-- `Γ` acts on the induced torsor by left multiplication on the first factor. -/
instance : MulAction Γ (InducedTorsor V χ hadd) where
  smul g := Quotient.map (fun p => (g * p.1, p.2)) fun p q ⟨h, hpq⟩ =>
    ⟨by simpa [mul_assoc] using h, by simpa [mul_assoc] using hpq⟩
  one_smul s := Quotient.inductionOn s fun p => by
    change Quotient.mk _ (1 * p.1, p.2) = _
    rw [one_mul]
  mul_smul g g' s := Quotient.inductionOn s fun p => by
    change Quotient.mk _ (g * g' * p.1, p.2) = Quotient.mk _ (g * (g' * p.1), p.2)
    rw [mul_assoc]

/-- `g₀ • [g, a] = [g₀ g, a]`. -/
theorem InducedTorsor.smul_mk (g₀ g : Γ) (a : A) :
    g₀ • (InducedTorsor.mk g a : InducedTorsor V χ hadd) = InducedTorsor.mk (g₀ * g) a := rfl

/-- Translation by `b ∈ A` on the induced torsor. -/
def InducedTorsor.translate (b : A) : InducedTorsor V χ hadd → InducedTorsor V χ hadd :=
  Quotient.map (fun p => (p.1, p.2 + b)) fun p q ⟨h, hpq⟩ => ⟨h, by
    change p.2 + b = q.2 + b + χ ⟨p.1⁻¹ * q.1, h⟩
    rw [hpq]
    abel⟩

/-- Translation by `b` sends `[g, a]` to `[g, a + b]`. -/
theorem InducedTorsor.translate_mk (b : A) (g : Γ) (a : A) :
    InducedTorsor.translate b (InducedTorsor.mk g a : InducedTorsor V χ hadd) =
      InducedTorsor.mk g (a + b) := rfl

/-- Translation commutes with the action of `Γ`. -/
theorem InducedTorsor.translate_smul (b : A) (g₀ : Γ) (s : InducedTorsor V χ hadd) :
    InducedTorsor.translate b (g₀ • s) = g₀ • InducedTorsor.translate b s :=
  Quotient.inductionOn s fun _ => rfl

/-- Translation by `0` is the identity. -/
theorem InducedTorsor.translate_zero (s : InducedTorsor V χ hadd) :
    InducedTorsor.translate 0 s = s :=
  Quotient.inductionOn s fun p => by
    change Quotient.mk _ (p.1, p.2 + 0) = _
    rw [add_zero]

/-- Translation by `b + b'` is translation by `b` followed by translation by `b'`. -/
theorem InducedTorsor.translate_add (b b' : A) (s : InducedTorsor V χ hadd) :
    InducedTorsor.translate (b + b') s =
      InducedTorsor.translate b' (InducedTorsor.translate b s) :=
  Quotient.inductionOn s fun p => by
    change Quotient.mk _ (p.1, p.2 + (b + b')) = Quotient.mk _ (p.1, p.2 + b + b')
    rw [add_assoc]

/-- The projection `[g, a] ↦ g V`. -/
def InducedTorsor.proj : InducedTorsor V χ hadd → Γ ⧸ V :=
  Quotient.lift (fun p => (QuotientGroup.mk p.1 : Γ ⧸ V)) fun _p _q ⟨h, _⟩ =>
    QuotientGroup.eq.2 h

/-- The projection sends `[g, a]` to the coset `g V`. -/
theorem InducedTorsor.proj_mk (g : Γ) (a : A) :
    InducedTorsor.proj (InducedTorsor.mk g a : InducedTorsor V χ hadd) = QuotientGroup.mk g := rfl

/-- The projection to `Γ / V` is `Γ`-equivariant. -/
theorem InducedTorsor.proj_smul (g₀ : Γ) (s : InducedTorsor V χ hadd) :
    InducedTorsor.proj (g₀ • s) = g₀ • InducedTorsor.proj s :=
  Quotient.inductionOn s fun _ => rfl

/-- The projection to `Γ / V` is invariant under translation. -/
theorem InducedTorsor.proj_translate (b : A) (s : InducedTorsor V χ hadd) :
    InducedTorsor.proj (InducedTorsor.translate b s) = InducedTorsor.proj s :=
  Quotient.inductionOn s fun _ => rfl

/-- Over the base coset, `v ∈ V` acts through `χ`: `v • [1, a] = [1, a + χ v]`. -/
theorem InducedTorsor.smul_mk_one (v : V) (a : A) :
    (v : Γ) • (InducedTorsor.mk 1 a : InducedTorsor V χ hadd) = InducedTorsor.mk 1 (a + χ v) := by
  rw [InducedTorsor.smul_mk, mul_one, InducedTorsor.mk_eq_mk_iff]
  have hv : ((v : Γ))⁻¹ * 1 ∈ V := by simp
  refine ⟨hv, ?_⟩
  have hsum := hadd v ⟨_, hv⟩
  have : v * ⟨_, hv⟩ = 1 := Subtype.ext (by simp)
  rw [this, map_one_eq_zero_of_map_mul hadd] at hsum
  rw [add_assoc, ← hsum, add_zero]

/-- Every point over the base coset is some `[1, a]`. -/
theorem InducedTorsor.exists_mk_one_of_proj (s : InducedTorsor V χ hadd)
    (hs : InducedTorsor.proj s = QuotientGroup.mk 1) : ∃ a, InducedTorsor.mk 1 a = s := by
  obtain ⟨g, a, rfl⟩ := InducedTorsor.surjective_mk s
  rw [InducedTorsor.proj_mk, QuotientGroup.eq] at hs
  have hv : (1 : Γ)⁻¹ * g ∈ V := by simpa using V.inv_mem hs
  exact ⟨a + χ ⟨_, hv⟩, (InducedTorsor.mk_eq_mk_iff _ _ _ _).2 ⟨hv, rfl⟩⟩

/-- The map `a ↦ [1, a]` is injective. -/
theorem InducedTorsor.mk_one_injective (a a' : A)
    (h : (InducedTorsor.mk 1 a : InducedTorsor V χ hadd) = InducedTorsor.mk 1 a') : a = a' := by
  rw [InducedTorsor.mk_eq_mk_iff] at h
  obtain ⟨_, h⟩ := h
  have : (⟨(1 : Γ)⁻¹ * 1, by simp⟩ : V) = 1 := Subtype.ext (by simp)
  rw [h, this, map_one_eq_zero_of_map_mul hadd, add_zero]

/-- The translations act freely. -/
theorem InducedTorsor.eq_of_translate_eq (b b' : A) (s : InducedTorsor V χ hadd)
    (h : InducedTorsor.translate b s = InducedTorsor.translate b' s) : b = b' := by
  obtain ⟨g, a, rfl⟩ := InducedTorsor.surjective_mk s
  rw [InducedTorsor.translate_mk, InducedTorsor.translate_mk] at h
  have h' := congrArg ((g⁻¹ : Γ) • ·) h
  simp only [InducedTorsor.smul_mk, inv_mul_cancel] at h'
  exact add_left_cancel (InducedTorsor.mk_one_injective _ _ h')

/-- The translations act transitively on the fibres of the projection. -/
theorem InducedTorsor.exists_translate_eq (s s' : InducedTorsor V χ hadd)
    (h : InducedTorsor.proj s = InducedTorsor.proj s') :
    ∃ b, InducedTorsor.translate b s = s' := by
  obtain ⟨g, a, rfl⟩ := InducedTorsor.surjective_mk s
  obtain ⟨g', a', rfl⟩ := InducedTorsor.surjective_mk s'
  rw [InducedTorsor.proj_mk, InducedTorsor.proj_mk, QuotientGroup.eq] at h
  refine ⟨a' + χ ⟨_, h⟩ - a, ?_⟩
  rw [InducedTorsor.translate_mk, InducedTorsor.mk_eq_mk_iff]
  exact ⟨h, by abel⟩

/-- **Comparison of characters through induced torsors.** If a map between the induced torsors of
`χ₁` and `χ₂` commutes with the translations, preserves the base coset and commutes with
`v ∈ V` on it, then `χ₁ v = χ₂ v`. -/
theorem eq_of_inducedTorsor_hom {χ₁ χ₂ : V → A} {hadd₁ : ∀ a b, χ₁ (a * b) = χ₁ a + χ₁ b}
    {hadd₂ : ∀ a b, χ₂ (a * b) = χ₂ a + χ₂ b}
    (Φ : InducedTorsor V χ₁ hadd₁ → InducedTorsor V χ₂ hadd₂)
    (hΦt : ∀ b s, Φ (InducedTorsor.translate b s) = InducedTorsor.translate b (Φ s))
    (hΦp : InducedTorsor.proj (Φ (InducedTorsor.mk 1 0)) = QuotientGroup.mk 1)
    (v : V) (hΦv : Φ ((v : Γ) • InducedTorsor.mk 1 0) = (v : Γ) • Φ (InducedTorsor.mk 1 0)) :
    χ₁ v = χ₂ v := by
  obtain ⟨a', ha'⟩ := InducedTorsor.exists_mk_one_of_proj _ hΦp
  rw [InducedTorsor.smul_mk_one, zero_add, ← ha', InducedTorsor.smul_mk_one] at hΦv
  have h2 : Φ (InducedTorsor.mk 1 (χ₁ v)) = InducedTorsor.mk 1 (a' + χ₁ v) := by
    have := hΦt (χ₁ v) (InducedTorsor.mk 1 0)
    rwa [InducedTorsor.translate_mk, zero_add, ← ha', InducedTorsor.translate_mk] at this
  rw [h2] at hΦv
  exact add_left_cancel (InducedTorsor.mk_one_injective _ _ hΦv)

end Stacks.LAdic

namespace AlgebraicGeometry

open Stacks.LAdic

variable {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X)
  {V : Subgroup (EtaleFundamentalGroup X x)} {A : Type*} [AddCommGroup A] [Finite A]
  {χ : V → A} {hadd : ∀ a b, χ (a * b) = χ a + χ b}

/-- The induced torsor of a locally constant character of an open subgroup of `π₁(X, x)` with
finite values is finite. -/
theorem finite_inducedTorsor (hV : IsOpen (V : Set (EtaleFundamentalGroup X x))) :
    Finite (InducedTorsor V χ hadd) := by
  have : ∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y) := finite_finiteEtaleFiber x
  have : Finite (EtaleFundamentalGroup X x ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  refine Finite.of_surjective (fun p : (EtaleFundamentalGroup X x ⧸ V) × A =>
    InducedTorsor.mk p.1.out p.2) fun s => ?_
  obtain ⟨g, a, rfl⟩ := InducedTorsor.surjective_mk s
  have hg : g⁻¹ * (QuotientGroup.mk g : EtaleFundamentalGroup X x ⧸ V).out ∈ V :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
  refine ⟨((QuotientGroup.mk g : EtaleFundamentalGroup X x ⧸ V), a - χ ⟨_, hg⟩), ?_⟩
  dsimp only
  rw [InducedTorsor.mk_eq_mk_iff]
  have hg' : ((QuotientGroup.mk g : EtaleFundamentalGroup X x ⧸ V).out)⁻¹ * g ∈ V := by
    simpa using V.inv_mem hg
  refine ⟨hg', ?_⟩
  have hsum := hadd ⟨_, hg⟩ ⟨_, hg'⟩
  have : (⟨_, hg⟩ : V) * ⟨_, hg'⟩ = 1 := Subtype.ext (by simp)
  rw [this, map_one_eq_zero_of_map_mul hadd] at hsum
  have hy : χ ⟨_, hg'⟩ = -χ ⟨_, hg⟩ := eq_neg_of_add_eq_zero_right hsum.symm
  rw [hy, sub_eq_add_neg]

omit [Finite A] in
/-- The stabilizers of the induced torsor of a locally constant character of an open subgroup are
open: the stabilizer of `[g, a]` is `g (ker χ) g⁻¹`. -/
theorem isOpen_stabilizer_inducedTorsor (hV : IsOpen (V : Set (EtaleFundamentalGroup X x)))
    (hχc : IsLocallyConstant χ) (s : InducedTorsor V χ hadd) :
    IsOpen (MulAction.stabilizer (EtaleFundamentalGroup X x) s :
      Set (EtaleFundamentalGroup X x)) := by
  obtain ⟨g, a, rfl⟩ := InducedTorsor.surjective_mk s
  set W : Set (EtaleFundamentalGroup X x) := Subtype.val '' {v : V | χ v = 0}
  have hW : IsOpen W := hV.isOpenMap_subtype_val _ (hχc.isOpen_fiber 0)
  have : (MulAction.stabilizer (EtaleFundamentalGroup X x) (InducedTorsor.mk g a :
      InducedTorsor V χ hadd) : Set (EtaleFundamentalGroup X x)) =
      (fun g₀ => (g₀ * g)⁻¹ * g) ⁻¹' W := by
    ext g₀
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, InducedTorsor.smul_mk,
      InducedTorsor.mk_eq_mk_iff, Set.mem_preimage, W, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h, ha⟩
      exact ⟨⟨_, h⟩, by simpa using (left_eq_add.1 ha), rfl⟩
    · rintro ⟨v, hv, hv'⟩
      refine ⟨hv' ▸ v.2, ?_⟩
      have : (⟨(g₀ * g)⁻¹ * g, hv' ▸ v.2⟩ : V) = v := Subtype.ext hv'.symm
      rw [this, hv, add_zero]
  rw [this]
  exact hW.preimage ((continuous_id.mul continuous_const).inv.mul continuous_const)

variable (χ hadd) in
/-- **The cover attached to a character of an open subgroup**: a finite étale cover `T_χ` of `X`
whose geometric fibre at `x` is, equivariantly, the induced torsor `π₁(X, x) ×^V A`. -/
theorem exists_inducedCharacterCover (hV : IsOpen (V : Set (EtaleFundamentalGroup X x)))
    (hχc : IsLocallyConstant χ) :
    ∃ (T : FiniteEtaleOver X) (e : (finiteEtaleFiberFunctor x).obj T ≃ InducedTorsor V χ hadd),
      ∀ (σ : EtaleFundamentalGroup X x) t, e (σ • t) = σ • e t := by
  have := finite_inducedTorsor x (χ := χ) (hadd := hadd) hV
  exact exists_finiteEtaleOver_fiber_equiv x (InducedTorsor V χ hadd)
    (isOpen_stabilizer_inducedTorsor x hV hχc)

end AlgebraicGeometry
