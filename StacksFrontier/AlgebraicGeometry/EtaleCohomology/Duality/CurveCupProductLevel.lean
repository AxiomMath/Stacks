module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveFirstCohomologyPairing

/-!
# Nondegeneracy of the cup product on `H¹` of a curve with `ℤ/ℓⁿ` coefficients

Let `X` be a smooth proper curve over an algebraically closed field `k`, `ℓ` a prime invertible
in `k` and `Λ = ℤ/ℓⁿ`. For every nonzero `a ∈ H¹(X, Λ) = Ext¹(Λ_X, Λ_X)` there is
`x ∈ H¹(X, Λ)` with `x ∪ a = x ∘ a ≠ 0` in `H²(X, Λ)`.

The case `n = 1` is `Stacks.EtaleCohomology.ExtensionTorsor.exists_comp_ne_zero_of_ne_zero`.
In general a suitable multiple `b = ℓᵏ a` is nonzero and killed by `ℓ`. Write `N = ℓⁿ⁺¹`; the
two short exact sequences of constant sheaves
`0 → ℤ/ℓⁿ → ℤ/N → ℤ/ℓ → 0` and `0 → ℤ/ℓ → ℤ/N → ℤ/ℓⁿ → 0`
(`Stacks.EtaleCohomology.LevelChange.inclusionShortComplex_shortExact`), the cardinalities
`#Hⁱ(X, ℤ/m) = m` for `i = 0, 2` and the vanishing of `H³`, give by counting:

* `ℓ`-torsion classes of `H¹(X, ℤ/N)` come from `H¹(X, ℤ/ℓ)`;
* `H¹(X, ℤ/N) → H¹(X, ℤ/ℓ)` is onto;
* `H²(X, ℤ/ℓ) → H²(X, ℤ/N)` is injective.

With the change of level `H^i(X, ℤ/ℓ) ≅ Ext^i_{ℤ/N}(ℤ/N_X, ℤ/ℓ_X)`, compatible with the Yoneda
product (`Stacks.EtaleCohomology.LevelChange.extMap_comp`), the case `n = 1` applied to `b` gives
`x` with `x ∘ b ≠ 0`, hence `x ∘ a ≠ 0`.

The divisibility of `Pic⁰` that enters is `Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero`.

## Main results

* `Stacks.EtaleCohomology.LevelChange.exists_comp_ne_zero_of_ne_zero`: the nondegeneracy.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.LevelChange

open ExtensionTorsor

section Counting

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {f : A →+ B} {g : B →+ C}

/-- For a homomorphism `g : B →+ C`, the cardinality of `B` is the product of the cardinalities of
the kernel and the range of `g`. -/
theorem natCard_eq_natCard_ker_mul_natCard_range (g : B →+ C) :
    Nat.card B = Nat.card g.ker * Nat.card g.range := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, mul_comm,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv]

/-- In an exact sequence `A → B → C → 0` of finite groups with `#A · #C ≤ #B`, the first map
is injective. -/
theorem injective_of_exact_of_surjective [Finite A] [Finite B] (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hcard : Nat.card A * Nat.card C ≤ Nat.card B) :
    Function.Injective f := by
  have hker : g.ker = f.range := hfg.addMonoidHom_ker_eq
  have hB := natCard_eq_natCard_ker_mul_natCard_range g
  rw [AddMonoidHom.range_eq_top_of_surjective g hg, hker] at hB
  have hC : Nat.card (⊤ : AddSubgroup C) = Nat.card C := Nat.card_congr (Equiv.Set.univ C)
  rw [hC] at hB
  have hCpos : 0 < Nat.card C := by
    have : Finite C := Finite.of_surjective g hg
    exact Nat.card_pos_iff.2 ⟨⟨g 0⟩, inferInstance⟩
  have hle : Nat.card A ≤ Nat.card f.range := by
    have := hcard.trans hB.le
    exact Nat.le_of_mul_le_mul_right this hCpos
  have hA := natCard_eq_natCard_ker_mul_natCard_range f
  have hpos : 0 < Nat.card f.range := Nat.card_pos_iff.2 ⟨⟨⟨0, zero_mem _⟩⟩, inferInstance⟩
  have hk : Nat.card f.ker ≤ 1 := by
    by_contra hk
    push Not at hk
    have : 2 * Nat.card f.range ≤ Nat.card f.ker * Nat.card f.range :=
      Nat.mul_le_mul_right _ hk
    omega
  have : Subsingleton f.ker := (Finite.card_le_one_iff_subsingleton).1 hk
  rw [injective_iff_map_eq_zero]
  intro a ha
  have := Subsingleton.elim (⟨a, ha⟩ : f.ker) ⟨0, map_zero f⟩
  exact congrArg Subtype.val this

/-- In an exact sequence `0 → A → B → C` of finite groups with `#A · #C ≤ #B`, the second map
is onto. -/
theorem surjective_of_exact_of_injective [Finite B] [Finite C] (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hcard : Nat.card A * Nat.card C ≤ Nat.card B) :
    Function.Surjective g := by
  have hker : g.ker = f.range := hfg.addMonoidHom_ker_eq
  have hB := natCard_eq_natCard_ker_mul_natCard_range g
  rw [hker] at hB
  have hfA : Nat.card f.range = Nat.card A :=
    (Nat.card_congr (Equiv.ofInjective f hf)).symm
  rw [hfA] at hB
  have hApos : 0 < Nat.card A := by
    have : Finite A := Finite.of_injective f hf
    exact Nat.card_pos_iff.2 ⟨⟨0⟩, inferInstance⟩
  have hle : Nat.card C ≤ Nat.card g.range := by
    have := hcard.trans hB.le
    exact Nat.le_of_mul_le_mul_left this hApos
  have htop : g.range = ⊤ := by
    have h1 : Nat.card g.range = Nat.card (⊤ : AddSubgroup C) :=
      le_antisymm (AddSubgroup.card_le_of_le le_top)
        (hle.trans_eq' (Nat.card_congr (Equiv.Set.univ C)).symm)
    exact AddSubgroup.eq_top_of_card_eq _ (h1.trans (Nat.card_congr (Equiv.Set.univ C)))
  exact AddMonoidHom.range_eq_top.1 htop

end Counting

section ExtCounting

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasExt 𝒞] {S : ShortComplex 𝒞}
  (hS : S.ShortExact) (O : 𝒞)

include hS in
/-- For a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, the sequence of abelian groups
`Ext^n(O, X₁) → Ext^n(O, X₂) → Ext^n(O, X₃)` is exact. -/
theorem function_exact_ext (n : ℕ) :
    Function.Exact ((Ext.mk₀ S.f).postcomp O (add_zero n))
      ((Ext.mk₀ S.g).postcomp O (add_zero n)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₂' O hS n)

include hS in
/-- **`Ext^n(O, X₁) → Ext^n(O, X₂)` is injective by counting**, when `Ext^{n+1}(O, X₁) = 0` and
`#Ext^n(O, X₁) · #Ext^n(O, X₃) ≤ #Ext^n(O, X₂)`. -/
theorem injective_comp_mk₀_f_of_natCard (n : ℕ) (h : Subsingleton (Ext O S.X₁ (n + 1)))
    [Finite (Ext O S.X₁ n)] [Finite (Ext O S.X₂ n)]
    (hcard : Nat.card (Ext O S.X₁ n) * Nat.card (Ext O S.X₃ n) ≤ Nat.card (Ext O S.X₂ n)) :
    Function.Injective (fun x : Ext O S.X₁ n => x.comp (Ext.mk₀ S.f) (add_zero n)) :=
  injective_of_exact_of_surjective (function_exact_ext hS O n)
    (Ext.surjective_comp_mk₀_g_of_subsingleton hS O n h) hcard

include hS in
/-- **`Ext^n(O, X₂) → Ext^n(O, X₃)` is onto by counting**, when `Ext^n(O, X₁) → Ext^n(O, X₂)`
is injective and `#Ext^n(O, X₁) · #Ext^n(O, X₃) ≤ #Ext^n(O, X₂)`. -/
theorem surjective_comp_mk₀_g_of_natCard (n : ℕ) [Finite (Ext O S.X₂ n)]
    [Finite (Ext O S.X₃ n)]
    (hinj : Function.Injective (fun x : Ext O S.X₁ n => x.comp (Ext.mk₀ S.f) (add_zero n)))
    (hcard : Nat.card (Ext O S.X₁ n) * Nat.card (Ext O S.X₃ n) ≤ Nat.card (Ext O S.X₂ n)) :
    Function.Surjective (fun x : Ext O S.X₂ n => x.comp (Ext.mk₀ S.g) (add_zero n)) :=
  surjective_of_exact_of_injective (function_exact_ext hS O n) hinj hcard

include hS in
/-- For a short exact sequence `0 → X₁ → X₂ → X₃ → 0`, composition with `X₁ → X₂` is injective
on `Ext⁰(O, X₁)`. -/
theorem injective_comp_mk₀_f_zero :
    Function.Injective (fun x : Ext O S.X₁ 0 => x.comp (Ext.mk₀ S.f) (add_zero 0)) := by
  have := hS.mono_f
  intro x y hxy
  rw [← Ext.mk₀_homEquiv₀_apply x, ← Ext.mk₀_homEquiv₀_apply y] at hxy ⊢
  simp only [Ext.mk₀_comp_mk₀] at hxy
  rw [(cancel_mono S.f).1 ((Ext.mk₀_bijective _ _).1 hxy)]

end ExtCounting

section ExtSmul

variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasExt 𝒞]

/-- `Ext.mk₀` commutes with multiplication by a natural number: `mk₀ (m • g) = m • mk₀ g`. -/
theorem mk₀_nsmul {A B : 𝒞} (g : A ⟶ B) (m : ℕ) : Ext.mk₀ (m • g) = m • Ext.mk₀ g := by
  induction m with
  | zero => simp [Ext.mk₀_zero]
  | succ m ih => rw [succ_nsmul, Ext.mk₀_add, ih, succ_nsmul]

/-- The Yoneda product commutes with multiplication by a natural number in the second factor:
`x.comp (m • y) h = m • x.comp y h`. -/
theorem comp_nsmul {A B D : 𝒞} {a b c : ℕ} (x : Ext A B a) (y : Ext B D b) (h : a + b = c)
    (m : ℕ) : x.comp (m • y) h = m • x.comp y h :=
  map_nsmul (Ext.bilinearComp A B D a b c h x) m y

/-- The Yoneda product commutes with multiplication by a natural number in the first factor:
`(m • x).comp y h = m • x.comp y h`. -/
theorem nsmul_comp {A B D : 𝒞} {a b c : ℕ} (x : Ext A B a) (y : Ext B D b) (h : a + b = c)
    (m : ℕ) : (m • x).comp y h = m • x.comp y h :=
  DFunLike.congr_fun (map_nsmul (Ext.bilinearComp A B D a b c h) m x) y

end ExtSmul

section Curve

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

/-- `#H²(X, ℤ/m) = m`, read as `Ext²_{ℤ/N}(ℤ/N_X, ℤ/m_X)` for `m ∣ N`. -/
theorem natCard_ext_two_restrict {N m : ℕ} [NeZero N] (hm : m ∣ N) (hmk : IsUnit (m : k))
    (hdiv : ∀ L : Picard.ofScheme X,
      Picard.picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 0 →
        ∃ M : Picard.ofScheme X, m • M = L) :
    Nat.card (Ext (unitSheaf (X := X) N) ((restrict X hm).obj (unitSheaf m)) 2) = m :=
  (Nat.card_congr (Equiv.ofBijective _ (extMap_bijective X hm (unitSheaf m) 2))).symm.trans
    (Stacks.Kummer.natCard_ext_two_constantModuleSheaf_of_smoothProperCurve f hmk hdiv)

omit [IsProper f] in
include f in
/-- `H³(X, ℤ/m) = 0`, read as `Ext³_{ℤ/N}(ℤ/N_X, ℤ/m_X)` for `m ∣ N`. -/
theorem subsingleton_ext_three_restrict {N m : ℕ} [NeZero N] (hm : m ∣ N)
    (hmk : IsUnit (m : k)) :
    Subsingleton (Ext (unitSheaf (X := X) N) ((restrict X hm).obj (unitSheaf m)) 3) :=
  @Equiv.subsingleton _ _ (Equiv.ofBijective _ (extMap_bijective X hm (unitSheaf m) 3)).symm
    (Stacks.Kummer.subsingleton_ext_constantModuleSheaf_of_smoothCurve (n := m) f hmk 3 le_rfl)

/-- Multiplication by `m` on `Ext(A, B)` vanishes when it vanishes on `B`. -/
theorem nsmul_eq_zero_of_nsmul_id {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞] [HasExt 𝒞] {A B : 𝒞}
    {m : ℕ} (hm : m • 𝟙 B = 0) {i : ℕ} (x : Ext A B i) : m • x = 0 := by
  rw [← Ext.comp_mk₀_id x, ← comp_nsmul, ← mk₀_nsmul, hm, Ext.mk₀_zero, Ext.comp_zero]

omit [IsAlgClosed k] [Smooth f] in
/-- `ℓ`-divisibility of `Pic⁰(X)` gives `ℓʲ`-divisibility. -/
theorem exists_pow_nsmul_eq {ℓ : ℕ} (hℓ0 : ℓ ≠ 0)
    (hdiv : ∀ L : Picard.ofScheme X,
      Picard.picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 0 →
        ∃ M : Picard.ofScheme X, ℓ • M = L) (j : ℕ) :
    ∀ L : Picard.ofScheme X,
      Picard.picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 0 →
        ∃ M : Picard.ofScheme X, ℓ ^ j • M = L := by
  induction j with
  | zero => exact fun L _ => ⟨L, by rw [pow_zero, one_smul]⟩
  | succ j ih =>
    intro L hL
    obtain ⟨M₁, rfl⟩ := hdiv L hL
    have hM₁ : Picard.picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le M₁ = 0 := by
      rw [map_nsmul, nsmul_eq_mul] at hL
      exact (mul_eq_zero.1 hL).resolve_left (by exact_mod_cast hℓ0)
    obtain ⟨M₂, rfl⟩ := ih M₁ hM₁
    exact ⟨M₂, by rw [pow_succ', mul_smul]⟩

/-- The `m`-divisibility of `Pic⁰(X)`, in the shape the trace map consumes. -/
abbrev PicDiv (m : ℕ) : Prop :=
  ∀ L : Picard.ofScheme X,
    Picard.picardDegree f (IsCurve.topologicalKrullDim_eq_one (f := f)).le L = 0 →
      ∃ M : Picard.ofScheme X, m • M = L

include f in
/-- For `N = d e` with `d, e, N` invertible in `k` and `Pic⁰(X)` divisible by them:
`H²(X, ℤ/e) → H²(X, ℤ/N)` is injective and `H¹(X, ℤ/N) → H¹(X, ℤ/d)` is onto, by counting in the
long exact sequence of `0 → ℤ/e → ℤ/N → ℤ/d → 0`. -/
theorem injective_two_and_surjective_one {N d e : ℕ} [NeZero N] (hde : d * e = N)
    (hd : IsUnit (d : k)) (he : IsUnit (e : k)) (hN : IsUnit (N : k))
    (hdivd : PicDiv f d) (hdive : PicDiv f e) (hdivN : PicDiv f N) :
    Function.Injective (fun x : Ext (unitSheaf (X := X) N) (inclusionShortComplex X hde).X₁ 2 =>
        x.comp (Ext.mk₀ (inclusionShortComplex X hde).f) (add_zero 2)) ∧
      Function.Surjective (fun x : Ext (unitSheaf (X := X) N) (inclusionShortComplex X hde).X₂ 1 =>
        x.comp (Ext.mk₀ (inclusionShortComplex X hde).g) (add_zero 1)) := by
  set S := inclusionShortComplex X hde
  have hS : S.ShortExact := inclusionShortComplex_shortExact X hde
  have c1 : Nat.card (Ext (unitSheaf (X := X) N) S.X₁ 2) = e :=
    natCard_ext_two_restrict f _ he hdive
  have c2 : Nat.card (Ext (unitSheaf (X := X) N) S.X₂ 2) = N :=
    Stacks.Kummer.natCard_ext_two_constantModuleSheaf_of_smoothProperCurve f hN hdivN
  have c3 : Nat.card (Ext (unitSheaf (X := X) N) S.X₃ 2) = d :=
    natCard_ext_two_restrict f _ hd hdivd
  have : Finite (Ext (unitSheaf (X := X) N) S.X₁ 2) :=
    Nat.finite_of_card_ne_zero (by rw [c1]; exact (neZero_right_of_mul_eq hde).ne)
  have : Finite (Ext (unitSheaf (X := X) N) S.X₂ 2) :=
    Nat.finite_of_card_ne_zero (by rw [c2]; exact NeZero.ne N)
  have hcard : Nat.card (Ext (unitSheaf (X := X) N) S.X₁ 2) *
      Nat.card (Ext (unitSheaf (X := X) N) S.X₃ 2) ≤
        Nat.card (Ext (unitSheaf (X := X) N) S.X₂ 2) := by
    rw [c1, c2, c3, mul_comm, hde]
  have hinj := injective_comp_mk₀_f_of_natCard hS (unitSheaf (X := X) N) 2
    (subsingleton_ext_three_restrict f _ he) hcard
  refine ⟨hinj, fun y => ?_⟩
  have hδ : y.comp hS.extClass (rfl : 1 + 1 = 2) = 0 := by
    apply hinj
    change (y.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero 2) =
      (0 : Ext (unitSheaf (X := X) N) S.X₁ 2).comp (Ext.mk₀ S.f) (add_zero 2)
    rw [Ext.zero_comp, Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]
  exact Ext.covariant_sequence_exact₃ _ hS y rfl hδ

/-- `#H⁰(Y, ℤ/m) = m` on a connected `Y`, read as `Ext⁰_{ℤ/N}(ℤ/N_Y, ℤ/m_Y)` for `m ∣ N`. -/
theorem natCard_ext_zero_restrict {Y : Scheme.{u}} [ConnectedSpace Y] {N m : ℕ} [NeZero N]
    (hm : m ∣ N) :
    Nat.card (Ext (unitSheaf (X := Y) N) ((restrict Y hm).obj (unitSheaf m)) 0) = m := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (extMap_bijective Y hm (unitSheaf m) 0)),
    Nat.card_congr Ext.homEquiv₀, natCard_hom_unitSheaf_unitSheaf,
    natCard_locallyConstant_of_connectedSpace (T := Y), Nat.card_zmod]

/-- `#H⁰(Y, ℤ/N) = N` on a connected `Y`. -/
theorem natCard_ext_zero_unitSheaf {Y : Scheme.{u}} [ConnectedSpace Y] (N : ℕ) :
    Nat.card (Ext (unitSheaf (X := Y) N) (unitSheaf N) 0) = N := by
  rw [Nat.card_congr Ext.homEquiv₀, natCard_hom_unitSheaf_unitSheaf,
    natCard_locallyConstant_of_connectedSpace (T := Y), Nat.card_zmod]

/-- **`d`-torsion classes of `H¹(Y, ℤ/N)` come from `H¹(Y, ℤ/d)`**, for `N = d e` on a connected
`Y`: multiplication by `d` is `ℤ/N --π--> ℤ/e --d--> ℤ/N`, and `H¹(Y, ℤ/e) → H¹(Y, ℤ/N)` is
injective since `H⁰(Y, ℤ/N) → H⁰(Y, ℤ/d)` is onto (all three are constant), so a class killed
by `d` is killed by `π`, hence comes from `ℤ/d_Y --e--> ℤ/N_Y`. -/
theorem exists_comp_inclusion_eq_of_nsmul_eq_zero {Y : Scheme.{u}} [ConnectedSpace Y]
    {N d e : ℕ} [NeZero N] (hde : d * e = N)
    (b : Ext (unitSheaf (X := Y) N) (unitSheaf N) 1) (hb : d • b = 0) :
    ∃ b' : Ext (unitSheaf (X := Y) N)
        (inclusionShortComplex Y ((mul_comm e d).trans hde)).X₁ 1,
      b'.comp (Ext.mk₀ (inclusionShortComplex Y ((mul_comm e d).trans hde)).f) (add_zero 1) =
        b := by
  set S := inclusionShortComplex Y hde
  have hS : S.ShortExact := inclusionShortComplex_shortExact Y hde
  set T := inclusionShortComplex Y ((mul_comm e d).trans hde)
  have hT : T.ShortExact := inclusionShortComplex_shortExact Y _
  have := neZero_left_of_mul_eq hde
  have := neZero_right_of_mul_eq hde
  have c1 : Nat.card (Ext (unitSheaf (X := Y) N) S.X₁ 0) = e := natCard_ext_zero_restrict _
  have c2 : Nat.card (Ext (unitSheaf (X := Y) N) S.X₂ 0) = N := natCard_ext_zero_unitSheaf N
  have c3 : Nat.card (Ext (unitSheaf (X := Y) N) S.X₃ 0) = d := natCard_ext_zero_restrict _
  have : Finite (Ext (unitSheaf (X := Y) N) S.X₂ 0) :=
    Nat.finite_of_card_ne_zero (by rw [c2]; exact NeZero.ne N)
  have : Finite (Ext (unitSheaf (X := Y) N) S.X₃ 0) :=
    Nat.finite_of_card_ne_zero (by rw [c3]; exact NeZero.ne d)
  have hsurj := surjective_comp_mk₀_g_of_natCard hS (unitSheaf (X := Y) N) 0
    (injective_comp_mk₀_f_zero hS (unitSheaf (X := Y) N)) (by rw [c1, c2, c3, mul_comm, hde])
  have hinj : ∀ w : Ext (unitSheaf (X := Y) N) S.X₁ 1,
      w.comp (Ext.mk₀ S.f) (add_zero 1) = 0 → w = 0 := by
    intro w hw
    obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ (unitSheaf (X := Y) N) hS w hw (zero_add 1)
    obtain ⟨x₂, rfl⟩ := hsurj x₃
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  refine Ext.covariant_sequence_exact₂ (unitSheaf (X := Y) N) hT b (hinj _ ?_)
  have hfac : T.g ≫ S.f = d • 𝟙 (unitSheaf (X := Y) N) := reduction_comp_inclusion Y hde
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hfac, mk₀_nsmul, comp_nsmul,
    Ext.comp_mk₀_id, hb]

/-- A nonzero `a` killed by some power of `ℓ` has a nonzero multiple `ℓ ^ j • a` killed by `ℓ`. -/
theorem exists_pow_nsmul_ne_zero_and_nsmul_eq_zero {G : Type*} [AddCommMonoid G] {a : G}
    (ha : a ≠ 0) {ℓ m : ℕ} (h : ℓ ^ m • a = 0) :
    ∃ j, ℓ ^ j • a ≠ 0 ∧ ℓ • (ℓ ^ j • a) = 0 := by
  classical
  have hex : ∃ j, ℓ ^ j • a = 0 := ⟨m, h⟩
  have h0 : Nat.find hex ≠ 0 := fun h0 => ha (by simpa [h0] using Nat.find_spec hex)
  refine ⟨Nat.find hex - 1, Nat.find_min hex (by omega), ?_⟩
  rw [smul_smul, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
  exact Nat.find_spec hex

variable {ℓ : ℕ} [Fact ℓ.Prime]

include f in
/-- **Nondegeneracy of the cup product on `H¹` of a curve with `ℤ/ℓⁿ` coefficients.** Let `X` be
a smooth proper curve over an algebraically closed field `k` and `ℓ` a prime invertible in `k`.
For every nonzero `a ∈ H¹(X, ℤ/ℓⁿ) = Ext¹(ℤ/ℓⁿ_X, ℤ/ℓⁿ_X)` there is `x ∈ H¹(X, ℤ/ℓⁿ)` with
`x ∪ a = x ∘ a ≠ 0` in `H²(X, ℤ/ℓⁿ)`. -/
theorem exists_comp_ne_zero_of_ne_zero (hℓ : IsUnit (ℓ : k))
    (n : ℕ) (a : Ext (unitSheaf (X := X) (ℓ ^ n)) (unitSheaf (ℓ ^ n)) 1) (ha : a ≠ 0) :
    ∃ x : Ext (unitSheaf (X := X) (ℓ ^ n)) (unitSheaf (ℓ ^ n)) 1,
      x.comp a (by norm_num : 1 + 1 = 2) ≠ 0 := by
  have hdivℓ : PicDiv f ℓ := fun L hL =>
    Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero f _ hℓ L hL
  have hp : ℓ.Prime := Fact.out
  have : IsIntegral X := IsCurve.toIsVariety.toIsIntegral (k := k) (f := f)
  have : ConnectedSpace X := inferInstanceAs (ConnectedSpace X)
  have hN0 : (ℓ ^ n) • a = 0 := nsmul_eq_zero_of_nsmul_id (nsmul_id_unitSheaf X) a
  obtain _ | m := n
  · exact absurd (by simpa only [pow_zero, one_smul] using hN0) ha
  have : NeZero (ℓ ^ (m + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  have hde1 : ℓ * ℓ ^ m = ℓ ^ (m + 1) := (pow_succ' ℓ m).symm
  have hde2 : ℓ ^ m * ℓ = ℓ ^ (m + 1) := (mul_comm (ℓ ^ m) ℓ).trans hde1
  have hdivX := fun j => exists_pow_nsmul_eq f hp.ne_zero hdivℓ j
  -- the three counting facts
  have hℓpow : ∀ i, IsUnit ((ℓ ^ i : ℕ) : k) := fun i => by simpa using hℓ.pow i
  have hsurj := (injective_two_and_surjective_one f hde1 hℓ (hℓpow m) (hℓpow (m + 1))
    hdivℓ (hdivX m) (hdivX (m + 1))).2
  have hinj := (injective_two_and_surjective_one f hde2 (hℓpow m) hℓ (hℓpow (m + 1))
    (hdivX m) hdivℓ (hdivX (m + 1))).1
  -- a nonzero multiple of `a` killed by `ℓ`
  obtain ⟨j, hj', hb⟩ := exists_pow_nsmul_ne_zero_and_nsmul_eq_zero ha hN0
  obtain ⟨b', hb'⟩ := exists_comp_inclusion_eq_of_nsmul_eq_zero hde1 _ hb
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    exact hj' (by rw [← hb', Ext.zero_comp])
  -- change of level to `ℤ/ℓ`
  have hℓN : ℓ ∣ ℓ ^ (m + 1) := dvd_of_mul_eq_left hde2
  obtain ⟨b₁, hb₁⟩ := (extMap_bijective X hℓN (unitSheaf ℓ) 1).2 b'
  have hb₁0 : b₁ ≠ 0 := by
    rintro rfl
    exact hb'0 (by rw [← hb₁, map_zero])
  obtain ⟨y₁, hy₁⟩ := ExtensionTorsor.exists_comp_ne_zero_of_ne_zero f hℓ b₁ hb₁0
  obtain ⟨y, hy⟩ := hsurj (extMap X hℓN (unitSheaf ℓ) 1 y₁)
  have hy' : y.comp (Ext.mk₀ (reduction X hℓN)) (add_zero 1) = extMap X hℓN (unitSheaf ℓ) 1 y₁ :=
    hy
  have key : y.comp b' (rfl : 1 + 1 = 2) = extMap X hℓN (unitSheaf ℓ) 2 (y₁.comp b₁ rfl) := by
    rw [← hb₁, extMap_apply, ← Ext.comp_assoc_of_second_deg_zero, hy', ← extMap_comp]
  have hne₂ : y.comp b' (rfl : 1 + 1 = 2) ≠ 0 := by
    rw [key]
    exact fun h0 => hy₁ ((extMap_bijective X hℓN (unitSheaf ℓ) 2).1 (h0.trans (map_zero _).symm))
  have hne : y.comp (ℓ ^ j • a) (rfl : 1 + 1 = 2) ≠ 0 := by
    rw [← hb', ← Ext.comp_assoc_of_third_deg_zero]
    refine fun h0 => hne₂ (hinj ?_)
    change _ = Ext.comp 0 _ _
    rwa [Ext.zero_comp]
  refine ⟨y, fun h0 => hne ?_⟩
  rw [comp_nsmul]
  exact (congrArg (ℓ ^ j • ·) h0).trans (smul_zero _)

end Curve

end Stacks.EtaleCohomology.LevelChange

end
