module

public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Project Tag 08BK (Modules, Lemma 17.17.11).

Let `(X, O_X)` be a ringed space and let `F` be a flat `O_X`-module. Let `U ⊆ X` be open,
let `n ∈ ℕ`, and let `f₁, …, fₙ ∈ O_X(U)` and `s₁, …, sₙ ∈ F(U)` be such that
the diagram
  `O_U → O_U^{⊕n} → F|_U`,
with first map `g ↦ (g·f₁, …, g·fₙ)` and second map `(g₁, …, gₙ) ↦ ∑ᵢ gᵢ·sᵢ`,
is a complex, i.e. `∑ᵢ fᵢ·sᵢ = 0` in `F(U)`.

Then for every `x ∈ U` there exist an open neighbourhood `V ⊆ U` of `x`, an integer `m ∈ ℕ`,
sections `t₁, …, t_m ∈ F(V)`, and a morphism `A : O_V^{⊕n} → O_V^{⊕m}` of `O_V`-modules
(given by an `m × n` matrix `(a_{ji})` with `a_{ji} ∈ O_X(V)`) such that
  `O_V^{⊕n} --A--> O_V^{⊕m} --(t₁,…,t_m)--> F|_V`
is a factorization of `(s₁, …, sₙ)|_V` and such that `A ∘ (f₁, …, fₙ)|_V = 0`.

Unwinding the morphisms on basis sections (cf. the "Equivalently" reformulation of
the source) this is exactly the existence of `m`, sections `t_j ∈ F(V)` and
scalars `a_{ji} ∈ O_X(V)` such that:
  - (Factorization)  `sᵢ|_V = ∑ⱼ a_{ji}·t_j`     for every `i`;
  - (Annihilation)   `∑ᵢ a_{ji}·fᵢ|_V = 0`        for every `j`.

The maps of Definitions 2–4 of the source (the morphisms `(f₁,…,fₙ)`, `(s₁,…,sₙ)`, and the
matrix morphism `A`) are `O`-linear and are determined by their values on the standard basis
sections; we therefore formalize the statement directly in terms of these elementwise scalar
equations, which is equivalent to the morphism-level formulation.

The algebraic input Stacks Tag 04VX (Algebra, Lemma 10.107.10), available in Mathlib as
`TensorProduct.vanishesTrivially_iff_sum_tmul_eq_zero`, may be cited in a proof.
-/

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.FlatEquationalCriterion

/-
We model the ringed space `(X, O_X)` by Mathlib's `AlgebraicGeometry.RingedSpace`, i.e. a
topological space with a sheaf of commutative rings `X.presheaf`. The stalk ring `O_{X,x}` is
`X.presheaf.stalk x`.
-/

-- Main Definition(s)

/-- The ring of sections `O_X(U)` of the structure sheaf over an open `U`, as a `Type`. -/
abbrev OSections (X : AlgebraicGeometry.RingedSpace.{u}) (U : Opens X) : Type u :=
  (X.presheaf.obj (op U) : Type u)

/-- The restriction ring homomorphism `O_X(U) → O_X(V)` for `V ≤ U`. -/
noncomputable def Ores (X : AlgebraicGeometry.RingedSpace.{u}) {U V : Opens X} (i : V ≤ U) :
    OSections X U →+* OSections X V :=
  (X.presheaf.map (homOfLE i).op).hom

/-- The stalk ring `O_{X,x}`, as a `Type`. -/
abbrev Ostalk (X : AlgebraicGeometry.RingedSpace.{u}) (x : X) : Type u :=
  (X.presheaf.stalk x : Type u)

/-- The germ ring homomorphism `O_X(U) → O_{X,x}` at a point `x ∈ U`. -/
noncomputable def Ogerm (X : AlgebraicGeometry.RingedSpace.{u}) (U : Opens X) (x : X)
    (h : x ∈ U) : OSections X U →+* Ostalk X x :=
  (X.presheaf.germ U x h).hom

/-- An `O_X`-module (Definition 1 background): a sheaf `F` of abelian groups on `X` together
with, for every open `U`, an `O_X(U)`-module structure on the sections `F(U)`, compatible with
restriction maps. We additionally bundle the data of the stalks `F_x` as modules over the
stalk rings `O_{X,x}` together with the germ maps satisfying the colimit (universal) properties;
this uniquely characterizes `F_x` as the stalk of `F` at `x` and is used to phrase flatness. -/
structure OXModule (X : AlgebraicGeometry.RingedSpace.{u}) where
  /-- The underlying sheaf of abelian groups. -/
  sheaf : TopCat.Presheaf AddCommGrpCat.{u} X.toPresheafedSpace
  /-- The sheaf condition for the underlying presheaf of abelian groups. -/
  isSheaf : sheaf.IsSheaf
  /-- For each open `U`, an `O_X(U)`-module structure on the sections `F(U)`. -/
  module : ∀ U : Opens X, Module (OSections X U) (sheaf.obj (op U))
  /-- Restriction is semilinear over the ring restriction: `(g • s)|_V = g|_V • s|_V`. -/
  res_smul : ∀ {U V : Opens X} (i : V ≤ U) (g : OSections X U) (s : sheaf.obj (op U)),
    letI := module U; letI := module V
    (sheaf.map (homOfLE i).op).hom (g • s) = Ores X i g • (sheaf.map (homOfLE i).op).hom s
  /-- The stalk `F_x` as an abelian group. -/
  stalk : X → Type u
  /-- The abelian group structure on `F_x`. -/
  stalkAddCommGroup : ∀ x, AddCommGroup (stalk x)
  /-- `F_x` is a module over the stalk ring `O_{X,x}`. -/
  stalkModule : ∀ x, @Module (Ostalk X x) (stalk x) _ (stalkAddCommGroup x).toAddCommMonoid
  /-- The germ map `F(U) → F_x` at `x ∈ U`. -/
  germ : ∀ (U : Opens X) (x : X) (_ : x ∈ U), sheaf.obj (op U) → stalk x
  /-- The germ map is additive. -/
  germ_add : ∀ (U : Opens X) (x : X) (h : x ∈ U) (s t : sheaf.obj (op U)),
    germ U x h (s + t) = (germ U x h s) + (germ U x h t)
  /-- The germ map is semilinear over the ring germ map: `germ (g • s) = (O.germ g) • germ s`. -/
  germ_smul : ∀ (U : Opens X) (x : X) (h : x ∈ U) (g : OSections X U) (s : sheaf.obj (op U)),
    letI := module U; letI := stalkAddCommGroup x; letI := stalkModule x
    germ U x h (g • s) = (Ogerm X U x h g) • (germ U x h s)
  /-- The germ map is compatible with restriction. -/
  germ_res : ∀ {U V : Opens X} (i : V ≤ U) (x : X) (hV : x ∈ V) (s : sheaf.obj (op U)),
    germ V x hV ((sheaf.map (homOfLE i).op).hom s) = germ U x (i hV) s
  /-- Every element of the stalk `F_x` is the germ of some section (colimit surjectivity). -/
  germ_exist : ∀ (x : X) (t : stalk x), ∃ (U : Opens X) (h : x ∈ U) (s : sheaf.obj (op U)),
    germ U x h s = t
  /-- Two sections with equal germ at `x` agree after restriction to a smaller open
  (colimit locality). -/
  germ_eq : ∀ {U : Opens X} (x : X) (hU : x ∈ U) (s t : sheaf.obj (op U)),
    germ U x hU s = germ U x hU t →
    ∃ (V : Opens X) (_ : x ∈ V) (i : V ≤ U),
      (sheaf.map (homOfLE i).op).hom s = (sheaf.map (homOfLE i).op).hom t

attribute [instance] OXModule.module OXModule.stalkAddCommGroup OXModule.stalkModule

/-- Restriction map on `F`-sections, `F(U) → F(V)` for `V ≤ U`. -/
noncomputable def OXModule.res {X : AlgebraicGeometry.RingedSpace.{u}} (M : OXModule X)
    {U V : Opens X} (i : V ≤ U) (s : M.sheaf.obj (op U)) : M.sheaf.obj (op V) :=
  (M.sheaf.map (homOfLE i).op).hom s

/-- Germ–restriction compatibility for an `OXModule`, phrased via `M.res`. -/
theorem OXModule.germ_res' {X : AlgebraicGeometry.RingedSpace.{u}} (M : OXModule X)
    {U V : Opens X} (i : V ≤ U) (x : X) (hV : x ∈ V) (s : M.sheaf.obj (op U)) :
    M.germ V x hV (M.res i s) = M.germ U x (i hV) s :=
  M.germ_res i x hV s

/-- Definition 1 (Flat `O_X`-module). `F` is *flat* if for every point `x ∈ X` the stalk `F_x`
is a flat `O_{X,x}`-module. -/
def OXModule.IsFlat {X : AlgebraicGeometry.RingedSpace.{u}} (M : OXModule X) : Prop :=
  ∀ x : X, Module.Flat (Ostalk X x) (M.stalk x)

/-- The germ map of an `OXModule` sends `0` to `0`. -/
theorem OXModule.germ_zero {X : AlgebraicGeometry.RingedSpace.{u}} (M : OXModule X)
    (U : Opens X) (x : X) (hx : x ∈ U) :
    letI := M.stalkAddCommGroup x
    M.germ U x hx 0 = 0 := by
  let := M.stalkAddCommGroup x
  have h2 := M.germ_add U x hx 0 0
  rw [add_zero] at h2
  have : M.germ U x hx 0 + M.germ U x hx 0 = M.germ U x hx 0 + 0 := by rw [add_zero, ← h2]
  exact add_left_cancel this

/-- The germ map of an `OXModule` commutes with finite sums. -/
theorem OXModule.germ_sum {X : AlgebraicGeometry.RingedSpace.{u}} (M : OXModule X)
    (U : Opens X) (x : X) (hx : x ∈ U) {ι : Type*} (s : Finset ι)
    (c : ι → M.sheaf.obj (op U)) :
    letI := M.stalkAddCommGroup x
    M.germ U x hx (∑ i ∈ s, c i) = ∑ i ∈ s, M.germ U x hx (c i) := by
  let := M.stalkAddCommGroup x
  let germHom : M.sheaf.obj (op U) →+ M.stalk x :=
    { toFun := M.germ U x hx
      map_zero' := M.germ_zero U x hx
      map_add' := M.germ_add U x hx }
  exact map_sum germHom c s

/-- Germ–restriction compatibility for the structure sheaf:
`Ogerm V (g|_V) = Ogerm U g`. -/
theorem Ogerm_res (X : AlgebraicGeometry.RingedSpace.{u}) {U V : Opens X} (i : V ≤ U) (x : X)
    (hV : x ∈ V) (g : OSections X U) :
    Ogerm X V x hV (Ores X i g) = Ogerm X U x (i hV) g := by
  simp [Ogerm, Ores]

/-- Restriction of `O_X`-sections collapses under composition:
`(g|_V)|_W = g|_W`. (Presheaf functoriality.) -/
theorem Ores_res (X : AlgebraicGeometry.RingedSpace.{u}) {U V W : Opens X}
    (iWV : W ≤ V) (iVU : V ≤ U) (g : OSections X U) :
    Ores X iWV (Ores X iVU g) = Ores X (le_trans iWV iVU) g := by
  unfold Ores
  rw [← X.presheaf.map_comp_apply]
  rfl

/-- Restriction of `F`-sections collapses under composition: `(s|_V)|_W = s|_W`. -/
theorem OXModule.res_res {X : AlgebraicGeometry.RingedSpace.{u}} (M : OXModule X)
    {U V W : Opens X} (iWV : W ≤ V) (iVU : V ≤ U) (s : M.sheaf.obj (op U)) :
    M.res iWV (M.res iVU s) = M.res (le_trans iWV iVU) s := by
  unfold OXModule.res
  rw [← M.sheaf.map_comp_apply]
  rfl

/-- `M.res` commutes with finite sums (it is the underlying map of an `AddCommGrp` hom). -/
theorem OXModule.res_sum {X : AlgebraicGeometry.RingedSpace.{u}} (M : OXModule X)
    {U V : Opens X} (i : V ≤ U) {ι : Type*} (S : Finset ι) (c : ι → M.sheaf.obj (op U)) :
    M.res i (∑ k ∈ S, c k) = ∑ k ∈ S, M.res i (c k) := by
  unfold OXModule.res
  exact map_sum _ c S

/-- `M.res` is semilinear over the ring restriction (restated form of `M.res_smul`). -/
theorem OXModule.res_smul' {X : AlgebraicGeometry.RingedSpace.{u}} (M : OXModule X)
    {U V : Opens X} (i : V ≤ U) (g : OSections X U) (s : M.sheaf.obj (op U)) :
    M.res i (g • s) = Ores X i g • M.res i s :=
  M.res_smul i g s

/-- The equational criterion for flatness (Tag 04VX, equational form): given a relation
`∑ φᵢ • σᵢ = 0` in a flat module `M`, there exist `k`, scalars `αᵢⱼ` and elements `τⱼ`
such that `σᵢ = ∑ⱼ αᵢⱼ • τⱼ` and `∑ᵢ φᵢ αᵢⱼ = 0`. -/
theorem flat_equational_criterion {R Mod : Type u} [CommRing R] [AddCommGroup Mod] [Module R Mod]
    [Module.Flat R Mod]
    {n : ℕ} (φ : Fin n → R) (σ : Fin n → Mod) (h : ∑ i, φ i • σ i = 0) :
    ∃ (k : ℕ) (α : Fin n → Fin k → R) (τ : Fin k → Mod),
      (∀ i, σ i = ∑ j, α i j • τ j) ∧ (∀ j, ∑ i, φ i * α i j = 0) := by
  have linmap_eval : ∀ {k : ℕ} (y : (Fin k →₀ R) →ₗ[R] Mod) (g : Fin k →₀ R),
      y g = ∑ j, g j • y (Finsupp.single j 1) := by
    intro k y g
    conv_lhs => rw [show g = ∑ j, Finsupp.single j (g j) by ext j; simp]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show Finsupp.single j (g j) = g j • Finsupp.single j (1:R) by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    rw [map_smul]
  set x : (Fin n →₀ R) →ₗ[R] Mod := Finsupp.linearCombination R σ with hx
  set fv : Fin n →₀ R := ∑ i, Finsupp.single i (φ i) with hfv
  have hxf : x fv = 0 := by
    rw [hx, hfv, map_sum]
    simp only [Finsupp.linearCombination_single]
    exact h
  obtain ⟨k, a, y, hcomp, haf⟩ := (Module.Flat.iff_forall_exists_factorization.mp ‹_›) hxf
  refine ⟨k, fun i j => (a (Finsupp.single i 1)) j, fun j => y (Finsupp.single j 1), ?_, ?_⟩
  · intro i
    have hsi : σ i = x (Finsupp.single i 1) := by
      rw [hx, Finsupp.linearCombination_single, one_smul]
    rw [hsi, hcomp, LinearMap.comp_apply, linmap_eval y (a (Finsupp.single i 1))]
  · intro j
    have key : a fv = ∑ i, φ i • a (Finsupp.single i 1) := by
      rw [hfv, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show Finsupp.single i (φ i) = φ i • Finsupp.single i (1:R) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      rw [map_smul]
    have hcoord : (a fv) j = ∑ i, φ i * (a (Finsupp.single i 1)) j := by
      rw [key, Finsupp.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finsupp.smul_apply, smul_eq_mul]
    rw [haf] at hcoord
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hcoord
    exact hcoord.symm

-- Main Statement(s)

/-- **Stacks Project Tag 08BK (Modules, Lemma 17.17.11).**

Let `(X, O_X)` be a ringed space and `F` a flat `O_X`-module. Let `U ⊆ X` be open, `n ∈ ℕ`,
`f₁, …, fₙ ∈ O_X(U)` and `s₁, …, sₙ ∈ F(U)` such that the diagram
`O_U → O_U^{⊕n} → F|_U` is a complex, i.e. `∑ᵢ fᵢ • sᵢ = 0` in `F(U)`.

Then for every `x ∈ U` there exist an open neighbourhood `V ⊆ U` of `x`, an integer `m`,
sections `t₁, …, t_m ∈ F(V)` and scalars `a_{ji} ∈ O_X(V)` such that:
  - (Factorization)  `sᵢ|_V = ∑ⱼ a_{ji} • t_j`   for every `i`;
  - (Annihilation)   `∑ᵢ a_{ji} • fᵢ|_V = 0`      for every `j`. -/
@[stacks 08BK]
theorem exists_local_factorization_of_isFlat {X : AlgebraicGeometry.RingedSpace.{u}}
  (M : OXModule X) (hM : M.IsFlat)
    (U : Opens X) (n : ℕ) (f : Fin n → OSections X U) (s : Fin n → M.sheaf.obj (op U))
    (hcomplex : ∑ i, f i • s i = 0)
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (_ : x ∈ V) (iVU : V ≤ U) (m : ℕ)
      (t : Fin m → M.sheaf.obj (op V)) (a : Fin m → Fin n → OSections X V),
      (∀ i, M.res iVU (s i) = ∑ j, a j i • t j) ∧
      (∀ j, ∑ i, a j i • Ores X iVU (f i) = 0) := by
  -- germs at x
  let := M.stalkAddCommGroup x
  let := M.stalkModule x
  set φ : Fin n → Ostalk X x := fun i => Ogerm X U x hx (f i) with hφ
  set σ : Fin n → M.stalk x := fun i => M.germ U x hx (s i) with hσ
  -- the germ relation
  have hrel : ∑ i, φ i • σ i = 0 := by
    have hsum : M.germ U x hx (∑ i, f i • s i) = ∑ i, φ i • σ i := by
      rw [M.germ_sum U x hx]
      apply Finset.sum_congr rfl
      intro i _
      rw [M.germ_smul U x hx (f i) (s i)]
    rw [← hsum, hcomplex, M.germ_zero U x hx]
  -- equational criterion at the flat stalk
  have : Module.Flat (Ostalk X x) (M.stalk x) := hM x
  obtain ⟨k, α, τ, hfact, hann⟩ := flat_equational_criterion φ σ hrel
  -- lift τ j to sections over neighborhoods Wt j
  choose Wt hWt t0 ht0 using fun j : Fin k => M.germ_exist x (τ j)
  -- lift α i j to ring sections over neighborhoods Wa
  have liftα : ∀ p : Fin n × Fin k, ∃ (W : Opens X) (h : x ∈ W) (g : OSections X W),
      Ogerm X W x h g = α p.1 p.2 := fun p => X.presheaf.exists_germ_eq (α p.1 p.2)
  choose Wa hWa a0 ha0 using liftα
  -- common neighbourhood V0
  set V0 : Opens X := U ⊓ (Finset.univ.inf Wt) ⊓ (Finset.univ.inf Wa) with hV0
  have hxV0 : x ∈ V0 := by
    rw [hV0]
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · rw [Opens.coe_finset_inf]
      simp only [Finset.inf_set_eq_iInter, Set.mem_iInter, Function.comp_apply]
      intro j _; exact hWt j
    · rw [Opens.coe_finset_inf]
      simp only [Finset.inf_set_eq_iInter, Set.mem_iInter, Function.comp_apply]
      intro p _; exact hWa p
  have hV0U : V0 ≤ U := le_trans inf_le_left inf_le_left
  have hV0Wt : ∀ j, V0 ≤ Wt j := fun j =>
    le_trans inf_le_left (le_trans inf_le_right (Finset.inf_le (Finset.mem_univ j)))
  have hV0Wa : ∀ p, V0 ≤ Wa p := fun p =>
    le_trans inf_le_right (Finset.inf_le (Finset.mem_univ p))
  -- candidate sections over V0
  set t : Fin k → M.sheaf.obj (op V0) := fun j => M.res (hV0Wt j) (t0 j) with ht
  set a : Fin k → Fin n → OSections X V0 := fun j i => Ores X (hV0Wa (i, j)) (a0 (i, j)) with ha
  -- factorization germ equality over V0
  have hgeq_fact : ∀ i, M.germ V0 x hxV0 (M.res hV0U (s i)) = M.germ V0 x hxV0 (∑ j, a j i • t
      j) := by
    intro i
    have hL : M.germ V0 x hxV0 (M.res hV0U (s i)) = σ i := by
      rw [hσ]; exact M.germ_res hV0U x hxV0 (s i)
    have hR : M.germ V0 x hxV0 (∑ j, a j i • t j) = σ i := by
      rw [M.germ_sum V0 x hxV0]
      have : ∀ j, M.germ V0 x hxV0 (a j i • t j) = α i j • τ j := by
        intro j
        rw [M.germ_smul V0 x hxV0 (a j i) (t j)]
        simp only [ha, ht]
        rw [Ogerm_res X (hV0Wa (i, j)) x hxV0 (a0 (i, j))]
        rw [M.germ_res' (hV0Wt j) x hxV0 (t0 j)]
        rw [ha0 (i, j), ht0 j]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      exact (hfact i).symm
    rw [hL, hR]
  -- annihilation germ equality over V0
  have hgeq_ann : ∀ j, Ogerm X V0 x hxV0 (∑ i, a j i • Ores X hV0U (f i)) =
      Ogerm X V0 x hxV0 0 := by
    intro j
    rw [map_zero]
    rw [map_sum]
    have : ∀ i, Ogerm X V0 x hxV0 (a j i • Ores X hV0U (f i)) = φ i * α i j := by
      intro i
      rw [smul_eq_mul, map_mul]
      rw [ha]
      rw [Ogerm_res X (hV0Wa (i, j)) x hxV0 (a0 (i, j)), ha0 (i, j)]
      rw [Ogerm_res X hV0U x hxV0 (f i)]
      rw [hφ]
      ring
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    exact hann j
  ----------------------------------------------------------------------------
  -- DESCENT: pass from germ equalities over V0 to honest section equalities
  -- over a smaller common neighbourhood V, then assemble the final witnesses.
  ----------------------------------------------------------------------------
  -- (A) Descend each factorization germ-equality to a section equality on some
  --     open `Vf i ∋ x`, `Vf i ≤ V0`.  This is the colimit-locality field
  --     `M.germ_eq` applied to `hgeq_fact i`; it returns exactly an open and a
  --     restriction-collapse of the two sides.
  -- SANITY CHECK PASSED
  have hfact_loc : ∀ i, ∃ (W : Opens X) (_ : x ∈ W) (iW : W ≤ V0),
      M.res iW (M.res hV0U (s i)) = M.res iW (∑ j, a j i • t j) := by
    intro i
    obtain ⟨W, hxW, iW, hW⟩ := M.germ_eq x hxV0 _ _ (hgeq_fact i)
    exact ⟨W, hxW, iW, hW⟩
  -- (B) Descend each annihilation germ-equality to a section equality on some
  --     open `Va j ∋ x`, `Va j ≤ V0`.  This is structure-sheaf colimit locality
  --     `TopCat.Presheaf.germ_eq` applied to `hgeq_ann j`; the right side is the
  --     germ of `0`, so after restriction the section restricts to `0`.
  --     The two inclusions returned by `germ_eq` are arrows `W ⟶ V0` in the thin
  --     poset category `Opens X`, hence equal, and `(map _).hom 0 = 0`.
  -- SANITY CHECK PASSED
  have hann_loc : ∀ j, ∃ (W : Opens X) (_ : x ∈ W) (iW : W ≤ V0),
      Ores X iW (∑ i, a j i • Ores X hV0U (f i)) = 0 := by
    intro j
    obtain ⟨W, hxW, iU, iV, hW⟩ :=
      TopCat.Presheaf.germ_eq X.presheaf (U := V0) (V := V0) x hxV0 hxV0
        (∑ i, a j i • Ores X hV0U (f i)) 0 (hgeq_ann j)
    refine ⟨W, hxW, iU.le, ?_⟩
    -- `iU, iV : W ⟶ V0` agree (thin category), and `(map iV.op).hom 0 = 0`.
    have hiUV : (homOfLE iU.le : W ⟶ V0) = iU := Subsingleton.elim _ _
    simpa only [Ores, hiUV, map_zero] using hW
  -- (C) Collect the descent neighbourhoods and form the common open `V`.
  choose Vf hxVf iVf hVf using hfact_loc
  choose Va hxVa iVa hVa using hann_loc
  set V : Opens X := V0 ⊓ (Finset.univ.inf Vf) ⊓ (Finset.univ.inf Va) with hVdef
  have hxV : x ∈ V := by
    rw [hVdef]
    refine ⟨⟨hxV0, ?_⟩, ?_⟩
    · rw [Opens.coe_finset_inf]
      simp only [Finset.inf_set_eq_iInter, Set.mem_iInter, Function.comp_apply]
      intro i _; exact hxVf i
    · rw [Opens.coe_finset_inf]
      simp only [Finset.inf_set_eq_iInter, Set.mem_iInter, Function.comp_apply]
      intro j _; exact hxVa j
  have hVV0 : V ≤ V0 := le_trans inf_le_left inf_le_left
  have hVVf : ∀ i, V ≤ Vf i := fun i =>
    le_trans inf_le_left (le_trans inf_le_right (Finset.inf_le (Finset.mem_univ i)))
  have hVVa : ∀ j, V ≤ Va j := fun j =>
    le_trans inf_le_right (Finset.inf_le (Finset.mem_univ j))
  have hVU : V ≤ U := le_trans hVV0 hV0U
  -- (D) Final witnesses: V, m := k, t' j := t j |_V, a' j i := a j i |_V.
  refine ⟨V, hxV, hVU, k, fun j => M.res hVV0 (t j), fun j i => Ores X hVV0 (a j i), ?_, ?_⟩
  · -- Factorization over V.  Restrict the descent equality (A) from `Vf i` to `V`
    -- (using `V ≤ Vf i`), then collapse all nested restrictions via `res_res`,
    -- and push `M.res` through the finite sum (`res_sum`) and the scalar action
    -- (`res_smul'`) so that `s i|_V = ∑ⱼ (a j i|_V) • (t j|_V)`.
    intro i
    -- restrict the section equality (A) from Vf i down to V
    have hres : M.res (hVVf i) (M.res (iVf i) (M.res hV0U (s i)))
        = M.res (hVVf i) (M.res (iVf i) (∑ j, a j i • t j)) := by
      rw [hVf i]
    -- collapse all nested restrictions to a single restriction to V
    rw [M.res_res, M.res_res, M.res_res] at hres
    -- push res through the sum and each `•` on the right of `hres`
    rw [M.res_sum] at hres
    have hsmul : ∀ j, M.res (le_trans (hVVf i) (iVf i)) (a j i • t j)
        = (Ores X hVV0 (a j i)) • (M.res hVV0 (t j)) := by
      intro j
      rw [M.res_smul']
    rw [Finset.sum_congr rfl (fun j _ => hsmul j)] at hres
    -- the LHS path `V ≤ U` of `hres` equals `hVU` by proof irrelevance
    convert hres using 2
  · -- Annihilation over V.  Restrict the descent equality (B) from `Va j` to `V`
    -- (using `V ≤ Va j`), then push `Ores` through the sum (`map_sum`) and the
    -- product (`smul_eq_mul`, `map_mul`) and collapse nested restrictions
    -- (`Ores_res`), giving `∑ᵢ (a j i|_V) • (f i|_V) = 0`.
    intro j
    have hres : Ores X (hVVa j) (Ores X (iVa j) (∑ i, a j i • Ores X hV0U (f i)))
        = Ores X (hVVa j) 0 := by
      rw [hVa j]
    rw [map_zero] at hres
    rw [Ores_res] at hres
    rw [map_sum] at hres
    -- push each summand through `Ores` (a ring hom) and collapse nested restrictions
    have hsmul : ∀ i, Ores X (le_trans (hVVa j) (iVa j)) (a j i • Ores X hV0U (f i))
        = (Ores X hVV0 (a j i)) • (Ores X hVU (f i)) := by
      intro i
      rw [smul_eq_mul, map_mul, smul_eq_mul]
      simp only [ha, Ores_res]
    rw [Finset.sum_congr rfl (fun i _ => hsmul i)] at hres
    convert hres using 2

end Stacks.FlatEquationalCriterion
