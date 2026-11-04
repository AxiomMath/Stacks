module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Invariants of an involution, and the switch on a tensor square along a short exact sequence

Let `C` be an abelian category in which `2` is invertible, in the sense that `2 • 𝟙 X` is an
isomorphism for every object `X`. An involution `τ` of an object `V` then splits `V` as the sum
of its *invariants* `V^+ = ker(𝟙 - τ)` and its *anti-invariants* `V^- = ker(𝟙 + τ)`, the
idempotents being `(𝟙 ± τ)/2`, and taking invariants is exact: an equivariant short exact
sequence gives short exact sequences of invariants and of anti-invariants.

Given a function `χ` on the objects of `C`, additive along short exact sequences of objects
satisfying a property `P` which has the two-out-of-three property (an `ExactClass`), the
*trace* of an involution `τ` is `χ(V^+) - χ(V^-)`. The main result,
`Stacks.SecondAdamsPerfect.switchTrace_tensorSquare`, is the argument of [Stacks, Tag 0FEJ] for
the second Adams operation, in a symmetric monoidal abelian category: for a short exact
sequence `0 → A → B → C → 0` which stays short exact after tensoring with any object, the trace
of the switch of the factors of `B ⊗ B` is the sum of the traces of the switch on `A ⊗ A` and
on `C ⊗ C`.

## Main definitions

* `Stacks.SecondAdamsPerfect.invariantIdempotent`, `antiInvariantIdempotent`: the idempotents
  `(𝟙 + τ)/2` and `(𝟙 - τ)/2` of an endomorphism `τ` of an object on which `2` is invertible.
* `Stacks.SecondAdamsPerfect.invariants`: the invariants `ker(𝟙 - τ)` of an endomorphism `τ`;
  the anti-invariants are the invariants of `-τ`.
* `Stacks.SecondAdamsPerfect.invariantsπ`: the projection onto the invariants, which together
  with the kernel inclusion splits `invariantIdempotent τ`.
* `Stacks.SecondAdamsPerfect.ExactClass`: a function on objects additive along short exact
  sequences inside a two-out-of-three class of objects closed under summands.
* `Stacks.SecondAdamsPerfect.switchTrace`: the trace `χ(V^+) - χ(V^-)` of an endomorphism.

## Main results

* `Stacks.SecondAdamsPerfect.invariantsShortComplex_shortExact`: taking invariants is exact.
* `Stacks.SecondAdamsPerfect.switchTrace_shortExact`: the trace is additive along equivariant
  short exact sequences.
* `Stacks.SecondAdamsPerfect.switchTrace_eq_zero_of_anticommute`: the trace of an involution
  vanishes when an involution anticommuting with it exists.
* `Stacks.SecondAdamsPerfect.switchTrace_tensorSquare`: **the trace of the switch on the tensor
  square is additive along a short exact sequence which stays short exact after tensoring.**

## Implementation notes

The source's proof of additivity for `ψ²` filters `Sym²` of the middle term in three steps,
with graded pieces `Sym² A`, `A ⊗ C` and `Sym² C`, and uses that the middle pieces of the
symmetric and the exterior square agree. Here the same filtration of `B ⊗ B` is used in the
form of two equivariant short exact sequences

`0 → A ⊗ A → (A ⊗ B) ⊕ (B ⊗ A) → F → 0`  and  `0 → F → B ⊗ B → C ⊗ C → 0`,

where `F` is the kernel of `p ⊗ p`. The first is a Mayer–Vietoris sequence: `F` is the sum of
the two subobjects `A ⊗ B` and `B ⊗ A`, whose intersection is `A ⊗ A`. The switch exchanges
the two summands of the middle term, so its trace there vanishes (an anticommuting involution
interchanges invariants and anti-invariants), and it acts on `A ⊗ A` with a sign, because of
the sign in the first map. This avoids identifying the graded piece `F/(A ⊗ A)` with
`(A ⊗ C) ⊕ (C ⊗ A)`. The exactness of the two sequences is proved by diagram chases up to
refinements, from the exactness of the given sequence tensored on either side.

## References

* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FEK](https://stacks.math.columbia.edu/tag/0FEK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v u

namespace Stacks.SecondAdamsPerfect

/-! ### The idempotents `(𝟙 ± τ)/2` -/

section Halving

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Halving commutes with every morphism. -/
@[reassoc]
theorem inv_two_smul_id_comp {X Y : C} [IsIso ((2 : ℤ) • 𝟙 X)] [IsIso ((2 : ℤ) • 𝟙 Y)]
    (f : X ⟶ Y) : inv ((2 : ℤ) • 𝟙 X) ≫ f = f ≫ inv ((2 : ℤ) • 𝟙 Y) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.comp_id, Category.id_comp]

/-- **The invariant idempotent `(𝟙 + τ)/2`** of an endomorphism `τ` of an object on which `2`
is invertible. -/
def invariantIdempotent {V : C} (τ : V ⟶ V) [IsIso ((2 : ℤ) • 𝟙 V)] : V ⟶ V :=
  inv ((2 : ℤ) • 𝟙 V) ≫ (𝟙 V + τ)

/-- **The anti-invariant idempotent `(𝟙 - τ)/2`** of an endomorphism `τ` of an object on which
`2` is invertible. -/
def antiInvariantIdempotent {V : C} (τ : V ⟶ V) [IsIso ((2 : ℤ) • 𝟙 V)] : V ⟶ V :=
  inv ((2 : ℤ) • 𝟙 V) ≫ (𝟙 V - τ)

/-- The anti-invariant idempotent of `τ` is the invariant idempotent of `-τ`. -/
theorem antiInvariantIdempotent_eq {V : C} (τ : V ⟶ V) [IsIso ((2 : ℤ) • 𝟙 V)] :
    antiInvariantIdempotent τ = invariantIdempotent (-τ) := by
  rw [antiInvariantIdempotent, invariantIdempotent, sub_eq_add_neg]

/-- The invariant idempotent commutes with a morphism intertwining the two endomorphisms. -/
private theorem invariantIdempotent_comp_comm {X Y : C} {τ : X ⟶ X} {τ' : Y ⟶ Y} (f : X ⟶ Y)
    [IsIso ((2 : ℤ) • 𝟙 X)] [IsIso ((2 : ℤ) • 𝟙 Y)] (h : f ≫ τ' = τ ≫ f) :
    invariantIdempotent τ ≫ f = f ≫ invariantIdempotent τ' := by
  have h' : (𝟙 _ + τ) ≫ f = f ≫ (𝟙 _ + τ') := by
    simp [Preadditive.add_comp, Preadditive.comp_add, h]
  rw [invariantIdempotent, invariantIdempotent, Category.assoc, h', inv_two_smul_id_comp_assoc]

/-- The invariant idempotent is compatible with conjugation by an isomorphism intertwining the
two endomorphisms. -/
theorem invariantIdempotent_conj {V W : C} (φ : V ≅ W) {τ : V ⟶ V} {τ' : W ⟶ W}
    (h : τ ≫ φ.hom = φ.hom ≫ τ') [IsIso ((2 : ℤ) • 𝟙 V)] [IsIso ((2 : ℤ) • 𝟙 W)] :
    φ.inv ≫ invariantIdempotent τ ≫ φ.hom = invariantIdempotent τ' := by
  rw [invariantIdempotent_comp_comm φ.hom h.symm, Iso.inv_hom_id_assoc]

/-- An additive functor carries the invariant idempotent of `τ` to that of its image. -/
theorem Functor.map_invariantIdempotent {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] {V : C} (τ : V ⟶ V) [IsIso ((2 : ℤ) • 𝟙 V)] [IsIso ((2 : ℤ) • 𝟙 (F.obj V))] :
    F.map (invariantIdempotent τ) = invariantIdempotent (F.map τ) := by
  have h : F.map (inv ((2 : ℤ) • 𝟙 V)) = inv ((2 : ℤ) • 𝟙 (F.obj V)) := by
    apply IsIso.eq_inv_of_hom_inv_id
    rw [show (2 : ℤ) • 𝟙 (F.obj V) = F.map ((2 : ℤ) • 𝟙 V) by rw [F.map_zsmul, F.map_id],
      ← F.map_comp,
      IsIso.hom_inv_id, F.map_id]
  rw [invariantIdempotent, invariantIdempotent, F.map_comp, h, F.map_add, F.map_id]

end Halving

/-! ### Invariants -/

section Invariants

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The invariants `ker(𝟙 - τ)`** of an endomorphism `τ`. The anti-invariants of `τ` are the
invariants of `-τ`. -/
abbrev invariants {V : C} (τ : V ⟶ V) : C := kernel (𝟙 V - τ)

/-- The endomorphism acts as the identity on its invariants. -/
@[reassoc]
theorem invariants_ι_comp {V : C} (τ : V ⟶ V) :
    kernel.ι (𝟙 V - τ) ≫ τ = kernel.ι (𝟙 V - τ) := by
  have h := kernel.condition (𝟙 V - τ)
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
  exact h.symm

variable [∀ X : C, IsIso ((2 : ℤ) • 𝟙 X)]

/-- The invariant idempotent of an involution is killed by `𝟙 - τ`. -/
theorem invariantIdempotent_comp_sub {V : C} {τ : V ⟶ V} (hτ : τ ≫ τ = 𝟙 V) :
    invariantIdempotent τ ≫ (𝟙 V - τ) = 0 := by
  rw [invariantIdempotent, Category.assoc, Preadditive.add_comp, Category.id_comp,
    Preadditive.comp_sub, Category.comp_id, hτ, sub_add_sub_cancel, sub_self, comp_zero]

/-- **The projection onto the invariants**, the factorization of `(𝟙 + τ)/2` through
`ker(𝟙 - τ)`. -/
def invariantsπ {V : C} (τ : V ⟶ V) (hτ : τ ≫ τ = 𝟙 V) : V ⟶ invariants τ :=
  kernel.lift _ (invariantIdempotent τ) (invariantIdempotent_comp_sub hτ)

/-- The projection onto the invariants followed by the inclusion is the invariant idempotent. -/
@[reassoc (attr := simp)]
theorem invariantsπ_ι {V : C} (τ : V ⟶ V) (hτ : τ ≫ τ = 𝟙 V) :
    invariantsπ τ hτ ≫ kernel.ι (𝟙 V - τ) = invariantIdempotent τ :=
  kernel.lift_ι _ _ _

/-- The invariant idempotent restricts to the identity on the invariants. -/
@[reassoc]
theorem ι_invariantIdempotent {V : C} (τ : V ⟶ V) :
    kernel.ι (𝟙 V - τ) ≫ invariantIdempotent τ = kernel.ι (𝟙 V - τ) := by
  rw [invariantIdempotent, ← Category.assoc, ← inv_two_smul_id_comp, Category.assoc,
    Preadditive.comp_add, Category.comp_id, invariants_ι_comp, IsIso.inv_comp_eq,
    Preadditive.zsmul_comp, Category.id_comp, two_smul]

/-- The inclusion of the invariants followed by the projection is the identity. -/
@[reassoc (attr := simp)]
theorem ι_invariantsπ {V : C} (τ : V ⟶ V) (hτ : τ ≫ τ = 𝟙 V) :
    kernel.ι (𝟙 V - τ) ≫ invariantsπ τ hτ = 𝟙 _ := by
  rw [← cancel_mono (kernel.ι (𝟙 V - τ)), Category.assoc, invariantsπ_ι, Category.id_comp,
    ι_invariantIdempotent]

/-- The invariants of `τ` meet the anti-invariants trivially. -/
@[reassoc]
theorem ι_invariantsπ_neg {V : C} (τ τ' : V ⟶ V) (h : τ' = -τ) (hτ' : τ' ≫ τ' = 𝟙 V) :
    kernel.ι (𝟙 V - τ) ≫ invariantsπ τ' hτ' = 0 := by
  rw [← cancel_mono (kernel.ι (𝟙 V - τ')), Category.assoc, invariantsπ_ι, zero_comp,
    invariantIdempotent, ← Category.assoc, ← inv_two_smul_id_comp, Category.assoc,
    Preadditive.comp_add, Category.comp_id, h, Preadditive.comp_neg, invariants_ι_comp,
    add_neg_cancel, comp_zero]

/-- **An involution splits its object as the sum of the invariants and the
anti-invariants.** -/
def invariantsBiprodIso {V : C} (τ : V ⟶ V) (hτ : τ ≫ τ = 𝟙 V) :
    V ≅ invariants τ ⊞ invariants (-τ) where
  hom := biprod.lift (invariantsπ τ hτ) (invariantsπ (-τ) (by simpa using hτ))
  inv := biprod.desc (kernel.ι _) (kernel.ι _)
  hom_inv_id := by
    rw [biprod.lift_desc, invariantsπ_ι, invariantsπ_ι, invariantIdempotent,
      invariantIdempotent, ← Preadditive.comp_add, IsIso.inv_comp_eq, Category.comp_id,
      show 𝟙 V + τ + (𝟙 V + -τ) = 𝟙 V + 𝟙 V by abel, two_smul]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp [ι_invariantsπ_neg τ (-τ) rfl, ι_invariantsπ_neg (-τ) τ (neg_neg τ).symm]

end Invariants

/-! ### Exactness of taking invariants -/

section Exactness

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short complex of invariants of an equivariant short complex. -/
abbrev invariantsShortComplex (S : ShortComplex C) (τ₁ : S.X₁ ⟶ S.X₁) (τ₂ : S.X₂ ⟶ S.X₂)
    (τ₃ : S.X₃ ⟶ S.X₃) (hf : S.f ≫ τ₂ = τ₁ ≫ S.f) (hg : S.g ≫ τ₃ = τ₂ ≫ S.g) :
    ShortComplex C where
  X₁ := invariants τ₁
  X₂ := invariants τ₂
  X₃ := invariants τ₃
  f := kernel.map _ _ S.f S.f (by simp [Preadditive.sub_comp, Preadditive.comp_sub, hf])
  g := kernel.map _ _ S.g S.g (by simp [Preadditive.sub_comp, Preadditive.comp_sub, hg])
  zero := by
    rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, ← Category.assoc,
      kernel.lift_ι, Category.assoc, S.zero, comp_zero, zero_comp]

variable [∀ X : C, IsIso ((2 : ℤ) • 𝟙 X)]

/-- **Taking invariants is exact**: the invariants of an equivariant short exact sequence of
involutions form a short exact sequence. The short complex of invariants is a retract of the
given one. -/
theorem invariantsShortComplex_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    {τ₁ : S.X₁ ⟶ S.X₁} {τ₂ : S.X₂ ⟶ S.X₂} {τ₃ : S.X₃ ⟶ S.X₃}
    (h₁ : τ₁ ≫ τ₁ = 𝟙 _) (h₂ : τ₂ ≫ τ₂ = 𝟙 _) (h₃ : τ₃ ≫ τ₃ = 𝟙 _)
    (hf : S.f ≫ τ₂ = τ₁ ≫ S.f) (hg : S.g ≫ τ₃ = τ₂ ≫ S.g) :
    (invariantsShortComplex S τ₁ τ₂ τ₃ hf hg).ShortExact := by
  have hf' := invariantIdempotent_comp_comm S.f hf
  have hg' := invariantIdempotent_comp_comm S.g hg
  let ι : invariantsShortComplex S τ₁ τ₂ τ₃ hf hg ⟶ S :=
    { τ₁ := kernel.ι _
      τ₂ := kernel.ι _
      τ₃ := kernel.ι _
      comm₁₂ := by simp
      comm₂₃ := by simp }
  let π : S ⟶ invariantsShortComplex S τ₁ τ₂ τ₃ hf hg :=
    { τ₁ := invariantsπ τ₁ h₁
      τ₂ := invariantsπ τ₂ h₂
      τ₃ := invariantsπ τ₃ h₃
      comm₁₂ := by
        refine (cancel_mono (kernel.ι (𝟙 S.X₂ - τ₂))).1 ?_
        simp [hf']
      comm₂₃ := by
        refine (cancel_mono (kernel.ι (𝟙 S.X₃ - τ₃))).1 ?_
        simp [hg'] }
  have hιπ : ι ≫ π = 𝟙 _ := by
    ext <;> simp [ι, π]
  have := hS.mono_f
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.exact_iff_isZero_homology]
    have : Mono (ShortComplex.homologyMap ι) := by
      refine ⟨fun a b h => ?_⟩
      have h' := congrArg (· ≫ ShortComplex.homologyMap π) h
      simpa [← ShortComplex.homologyMap_comp, hιπ] using h'
    exact IsZero.of_mono (ShortComplex.homologyMap ι)
      ((ShortComplex.exact_iff_isZero_homology S).1 hS.exact)
  · exact mono_of_mono_fac (show (invariantsShortComplex S τ₁ τ₂ τ₃ hf hg).f ≫
      kernel.ι (𝟙 S.X₂ - τ₂) = kernel.ι (𝟙 S.X₁ - τ₁) ≫ S.f by simp)
  · have : IsSplitEpi (invariantsπ τ₃ h₃) := IsSplitEpi.mk' ⟨kernel.ι _, ι_invariantsπ τ₃ h₃⟩
    exact epi_of_epi_fac (show invariantsπ τ₂ h₂ ≫ (invariantsShortComplex S τ₁ τ₂ τ₃ hf hg).g =
      S.g ≫ invariantsπ τ₃ h₃ from π.comm₂₃)

end Exactness

/-! ### Additive classes and the trace of an involution -/

section Trace

variable (C : Type u) [Category.{v} C] [Abelian C] (G : Type*) [AddCommGroup G]

/-- **An additive class on an abelian category**: a function `χ` on objects with values in an
abelian group, together with a class `P` of objects closed under isomorphisms and under
summands and with the two-out-of-three property along short exact sequences, such that `χ` is
invariant under isomorphism and additive along short exact sequences of objects of `P`. -/
structure ExactClass where
  /-- The class of objects on which `χ` is additive. -/
  P : ObjectProperty C
  /-- The function on objects. -/
  χ : C → G
  /-- The class is closed under isomorphisms. -/
  of_iso : ∀ {X Y : C}, (X ≅ Y) → P X → P Y
  /-- The function is invariant under isomorphisms. -/
  χ_eq_of_iso : ∀ {X Y : C}, (X ≅ Y) → χ X = χ Y
  /-- Two out of three along a short exact sequence: the kernel term. -/
  of_shortExact₁ : ∀ S : ShortComplex C, S.ShortExact → P S.X₂ → P S.X₃ → P S.X₁
  /-- Two out of three along a short exact sequence: the middle term. -/
  of_shortExact₂ : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂
  /-- The function is additive along short exact sequences of objects of the class. -/
  χ_shortExact : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₂ → P S.X₃ →
    χ S.X₂ = χ S.X₁ + χ S.X₃
  /-- The class is closed under summands. -/
  of_biprod_fst : ∀ X Y : C, P (X ⊞ Y) → P X

variable {C G}

namespace ExactClass

variable (F : ExactClass C G)

/-- The class is closed under the second summand of a biproduct. -/
theorem of_biprod_snd {X Y : C} (h : F.P (X ⊞ Y)) : F.P Y :=
  F.of_biprod_fst Y X (F.of_iso (biprod.braiding X Y) h)

/-- The class is closed under binary biproducts. -/
theorem of_biprod {X Y : C} (hX : F.P X) (hY : F.P Y) : F.P (X ⊞ Y) :=
  F.of_shortExact₂ _ (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact hX hY

end ExactClass

/-- **The trace of an endomorphism** with respect to an additive class: `χ(V^+) - χ(V^-)`,
the anti-invariants being the invariants of `-τ`. -/
def switchTrace (F : ExactClass C G) {V : C} (τ : V ⟶ V) : G :=
  F.χ (invariants τ) - F.χ (invariants (-τ))

variable (F : ExactClass C G)

/-- The trace of `-τ` is minus the trace of `τ`: invariants and anti-invariants exchange. -/
theorem switchTrace_neg {V : C} (τ : V ⟶ V) : switchTrace F (-τ) = -switchTrace F τ := by
  rw [switchTrace, switchTrace, neg_neg, neg_sub]

/-- **The trace of an involution vanishes when an involution anticommutes with it**: such an
involution interchanges the invariants and the anti-invariants. -/
theorem switchTrace_eq_zero_of_anticommute {V : C} (τ u : V ⟶ V) (hu : u ≫ u = 𝟙 V)
    (hτu : u ≫ τ = -(τ ≫ u)) : switchTrace F τ = 0 := by
  have h₁ : (kernel.ι (𝟙 V - τ) ≫ u) ≫ (𝟙 V - -τ) = 0 := by
    simp only [Category.assoc, Preadditive.comp_sub, Preadditive.comp_neg, Category.comp_id,
      hτu, neg_neg, invariants_ι_comp_assoc, sub_self]
  have h₂ : (kernel.ι (𝟙 V - -τ) ≫ u) ≫ (𝟙 V - τ) = 0 := by
    have h := invariants_ι_comp (-τ)
    rw [Preadditive.comp_neg, neg_eq_iff_eq_neg] at h
    simp only [Category.assoc, Preadditive.comp_sub, Category.comp_id, hτu,
      Preadditive.comp_neg, sub_neg_eq_add, reassoc_of% h, Preadditive.neg_comp,
      add_neg_cancel]
  let e : invariants τ ≅ invariants (-τ) :=
    { hom := kernel.lift _ _ h₁
      inv := kernel.lift _ _ h₂
      hom_inv_id := by
        rw [← cancel_mono (kernel.ι _)]
        simp [hu]
      inv_hom_id := by
        rw [← cancel_mono (kernel.ι _)]
        simp [hu] }
  rw [switchTrace, F.χ_eq_of_iso e, sub_self]

variable [∀ X : C, IsIso ((2 : ℤ) • 𝟙 X)]

/-- The invariants of an involution of an object of the class lie in the class. -/
theorem ExactClass.P_invariants {V : C} (τ : V ⟶ V) (hτ : τ ≫ τ = 𝟙 V) (hV : F.P V) :
    F.P (invariants τ) :=
  F.of_biprod_fst _ _ (F.of_iso (invariantsBiprodIso τ hτ) hV)

/-- **The trace is additive along equivariant short exact sequences of involutions.** -/
theorem switchTrace_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    {τ₁ : S.X₁ ⟶ S.X₁} {τ₂ : S.X₂ ⟶ S.X₂} {τ₃ : S.X₃ ⟶ S.X₃}
    (h₁ : τ₁ ≫ τ₁ = 𝟙 _) (h₂ : τ₂ ≫ τ₂ = 𝟙 _) (h₃ : τ₃ ≫ τ₃ = 𝟙 _)
    (hf : S.f ≫ τ₂ = τ₁ ≫ S.f) (hg : S.g ≫ τ₃ = τ₂ ≫ S.g)
    (hP₁ : F.P S.X₁) (hP₂ : F.P S.X₂) (hP₃ : F.P S.X₃) :
    switchTrace F τ₂ = switchTrace F τ₁ + switchTrace F τ₃ := by
  have hn : ∀ {V : C} (τ : V ⟶ V), τ ≫ τ = 𝟙 V → (-τ) ≫ (-τ) = 𝟙 V := by simp
  have hn₁ := hn _ h₁
  have hn₂ := hn _ h₂
  have hn₃ := hn _ h₃
  have hnf : S.f ≫ (-τ₂) = (-τ₁) ≫ S.f := by simp [hf]
  have hng : S.g ≫ (-τ₃) = (-τ₂) ≫ S.g := by simp [hg]
  have ep := F.χ_shortExact _ (invariantsShortComplex_shortExact hS h₁ h₂ h₃ hf hg)
    (F.P_invariants τ₁ h₁ hP₁) (F.P_invariants τ₂ h₂ hP₂) (F.P_invariants τ₃ h₃ hP₃)
  have em := F.χ_shortExact _ (invariantsShortComplex_shortExact hS hn₁ hn₂ hn₃ hnf hng)
    (F.P_invariants _ hn₁ hP₁) (F.P_invariants _ hn₂ hP₂) (F.P_invariants _ hn₃ hP₃)
  dsimp only [invariantsShortComplex] at ep em
  rw [switchTrace, switchTrace, switchTrace, ep, em]
  abel

end Trace

/-! ### The switch on a tensor square along a short exact sequence -/

section TensorSquare

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C]

/-- Tensoring on the left is exact along `S` when tensoring on the right is, the two short
complexes being isomorphic through the symmetry. -/
theorem shortExact_map_tensorLeft {S : ShortComplex C}
    (hR : ∀ X : C, (S.map (tensorRight X)).ShortExact) (X : C) :
    (S.map (tensorLeft X)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (β_ S.X₁ X) (β_ S.X₂ X) (β_ S.X₃ X)
      (by simp [BraidedCategory.braiding_naturality_left])
      (by simp [BraidedCategory.braiding_naturality_left])) (hR X)

omit [SymmetricCategory C] in
/-- `(A ⊗ B) ⊕ (B ⊗ A) ⟶ B ⊗ B ⟶ C ⊗ C` is a complex. -/
@[reassoc]
theorem biprodDesc_comp_tensorHom (S : ShortComplex C) :
    biprod.desc (S.f ▷ S.X₂) (S.X₂ ◁ S.f) ≫ (S.g ⊗ₘ S.g) = 0 := by
  ext <;> simp [tensorHom_def, ← comp_whiskerRight_assoc, ← whiskerLeft_comp,
    whisker_exchange_assoc]

omit [MonoidalPreadditive C] [SymmetricCategory C] in
/-- `A ⊗ A ⟶ (A ⊗ B) ⊕ (B ⊗ A) ⟶ B ⊗ B` is a complex. -/
@[reassoc]
theorem biprodLift_comp_biprodDesc (S : ShortComplex C) :
    biprod.lift (S.X₁ ◁ S.f) (-(S.f ▷ S.X₁)) ≫ biprod.desc (S.f ▷ S.X₂) (S.X₂ ◁ S.f) = 0 := by
  simp [whisker_exchange]

variable {S : ShortComplex C} (hR : ∀ X : C, (S.map (tensorRight X)).ShortExact)

include hR

/-- The kernel of `p ⊗ p` is the image of `(A ⊗ B) ⊕ (B ⊗ A)`: exactness of
`(A ⊗ B) ⊕ (B ⊗ A) ⟶ B ⊗ B ⟶ C ⊗ C`. -/
theorem exact_biprodDesc_tensorHom :
    (ShortComplex.mk (biprod.desc (S.f ▷ S.X₂) (S.X₂ ◁ S.f)) (S.g ⊗ₘ S.g)
      (biprodDesc_comp_tensorHom S)).Exact := by
  have hL := shortExact_map_tensorLeft hR
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x hx
  dsimp at x hx
  have hx' : (x ≫ S.g ▷ S.X₂) ≫ S.X₃ ◁ S.g = 0 := by rw [Category.assoc, ← tensorHom_def, hx]
  obtain ⟨T₁, π₁, hπ₁, y, hy⟩ := (hL S.X₃).exact.exact_up_to_refinements (x ≫ S.g ▷ S.X₂) hx'
  have : Epi (S.g ▷ S.X₁) := (hR S.X₁).epi_g
  obtain ⟨T₂, π₂, hπ₂, z, hz⟩ := surjective_up_to_refinements_of_epi (S.g ▷ S.X₁) y
  dsimp at hy hz
  have hw : (π₂ ≫ π₁ ≫ x - z ≫ S.X₂ ◁ S.f) ≫ S.g ▷ S.X₂ = 0 := by
    simp only [Preadditive.sub_comp, Category.assoc]
    rw [hy, reassoc_of% hz, whisker_exchange, sub_self]
  obtain ⟨T₃, π₃, hπ₃, w, hw'⟩ := (hR S.X₂).exact.exact_up_to_refinements _ hw
  dsimp at hw'
  refine ⟨T₃, π₃ ≫ π₂ ≫ π₁, inferInstance, biprod.lift w (π₃ ≫ z), ?_⟩
  dsimp
  rw [biprod.lift_desc, ← hw']
  simp only [Preadditive.comp_sub, Category.assoc, sub_add_cancel]

/-- The kernel of `(A ⊗ B) ⊕ (B ⊗ A) ⟶ B ⊗ B` is `A ⊗ A`, embedded by `(A ◁ i, -(i ▷ A))`. -/
theorem exact_biprodLift_biprodDesc :
    (ShortComplex.mk (biprod.lift (S.X₁ ◁ S.f) (-(S.f ▷ S.X₁)))
      (biprod.desc (S.f ▷ S.X₂) (S.X₂ ◁ S.f)) (biprodLift_comp_biprodDesc S)).Exact := by
  have hL := shortExact_map_tensorLeft hR
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T m hm
  dsimp at m hm
  have hsum : (m ≫ biprod.fst) ≫ S.f ▷ S.X₂ + (m ≫ biprod.snd) ≫ S.X₂ ◁ S.f = 0 := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, ← biprod.desc_eq, hm]
  have hw : (m ≫ biprod.fst ≫ S.X₁ ◁ S.g) ≫ S.f ▷ S.X₃ = 0 := by
    have h := congrArg (· ≫ S.X₂ ◁ S.g) hsum
    simp only [Preadditive.add_comp, Category.assoc, zero_comp, ← whiskerLeft_comp, S.zero,
      MonoidalPreadditive.whiskerLeft_zero, comp_zero, add_zero] at h
    rw [Category.assoc, Category.assoc, whisker_exchange, ← h]
  have : Mono (S.f ▷ S.X₃) := (hR S.X₃).mono_f
  have hw₀ : (m ≫ biprod.fst) ≫ S.X₁ ◁ S.g = 0 := by
    rw [← cancel_mono (S.f ▷ S.X₃), zero_comp]
    simpa [Category.assoc] using hw
  obtain ⟨T₁, π, hπ, t, ht⟩ := (hL S.X₁).exact.exact_up_to_refinements _ hw₀
  dsimp at ht
  refine ⟨T₁, π, hπ, t, ?_⟩
  dsimp
  have : Mono (S.X₂ ◁ S.f) := (hL S.X₂).mono_f
  apply biprod.hom_ext
  · simpa using ht
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← cancel_mono (S.X₂ ◁ S.f)]
    have h := congrArg (π ≫ ·) hsum
    simp only [Preadditive.comp_add, comp_zero, Category.assoc] at h
    simp only [Category.assoc]
    rw [eq_neg_of_add_eq_zero_right h, reassoc_of% ht]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, whisker_exchange]

/-- `p ⊗ p : B ⊗ B ⟶ C ⊗ C` is an epimorphism. -/
private theorem epi_tensorHom_g : Epi (S.g ⊗ₘ S.g) := by
  have : Epi (S.g ▷ S.X₂) := (hR S.X₂).epi_g
  have : Epi (S.X₃ ◁ S.g) := (shortExact_map_tensorLeft hR S.X₃).epi_g
  rw [tensorHom_def]
  infer_instance

/-- The sequence `0 → A ⊗ A → (A ⊗ B) ⊕ (B ⊗ A) → ker (p ⊗ p) → 0` is short exact. -/
private theorem shortExact_biprodLift_kernelLift :
    (ShortComplex.mk (biprod.lift (S.X₁ ◁ S.f) (-(S.f ▷ S.X₁)))
      (kernel.lift (S.g ⊗ₘ S.g) (biprod.desc (S.f ▷ S.X₂) (S.X₂ ◁ S.f))
        (biprodDesc_comp_tensorHom S)) (by
          rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, zero_comp]
          exact biprodLift_comp_biprodDesc S)).ShortExact := by
  have : Mono (S.X₁ ◁ S.f) := (shortExact_map_tensorLeft hR S.X₁).mono_f
  have hmono : Mono (biprod.lift (S.X₁ ◁ S.f) (-(S.f ▷ S.X₁))) :=
    mono_of_mono_fac (biprod.lift_fst _ _)
  have hepi := (ShortComplex.exact_iff_epi_kernel_lift _).1 (exact_biprodDesc_tensorHom hR)
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₂ := ShortComplex.mk _ _ (biprodLift_comp_biprodDesc S))
    (ShortComplex.Hom.mk (𝟙 (S.X₁ ⊗ S.X₁)) (𝟙 (S.X₁ ⊗ S.X₂ ⊞ S.X₂ ⊗ S.X₁))
      (kernel.ι (S.g ⊗ₘ S.g)) ?_ ?_)).2 (exact_biprodLift_biprodDesc hR) <;> simp

variable {G : Type*} [AddCommGroup G] [∀ X : C, IsIso ((2 : ℤ) • 𝟙 X)]

/-- **The trace of the switch on a tensor square is additive along a short exact sequence which
stays short exact after tensoring with any object.** For `0 → A → B → C → 0` this is
`tr(β | B ⊗ B) = tr(β | A ⊗ A) + tr(β | C ⊗ C)`, the argument of [Stacks, Tag 0FEJ]: the
kernel `F` of `p ⊗ p` sits in the equivariant short exact sequences
`0 → F → B ⊗ B → C ⊗ C → 0` and `0 → A ⊗ A → (A ⊗ B) ⊕ (B ⊗ A) → F → 0`, the switch acting on
`A ⊗ A` with a sign in the second; the trace on the middle term of the second vanishes since the
switch exchanges its two summands. -/
theorem switchTrace_tensorSquare (F : ExactClass C G)
    (h₁₁ : F.P (S.X₁ ⊗ S.X₁)) (h₂₂ : F.P (S.X₂ ⊗ S.X₂)) (h₃₃ : F.P (S.X₃ ⊗ S.X₃))
    (h₁₂ : F.P (S.X₁ ⊗ S.X₂)) (h₂₁ : F.P (S.X₂ ⊗ S.X₁)) :
    switchTrace F (β_ S.X₂ S.X₂).hom =
      switchTrace F (β_ S.X₁ S.X₁).hom + switchTrace F (β_ S.X₃ S.X₃).hom := by
  let Sβ := ShortComplex.mk (kernel.ι (S.g ⊗ₘ S.g)) (S.g ⊗ₘ S.g) (kernel.condition _)
  have hSβ : Sβ.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
      inferInstance (epi_tensorHom_g hR)
  let τF : kernel (S.g ⊗ₘ S.g) ⟶ kernel (S.g ⊗ₘ S.g) :=
    kernel.map _ _ (β_ S.X₂ S.X₂).hom (β_ S.X₃ S.X₃).hom
      (BraidedCategory.braiding_naturality S.g S.g)
  have hτF : τF ≫ τF = 𝟙 _ := by
    rw [← cancel_mono (kernel.ι _)]
    simp [τF]
  have hPF : F.P (kernel (S.g ⊗ₘ S.g)) := F.of_shortExact₁ Sβ hSβ h₂₂ h₃₃
  have eβ := switchTrace_shortExact F hSβ hτF (SymmetricCategory.symmetry _ _)
    (SymmetricCategory.symmetry _ _) (by simp [Sβ, τF])
    (BraidedCategory.braiding_naturality S.g S.g) hPF h₂₂ h₃₃
  let τM : S.X₁ ⊗ S.X₂ ⊞ S.X₂ ⊗ S.X₁ ⟶ S.X₁ ⊗ S.X₂ ⊞ S.X₂ ⊗ S.X₁ :=
    biprod.lift (biprod.snd ≫ (β_ S.X₂ S.X₁).hom) (biprod.fst ≫ (β_ S.X₁ S.X₂).hom)
  let ψ : S.X₁ ⊗ S.X₂ ⊞ S.X₂ ⊗ S.X₁ ⟶ kernel (S.g ⊗ₘ S.g) :=
    kernel.lift _ (biprod.desc (S.f ▷ S.X₂) (S.X₂ ◁ S.f)) (biprodDesc_comp_tensorHom S)
  let Sα := ShortComplex.mk (biprod.lift (S.X₁ ◁ S.f) (-(S.f ▷ S.X₁))) ψ (by
    rw [← cancel_mono (kernel.ι _), Category.assoc, kernel.lift_ι, zero_comp]
    exact biprodLift_comp_biprodDesc S)
  have hSα : Sα.ShortExact := shortExact_biprodLift_kernelLift hR
  have hτM : τM ≫ τM = 𝟙 _ := by ext <;> simp [τM]
  have hfα : Sα.f ≫ τM = (-(β_ S.X₁ S.X₁).hom) ≫ Sα.f := by
    ext <;> simp [Sα, τM, BraidedCategory.braiding_naturality_left,
      BraidedCategory.braiding_naturality_right]
  have hgα : Sα.g ≫ τF = τM ≫ Sα.g := by
    rw [← cancel_mono (kernel.ι _)]
    ext <;> simp [Sα, ψ, τF, τM, BraidedCategory.braiding_naturality_left,
      BraidedCategory.braiding_naturality_right]
  have eα := switchTrace_shortExact F hSα (by simp; rfl) hτM hτF hfα hgα h₁₁
    (F.of_biprod h₁₂ h₂₁) hPF
  -- the switch exchanges the two summands of `(A ⊗ B) ⊕ (B ⊗ A)`
  have e₀ : switchTrace F τM = 0 :=
    switchTrace_eq_zero_of_anticommute F τM (biprod.map (𝟙 _) (-𝟙 _)) (by ext <;> simp)
      (by ext <;> simp [τM])
  rw [e₀, switchTrace_neg, eq_comm, neg_add_eq_zero] at eα
  rw [eβ, ← eα]

end TensorSquare

end Stacks.SecondAdamsPerfect

end
