module

public import Mathlib.Algebra.GradedMonoid
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower

/-!
# The graded ring of sections of an invertible sheaf

Let `L` be an invertible sheaf of modules on a ringed site. Tag 01CV defines the *associated
graded ring*

  `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})`,

whose multiplication sends `s ∈ Γ(X, L^{⊗ a})` and `t ∈ Γ(X, L^{⊗ b})` to the section of
`L^{⊗ (a + b)}` corresponding to `s ⊗ t` under the multiplication isomorphism
`L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}` of Tag 01CU. This file builds that multiplication and the
part of its ring axioms which is a formal consequence of the monoidal structure: associativity
and the two unit laws; commutativity and additivity are proved in sibling files (see the
implementation notes).

The construction is done twice. First abstractly: in any monoidal category `C` the global
sections of an object `M` are the morphisms `𝟙_ C ⟶ M`, and `Hom(𝟙_ C, -)` carries a
multiplication `Γ(M) × Γ(N) → Γ(M ⊗ N)`, namely `s ⊗ₘ t` precomposed with the inverse of the
left unitor of the unit. A `Stacks.Monoidal.PowerSystem` is then a family `obj : ℕ → C` of
candidate tensor powers of an object, with `obj 0 ≅ 𝟙_ C` and with successor comparisons
`obj n ⊗ gen ≅ obj (n + 1)`; from these the multiplication isomorphisms `μ_{a,b}` are built by
induction on `b`, they are proved associative, and the multiplication of sections inherits
associativity and the unit laws. Second concretely: the integer tensor powers of Tag 01CU, for
non-negative exponents, form such a power system, and the sheaf-level multiplication of global
sections is read off it.

## Main definitions

* `Stacks.Monoidal.sectionTensor`: the product `Γ(M) × Γ(N) → Γ(M ⊗ N)` of global sections in
  a monoidal category.
* `Stacks.Monoidal.PowerSystem`: a family of candidate tensor powers of an object, with the
  identification of the zeroth power with the tensor unit and the successor comparisons.
* `Stacks.Monoidal.PowerSystem.mulIso`: the multiplication isomorphism
  `obj a ⊗ obj b ≅ obj (a + b)`.
* `Stacks.Monoidal.PowerSystem.sectionMul` and `sectionOne`: the graded multiplication of
  global sections, and the unit in degree zero.
* `Stacks.Monoidal.PowerSystem.gradedMonoid`: the resulting `GradedMonoid.GMonoid` structure
  on `n ↦ (𝟙_ C ⟶ obj n)`.
* `Stacks.SheafOfModules.Invertible.tensorPowerSystem`: the non-negative tensor powers of an
  invertible sheaf of modules, as a power system.
* `Stacks.SheafOfModules.Invertible.tensorPowerMulIso`: the multiplication isomorphism
  `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}`, and `tensorSheafPowerMulIso` for the same written with
  the tensor product sheaf of Tag 05NA.
* `Stacks.SheafOfModules.Invertible.sectionMul`, `sectionOne` and `sectionPow`: the
  multiplication `Γ(X, L^{⊗ a}) × Γ(X, L^{⊗ b}) → Γ(X, L^{⊗ (a + b)})` on the sections of
  Mathlib's `SheafOfModules.sections`, the unit section, and powers of a single section.
* `Stacks.SheafOfModules.Invertible.sectionsCongr`: transport of a global section along an
  equality of exponents, which is what the statements of associativity and of the left unit
  law need.
* `Stacks.SheafOfModules.Invertible.sectionsGradedMonoid`: the `GradedMonoid.GMonoid` structure
  on `n ↦ Γ(X, L^{⊗ n})`.

## Main results

* `Stacks.Monoidal.sectionTensor_comp_associator`, `sectionTensor_comp_leftUnitor`,
  `sectionTensor_comp_rightUnitor` and `sectionTensor_comp_braiding`: the product of global
  sections is associative, unital and commutative, up to the structural isomorphisms of the
  monoidal category. The last of these holds in any braided category because the braiding of
  the tensor unit with itself is the identity.
* `Stacks.Monoidal.PowerSystem.mulIso_assoc`: **the multiplication isomorphisms of a power
  system are associative.** This is the associativity constraint of Tag 01CU; it is a formal
  consequence of the pentagon and the naturality of the structural isomorphisms.
* `Stacks.Monoidal.PowerSystem.mulIso_zeroLeft`: in degree `(0, b)` the multiplication
  isomorphism is the left unitor.
* `Stacks.Monoidal.PowerSystem.sectionMul_assoc`, `sectionMul_sectionOne` and
  `sectionOne_sectionMul`: the graded multiplication of sections is associative with two-sided
  unit the degree-zero section `1`.
* `Stacks.Monoidal.PowerSystem.sectionMul_comm`: the graded multiplication is commutative
  *given* the commutativity constraint of Tag 01CU for the multiplication isomorphisms.
* `Stacks.SheafOfModules.Invertible.tensorPowerMulIso_assoc`: associativity of the
  multiplication isomorphisms of the tensor powers of an invertible sheaf of modules.
* `Stacks.SheafOfModules.Invertible.sectionMul_assoc`,
  `Stacks.SheafOfModules.Invertible.sectionMul_sectionOne` and
  `Stacks.SheafOfModules.Invertible.sectionOne_sectionMul`: the same three identities for the
  sections of the tensor powers of an invertible sheaf of modules.

## Implementation notes

The two remaining ring axioms are proved in sibling files.

1. *Commutativity.* `s * t` and `t * s` differ by the scalar comparing `μ_{a,b}` with
   `β ≫ μ_{b,a}`, which is the commutativity constraint whose formulation Tag 01CU omits. It
   is **not** a formal consequence of the symmetric monoidal axioms: in a general symmetric
   monoidal category an invertible object only satisfies `β ≫ β = 𝟙`, and the odd line in
   super vector spaces has `β = -𝟙`. `sectionMul_comm` is therefore stated with the constraint
   as an explicit hypothesis. For the tensor powers of an invertible sheaf the constraint is
   `Stacks.SheafOfModules.Invertible.tensorPowerMulIso_comm` in `Commutativity.lean`.
2. *Additivity.* Passing from the graded *monoid* to a graded *ring* on
   `⨁_n Γ(X, L^{⊗ n})` — a `DirectSum.GSemiring`, i.e. the distributive laws — needs the
   multiplication to be biadditive, which is `CategoryTheory.MonoidalPreadditive` for the
   tensor product of sheaves of modules, `Stacks.SheafOfModules.monoidalPreadditive`. The
   graded ring is `Stacks.Monoidal.PowerSystem.gradedRing` and
   `Stacks.SheafOfModules.Invertible.homGradedRing`.

Everything in *this file* is independent of both, so the multiplication, its associativity, its
unit laws and the resulting `GradedMonoid.GMonoid` structure are unconditional and need no
preadditivity; the graded ring is assembled in `Ring.lean` and made commutative in
`Commutativity.lean`, where `Stacks.SheafOfModules.Invertible.homGradedCommRingOfInvertible`
carries `@[stacks 01CV "associated graded ring"]`.

The grading is by `ℕ`, as in Tag 01CV (`⨁_{n ≥ 0}`), and this is also what makes the
construction cheap: in `ℕ` the identities `a + 0 = a` and `a + (b + 1) = (a + b) + 1` hold by
`rfl`, so the recursion defining `mulIso` and the statement of the unit law in degree
`(a, 0)` need no transport along an equality of exponents. The `ℤ`-graded module
`Γ_*(X, L, F)` of Tag 01CV is not built here; the same recursion gives the multiplication
`Γ(L^{⊗ a}) × Γ(L^{⊗ b}) → Γ(L^{⊗ (a + b)})` for `a : ℤ` and `b : ℕ`, at the cost of a
`tensorPowerReindex` at every step.

The tensor powers are `Stacks.SheafOfModules.Invertible.tensorPower`, keyed on
`AlgebraicGeometry.SheafOfModules.IsInvertible`, and the monoidal structure on sheaves of
modules is `Stacks.SheafOfModules.monoidalCategory`, activated here as a local instance as
that file prescribes. The two are related by `Stacks.SheafOfModules.tensorObjIso`, which
identifies the monoidal tensor product with the tensor product sheaf
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` that the successor comparison
`tensorPowerSuccIso` is stated for.

`tensorPowerSystem` is marked `@[implicit_reducible]`: the generic lemmas about a power system
speak of `(tensorPowerSystem O hO L).obj n` while the sheaf-level statements speak of
`tensorPower O hO L (n : ℤ)`, and without reducibility `rw` rejects every goal mixing the two
with "target expression is not type-correct under the `implicit` transparency level".

The multiplicativity of nonvanishing loci, `X_{s t} = X_s ∩ X_t`, is not here: it is a
statement about germs, not about the monoidal structure, and it needs the local description of
the tensor product of invertible sheaves.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe v u w

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Multiplication of global sections in a monoidal category -/

/-- The product of two global sections: the tensor product of the two morphisms out of the
tensor unit, precomposed with the inverse of the left unitor of the unit. -/
def sectionTensor {M N : C} (s : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N) : 𝟙_ C ⟶ M ⊗ N :=
  (λ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t)

/-- Postcomposing a product of global sections with a tensor product of morphisms is the product
of the postcomposed sections. -/
@[reassoc (attr := simp)]
theorem sectionTensor_comp_tensorHom {M N M' N' : C} (s : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N)
    (f : M ⟶ M') (g : N ⟶ N') :
    sectionTensor s t ≫ (f ⊗ₘ g) = sectionTensor (s ≫ f) (t ≫ g) := by
  simp [sectionTensor]

/-- Postcomposing a product of global sections with a left whiskering postcomposes the second
section. -/
@[reassoc (attr := simp)]
theorem sectionTensor_comp_whiskerLeft {M N N' : C} (s : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N)
    (g : N ⟶ N') : sectionTensor s t ≫ (M ◁ g) = sectionTensor s (t ≫ g) := by
  rw [← id_tensorHom, sectionTensor_comp_tensorHom, Category.comp_id]

/-- Postcomposing a product of global sections with a right whiskering postcomposes the first
section. -/
@[reassoc (attr := simp)]
theorem sectionTensor_comp_whiskerRight {M N M' : C} (s : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N)
    (f : M ⟶ M') : sectionTensor s t ≫ (f ▷ N) = sectionTensor (s ≫ f) t := by
  rw [← tensorHom_id, sectionTensor_comp_tensorHom, Category.comp_id]

/-- The identity of the tensor unit is a left unit for the product of global sections. -/
@[reassoc]
theorem sectionTensor_comp_leftUnitor {N : C} (t : 𝟙_ C ⟶ N) :
    sectionTensor (𝟙 (𝟙_ C)) t ≫ (λ_ N).hom = t := by
  simp [sectionTensor, id_tensorHom]

/-- The identity of the tensor unit is a right unit for the product of global sections. -/
@[reassoc]
theorem sectionTensor_comp_rightUnitor {M : C} (s : 𝟙_ C ⟶ M) :
    sectionTensor s (𝟙 (𝟙_ C)) ≫ (ρ_ M).hom = s := by
  simp [sectionTensor, tensorHom_id, ← unitors_equal]

/-- The product of global sections is associative, up to the associator. -/
@[reassoc]
theorem sectionTensor_comp_associator {M N P : C} (s : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N)
    (u : 𝟙_ C ⟶ P) :
    sectionTensor (sectionTensor s t) u ≫ (α_ M N P).hom
      = sectionTensor s (sectionTensor t u) := by
  have hcoh : (λ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).inv ▷ 𝟙_ C ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom
      = (λ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ (λ_ (𝟙_ C)).inv := by
    monoidal_coherence
  simp only [sectionTensor, Category.assoc, ← whiskerRight_comp_tensorHom,
    ← whiskerLeft_comp_tensorHom]
  rw [associator_naturality, reassoc_of% hcoh]

/-- The product of global sections is commutative, up to the braiding. This needs no hypothesis
beyond braidedness: the braiding of the tensor unit with itself is the identity. -/
@[reassoc]
theorem sectionTensor_comp_braiding [BraidedCategory C] {M N : C}
    (s : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ N) :
    sectionTensor s t ≫ (β_ M N).hom = sectionTensor t s := by
  simp only [sectionTensor, Category.assoc, BraidedCategory.braiding_naturality]
  rw [← Category.assoc]
  congr 1
  simp [← unitors_equal]

/-! ### Coherence lemmas for the multiplication of tensor powers -/

/-- A right unitor may be read as a left unitor through an isomorphism onto the tensor unit. -/
theorem unitor_comp_iso_unit {E : C} (e : E ≅ 𝟙_ C) :
    (E ◁ e.hom) ≫ (ρ_ E).hom = (e.hom ▷ E) ≫ (λ_ E).hom := by
  rw [← cancel_mono e.hom, Category.assoc, Category.assoc, ← rightUnitor_naturality,
    ← leftUnitor_naturality, ← Category.assoc, ← Category.assoc, whisker_exchange,
    unitors_equal]

/-- The degree-zero case of associativity of the multiplication of tensor powers, isolated
from the indices. -/
theorem mulIso_assoc_aux_zero {A B D E : C} (f : A ⊗ B ⟶ D) (e : E ≅ 𝟙_ C) :
    (f ▷ E) ≫ (D ◁ e.hom) ≫ (ρ_ D).hom
      = (α_ A B E).hom ≫ (A ◁ ((B ◁ e.hom) ≫ (ρ_ B).hom)) ≫ f := by
  rw [← whisker_exchange_assoc, rightUnitor_naturality]
  simp

/-- The inductive step of associativity of the multiplication of tensor powers, isolated from
the indices: only the naturality of the structural isomorphisms and the pentagon are used. -/
theorem mulIso_assoc_aux_succ {A B D E G F Pc Pc1 E1 F1 G1 Lg : C}
    (f : A ⊗ B ⟶ D) (g : D ⊗ Pc ⟶ E) (h : B ⊗ Pc ⟶ F) (k : A ⊗ F ⟶ G)
    {q : G ⟶ E} {q1 : G1 ⟶ E1}
    (σc : Pc ⊗ Lg ≅ Pc1) (σE : E ⊗ Lg ≅ E1) (σF : F ⊗ Lg ≅ F1) (σG : G ⊗ Lg ≅ G1)
    (hq : (q ▷ Lg) ≫ σE.hom = σG.hom ≫ q1)
    (ih : (f ▷ Pc) ≫ g = (α_ A B Pc).hom ≫ (A ◁ h) ≫ k ≫ q) :
    (f ▷ Pc1) ≫ ((D ◁ σc.inv) ≫ (α_ D Pc Lg).inv ≫ (g ▷ Lg) ≫ σE.hom)
      = (α_ A B Pc1).hom ≫
          (A ◁ ((B ◁ σc.inv) ≫ (α_ B Pc Lg).inv ≫ (h ▷ Lg) ≫ σF.hom)) ≫
          ((A ◁ σF.inv) ≫ (α_ A F Lg).inv ≫ (k ▷ Lg) ≫ σG.hom) ≫ q1 := by
  have hcoh : (α_ (A ⊗ B) Pc Lg).inv ≫ (α_ A B Pc).hom ▷ Lg
      = (α_ A B (Pc ⊗ Lg)).hom ≫ A ◁ (α_ B Pc Lg).inv ≫ (α_ A (B ⊗ Pc) Lg).inv := by
    monoidal_coherence
  simp only [Category.assoc]
  rw [← hq]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, ih]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← associator_naturality_right_assoc,
    reassoc_of% hcoh]

/-! ### Systems of tensor powers -/

/-- A *power system* in a monoidal category: an object `gen`, a family `obj n` of candidate
`n`-th tensor powers of it, the identification of the zeroth with the tensor unit, and the
successor comparisons `obj n ⊗ gen ≅ obj (n + 1)`. -/
structure PowerSystem (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  /-- The object whose tensor powers are being described. -/
  gen : C
  /-- The `n`-th tensor power. -/
  obj : ℕ → C
  /-- The zeroth tensor power is the tensor unit. -/
  objZeroIso : obj 0 ≅ 𝟙_ C
  /-- One more tensor factor. -/
  succIso : ∀ n, obj n ⊗ gen ≅ obj (n + 1)

namespace PowerSystem

variable (S : PowerSystem C)

/-- The multiplication isomorphism `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}`, by induction on `b`:
the right unitor in degree `(a, 0)`, and otherwise one more tensor factor split off by the
successor comparison and reassociated. -/
noncomputable def mulIso (a : ℕ) : (b : ℕ) → S.obj a ⊗ S.obj b ≅ S.obj (a + b)
  | 0 => whiskerLeftIso _ S.objZeroIso ≪≫ ρ_ _
  | b + 1 => whiskerLeftIso _ (S.succIso b).symm ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso (mulIso a b) S.gen ≪≫ S.succIso (a + b)

/-- In degree `(a, 0)` the multiplication isomorphism is the right unitor, after identifying
the zeroth power with the tensor unit. -/
theorem mulIso_zero (a : ℕ) :
    S.mulIso a 0 = whiskerLeftIso _ S.objZeroIso ≪≫ ρ_ _ := rfl

/-- In degree `(a, b + 1)` the multiplication isomorphism splits off one tensor factor by the
successor comparison, reassociates, and applies the multiplication isomorphism in degree
`(a, b)`. -/
theorem mulIso_succ (a b : ℕ) :
    S.mulIso a (b + 1) = whiskerLeftIso _ (S.succIso b).symm ≪≫ (α_ _ _ _).symm ≪≫
      whiskerRightIso (S.mulIso a b) S.gen ≪≫ S.succIso (a + b) := rfl

/-- Transport along an equality of exponents commutes with the successor comparison. -/
theorem eqToHom_whiskerRight_succIso {m n : ℕ} (e : m = n) :
    (eqToHom (congrArg S.obj e) ▷ S.gen) ≫ (S.succIso n).hom
      = (S.succIso m).hom ≫ eqToHom (congrArg S.obj (congrArg (· + 1) e)) := by
  subst e; simp

/-- **The multiplication isomorphisms of a power system are associative**: this is the
associativity constraint of Tag 01CU, for non-negative exponents. -/
theorem mulIso_assoc (a b : ℕ) : ∀ (c : ℕ),
    ((S.mulIso a b).hom ▷ S.obj c) ≫ (S.mulIso (a + b) c).hom
      = (α_ _ _ _).hom ≫ (S.obj a ◁ (S.mulIso b c).hom) ≫ (S.mulIso a (b + c)).hom
          ≫ eqToHom (congrArg S.obj (Nat.add_assoc a b c).symm)
  | 0 => by
      simp only [mulIso_zero, Iso.trans_hom, whiskerLeftIso_hom, eqToHom_refl, Category.comp_id]
      exact mulIso_assoc_aux_zero (S.mulIso a b).hom S.objZeroIso
  | c + 1 =>
      mulIso_assoc_aux_succ (S.mulIso a b).hom (S.mulIso (a + b) c).hom (S.mulIso b c).hom
        (S.mulIso a (b + c)).hom (S.succIso c) (S.succIso (a + b + c))
        (S.succIso (b + c)) (S.succIso (a + (b + c)))
        (S.eqToHom_whiskerRight_succIso (Nat.add_assoc a b c).symm)
        (mulIso_assoc a b c)

/-- The multiplication isomorphism in degree `(0, b)` is the left unitor. -/
theorem mulIso_zeroLeft : ∀ (b : ℕ),
    (S.mulIso 0 b).hom = (S.objZeroIso.hom ▷ S.obj b) ≫ (λ_ (S.obj b)).hom
        ≫ eqToHom (congrArg S.obj (Nat.zero_add b).symm)
  | 0 => by
      simp only [mulIso_zero, Iso.trans_hom, whiskerLeftIso_hom, eqToHom_refl, Category.comp_id]
      exact unitor_comp_iso_unit S.objZeroIso
  | b + 1 => by
      rw [mulIso_succ]
      simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom]
      rw [mulIso_zeroLeft b]
      simp only [comp_whiskerRight, Category.assoc]
      rw [S.eqToHom_whiskerRight_succIso (Nat.zero_add b).symm,
        ← associator_inv_naturality_left_assoc, ← leftUnitor_tensor_hom_assoc,
        whisker_exchange_assoc, leftUnitor_naturality_assoc]
      simp only [Iso.inv_hom_id_assoc]

/-! ### The graded multiplication of global sections -/

/-- The product of a global section of `L^{⊗ a}` and a global section of `L^{⊗ b}`, as a
global section of `L^{⊗ (a + b)}`. -/
noncomputable def sectionMul {a b : ℕ} (s : 𝟙_ C ⟶ S.obj a) (t : 𝟙_ C ⟶ S.obj b) :
    𝟙_ C ⟶ S.obj (a + b) :=
  sectionTensor s t ≫ (S.mulIso a b).hom

/-- The unit global section, in degree zero. -/
noncomputable def sectionOne : 𝟙_ C ⟶ S.obj 0 := S.objZeroIso.inv

/-- The unit section is a right unit for the graded multiplication of global sections. -/
@[simp]
theorem sectionMul_sectionOne {a : ℕ} (s : 𝟙_ C ⟶ S.obj a) :
    S.sectionMul s S.sectionOne = s := by
  rw [sectionMul, sectionOne, mulIso_zero]
  simp only [Iso.trans_hom, whiskerLeftIso_hom, sectionTensor_comp_whiskerLeft_assoc,
    Iso.inv_hom_id]
  exact sectionTensor_comp_rightUnitor s

/-- The unit section is a left unit for the graded multiplication of global sections, up to
transport along `0 + b = b`. -/
theorem sectionOne_sectionMul {b : ℕ} (t : 𝟙_ C ⟶ S.obj b) :
    S.sectionMul S.sectionOne t = t ≫ eqToHom (congrArg S.obj (Nat.zero_add b).symm) := by
  rw [sectionMul, mulIso_zeroLeft, sectionOne, sectionTensor_comp_whiskerRight_assoc,
    Iso.inv_hom_id, sectionTensor_comp_leftUnitor_assoc]

/-- **The graded multiplication of global sections is associative.** -/
theorem sectionMul_assoc {a b c : ℕ} (s : 𝟙_ C ⟶ S.obj a) (t : 𝟙_ C ⟶ S.obj b)
    (u : 𝟙_ C ⟶ S.obj c) :
    S.sectionMul (S.sectionMul s t) u
      = S.sectionMul s (S.sectionMul t u)
          ≫ eqToHom (congrArg S.obj (Nat.add_assoc a b c).symm) := by
  rw [sectionMul, sectionMul, ← sectionTensor_comp_whiskerRight, Category.assoc,
    mulIso_assoc, sectionTensor_comp_associator_assoc,
    sectionTensor_comp_whiskerLeft_assoc, sectionMul, sectionMul, Category.assoc]

/-- The graded multiplication of global sections is commutative, *given* the commutativity
constraint of Tag 01CU for the multiplication isomorphisms. -/
theorem sectionMul_comm [BraidedCategory C]
    (hβ : ∀ a b : ℕ, (β_ (S.obj a) (S.obj b)).hom ≫ (S.mulIso b a).hom
      = (S.mulIso a b).hom ≫ eqToHom (congrArg S.obj (Nat.add_comm a b)))
    {a b : ℕ} (s : 𝟙_ C ⟶ S.obj a) (t : 𝟙_ C ⟶ S.obj b) :
    S.sectionMul s t = S.sectionMul t s ≫ eqToHom (congrArg S.obj (Nat.add_comm b a)) := by
  rw [sectionMul, sectionMul, ← sectionTensor_comp_braiding t s, Category.assoc, hβ b a,
    Category.assoc]

/-- **The global sections of the tensor powers form an `ℕ`-graded monoid** under the
multiplication of sections. This is the multiplicative half of Tag 01CV, and needs nothing
beyond the monoidal structure: no additivity, and no commutativity constraint. -/
@[instance_reducible]
noncomputable def gradedMonoid :
    GradedMonoid.GMonoid (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := by
  let : GradedMonoid.GOne (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := ⟨S.sectionOne⟩
  let : GradedMonoid.GMul (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := ⟨S.sectionMul⟩
  exact {
    one := S.sectionOne
    mul := S.sectionMul
    one_mul := fun ⟨n, a⟩ => Sigma.ext (zero_add n) <| by
      change HEq (S.sectionMul S.sectionOne a) a
      rw [S.sectionOne_sectionMul]
      exact comp_eqToHom_heq _ _
    mul_one := fun ⟨n, a⟩ => Sigma.ext (add_zero n) (heq_of_eq (S.sectionMul_sectionOne a))
    mul_assoc := fun ⟨n, a⟩ ⟨m, b⟩ ⟨k, c⟩ => Sigma.ext (add_assoc n m k) <| by
      change HEq (S.sectionMul (S.sectionMul a b) c) (S.sectionMul a (S.sectionMul b c))
      rw [S.sectionMul_assoc]
      exact comp_eqToHom_heq _ _ }

end PowerSystem

end Stacks.Monoidal

namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.braidedCategory Stacks.SheafOfModules.symmetricCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L]

/-- The non-negative integer tensor powers of an invertible sheaf of modules, as a power system
for the tensor product of sheaves of modules. The zeroth power is the tensor unit on the nose,
and the successor comparison is Tag 01CU's `tensorPowerSuccIso` read through the identification
of the monoidal tensor product with the tensor product sheaf. -/
@[implicit_reducible]
noncomputable def tensorPowerSystem :
    Stacks.Monoidal.PowerSystem
      (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        where
  gen := L
  obj n := tensorPower O hO L (n : ℤ)
  objZeroIso := Iso.refl _
  succIso n := Stacks.SheafOfModules.tensorObjIso O hO _ _ ≪≫ tensorPowerSuccIso O hO L (n : ℤ)

/-- A global section of a tensor power, read as a morphism out of the tensor unit. -/
noncomputable def sectionToHom {n : ℕ} (s : (tensorPower O hO L (n : ℤ)).sections) :
    𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      ⟶ tensorPower O hO L (n : ℤ) :=
  (_root_.SheafOfModules.unitHomEquiv _).symm s

/-- A morphism out of the tensor unit, read as a global section of a tensor power. -/
noncomputable def homToSection {n : ℕ}
    (f : 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
      ⟶ tensorPower O hO L (n : ℤ)) : (tensorPower O hO L (n : ℤ)).sections :=
  _root_.SheafOfModules.unitHomEquiv _ f

/-- Reading a global section as a morphism and back gives the section. -/
@[simp]
theorem homToSection_sectionToHom {n : ℕ} (s : (tensorPower O hO L (n : ℤ)).sections) :
    homToSection O hO L (sectionToHom O hO L s) = s :=
  Equiv.apply_symm_apply _ _

/-- Reading a morphism out of the tensor unit as a global section and back gives the morphism. -/
@[simp]
theorem sectionToHom_homToSection {n : ℕ}
    (f : 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
      ⟶ tensorPower O hO L (n : ℤ)) :
    sectionToHom O hO L (homToSection O hO L f) = f :=
  Equiv.symm_apply_apply _ _

/-- Reading a composite as a global section is applying the second factor to the section. -/
theorem homToSection_comp {m n : ℕ}
    (f : 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
      ⟶ tensorPower O hO L (m : ℤ))
    (p : tensorPower O hO L (m : ℤ) ⟶ tensorPower O hO L (n : ℤ)) :
    homToSection O hO L (f ≫ p) = _root_.SheafOfModules.sectionsMap p (homToSection O hO L f) :=
  rfl

/-- **The multiplication isomorphism `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}`** of Tag 01CU, for
non-negative exponents. -/
noncomputable def tensorPowerMulIso (a b : ℕ) :
    tensorPower O hO L (a : ℤ) ⊗ tensorPower O hO L (b : ℤ)
      ≅ tensorPower O hO L ((a + b : ℕ) : ℤ) :=
  (tensorPowerSystem O hO L).mulIso a b

/-- The multiplication isomorphism written with the tensor product sheaf of Tag 05NA, the form
in which the rest of the development of Tag 01CU is stated. -/
noncomputable def tensorSheafPowerMulIso (a b : ℕ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((tensorPower O hO L (a : ℤ)))).obj ((tensorPower O hO L (b : ℤ))))
      ≅ tensorPower O hO L ((a + b : ℕ) : ℤ) :=
  (Stacks.SheafOfModules.tensorObjIso O hO _ _).symm ≪≫ tensorPowerMulIso O hO L a b

/-- The multiplication isomorphisms are associative. -/
theorem tensorPowerMulIso_assoc (a b c : ℕ) :
    ((tensorPowerMulIso O hO L a b).hom ▷ tensorPower O hO L (c : ℤ))
        ≫ (tensorPowerMulIso O hO L (a + b) c).hom
      = (α_ _ _ _).hom
          ≫ (tensorPower O hO L (a : ℤ) ◁ (tensorPowerMulIso O hO L b c).hom)
          ≫ (tensorPowerMulIso O hO L a (b + c)).hom
          ≫ eqToHom (congrArg (fun k : ℕ => tensorPower O hO L (k : ℤ))
              (Nat.add_assoc a b c).symm) :=
  (tensorPowerSystem O hO L).mulIso_assoc a b c

/-- Transport of a global section along an equality of exponents. -/
noncomputable def sectionsCongr {m n : ℕ} (h : m = n)
    (s : (tensorPower O hO L (m : ℤ)).sections) : (tensorPower O hO L (n : ℤ)).sections :=
  _root_.SheafOfModules.sectionsMap
    (eqToHom (congrArg (fun k : ℕ => tensorPower O hO L (k : ℤ)) h)) s

/-- Transport of a global section along `n = n` is the identity. -/
@[simp]
theorem sectionsCongr_rfl {n : ℕ} (h : n = n)
    (s : (tensorPower O hO L (n : ℤ)).sections) : sectionsCongr O hO L h s = s := by
  rw [sectionsCongr, eqToHom_refl, _root_.SheafOfModules.sectionsMap_id]

/-- **The product of a global section of `L^{⊗ a}` and a global section of `L^{⊗ b}`**, a
global section of `L^{⊗ (a + b)}`. This is the multiplication of Tag 01CV. -/
noncomputable def sectionMul {a b : ℕ}
    (s : (tensorPower O hO L (a : ℤ)).sections) (t : (tensorPower O hO L (b : ℤ)).sections) :
    (tensorPower O hO L ((a + b : ℕ) : ℤ)).sections :=
  homToSection O hO L ((tensorPowerSystem O hO L).sectionMul
    (sectionToHom O hO L s) (sectionToHom O hO L t))

/-- The unit global section of `L^{⊗ 0} = 𝒪_X`. -/
noncomputable def sectionOne : (tensorPower O hO L ((0 : ℕ) : ℤ)).sections :=
  homToSection O hO L (tensorPowerSystem O hO L).sectionOne

/-- The unit section is a right unit for the multiplication of global sections of the tensor
powers. -/
@[simp]
theorem sectionMul_sectionOne {a : ℕ} (s : (tensorPower O hO L (a : ℤ)).sections) :
    sectionMul O hO L s (sectionOne O hO L) = s := by
  rw [sectionMul, sectionOne, sectionToHom_homToSection,
    Stacks.Monoidal.PowerSystem.sectionMul_sectionOne, homToSection_sectionToHom]

/-- The unit section is a left unit for the multiplication of global sections of the tensor
powers, up to transport along `0 + b = b`. -/
theorem sectionOne_sectionMul {b : ℕ} (t : (tensorPower O hO L (b : ℤ)).sections) :
    sectionMul O hO L (sectionOne O hO L) t = sectionsCongr O hO L (Nat.zero_add b).symm t := by
  rw [sectionMul, sectionOne, sectionToHom_homToSection,
    Stacks.Monoidal.PowerSystem.sectionOne_sectionMul, homToSection_comp,
    homToSection_sectionToHom, sectionsCongr]

/-- **The multiplication of global sections of the tensor powers is associative.** -/
theorem sectionMul_assoc {a b c : ℕ} (s : (tensorPower O hO L (a : ℤ)).sections)
    (t : (tensorPower O hO L (b : ℤ)).sections) (u : (tensorPower O hO L (c : ℤ)).sections) :
    sectionMul O hO L (sectionMul O hO L s t) u
      = sectionsCongr O hO L (Nat.add_assoc a b c).symm
          (sectionMul O hO L s (sectionMul O hO L t u)) := by
  rw [sectionMul, sectionMul, sectionMul, sectionMul, sectionToHom_homToSection,
    sectionToHom_homToSection, Stacks.Monoidal.PowerSystem.sectionMul_assoc,
    homToSection_comp, sectionsCongr]

/-- The `k`-th power of a global section of `L^{⊗ n}`, a global section of `L^{⊗ (n * k)}`. -/
noncomputable def sectionPow {n : ℕ} (s : (tensorPower O hO L (n : ℤ)).sections) :
    (k : ℕ) → (tensorPower O hO L ((n * k : ℕ) : ℤ)).sections
  | 0 => sectionOne O hO L
  | k + 1 => sectionMul O hO L (sectionPow s k) s

/-- The zeroth power of a global section is the unit section. -/
theorem sectionPow_zero {n : ℕ} (s : (tensorPower O hO L (n : ℤ)).sections) :
    sectionPow O hO L s 0 = sectionOne O hO L := rfl

/-- The `(k + 1)`-st power of a global section is its `k`-th power times the section. -/
theorem sectionPow_succ {n : ℕ} (s : (tensorPower O hO L (n : ℤ)).sections) (k : ℕ) :
    sectionPow O hO L s (k + 1) = sectionMul O hO L (sectionPow O hO L s k) s := rfl

/-- Transport along an equality of exponents does not change a section. -/
theorem sectionsCongr_heq {m n : ℕ} (h : m = n)
    (s : (tensorPower O hO L (m : ℤ)).sections) : HEq (sectionsCongr O hO L h s) s := by
  cases h
  exact heq_of_eq (sectionsCongr_rfl O hO L _ s)

/-- **The global sections of the tensor powers of an invertible sheaf of modules form an
`ℕ`-graded monoid** under the multiplication of sections: the multiplicative half of Tag
01CV. -/
@[instance_reducible]
noncomputable def sectionsGradedMonoid :
    GradedMonoid.GMonoid (fun n : ℕ => (tensorPower O hO L (n : ℤ)).sections) := by
  let : GradedMonoid.GOne (fun n : ℕ => (tensorPower O hO L (n : ℤ)).sections) :=
    ⟨sectionOne O hO L⟩
  let : GradedMonoid.GMul (fun n : ℕ => (tensorPower O hO L (n : ℤ)).sections) :=
    ⟨fun {_ _} => sectionMul O hO L⟩
  exact {
    one := sectionOne O hO L
    mul := fun {_ _} => sectionMul O hO L
    one_mul := fun ⟨n, a⟩ => Sigma.ext (zero_add n) <| by
      change HEq (sectionMul O hO L (sectionOne O hO L) a) a
      rw [sectionOne_sectionMul]
      exact sectionsCongr_heq O hO L _ a
    mul_one := fun ⟨n, a⟩ => Sigma.ext (add_zero n) (heq_of_eq (sectionMul_sectionOne O hO L a))
    mul_assoc := fun ⟨n, a⟩ ⟨m, b⟩ ⟨k, c⟩ => Sigma.ext (add_assoc n m k) <| by
      change HEq (sectionMul O hO L (sectionMul O hO L a b) c)
        (sectionMul O hO L a (sectionMul O hO L b c))
      rw [sectionMul_assoc]
      exact sectionsCongr_heq O hO L _ _ }

/-- The multiplication of global sections is commutative, *given* the commutativity constraint
of Tag 01CU for the multiplication isomorphisms. -/
theorem sectionMul_comm
    (hβ : ∀ a b : ℕ, (β_ (tensorPower O hO L (a : ℤ)) (tensorPower O hO L (b : ℤ))).hom
        ≫ (tensorPowerMulIso O hO L b a).hom
      = (tensorPowerMulIso O hO L a b).hom
        ≫ eqToHom (congrArg (fun k : ℕ => tensorPower O hO L (k : ℤ)) (Nat.add_comm a b)))
    {a b : ℕ} (s : (tensorPower O hO L (a : ℤ)).sections)
    (t : (tensorPower O hO L (b : ℤ)).sections) :
    sectionMul O hO L s t = sectionsCongr O hO L (Nat.add_comm b a) (sectionMul O hO L t s) := by
  rw [sectionMul, sectionMul,
    Stacks.Monoidal.PowerSystem.sectionMul_comm (tensorPowerSystem O hO L) hβ,
    homToSection_comp, sectionsCongr]

end Stacks.SheafOfModules.Invertible

end
