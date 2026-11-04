module

public import Mathlib.Algebra.Module.GradedModule
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Ring

/-!
# Graded modules over the section ring of a power system

Let `C` be a monoidal category and `S : Stacks.Monoidal.PowerSystem C` a system of tensor
powers of an object `S.gen`. A *module system* over `S` is a family `M.obj : ℤ → C` together
with comparisons `S.gen ⊗ M.obj n ≅ M.obj (n + 1)`: one more tensor factor of the generator
raises the index by one. The global sections of such a family, `⨁_{n ∈ ℤ} (𝟙_ C ⟶ M.obj n)`,
then form a graded module over the graded section ring `⨁_{n ≥ 0} (𝟙_ C ⟶ S.obj n)` of `S`.

The module is graded by `ℤ` while the ring is graded by `ℕ`, so the action raises the degree by
an amount coming from a different index type. The degree map is the `VAdd ℕ ℤ` of
`Stacks.Monoidal.natVAddInt`, which sends `a +ᵥ b` to `b + a`.

## Main definitions

* `Stacks.Monoidal.natShift`: addition of a natural number to an integer, written as a
  recursion on the natural number, and the `VAdd ℕ ℤ` instance it supplies.
* `Stacks.Monoidal.ModuleSystem`: a family of candidate twists of an object by the powers of
  `S.gen`, with the successor comparisons.
* `Stacks.Monoidal.ModuleSystem.actIso`: the action isomorphism
  `S.obj a ⊗ M.obj b ≅ M.obj (a +ᵥ b)`, built by recursion on `a`.
* `Stacks.Monoidal.ModuleSystem.sectionSMul`: the induced action
  `(𝟙_ C ⟶ S.obj a) → (𝟙_ C ⟶ M.obj b) → (𝟙_ C ⟶ M.obj (a +ᵥ b))` on global sections.
* `Stacks.Monoidal.ModuleSystem.gmodule`: the resulting `DirectSum.Gmodule` structure, whose
  homogeneous action is `sectionSMul` by construction, and
  `Stacks.Monoidal.ModuleSystem.module` the `Module` structure on the direct sums it produces.
  `DirectSum.Gmodule.of_smul_of` then computes the action on homogeneous elements.

## Main results

* `Stacks.Monoidal.ModuleSystem.actIso_assoc`: **the action isomorphisms are associative for
  the multiplication isomorphisms of the power system.** Like
  `Stacks.Monoidal.PowerSystem.mulIso_assoc` this is a formal consequence of the pentagon and
  the naturality of the structural isomorphisms.
* `Stacks.Monoidal.ModuleSystem.sectionOne_sectionSMul` and
  `Stacks.Monoidal.ModuleSystem.sectionSMul_assoc`: the action of global sections is unital and
  associative.

## Implementation notes

The degree arithmetic is kept definitional by taking the `VAdd ℕ ℤ` to be
`Stacks.Monoidal.natShift`, which is `fun a b => b + a` *written as a recursion on* `a`. Its
two defining equations `0 +ᵥ b = b` and `(a + 1) +ᵥ b = a +ᵥ (b + 1)` hold by `rfl`, so
`actIso` needs no transport along an equality of degrees and the unit law of the action is an
equation on the nose. Only `Stacks.Monoidal.natVAdd_add` is a propositional equality, which is
why associativity — exactly as for `Stacks.Monoidal.PowerSystem.mulIso_assoc` — carries one
`eqToHom`. The ordinary formula for the degree is `Stacks.Monoidal.natVAdd_eq`.

The action is built from the *left* comparison `S.gen ⊗ M.obj n ≅ M.obj (n + 1)` rather than
the right one. With the right comparison the recursion produces a right action, and turning a
right action into a left one would need the multiplication of the section ring to be
commutative — which is the commutativity constraint of Tag 01CU, and is not available. With
the left comparison no commutativity is used anywhere.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped DirectSum

universe v u

namespace Stacks.Monoidal

/-! ### The degree map of a `ℤ`-graded module over an `ℕ`-graded ring -/

/-- Addition of a natural number to an integer, written as a recursion on the natural number. -/
@[reducible]
def natShift : ℕ → ℤ → ℤ
  | 0, b => b
  | a + 1, b => natShift a (b + 1)

/-- A natural number acts on the integers by addition. This is the degree map of a `ℤ`-graded
module over an `ℕ`-graded ring. -/
@[reducible]
scoped instance natVAddInt : VAdd ℕ ℤ where
  vadd := natShift

/-- The natural number `0` acts on `ℤ` as the identity. -/
@[simp]
theorem natVAdd_zero (b : ℤ) : (0 : ℕ) +ᵥ b = b := rfl

/-- `(a + 1) +ᵥ b = a +ᵥ (b + 1)` for `a : ℕ` and `b : ℤ`. -/
theorem natVAdd_succ (a : ℕ) (b : ℤ) : (a + 1) +ᵥ b = a +ᵥ (b + 1) := rfl

/-- The action of `a : ℕ` on `b : ℤ` is `b + a`. -/
theorem natVAdd_eq (a : ℕ) (b : ℤ) : a +ᵥ b = b + a := by
  induction a generalizing b with
  | zero => simp
  | succ a ih =>
    rw [natVAdd_succ, ih]
    omega

/-- The action of `ℕ` on `ℤ` is compatible with addition in `ℕ`. -/
theorem natVAdd_add (a c : ℕ) (b : ℤ) : (a + c) +ᵥ b = a +ᵥ (c +ᵥ b) := by
  simp only [natVAdd_eq]
  omega

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Coherence lemmas for the action isomorphisms -/

/-- The degree-zero case of associativity of the action isomorphisms, isolated from the
degrees: only the triangle and the naturality of the associator are used. -/
@[reassoc]
theorem actIso_assoc_aux_zero {A B D : C} (e : B ≅ 𝟙_ C) :
    (((A ◁ e.hom) ≫ (ρ_ A).hom) ▷ D)
      = (α_ A B D).hom ≫ (A ◁ ((e.hom ▷ D) ≫ (λ_ D).hom)) :=
  calc (((A ◁ e.hom) ≫ (ρ_ A).hom) ▷ D)
      = ((A ◁ e.hom) ▷ D) ≫ ((ρ_ A).hom ▷ D) := by rw [comp_whiskerRight]
    _ = ((A ◁ e.hom) ▷ D) ≫ (α_ A (𝟙_ C) D).hom ≫ (A ◁ (λ_ D).hom) := by
        rw [MonoidalCategory.triangle]
    _ = (α_ A B D).hom ≫ (A ◁ (e.hom ▷ D)) ≫ (A ◁ (λ_ D).hom) := by
        rw [← Category.assoc, associator_naturality_middle, Category.assoc]
    _ = (α_ A B D).hom ≫ (A ◁ ((e.hom ▷ D) ≫ (λ_ D).hom)) := by rw [whiskerLeft_comp]

/-- The inductive step of associativity of the action isomorphisms, isolated from the degrees:
only the naturality of the structural isomorphisms and the pentagon are used. -/
theorem actIso_assoc_aux_succ {A B D E G F Mb Mb1 B1 D1 Lg : C}
    (f : A ⊗ B ⟶ D) (g : D ⊗ Mb1 ⟶ E) (h : B ⊗ Mb1 ⟶ F) (k : A ⊗ F ⟶ G) {q : G ⟶ E}
    (σB : B ⊗ Lg ≅ B1) (σD : D ⊗ Lg ≅ D1) (τ : Lg ⊗ Mb ≅ Mb1)
    (ih : (f ▷ Mb1) ≫ g = (α_ A B Mb1).hom ≫ (A ◁ h) ≫ k ≫ q) :
    ((((A ◁ σB.inv) ≫ (α_ A B Lg).inv ≫ (f ▷ Lg) ≫ σD.hom) ▷ Mb)
        ≫ (σD.inv ▷ Mb) ≫ (α_ D Lg Mb).hom ≫ (D ◁ τ.hom) ≫ g)
      = (α_ A B1 Mb).hom
          ≫ (A ◁ ((σB.inv ▷ Mb) ≫ (α_ B Lg Mb).hom ≫ (B ◁ τ.hom) ≫ h)) ≫ k ≫ q := by
  have hpent : ((α_ A B Lg).inv ▷ Mb) ≫ (α_ (A ⊗ B) Lg Mb).hom ≫ (α_ A B (Lg ⊗ Mb)).hom
      = (α_ A (B ⊗ Lg) Mb).hom ≫ (A ◁ (α_ B Lg Mb).hom) := by
    monoidal_coherence
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← comp_whiskerRight_assoc σD.hom σD.inv, σD.hom_inv_id, id_whiskerRight,
    Category.id_comp, associator_naturality_left_assoc, ← whisker_exchange_assoc, ih,
    associator_naturality_right_assoc, reassoc_of% hpent,
    associator_naturality_middle_assoc]

/-! ### Module systems -/

/-- A *module system* over a power system `S`: a family `obj n` of candidate twists of an
object by the `n`-th tensor power of `S.gen`, indexed by the integers, together with the
comparisons `S.gen ⊗ obj n ≅ obj (n + 1)` adding one more tensor factor. -/
structure ModuleSystem (S : PowerSystem C) where
  /-- The twist of the object by the `n`-th tensor power of the generator. -/
  obj : ℤ → C
  /-- One more tensor factor of the generator. -/
  succIso : ∀ n : ℤ, S.gen ⊗ obj n ≅ obj (n + 1)

namespace ModuleSystem

variable {S : PowerSystem C} (M : ModuleSystem S)

/-- The action isomorphism `S.obj a ⊗ M.obj b ≅ M.obj (a +ᵥ b)`, by induction on `a`: the left
unitor in degree zero, and otherwise one tensor factor of the generator split off the power and
absorbed into the module by the successor comparison. -/
noncomputable def actIso : (a : ℕ) → (b : ℤ) → S.obj a ⊗ M.obj b ≅ M.obj (a +ᵥ b)
  | 0, _ => whiskerRightIso S.objZeroIso _ ≪≫ λ_ _
  | a + 1, b => whiskerRightIso (S.succIso a).symm _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (M.succIso b) ≪≫ actIso a (b + 1)

/-- In degree zero, the action isomorphism is the left unitor composed with the identification
`S.obj 0 ≅ 𝟙_ C`. -/
theorem actIso_zero (b : ℤ) :
    M.actIso 0 b = whiskerRightIso S.objZeroIso _ ≪≫ λ_ _ := rfl

/-- The action isomorphism in degree `a + 1` splits off one tensor factor of the generator,
absorbs it into the module by the successor comparison, and applies the action isomorphism in
degree `a`. -/
theorem actIso_succ (a : ℕ) (b : ℤ) :
    M.actIso (a + 1) b = whiskerRightIso (S.succIso a).symm _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (M.succIso b) ≪≫ M.actIso a (b + 1) := rfl

/-- **The action isomorphisms are associative for the multiplication isomorphisms of the power
system.** Together with `Stacks.Monoidal.PowerSystem.mulIso_assoc` this is what makes the
global sections of a module system a graded module. -/
theorem actIso_assoc (a : ℕ) : ∀ (c : ℕ) (b : ℤ),
    ((S.mulIso a c).hom ▷ M.obj b) ≫ (M.actIso (a + c) b).hom
      = (α_ _ _ _).hom ≫ (S.obj a ◁ (M.actIso c b).hom) ≫ (M.actIso a (c +ᵥ b)).hom
          ≫ eqToHom (congrArg M.obj (natVAdd_add a c b).symm)
  | 0, b => by
      have e : eqToHom (congrArg M.obj (natVAdd_add a 0 b).symm)
          = 𝟙 (M.obj (a +ᵥ (0 +ᵥ b))) := rfl
      rw [e, Category.comp_id]
      simp only [PowerSystem.mulIso_zero, actIso_zero, Iso.trans_hom, whiskerLeftIso_hom,
        whiskerRightIso_hom]
      exact actIso_assoc_aux_zero_assoc S.objZeroIso (M.actIso a b).hom
  | c + 1, b => by
      simp only [PowerSystem.mulIso_succ, actIso_succ, Iso.trans_hom, Iso.symm_hom,
        whiskerLeftIso_hom, whiskerRightIso_hom]
      exact actIso_assoc_aux_succ (S.mulIso a c).hom (M.actIso (a + c) (b + 1)).hom
        (M.actIso c (b + 1)).hom (M.actIso a (c +ᵥ (b + 1))).hom
        (S.succIso c) (S.succIso (a + c)) (M.succIso b) (actIso_assoc a c (b + 1))

/-! ### The graded module of global sections -/

/-- The action of a global section of `S.obj a` on a global section of `M.obj b`, as a global
section of `M.obj (a +ᵥ b)`. -/
noncomputable def sectionSMul {a : ℕ} {b : ℤ} (s : 𝟙_ C ⟶ S.obj a) (t : 𝟙_ C ⟶ M.obj b) :
    𝟙_ C ⟶ M.obj (a +ᵥ b) :=
  sectionTensor s t ≫ (M.actIso a b).hom

/-- The unit section acts as the identity. -/
@[simp]
theorem sectionOne_sectionSMul {b : ℤ} (t : 𝟙_ C ⟶ M.obj b) :
    M.sectionSMul S.sectionOne t = t := by
  have key : sectionTensor S.objZeroIso.inv t
      ≫ ((S.objZeroIso.hom ▷ M.obj b) ≫ (λ_ (M.obj b)).hom) = t := by
    rw [← Category.assoc, sectionTensor_comp_whiskerRight, Iso.inv_hom_id,
      sectionTensor_comp_leftUnitor]
  exact key

/-- The action of global sections is associative for the multiplication of the section ring. -/
theorem sectionSMul_assoc {a c : ℕ} {b : ℤ} (s : 𝟙_ C ⟶ S.obj a) (u : 𝟙_ C ⟶ S.obj c)
    (t : 𝟙_ C ⟶ M.obj b) :
    M.sectionSMul (S.sectionMul s u) t
      = M.sectionSMul s (M.sectionSMul u t)
          ≫ eqToHom (congrArg M.obj (natVAdd_add a c b).symm) := by
  rw [sectionSMul, sectionSMul, sectionSMul, PowerSystem.sectionMul,
    ← sectionTensor_comp_whiskerRight, Category.assoc, M.actIso_assoc a c b,
    sectionTensor_comp_associator_assoc, sectionTensor_comp_whiskerLeft_assoc,
    Category.assoc]

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

/-- A global section acting on the zero section gives zero. -/
@[simp]
theorem sectionSMul_zero {a : ℕ} {b : ℤ} (s : 𝟙_ C ⟶ S.obj a) :
    M.sectionSMul s (0 : 𝟙_ C ⟶ M.obj b) = 0 := by
  simp [sectionSMul]

/-- The zero section acts as zero. -/
@[simp]
theorem zero_sectionSMul {a : ℕ} {b : ℤ} (t : 𝟙_ C ⟶ M.obj b) :
    M.sectionSMul (0 : 𝟙_ C ⟶ S.obj a) t = 0 := by
  simp [sectionSMul]

/-- The action of a global section is additive in the module section. -/
@[simp]
theorem sectionSMul_add {a : ℕ} {b : ℤ} (s : 𝟙_ C ⟶ S.obj a) (t t' : 𝟙_ C ⟶ M.obj b) :
    M.sectionSMul s (t + t') = M.sectionSMul s t + M.sectionSMul s t' := by
  simp [sectionSMul, Preadditive.add_comp]

/-- The action is additive in the acting section. -/
@[simp]
theorem add_sectionSMul {a : ℕ} {b : ℤ} (s s' : 𝟙_ C ⟶ S.obj a) (t : 𝟙_ C ⟶ M.obj b) :
    M.sectionSMul (s + s') t = M.sectionSMul s t + M.sectionSMul s' t := by
  simp [sectionSMul, Preadditive.add_comp]

/-- **The global sections of a module system form a `ℤ`-graded module over the `ℕ`-graded
section ring of the power system.** No commutativity of the section ring is used. -/
@[instance_reducible]
noncomputable def gmodule :
    letI : GradedMonoid.GMonoid (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := S.gradedMonoid
    DirectSum.Gmodule (fun n : ℕ => 𝟙_ C ⟶ S.obj n) (fun n : ℤ => 𝟙_ C ⟶ M.obj n) := by
  letI : GradedMonoid.GOne (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := ⟨S.sectionOne⟩
  letI : GradedMonoid.GMul (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := ⟨S.sectionMul⟩
  letI : GradedMonoid.GMonoid (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := S.gradedMonoid
  letI : GradedMonoid.GSMul (fun n : ℕ => 𝟙_ C ⟶ S.obj n) (fun n : ℤ => 𝟙_ C ⟶ M.obj n) :=
    ⟨M.sectionSMul⟩
  exact {
    smul := M.sectionSMul
    one_smul := by
      rintro ⟨n, t⟩
      change GradedMonoid.mk _ _ = GradedMonoid.mk _ _
      apply Sigma.ext (natVAdd_zero n)
      change HEq (M.sectionSMul S.sectionOne t) t
      rw [M.sectionOne_sectionSMul]
    mul_smul := by
      rintro ⟨n, s⟩ ⟨m, u⟩ ⟨k, t⟩
      change GradedMonoid.mk _ _ = GradedMonoid.mk _ _
      apply Sigma.ext (natVAdd_add n m k)
      change HEq (M.sectionSMul (S.sectionMul s u) t)
        (M.sectionSMul s (M.sectionSMul u t))
      rw [M.sectionSMul_assoc]
      exact comp_eqToHom_heq _ _
    smul_add := M.sectionSMul_add
    smul_zero := M.sectionSMul_zero
    add_smul := M.add_sectionSMul
    zero_smul := M.zero_sectionSMul }

/-- The direct sum of the global sections of a module system is a module over the section ring
of the power system. -/
@[instance_reducible]
noncomputable def module :
    letI : DirectSum.GRing (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := S.gradedRing
    Module (⨁ n : ℕ, (𝟙_ C ⟶ S.obj n)) (⨁ n : ℤ, (𝟙_ C ⟶ M.obj n)) := by
  letI : DirectSum.GRing (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := S.gradedRing
  letI : DirectSum.Gmodule (fun n : ℕ => 𝟙_ C ⟶ S.obj n) (fun n : ℤ => 𝟙_ C ⟶ M.obj n) :=
    M.gmodule
  exact DirectSum.Gmodule.module _ _

end Preadditive

end ModuleSystem

end Stacks.Monoidal
