module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.Order.Category.Preord
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The limit of a diagram of commutative algebras as compatible families

Let `R` be a commutative ring and `F : J ⥤ CommAlgCat R` a diagram over a small index category.
The compatible families `(a_j) ∈ ∏_j F(j)`, those with `F(f)(a_i) = a_j` for every arrow
`f : i ⟶ j`, form an `R`-subalgebra of the product, and with the projections it is a limit cone
of `F`.

For an inverse system indexed by `ℕᵒᵖ` whose transition maps `F(n + 1) ⟶ F(n)` are surjective,
every transition map is surjective and so is every projection from the limit.

## Main definitions

* `CommAlgCat.sectionsSubalgebra F`: the compatible families.
* `CommAlgCat.sectionsCone F`: the cone with vertex the compatible families.
* `CommAlgCat.isLimitSectionsCone F`: it is a limit cone.

## Main results

* `CommAlgCat.surjective_map_of_surjective_succ`: in an inverse system indexed by `ℕᵒᵖ` with
  surjective successor transitions, every transition map is surjective.
* `CommAlgCat.surjective_sectionsCone_π`: the projections of the limit of such a system are
  surjective.
* `CommAlgCat.ker_sectionsCone_π_zero_sq_eq_bot`: if the transition maps onto the bottom level
  have square-zero kernels, so does the projection of the limit onto it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CommAlgCat

variable {R : Type u} [CommRing R]

section Sections

variable {J : Type} [SmallCategory J] (F : J ⥤ CommAlgCat.{u} R)

/-- The compatible families of a diagram of commutative `R`-algebras: the elements `(a_j)` of
`∏_j F(j)` with `F(f)(a_i) = a_j` for every arrow `f : i ⟶ j`. -/
def sectionsSubalgebra : Subalgebra R (∀ j, F.obj j) where
  carrier := {a | ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f (a i) = a j}
  mul_mem' {a b} ha hb i j f := by
    simp only [Set.mem_ofPred_eq, Pi.mul_apply, map_mul] at ha hb ⊢
    rw [ha f, hb f]
  add_mem' {a b} ha hb i j f := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, map_add] at ha hb ⊢
    rw [ha f, hb f]
  algebraMap_mem' r i j f := by
    simp only [Pi.algebraMap_apply, AlgHom.commutes]

variable {F} in
/-- A family `a ∈ ∏_j F(j)` lies in `sectionsSubalgebra F` if and only if `F(f)(a_i) = a_j` for
every arrow `f : i ⟶ j`. -/
theorem mem_sectionsSubalgebra_iff (a : ∀ j, F.obj j) :
    a ∈ sectionsSubalgebra F ↔ ∀ ⦃i j : J⦄ (f : i ⟶ j), F.map f (a i) = a j :=
  Iff.rfl

/-- The cone over a diagram of commutative `R`-algebras whose vertex is the algebra of its
compatible families and whose legs are the projections. -/
def sectionsCone : Cone F where
  pt := of R (sectionsSubalgebra F)
  π :=
    { app j := ofHom ((Pi.evalAlgHom R (fun j => F.obj j) j).comp (sectionsSubalgebra F).val)
      naturality i j f := by
        ext a
        exact ((mem_sectionsSubalgebra_iff a.1).mp a.2 f).symm }

/-- The leg of `sectionsCone F` at `j` sends a compatible family `a` to its component `a_j`. -/
theorem sectionsCone_π_app_apply (j : J) (a : sectionsSubalgebra F) :
    (sectionsCone F).π.app j a = a.1 j := rfl

/-- The cone of compatible families is a limit cone. -/
def isLimitSectionsCone : IsLimit (sectionsCone F) where
  lift s := ofHom ((AlgHom.pi fun j => (s.π.app j).hom).codRestrict _
    fun x => (mem_sectionsSubalgebra_iff _).mpr fun i j f => by
      change (s.π.app i ≫ F.map f) x = s.π.app j x
      rw [s.w])
  fac s j := rfl
  uniq s m hm := by
    ext x
    refine Subtype.ext (funext fun j => ?_)
    change (m ≫ (sectionsCone F).π.app j) x = s.π.app j x
    rw [hm]

end Sections

section Sequential

variable (F : ℕᵒᵖ ⥤ CommAlgCat.{u} R)

/-- The transition map of an `ℕᵒᵖ`-diagram along the identity inequality is the identity. -/
private theorem map_homOfLE_op_refl (n : ℕ) :
    F.map (homOfLE (le_refl n)).op = 𝟙 (F.obj (op n)) := by
  rw [← F.map_id]
  rfl

/-- Transition maps of an `ℕᵒᵖ`-diagram compose along composite inequalities. -/
private theorem map_homOfLE_op_trans {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    F.map (homOfLE (hab.trans hbc)).op = F.map (homOfLE hbc).op ≫ F.map (homOfLE hab).op := by
  rw [← F.map_comp, ← op_comp, homOfLE_comp]

/-- In an inverse system of commutative algebras whose successor transition maps are surjective,
every transition map is surjective. -/
theorem surjective_map_of_surjective_succ
    (h : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) {i j : ℕᵒᵖ}
    (f : i ⟶ j) : Function.Surjective (F.map f) := by
  obtain ⟨m⟩ := i
  obtain ⟨n⟩ := j
  have hnm : n ≤ m := leOfHom f.unop
  obtain rfl : f = (homOfLE hnm).op := Subsingleton.elim _ _
  induction m, hnm using Nat.le_induction with
  | base =>
    rw [map_homOfLE_op_refl]
    exact Function.surjective_id
  | succ m hnm ih =>
    rw [map_homOfLE_op_trans F hnm (Nat.le_succ m)]
    exact ih.comp (h m)

/-- In an inverse system of commutative algebras whose successor transition maps are surjective,
every projection out of the algebra of compatible families is surjective. -/
theorem surjective_sectionsCone_π
    (h : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) (k : ℕ) :
    Function.Surjective ((sectionsCone F).π.app (op k)) := by
  intro b
  let seq : ∀ n : ℕ, F.obj (op (k + n)) :=
    fun n => Nat.rec (motive := fun n => F.obj (op (k + n))) b
      (fun n x => Function.surjInv (h (k + n)) x) n
  have hs : ∀ n, F.map (homOfLE (Nat.le_succ (k + n))).op (seq (n + 1)) = seq n :=
    fun n => Function.surjInv_eq (h (k + n)) _
  have hseq {n m : ℕ} (hnm : n ≤ m) :
      F.map (homOfLE (Nat.add_le_add_left hnm k)).op (seq m) = seq n := by
    induction m, hnm using Nat.le_induction with
    | base =>
      rw [map_homOfLE_op_refl]
      rfl
    | succ m hnm ih =>
      refine (ConcreteCategory.congr_hom
        (map_homOfLE_op_trans F (Nat.add_le_add_left hnm k) (Nat.le_succ (k + m))) _).trans ?_
      rwa [ConcreteCategory.comp_apply, hs m]
  let a : ∀ j : ℕᵒᵖ, F.obj j := fun j => F.map (homOfLE (Nat.le_add_left j.unop k)).op
    (seq j.unop)
  have ha : a ∈ sectionsSubalgebra F := by
    refine (mem_sectionsSubalgebra_iff a).mpr fun i j f => ?_
    obtain ⟨m⟩ := i
    obtain ⟨n⟩ := j
    show F.map f (F.map _ (seq m)) = F.map _ (seq n)
    rw [← hseq (leOfHom f.unop), ← ConcreteCategory.comp_apply, ← F.map_comp,
      ← ConcreteCategory.comp_apply, ← F.map_comp]
    rfl
  exact ⟨⟨a, ha⟩, hseq k.zero_le⟩

/-- If every transition map onto the bottom level `F(0)` of an inverse system has square-zero
kernel, then so does the projection from the algebra of compatible families to `F(0)`. -/
theorem ker_sectionsCone_π_zero_sq_eq_bot
    (h : ∀ n : ℕ, RingHom.ker (F.map (homOfLE (Nat.zero_le n)).op).hom.toRingHom ^ 2 = ⊥) :
    RingHom.ker ((sectionsCone F).π.app (op 0)).hom.toRingHom ^ 2 = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [pow_two, Submodule.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  refine Subtype.ext (funext fun j => ?_)
  obtain ⟨n⟩ := j
  have hmem : ∀ c : sectionsSubalgebra F,
      c ∈ RingHom.ker ((sectionsCone F).π.app (op 0)).hom.toRingHom →
        c.1 (op n) ∈ RingHom.ker (F.map (homOfLE (Nat.zero_le n)).op).hom.toRingHom := by
    intro c hc
    show F.map (homOfLE (Nat.zero_le n)).op (c.1 (op n)) = 0
    rw [(mem_sectionsSubalgebra_iff c.1).mp c.2]
    exact hc
  have := Ideal.mul_mem_mul (hmem a ha) (hmem b hb)
  rwa [← pow_two, h n, Ideal.mem_bot] at this

end Sequential

end CommAlgCat

end
