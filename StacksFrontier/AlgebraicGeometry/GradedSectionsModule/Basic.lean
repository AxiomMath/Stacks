module

public import Mathlib.Algebra.Module.GradedModule
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Commutativity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graded module of global sections of the twists of a sheaf of modules

[Stacks, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) attaches to an invertible sheaf
`L` on a space `X` not only the graded ring

  `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})`

but also, for an arbitrary sheaf of `𝒪_X`-modules `F`, a graded `Γ_*(X, L)`-module

  `Γ_*(X, L, F) = ⨁_n Γ(X, L^{⊗ n} ⊗_{𝒪_X} F)`.

`StacksFrontier/AlgebraicGeometry/GradedSectionRing/` builds the ring; this file builds the
module, in the same `Stacks.Monoidal.PowerSystem` style and at the same `ℕ` grading, so that
`⨁_{n ≥ 0} Γ(X, L^{⊗ n} ⊗ F)` is a module over `⨁_{n ≥ 0} Γ(X, L^{⊗ n})`.

The scalar action is the only new construction: a global section `t` of `L^{⊗ b}` and a global
section `u` of `L^{⊗ a} ⊗ F` are tensored together and the two power factors are reassociated
and multiplied,

  `𝟙_ ⟶ L^{⊗ b} ⊗ (L^{⊗ a} ⊗ F) ⟶ (L^{⊗ b} ⊗ L^{⊗ a}) ⊗ F ⟶ L^{⊗ (b + a)} ⊗ F`.

Associativity and unitality then reduce, by the pentagon and the naturality of the associator,
to the associativity `Stacks.Monoidal.PowerSystem.mulIsoAt_assoc` and the unit law
`Stacks.Monoidal.PowerSystem.mulIsoAt_zero_left_hom` of the multiplication isomorphisms
themselves, which are the coherence of Tag 01CU; nothing new about tensor powers is needed, and
in particular no commutativity constraint and no braiding.

## Main definitions

* `Stacks.Monoidal.PowerSystem.sectionSMulAt`: the scalar action, with its target exponent named
  by an arbitrary witness of `b + a = s`, as `Stacks.Monoidal.PowerSystem.mulIsoAt` does for the
  multiplication isomorphisms.
* `Stacks.Monoidal.PowerSystem.sectionSMul`: the same at the exponent `b + a` itself, which is
  the shape `DirectSum.Gmodule` asks for.
* `Stacks.Monoidal.PowerSystem.gradedModule`: the `DirectSum.Gmodule` structure.
* `Stacks.Monoidal.PowerSystem.sectionModule`: that structure read through
  `DirectSum.Gmodule.module` and the graded ring `Stacks.Monoidal.PowerSystem.gradedRing`, i.e.
  a genuine `Module (⨁ n : ℕ, (𝟙_ C ⟶ S.obj n)) (⨁ n : ℕ, (𝟙_ C ⟶ S.obj n ⊗ F))`.
* `Stacks.SheafOfModules.Invertible.homGradedModule` and
  `Stacks.SheafOfModules.Invertible.homSectionModule`: the same two for the non-negative tensor
  powers of an invertible sheaf of modules, so that `⨁_{n ≥ 0} Γ(X, L^{⊗ n} ⊗ F)` is a graded
  `Γ_*(X, L)`-module.

## Main results

* `Stacks.Monoidal.PowerSystem.sectionOne_sectionSMulAt`: the unit section acts as the identity.
* `Stacks.Monoidal.PowerSystem.sectionSMulAt_assoc`: **the action is associative against the
  multiplication of the graded ring**, which is the module axiom of Tag 01CV.
* `Stacks.Monoidal.PowerSystem.sectionSMulAt_add`, `add_sectionSMulAt`, `sectionSMulAt_zero` and
  `zero_sectionSMulAt`: the action is biadditive. These are the remaining `DirectSum.Gmodule`
  fields and come, exactly as the distributive laws of the ring do, from
  `CategoryTheory.MonoidalPreadditive`.

## Implementation notes

**The grading is by `ℕ`.** Tag 01CV's module is graded by all of `ℤ`. What is built here is its
non-negative part, which is a module over the whole of `Γ_*(X, L)` (itself non-negatively graded)
and is the part that [Stacks, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L) uses: the
degree-zero part of the localization of `Γ_*(X, L, F)` at a section `s` of `L` consists of the
fractions `t / s^n` with `t` of degree `n`, and `s^n` lies in the ring only for `n ≥ 0`. The
`ℤ`-graded module is a second construction, from the integer multiplication
`Stacks.Monoidal.IntPower.mulAt`, in
`StacksFrontier/AlgebraicGeometry/GradedSectionsModule/IntGraded.lean`.

**The twisting factor is on the right: `L^{⊗ n} ⊗ F`, where Tag 01CV writes
`F ⊗_{𝒪_X} L^{⊗ n}`.** The two are the same module up to the canonical symmetry of the tensor
product of sheaves of modules, but the choice is forced and is not cosmetic.
`DirectSum.Gmodule` is a *left* module structure: a degree-`b` scalar acting on a degree-`a`
element must land in degree `b + a`, so the scalar's tensor factor `L^{⊗ b}` has to be tensored
on the **left**. With `F` on the left it would have to be moved past `F` first, which needs the
braiding, and the module structure would then depend on symmetry *and* — because the resulting
action would be a right action read backwards — on the commutativity constraint of Tag 01CU.
With `F` on the right nothing of the kind is used, and the construction is unconditional.

**The summands are morphisms out of the tensor unit**, as in
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Ring.lean`, and for the same reason:
`DirectSum.Gmodule` needs an `AddMonoid` on every summand, and a morphism group of a preadditive
category has one while `PresheafOfModules.sections` — a bare subtype of a product — does not.
`SheafOfModules.unitHomEquiv` identifies the two.

**The two coherence inputs are isolated as object-level lemmas.** `sectionSMul_assoc_aux` and
`sectionSMul_one_aux` mention no exponents at all: they say that whiskering a factor `F` onto an
associativity, respectively a unit law, of a multiplication gives one again. This is the same
device as `Stacks.Monoidal.mulIso_assoc_aux_succ`, and it keeps the index
bookkeeping of the `DirectSum.Gmodule` fields separate from the monoidal coherence.

**Why the target exponent is named.** `sectionSMulAt` takes a witness of `b + a = s` rather than
returning a section of `S.obj (b + a)`, because `DirectSum.Gmodule`'s `one_smul` and `mul_smul`
are equalities in a sigma type whose indices are `0 + a` and `b + c + a`, neither of which is
syntactically the index the action produces. Naming the target means the index is adjusted by
`sectionSMulAt_heq` alone, and no `eqToHom` appears in any statement or proof in this file.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ### Coherence lemmas for the action on a twisted object -/

/-- Whiskering a factor `F` onto an associativity identity between multiplications gives an
associativity identity for the induced maps on `- ⊗ F`. The exponents of a power system play no
part, so they are absent. -/
theorem sectionSMul_assoc_aux {B D A BD DA T : C} (F : C) (mbd : B ⊗ D ⟶ BD)
    (mbda : BD ⊗ A ⟶ T) (mda : D ⊗ A ⟶ DA) (mbda' : B ⊗ DA ⟶ T)
    (h : (mbd ▷ A) ≫ mbda = (α_ B D A).hom ≫ (B ◁ mda) ≫ mbda') :
    (α_ B D (A ⊗ F)).hom ≫ (B ◁ ((α_ D A F).inv ≫ (mda ▷ F))) ≫ (α_ B DA F).inv
        ≫ (mbda' ▷ F)
      = (mbd ▷ (A ⊗ F)) ≫ (α_ BD A F).inv ≫ (mbda ▷ F) := by
  have hcoh : (α_ B D (A ⊗ F)).hom ≫ (B ◁ (α_ D A F).inv) ≫ (α_ B (D ⊗ A) F).inv
      = (α_ (B ⊗ D) A F).inv ≫ ((α_ B D A).hom ▷ F) := by
    monoidal_coherence
  rw [whiskerLeft_comp, Category.assoc, associator_inv_naturality_middle_assoc,
    reassoc_of% hcoh, ← comp_whiskerRight_assoc, ← comp_whiskerRight]
  simp only [Category.assoc]
  rw [← h, comp_whiskerRight, associator_inv_naturality_left_assoc]

/-- Whiskering a factor `F` onto a unit law for a multiplication gives a unit law for the
induced map on `- ⊗ F`. -/
theorem sectionSMul_one_aux {A E : C} (F : C) (e : E ≅ 𝟙_ C) :
    (α_ E A F).inv ≫ (((e.hom ▷ A) ≫ (λ_ A).hom) ▷ F)
      = (e.hom ▷ (A ⊗ F)) ≫ (λ_ (A ⊗ F)).hom := by
  have hcoh : (α_ (𝟙_ C) A F).inv ≫ ((λ_ A).hom ▷ F) = (λ_ (A ⊗ F)).hom := by
    monoidal_coherence
  rw [comp_whiskerRight, ← associator_inv_naturality_left_assoc, hcoh]

namespace PowerSystem

variable (S : PowerSystem C) (F : C)

/-! ### The action of the graded ring on the twisted sections -/

/-- The action of a global section `t` of the `b`-th power on a global section `u` of
`L^{⊗ a} ⊗ F`, landing in `L^{⊗ s} ⊗ F` for any named witness of `b + a = s`. -/
noncomputable def sectionSMulAt {a b : ℕ} (t : 𝟙_ C ⟶ S.obj b) (u : 𝟙_ C ⟶ S.obj a ⊗ F)
    (s : ℕ) (h : b + a = s) : 𝟙_ C ⟶ S.obj s ⊗ F :=
  sectionTensor t u ≫ (α_ (S.obj b) (S.obj a) F).inv ≫ ((S.mulIsoAt b a s h).hom ▷ F)

/-- The action of a global section of the `b`-th power on a global section of `L^{⊗ a} ⊗ F`, at
the exponent `b + a`. -/
noncomputable def sectionSMul {a b : ℕ} (t : 𝟙_ C ⟶ S.obj b) (u : 𝟙_ C ⟶ S.obj a ⊗ F) :
    𝟙_ C ⟶ S.obj (b + a) ⊗ F :=
  S.sectionSMulAt F t u (b + a) rfl

/-- Two namings of the same target exponent give the same action, up to `HEq`. This is the only
index adjustment the `DirectSum.Gmodule` fields need. -/
theorem sectionSMulAt_heq {a b s s' : ℕ} (t : 𝟙_ C ⟶ S.obj b) (u : 𝟙_ C ⟶ S.obj a ⊗ F)
    (h : b + a = s) (h' : b + a = s') :
    HEq (S.sectionSMulAt F t u s h) (S.sectionSMulAt F t u s' h') := by
  subst h
  subst h'
  rfl

/-- **The unit section acts as the identity.** -/
@[simp]
theorem sectionOne_sectionSMulAt {a : ℕ} (u : 𝟙_ C ⟶ S.obj a ⊗ F) :
    S.sectionSMulAt F S.sectionOne u a (Nat.zero_add a) = u := by
  rw [sectionSMulAt, sectionOne, S.mulIsoAt_zero_left_hom a, sectionSMul_one_aux,
    sectionTensor_comp_whiskerRight_assoc, Iso.inv_hom_id,
    sectionTensor_comp_leftUnitor]

/-- **The action is associative against the multiplication of the graded ring.** This is the
module axiom of Tag 01CV; it is the associativity `mulIsoAt_assoc` of the multiplication
isomorphisms of Tag 01CU with the factor `F` whiskered on. -/
theorem sectionSMulAt_assoc {a b c : ℕ} (t : 𝟙_ C ⟶ S.obj b) (t' : 𝟙_ C ⟶ S.obj c)
    (u : 𝟙_ C ⟶ S.obj a ⊗ F) (ca s : ℕ) (hca : c + a = ca) (hs : b + ca = s) :
    S.sectionSMulAt F t (S.sectionSMulAt F t' u ca hca) s hs
      = S.sectionSMulAt F (S.sectionMul t t') u s (by omega) := by
  have hassoc : ((S.mulIso b c).hom ▷ S.obj a) ≫ (S.mulIsoAt (b + c) a s (by omega)).hom
      = (α_ (S.obj b) (S.obj c) (S.obj a)).hom ≫ (S.obj b ◁ (S.mulIsoAt c a ca hca).hom)
        ≫ (S.mulIsoAt b ca s hs).hom := by
    rw [← S.mulIsoAt_rfl b c]
    exact S.mulIsoAt_assoc b c a (b + c) ca s rfl hca (by omega)
  have key := sectionSMul_assoc_aux F (S.mulIso b c).hom
    (S.mulIsoAt (b + c) a s (by omega)).hom (S.mulIsoAt c a ca hca).hom
    (S.mulIsoAt b ca s hs).hom hassoc
  simp only [sectionSMulAt, sectionMul, ← sectionTensor_comp_whiskerLeft,
    ← sectionTensor_comp_associator, ← sectionTensor_comp_whiskerRight, Category.assoc]
  rw [key]

/-! ### Biadditivity of the action -/

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

/-- The action of a section of `S.obj b` on the zero section of `S.obj a ⊗ F` is zero. -/
@[simp]
theorem sectionSMulAt_zero {a b : ℕ} (t : 𝟙_ C ⟶ S.obj b) (s : ℕ) (h : b + a = s) :
    S.sectionSMulAt F t (0 : 𝟙_ C ⟶ S.obj a ⊗ F) s h = 0 := by
  simp [sectionSMulAt]

/-- The action of the zero section of `S.obj b` on any section of `S.obj a ⊗ F` is zero. -/
@[simp]
theorem zero_sectionSMulAt {a b : ℕ} (u : 𝟙_ C ⟶ S.obj a ⊗ F) (s : ℕ) (h : b + a = s) :
    S.sectionSMulAt F (0 : 𝟙_ C ⟶ S.obj b) u s h = 0 := by
  simp [sectionSMulAt]

/-- The action is additive in the section of `S.obj a ⊗ F`. -/
@[simp]
theorem sectionSMulAt_add {a b : ℕ} (t : 𝟙_ C ⟶ S.obj b) (u u' : 𝟙_ C ⟶ S.obj a ⊗ F)
    (s : ℕ) (h : b + a = s) :
    S.sectionSMulAt F t (u + u') s h
      = S.sectionSMulAt F t u s h + S.sectionSMulAt F t u' s h := by
  simp [sectionSMulAt, Preadditive.add_comp]

/-- The action is additive in the acting section of `S.obj b`. -/
@[simp]
theorem add_sectionSMulAt {a b : ℕ} (t t' : 𝟙_ C ⟶ S.obj b) (u : 𝟙_ C ⟶ S.obj a ⊗ F)
    (s : ℕ) (h : b + a = s) :
    S.sectionSMulAt F (t + t') u s h
      = S.sectionSMulAt F t u s h + S.sectionSMulAt F t' u s h := by
  simp [sectionSMulAt, Preadditive.add_comp]

/-! ### The graded module of twisted sections -/

/-- **The global sections of the twists `L^{⊗ n} ⊗ F` form a graded module over the graded ring
of global sections of the powers `L^{⊗ n}`.** This is the module of Tag 01CV, at the
non-negative part of its grading; see the implementation notes. Through
`DirectSum.Gmodule.module` and `Stacks.Monoidal.PowerSystem.gradedRing` it makes
`⨁ n : ℕ, (𝟙_ C ⟶ S.obj n ⊗ F)` a module over `⨁ n : ℕ, (𝟙_ C ⟶ S.obj n)`. -/
@[instance_reducible]
noncomputable def gradedModule :
    letI : GradedMonoid.GMonoid (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := S.gradedMonoid
    DirectSum.Gmodule (fun n : ℕ => 𝟙_ C ⟶ S.obj n) (fun n : ℕ => 𝟙_ C ⟶ S.obj n ⊗ F) := by
  letI : GradedMonoid.GMonoid (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := S.gradedMonoid
  letI : GradedMonoid.GSMul (fun n : ℕ => 𝟙_ C ⟶ S.obj n)
      (fun n : ℕ => 𝟙_ C ⟶ S.obj n ⊗ F) := ⟨S.sectionSMul F⟩
  exact {
    smul := S.sectionSMul F
    one_smul := by
      rintro ⟨a, u⟩
      change GradedMonoid.mk _ _ = GradedMonoid.mk _ _
      refine Sigma.ext (Nat.zero_add a) ?_
      change HEq (S.sectionSMulAt F S.sectionOne u (0 + a) rfl) u
      refine HEq.trans (S.sectionSMulAt_heq F S.sectionOne u rfl (Nat.zero_add a)) ?_
      exact heq_of_eq (S.sectionOne_sectionSMulAt F u)
    mul_smul := by
      rintro ⟨b, t⟩ ⟨c, t'⟩ ⟨a, u⟩
      change GradedMonoid.mk _ _ = GradedMonoid.mk _ _
      refine Sigma.ext (Nat.add_assoc b c a) ?_
      change HEq (S.sectionSMulAt F (S.sectionMul t t') u (b + c + a) rfl)
        (S.sectionSMulAt F t (S.sectionSMulAt F t' u (c + a) rfl) (b + (c + a)) rfl)
      refine HEq.trans
        (S.sectionSMulAt_heq F (S.sectionMul t t') u rfl (Nat.add_assoc b c a))
        (heq_of_eq ?_)
      exact (S.sectionSMulAt_assoc F t t' u (c + a) (b + (c + a)) rfl rfl).symm
    smul_add := fun t u u' => S.sectionSMulAt_add F t u u' _ _
    smul_zero := fun t => S.sectionSMulAt_zero F t _ _
    add_smul := fun t t' u => S.add_sectionSMulAt F t t' u _ _
    zero_smul := fun u => S.zero_sectionSMulAt F u _ _ }

/-- **`Γ_*(X, L, F)` is a module over `Γ_*(X, L)`.** This is `gradedModule` read through
`DirectSum.Gmodule.module`: the direct sum of the groups of global sections of the twists
`L^{⊗ n} ⊗ F` is a module over the direct sum of the groups of global sections of the powers
`L^{⊗ n}`, which is the ring `Stacks.Monoidal.PowerSystem.sectionRing` of
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Evaluation.lean`. -/
@[instance_reducible]
noncomputable def sectionModule :
    letI : DirectSum.GSemiring (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := S.gradedRing.toGSemiring
    letI : DirectSum.Gmodule (fun n : ℕ => 𝟙_ C ⟶ S.obj n)
      (fun n : ℕ => 𝟙_ C ⟶ S.obj n ⊗ F) := S.gradedModule F
    Module (DirectSum ℕ (fun n : ℕ => 𝟙_ C ⟶ S.obj n))
      (DirectSum ℕ (fun n : ℕ => 𝟙_ C ⟶ S.obj n ⊗ F)) := by
  letI : DirectSum.GSemiring (fun n : ℕ => 𝟙_ C ⟶ S.obj n) := S.gradedRing.toGSemiring
  letI : DirectSum.Gmodule (fun n : ℕ => 𝟙_ C ⟶ S.obj n)
      (fun n : ℕ => 𝟙_ C ⟶ S.obj n ⊗ F) := S.gradedModule F
  infer_instance

end Preadditive

end PowerSystem

end Stacks.Monoidal

namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.monoidalPreadditive

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
  (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- **The global sections of the twists `L^{⊗ n} ⊗ F` of a sheaf of modules by the non-negative
tensor powers of an invertible sheaf of modules form a graded module** over the graded ring
`Stacks.SheafOfModules.Invertible.homGradedRing` of global sections of those powers. This is the
module `Γ_*(X, L, F)` of Tag 01CV, at the non-negative part of its grading. -/
@[instance_reducible, ega "0 5.4.6" "partial"]
noncomputable def homGradedModule :
    letI : GradedMonoid.GMonoid
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ)) := (tensorPowerSystem O hO L).gradedMonoid
    DirectSum.Gmodule
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ))
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ) ⊗ F) :=
  (tensorPowerSystem O hO L).gradedModule F

/-- **The graded module `Γ_*(X, L, F)` of Tag 01CV is a module over the graded ring
`Γ_*(X, L)`**, at the non-negative part of its grading: `⨁_{n ≥ 0} Γ(X, L^{⊗ n} ⊗ F)` is a module
over `⨁_{n ≥ 0} Γ(X, L^{⊗ n})`. -/
@[instance_reducible]
noncomputable def homSectionModule :
    letI : DirectSum.GSemiring
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ)) := (tensorPowerSystem O hO L).gradedRing.toGSemiring
    letI : DirectSum.Gmodule
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ))
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ) ⊗ F) := (tensorPowerSystem O hO L).gradedModule F
    Module
      (DirectSum ℕ (fun n : ℕ =>
        𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO))
          ⟶ tensorPower O hO L (n : ℤ)))
      (DirectSum ℕ (fun n : ℕ =>
        𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO))
          ⟶ tensorPower O hO L (n : ℤ) ⊗ F)) :=
  (tensorPowerSystem O hO L).sectionModule F

end Stacks.SheafOfModules.Invertible

end
