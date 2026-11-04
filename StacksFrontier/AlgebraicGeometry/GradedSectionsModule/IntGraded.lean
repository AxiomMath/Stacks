module

public import StacksFrontier.AlgebraicGeometry.GradedSectionsModule.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseGrading
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The integer-graded module of twisted global sections

[Stacks, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) attaches to a scheme `X`, an
invertible sheaf `L` on `X` and a sheaf of `𝒪_X`-modules `F` two objects: the graded ring

  `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})`

and the graded `Γ_*(X, L)`-module

  `Γ_*(X, L, F) = ⨁_{n ∈ ℤ} Γ(X, F ⊗_{𝒪_X} L^{⊗ n}).`

The ring is `Stacks.SheafOfModules.Invertible.homGradedCommRingOfInvertible`
(`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Commutativity.lean`). The module is built in
`StacksFrontier/AlgebraicGeometry/GradedSectionsModule/Basic.lean` **at the `ℕ` grading**, which
is its non-negative part. This file builds it at the `ℤ` grading of the tag.

The grading of the ring stays `ℕ`, as the tag has it, so the module is indexed by a *different*
type from the ring. `DirectSum.Gmodule` supports this through a `VAdd ιA ιM`, and the one used
here is the repository's exported `Stacks.Veronese.instVAddNatInt`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.intSucc` and `intZero`: the successor comparisons
  `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` for every *integer* `n`, and the identification of `L^{⊗ 0}` with
  the tensor unit, in the localized monoidal structure on sheaves of modules. Together with
  `L` they make the integer tensor powers an integer power system in the sense of
  `StacksFrontier/AlgebraicGeometry/TensorPowerCoherence/IntPowerSystem.lean`.
* `Stacks.Monoidal.IntPower.sectionMulAt` and `sectionSMulAt`: the product of two global sections
  of integer tensor powers, and the action of such a section on a global section of a twist
  `L^{⊗ n} ⊗ F`, both with their target exponent named by a witness.
* `Stacks.SheafOfModules.Invertible.intHomGradedModule`: the `DirectSum.Gmodule` structure
  making `⨁_{n ∈ ℤ} Γ(X, L^{⊗ n} ⊗ F)` a graded module over `⨁_{n ≥ 0} Γ(X, L^{⊗ n})`.
* `Stacks.SheafOfModules.Invertible.intHomSectionModule`: **`Γ_*(X, L, F)` is a
  `Γ_*(X, L)`-module**, at the `ℤ` grading of Tag 01CV.

## Main results

* `Stacks.Monoidal.PowerSystem.mulIso_succ_hom`: the successor recursion of a power system's
  multiplication isomorphisms, written in the shape of
  `Stacks.Monoidal.IntPower.mulAt_step`.
* `Stacks.SheafOfModules.Invertible.full_tensorRight` and `faithful_tensorRight`: **tensoring on
  the right by an invertible sheaf of modules is fully faithful in the localized monoidal
  structure.** This is what the two-sided recursion over `ℤ` needs.
* `Stacks.SheafOfModules.Invertible.mulAt_natCast`: **the multiplication isomorphisms of the
  integer power system agree, at non-negative exponents, with those of the `ℕ`-indexed power
  system** the graded ring is built from. This is the identity that lets an `ℤ`-graded module
  act over the `ℕ`-graded ring.
* `Stacks.Monoidal.IntPower.sectionOne_sectionSMulAt` and `sectionSMulAt_assoc`: the unit and
  associativity laws of the action, the module axioms of Tag 01CV.

## Implementation notes

**Why this is a second construction and not a generalisation.** The `ℕ`-graded module of
`GradedSectionsModule/Basic.lean` builds its action from
`Stacks.Monoidal.PowerSystem.mulIsoAt`, whose exponents are natural numbers; an `ℤ`-graded
module has to multiply a natural exponent by an integer one, which only
`Stacks.Monoidal.IntPower.mulAt` does. The two multiplications are built by the same recursion
from the same data, but in different index types, so neither is an instance of the other and the
bridge between them has to be proved. That bridge is `mulAt_natCast`, by induction on the
second exponent: both satisfy the recursion of `Stacks.Monoidal.IntPower.mulAt_step`, whose
right-hand side is pre-composed with an isomorphism and therefore determines its left-hand side
outright.

**The twisting factor is on the left: `L^{⊗ n} ⊗ F`**, as in `GradedSectionsModule/Basic.lean`
and for the same reason — `DirectSum.Gmodule` is a *left* module structure, so a degree-`b`
scalar acting on a degree-`n` element must land in degree `b + n`, which puts the scalar's
tensor factor `L^{⊗ b}` on the left. Tag 01CV writes `F ⊗ L^{⊗ n}`; the two agree up to the
symmetry of the tensor product, and with `F` on the right no braiding and no commutativity
constraint is used, so the construction is unconditional.

**The two coherence inputs are the ones `GradedSectionsModule/Basic.lean` isolated.**
`Stacks.Monoidal.sectionSMul_assoc_aux` and `sectionSMul_one_aux` mention no exponents at all,
so they serve the `ℤ`-indexed action unchanged; only the associativity and unit law of the
multiplication isomorphisms have to be supplied in the integer form, and those are
`Stacks.Monoidal.IntPower.mulAt_assoc` and `intMulAt_zero_left`.

**Fully faithfulness of `tensorRight L` had to be transported.**
`Stacks.Monoidal.IntPower` needs `(MonoidalCategory.tensorRight Z).Full` and
`(MonoidalCategory.tensorRight Z).Faithful` to run
its recursion in both directions. In the *unlocalized* monoidal structure
`Stacks.SheafOfModules.sheafTensorMonoidal` these hold by `change`, because there
`tensorRight L` is `(Stacks.SheafOfModules.Tensor.sheafTensor _).flip.obj L` on the nose; that
is how
`Stacks.SheafOfModules.Invertible.tensorPowerCoherence_exists` obtains them. The graded ring,
however, lives in `Stacks.SheafOfModules.monoidalCategory`, where the two functors are only
isomorphic, and a statement mixing the two monoidal structures is exactly the kind this
development avoids. So the natural isomorphism is built explicitly from
`Stacks.SheafOfModules.tensorObjIso` — natural in the left factor by
`tensorObjIso_whiskerRight` — and the two properties are transported along it.

**`rw` cannot cross `Nat.cast`.** `mulAt_natCast` compares `mulAt` at exponents `((b : ℕ) : ℤ)`
with `mulAt` at `(b : ℤ) + 1`, and `↑(b + 1)` and `↑b + 1` are definitionally but not
syntactically equal, so a `rw` by `mulAt_step` or `mulAt_zero_hom` fails to find its pattern.
Both steps are therefore taken by binding the specialised equation in a `have` *with a declared
type* in the spelling the goal uses, which is checked up to definitional equality, or by
`refine _.trans ?_`, which forms no rewrite motive. No transparency option and no `erw` is used.

**A hazard for the degree-zero localization.** `GradedModuleDegreeZeroLocalization`
(`StacksFrontier/AlgebraicGeometry/Constructions/ProjModuleRestriction.lean`) takes
`[SetLike.GradedSMul 𝒜 𝒨]` for `𝒜 : ℕ → σ` and `𝒨 : ℤ → τ`, and its file declares its own
*file-local* `VAdd ℕ ℤ`. The instance baked into that signature is therefore not
`Stacks.Veronese.instVAddNatInt`, which is the one used here. The two are definitionally equal,
so a term-level application goes through, but instance search will not cross between them: the
`GradedSMul` has to be supplied as an explicit argument.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w

namespace Stacks.Monoidal

namespace PowerSystem

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (S : PowerSystem C)

/-- The successor recursion of the multiplication isomorphisms of a power system, in the shape
of `Stacks.Monoidal.IntPower.mulAt_step`: pre-composed with an isomorphism, the multiplication
in degree `(a, b + 1)` is the multiplication in degree `(a, b)` with one more tensor factor
split off. Since the pre-composed map is an isomorphism, this determines the degree-`(a, b + 1)`
multiplication, which is what identifies it with its integer-indexed counterpart. -/
theorem mulIso_succ_hom (a b : ℕ) :
    (α_ (S.obj a) (S.obj b) S.gen).hom ≫ S.obj a ◁ (S.succIso b).hom
          ≫ (S.mulIso a (b + 1)).hom
      = ((S.mulIso a b).hom ▷ S.gen) ≫ (S.succIso (a + b)).hom := by
  rw [PowerSystem.mulIso_succ]
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    ← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp,
    Iso.hom_inv_id_assoc]

end PowerSystem

namespace IntPower

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  (P : ℤ → D) (Z : D) [(MonoidalCategory.tensorRight Z).Full]
  [(MonoidalCategory.tensorRight Z).Faithful]
  (p : ∀ n, P n ⊗ Z ≅ P (n + 1)) (u : P 0 ≅ 𝟙_ D) (F : D)

/-! ### The action on the twists of an object -/

/-- The product of a global section of `P b` and a global section of `P c`, as a global section
of `P s` for any named witness of `b + c = s`. -/
noncomputable def sectionMulAt {b c : ℤ} (t : 𝟙_ D ⟶ P b) (t' : 𝟙_ D ⟶ P c)
    (s : ℤ) (h : b + c = s) : 𝟙_ D ⟶ P s :=
  sectionTensor t t' ≫ (mulAt P Z p u b c s h).hom

/-- The action of a global section of `P b` on a global section of the twist `P n ⊗ F`, landing
in `P s ⊗ F` for any named witness of `b + n = s`. -/
noncomputable def sectionSMulAt {b n : ℤ} (t : 𝟙_ D ⟶ P b) (ω : 𝟙_ D ⟶ P n ⊗ F)
    (s : ℤ) (h : b + n = s) : 𝟙_ D ⟶ P s ⊗ F :=
  sectionTensor t ω ≫ (α_ (P b) (P n) F).inv ≫ ((mulAt P Z p u b n s h).hom ▷ F)

/-- Two namings of the same target exponent give the same product, up to `HEq`. -/
theorem sectionMulAt_heq {b c s s' : ℤ} (t : 𝟙_ D ⟶ P b) (t' : 𝟙_ D ⟶ P c)
    (h : b + c = s) (h' : b + c = s') :
    HEq (sectionMulAt P Z p u t t' s h) (sectionMulAt P Z p u t t' s' h') := by
  subst h; subst h'; rfl

/-- Two namings of the same target exponent give the same action, up to `HEq`. This is the only
index adjustment the `DirectSum.Gmodule` fields need. -/
theorem sectionSMulAt_heq {b n s s' : ℤ} (t : 𝟙_ D ⟶ P b) (ω : 𝟙_ D ⟶ P n ⊗ F)
    (h : b + n = s) (h' : b + n = s') :
    HEq (sectionSMulAt P Z p u F t ω s h) (sectionSMulAt P Z p u F t ω s' h') := by
  subst h; subst h'; rfl

/-- **The unit section acts as the identity**, given the left unit law for the multiplication
isomorphisms. -/
theorem sectionOne_sectionSMulAt
    (hl : ∀ n, mulAt P Z p u 0 n n (Int.zero_add n) = whiskerRightIso u (P n) ≪≫ λ_ (P n))
    {n : ℤ} (ω : 𝟙_ D ⟶ P n ⊗ F) :
    sectionSMulAt P Z p u F u.inv ω n (Int.zero_add n) = ω := by
  rw [sectionSMulAt, hl n]
  simp only [Iso.trans_hom, whiskerRightIso_hom]
  rw [sectionSMul_one_aux F u, sectionTensor_comp_whiskerRight_assoc, Iso.inv_hom_id,
    sectionTensor_comp_leftUnitor]

/-- **The action is associative against the product of sections**, which is the module axiom of
Tag 01CV. It is the associativity `Stacks.Monoidal.IntPower.mulAt_assoc` of the multiplication
isomorphisms of Tag 01CU with the factor `F` whiskered on. -/
theorem sectionSMulAt_assoc {b c n : ℤ} (t : 𝟙_ D ⟶ P b) (t' : 𝟙_ D ⟶ P c)
    (ω : 𝟙_ D ⟶ P n ⊗ F) (bc cn s : ℤ) (hbc : b + c = bc) (hcn : c + n = cn)
    (hs : bc + n = s) :
    sectionSMulAt P Z p u F t (sectionSMulAt P Z p u F t' ω cn hcn) s (by omega)
      = sectionSMulAt P Z p u F (sectionMulAt P Z p u t t' bc hbc) ω s hs := by
  have key := sectionSMul_assoc_aux F (mulAt P Z p u b c bc hbc).hom
    (mulAt P Z p u bc n s hs).hom (mulAt P Z p u c n cn hcn).hom
    (mulAt P Z p u b cn s (by omega)).hom
    (mulAt_assoc P Z p u n b c bc cn s hbc hcn hs)
  simp only [sectionSMulAt, sectionMulAt, ← sectionTensor_comp_whiskerLeft,
    ← sectionTensor_comp_associator, ← sectionTensor_comp_whiskerRight, Category.assoc]
  rw [key]

/-! ### Biadditivity of the action -/

section Preadditive

variable [Preadditive D] [MonoidalPreadditive D]

/-- A section acting on the zero section of `P n ⊗ F` gives zero. -/
@[simp]
theorem sectionSMulAt_zero {b n : ℤ} (t : 𝟙_ D ⟶ P b) (s : ℤ) (h : b + n = s) :
    sectionSMulAt P Z p u F t (0 : 𝟙_ D ⟶ P n ⊗ F) s h = 0 := by
  simp [sectionSMulAt]

/-- The zero section of `P b` acts as zero on every section of `P n ⊗ F`. -/
@[simp]
theorem zero_sectionSMulAt {b n : ℤ} (ω : 𝟙_ D ⟶ P n ⊗ F) (s : ℤ) (h : b + n = s) :
    sectionSMulAt P Z p u F (0 : 𝟙_ D ⟶ P b) ω s h = 0 := by
  simp [sectionSMulAt]

/-- The action of a section of `P b` is additive in the section of `P n ⊗ F`. -/
@[simp]
theorem sectionSMulAt_add {b n : ℤ} (t : 𝟙_ D ⟶ P b) (ω ω' : 𝟙_ D ⟶ P n ⊗ F)
    (s : ℤ) (h : b + n = s) :
    sectionSMulAt P Z p u F t (ω + ω') s h
      = sectionSMulAt P Z p u F t ω s h + sectionSMulAt P Z p u F t ω' s h := by
  simp [sectionSMulAt, Preadditive.add_comp]

/-- The action on a section of `P n ⊗ F` is additive in the acting section of `P b`. -/
@[simp]
theorem add_sectionSMulAt {b n : ℤ} (t t' : 𝟙_ D ⟶ P b) (ω : 𝟙_ D ⟶ P n ⊗ F)
    (s : ℤ) (h : b + n = s) :
    sectionSMulAt P Z p u F (t + t') ω s h
      = sectionSMulAt P Z p u F t ω s h + sectionSMulAt P Z p u F t' ω s h := by
  simp [sectionSMulAt, Preadditive.add_comp]

end Preadditive

end IntPower

end Stacks.Monoidal

namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.braidedCategory Stacks.SheafOfModules.symmetricCategory
  Stacks.SheafOfModules.monoidalPreadditive

open Stacks.Monoidal AlgebraicGeometry

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]

/-! ### Tensoring on the right by an invertible sheaf is fully faithful -/

/-- Tensoring on the right by `L` in the localized monoidal structure is the native tensor
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` with its right-hand argument fixed at `L`,
by `Stacks.SheafOfModules.tensorObjIso`. -/
noncomputable def tensorRightNatIso :
    MonoidalCategory.tensorRight L ≅
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L :=
  NatIso.ofComponents (fun M => Stacks.SheafOfModules.tensorObjIso O hO M L)
    (fun {_ _} f => (tensorObjIso_whiskerRight O hO f L).symm)

/-- **Tensoring on the right by an invertible sheaf of modules is full** in the localized
monoidal structure. -/
theorem full_tensorRight : (MonoidalCategory.tensorRight L).Full :=
  Functor.Full.of_iso
    (F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L)
    (tensorRightNatIso O hO L).symm

/-- **Tensoring on the right by an invertible sheaf of modules is faithful** in the localized
monoidal structure. -/
theorem faithful_tensorRight : (MonoidalCategory.tensorRight L).Faithful :=
  Functor.Faithful.of_iso
    (F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L)
    (tensorRightNatIso O hO L).symm

/-! ### The integer power system of an invertible sheaf -/

/-- The successor comparison `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` for an arbitrary integer `n`, in the
localized monoidal structure. At non-negative `n` this is
`Stacks.SheafOfModules.Invertible.tensorPowerSystem`'s successor comparison. -/
noncomputable def intSucc (n : ℤ) :
    tensorPower O hO L n ⊗ L ≅ tensorPower O hO L (n + 1) :=
  Stacks.SheafOfModules.tensorObjIso O hO _ _ ≪≫ tensorPowerSuccIso O hO L n

/-- The zeroth tensor power is the tensor unit on the nose. -/
noncomputable def intZero :
    tensorPower O hO L 0
      ≅ 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO)) :=
  Iso.refl _

section PowerSystemComparison

variable [(MonoidalCategory.tensorRight L).Full] [(MonoidalCategory.tensorRight L).Faithful]

/-- **The multiplication isomorphisms of the integer power system agree, at non-negative
exponents, with those of the `ℕ`-indexed power system.** This is the identity that lets the
`ℤ`-graded module of twisted sections act over the `ℕ`-graded ring of sections: both
multiplications are built by the same recursion from the same successor comparison, in different
index types. -/
theorem mulAt_natCast (a : ℕ) : ∀ (b : ℕ),
    IntPower.mulAt (tensorPower O hO L) L (intSucc O hO L) (intZero O hO L)
        (a : ℤ) (b : ℤ) ((a + b : ℕ) : ℤ) (by push_cast; ring)
      = (tensorPowerSystem O hO L).mulIso a b
  | 0 => by
      apply Iso.ext
      refine (IntPower.mulAt_zero_hom (tensorPower O hO L) L (intSucc O hO L)
        (intZero O hO L) (a : ℤ)).trans ?_
      rfl
  | b + 1 => by
      apply Iso.ext
      have hstep :
          (α_ (tensorPower O hO L (a : ℤ)) (tensorPower O hO L (b : ℤ)) L).hom
              ≫ tensorPower O hO L (a : ℤ) ◁ (intSucc O hO L (b : ℤ)).hom
              ≫ (IntPower.mulAt (tensorPower O hO L) L (intSucc O hO L) (intZero O hO L)
                  (a : ℤ) ((b + 1 : ℕ) : ℤ) ((a + (b + 1) : ℕ) : ℤ) (by push_cast; ring)).hom
            = ((tensorPowerSystem O hO L).mulIso a b).hom ▷ L
                ≫ (intSucc O hO L ((a + b : ℕ) : ℤ)).hom := by
        have h := IntPower.mulAt_step (tensorPower O hO L) L (intSucc O hO L) (intZero O hO L)
          (a : ℤ) (b : ℤ) ((a + b : ℕ) : ℤ) (by push_cast; ring)
        rw [mulAt_natCast a b] at h
        exact h.symm
      exact (cancel_epi ((α_ (tensorPower O hO L (a : ℤ)) (tensorPower O hO L (b : ℤ)) L).hom
        ≫ tensorPower O hO L (a : ℤ) ◁ (intSucc O hO L (b : ℤ)).hom)).mp
          (by
          rw [Category.assoc, Category.assoc]
          exact hstep.trans ((tensorPowerSystem O hO L).mulIso_succ_hom a b).symm)

/-- In degree `(n, 0)` the integer multiplication isomorphism is the right unitor. -/
theorem intMulAt_zero_right (n : ℤ) :
    (IntPower.mulAt (tensorPower O hO L) L (intSucc O hO L) (intZero O hO L)
        n 0 n (Int.add_zero n)).hom
      = (ρ_ (tensorPower O hO L n)).hom := by
  refine (IntPower.mulAt_zero_hom (tensorPower O hO L) L (intSucc O hO L)
    (intZero O hO L) n).trans ?_
  show tensorPower O hO L n ◁ 𝟙 _ ≫ (ρ_ (tensorPower O hO L n)).hom
    = (ρ_ (tensorPower O hO L n)).hom
  rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- **In degree `(0, n)` the integer multiplication isomorphism is the left unitor.** This is
the left unit law the module axiom `Stacks.Monoidal.IntPower.sectionOne_sectionSMulAt` takes as
a hypothesis; it is not part of the recursion, which only fixes the degree-`(n, 0)` value, and
is proved from associativity exactly as in
`Stacks.SheafOfModules.Invertible.tensorPowerCoherence_exists`. -/
theorem intMulAt_zero_left (n : ℤ) :
    IntPower.mulAt (tensorPower O hO L) L (intSucc O hO L) (intZero O hO L)
        0 n n (Int.zero_add n)
      = whiskerRightIso (intZero O hO L) (tensorPower O hO L n) ≪≫ λ_ (tensorPower O hO L n) := by
  have hunit :
      whiskerRightIso (intZero O hO L) (tensorPower O hO L n) ≪≫ λ_ (tensorPower O hO L n)
        = λ_ (tensorPower O hO L n) := by
    apply Iso.ext
    show (𝟙 (tensorPower O hO L 0) ▷ tensorPower O hO L n)
      ≫ (λ_ (tensorPower O hO L n)).hom = (λ_ (tensorPower O hO L n)).hom
    rw [MonoidalCategory.id_whiskerRight]
    exact Category.id_comp _
  rw [hunit]
  apply IntPower.eq_leftUnitor_of_assoc
  have ha := IntPower.mulAt_assoc (tensorPower O hO L) L (intSucc O hO L) (intZero O hO L)
    n 0 0 0 n n (Int.add_zero 0) (Int.zero_add n) (Int.zero_add n)
  rwa [intMulAt_zero_right O hO L 0] at ha

/-! ### The graded module -/

/-- The product of two global sections of non-negative tensor powers, read through the integer
power system, is the product of the graded ring of sections. -/
theorem intSectionMulAt_natCast {b c : ℕ}
    (t : 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
      ⟶ tensorPower O hO L (b : ℤ))
    (t' : 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
      ⟶ tensorPower O hO L (c : ℤ)) :
    IntPower.sectionMulAt (tensorPower O hO L) L (intSucc O hO L) (intZero O hO L)
        t t' ((b + c : ℕ) : ℤ) (by push_cast; ring)
      = (tensorPowerSystem O hO L).sectionMul t t' := by
  rw [IntPower.sectionMulAt, PowerSystem.sectionMul, mulAt_natCast O hO L b c]

/-- **The global sections of the twists `L^{⊗ n} ⊗ F`, for `n` ranging over all of `ℤ`, form a
graded module over the graded ring of global sections of the non-negative powers `L^{⊗ n}`.**
This is the module `Γ_*(X, L, F)` of Tag 01CV, at the `ℤ` grading of that tag. -/
@[instance_reducible]
noncomputable def intHomGradedModule
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      :
    letI : GradedMonoid.GMonoid
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ)) := (tensorPowerSystem O hO L).gradedMonoid
    DirectSum.Gmodule
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ))
      (fun n : ℤ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L n ⊗ F) := by
  let : GradedMonoid.GMonoid
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ)) := (tensorPowerSystem O hO L).gradedMonoid
  let : GradedMonoid.GSMul
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ))
      (fun n : ℤ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L n ⊗ F) :=
    ⟨fun {i j} t ω => IntPower.sectionSMulAt (tensorPower O hO L) L (intSucc O hO L)
      (intZero O hO L) F t ω ((i : ℕ) +ᵥ (j : ℤ)) rfl⟩
  exact {
    smul := fun {i j} t ω => IntPower.sectionSMulAt (tensorPower O hO L) L (intSucc O hO L)
      (intZero O hO L) F t ω ((i : ℕ) +ᵥ (j : ℤ)) rfl
    one_smul := by
      rintro ⟨n, ω⟩
      change GradedMonoid.mk _ _ = GradedMonoid.mk _ _
      refine Sigma.ext (zero_add n) ?_
      refine HEq.trans (IntPower.sectionSMulAt_heq (tensorPower O hO L) L (intSucc O hO L)
        (intZero O hO L) F (intZero O hO L).inv ω rfl (Int.zero_add n)) ?_
      exact heq_of_eq (IntPower.sectionOne_sectionSMulAt (tensorPower O hO L) L
        (intSucc O hO L) (intZero O hO L) F (intMulAt_zero_left O hO L) ω)
    mul_smul := by
      rintro ⟨b, t⟩ ⟨c, t'⟩ ⟨n, ω⟩
      change GradedMonoid.mk _ _ = GradedMonoid.mk _ _
      refine Sigma.ext (show ((b + c : ℕ) : ℤ) + n = (b : ℤ) + (((c : ℕ) : ℤ) + n) by
        push_cast; ring) ?_
      refine HEq.trans (IntPower.sectionSMulAt_heq (tensorPower O hO L) L (intSucc O hO L)
        (intZero O hO L) F ((tensorPowerSystem O hO L).sectionMul t t') ω rfl
        (show ((b + c : ℕ) : ℤ) + n = (b : ℤ) + (((c : ℕ) : ℤ) + n) by push_cast; ring))
        (heq_of_eq ?_)
      rw [← intSectionMulAt_natCast O hO L t t']
      exact (IntPower.sectionSMulAt_assoc (tensorPower O hO L) L (intSucc O hO L)
        (intZero O hO L) F t t' ω ((b + c : ℕ) : ℤ) ((c : ℤ) + n)
        ((b : ℤ) + ((c : ℤ) + n)) (by push_cast; ring) rfl (by push_cast; ring)).symm
    smul_add := fun t ω ω' => IntPower.sectionSMulAt_add (tensorPower O hO L) L
      (intSucc O hO L) (intZero O hO L) F t ω ω' _ _
    smul_zero := fun t => IntPower.sectionSMulAt_zero (tensorPower O hO L) L
      (intSucc O hO L) (intZero O hO L) F t _ _
    add_smul := fun t t' ω => IntPower.add_sectionSMulAt (tensorPower O hO L) L
      (intSucc O hO L) (intZero O hO L) F t t' ω _ _
    zero_smul := fun ω => IntPower.zero_sectionSMulAt (tensorPower O hO L) L
      (intSucc O hO L) (intZero O hO L) F ω _ _ }

/-- **`Γ_*(X, L, F)` is a `Γ_*(X, L)`-module**, at the `ℤ` grading of Tag 01CV: the direct sum
over all integers `n` of the groups of global sections of the twists `L^{⊗ n} ⊗ F` is a module
over the ring `Stacks.Monoidal.PowerSystem.sectionRing` of the non-negative powers. -/
@[instance_reducible, ega "II 2.6.1" "(F)", ega "III 2.1.1" "partial", ega "III 2.1.2"]
noncomputable def intHomSectionModule
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      :
    letI : DirectSum.GSemiring
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ)) := (homGradedRing O hO L).toGSemiring
    letI : DirectSum.Gmodule
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ))
      (fun n : ℤ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L n ⊗ F) := intHomGradedModule O hO L F
    Module
      (DirectSum ℕ fun n : ℕ =>
        𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO))
          ⟶ tensorPower O hO L (n : ℤ))
      (DirectSum ℤ fun n : ℤ =>
        𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
          hO))
          ⟶ tensorPower O hO L n ⊗ F) := by
  let : DirectSum.GSemiring
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ)) := (homGradedRing O hO L).toGSemiring
  let : DirectSum.Gmodule
      (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L (n : ℤ))
      (fun n : ℤ => 𝟙_ (_root_.SheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
        ⟶ tensorPower O hO L n ⊗ F) := intHomGradedModule O hO L F
  infer_instance

end PowerSystemComparison

end Stacks.SheafOfModules.Invertible

end
