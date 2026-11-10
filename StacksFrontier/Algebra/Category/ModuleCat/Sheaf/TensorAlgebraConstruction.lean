module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras

/-!
# Towards the tensor, exterior and symmetric algebras of a sheaf of modules

`SheafOfModules.TensorExteriorSymmetricAlgebras J F` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`) bundles the three
graded algebras Stacks Section 17.21 attaches to a sheaf of modules `F`, together with their
universal properties, the identification of the pieces of `T(F)` with the sheafified tensor
powers, and the two quotient maps. `Stacks.GradedAlgebra.sheafify` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification`) turns a *sectionwise*
graded algebra of presheaves of modules into a `SheafOfModules.GradedAlgebra`. This file supplies
the three pieces of machinery that stand between the two, each stated for an arbitrary
sectionwise graded algebra so that it applies verbatim to the tensor, the exterior and the
symmetric case:

1. **the second half of a universal property** — `Stacks.GradedAlgebra.isUniversal_sheafify`
   reduces `SheafOfModules.GradedAlgebra.IsUniversal` for a sheafified graded algebra to a
   *presheaf-level* universal property stated against the restriction of scalars of a sheaf of
   graded algebras, for which `SheafOfModules.GradedAlgebra.restrictScalars` and
   `Stacks.GradedAlgebra.UnitalHom` are built here;
2. **the tensor-power comparison** — `SheafOfModules.tensorPowerSheafifyIso` identifies the
   sheafification of a sectionwise family satisfying the tensor-power recursion with
   `SheafOfModules.tensorPower`, and `tensorPowerSheafifyIso_add_two_unit` pins it down on pure
   tensors of unit images;
3. **vanishing in negative degrees** — `Stacks.GradedAlgebra.sheafify_piece_eq_zero` says that a
   degree in which the sectionwise algebra has no sections is a degree in which its
   sheafification has none.

## Main definitions

* `Stacks.GradedAlgebra.Hom` and `Stacks.GradedAlgebra.UnitalHom`: homomorphisms, and unital
  homomorphisms, of graded algebras of presheaves of modules, with `Hom.id`, `Hom.comp` and
  their unital analogues. These are the presheaf-level counterparts of
  `SheafOfModules.GradedAlgebra.Hom` and `UnitalHom`, and the two families of homogeneous pieces
  are independent parameters, so there is no category of graded algebras on a *fixed* family.
* `SheafOfModules.GradedAlgebra.restrictScalars`: a sheaf of graded algebras over `R`, read along
  `α : R₀ ⟶ R.obj` as a graded algebra of presheaves of `R₀`-modules.
* `Stacks.GradedAlgebra.restrictUnitalHom`: a unital homomorphism out of a sheafified graded
  algebra, restricted along the sheafification units to a unital homomorphism out of the
  sectionwise algebra.
* `SheafOfModules.tensorPowerSheafifyIso`: the comparison of the sheafified sectionwise tensor
  powers with `SheafOfModules.tensorPower`.
* `PresheafOfModules.sheafification_hom_ext_apply`, `SheafOfModules.hom_congr_app_apply` and
  `SheafOfModules.iso_inv_hom_app_apply`: the three section-level forms of extensionality and
  congruence that the proofs below are written in.

## Main results

* `Stacks.GradedAlgebra.isUniversal_sheafify`: **the second component of a universal property.**
  If the sectionwise graded algebra `A` with degree-one generator `gen` is universal among
  *restrictions of scalars* of sheaves of graded algebras — for every sheaf of graded algebras
  `B` and every degree-one generator `κ` of `B` with the property in question, there is a unique
  unital homomorphism `A ⟶ B|_{R₀}` carrying `gen` to `κ` read on unit images — then
  `A.sheafify α` with the generator `A.sheafifyGen α gen` is universal in
  `SheafOfModules.GradedAlgebra.IsUniversal`.
* `Stacks.GradedAlgebra.isTensorAlgebra_sheafify`, `isExteriorAlgebra_sheafify` and
  `isSymmetricAlgebra_sheafify`: the three instances of the previous result for the three
  properties of Section 17.21, with the first component discharged by
  `Stacks.GradedAlgebra.squareZero_sheafifyGen` and `pairwiseCommutes_sheafifyGen`. These are
  the `tensor_isTensorAlgebra`, `exterior_isExteriorAlgebra` and `symmetric_isSymmetricAlgebra`
  fields of `SheafOfModules.TensorExteriorSymmetricAlgebras`, reduced to sectionwise data.
* `SheafOfModules.tensorPowerSheafifyIso_add_two_unit`: the comparison carries the unit image of
  a sectionwise section of degree `n + 2` which is a pure tensor to the corresponding pure
  tensor of unit images. This is the equation that determines it, and it is the input to the
  `tensorPieceIso_mul_left` field of the bundle.
* `PresheafOfModules.tensorSheafBifunctor_map_unit_tmul`: the tensor product bifunctor on sheaves
  of modules, on a morphism, read on the unit image of a pure tensor.
* `PresheafOfModules.sheafificationTensorIso_inv_unit_tmul`: Tag 0GMW read in the direction the
  induction above needs.
* `PresheafOfModules.sheafification_section_eq_zero`: the sheafification of a presheaf of modules
  with no nonzero sections has no nonzero sections, and
  `Stacks.GradedAlgebra.sheafify_piece_eq_zero`, its graded form: this is the
  `tensorPiece_eq_zero_of_neg`, `exteriorPiece_eq_zero_of_neg` and
  `symmetricPiece_eq_zero_of_neg` fields of
  `SheafOfModules.TensorExteriorSymmetricAlgebras`, reduced to sectionwise data.

## Implementation notes

**What is here and what is not.** This file does **not** construct an inhabitant of
`SheafOfModules.TensorExteriorSymmetricAlgebras`. What is still missing for that is the
*sectionwise* input: a `Stacks.GradedAlgebra` on the family `n ↦ Tⁿ(F.val)` of sectionwise tensor
powers (and its exterior analogue) with its degree-one generator, together with the presheaf-level
universal property that `isUniversal_sheafify` consumes. That needs base change of
`TensorAlgebra` and `ExteriorAlgebra` along a ring homomorphism — the analogue of
`SymmetricAlgebra.mapₛₗ` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerSheafification`, absent from Mathlib
for all three — and the extension of an `ℕ`-graded sectionwise algebra to the `ℤ`-graded one that
`Stacks.GradedAlgebra.sheafify` takes, the pieces in negative degrees being zero. Everything
below is stated so that it applies to such a family once it exists, and nothing below is
specialized in anticipation of it.

**Why the universal property splits the way it does.**
`Stacks.GradedAlgebra.existsUnique_desc` descends a *degreewise* morphism out of the sectionwise
algebra, with multiplicativity and unitality stated on sections, to a unital homomorphism out of
the sheafification. `isUniversal_sheafify` repackages that as the statement
`SheafOfModules.GradedAlgebra.IsUniversal` asks for, and for that repackaging the degreewise
morphism has to be bundled: its multiplicativity and unitality are exactly the laws of a
`Stacks.GradedAlgebra.UnitalHom` into `SheafOfModules.GradedAlgebra.restrictScalars`, and the
uniqueness half needs the converse passage `restrictUnitalHom`, from a unital homomorphism out of
the sheafification back to one out of the sectionwise algebra. Neither the restriction of
scalars nor the presheaf-level `UnitalHom` existed before this file.

**The tensor-power induction, and the two bridges it needs.** `tensorPowerSheafifyIso` is a
two-step recursion on `ℕ`: degrees `0` and `1` are hypotheses, and the step from `n + 1` to
`n + 2` is Tag 0GMW (`PresheafOfModules.sheafificationTensorIso`) followed by the tensor
bifunctor applied to the degree-one identification and the inductive one. The two section-level
bridges this needs are stated here rather than inlined, because each is delicate:
`tensorSheafBifunctor_map_unit_tmul` is proved through `tensorSheafBifunctor_map`, whose
`Functor.comp` spelling is what keeps the unifier from unfolding the sheafification functor, and
`sheafificationTensorIso_inv_unit_tmul` is the *inverse* direction of
`sheafificationTensorIso_hom_unit_tmul`, obtained from it by `iso_inv_hom_app_apply` rather than
by a second descent argument.

**Vanishing in negative degrees is a separatedness argument, not a colimit argument.** A section
of a sheafification lifts along the unit on a covering sieve (`Stacks.liftSieve_mem`), the lift
is zero because the presheaf has no nonzero sections, and the target is separated
(`Stacks.eq_of_isSeparated`). No exactness property of sheafification is used, and in particular
nothing about preservation of zero objects.

**Universes.** In the graded-algebra half the site universes `u`, `v`, the ring universe `t` and
the module universe `a` are independent, exactly as in `Stacks.GradedAlgebra` and
`SheafOfModules.GradedAlgebra`. In the tensor-power half the module universe equals the ring
universe `w`, which is forced and not chosen: `SheafOfModules.tensorPower` is built from
`Stacks.SheafOfModules.Tensor.sheafTensor` and has the zeroth power the structure sheaf, whose
sections are the ring's. See the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras` for the same
point. Nothing here relates or specializes a universe beyond that.

**No `@[stacks]` tag.** Tag 0FQW is the definition of a sheaf of graded algebras, carried by
`SheafOfModules.GradedAlgebra`; Tag 0GMW is carried by
`PresheafOfModules.sheafificationTensorIso`; and Tag 01CG is the symmetric-power sheafification
statement, which is not proved here. Everything below is infrastructure for Section 17.21 rather
than the content of a tag.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules

open scoped TensorProduct

universe v u t a w

/-! ### Congruence and extensionality on sections -/

namespace SheafOfModules

section Congr

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- An equation between morphisms of sheaves of modules, read on sections. -/
theorem hom_congr_app_apply {M N : SheafOfModules.{a} R} {φ ψ : M ⟶ N} (h : φ = ψ) (X : Cᵒᵖ)
    (x : M.val.obj X) : φ.val.app X x = ψ.val.app X x := by rw [h]

/-- The inverse of an isomorphism of sheaves of modules undoes it on sections. -/
theorem iso_inv_hom_app_apply {M N : SheafOfModules.{a} R} (e : M ≅ N) (X : Cᵒᵖ)
    (x : M.val.obj X) : e.inv.val.app X (e.hom.val.app X x) = x :=
  hom_congr_app_apply e.hom_inv_id X x

end Congr

end SheafOfModules

/-! ### Homomorphisms of graded algebras of presheaves of modules -/

namespace Stacks

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}} {ι : Type} [AddMonoid ι]
  {P Q S : ι → PresheafOfModules.{a} R}

/-- A homomorphism of graded algebras of presheaves of modules: a morphism of presheaves of
modules in each degree, preserving products of homogeneous local sections. The distinguished
degree-zero unit need not be preserved; the homomorphisms that preserve it are `UnitalHom`.

This is the presheaf-level counterpart of `SheafOfModules.GradedAlgebra.Hom`. The two families
of homogeneous pieces are parameters rather than fields, so these homomorphisms do not form a
category: `Hom.id` and `Hom.comp` are the composition laws in the form they are available. -/
structure GradedAlgebra.Hom (A : GradedAlgebra P) (B : GradedAlgebra Q) where
  /-- The morphism of presheaves of modules in each degree. -/
  app (n : ι) : P n ⟶ Q n
  /-- Products of homogeneous local sections are preserved. -/
  map_mul (i j : ι) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X) :
    PresheafOfModules.Hom.app (app (i + j)) X ((A.mul i j).app X x y) =
      (B.mul i j).app X (PresheafOfModules.Hom.app (app i) X x)
        (PresheafOfModules.Hom.app (app j) X y)

/-- A unital homomorphism of graded algebras of presheaves of modules: a `Hom` which in addition
carries the degree-zero unit to the degree-zero unit. -/
structure GradedAlgebra.UnitalHom (A : GradedAlgebra P) (B : GradedAlgebra Q)
    extends GradedAlgebra.Hom A B where
  /-- The degree-zero unit is preserved. -/
  map_one (X : Cᵒᵖ) :
    PresheafOfModules.Hom.app (toHom.app 0) X (A.one.eval X) = B.one.eval X

namespace GradedAlgebra

variable {A : GradedAlgebra P} {B : GradedAlgebra Q} {D : GradedAlgebra S}

/-- Two homomorphisms of graded algebras of presheaves of modules agree as soon as all their
homogeneous components do. -/
@[ext]
theorem Hom.ext {f g : Hom A B} (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f; cases g; congr; funext n; exact h n

/-- Two unital homomorphisms agree as soon as all their homogeneous components do. -/
@[ext]
theorem UnitalHom.ext {f g : UnitalHom A B} (h : ∀ n, f.app n = g.app n) : f = g := by
  obtain ⟨f, _⟩ := f
  obtain ⟨g, _⟩ := g
  obtain rfl : f = g := Hom.ext h
  rfl

/-- The identity homomorphism of a graded algebra of presheaves of modules. -/
def Hom.id (A : GradedAlgebra P) : Hom A A where
  app _ := 𝟙 _
  map_mul _ _ _ _ _ := rfl

/-- Composition of homomorphisms of graded algebras of presheaves of modules. -/
def Hom.comp (f : Hom A B) (g : Hom B D) : Hom A D where
  app n := f.app n ≫ g.app n
  map_mul i j X x y := by
    change PresheafOfModules.Hom.app (g.app (i + j)) X
      (PresheafOfModules.Hom.app (f.app (i + j)) X _) = _
    rw [f.map_mul, g.map_mul]
    rfl

/-- The identity unital homomorphism. -/
def UnitalHom.id (A : GradedAlgebra P) : UnitalHom A A where
  toHom := Hom.id A
  map_one _ := rfl

/-- Composition of unital homomorphisms. -/
def UnitalHom.comp (f : UnitalHom A B) (g : UnitalHom B D) : UnitalHom A D where
  toHom := f.toHom.comp g.toHom
  map_one X := by
    change PresheafOfModules.Hom.app (g.app 0) X (PresheafOfModules.Hom.app (f.app 0) X _) = _
    rw [f.map_one, g.map_one]

/-- The identity homomorphism is the identity in every degree. -/
@[simp] theorem Hom.id_app (A : GradedAlgebra P) (n : ι) : (Hom.id A).app n = 𝟙 _ := rfl

/-- A composite homomorphism is the degreewise composite. -/
@[simp] theorem Hom.comp_app (f : Hom A B) (g : Hom B D) (n : ι) :
    (f.comp g).app n = f.app n ≫ g.app n := rfl

/-- The identity unital homomorphism is the identity in every degree. -/
@[simp] theorem UnitalHom.id_app (A : GradedAlgebra P) (n : ι) :
    (UnitalHom.id A).app n = 𝟙 _ := rfl

/-- A composite unital homomorphism is the degreewise composite. -/
@[simp] theorem UnitalHom.comp_app (f : UnitalHom A B) (g : UnitalHom B D) (n : ι) :
    (f.comp g).app n = f.app n ≫ g.app n := rfl

end GradedAlgebra

end Stacks

/-! ### Restriction of scalars of a sheaf of graded algebras -/

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}}

/-- **A sheaf of graded algebras over `R`, read as a graded algebra of presheaves of
`R₀`-modules along `α : R₀ ⟶ R.obj`.** The multiplication, the unit and the three laws are the
same data: only the sheaf conditions on the pieces are forgotten, and each scalar law is the old
one evaluated at the image of the scalar under `α`. -/
noncomputable def restrictScalars (B : GradedAlgebra.{t, a} R) (α : R₀ ⟶ R.obj) :
    Stacks.GradedAlgebra (fun n : ℤ =>
      (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).obj (B.piece n)) where
  mul i j :=
    { app := fun X => (B.mul i j).app X
      map_smul_left := fun X r x y => (B.mul i j).map_smul_left X (α.app X r) x y
      map_smul_right := fun X r x y => (B.mul i j).map_smul_right X (α.app X r) x y
      naturality := fun f x y => (B.mul i j).naturality f x y }
  one := PresheafOfModules.sectionsMk (fun X => B.one.eval X) fun {_ _} f =>
    PresheafOfModules.sections_property B.one f
  mul_assoc i j k X x y z := B.mul_assoc i j k X x y z
  one_mul i X x := B.one_mul i X x
  mul_one i X x := B.mul_one i X x

/-- The multiplication of `B.restrictScalars α` is that of `B` on sections. -/
theorem restrictScalars_mul_app (B : GradedAlgebra.{t, a} R) (α : R₀ ⟶ R.obj) (i j : ℤ)
    (X : Cᵒᵖ) (x : (B.piece i).val.obj X) (y : (B.piece j).val.obj X) :
    ((B.restrictScalars α).mul i j).app X x y = (B.mul i j).app X x y := rfl

/-- The unit of `B.restrictScalars α` has the same sections as the unit of `B`. -/
theorem restrictScalars_one_eval (B : GradedAlgebra.{t, a} R) (α : R₀ ⟶ R.obj) (X : Cᵒᵖ) :
    (B.restrictScalars α).one.eval X = B.one.eval X := rfl

end SheafOfModules.GradedAlgebra

/-! ### Sections of a sheafification -/

namespace PresheafOfModules

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]

/-- `PresheafOfModules.sheafification_hom_ext` read on sections: two morphisms out of the
sheafification of a presheaf of modules are equal as soon as they agree on the unit images of
local sections. -/
theorem sheafification_hom_ext_apply {M : PresheafOfModules.{a} R₀} {N : SheafOfModules.{a} R}
    {f g : (sheafification α).obj M ⟶ N}
    (h : ∀ (X : Cᵒᵖ) (s : M.obj X),
      f.val.app X (PresheafOfModules.Hom.app (sheafifyUnit α M) X s) =
        g.val.app X (PresheafOfModules.Hom.app (sheafifyUnit α M) X s)) : f = g :=
  sheafification_hom_ext (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun s => h X s))

/-- **The sheafification of a presheaf of modules with no nonzero sections has no nonzero
sections.** A section of the sheafification lifts along the unit on a covering sieve, every lift
is zero, and the sheafification is separated. -/
theorem sheafification_section_eq_zero (M : PresheafOfModules.{a} R₀)
    (hM : ∀ (X : Cᵒᵖ) (m : M.obj X), m = 0) {X : Cᵒᵖ}
    (s : ((sheafification α).obj M).val.obj X) : s = 0 := by
  refine Stacks.eq_of_isSeparated ((sheafification α).obj M) (Stacks.liftSieve_mem α M s) ?_
  rintro Y f ⟨m, hm⟩
  have hm' : PresheafOfModules.Hom.app (sheafifyUnit α M) (op Y) m =
    ((sheafification α).obj M).val.map f.op s := hm
  rw [← hm', hM (op Y) m, map_zero, map_zero]
  rfl

end Sheafify

end PresheafOfModules

/-! ### The universal property of a sheafified graded algebra -/

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {P : ℤ → PresheafOfModules.{a} R₀} (A : GradedAlgebra P)
  {B : SheafOfModules.GradedAlgebra.{t, a} R}

/-- **A unital homomorphism out of a sheafified graded algebra, restricted along the
sheafification units.** This is the converse of `Stacks.GradedAlgebra.existsUnique_desc`, and it
is what makes the uniqueness half of `isUniversal_sheafify` available. -/
noncomputable def restrictUnitalHom
    (h : SheafOfModules.GradedAlgebra.UnitalHom (A.sheafify α) B) :
    UnitalHom A (B.restrictScalars α) where
  app n := sheafifyUnit α (P n) ≫
    (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α).map (h.app n)
  map_mul i j X x y := by
    have hm := h.map_mul i j X (PresheafOfModules.Hom.app (sheafifyUnit α (P i)) X x)
      (PresheafOfModules.Hom.app (sheafifyUnit α (P j)) X y)
    rw [A.sheafify_mul_unit α i j X x y] at hm
    exact hm
  map_one X := by
    have hm := h.map_one X
    rw [A.sheafify_one_eval α X] at hm
    exact hm

/-- In degree `n`, `A.restrictUnitalHom α h` sends a section `s` to the image under `h.app n` of
its image in the sheafification. -/
@[simp]
theorem restrictUnitalHom_app_apply
    (h : SheafOfModules.GradedAlgebra.UnitalHom (A.sheafify α) B) (n : ℤ) (X : Cᵒᵖ)
    (s : (P n).obj X) :
    PresheafOfModules.Hom.app ((A.restrictUnitalHom α h).app n) X s =
      (h.app n).val.app X (PresheafOfModules.Hom.app (sheafifyUnit α (P n)) X s) := rfl

/-- **A degree in which the sectionwise algebra has no sections is a degree in which its
sheafification has none.** This is the form in which the three algebras of Section 17.21 are
concentrated in nonnegative degrees. -/
theorem sheafify_piece_eq_zero (n : ℤ) (hP : ∀ (X : Cᵒᵖ) (m : (P n).obj X), m = 0) (X : Cᵒᵖ)
    (x : ((A.sheafify α).piece n).val.obj X) : x = 0 :=
  PresheafOfModules.sheafification_section_eq_zero α (P n) hP x

section Universal

variable {F : PresheafOfModules.{a} R₀} (gen : F ⟶ P 1)
  (Pr : ∀ B : SheafOfModules.GradedAlgebra.{t, a} R,
    ((sheafification α).obj F ⟶ B.piece 1) → Prop)

/-- **The universal property of a sheafified graded algebra.** Let `A` be a graded algebra of
presheaves of modules with a degree-one generator `gen : F ⟶ P 1`, and let `Pr` be a property of
degree-one generators of sheaves of graded algebras. If

* the sheafified generator has `Pr`, and
* for every sheaf of graded algebras `B` and every degree-one generator `κ` of `B` with `Pr`
  there is a *unique* unital homomorphism `A ⟶ B|_{R₀}` of graded algebras of presheaves
  carrying `gen` to `κ`, read on the unit images of local sections,

then the sheafification of `A` with the sheafified generator is universal for `Pr`.

Taking `Pr = fun _ _ => True`, `SquareZero` and `PairwiseCommutes` this is
`SheafOfModules.GradedAlgebra.IsTensorAlgebra`, `IsExteriorAlgebra` and `IsSymmetricAlgebra` for
the sheafification; for the latter two the first hypothesis is
`Stacks.GradedAlgebra.squareZero_sheafifyGen` and `pairwiseCommutes_sheafifyGen`. -/
theorem isUniversal_sheafify
    (hgen : Pr (A.sheafify α) (A.sheafifyGen α gen))
    (huniv : ∀ (B : SheafOfModules.GradedAlgebra.{t, a} R)
      (κ : (sheafification α).obj F ⟶ B.piece 1), Pr B κ →
      ∃! g : UnitalHom A (B.restrictScalars α), ∀ (X : Cᵒᵖ) (s : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X (PresheafOfModules.Hom.app gen X s) =
          κ.val.app X (PresheafOfModules.Hom.app (sheafifyUnit α F) X s)) :
    SheafOfModules.GradedAlgebra.IsUniversal Pr (A.sheafify α) (A.sheafifyGen α gen) := by
  refine ⟨hgen, fun B κ hκ => ?_⟩
  obtain ⟨g, hg, hgu⟩ := huniv B κ hκ
  obtain ⟨hh, hhspec, hhu⟩ := A.existsUnique_desc α g.app g.map_mul g.map_one
  refine ⟨hh, sheafification_hom_ext_apply α fun X s => ?_, fun h' hh' => ?_⟩
  · rw [show (A.sheafifyGen α gen ≫ hh.app 1).val.app X
        (PresheafOfModules.Hom.app (sheafifyUnit α F) X s) =
      (hh.app 1).val.app X ((A.sheafifyGen α gen).val.app X
        (PresheafOfModules.Hom.app (sheafifyUnit α F) X s)) from rfl,
      A.sheafifyGen_unit α gen X s, hhspec 1 X (PresheafOfModules.Hom.app gen X s), hg X s]
  · have hgg : A.restrictUnitalHom α h' = g := hgu _ fun X s => by
      rw [restrictUnitalHom_app_apply, ← A.sheafifyGen_unit α gen X s]
      exact SheafOfModules.hom_congr_app_apply hh' X
        (PresheafOfModules.Hom.app (sheafifyUnit α F) X s)
    exact hhu h' fun n X s => by rw [← hgg]; rfl

/-- The tensor-algebra instance of `Stacks.GradedAlgebra.isUniversal_sheafify`: the
sheafification of a sectionwise graded algebra which is initial among restrictions of scalars,
with no side condition on the generator, is the tensor algebra of the sheafified generator. -/
theorem isTensorAlgebra_sheafify
    (huniv : ∀ (B : SheafOfModules.GradedAlgebra.{t, a} R)
      (κ : (sheafification α).obj F ⟶ B.piece 1),
      ∃! g : UnitalHom A (B.restrictScalars α), ∀ (X : Cᵒᵖ) (s : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X (PresheafOfModules.Hom.app gen X s) =
          κ.val.app X (PresheafOfModules.Hom.app (sheafifyUnit α F) X s)) :
    SheafOfModules.GradedAlgebra.IsTensorAlgebra (A.sheafify α) (A.sheafifyGen α gen) :=
  A.isUniversal_sheafify α gen (fun _ _ => True) trivial fun B κ _ => huniv B κ

/-- The exterior-algebra instance of `Stacks.GradedAlgebra.isUniversal_sheafify`. The first
hypothesis is the sectionwise square-zero condition, which
`Stacks.GradedAlgebra.squareZero_sheafifyGen` transfers to the sheafification. -/
theorem isExteriorAlgebra_sheafify
    (hsq : ∀ (X : Cᵒᵖ) (x : F.obj X),
      (A.mul 1 1).app X (PresheafOfModules.Hom.app gen X x)
        (PresheafOfModules.Hom.app gen X x) = 0)
    (huniv : ∀ (B : SheafOfModules.GradedAlgebra.{t, a} R)
      (κ : (sheafification α).obj F ⟶ B.piece 1),
      SheafOfModules.GradedAlgebra.SquareZero κ →
      ∃! g : UnitalHom A (B.restrictScalars α), ∀ (X : Cᵒᵖ) (s : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X (PresheafOfModules.Hom.app gen X s) =
          κ.val.app X (PresheafOfModules.Hom.app (sheafifyUnit α F) X s)) :
    SheafOfModules.GradedAlgebra.IsExteriorAlgebra (A.sheafify α) (A.sheafifyGen α gen) :=
  A.isUniversal_sheafify α gen (fun _ κ => SheafOfModules.GradedAlgebra.SquareZero κ)
    (A.squareZero_sheafifyGen α gen hsq) huniv

/-- The symmetric-algebra instance of `Stacks.GradedAlgebra.isUniversal_sheafify`. The first
hypothesis is the sectionwise commutation condition, which
`Stacks.GradedAlgebra.pairwiseCommutes_sheafifyGen` transfers to the sheafification. -/
theorem isSymmetricAlgebra_sheafify
    (hc : ∀ (X : Cᵒᵖ) (x y : F.obj X),
      (A.mul 1 1).app X (PresheafOfModules.Hom.app gen X x)
          (PresheafOfModules.Hom.app gen X y) =
        (A.mul 1 1).app X (PresheafOfModules.Hom.app gen X y)
          (PresheafOfModules.Hom.app gen X x))
    (huniv : ∀ (B : SheafOfModules.GradedAlgebra.{t, a} R)
      (κ : (sheafification α).obj F ⟶ B.piece 1),
      SheafOfModules.GradedAlgebra.PairwiseCommutes κ →
      ∃! g : UnitalHom A (B.restrictScalars α), ∀ (X : Cᵒᵖ) (s : F.obj X),
        PresheafOfModules.Hom.app (g.app 1) X (PresheafOfModules.Hom.app gen X s) =
          κ.val.app X (PresheafOfModules.Hom.app (sheafifyUnit α F) X s)) :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra (A.sheafify α) (A.sheafifyGen α gen) :=
  A.isUniversal_sheafify α gen (fun _ κ => SheafOfModules.GradedAlgebra.PairwiseCommutes κ)
    (A.pairwiseCommutes_sheafifyGen α gen hc) huniv

end Universal

end Stacks.GradedAlgebra

/-! ### The tensor-power comparison -/

namespace PresheafOfModules

section Bridges

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The tensor product bifunctor on sheaves of modules, on a morphism, read on the unit image
of a pure tensor.** The proof goes through `tensorSheafBifunctor_map`, whose `Functor.comp`
spelling of the right-hand side is what keeps the unifier from unfolding the sheafification
functor. -/
theorem tensorSheafBifunctor_map_unit_tmul
    {M₁ M₂ N₁ N₂ : SheafOfModules.{w} (toRingCat J Osharp)} (fg : (M₁, N₁) ⟶ (M₂, N₂))
    (X : Cᵒᵖ) (x : M₁.val.obj X) (y : N₁.val.obj X) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map fg.1).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).map fg.2)).val.app X
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
            Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj M₁.val N₁.val)) X (x ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj M₂.val N₂.val)) X
        (fg.1.val.app X x ⊗ₜ fg.2.val.app X y) := by
  refine (hom_congr_apply'
    (congrArg (SheafOfModules.forget
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)).map
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Osharp fg.1 fg.2)) X
    (((sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
        (tensorObj M₁.val N₁.val)).app X (x ⊗ₜ y))).trans ?_
  refine (unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    (tensorHom fg.1.val fg.2.val)
    X (x ⊗ₜ y)).trans ?_
  exact congrArg (fun z => Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
      Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj M₂.val N₂.val)) X z)
    (tensorHom_tmul fg.1.val fg.2.val X x y)

/-- **Stacks Project, Tag 0GMW, in the inverse direction.** The inverse of the comparison
isomorphism carries the unit image of a pure tensor of local sections to the unit image of the
pure tensor of their unit images. -/
theorem sheafificationTensorIso_inv_unit_tmul
    (F G : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
    (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    ((sheafificationTensorIso J a).app (F, G)).inv.val.app X
        (Hom.app (moduleSheafificationUnit J a (tensorObj F G)) X (x ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R :=
          Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj ((moduleSheafification J a).obj F).val ((moduleSheafification J
          a).obj G).val)) X
        (Hom.app (moduleSheafificationUnit J a F) X x ⊗ₜ
          Hom.app (moduleSheafificationUnit J a G) X y) := by
  rw [← sheafificationTensorIso_hom_unit_tmul J a F G X x y]
  exact SheafOfModules.iso_inv_hom_app_apply ((sheafificationTensorIso J a).app (F, G)) X _

end Bridges

end PresheafOfModules

namespace SheafOfModules

section TensorPower

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The sheafified sectionwise tensor powers are the tensor powers.** Let `Q` be a family of
presheaves of modules whose sheafification in degree `0` is the structure sheaf, whose
sheafification in degree `1` is `F`, and which satisfies the tensor-power recursion
`Q (n + 2) ≅ Q 1 ⊗ Q (n + 1)` sectionwise. Then the sheafification of `Q n` is the `n`-fold
tensor power of `F`.

The step from `n + 1` to `n + 2` is Tag 0GMW (`PresheafOfModules.sheafificationTensorIso`)
followed by the tensor bifunctor applied to the degree-one identification and the inductive one;
`tensorPowerSheafifyIso_add_two_unit` reads the result on pure tensors. -/
noncomputable def tensorPowerSheafifyIso
    {Q : ℕ → PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
    {F : SheafOfModules.{w} (toRingCat J Osharp)}
    (e0 : (moduleSheafification J a).obj (Q 0) ≅ SheafOfModules.unit (toRingCat J Osharp))
    (e1 : (moduleSheafification J a).obj (Q 1) ≅ F)
    (e2 : ∀ n : ℕ, Q (n + 2) ≅ tensorObj (Q 1) (Q (n + 1))) :
    ∀ n : ℕ, (moduleSheafification J a).obj (Q n) ≅ tensorPower J F n
  | 0 => e0
  | 1 => e1
  | (n + 2) =>
      (moduleSheafification J a).mapIso (e2 n) ≪≫
        ((sheafificationTensorIso J a).app (Q 1, Q (n + 1))).symm ≪≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).mapIso e1).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).mapIso (tensorPowerSheafifyIso e0 e1
          e2 (n + 1)))

variable {Q : ℕ → PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
  {F : SheafOfModules.{w} (toRingCat J Osharp)}
  (e0 : (moduleSheafification J a).obj (Q 0) ≅ SheafOfModules.unit (toRingCat J Osharp))
  (e1 : (moduleSheafification J a).obj (Q 1) ≅ F)
  (e2 : ∀ n : ℕ, Q (n + 2) ≅ tensorObj (Q 1) (Q (n + 1)))

/-- In degree zero, `tensorPowerSheafifyIso` is `e0`. -/
theorem tensorPowerSheafifyIso_zero : tensorPowerSheafifyIso J a e0 e1 e2 0 = e0 := rfl

/-- In degree one, `tensorPowerSheafifyIso` is `e1`. -/
theorem tensorPowerSheafifyIso_one : tensorPowerSheafifyIso J a e0 e1 e2 1 = e1 := rfl

/-- In degree `n + 2`, `tensorPowerSheafifyIso` is the composite of the sheafification of `e2 n`,
the inverse of the sheafification-tensor comparison, and the tensor product of `e1` with the
isomorphism in degree `n + 1`. -/
theorem tensorPowerSheafifyIso_add_two (n : ℕ) :
    tensorPowerSheafifyIso J a e0 e1 e2 (n + 2) =
      (moduleSheafification J a).mapIso (e2 n) ≪≫
        ((sheafificationTensorIso J a).app (Q 1, Q (n + 1))).symm ≪≫
          (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).mapIso e1).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).mapIso (tensorPowerSheafifyIso J a
          e0 e1 e2 (n + 1))) := rfl

/-- **The tensor-power comparison on pure tensors.** If a local section of `Q (n + 2)` is the
pure tensor `x ⊗ₜ y` under the recursion isomorphism, then the comparison carries its unit image
to the pure tensor of the images of the unit images of `x` and `y`. Since the unit images of
pure tensors generate locally, this is the equation that determines
`tensorPowerSheafifyIso`. -/
theorem tensorPowerSheafifyIso_add_two_unit (n : ℕ) (X : Cᵒᵖ) (z : (Q (n + 2)).obj X)
    (x : (Q 1).obj X) (y : (Q (n + 1)).obj X)
    (hz : PresheafOfModules.Hom.app (e2 n).hom X z = x ⊗ₜ y) :
    (tensorPowerSheafifyIso J a e0 e1 e2 (n + 2)).hom.val.app X
        (PresheafOfModules.Hom.app (moduleSheafificationUnit J a (Q (n + 2))) X z) =
      PresheafOfModules.Hom.app
        ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf
            Osharp)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj F.val (tensorPower J F (n + 1)).val)) X
        (e1.hom.val.app X
            (PresheafOfModules.Hom.app (moduleSheafificationUnit J a (Q 1)) X x) ⊗ₜ
          (tensorPowerSheafifyIso J a e0 e1 e2 (n + 1)).hom.val.app X
            (PresheafOfModules.Hom.app (moduleSheafificationUnit J a (Q (n + 1))) X y)) := by
  have h1 := (unit_naturality_apply (α := toRingCatMap J a) (e2 n).hom X z).trans
    (congrArg
      (fun z => PresheafOfModules.Hom.app
        (moduleSheafificationUnit J a (tensorObj (Q 1) (Q (n + 1)))) X z) hz)
  change ((((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map ((Iso.prod e1
      (tensorPowerSheafifyIso J a e0 e1 e2 (n + 1))).hom).1).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj _).map ((Iso.prod e1
          (tensorPowerSheafifyIso J a e0 e1 e2 (n + 1))).hom).2)).val.app X
    (((sheafificationTensorIso J a).app (Q 1, Q (n + 1))).inv.val.app X
      (((moduleSheafification J a).map (e2 n).hom).val.app X
        (PresheafOfModules.Hom.app (moduleSheafificationUnit J a (Q (n + 2))) X z))) = _
  rw [h1, sheafificationTensorIso_inv_unit_tmul]
  exact tensorSheafBifunctor_map_unit_tmul J
    (Iso.prod e1 (tensorPowerSheafifyIso J a e0 e1 e2 (n + 1))).hom X _ _

end TensorPower

end SheafOfModules
