module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalRightUnitorCompare
public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.SheafOfModules
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PullbackMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence

/-!
# The addition law on tensor powers, at the tensor product sheaf

Let `𝒪` be a sheaf of commutative rings on a site and `L` an invertible sheaf of `𝒪`-modules.
`AlgebraicGeometry.SheafOfModules.tensorPowAddIso` is the addition law
`L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` of Stacks Tag 01CU for the *localized* monoidal structure
`Stacks.SheafInternalHom.monoidalCategory`, and
`StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/SheafOfModules.lean` proves its associativity
constraint there, in nonnegative degree. `AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf`
— the spelling `Stacks.Ample.tensorPowModuleAddIso`, and hence the whole ampleness and twist
calculus, is written in — has the tensor product *sheaf* of Stacks Tag 01CA as its source, which
is the tensor product of the **strict** monoidal structure
`Stacks.SheafOfModules.Strict.monoidalCategory`. No associativity constraint was available at
that spelling, while the canonical multiplication of the twists on the degree `d` open is:
`Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_assoc` is stated there.

This file transports the constraint across, so that the two sides of a graded multiplicativity
square can be written in one monoidal structure.

## Main results

* `Stacks.AlgebraicGeometry.ThetaMul.addIsoSheaf_assoc`: **the associativity constraint of the
  addition law with the tensor product sheaf as source**, in nonnegative degree, against the
  associator of `Stacks.SheafOfModules.Strict.monoidalCategory`.
* `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc`: the same for a scheme, in the
  vocabulary `Stacks.Ample.tensorPowModuleAddIso` and
  `Stacks.RelativeVeryAmple.tensorModules` of the ampleness theory.
* `Stacks.AlgebraicGeometry.ThetaMul.addIsoSheaf_zero_left`: **the left unit constraint of the
  addition law with the tensor product sheaf as source**, against the left unitor of
  `Stacks.SheafOfModules.Strict.monoidalCategory`, and
  `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left`: the same for a scheme.
  Together with `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_one_left` on the twist side
  these are the two unit laws the degree-one value of
  `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta` is pinned down by.
* `Stacks.AlgebraicGeometry.ThetaMul.addIsoSheaf_zero_right` and
  `tensorPowModuleAddIso_zero_right`: **the right unit constraint of the same addition law**,
  against the right unitor; with
  `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_one_right` these are the two unit laws the
  multiplicativity square in a bidegree whose second entry is zero rests on.
* `Stacks.AlgebraicGeometry.ThetaMul.rightUnitor_monoidalCategory_hom`: the two localizations of
  the monoidal structure on sheaves of modules have the same right unitor up to the comparison of
  their units — the mirror, on a site, of
  `AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom`.
* `Stacks.AlgebraicGeometry.ThetaMul.twistMulIso_assoc`: **associativity of the canonical
  multiplication isomorphism of the degree `d` open of Stacks Tag 01N5**, read at the same
  monoidal structure, so that the two sides of a graded multiplicativity square for
  `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat` are now stated against one
  associator.
* `Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom`: the functorial action of the
  tensor product sheaf on a pair of isomorphisms is the monoidal tensor product of their forward
  maps. This converts between the two ways the calculus writes a map of a tensor product.
* `Stacks.AlgebraicGeometry.ThetaMul.tensorIso_eq`: the two comparison isomorphisms between the
  localized tensor product and the tensor product sheaf agree.
* `Stacks.AlgebraicGeometry.ThetaMul.twistMulIso_zero_left`: **the left unit law of the canonical
  multiplication isomorphism of the degree `d` open**, read at the same monoidal structure.
* `Stacks.AlgebraicGeometry.ThetaMul.theta_one_eq`: **the degree one value of the comparison
  family `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta` is the canonical
  identification `𝒪_{U_d}(d)^{⊗ 1} ≅ 𝒪_{U_d}(d · 1)`**, which is what the two left unit laws pin
  down.
* `Stacks.AlgebraicGeometry.ThetaMul.theta_mul` and
  `Stacks.AlgebraicGeometry.ThetaMul.thetaNat_mul`: **the multiplicativity square of the
  comparison family in an arbitrary bidegree `(n, m)`**, the second with every twist degree
  spelled as the `d`-th Veronese section ring spells it. Both degrees are arbitrary natural
  numbers: the positive ones come from the associativity step and the bidegree `(n, 0)` from the
  two right unit laws, as `theta_mul_zero_nat`.

## Implementation notes

**Three obstacles, none of them the mathematics.**

First, the library carries *two* localizations of the monoidal structure on presheaves of
modules: `Stacks.SheafInternalHom.monoidalCategory`, whose unit is the sheafification of the
presheaf unit, and `Stacks.SheafOfModules.monoidalCategory`, whose unit is
`SheafOfModules.unit`. They are not equal — their unit objects differ, which is what
`AlgebraicGeometry.SheafOfModules.unitIso` compares — but their tensor product, whiskerings and
associator are definitionally the same. The conjugation lemmas
`Stacks.SheafOfModules.Strict.whiskerRight_eq`, `whiskerLeft_eq` and `associator_eq` are stated
at the second while the tensor powers live at the first, so `str_whiskerRight`,
`str_whiskerLeft` and `str_associator` below are those three lemmas read at the first spelling,
each by `rfl`.

Second, `tensorPowAddIsoSheaf` is built from `AlgebraicGeometry.SheafOfModules.tensorIso` while
the conjugation lemmas are stated with `Stacks.SheafOfModules.tensorObjIso`. The two
isomorphisms agree, but only their forward maps agree by `rfl`; `tensorIso_eq` is `Iso.ext` of
that, which is what makes the inverses agree too.

Third — and this is the step that makes the difference between a proof and a wall of stuck
`simp` calls — a composite of a morphism typed at one of the two localized tensor products with
a morphism typed at the other is type-correct only at *default* transparency. The simplifier
checks the type-correctness of its congruence steps at `instances` transparency, so on such a
composite every one of them silently fails, including `Category.assoc` and
`Iso.hom_inv_id_assoc`. `addIsoLoc` is the addition law retyped by ascription at the second
spelling; after that retyping every term in sight is type-correct at the transparency the
simplifier works at, and the computation is the one `simp only` in `addIsoSheaf_assoc`.

**What the computation is.** Both composites are conjugated into the localized structure by the
comparison isomorphism; the conjugating factors cancel in pairs, and what is left is
`AlgebraicGeometry.SheafOfModules.tensorPowAddIso_assoc_natCast`. Nothing about tensor powers is
re-proved.

**The unitors are the structural morphisms the two localizations do not share** — they are where
the choice of unit object enters — so `str_leftUnitor` is not the end of the matter: it expresses
the strict left unitor through the
left unitor of `Stacks.SheafOfModules.monoidalCategory`, and
`AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom` is then what carries that to the left
unitor of `Stacks.SheafInternalHom.monoidalCategory`, the one
`AlgebraicGeometry.SheafOfModules.tensorPowAddIso_zero_left_natCast` is stated at. The two
cancellations the computation needs are done by `str_whiskerRight_leftUnitor` and
`whiskerRight_comp_cancel`, both stated with the objects as *variables*: at the concrete objects
`tensorPow 𝒪 h𝒪 L 0` and `𝟙_`, which are equal by `rfl` and not syntactically, neither `rw` nor
`simp` will perform them.

**The same device carries the whole multiplicativity argument.** `unit_tensorHom_cancel`,
`tensorHom_unit_square` and `square_step` are the three computations the comparison family needs —
the degree one value out of the two left unit laws, the bidegree `(n, 0)` square out of the two
right unit laws, and the bidegree `(n, m + 1)` square out of the bidegree `(n, m)` square and the
two associativity constraints — stated in an abstract monoidal category with every object a
variable. At the concrete objects the degrees `d · ↑n + d · ↑m` and `d · ↑(n + m)` are equal by
`rfl` and not syntactically, so a `rw` or `simp` proof of either computation does not get off the
ground, while `exact` unifies them at default transparency. The transports that the
associativity constraints carry are identities in the third degree `1`, and
`comp_comp_comp_eq_self` removes them for the same reason.

Because every object in them is a variable, these five computations and `comp_cancel_left` say
nothing about the degree `d` open and are *not* `private`:
`StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaGlobalMultiplicativity` runs the same induction
for the comparison family of `Stacks.AlgebraicGeometry.ThetaGlobal` on all of `Proj S` and uses
them unchanged.

**Natural-number spellings are retypings.** `thetaStepNat`, `twistMulIsoNat` and
`twistMulIsoVeronese` are `def`s whose bodies are the existing addition law and multiplication
isomorphism with nothing changed but the ascribed type: the source read at the tensor product of
`schemeMonoidal` rather than at `Stacks.RelativeVeryAmple.tensorModules`, and the degrees read as
natural numbers. The ascription is what keeps the kernel's work on each statement to one
comparison of the two tensor products instead of one per occurrence.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the tensor powers of an
  invertible sheaf of modules and their canonical multiplication.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules, with its associator.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.RelativeVeryAmple
open Stacks.SheafOfModules.TensorSheafification

namespace Stacks.AlgebraicGeometry.ThetaMul

universe u w

section UnitComparison

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- Inserting an arrow known to be an identity into a composite. Isolated as a lemma because the
statement below mentions both unit objects at once and is not type-correct at the transparency
`rw` checks its motive at. -/
private theorem comp_id_comp {D : Type*} [Category D] {A B E : D} (a : A ⟶ B) (i : B ⟶ B)
    (hi : i = 𝟙 B) (r : B ⟶ E) : a ≫ r = a ≫ i ≫ r := by rw [hi, Category.id_comp]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

/-- **The two localized monoidal structures on sheaves of `𝒪`-modules have the same right unitor
up to the comparison of their units.** They localize the same monoidal structure on presheaves of
modules along the same sheafification and differ only in the chosen unit object, so the two right
unitors differ by `AlgebraicGeometry.SheafOfModules.unitIso` whiskered into the second variable.

The mirror of `AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom`, which is stated on a
site; `AlgebraicGeometry.rightUnitor_sheafOfModulesMonoidal_hom` is this statement for the
modules of a scheme. -/
theorem rightUnitor_monoidalCategory_hom (M : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    (MonoidalCategoryStruct.rightUnitor (self :=
        (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪).toMonoidalCategoryStruct) M).hom =
      M ◁ (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv ≫ (ρ_ M).hom := by
  refine comp_id_comp (M ◁ (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).inv)
    (M ◁ 𝟙 _) ?_ _
  exact MonoidalCategory.whiskerLeft_id M _

end UnitComparison

section Bridge

/-- Two morphisms whose composite is the identity, each whiskered into the same object, cancel.
Isolated as a lemma in an abstract monoidal category: the two morphisms below are the forward and
backward map of one and the same isomorphism under two different names, and at the concrete
objects of this file `rw` will not see that, while here the objects are variables.

Public because `StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerBidegree.lean` held a
second copy of this statement, named `whiskerRight_cancel_mid`, until it was deleted in favour
of this one. -/
theorem whiskerRight_comp_cancel {D : Type*} [Category D] [MonoidalCategory D]
    {A B Z W : D} (p : A ⟶ B) (q : B ⟶ A) (hpq : p ≫ q = 𝟙 A) (m : A ⊗ Z ⟶ W) :
    p ▷ Z ≫ q ▷ Z ≫ m = m := by
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hpq,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- The same cancellation in the second variable. -/
theorem whiskerLeft_comp_cancel {D : Type*} [Category D] [MonoidalCategory D]
    {A B W : D} (Z : D) (p : A ⟶ B) (q : B ⟶ A) (hpq : p ≫ q = 𝟙 A) (m : Z ⊗ A ⟶ W) :
    Z ◁ p ≫ Z ◁ q ≫ m = m := by
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hpq,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- A composite whose last factor is a morphism from an object to itself known to be the
identity. The transports between two spellings of one degree are of that kind, and at the
concrete objects they are not syntactically identities, so `rw` will not remove them. -/
theorem comp_comp_eq_self {C : Type*} [Category C] {A E B : C} (u : A ⟶ E) (f : E ⟶ B)
    (i : B ⟶ B) (hi : i = 𝟙 B) : u ≫ f ≫ i = u ≫ f := by rw [hi, Category.comp_id]

/-- The same for a four-fold composite, which is the shape of the right-hand side of an
associativity constraint: associator, whiskering, multiplication, transport. -/
theorem comp_comp_comp_eq_self {C : Type*} [Category C] {A E F B : C} (u : A ⟶ E)
    (v : E ⟶ F) (f : F ⟶ B) (i : B ⟶ B) (hi : i = 𝟙 B) : u ≫ v ≫ f ≫ i = u ≫ v ≫ f := by
  rw [hi, Category.comp_id]

/-- The same with the identity in the middle of a composite. -/
theorem comp_cancel_left {C : Type*} [Category C] {A B E : C} (f : A ⟶ B) (i : B ⟶ B)
    (hi : i = 𝟙 B) (g : B ⟶ E) : (f ≫ i) ≫ g = f ≫ g := by rw [hi, Category.comp_id]

/-- **One unit law of a tensor product of morphisms, in an abstract monoidal category.** If `q`
lands in the unit object, if `w` out of it satisfies the unit law `w ▷ T ≫ μ = (λ_ T).hom ≫ tr'`
for a multiplication `μ` and a transport `tr'` inverse to `tr`, and if `q ▷ P` followed by the
left unitor is a splitting `stp` inverted by `stpi`, then the tensor product of `q ≫ w` with a
morphism `θ` is, after `stpi` in front and `μ ≫ tr` behind, just `θ`.

The computation is a whisker exchange, naturality of the left unitor, and two cancellations.
Isolated with the objects as variables: at the concrete objects of the degree `d` open the two
spellings of the zeroth tensor power and of the unit object are equal by `rfl` and not
syntactically, so neither `rw` nor `simp` performs any of these steps. -/
theorem unit_tensorHom_cancel {D : Type*} [Category D] [MonoidalCategory D]
    {A Z P T M : D} (q : A ⟶ 𝟙_ D) (w : 𝟙_ D ⟶ Z) (θ : P ⟶ T)
    (map : A ⊗ P ⟶ Z ⊗ T) (μ : Z ⊗ T ⟶ M) (tr : M ⟶ T) (tr' : T ⟶ M)
    (stpi : P ⟶ A ⊗ P) (stp : A ⊗ P ⟶ P)
    (hmap : map = (q ≫ w) ⊗ₘ θ)
    (hunit : w ▷ T ≫ μ = (λ_ T).hom ≫ tr')
    (htr : tr' ≫ tr = 𝟙 T)
    (hzero : q ▷ P ≫ (λ_ P).hom = stp)
    (hstep : stpi ≫ stp = 𝟙 P) :
    stpi ≫ map ≫ μ ≫ tr = θ := by
  have hu : w ▷ T ≫ μ ≫ tr = (λ_ T).hom := by
    rw [← Category.assoc, hunit, Category.assoc, htr, Category.comp_id]
  subst hmap
  rw [MonoidalCategory.tensorHom_def', MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [hu, ← Category.assoc (A ◁ θ), MonoidalCategory.whisker_exchange]
  simp only [Category.assoc]
  rw [MonoidalCategory.leftUnitor_naturality, ← Category.assoc (q ▷ P) (λ_ P).hom θ, hzero,
    ← Category.assoc, hstep, Category.id_comp]

/-- **The other unit law of a tensor product of morphisms, in an abstract monoidal category.** If
`q` lands in the unit object, if `w` out of it satisfies the unit law
`T ◁ w ≫ μ = (ρ_ T).hom ≫ tr` for a multiplication `μ` and a transport `tr`, and if `P ◁ q`
followed by the right unitor is a splitting `stp`, then the square relating `stp` to `μ` along the
tensor product of `θ` with `q ≫ w` commutes, up to that transport.

The mirror of `unit_tensorHom_cancel`: a whisker exchange, naturality of the right unitor, and
the splitting. Isolated with the objects as variables for the same reason — at the concrete
objects the two spellings of the zeroth tensor power and of the unit object are equal by `rfl` and
not syntactically. -/
theorem tensorHom_unit_square {D : Type*} [Category D] [MonoidalCategory D]
    {A P T Z M : D} (q : A ⟶ 𝟙_ D) (w : 𝟙_ D ⟶ Z) (θ : P ⟶ T)
    (map : P ⊗ A ⟶ T ⊗ Z) (μ : T ⊗ Z ⟶ M) (tr : T ⟶ M) (stp : P ⊗ A ⟶ P)
    (hmap : map = θ ⊗ₘ (q ≫ w))
    (hunit : T ◁ w ≫ μ = (ρ_ T).hom ≫ tr)
    (hzero : P ◁ q ≫ (ρ_ P).hom = stp) :
    stp ≫ θ ≫ tr = map ≫ μ := by
  subst hmap
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [hunit, ← Category.assoc (θ ▷ A), ← MonoidalCategory.whisker_exchange]
  simp only [Category.assoc]
  rw [← Category.assoc (θ ▷ 𝟙_ D), MonoidalCategory.rightUnitor_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (P ◁ q) (ρ_ P).hom (θ ≫ tr), hzero]

/-- **Three commuting squares out of an associativity diagram force the fourth**, in an abstract
monoidal category. Given two multiplications `(a, p, r)` and `(a', p', r')` that are associative
against the same associator, and a degreewise comparison `(f, g, h, fg, gh, fgh)` whose squares
commute at `(A, B)`, at `(AB, C)` and at `(B, C)`, the square at `(A, BC)` commutes.

The proof conjugates the `(AB, C)` square along the associativity constraint of each
multiplication and cancels the associator together with `A ◁ b`, which is why `b` is asked for as
an isomorphism. This is the induction step of a graded multiplicativity statement: `A`, `B`, `C`
are the tensor powers in degrees `n`, `m`, `1`. -/
theorem square_step {D : Type*} [Category D] [MonoidalCategory D]
    {A B C AB BC ABC A' B' C' AB' BC' ABC' : D}
    {a : A ⊗ B ⟶ AB} {b : B ⊗ C ≅ BC} {p : AB ⊗ C ⟶ ABC} {r : A ⊗ BC ⟶ ABC}
    {a' : A' ⊗ B' ⟶ AB'} {b' : B' ⊗ C' ⟶ BC'} {p' : AB' ⊗ C' ⟶ ABC'}
    {r' : A' ⊗ BC' ⟶ ABC'}
    {f : A ⟶ A'} {g : B ⟶ B'} {h : C ⟶ C'} {fg : AB ⟶ AB'} {gh : BC ⟶ BC'}
    {fgh : ABC ⟶ ABC'}
    (hL : a ▷ C ≫ p = (α_ A B C).hom ≫ A ◁ b.hom ≫ r)
    (hR : a' ▷ C' ≫ p' = (α_ A' B' C').hom ≫ A' ◁ b' ≫ r')
    (h1 : a ≫ fg = (f ⊗ₘ g) ≫ a')
    (h2 : p ≫ fgh = (fg ⊗ₘ h) ≫ p')
    (h3 : b.hom ≫ gh = (g ⊗ₘ h) ≫ b') :
    r ≫ fgh = (f ⊗ₘ gh) ≫ r' := by
  refine (Iso.cancel_iso_hom_left (α_ A B C ≪≫ MonoidalCategory.whiskerLeftIso A b) _ _).mp ?_
  simp only [Iso.trans_hom, MonoidalCategory.whiskerLeftIso_hom, Category.assoc]
  have e1 : a ▷ C ≫ (fg ⊗ₘ h) = ((f ⊗ₘ g) ⊗ₘ h) ≫ a' ▷ C' := by
    simp only [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom, ← h1,
      Category.id_comp, Category.comp_id]
  have e2 : (f ⊗ₘ (g ⊗ₘ h)) ≫ A' ◁ b' = A ◁ b.hom ≫ (f ⊗ₘ gh) := by
    simp only [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom, ← h3,
      Category.id_comp, Category.comp_id]
  calc (α_ A B C).hom ≫ A ◁ b.hom ≫ r ≫ fgh
      = (a ▷ C ≫ p) ≫ fgh := by rw [hL]; simp only [Category.assoc]
    _ = ((f ⊗ₘ g) ⊗ₘ h) ≫ (a' ▷ C' ≫ p') := by
          rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc]
    _ = (α_ A B C).hom ≫ (f ⊗ₘ (g ⊗ₘ h)) ≫ A' ◁ b' ≫ r' := by
          rw [hR, ← Category.assoc, MonoidalCategory.associator_naturality]
          simp only [Category.assoc]
    _ = (α_ A B C).hom ≫ A ◁ b.hom ≫ (f ⊗ₘ gh) ≫ r' := by
          rw [← Category.assoc (f ⊗ₘ _), e2, Category.assoc]

/-- **An associativity constraint survives conjugation by comparison isomorphisms**, in an
abstract monoidal category. The three structural morphisms `wr`, `al` and `wl` of a second
monoidal structure on the same objects are given by what they are conjugates of — a right
whiskering, an associator and a left whiskering of the structure in scope, read through the
comparison isomorphisms `iw`, `iab`, `ipc`, `ibc`, `iu` and `iq` — and the two multiplications
`mab`, `mpc`, `mbc`, `maq` satisfy the associativity constraint `hloc` against the associator of
the structure in scope. Then the conjugated square commutes: the conjugating factors cancel in
pairs and `hloc` is all that is left.

Isolated with every object a variable, for the reason given for `square_step`: at the concrete
objects of this file the source of a whiskering and the tensor product sheaf of Stacks Tag 01CA
are equal by `rfl` and not syntactically, so no step of this computation can be done there by
`rw` or by `simp` — the congruence check of either rejects a term that mixes the two spellings —
while `hwr`, `hal` and `hwl` are `rfl` and `exact` unifies the two spellings at default
transparency. -/
private theorem assoc_conj_square {D : Type*} [Category D] [MonoidalCategory D]
    {A B E TAB P Q TBC W V V' U G G' : D}
    {iw : TAB ⊗ E ≅ W} {iab : A ⊗ B ≅ TAB} {ipc : P ⊗ E ≅ V} {ibc : B ⊗ E ≅ TBC}
    {iu : A ⊗ TBC ≅ U} {iq : A ⊗ Q ≅ V'}
    {mab : A ⊗ B ⟶ P} {mpc : P ⊗ E ⟶ G} {mbc : B ⊗ E ⟶ Q} {maq : A ⊗ Q ⟶ G'} {k : G' ⟶ G}
    {wr : W ⟶ V} {al : W ⟶ U} {wl : U ⟶ V'}
    (hwr : wr = iw.inv ≫ (iab.inv ≫ mab) ▷ E ≫ ipc.hom)
    (hal : al = (iw.inv ≫ (iab.inv ⊗ₘ 𝟙 E)) ≫ ((α_ A B E).hom ≫ ((𝟙 A ⊗ₘ ibc.hom) ≫ iu.hom)))
    (hwl : wl = iu.inv ≫ A ◁ (ibc.inv ≫ mbc) ≫ iq.hom)
    (hloc : mab ▷ E ≫ mpc = (α_ A B E).hom ≫ A ◁ mbc ≫ maq ≫ k) :
    wr ≫ ipc.inv ≫ mpc = al ≫ wl ≫ (iq.inv ≫ maq) ≫ k := by
  subst hwr hal hwl
  simp only [Category.assoc, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom, Iso.hom_inv_id_assoc,
    MonoidalCategory.whiskerLeft_hom_inv_assoc]
  rw [hloc]

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The strict monoidal structure of Stacks Tag 01CA, as a `MonoidalCategoryStruct`, so that its
structural morphisms can be named while the localized structure is the one in scope. -/
abbrev strStruct : MonoidalCategoryStruct (SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :=
  (Stacks.SheafOfModules.Strict.monoidalCategory 𝒪 h𝒪).toMonoidalCategoryStruct

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The tensor product of the strict structure is the tensor product sheaf of Stacks Tag 01CA. -/
theorem strStruct_tensorObj (A B : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    MonoidalCategoryStruct.tensorObj (self := strStruct 𝒪 h𝒪) A B =
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
          (A)).obj (B)) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Right whiskering in the strict structure is right whiskering in the localized one**,
conjugated by the comparison isomorphism. This is
`Stacks.SheafOfModules.Strict.whiskerRight_eq`, read with the other localized structure in
scope. -/
theorem str_whiskerRight {A A' : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)} (f : A ⟶ A')
    (Z : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    MonoidalCategoryStruct.whiskerRight (self := strStruct 𝒪 h𝒪) f Z =
      (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 A Z).inv ≫ f ▷ Z ≫
        (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 A' Z).hom :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Left whiskering in the strict structure is left whiskering in the localized one**,
conjugated by the comparison isomorphism. -/
theorem str_whiskerLeft (A : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪))
    {B B' : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)} (g : B ⟶ B') :
    MonoidalCategoryStruct.whiskerLeft (self := strStruct 𝒪 h𝒪) A g =
      (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 A B).inv ≫ A ◁ g ≫
        (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 A B').hom :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The associator of the strict structure is the localized associator**, conjugated by the
comparison isomorphism on both sides. -/
theorem str_associator (A B E : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    (MonoidalCategoryStruct.associator (self := strStruct 𝒪 h𝒪) A B E).hom =
      ((Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
              (A)).obj (B))) E).inv ≫
          ((Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 A B).inv ⊗ₘ 𝟙 E)) ≫
        ((α_ A B E).hom ≫
          ((𝟙 A ⊗ₘ (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 B E).hom) ≫
            (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 A
              ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat)
                  (h𝒪)⟩).obj (B)).obj (E)))).hom)) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The left unitor of the strict structure is the localized left unitor**, precomposed with the
comparison isomorphism. Unlike the associator and the two whiskerings, this is *not* the left
unitor of `Stacks.SheafInternalHom.monoidalCategory`: the unit objects of the two localizations
differ, and `AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom` is what carries one to the
other. -/
theorem str_leftUnitor (A : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    (MonoidalCategoryStruct.leftUnitor (self := strStruct 𝒪 h𝒪) A).hom =
      (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪
          (_root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) A).inv ≫ (λ_ A).hom :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Right whiskering a morphism into the unit object, followed by the left unitor of the strict
structure**: the two inner comparison isomorphisms cancel, so only the outer one survives. The
objects are variables here, which is what lets the cancellation be done by `rw` at all. -/
theorem str_whiskerRight_leftUnitor {A : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)}
    (g : A ⟶ _root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪))
    (Z : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    MonoidalCategoryStruct.whiskerRight (self := strStruct 𝒪 h𝒪) g Z ≫
        (MonoidalCategoryStruct.leftUnitor (self := strStruct 𝒪 h𝒪) Z).hom =
      (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 A Z).inv ≫ g ▷ Z ≫ (λ_ Z).hom := by
  rw [str_whiskerRight, str_leftUnitor, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The right unitor of the strict structure is the localized right unitor**, precomposed with
the comparison isomorphism. As for the left unitor, this is *not* the right unitor of
`Stacks.SheafInternalHom.monoidalCategory`, and `rightUnitor_monoidalCategory_hom` is what carries
one to the other. -/
theorem str_rightUnitor (A : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    (MonoidalCategoryStruct.rightUnitor (self := strStruct 𝒪 h𝒪) A).hom =
      (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 A
          (_root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪))).inv ≫ (ρ_ A).hom :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Whiskering a morphism into the unit object on the left, followed by the right unitor of the
strict structure**: as in `str_whiskerRight_leftUnitor` the two inner comparison isomorphisms
cancel, so only the outer one survives. -/
theorem str_whiskerLeft_rightUnitor (Z : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪))
    {A : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)}
    (g : A ⟶ _root_.SheafOfModules.unit (structureSheaf 𝒪 h𝒪)) :
    MonoidalCategoryStruct.whiskerLeft (self := strStruct 𝒪 h𝒪) Z g ≫
        (MonoidalCategoryStruct.rightUnitor (self := strStruct 𝒪 h𝒪) Z).hom =
      (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 Z A).inv ≫ Z ◁ g ≫ (ρ_ Z).hom := by
  rw [str_whiskerLeft, str_rightUnitor, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc]

section Powers

open AlgebraicGeometry.SheafOfModules

variable (L : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) [IsInvertible 𝒪 h𝒪 L]

/-- The addition law of the tensor powers, retyped at `Stacks.SheafOfModules.monoidalCategory`.
The body is `AlgebraicGeometry.SheafOfModules.tensorPowAddIso`, which is typed at
`Stacks.SheafInternalHom.monoidalCategory`; the ascription is the whole content, and it is what
keeps a composite with the comparison isomorphism type-correct at the transparency the
simplifier checks its congruences at. -/
def addIsoLoc (n m : ℤ) :
    tensorPow 𝒪 h𝒪 L n ⊗ tensorPow 𝒪 h𝒪 L m ≅ tensorPow 𝒪 h𝒪 L (n + m) :=
  tensorPowAddIso 𝒪 h𝒪 L n m

/-- **The addition law with the tensor product sheaf as source is the localized addition law**,
precomposed with the comparison isomorphism. This is the definition of
`AlgebraicGeometry.SheafOfModules.tensorPowAddIsoSheaf`, read through `tensorIso_eq`. -/
theorem addIsoSheaf_hom (n m : ℤ) :
    (tensorPowAddIsoSheaf 𝒪 h𝒪 L n m).hom =
      (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L n) (tensorPow 𝒪 h𝒪 L m)).inv ≫
        (addIsoLoc 𝒪 h𝒪 L n m).hom :=
  congrArg (fun φ => φ ≫ (addIsoLoc 𝒪 h𝒪 L n m).hom)
    (congrArg Iso.inv (tensorIso_eq 𝒪 h𝒪 (tensorPow 𝒪 h𝒪 L n) (tensorPow 𝒪 h𝒪 L m)))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The associativity constraint of the addition law at the localized structure, read at the
retyping `addIsoLoc`. -/
theorem loc_addIso_assoc (a b c : ℕ) :
    (addIsoLoc 𝒪 h𝒪 L (a : ℤ) (b : ℤ)).hom ▷ tensorPow 𝒪 h𝒪 L (c : ℤ) ≫
        (addIsoLoc 𝒪 h𝒪 L ((a : ℤ) + (b : ℤ)) (c : ℤ)).hom =
      (α_ (tensorPow 𝒪 h𝒪 L (a : ℤ)) (tensorPow 𝒪 h𝒪 L (b : ℤ))
          (tensorPow 𝒪 h𝒪 L (c : ℤ))).hom ≫
        tensorPow 𝒪 h𝒪 L (a : ℤ) ◁ (addIsoLoc 𝒪 h𝒪 L (b : ℤ) (c : ℤ)).hom ≫
          (addIsoLoc 𝒪 h𝒪 L (a : ℤ) ((b : ℤ) + (c : ℤ))).hom ≫
            (tensorPowNatCongrIso 𝒪 h𝒪 L (Nat.add_assoc a b c).symm).hom :=
  congrArg Iso.hom (tensorPowAddIso_assoc_natCast 𝒪 h𝒪 L a b c)

/-- **The associativity constraint on the multiplication of tensor powers, with the tensor
product sheaf of Stacks Tag 01CA as source**, in nonnegative degree, against the associator of
the strict monoidal structure. Both composites are conjugated into the localized structure by
the comparison isomorphism, where the constraint is
`AlgebraicGeometry.SheafOfModules.tensorPowAddIso_assoc_natCast`. -/
theorem addIsoSheaf_assoc (a b c : ℕ) :
    MonoidalCategoryStruct.whiskerRight (self := strStruct 𝒪 h𝒪)
          (tensorPowAddIsoSheaf 𝒪 h𝒪 L (a : ℤ) (b : ℤ)).hom (tensorPow 𝒪 h𝒪 L (c : ℤ)) ≫
        (tensorPowAddIsoSheaf 𝒪 h𝒪 L ((a : ℤ) + (b : ℤ)) (c : ℤ)).hom =
      (MonoidalCategoryStruct.associator (self := strStruct 𝒪 h𝒪) (tensorPow 𝒪 h𝒪 L (a : ℤ))
          (tensorPow 𝒪 h𝒪 L (b : ℤ)) (tensorPow 𝒪 h𝒪 L (c : ℤ))).hom ≫
        MonoidalCategoryStruct.whiskerLeft (self := strStruct 𝒪 h𝒪) (tensorPow 𝒪 h𝒪 L (a : ℤ))
            (tensorPowAddIsoSheaf 𝒪 h𝒪 L (b : ℤ) (c : ℤ)).hom ≫
          (tensorPowAddIsoSheaf 𝒪 h𝒪 L (a : ℤ) ((b : ℤ) + (c : ℤ))).hom ≫
            (tensorPowNatCongrIso 𝒪 h𝒪 L (Nat.add_assoc a b c).symm).hom := by
  simp only [addIsoSheaf_hom 𝒪 h𝒪 L]
  exact assoc_conj_square (str_whiskerRight 𝒪 h𝒪 _ _) (str_associator 𝒪 h𝒪 _ _ _)
    (str_whiskerLeft 𝒪 h𝒪 _ _) (loc_addIso_assoc 𝒪 h𝒪 L a b c)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The identification of the zeroth tensor power with the structure sheaf is the comparison of
the two unit objects: `tensorPowZeroIso` is `AlgebraicGeometry.SheafOfModules.unitIso` by
definition, so the two cancel. -/
theorem tensorPowZeroIso_hom_comp_unitIso_inv :
    (tensorPowZeroIso 𝒪 h𝒪 L).hom ≫ (unitIso 𝒪 h𝒪).inv = 𝟙 (tensorPow 𝒪 h𝒪 L 0) :=
  (tensorPowZeroIso 𝒪 h𝒪 L).hom_inv_id

/-- **The left unit constraint of the addition law with the tensor product sheaf as source**:
multiplication by `L ^⊗ 0` on the left is the left unitor of the strict monoidal structure of
Stacks Tag 01CA, the zeroth power being identified with the structure sheaf by
`AlgebraicGeometry.SheafOfModules.tensorPowZeroIso`.

Both sides are conjugated into the localized structure by the comparison isomorphism; the unit
objects of the two localizations are matched by
`AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom`, and what is left is
`AlgebraicGeometry.SheafOfModules.tensorPowAddIso_zero_left_natCast`. -/
theorem addIsoSheaf_zero_left (b : ℕ) :
    MonoidalCategoryStruct.whiskerRight (self := strStruct 𝒪 h𝒪)
          (tensorPowZeroIso 𝒪 h𝒪 L).hom (tensorPow 𝒪 h𝒪 L (b : ℤ)) ≫
        (MonoidalCategoryStruct.leftUnitor (self := strStruct 𝒪 h𝒪)
          (tensorPow 𝒪 h𝒪 L (b : ℤ))).hom =
      (tensorPowAddIsoSheaf 𝒪 h𝒪 L ((0 : ℕ) : ℤ) (b : ℤ)).hom ≫
        (tensorPowNatCongrIso 𝒪 h𝒪 L (Nat.zero_add b)).hom := by
  have hzl := congrArg Iso.hom (tensorPowAddIso_zero_left_natCast 𝒪 h𝒪 L b)
  rw [Iso.trans_hom] at hzl
  rw [addIsoSheaf_hom, str_whiskerRight_leftUnitor,
    _root_.AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom, ← hzl]
  refine Eq.trans (congrArg (fun z ↦ (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪
      (tensorPow 𝒪 h𝒪 L 0) (tensorPow 𝒪 h𝒪 L (b : ℤ))).inv ≫ z)
    (whiskerRight_comp_cancel (tensorPowZeroIso 𝒪 h𝒪 L).hom (unitIso 𝒪 h𝒪).inv
      (tensorPowZeroIso_hom_comp_unitIso_inv 𝒪 h𝒪 L)
      ((tensorPowAddIso 𝒪 h𝒪 L ((0 : ℕ) : ℤ) (b : ℤ)).hom ≫
        (tensorPowNatCongrIso 𝒪 h𝒪 L (Nat.zero_add b)).hom))) ?_
  exact (Category.assoc _ _ _).symm

/-- **The right unit constraint of the addition law with the tensor product sheaf as source**:
multiplication by `L ^⊗ 0` on the right is the right unitor of the strict monoidal structure of
Stacks Tag 01CA, the zeroth power being identified with the structure sheaf by
`AlgebraicGeometry.SheafOfModules.tensorPowZeroIso`.

The mirror of `addIsoSheaf_zero_left`, with `rightUnitor_monoidalCategory_hom` matching the unit
objects of the two localizations and
`AlgebraicGeometry.SheafOfModules.tensorPowAddIso_zero_right_natCast` — which carries no
transport, the degrees `a + 0` and `a` being the same — as the input. -/
theorem addIsoSheaf_zero_right (a : ℕ) :
    MonoidalCategoryStruct.whiskerLeft (self := strStruct 𝒪 h𝒪) (tensorPow 𝒪 h𝒪 L (a : ℤ))
          (tensorPowZeroIso 𝒪 h𝒪 L).hom ≫
        (MonoidalCategoryStruct.rightUnitor (self := strStruct 𝒪 h𝒪)
          (tensorPow 𝒪 h𝒪 L (a : ℤ))).hom =
      (tensorPowAddIsoSheaf 𝒪 h𝒪 L (a : ℤ) ((0 : ℕ) : ℤ)).hom := by
  have hzr := congrArg Iso.hom (tensorPowAddIso_zero_right_natCast 𝒪 h𝒪 L a)
  rw [addIsoSheaf_hom, str_whiskerLeft_rightUnitor, rightUnitor_monoidalCategory_hom, ← hzr]
  exact congrArg (fun z ↦ (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪
      (tensorPow 𝒪 h𝒪 L (a : ℤ)) (tensorPow 𝒪 h𝒪 L 0)).inv ≫ z)
    (whiskerLeft_comp_cancel (tensorPow 𝒪 h𝒪 L (a : ℤ)) (tensorPowZeroIso 𝒪 h𝒪 L).hom
      (unitIso 𝒪 h𝒪).inv (tensorPowZeroIso_hom_comp_unitIso_inv 𝒪 h𝒪 L)
      (tensorPowAddIso 𝒪 h𝒪 L (a : ℤ) ((0 : ℕ) : ℤ)).hom)

end Powers

end Bridge

/-! ### On a scheme -/

section Scheme

/-- The strict monoidal structure of Stacks Tag 01CA on the `𝒪_X`-modules of a scheme, named at
the `AlgebraicGeometry.Scheme.Modules` spelling, which is the spelling the ampleness theory and
the twists of `Proj` are typed in. The body is `Stacks.PullbackGradedAlgebra.monoidalCategory`
of the underlying ringed space. -/
@[instance_reducible]
def schemeMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace

/-- The same monoidal structure, named at the
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` spelling of the ring sheaf, which is
the spelling the addition law of the tensor powers is typed in. Every argument is determined by
the scheme, so unlike `Stacks.SheafOfModules.Strict.monoidalCategory` applied by hand this is
found by instance search without the sheaf condition and the three sheafification hypotheses of
the site having to be recovered from the type. -/
@[instance_reducible]
def strictSchemeMonoidal (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))) :=
  Stacks.SheafOfModules.Strict.monoidalCategory X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)

attribute [local instance] schemeMonoidal strictSchemeMonoidal

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

variable (X : Scheme.{u})

/-- **The functorial action of the tensor product sheaf on a pair of isomorphisms is the monoidal
tensor product of their forward maps.** `Stacks.RelativeVeryAmple.tensorModulesMapIso` reads the
action off the bifunctor `Stacks.RingedSpace.tensorSheaf`, and the strict monoidal structure
takes the same bifunctor for its tensor product; this is
`Stacks.SheafOfModules.tensorSheafMapIso_hom_eq` at the scheme spelling. -/
theorem tensorModulesMapIso_hom {A A' B B' : X.Modules} (e : A ≅ A') (g : B ≅ B') :
    (tensorModulesMapIso X e g).hom = e.hom ⊗ₘ g.hom :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf e.hom g.hom).trans
    (Stacks.SheafOfModules.tensorSheafMapIso_hom_eq X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) e g)

/-- **The associativity constraint on the multiplication of the tensor powers of an invertible
`𝒪_X`-module**, in nonnegative degree, in the vocabulary `Stacks.Ample.tensorPowModuleAddIso`
and `Stacks.RelativeVeryAmple.tensorModules` that the ampleness theory and the twists of `Proj`
are written in, and against the associator of the strict monoidal structure of Stacks Tag 01CA —
the structure `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_assoc` is stated at. -/
theorem tensorPowModuleAddIso_assoc (L : X.Modules) [IsInvertibleModule X L] (a b c : ℕ) :
    MonoidalCategoryStruct.whiskerRight
        (self := (schemeMonoidal X).toMonoidalCategoryStruct)
        (tensorPowModuleAddIso X L (a : ℤ) (b : ℤ)).hom (tensorPowModule X L (c : ℤ)) ≫
        (tensorPowModuleAddIso X L ((a : ℤ) + (b : ℤ)) (c : ℤ)).hom =
      (MonoidalCategoryStruct.associator (self := (schemeMonoidal X).toMonoidalCategoryStruct)
          (tensorPowModule X L (a : ℤ)) (tensorPowModule X L (b : ℤ))
          (tensorPowModule X L (c : ℤ))).hom ≫
        MonoidalCategoryStruct.whiskerLeft
          (self := (schemeMonoidal X).toMonoidalCategoryStruct)
          (tensorPowModule X L (a : ℤ)) (tensorPowModuleAddIso X L (b : ℤ) (c : ℤ)).hom ≫
          (tensorPowModuleAddIso X L (a : ℤ) ((b : ℤ) + (c : ℤ))).hom ≫
            (tensorPowModuleCongr X L
              (show (a : ℤ) + ((b : ℤ) + (c : ℤ)) = (a : ℤ) + (b : ℤ) + (c : ℤ) from
                by ring)).hom :=
  addIsoSheaf_assoc X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L a b c

/-- **The left unit constraint on the multiplication of the tensor powers of an invertible
`𝒪_X`-module**, in the same vocabulary and against the left unitor of the strict monoidal
structure of Stacks Tag 01CA: multiplying by the zeroth power on the left, after identifying it
with `𝒪_X` by `Stacks.Ample.tensorPowModuleZeroIso`, is that left unitor. -/
theorem tensorPowModuleAddIso_zero_left (L : X.Modules) [IsInvertibleModule X L] (b : ℕ) :
    (tensorPowModuleZeroIso X L).hom ▷ tensorPowModule X L (b : ℤ) ≫
        (λ_ (tensorPowModule X L (b : ℤ))).hom =
      (tensorPowModuleAddIso X L ((0 : ℕ) : ℤ) (b : ℤ)).hom ≫
        (tensorPowModuleCongr X L
          (show (((0 : ℕ) : ℤ) + (b : ℤ)) = (b : ℤ) from by push_cast; ring)).hom :=
  addIsoSheaf_zero_left X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L b

/-- **The right unit constraint on the multiplication of the tensor powers of an invertible
`𝒪_X`-module**, in the same vocabulary and against the right unitor of the strict monoidal
structure of Stacks Tag 01CA: multiplying by the zeroth power on the right, after identifying it
with `𝒪_X` by `Stacks.Ample.tensorPowModuleZeroIso`, is that right unitor. No transport appears:
the target degree `a + 0` is the degree `a`. -/
theorem tensorPowModuleAddIso_zero_right (L : X.Modules) [IsInvertibleModule X L] (a : ℕ) :
    tensorPowModule X L (a : ℤ) ◁ (tensorPowModuleZeroIso X L).hom ≫
        (ρ_ (tensorPowModule X L (a : ℤ))).hom =
      (tensorPowModuleAddIso X L (a : ℤ) ((0 : ℕ) : ℤ)).hom :=
  addIsoSheaf_zero_right X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L a

end Scheme

/-! ### The two multiplications of the degree `d` open, in one monoidal structure -/

section DegreeOpen

open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen

attribute [local instance] schemeMonoidal strictSchemeMonoidal

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-- **Associativity of the canonical multiplication isomorphism of the degree `d` open**, read at
the spelling `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso` is stated in and
against the associator of `schemeMonoidal` — the same monoidal structure
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc` is stated at.

This is `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_assoc`, whose objects are the
pulled-back twists `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwist` along the open immersion;
the module pullback of a morphism of schemes is `Stacks.RingedSpace.pullbackFunctor` of the
underlying morphism of ringed spaces, so those are the restricted twists on the nose, and the two
transports are `eqToHom` of equality proofs between the same two objects. -/
theorem twistMulIso_assoc (n m k : ℤ) :
    (twistMulIso 𝒮 d n m).hom ▷ twist 𝒮 d ((d : ℤ) * k) ≫ (twistMulIso 𝒮 d (n + m) k).hom =
      (α_ (twist 𝒮 d ((d : ℤ) * n)) (twist 𝒮 d ((d : ℤ) * m))
          (twist 𝒮 d ((d : ℤ) * k))).hom ≫
        twist 𝒮 d ((d : ℤ) * n) ◁ (twistMulIso 𝒮 d m k).hom ≫
          (twistMulIso 𝒮 d n (m + k)).hom ≫
            eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
              (show (d : ℤ) * (n + (m + k)) = (d : ℤ) * (n + m + k) from by ring)) :=
  Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_assoc 𝒮 d n m k

/-- **The left unit law of the canonical multiplication isomorphism of the degree `d` open**,
read at the spelling `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso` is
stated in and against the left unitor of `schemeMonoidal`: the inverse of
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistZeroIsoUnit`, transported to degree
`d · 0`, whiskered into `𝒪_{U_d}(dm)` and multiplied, is that left unitor.

This is `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_one_left`, whose unit is
`Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit` — equal to `(twistZeroIsoUnit 𝒮 d).inv`
by `rfl`, so the degree zero value of the comparison family is the isomorphism the law speaks
about and no second `𝒪_{U_d}(0) ≅ 𝒪_{U_d}` enters. -/
theorem twistMulIso_zero_left (m : ℤ) :
    ((twistZeroIsoUnit 𝒮 d).inv ≫
          eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
            (show (0 : ℤ) = (d : ℤ) * 0 from by ring))) ▷ twist 𝒮 d ((d : ℤ) * m) ≫
        (twistMulIso 𝒮 d 0 m).hom =
      (λ_ (twist 𝒮 d ((d : ℤ) * m))).hom ≫
        eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
          (show (d : ℤ) * m = (d : ℤ) * (0 + m) from by ring)) :=
  Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_one_left 𝒮 d m

/-- **The right unit law of the canonical multiplication isomorphism of the degree `d` open**,
the mirror of `twistMulIso_zero_left`: the inverse of
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistZeroIsoUnit`, transported to degree
`d · 0`, whiskered into `𝒪_{U_d}(dn)` on the left and multiplied, is the right unitor of
`schemeMonoidal`.

This is `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_one_right`, whose unit is again
`Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit`, so this is a statement about the very
isomorphism the comparison family is built from in degree zero. -/
theorem twistMulIso_zero_right (n : ℤ) :
    twist 𝒮 d ((d : ℤ) * n) ◁
          ((twistZeroIsoUnit 𝒮 d).inv ≫
            eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
              (show (0 : ℤ) = (d : ℤ) * 0 from by ring))) ≫
        (twistMulIso 𝒮 d n 0).hom =
      (ρ_ (twist 𝒮 d ((d : ℤ) * n))).hom ≫
        eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
          (show (d : ℤ) * n = (d : ℤ) * (n + 0) from by ring)) :=
  Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_one_right 𝒮 d n

/-- **The degree one value of the comparison family is the canonical identification of the first
tensor power**: `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta 𝒮 d 1` is
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistOneIso 𝒮 d`.

By the recursion, the degree one value is built out of the degree zero one, which is the
canonical `𝒪_{U_d}(d)^{⊗ 0} ≅ 𝒪_{U_d} ≅ 𝒪_{U_d}(0)`. The two unit laws
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left` and `twistMulIso_zero_left`
say that the two multiplications agree with the left unitor of Stacks Tag 01CA on that
identification, which pins the degree one value down. -/
theorem theta_one_eq : theta 𝒮 d 1 = twistOneIso 𝒮 d :=
  Iso.ext
    (unit_tensorHom_cancel
      (tensorPowModuleZeroIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (twist 𝒮 d (d : ℤ))).hom
      ((twistZeroIsoUnit 𝒮 d).inv ≫
        eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
          (show (0 : ℤ) = (d : ℤ) * 0 from by ring)))
      (twistOneIso 𝒮 d).hom
      (tensorModulesMapIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (theta 𝒮 d 0) (twistOneIso 𝒮 d)).hom
      (twistMulIso 𝒮 d 0 1).hom
      (eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
        (show (d : ℤ) * ((0 : ℤ) + 1) = (d : ℤ) * (((0 + 1 : ℕ)) : ℤ) from by push_cast; ring)))
      (eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
        (show (d : ℤ) * 1 = (d : ℤ) * (0 + 1) from by ring)))
      (thetaStep 𝒮 d 0).inv (thetaStep 𝒮 d 0).hom
      ((tensorModulesMapIso_hom (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (theta 𝒮 d 0) (twistOneIso 𝒮 d)).trans
        (congrArg (fun φ ↦ φ ⊗ₘ (twistOneIso 𝒮 d).hom) (rfl : (theta 𝒮 d 0).hom = _)))
      (twistMulIso_zero_left 𝒮 d 1)
      (by rw [eqToHom_trans]; rfl)
      (tensorPowModuleAddIso_zero_left (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (twist 𝒮 d (d : ℤ)) 1)
      (thetaStep 𝒮 d 0).inv_hom_id)

/-! ### The multiplicativity square in a full bidegree -/

/-- **The addition law of the tensor powers of `𝒪_{U_d}(d)` in a pair of natural-number
exponents**, `𝒪_{U_d}(d)^{⊗ n} ⊗ 𝒪_{U_d}(d)^{⊗ m} ≅ 𝒪_{U_d}(d)^{⊗ (n+m)}`. The body is
`Stacks.Ample.tensorPowModuleAddIso`; the ascription spells the source with the tensor product of
`schemeMonoidal` and the target exponent as the natural number `n + m`, which is how the
comparison family is indexed. At `m = 1` this is
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaStep`. -/
def thetaStepNat (n m : ℕ) :
    tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
          (n : ℤ) ⊗
        tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
          (m : ℤ) ≅
      tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
        ((n + m : ℕ) : ℤ) :=
  tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
    (twist 𝒮 d (d : ℤ)) (n : ℤ) (m : ℤ)

/-- **The canonical multiplication isomorphism of the degree `d` open in a pair of natural-number
degrees**, `𝒪_{U_d}(dn) ⊗ 𝒪_{U_d}(dm) ≅ 𝒪_{U_d}(d(n+m))`. The body is
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso`; the ascription spells the
target degree with the natural number `n + m`. -/
def twistMulIsoNat (n m : ℕ) :
    twist 𝒮 d ((d : ℤ) * (n : ℤ)) ⊗ twist 𝒮 d ((d : ℤ) * (m : ℤ)) ≅
      twist 𝒮 d ((d : ℤ) * ((n + m : ℕ) : ℤ)) :=
  twistMulIso 𝒮 d (n : ℤ) (m : ℤ)

/-- The associativity constraint of the addition law in the bidegrees `(n, m)` and `(n + m, 1)`,
at the natural-number spelling. This is `tensorPowModuleAddIso_assoc` with the transport along
`n + (m + 1) = n + m + 1` removed: in the third degree `1` its two ends are the same object. -/
theorem thetaStepNat_assoc (n m : ℕ) :
    (thetaStepNat 𝒮 d n m).hom ▷
        tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
          (((1 : ℕ)) : ℤ) ≫
        (thetaStepNat 𝒮 d (n + m) 1).hom =
      (α_ _ _ _).hom ≫
        tensorPowModule (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
            (n : ℤ) ◁ (thetaStepNat 𝒮 d m 1).hom ≫
          (thetaStepNat 𝒮 d n (m + 1)).hom :=
  (tensorPowModuleAddIso_assoc (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ)) n m 1).trans (comp_comp_comp_eq_self _ _ _ _ rfl)

/-- The associativity constraint of the canonical multiplication in the same two bidegrees. This
is `twistMulIso_assoc` with the transport along `d(n + (m + 1)) = d(n + m + 1)` removed. -/
theorem twistMulIsoNat_assoc (n m : ℕ) :
    (twistMulIsoNat 𝒮 d n m).hom ▷ twist 𝒮 d ((d : ℤ) * (((1 : ℕ)) : ℤ)) ≫
        (twistMulIsoNat 𝒮 d (n + m) 1).hom =
      (α_ _ _ _).hom ≫
        twist 𝒮 d ((d : ℤ) * (n : ℤ)) ◁ (twistMulIsoNat 𝒮 d m 1).hom ≫
          (twistMulIsoNat 𝒮 d n (m + 1)).hom :=
  (twistMulIso_assoc 𝒮 d (n : ℤ) (m : ℤ) (((1 : ℕ)) : ℤ)).trans
    (comp_comp_comp_eq_self _ _ _ _ rfl)

/-- **Multiplicativity of the comparison family in the bidegree `(n, 1)`**, at the spellings
above: `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta_mul_one` with the degree one
factor read as the degree one value of the family through `theta_one_eq`, the tensor product of
the two comparisons read as a monoidal tensor product of morphisms through
`tensorModulesMapIso_hom`, and the two transports absorbed. -/
theorem theta_mul_one_nat (n : ℕ) :
    (thetaStepNat 𝒮 d n 1).hom ≫ (theta 𝒮 d (n + 1)).hom =
      ((theta 𝒮 d n).hom ⊗ₘ (theta 𝒮 d 1).hom) ≫ (twistMulIsoNat 𝒮 d n 1).hom :=
  (comp_cancel_left (thetaStepNat 𝒮 d n 1).hom _ rfl (theta 𝒮 d (n + 1)).hom).symm.trans
    ((theta_mul_one 𝒮 d n).trans
      ((comp_comp_eq_self _ _ _ rfl).trans
        (congrArg (fun z ↦ z ≫ (twistMulIsoNat 𝒮 d n 1).hom)
          ((tensorModulesMapIso_hom (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
              (theta 𝒮 d n) (twistOneIso 𝒮 d)).trans
            (congrArg (fun e ↦ (theta 𝒮 d n).hom ⊗ₘ Iso.hom e)
              (theta_one_eq 𝒮 d).symm)))))

/-- **Multiplicativity of the comparison family in the bidegree `(n, 0)`**, which is the right
unit law: the degree zero value of the family is the identification
`𝒪_{U_d}(d)^{⊗ 0} ≅ 𝒪_{U_d} ≅ 𝒪_{U_d}(0)`, and the two right unit laws
`tensorPowModuleAddIso_zero_right` and `twistMulIso_zero_right` say that the two multiplications
agree with the right unitor of Stacks Tag 01CA on it. The transport between the two spellings
`d · n` and `d · (n + 0)` of the target degree is an identity. -/
theorem theta_mul_zero_nat (n : ℕ) :
    (thetaStepNat 𝒮 d n 0).hom ≫ (theta 𝒮 d (n + 0)).hom =
      ((theta 𝒮 d n).hom ⊗ₘ (theta 𝒮 d 0).hom) ≫ (twistMulIsoNat 𝒮 d n 0).hom :=
  (comp_comp_eq_self (thetaStepNat 𝒮 d n 0).hom (theta 𝒮 d n).hom _ rfl).symm.trans
    (tensorHom_unit_square
      (tensorPowModuleZeroIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (twist 𝒮 d (d : ℤ))).hom
      ((twistZeroIsoUnit 𝒮 d).inv ≫
        eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
          (show (0 : ℤ) = (d : ℤ) * 0 from by ring)))
      (theta 𝒮 d n).hom
      ((theta 𝒮 d n).hom ⊗ₘ (theta 𝒮 d 0).hom)
      (twistMulIsoNat 𝒮 d n 0).hom
      (eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
        (show (d : ℤ) * (n : ℤ) = (d : ℤ) * ((n : ℤ) + 0) from by ring)))
      (thetaStepNat 𝒮 d n 0).hom
      (congrArg (fun φ ↦ (theta 𝒮 d n).hom ⊗ₘ φ) (rfl : (theta 𝒮 d 0).hom = _))
      (twistMulIso_zero_right 𝒮 d (n : ℤ))
      (tensorPowModuleAddIso_zero_right (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (twist 𝒮 d (d : ℤ)) n))

/-- **Multiplicativity of the comparison family in an arbitrary bidegree `(n, m)`**: the addition
law of the tensor powers followed by the comparison in degree `n + m` is the comparisons in
degrees `n` and `m` on the two factors followed by the canonical multiplication at `(dn, dm)`.
Both degrees are arbitrary natural numbers; in particular the bidegrees `(n, 0)` and `(0, m)` are
included.

By induction on `m`. The base case `m = 0` is the right unit law `theta_mul_zero_nat`; the step is
`square_step` fed with the two associativity constraints `thetaStepNat_assoc` and
`twistMulIsoNat_assoc` together with the squares in the bidegrees `(n, m)`, `(n + m, 1)` and
`(m, 1)`. -/
theorem theta_mul (n m : ℕ) :
    (thetaStepNat 𝒮 d n m).hom ≫ (theta 𝒮 d (n + m)).hom =
      ((theta 𝒮 d n).hom ⊗ₘ (theta 𝒮 d m).hom) ≫ (twistMulIsoNat 𝒮 d n m).hom := by
  induction m with
  | zero => exact theta_mul_zero_nat 𝒮 d n
  | succ k ih =>
      exact square_step (thetaStepNat_assoc 𝒮 d n k) (twistMulIsoNat_assoc 𝒮 d n k) ih
        (theta_mul_one_nat 𝒮 d (n + k)) (theta_mul_one_nat 𝒮 d k)

/-- **The canonical multiplication isomorphism with the twist degrees spelled as the `d`-th
Veronese section ring spells them**, `𝒪_{U_d}(nd) ⊗ 𝒪_{U_d}(md) ≅ 𝒪_{U_d}((n+m)d)`. This is
`twistMulIsoNat` conjugated by the transports along `nd = dn`. -/
def twistMulIsoVeronese (n m : ℕ) :
    twist 𝒮 d ((n * d : ℕ) : ℤ) ⊗ twist 𝒮 d ((m * d : ℕ) : ℤ) ≅
      twist 𝒮 d (((n + m) * d : ℕ) : ℤ) :=
  (eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
        (show ((n * d : ℕ) : ℤ) = (d : ℤ) * (n : ℤ) from by push_cast; ring)) ⊗ᵢ
      eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
        (show ((m * d : ℕ) : ℤ) = (d : ℤ) * (m : ℤ) from by push_cast; ring))) ≪≫
    twistMulIsoNat 𝒮 d n m ≪≫
    eqToIso (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
      (show (d : ℤ) * ((n + m : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by push_cast; ring))

/-- The Veronese spelling of the comparison family is the comparison family followed by the
transport along `dn = nd`. -/
theorem thetaNat_hom (n : ℕ) :
    (thetaNat 𝒮 d n).hom = (theta 𝒮 d n).hom ≫
      eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
        (show (d : ℤ) * (n : ℤ) = ((n * d : ℕ) : ℤ) from by push_cast; ring)) :=
  rfl

/-- The Veronese spelling of the canonical multiplication, unfolded into its three factors. -/
theorem twistMulIsoVeronese_hom (n m : ℕ) :
    (twistMulIsoVeronese 𝒮 d n m).hom =
      (eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
            (show ((n * d : ℕ) : ℤ) = (d : ℤ) * (n : ℤ) from by push_cast; ring)) ⊗ₘ
          eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
            (show ((m * d : ℕ) : ℤ) = (d : ℤ) * (m : ℤ) from by push_cast; ring))) ≫
        (twistMulIsoNat 𝒮 d n m).hom ≫
          eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
            (show (d : ℤ) * ((n + m : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
              push_cast; ring)) :=
  rfl

/-- The two transports between the degrees `dn` and `nd` cancel. -/
private theorem veronese_eqToHom_cancel (n : ℕ) :
    eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
        (show (d : ℤ) * (n : ℤ) = ((n * d : ℕ) : ℤ) from by push_cast; ring)) ≫
      eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
        (show ((n * d : ℕ) : ℤ) = (d : ℤ) * (n : ℤ) from by push_cast; ring)) =
      𝟙 (twist 𝒮 d ((d : ℤ) * (n : ℤ))) := by
  rw [eqToHom_trans]; rfl

/-- The left-hand side of the multiplicativity square, carried to the Veronese spelling of the
target degree. -/
private theorem thetaNat_mul_left (n m : ℕ)
    (h : (thetaStepNat 𝒮 d n m).hom ≫ (theta 𝒮 d (n + m)).hom =
      ((theta 𝒮 d n).hom ⊗ₘ (theta 𝒮 d m).hom) ≫ (twistMulIsoNat 𝒮 d n m).hom) :
    (thetaStepNat 𝒮 d n m).hom ≫ (thetaNat 𝒮 d (n + m)).hom =
      ((theta 𝒮 d n).hom ⊗ₘ (theta 𝒮 d m).hom) ≫
        (twistMulIsoNat 𝒮 d n m).hom ≫
          eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
            (show (d : ℤ) * ((n + m : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
              push_cast; ring)) := by
  rw [thetaNat_hom, ← Category.assoc, h, Category.assoc]

/-- The right-hand side of the multiplicativity square, carried to the Veronese spelling of the
two source degrees: the four transports cancel in pairs. -/
private theorem thetaNat_mul_right (n m : ℕ) :
    ((theta 𝒮 d n).hom ⊗ₘ (theta 𝒮 d m).hom) ≫
        (twistMulIsoNat 𝒮 d n m).hom ≫
          eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
            (show (d : ℤ) * ((n + m : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
              push_cast; ring)) =
      ((thetaNat 𝒮 d n).hom ⊗ₘ (thetaNat 𝒮 d m).hom) ≫ (twistMulIsoVeronese 𝒮 d n m).hom := by
  rw [thetaNat_hom, thetaNat_hom, twistMulIsoVeronese_hom,
    ← Category.assoc (((theta 𝒮 d n).hom ≫ _) ⊗ₘ ((theta 𝒮 d m).hom ≫ _)),
    MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc (theta 𝒮 d n).hom,
    Category.assoc (theta 𝒮 d m).hom, veronese_eqToHom_cancel, veronese_eqToHom_cancel,
    Category.comp_id, Category.comp_id]

/-- **Multiplicativity of `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(nd)` in an arbitrary bidegree `(n, m)`**,
with every twist degree spelled as the `d`-th Veronese section ring spells it. This is `theta_mul`
with the three degrees carried along the transports `dn = nd`, which cancel against the ones
inside `twistMulIsoVeronese`. As in `theta_mul` both degrees are arbitrary natural numbers. -/
theorem thetaNat_mul (n m : ℕ) :
    (thetaStepNat 𝒮 d n m).hom ≫ (thetaNat 𝒮 d (n + m)).hom =
      ((thetaNat 𝒮 d n).hom ⊗ₘ (thetaNat 𝒮 d m).hom) ≫
        (twistMulIsoVeronese 𝒮 d n m).hom :=
  (thetaNat_mul_left 𝒮 d n m (theta_mul 𝒮 d n m)).trans
    (thetaNat_mul_right 𝒮 d n m)

end DegreeOpen

end Stacks.AlgebraicGeometry.ThetaMul

end
