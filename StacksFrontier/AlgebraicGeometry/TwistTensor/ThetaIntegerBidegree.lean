module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerSuccSheaf
public import StacksFrontier.AlgebraicGeometry.TwistTensor.GradedLaurentMul
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerInvLaw

/-!
# Multiplicativity of the comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` in an integer bidegree

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring and `U_d ⊆ Proj 𝒮` the degree `d` open of Stacks Tag
01N5.  `Stacks.AlgebraicGeometry.ThetaMul.thetaInt` compares the tensor powers of `𝒪_{U_d}(d)`
with the `d`-divisible twists in every *integer* degree, and
`Stacks.AlgebraicGeometry.ThetaMul.theta_mul` says that the comparison is multiplicative — that it
carries the addition law `Stacks.Ample.tensorPowModuleAddIso` of the tensor powers to the canonical
multiplication `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso` of the twists —
in a bidegree of *natural* numbers.  This file removes that restriction.

Three things were missing, and the first two are the content.

**The associativity constraint of the addition law in an arbitrary integer tridegree, at the
modules of a scheme.**  `Stacks.TensorPowers.TensorInverse.addIso_assoc` proves it where the
powers are defined; what is here is the transport along the same steps
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerAssoc.lean` transports the natural-number
constraint along, together with the left unit law in an arbitrary integer degree, which travels
the same way.

**The snake-compatibility of the two inverse laws of a tensor power, at the modules of a
scheme.**  `Stacks.TensorPowers.TensorInverse.addIso_snake` proves it abstractly, but carrying
that statement across would mean conjugating five structure maps of the monoidal structure and the
two unit comparisons; it is shorter to repeat its argument once the associativity constraint has
been transported, which is what `tensorPowModuleAddIso_snake` does.  With it,
`Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso` applies directly to the definition
of the comparison in a negative degree and yields the **inverse-law square**, the one face of a
multiplicativity statement crossing the degree zero that no square chase reaches from the
nonnegative degrees.

**The square chase.**  From the inverse-law square the bidegree `(k, 1)` for a negative `k` is
`Stacks.Monoidal.square_step_left` on the associativity diagram in the tridegree `(-(a+1), 1, a)`,
and then every integer bidegree is an induction over `ℤ` in the second degree, with
`Stacks.AlgebraicGeometry.ThetaMul.square_step` upwards and `square_step_left` downwards.

## Main results

* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul`: **multiplicativity of the comparison family in
  an arbitrary integer bidegree.**  This is the conclusion of the file.
* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_one`: multiplicativity in the bidegree `(k, 1)`
  for an arbitrary integer `k`, which is the column the induction over `ℤ` is run along.
* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_neg_succ` and `thetaInt_mul_add_eq_zero`: **the
  inverse-law square**, in the bidegree `(-(j+1), j+1)` and then at every bidegree summing to zero
  with a nonnegative second exponent.
* `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int`: **the associativity
  constraint on the multiplication of the tensor powers of an invertible `𝒪_X`-module in an
  arbitrary integer tridegree**, with
  `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_assoc_int`,
  `Stacks.AlgebraicGeometry.ThetaMul.loc_addIso_assoc_int` and `addIsoSheaf_assoc_int` the three
  intermediate spellings.  This lifts the restriction on the second and third exponents that
  `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_natCast_right` still carried.
* `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left_int`: the left unit law in
  every integer degree, again with the intermediate spellings
  `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_zero_left_int` and
  `Stacks.AlgebraicGeometry.ThetaMul.addIsoSheaf_zero_left_int`.
* `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_snake`: **the two inverse laws of an
  integer tensor power of an invertible `𝒪_X`-module are snake-compatible.**
* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_of_eq` and `thetaInt_mul_corner_iff`: the two
  pieces of bookkeeping the chase runs on — moving a square between two spellings of its bidegree,
  and moving the transport of the total degree between the comparison and the multiplication of
  the twists.

## Implementation notes

**Why no degree here is a natural number.**  Every statement is phrased with integer exponents and
every degree identity is proved by `ring` or `omega`, so that `thetaInt_mul_of_eq` can move a
square from the spelling one lemma produces to the spelling the next consumes.  The alternative —
chasing with `tensorPowModuleAddIso_assoc_natCast_right`, whose second and third exponents are
natural numbers — crosses the `((1 : ℕ) : ℤ)` versus `(1 : ℤ)` spelling at every step, and `rw`
does not see through that.

**`Mono` by hand.**  `Stacks.Monoidal.square_step_left` asks for `Mono p'` as an instance.  At the
twists that instance is not found: the monoidal structure in scope is
`Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`, which exposes the modules of the degree `d`
open under the `SheafOfModules` spelling of their type, and an instance keyed on the
`AlgebraicGeometry.Scheme.Modules` spelling is not tried against a goal keyed on the other.
`Stacks.Monoidal.square_step_left_of_mono` of
`StacksFrontier/AlgebraicGeometry/TwistTensor/GradedLaurentMul.lean` takes the hypothesis
explicitly instead, discharged by `Stacks.Monoidal.mono_iso_hom` there.

**The free-object helpers.**  `snake_free`, `inv_law_free` and `absorb_iff` state their
computations with every object and morphism as a variable.  At the concrete objects the degrees
`0 + p`, `p + 0` and `p` are three spellings of one object and the zeroth tensor power is a
spelling of the unit, so neither `rw` nor `simp` performs any of their steps.

The monoidal structure is `Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`, the strict structure
of Stacks Tag 01CA on `X.Modules`, brought in as a local instance exactly as in
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaMultiplicativity.lean`: there is no global
monoidal instance at `(Proj.degreeOpen 𝒮 d).toScheme.Modules`.

## References

* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

universe v u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open Stacks.Ample
open Stacks.RelativeVeryAmple
open Stacks.SheafOfModules.TensorSheafification

namespace AlgebraicGeometry.SheafOfModules

section Loc

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{v})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : _root_.SheafOfModules.{v} (structureSheaf 𝒪 h𝒪)) [IsInvertible 𝒪 h𝒪 L]

/-- **The associativity constraint on the multiplication of the tensor powers of an invertible
sheaf of modules, in an arbitrary integer tridegree**, for the localized monoidal structure. -/
theorem tensorPowAddIso_assoc_int (n m c : ℤ) :
    (tensorPowAddIso 𝒪 h𝒪 L n m).hom ▷ tensorPow 𝒪 h𝒪 L c ≫
        (tensorPowAddIso 𝒪 h𝒪 L (n + m) c).hom =
      (α_ (tensorPow 𝒪 h𝒪 L n) (tensorPow 𝒪 h𝒪 L m) (tensorPow 𝒪 h𝒪 L c)).hom ≫
        tensorPow 𝒪 h𝒪 L n ◁ (tensorPowAddIso 𝒪 h𝒪 L m c).hom ≫
          (tensorPowAddIso 𝒪 h𝒪 L n (m + c)).hom ≫
            (eqToIso (congrArg (tensorPow 𝒪 h𝒪 L)
              (show n + (m + c) = n + m + c from by ring))).hom :=
  Stacks.TensorPowers.TensorInverse.addIso_assoc (tensorInverse 𝒪 h𝒪 L)
    (tensorInverse_snake 𝒪 h𝒪 L) n m c

/-- **The left unit law of the addition law on the tensor powers of an invertible sheaf of
modules, in every integer degree**, for the localized monoidal structure. -/
theorem tensorPowAddIso_zero_left_int (c : ℤ) :
    (tensorPowAddIso 𝒪 h𝒪 L 0 c).hom =
      (λ_ (tensorPow 𝒪 h𝒪 L c)).hom ≫
        eqToHom (congrArg (tensorPow 𝒪 h𝒪 L) (show c = 0 + c from by omega)) :=
  Stacks.TensorPowers.TensorInverse.addIso_zero_left (tensorInverse 𝒪 h𝒪 L)
    (tensorInverse_snake 𝒪 h𝒪 L) c

/-- `tensorPowAddIso_zero_left_int` with the transport moved to the other side, which is the form
the transport to the tensor product sheaf of Stacks Tag 01CA consumes. -/
theorem tensorPowAddIso_zero_left_int_hom (c : ℤ) :
    (tensorPowAddIso 𝒪 h𝒪 L 0 c).hom ≫
        eqToHom (congrArg (tensorPow 𝒪 h𝒪 L) (show (0 : ℤ) + c = c from by omega)) =
      (λ_ (tensorPow 𝒪 h𝒪 L c)).hom := by
  refine Eq.trans (congrArg (fun z ↦ z ≫ eqToHom (congrArg (tensorPow 𝒪 h𝒪 L)
    (show (0 : ℤ) + c = c from by omega))) (tensorPowAddIso_zero_left_int 𝒪 h𝒪 L c)) ?_
  exact CategoryTheory.comp_cancel_right (λ_ (tensorPow 𝒪 h𝒪 L c)).hom
    (by rw [eqToHom_trans]; rfl)

end Loc

end AlgebraicGeometry.SheafOfModules

namespace Stacks.AlgebraicGeometry.ThetaMul

section Bridge

open AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

variable (L : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) [IsInvertible 𝒪 h𝒪 L]

/-- The associativity constraint in an arbitrary integer tridegree at the localized structure,
read at the retyping `Stacks.AlgebraicGeometry.ThetaMul.addIsoLoc`. -/
theorem loc_addIso_assoc_int (n m c : ℤ) :
    (addIsoLoc 𝒪 h𝒪 L n m).hom ▷ tensorPow 𝒪 h𝒪 L c ≫
        (addIsoLoc 𝒪 h𝒪 L (n + m) c).hom =
      (α_ (tensorPow 𝒪 h𝒪 L n) (tensorPow 𝒪 h𝒪 L m) (tensorPow 𝒪 h𝒪 L c)).hom ≫
        tensorPow 𝒪 h𝒪 L n ◁ (addIsoLoc 𝒪 h𝒪 L m c).hom ≫
          (addIsoLoc 𝒪 h𝒪 L n (m + c)).hom ≫
            (eqToIso (congrArg (tensorPow 𝒪 h𝒪 L)
              (show n + (m + c) = n + m + c from by ring))).hom :=
  tensorPowAddIso_assoc_int 𝒪 h𝒪 L n m c

/-- **The associativity constraint with the tensor product sheaf of Stacks Tag 01CA as source, in
an arbitrary integer tridegree.** -/
theorem addIsoSheaf_assoc_int (n m c : ℤ) :
    MonoidalCategoryStruct.whiskerRight (self := strStruct 𝒪 h𝒪)
          (tensorPowAddIsoSheaf 𝒪 h𝒪 L n m).hom (tensorPow 𝒪 h𝒪 L c) ≫
        (tensorPowAddIsoSheaf 𝒪 h𝒪 L (n + m) c).hom =
      (MonoidalCategoryStruct.associator (self := strStruct 𝒪 h𝒪) (tensorPow 𝒪 h𝒪 L n)
          (tensorPow 𝒪 h𝒪 L m) (tensorPow 𝒪 h𝒪 L c)).hom ≫
        MonoidalCategoryStruct.whiskerLeft (self := strStruct 𝒪 h𝒪) (tensorPow 𝒪 h𝒪 L n)
            (tensorPowAddIsoSheaf 𝒪 h𝒪 L m c).hom ≫
          (tensorPowAddIsoSheaf 𝒪 h𝒪 L n (m + c)).hom ≫
            (eqToIso (congrArg (tensorPow 𝒪 h𝒪 L)
              (show n + (m + c) = n + m + c from by ring))).hom := by
  simp only [addIsoSheaf_hom 𝒪 h𝒪 L, str_whiskerRight 𝒪 h𝒪, str_whiskerLeft 𝒪 h𝒪,
    str_associator 𝒪 h𝒪, strStruct_tensorObj 𝒪 h𝒪,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, MonoidalCategory.whiskerLeft_hom_inv_assoc]
  rw [loc_addIso_assoc_int 𝒪 h𝒪 L n m c]

/-- **The left unit law of the addition law with the tensor product sheaf of Stacks Tag 01CA as
source, in every integer degree**: multiplying by the zeroth power on the left, after identifying
it with the structure sheaf by `AlgebraicGeometry.SheafOfModules.tensorPowZeroIso`, is the left
unitor of the strict monoidal structure, followed by the transport between the two spellings of
the degree.  This is `Stacks.AlgebraicGeometry.ThetaMul.addIsoSheaf_zero_left` with the
natural-number degree replaced by an integer one. -/
theorem addIsoSheaf_zero_left_int (c : ℤ) :
    MonoidalCategoryStruct.whiskerRight (self := strStruct 𝒪 h𝒪)
          (tensorPowZeroIso 𝒪 h𝒪 L).hom (tensorPow 𝒪 h𝒪 L c) ≫
        (MonoidalCategoryStruct.leftUnitor (self := strStruct 𝒪 h𝒪)
          (tensorPow 𝒪 h𝒪 L c)).hom =
      (tensorPowAddIsoSheaf 𝒪 h𝒪 L 0 c).hom ≫
        eqToHom (congrArg (tensorPow 𝒪 h𝒪 L) (show (0 : ℤ) + c = c from by omega)) := by
  rw [addIsoSheaf_hom 𝒪 h𝒪 L, str_whiskerRight_leftUnitor 𝒪 h𝒪,
    _root_.AlgebraicGeometry.leftUnitor_sheafOfModulesMonoidal_hom, Category.assoc,
    ← tensorPowAddIso_zero_left_int_hom 𝒪 h𝒪 L c]
  exact congrArg (fun z ↦ (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪
      (tensorPow 𝒪 h𝒪 L 0) (tensorPow 𝒪 h𝒪 L c)).inv ≫ z)
    (Stacks.AlgebraicGeometry.ThetaMul.whiskerRight_comp_cancel
      (tensorPowZeroIso 𝒪 h𝒪 L).hom (unitIso 𝒪 h𝒪).inv
      (tensorPowZeroIso_hom_comp_unitIso_inv 𝒪 h𝒪 L)
      ((tensorPowAddIso 𝒪 h𝒪 L 0 c).hom ≫ _))

end Bridge

section Scheme

attribute [local instance] schemeMonoidal strictSchemeMonoidal

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

/-- **The snake identity out of an associativity constraint and the two unit laws**, with every
object and morphism free.  The two inverse laws `u ≫ cu ≫ zh` and `v ≫ cv ≫ zh` of `A` against
`B` are the two multiplications read into the degree zero and then into the unit object; given the
associativity constraint `hassoc`, the factorisations `hP` and `hR` of the two outer
multiplications through the degree zero, the two unit laws `hLu` and `hRu`, and the two
compositions `hgL`, `hgR` of transports, the two cancellations agree.

Isolated with the objects as variables: at the tensor powers the degrees `0 + p`, `p + 0` and `p`
are three spellings of one object, so neither `rw` nor `simp` performs any of these steps. -/
private theorem snake_free {D : Type*} [Category D] [MonoidalCategory D]
    {A B Zu Zv Z0 Z0A ZA0 Tl Tr : D}
    (u : A ⊗ B ⟶ Zu) (v : B ⊗ A ⟶ Zv) (cu : Zu ⟶ Z0) (cv : Zv ⟶ Z0) (zh : Z0 ⟶ 𝟙_ D)
    (P : Zu ⊗ A ⟶ Tl) (R : A ⊗ Zv ⟶ Tr) (t : Tr ⟶ Tl)
    (M : Z0 ⊗ A ⟶ Z0A) (N : A ⊗ Z0 ⟶ ZA0)
    (sL : Z0A ⟶ Tl) (sR : ZA0 ⟶ Tr) (gL : Z0A ⟶ A) (gR : ZA0 ⟶ A) (k : A ≅ Tl)
    (hassoc : u ▷ A ≫ P = (α_ A B A).hom ≫ A ◁ v ≫ R ≫ t)
    (hP : P = (cu ▷ A) ≫ M ≫ sL)
    (hR : R = (A ◁ cv) ≫ N ≫ sR)
    (hLu : zh ▷ A ≫ (λ_ A).hom = M ≫ gL)
    (hRu : A ◁ zh ≫ (ρ_ A).hom = N ≫ gR)
    (hgL : gL ≫ k.hom = sL) (hgR : gR ≫ k.hom = sR ≫ t) :
    (u ≫ cu ≫ zh) ▷ A ≫ (λ_ A).hom =
      (α_ A B A).hom ≫ A ◁ (v ≫ cv ≫ zh) ≫ (ρ_ A).hom := by
  have hleft : ((u ≫ cu ≫ zh) ▷ A ≫ (λ_ A).hom) ≫ k.hom = u ▷ A ≫ P := by
    rw [MonoidalCategory.comp_whiskerRight, MonoidalCategory.comp_whiskerRight]
    simp only [Category.assoc]
    rw [← Category.assoc (zh ▷ A) (λ_ A).hom k.hom, hLu, Category.assoc M gL k.hom, hgL, hP]
  have hright : ((α_ A B A).hom ≫ A ◁ (v ≫ cv ≫ zh) ≫ (ρ_ A).hom) ≫ k.hom =
      (α_ A B A).hom ≫ A ◁ v ≫ R ≫ t := by
    rw [MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (A ◁ zh) (ρ_ A).hom k.hom, hRu, Category.assoc N gR k.hom, hgR, hR]
    simp only [Category.assoc]
  exact (cancel_mono k.hom).mp (hleft.trans (hassoc.trans hright.symm))

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]

/-- A transport along a reflexive equality of degrees is the identity. -/
theorem tensorPowModuleCongr_self {n : ℤ} (h : n = n) :
    (tensorPowModuleCongr X L h).hom = 𝟙 (tensorPowModule X L n) := rfl

/-- Two transports along composable equalities of degrees compose. -/
theorem tensorPowModuleCongr_comp {n m k : ℤ} (h₁ : n = m) (h₂ : m = k) :
    (tensorPowModuleCongr X L h₁).hom ≫ (tensorPowModuleCongr X L h₂).hom =
      (tensorPowModuleCongr X L (h₁.trans h₂)).hom := by
  simp only [tensorPowModuleCongr_hom, eqToHom_trans]

/-- **The associativity constraint on the multiplication of the tensor powers of an invertible
`𝒪_X`-module in an arbitrary integer tridegree**, in the vocabulary
`Stacks.Ample.tensorPowModuleAddIso` the ampleness theory and the twists of `Proj` are written in.
This is `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_natCast_right` with the
restriction on the second and third exponents removed. -/
theorem tensorPowModuleAddIso_assoc_int (n m c : ℤ) :
    MonoidalCategoryStruct.whiskerRight
        (self := (schemeMonoidal X).toMonoidalCategoryStruct)
        (tensorPowModuleAddIso X L n m).hom (tensorPowModule X L c) ≫
        (tensorPowModuleAddIso X L (n + m) c).hom =
      (MonoidalCategoryStruct.associator (self := (schemeMonoidal X).toMonoidalCategoryStruct)
          (tensorPowModule X L n) (tensorPowModule X L m) (tensorPowModule X L c)).hom ≫
        MonoidalCategoryStruct.whiskerLeft
            (self := (schemeMonoidal X).toMonoidalCategoryStruct)
            (tensorPowModule X L n) (tensorPowModuleAddIso X L m c).hom ≫
          (tensorPowModuleAddIso X L n (m + c)).hom ≫
            (tensorPowModuleCongr X L
              (show n + (m + c) = n + m + c from by ring)).hom :=
  addIsoSheaf_assoc_int X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n m c

/-- **The left unit law on the multiplication of the tensor powers of an invertible `𝒪_X`-module,
in every integer degree**, against the left unitor of the strict monoidal structure of Stacks Tag
01CA.  This is `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_left` with the
natural-number degree replaced by an integer one, at the cost of the transport along
`0 + c = c`. -/
theorem tensorPowModuleAddIso_zero_left_int (c : ℤ) :
    (tensorPowModuleZeroIso X L).hom ▷ tensorPowModule X L c ≫
        (λ_ (tensorPowModule X L c)).hom =
      (tensorPowModuleAddIso X L 0 c).hom ≫
        (tensorPowModuleCongr X L (show (0 : ℤ) + c = c from by omega)).hom :=
  addIsoSheaf_zero_left_int X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L c

/-- The multiplication commutes with the transport along an equality of the first exponent. -/
theorem tensorPowModuleAddIso_congr_left {n n' : ℤ} (hn : n = n') (m : ℤ) :
    (tensorPowModuleAddIso X L n' m).hom =
      ((tensorPowModuleCongr X L hn.symm).hom ▷ tensorPowModule X L m) ≫
        (tensorPowModuleAddIso X L n m).hom ≫
          (tensorPowModuleCongr X L (show n + m = n' + m from by omega)).hom := by
  cases hn
  exact Stacks.AlgebraicGeometry.ThetaMul.eq_id_comp_comp_id (tensorPowModuleAddIso X L n m).hom _ _
    (MonoidalCategory.id_whiskerRight _ _) (tensorPowModuleCongr_self X L _)

/-- The multiplication commutes with the transport along an equality of the second exponent. -/
theorem tensorPowModuleAddIso_congr_right (n : ℤ) {m m' : ℤ} (hm : m = m') :
    (tensorPowModuleAddIso X L n m').hom =
      (tensorPowModule X L n ◁ (tensorPowModuleCongr X L hm.symm).hom) ≫
        (tensorPowModuleAddIso X L n m).hom ≫
          (tensorPowModuleCongr X L (show n + m = n + m' from by omega)).hom := by
  cases hm
  exact Stacks.AlgebraicGeometry.ThetaMul.eq_id_comp_comp_id (tensorPowModuleAddIso X L n m).hom _ _
    (MonoidalCategory.whiskerLeft_id _ _) (tensorPowModuleCongr_self X L _)

/-- **The inverse law of the integer tensor powers in the other order**,
`L ^⊗ (-n) ⊗ L ^⊗ n ≅ 𝒪_X`.  This is the multiplication at the bidegree `(-n, n)`, reindexed to
the degree `0`, where the power is the structure sheaf; the mirror of
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleInvIso`, whose two exponents are in the
opposite order. -/
def tensorPowModuleInvIsoLeft (n : ℤ) :
    tensorPowModule X L (-n) ⊗ tensorPowModule X L n ≅ 𝟙_ X.Modules :=
  tensorPowModuleAddIso X L (-n) n ≪≫
    tensorPowModuleCongr X L (show -n + n = 0 from by ring) ≪≫ tensorPowModuleZeroIso X L

/-- **The two inverse laws of an integer tensor power of an invertible `𝒪_X`-module are
snake-compatible**: for `p + q = 0` the power `L ^⊗ q` is a tensor inverse of `L ^⊗ p` on both
sides, the two laws being the multiplication at the bidegrees `(p, q)` and `(q, p)` read into the
degree `0`, and cancelling the first two factors of `L ^⊗ p ⊗ L ^⊗ q ⊗ L ^⊗ p` against the first
agrees with cancelling the last two against the second.

This is `Stacks.TensorPowers.TensorInverse.addIso_snake` in the vocabulary the ampleness theory
and the twists of `Proj` are written in and against the structure maps of Stacks Tag 01CA.  The
proof is the same: the associativity constraint in the tridegree `(p, q, p)`, which
`tensorPowModuleAddIso_assoc_int` now supplies, together with the two unit laws, which in the
degree `0` turn the two outer multiplications into the left and the right unitor. -/
theorem tensorPowModuleAddIso_snake (p q : ℤ) (hpq : p + q = 0) :
    MonoidalCategoryStruct.whiskerRight
          (self := (schemeMonoidal X).toMonoidalCategoryStruct)
          ((tensorPowModuleAddIso X L p q).hom ≫ (tensorPowModuleCongr X L hpq).hom ≫
            (tensorPowModuleZeroIso X L).hom) (tensorPowModule X L p) ≫
        (MonoidalCategoryStruct.leftUnitor (self := (schemeMonoidal X).toMonoidalCategoryStruct)
          (tensorPowModule X L p)).hom =
      (MonoidalCategoryStruct.associator (self := (schemeMonoidal X).toMonoidalCategoryStruct)
          (tensorPowModule X L p) (tensorPowModule X L q) (tensorPowModule X L p)).hom ≫
        MonoidalCategoryStruct.whiskerLeft
            (self := (schemeMonoidal X).toMonoidalCategoryStruct)
            (tensorPowModule X L p) ((tensorPowModuleAddIso X L q p).hom ≫
              (tensorPowModuleCongr X L (show q + p = 0 from by omega)).hom ≫
                (tensorPowModuleZeroIso X L).hom) ≫
          (MonoidalCategoryStruct.rightUnitor (self := (schemeMonoidal X).toMonoidalCategoryStruct)
            (tensorPowModule X L p)).hom :=
  @snake_free X.Modules _ (schemeMonoidal X) _ _ _ _ _ _ _ _ _
    (tensorPowModuleAddIso X L p q).hom (tensorPowModuleAddIso X L q p).hom
    (tensorPowModuleCongr X L hpq).hom
    (tensorPowModuleCongr X L (show q + p = 0 from by omega)).hom
    (tensorPowModuleZeroIso X L).hom
    (tensorPowModuleAddIso X L (p + q) p).hom
    (tensorPowModuleAddIso X L p (q + p)).hom
    (tensorPowModuleCongr X L (show p + (q + p) = p + q + p from by ring)).hom
    (tensorPowModuleAddIso X L 0 p).hom
    (tensorPowModuleAddIso X L p 0).hom
    (tensorPowModuleCongr X L (show (0 : ℤ) + p = p + q + p from by omega)).hom
    (tensorPowModuleCongr X L (show p + 0 = p + (q + p) from by omega)).hom
    (tensorPowModuleCongr X L (show (0 : ℤ) + p = p from by omega)).hom
    (tensorPowModuleCongr X L (show p + 0 = p from by omega)).hom
    (tensorPowModuleCongr X L (show p = p + q + p from by omega))
    (tensorPowModuleAddIso_assoc_int X L p q p)
    (tensorPowModuleAddIso_congr_left X L (show (0 : ℤ) = p + q from by omega) p)
    (tensorPowModuleAddIso_congr_right X L p (show (0 : ℤ) = q + p from by omega))
    (tensorPowModuleAddIso_zero_left_int X L p)
    (tensorPowModuleAddIso_zero_right_int X L p)
    (tensorPowModuleCongr_comp X L _ _)
    ((tensorPowModuleCongr_comp X L (show p + 0 = p from by omega)
        (show p = p + q + p from by omega)).trans
      (tensorPowModuleCongr_comp X L (show p + 0 = p + (q + p) from by omega)
        (show p + (q + p) = p + q + p from by ring)).symm)

end Scheme

section DegreeOpen

open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen

attribute [local instance] schemeMonoidal strictSchemeMonoidal

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-! The two helpers this section used to declare -- `mono_iso_hom`, the forward map of an
isomorphism as a `Mono` term rather than an instance, and `square_step_left_of_mono`,
`Stacks.Monoidal.square_step_left` with that instance taken explicitly -- are
`Stacks.Monoidal.mono_iso_hom` and `Stacks.Monoidal.square_step_left_of_mono` of
`StacksFrontier/AlgebraicGeometry/TwistTensor/GradedLaurentMul.lean`, which are public and have the
same statements. The copies are deleted and the chase below uses those. -/

/-- **The multiplicativity square transported along equalities of the two degrees.**  Every square
chased below is produced at one spelling of its bidegree and consumed at another; this moves it,
and it is the whole reason the chase can be run with `omega`-proved degree identities rather than
with transports. -/
theorem thetaInt_mul_of_eq {p q p' q' : ℤ} (hp : p = p') (hq : q = q')
    (H : (tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
            (twist 𝒮 d (d : ℤ)) p q).hom ≫ (thetaInt 𝒮 d (p + q)).hom =
          ((thetaInt 𝒮 d p).hom ⊗ₘ (thetaInt 𝒮 d q).hom) ≫ (twistMulIso 𝒮 d p q).hom) :
    (tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) p' q').hom ≫ (thetaInt 𝒮 d (p' + q')).hom =
      ((thetaInt 𝒮 d p').hom ⊗ₘ (thetaInt 𝒮 d q').hom) ≫ (twistMulIso 𝒮 d p' q').hom := by
  cases hp; cases hq; exact H

/-- Three transports around a triangle of equal objects compose to the identity.  Isolated with
the objects as variables: at the concrete twists the composite is not type-correct at the
transparency `rw` checks its motive at. -/
private theorem eqToHom_comp_comp_eq_id {D : Type*} [Category D] {A B E : D} (p : A = B)
    (q : B = E) (r : E = A) : eqToHom p ≫ eqToHom q ≫ eqToHom r = 𝟙 A := by
  rw [eqToHom_trans, eqToHom_trans, eqToHom_refl]

/-- The inverse-law square, with every object and morphism free: the comparison of the two inverse
laws, followed by the chain of transports that identifies the degree zero value of the target
family with the unit object and back, is the multiplicativity square in that bidegree. -/
private theorem inv_law_free {D : Type*} [Category D] {A B Z Un T0 Td0 Tpq P : D}
    (u : A ⟶ B) (c : B ⟶ Z) (zh : Z ⟶ Un) (w : Un ⟶ T0) (e0 : T0 ⟶ Td0) (e1 : Td0 ⟶ Tpq)
    (tp : A ⟶ P) (mu : P ⟶ Tpq) (ff : Tpq ⟶ T0) (wi : T0 ⟶ Un)
    (hinv : u ≫ c ≫ zh = tp ≫ mu ≫ ff ≫ wi)
    (hw : wi ≫ w = 𝟙 T0) (he : ff ≫ e0 ≫ e1 = 𝟙 Tpq) :
    u ≫ c ≫ zh ≫ w ≫ e0 ≫ e1 = tp ≫ mu := by
  have h := congrArg (fun z ↦ z ≫ w ≫ e0 ≫ e1) hinv
  simp only [Category.assoc] at h
  rw [h, ← Category.assoc wi w (e0 ≫ e1), hw, Category.id_comp, he, Category.comp_id]

/-- **The inverse-law square for the comparison family**, in the bidegree `(-(j+1), j+1)`: the
comparisons in the two degrees, tensored together, carry the inverse law of the tensor powers to
the inverse law of the twists.  This is the one face of the multiplicativity statement that no
arrangement of `Stacks.AlgebraicGeometry.ThetaMul.square_step` and
`Stacks.Monoidal.square_step_left` reaches from the nonnegative degrees, and it holds because in a
negative degree the comparison is *defined* as the comparison induced on the tensor inverses:
`Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso` is the identity that says so, and
its snake hypothesis is `tensorPowModuleAddIso_snake`.

The degree zero value of the family is the identification
`𝒪_{U_d}(d)^{⊗ 0} ≅ 𝒪_{U_d} ≅ 𝒪_{U_d}(0)`, which is what turns that identity into a square. -/
theorem thetaInt_mul_neg_succ (j : ℕ) :
    (tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) (-(((j + 1 : ℕ)) : ℤ)) (((j + 1 : ℕ)) : ℤ)).hom ≫
        (thetaInt 𝒮 d (-(((j + 1 : ℕ)) : ℤ) + (((j + 1 : ℕ)) : ℤ))).hom =
      ((thetaInt 𝒮 d (-(((j + 1 : ℕ)) : ℤ))).hom ⊗ₘ
          (thetaInt 𝒮 d (((j + 1 : ℕ)) : ℤ)).hom) ≫
        (twistMulIso 𝒮 d (-(((j + 1 : ℕ)) : ℤ)) (((j + 1 : ℕ)) : ℤ)).hom := by
  refine Eq.trans (congrArg (fun z ↦ (tensorPowModuleAddIso
      (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ))
      (-(((j + 1 : ℕ)) : ℤ)) (((j + 1 : ℕ)) : ℤ)).hom ≫ z)
    (thetaInt_congr 𝒮 d (show -(((j + 1 : ℕ)) : ℤ) + (((j + 1 : ℕ)) : ℤ) = 0 from
      by ring))) ?_
  exact inv_law_free
    (tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ)) (-(((j + 1 : ℕ)) : ℤ)) (((j + 1 : ℕ)) : ℤ)).hom
    (tensorPowModuleCongr (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ))
      (show -(((j + 1 : ℕ)) : ℤ) + (((j + 1 : ℕ)) : ℤ) = 0 from by ring)).hom
    (tensorPowModuleZeroIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ))).hom
    (twistZeroIsoUnit 𝒮 d).inv
    (eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
      (show (0 : ℤ) = (d : ℤ) * 0 from by ring)))
    (eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
      (show (d : ℤ) * 0 = (d : ℤ) * (-(((j + 1 : ℕ)) : ℤ) + (((j + 1 : ℕ)) : ℤ)) from by ring)))
    ((thetaInt 𝒮 d (-(((j + 1 : ℕ)) : ℤ))).hom ⊗ₘ (thetaInt 𝒮 d (((j + 1 : ℕ)) : ℤ)).hom)
    (twistMulIso 𝒮 d (-(((j + 1 : ℕ)) : ℤ)) (((j + 1 : ℕ)) : ℤ)).hom
    (eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
      (show (d : ℤ) * (-(((j + 1 : ℕ)) : ℤ) + (((j + 1 : ℕ)) : ℤ)) = 0 from by ring)))
    (twistZeroIsoUnit 𝒮 d).hom
    (Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso (theta 𝒮 d (j + 1))
      (tensorPowModuleInvIso 𝒮 d (((j + 1 : ℕ)) : ℤ))
      (tensorPowModuleInvIsoLeft (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (twist 𝒮 d (d : ℤ)) (((j + 1 : ℕ)) : ℤ))
      (twistInvIso 𝒮 d (((j + 1 : ℕ)) : ℤ))
      (tensorPowModuleAddIso_snake (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (twist 𝒮 d (d : ℤ)) (-(((j + 1 : ℕ)) : ℤ)) (((j + 1 : ℕ)) : ℤ) (by ring))).symm
    (twistZeroIsoUnit 𝒮 d).hom_inv_id
    (eqToHom_comp_comp_eq_id _ _ _)

/-- **The inverse-law square for the comparison family, at every bidegree summing to zero with a
nonnegative second exponent.**  In the degree zero it is the right unit law
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_zero`, and otherwise it is
`thetaInt_mul_neg_succ`. -/
theorem thetaInt_mul_add_eq_zero (p q : ℤ) (hq : 0 ≤ q) (hpq : p + q = 0) :
    (tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) p q).hom ≫ (thetaInt 𝒮 d (p + q)).hom =
      ((thetaInt 𝒮 d p).hom ⊗ₘ (thetaInt 𝒮 d q).hom) ≫ (twistMulIso 𝒮 d p q).hom := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  cases j with
  | zero =>
      exact thetaInt_mul_of_eq 𝒮 d (show (0 : ℤ) = p from by omega)
        (show (0 : ℤ) = (((0 : ℕ)) : ℤ) from by omega) (thetaInt_mul_zero 𝒮 d 0)
  | succ i =>
      exact thetaInt_mul_of_eq 𝒮 d (show -(((i + 1 : ℕ)) : ℤ) = p from by omega) rfl
        (thetaInt_mul_neg_succ 𝒮 d i)

/-- Two transports along mutually inverse equalities of objects cancel.  Isolated with the
objects as variables, for the same reason as `eqToHom_comp_comp_eq_id`. -/
private theorem eqToHom_comp_eq_id {D : Type*} [Category D] {A B : D} (p : A = B) (q : B = A) :
    eqToHom p ≫ eqToHom q = 𝟙 A := by
  rw [eqToHom_trans, eqToHom_refl]

/-- **Moving a transport of the total degree from the comparison onto the target family's
multiplication**, with every object and morphism free.  This is the one bookkeeping step between
the multiplicativity square in a bidegree and the shape of the `(A, BC)` corner that
`Stacks.AlgebraicGeometry.ThetaMul.square_step` produces and `Stacks.Monoidal.square_step_left`
consumes. -/
theorem absorb_iff {D : Type*} [Category D] {A B E F G H : D}
    (x : A ⟶ B) (c : B ⟶ E) (θ : E ⟶ F) (ee : F ⟶ G) (ef : G ⟶ F)
    (tp : A ⟶ H) (mu : H ⟶ G) (hef : ee ≫ ef = 𝟙 F) (hfe : ef ≫ ee = 𝟙 G) :
    (x ≫ c ≫ θ ≫ ee = tp ≫ mu) ↔ ((x ≫ c) ≫ θ = tp ≫ mu ≫ ef) := by
  have : IsIso ef := ⟨ee, hfe, hef⟩
  rw [← cancel_mono ef]
  simp only [Category.assoc, hef, Category.comp_id]

/-- **The multiplicativity square in the bidegree `(p, b + c)`, read at the `(A, BC)` corner of
the associativity diagram in the tridegree `(p, b, c)`.**  The two sides differ only by where the
transport between the two spellings `p + (b + c)` and `p + b + c` of the total degree sits: on the
comparison, or on the canonical multiplication of the twists.  The second form is what
`Stacks.AlgebraicGeometry.ThetaMul.square_step` produces and what
`Stacks.Monoidal.square_step_left` consumes, because the associativity constraints of both
families carry that transport. -/
theorem thetaInt_mul_corner_iff (p b c : ℤ) :
    ((tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
            (twist 𝒮 d (d : ℤ)) p (b + c)).hom ≫ (thetaInt 𝒮 d (p + (b + c))).hom =
        ((thetaInt 𝒮 d p).hom ⊗ₘ (thetaInt 𝒮 d (b + c)).hom) ≫
          (twistMulIso 𝒮 d p (b + c)).hom) ↔
      (((tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
              (twist 𝒮 d (d : ℤ)) p (b + c)).hom ≫
            (tensorPowModuleCongr (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
              (twist 𝒮 d (d : ℤ))
              (show p + (b + c) = p + b + c from by ring)).hom) ≫
          (thetaInt 𝒮 d (p + b + c)).hom =
        ((thetaInt 𝒮 d p).hom ⊗ₘ (thetaInt 𝒮 d (b + c)).hom) ≫
          (twistMulIso 𝒮 d p (b + c)).hom ≫
            eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
              (show (d : ℤ) * (p + (b + c)) = (d : ℤ) * (p + b + c) from by ring))) :=
  Iff.trans
    (Iff.of_eq (congrArg (fun z ↦ z = ((thetaInt 𝒮 d p).hom ⊗ₘ
        (thetaInt 𝒮 d (b + c)).hom) ≫ (twistMulIso 𝒮 d p (b + c)).hom)
      (congrArg (fun z ↦ (tensorPowModuleAddIso
          (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ)) p (b + c)).hom ≫ z)
        (thetaInt_congr 𝒮 d (show p + (b + c) = p + b + c from by ring)))))
    (absorb_iff _ _ _ _ _ _ _ (eqToHom_comp_eq_id _ _) (eqToHom_comp_eq_id _ _))

/-- **Multiplicativity of the comparison family in the bidegree `(k, 1)` for an arbitrary integer
`k`.**  In a nonnegative degree this is `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_natCast`.
In a negative degree `k = -(a+1)` it is `Stacks.Monoidal.square_step_left` applied to the
associativity diagram in the tridegree `(-(a+1), 1, a)`, whose other three squares are the two
inverse-law squares at `(-a, a)` and at `(-(a+1), a+1)` and the natural-number square at
`(1, a)`. -/
theorem thetaInt_mul_one (k : ℤ) :
    (tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) k 1).hom ≫ (thetaInt 𝒮 d (k + 1)).hom =
      ((thetaInt 𝒮 d k).hom ⊗ₘ (thetaInt 𝒮 d 1).hom) ≫ (twistMulIso 𝒮 d k 1).hom := by
  by_cases hk : 0 ≤ k
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    exact thetaInt_mul_of_eq 𝒮 d rfl (show (((1 : ℕ)) : ℤ) = 1 from by omega)
      (thetaInt_mul_natCast 𝒮 d j 1)
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, k = -((a : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    exact Stacks.Monoidal.square_step_left_of_mono
      (Stacks.Monoidal.mono_iso_hom (twistMulIso 𝒮 d (-((a : ℤ) + 1) + 1) (a : ℤ)))
      (tensorPowModuleInvIso 𝒮 d (a : ℤ))
      (tensorPowModuleAddIso_assoc_int (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (twist 𝒮 d (d : ℤ)) (-((a : ℤ) + 1)) 1 (a : ℤ))
      (twistMulIso_assoc 𝒮 d (-((a : ℤ) + 1)) 1 (a : ℤ))
      (thetaInt_mul_add_eq_zero 𝒮 d (-((a : ℤ) + 1) + 1) (a : ℤ) (by omega) (by ring))
      (thetaInt_mul_of_eq 𝒮 d (show (((1 : ℕ)) : ℤ) = 1 from by omega) rfl
        (thetaInt_mul_natCast 𝒮 d 1 a))
      ((thetaInt_mul_corner_iff 𝒮 d (-((a : ℤ) + 1)) 1 (a : ℤ)).mp
        (thetaInt_mul_add_eq_zero 𝒮 d (-((a : ℤ) + 1)) (1 + (a : ℤ)) (by omega) (by ring)))

/-- **Multiplicativity of the comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` in an arbitrary
integer bidegree**: the addition law `Stacks.Ample.tensorPowModuleAddIso` of the tensor powers at
`(n, m)`, followed by the comparison in the degree `n + m`, is the comparisons in the degrees `n`
and `m` on the two factors, followed by the canonical multiplication
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso` at `(dn, dm)`.  Both degrees
are arbitrary integers.

This is `Stacks.AlgebraicGeometry.ThetaMul.theta_mul` with the restriction to natural-number
degrees removed.  The induction is over `ℤ` in the second degree, with the right unit law
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_zero` as base case,
`Stacks.AlgebraicGeometry.ThetaMul.square_step` upwards and `Stacks.Monoidal.square_step_left`
downwards, both fed with the associativity constraints `tensorPowModuleAddIso_assoc_int` and
`Stacks.AlgebraicGeometry.ThetaMul.twistMulIso_assoc` in the tridegree `(n, m, 1)` and with the
bidegree `(k, 1)` column `thetaInt_mul_one`. -/
theorem thetaInt_mul (n m : ℤ) :
    (tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) n m).hom ≫ (thetaInt 𝒮 d (n + m)).hom =
      ((thetaInt 𝒮 d n).hom ⊗ₘ (thetaInt 𝒮 d m).hom) ≫ (twistMulIso 𝒮 d n m).hom := by
  induction m using Int.induction_on with
  | zero => exact thetaInt_mul_zero 𝒮 d n
  | succ i ih =>
      exact (thetaInt_mul_corner_iff 𝒮 d n (i : ℤ) 1).mpr
        (square_step
          (tensorPowModuleAddIso_assoc_int (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
            (twist 𝒮 d (d : ℤ)) n (i : ℤ) 1)
          (twistMulIso_assoc 𝒮 d n (i : ℤ) 1) ih
          (thetaInt_mul_one 𝒮 d (n + (i : ℤ))) (thetaInt_mul_one 𝒮 d (i : ℤ)))
  | pred i ih =>
      exact Stacks.Monoidal.square_step_left_of_mono
        (Stacks.Monoidal.mono_iso_hom (twistMulIso 𝒮 d (n + (-(i : ℤ) - 1)) 1))
        (tensorPowModuleInvIso 𝒮 d 1)
        (tensorPowModuleAddIso_assoc_int (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) n (-(i : ℤ) - 1) 1)
        (twistMulIso_assoc 𝒮 d n (-(i : ℤ) - 1) 1)
        (thetaInt_mul_one 𝒮 d (n + (-(i : ℤ) - 1)))
        (thetaInt_mul_one 𝒮 d (-(i : ℤ) - 1))
        ((thetaInt_mul_corner_iff 𝒮 d n (-(i : ℤ) - 1) 1).mp
          (thetaInt_mul_of_eq 𝒮 d rfl (show -(i : ℤ) = -(i : ℤ) - 1 + 1 from by omega) ih))

end DegreeOpen

end Stacks.AlgebraicGeometry.ThetaMul

end
