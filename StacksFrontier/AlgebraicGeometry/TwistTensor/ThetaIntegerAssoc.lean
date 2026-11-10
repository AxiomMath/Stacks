module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerMul
public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerLeft

/-!
# The multiplication of integer tensor powers is associative in a negative first degree

`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc` is the associativity constraint
of the multiplication `Stacks.Ample.tensorPowModuleAddIso` of the integer tensor powers of an
invertible `𝒪_X`-module, against the associator of the strict monoidal structure of Stacks Tag
01CA, with all three exponents natural numbers.  This file removes the restriction on the
**first** exponent, which was never a restriction on the mathematics: the addition law recurses on
its second exponent alone, so the constraint holds for an arbitrary integer first exponent, and
`Stacks.TensorPowers.TensorInverse.addNatIso_assoc` proves it where the powers are defined.  What
is here is the transport of that statement along the same three steps the natural-number
constraint is transported along, plus the two pieces of monoidal algebra that a multiplicativity
statement crossing the degree zero consumes.

**No dictionary between the repository's two integer power families is needed for this.**  The
note at the head of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/ChartDegreewiseFamily.lean` reads the
natural-number restriction as calling for a comparison with
`Stacks.SheafOfModules.TensorPower.monoidalMulIso`, whose associativity law does hold in every
integer degree; that comparison is not used below and the restriction is lifted inside the family
that has it.

## Main results

* `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_natCast_right`: **the
  associativity constraint on the multiplication of the tensor powers of an invertible
  `𝒪_X`-module with an arbitrary integer first exponent**, in the vocabulary the ampleness theory
  and the twists of `Proj` are written in.  This is the conclusion of the file.
* `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_assoc_natCast_right`,
  `Stacks.AlgebraicGeometry.ThetaMul.loc_addIso_assoc_natCast_right` and
  `Stacks.AlgebraicGeometry.ThetaMul.addIsoSheaf_assoc_natCast_right`: the same constraint at the
  three intermediate spellings — the localized monoidal structure on sheaves of modules, its
  retyping `Stacks.AlgebraicGeometry.ThetaMul.addIsoLoc`, and the tensor product sheaf of Stacks
  Tag 01CA as source.  Each mirrors the natural-number statement of
  `StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaMultiplicativity.lean` line for line.
* `Stacks.Monoidal.whiskerRight_injective_of_tensorInverse`: **right whiskering by a
  tensor-invertible object is injective on morphisms.**  This replaces the
  `MonoidalCategory.tensorRight` faithfulness hypothesis that the comparison lemmas of
  `StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerMul.lean` carry, which no instance in
  the repository discharges for the tensor powers of a module.
* `Stacks.Monoidal.square_step_left`: **three commuting squares out of an associativity diagram
  force the fourth, solved for the left-hand square.**  `square_step` of
  `StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaMultiplicativity.lean` derives the square at
  `(A, BC)`; this derives the square at `(A, B)`, which is the direction a multiplicativity
  statement in a negative degree needs, the known squares being the ones in which the first
  exponent has been pushed back up to zero or above.

## Implementation notes

The first three transports are definitional: `tensorPowAddIso` is
`Stacks.TensorPowers.TensorInverse.addIso` of the chosen inverse, and `addIsoLoc` is a retyping,
so each is discharged by `exact`.  Only `addIsoSheaf_assoc_natCast_right` has content, and it is
the same `simp only` over the structure maps of the strict structure as its natural-number
counterpart: the degrees play no part in that proof, which is why the generalisation costs
nothing there.

`square_step_left` asks for `Mono p'` on the target family's multiplication and for a tensor
inverse of the third object; both are available at a tensor power and at a twist, where every
multiplication is an isomorphism.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)

## What this is for

**The multiplicativity of `Stacks.AlgebraicGeometry.ThetaMul.thetaInt` in the bidegree `(n, 1)`
for a negative `n`**, which is now `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_one` of
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerBidegree.lean`.  With
`Stacks.AlgebraicGeometry.ThetaMul.twistMulIso_assoc` on the twist side, `square_step_left`
reduces it, for `n = -(a + 1)`, to the three squares at the bidegrees `(-a, a)`, `(1, a)` and
`(-(a+1), a+1)`.  The middle one is
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_natCast`.  The outer two are **the inverse-law
square**: the comparison in the degrees `-m` and `m` carries the inverse law of the tensor powers
to the inverse law of the twists, and that is
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_neg_succ`.

That square is where the content sits, and it is not reachable from the squares in nonnegative
degrees by any arrangement of `square_step` and `square_step_left`: every face of an
associativity diagram with natural-number second and third exponents has a nonnegative second
exponent and a first exponent of the same family one started with, so no diagram anchors the
column `(n, 1)`.  `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp` is the identity that proves
it — `thetaInt` in a negative degree is by definition the comparison of two tensor inverses — and
its hypothesis is the compatibility of the two orders of the inverse law of `L ^⊗ (-m)`.  That
compatibility needs **no** dictionary to the repository's other power family and no commutativity
of this one: `Stacks.TensorPowers.TensorInverse.addIso_snake` derives it from the associativity
constraint in the tridegree `(-m, m, -m)`, and
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_snake` repeats that derivation at the
modules of a scheme, where the comparison family lives.

The associativity constraint used there needs all three exponents arbitrary integers, so the
natural-number restriction on the second and third exponents left below is lifted in turn by
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int`.
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

universe v u w

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open Stacks.Ample
open Stacks.RelativeVeryAmple
open Stacks.SheafOfModules.TensorSheafification

namespace Stacks.Monoidal

section Cancel

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- **Right whiskering by a tensor-invertible object is injective on morphisms.**  If `Z` has a
tensor inverse `Z'` then a morphism is determined by its right whiskering into `Z`: it is
recovered from it by whiskering into `Z'`, reassociating and cancelling with the inverse law. -/
theorem whiskerRight_injective_of_tensorInverse {X Y Z Z' : D} (e : Z ⊗ Z' ≅ 𝟙_ D)
    {u v : X ⟶ Y} (huv : u ▷ Z = v ▷ Z) : u = v := by
  have key : ∀ w : X ⟶ Y,
      (X ◁ e.hom) ≫ (ρ_ X).hom ≫ w =
        (α_ X Z Z').inv ≫ ((w ▷ Z) ▷ Z') ≫ (α_ Y Z Z').hom ≫ (Y ◁ e.hom) ≫
          (ρ_ Y).hom := by
    intro w
    have hassoc : (α_ X Z Z').inv ≫ ((w ▷ Z) ▷ Z') ≫ (α_ Y Z Z').hom = w ▷ (Z ⊗ Z') := by
      rw [MonoidalCategory.associator_naturality_left, Iso.inv_hom_id_assoc]
    calc (X ◁ e.hom) ≫ (ρ_ X).hom ≫ w
        = (X ◁ e.hom) ≫ (w ▷ 𝟙_ D) ≫ (ρ_ Y).hom := by
          rw [MonoidalCategory.rightUnitor_naturality]
      _ = (w ▷ (Z ⊗ Z')) ≫ (Y ◁ e.hom) ≫ (ρ_ Y).hom := by
          rw [← Category.assoc, MonoidalCategory.whisker_exchange, Category.assoc]
      _ = _ := by rw [← hassoc]; simp only [Category.assoc]
  refine (cancel_epi (ρ_ X).hom).mp ((cancel_epi (X ◁ e.hom)).mp ?_)
  rw [key u, key v, huv]

end Cancel

section Square

variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- **Three commuting squares out of an associativity diagram force the fourth, solved for the
left-hand square.**  This is `Stacks.AlgebraicGeometry.ThetaMul.square_step` with the roles of the
conclusion and the first hypothesis exchanged: given the squares at `(AB, C)`, at `(B, C)` and at
`(A, BC)`, the square at `(A, B)` commutes.

Where `square_step` cancels the associator and `A ◁ b`, this one cancels the multiplication `p'`
of the target family, the comparison `h` in the third degree, and finally the right whiskering by
`C`, for which `C` is asked to have a tensor inverse. -/
theorem square_step_left {A B Cc AB BC ABC A' B' C' AB' BC' ABC' Z' : D}
    {a : A ⊗ B ⟶ AB} {b : B ⊗ Cc ≅ BC} {p : AB ⊗ Cc ⟶ ABC} {r : A ⊗ BC ⟶ ABC}
    {a' : A' ⊗ B' ⟶ AB'} {b' : B' ⊗ C' ⟶ BC'} {p' : AB' ⊗ C' ⟶ ABC'}
    {r' : A' ⊗ BC' ⟶ ABC'}
    {f : A ⟶ A'} {g : B ⟶ B'} {h : Cc ≅ C'} {fg : AB ⟶ AB'} {gh : BC ⟶ BC'}
    {fgh : ABC ⟶ ABC'} [Mono p'] (e : Cc ⊗ Z' ≅ 𝟙_ D)
    (hL : a ▷ Cc ≫ p = (α_ A B Cc).hom ≫ A ◁ b.hom ≫ r)
    (hR : a' ▷ C' ≫ p' = (α_ A' B' C').hom ≫ A' ◁ b' ≫ r')
    (h2 : p ≫ fgh = (fg ⊗ₘ h.hom) ≫ p')
    (h3 : b.hom ≫ gh = (g ⊗ₘ h.hom) ≫ b')
    (hD : r ≫ fgh = (f ⊗ₘ gh) ≫ r') :
    a ≫ fg = (f ⊗ₘ g) ≫ a' := by
  have hX : (a ≫ fg) ▷ Cc ≫ AB' ◁ h.hom = ((f ⊗ₘ g) ≫ a') ▷ Cc ≫ AB' ◁ h.hom := by
    refine (cancel_mono p').mp ?_
    simp only [Category.assoc]
    calc (a ≫ fg) ▷ Cc ≫ AB' ◁ h.hom ≫ p'
        = a ▷ Cc ≫ (fg ⊗ₘ h.hom) ≫ p' := by
          rw [MonoidalCategory.tensorHom_def, MonoidalCategory.comp_whiskerRight]
          simp only [Category.assoc]
      _ = (a ▷ Cc ≫ p) ≫ fgh := by rw [Category.assoc, h2]
      _ = (α_ A B Cc).hom ≫ A ◁ b.hom ≫ r ≫ fgh := by rw [hL]; simp only [Category.assoc]
      _ = (α_ A B Cc).hom ≫ A ◁ b.hom ≫ (f ⊗ₘ gh) ≫ r' := by rw [hD]
      _ = (α_ A B Cc).hom ≫ (f ⊗ₘ (b.hom ≫ gh)) ≫ r' := by
          rw [← Category.assoc (A ◁ b.hom), ← MonoidalCategory.id_tensorHom,
            MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
      _ = (α_ A B Cc).hom ≫ (f ⊗ₘ ((g ⊗ₘ h.hom) ≫ b')) ≫ r' := by rw [h3]
      _ = (α_ A B Cc).hom ≫ (f ⊗ₘ (g ⊗ₘ h.hom)) ≫ A' ◁ b' ≫ r' := by
          rw [← Category.assoc (f ⊗ₘ (g ⊗ₘ h.hom)), ← MonoidalCategory.id_tensorHom,
            MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
      _ = ((f ⊗ₘ g) ⊗ₘ h.hom) ≫ (α_ A' B' C').hom ≫ A' ◁ b' ≫ r' := by
          rw [← Category.assoc, ← MonoidalCategory.associator_naturality]
          simp only [Category.assoc]
      _ = ((f ⊗ₘ g) ⊗ₘ h.hom) ≫ a' ▷ C' ≫ p' := by rw [hR]
      _ = ((f ⊗ₘ g) ≫ a') ▷ Cc ≫ AB' ◁ h.hom ≫ p' := by
          rw [MonoidalCategory.comp_whiskerRight, MonoidalCategory.tensorHom_def]
          simp only [Category.assoc]
          rw [MonoidalCategory.whisker_exchange_assoc]
  exact whiskerRight_injective_of_tensorInverse e ((cancel_mono (AB' ◁ h.hom)).mp hX)

end Square

end Stacks.Monoidal

namespace AlgebraicGeometry.SheafOfModules

section Loc

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) [IsInvertible 𝒪 h𝒪 L]

/-- **The associativity constraint on the multiplication of tensor powers with an arbitrary
integer first exponent.** -/
theorem tensorPowAddIso_assoc_natCast_right (n : ℤ) (b c : ℕ) :
    (tensorPowAddIso 𝒪 h𝒪 L n (b : ℤ)).hom ▷ tensorPow 𝒪 h𝒪 L (c : ℤ) ≫
        (tensorPowAddIso 𝒪 h𝒪 L (n + (b : ℤ)) (c : ℤ)).hom =
      (α_ (tensorPow 𝒪 h𝒪 L n) (tensorPow 𝒪 h𝒪 L (b : ℤ))
          (tensorPow 𝒪 h𝒪 L (c : ℤ))).hom ≫
        tensorPow 𝒪 h𝒪 L n ◁ (tensorPowAddIso 𝒪 h𝒪 L (b : ℤ) (c : ℤ)).hom ≫
          (tensorPowAddIso 𝒪 h𝒪 L n ((b : ℤ) + (c : ℤ))).hom ≫
            (eqToIso (congrArg (tensorPow 𝒪 h𝒪 L)
              (show n + ((b : ℤ) + (c : ℤ)) = n + (b : ℤ) + (c : ℤ) from by ring))).hom :=
  Stacks.TensorPowers.TensorInverse.addNatIso_assoc (tensorInverse 𝒪 h𝒪 L) n b c

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

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The associativity constraint at the localized structure, read at the retyping
`Stacks.AlgebraicGeometry.ThetaMul.addIsoLoc`. -/
theorem loc_addIso_assoc_natCast_right (n : ℤ) (b c : ℕ) :
    (addIsoLoc 𝒪 h𝒪 L n (b : ℤ)).hom ▷ tensorPow 𝒪 h𝒪 L (c : ℤ) ≫
        (addIsoLoc 𝒪 h𝒪 L (n + (b : ℤ)) (c : ℤ)).hom =
      (α_ (tensorPow 𝒪 h𝒪 L n) (tensorPow 𝒪 h𝒪 L (b : ℤ))
          (tensorPow 𝒪 h𝒪 L (c : ℤ))).hom ≫
        tensorPow 𝒪 h𝒪 L n ◁ (addIsoLoc 𝒪 h𝒪 L (b : ℤ) (c : ℤ)).hom ≫
          (addIsoLoc 𝒪 h𝒪 L n ((b : ℤ) + (c : ℤ))).hom ≫
            (eqToIso (congrArg (tensorPow 𝒪 h𝒪 L)
              (show n + ((b : ℤ) + (c : ℤ)) = n + (b : ℤ) + (c : ℤ) from by ring))).hom :=
  tensorPowAddIso_assoc_natCast_right 𝒪 h𝒪 L n b c

/-- **The associativity constraint with the tensor product sheaf of Stacks Tag 01CA as source and
an arbitrary integer first exponent.** -/
theorem addIsoSheaf_assoc_natCast_right (n : ℤ) (b c : ℕ) :
    MonoidalCategoryStruct.whiskerRight (self := strStruct 𝒪 h𝒪)
          (tensorPowAddIsoSheaf 𝒪 h𝒪 L n (b : ℤ)).hom (tensorPow 𝒪 h𝒪 L (c : ℤ)) ≫
        (tensorPowAddIsoSheaf 𝒪 h𝒪 L (n + (b : ℤ)) (c : ℤ)).hom =
      (MonoidalCategoryStruct.associator (self := strStruct 𝒪 h𝒪) (tensorPow 𝒪 h𝒪 L n)
          (tensorPow 𝒪 h𝒪 L (b : ℤ)) (tensorPow 𝒪 h𝒪 L (c : ℤ))).hom ≫
        MonoidalCategoryStruct.whiskerLeft (self := strStruct 𝒪 h𝒪) (tensorPow 𝒪 h𝒪 L n)
            (tensorPowAddIsoSheaf 𝒪 h𝒪 L (b : ℤ) (c : ℤ)).hom ≫
          (tensorPowAddIsoSheaf 𝒪 h𝒪 L n ((b : ℤ) + (c : ℤ))).hom ≫
            (eqToIso (congrArg (tensorPow 𝒪 h𝒪 L)
              (show n + ((b : ℤ) + (c : ℤ)) = n + (b : ℤ) + (c : ℤ) from by ring))).hom := by
  simp only [addIsoSheaf_hom 𝒪 h𝒪 L, str_whiskerRight 𝒪 h𝒪, str_whiskerLeft 𝒪 h𝒪,
    str_associator 𝒪 h𝒪, strStruct_tensorObj 𝒪 h𝒪,
    MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom, Category.assoc,
    Iso.hom_inv_id_assoc, MonoidalCategory.whiskerLeft_hom_inv_assoc]
  rw [loc_addIso_assoc_natCast_right 𝒪 h𝒪 L n b c]

end Bridge

section Scheme

attribute [local instance] schemeMonoidal strictSchemeMonoidal

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

/-- **The associativity constraint on the multiplication of the tensor powers of an invertible
`𝒪_X`-module with an arbitrary integer first exponent.** -/
theorem tensorPowModuleAddIso_assoc_natCast_right (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (n : ℤ) (b c : ℕ) :
    MonoidalCategoryStruct.whiskerRight
        (self := (schemeMonoidal X).toMonoidalCategoryStruct)
        (tensorPowModuleAddIso X L n (b : ℤ)).hom (tensorPowModule X L (c : ℤ)) ≫
        (tensorPowModuleAddIso X L (n + (b : ℤ)) (c : ℤ)).hom =
      (MonoidalCategoryStruct.associator (self := (schemeMonoidal X).toMonoidalCategoryStruct)
          (tensorPowModule X L n) (tensorPowModule X L (b : ℤ))
          (tensorPowModule X L (c : ℤ))).hom ≫
        MonoidalCategoryStruct.whiskerLeft
          (self := (schemeMonoidal X).toMonoidalCategoryStruct)
          (tensorPowModule X L n) (tensorPowModuleAddIso X L (b : ℤ) (c : ℤ)).hom ≫
          (tensorPowModuleAddIso X L n ((b : ℤ) + (c : ℤ))).hom ≫
            (tensorPowModuleCongr X L
              (show n + ((b : ℤ) + (c : ℤ)) = n + (b : ℤ) + (c : ℤ) from by ring)).hom :=
  addIsoSheaf_assoc_natCast_right X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n b c

end Scheme

end Stacks.AlgebraicGeometry.ThetaMul

end
