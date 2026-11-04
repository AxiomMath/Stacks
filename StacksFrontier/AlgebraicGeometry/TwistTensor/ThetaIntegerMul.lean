module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaInteger
public import StacksFrontier.CategoryTheory.CancelRetraction

/-!
# Multiplicativity of the comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` in an integer bidegree

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring and `U_d ⊆ Proj 𝒮` the degree `d` open of Stacks Tag
01N5.  `Stacks.AlgebraicGeometry.ThetaMul.thetaInt` is the comparison
`𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(dn)` in every integer degree `n`, and
`Stacks.AlgebraicGeometry.ThetaMul.theta_mul` is its multiplicativity — the square relating the
addition law `Stacks.Ample.tensorPowModuleAddIso` of the tensor powers to the canonical
multiplication `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso` of the twists
— in a bidegree of *natural* numbers.

This file carries that square into bidegrees where the exponents are integers.  What it proves is
the bidegree `(n, 0)` for an arbitrary integer `n`, which is the right unit law, together with the
integer right unit law of the addition law of the tensor powers that it rests on: in the degree
`(n, 0)` the addition law is the right unitor read through
`Stacks.Ample.tensorPowModuleZeroIso`, in *every* integer degree `n`, because
`Stacks.TensorPowers.TensorInverse.addNatIso` is the right unitor at the second exponent `0` by
definition and the recursion that produces the negative exponents never enters.

It also develops the monoidal calculus of
`Stacks.Monoidal.isoOfTensorInverse` — the comparison of two tensor inverses, which is how the
comparison family is built in a negative degree — far enough to say when such a comparison is
multiplicative: it is, against the two inverse laws of the object, provided those two laws are
compatible, and that compatibility is a formal consequence of the triviality of the self-braiding
of the object.

## Main results

* `Stacks.Monoidal.whiskerRight_isoOfTensorInverse`: the identity that characterises the
  comparison of two tensor inverses.
* `Stacks.Monoidal.braiding_eval_snake`: **the two inverse laws of a tensor-invertible object
  whose self-braiding is trivial are compatible.**  This is the one non-formal input in a
  multiplicativity statement that crosses the degree zero, and the hypothesis is not removable:
  the odd line in super vector spaces is invertible and the two cancellations differ by a sign
  there.
* `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp`: **the comparison of two tensor inverses is
  multiplicative against the inverse laws**, given that compatibility.
* `Stacks.TensorPowers.TensorInverse.addIso_zero_right_int`,
  `AlgebraicGeometry.SheafOfModules.tensorPowAddIso_zero_right_int`,
  `Stacks.AlgebraicGeometry.ThetaMul.addIsoSheaf_zero_right_int` and
  `tensorPowModuleAddIso_zero_right_int`: **the right unit law of the addition law of the integer
  tensor powers, in every integer degree**, at the four spellings the calculus uses — an abstract
  monoidal category, a sheaf of modules on a site for the localized monoidal structure, the
  tensor product sheaf of Stacks Tag 01CA, and the modules of a scheme.  The natural-number
  versions are `Stacks.TensorPowers.TensorInverse.addIso_zero_right_natCast` and the laws it
  feeds; the degree of the second factor is what is extended here, not the degree of the first.
* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_congr`: the comparison family commutes with the
  transport along an equality of degrees.
* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_zero`: **multiplicativity of the comparison
  family in the bidegree `(n, 0)` for an arbitrary integer `n`.**
* `Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_natCast`: multiplicativity in a bidegree of
  natural numbers, at the integer spelling of the two exponents.

## Implementation notes

The right unit law is proved where the tensor powers are defined — in an abstract monoidal
category, for a two-sided tensor inverse — and then transported along the same three steps the
natural-number law is transported along: `AlgebraicGeometry.SheafOfModules.tensorPowAddIso` is
the abstract addition law at the localized monoidal structure on sheaves of modules,
`tensorPowAddIsoSheaf` reads its source as the tensor product sheaf of Stacks Tag 01CA, and
`Stacks.Ample.tensorPowModuleAddIso` is that for the modules of a scheme.  The second step is the
only one with content, and it is the same cancellation of the two unit comparisons as in
`Stacks.AlgebraicGeometry.ThetaMul.addIsoSheaf_zero_right`.

Unlike the natural-number law, every statement here carries a transport along `n + 0 = n`: for a
natural number `a` the degrees `(a : ℤ) + ((0 : ℕ) : ℤ)` and `(a : ℤ)` are the same term, while
for a variable integer `n` the degrees `n + 0` and `n` are not.

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

universe v u

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open Stacks.Ample
open Stacks.RelativeVeryAmple
open Stacks.SheafOfModules.TensorSheafification

namespace Stacks.TensorPowers.TensorInverse

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The right unit law of the addition law for integer tensor powers, in every integer
degree**: `L ^⊗ n ⊗ L ^⊗ 0 ≅ L ^⊗ (n + 0)` is the right unitor followed by the reindexing.  The
addition law recurses on its second exponent and this is the value it starts from, so no sign
condition on `n` appears and nothing about the tensor inverse is used.  Compare
`Stacks.TensorPowers.TensorInverse.addIso_zero_right_natCast`, which needs no reindexing because
for a natural number `a` the degrees `(a : ℤ) + ((0 : ℕ) : ℤ)` and `(a : ℤ)` are the same term. -/
theorem addIso_zero_right_int {L : C} (h : TensorInverse L) (n : ℤ) :
    h.addIso n 0 =
      ρ_ (intTensorPow L h.inv n) ≪≫
        reindex L h.inv (show n = n + ((0 : ℕ) : ℤ) from by omega) :=
  rfl

end Stacks.TensorPowers.TensorInverse

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Two morphisms inverse to each other, whiskered into the same object on the right, cancel out
of a composite. -/
private theorem whiskerRight_cancel_mid {A B Z W : C} (p : A ⟶ B) (q : B ⟶ A)
    (hpq : p ≫ q = 𝟙 A) (m : A ⊗ Z ⟶ W) : p ▷ Z ≫ q ▷ Z ≫ m = m := by
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hpq,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- **The identity that characterises `Stacks.Monoidal.isoOfTensorInverse`.**  Reading the
comparison `X ≅ Y` of two tensor inverses off the inverse law `hx : A ⊗ X ≅ 𝟙` of `X` requires
undoing the inverse law `hy : Y ⊗ B ≅ 𝟙` of `Y` and the isomorphism `e : A ≅ B`, and this is that
statement with the undoing moved to the other side.  It determines the comparison, both sides
being composites of isomorphisms. -/
theorem whiskerRight_isoOfTensorInverse {A B X Y : C} (e : A ≅ B) (hx : A ⊗ X ≅ 𝟙_ C)
    (hy : Y ⊗ B ≅ 𝟙_ C) :
    (Y ◁ e.hom) ▷ X ≫ hy.hom ▷ X ≫ (λ_ X).hom ≫ (isoOfTensorInverse e hx hy).hom =
      (α_ Y A X).hom ≫ Y ◁ hx.hom ≫ (ρ_ Y).hom := by
  rw [isoOfTensorInverse_hom]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]
  rw [whiskerRight_cancel_mid hy.hom hy.inv hy.hom_inv_id, whiskerRight_cancel_mid
    (Y ◁ e.hom) (Y ◁ e.inv)
    (by rw [← MonoidalCategory.whiskerLeft_comp, e.hom_inv_id,
      MonoidalCategory.whiskerLeft_id])]

/-- **The two inverse laws of a tensor-invertible object are compatible when its self-braiding is
trivial.**  An inverse law `e : L ⊗ L' ⟶ 𝟙` can be used to cancel the first two factors of
`L ⊗ L' ⊗ L`, or — after braiding the last two factors past each other — the last two; the two
cancellations agree.

This is *not* a formal consequence of the symmetric monoidal axioms, and the triviality of the
self-braiding is exactly what it needs: in super vector spaces the odd line `L` is invertible with
`β_ L L = -𝟙` and the two cancellations differ by a sign.  Given the hypothesis it follows from
the hexagon, which turns `β_ (L ⊗ L') L` into the associator followed by `L ◁ β_ L' L` as soon as
`β_ L L` is the identity, together with the naturality of the braiding in its first variable and
`CategoryTheory.braiding_rightUnitor`.

For an invertible sheaf of modules the hypothesis is
`Stacks.SelfBraidingInvertible.hasTrivialSelfBraiding`, so nothing is assumed there. -/
theorem braiding_eval_snake [BraidedCategory C] {L L' : C}
    [Stacks.GradedSections.HasTrivialSelfBraiding L] (e : L ⊗ L' ⟶ 𝟙_ C) :
    (α_ L L' L).hom ≫ L ◁ ((β_ L' L).hom ≫ e) ≫ (ρ_ L).hom = e ▷ L ≫ (λ_ L).hom := by
  have hb : (β_ (L ⊗ L') L).hom = (α_ L L' L).hom ≫ L ◁ (β_ L' L).hom := by
    rw [BraidedCategory.braiding_tensor_left_hom,
      Stacks.GradedSections.HasTrivialSelfBraiding.braiding_self,
      MonoidalCategory.id_whiskerRight, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  calc (α_ L L' L).hom ≫ L ◁ ((β_ L' L).hom ≫ e) ≫ (ρ_ L).hom
      = (β_ (L ⊗ L') L).hom ≫ L ◁ e ≫ (ρ_ L).hom := by
        rw [hb, MonoidalCategory.whiskerLeft_comp]
        simp only [Category.assoc]
    _ = e ▷ L ≫ (β_ (𝟙_ C) L).hom ≫ (ρ_ L).hom := by
        rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left e L, Category.assoc]
    _ = e ▷ L ≫ (λ_ L).hom := by rw [braiding_rightUnitor]

/-- **The comparison of two tensor inverses is multiplicative against the inverse laws.**  Let
`e : A ≅ B`, let `hx : A ⊗ X ≅ 𝟙` and `hx' : X ⊗ A ≅ 𝟙` be the two inverse laws of `X` against
`A`, compatible in the sense of `braiding_eval_snake`, and let `hy : Y ⊗ B ≅ 𝟙` be an inverse law
of `Y` against `B`.  Then the comparison `X ≅ Y` of `Stacks.Monoidal.isoOfTensorInverse`,
tensored with `e` and followed by `hy`, is `hx'`.

This is the square that identifies a comparison built by inverse-uniqueness with one built
multiplicatively, and it is where the compatibility of the two orders of the inverse law of `X`
enters.  Faithfulness of tensoring on the right by `X` is what lets the snake hypothesis be used:
both sides are morphisms out of `X ⊗ A`, and the hypothesis speaks of them whiskered by `X`. -/
theorem isoOfTensorInverse_tensorHom_comp {A B X Y : C} (e : A ≅ B) (hx : A ⊗ X ≅ 𝟙_ C)
    (hx' : X ⊗ A ≅ 𝟙_ C) (hy : Y ⊗ B ≅ 𝟙_ C) [(MonoidalCategory.tensorRight X).Faithful]
    (hsnake : hx'.hom ▷ X ≫ (λ_ X).hom = (α_ X A X).hom ≫ X ◁ hx.hom ≫ (ρ_ X).hom) :
    ((isoOfTensorInverse e hx hy).hom ⊗ₘ e.hom) ≫ hy.hom = hx'.hom := by
  apply (MonoidalCategory.tensorRight X).map_injective
  apply (cancel_mono (λ_ X).hom).mp
  change (((isoOfTensorInverse e hx hy).hom ⊗ₘ e.hom) ≫ hy.hom) ▷ X ≫ (λ_ X).hom =
    hx'.hom ▷ X ≫ (λ_ X).hom
  rw [hsnake, MonoidalCategory.tensorHom_def, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  apply (cancel_mono (isoOfTensorInverse e hx hy).hom).mp
  simp only [Category.assoc]
  rw [whiskerRight_isoOfTensorInverse e hx hy, ← Category.assoc,
    MonoidalCategory.associator_naturality_left]
  simp only [Category.assoc]
  rw [← Category.assoc ((isoOfTensorInverse e hx hy).hom ▷ (A ⊗ X)),
    ← MonoidalCategory.whisker_exchange]
  simp only [Category.assoc]
  rw [MonoidalCategory.rightUnitor_naturality]

end Stacks.Monoidal

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{v})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : _root_.SheafOfModules.{v} (structureSheaf 𝒪 h𝒪)) [IsInvertible 𝒪 h𝒪 L]

/-- **The right unit law of the addition law on the tensor powers of an invertible sheaf of
modules, in every integer degree**, for the localized monoidal structure: multiplication by
`L ^⊗ 0` on the right is the right unitor, followed by the transport between the two spellings
`n` and `n + 0` of the degree. -/
theorem tensorPowAddIso_zero_right_int (n : ℤ) :
    tensorPowAddIso 𝒪 h𝒪 L n 0 =
      ρ_ (tensorPow 𝒪 h𝒪 L n) ≪≫
        eqToIso (congrArg (tensorPow 𝒪 h𝒪 L) (show n = n + 0 from by omega)) :=
  Stacks.TensorPowers.TensorInverse.addIso_zero_right_int _ n

/-- `tensorPowAddIso_zero_right_int` with the transport moved to the other side, which is the form
the transport to the tensor product sheaf of Stacks Tag 01CA consumes. -/
theorem tensorPowAddIso_zero_right_int_hom (n : ℤ) :
    (tensorPowAddIso 𝒪 h𝒪 L n 0).hom ≫
        eqToHom (congrArg (tensorPow 𝒪 h𝒪 L) (show n + 0 = n from by omega)) =
      (ρ_ (tensorPow 𝒪 h𝒪 L n)).hom := by
  rw [congrArg Iso.hom (tensorPowAddIso_zero_right_int 𝒪 h𝒪 L n), Iso.trans_hom, eqToIso.hom]
  exact CategoryTheory.comp_cancel_right (ρ_ (tensorPow 𝒪 h𝒪 L n)).hom
    (by rw [eqToHom_trans]; rfl)

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

/-- **The right unit law of the addition law with the tensor product sheaf of Stacks Tag 01CA as
source, in every integer degree**: multiplying by the zeroth power on the right, after
identifying it with the structure sheaf by
`AlgebraicGeometry.SheafOfModules.tensorPowZeroIso`, is the right unitor of the strict monoidal
structure, followed by the transport between the two spellings of the degree.

Both sides are conjugated into the localized structure by the comparison isomorphism; the unit
objects of the two localizations are matched by
`Stacks.AlgebraicGeometry.ThetaMul.rightUnitor_monoidalCategory_hom`, and what is left is
`AlgebraicGeometry.SheafOfModules.tensorPowAddIso_zero_right_int_hom`.  This is
`Stacks.AlgebraicGeometry.ThetaMul.addIsoSheaf_zero_right` with the natural-number degree
replaced by an integer one. -/
theorem addIsoSheaf_zero_right_int (n : ℤ) :
    MonoidalCategoryStruct.whiskerLeft (self := strStruct 𝒪 h𝒪) (tensorPow 𝒪 h𝒪 L n)
          (tensorPowZeroIso 𝒪 h𝒪 L).hom ≫
        (MonoidalCategoryStruct.rightUnitor (self := strStruct 𝒪 h𝒪)
          (tensorPow 𝒪 h𝒪 L n)).hom =
      (tensorPowAddIsoSheaf 𝒪 h𝒪 L n 0).hom ≫
        eqToHom (congrArg (tensorPow 𝒪 h𝒪 L) (show n + 0 = n from by omega)) := by
  rw [addIsoSheaf_hom, str_whiskerLeft_rightUnitor, rightUnitor_monoidalCategory_hom]
  refine (congrArg (_ ≫ ·) (whiskerLeft_comp_cancel (tensorPow 𝒪 h𝒪 L n)
    (tensorPowZeroIso 𝒪 h𝒪 L).hom (unitIso 𝒪 h𝒪).inv
    (tensorPowZeroIso_hom_comp_unitIso_inv 𝒪 h𝒪 L) _)).trans ?_
  exact (congrArg (_ ≫ ·) (tensorPowAddIso_zero_right_int_hom 𝒪 h𝒪 L n).symm).trans
    (Category.assoc _ _ _).symm

end Bridge

section Scheme

attribute [local instance] schemeMonoidal strictSchemeMonoidal

/-- The reindexing of the tensor powers is the transport of its own index equality.  The two
sides are the same term; the lemma exists because `Stacks.RelativeVeryAmple.tensorPowModuleCongr`
is a `def`, so a term whose head is the reindexing is not syntactically a transport. -/
theorem tensorPowModuleCongr_hom (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]
    {n m : ℤ} (h : n = m) :
    (tensorPowModuleCongr X L h).hom = eqToHom (congrArg (tensorPowModule X L) h) :=
  rfl

/-- **The right unit law on the multiplication of the tensor powers of an invertible
`𝒪_X`-module, in every integer degree**, in the vocabulary `Stacks.Ample.tensorPowModuleAddIso`
the ampleness theory and the twists of `Proj` are written in and against the right unitor of the
strict monoidal structure of Stacks Tag 01CA.  This is
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_zero_right` with the natural-number
degree replaced by an integer one, at the cost of the transport along `n + 0 = n`. -/
theorem tensorPowModuleAddIso_zero_right_int (X : Scheme.{u}) (L : X.Modules)
    [IsInvertibleModule X L] (n : ℤ) :
    tensorPowModule X L n ◁ (tensorPowModuleZeroIso X L).hom ≫
        (ρ_ (tensorPowModule X L n)).hom =
      (tensorPowModuleAddIso X L n 0).hom ≫
        (tensorPowModuleCongr X L (show n + 0 = n from by omega)).hom :=
  addIsoSheaf_zero_right_int X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n

end Scheme

section DegreeOpen

open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen

attribute [local instance] schemeMonoidal strictSchemeMonoidal

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-- Two endomorphisms known to be identities may be inserted at either end of a morphism.

Public because `StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerBidegree.lean` runs the
same chase and held a second copy of this statement until it was deleted in favour of this one. -/
theorem eq_id_comp_comp_id {D : Type*} [Category D] {A B : D} (f : A ⟶ B) (p : A ⟶ A)
    (q : B ⟶ B) (hp : p = 𝟙 A) (hq : q = 𝟙 B) : f = p ≫ f ≫ q := by
  rw [hp, hq, Category.id_comp, Category.comp_id]

/-- **The comparison family commutes with the transport along an equality of degrees**: the
comparison in the degree `m` is the reindexing of the tensor powers, the comparison in the degree
`n`, and the transport of the twists. -/
theorem thetaInt_congr {n m : ℤ} (h : m = n) :
    (thetaInt 𝒮 d m).hom =
      (tensorPowModuleCongr (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) h).hom ≫
        (thetaInt 𝒮 d n).hom ≫
          eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
            (show (d : ℤ) * n = (d : ℤ) * m from by rw [h])) := by
  cases h
  exact eq_id_comp_comp_id (thetaInt 𝒮 d _).hom _ _
    ((tensorPowModuleCongr_hom (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ)) rfl).trans (eqToHom_refl _ _)) (eqToHom_refl _ _)

/-- Re-associating a composite whose first factor splits. -/
private theorem comp_assoc_left {D : Type*} [Category D] {A E B F : D} (u : A ⟶ E) (v : E ⟶ B)
    (f : B ⟶ F) : (u ≫ v) ≫ f = u ≫ v ≫ f :=
  Category.assoc u v f

/-- **Multiplicativity of the integer comparison family in the bidegree `(n, 0)`**, for an
arbitrary integer `n`: the addition law of the tensor powers at `(n, 0)` followed by the
comparison in the degree `n + 0` is the comparisons in the degrees `n` and `0` on the two
factors followed by the canonical multiplication at `(dn, 0)`.

This is the right unit law.  The two multiplications agree with the right unitor of Stacks Tag
01CA on the identification `𝒪_{U_d}(d)^{⊗ 0} ≅ 𝒪_{U_d} ≅ 𝒪_{U_d}(0)` — on the tensor power side
by `tensorPowModuleAddIso_zero_right_int`, on the twist side by
`Stacks.AlgebraicGeometry.ThetaMul.twistMulIso_zero_right`, both of which hold in every integer
degree — and the degree zero value of the family *is* that identification.  Nothing is needed
about the value of the family in the degree `n`, which is why no sign condition on `n` appears. -/
theorem thetaInt_mul_zero (n : ℤ) :
    (tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) n 0).hom ≫ (thetaInt 𝒮 d (n + 0)).hom =
      ((thetaInt 𝒮 d n).hom ⊗ₘ (thetaInt 𝒮 d 0).hom) ≫ (twistMulIso 𝒮 d n 0).hom := by
  refine Eq.trans (congrArg (fun z ↦ (tensorPowModuleAddIso
      (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme (twist 𝒮 d (d : ℤ)) n 0).hom ≫ z)
    (thetaInt_congr 𝒮 d (show n + 0 = n from by omega))) ?_
  refine Eq.trans (comp_assoc_left _ _ _).symm ?_
  exact Stacks.AlgebraicGeometry.ThetaMul.tensorHom_unit_square
    (tensorPowModuleZeroIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ))).hom
    ((twistZeroIsoUnit 𝒮 d).inv ≫
      eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
        (show (0 : ℤ) = (d : ℤ) * 0 from by ring)))
    (thetaInt 𝒮 d n).hom
    ((thetaInt 𝒮 d n).hom ⊗ₘ (thetaInt 𝒮 d 0).hom)
    (twistMulIso 𝒮 d n 0).hom
    (eqToHom (congrArg (restrictedTwist 𝒮 (AlgebraicGeometry.Proj.degreeOpen 𝒮 d))
      (show (d : ℤ) * n = (d : ℤ) * (n + 0) from by ring)))
    ((tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (twist 𝒮 d (d : ℤ)) n 0).hom ≫
      (tensorPowModuleCongr (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
        (twist 𝒮 d (d : ℤ)) (show n + 0 = n from by omega)).hom)
    (congrArg (fun φ ↦ (thetaInt 𝒮 d n).hom ⊗ₘ φ) (rfl : (thetaInt 𝒮 d 0).hom = _))
    (twistMulIso_zero_right 𝒮 d n)
    (tensorPowModuleAddIso_zero_right_int (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
      (twist 𝒮 d (d : ℤ)) n)

/-- **Multiplicativity of the integer comparison family in a bidegree of natural numbers**, at
the integer spelling of the two exponents: this is
`Stacks.AlgebraicGeometry.ThetaMul.theta_mul`, whose `thetaStepNat` and `twistMulIsoNat` are the
addition law and the canonical multiplication with their target degrees ascribed as the natural
number `n + m`, and whose comparison family is `thetaInt` in a nonnegative degree by
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt_natCast`. -/
theorem thetaInt_mul_natCast (n m : ℕ) :
    (tensorPowModuleAddIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
          (twist 𝒮 d (d : ℤ)) (n : ℤ) (m : ℤ)).hom ≫
        (thetaInt 𝒮 d ((n : ℤ) + (m : ℤ))).hom =
      ((thetaInt 𝒮 d (n : ℤ)).hom ⊗ₘ (thetaInt 𝒮 d (m : ℤ)).hom) ≫
        (twistMulIso 𝒮 d (n : ℤ) (m : ℤ)).hom :=
  theta_mul 𝒮 d n m

end DegreeOpen

end Stacks.AlgebraicGeometry.ThetaMul

end
