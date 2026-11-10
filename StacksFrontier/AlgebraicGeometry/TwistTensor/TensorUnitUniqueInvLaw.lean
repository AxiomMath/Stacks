module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerMul
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaMultiplicativity
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistBraiding

/-!
# The inverse law that characterises the braided comparison of two tensor inverses

`Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso X A A' B e e'` compares two
tensor inverses `A` and `A'` of one invertible `𝒪_X`-module `B`, from the two inverse laws
`e : A ⊗ B ≅ 𝒪_X` and `e' : A' ⊗ B ≅ 𝒪_X`.  Every multiplicativity statement about a comparison
*defined* that way needs the identity saying so,

`(isoOfTensorUnitIso X A A' B e e').hom ▷ B ≫ e'.hom = e.hom`,

and this file proves it.  Without it a square chase through a negative tensor power cannot cross
the degree zero, because in a negative degree
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleNegSuccIso` and
`tensorPowModuleIsoOfIsoNegSucc` *are* `isoOfTensorUnitIso` and nothing else is known about them.

## The braiding is the content

`isoOfTensorUnitIso` is built from `Stacks.SheafOfModules.tensorInverseUniqueIso`, which goes
`A ≅ A ⊗ 𝒪_X ≅ A ⊗ (A' ⊗ B) ≅ A ⊗ (B ⊗ A') ≅ (A ⊗ B) ⊗ A' ≅ 𝒪_X ⊗ A' ≅ A'`; the third step is the
symmetry constraint `Stacks.SheafOfModules.picardTensorComm`.  The identity is therefore **not** a
formal consequence of the symmetric monoidal axioms: in super vector spaces the odd line `L` is
invertible with `β_ L L = -𝟙`, the comparison of `L` with itself built this way is `-𝟙`, and the
two sides of the identity differ by a sign.

What it does follow from is `Stacks.Monoidal.braiding_eval_snake`, whose hypothesis
`Stacks.GradedSections.HasTrivialSelfBraiding` is about the self-braiding of a *single* object and
leaves the pair unconstrained.  Here that object is the common tensor inverse `B`, and for an
invertible sheaf of modules the hypothesis is discharged — by
`Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl`, which is the Tag 01CU commutativity
constraint.  So the counterexample above is excluded and the identity holds.

The sibling identity for the *two-sided* uniqueness isomorphism
`Stacks.Monoidal.isoOfTensorInverse` is
`Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso`, and the two proofs are the same
shape: reduce the whiskered comparison to a single endomorphism of the common inverse, and
recognise that endomorphism as the identity by a snake.

## Main results

* `Stacks.Monoidal.whiskerRight_tensorUnitComparison`: **the identity, for an arbitrary braided
  monoidal category** and the comparison written out as the composite
  `tensorInverseUniqueIso` is.
* `Stacks.AlgebraicGeometry.TensorUnitInvLaw.isoOfTensorUnitIso_whiskerRight`: **the identity for
  `Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso`**, at the `𝒪_X`-modules of a
  scheme and against the structure maps of the strict monoidal structure of Stacks Tag 01CA.

## Implementation notes

**Two spellings of the structure maps.**  `isoOfTensorUnitIso` is built from the Picard-group
constraints of `StacksFrontier/AlgebraicGeometry/PicardGroup/Basic.lean`, which are the
`Stacks.SheafOfModules.Invertible.tensorProduct*` family; the monoidal structure of Stacks Tag
01CA has `Stacks.SheafOfModules.tensorSheaf*`.  The first pair is definitionally the second, so
`show` moves between them, but `α_` is *not* definitionally `tensorSheafAssociator` — that is the
lemma `Stacks.SheafOfModules.associator_eq_tensorSheafAssociator`, stated at the
`SheafOfModules (structureSheaf 𝒪 h𝒪)` spelling of the category.  The four restatements
`schemeAssociator_eq_tensorSheafAssociator` and friends move it to the
`AlgebraicGeometry.Scheme.Modules` spelling, which is the only spelling in which a rewrite fires
against a goal about `X.Modules`; this is what
`Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom` already does for the tensor product of
a pair of morphisms.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.Ample Stacks.RelativeVeryAmple

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Two evaluations in disjoint positions commute**: cancelling `T` against the unit first and
then `S` is cancelling `S` first and then `T`. -/
theorem eval_exchange {T S : C} (f : T ⟶ 𝟙_ C) (s : S ⟶ 𝟙_ C) :
    f ▷ S ≫ (λ_ S).hom ≫ s = T ◁ s ≫ (ρ_ T).hom ≫ f := by
  rw [← MonoidalCategory.leftUnitor_naturality s]
  rw [← Category.assoc, ← MonoidalCategory.whisker_exchange]
  rw [Category.assoc, ← MonoidalCategory.rightUnitor_naturality f]
  rw [MonoidalCategory.unitors_equal]

/-- `eval_exchange` with the second factor split in two, so that the left-hand side is a
morphism out of `(T ⊗ A') ⊗ B`. -/
theorem eval_exchange_assoc {T A' B : C} (f : T ⟶ 𝟙_ C) (s : A' ⊗ B ⟶ 𝟙_ C) :
    (f ▷ A') ▷ B ≫ (λ_ A').hom ▷ B ≫ s = (α_ T A' B).hom ≫ T ◁ s ≫ (ρ_ T).hom ≫ f := by
  have h1 : (f ▷ A') ▷ B ≫ (λ_ A').hom ▷ B =
      (α_ T A' B).hom ≫ f ▷ (A' ⊗ B) ≫ (λ_ (A' ⊗ B)).hom := by
    rw [MonoidalCategory.leftUnitor_whiskerRight, ← Category.assoc,
      MonoidalCategory.associator_naturality_left, Category.assoc]
  rw [← Category.assoc, h1]
  simp only [Category.assoc]
  rw [eval_exchange f s]

/-- The inverse right unitor against the associator is the inverse left unitor: the triangle
axiom, read as a rewrite of the unit inserted between the two factors. -/
theorem rightUnitor_inv_whiskerRight_associator (A B : C) :
    (ρ_ A).inv ▷ B ≫ (α_ A (𝟙_ C) B).hom = A ◁ (λ_ B).inv := by
  simp

/-- `rightUnitor_inv_whiskerRight_associator`, reassociated so that it fires inside a longer
composite. -/
theorem rightUnitor_inv_whiskerRight_associator_assoc (A B : C) {Z : C}
    (h : A ⊗ (𝟙_ C ⊗ B) ⟶ Z) :
    (ρ_ A).inv ▷ B ≫ (α_ A (𝟙_ C) B).hom ≫ h = A ◁ (λ_ B).inv ≫ h := by
  rw [← Category.assoc, rightUnitor_inv_whiskerRight_associator]

/-- **The structural half of the inverse-law identity.**  The comparison of two tensor inverses,
whiskered by the common inverse `B` and evaluated against the inverse law of `A'`, is the
evaluation of the inverse law of `A` precomposed with a single endomorphism of `B`.  No braiding
enters: the step inserting `B ⊗ A'` into the unit is taken as the free morphism `k`, and the four
rewrites are the pentagon, the triangle and the naturality of the associator in its three
variables.

Stated with `f`, `s` and `k` free because at the tensor powers of an invertible module the three
spellings `0 + p`, `p + 0` and `p` of a degree are one object, so a rewrite inside the concrete
composite does not fire. -/
theorem tensorUnitComparison_reduce {A A' B : C} (f : A ⊗ B ⟶ 𝟙_ C) (s : A' ⊗ B ⟶ 𝟙_ C)
    (k : 𝟙_ C ⟶ B ⊗ A') :
    ((ρ_ A).inv ≫ A ◁ k ≫ (α_ A B A').inv ≫ f ▷ A' ≫ (λ_ A').hom) ▷ B ≫ s =
      A ◁ ((λ_ B).inv ≫ k ▷ B ≫ (α_ B A' B).hom ≫ B ◁ s ≫ (ρ_ B).hom) ≫ f := by
  simp only [MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  rw [eval_exchange_assoc f s, MonoidalCategory.rightUnitor_tensor_hom]
  simp only [Category.assoc]
  rw [MonoidalCategory.associator_naturality_right_assoc,
    ← MonoidalCategory.pentagon_assoc,
    MonoidalCategory.inv_hom_whiskerRight_assoc,
    MonoidalCategory.associator_naturality_middle_assoc,
    rightUnitor_inv_whiskerRight_associator_assoc]

/-- **`Stacks.Monoidal.braiding_eval_snake` for an inverse law written in the other order.**  For
`s : A' ⊗ B ⟶ 𝟙` the two cancellations of `(A' ⊗ B) ⊗ B` against `s` — the last two factors
directly, or the first two after braiding `A'` past `B` — agree, provided the self-braiding of
`B` is trivial.  Obtained from `braiding_eval_snake` at the inverse law `(β_ A' B).inv ≫ s`, whose
braided form is `s` again. -/
theorem braiding_eval_snake_left [BraidedCategory C] {A' B : C}
    [Stacks.GradedSections.HasTrivialSelfBraiding B] (s : A' ⊗ B ⟶ 𝟙_ C) :
    (β_ A' B).hom ▷ B ≫ (α_ B A' B).hom ≫ B ◁ s ≫ (ρ_ B).hom =
      s ▷ B ≫ (λ_ B).hom := by
  have h := braiding_eval_snake (C := C) (L := B) (L' := A') ((β_ A' B).inv ≫ s)
  rw [Iso.hom_inv_id_assoc] at h
  rw [h, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id_assoc]

/-- **The inverse-law identity for the braided comparison of two tensor inverses.**  Let `B` be an
object with trivial self-braiding and let `e : A ⊗ B ≅ 𝟙` and `e' : A' ⊗ B ≅ 𝟙` exhibit `A` and
`A'` as tensor inverses of `B`.  The comparison `A ≅ A'` built by
`Stacks.SheafOfModules.tensorInverseUniqueIso` — written out here as the composite
`A ≅ A ⊗ 𝟙 ≅ A ⊗ (A' ⊗ B) ≅ A ⊗ (B ⊗ A') ≅ (A ⊗ B) ⊗ A' ≅ 𝟙 ⊗ A' ≅ A'`, with the middle three
legs spelled as tensor products of morphisms rather than whiskerings, which is how the
construction produces them — carries `e'` back to `e`.

This determines the comparison, tensoring on the right by `B` being an equivalence, and it is
what a multiplicativity square at a bidegree summing to zero needs.  The hypothesis on the
self-braiding is not removable; see the module docstring. -/
theorem whiskerRight_tensorUnitComparison [BraidedCategory C] {A A' B : C}
    [Stacks.GradedSections.HasTrivialSelfBraiding B]
    (e : A ⊗ B ≅ 𝟙_ C) (e' : A' ⊗ B ≅ 𝟙_ C) :
    ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ e'.inv) ≫ (𝟙 A ⊗ₘ (β_ A' B).hom) ≫ (α_ A B A').inv ≫
        (e.hom ⊗ₘ 𝟙 A') ≫ (λ_ A').hom) ▷ B ≫ e'.hom = e.hom := by
  rw [MonoidalCategory.id_tensorHom, MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.whiskerLeft_comp_assoc A e'.inv (β_ A' B).hom,
    tensorUnitComparison_reduce e.hom e'.hom (e'.inv ≫ (β_ A' B).hom),
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [braiding_eval_snake_left e'.hom, MonoidalCategory.inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]

end Stacks.Monoidal

namespace Stacks.AlgebraicGeometry.TensorUnitInvLaw

open Stacks.SheafOfModules
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

attribute [local instance] Stacks.Algebraization.strictModulesMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal
  Stacks.Algebraization.strictModulesBraided

variable (X : Scheme.{u})

/-- The sheaf condition on the structure presheaf of rings of a scheme, abbreviated: it is the
second argument of every constraint of the tensor product sheaf used below. -/
abbrev sheafCondition := Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X

/-- `Stacks.SheafOfModules.associator_eq_tensorSheafAssociator` at the
`AlgebraicGeometry.Scheme.Modules` spelling of the category, which is the spelling a rewrite has
to be in to fire against a goal about `X.Modules`. -/
theorem schemeAssociator_eq_tensorSheafAssociator (A B D : X.Modules) :
    α_ A B D = tensorSheafAssociator X.presheaf (sheafCondition X) A B D :=
  associator_eq_tensorSheafAssociator X.presheaf (sheafCondition X) A B D

/-- `Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor` at the
`AlgebraicGeometry.Scheme.Modules` spelling of the category. -/
theorem schemeLeftUnitor_eq_tensorSheafLeftUnitor (A : X.Modules) :
    λ_ A = tensorSheafLeftUnitor X.presheaf (sheafCondition X) A :=
  leftUnitor_eq_tensorSheafLeftUnitor X.presheaf (sheafCondition X) A

/-- `Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor` at the
`AlgebraicGeometry.Scheme.Modules` spelling of the category. -/
theorem schemeRightUnitor_eq_tensorSheafRightUnitor (A : X.Modules) :
    ρ_ A = tensorLeftFunctorObjUnitIso X.presheaf (sheafCondition X) A :=
  rightUnitor_eq_tensorSheafRightUnitor X.presheaf (sheafCondition X) A

/-- `Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding` at the
`AlgebraicGeometry.Scheme.Modules` spelling of the category. -/
theorem schemeBraiding_eq_tensorSheafBraiding (A B : X.Modules) :
    β_ A B = tensorSheafBraiding X.presheaf (sheafCondition X) A B :=
  braiding_eq_tensorSheafBraiding X.presheaf (sheafCondition X) A B

/-- **An invertible `𝒪_X`-module has trivial self-braiding for the strict monoidal structure of
Stacks Tag 01CA.**  `Stacks.SectionRingGeometric.schemeHasTrivialSelfBraiding` is the same fact
for the localized structure `Stacks.SheafInternalHom.schemeMonoidalCategory`; the braiding here is
`Stacks.SheafOfModules.tensorSheafBraiding`, whose triviality on an invertible module is the Tag
01CU commutativity constraint `Stacks.SheafOfModules.tensorSheafBraiding_self_eq_refl`.

A `local instance`: a global one would be found in every statement about the modules of a scheme,
including those meaning a different monoidal structure. -/
local instance strictHasTrivialSelfBraiding (B : X.Modules) [IsInvertibleModule X B] :
    Stacks.GradedSections.HasTrivialSelfBraiding B :=
  ⟨congrArg Iso.hom ((schemeBraiding_eq_tensorSheafBraiding X B B).trans
    (tensorSheafBraiding_self_eq_refl X.presheaf (sheafCondition X) B))⟩

set_option maxHeartbeats 1000000 in
-- large `simp only`/`change`/`rw` steps unfolding the Picard-group monoidal structure
/-- **The comparison of two tensor inverses, written out.**  `isoOfTensorUnitIso` packages its
three modules into the full subcategory of invertible sheaves, applies
`Stacks.SheafOfModules.tensorInverseUniqueIso` and reads the result off the inclusion; this is the
composite that comes out, against the structure maps of the strict monoidal structure of Stacks
Tag 01CA.  The two unit constraints and the associator of the Picard group are definitionally
those of the tensor product sheaf, so the four `scheme*_eq_tensorSheaf*` rewrites reach them; its
functoriality constraint is the bifunctor's map on a pair, which is
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso`, and
`Stacks.SheafOfModules.tensorSheafMapIso_hom_eq` reads that as a tensor product of morphisms. -/
theorem isoOfTensorUnitIso_hom (A A' B : X.Modules) [IsInvertibleModule X A]
    [IsInvertibleModule X A'] [IsInvertibleModule X B]
    (e : tensorModules X A B ≅ unitModule X) (e' : tensorModules X A' B ≅ unitModule X) :
    (isoOfTensorUnitIso X A A' B e e').hom =
      (ρ_ A).inv ≫ (𝟙 A ⊗ₘ e'.inv) ≫ (𝟙 A ⊗ₘ (β_ A' B).hom) ≫ (α_ A B A').inv ≫
        (e.hom ⊗ₘ 𝟙 A') ≫ (λ_ A').hom := by
  rw [isoOfTensorUnitIso, Stacks.SheafOfModules.tensorInverseUniqueIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Stacks.SheafOfModules.picardTensorUnitIso, Stacks.SheafOfModules.picardTensorIso,
    Stacks.SheafOfModules.picardTensorComm, Stacks.SheafOfModules.picardTensorAssoc,
    Stacks.SheafOfModules.picardUnitTensorIso]
  dsimp only [ObjectProperty.ι_map, ObjectProperty.isoMk_hom, ObjectProperty.isoMk_inv,
    ObjectProperty.homMk_hom]
  change (tensorLeftFunctorObjUnitIso X.presheaf (sheafCondition X) A).inv ≫
      (Stacks.SheafOfModules.TensorPower.tensorSheafMapIso X.presheaf (sheafCondition X)
        (Iso.refl A) e'.symm).hom ≫
      (Stacks.SheafOfModules.TensorPower.tensorSheafMapIso X.presheaf (sheafCondition X)
        (Iso.refl A) (tensorSheafBraiding X.presheaf (sheafCondition X) A' B)).hom ≫
      (tensorSheafAssociator X.presheaf (sheafCondition X) A B A').inv ≫
      (Stacks.SheafOfModules.TensorPower.tensorSheafMapIso X.presheaf (sheafCondition X)
        e (Iso.refl A')).hom ≫
      (tensorSheafLeftUnitor X.presheaf (sheafCondition X) A').hom = _
  rw [Stacks.SheafOfModules.tensorSheafMapIso_hom_eq X.presheaf (sheafCondition X)
      (Iso.refl A) e'.symm,
    Stacks.SheafOfModules.tensorSheafMapIso_hom_eq X.presheaf (sheafCondition X) (Iso.refl A)
      (tensorSheafBraiding X.presheaf (sheafCondition X) A' B),
    Stacks.SheafOfModules.tensorSheafMapIso_hom_eq X.presheaf (sheafCondition X) e (Iso.refl A'),
    ← schemeRightUnitor_eq_tensorSheafRightUnitor,
    ← schemeAssociator_eq_tensorSheafAssociator,
    ← schemeLeftUnitor_eq_tensorSheafLeftUnitor, ← schemeBraiding_eq_tensorSheafBraiding]
  simp only [Iso.refl_hom, Iso.symm_hom]
  rfl

/-- **The inverse-law identity for
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso`.**  The comparison of two tensor
inverses `A` and `A'` of an invertible `𝒪_X`-module `B`, whiskered by `B` and followed by the
inverse law of `A'`, is the inverse law of `A`.

This is the identity that characterises `isoOfTensorUnitIso`, and the one a multiplicativity
square at a bidegree summing to zero needs: in a negative degree
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleNegSuccIso` and
`tensorPowModuleIsoOfIsoNegSucc` are defined as `isoOfTensorUnitIso` and nothing else is known
about them. -/
theorem isoOfTensorUnitIso_whiskerRight (A A' B : X.Modules) [IsInvertibleModule X A]
    [IsInvertibleModule X A'] [IsInvertibleModule X B]
    (e : tensorModules X A B ≅ unitModule X) (e' : tensorModules X A' B ≅ unitModule X) :
    (isoOfTensorUnitIso X A A' B e e').hom ▷ B ≫ e'.hom = e.hom := by
  rw [isoOfTensorUnitIso_hom X A A' B e e']
  exact Stacks.Monoidal.whiskerRight_tensorUnitComparison e e'

end Stacks.AlgebraicGeometry.TensorUnitInvLaw

end
