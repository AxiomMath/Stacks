module

public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassInvariance
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Deformation.RingedSpaceThickening.SquareZeroAlgebraExtension

/-!
# The class of a square-zero extension of `f⁻¹𝒪_S`-algebras

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. To an
extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras with `𝒢` an ideal of square zero the
construction of **Stacks 0GQ0** attaches a class in `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`: present `𝒪_X` by
the sheaf of sets `ℰ` underlying `𝒪_{X'}`, so that `α' : ℰ ⟶ 𝒪_{X'}` is the identity, take the
homomorphism `𝒥/𝒥² ⟶ 𝒢` it induces on the conormal sheaf of `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`, and read its
class in `Ext¹_{𝒪_X}(𝖭𝖫(α), 𝒢)` through the quasi-isomorphism `𝖭𝖫(α) ⟶ 𝖭𝖫_{X/S}` of
**Stacks 08TL**.

The class is invariant under morphisms of extensions, hence descends to the set of isomorphism
classes: this is the map underlying the canonical bijection of **Stacks 0GPZ**.

## Main definitions

* `SquareZeroAlgebraExtension.extClass`: the class of an extension in
  `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`.
* `SquareZeroAlgebraExtension.classMap`: the induced map on isomorphism classes.

## Main results

* `SquareZeroAlgebraExtension.extClass_eq_of_hom`: isomorphic extensions have the same class.
* `SquareZeroAlgebraExtension.classMap_mk`: the map sends the class of `𝒪_{X'}` to its class.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

attribute [local instance] HasDerivedCategory.standard

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- **The class of a square-zero extension of `f⁻¹𝒪_S`-algebras** in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`: the class of the homomorphism `𝒥/𝒥² ⟶ 𝒢` of the presentation of
`𝒪_X` by the sheaf of sets underlying `𝒪_{X'}`, as in **Stacks 0GQ0**, read through the
quasi-isomorphism of **Stacks 08TL**. -/
def extClass (P : SquareZeroAlgebraExtension f G) : extOneNaiveCotangent f G :=
  P.toAlgebraSquareZeroExtension.toPresented.extClass

/-- Extensions related by a morphism of extensions have the same class. -/
theorem extClass_eq_of_hom {P Q : SquareZeroAlgebraExtension f G} (φ : P ⟶ Q) :
    P.extClass = Q.extClass :=
  PresentedSquareZeroExtension.extClass_eq_of_hom P.toPresented Q.toPresented
    (Functor.whiskerRight φ.hom.hom (forget CommRingCat.{u}))
    ((Functor.whiskerRight_comp _ _ _).symm.trans
      (congrArg (fun t : P.sheaf ⟶ X.sheaf ↦ Functor.whiskerRight t.hom
        (forget CommRingCat.{u})) φ.hom_reduction))
    φ.hom φ.hom_reduction φ.base_hom
    ((Category.id_comp _).trans (Category.comp_id _).symm) φ.ideal_hom

variable (f G) in
/-- **The map underlying the bijection of Stacks 0GPZ**: the class of an extension, on
isomorphism classes. -/
def classMap : IsomorphismClasses f G → extOneNaiveCotangent f G :=
  Quotient.lift extClass fun _ _ ⟨e⟩ ↦ extClass_eq_of_hom e.hom

/-- The map `classMap f G` sends the isomorphism class of an extension to its class
`SquareZeroAlgebraExtension.extClass`. -/
@[simp]
theorem classMap_mk (P : SquareZeroAlgebraExtension f G) :
    classMap f G (Quotient.mk _ P) = P.extClass :=
  rfl

end AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

end
