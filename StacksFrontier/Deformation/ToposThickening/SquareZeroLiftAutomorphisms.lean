module

public import StacksFrontier.Deformation.ToposThickening.SquareZeroDerivedObstruction

/-!
# The automorphisms of a lift of a bounded above complex across a square-zero thickening

Let `C` be a site and `f : O ⟶ O₀` a surjection of sheaves of commutative rings whose kernel `I`
has square zero. Let `K₀ ∈ D⁻(O₀)` and let `(K, α)` be a lift of `K₀`: an object `K ∈ D⁻(O)`
together with an isomorphism `α : K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`. Part (1) of Stacks 0DIZ says that
the group of automorphisms of the pair `(K, α)` is canonically the cokernel of a map

`Ext⁻¹_{O₀}(K₀, K₀) ⟶ Hom_{O₀}(K₀, K₀ ⊗^L_{O₀} I)`.

Everything in that statement is constructed, none of it is a parameter:

* the derived base change `- ⊗^L_O O₀` is `Deformation.ComplexLift.derivedExtensionOfScalarsData`
  (Stacks 0794 at flat resolutions), and a lift is a `Deformation.ComplexLift.DerivedLift` for it;
* the square-zero ideal `I`, as a sheaf of `O₀`-modules, is
  `Deformation.ComplexLift.squareZeroIdeal`, and `- ⊗^L_{O₀} I` is
  `Deformation.ComplexLift.derivedTensorRight`;
* the map is `Deformation.ComplexLift.boundary` at the reduction triangle
  `Deformation.ComplexLift.squareZeroReduction` of `f`: the connecting map of the distinguished
  triangle `K ⊗^L_O I ⟶ K ⟶ K ⊗^L_O O₀ ⟶ (K ⊗^L_O I)⟦1⟧` attached to `0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0`,
  read in the two groups of the source through the adjunction between derived base change and
  restriction of scalars, as in the proof of the source.

## Main definitions

* `Deformation.ComplexLift.squareZeroLiftBoundary`: the map
  `Ext⁻¹_{O₀}(K₀, K₀) ⟶ Hom_{O₀}(K₀, K₀ ⊗^L_{O₀} I)`.
* `Deformation.ComplexLift.squareZeroLiftAutEquiv`: the automorphisms of the pair `(K, α)` are
  the cokernel of that map. Stacks 0DIZ (1) itself is registered, for sites with morphisms in an
  arbitrary universe, as `Deformation.ComplexLift.squareZeroFlatLiftAutEquiv`.

## Implementation notes

An automorphism of the pair `(K, α)` is an automorphism `φ` of `K` with `α ∘ (φ ⊗^L id) = α`,
that is with `φ ⊗^L id = id` since `α` is an isomorphism; that subgroup of `Aut K` is
`Deformation.ComplexLift.automorphismsOfLift`. `Ext^i_{O₀}(K₀, M)` is the group of morphisms
`K₀ ⟶ M⟦i⟧` in `D(O₀)`, and the cokernel of an additive map `β` is the quotient of its target by
its range, written multiplicatively since the automorphism group is.

The surjection is local surjectivity, `Presheaf.IsLocallySurjective J f.hom`, and "kernel of
square zero" is the sectionwise condition that the product of two sections killed by `f`
vanishes; these are the hypotheses of `Deformation.ComplexLift.squareZeroReduction`. The site
has objects in an arbitrary universe and morphisms in the universe of the sections of `O`.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe d d₀ u u'

namespace Deformation.ComplexLift

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u'} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
  (hf : Presheaf.IsLocallySurjective J f.hom)
  (hsq : ∀ (U : Cᵒᵖ) (a b : O.obj.obj U), f.hom.app U a = 0 → f.hom.app U b = 0 → a * b = 0)
variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

/-- **Stacks 0DIZ (1), the map.** For a lift `(K, α)` of `K₀ ∈ D⁻(O₀)` across the square-zero
surjection `f`, the canonical map

`Ext⁻¹_{O₀}(K₀, K₀) ⟶ Hom_{O₀}(K₀, K₀ ⊗^L_{O₀} I)`

whose cokernel the automorphism group of `(K, α)` is: the connecting map of the reduction
triangle `K ⊗^L_O I ⟶ K ⟶ K ⊗^L_O O₀ ⟶ (K ⊗^L_O I)⟦1⟧` of `f`, read through the adjunction
between derived base change and restriction of scalars and through `α`. -/
def squareZeroLiftBoundary (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀) :
    (K₀.obj ⟶ K₀.obj⟦(-1 : ℤ)⟧) →+
      (K₀.obj ⟶ (derivedTensorRight.{d₀, u, u, u'} (squareZeroIdeal.{u, u, u'} f hf hsq)).obj
        K₀.obj) :=
  boundary (squareZeroReduction f hf hsq) L

/-- **Stacks 0DIZ (1).** Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a
site whose kernel `I` is an ideal of square zero, let `K₀ ∈ D⁻(O₀)` and let `(K, α)` be a lift
of `K₀`, i.e. `K ∈ D⁻(O)` with `α : K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`. Then the group of
automorphisms of the pair `(K, α)` is canonically the cokernel of the map
`Ext⁻¹_{O₀}(K₀, K₀) ⟶ Hom_{O₀}(K₀, K₀ ⊗^L_{O₀} I)` of
`Deformation.ComplexLift.squareZeroLiftBoundary`. -/
def squareZeroLiftAutEquiv (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀) :
    Multiplicative (K₀.obj ⟶
        (derivedTensorRight.{d₀, u, u, u'} (squareZeroIdeal.{u, u, u'} f hf hsq)).obj K₀.obj) ⧸
        AddSubgroup.toSubgroup (squareZeroLiftBoundary f hf hsq L).range ≃*
      automorphismsOfLift (derivedExtensionOfScalarsData.{d, d₀} f) L :=
  automorphismsOfLiftMulEquiv (squareZeroReduction f hf hsq) L

end Deformation.ComplexLift

end
