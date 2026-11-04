module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Quotient.LocallySmall
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Homology.Injectives.Spaltenstein.Enlargement
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsLocalizing
public import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian objects form a strictly full saturated triangulated subcategory

Let `C` be a category viewed as a site with the chaotic topology and let `O : Cᵒᵖ ⥤ RingCat` be a
sheaf of rings on `C`. Tag 0GYV singles out the *cartesian* objects of `D(O)`, those `K` for which
the canonical comparison `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an isomorphism for every
`a : V ⟶ U` in `Cᵒᵖ`, and calls the resulting full subcategory `QC(O)`. This file proves the first
assertion of tag 0GYW: `QC(O)` is a strictly full, saturated, triangulated subcategory of `D(O)`
preserved by arbitrary direct sums.

## Main results

* `isCartesian_isClosedUnderIsomorphisms`: cartesian objects are closed under isomorphism, i.e.
  `QC(O)` is strictly full.
* `isCartesian_isSaturated`: cartesian objects are closed under direct summands, i.e. `QC(O)` is
  saturated (thick).
* `isCartesian_isTriangulated`: `QC(O)` is a triangulated subcategory.
* `isCartesian_isClosedUnderCoproducts_of_smallSite`: `QC(O)` is closed under arbitrary direct
  sums.

## Implementation notes

`Stacks.ModulesOnACategory.CartesianObjects.IsCartesian O hO` is the cartesian condition
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.IsQC` of the canonical base-change data
`Stacks.ModulesOnACategory.CartesianObjects.canonicalBaseChangeData O hO`, so each of the four
assertions is the instance at that base-change datum of the corresponding assertion for an
arbitrary one: `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderIsomorphisms`,
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isSaturated`,
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isTriangulated` and
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderColimitsOfShape`. All four
rest on the same structural fact: for a fixed `a : V ⟶ U` the comparison maps are the components
of a *natural* transformation `RΓ(V, -) ⋙ baseChange a ⟶ RΓ(U, -)`, and the locus where a natural
transformation is invertible is closed under isomorphism, under retracts, and — once the two
functors are triangulated and the transformation commutes with the shift — is a triangulated
subcategory closed under the direct sums both functors preserve.

This file inherits the two deviations of
  `Stacks.ModulesOnACategory.CartesianObjects.canonicalBaseChangeData` from the source:
the section rings are in `RingCat.{0}` and are assumed pointwise commutative (`hO`), derived
extension of scalars being available for commutative rings only. A third narrowing comes down
the same chain: the coefficient module universe is not independent but the one
`StacksDraft.Ch21.Sec43.Tag0H0R` determines for
  `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.DMod O`, namely `max u v` for
`C : Type u` with `[Category.{v} C]` and the structure sheaf at `RingCat.{0}`. The direct-sums
clause is registered on `isCartesian_isClosedUnderCoproducts_of_smallSite`, where `C : Type` with
`[SmallCategory C]`, the standing smallness convention of the source. These three narrowings are
properties of the 0GYV/0H0R chain, not local choices of this file.

Tag 0GZ0 asserts, as its `subcategory` clause, exactly the four statements this file proves —
that `QC(O)` is a strictly full, saturated, triangulated subcategory closed under arbitrary
direct sums. It is therefore registered on the same four declarations that carry 0GYW, under
the same three inherited narrowings and no further hypothesis, rather than restated.

## References

* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
* [Stacks Project, Tag 0GZ0](https://stacks.math.columbia.edu/tag/0GZ0)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0H0R](https://stacks.math.columbia.edu/tag/0H0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open ZeroObject

namespace Stacks.ModulesOnACategory.CartesianSubcategory

attribute [local instance] HasDerivedCategory.standard

universe u v

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{0})
  (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x)

/-! ### The invertibility locus of a natural transformation -/

/-! ### Strict fullness, saturation and triangulatedness -/

/-- **Tag 0GYW, strict fullness.** The cartesian objects of `D(O)` are closed under isomorphism,
so `QC(O)` is a strictly full subcategory of `D(O)`. -/
@[stacks 0GYW "strictly full"]
instance isCartesian_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (Stacks.ModulesOnACategory.CartesianObjects.IsCartesian
      O hO) :=
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderIsomorphisms
    (Stacks.ModulesOnACategory.CartesianObjects.canonicalBaseChangeData O hO)

/-- **Tag 0GYW, saturation.** The cartesian objects of `D(O)` are closed under direct summands, so
`QC(O)` is a saturated (thick) subcategory of `D(O)`. -/
@[stacks 0GYW "saturated"]
instance isCartesian_isSaturated :
    ObjectProperty.IsSaturated (Stacks.ModulesOnACategory.CartesianObjects.IsCartesian O hO) :=
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isSaturated
    (Stacks.ModulesOnACategory.CartesianObjects.canonicalBaseChangeData O hO)

/-- **Tag 0GYW, triangulatedness.** `QC(O)` is a triangulated subcategory of `D(O)`: for each
`a : V ⟶ U` the comparison maps are the components of a shift-compatible natural transformation
between triangulated functors, `- ⊗^L_{O(V)} O(U)` being triangulated as a left adjoint of a
triangulated functor, and the locus where such a transformation is invertible is triangulated. -/
@[stacks 0GYW "triangulated"]
instance isCartesian_isTriangulated :
    ObjectProperty.IsTriangulated (Stacks.ModulesOnACategory.CartesianObjects.IsCartesian O hO) :=
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isTriangulated
    (Stacks.ModulesOnACategory.CartesianObjects.canonicalBaseChangeData O hO)

/-! ### Arbitrary direct sums

Closure under arbitrary direct sums is the one assertion that constrains the universes: a
`Discrete J`-colimit in `D(O)` is, after discarding the zero members, a coproduct indexed by a
type small in the *morphism* universe of `D(O)`, and that coproduct has to exist in
`PresheafOfModules.{max u v} O`, whose coproducts are indexed by types small in the *module*
universe `max u v`. The two are reconciled by tag 079Q: the derived category of a Grothendieck
abelian category is already locally small in the category's own universe, whichever model of the
derived category is in force. That is `locallySmall_derivedCategory` below.
-/

section Generic

universe w d

/-- **Tag 079Q.** The derived category of a Grothendieck abelian category is locally small in the
universe in which the category itself is locally small, *whatever model of the derived category
is in force* — in particular for the standard universe-bumping localization: every object of
`D(C)` is, up to isomorphism, the image of a cochain complex, and derived morphisms into a complex
are exactly homotopy classes of maps into its K-injective resolution, of which there are only
`w`-many. The functorial K-injective resolutions are those of tag 079P. -/
instance locallySmall_derivedCategory (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{d} A] [IsGrothendieckAbelian.{w} A] :
    LocallySmall.{w} (DerivedCategory A) := by
  let r := (Stacks.Injectives.exists_functorial_quasiIso_isKInjective A).some
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let qh := DerivedCategory.Qh (C := A)
  have : LocallySmall.{w} (HomologicalComplex A (ComplexShape.up ℤ)) := inferInstance
  have : LocallySmall.{w} (HomotopyCategory A (ComplexShape.up ℤ)) :=
    inferInstanceAs (LocallySmall.{w}
      (CategoryTheory.Quotient (homotopic A (ComplexShape.up ℤ))))
  have : qh.EssSurj :=
    Localization.essSurj qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  refine ⟨?_⟩
  intro X Y
  obtain ⟨B, ⟨eA⟩⟩ := Functor.EssSurj.mem_essImage qh X
  obtain ⟨B', ⟨eB⟩⟩ := Functor.EssSurj.mem_essImage qh Y
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective B'
  let R := r.functor.obj L
  let η := r.inclusion.app L
  have : QuasiIso η := r.quasiIso L
  have : R.IsKInjective := r.isKInjective L
  let i := DerivedCategory.quotientCompQhIso A
  let eη : qh.obj (q.obj L) ≅ qh.obj (q.obj R) :=
    i.app L ≪≫ asIso (DerivedCategory.Q.map η) ≪≫ (i.app R).symm
  let eY : qh.obj (q.obj R) ≅ Y := eη.symm ≪≫ eB
  let hbij := CochainComplex.IsKInjective.Qh_map_bijective B R
  let preimage (f : X ⟶ Y) : B ⟶ q.obj R :=
    Classical.choose (hbij.surjective (eA.hom ≫ f ≫ eY.inv))
  have preimage_spec (f : X ⟶ Y) :
      qh.map (preimage f) = eA.hom ≫ f ≫ eY.inv :=
    Classical.choose_spec (hbij.surjective (eA.hom ≫ f ≫ eY.inv))
  refine small_of_injective (f := preimage) ?_
  intro f g hfg
  apply (Iso.homCongr eA.symm eY.symm).injective
  simpa only [Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom] using
    (preimage_spec f).symm.trans ((congrArg qh.map hfg).trans (preimage_spec g))

end Generic

section DirectSums

universe m

/-- Countable products are exact in presheaves of modules: products are computed pointwise, and
products of abelian groups are exact.

The three `letI`s name the instances for `AddCommGrpCat.{max u v}` and for the presheaf category
built from it: searching for them inside the module universe `max u v` instead stalls on the
shape universe of Mathlib's `HasExactLimitsOfShape (Discrete J) AddCommGrpCat` instance, which
is stated with the shape in the same universe as the groups. -/
instance hasExactLimitsOfShape_nat_presheafOfModules :
    HasExactLimitsOfShape (Discrete ℕ) (PresheafOfModules.{max u v} O) :=
  letI : HasExactLimitsOfShape (Discrete ℕ) AddCommGrpCat.{max u v} := inferInstance
  letI : HasLimitsOfShape (Discrete ℕ) AddCommGrpCat.{max u v} := inferInstance
  letI : HasExactLimitsOfShape (Discrete ℕ) (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) := inferInstance
  HasExactLimitsOfShape.domain_of_functor (Discrete ℕ) (PresheafOfModules.toPresheaf O)

/-- Countable products are exact in the category of modules over a section ring, with the modules
in an arbitrary universe `m`: products are computed on the underlying abelian groups, and products
of abelian groups are exact. Mathlib's `AB4Star (ModuleCat.{r} R)` instance puts the module
universe at the ring universe, so it does not cover the coefficient universe `max u v` of `D(O)`
for a section ring in `RingCat.{0}`; this is the same argument with the two universes separated.
The two `letI`s name the `AddCommGrpCat.{m}` instances for the reason recorded above. -/
instance hasExactLimitsOfShape_nat_moduleCat (R : RingCat.{0}) :
    HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{m} R) :=
  letI : HasExactLimitsOfShape (Discrete ℕ) AddCommGrpCat.{m} := inferInstance
  letI : HasLimitsOfShape (Discrete ℕ) AddCommGrpCat.{m} := inferInstance
  HasExactLimitsOfShape.domain_of_functor (Discrete ℕ)
    (forget₂ (ModuleCat.{m} R) AddCommGrpCat.{m})

end DirectSums

section SmallSite

universe j

/-- **Tag 0GYW, arbitrary direct sums.** `QC(O)` is closed under direct sums indexed by an
arbitrary type. Discarding the zero summands leaves an index type small in the module universe,
because `D(O)` is locally small there by tag 079Q, and both `RΓ(V, -) ⋙ (- ⊗^L_{O(V)} O(U))` and
`RΓ(U, -)` preserve direct sums of that size — the first as a left adjoint, the second as the
derived functor of the exact evaluation. Stated for a small site, the standing smallness
convention of the source. -/
@[stacks 0GYW "arbitrary direct sums"]
instance isCartesian_isClosedUnderCoproducts_of_smallSite {C : Type} [SmallCategory C]
    (O : Cᵒᵖ ⥤ RingCat.{0}) (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x) (J : Type j) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (Stacks.ModulesOnACategory.CartesianObjects.IsCartesian O hO) (Discrete J) :=
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isQC_isClosedUnderColimitsOfShape
    (Stacks.ModulesOnACategory.CartesianObjects.canonicalBaseChangeData O hO) J

end SmallSite

/-! ### Tag 0GZ0, the `subcategory` clause

The first assertion of tag 0GZ0 is that `QC(O)` is a strictly full, saturated, triangulated
subcategory of `D(O)` closed under arbitrary direct sums — the four statements proved above
for 0GYW. The clause is registered on that same covering set; see the implementation notes
for the three narrowings it inherits from the 0GYV/0H0R chain. -/

add_to_stacks 0GZ0 "subcategory" isCartesian_isClosedUnderIsomorphisms
add_to_stacks 0GZ0 "subcategory" isCartesian_isSaturated
add_to_stacks 0GZ0 "subcategory" isCartesian_isTriangulated
add_to_stacks 0GZ0 "subcategory" isCartesian_isClosedUnderCoproducts_of_smallSite

end Stacks.ModulesOnACategory.CartesianSubcategory

end
