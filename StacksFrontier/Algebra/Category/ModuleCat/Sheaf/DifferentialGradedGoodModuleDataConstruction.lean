module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategoryLocalization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedModule

/-!
# The flat-resolution theory of a sheaf of differential graded algebras, over the real objects

`SheafOfModules.DifferentialGradedModule.GoodModuleData` packages the derived category of a
sheaf of differential graded algebras together with its localization functor, the good right
differential graded modules, the tensor product with a left differential graded module, and the
two properties of the flat-resolution theory that the derived tensor product and derived
pullback results use. On a ringed site whose structure sheaf is a sheaf of commutative rings,
every one of those clauses is supplied here by the development's own objects, with one
exception: that every right differential graded module receives a quasi-isomorphism from a good
one. The notion of goodness used for those resolutions is left as a parameter, since the two
clauses the results use are K-flatness and resolution existence, and nothing else about it.

Two clauses — the two about the localization — need neither the commutativity of the structure
sheaf nor a particular tensor product, so they are discharged once and for all in
`GoodModuleData.ofLeftTensor`, over an arbitrary sheaf of rings on an arbitrary site and for an
arbitrary tensor product with a left differential graded module; `GoodModuleData.ofExistsGood`
is that constructor at `RelativeTensor.dgTensor`.

The clauses and where they come from:

* the derived category is `derivedCategory A`, the localization of the homotopy category at the
  quasi-isomorphisms, and the localization functor is `toDerivedCategory A`;
* that every object of it is the image of a module is `derivedCategoryModule`, and
  that a homomorphism with acyclic cone becomes invertible is
  `isIso_toDerivedCategory_map_of_acyclic_cone`;
* the good modules are a parameter `Good`, to be instantiated at `IsGood` or at the
  base-change-corrected `IsGoodCocontinuousBaseChange`;
* the tensor product is `RelativeTensor.dgTensor`;
* that a good module tensored with an acyclic left module is acyclic is the hypothesis
  `hKFlat`, which `IsGood.isKFlat` and `IsGoodCocontinuousBaseChange.isKFlat` both discharge.

The existence of good resolutions is the remaining input, and it is an explicit hypothesis of
`GoodModuleData.ofExistsGood` rather than a clause of a carried structure. The development has
the two halves of its proof — a flat generating family assembles into one resolving step, and a
tower of such steps passes to the colimit — but not the tower itself, which needs the sheaf of
graded sets of closed sections of a module and the twisted extension of a module by a free one.
Both halves conclude flatness and K-flatness rather than `IsGood`, which is why goodness is a
parameter here.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.GoodModuleData.ofLeftTensor` is the flat-resolution
  theory of `(A, d)` on the derived category `derivedCategory A` over an arbitrary sheaf of
  rings on an arbitrary site, given a notion of goodness, a tensor product with a left
  differential graded module, the K-flatness of a good module and the resolutions.
* `SheafOfModules.DifferentialGradedModule.GoodModuleData.ofExistsGood` is the
  flat-resolution theory of `(A, d)` on the derived category `derivedCategory A`, built from the
  development's own derived category and tensor product, given a notion of goodness whose
  modules are K-flat and which every module is resolved by.

## References

* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public section

open CategoryTheory

universe t a m v u m₁ v₁ u₁

namespace SheafOfModules.DifferentialGradedModule

section General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- The flat-resolution theory of `(A, d)`, carried on the derived category `derivedCategory A`,
over an arbitrary sheaf of rings on an arbitrary site. The two clauses about the localization
are proved rather than assumed — every object of the derived category is the image of a module,
and a homomorphism with acyclic cone becomes invertible — so that the inputs are exactly the
notion `Good` of goodness used for the resolutions, the tensor product with a left differential
graded module, the K-flatness of a good module, and the existence of good resolutions. -/
noncomputable def GoodModuleData.ofLeftTensor
    (Good : DifferentialGradedModule.{t, a, m} A → Prop)
    (leftTensor : DifferentialGradedModule.{t, a, m} A →
      LeftDifferentialGradedModule.{t, a, m} A → CochainComplex (SheafOfModules.{m} R) ℤ)
    (hKFlat : ∀ {P : DifferentialGradedModule.{t, a, m} A}, Good P →
      ∀ (N : LeftDifferentialGradedModule.{t, a, m} A), N.complex.Acyclic →
        (leftTensor P N).Acyclic)
    (h : ∀ M : DifferentialGradedModule.{t, a, m} A,
      ∃ (P : DifferentialGradedModule.{t, a, m} A) (p : P ⟶ M),
        Good P ∧ (cone p).complex.Acyclic) :
    GoodModuleData.{t, a, m, v, u} A (derivedCategory.{t, a, m} A) where
  localization := toDerivedCategory.{t, a, m} A
  exists_iso_localization X := ⟨derivedCategoryModule A X, ⟨Iso.refl _⟩⟩
  isIso_localization_map f hf := isIso_toDerivedCategory_map_of_acyclic_cone A f hf
  IsGood := Good
  leftTensor := leftTensor
  leftTensor_acyclic hP N hN := hKFlat hP N hN
  exists_isGood M := h M

/-- The localization functor of `GoodModuleData.ofLeftTensor` is the canonical one. -/
@[simp]
theorem GoodModuleData.ofLeftTensor_localization
    (Good : DifferentialGradedModule.{t, a, m} A → Prop) (leftTensor) (hKFlat) (h) :
    (GoodModuleData.ofLeftTensor.{t, a, m, v, u} Good leftTensor hKFlat h).localization =
      toDerivedCategory.{t, a, m} A :=
  rfl

/-- The good modules of `GoodModuleData.ofLeftTensor` are the given ones. -/
@[simp]
theorem GoodModuleData.ofLeftTensor_isGood
    (Good : DifferentialGradedModule.{t, a, m} A → Prop) (leftTensor) (hKFlat) (h) :
    (GoodModuleData.ofLeftTensor.{t, a, m, v, u} Good leftTensor hKFlat h).IsGood = Good :=
  rfl

end General

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (Sheaf.toRingCat J Osharp)}

/-- The flat-resolution theory of `(A, d)`, carried on the derived category
`derivedCategory A` and built from the development's own objects: the tensor product is
`RelativeTensor.dgTensor` and the two clauses about the localization are proved rather than
assumed. Two inputs remain, both about the notion `Good` of goodness used for the resolutions:
that a good module is K-flat, and that every right differential graded `A`-module receives a
homomorphism from a good one whose cone is acyclic.

`Good` is a parameter rather than `IsGood` because the two clauses above are all that the
results proved from a `GoodModuleData` use, and the resolution theory of this development
produces flatness and K-flatness without the base-change clause of `IsGood`. Instantiate it at
`IsGood` with `IsGood.isKFlat`, or at `IsGoodCocontinuousBaseChange` with
`IsGoodCocontinuousBaseChange.isKFlat`. -/
noncomputable def GoodModuleData.ofExistsGood
    (Good : DifferentialGradedModule.{t, m, m} A → Prop)
    (hKFlat : ∀ {P : DifferentialGradedModule.{t, m, m} A}, Good P → RelativeTensor.IsKFlat P)
    (h : ∀ M : DifferentialGradedModule.{t, m, m} A,
      ∃ (P : DifferentialGradedModule.{t, m, m} A) (p : P ⟶ M),
        Good P ∧ (cone p).complex.Acyclic) :
    GoodModuleData A (derivedCategory.{t, m, m} A) :=
  GoodModuleData.ofLeftTensor Good (fun P N => RelativeTensor.dgTensor P N)
    (fun hP N hN => hKFlat hP N hN) h

end SheafOfModules.DifferentialGradedModule

end
