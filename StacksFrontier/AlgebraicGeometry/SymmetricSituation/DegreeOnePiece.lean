module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.Quasicoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# Degree one of the symmetric algebra is the module itself

`PresheafOfModules.symmetricAlgebraSheafify α F` is the symmetric algebra of the sheafification
of a presheaf of modules `F`, built as the degreewise sheafification of the sectionwise symmetric
algebra `PresheafOfModules.symPowIntGradedAlgebra F`, and
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X F` is its instantiation at a module sheaf on
a scheme. This file identifies the degree-one piece of either with the module it is built from,
by an isomorphism whose forward direction is the degree-one generator.

Sectionwise, `Sym¹_{O(U)}(F(U))` is `F(U)`, since `Sym¹` is the range of the injective map
`SymmetricAlgebra.ι`. The degree-one generator of the sheafified algebra is the sheafification of
the sectionwise one, and on a scheme it is in addition precomposed with the counit identifying the
sheafification of `F` with `F`.

## Main definitions

* `PresheafOfModules.symmetricAlgebraSheafifyPieceOneIso`: degree one of `Sym(F)` is the
  sheafification of `F`.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGenIso` and
  `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceOneIso`: `F ≅ Sym¹(F)` for the symmetric
  algebra of a module sheaf on a scheme, and its inverse.

## Main results

* `PresheafOfModules.isIso_symPowIntGen`: the sectionwise degree-one generator of
  `PresheafOfModules.symPowIntGradedAlgebra` is an isomorphism.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGenIso_hom` and
  `AlgebraicGeometry.Scheme.Modules.isIso_symmetricAlgebraGen`: the degree-one generator
  `F ⟶ Sym¹(F)` on a scheme is an isomorphism, the forward direction of `symmetricAlgebraGenIso`.

## Implementation notes

The forward direction of each identification is definitionally the degree-one generator
(`symmetricAlgebraGenIso_hom` is `rfl`): the generator is the sheafification of the sectionwise
generator composed with the counit, and the isomorphism is built from the same two factors in the
same order.

The sectionwise generators `PresheafOfModules.symPowIntGen` and
`PresheafOfModules.symPowIntGen` are definitionally equal, so the sectionwise
identification is `PresheafOfModules.symmetricAlgebraGenIso`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules TopologicalSpace

universe v u w a

namespace PresheafOfModules

/-! ### The sectionwise identification -/

section Sectionwise

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- **The degree-one generator of the sectionwise symmetric algebra is an isomorphism**: the
degree-one piece of `Sym_{O(U)}(F(U))` is `F(U)`, naturally in `U`. -/
theorem isIso_symPowIntGen : IsIso (symPowIntGen F) :=
  inferInstanceAs (IsIso (symmetricAlgebraGenIso F).hom)

end Sectionwise

/-! ### The identification after sheafification -/

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {R : Sheaf J RingCat.{w}}
  (α : (O ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  [HasWeakSheafify J AddCommGrpCat.{max w a}]
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ CommRingCat RingCat))

/-- **Degree one of `Sym(F)` is the sheafification of `F`.** The degree-one generator of `Sym(F)`
is the sheafification of the sectionwise degree-one generator, which is an isomorphism. -/
noncomputable def symmetricAlgebraSheafifyPieceOneIso :
    (sheafification α).obj F ≅ (symmetricAlgebraSheafify α F).piece 1 :=
  (sheafification α).mapIso (symmetricAlgebraGenIso F)

/-- `PresheafOfModules.symmetricAlgebraSheafifyPieceOneIso` is the degree-one generator. -/
@[simp]
theorem symmetricAlgebraSheafifyPieceOneIso_hom :
    (symmetricAlgebraSheafifyPieceOneIso α F).hom = symmetricAlgebraSheafifyGen α F := rfl

/-- **The degree-one generator of `Sym(F)` is an isomorphism.** -/
theorem isIso_symmetricAlgebraSheafifyGen : IsIso (symmetricAlgebraSheafifyGen α F) :=
  inferInstanceAs (IsIso (symmetricAlgebraSheafifyPieceOneIso α F).hom)

end Sheafify

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) (F : SheafOfModules.{u} X.ringCatSheaf)

/-- **`F ≅ Sym¹(F)` for a module sheaf on a scheme**, the degree-one generator of its symmetric
algebra: the counit identifying the sheafification of `F` with `F`, followed by the sheafification
of the sectionwise degree-one generator. -/
noncomputable def symmetricAlgebraGenIso : F ≅ (symmetricAlgebra X F).piece 1 :=
  (sheafificationIso X F).symm ≪≫
    @PresheafOfModules.symmetricAlgebraSheafifyPieceOneIso.{u, u, u, u} _ _ _ X.sheaf.obj
      X.ringCatSheaf (𝟙 X.ringCatSheaf.obj) (isLocallyInjective_id_ringCatSheaf X)
      (isLocallySurjective_id_ringCatSheaf X) inferInstance inferInstance F.val

/-- `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGenIso` is the degree-one generator. -/
@[simp]
theorem symmetricAlgebraGenIso_hom :
    (symmetricAlgebraGenIso X F).hom = symmetricAlgebraGen X F := rfl

/-- **The degree-one generator `F ⟶ Sym¹(F)` of the symmetric algebra of a module sheaf on a
scheme is an isomorphism.** -/
theorem isIso_symmetricAlgebraGen : IsIso (symmetricAlgebraGen X F) :=
  inferInstanceAs (IsIso (symmetricAlgebraGenIso X F).hom)

/-- **Degree one of the symmetric algebra of a module sheaf on a scheme is that module sheaf.** -/
noncomputable def symmetricAlgebraPieceOneIso : (symmetricAlgebra X F).piece 1 ≅ F :=
  (symmetricAlgebraGenIso X F).symm

end AlgebraicGeometry.Scheme.Modules

end
