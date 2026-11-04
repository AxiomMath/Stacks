module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.AffineChartSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Sectionwise

/-!
# The affine-open sections of the homogeneous pieces of `Sym(E)`

The library carries two presheaves of sectionwise symmetric powers:
`Stacks.SymGraded.siteGradedPiece`, used by the `Stacks.SymGraded` development of
`Sym(E)` on a scheme, and `PresheafOfModules.symPowInt`, used by
`PresheafOfModules.symmetricAlgebraSheafify` and hence by
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`. This file records that **they are the same
presheaf of modules, on the nose**, and reads the affine-chart computation of the first one off as
a statement about the homogeneous pieces of the second.

## Main results

* `Stacks.SymGraded.siteGradedPiece_eq_symPowInt`: **the two presheaves of sectionwise symmetric
  powers are equal**, by `rfl`. Both are `PresheafOfModules.ofPresheaf` of the same presheaf of
  abelian groups: the sections are the degree-`n` submodule of the symmetric algebra of the
  sections, and the restriction maps are `SymmetricAlgebra.mapₛₗ` of the restriction maps.
* `AlgebraicGeometry.Scheme.Modules.bijective_symmetricAlgebra_sheafifyUnit_of_isAffineOpen`:
  **the sheafification unit is bijective on the sections of the degree-`n` piece of `Sym(E)` over
  an affine open**, for `E` quasi-coherent.
* `AlgebraicGeometry.Scheme.Modules.symmetricAlgebraPieceEquiv`: that bijection as an equivalence,
  i.e. `Γ(V, Symⁿ(E)) = Symⁿ_{Γ(X, V)}(Γ(E, V))` for `V` affine.

## Implementation notes

The equality of the two presheaves is what makes
`Stacks.SymGraded.bijective_sheafifyUnit_app_of_isAffineOpen` — which is stated for
`siteGradedPiece` — applicable to the pieces of
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`, whose degree-`n` piece is the sheafification
of `PresheafOfModules.symPowInt n E.val` by `PresheafOfModules.symmetricAlgebraSheafify_piece`.
The two spellings of the symmetric power are therefore crossed exactly once, here, and by the
type ascription in the statement of
`bijective_symmetricAlgebra_sheafifyUnit_of_isAffineOpen`; nothing downstream has to mention
`siteGradedPiece`.

**What this is for.** It is the degreewise input to the ring of sections of the *ungraded*
realization over an affine open, i.e. to
`Γ(V, Sym(E)) = Sym_{Γ(X, V)}(Γ(E, V))` and hence to finite presentation of the algebra sheaf
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraSheaf`. What is still missing for that is
bijectivity of `Stacks.GradedAlgebra.totalUnit` over an affine open — the identification of the
sections of the sheafification of the objectwise direct sum with the direct sum of the sections,
which is `Stacks.SheafOfModules.preservesCoproducts_evaluation_of_isCompact` (Tag 01AI) combined
with `Stacks.RelativeSpec.gradedCoprodIsoUnderlyingModule`, and which is not assembled anywhere.

**No `@[stacks]` tag.** The affine-chart computation is `Stacks.SymGraded`'s, and the tag
discussion in the module docstring of
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.AffineChartSections` applies unchanged:
nothing here is Tag 01CG's assertion.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01AI](https://stacks.math.columbia.edu/tag/01AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open PresheafOfModules

universe v u w

namespace Stacks.SymGraded

/-- **The two presheaves of sectionwise symmetric powers in the library are the same presheaf of
modules.** `Stacks.SymGraded.siteGradedPiece` and `PresheafOfModules.symPowInt` are both
`PresheafOfModules.ofPresheaf` of the presheaf of abelian groups whose sections over `X` are the
degree-`n` submodule of `Sym_{O(X)}(F(X))` and whose restriction maps are the semilinear
`SymmetricAlgebra.mapₛₗ` of the restriction maps of `F`. -/
theorem siteGradedPiece_eq_symPowInt {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    (F : PresheafOfModules.{w} (O ⋙ forget₂ _ RingCat)) (n : ℤ) :
    siteGradedPiece F n = PresheafOfModules.symPowInt.{v, u, w, w} n F :=
  rfl

end Stacks.SymGraded

namespace AlgebraicGeometry.Scheme.Modules

universe u'

variable {X : Scheme.{u'}} (E : SheafOfModules.{u'} X.ringCatSheaf) [E.IsQuasicoherent]
  {V : X.Opens}

/-- **The sheafification unit is bijective on the sections of the degree-`n` piece of `Sym(E)`
over an affine open**, for `E` quasi-coherent: this is
`Stacks.SymGraded.bijective_sheafifyUnit_app_of_isAffineOpen`, stated for
`PresheafOfModules.symPowInt` rather than for `Stacks.SymGraded.siteGradedPiece`. -/
theorem bijective_symmetricAlgebra_sheafifyUnit_of_isAffineOpen (hV : IsAffineOpen V) (n : ℤ) :
    Function.Bijective (PresheafOfModules.Hom.app
      (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
        (PresheafOfModules.symPowInt n E.val)) (op V)) :=
  Stacks.SymGraded.bijective_sheafifyUnit_app_of_isAffineOpen E hV n

/-- **`Symⁿ` of the sections of `E` over an affine open is the sections of `Symⁿ(E)` there**: the
affine-chart identification `Γ(V, Symⁿ(E)) = Symⁿ_{Γ(X, V)}(Γ(E, V))` for the homogeneous pieces
of `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`. -/
def symmetricAlgebraPieceEquiv (hV : IsAffineOpen V) (n : ℤ) :
    ((PresheafOfModules.symPowInt n E.val).obj (op V) : Type u') ≃
      (((symmetricAlgebra X E).piece n).val.obj (op V) : Type u') :=
  Equiv.ofBijective _ (bijective_symmetricAlgebra_sheafifyUnit_of_isAffineOpen E hV n)

/-- The equivalence `symmetricAlgebraPieceEquiv E hV n` is given by the component at `V` of the
sheafification unit of `PresheafOfModules.symPowInt n E.val`. -/
@[simp]
theorem symmetricAlgebraPieceEquiv_apply (hV : IsAffineOpen V) (n : ℤ)
    (x : (PresheafOfModules.symPowInt n E.val).obj (op V)) :
    symmetricAlgebraPieceEquiv E hV n x =
      PresheafOfModules.Hom.app (sheafifyUnit (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)
        (PresheafOfModules.symPowInt n E.val)) (op V) x := rfl

end AlgebraicGeometry.Scheme.Modules

end
