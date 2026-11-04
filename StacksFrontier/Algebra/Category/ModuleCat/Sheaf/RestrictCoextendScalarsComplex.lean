module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextension
public import StacksFrontier.Algebra.Homology.HomComplexAdjunction

/-!
# Restriction and coextension of scalars for complexes of sheaves of modules

Let `φ : O ⟶ O'` be a morphism of sheaves of rings on a site. Restriction of scalars along `φ`
is left adjoint to coextension of scalars `F ↦ SheafHom_O(O', F)`; this is the sheaf case of
Stacks Tag 0932, recorded as
`Stacks.SheafOfModules.CoextendScalars.restrictScalars_coextendScalars_adjunction`. Applying both
functors degreewise to cochain complexes, the Hom-set bijection of that adjunction becomes an
isomorphism of Hom complexes

`Hom^•_O(L_O, I) ≅ Hom^•_{O'}(L, SheafHom_O(O', I))`

for a complex `L` of sheaves of `O'`-modules and a complex `I` of sheaves of `O`-modules. This
is the form in which Tag 0932 is used in the proof of Stacks Tag 0996(2): a complex of
`O_f`-modules may be mapped into a complex of `O`-modules either over `O`, after restricting
scalars, or over `O_f`, after applying `SheafHom_O(O_f, -)` to the target.

## Main definitions

* `Stacks.SheafOfModules.CoextendScalars.homComplexRestrictCoextendIso`: the isomorphism of Hom
  complexes `Hom^•_O(L_O, I) ≅ Hom^•_{O'}(L, SheafHom_O(O', I))`.

## Main results

* `Stacks.SheafOfModules.CoextendScalars.homComplexRestrictCoextendIso_hom_apply`: the
  isomorphism acts on a homogeneous cochain componentwise by the Hom-set bijection
  `Stacks.SheafOfModules.CoextendScalars.coextendScalarsSheafHomEquiv` of Tag 0932, which pins it
  down.

## Implementation notes

The isomorphism is obtained from `CategoryTheory.Adjunction.homComplexIso`, applied to the
adjunction of Tag 0932, rather than built degreewise: the compatibility with the differential of
the Hom complex is then the two naturality squares of the adjunction, which Tag 0932 already
supplies, and nothing has to be re-proved about cochains.

Additivity of coextension of scalars is not a separate construction either: a right adjoint of
an additive functor between preadditive categories is additive, so it is read off the adjunction
of Tag 0932 and registered as an instance here.

## References

* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

namespace Stacks.SheafOfModules.CoextendScalars

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O O' : Sheaf J RingCat.{u}}

/-- Coextension of scalars is additive, being a right adjoint of the additive functor
`SheafOfModules.restrictScalars φ` between preadditive categories. -/
instance additive_coextendScalars (φ : O ⟶ O') :
    (coextendScalars.{u} φ).Additive :=
  (restrictScalars_coextendScalars_adjunction φ).right_adjoint_additive

/-- **Stacks Tag 0932 for complexes.** For a morphism `φ : O ⟶ O'` of sheaves of rings on a
site, a complex `L` of sheaves of `O'`-modules and a complex `I` of sheaves of `O`-modules, the
Hom complex of the restriction of `L` to `O` and of `I` is isomorphic to the Hom complex of `L`
and of `SheafHom_O(O', I)`, degreewise by the Hom-set bijection
`Stacks.SheafOfModules.CoextendScalars.coextendScalarsSheafHomEquiv` of Tag 0932. -/
def homComplexRestrictCoextendIso (φ : O ⟶ O')
    (L : CochainComplex (SheafOfModules.{u} O') ℤ)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) :
    CochainComplex.HomComplex
        (((SheafOfModules.restrictScalars.{u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) I ≅
      CochainComplex.HomComplex L
        (((coextendScalars.{u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (restrictScalars_coextendScalars_adjunction φ).homComplexIso L I

/-- The isomorphism `homComplexRestrictCoextendIso φ L I` sends a cochain `z` of degree `n` to the
cochain whose component from `p` to `q` is the image of the component `z.v p q hpq` under the
Hom-set bijection `coextendScalarsSheafHomEquiv φ (L.X p) (I.X q)`. -/
theorem homComplexRestrictCoextendIso_hom_apply (φ : O ⟶ O')
    (L : CochainComplex (SheafOfModules.{u} O') ℤ)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) (n : ℤ)
    (z : Cochain (((SheafOfModules.restrictScalars.{u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L) I n) (p q : ℤ) (hpq : p + n = q) :
    (AddCommGrpCat.Hom.hom ((homComplexRestrictCoextendIso φ L I).hom.f n) z).v p q hpq =
      coextendScalarsSheafHomEquiv φ (L.X p) (I.X q) (z.v p q hpq) :=
  rfl

end Stacks.SheafOfModules.CoextendScalars

end
