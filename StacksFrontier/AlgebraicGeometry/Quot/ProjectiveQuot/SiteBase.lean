module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyContraction
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget

/-!
# The base `Spec ℤ` of the big fppf site, as a terminal object

The Quot scheme `Quot^P_{𝒪^{⊕ r}/ℙⁿ_ℤ/ℤ}` of Stacks 0DPA lives over `Spec ℤ`.  On the big fppf
site over the scheme `AlgebraicGeometry.integerBase` (which every big fppf site contains,
`AlgebraicGeometry.BigFppfSite.contains_integerBase`) the base is the identity object
`AlgebraicGeometry.ProjectiveQuot.siteBase`, a terminal object of the site.  Every presheaf on the
site therefore has exactly one morphism to the algebraic space it represents; this is what makes
"the morphism to the base" of a presheaf on the site unambiguous.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.siteBase`: `Spec ℤ` as an object of the big fppf site over
  itself.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isTerminal_siteBase`: it is terminal.
* `AlgebraicGeometry.ProjectiveQuot.subsingleton_hom_yoneda_siteBase`: a presheaf on the site has
  at most one morphism to the presheaf represented by it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveQuot

universe u

variable (B : BigFppfSite.{u})

/-- `Spec ℤ` as an object of the big fppf site over itself: the identity of
`AlgebraicGeometry.integerBase`. -/
abbrev siteBase : BigFppfOver B integerBase B.contains_integerBase :=
  Over.mk (𝟙 _)

/-- `Spec ℤ` is a terminal object of the big fppf site over itself. -/
def isTerminal_siteBase : IsTerminal (siteBase B) :=
  Over.mkIdTerminal

/-- Any two morphisms to `Spec ℤ` in the big fppf site over it agree. -/
instance subsingleton_hom_siteBase (T : BigFppfOver B integerBase B.contains_integerBase) :
    Subsingleton (T ⟶ siteBase B) :=
  ⟨fun a b => (isTerminal_siteBase B).hom_ext a b⟩

/-- A presheaf on the big fppf site over `Spec ℤ` has at most one morphism to the presheaf
represented by `Spec ℤ`. -/
instance subsingleton_hom_yoneda_siteBase
    (F : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ ⥤ Type u) :
    Subsingleton (F ⟶ yoneda.obj (siteBase B)) :=
  ⟨fun a b => by
    ext T x
    exact (isTerminal_siteBase B).hom_ext _ _⟩

/-- An algebraic space over `Spec ℤ` has exactly one morphism to the algebraic space `Spec ℤ`. -/
instance subsingleton_hom_schemeSpace_siteBase
    (X : AlgebraicSpaces B integerBase B.contains_integerBase) :
    Subsingleton (X ⟶ schemeSpace (siteBase B)) :=
  ⟨fun a b => ObjectProperty.hom_ext _
    (Subsingleton.elim (α := X.obj ⟶ yoneda.obj (siteBase B)) a.hom b.hom)⟩

end AlgebraicGeometry.ProjectiveQuot

end
