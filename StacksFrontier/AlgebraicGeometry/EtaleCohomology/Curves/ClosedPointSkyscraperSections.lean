module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantSheafSections

/-!
# Sections of the skyscraper sheaf `i_{x,*} ℤ` at a point of a scheme

The third term of the divisor sequence of Stacks 03RM has one summand
`Stacks.EtaleCohomology.integerSkyscraper` for each closed point `x` of the curve. Its sections
over an étale `X`-scheme `U` are the sections of the constant sheaf `ℤ` on the small étale site
of the residue field over the fibre `U ×_X Spec κ(x)`, and those are, by the sections
description of the constant sheaf, the locally constant `ℤ`-valued maps on that fibre. Such a
map is in general not constant, the fibre being a disjoint union of spectra of finite separable
extensions of `κ(x)`.

## Main definitions

* `Stacks.EtaleCohomology.integerSkyscraperSectionsIsoLocallyConstantMaps` — the sections of
  `i_{x,*} ℤ` over an étale `X`-scheme as the locally constant `ℤ`-valued maps on the fibre.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- The sections of the skyscraper sheaf `i_{x,*} ℤ` over an étale `X`-scheme `U` are the group
of locally constant `ℤ`-valued maps on the fibre `U ×_X Spec κ(x)`. -/
def integerSkyscraperSectionsIsoLocallyConstantMaps (X : Scheme.{u}) (x : X) (U : X.Etale) :
    (integerSkyscraper.{u, v} X x).obj.obj (op U) ≅
      AddCommGrpCat.of (LocallyConstant
        ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).left
        (ULift.{max (u + 1) v} ℤ)) :=
  smallEtaleConstantSheafSectionsIsoLocallyConstantMapsAb.{u, v}
    (Spec (X.residueField x)) (ULift.{max (u + 1) v} ℤ)
    ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U)

end Stacks.EtaleCohomology

end
