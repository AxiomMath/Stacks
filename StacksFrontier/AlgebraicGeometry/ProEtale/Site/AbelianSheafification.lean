module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Sheafification of abelian presheaves on the small pro-étale site

Presheaves of abelian groups on the small pro-étale site of a scheme admit sheafification: the
site is essentially small in any universe containing its objects, so the sheafification
adjunction exists there and is left exact.

## Main results

* `AlgebraicGeometry.ProEtale.hasSheafify_proetale`: abelian presheaves on the small pro-étale
  site can be sheafified.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ProEtale

/-- Presheaves of abelian groups on the small pro-étale site admit sheafification. -/
theorem hasSheafify_proetale (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  hasSheafifyEssentiallySmallSite _ _

end AlgebraicGeometry.ProEtale

end
