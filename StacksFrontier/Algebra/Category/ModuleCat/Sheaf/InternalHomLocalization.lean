module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence

/-!
# The localization of a ringed site at an object

A ringed site `(C, J, O)` localized at an object `V` is the slice `(C/V, J/V, O|_V)`.  It is what
lets a statement about sheaves of modules on a ringed site — the internal hom sheaf of
Stacks 03EM, say, or its invariance under an equivalence of ringed sites — be applied to the
restrictions of modules to a slice, which otherwise are only sheaves of modules over the
restricted sheaf of rings and over no ringed site at all.

The two identifications below are both `rfl`: the sheaf of rings underlying the restricted
structure sheaf is the restriction of the sheaf of rings underlying the structure sheaf, because
forgetting commutativity and restricting to a slice are composition with two functors in opposite
positions; and the internal hom sheaf of the localization is, by the very definition of
`AlgebraicGeometry.RingedSite.internalHomSheaf`, the internal hom presheaf of the restricted
structure sheaf.

## Main definitions

* `AlgebraicGeometry.RingedSite.localizationAtObject`: **the localization of a ringed site at an
  object.**

## Main results

* `AlgebraicGeometry.RingedSite.ringSheaf_localizationAtObject`: the sheaf of rings of a
  localization is the restriction of the sheaf of rings, on the nose.
* `AlgebraicGeometry.RingedSite.internalHomSheaf_localizationAtObject_val`: the underlying
  presheaf of the internal hom sheaf of a localization is the internal hom presheaf of the
  restricted structure sheaf, on the nose.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03CH](https://stacks.math.columbia.edu/tag/03CH)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04M1](https://stacks.math.columbia.edu/tag/04M1)
-/

@[expose] public section

open CategoryTheory

universe u v w m

namespace AlgebraicGeometry.RingedSite

/-- **The localization of a ringed site at an object `V`**: the slice category `C/V` with the
localized topology `J/V` and the restricted structure sheaf `O|_V`.

Its objects live in `Type (max u v)` rather than `Type u`, since an object of `C/V` is an object
of `C` together with an arrow to `V`. -/
def localizationAtObject (X : RingedSite.{u, v, w}) (V : X.C) : RingedSite.{max u v, v, w} where
  C := Over V
  J := X.J.over V
  O := X.O.over V

/-- The sheaf of rings underlying the structure sheaf of a localization is the restriction to the
slice of the sheaf of rings underlying the structure sheaf.  Forgetting commutativity and
restricting to the slice are composition with functors on opposite sides, so this is `rfl`. -/
theorem ringSheaf_localizationAtObject (X : RingedSite.{u, v, w}) (V : X.C) :
    Stacks.SheafOfModules.Tensor.ringSheaf (X.localizationAtObject V).O =
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V := rfl

/-- The underlying presheaf of modules of the internal hom sheaf of a localization is the
internal hom presheaf of Stacks 03EM formed for the restricted structure sheaf.  This is `rfl`:
it is the definition of `AlgebraicGeometry.RingedSite.internalHomSheaf` at the localization. -/
theorem internalHomSheaf_localizationAtObject_val (X : RingedSite.{u, v, w}) (V : X.C)
    (A B : SheafOfModules.{m}
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.localizationAtObject V).O)) :
    (internalHomSheaf (X.localizationAtObject V) A B).val =
      internalHom (X.O.over V).obj A.val B.val := rfl

end AlgebraicGeometry.RingedSite

end
