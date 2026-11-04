module

public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.IsoStructureMap
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation
import StacksCore.Tactic.StacksAttribute

/-!
# A localization morphism of ringed topoi is flat

Let `(C, O)` be a ringed site and `T` an object of `C`. The localization morphism of ringed topoi
`π : (Sh(C/T), O|_T) ⟶ (Sh(C), O)` of Stacks 04IX is flat in the sense *defined* by Tag 04JB: its
structure map in inverse-image form is an isomorphism, by
`AlgebraicGeometry.RingedSite.isIso_localizationRingedToposHom_fSharpInverseImage`, and an
isomorphism of sheaves of commutative rings is flat.

This is the degenerate case of flatness: no extension of scalars happens along `π` at all, which
is the same fact that makes the second factor of the pullback of sheaves of modules an
equivalence in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap`.

## Main results

* `AlgebraicGeometry.RingedSite.isFlat_localizationRingedToposHom`: every localization morphism
  of ringed topoi is flat, for the notion of flatness that Tag 04JB defines.

## Implementation notes

The import of
`StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation` is for the single
general lemma `AlgebraicGeometry.SheafOfModules.isFlatMapULift_of_isIso`, which is a fact about
flatness rather than about simplicial objects and happens to be homed there. It is imported here,
in a flatness module, rather than into
`StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.IsoStructureMap`, so that the
localization module keeps its small closure and does not acquire a dependency on the simplicial
development.

## References

* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.RingedSite

universe u v w

variable (X : RingedSite.{u, v, max u v w}) (T : X.C)
  [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [(X.J.over T).HasSheafCompose (forget RingCat.{max u v w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [(X.J.over T).HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]

omit [X.J.HasSheafCompose (forget RingCat.{max u v w})]
  [(X.J.over T).HasSheafCompose (forget RingCat.{max u v w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [(X.J.over T).HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- **Every localization morphism of ringed topoi is flat.** Its structure map in inverse-image
form is the identification of Stacks 04IX, hence an isomorphism, and an isomorphism of sheaves of
commutative rings is flat.

The notion of flatness instantiated here is the one Tag 04JB *defines*,
`AlgebraicGeometry.RingedToposHom.IsFlat`; this is a corollary that uses that definition, not a
discharge of it, so it carries no registration. Tag 04JB is registered where it belongs, on the
two definitions themselves, in
`StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi`. -/
theorem isFlat_localizationRingedToposHom :
    AlgebraicGeometry.RingedToposHom.IsFlat (X.localizationRingedToposHom T) :=
  SheafOfModules.isFlatMapULift_of_isIso _ inferInstance

end AlgebraicGeometry.RingedSite

end
