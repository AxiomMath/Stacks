module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwaySections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact

/-!
# `𝒪_f` as a sheafification, at the spelling the tensor product of sheaves speaks

Let `(𝒞, 𝒪)` be a ringed site and let `f` be a global section of `𝒪`.
`AlgebraicGeometry.RingedSite.awaySheafificationIsoAwayModule` of `AwaySections.lean` exhibits
`𝒪_f` as the sheafification of the presheaf `U ↦ 𝒪(U)[1/f|_U]` of sectionwise localizations, in
the spelling `PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
X.O).obj)`. The compatibility of sheafification with tensor products,
`PresheafOfModules.sheafificationTensorIso` (Stacks 0GMW), speaks the other spelling:
`PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)`, whose source is presheaves of modules
over `X.O.obj ⋙ forget₂ CommRingCat RingCat`. This file names the bridge between the two once,
so that everything downstream speaks through it.

## Main definitions

* `AlgebraicGeometry.RingedSite.awayModulePresheafAlt`: the presheaf of sectionwise
  localizations, re-typed at the spelling of the presheaf of rings that the monoidal structure
  on presheaves of modules uses.
* `AlgebraicGeometry.RingedSite.awayModuleSheafificationIso`: **the bridge** — `𝒪_f` is the
  sheafification of that presheaf, at that spelling.

## Implementation notes

Both are definitional, which is worth recording because it is not what the warning in
`AwaySections.lean` leads one to expect. That warning — that the two descriptions of the
presheaf of rings agree only after unfolding `CategoryTheory.sheafCompose` — is about *instance
search*, which does not unfold `sheafCompose` and so does not cross between the two spellings.
Terms do cross: `sheafCompose` is a `def`, so the two presheaves of rings are definitionally
equal, and `CategoryTheory.Sheaf.toRingCatMap X.J (𝟙 X.O.obj)` is
`𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj` on the nose. So no `eqToHom` and no
transport is needed here, and `awaySheafificationIsoAwayModule` proves the bridge outright.

What the other spelling needs is instances: local injectivity and local surjectivity of the
identity, which are global instances of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorProductRightExact.lean`. Those are stated at
`CategoryTheory.Sheaf.toRingCatMap`, whose type is written with the *reducible*
`CategoryTheory.Sheaf.toRingCat`, and so is exactly the form
`PresheafOfModules.moduleSheafification` asks for. The sheafification functor must therefore be
named at that spelling rather than through `AlgebraicGeometry.SheafOfModules.moduleSheafification`,
which asks instead for them at `AlgebraicGeometry.SheafOfModules.associatedRingMap`: that type is
written with `Stacks.SheafOfModules.Tensor.ringSheaf`, a plain `def`, which instance search does
not unfold, so the very same instances do not apply there.

## References

* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The presheaf `U ↦ 𝒪(U)[1/f|_U]` of sectionwise localizations, re-typed over the spelling
`X.O.obj ⋙ forget₂ CommRingCat RingCat` of the presheaf of rings. -/
abbrev awayModulePresheafAlt :
    PresheafOfModules.{u} (X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  awayModulePresheaf X h

/-- **`𝒪_f` is the sheafification of the presheaf of sectionwise localizations**, at the
spelling of the sheafification functor that `sheafificationTensorIso` speaks. -/
def awayModuleSheafificationIso :
    (PresheafOfModules.moduleSheafification X.J (𝟙 X.O.obj)).obj (awayModulePresheafAlt X h) ≅
      awayModule X h :=
  awaySheafificationIsoAwayModule X h

end AlgebraicGeometry.RingedSite

end
