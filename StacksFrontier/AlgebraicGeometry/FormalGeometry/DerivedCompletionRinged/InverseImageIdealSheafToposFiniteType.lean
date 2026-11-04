module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.InverseImageIdealSheafTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFiniteType

/-!
# `f^{-1}ℐ · 𝒪_X` is of finite type, at a morphism of ringed topoi

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed topoi and `ℐ ⊂ 𝒪` a sheaf of ideals
of finite type. `InverseImageIdealSheafTopos.lean` builds `ℐ' = f^{-1}ℐ · 𝒪_X ⊂ 𝒪'` as the image
of `f^*ℐ ⟶ 𝒪'`. This file proves that `ℐ'` is again of finite type, which is what makes the
derived completion functor along `ℐ'` exist by [Stacks, Tag 099F] and so is the second property
[Stacks, Tag 0A0G] needs of the construction, after the relation of [Stacks, Tag 099J].

## Main results

* `AlgebraicGeometry.RingedToposHom.isFiniteType_pullbackModules`: **[Stacks, Tag 03DO] for the
  clause [Stacks, Tag 03DL] (5), at the two-field morphism of ringed topoi** — `f^*` preserves
  finite type, along an **arbitrary** morphism.
* `AlgebraicGeometry.RingedToposHom.isFiniteType_inverseImageIdealSheaf`: **`ℐ'` is of finite type
  when `ℐ` is.**
* `AlgebraicGeometry.RingedToposHom.isFiniteType_inverseImageIdealSheaf_of_instance`: the same, as
  an instance.

## Implementation notes

`Stacks.Sheaves.FiniteType.pullbackModules_isFiniteType` is [Stacks, Tag 03DO] for
`Stacks.Sheaves.RingedToposModules.pullbackModules`, the pullback of the modules development,
which is indexed by the four-field `Stacks.Sheaves.RingedToposModules.RingedToposHom`. It carries
no hypothesis on the morphism. The two-field `AlgebraicGeometry.RingedToposHom.pullbackModules` of
[Stacks, Tag 03D6] part (2) is *defined* as that functor at `toModulesHom`, so the tag applies to
it on the nose, with no comparison isomorphism and no passage between `RingCat` and `CommRingCat`.
This is the same reduction `AlgebraicGeometry.RingedToposHom.isFiniteType_iff_pullbackModules`
performs in its forward direction.

Preservation of finite type by `pullbackModules` along a general morphism of ringed topoi is the
first theorem below, which is the two-field reading of the four-field statement.
`isFiniteType_iff_pullbackModules` is not that statement: it asks `f` to be an equivalence, and so
gives invariance under the dense-subsite replacement of [Stacks, Tag 03CR] rather than
preservation.

The slice-site sheafification hypotheses are the ones [Stacks, Tag 03DO] itself carries: finite
type is a condition on a covering of each object, so the proof passes to the localised sites.
`HasSheafify` on `X.J` and on its slices is derived from them inside the second proof, where the
image subsheaf needs it, exactly as in the ringed-sites
`AlgebraicGeometry.RingedSite.isFiniteType_inverseImageIdealSheaf`.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y)
  (I : SheafOfModules.Submodule (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-- The inverse image `f^*M` of a sheaf of modules `M` of finite type along an arbitrary
morphism of ringed topoi `f` is of finite type.

`Stacks.Sheaves.FiniteType.pullbackModules_isFiniteType` is the tag, for the pullback
`Stacks.Sheaves.RingedToposModules.pullbackModules` of the modules development over the four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom`.
`AlgebraicGeometry.RingedToposHom.pullbackModules` is that functor at
`AlgebraicGeometry.RingedToposHom.toModulesHom`, by definition, so the tag transfers on the nose —
unlike the route through `toRingedToposModulesHom`, which would need
`AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso`. -/
theorem isFiniteType_pullbackModules
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hM : M.IsFiniteType) :
    ((f.toModulesHom.pullbackModules).obj M).IsFiniteType :=
  Stacks.Sheaves.FiniteType.pullbackModules_isFiniteType f.toModulesHom M hM

/-- **`ℐ' = f^{-1}ℐ · 𝒪_X` is of finite type when `ℐ` is**, for an arbitrary morphism of ringed
topoi. With the relation of [Stacks, Tag 099J] — proved by
`AlgebraicGeometry.RingedToposHom.idealCompatible_inverseImageIdealSheaf` — this is the second of
the two properties Section 52.7 needs of its ideal sheaf: it is what makes the derived completion
functor along `ℐ'` exist, by [Stacks, Tag 099F] in the form
`AlgebraicGeometry.RingedSite.isRightAdjoint_ι_isDerivedComplete`.

`ℐ'` is the image of `f^*ℐ ⟶ 𝒪'`; the source is of finite type by `isFiniteType_pullbackModules`,
and the image of a morphism out of a sheaf of modules of finite type is of finite type by
`Stacks.SheafOfModules.ImageSubsheaf.isFiniteType_imageSubmodule`. This is the ringed-topoi
counterpart of `AlgebraicGeometry.RingedSite.isFiniteType_inverseImageIdealSheaf`, and the proof
is the same two steps. -/
theorem isFiniteType_inverseImageIdealSheaf (hI : I.toSheafOfModules.IsFiniteType) :
    (inverseImageIdealSheaf.{u} f I).toSheafOfModules.IsFiniteType :=
  have : HasSheafify X.J AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have : ∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u} := fun _ =>
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  Stacks.SheafOfModules.ImageSubsheaf.isFiniteType_imageSubmodule (inverseImageIdealMap f I)
    (isFiniteType_pullbackModules f I.toSheafOfModules hI)

/-- `AlgebraicGeometry.RingedToposHom.isFiniteType_inverseImageIdealSheaf` as an instance, for an
`ℐ` carrying the finite-type instance. -/
instance isFiniteType_inverseImageIdealSheaf_of_instance [I.toSheafOfModules.IsFiniteType] :
    (inverseImageIdealSheaf.{u} f I).toSheafOfModules.IsFiniteType :=
  isFiniteType_inverseImageIdealSheaf f I inferInstance

end AlgebraicGeometry.RingedToposHom

end
