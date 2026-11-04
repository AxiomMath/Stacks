module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Module.Adequate.Pushforward
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Abelian

/-!
# The direct images along a morphism of chosen big sites

Let `f : T ⟶ S` be a morphism of schemes. On the big sites the direct image is *restriction
along base change*: an object `V` of the site over `S` is carried to `V ×_S T`, an object of the
site over `T`, and

`(f_*𝓕)(V) = 𝓕(V ×_S T)`,

with the scalars transported along the first projection `V ×_S T ⟶ V` of the fibre square. That
is [Stacks, Tag 021W] for modules, and it is how the direct image is built here: as
`CategoryTheory.SheafOfModules.pushforward` along the base-change functor of the two sites, for
the morphism of structure sheaves induced by the first projection.

## Main definitions

* `Stacks.Adequate.IsBaseChangeAlong` — the assertion that a functor `Φ` from the site over `S`
  to the site over `T`, together with a natural morphism of schemes `ν`, computes base change
  along `f`: each `ν.app V` is the first projection of a fibre square exhibiting
  `Φ.obj V = V ×_S T`.
* `Stacks.Adequate.directImageScalars` — the morphism of structure sheaves induced by `ν`, the
  change of scalars `Γ(V) ⟶ Γ(V ×_S T)` along which `f_*` restricts.
* `Stacks.Adequate.directImage` — the direct image `f_*` of sheaves of modules on the big sites.
* `Stacks.Adequate.higherDirectImage` — the higher direct image `R^i f_*`, the `i`-th right
  derived functor of `Stacks.Adequate.directImage`.

## Main results

* `Stacks.Adequate.directImage_obj_val_obj` and `Stacks.Adequate.directImage_obj_val_map` — the
  source's formula `(f_*𝓕)(V) = 𝓕(V ×_S T)` together with the matching identity for the
  restriction maps.

## Implementation notes

*The two sites and the base change.* A `Stacks.Adequate.BigSite` records the topology of each
site only in terms of the accepted big-site construction over its own base, and records no
compatibility between the site over `T` and the site over `S`; in particular the schemes
`V ×_S T` need not lie below the cutoff of the site over `T`. So the base-change functor `Φ`
between them and the first projection `ν` are taken as arguments, and that `Φ` really is base
change along `f` is `Stacks.Adequate.IsBaseChangeAlong`, which pins it down up to canonical
isomorphism by the universal property of the fibre product. Continuity of `Φ` is what makes the
restriction of a sheaf a sheaf; for the localizations of one big topology it is
`CategoryTheory.GrothendieckTopology.instIsContinuousOverPullbackOver`.

*The higher direct images.* `R^i f_*` is the `i`-th right derived functor of `f_*`, the source's
own definition. The abelian structure on the two categories of sheaves of modules, in the form
of the `HasSheafify` and `WEqualsLocallyBijective` assumptions from which Mathlib derives it,
and the injectives in the source category enter as typeclass assumptions of the definition, so
that it is available at every value universe; at the universe of the schemes of the sites all of
them are instances (`Stacks.Adequate.BigSite.hasSheafify_addCommGrpCat`,
`Stacks.Adequate.BigSite.wEqualsLocallyBijective_addCommGrpCat`,
`Stacks.Adequate.BigSite.enoughInjectives_sheafOfModules`).

## References

* [Stacks Project, Tag 06VR](https://stacks.math.columbia.edu/tag/06VR)
* [Stacks Project, Tag 021W](https://stacks.math.columbia.edu/tag/021W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S T : Scheme.{u}}

/-! ### Base change between two chosen big sites -/

section BaseChange

variable (B : BigSite τ S) (C : BigSite τ T) (f : T ⟶ S) (Φ : B.category ⥤ C.category)
  (ν : Φ ⋙ C.toOver ⋙ Over.forget T ⟶ B.toOver ⋙ Over.forget S)

/-- The assertion that the functor `Φ` from a chosen big site over `S` to a chosen big site over
`T`, together with the natural morphism of schemes `ν`, computes base change along `f`: for every
object `V` of the site over `S` the square with sides `ν.app V`, the structure morphism of
`Φ.obj V` over `T`, the structure morphism of `V` over `S` and `f` is a fibre square. So
`Φ.obj V` is `V ×_S T` and `ν.app V` is its first projection, which determines `Φ` up to
canonical isomorphism. -/
public def IsBaseChangeAlong : Prop :=
  ∀ V : B.category,
    IsPullback (ν.app V) (C.toOver.obj (Φ.obj V)).hom (B.toOver.obj V).hom f

end BaseChange

/-! ### The direct image of sheaves of modules on the big sites -/

section DirectImage

variable (B : BigSite τ S) (C : BigSite τ T) (Φ : B.category ⥤ C.category)
  (ν : Φ ⋙ C.toOver ⋙ Over.forget T ⟶ B.toOver ⋙ Over.forget S)
  [Φ.IsContinuous B.topology C.topology]

/-- The change of scalars along which the direct image restricts: the ring map
`Γ(V) ⟶ Γ(V ×_S T)` induced by the first projection of the fibre square, for every object `V` of
the site over `S`. Both structure sheaves assign to an object of their site the ring of global
functions on its underlying scheme, so this is the global-functions functor applied to `ν`. -/
public def directImageScalars :
    B.structureSheaf ⟶
      (Φ.sheafPushforwardContinuous RingCat.{u} B.topology C.topology).obj C.structureSheaf :=
  ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op ν) (Scheme.Γ.{u} ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

/-- The direct image `f_*` of sheaves of modules along a morphism of the big sites: restriction
along base change, with the scalars transported along the first projection. This is
[Stacks, Tag 021W] for modules. -/
public def directImage :
    SheafOfModules.{m} C.structureSheaf ⥤ SheafOfModules.{m} B.structureSheaf :=
  SheafOfModules.pushforward (directImageScalars B C Φ ν)

/-- **The source's formula `(f_*𝓕)(V) = 𝓕(V ×_S T)`**: the sections of the direct image over an
object `V` of the site over `S` are the sections of `𝓕` over `Φ.obj V`, which
`Stacks.Adequate.IsBaseChangeAlong` identifies with `V ×_S T`. -/
public theorem directImage_obj_val_obj (F : SheafOfModules.{m} C.structureSheaf)
    (V : B.categoryᵒᵖ) :
    (((directImage.{u, m} B C Φ ν).obj F).val.obj V : Type m) =
      (F.val.obj (Φ.op.obj V) : Type m) := rfl

/-- The restriction maps of the direct image are those of `𝓕` along base change. -/
public theorem directImage_obj_val_map (F : SheafOfModules.{m} C.structureSheaf)
    {V W : B.categoryᵒᵖ} (k : V ⟶ W)
    (x : ((directImage.{u, m} B C Φ ν).obj F).val.obj V) :
    ((directImage.{u, m} B C Φ ν).obj F).val.map k x = F.val.map (Φ.op.map k) x := rfl

/-- The direct image is additive. -/
public instance directImage_additive : (directImage.{u, m} B C Φ ν).Additive where
  map_add := rfl

/-- The higher direct image `R^i f_*`, the `i`-th right derived functor of the direct image.
This is the source's own definition of the higher direct images. -/
public abbrev higherDirectImage [HasSheafify C.topology AddCommGrpCat.{m}]
    [C.topology.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify B.topology AddCommGrpCat.{m}]
    [B.topology.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [EnoughInjectives (SheafOfModules.{m} C.structureSheaf)] (i : ℕ) :
    SheafOfModules.{m} C.structureSheaf ⥤ SheafOfModules.{m} B.structureSheaf :=
  (directImage.{u, m} B C Φ ν).rightDerived i

end DirectImage

end Stacks.Adequate

end
