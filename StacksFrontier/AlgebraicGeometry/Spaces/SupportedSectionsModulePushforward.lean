module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsPushforward
import all StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsPushforward
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite

/-!
# Stacks 085B in the spelling of the direct image of Stacks 03LU

`StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsPushforward` identifies, for a morphism
`f : X ⟶ Y` of algebraic spaces and a closed subset `T` of the points of `Y`, the direct image of
the subsheaf of sections supported over `|f|⁻¹T` with the subsheaf of `f_*F` of sections
supported on `T`, for the direct image attached to the morphism of ringed topoi of Stacks 03G8.
This file states the same identification with the direct image spelled as
`AlgebraicGeometry.Space.modulePushforward`, the direct image of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.modulePushforward_supportedSectionsSubmodule_range_eq`.

## Implementation notes

The two spellings differ by a restriction of scalars, which changes no sections; the passage
between them is `AlgebraicGeometry.Space.range_modulePushforward_map_val_app_eq` and
`AlgebraicGeometry.Space.setOf_sectionSupportedIn_modulePushforward_eq`, both by `rfl`.

## References

* [Stacks Project, Tag 085B](https://stacks.math.columbia.edu/tag/085B)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **The two spellings of the direct image agree on the image of a morphism on the sections
over a chart.**  `AlgebraicGeometry.Space.modulePushforward`, the direct image of Stacks 03LU,
is the direct image attached to the morphism of ringed topoi of Stacks 03G8 followed by a
restriction of scalars along the structure map; restriction of scalars changes the ring the
sections are a module over and not the sections themselves, so the two images coincide on the
nose.

The two functors are also *equal*, by
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, but that is an equality of
functors, and rewriting with it abstracts a motive over a functor; the resulting term is
rejected by the kernel budget.  This equation and
`AlgebraicGeometry.Space.setOf_sectionSupportedIn_modulePushforward_eq` are the two places
where the identification is needed, and each is small enough to hold by `rfl`. -/
theorem range_modulePushforward_map_val_app_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) (W : SmallEtale B S hS Y.1) :
    Set.range (((modulePushforward B S hS f).map φ).val.app (op W)) =
      Set.range ((((smallEtaleRingedToposHom B S hS f).pushforwardModules).map φ).val.app
        (op W)) :=
  rfl

/-- **The two spellings of the direct image agree on the support condition of Stacks 0859.**
The condition is a statement about the underlying abelian sheaf of the module, which a
restriction of scalars leaves alone. -/
theorem setOf_sectionSupportedIn_modulePushforward_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (T : Set (points B S hS Y.1))
    (F : Modules.{u, u} B S hS X.1 X.2) (W : SmallEtale B S hS Y.1) :
    {s : (((modulePushforward B S hS f).obj F).val.obj (op W) : Type u) |
        SectionSupportedIn B S hS Y.1 Y.2 T ((modulePushforward B S hS f).obj F) W s} =
      {s : ((((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F).val.obj
            (op W) : Type u) |
        SectionSupportedIn B S hS Y.1 Y.2 T
          (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F) W s} :=
  rfl

/-- **Stacks 085B with the direct image spelled as the one of Stacks 03LU.**  For a morphism
`f : X ⟶ Y` of algebraic spaces over `S`, a closed subset `T` of the points of `Y` and an
`𝒪_X`-module `F`, the direct image `f_*` of Stacks 03LU of the subsheaf of sections supported
over `|f|⁻¹T` is the subsheaf of `f_*F` of sections supported on `T`: the two canonical
inclusions into `f_*F` have the same image over every étale chart of `Y`.

This is the same identification as
`AlgebraicGeometry.Space.pushforward_supportedSectionsSubmodule_range_eq`, which states it for
the direct image attached to the morphism of ringed topoi of Stacks 03G8.  Both spellings are
registered, because consumers of the tag are written against one or the other and the passage
between them is not available downstream: it is cheap only at the two small equations above,
which is why it is made here. -/
@[stacks 085B "the identification of the two subsheaves of the direct image, with the direct \
image spelled as the one of Stacks 03LU"]
theorem modulePushforward_supportedSectionsSubmodule_range_eq
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (T : Set (points B S hS Y.1))
    (hT : @IsClosed _ (pointTopology B S hS Y.1) T)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS Y.1) :
    Set.range (((modulePushforward B S hS f).map
        (supportedSectionsSubmodule B S hS X.1 X.2
          (pointsMap B S hS X.1 f.hom ⁻¹' T) F).ι).val.app (op W)) =
      Set.range ((supportedSectionsSubmodule B S hS Y.1 Y.2 T
        ((modulePushforward B S hS f).obj F)).ι.val.app (op W)) :=
  by
  have hpf : Set.range ((((smallEtaleRingedToposHom B S hS f).pushforwardModules).map
        (supportedSectionsSubmodule B S hS X.1 X.2
          (pointsMap B S hS X.1 f.hom ⁻¹' T) F).ι).val.app (op W)) =
      {s : ((((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F).val.obj
            (op W) : Type u) |
        SectionSupportedIn B S hS Y.1 Y.2 T
          (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F) W s} :=
    (pushforward_supportedSectionsSubmodule_range_eq B S hS f T hT F W).trans
      (range_supportedSectionsSubmodule B S hS Y T
        (((smallEtaleRingedToposHom B S hS f).pushforwardModules).obj F) W)
  have hmp : Set.range (((modulePushforward B S hS f).map
        (supportedSectionsSubmodule B S hS X.1 X.2
          (pointsMap B S hS X.1 f.hom ⁻¹' T) F).ι).val.app (op W)) =
      {s : (((modulePushforward B S hS f).obj F).val.obj (op W) : Type u) |
        SectionSupportedIn B S hS Y.1 Y.2 T ((modulePushforward B S hS f).obj F) W s} := by
    rw [range_modulePushforward_map_val_app_eq B S hS f
      (supportedSectionsSubmodule B S hS X.1 X.2
        (pointsMap B S hS X.1 f.hom ⁻¹' T) F).ι W,
      setOf_sectionSupportedIn_modulePushforward_eq B S hS f T F W]
    exact hpf
  rw [hmp, range_supportedSectionsSubmodule B S hS Y T ((modulePushforward B S hS f).obj F) W]

end AlgebraicGeometry.Space

end
