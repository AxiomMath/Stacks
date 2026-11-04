module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ampleness restricted to a quasi-compact open subscheme

An ample invertible module on a scheme restricts to an ample invertible module on any quasi-compact
open subscheme. This is the case of [Stacks, Tag 0B3E] for the open immersion `V.ι : V ⟶ X` of an
open whose underlying space is quasi-compact, with ampleness read as
`AlgebraicGeometry.Scheme.Modules.IsAmple`, invertibility as
`AlgebraicGeometry.SheafOfModules.IsInvertible` at the structure presheaf of the underlying ringed
space, and the restriction as `(AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj L`.

## Main results

* `Stacks.AmpleRestrict.isInvertible_pullback`: the pullback of an invertible module along a
  morphism of schemes is invertible ([Stacks, Tag 0B8L]).
* `Stacks.AmpleRestrict.isAmple_pullback_ι`: the restriction of an ample invertible module to a
  quasi-compact open subscheme is ample ([Stacks, Tag 0B3E]).
* `Stacks.AmpleRestrict.isNoetherian_opens_toScheme`: an open subscheme of a Noetherian scheme is
  Noetherian.
* `Stacks.AmpleRestrict.isAmple_pullback_ι_of_isNoetherian`: the restriction of an ample invertible
  module on a Noetherian scheme to any open subscheme is ample.

## References

* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01OZ](https://stacks.math.columbia.edu/tag/01OZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AmpleRestrict

/-- The pullback of an invertible `𝒪_X`-module along a morphism of schemes `f : W ⟶ X` is an
invertible `𝒪_W`-module ([Stacks, Tag 0B8L]). -/
public instance isInvertible_pullback {W X : Scheme.{u}} (f : W ⟶ X) (L : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible W.toRingedSpace.presheaf
      (structureSheafRing W.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj L) :=
  @Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback W.toRingedSpace
    X.toRingedSpace f.toLRSHom.toShHom L h

variable {X : Scheme.{u}}

/-- The restriction `Stacks.AmpleLocallyClosed.pullbackModule V.ι L` of an ample invertible module
`L` to a quasi-compact open `V` is ample, for `Stacks.Ample.IsAmple` ([Stacks, Tag 0B3E]). -/
public theorem isAmple_pullbackModule_ι (V : X.Opens) [CompactSpace V.toScheme] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) :
    Stacks.Ample.IsAmple V.toScheme (Stacks.AmpleLocallyClosed.pullbackModule V.ι L) :=
  Stacks.SectionExtension.isAmple_pullbackModule V.ι L hL
    (Or.inr (Or.inl ⟨‹CompactSpace V.toScheme›, inferInstance⟩))

/-- The restriction `Stacks.AmpleLocallyClosed.pullbackModule V.ι L` of an ample invertible module
`L` to a quasi-compact open `V` is ample for `AlgebraicGeometry.Scheme.Modules.IsAmple`.
-/
public theorem modulesIsAmple_pullbackModule_ι (V : X.Opens) [CompactSpace V.toScheme]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) :
    AlgebraicGeometry.Scheme.Modules.IsAmple V.toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule V.ι L) :=
  (Stacks.AmpleBridge.isAmple_iff_isAmple V.toScheme
    (Stacks.AmpleLocallyClosed.pullbackModule V.ι L)).mp (isAmple_pullbackModule_ι V L hL)

/-- The restriction `(AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj L` of an ample invertible
module `L` on a scheme to a quasi-compact open `V` is ample ([Stacks, Tag 0B3E]). -/
public theorem isAmple_pullback_ι (V : X.Opens) [CompactSpace V.toScheme] (L : X.Modules)
    [inst : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) :
    AlgebraicGeometry.Scheme.Modules.IsAmple V.toScheme
      ((Scheme.Modules.pullback V.ι).obj L) :=
  have : Stacks.Ample.IsInvertibleModule X L := inst
  modulesIsAmple_pullbackModule_ι V L ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr hL)

/-- An open subscheme of a Noetherian scheme is quasi-compact. -/
public theorem compactSpace_opens_toScheme [IsNoetherian X] (V : X.Opens) :
    CompactSpace V.toScheme :=
  have : TopologicalSpace.NoetherianSpace (V.toScheme : Type u) :=
    TopologicalSpace.NoetherianSpace.set (V : Set X)
  inferInstance

/-- An open subscheme of a Noetherian scheme is Noetherian. -/
@[ega "I 10.4.4" "special case", ega "I 6.1.4" "special case"]
public theorem isNoetherian_opens_toScheme [IsNoetherian X] (V : X.Opens) :
    IsNoetherian V.toScheme :=
  have : CompactSpace V.toScheme := compactSpace_opens_toScheme V
  { }

/-- The restriction `(AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj L` of an ample invertible
module `L` on a Noetherian scheme to any open `V` is ample ([Stacks, Tag 0B3E]). -/
public theorem isAmple_pullback_ι_of_isNoetherian [IsNoetherian X] (V : X.Opens)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) :
    AlgebraicGeometry.Scheme.Modules.IsAmple V.toScheme
      ((Scheme.Modules.pullback V.ι).obj L) :=
  have : CompactSpace V.toScheme := compactSpace_opens_toScheme V
  isAmple_pullback_ι V L hL

end Stacks.AmpleRestrict

end
