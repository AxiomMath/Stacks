module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.LocalKernel
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf-hom of two coherent modules on a locally Noetherian scheme is quasi-coherent

Let `X` be a locally Noetherian scheme and `F`, `G` coherent `𝒪_X`-modules. Then the sheaf-hom
`SheafHom(F, G)`, whose sections over an open `U` are the `𝒪_U`-linear maps `F|_U ⟶ G|_U`, is a
quasi-coherent `𝒪_X`-module.

This is the input that [Stacks, Tag 01YB] calls on in its morphism clause and which Schemes,
Section 26.24 ([Stacks, Tag 01LA]) supplies: a coherent module on a locally Noetherian scheme is
of finite presentation, so the local-kernel description of [Stacks, Tag 01CQ] applies and makes
`SheafHom(F, G)` coherent, hence quasi-coherent by [Stacks, Tag 01XZ].

## Main definitions

* `Stacks.AlgebraicGeometry.InternalHomScheme.internalHomSheaf`: the sheaf-hom of two
  `𝒪_X`-modules, as an `𝒪_X`-module.

## Main results

* `Stacks.AlgebraicGeometry.InternalHomScheme.isCoherent_internalHomSheaf`: it is coherent when
  both arguments are.
* `Stacks.AlgebraicGeometry.InternalHomScheme.isQuasicoherent_internalHomSheaf`: hence
  quasi-coherent.
* `Stacks.AlgebraicGeometry.InternalHomScheme.isFinitePresentation_internalHomSheaf`: and of
  finite presentation.

## Implementation notes

Nothing here is new mathematics; the point is the spelling. The coherence of a sheaf-hom is
proved on a ringed *site* in
`Stacks.SheafOfModules.InternalHom.isCoherent_sheafInternalHom'`, indexed by
`AlgebraicGeometry.RingedSite.ringSheaf` of the site
`Stacks.SheafOfModules.InternalHom.spaceRingedSite X.sheaf`. That sheaf of rings is the same as
`AlgebraicGeometry.Scheme.ringCatSheaf` only up to unfolding a non-reducible definition, and the
two coherence predicates `SheafOfModules.IsCoherent` and `Stacks.SheafOfModules.IsCoherent` both
resolve unqualified inside this namespace, so every occurrence below is written `_root_.`
explicitly. `internalHomSheaf` is given in the `X.Modules` spelling, with the same body as
`sheafInternalHom`, so that its consumers never meet the site at all.

The special case `G = 𝒪_X` is `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`, whose
finite presentation is
`Stacks.AlgebraicGeometry.Reflexive.isFinitePresentation_dualSheaf`; this definition has the
same body with the structure sheaf in place of `G`.

What this does *not* give is [Stacks, Tag 01LA] in its own generality, where the source is only
of finite presentation and the target only quasi-coherent. The route to that is the gluing step
"locally a kernel of a map between finite coproducts of a quasi-coherent module, hence
quasi-coherent", the quasi-coherent analogue of
`Stacks.SheafOfModules.isCoherent_of_locallyKernelFiniteCoproduct`, which is not in this
library. The coherent case proved here is what the morphism clause of [Stacks, Tag 01YB] is
applied to on a Noetherian scheme, so it is the case [Stacks, Tag 0BJZ] needs.

## References

* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.PresheafOfModules.InternalHom
open Stacks.SheafOfModules.InternalHom

universe u

namespace Stacks.AlgebraicGeometry.InternalHomScheme

variable {X : Scheme.{u}}

/-- **The sheaf-hom of two `𝒪_X`-modules**, as an `𝒪_X`-module: its sections over an open `U`
are the `𝒪_U`-linear maps `F|_U ⟶ G|_U`.

This is `Stacks.SheafOfModules.InternalHom.sheafInternalHom` at the ringed site of `X`, written
in the `AlgebraicGeometry.Scheme.Modules` spelling. The sheaf condition needs only that `G` is a
sheaf. -/
public noncomputable def internalHomSheaf (F G : X.Modules) : X.Modules where
  val := internalHom X.sheaf.obj F.val G.val
  isSheaf := internalHom_isSheaf X.sheaf.obj F.val G.val G.isSheaf

/-- **The sheaf-hom of two coherent modules on a locally Noetherian scheme is coherent.** This
is the second clause of [Stacks, Tag 01CQ]: a coherent module on a locally Noetherian scheme is
of finite presentation, and the sheaf-hom out of a module of finite presentation into a coherent
module is coherent. -/
@[sga "2 VI 2.1" "Z = X"]
public theorem isCoherent_internalHomSheaf [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G] :
    _root_.SheafOfModules.IsCoherent (internalHomSheaf F G) := by
  let : _root_.SheafOfModules.IsFinitePresentation
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite X.sheaf).O)) F :=
    _root_.isFinitePresentation_of_isCoherent F
  let : _root_.SheafOfModules.IsCoherent
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (spaceRingedSite X.sheaf).O)) G :=
    ‹_root_.SheafOfModules.IsCoherent G›
  exact isCoherent_sheafInternalHom' X.sheaf F G

/-- **The sheaf-hom of two coherent modules on a locally Noetherian scheme is quasi-coherent.**
This is the input [Stacks, Tag 01LA] supplies to the morphism clause of [Stacks, Tag 01YB], in
the generality in which that clause is applied on a Noetherian scheme.

It is `isCoherent_internalHomSheaf` followed by the implication (1) ⇒ (2) of
[Stacks, Tag 01XZ]. -/
public theorem isQuasicoherent_internalHomSheaf [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G] :
    (internalHomSheaf F G).IsQuasicoherent :=
  have : _root_.SheafOfModules.IsCoherent (internalHomSheaf F G) :=
    isCoherent_internalHomSheaf F G
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    (internalHomSheaf F G)).1

/-- The sheaf-hom of two coherent modules on a locally Noetherian scheme is of finite
presentation: it is coherent, and a coherent module is of finite presentation. -/
public theorem isFinitePresentation_internalHomSheaf [IsLocallyNoetherian X] (F G : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] [_root_.SheafOfModules.IsCoherent G] :
    (internalHomSheaf F G).IsFinitePresentation :=
  have : _root_.SheafOfModules.IsCoherent (internalHomSheaf F G) :=
    isCoherent_internalHomSheaf F G
  _root_.isFinitePresentation_of_isCoherent (internalHomSheaf F G)

end Stacks.AlgebraicGeometry.InternalHomScheme

end
