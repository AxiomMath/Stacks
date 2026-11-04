module

public import StacksFrontier.AlgebraicGeometry.Coherent.SheafHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHom
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.SchemeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.InternalHomLocalKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteLocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sheaf Hom of two finite locally free modules is finite locally free

Let `X` be a scheme and let `ℰ` and `𝒢` be finite locally free `𝒪_X`-modules. Then the sheaf Hom
`SheafHom(ℰ, 𝒢)` is again finite locally free, with no assumption that the ranks of `ℰ` and `𝒢`
be constant.

The argument is local and does not go through the ranks. Pick a point of `X`, a member `U₁` of a
local free presentation of `ℰ` containing it and a member `U₂` of a local free presentation of
`𝒢` containing it; on `U = U₁ ⊓ U₂` both restrictions are free, on finite index sets `I` and `K`
respectively. Sheaf Hom commutes with restriction to `U`, it turns the finite coproduct
`𝒪_U^{⊕I}` in its first variable into the finite product of copies of `𝒢|_U`, which in an
additive category is the coproduct `∐_{i : I} 𝒢|_U`, and a coproduct of free modules is free on
the sigma type. So `SheafHom(ℰ, 𝒢)|_U` is free on `Σ _ : I, K`, and the intersections `U`
obtained this way cover `X`.

## Main definitions

* `Stacks.AlgebraicGeometry.SheafHomLocallyFree.freeIsoSheafHomOver`: on an open over which the
  source is free on a finite index set `I` and the target is free on a finite index set `K`, the
  sheaf Hom is free on `Σ _ : I, K`.

## Main results

* `Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_sheafHomFunctor`: the sheaf
  Hom of two finite locally free modules on a scheme is finite locally free, stated for the
  Tag 03EN second-variable functor `Stacks.Algebraization.sheafHomFunctor`.
* `Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_internalHomSheaf` and
  `Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_sheafHomModules`: the same
  conclusion for the two other spellings of the sheaf Hom on a scheme,
  `Stacks.AlgebraicGeometry.InternalHomScheme.internalHomSheaf` and
  `Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules`.
* `Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_internalHomCoherent`: the
  internal hom of two coherent modules on a locally Noetherian scheme, packaged as a coherent
  module by `Stacks.Algebraization.internalHomCoherent`, is finite locally free when both
  arguments are.

## Implementation notes

All three spellings of the sheaf Hom of two modules on a scheme that appear here —
`(Stacks.Algebraization.sheafHomFunctor X ℰ).obj 𝒢` (the Tag 03EN second-variable functor),
`Stacks.AlgebraicGeometry.InternalHomScheme.internalHomSheaf ℰ 𝒢` and
`Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules ℰ 𝒢` — have underlying presheaf of
modules `Stacks.PresheafOfModules.InternalHom.internalHom X.sheaf.obj ℰ.val 𝒢.val` on the nose,
and the sheaf condition is a proposition, so they are the same object and nothing has to be
transported between them. The same holds of the underlying module of
`Stacks.Algebraization.internalHomCoherent`, which is what
`Stacks.Algebraization.internalHomCoherent_obj` records.

The two local inputs are read off results already stated for a ringed site, at the ringed site
`Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X` of the opens of `X`: that sheaf
Hom commutes with restriction is `Stacks.AlgebraicGeometry.InternalHomLocalKernel`'s
`sheafInternalHomOverIso`, the sheaf form of Tag 0E8H, and that sheaf Hom out of a finite free
module is a finite coproduct of copies of the target is `freeSheafInternalHomIso`, both read on
the slice site over `U`. No computation with local sections and no local dual basis enters.

The common refinement of the two local free presentations is the only thing this argument needs
beyond the `𝒢 = 𝒪_X` case,
`Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf`. Restricting a free
trivialisation from an open to a smaller one is `Stacks.SheafOfModules.overIsoFree`, and the two
members of the two presentations are intersected in `X.Opens`, so the refinement is a binary
meet and no covering family has to be built by hand.

The rank-indexed results of the library require a constant rank and so do not apply: a finite
locally free module has a rank only locally, and the index sets of a local free presentation vary
from one member of the covering to another. What replaces them is
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_forall_exists_iso_free_over`, which
assembles finite local freeness from free restrictions on a neighbourhood of every point and so
never names a global rank. The index set used at a point is `Σ _ : I, K` for the index sets `I`
and `K` the two presentations provide there — the sigma type rather than the product, because
that is the shape in which `SheafOfModules.freeSigmaIso` folds a coproduct of free modules back
into a free module.

## References

* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.AlgebraicGeometry.SheafHomLocallyFree

/-- **The sheaf Hom of two free modules on finite index sets is free**, read on the slice site of
the opens of `X` over `U`: if the restriction of `E` to `U` is free on a finite index set `I` and
the restriction of `G` to `U` is free on a finite index set `K`, then the restriction of
`SheafHom(E, G)` to `U` is free on `Σ _ : I, K`.

The restriction of the sheaf Hom is the sheaf Hom of the restrictions, by Tag 0E8H; the sheaf
Hom out of `𝒪_U^{⊕I}` is `∐_{i : I} G|_U`, by Tag 03EN together with the computation of the
sheaf Hom out of `𝒪_U`; and a coproduct of free modules is free on the sigma type. -/
noncomputable def freeIsoSheafHomOver (X : Scheme.{u}) (U : X.Opens) (E G : X.Modules)
    {I K : Type u} [Finite I] [Finite K]
    (eE : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ E.over U)
    (eG : G.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) K) :
    ((Stacks.Algebraization.sheafHomFunctor X E).obj G).over U ≅
      SheafOfModules.free (R := X.ringCatSheaf.over U) ((_ : I) × K) :=
  InternalHomLocalKernel.sheafInternalHomOverIso (schemeRingedSite X) U E G ≪≫
    ((Stacks.SheafOfModules.InternalHom.sheafInternalHomFunctor
        ((Opens.grothendieckTopology ↥X).over U) (X.sheaf.over U)
        (G.over U)).mapIso eE).unop ≪≫
      InternalHomLocalKernel.freeSheafInternalHomIso (X.sheaf.over U) (G.over U) I ≪≫
        Sigma.mapIso (fun _ : I => eG) ≪≫
          SheafOfModules.freeSigmaIso (O := X.ringCatSheaf.over U) (fun _ : I => K)

/-- Around every point, a finite locally free module is free on a finite index set over some open
neighbourhood. -/
private theorem exists_mem_open_nonempty_over_iso_free {X : Scheme.{u}} (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E) (x : X) :
    ∃ (V : X.Opens) (I : Type u), x ∈ V ∧ Finite I ∧
      Nonempty (E.over V ≅ SheafOfModules.free (R := X.ringCatSheaf.over V) I) := by
  obtain ⟨q, hq, hqf⟩ := hE.exists_isFiniteLocallyFreeData
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff _ q.X).1 q.coversTop).exists_mem x
  have := hq.isIso i
  exact ⟨q.X i, _, hxi, (hqf.isFiniteType i).finite, ⟨(asIso (q.generators i).π).symm⟩⟩

/-- **The sheaf Hom of two finite locally free modules on a scheme is finite locally free.**
Neither rank is assumed constant.

Every point has a neighbourhood `U` — the intersection of a member of a local free presentation
of `E` with a member of one of `G` — on which both modules are free on finite index sets `I` and
`K`, and there `SheafHom(E, G)` is free on `Σ _ : I, K` by `freeIsoSheafHomOver`. -/
theorem isFiniteLocallyFree_sheafHomFunctor {X : Scheme.{u}} (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      ((Stacks.Algebraization.sheafHomFunctor X E).obj G) := by
  apply SheafOfModules.isFiniteLocallyFree_of_forall_exists_iso_free_over
  intro x
  obtain ⟨V, I, hxV, _, ⟨eE⟩⟩ := exists_mem_open_nonempty_over_iso_free E hE x
  obtain ⟨W, K, hxW, _, ⟨eG⟩⟩ := exists_mem_open_nonempty_over_iso_free G hG x
  exact ⟨V ⊓ W, ⟨hxV, hxW⟩, (_ : I) × K, inferInstance,
    ⟨(freeIsoSheafHomOver X (V ⊓ W) E G
      (Stacks.SheafOfModules.overIsoFree (homOfLE inf_le_left) _ eE).symm
      (Stacks.SheafOfModules.overIsoFree (homOfLE inf_le_right) _ eG)).symm⟩⟩

/-- **The sheaf Hom of two finite locally free modules on a scheme is finite locally free**, for
the `Stacks.AlgebraicGeometry.InternalHomScheme.internalHomSheaf` spelling of the sheaf Hom. -/
@[sga "2 X 2.2" "Hom(E"]
theorem isFiniteLocallyFree_internalHomSheaf {X : Scheme.{u}} (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Stacks.AlgebraicGeometry.InternalHomScheme.internalHomSheaf E G) :=
  isFiniteLocallyFree_sheafHomFunctor E G hE hG

/-- **The sheaf Hom of two finite locally free modules on a scheme is finite locally free**, for
the `Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules` spelling of the sheaf Hom. -/
@[sga "2 X 2.2" "Hom(E"]
theorem isFiniteLocallyFree_sheafHomModules {X : Scheme.{u}} (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Stacks.AlgebraicGeometry.InternalHomModules.sheafHomModules E G) :=
  isFiniteLocallyFree_sheafHomFunctor E G hE hG

/-- **The internal hom of two coherent modules which are finite locally free is finite locally
free**, for the packaging `Stacks.Algebraization.internalHomCoherent` of the internal hom of two
coherent modules on a locally Noetherian scheme as a coherent module.

The underlying module of `internalHomCoherent X G F` is `SheafHom(G, F)` on the nose, by
`Stacks.Algebraization.internalHomCoherent_obj`, so this is
`isFiniteLocallyFree_sheafHomFunctor`. -/
@[sga "2 X 2.2" "Hom(E"]
theorem isFiniteLocallyFree_internalHomCoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G.obj)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F.obj) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.Algebraization.internalHomCoherent X G F).obj :=
  isFiniteLocallyFree_sheafHomFunctor (X := X) G.obj F.obj hG hF

end Stacks.AlgebraicGeometry.SheafHomLocallyFree

end
