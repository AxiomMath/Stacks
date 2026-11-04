module

public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeLocal
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType

/-!
# Coherence and reflexivity are local on affine opens

Both assertions of [Stacks, Tag 0EY6] about the extension algebra of a finite étale cover are
assertions about a module on a locally Noetherian — not necessarily quasi-compact — scheme, while
the extension theorem they rest on ([Stacks, Tag 0G41] part (2)) needs quasi-compactness. This
file supplies the reduction that bridges the two: a module on a locally Noetherian scheme is
coherent, resp. reflexive, as soon as its restriction to every affine open is.

Coherence is quasi-coherence together with finite type ([Stacks, Tag 01XZ]), and both of those
are local on the base — `AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen` and
`AlgebraicGeometry.isFiniteType_of_restrict`. Reflexivity is not local as stated, but it is
equivalent to reflexivity of all the stalks for a coherent module ([Stacks, Tag 0AY3]), and a
stalk of `F` at a point of an open `W` is a stalk of `F|_W`.

## Main results

* `isCoherent_of_isAffineOpen_restrict` — coherence is local on affine opens.
* `isReflexive_of_isAffineOpen_restrict` — reflexivity of a coherent module is local on affine
  opens.

## Implementation notes

The coherence predicate is written `_root_.SheafOfModules.IsCoherent` throughout. That is not
cosmetic: the library carries two distinct coherence constants with identical fields, and inside
the `Stacks.` namespace both the unqualified name and dot notation resolve to the other one, with
no error anywhere. See the implementation notes of
`StacksFrontier/AlgebraicGeometry/PushforwardCoherent.lean`.

Finite type is tested on the family of *all* affine opens, whose supremum is `⊤` by
`AlgebraicGeometry.iSup_affineOpens_eq_top`, rather than on a chosen cover: the hypothesis is
quantified over all affine opens anyway, so there is nothing to choose.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.ReflexiveEquivalence

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

variable {X : Scheme.{u}}

/-! ### Coherence -/

/-- **Coherence is local on affine opens.** A module on a locally Noetherian scheme whose
restriction to every affine open is coherent is coherent.

By [Stacks, Tag 01XZ] coherence is quasi-coherence together with finite type, and each of those
descends from the affine opens: quasi-coherence by
`AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen` and finite type by
`AlgebraicGeometry.isFiniteType_of_restrict` applied to the family of all affine opens. -/
public theorem isCoherent_of_isAffineOpen_restrict [IsLocallyNoetherian X] (F : X.Modules)
    (hF : ∀ W : X.Opens, IsAffineOpen W → _root_.SheafOfModules.IsCoherent (F.restrict W.ι)) :
    _root_.SheafOfModules.IsCoherent F := by
  have hq : F.IsQuasicoherent := by
    refine isQuasicoherent_of_restrict_isAffineOpen F fun W hW => ?_
    have := hF W hW
    exact isQuasicoherent_of_isCoherent _
  have hft : F.IsFiniteType := by
    refine isFiniteType_of_restrict F (fun V : X.affineOpens => (V : X.Opens))
      (iSup_affineOpens_eq_top X) fun V => ?_
    have := hF (V : X.Opens) V.2
    exact _root_.SheafOfModules.IsCoherent.isFiniteType
  exact Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
    F

/-! ### Reflexivity -/

/-- **Reflexivity of a coherent module is local on affine opens.** A coherent module on a locally
Noetherian scheme whose restriction to every affine open is reflexive is reflexive.

By [Stacks, Tag 0AY3] a coherent module is reflexive exactly when all of its stalks are, and the
stalk of `F` at a point `x` of an affine open `W` is the stalk of `F|_W` there, by
`Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_stalk_of_isReflexive_stalk_restrict`. -/
public theorem isReflexive_of_isAffineOpen_restrict [IsLocallyNoetherian X] (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F]
    (hF : ∀ W : X.Opens, IsAffineOpen W → IsReflexive (F.restrict W.ι)) :
    IsReflexive F := by
  have hfp : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have hdfp : (dualSheaf F).IsFinitePresentation := isFinitePresentation_dualSheaf F
  refine isReflexive_of_forall_isReflexive_stalk F fun x => ?_
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have : IsLocallyNoetherian W.toScheme := isLocallyNoetherian_of_isOpenImmersion W.ι
  have hc : _root_.SheafOfModules.IsCoherent (F.restrict W.ι) := isCoherent_restrict W F
  have hfp' : (F.restrict W.ι).IsFinitePresentation := isFinitePresentation_of_isCoherent _
  have hdfp' : (dualSheaf (F.restrict W.ι)).IsFinitePresentation :=
    isFinitePresentation_dualSheaf _
  exact isReflexive_stalk_of_isReflexive_stalk_restrict W.ι F ⟨x, hxW⟩
    (isReflexive_stalk_of_isReflexive (F.restrict W.ι) (hF W hW) ⟨x, hxW⟩)

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
