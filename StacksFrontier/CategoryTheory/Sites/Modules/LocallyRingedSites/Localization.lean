module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Defs
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
import StacksCore.Tactic.StacksAttribute

/-!
# The localization of a locally ringed site is locally ringed

Let `(C, O)` be a locally ringed site and `U` an object of `C`. Stacks 04IX localizes it to the
ringed site `(C/U, O|_U)`, and this file proves that the localization is again locally ringed.

Both conjuncts of `AlgebraicGeometry.RingedSite.IsLocallyRinged` transport, for different
reasons. The local-unit condition is a statement about sections, and the sections of `O|_U` over
`V ⟶ U` are the sections of `O` over `V`, so a covering of `V` witnessing the condition for `O`
pulls back to a covering of `V ⟶ U` in the localized topology — that is
`Sieve.overEquiv`. Nonvanishing of `1` is a categorical statement, that the canonical map from
the initial sheaf to the equalizer of the zero and one sections is an isomorphism; restriction
along `Over.forget U` preserves that equalizer, being a right adjoint, and it also preserves the
initial object, so the map transports.

## Main results

* `AlgebraicGeometry.RingedSite.locallyEitherUnit_over`: the local-unit condition passes to the
  restricted structure sheaf.
* `AlgebraicGeometry.RingedSite.isIso_oneIsNeverZero_over`: nonvanishing of `1` passes to the
  localization.
* `AlgebraicGeometry.RingedSite.isLocallyRinged_over`: **Stacks 04IH (1), first assertion**, the
  localization of a locally ringed site is locally ringed.

## Implementation notes

That `AlgebraicGeometry.RingedSite.over` is written `X.over U` and its structure sheaf is
`X.O.over U` on the nose (`AlgebraicGeometry.RingedSite.over_O`) is what makes the sections
argument a matter of transporting a sieve: no comparison map intervenes.

**A duplicated private helper.** Preservation of the initial object by restriction does not come
from an adjunction without a size hypothesis: `overPullback` is
`(Over.forget U).sheafPushforwardContinuous`, which is a *right* adjoint by
`Functor.sheafAdjunctionContinuous` — good for the equalizer, useless for the initial object —
and making it a left adjoint via `Functor.sheafAdjunctionCocontinuous` requires
`HasPointwiseRightKanExtension`, which relates the universe of the sections to that of the site
and is not available here. So initiality is established by hand, from the explicit initial sheaf
whose sections over an object are the proofs that the empty sieve covers it. That sheaf and its
initiality are `CategoryTheory.emptySheaf` and `CategoryTheory.emptySheafIsInitial` of
`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/Defs.lean`, and are used from
there directly.

## References

* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

attribute [local instance] CategoryTheory.hasInitialSheafOfTypes

namespace AlgebraicGeometry.RingedSite

section EmptySheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Restriction along `Over.forget U` carries the explicit initial sheaf to an initial sheaf:
an object `V ⟶ U` of the localized site is covered by the empty sieve exactly when `V` is. -/
private noncomputable def overPullbackEmptyTypeSheafIsInitial (U : C) :
    IsInitial ((J.overPullback (Type w) U).obj (CategoryTheory.emptySheaf J)) := by
  classical
  have h (G : Sheaf (J.over U) (Type w)) (V : Over U) (x : (⊥ : Sieve V.left) ∈ J V.left) :
      Unique (G.obj.obj (op V)) :=
    Types.isTerminalEquivUnique _ (G.isTerminalOfBotCover V (by
      rw [GrothendieckTopology.mem_over_iff]
      simpa using x))
  refine IsInitial.ofUniqueHom (fun G => ⟨{
    app := fun V : (Over U)ᵒᵖ => TypeCat.ofHom (fun x => ?_)
    naturality := ?_ }⟩) ?_
  · exact (h G V.unop x.down.down).default
  · intro V W f
    ext x
    have := h G W.unop (by simpa using J.pullback_stable f.unop.left x.down.down)
    exact Subsingleton.elim _ _
  · intro G f
    ext V x
    have := h G V.unop x.down.down
    exact Subsingleton.elim _ _

/-- Restriction along `Over.forget U` preserves the initial sheaf of sets. -/
private noncomputable def overPullbackInitialIso (U : C) :
    (J.overPullback (Type w) U).obj (⊥_ (Sheaf J (Type w))) ≅
      ⊥_ (Sheaf (J.over U) (Type w)) :=
  (J.overPullback (Type w) U).mapIso
      (initialIsInitial.uniqueUpToIso (CategoryTheory.emptySheafIsInitial J)) ≪≫
    (overPullbackEmptyTypeSheafIsInitial J U).uniqueUpToIso initialIsInitial

end EmptySheaf

/-- The local-unit condition passes to the restriction of the structure sheaf: a covering of `V`
witnessing it for `O` becomes, under `Sieve.overEquiv`, a covering of `V ⟶ U` in the localized
topology, and the sections involved are literally the same. -/
theorem locallyEitherUnit_over {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{w}) (U : C) (hO : LocallyEitherUnit O) :
    LocallyEitherUnit (O.over U) := by
  intro V f
  change O.obj.obj (op V.left) at f
  obtain ⟨S, hS, hP⟩ := hO V.left f
  refine ⟨(Sieve.overEquiv V).symm S, ?_, ?_⟩
  · rw [GrothendieckTopology.mem_over_iff]
    simpa using hS
  · intro W g hg
    change IsUnit (O.obj.map g.left.op f) ∨ IsUnit (O.obj.map g.left.op (1 - f))
    exact hP g.left (by simpa using hg)

/-- Nonvanishing of `1` passes to the localization: restriction along `Over.forget U` preserves
both the initial sheaf and the equalizer of the zero and one sections, and carries the one
canonical map to the other. -/
theorem isIso_oneIsNeverZero_over (X : RingedSite.{u, v, w}) (U : X.C)
    (hX : IsIso (oneIsNeverZero X)) :
    IsIso (oneIsNeverZero (X.over U)) := by
  let F := X.J.overPullback (Type w) U
  have h0 : F.map (zeroSection X) = zeroSection (X.over U) := by ext V x; rfl
  have h1 : F.map (oneSection X) = oneSection (X.over U) := by ext V x; rfl
  have hEq : equalizer (F.map (zeroSection X)) (F.map (oneSection X)) =
      equalizer (zeroSection (X.over U)) (oneSection (X.over U)) := by rw [h0, h1]; rfl
  let ieq := PreservesEqualizer.iso F (zeroSection X) (oneSection X) ≪≫ eqToIso hEq
  have : IsIso (oneIsNeverZero X) := hX
  have hc : (overPullbackInitialIso X.J U).inv ≫ F.map (oneIsNeverZero X) ≫ ieq.hom =
      oneIsNeverZero (X.over U) := initialIsInitial.hom_ext _ _
  rw [← hc]
  infer_instance

/-- **Stacks 04IH (1), first assertion.** A localization `(C/U, O_U)` of a locally ringed site
is again a locally ringed site. -/
@[stacks 04IH "(1), first assertion: the localization `(C/U, O_U)` of a locally ringed site is
again a locally ringed site"]
theorem isLocallyRinged_over (X : RingedSite.{u, v, w}) (U : X.C)
    (hX : IsLocallyRinged X) : IsLocallyRinged (X.over U) :=
  ⟨isIso_oneIsNeverZero_over X U hX.1, locallyEitherUnit_over X.O U hX.2⟩

end AlgebraicGeometry.RingedSite
