module

public import Mathlib.Topology.Sheaves.Stalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a direct image at a point where the map is locally a homeomorphism

Mathlib's `TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing` inverts the
comparison map `(f _* F).stalk (f x) ⟶ F.stalk x` under a hypothesis on **all** of `f`: that
`f` is inducing. The hypothesis it really uses is local at the single point `x`, namely that
the preimages of the open neighbourhoods of `f x` are cofinal among the open neighbourhoods of
`x`, and that is what this file isolates.

The cofinality is packaged as the initiality of `TopologicalSpace.OpenNhds.map f x`, obtained
from a right adjoint to it: the preimage map `Opens Y → Opens X` always has the right adjoint
`W ↦ ⨆ {V | f ⁻¹ V ≤ W}`, because preimage commutes with unions; the one thing to check is that
the supremum contains `f x`, and that is exactly the hypothesis.

## Main results

* `TopCat.Presheaf.openNhdsMapRightAdjoint`: the right adjoint of
  `TopologicalSpace.OpenNhds.map f x`, for a point `x` at which the preimages are cofinal.
* `TopCat.Presheaf.initial_openNhds_map`: hence `TopologicalSpace.OpenNhds.map f x` is initial.
* `TopCat.Presheaf.isIso_stalkPushforward_of_exists_preimage_le`: hence the comparison map on
  stalks at `x` is an isomorphism.

## Implementation notes

The hypothesis is stated as "for every open `W` containing `x` there is an open `V` containing
`f x` with `f ⁻¹ V ≤ W`" rather than as a property of `f`, so that it can be verified at one
point of one map. For an inducing `f` it holds at every point, so this subsumes
`TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`; the application it is
written for is a morphism which is **not** inducing globally but is an isomorphism above an
open neighbourhood of the image of `x`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open TopologicalSpace Opposite

universe v u

variable {C : Type u} [Category.{v} C] [HasColimits.{v} C]
variable {X Y : TopCat.{v}}

namespace TopCat.Presheaf

/-- The largest open of `Y` whose preimage is contained in a given open `W` of `X`: the
supremum of all the opens with that property, which still has the property because taking
preimages commutes with unions. -/
def preimageLeSup (f : X ⟶ Y) (W : Opens X) : Opens Y :=
  sSup {V : Opens Y | (Opens.map f).obj V ≤ W}

/-- The preimage of `preimageLeSup f W` is contained in `W`. -/
theorem preimage_preimageLeSup_le (f : X ⟶ Y) (W : Opens X) :
    (Opens.map f).obj (preimageLeSup f W) ≤ W := by
  intro a ha
  obtain ⟨V, hV, haV⟩ := Opens.mem_sSup.1 ha
  exact hV haV

/-- Every open of `Y` whose preimage is contained in `W` is contained in `preimageLeSup f W`. -/
theorem le_preimageLeSup (f : X ⟶ Y) {V : Opens Y} {W : Opens X}
    (h : (Opens.map f).obj V ≤ W) : V ≤ preimageLeSup f W :=
  le_sSup h

/-- `preimageLeSup f` is monotone in the open `W` of `X`. -/
theorem preimageLeSup_mono (f : X ⟶ Y) {W W' : Opens X} (h : W ≤ W') :
    preimageLeSup f W ≤ preimageLeSup f W' :=
  sSup_le_sSup fun _ hV => hV.trans h

/-- The right adjoint of the preimage functor `TopologicalSpace.OpenNhds.map f x`, available at
a point `x` for which the preimages of the open neighbourhoods of `f x` are cofinal among the
open neighbourhoods of `x`. -/
def openNhdsMapRightAdjoint (f : X ⟶ Y) (x : X)
    (h : ∀ W : Opens X, x ∈ W → ∃ V : Opens Y, f x ∈ V ∧ (Opens.map f).obj V ≤ W) :
    OpenNhds x ⥤ OpenNhds (f x) where
  obj W := ⟨preimageLeSup f W.1, by
    obtain ⟨V, hV, hVW⟩ := h W.1 W.2
    exact le_preimageLeSup f hVW hV⟩
  map {W W'} i := homOfLE (preimageLeSup_mono f (leOfHom i))

/-- `TopologicalSpace.OpenNhds.map f x` is a left adjoint, hence initial: the preimages of the
open neighbourhoods of `f x` are cofinal among the open neighbourhoods of `x`. -/
def openNhdsMapAdjunction (f : X ⟶ Y) (x : X)
    (h : ∀ W : Opens X, x ∈ W → ∃ V : Opens Y, f x ∈ V ∧ (Opens.map f).obj V ≤ W) :
    OpenNhds.map f x ⊣ openNhdsMapRightAdjoint f x h where
  unit := { app := fun V => homOfLE (le_preimageLeSup f le_rfl) }
  counit := { app := fun W => homOfLE (preimage_preimageLeSup_le f W.1) }

/-- If every open neighbourhood of `x` contains the preimage of an open neighbourhood of `f x`,
then `TopologicalSpace.OpenNhds.map f x` is initial. -/
theorem initial_openNhds_map (f : X ⟶ Y) (x : X)
    (h : ∀ W : Opens X, x ∈ W → ∃ V : Opens Y, f x ∈ V ∧ (Opens.map f).obj V ≤ W) :
    (OpenNhds.map f x).Initial :=
  initial_of_adjunction (openNhdsMapAdjunction f x h)

/-- **The stalk of a direct image at a point where the preimages are cofinal.** If every open
neighbourhood of `x` contains the preimage of an open neighbourhood of `f x`, then the
comparison map `(f _* F).stalk (f x) ⟶ F.stalk x` is an isomorphism, for every presheaf `F`.

This is `TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing` with its
hypothesis localised at `x`: the proof is the same, the initiality of
`TopologicalSpace.OpenNhds.map f x` coming from `TopCat.Presheaf.openNhdsMapAdjunction` instead
of from `Topology.IsInducing.adjunctionNhds`. -/
@[ega "0 3.4.5" "more general"]
theorem isIso_stalkPushforward_of_exists_preimage_le (f : X ⟶ Y) (F : X.Presheaf C) (x : X)
    (h : ∀ W : Opens X, x ∈ W → ∃ V : Opens Y, f x ∈ V ∧ (Opens.map f).obj V ≤ W) :
    IsIso (F.stalkPushforward C f x) := by
  have := initial_openNhds_map f x h
  convert!
    (Functor.Final.colimitIso (OpenNhds.map f x).op ((OpenNhds.inclusion x).op ⋙ F)).isIso_hom
  refine stalk_hom_ext _ fun U hU ↦ (stalkPushforward_germ _ f F _ x hU).trans ?_
  symm
  exact colimit.ι_pre ((OpenNhds.inclusion x).op ⋙ F) (OpenNhds.map f x).op _

end TopCat.Presheaf

end
