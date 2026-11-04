module

public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import Mathlib.Topology.Sheaves.Functors
import StacksCore.Tactic.EgaSgaAttribute

/-! # An open continuous map as a cocontinuous functor of Zariski sites

Let `f : X ⟶ Y` be an *open* continuous map of topological spaces and give `X` and `Y` the Zariski
sites of Stacks 00VJ.  Besides the continuous functor `u : V ↦ f⁻¹(V)` of Stacks 00X2, there is now
the functor in the other direction `v : X_Zar ⥤ Y_Zar`, `U ↦ f(U)`, which is
`IsOpenMap.functor`.  Stacks 00XQ asserts that `v` is cocontinuous, so that Stacks 00XO attaches to
it a morphism of topoi `Sh(X) → Sh(Y)` given by `({}_sv, (v^p)^#)`, and that this morphism of topoi
is the one attached to `f`: `(v^p)^# = f⁻¹` and `{}_sv = f_*`.

The source proves `(v^p)^# = f⁻¹` by identifying the presheaf pullbacks `u_p = v^p`, which holds
because `(f(U), U ⊆ f⁻¹(f(U)))` is an initial object of the index category `I_U^u` of
Stacks 00VC — that initial object is exactly the unit of the adjunction `v ⊣ u`
(`IsOpenMap.adjunction`), so the identification is the general Stacks 00XX (2)
(`CategoryTheory.Functor.sheafPullbackCocontinuousIsoLan`).  The identification `{}_sv = f_*` then
follows by uniqueness of adjoints, as in the source.

## Main results

* `StacksOpenMapSite.isCocontinuous_isOpenMapFunctor`: `v = IsOpenMap.functor` is cocontinuous.
* `StacksOpenMapSite.sheafPullbackCocontinuousIsoTopPullback`: `(v^p)^# = f⁻¹`.
* `StacksOpenMapSite.sheafPushforwardCocontinuousIsoTopPushforward`: `{}_sv = f_*`.

Tags covered: 00XQ.
-/

@[expose] public section

namespace StacksOpenMapSite

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : IsOpenMap f)

/-- **Stacks 00XQ.** For an open continuous map `f : X ⟶ Y` the functor
`v : X_Zar ⥤ Y_Zar`, `U ↦ f(U)`, is cocontinuous: if `f(U) = ⋃ V j` is an open covering then
`U = ⋃ (f⁻¹(V j) ∩ U)` is an open covering refining it.

Formally, `v` is a left adjoint of the continuous functor `u = Opens.map f`
(`IsOpenMap.adjunction`), and a left adjoint is cocontinuous exactly when its right adjoint
preserves covering sieves (`Adjunction.isCocontinuous_iff_coverPreserving`). -/
@[stacks 00XQ, sga "4 III 2.5" "(ii), special case", sga "4 III 2.7" "cocontinuity of Φ"]
theorem isCocontinuous_isOpenMapFunctor :
    (IsOpenMap.functor hf).IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := by
  rw [hf.adjunction.isCocontinuous_iff_coverPreserving]
  exact CoverPreserving.of_isContinuous _ _ _

/-- **Stacks 00XQ.** The pullback `(v^p)^#` of the morphism of topoi attached to the cocontinuous
functor `v = IsOpenMap.functor` is the usual topological pullback `f⁻¹` on sheaves of sets.

By Stacks 00XX (2) the presheaf restriction along `v` is the left Kan extension along
`u = Opens.map f`, so sheafifying identifies `(v^p)^#` with the construction of `f⁻¹` as
`(u_p)^#`. -/
@[stacks 00XQ]
noncomputable def sheafPullbackCocontinuousIsoTopPullback :
    (IsOpenMap.functor hf).sheafPullbackCocontinuous (Type u) (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Y) ≅
      TopCat.Sheaf.pullback (Type u) f :=
  ((IsOpenMap.functor hf).sheafPullbackCocontinuousIsoLan (Type u)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) hf.adjunction).trans
    (Functor.sheafPullbackConstruction.sheafPullbackIso (Opens.map f) (Type u)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).symm

/-- **Stacks 00XQ.** The pushforward `{}_sv` of the morphism of topoi attached to the cocontinuous
functor `v = IsOpenMap.functor` is the usual topological pushforward `f_*` on sheaves of sets.

Both are right adjoint to `f⁻¹`: for `{}_sv` this is Stacks 00XL
(`CategoryTheory.Functor.sheafAdjunctionPullbackCocontinuous`) transported along
`sheafPullbackCocontinuousIsoTopPullback`, and for `f_*` it is
`TopCat.Sheaf.pullbackPushforwardAdjunction`. -/
@[stacks 00XQ, sga "4 III 2.7" "Φ_* ≅ (i^{-1})_s"]
noncomputable def sheafPushforwardCocontinuousIsoTopPushforward :
    haveI := isCocontinuous_isOpenMapFunctor hf
    (IsOpenMap.functor hf).sheafPushforwardCocontinuous (Type u) (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Y) ≅
      TopCat.Sheaf.pushforward (Type u) f :=
  haveI := isCocontinuous_isOpenMapFunctor hf
  Adjunction.rightAdjointUniq
    (((IsOpenMap.functor hf).sheafAdjunctionPullbackCocontinuous (Type u)
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).ofNatIsoLeft
      (sheafPullbackCocontinuousIsoTopPullback hf))
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)

end StacksOpenMapSite
