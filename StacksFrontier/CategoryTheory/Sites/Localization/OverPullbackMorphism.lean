module

public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relocalization along a morphism of a site with fibre products

Let `(C, J)` be a site with fibre products and let `f : U ⟶ V` be a morphism of `C`. The
relocalization functor `j = j_{U/V} : C/U ⥤ C/V` is `Over.map f`. It has a continuous right
adjoint `v : X/V ↦ X ×_V U / U`, `v` defines a morphism of sites `C/U → C/V` whose associated
morphism of topoi is the one induced by `j`, and consequently `j_*F(X/V) = F(X ×_V U / U)`.

## Main results

* `StacksRelocalization.isMorphismOfSites_overPullback`: `v = Over.pullback f` defines a morphism
  of sites `C/U → C/V`.
* `StacksRelocalization.sheafPushforwardOverMapIso`,
  `StacksRelocalization.sheafPullbackOverPullbackIso`: the morphism of topoi attached to `v` is the
  one attached to `j`.
* `StacksRelocalization.sheafPushforwardObjEquiv`: `j_*F(X/V) = F(X ×_V U / U)`.

## References

* [Stacks Project, Tag 09W9](https://stacks.math.columbia.edu/tag/09W9)
-/

@[expose] public section

namespace StacksRelocalization

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (J : GrothendieckTopology C)
  {U V : C} (f : U ⟶ V)

/-- The functor `v = Over.pullback f : C/V ⥤ C/U`, given on objects by `X/V ↦ X ×_V U / U`,
defines a morphism of sites `C/U → C/V`: it is continuous, and the induced pullback on sheaves of
sets is exact. -/
@[stacks 09W9, sga "4 IV 5.5" "loc(f) (5.5.2)"]
theorem isMorphismOfSites_overPullback :
    (Over.pullback f).IsMorphismOfSites (J.over V) (J.over U) :=
  Functor.isMorphismOfSites_of_representablyFlat (Over.pullback f) (J.over V) (J.over U)

/-- The pushforward `j_*` of the morphism of topoi attached to the continuous and cocontinuous
functor `j = Over.map f` agrees with the pushforward `v^s` of the morphism of sites given by
`v = Over.pullback f`; that is, the two morphisms of topoi coincide. -/
@[stacks 09W9]
noncomputable def sheafPushforwardOverMapIso :
    (Over.map f).sheafPushforwardCocontinuous (Type u) (J.over U) (J.over V) ≅
      (Over.pullback f).sheafPushforwardContinuous (Type u) (J.over V) (J.over U) :=
  (Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso (Type u)

/-- The pullback `v_s = f⁻¹` of the morphism of sites given by `v = Over.pullback f` is the
restriction functor `j⁻¹` along `j = Over.map f`. -/
@[stacks 09W9, sga "4 IV 5.5" "f^* = restriction"]
noncomputable def sheafPullbackOverPullbackIso :
    (Over.pullback f).sheafPullback (Type u) (J.over V) (J.over U) ≅
      (Over.map f).sheafPushforwardContinuous (Type u) (J.over U) (J.over V) :=
  (Over.mapPullbackAdj f).sheafPullbackIso (Type u)

/-- For a sheaf `F` on `C/U` the sections of `j_*F` over an object `X/V` of `C/V` are the sections
of `F` over `X ×_V U / U`. -/
@[stacks 09W9, sga "4 IV 5.5" "f_* formula (5.5.3)"]
noncomputable def sheafPushforwardObjEquiv (F : Sheaf (J.over U) (Type u)) (X : Over V) :
    (((Over.map f).sheafPushforwardCocontinuous (Type u) (J.over U) (J.over V)).obj F).obj.obj
        (op X) ≃
      F.obj.obj (op ((Over.pullback f).obj X)) :=
  (((sheafToPresheaf (J.over V) (Type u)).mapIso
    ((sheafPushforwardOverMapIso J f).app F)).app (op X)).toEquiv

end StacksRelocalization
