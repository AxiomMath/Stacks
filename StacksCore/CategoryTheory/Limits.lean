module

public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Fubini
import StacksCore.Tactic.StacksAttribute

/-! # Basic definitions and constructions
This file adds stacks tags to various mathlib declarations around specific limits and colimits.
-/

@[expose] public section

open CategoryTheory Limits

add_to_stacks 002E "Structure for bundled limiting cones" LimitCone
add_to_stacks 002E "uniqueness" IsLimit.uniqueUpToIso
add_to_stacks 002E "an arbitrary choice of limit, when one exists" limit

add_to_stacks 002E "Structure for bundled limiting cocones" ColimitCocone
add_to_stacks 002F "an arbitrary choice of limit, when one exists" limit
add_to_stacks 002F "uniqueness" IsColimit.uniqueUpToIso

add_to_stacks 002H "part 1" coyoneda_preservesLimits
add_to_stacks 002H "part 2" yoneda_preservesLimits

add_to_stacks 0G2U "structure for cones on a functor" Cone
add_to_stacks 0G2U "the category structure on cones" Cone.category
add_to_stacks 0G2U "cones are limiting iff they are terminal" Cone.isLimitEquivIsTerminal
add_to_stacks 0G2U "structure for cocones on a functor" Cocone
add_to_stacks 0G2U "the category structure on cocones" Cocone.category
add_to_stacks 0G2U "cocones are limiting iff they are initial" Cocone.isColimitEquivIsInitial

add_to_stacks 002K "version for `IsColimit`" IsColimit.map
add_to_stacks 002K "version for `colimit`" colimMap
add_to_stacks 002K "the resulting functor" colim

@[stacks 002K "uniqueness"]
lemma CategoryTheory.Limits.IsColimit.map_unique {J C : Type*} [Category* J] [Category* C]
    (F G : J ⥤ C) {s : Cocone F} (P : IsColimit s) (t : Cocone G) (α : F ⟶ G) {f : s.pt ⟶ t.pt}
    (hf : ∀ i, s.ι.app i ≫ f = α.app i ≫ t.ι.app i) : f = map P t α :=
  P.hom_ext fun i ↦ (hf i).trans (P.ι_map t α i).symm

add_to_stacks 002L "version for `IsLimit`" IsLimit.map
add_to_stacks 002L "version for `limit`" limMap
add_to_stacks 002L "the resulting functor" lim

@[stacks 002L "uniqueness"]
lemma CategoryTheory.Limits.IsLimit.map_unique {J C : Type*} [Category* J] [Category* C]
    (F G : J ⥤ C) (s : Cone F) {t : Cone G} (P : IsLimit t) (α : F ⟶ G) {f : s.pt ⟶ t.pt}
    (hf : ∀ i, f ≫ t.π.app i = s.π.app i ≫ α.app i) : f = map s P α :=
  P.hom_ext fun i ↦ (hf i).trans (P.map_π s α i).symm

add_to_stacks 002M "the colimit functor preserves colimits" Adjunction.colim_preservesColimits
add_to_stacks 002M "explicit isomorphism for uncurried functors" colimitIsoColimitCurryCompColim
add_to_stacks 002M "the limit functor preserves limits" Adjunction.lim_preservesLimits
add_to_stacks 002M "explicit isomorphism for uncurried functors" limitIsoLimitCurryCompLim

add_to_stacks 002N limitConeOfEqualizerAndProduct

add_to_stacks 002P colimitCoconeOfCoequalizerAndCoproduct
