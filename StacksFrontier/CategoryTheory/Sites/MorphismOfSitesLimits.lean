module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Criteria for a continuous functor to define a morphism of sites

A continuous functor `u : C ⥤ D` defines a morphism of sites `f : D → C` as soon as the pullback
`u_s = f⁻¹` on sheaves of sets is left exact (`Functor.isMorphismOfSites_iff_preservesFiniteLimits`
in `StacksFrontier.CategoryTheory.Sites.MorphismOfSites`). This file proves two standard
sufficient conditions for that.

## Main results

* `Functor.isMorphismOfSites_of_isFiltered_op` (Stacks Tag 00X5): it suffices that all the
  opposites `(I_V^u)ᵒᵖ` of the index categories of Stacks 00VC be filtered. Stacks' `I_V^u` is
  the comma category `StructuredArrow V u`, so this hypothesis is exactly Mathlib's
  `RepresentablyFlat u` (`Functor.representablyFlat_iff_isFiltered_op`).

* `Functor.isMorphismOfSites_of_isTerminal` (Stacks Tag 00X6): it suffices that `C` have a final
  object whose image under `u` is final in `D`, and that `C` have fibre products which `u`
  preserves.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

section GeneralUniverses

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The index categories `I_V^u` of Stacks 00VC are the comma categories `StructuredArrow V u`, so
Stacks' hypothesis that every `(I_V^u)ᵒᵖ` is filtered is exactly Mathlib's `RepresentablyFlat u`.
-/
theorem representablyFlat_iff_isFiltered_op (u : C ⥤ D) :
    RepresentablyFlat u ↔ ∀ V : D, IsFiltered (StructuredArrow V u)ᵒᵖ :=
  ⟨fun _ V => (isFiltered_op_iff_isCofiltered (StructuredArrow V u)).mpr inferInstance,
    fun h => ⟨fun V => (isFiltered_op_iff_isCofiltered (StructuredArrow V u)).mp (h V)⟩⟩

/-- A functor sending some final object of `C` to a final object of `D` preserves terminal objects.
-/
theorem preservesLimitsOfShape_pempty_of_isTerminal (u : C ⥤ D) {X : C} (hX : IsTerminal X)
    (huX : IsTerminal (u.obj X)) : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
  have : PreservesLimit (Functor.empty.{0} C) u :=
    preservesLimit_of_preserves_limit_cone hX ((isLimitMapConeEmptyConeEquiv u X).symm huX)
  preservesLimitsOfShape_pempty_of_preservesTerminal u

end GeneralUniverses

universe u

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/-- For a continuous representably flat `u`, the pullback `u_s` on sheaves of sets is left exact.
-/
theorem preservesFiniteLimits_sheafPullback (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] [RepresentablyFlat u] :
    PreservesFiniteLimits (u.sheafPullback (Type u) J K) :=
  sheafPullbackConstruction.preservesFiniteLimits u (Type u) J K

/-- A continuous representably flat functor defines a morphism of sites. -/
theorem isMorphismOfSites_of_representablyFlat (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] [RepresentablyFlat u] :
    u.IsMorphismOfSites J K :=
  (isMorphismOfSites_iff_preservesFiniteLimits u J K).mpr
    (preservesFiniteLimits_sheafPullback u J K)

/-- Let `u : C ⥤ D` be a continuous functor between sites and assume that all the
categories `(I_V^u)ᵒᵖ` of Stacks 00VC are filtered. Then `u` defines a morphism of sites `D → C`,
in other words `u_s` is exact. -/
@[stacks 00X5 "A continuous functor all of whose index categories `(I_V^u)ᵒᵖ` are filtered defines
  a morphism of sites; equivalently a continuous representably flat functor does."]
theorem isMorphismOfSites_of_isFiltered_op (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K]
    (h : ∀ V : D, IsFiltered (StructuredArrow V u)ᵒᵖ) : u.IsMorphismOfSites J K :=
  have := (representablyFlat_iff_isFiltered_op u).mpr h
  isMorphismOfSites_of_representablyFlat u J K

/-- A continuous left exact functor out of a finitely complete site defines a morphism of sites.
-/
@[sga "4 IV 4.1.1" "more general", sga "4 IV 4.9.2", sga "4 VI 7.2.4" "special case"]
theorem isMorphismOfSites_of_preservesFiniteLimits (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] [HasFiniteLimits C]
    [PreservesFiniteLimits u] : u.IsMorphismOfSites J K :=
  have := flat_of_preservesFiniteLimits u
  isMorphismOfSites_of_representablyFlat u J K

/-- Let `u : C ⥤ D` be a continuous functor between sites. Assume furthermore that

1. the category `C` has a final object `X` and `u(X)` is a final object of `D`, and
2. the category `C` has fibre products and `u` commutes with them.

Then `u` defines a morphism of sites `D → C`, in other words `u_s` is exact. -/
@[stacks 00X6 "A continuous functor `u` such that `C` has a final object sent by `u` to a final
  object and has fibre products preserved by `u` defines a morphism of sites; this is the criterion
  under which `u` induces a morphism of topoi with exact pullback.",
  sga "4 IV 4.9.2" "sufficient condition", sga "4 III 1.3" "5)"]
theorem isMorphismOfSites_of_isTerminal (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan u] {X : C} (hX : IsTerminal X)
    (huX : IsTerminal (u.obj X)) : u.IsMorphismOfSites J K :=
  have := hX.hasTerminal
  have := preservesLimitsOfShape_pempty_of_isTerminal u hX huX
  have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits u := preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  isMorphismOfSites_of_preservesFiniteLimits u J K

end CategoryTheory.Functor
