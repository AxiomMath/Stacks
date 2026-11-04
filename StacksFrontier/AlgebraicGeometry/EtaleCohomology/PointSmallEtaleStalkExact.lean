module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of the étale stalk functors at a geometric point

Let `s : Spec Ω ⟶ S` be a geometric point of a scheme `S`, with `Ω` a separably closed field, and
let `pointSmallEtale s` be the corresponding point of the small étale site of `S`. Its fibre
functors `presheafFiber` and `sheafFiber` are the stalk functors `𝓕 ↦ 𝓕_s̄` on presheaves and on
sheaves. This file records that these stalk functors are exact and commute with colimits, and that
the stalk of a presheaf of sets is the stalk of its sheafification.

## Main results

* `AlgebraicGeometry.Scheme.pointSmallEtale_presheafFiber_ab_exact` — the stalk functor on abelian
  presheaves is exact.
* `AlgebraicGeometry.Scheme.isIso_pointSmallEtale_presheafFiber_map_toSheafify` and
  `AlgebraicGeometry.Scheme.isIso_pointSmallEtale_presheafFiber_map_toSheafify'` — the canonical
  map from the stalk of a presheaf of sets to the stalk of its sheafification is an isomorphism.
* `AlgebraicGeometry.Scheme.pointSmallEtale_sheafFiber_ab_exact` — the stalk functor on abelian
  sheaves is exact.
* `AlgebraicGeometry.Scheme.pointSmallEtale_presheafFiber_type_exact` and
  `AlgebraicGeometry.Scheme.pointSmallEtale_sheafFiber_type_exact` — the stalk functors on
  presheaves and on sheaves of sets are exact and commute with arbitrary colimits.

## Implementation notes

The points of the small étale site of `S : Scheme.{u}` have fibres in `Type u`, so the stalk is a
colimit over a `u`-small filtered category; it is defined for coefficients in any universe
`max u v`. Exactness is meant in the sense of Stacks, Tag 0034: commuting with finite limits and
finite colimits. Commuting with arbitrary colimits is stated for colimits of every size, using
that the stalk functors are left adjoint to the skyscraper functors. Sheafification of presheaves
of sets on the small étale site is available in Mathlib for `Type u` and for
`Type (max (u + 1) v)`, and part (2) is stated for both.

## References

* [Stacks Project, Tag 03PT](https://stacks.math.columbia.edu/tag/03PT)
-/

@[expose] public section

universe w₁ w₂ v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- A left adjoint preserves finite colimits. -/
private theorem preservesFiniteColimits_of_adjunction {C A : Type*} [Category C] [Category A]
    {F : C ⥤ A} {G : A ⥤ C} (adj : F ⊣ G) : PreservesFiniteColimits F :=
  have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **The stalk functor on abelian presheaves is exact.** For a geometric point `s` of `S`, the
stalk functor `PAb(S_et) ⥤ Ab`, `𝓕 ↦ 𝓕_s̄`, commutes with finite limits and finite colimits. -/
@[stacks 03PT "(1) the stalk functor on abelian presheaves is exact"]
theorem pointSmallEtale_presheafFiber_ab_exact :
    PreservesFiniteLimits ((pointSmallEtale s).presheafFiber (A := AddCommGrpCat.{max u v})) ∧
      PreservesFiniteColimits
        ((pointSmallEtale s).presheafFiber (A := AddCommGrpCat.{max u v})) := by
  have := AB5OfSize_shrink.{u, u, v, v} AddCommGrpCat.{max u v}
  exact ⟨inferInstance, preservesFiniteColimits_of_adjunction
    (pointSmallEtale s).skyscraperPresheafAdjunction⟩

/-- **Stalks of a presheaf of sets and of its sheafification agree.** For a geometric point `s` of
`S` and a presheaf of sets `𝓕` on `S_et`, the map `𝓕_s̄ ⟶ (𝓕^#)_s̄` induced by `𝓕 ⟶ 𝓕^#` is an
isomorphism. -/
@[stacks 03PT "(2) the stalk of a presheaf of sets equals the stalk of its sheafification"]
theorem isIso_pointSmallEtale_presheafFiber_map_toSheafify
    (F : S.Etaleᵒᵖ ⥤ Type u) :
    IsIso ((pointSmallEtale s).presheafFiber.map (toSheafify (smallEtaleTopology S) F)) :=
  inferInstance

/-- **Stalks of a presheaf of sets and of its sheafification agree**, for presheaves of sets in
`Type (max (u + 1) v)`. For a geometric point `s` of `S` and a presheaf of sets `𝓕` on `S_et`, the
map `𝓕_s̄ ⟶ (𝓕^#)_s̄` induced by `𝓕 ⟶ 𝓕^#` is an isomorphism. -/
@[stacks 03PT "(2) the stalk of a presheaf of sets equals the stalk of its sheafification"]
theorem isIso_pointSmallEtale_presheafFiber_map_toSheafify'
    (F : S.Etaleᵒᵖ ⥤ Type (max (u + 1) v)) :
    IsIso ((pointSmallEtale s).presheafFiber.map (toSheafify (smallEtaleTopology S) F)) :=
  inferInstance

/-- **The stalk functor on abelian sheaves is exact.** For a geometric point `s` of `S`, the stalk
functor `Ab(S_et) ⥤ Ab`, `𝓕 ↦ 𝓕_s̄`, commutes with finite limits and finite colimits. -/
@[stacks 03PT "(3) the stalk functor on abelian sheaves is exact"]
theorem pointSmallEtale_sheafFiber_ab_exact :
    PreservesFiniteLimits ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{max u v})) ∧
      PreservesFiniteColimits ((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{max u v})) := by
  have := AB5OfSize_shrink.{u, u, v, v} AddCommGrpCat.{max u v}
  exact ⟨inferInstance, preservesFiniteColimits_of_adjunction
    (pointSmallEtale s).skyscraperSheafAdjunction⟩

/-- **The stalk functor on presheaves of sets is exact and commutes with colimits.** For a
geometric point `s` of `S`, the stalk functor `PSh(S_et) ⥤ Sets`, `𝓕 ↦ 𝓕_s̄`, commutes with
finite limits, with finite colimits, and with colimits of any size. -/
@[stacks 03PT "(4) the stalk functor on presheaves of sets is exact and commutes with colimits"]
theorem pointSmallEtale_presheafFiber_type_exact :
    PreservesFiniteLimits ((pointSmallEtale s).presheafFiber (A := Type (max u v))) ∧
      PreservesFiniteColimits ((pointSmallEtale s).presheafFiber (A := Type (max u v))) ∧
      PreservesColimitsOfSize.{w₁, w₂}
        ((pointSmallEtale s).presheafFiber (A := Type (max u v))) := by
  have := AB5OfSize_shrink.{u, u, v, v} (Type (max u v))
  have hadj := (pointSmallEtale s).skyscraperPresheafAdjunction (A := Type (max u v))
  exact ⟨inferInstance, preservesFiniteColimits_of_adjunction hadj,
    hadj.leftAdjoint_preservesColimits⟩

/-- **The stalk functor on sheaves of sets is exact and commutes with colimits.** For a geometric
point `s` of `S`, the stalk functor `Sh(S_et) ⥤ Sets`, `𝓕 ↦ 𝓕_s̄`, commutes with finite limits,
with finite colimits, and with colimits of any size. -/
@[stacks 03PT "(4) the stalk functor on sheaves of sets is exact and commutes with colimits"]
theorem pointSmallEtale_sheafFiber_type_exact :
    PreservesFiniteLimits ((pointSmallEtale s).sheafFiber (A := Type (max u v))) ∧
      PreservesFiniteColimits ((pointSmallEtale s).sheafFiber (A := Type (max u v))) ∧
      PreservesColimitsOfSize.{w₁, w₂}
        ((pointSmallEtale s).sheafFiber (A := Type (max u v))) := by
  have := AB5OfSize_shrink.{u, u, v, v} (Type (max u v))
  have hadj := (pointSmallEtale s).skyscraperSheafAdjunction (A := Type (max u v))
  exact ⟨inferInstance, preservesFiniteColimits_of_adjunction hadj,
    hadj.leftAdjoint_preservesColimits⟩

end AlgebraicGeometry.Scheme
