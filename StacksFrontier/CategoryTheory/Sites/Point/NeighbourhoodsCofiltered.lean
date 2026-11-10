module

public import Mathlib.CategoryTheory.Sites.LocalSite
public import StacksFrontier.CategoryTheory.Sites.Point.StalkLeftAdjoint
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Neighbourhoods of a point are cofiltered, and its stalk functor is left exact

Stacks tag 00YB. Let `C` be a site with a final object `X` and all fibred products, and
let `p = u : C ⥤ Sets` be a covariant functor such that `u(X)` is a singleton and, for
every `f : U ⟶ W` and `g : V ⟶ W`, the canonical comparison map
`u(U ×_W V) ⟶ u(U) ×_{u(W)} u(V)` is bijective — the hypotheses packaged as `IsPoint`.

The category of neighbourhoods `Nbh(p)`, whose objects are the pairs `(U, x)` with
`x ∈ u(U)` and whose morphisms `(V, y) ⟶ (U, x)` are the `α : V ⟶ U` with `u(α)(y) = x`
(Mathlib's category of elements `u.Elements`), is then cofiltered. Consequently the stalk
functor at `p`, sending a sheaf of sets `F` to `F_p = colim_{(U,x) ∈ Nbh(p)ᵒᵖ} F(U)`
(Section 7.32, tag 00Y3), commutes with finite limits: filtered colimits of sets are left
exact.
-/

@[expose] public section

open CategoryTheory CategoryOfElements Limits

universe w

namespace StacksStalk

-- We work with a small site `C : Type w` with `Sets = Type w`.
variable {C : Type w} [SmallCategory C]

/-! ## The category of neighbourhoods -/

-- The category of neighbourhoods `Nbh(p)` of `p = u` is Mathlib's category of elements
-- `u.Elements`: objects are pairs `(U, x)` with `x ∈ u(U)`, and a morphism `(V, y) ⟶ (U, x)` is a
-- map `α : V ⟶ U` of `C` with `u(α)(y) = x`.  The stalk functor it computes is
-- `CategoryTheory.elementColimit u (Type w)`, equivalently Mathlib's
-- `CategoryTheory.GrothendieckTopology.Point.presheafFiber`; neither is restated here.

/-- A morphism `α : a.1 ⟶ b.1` of `C` underlies a morphism `a ⟶ b` of `u.Elements` exactly when
`u(α)(a.2) = b.2`. -/
theorem elements_hom_iff (u : C ⥤ Type w) (a b : u.Elements) (f : a.1 ⟶ b.1) :
    (∃ g : a ⟶ b, g.1 = f) ↔ u.map f a.2 = b.2 := by
  refine ⟨?_, fun h => ⟨⟨f, h⟩, rfl⟩⟩
  rintro ⟨g, rfl⟩
  exact g.2

/-! ## Hypotheses on the point `p = u` -/

/-- The hypotheses on `p = u` from the Main Statement: `u(X)` is a singleton (for
`X` the terminal object) and `u` sends every pullback comparison map to a
bijection. Here `pullbackComparison u f g` is precisely the canonical map
`u(U ×_W V) ⟶ u(U) ×_{u(W)} u(V)`. -/
structure IsPoint [HasTerminal C] [HasPullbacks C] (u : C ⥤ Type w) : Prop where
  /-- `u(X)` is a singleton: it is a subsingleton and nonempty. -/
  terminal_singleton : Subsingleton (u.obj (⊤_ C)) ∧ Nonempty (u.obj (⊤_ C))
  /-- For all `f : U ⟶ W`, `g : V ⟶ W`, the canonical comparison map
  `u(U ×_W V) ⟶ u(U) ×_{u(W)} u(V)` is bijective. -/
  pullback_bijective : ∀ {U V W : C} (f : U ⟶ W) (g : V ⟶ W),
    Function.Bijective (pullbackComparison u f g)

/-! ## Main Statement(s) -/

/-- Statement 1 (Main, tag `00YB`): under the hypotheses, the category of
neighbourhoods `Nbh(p)` of `p` is cofiltered. -/
@[stacks 00YB "(1)", sga "4 IV 6.8.2" "special case", sga "4 IV 6.8.5" "partial"]
theorem nbh_isCofiltered [HasTerminal C] [HasPullbacks C]
    (u : C ⥤ Type w) (hu : IsPoint u) : IsCofiltered u.Elements := by
  -- `u` preserves finite limits: it preserves the terminal object (as `u(X)` is a
  -- singleton) and all pullbacks (as the comparison maps are bijective, hence iso).
  obtain ⟨⟨hs, hn⟩, hpb⟩ := hu
  -- preserves the terminal object.
  have hT : IsTerminal (u.obj (⊤_ C)) := by
    have : Unique (u.obj (⊤_ C)) := ⟨⟨hn.some⟩, fun a => hs.elim a hn.some⟩
    exact (Limits.Types.isTerminalEquivUnique _).symm inferInstance
  have hpe : PreservesLimit (Functor.empty.{0} C) u :=
    preservesTerminal_of_iso u (hT.uniqueUpToIso terminalIsTerminal)
  have hterm : PreservesLimitsOfShape (Discrete PEmpty.{1}) u :=
    preservesLimitsOfShape_pempty_of_preservesTerminal u
  -- preserves pullbacks.
  have hpull : PreservesLimitsOfShape WalkingCospan u := by
    refine ⟨fun {K} => ?_⟩
    have : IsIso (pullbackComparison u (K.map WalkingCospan.Hom.inl)
        (K.map WalkingCospan.Hom.inr)) :=
      (isIso_iff_bijective _).mpr (hpb _ _)
    have : PreservesLimit (cospan (K.map WalkingCospan.Hom.inl)
        (K.map WalkingCospan.Hom.inr)) u := PreservesPullback.of_iso_comparison u
    exact preservesLimit_of_iso_diagram u (diagramIsoCospan K).symm
  have : PreservesFiniteLimits u :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks u
  have : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
  -- A finite-limit-preserving functor out of a category with finite limits is flat,
  -- so its categories of structured arrows are cofiltered.
  have : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  have : IsCofiltered (StructuredArrow PUnit.{w + 1} u) := RepresentablyFlat.cofiltered _
  -- transport cofilteredness along `u.Elements ≌ StructuredArrow PUnit u`.
  exact (IsCofiltered.iff_of_equivalence
    (Functor.Elements.structuredArrowEquivalence u)).mpr inferInstance

/-- Statement 2 (Consequence, tag `00YB`): under the hypotheses, the stalk
functor on sheaves commutes with finite limits, i.e. it is left exact. -/
@[stacks 00YB "(2)"]
theorem sheafStalkFunctor_preservesFiniteLimits
    [HasTerminal C] [HasPullbacks C] (J : GrothendieckTopology C)
    (u : C ⥤ Type w) (hu : IsPoint u) :
    PreservesFiniteLimits
      (sheafToPresheaf J (Type w) ⋙ CategoryTheory.elementColimit u (Type w)) := by
  -- `Nbh u` is cofiltered, hence `(Nbh u)ᵒᵖ` is filtered.
  have : IsCofiltered u.Elements := nbh_isCofiltered u hu
  -- `colim` over the filtered category `u.Elementsᵒᵖ` preserves finite limits in `Type`.
  have : PreservesFiniteLimits (colim : ((u.Elements)ᵒᵖ ⥤ Type w) ⥤ Type w) :=
    filtered_colim_preservesFiniteLimits_of_types
  -- Restriction along `(CategoryOfElements.π u).op` preserves finite limits (pointwise limits).
  have : PreservesFiniteLimits
      ((Functor.whiskeringLeft u.Elementsᵒᵖ Cᵒᵖ (Type w)).obj (Functor.Elements.π u).op) :=
    inferInstance
  -- Hence the stalk functor on presheaves preserves finite limits.
  have : PreservesFiniteLimits (CategoryTheory.elementColimit u (Type w)) :=
    comp_preservesFiniteLimits _ _
  -- The stalk functor on sheaves is their composite.
  exact comp_preservesFiniteLimits _ _

end StacksStalk
