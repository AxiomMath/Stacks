/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ReducedOfStalkUnit
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverFieldProperties.Reduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduction of a group scheme as a closed subgroup scheme

Over a perfect field the reduction `G_red` of a group scheme `G` is a closed subgroup scheme
([Stacks, Tag 047R]).  This file records the facts about the inclusion `G_red ⟶ G` used when
reducing questions about the local ring of `G` at its unit to statements about `G_red`: the
inclusion is a surjective closed immersion, hence a homeomorphism; opens of `G_red` are cut out
by affine opens of `G`; reduced closed subgroup schemes of `G` factor through `G_red`; and, when
the closed points of `G` are rational and dense, every nonempty open of `G_red` contains a
rational point of `G_red`.

## Main results

* `AlgebraicGeometry.exists_reduction_closedSubgroupScheme`.
* `AlgebraicGeometry.exists_isAffineOpen_preimage_le`.
* `AlgebraicGeometry.exists_lift_closedSubgroupScheme_of_isReduced`.
* `AlgebraicGeometry.exists_rationalPoint_mem_of_surjective`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- **The reduction as a closed subgroup scheme.**  Over a perfect field, a group scheme `G` has
a reduced closed subgroup scheme whose inclusion is surjective ([Stacks, Tag 047R]). -/
@[sga "3 VIA 0.2" "partial",
  sga "3 VIA 2.5.4" "more general",
  sga "3 VIA 5.6" "more general",
  sga "3 VIB 12.1" "Over the base field",
  sga "3 VIIA 8.3" "Over a perfect field",
  sga "3 XII 1.0" "partial",
  sga "3 XII 4.4" "partial",
  sga "3 XVII 1.6" "Over a perfect field"]
theorem exists_reduction_closedSubgroupScheme {k : Type u} [Field k] [PerfectField k]
    (G : Grp (Over (Spec (.of k)))) :
    ∃ L : ClosedSubgroupScheme G, Surjective L.ι.hom.hom.left ∧ IsReduced L.carrier.X.left := by
  obtain ⟨L, e, he⟩ := exists_closedSubgroupScheme_reduction G
  let I := Scheme.IdealSheafData.vanishingIdeal (⊤ : TopologicalSpace.Closeds G.X.left)
  have : IsIso e.inv.left := by
    change IsIso ((Over.forget _).map e.inv)
    infer_instance
  have hL : L.ι.hom.hom.left = e.inv.left ≫ I.subschemeι := by
    have h1 := congrArg (fun f => f.left) he
    simp only [Over.homMk_left, Over.comp_left] at h1
    calc L.ι.hom.hom.left = (e.inv.left ≫ e.hom.left) ≫ L.ι.hom.hom.left := by
          rw [← Over.comp_left, e.inv_hom_id, Over.id_left, Category.id_comp]
      _ = e.inv.left ≫ I.subschemeι := by
          rw [Category.assoc]
          exact congrArg _ h1.symm
  refine ⟨L, ⟨?_⟩, @isReduced_of_isOpenImmersion _ _ e.inv.left _
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _)⟩
  rw [hL]
  have hsurj : Function.Surjective I.subschemeι := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  exact hsurj.comp (ConcreteCategory.bijective_of_isIso e.inv.left.base).2

/-- A surjective closed immersion is a homeomorphism. -/
lemma isHomeomorph_of_isClosedImmersion_of_surjective {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [Surjective i] : IsHomeomorph i :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨i.isClosedEmbedding.isEmbedding, i.surjective⟩

/-- The source of a surjective closed immersion into an irreducible scheme is irreducible. -/
lemma irreducibleSpace_of_isClosedImmersion_of_surjective {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [Surjective i] [IrreducibleSpace X] : IrreducibleSpace Y :=
  (isHomeomorph_of_isClosedImmersion_of_surjective i).homeomorph.irreducibleSpace_iff.mpr
    inferInstance

/-- For a surjective closed immersion `i : Y ⟶ X` and an open `W` of `Y` containing `y`, there is
an affine open `U` of `X` containing `i y` with `i⁻¹ U ⊆ W`. -/
lemma exists_isAffineOpen_preimage_le {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    [Surjective i] (W : Y.Opens) {y : Y} (hy : y ∈ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ i y ∈ U ∧ i ⁻¹ᵁ U ≤ W := by
  have hi := isHomeomorph_of_isClosedImmersion_of_surjective i
  let W' : X.Opens := ⟨i '' W, hi.isOpenMap _ W.2⟩
  obtain ⟨U, hU, hyU, hUW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show i y ∈ W' from ⟨y, hy, rfl⟩)
  refine ⟨U, hU, hyU, fun z hz => ?_⟩
  obtain ⟨w, hw, hwz⟩ := hUW hz
  rwa [← hi.injective hwz]

/-- A morphism from a reduced scheme factors through a surjective closed immersion. -/
private lemma exists_lift_of_isClosedImmersion_of_surjective' {X Y Z : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] [Surjective i] (f : Z ⟶ X) [IsReduced Z] :
    ∃ g : Z ⟶ Y, g ≫ i = f :=
  exists_lift_of_isClosedImmersion i f (by simp [Set.range_eq_univ.mpr i.surjective])

/-- A reduced closed subgroup scheme factors through a closed subgroup scheme with surjective
inclusion (such as the reduction). -/
@[sga "3 XII 1.0" "partial", sga "3 XVII 1.6" "partial"]
lemma exists_lift_closedSubgroupScheme_of_isReduced {S : Scheme.{u}} {G : Grp (Over S)}
    (L : ClosedSubgroupScheme G) [Surjective L.ι.hom.hom.left] (Z : ClosedSubgroupScheme G)
    [IsReduced Z.carrier.X.left] :
    ∃ iZ : Z.carrier.X.left ⟶ L.carrier.X.left, iZ ≫ L.ι.hom.hom.left = Z.ι.hom.hom.left := by
  have := L.isClosedImmersion
  exact exists_lift_of_isClosedImmersion_of_surjective' _ _

/-- The inclusion of a closed subgroup scheme sends the unit to the unit. -/
lemma closedSubgroupScheme_ι_unit {S : Scheme.{u}} {G : Grp (Over S)} (L : ClosedSubgroupScheme G)
    (p : (𝟙_ (Over S)).left) :
    L.ι.hom.hom.left ((η[L.carrier.X]).left p) = (η[G.X]).left p := by
  have h : η[L.carrier.X] ≫ L.ι.hom.hom = η[G.X] := IsMonHom.one_hom _
  rw [← h, Over.comp_left, Scheme.Hom.comp_apply]

/-- **Rational points of the reduction.**  If the closed points of a Jacobson group scheme `G` over
an algebraically closed field `Ω` are `Ω`-rational, then every nonempty open of a reduced closed
subgroup scheme with surjective inclusion contains an `Ω`-rational point. -/
lemma exists_rationalPoint_mem_of_surjective {Ω : Type u} [Field Ω]
    (G : Grp (Over (Spec (.of Ω)))) [JacobsonSpace G.X.left]
    (hrat : ∀ x ∈ closedPoints G.X.left, ∃ p : 𝟙_ (Over (Spec (.of Ω))) ⟶ G.X,
      p.left (basePoint Ω) = x)
    (L : ClosedSubgroupScheme G) [Surjective L.ι.hom.hom.left]
    (W : L.carrier.X.left.Opens) (hW : (W : Set L.carrier.X.left).Nonempty) :
    ∃ g : 𝟙_ (Over (Spec (.of Ω))) ⟶ L.carrier.X, g.left (basePoint Ω) ∈ W := by
  have := L.isClosedImmersion
  let i := L.ι.hom.hom.left
  have hi := isHomeomorph_of_isClosedImmersion_of_surjective i
  obtain ⟨_, ⟨⟨w, hw, rfl⟩, hx⟩⟩ := nonempty_inter_closedPoints (hW.image i)
    (hi.isOpenMap _ W.2).isLocallyClosed
  obtain ⟨p, hp⟩ := hrat _ hx
  have : IsReduced (𝟙_ (Over (Spec (.of Ω)))).left := inferInstanceAs (IsReduced (Spec (.of Ω)))
  obtain ⟨q, hq⟩ := exists_lift_of_isClosedImmersion_of_surjective' i p.left
  refine ⟨Over.homMk q ?_, ?_⟩
  · rw [← Over.w L.ι.hom.hom, ← Category.assoc, hq, Over.w p]
  · change q (basePoint Ω) ∈ W
    have : i (q (basePoint Ω)) = i w := by
      rw [← Scheme.Hom.comp_apply, hq, hp]
    rwa [hi.injective this]

end AlgebraicGeometry

end
