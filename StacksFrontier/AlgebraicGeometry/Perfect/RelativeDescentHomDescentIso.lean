module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom

/-!
# The conclusion of Stacks 0DI7 depends on its second argument only up to isomorphism

The induction of Stacks 08DR that proves Stacks 0DI7 runs over a *family* of second arguments,
because the five lemma in degree `n` consumes degrees `n - 1` and `n + 1`; the family used in
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentCapstone.lean` is the family of shifts
`L₀⟦n⟧` of a single object. What the tag asserts is the statement for `L₀` itself, so the
induction's output has to be read back at `n = 0`, and for that
`AlgebraicGeometry.RelativeDescentSituation.HomDescent` must be invariant under an isomorphism of
its second argument.

That invariance is proved here. The transport is postcomposition with the derived pullback of the
isomorphism, at a stage and at the limit, and the only thing to check is that it commutes with the
transition and comparison maps of the system of derived morphism sets. Both are instances of
`Stacks.DerivedPullback.schemeFactorHom`, so one naturality statement about `factorHom` does it.

## Main results

* `Stacks.DerivedPullback.factorHom_comp_map` and
  `Stacks.DerivedPullback.schemeFactorHom_comp_map`: the map on derived morphism sets attached to
  a factorisation `f ≫ g = k` is natural in the target, i.e. commutes with postcomposition by the
  derived pullback of a morphism `L ⟶ L'`.
* `AlgebraicGeometry.RelativeDescentSituation.homTransition_comp_map` and
  `homComparison_comp_map`: the same for the transition and comparison maps of the system.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_of_iso`: **`HomDescent` is invariant
  under an isomorphism of its second argument.**
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_shiftZero`: `HomDescent K₀ (L₀⟦(0 : ℤ)⟧)`
  gives `HomDescent K₀ L₀`, which is how the family form of the tag is read at the tag's own
  statement.
* `Stacks.DerivedPullback.subsingleton_derivedPullback_hom_of_isZero` and
  `AlgebraicGeometry.RelativeDescentSituation.homDescent_of_isZero`: **`HomDescent` holds, with no
  hypothesis on the situation, when its first argument is a zero object.** The derived pullback of
  a zero object is initial because the derived pullback has a right adjoint, so every stage of the
  system of derived morphism sets is a singleton. This is the one unconditional source of a term
  of `HomDescent` in the tree, and it is what makes the hypothesis of `homDescent_of_iso`
  instantiable rather than merely satisfiable.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedAdjunction)

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.DerivedPullback

/-! ### Naturality of the factorisation map in its target -/

section RingedSpaces

variable {X Y Z : RingedSpace.{u, u}}

/-- **The map on derived morphism sets attached to a factorisation is natural in its target.**
For `f ≫ g = k` and `ε : L ⟶ L'`, postcomposing by `Lg^*ε` before applying `factorHom` is the
same as applying `factorHom` and then postcomposing by `Lk^*ε`. -/
theorem factorHom_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L L' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) (ε : L ⟶ L')
    (φ : (derivedPullback g).obj K ⟶ (derivedPullback g).obj L) :
    factorHom f g k h K L' (φ ≫ (derivedPullback g).map ε) =
      factorHom f g k h K L φ ≫ (derivedPullback k).map ε := by
  have nat := (factorIso f g k h).hom.naturality ε
  simp only [Functor.comp_map] at nat
  simp only [factorHom, Iso.homCongr_apply, Functor.map_comp, Category.assoc, Iso.app_hom,
    Iso.app_inv]
  rw [nat]

/-- **The derived morphism sets out of the derived pullback of a zero object are singletons.**
The derived pullback has a right adjoint, so morphisms out of `Lf^*K` are morphisms out of `K`,
and `K` is a zero object. -/
theorem subsingleton_derivedPullback_hom_of_isZero (f : X ⟶ Y)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (hK : IsZero K)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    Subsingleton ((derivedPullback f).obj K ⟶ (derivedPullback f).obj L) :=
  ⟨fun _ _ => ((derivedAdjunction f).homEquiv K ((derivedPullback f).obj L)).injective
    (hK.eq_of_src _ _)⟩

end RingedSpaces

section Schemes

variable {X Y Z : Scheme.{u}}

/-- The map on derived morphism sets attached to a factorisation of morphisms of schemes is
natural in its target. -/
theorem schemeFactorHom_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L L' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (ε : L ⟶ L')
    (φ : (derivedPullback g.toLRSHom.toShHom).obj K ⟶
      (derivedPullback g.toLRSHom.toShHom).obj L) :
    schemeFactorHom f g k h K L' (φ ≫ (derivedPullback g.toLRSHom.toShHom).map ε) =
      schemeFactorHom f g k h K L φ ≫ (derivedPullback k.toLRSHom.toShHom).map ε :=
  factorHom_comp_map f.toLRSHom.toShHom g.toLRSHom.toShHom k.toLRSHom.toShHom
    (congrArg (fun m : X ⟶ Z ↦ m.toLRSHom.toShHom) h) K L L' ε φ

end Schemes

end Stacks.DerivedPullback

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{v, u} I)
  (K₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

variable {L L' : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace))}

/-- **The transition maps of the system of derived morphism sets are natural in the second
argument.** -/
theorem homTransition_comp_map (ε : L ⟶ L') {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L) :
    D.homTransition K₀ L' h
        (φ ≫ (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map ε) =
      D.homTransition K₀ L h φ ≫
        (derivedPullback (D.toFixedStage j).toLRSHom.toShHom).map ε :=
  Stacks.DerivedPullback.schemeFactorHom_comp_map (D.transition h) (D.toFixedStage i)
    (D.toFixedStage j) (D.transition_comp_toFixedStage h) K₀ L L' ε φ

/-- **The comparison maps of the system of derived morphism sets are natural in the second
argument.** -/
theorem homComparison_comp_map (ε : L ⟶ L') (i : D.LaterIndex)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L) :
    D.homComparison K₀ L' i (φ ≫ (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map ε) =
      D.homComparison K₀ L i φ ≫ (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).map ε :=
  Stacks.DerivedPullback.schemeFactorHom_comp_map (D.projection i) (D.toFixedStage i)
    D.limitToFixedStage (D.projection_comp_toFixedStage i) K₀ L L' ε φ

/-- **The conclusion of Stacks 0DI7 is invariant under an isomorphism of its second argument.**
Postcomposition with the derived pullback of `e` is a bijection on derived morphism sets at every
stage and at the limit, and by `homTransition_comp_map` and `homComparison_comp_map` it is
compatible with the transition and comparison maps of the system. -/
theorem homDescent_of_iso (e : L ≅ L') (hd : D.HomDescent K₀ L) : D.HomDescent K₀ L' := by
  obtain ⟨hsurj, hinj⟩ := hd
  refine ⟨fun ψ => ?_, fun i φ φ' hφ => ?_⟩
  · obtain ⟨i, φ, hφ⟩ :=
      hsurj (ψ ≫ (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).map e.inv)
    refine ⟨i, φ ≫ (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map e.hom, ?_⟩
    rw [D.homComparison_comp_map K₀ e.hom i φ, hφ]
    simp
  · obtain ⟨j, hij, hj⟩ :=
      hinj i (φ ≫ (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map e.inv)
        (φ' ≫ (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map e.inv) (by
          rw [D.homComparison_comp_map K₀ e.inv i φ, D.homComparison_comp_map K₀ e.inv i φ', hφ])
    refine ⟨j, hij, ?_⟩
    have := congrArg
      (fun χ => χ ≫ (derivedPullback (D.toFixedStage j).toLRSHom.toShHom).map e.hom) hj
    simpa [D.homTransition_comp_map K₀ e.inv hij] using this

/-- **The family form of Stacks 0DI7 read at the tag's own statement.** The induction proves the
conclusion of the tag for the family of shifts `L₀⟦n⟧`; at `n = 0` the shift is isomorphic to `L₀`
itself, so `homDescent_of_iso` returns the conclusion for `L₀`. -/
theorem homDescent_shiftZero
    (L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
    (hd : D.HomDescent K₀ (L₀⟦(0 : ℤ)⟧)) : D.HomDescent K₀ L₀ :=
  D.homDescent_of_iso K₀ ((shiftFunctorZero _ ℤ).app L₀) hd

/-- **The conclusion of Stacks 0DI7 holds unconditionally when its first argument is a zero
object.** Every stage of the system of derived morphism sets and the group over it are singletons
by `Stacks.DerivedPullback.subsingleton_derivedPullback_hom_of_isZero`, so both clauses are
witnessed by the zero morphism at the fixed stage. This is the unconditional term of `HomDescent`
that makes the hypothesis of `homDescent_of_iso` instantiable. -/
theorem homDescent_of_isZero
    (L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
    (hK₀ : IsZero K₀) : D.HomDescent K₀ L₀ := by
  refine ⟨fun _ => ⟨⟨D.descent.base, le_rfl⟩, 0, ?_⟩, fun i _ _ _ => ⟨i, le_rfl, ?_⟩⟩ <;>
    exact (Stacks.DerivedPullback.subsingleton_derivedPullback_hom_of_isZero _ hK₀ L₀).elim _ _

end AlgebraicGeometry.RelativeDescentSituation

end
