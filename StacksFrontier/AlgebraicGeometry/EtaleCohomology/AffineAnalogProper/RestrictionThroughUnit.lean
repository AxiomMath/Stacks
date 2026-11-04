module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteDirectImageRestriction

/-!
# Restriction of étale cohomology through the unit of the adjunction

For a morphism of schemes `π : Y' ⟶ Y` and an abelian sheaf `N` on the small étale site of `Y`,
the restriction of a class `x ∈ H^q(Y, N)` to `Y'` is, up to the adjunction isomorphism
`Ext^q(ℤ_Y, π_* π⁻¹N) ≅ Ext^q(π⁻¹ℤ_Y, π⁻¹N)` and the constant-sheaf comparison, the image of `x`
under the unit `N ⟶ π_* π⁻¹ N`. When `π_*` is exact — `π` integral, finite for instance — the
adjunction map is bijective, so `x` restricts to zero on `Y'` exactly when it dies along the unit.

This is the step of the proof of [Stacks, Tag 09ZE] that turns "the class dies after a finite
surjective base change `Y' ⟶ Y`" (Stacks 09ZD (2)) into "the class dies along the monomorphism
`M ⟶ π_* M`".

## Main results

* `Stacks.ExtAdjunction.mapExactFunctor_eq_extMap_comp_unit` — the triangle identity on `Ext`.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_eq_zero_iff_comp_unit_eq_zero` — a class
  restricts to zero along an integral morphism iff it dies along the unit.

## References

* [Stacks Project, Tag 09ZE](https://stacks.math.columbia.edu/tag/09ZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

universe w w' v v' u u'

namespace Stacks.ExtAdjunction

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [HasExt.{w} C] [HasExt.{w'} D]

/-- **The triangle identity on `Ext`.** Applying the exact left adjoint `L` to a class `e` is the
adjunction map applied to `e` followed by the unit. -/
theorem mapExactFunctor_eq_extMap_comp_unit {A B : C} {n : ℕ} (e : Ext.{w} A B n) :
    e.mapExactFunctor L =
      extMap adj A (L.obj B) n (e.comp (Ext.mk₀ (adj.unit.app B)) (add_zero n)) := by
  rw [extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, adj.left_triangle_components,
    Ext.comp_mk₀_id]

end Stacks.ExtAdjunction

namespace Stacks.EtaleCohomology

variable {Y Y' : Scheme.{u}} (p : Y' ⟶ Y) [IsIntegralHom p]

/-- **Restriction along an integral morphism kills a class exactly when the unit does.** For
`p : Y' ⟶ Y` integral and `x ∈ H^q(Y, N)`, the restriction of `x` to `Y'` vanishes if and only
if the image of `x` in `H^q(Y, p_* p⁻¹ N)` under the unit vanishes. -/
theorem etaleCohomologyRestrictionMap_eq_zero_iff_comp_unit_eq_zero
    (N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} N q) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} p N q x = 0 ↔
      x.comp (Ext.mk₀ ((etaleAbelianInverseImageDirectImageAdj.{u, 0} p).unit.app N))
        (add_zero q) = 0 := by
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, 0} p
  have hbij := Stacks.ExtAdjunction.extMap_bijective adj
    ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) ((etaleAbelianInverseImage.{u, 0} p).obj N) q
  have hres : etaleCohomologyRestrictionMap.{u, 0, u + 1} p N q x =
      (Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} p).app
        (AddCommGrpCat.of (ULift ℤ))).inv).comp
        (Stacks.ExtAdjunction.extMap adj _ _ q
          (x.comp (Ext.mk₀ (adj.unit.app N)) (add_zero q))) (zero_add q) := by
    rw [etaleCohomologyRestrictionMap_apply,
      Stacks.ExtAdjunction.mapExactFunctor_eq_extMap_comp_unit adj]
  have hpre := Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso
    ((etaleAbelianInverseImageConstantIso.{u, 0} p).app (AddCommGrpCat.of (ULift ℤ))).inv
      (Z := (etaleAbelianInverseImage.{u, 0} p).obj N) q
  rw [hres]
  refine ⟨fun h ↦ hbij.1 ((hpre.1 (h.trans (map_zero _).symm)).trans (map_zero _).symm),
    fun h ↦ ?_⟩
  rw [h, map_zero, Ext.comp_zero]

end Stacks.EtaleCohomology
