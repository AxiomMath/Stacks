module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryAdjunctionUnit

/-!
# The unit of a degreewise derived adjunction transported along its right adjoint

Let `adj₀ : F ⊣ G` be an adjunction of exact additive functors between abelian categories with
derived categories.  It induces `F.mapDerivedCategory ⊣ G.mapDerivedCategory` on unbounded derived
categories and `F.mapHomotopyCategory ⊣ G.mapHomotopyCategory` on homotopy categories.  In practice
the right adjoints are often known under other names: a functor `L` on derived categories with
`ι : L ≅ G.mapDerivedCategory`, and a functor `hG` on homotopy categories with
`ε : G.mapHomotopyCategory ≅ hG`, related by a comparison `c : Qh ⋙ L ⟶ hG ⋙ Qh` compatible with
`ι` and `ε`.  This file computes the unit of the transported derived adjunction
`F.mapDerivedCategory ⊣ L` at the image of an object of the homotopy category: read through the
comparisons, it is the image of the unit of the transported adjunction
`F.mapHomotopyCategory ⊣ hG`.

## Main results

* `CategoryTheory.mapDerivedCategoryAdjunction_ofNatIsoRight_unit_app_Qh`.

## Implementation notes

The two adjunctions are taken as arbitrary terms together with equations identifying them with the
transported adjunctions.  A consumer whose adjunctions are definitions then discharges the
equations by `rfl` once, at the level of adjunctions, and the statement it receives mentions its
definitions rather than their unfolded bodies.
-/

@[expose] public section

namespace CategoryTheory

open Category

variable {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A] [Category B] [Abelian B]
  [HasDerivedCategory B] {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]

/-- **The unit of a transported degreewise derived adjunction, on the homotopy category.**  Let
`adjD = adj₀.mapDerivedCategory.ofNatIsoRight ι.symm` and
`hadj = (mapHomotopyCategoryAdjunction adj₀).ofNatIsoRight ε`, and let `c : Qh ⋙ L ⟶ hG ⋙ Qh`
be compatible with `ι` and `ε` (`hfac`).  Then at the image of `M`, the unit of `adjD` followed by
the comparisons of `F.mapDerivedCategory` and `c` is the image of the unit of `hadj`. -/
theorem mapDerivedCategoryAdjunction_ofNatIsoRight_unit_app_Qh (adj₀ : F ⊣ G)
    {L : DerivedCategory B ⥤ DerivedCategory A} (ι : L ≅ G.mapDerivedCategory)
    {hG : HomotopyCategory B (ComplexShape.up ℤ) ⥤ HomotopyCategory A (ComplexShape.up ℤ)}
    (ε : G.mapHomotopyCategory (ComplexShape.up ℤ) ≅ hG)
    (c : DerivedCategory.Qh ⋙ L ⟶ hG ⋙ DerivedCategory.Qh)
    (hfac : ∀ N, ι.hom.app (DerivedCategory.Qh.obj N) ≫ G.mapDerivedCategoryFactorsh.hom.app N =
      c.app N ≫ DerivedCategory.Qh.map (ε.inv.app N))
    (adjD : F.mapDerivedCategory ⊣ L) (hadjD : adjD = adj₀.mapDerivedCategory.ofNatIsoRight ι.symm)
    (hadj : F.mapHomotopyCategory (ComplexShape.up ℤ) ⊣ hG)
    (hhadj : hadj =
      (Adjunction.mapHomotopyCategoryAdjunction adj₀ (ComplexShape.up ℤ)).ofNatIsoRight ε)
    (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    adjD.unit.app (DerivedCategory.Qh.obj M) ≫ L.map (F.mapDerivedCategoryFactorsh.hom.app M) ≫
        c.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) =
      DerivedCategory.Qh.map (hadj.unit.app M) := by
  subst hadjD hhadj
  have hc : ∀ N, G.mapDerivedCategoryFactorsh.inv.app N ≫ ι.inv.app (DerivedCategory.Qh.obj N) ≫
      c.app N = DerivedCategory.Qh.map (ε.hom.app N) := by
    intro N
    rw [← cancel_epi (G.mapDerivedCategoryFactorsh.hom.app N), Iso.hom_inv_id_app_assoc,
      ← cancel_epi (ι.hom.app (DerivedCategory.Qh.obj N)), Iso.hom_inv_id_app_assoc,
      reassoc_of% (hfac N), ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, comp_id]
  have hn := ι.inv.naturality (F.mapDerivedCategoryFactorsh.hom.app M)
  have hu := mapDerivedCategoryAdjunction_unit_app_Qh adj₀ M
  rw [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerLeft_app, Iso.symm_hom, assoc,
    ← reassoc_of% hn, reassoc_of% hu, hc, Functor.map_comp]

end CategoryTheory
