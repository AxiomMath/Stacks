module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangeResolution

/-!
# A base change map is invertible where its degreewise comparison is a quasi-isomorphism

This is the converse of
`Stacks.Cohomology.DerivedBaseChangeResolution.isIso_Q_map_comp_of_isIso_derivedBaseChange`. In
the situation of that lemma (a square of additive functors with `G`, `G'` exact, a comparison
`α : F ⋙ G ⟶ G' ⋙ F'`, transformations `ε`, `ε'` from the homotopy categories invertible at `K`
and at the target `K'` of a quasi-isomorphism `q : G'(K) ⟶ K'`, and a base change map
`β : RF ⋙ G ⟶ G' ⋙ RF'` characterized at `K` by the usual equation), the base change map `β` is
invertible at `K` as soon as the morphism of complexes `α_K ≫ F'(q)` is a quasi-isomorphism.

## Main results

* `Stacks.Cohomology.DerivedBaseChangeResolution.isIso_derivedBaseChange_of_isIso_Q_map_comp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedBaseChangeResolution

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  (F : A ⥤ B) (G : B ⥤ B') (G' : A ⥤ A') (F' : A' ⥤ B')
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- **The base change map is invertible where the degreewise comparison through a resolution is a
quasi-isomorphism.** Under the hypotheses of `isIso_Q_map_comp_of_isIso_derivedBaseChange`, if
`α_K ≫ F'(q)` is an isomorphism of the derived category, so is `β` at `K`: by naturality of `ε'`
along `q` the localized `α_K` followed by `ε'` at `G'(K)` is invertible, and by `hfac` it is the
base change map precomposed with an isomorphism. -/
theorem isIso_derivedBaseChange_of_isIso_Q_map_comp (α : F ⋙ G ⟶ G' ⋙ F')
    (RF : DerivedCategory A ⥤ DerivedCategory B) (RF' : DerivedCategory A' ⥤ DerivedCategory B')
    (ε : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (ε' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF')
    (β : RF ⋙ G.mapDerivedCategory ⟶ G'.mapDerivedCategory ⋙ RF')
    (H : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ F'.mapHomotopyCategory (ComplexShape.up ℤ))
    (K : CochainComplex A ℤ) (K' : CochainComplex A' ℤ)
    (q : (G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ K') [QuasiIso q]
    (hH : H.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K))
    (hfac : G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
      G.mapDerivedCategory.map (ε.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
      β.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map (H.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        ε'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≫
        RF'.map (G'.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)))
    (h₁ : IsIso (ε.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)))
    (h₂ : IsIso (ε'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K')))
    (hq : IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K ≫
        (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map q))) :
    IsIso (β.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) := by
  let K₀ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K
  let qb := (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map q
  -- the localized degreewise comparison followed by `F'(q)` is invertible
  have hC : IsIso (DerivedCategory.Qh.map (H.app K₀) ≫
      DerivedCategory.Qh.map ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).map qb)) := by
    rw [← Functor.map_comp, hH]
    show IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) ≫
      (HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).map q)))
    rw [← Functor.map_comp]
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso B') _).2 hq
  have hq' : IsIso (DerivedCategory.Qh.map qb) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact inferInstanceAs (QuasiIso q)
  have hnat := ε'.naturality qb
  simp only [Functor.comp_map] at hnat
  -- the localized degreewise comparison followed by `ε'` at `G'(K)` is invertible
  have hA : IsIso (DerivedCategory.Qh.map (H.app K₀) ≫
      ε'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K₀)) := by
    have e : (DerivedCategory.Qh.map (H.app K₀) ≫
        ε'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K₀)) ≫
          RF'.map (DerivedCategory.Qh.map qb) =
        (DerivedCategory.Qh.map (H.app K₀) ≫
          DerivedCategory.Qh.map ((F'.mapHomotopyCategory (ComplexShape.up ℤ)).map qb)) ≫
          ε'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K') := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (DerivedCategory.Qh.map (H.app K₀) ≫ ·) hnat.symm
    have hB : IsIso ((DerivedCategory.Qh.map (H.app K₀) ≫
        ε'.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj K₀)) ≫
          RF'.map (DerivedCategory.Qh.map qb)) := by
      rw [e]
      exact IsIso.comp_isIso' hC h₂
    have : IsIso (RF'.map (DerivedCategory.Qh.map qb)) :=
      inferInstanceAs (IsIso (RF'.mapIso (@asIso _ _ _ _ (DerivedCategory.Qh.map qb) hq')).hom)
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ this hB
  have hR : IsIso (G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K₀) ≫
      G.mapDerivedCategory.map (ε.app K₀) ≫ β.app (DerivedCategory.Qh.obj K₀)) := by
    rw [hfac, ← Category.assoc]
    exact IsIso.comp_isIso' hA inferInstance
  rw [← Category.assoc] at hR
  exact IsIso.of_isIso_comp_left (G.mapDerivedCategoryFactorsh.inv.app
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K₀) ≫ G.mapDerivedCategory.map (ε.app K₀)) _

end Stacks.Cohomology.DerivedBaseChangeResolution

end
