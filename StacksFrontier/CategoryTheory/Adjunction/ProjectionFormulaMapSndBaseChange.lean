module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# The projection-formula map with the counit in the second factor and base change

For a square of categories whose horizontal functors `Lf`, `Lf'` have right adjoints `Rf`,
`Rf'`, whose composites are identified with one functor, and for bifunctors on the four corners
with compatible comparisons (`Stacks.AffineProjectionFormula.TensorComparisonCompatible`), the
map `Stacks.ProjectionFormula.adjunctionTensorMapSnd` `A(H, Rf G) ⟶ Rf(B(Lf H, G))` is
compatible with the base change map `Lg Rf ⟶ Rf' Lg'`. This is the mirror image of
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`.

## Main results

* `Stacks.AffineProjectionFormula.adjunctionTensorMapSnd_baseChange_square`
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.AffineProjectionFormula

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
  (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
  (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B')

/-- The defining equation of `adjunctionTensorMapSnd`, transposed. -/
lemma map_adjunctionTensorMapSnd_comp_counit (H : S) (G : T) :
    Lf.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd adjf A B αf H G) ≫
        adjf.counit.app (B.obj (Lf.obj H, G)) =
      αf.app (H, Rf.obj G) ≫ B.map (𝟙 (Lf.obj H) ×ₘ adjf.counit.app G) := by
  have h := (adjf.homEquiv (A.obj (H, Rf.obj G)) (B.obj (Lf.obj H, G))).symm_apply_apply
    (αf.app (H, Rf.obj G) ≫ B.map (𝟙 (Lf.obj H) ×ₘ adjf.counit.app G))
  rw [Adjunction.homEquiv_counit] at h
  exact h

/-- **The projection-formula map with the counit in the second factor is compatible with base
change**: the hexagon of Stacks 0E48 with the roles of the two factors exchanged. -/
theorem adjunctionTensorMapSnd_baseChange_square (H : S) (G : T)
    (hsq : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' H (Rf.obj G)) :
    αg.app (H, Rf.obj G) ≫
        A'.map (𝟙 (Lg.obj H) ×ₘ Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef G) ≫
          Stacks.ProjectionFormula.adjunctionTensorMapSnd adjf' A' B' αf' (Lg.obj H) (Lg'.obj G) =
      Lg.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd adjf A B αf H G) ≫
        Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef (B.obj (Lf.obj H, G)) ≫
          Rf'.map (αg'.app (Lf.obj H, G) ≫
            B'.map ((squareCompositeIso eg ef).inv.app H ×ₘ 𝟙 (Lg'.obj G))) := by
  rw [TensorComparisonCompatible] at hsq
  have h1 : Lf'.map (A'.map
        (𝟙 (Lg.obj H) ×ₘ Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef G)) ≫
      αf'.app (Lg.obj H, Rf'.obj (Lg'.obj G)) =
      αf'.app (Lg.obj H, Lg.obj (Rf.obj G)) ≫
        B'.map (𝟙 (Lf'.obj (Lg.obj H)) ×ₘ
          Lf'.map (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef G)) := by
    have h := αf'.naturality
      (X := ((Lg.obj H, Lg.obj (Rf.obj G)) : S' × S'))
      (Y := ((Lg.obj H, Rf'.obj (Lg'.obj G)) : S' × S'))
      (𝟙 (Lg.obj H) ×ₘ Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef G)
    simpa using h
  have h2 : Lf'.map (Lg.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd adjf A B αf H G)) ≫
      (squareCompositeIso eg ef).hom.app (Rf.obj (B.obj (Lf.obj H, G))) =
      (squareCompositeIso eg ef).hom.app (A.obj (H, Rf.obj G)) ≫
        Lg'.map (Lf.map (Stacks.ProjectionFormula.adjunctionTensorMapSnd adjf A B αf H G)) := by
    have h := (squareCompositeIso eg ef).hom.naturality
      (Stacks.ProjectionFormula.adjunctionTensorMapSnd adjf A B αf H G)
    simpa using h
  have h3 : Lg'.map (B.map (𝟙 (Lf.obj H) ×ₘ adjf.counit.app G)) ≫
      αg'.app (Lf.obj H, G) =
      αg'.app (Lf.obj H, Lf.obj (Rf.obj G)) ≫
        B'.map (𝟙 (Lg'.obj (Lf.obj H)) ×ₘ Lg'.map (adjf.counit.app G)) := by
    have h := αg'.naturality
      (X := ((Lf.obj H, Lf.obj (Rf.obj G)) : T × T))
      (Y := ((Lf.obj H, G) : T × T))
      (𝟙 (Lf.obj H) ×ₘ adjf.counit.app G)
    simpa using h
  refine (adjf'.homEquiv _ _).symm.injective ?_
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    map_adjunctionTensorMapSnd_comp_counit,
    Adjunction.counit_naturality, Adjunction.counit_naturality_assoc,
    map_baseChangeMap_comp_counit_assoc]
  conv_lhs => rw [reassoc_of% h1, ← Functor.map_comp, prod_comp, Category.comp_id,
    map_baseChangeMap_comp_counit]
  conv_rhs => rw [reassoc_of% h2, ← Functor.map_comp_assoc,
    map_adjunctionTensorMapSnd_comp_counit, Functor.map_comp, Category.assoc,
    reassoc_of% h3, ← Functor.map_comp, prod_comp, Category.comp_id, Category.id_comp,
    ← reassoc_of% hsq, ← Functor.map_comp, prod_comp, Iso.hom_inv_id_app]
  rfl

end Stacks.AffineProjectionFormula

end
