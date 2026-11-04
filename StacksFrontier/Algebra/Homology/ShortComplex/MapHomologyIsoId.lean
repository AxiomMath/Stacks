module

public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# The homology comparison of the identity functor

Further declarations about `StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp`
(`mapHomologyIso_id_hom`), kept in its own module.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

end Functor

namespace ShortComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  (S : ShortComplex C) (F : C ⥤ D) (G : D ⥤ E)
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [S.HasHomology] [(S.map F).HasHomology] [(S.map (F ⋙ G)).HasHomology]
  [((S.map F).map G).HasHomology]
  [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)]
  [(F ⋙ G).PreservesLeftHomologyOf S]

section Identity

/-- The homology comparison for the identity functor is the identity. -/
theorem mapHomologyIso_id_hom {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) [S.HasHomology] :
    (S.mapHomologyIso (𝟭 C)).hom = 𝟙 _ := by
  let d : ShortComplex.LeftHomologyMapData (𝟙 S) S.homologyData.left
      (S.homologyData.left.map (𝟭 C)) :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := (Category.id_comp _).trans (Category.comp_id _).symm
      commf' := by
        rw [ShortComplex.LeftHomologyData.map_f']
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      commπ := (Category.comp_id _).trans (Category.id_comp _).symm }
  have hcomm := d.homologyMap_comm
  rw [ShortComplex.homologyMap_id, Category.id_comp,
    show S.homologyData.left.homologyIso.hom = 𝟙 _ from Iso.inv_hom_id _] at hcomm
  exact hcomm.trans (Category.id_comp _)

end Identity

end ShortComplex

namespace ShortComplex

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  (S : ShortComplex C) (R : C ⥤ D) (P : D ⥤ E)
  [R.PreservesZeroMorphisms] [P.PreservesZeroMorphisms]
  {S' S'' : ShortComplex D} (a : S' ⟶ S'') (b : S'' ⟶ S.map R) (b' : S.map R ⟶ S'')

end ShortComplex

namespace ShortComplex

end ShortComplex

end CategoryTheory

end
