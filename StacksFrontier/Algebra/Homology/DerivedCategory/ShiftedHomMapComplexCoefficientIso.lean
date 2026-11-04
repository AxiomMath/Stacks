module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ShiftedHomMapComplex

/-!
# The action of an exact functor on `Ext`, followed by an identification of coefficients

`DerivedCategory.shiftedHomMapComplex_comp_triangleOfSESδ` says that the action
`shiftedHomMapComplex Φ` of an exact functor `Φ` on `Ext` groups commutes with the boundary maps of
a short exact sequence of complexes.  Here the same compatibility is stated after an identification
`κ : C ⋙ Φ ≅ C'` of coefficient complexes, for a short exact sequence `T` sent by `C` and `C'` to
short exact sequences of complexes.

## Main results

* `DerivedCategory.shiftedHomMapComplex_comp_iso_comp_triangleOfSESδ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t t' v v' u u'

namespace DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {𝒜' : Type u'} [Category.{v'} 𝒜'] [Abelian 𝒜']
  [HasDerivedCategory.{t} 𝒜] [HasDerivedCategory.{t'} 𝒜']
  (Φ : 𝒜 ⥤ 𝒜') [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- **The action of `Φ`, followed by an identification `κ : C ⋙ Φ ≅ C'` of coefficient complexes,
is compatible with the boundary maps** of a short exact sequence `T` sent by `C` and `C'` to short
exact sequences of complexes. -/
theorem shiftedHomMapComplex_comp_iso_comp_triangleOfSESδ {𝒞 : Type*} [Category 𝒞]
    [Limits.HasZeroMorphisms 𝒞] (C : 𝒞 ⥤ CochainComplex 𝒜 ℤ) (C' : 𝒞 ⥤ CochainComplex 𝒜' ℤ)
    [hC : C.PreservesZeroMorphisms] [hC' : C'.PreservesZeroMorphisms]
    (κ : C ⋙ Φ.mapHomologicalComplex (ComplexShape.up ℤ) ≅ C') (E : DerivedCategory 𝒜)
    (T : ShortComplex 𝒞) (hT : (C.mapShortComplex.obj T).ShortExact)
    (hT' : (C'.mapShortComplex.obj T).ShortExact) (i : ℤ)
    (e : ShiftedHom E (Q.obj (C.obj T.X₃)) i) :
    shiftedHomMapComplex Φ E (C.obj T.X₁) (i + 1) (e.comp (triangleOfSESδ hT) (add_comm 1 i)) ≫
        (Q.map (κ.hom.app T.X₁))⟦i + 1⟧' =
      (show ShiftedHom (Φ.mapDerivedCategory.obj E) (Q.obj (C'.obj T.X₃)) i from
        shiftedHomMapComplex Φ E (C.obj T.X₃) i e ≫ (Q.map (κ.hom.app T.X₃))⟦i⟧').comp
        (triangleOfSESδ hT') (add_comm 1 i) := by
  let hΦ := hT.map_of_exact (Φ.mapHomologicalComplex (ComplexShape.up ℤ))
  have hnat := triangleOfSESδ_naturality hΦ hT' (T.mapNatTrans κ.hom)
  have hadd := (shiftFunctorAdd' (DerivedCategory 𝒜') 1 i (i + 1) (add_comm 1 i)).inv.naturality
      (Q.map (κ.hom.app T.X₁))
  have key : (triangleOfSESδ hΦ)⟦i⟧' ≫
      (shiftFunctorAdd' _ 1 i (i + 1) (add_comm 1 i)).inv.app _ ≫
        (Q.map (κ.hom.app T.X₁))⟦i + 1⟧' =
      (Q.map (κ.hom.app T.X₃))⟦i⟧' ≫ (triangleOfSESδ hT')⟦i⟧' ≫
        (shiftFunctorAdd' _ 1 i (i + 1) (add_comm 1 i)).inv.app _ := by
    refine (congrArg (_ ≫ ·) hadd.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) ((Functor.map_comp _ _ _).symm.trans
      ((congrArg (shiftFunctor _ i).map hnat).trans (Functor.map_comp _ _ _)))).trans ?_
    exact Category.assoc _ _ _
  refine (congrArg (· ≫ (Q.map (κ.hom.app T.X₁))⟦i + 1⟧')
    (shiftedHomMapComplex_comp_triangleOfSESδ Φ E hT i e)).trans ?_
  dsimp only [ShiftedHom.comp]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) key

end DerivedCategory

end
