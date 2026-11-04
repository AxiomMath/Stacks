module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ShortExactFunctorsTriangle

/-!
# The distinguished triangle of a short exact sequence of exact functors ending at the identity

Let `C` be an abelian category with a chosen derived category, let `L` and `M` be exact additive
endofunctors of `C`, and let `α : L ⟶ M` and `β : M ⟶ 𝟭 C` be natural transformations such that
`0 → L F → M F → F → 0` is short exact for every object `F` of `C`.  Then every object `K` of
the derived category of `C` sits in a distinguished triangle
`L K → M K → K → (L K)[1]`
whose first two arrows are the natural transformations induced by `α` and `β`.

This is the variant of `StacksFrontier.Algebra.Homology.DerivedCategory.ShortExactFunctorsTriangle`
in which the identity functor is the *third* term of the short exact sequence rather than the
middle one; the middle functor is then an arbitrary exact functor and the transformation `α`
relating it to `L` is no longer a transformation to or from the identity.

## Main definitions

* `CategoryTheory.derivedNatTrans`: the natural transformation
  `F.mapDerivedCategory ⟶ G.mapDerivedCategory` induced by `α : F ⟶ G` for exact `F` and `G`,
  between derived categories of possibly different abelian categories.

## Main results

* `DerivedCategory.exists_distTriang_of_natTrans_shortExact_toId`: the distinguished triangle
  `L K ⟶ M K ⟶ K ⟶ (L K)[1]`, with the first two arrows the induced natural transformations
  at `K`.

## Implementation notes

The argument is the one of the file this builds on: an object `K` of the derived category is
written as `Q K₀` for a cochain complex `K₀`, the transformations are applied degreewise, the
resulting short complex of cochain complexes is short exact because it is degreewise short
exact, and `DerivedCategory.triangleOfSES` produces the triangle, whose vertices are then
identified with the induced functors by `CategoryTheory.Functor.mapDerivedCategoryFactors`.

The third arrow is produced existentially: the connecting map of a distinguished triangle is
not determined by the first two arrows.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe w v u

namespace CategoryTheory

section Derived

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F G : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- A natural transformation of exact functors induces one on derived categories, by lifting the
transformation it induces on complexes through the localization at quasi-isomorphisms.

Both functors are liftings through the localization functor `DerivedCategory.Q` of the functors
on cochain complexes induced by `F` and `G`, so the degreewise transformation descends. -/
def derivedNatTrans (α : F ⟶ G) : F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- On the image of a complex, `derivedNatTrans` is the transformation induced on complexes,
read through the two identifications of the derived functors with the localized ones. -/
theorem derivedNatTrans_app_Q (α : F ⟶ G) (X : CochainComplex A ℤ) :
    (derivedNatTrans F G α).app (DerivedCategory.Q.obj X) ≫
        G.mapDerivedCategoryFactors.hom.app X =
      F.mapDerivedCategoryFactors.hom.app X ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app X) := by
  rw [derivedNatTrans, Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

/-- The component of `CategoryTheory.derivedNatTrans` at the image of a cochain complex. -/
theorem derivedNatTrans_app (α : F ⟶ G) (K : CochainComplex A ℤ) :
    (derivedNatTrans F G α).app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K) ≫
        G.mapDerivedCategoryFactors.inv.app K := by
  rw [derivedNatTrans, Localization.liftNatTrans_app]
  rfl

/-- The component of `CategoryTheory.derivedNatTrans` at an object of the derived category
presented as the image of a cochain complex. -/
theorem derivedNatTrans_app_of_iso (α : F ⟶ G) {K₀ : CochainComplex A ℤ}
    {K : DerivedCategory A} (e : DerivedCategory.Q.obj K₀ ≅ K) :
    (derivedNatTrans F G α).app K =
      F.mapDerivedCategory.map e.inv ≫ F.mapDerivedCategoryFactors.hom.app K₀ ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K₀) ≫
        G.mapDerivedCategoryFactors.inv.app K₀ ≫ G.mapDerivedCategory.map e.hom := by
  have hnat := (derivedNatTrans F G α).naturality e.hom
  rw [derivedNatTrans_app] at hnat
  rw [← Functor.mapIso_inv, Iso.eq_inv_comp, Functor.mapIso_hom, hnat]
  simp

end Derived

end CategoryTheory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (L M : C ⥤ C) [L.Additive] [M.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  (α : L ⟶ M) (β : M ⟶ 𝟭 C) (hαβ : ∀ F, α.app F ≫ β.app F = 0)
  (hSES : ∀ F, (ShortComplex.mk (α.app F) (β.app F) (hαβ F)).ShortExact)

include hSES

/-- **The distinguished triangle of a short exact sequence of exact endofunctors ending at the
identity.**  Let `L` and `M` be exact additive endofunctors of an abelian category `C`, and let
`α : L ⟶ M` and `β : M ⟶ 𝟭 C` be natural transformations for which `0 → L F → M F → F → 0` is
short exact for every object `F`.  Then every object `K` of the derived category of `C` fits
into a distinguished triangle
`L K ⟶ M K ⟶ K ⟶ (L K)[1]`
whose first two arrows are the natural transformations induced by `α` and `β`.

The connecting map is existential, as a distinguished triangle is not determined by its first
two arrows. -/
theorem exists_distTriang_of_natTrans_shortExact_toId (K : DerivedCategory C) :
    ∃ δ : K ⟶ (L.mapDerivedCategory.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk ((derivedNatTrans L M α).app K)
        ((M.mapDerivedCategoryTransToId β).app K) δ ∈ distTriang (DerivedCategory C) := by
  obtain ⟨K₀, ⟨e⟩⟩ : ∃ K₀ : CochainComplex C ℤ, Nonempty (DerivedCategory.Q.obj K₀ ≅ K) :=
    ⟨_, ⟨Q.objObjPreimageIso K⟩⟩
  have hzero : (NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K₀ ≫
      (Functor.mapCochainComplexTransToId β).app K₀ = 0 := by
    ext n
    simpa using hαβ (K₀.X n)
  have hSexact : (ShortComplex.mk
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K₀)
      ((Functor.mapCochainComplexTransToId β).app K₀) hzero).ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
    refine ShortComplex.shortExact_of_iso ?_ (hSES (K₀.X n))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  let εL : DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) ≅
      L.mapDerivedCategory.obj K :=
    (L.mapDerivedCategoryFactors.app K₀).symm ≪≫ L.mapDerivedCategory.mapIso e
  let εM : DerivedCategory.Q.obj ((M.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) ≅
      M.mapDerivedCategory.obj K :=
    (M.mapDerivedCategoryFactors.app K₀).symm ≪≫ M.mapDerivedCategory.mapIso e
  refine ⟨e.inv ≫ triangleOfSESδ hSexact ≫ (shiftFunctor (DerivedCategory C) (1 : ℤ)).map εL.hom,
    isomorphic_distinguished _ (triangleOfSES_distinguished hSexact) _
      (Triangle.isoMk _ _ εL.symm εM.symm e.symm ?_ ?_ ?_)⟩
  · dsimp [triangleOfSES, εL, εM]
    rw [derivedNatTrans_app_of_iso L M α e]
    simp
  · dsimp [triangleOfSES, εM]
    rw [Functor.mapDerivedCategoryTransToId_app_of_iso M β e]
    simp
  · dsimp [triangleOfSES]
    simp only [assoc, ← Functor.map_comp, Iso.hom_inv_id]
    simp

end DerivedCategory

end
