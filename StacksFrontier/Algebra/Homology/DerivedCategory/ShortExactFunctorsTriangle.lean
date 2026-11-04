module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# The distinguished triangle of a short exact sequence of exact endofunctors

Let `C` be an abelian category with a chosen derived category, let `L` and `R` be exact additive
endofunctors of `C`, and let `α : L ⟶ 𝟭 C` and `β : 𝟭 C ⟶ R` be natural transformations such
that `0 → L F → F → R F → 0` is short exact for every object `F` of `C`.  Then every object `K`
of the derived category of `C` sits in a distinguished triangle
`L K → K → R K → (L K)[1]`
whose first two arrows are the natural transformations induced by `α` and `β` on derived
categories.

The functors on derived categories are the ones induced by exactness,
`CategoryTheory.Functor.mapDerivedCategory`; nothing is right or left derived, because an exact
functor is computed termwise on any complex representing `K`.

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryTransToId`: the natural transformation
  `F.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C)` induced by `α : F ⟶ 𝟭 C` for exact `F`.
* `CategoryTheory.Functor.mapDerivedCategoryTransFromId`: the natural transformation
  `𝟭 (DerivedCategory C) ⟶ F.mapDerivedCategory` induced by `β : 𝟭 C ⟶ F` for exact `F`.

## Main results

* `DerivedCategory.exists_distTriang_of_natTrans_shortExact`: the distinguished triangle
  `L K ⟶ K ⟶ R K ⟶ (L K)[1]` in the derived category, with the first two arrows the induced
  natural transformations at `K`.
* `CategoryTheory.Functor.preservesEpimorphisms_of_epi_natTrans_app_from_id`: a functor receiving
  a natural transformation from the identity functor whose components are epimorphisms preserves
  epimorphisms.  Together with left exactness this makes such a functor exact, which is how the
  right-hand term of a short exact sequence of functors is seen to be exact.

## Implementation notes

An object `K` of the derived category is represented by a cochain complex `K₀` together with an
isomorphism `e : Q K₀ ≅ K`, using essential surjectivity of the localization functor
`DerivedCategory.Q`.  Applying `α` and `β` degreewise to `K₀` gives a short complex of cochain
complexes which is short exact because it is degreewise short exact
(`HomologicalComplex.shortExact_of_degreewise_shortExact`), so Mathlib's
`DerivedCategory.triangleOfSES` produces a distinguished triangle with vertices `Q (L K₀)`,
`Q K₀` and `Q (R K₀)`.  The comparison isomorphisms
`CategoryTheory.Functor.mapDerivedCategoryFactors` identify the outer vertices with
`L.mapDerivedCategory.obj K` and `R.mapDerivedCategory.obj K` after transport along `e`, and the
first two arrows then become the induced natural transformations at `K` by naturality.

The third arrow is produced existentially, as in the source: the connecting map of a
distinguished triangle is not determined by the first two arrows, so the statement names only
the two canonical ones.

The induced natural transformations are obtained from `CategoryTheory.Localization.liftNatTrans`
applied to the degreewise transformation of cochain complexes; the identity side uses the
lifting instance `CategoryTheory.Localization.Lifting.id`, which is why the component formulas
involve only one comparison isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe w v u

namespace CategoryTheory.Functor

section Degreewise

variable {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive]

/-- The transformation of cochain complexes, degreewise given by `α`, from the functor induced by
`F` to the identity functor. -/
def mapCochainComplexTransToId (α : F ⟶ 𝟭 C) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⟶ 𝟭 (CochainComplex C ℤ) :=
  NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).hom

/-- The transformation of cochain complexes, degreewise given by `β`, from the identity functor to
the functor induced by `F`. -/
def mapCochainComplexTransFromId (β : 𝟭 C ⟶ F) :
    𝟭 (CochainComplex C ℤ) ⟶ F.mapHomologicalComplex (ComplexShape.up ℤ) :=
  (Functor.mapHomologicalComplexIdIso C (ComplexShape.up ℤ)).inv ≫
    NatTrans.mapHomologicalComplex β (ComplexShape.up ℤ)

/-- In degree `n`, the component of `mapCochainComplexTransToId α` at `K` is `α.app (K.X n)`. -/
@[simp]
theorem mapCochainComplexTransToId_app_f (α : F ⟶ 𝟭 C) (K : CochainComplex C ℤ) (n : ℤ) :
    ((mapCochainComplexTransToId α).app K).f n = α.app (K.X n) := by
  simp [mapCochainComplexTransToId]

/-- In degree `n`, the component of `mapCochainComplexTransFromId β` at `K` is
`β.app (K.X n)`. -/
@[simp]
theorem mapCochainComplexTransFromId_app_f (β : 𝟭 C ⟶ F) (K : CochainComplex C ℤ) (n : ℤ) :
    ((mapCochainComplexTransFromId β).app K).f n = β.app (K.X n) := by
  simp [mapCochainComplexTransFromId]

end Degreewise

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The natural transformation `F.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C)` induced by a
natural transformation `α : F ⟶ 𝟭 C` out of an exact functor `F`.

Both functors are liftings through the localization functor `DerivedCategory.Q` of functors on
cochain complexes, so the degreewise transformation descends. -/
def mapDerivedCategoryTransToId (α : F ⟶ 𝟭 C) :
    F.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C) :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) DerivedCategory.Q
    F.mapDerivedCategory (𝟭 _)
    { app K := DerivedCategory.Q.map ((mapCochainComplexTransToId α).app K)
      naturality K L f := by
        dsimp
        rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
        exact congrArg _ ((mapCochainComplexTransToId α).naturality f) }

/-- The natural transformation `𝟭 (DerivedCategory C) ⟶ F.mapDerivedCategory` induced by a
natural transformation `β : 𝟭 C ⟶ F` into an exact functor `F`. -/
def mapDerivedCategoryTransFromId (β : 𝟭 C ⟶ F) :
    𝟭 (DerivedCategory C) ⟶ F.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    DerivedCategory.Q (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (𝟭 _) F.mapDerivedCategory
    { app K := DerivedCategory.Q.map ((mapCochainComplexTransFromId β).app K)
      naturality K L f := by
        dsimp
        rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
        exact congrArg _ ((mapCochainComplexTransFromId β).naturality f) }

/-- The component of `CategoryTheory.Functor.mapDerivedCategoryTransToId` at the image of a
cochain complex. -/
theorem mapDerivedCategoryTransToId_app (α : F ⟶ 𝟭 C) (K : CochainComplex C ℤ) :
    (F.mapDerivedCategoryTransToId α).app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((mapCochainComplexTransToId α).app K) := by
  rw [mapDerivedCategoryTransToId, Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

/-- The component of `CategoryTheory.Functor.mapDerivedCategoryTransFromId` at the image of a
cochain complex. -/
theorem mapDerivedCategoryTransFromId_app (β : 𝟭 C ⟶ F) (K : CochainComplex C ℤ) :
    (F.mapDerivedCategoryTransFromId β).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((mapCochainComplexTransFromId β).app K) ≫
        F.mapDerivedCategoryFactors.inv.app K := by
  rw [mapDerivedCategoryTransFromId, Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso]

/-- The component of `CategoryTheory.Functor.mapDerivedCategoryTransToId` at an object of the
derived category presented as the image of a cochain complex. -/
theorem mapDerivedCategoryTransToId_app_of_iso (α : F ⟶ 𝟭 C) {K₀ : CochainComplex C ℤ}
    {K : DerivedCategory C} (e : DerivedCategory.Q.obj K₀ ≅ K) :
    (F.mapDerivedCategoryTransToId α).app K =
      F.mapDerivedCategory.map e.inv ≫ F.mapDerivedCategoryFactors.hom.app K₀ ≫
        DerivedCategory.Q.map ((mapCochainComplexTransToId α).app K₀) ≫ e.hom := by
  have hnat := (F.mapDerivedCategoryTransToId α).naturality e.hom
  rw [mapDerivedCategoryTransToId_app] at hnat
  rw [← Functor.mapIso_inv, Iso.eq_inv_comp, Functor.mapIso_hom, hnat]
  simp

/-- The component of `CategoryTheory.Functor.mapDerivedCategoryTransFromId` at an object of the
derived category presented as the image of a cochain complex. -/
theorem mapDerivedCategoryTransFromId_app_of_iso (β : 𝟭 C ⟶ F) {K₀ : CochainComplex C ℤ}
    {K : DerivedCategory C} (e : DerivedCategory.Q.obj K₀ ≅ K) :
    (F.mapDerivedCategoryTransFromId β).app K =
      e.inv ≫ DerivedCategory.Q.map ((mapCochainComplexTransFromId β).app K₀) ≫
        F.mapDerivedCategoryFactors.inv.app K₀ ≫ F.mapDerivedCategory.map e.hom := by
  have hnat := (F.mapDerivedCategoryTransFromId β).naturality e.hom
  rw [mapDerivedCategoryTransFromId_app] at hnat
  rw [Iso.eq_inv_comp]
  simpa using hnat

end Derived

/-- A functor `F` receiving a natural transformation `β : 𝟭 C ⟶ F` all of whose components are
epimorphisms preserves epimorphisms: for `γ : X ⟶ Y` an epimorphism the composite `γ ≫ β.app Y`
is one, and naturality rewrites it as `β.app X ≫ F.map γ`, so `F.map γ` is an epimorphism. -/
theorem preservesEpimorphisms_of_epi_natTrans_app_from_id {C : Type u} [Category.{v} C]
    {F : C ⥤ C} (β : 𝟭 C ⟶ F) (hβ : ∀ X, Epi (β.app X)) : F.PreservesEpimorphisms where
  preserves {X Y} γ hγ := by
    have hsq : γ ≫ β.app Y = β.app X ≫ F.map γ := by simpa using β.naturality γ
    have h : Epi (γ ≫ β.app Y) := @epi_comp _ _ _ _ _ γ hγ _ (hβ Y)
    rw [hsq] at h
    exact epi_of_epi (β.app X) (F.map γ)

end CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (L R : C ⥤ C) [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (α : L ⟶ 𝟭 C) (β : 𝟭 C ⟶ R) (hαβ : ∀ F, α.app F ≫ β.app F = 0)
  (hSES : ∀ F, (ShortComplex.mk (α.app F) (β.app F) (hαβ F)).ShortExact)

include hSES

/-- **The distinguished triangle of a short exact sequence of exact endofunctors.**  Let `L` and
`R` be exact additive endofunctors of an abelian category `C`, and let `α : L ⟶ 𝟭 C` and
`β : 𝟭 C ⟶ R` be natural transformations for which `0 → L F → F → R F → 0` is short exact for
every object `F`.  Then every object `K` of the derived category of `C` fits into a
distinguished triangle
`L K ⟶ K ⟶ R K ⟶ (L K)[1]`
whose first two arrows are the natural transformations induced by `α` and `β`.

The connecting map is existential, as in the source: a distinguished triangle is not determined
by its first two arrows. -/
theorem exists_distTriang_of_natTrans_shortExact (K : DerivedCategory C) :
    ∃ δ : R.mapDerivedCategory.obj K ⟶ (L.mapDerivedCategory.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk ((L.mapDerivedCategoryTransToId α).app K)
        ((R.mapDerivedCategoryTransFromId β).app K) δ ∈ distTriang (DerivedCategory C) := by
  obtain ⟨K₀, ⟨e⟩⟩ : ∃ K₀ : CochainComplex C ℤ, Nonempty (DerivedCategory.Q.obj K₀ ≅ K) :=
    ⟨_, ⟨Q.objObjPreimageIso K⟩⟩
  have hzero : (Functor.mapCochainComplexTransToId α).app K₀ ≫
      (Functor.mapCochainComplexTransFromId β).app K₀ = 0 := by
    ext n
    simpa using hαβ (K₀.X n)
  have hSexact : (ShortComplex.mk ((Functor.mapCochainComplexTransToId α).app K₀)
      ((Functor.mapCochainComplexTransFromId β).app K₀) hzero).ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
    refine ShortComplex.shortExact_of_iso ?_ (hSES (K₀.X n))
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  let εL : DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) ≅
      L.mapDerivedCategory.obj K :=
    (L.mapDerivedCategoryFactors.app K₀).symm ≪≫ L.mapDerivedCategory.mapIso e
  let εR : DerivedCategory.Q.obj ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀) ≅
      R.mapDerivedCategory.obj K :=
    (R.mapDerivedCategoryFactors.app K₀).symm ≪≫ R.mapDerivedCategory.mapIso e
  refine ⟨εR.inv ≫ triangleOfSESδ hSexact ≫ (shiftFunctor (DerivedCategory C) (1 : ℤ)).map εL.hom,
    isomorphic_distinguished _ (triangleOfSES_distinguished hSexact) _
      (Triangle.isoMk _ _ εL.symm e.symm εR.symm ?_ ?_ ?_)⟩
  · dsimp [triangleOfSES, εL]
    rw [Functor.mapDerivedCategoryTransToId_app_of_iso L α e]
    simp
  · dsimp [triangleOfSES, εR]
    rw [Functor.mapDerivedCategoryTransFromId_app_of_iso R β e]
    simp
  · dsimp [triangleOfSES]
    simp only [assoc, ← Functor.map_comp, Iso.hom_inv_id]
    simp

end DerivedCategory

end
