module

public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# The total complex of a bifunctor, with regular kernel reducibility hints

Mathlib's `HomologicalComplex.HasMapBifunctor` and `HomologicalComplex.mapBifunctor` are
`abbrev`s, so the kernel gives them `abbrev` reducibility hints. When it compares two
applications of one constant, the kernel compares their arguments first only if that constant
has a *regular* hint. Two applications of these `abbrev`s whose arguments are spelled
differently are therefore unfolded on both sides. When the bifunctor is the tensor product of
sheaves of modules, the kernel then evaluates the sheafification inside it.

This file gives the four constants copies that are `@[reducible] def`s. The elaborator unfolds
a reducible definition exactly as it unfolds an `abbrev`, so instance search, `simp` and `dsimp`
see through the copies; the kernel sees regular hints. A copy only helps when it meets another
copy: compared with Mathlib's `abbrev`, it is unfolded as before.

## Main definitions

* `HomologicalComplex.HasMapBifunctorReg`, `HomologicalComplex.mapBifunctorReg` and
  `HomologicalComplex.mapBifunctorMapReg`: copies of `HasMapBifunctor`, `mapBifunctor` and
  `mapBifunctorMap`, the last one typed between copies.
* `CategoryTheory.Functor.map₂HomologicalComplexReg`: `Functor.map₂HomologicalComplex`, with
  objects `mapBifunctorReg` and morphisms `mapBifunctorMapReg`.
* The `CommShift` instances of Mathlib's `Functor.map₂CochainComplex`, read at
  `map₂HomologicalComplexReg`. The copy is a different constant, so instance search does not
  find Mathlib's instances for it.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

/-- `HasMapBifunctor`, with a regular kernel reducibility hint. -/
@[reducible] def HasMapBifunctorReg : Prop := HasMapBifunctor K₁ K₂ F c

variable [HasMapBifunctorReg K₁ K₂ F c] [HasMapBifunctorReg L₁ L₂ F c] [DecidableEq J]

/-- `mapBifunctor`, with a regular kernel reducibility hint. -/
@[reducible] def mapBifunctorReg : HomologicalComplex D c := mapBifunctor K₁ K₂ F c

variable {K₁ K₂ L₁ L₂}

/-- `mapBifunctorMap`, typed between the `mapBifunctorReg` copies. -/
@[reducible] def mapBifunctorMapReg : mapBifunctorReg K₁ K₂ F c ⟶ mapBifunctorReg L₁ L₂ F c :=
  mapBifunctorMap f₁ f₂ F c

end HomologicalComplex

namespace CategoryTheory.Functor

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c : ComplexShape J)
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]

open HomologicalComplex

/-- `Functor.map₂HomologicalComplex`, with objects `mapBifunctorReg` and morphisms
`mapBifunctorMapReg`. -/
@[simps]
def map₂HomologicalComplexReg
    [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
      HasMapBifunctorReg K₁ K₂ F c] :
    HomologicalComplex C₁ c₁ ⥤ HomologicalComplex C₂ c₂ ⥤ HomologicalComplex D c where
  obj K₁ :=
    { obj K₂ := mapBifunctorReg K₁ K₂ F c
      map g := mapBifunctorMapReg (𝟙 K₁) g F c
      map_id K₂ := ((F.map₂HomologicalComplex c₁ c₂ c).obj K₁).map_id K₂
      map_comp g g' := ((F.map₂HomologicalComplex c₁ c₂ c).obj K₁).map_comp g g' }
  map f :=
    { app K₂ := mapBifunctorMapReg f (𝟙 K₂) F c
      naturality _ _ g := ((F.map₂HomologicalComplex c₁ c₂ c).map f).naturality g }
  map_id K₁ := (F.map₂HomologicalComplex c₁ c₂ c).map_id K₁
  map_comp f f' := (F.map₂HomologicalComplex c₁ c₂ c).map_comp f f'

end CategoryTheory.Functor

/-! ### Shifts -/

namespace CategoryTheory.Functor

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ F (.up ℤ)]

/-- Mathlib's shift on `F.map₂CochainComplex.obj K₁`, read at the copy. -/
instance map₂HomologicalComplexReg_obj_commShift (K₁ : CochainComplex C₁ ℤ) :
    ((F.map₂HomologicalComplexReg (.up ℤ) (.up ℤ) (.up ℤ)).obj K₁).CommShift ℤ :=
  inferInstanceAs ((F.map₂CochainComplex.obj K₁).CommShift ℤ)

/-- Mathlib's shift compatibility of `F.map₂CochainComplex.map f`, read at the copy. -/
instance map₂HomologicalComplexReg_map_commShift {K₁ L₁ : CochainComplex C₁ ℤ} (f : K₁ ⟶ L₁) :
    NatTrans.CommShift ((F.map₂HomologicalComplexReg (.up ℤ) (.up ℤ) (.up ℤ)).map f) ℤ :=
  inferInstanceAs (NatTrans.CommShift (F.map₂CochainComplex.map f) ℤ)

/-- Mathlib's shift on `F.map₂CochainComplex.flip.obj K₂`, read at the copy. -/
instance map₂HomologicalComplexReg_flip_obj_commShift (K₂ : CochainComplex C₂ ℤ) :
    ((F.map₂HomologicalComplexReg (.up ℤ) (.up ℤ) (.up ℤ)).flip.obj K₂).CommShift ℤ :=
  inferInstanceAs ((F.map₂CochainComplex.flip.obj K₂).CommShift ℤ)

/-- Mathlib's shift compatibility of `F.map₂CochainComplex.flip.map g`, read at the copy. -/
instance map₂HomologicalComplexReg_flip_map_commShift {K₂ L₂ : CochainComplex C₂ ℤ}
    (g : K₂ ⟶ L₂) :
    NatTrans.CommShift ((F.map₂HomologicalComplexReg (.up ℤ) (.up ℤ) (.up ℤ)).flip.map g) ℤ :=
  inferInstanceAs (NatTrans.CommShift (F.map₂CochainComplex.flip.map g) ℤ)

/-- Mathlib's `CommShift₂Int` structure on `F.map₂CochainComplex`, read at the copy. -/
instance map₂HomologicalComplexReg_commShift₂Int :
    (F.map₂HomologicalComplexReg (.up ℤ) (.up ℤ) (.up ℤ)).CommShift₂Int :=
  inferInstanceAs F.map₂CochainComplex.CommShift₂Int

end CategoryTheory.Functor
