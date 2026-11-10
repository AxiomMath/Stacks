module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfComplexes
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.InjectiveHom

/-!
# The derived canonical map of a square, and its triangle on derived objects

Given a square of objects of a site, this file descends the canonical map `I(X) ⟶ C(β)[-1]` of
[Stacks, Tag 0F16], from the sections over the fourth corner to the mapping cocone of the
signed restriction map, to the derived category of sheaves of modules, and builds the triangle
on derived sections, which is distinguished wherever the canonical map is invertible.

## Main definitions

* `Stacks.MayerVietoris.CanonicalMapOfComplexes.biprodComplexFunctor`,
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.coconeComplexFunctor`: the degreewise biproduct
  of the sections over the two middle corners, and the mapping cocone of the signed restriction
  map, as functors of the complex of module sheaves.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.firstMapNatTrans`,
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.secondMapNatTrans`,
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquareNatTrans`,
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.coconeFstNatTrans`,
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.coconeBoundaryNatTrans`: the five chain-level
  maps, as natural transformations between those functors.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.DerivedSectionsData`: a system of right derived
  section functors over the objects of the site, with its units, its right-derived-functor
  property, the invertibility of the units on K-injective complexes, and compatibility with
  restriction.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.DerivedCSquareData`: the descended canonical map
  together with the mapping-cocone projection and boundary, specified by their computations on
  K-injective representatives.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.DerivedCSquareData.cSquareTriangle`: the
  triangle on derived sections, with the boundary obtained using the inverse of the canonical
  map.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedSectionsData`: a `DerivedSectionsData`,
  built from Spaltenstein's unbounded right derived functors.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData`: a `DerivedCSquareData`,
  built from the same derived functors.

## Main results

* `Stacks.MayerVietoris.CanonicalMapOfComplexes.mappingCocone_triangle_mor₃_naturality`: the
  mapping-cocone boundary is natural in the complex.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.DerivedCSquareData.isCSquareIso_iff_quasiIso`:
  for any such data, the derived isomorphism condition can be tested on any K-injective
  representative.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.DerivedCSquareData.cSquareTriangle_functorial`:
  for any such data, every derived morphism induces a unique morphism of the derived triangles
  with the expected three components.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.DerivedCSquareData.cSquareTriangle_distinguished`
  and `Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquareTriangle_distinguished`: the
  derived-section triangle is a distinguished triangle of `D(Ab)` at every derived object where
  the canonical map is invertible.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.invertsQuasiIso_sectionsComplex`,
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.invertsQuasiIso_coconeComplexFunctor`,
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.hasRightDerivedFunctor_sectionsComplex` and
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.hasRightDerivedFunctor_coconeComplexFunctor`:
  degreewise sections and the mapping cocone invert quasi-isomorphisms between K-injective
  complexes, hence have unbounded right derived functors.
* `Stacks.MayerVietoris.CanonicalMapOfComplexes.exists_kInjectiveResolution` and
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.exists_kInjective_iso`: every complex of sheaves
  of modules has a K-injective resolution, and every object of the derived category is
  represented by a K-injective complex.

## Implementation notes

The construction is stated in the `General` namespace for an arbitrary contravariant system
`S : ιᵒᵖ ⥤ (A ⥤ B)` of additive section functors between abelian categories carrying derived
categories, together with a square of objects of `ι`; the per-corner sections are
`S.obj (op U)` and restriction is `S.map f.op`. The site-theoretic statements are that
construction at `sectionsSystem`, the system of sections functors of the site, and the two
structures `DerivedSectionsData` and `DerivedCSquareData` are abbreviations of the general ones.

The derived functors are the unbounded ones of [Stacks, Tag 079P], which need the coefficient
category to be Grothendieck abelian. The `Construction` sections assume
`IsGrothendieckAbelian`, and the declarations stated under `UnivLE` discharge it with
`SheafOfModules.isGrothendieckAbelian_of_univLE`.

Each of the three descended natural transformations is a `Functor.rightDerivedDesc`, which asks
only the source to be a right derived functor, so the pointwise biproduct functor on `D(𝒪)` is
never presented as one.

## References

* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pretriangulated

universe u v w r t

namespace Stacks.MayerVietoris.CanonicalMapOfComplexes

open CochainComplex.FilteredInjective.Hom (biprod_map_id)


open MappingCoconeAux

section BiprodMap

variable {V : Type*} [Category V] [Preadditive V]

/-- The biproduct of two composites is the composite of the biproducts. -/
theorem biprod_map_comp {X Y Z X' Y' Z' : V} [HasBinaryBiproduct X X']
    [HasBinaryBiproduct Y Y'] [HasBinaryBiproduct Z Z'] (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y')
    (g' : Y' ⟶ Z') : biprod.map (f ≫ g) (f' ≫ g') = biprod.map f f' ≫ biprod.map g g' := by
  apply biprod.hom_ext <;> simp

variable [HasBinaryBiproducts V]

/-- The biproduct of two isomorphisms is an isomorphism. -/
theorem isIso_biprod_map {X Y X' Y' : V} (f : X ⟶ X') (g : Y ⟶ Y') [IsIso f] [IsIso g] :
    IsIso (biprod.map f g) :=
  ⟨biprod.map (inv f) (inv g), by apply biprod.hom_ext <;> simp,
    by apply biprod.hom_ext <;> simp⟩

/-- A common factor can be pulled out of a lift. -/
theorem comp_lift {X T A B : V} (f : X ⟶ T) (g : T ⟶ A) (h : T ⟶ B) :
    biprod.lift (f ≫ g) (f ≫ h) = f ≫ biprod.lift g h := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp

end BiprodMap

section BiprodFunctor

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {W' : Type*} [Category W'] [Preadditive W'] [HasBinaryBiproducts W']

/-- An additive functor inverts the comparison from its value on a biproduct to the biproduct
of its values. -/
theorem isIso_biprod_lift_map_fst_snd (F : V ⥤ W') [F.Additive] (A B : V) :
    IsIso (biprod.lift (F.map (biprod.fst : A ⊞ B ⟶ A))
      (F.map (biprod.snd : A ⊞ B ⟶ B))) := by
  refine ⟨biprod.desc (F.map (biprod.inl : A ⟶ A ⊞ B)) (F.map (biprod.inr : B ⟶ A ⊞ B)),
    ?_, ?_⟩
  · rw [biprod.lift_desc, ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  · refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [← F.map_comp]

/-- The image of a lift, followed by the biproduct comparison twisted by two maps, is the lift
of the twisted images. -/
theorem map_lift_comp_lift (F : V ⥤ W') [F.Additive] {T A B : V} (a : T ⟶ A) (b : T ⟶ B)
    {A' B' : W'} (x : F.obj A ⟶ A') (y : F.obj B ⟶ B') :
    F.map (biprod.lift a b) ≫
        biprod.lift (F.map (biprod.fst : A ⊞ B ⟶ A) ≫ x)
          (F.map (biprod.snd : A ⊞ B ⟶ B) ≫ y) =
      biprod.lift (F.map a ≫ x) (F.map b ≫ y) := by
  refine biprod.hom_ext _ _ ?_ ?_
  · simp only [Category.assoc, biprod.lift_fst]
    rw [← Category.assoc, ← F.map_comp, biprod.lift_fst]
  · simp only [Category.assoc, biprod.lift_snd]
    rw [← Category.assoc, ← F.map_comp, biprod.lift_snd]

/-- The image of a desc, followed by a map, read through the biproduct comparison twisted by
two maps.  The two hypotheses are the comparison on each summand. -/
theorem map_desc_comp (F : V ⥤ W') [F.Additive] {A B T : V} (a : A ⟶ T) (b : B ⟶ T)
    {T' A' B' : W'} (z : F.obj T ⟶ T') (x : F.obj A ⟶ A') (y : F.obj B ⟶ B')
    (c : A' ⟶ T') (d : B' ⟶ T') (hc : F.map a ≫ z = x ≫ c) (hd : F.map b ≫ z = y ≫ d) :
    F.map (biprod.desc a b) ≫ z =
      biprod.lift (F.map (biprod.fst : A ⊞ B ⟶ A) ≫ x)
        (F.map (biprod.snd : A ⊞ B ⟶ B) ≫ y) ≫ biprod.desc c d := by
  rw [biprod.lift_desc, biprod.desc_eq, F.map_add, F.map_comp, F.map_comp,
    Preadditive.add_comp]
  simp only [Category.assoc]
  rw [hc, hd]

end BiprodFunctor

section ConeGeneric

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]

/-- The boundary of the mapping-cocone triangle, in terms of the right inclusion of the
mapping cone and the shift comparison. -/
theorem mappingCocone_triangle_mor₃_eq {K L : CochainComplex V ℤ} (φ : K ⟶ L) :
    (CochainComplex.mappingCocone.triangle φ).mor₃ =
      CochainComplex.mappingCone.inr φ ≫
        (shiftFunctorCompIsoId (CochainComplex V ℤ) (-1 : ℤ) 1 (by lia)).inv.app
          (CochainComplex.mappingCone φ) := rfl

/-- The right inclusion into a mapping cone is compatible with the map of mapping cones
induced by a commutative square. -/
theorem inr_comp_coneMap {K₁ L₁ K₂ L₂ : CochainComplex V ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) :
    CochainComplex.mappingCone.inr φ₁ ≫ CochainComplex.mappingCone.map φ₁ φ₂ a b comm =
      b ≫ CochainComplex.mappingCone.inr φ₂ := by
  simp [CochainComplex.mappingCone.map]

end ConeGeneric

namespace General

section Chain

variable {ι : Type*} [Category* ι]
  {A : Type*} [Category* A] [Preadditive A]
  {B : Type*} [Category* B] [Preadditive B] [HasBinaryBiproducts B]
  (S : ιᵒᵖ ⥤ (A ⥤ B)) [∀ X : ιᵒᵖ, (S.obj X).Additive] (sq : Square ι)

/-- The degreewise biproduct of the sections over the two middle corners of the square,
as a functor of the complex. -/
noncomputable def biprodComplexFunctor : CochainComplex A ℤ ⥤ CochainComplex B ℤ where
  obj I := (complexFunctor S sq.X₃).obj I ⊞ (complexFunctor S sq.X₂).obj I
  map f := biprod.map ((complexFunctor S sq.X₃).map f) ((complexFunctor S sq.X₂).map f)
  map_id I := by apply biprod.hom_ext <;> simp
  map_comp f g := by apply biprod.hom_ext <;> simp

/-- The first map, as a natural transformation of functors of the complex. -/
noncomputable def firstMapNatTrans : complexFunctor S sq.X₄ ⟶ biprodComplexFunctor S sq where
  app I := firstMap S sq I
  naturality _ _ f := firstMap_natural S sq f

/-- The signed second map, as a natural transformation of functors of the complex. -/
noncomputable def secondMapNatTrans : biprodComplexFunctor S sq ⟶ complexFunctor S sq.X₁ where
  app I := secondMap S sq I
  naturality _ _ f := (secondMapArrowMap S sq f).w

/-- The induced map of mapping cocones of an identity is the identity. -/
theorem mappingCoconeMap_id (I : CochainComplex A ℤ) :
    mappingCoconeMap S sq (𝟙 I) = 𝟙 (CochainComplex.mappingCocone (secondMap S sq I)) := by
  refine hom_ext _ (fun p => ?_) (fun p => ?_)
  · rw [mappingCoconeMap_f_fst_f, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, biprod_map_id]
    simp
  · rw [mappingCoconeMap_f_snd_v, CategoryTheory.Functor.map_id]
    simp

/-- The induced maps of mapping cocones compose. -/
theorem mappingCoconeMap_comp {I I' I'' : CochainComplex A ℤ} (f : I ⟶ I') (g : I' ⟶ I'') :
    mappingCoconeMap S sq (f ≫ g) = mappingCoconeMap S sq f ≫ mappingCoconeMap S sq g := by
  refine hom_ext _ (fun p => ?_) (fun p => ?_)
  · rw [mappingCoconeMap_f_fst_f, HomologicalComplex.comp_f, Category.assoc,
      mappingCoconeMap_f_fst_f, ← Category.assoc, mappingCoconeMap_f_fst_f, Category.assoc,
      Functor.map_comp, Functor.map_comp, biprod_map_comp, HomologicalComplex.comp_f]
  · rw [mappingCoconeMap_f_snd_v, HomologicalComplex.comp_f, Category.assoc,
      mappingCoconeMap_f_snd_v, ← Category.assoc, mappingCoconeMap_f_snd_v, Category.assoc,
      Functor.map_comp, HomologicalComplex.comp_f]

/-- The mapping cocone of the signed second map, as a functor of the complex. -/
noncomputable def coconeComplexFunctor : CochainComplex A ℤ ⥤ CochainComplex B ℤ where
  obj I := CochainComplex.mappingCocone (secondMap S sq I)
  map f := mappingCoconeMap S sq f
  map_id I := mappingCoconeMap_id S sq I
  map_comp f g := mappingCoconeMap_comp S sq f g

/-- The value of `biprodComplexFunctor` on a complex. -/
@[simp]
theorem biprodComplexFunctor_obj (I : CochainComplex A ℤ) :
    (biprodComplexFunctor S sq).obj I =
      ((complexFunctor S sq.X₃).obj I ⊞ (complexFunctor S sq.X₂).obj I) := rfl

/-- The value of `biprodComplexFunctor` on a morphism. -/
@[simp]
theorem biprodComplexFunctor_map {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    (biprodComplexFunctor S sq).map f =
      biprod.map ((complexFunctor S sq.X₃).map f) ((complexFunctor S sq.X₂).map f) := rfl

/-- The value of `coconeComplexFunctor` on a complex. -/
@[simp]
theorem coconeComplexFunctor_obj (I : CochainComplex A ℤ) :
    (coconeComplexFunctor S sq).obj I = CochainComplex.mappingCocone (secondMap S sq I) := rfl

/-- The value of `coconeComplexFunctor` on a morphism. -/
@[simp]
theorem coconeComplexFunctor_map {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    (coconeComplexFunctor S sq).map f = mappingCoconeMap S sq f := rfl

/-- The projection onto the sections over the third corner, as a natural transformation. -/
noncomputable def biprodFstNatTrans :
    biprodComplexFunctor S sq ⟶ complexFunctor S sq.X₃ where
  app _ := biprod.fst
  naturality _ _ _ := biprod.map_fst _ _

/-- The projection onto the sections over the second corner, as a natural transformation. -/
noncomputable def biprodSndNatTrans :
    biprodComplexFunctor S sq ⟶ complexFunctor S sq.X₂ where
  app _ := biprod.snd
  naturality _ _ _ := biprod.map_snd _ _

/-- The canonical map of complexes, as a natural transformation. -/
noncomputable def cSquareNatTrans : complexFunctor S sq.X₄ ⟶ coconeComplexFunctor S sq where
  app I := cSquare S sq I
  naturality _ _ f := cSquare_natural S sq f

/-- The canonical map of complexes followed by the mapping-cocone projection is the first
map: this is the defining property of the lift. -/
theorem cSquare_comp_fst (I : CochainComplex A ℤ) :
    cSquare S sq I ≫ CochainComplex.mappingCocone.fst (secondMap S sq I) = firstMap S sq I :=
  CochainComplex.mappingCocone.lift_fst _ _ _ _

/-- The induced map of mapping cocones is compatible with the first projections. -/
theorem mappingCoconeMap_comp_fst {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    mappingCoconeMap S sq f ≫ CochainComplex.mappingCocone.fst (secondMap S sq I') =
      CochainComplex.mappingCocone.fst (secondMap S sq I) ≫
        biprod.map ((complexFunctor S sq.X₃).map f) ((complexFunctor S sq.X₂).map f) :=
  HomologicalComplex.hom_ext _ _ (fun p => mappingCoconeMap_f_fst_f S sq f p)

/-- The mapping-cocone projection, as a natural transformation. -/
noncomputable def coconeFstNatTrans :
    coconeComplexFunctor S sq ⟶ biprodComplexFunctor S sq where
  app I := CochainComplex.mappingCocone.fst (secondMap S sq I)
  naturality _ _ f := mappingCoconeMap_comp_fst S sq f

/-- The commutative square underlying the morphism of signed restriction arrows. -/
theorem secondMap_square {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    secondMap S sq I ≫ (complexFunctor S sq.X₁).map f =
      biprod.map ((complexFunctor S sq.X₃).map f) ((complexFunctor S sq.X₂).map f) ≫
        secondMap S sq I' :=
  (secondMapArrowMap S sq f).w.symm

/-- The induced map of mapping cocones is the shift of the induced map of mapping cones. -/
theorem mappingCoconeMap_eq_shift_coneMap {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    mappingCoconeMap S sq f =
      (shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).map
        (CochainComplex.mappingCone.map (secondMap S sq I) (secondMap S sq I')
          (biprod.map ((complexFunctor S sq.X₃).map f) ((complexFunctor S sq.X₂).map f))
          ((complexFunctor S sq.X₁).map f) (secondMap_square S sq f)) :=
  congrArg (shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).map
    (mapArrowHom_eq_coneMap _ _ _ (secondMapArrowMap S sq f))

/-- Naturality of the mapping-cone right inclusion followed by the shift comparison, in the
spelling in which both sides are compositions of maps of mapping cones. -/
theorem inr_comp_shiftComparison_naturality {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    (complexFunctor S sq.X₁).map f ≫ CochainComplex.mappingCone.inr (secondMap S sq I') ≫
        (shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1 (by lia)).inv.app
          (CochainComplex.mappingCone (secondMap S sq I')) =
      (CochainComplex.mappingCone.inr (secondMap S sq I) ≫
          (shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1 (by lia)).inv.app
            (CochainComplex.mappingCone (secondMap S sq I))) ≫
        (shiftFunctor (CochainComplex B ℤ) (1 : ℤ)).map
          ((shiftFunctor (CochainComplex B ℤ) (-1 : ℤ)).map
            (CochainComplex.mappingCone.map (secondMap S sq I) (secondMap S sq I')
              (biprod.map ((complexFunctor S sq.X₃).map f) ((complexFunctor S sq.X₂).map f))
              ((complexFunctor S sq.X₁).map f) (secondMap_square S sq f))) := by
  have hinr := inr_comp_coneMap (secondMap S sq I) (secondMap S sq I')
    (biprod.map ((complexFunctor S sq.X₃).map f) ((complexFunctor S sq.X₂).map f))
    ((complexFunctor S sq.X₁).map f) (secondMap_square S sq f)
  rw [← Category.assoc, ← hinr, Category.assoc, Category.assoc]
  exact congrArg (fun z => CochainComplex.mappingCone.inr (secondMap S sq I) ≫ z)
    ((shiftFunctorCompIsoId (CochainComplex B ℤ) (-1 : ℤ) 1 (by lia)).inv.naturality _)

/-- The boundary of the mapping-cocone triangle is natural in the complex. -/
theorem mappingCocone_triangle_mor₃_naturality {I I' : CochainComplex A ℤ} (f : I ⟶ I') :
    (complexFunctor S sq.X₁).map f ≫
        (CochainComplex.mappingCocone.triangle (secondMap S sq I')).mor₃ =
      (CochainComplex.mappingCocone.triangle (secondMap S sq I)).mor₃ ≫
        (shiftFunctor (CochainComplex B ℤ) (1 : ℤ)).map (mappingCoconeMap S sq f) := by
  have h := inr_comp_shiftComparison_naturality S sq f
  rwa [← mappingCoconeMap_eq_shift_coneMap] at h

/-- The mapping-cocone boundary, as a natural transformation. -/
noncomputable def coconeBoundaryNatTrans :
    complexFunctor S sq.X₁ ⟶
      coconeComplexFunctor S sq ⋙ shiftFunctor (CochainComplex B ℤ) (1 : ℤ) where
  app I := (CochainComplex.mappingCocone.triangle (secondMap S sq I)).mor₃
  naturality _ _ f := mappingCocone_triangle_mor₃_naturality S sq f

end Chain

section Derived

variable {ι : Type*} [Category* ι]
  {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (S : ιᵒᵖ ⥤ (A ⥤ B)) [∀ X : ιᵒᵖ, (S.obj X).Additive] (sq : Square ι)

/-- A system of right derived section functors, with the canonical units and restriction maps. -/
structure DerivedSectionsData where
  /-- Derived sections, contravariantly in the index. -/
  functor : ιᵒᵖ ⥤ (DerivedCategory A ⥤ DerivedCategory B)
  /-- The unit from ordinary to derived sections. -/
  unit (U : ι) : complexFunctor S U ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ functor.obj (op U)
  /-- Each section functor is the right derived functor of degreewise sections. -/
  isRightDerivedFunctor (U : ι) :
    (functor.obj (op U)).IsRightDerivedFunctor (unit U)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  /-- K-injective complexes compute the derived sections. -/
  isIso_unit_app (U : ι) (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso ((unit U).app I)
  /-- The units commute with restriction along every morphism of the index. -/
  unit_restriction {U V : ι} (f : U ⟶ V) (I : CochainComplex A ℤ) :
    DerivedCategory.Q.map ((restrictionComplex S f).app I) ≫ (unit U).app I =
      (unit V).app I ≫ (functor.map f.op).app (DerivedCategory.Q.obj I)

attribute [instance] DerivedSectionsData.isRightDerivedFunctor
  DerivedSectionsData.isIso_unit_app

namespace DerivedSectionsData

variable {S}
variable (D : DerivedSectionsData S)

/-- The functor `RΓ(Z, -) ⊞ RΓ(Y, -)`, with its pointwise biproduct model. -/
noncomputable def biprodFunctor : DerivedCategory A ⥤ DerivedCategory B where
  obj K := (D.functor.obj (op sq.X₃)).obj K ⊞ (D.functor.obj (op sq.X₂)).obj K
  map f := biprod.map ((D.functor.obj (op sq.X₃)).map f) ((D.functor.obj (op sq.X₂)).map f)
  map_id K := by apply biprod.hom_ext <;> simp
  map_comp f g := by apply biprod.hom_ext <;> simp

@[simp]
theorem biprodFunctor_map {K K' : DerivedCategory A} (f : K ⟶ K') :
    (D.biprodFunctor sq).map f =
      biprod.map ((D.functor.obj (op sq.X₃)).map f) ((D.functor.obj (op sq.X₂)).map f) := rfl

/-- The comparison from localized sections of the biproduct to derived sections. -/
noncomputable def biprodComparison (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((complexFunctor S sq.X₃).obj I ⊞ (complexFunctor S sq.X₂).obj I) ⟶
      (D.biprodFunctor sq).obj (DerivedCategory.Q.obj I) :=
  biprod.lift
    (DerivedCategory.Q.map (biprod.fst : (complexFunctor S sq.X₃).obj I ⊞
      (complexFunctor S sq.X₂).obj I ⟶ _) ≫ (D.unit sq.X₃).app I)
    (DerivedCategory.Q.map (biprod.snd : (complexFunctor S sq.X₃).obj I ⊞
      (complexFunctor S sq.X₂).obj I ⟶ _) ≫ (D.unit sq.X₂).app I)

/-- A natural transformation into the pointwise biproduct functor, from its two legs. -/
noncomputable def liftNatTrans {E : Type*} [Category* E]
    {F : E ⥤ DerivedCategory B} {T : E ⥤ DerivedCategory A}
    (p : F ⟶ T ⋙ D.functor.obj (op sq.X₃)) (q : F ⟶ T ⋙ D.functor.obj (op sq.X₂)) :
    F ⟶ T ⋙ D.biprodFunctor sq where
  app K := biprod.lift (p.app K) (q.app K)
  naturality K K' f := by
    have hp := p.naturality f
    have hq := q.naturality f
    simp only [Functor.comp_map] at hp hq
    change F.map f ≫ biprod.lift (p.app K') (q.app K') =
      biprod.lift (p.app K) (q.app K) ≫
        biprod.map ((D.functor.obj (op sq.X₃)).map (T.map f))
          ((D.functor.obj (op sq.X₂)).map (T.map f))
    refine biprod.hom_ext _ _ ?_ ?_
    · simp [hp]
    · simp [hq]

/-- The comparison from localized sections of the degreewise biproduct to derived sections,
as a natural transformation of functors of the complex. -/
noncomputable def biprodComparisonNatTrans :
    biprodComplexFunctor S sq ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ D.biprodFunctor sq :=
  D.liftNatTrans sq
    (Functor.whiskerRight (biprodFstNatTrans S sq) DerivedCategory.Q ≫ D.unit sq.X₃)
    (Functor.whiskerRight (biprodSndNatTrans S sq) DerivedCategory.Q ≫ D.unit sq.X₂)

/-- The component of `biprodComparisonNatTrans` at a complex is `biprodComparison`. -/
theorem biprodComparisonNatTrans_app (I : CochainComplex A ℤ) :
    (D.biprodComparisonNatTrans sq).app I = D.biprodComparison sq I := rfl

/-- The first map on derived sections. -/
noncomputable def firstMap (K : DerivedCategory A) :
    (D.functor.obj (op sq.X₄)).obj K ⟶ (D.biprodFunctor sq).obj K :=
  biprod.lift ((D.functor.map sq.f₃₄.op).app K) ((D.functor.map sq.f₂₄.op).app K)

/-- The signed second map on derived sections. -/
noncomputable def secondMap (K : DerivedCategory A) :
    (D.biprodFunctor sq).obj K ⟶ (D.functor.obj (op sq.X₁)).obj K :=
  biprod.desc ((D.functor.map sq.f₁₃.op).app K) (-((D.functor.map sq.f₁₂.op).app K))

/-- The first map on derived sections is natural in the derived object. -/
theorem firstMap_naturality {K K' : DerivedCategory A} (f : K ⟶ K') :
    D.firstMap sq K ≫ (D.biprodFunctor sq).map f =
      (D.functor.obj (op sq.X₄)).map f ≫ D.firstMap sq K' := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp [DerivedSectionsData.firstMap, DerivedSectionsData.biprodFunctor,
      NatTrans.naturality]

/-- The signed second map on derived sections is natural in the derived object. -/
theorem secondMap_naturality {K K' : DerivedCategory A} (f : K ⟶ K') :
    D.secondMap sq K ≫ (D.functor.obj (op sq.X₁)).map f =
      (D.biprodFunctor sq).map f ≫ D.secondMap sq K' := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;>
    simp [DerivedSectionsData.secondMap, DerivedSectionsData.biprodFunctor,
      NatTrans.naturality]

/-- The biproduct comparison factors through the localization's own comparison from the
localized biproduct to the biproduct of the localizations. -/
theorem biprodComparison_eq (I : CochainComplex A ℤ) :
    D.biprodComparison sq I =
      biprod.lift (DerivedCategory.Q.map (biprod.fst :
          (complexFunctor S sq.X₃).obj I ⊞ (complexFunctor S sq.X₂).obj I ⟶ _))
        (DerivedCategory.Q.map (biprod.snd :
          (complexFunctor S sq.X₃).obj I ⊞ (complexFunctor S sq.X₂).obj I ⟶ _)) ≫
        biprod.map ((D.unit sq.X₃).app I) ((D.unit sq.X₂).app I) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp [DerivedSectionsData.biprodComparison]

/-- The biproduct comparison is invertible on a K-injective complex. -/
theorem isIso_biprodComparison (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso (D.biprodComparison sq I) := by
  have h₁ := isIso_biprod_lift_map_fst_snd (DerivedCategory.Q (C := B))
    ((complexFunctor S sq.X₃).obj I) ((complexFunctor S sq.X₂).obj I)
  have h₂ := isIso_biprod_map ((D.unit sq.X₃).app I) ((D.unit sq.X₂).app I)
  rw [biprodComparison_eq]
  exact IsIso.comp_isIso' h₁ h₂

/-- The biproduct comparison, as an isomorphism, on a K-injective complex. -/
noncomputable def biprodComparisonIso (I : CochainComplex A ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj
        ((complexFunctor S sq.X₃).obj I ⊞ (complexFunctor S sq.X₂).obj I) ≅
      (D.biprodFunctor sq).obj (DerivedCategory.Q.obj I) :=
  have := D.isIso_biprodComparison sq I
  asIso (D.biprodComparison sq I)

/-- The unit, as an isomorphism, on a K-injective complex. -/
noncomputable def unitIso (U : ι) (I : CochainComplex A ℤ) [I.IsKInjective] :
    (complexFunctor S U ⋙ DerivedCategory.Q).obj I ≅
      (DerivedCategory.Q ⋙ D.functor.obj (op U)).obj I :=
  asIso ((D.unit U).app I)

/-- The unit carries the chain-level first map to the first map on derived sections. -/
theorem unit_comp_firstMap (I : CochainComplex A ℤ) :
    DerivedCategory.Q.map (General.firstMap S sq I) ≫ D.biprodComparison sq I =
      (D.unit sq.X₄).app I ≫ D.firstMap sq (DerivedCategory.Q.obj I) := by
  have h₃ := D.unit_restriction sq.f₃₄ I
  have h₂ := D.unit_restriction sq.f₂₄ I
  have key := map_lift_comp_lift (DerivedCategory.Q (C := B))
    ((restrictionComplex S sq.f₃₄).app I) ((restrictionComplex S sq.f₂₄).app I)
    ((D.unit sq.X₃).app I) ((D.unit sq.X₂).app I)
  rw [h₃, h₂] at key
  exact key.trans (comp_lift _ _ _)

/-- The unit carries the chain-level signed second map to the second map on derived sections,
sign included. -/
theorem unit_comp_secondMap (I : CochainComplex A ℤ) :
    DerivedCategory.Q.map (General.secondMap S sq I) ≫ (D.unit sq.X₁).app I =
      D.biprodComparison sq I ≫ D.secondMap sq (DerivedCategory.Q.obj I) := by
  have h₃ := D.unit_restriction sq.f₁₃ I
  have h₂ := D.unit_restriction sq.f₁₂ I
  refine map_desc_comp (DerivedCategory.Q (C := B)) _ _ _ _ _ _ _ h₃ ?_
  rw [DerivedCategory.Q.map_neg, Preadditive.neg_comp, h₂, Preadditive.comp_neg]

end DerivedSectionsData

/-- Over a Grothendieck abelian category, every derived object is isomorphic to the localization
of a K-injective complex. -/
private theorem exists_kInjective_iso_of_isGrothendieckAbelian {A : Type*} [Category* A]
    [Abelian A] [HasDerivedCategory A] [IsGrothendieckAbelian.{t} A] (K : DerivedCategory A) :
    ∃ (I : CochainComplex A ℤ) (_ : I.IsKInjective), Nonempty (DerivedCategory.Q.obj I ≅ K) := by
  obtain ⟨NR⟩ := Stacks.Injectives.exists_functorial_quasiIso_isKInjective A
  set M := DerivedCategory.Q.objPreimage K
  have : (NR.functor.obj M).IsKInjective := NR.isKInjective M
  have : QuasiIso (NR.inclusion.app M) := NR.quasiIso M
  have : IsIso (DerivedCategory.Q.map (NR.inclusion.app M)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  exact ⟨NR.functor.obj M, inferInstance,
    ⟨(asIso (DerivedCategory.Q.map (NR.inclusion.app M))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- The descended canonical map and mapping-cocone maps, specified by their natural
K-injective computations. -/
structure DerivedCSquareData where
  /-- The derived sections used at the four vertices. -/
  sectionsData : DerivedSectionsData S
  /-- The functor computed by `C(β)[-1]` on K-injective representatives. -/
  coconeFunctor : DerivedCategory A ⥤ DerivedCategory B
  /-- The canonical map, natural on the derived category. -/
  comparison : sectionsData.functor.obj (op sq.X₄) ⟶ coconeFunctor
  /-- The mapping-cocone projection. -/
  projection : coconeFunctor ⟶ sectionsData.biprodFunctor sq
  /-- The mapping-cocone boundary. -/
  boundary : sectionsData.functor.obj (op sq.X₁) ⟶
    coconeFunctor ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ)
  /-- Computation of the cocone functor on a K-injective complex. -/
  coconeIso (I : CochainComplex A ℤ) [I.IsKInjective] :
    DerivedCategory.Q.obj (CochainComplex.mappingCocone (secondMap S sq I)) ≅
      coconeFunctor.obj (DerivedCategory.Q.obj I)
  /-- Naturality of the computation isomorphism. -/
  coconeIso_naturality {I I' : CochainComplex A ℤ}
      [I.IsKInjective] [I'.IsKInjective] (f : I ⟶ I') :
    DerivedCategory.Q.map (mappingCoconeMap S sq f) ≫ (coconeIso I').hom =
      (coconeIso I).hom ≫ coconeFunctor.map (DerivedCategory.Q.map f)
  /-- The descended comparison is precisely the canonical zero-null-homotopy map. -/
  comparison_eq (I : CochainComplex A ℤ) [I.IsKInjective] :
    DerivedCategory.Q.map (cSquare S sq I) ≫ (coconeIso I).hom =
      (sectionsData.unit sq.X₄).app I ≫ comparison.app (DerivedCategory.Q.obj I)
  /-- The descended projection is the standard mapping-cocone projection. -/
  projection_eq (I : CochainComplex A ℤ) [I.IsKInjective] :
    DerivedCategory.Q.map (CochainComplex.mappingCocone.fst (secondMap S sq I)) ≫
        sectionsData.biprodComparison sq I =
      (coconeIso I).hom ≫ projection.app (DerivedCategory.Q.obj I)
  /-- The descended boundary is the standard mapping-cocone boundary, including its sign. -/
  boundary_eq (I : CochainComplex A ℤ) [I.IsKInjective] :
    ((DerivedCategory.Q.mapTriangle).obj
        (CochainComplex.mappingCocone.triangle (secondMap S sq I))).mor₃ ≫
        (coconeIso I).hom⟦1⟧' =
      (sectionsData.unit sq.X₁).app I ≫ boundary.app (DerivedCategory.Q.obj I)

namespace DerivedCSquareData

section Elementary

/-- Two squares with invertible vertical edges detect invertibility of one another's
horizontal edges. -/
theorem isIso_iff_of_comp_eq {V : Type*} [Category V] {X Y X' Y' : V} {f : X ⟶ Y} {g : X ⟶ X'}
    {h : X' ⟶ Y'} {k : Y ⟶ Y'} (hsq : f ≫ k = g ≫ h) [IsIso g] [IsIso k] :
    IsIso f ↔ IsIso h := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · have : IsIso (g ≫ h) := hsq ▸ inferInstance
    exact IsIso.of_isIso_comp_left g h
  · have : IsIso (f ≫ k) := hsq ▸ inferInstance
    exact IsIso.of_isIso_comp_right f k

end Elementary

variable {S} {sq}
variable (D : DerivedCSquareData S sq)

/-- Derived sections in the square construction. -/
noncomputable abbrev derivedSections (U : ι) : DerivedCategory A ⥤ DerivedCategory B :=
  D.sectionsData.functor.obj (op U)

/-- The canonical natural transformation on the derived category. -/
noncomputable abbrev derivedCSquare : D.derivedSections sq.X₄ ⟶ D.coconeFunctor := D.comparison

/-- The property that the canonical map for a derived object is an isomorphism. -/
abbrev IsCSquareIso (K : DerivedCategory A) : Prop := IsIso (D.derivedCSquare.app K)

/-- The triangle on derived sections, with boundary obtained using the inverse of `c`. -/
noncomputable def cSquareTriangle (K : DerivedCategory A) [D.IsCSquareIso K] :
    Triangle (DerivedCategory B) :=
  Triangle.mk
    (D.sectionsData.firstMap sq K)
    (D.sectionsData.secondMap sq K)
    (D.boundary.app K ≫ (inv (D.derivedCSquare.app K))⟦1⟧')

/-- The canonical condition on a derived object can be tested on any K-injective
representative. -/
theorem isCSquareIso_iff_quasiIso (K : DerivedCategory A) (I : CochainComplex A ℤ)
    [I.IsKInjective] (e : DerivedCategory.Q.obj I ≅ K) :
    D.IsCSquareIso K ↔ QuasiIso (cSquare S sq I) := by
  have h₁ : IsIso (D.derivedCSquare.app (DerivedCategory.Q.obj I)) ↔
      IsIso (D.derivedCSquare.app K) :=
    isIso_iff_of_comp_eq (D.comparison.naturality e.hom).symm
  have h₂ : IsIso (DerivedCategory.Q.map (cSquare S sq I)) ↔
      IsIso (D.derivedCSquare.app (DerivedCategory.Q.obj I)) :=
    isIso_iff_of_comp_eq (D.comparison_eq I)
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, h₂, h₁]

/-- The boundary obtained from the inverse of the canonical map is natural in the derived
object. -/
theorem boundary_inv_naturality {K K' : DerivedCategory A} (f : K ⟶ K')
    [D.IsCSquareIso K] [D.IsCSquareIso K'] :
    (D.boundary.app K ≫
          (shiftFunctor (DerivedCategory B) (1 : ℤ)).map (inv (D.derivedCSquare.app K))) ≫
        (shiftFunctor (DerivedCategory B) (1 : ℤ)).map
          ((D.sectionsData.functor.obj (op sq.X₄)).map f) =
      (D.sectionsData.functor.obj (op sq.X₁)).map f ≫
        D.boundary.app K' ≫
          (shiftFunctor (DerivedCategory B) (1 : ℤ)).map (inv (D.derivedCSquare.app K')) := by
  have hb := D.boundary.naturality f
  simp only [Functor.comp_map] at hb
  have hc : inv (D.derivedCSquare.app K) ≫ (D.sectionsData.functor.obj (op sq.X₄)).map f =
      D.coconeFunctor.map f ≫ inv (D.derivedCSquare.app K') := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← D.comparison.naturality f, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [Category.assoc, ← Functor.map_comp, hc, Functor.map_comp, ← Category.assoc, ← hb,
    Category.assoc]

/-- Every derived morphism induces a unique morphism of the derived triangles with the given
three components. -/
theorem cSquareTriangle_functorial {K K' : DerivedCategory A} (f : K ⟶ K')
    [D.IsCSquareIso K] [D.IsCSquareIso K'] :
    ∃! t : D.cSquareTriangle K ⟶ D.cSquareTriangle K',
      t.hom₁ = (D.derivedSections sq.X₄).map f ∧
        t.hom₂ = biprod.map ((D.derivedSections sq.X₃).map f)
          ((D.derivedSections sq.X₂).map f) ∧
        t.hom₃ = (D.derivedSections sq.X₁).map f := by
  refine ⟨⟨(D.derivedSections sq.X₄).map f,
      biprod.map ((D.derivedSections sq.X₃).map f) ((D.derivedSections sq.X₂).map f),
      (D.derivedSections sq.X₁).map f, ?_, ?_, ?_⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
  · exact D.sectionsData.firstMap_naturality sq f
  · exact D.sectionsData.secondMap_naturality sq f
  · exact D.boundary_inv_naturality f
  · rintro t ⟨h₁, h₂, h₃⟩
    exact Triangle.hom_ext _ _ h₁ h₂ h₃

/-- The canonical map followed by the mapping-cocone projection is the first map, at a
K-injective complex. -/
theorem comparison_comp_projection (I : CochainComplex A ℤ) [I.IsKInjective] :
    D.comparison.app (DerivedCategory.Q.obj I) ≫
        D.projection.app (DerivedCategory.Q.obj I) =
      D.sectionsData.firstMap sq (DerivedCategory.Q.obj I) := by
  rw [← cancel_epi ((D.sectionsData.unit sq.X₄).app I), ← Category.assoc,
    ← D.comparison_eq I, Category.assoc, ← D.projection_eq I, ← Category.assoc,
    ← DerivedCategory.Q.map_comp, cSquare_comp_fst, D.sectionsData.unit_comp_firstMap]

/-- The canonical map on derived objects, as an isomorphism where it is one. -/
noncomputable def derivedCSquareIso (K : DerivedCategory A) [D.IsCSquareIso K] :
    (D.derivedSections sq.X₄).obj K ≅ D.coconeFunctor.obj K :=
  asIso (D.derivedCSquare.app K)

/-- The triangle built on the cocone functor rather than on the fourth derived sections: the
same three maps as `cSquareTriangle`, but with the boundary used as it stands instead of
twisted by the inverse of the canonical map. -/
noncomputable def coconeTriangle (K : DerivedCategory A) : Triangle (DerivedCategory B) :=
  Triangle.mk (D.projection.app K) (D.sectionsData.secondMap sq K) (D.boundary.app K)

/-- The cocone triangle is distinguished at a K-injective representative. -/
theorem coconeTriangle_distinguished (I : CochainComplex A ℤ) [I.IsKInjective] :
    D.coconeTriangle (DerivedCategory.Q.obj I) ∈ distTriang (DerivedCategory B) :=
  isomorphic_distinguished _
    (DerivedCategory.mappingCocone_triangle_distinguished (secondMap S sq I)) _
    (Triangle.isoMk _ _ (D.coconeIso I) (D.sectionsData.biprodComparisonIso sq I)
      (D.sectionsData.unitIso sq.X₁ I) (D.projection_eq I)
      (D.sectionsData.unit_comp_secondMap sq I) (D.boundary_eq I)).symm

/-- The derived-section triangle is distinguished at a K-injective representative at which the
canonical map is invertible. -/
theorem cSquareTriangle_distinguished_of_isKInjective (I : CochainComplex A ℤ)
    [I.IsKInjective] [D.IsCSquareIso (DerivedCategory.Q.obj I)] :
    D.cSquareTriangle (DerivedCategory.Q.obj I) ∈ distTriang (DerivedCategory B) := by
  refine isomorphic_distinguished _ (D.coconeTriangle_distinguished I) _
    (Triangle.isoMk _ _ (D.derivedCSquareIso (DerivedCategory.Q.obj I))
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · dsimp only [cSquareTriangle, coconeTriangle, Triangle.mk_mor₁, Triangle.mk_obj₁,
      Triangle.mk_obj₂]
    simpa [derivedCSquareIso] using (D.comparison_comp_projection I).symm
  · simp [cSquareTriangle, coconeTriangle]
  · simp [cSquareTriangle, coconeTriangle, derivedCSquareIso]

/-- **The derived-section triangle is distinguished**, for every derived object at which the
canonical map is invertible. -/
theorem cSquareTriangle_distinguished [IsGrothendieckAbelian.{t} A] (K : DerivedCategory A)
    [D.IsCSquareIso K] :
    D.cSquareTriangle K ∈ distTriang (DerivedCategory B) := by
  obtain ⟨I, _, ⟨e⟩⟩ := exists_kInjective_iso_of_isGrothendieckAbelian.{t} K
  have : D.IsCSquareIso (DerivedCategory.Q.obj I) :=
    (isIso_iff_of_comp_eq (D.comparison.naturality e.hom).symm).2 ‹_›
  exact isomorphic_distinguished _
    (D.cSquareTriangle_distinguished_of_isKInjective I) _
    (Triangle.isoMk _ _ ((D.derivedSections sq.X₄).mapIso e)
      ((D.sectionsData.biprodFunctor sq).mapIso e) ((D.derivedSections sq.X₁).mapIso e)
      (D.sectionsData.firstMap_naturality sq e.hom)
      (D.sectionsData.secondMap_naturality sq e.hom)
      (D.boundary_inv_naturality e.hom)).symm

end DerivedCSquareData

omit [HasDerivedCategory A] in
/-- A quasi-isomorphism between K-injective complexes is inverted by degreewise sections
followed by the localization. -/
theorem invertsQuasiIso_complexFunctor (U : ι) :
    Stacks.Injectives.KInjectiveResolution.InvertsQuasiIsoOfIsKInjective
      (complexFunctor S U ⋙ DerivedCategory.Q) := by
  intro I I' f hI hI' hf
  have h : QuasiIso ((complexFunctor S U).map f) :=
    Stacks.Injectives.KInjectiveResolution.quasiIso_mapHomologicalComplex_map_of_isKInjective
      (S.obj (op U)) f hI hI' hf
  exact Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)) _
    ((HomologicalComplex.mem_quasiIso_iff _).2 h)

omit [HasDerivedCategory A] in
/-- A quasi-isomorphism between K-injective complexes is inverted by the mapping cocone
followed by the localization. -/
theorem invertsQuasiIso_coconeComplexFunctor :
    Stacks.Injectives.KInjectiveResolution.InvertsQuasiIsoOfIsKInjective
      (coconeComplexFunctor S sq ⋙ DerivedCategory.Q) := by
  intro I I' f hI hI' hf
  have := hI
  have := hI'
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).1 hf
  have hsec : ∀ U : ι, IsIso (DerivedCategory.Q.map ((complexFunctor S U).map e.hom)) := by
    intro U
    have : QuasiIso ((complexFunctor S U).map e.hom) := by
      rw [← HomologicalComplex.mem_quasiIso_iff]
      exact homotopyEquivalences_le_quasiIso _ _ _ ⟨(S.obj (op U)).mapHomotopyEquiv e, rfl⟩
    infer_instance
  have h₃ := hsec sq.X₃
  have h₂ := hsec sq.X₂
  have hbip : IsIso (DerivedCategory.Q.map (biprod.map ((complexFunctor S sq.X₃).map e.hom)
      ((complexFunctor S sq.X₂).map e.hom))) :=
    MappingCoconeAux.isIso_map_biprod_map DerivedCategory.Q _ _
  have hconemap : IsIso (DerivedCategory.Q.map
      (CochainComplex.mappingCone.map (secondMap S sq I) (secondMap S sq I')
        (biprod.map ((complexFunctor S sq.X₃).map e.hom)
          ((complexFunctor S sq.X₂).map e.hom))
        ((complexFunctor S sq.X₁).map e.hom) (secondMap_square S sq e.hom))) :=
    Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map
        (CochainComplex.mappingCone.triangleMap (secondMap S sq I) (secondMap S sq I') _ _
          (secondMap_square S sq e.hom)))
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _) hbip (hsec sq.X₁)
  have hquasi : QuasiIso (CochainComplex.mappingCone.map (secondMap S sq I) (secondMap S sq I')
      (biprod.map ((complexFunctor S sq.X₃).map e.hom)
        ((complexFunctor S sq.X₂).map e.hom))
      ((complexFunctor S sq.X₁).map e.hom) (secondMap_square S sq e.hom)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hconemap
  have hs : QuasiIso (mappingCoconeMap S sq e.hom) := by
    rw [mappingCoconeMap_eq_shift_coneMap]
    exact (CochainComplex.quasiIso_shift_iff _ _).2 hquasi
  change IsIso (DerivedCategory.Q.map (mappingCoconeMap S sq e.hom))
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hs

section Construction

variable [IsGrothendieckAbelian.{t} A]

omit [HasDerivedCategory A] in
/-- Degreewise sections followed by the localization has an unbounded right derived
functor. -/
theorem hasRightDerivedFunctor_complexFunctor (U : ι) :
    (complexFunctor S U ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (S.obj (op U))

/-- The derived sections functor over an object of the index. -/
noncomputable abbrev derivedSectionsObj (U : ι) : DerivedCategory A ⥤ DerivedCategory B :=
  have := hasRightDerivedFunctor_complexFunctor S U
  (complexFunctor S U ⋙ DerivedCategory.Q).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- The unit of the derived sections functor over an object of the index. -/
noncomputable abbrev derivedSectionsUnit (U : ι) :
    complexFunctor S U ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ derivedSectionsObj S U :=
  have := hasRightDerivedFunctor_complexFunctor S U
  (complexFunctor S U ⋙ DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- Derived sections, contravariantly functorial in the index. -/
noncomputable def derivedSectionsFunctor :
    ιᵒᵖ ⥤ (DerivedCategory A ⥤ DerivedCategory B) where
  obj X := derivedSectionsObj S X.unop
  map {X Y} g := Functor.rightDerivedNatTrans _ _ (derivedSectionsUnit S X.unop)
    (derivedSectionsUnit S Y.unop)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (Functor.whiskerRight (restrictionComplex S g.unop) DerivedCategory.Q)
  map_id X := by
    rw [unop_id, restrictionComplex_id, Functor.whiskerRight_id',
      Functor.rightDerivedNatTrans_id]
  map_comp {X Y Z} g h := by
    rw [unop_comp, restrictionComplex_comp, Functor.whiskerRight_comp,
      Functor.rightDerivedNatTrans_comp]

/-- The derived sections data assembled from the right derived section functors. -/
noncomputable def derivedSectionsData : DerivedSectionsData S where
  functor := derivedSectionsFunctor S
  unit U := derivedSectionsUnit S U
  isRightDerivedFunctor U :=
    inferInstanceAs ((derivedSectionsObj S U).IsRightDerivedFunctor
      (derivedSectionsUnit S U) (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)))
  isIso_unit_app U I _ :=
    Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective DerivedCategory.Q
      (derivedSectionsObj S U) (derivedSectionsUnit S U)
      (invertsQuasiIso_complexFunctor S U) I ‹_›
  unit_restriction {U V} f I :=
    (Functor.rightDerivedNatTrans_app (derivedSectionsObj S V) (derivedSectionsObj S U)
      (derivedSectionsUnit S V) (derivedSectionsUnit S U)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (Functor.whiskerRight (restrictionComplex S f) DerivedCategory.Q) I).symm

omit [HasDerivedCategory A] in
/-- The mapping cocone followed by the localization has an unbounded right derived
functor. -/
theorem hasRightDerivedFunctor_coconeComplexFunctor :
    (coconeComplexFunctor S sq ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_of_isKInjective
    (invertsQuasiIso_coconeComplexFunctor S sq)

/-- The right derived functor of the mapping cocone of the signed restriction map. -/
noncomputable abbrev coconeDerivedObj : DerivedCategory A ⥤ DerivedCategory B :=
  have := hasRightDerivedFunctor_coconeComplexFunctor S sq
  (coconeComplexFunctor S sq ⋙ DerivedCategory.Q).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- The unit of the right derived functor of the mapping cocone. -/
noncomputable abbrev coconeDerivedUnit :
    coconeComplexFunctor S sq ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coconeDerivedObj S sq :=
  have := hasRightDerivedFunctor_coconeComplexFunctor S sq
  (coconeComplexFunctor S sq ⋙ DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- The descended canonical map. -/
noncomputable def comparisonNatTrans : derivedSectionsObj S sq.X₄ ⟶ coconeDerivedObj S sq :=
  (derivedSectionsObj S sq.X₄).rightDerivedDesc (derivedSectionsUnit S sq.X₄)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (coconeDerivedObj S sq)
    (Functor.whiskerRight (cSquareNatTrans S sq) DerivedCategory.Q ≫ coconeDerivedUnit S sq)

/-- The descended mapping-cocone projection, into the pointwise biproduct of the two middle
derived section functors. -/
noncomputable def projectionNatTrans (D : DerivedSectionsData S) :
    coconeDerivedObj S sq ⟶ D.biprodFunctor sq :=
  (coconeDerivedObj S sq).rightDerivedDesc (coconeDerivedUnit S sq)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (D.biprodFunctor sq)
    (Functor.whiskerRight (coconeFstNatTrans S sq) DerivedCategory.Q ≫
      D.biprodComparisonNatTrans sq)

/-- The descended mapping-cocone boundary: the descent of the chain-level boundary followed by
the commutation of the localization functor with the shift and by the unit of the cocone's
derived functor. -/
noncomputable def boundaryNatTrans :
    derivedSectionsObj S sq.X₁ ⟶
      coconeDerivedObj S sq ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ) :=
  (derivedSectionsObj S sq.X₁).rightDerivedDesc (derivedSectionsUnit S sq.X₁)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (coconeDerivedObj S sq ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ))
    (Functor.whiskerRight (coconeBoundaryNatTrans S sq) DerivedCategory.Q ≫
      Functor.whiskerLeft (coconeComplexFunctor S sq)
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom ≫
      Functor.whiskerRight (coconeDerivedUnit S sq)
        (shiftFunctor (DerivedCategory B) (1 : ℤ)))

/-- A K-injective complex computes the derived functor of the mapping cocone. -/
theorem isIso_coconeDerivedUnit_app (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((coconeDerivedUnit S sq).app I) :=
  Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective DerivedCategory.Q
    (coconeDerivedObj S sq) (coconeDerivedUnit S sq)
    (invertsQuasiIso_coconeComplexFunctor S sq) I ‹_›

/-- The computation of the derived mapping cocone on a K-injective complex: the unit of its
derived functor there, as an isomorphism. -/
noncomputable def coconeDerivedIso (I : CochainComplex A ℤ) [I.IsKInjective] :
    (coconeComplexFunctor S sq ⋙ DerivedCategory.Q).obj I ≅
      (DerivedCategory.Q ⋙ coconeDerivedObj S sq).obj I :=
  have := isIso_coconeDerivedUnit_app S sq I
  asIso ((coconeDerivedUnit S sq).app I)

/-- The forward map of `coconeDerivedIso` is the unit of the derived mapping cocone. -/
theorem coconeDerivedIso_hom (I : CochainComplex A ℤ) [I.IsKInjective] :
    (coconeDerivedIso S sq I).hom = (coconeDerivedUnit S sq).app I := rfl

/-- **The derived construction of [Stacks, Tag 0F16]**, assuming the coefficient category
Grothendieck abelian: the derived section functors of the four corners, the derived
functor of the mapping cocone, and the three descended natural transformations, each
identified on K-injective representatives with its chain-level construction. -/
noncomputable def derivedCSquareDataOfIsGrothendieckAbelian : DerivedCSquareData S sq where
  sectionsData := derivedSectionsData S
  coconeFunctor := coconeDerivedObj S sq
  comparison := comparisonNatTrans S sq
  projection := projectionNatTrans S sq (derivedSectionsData S)
  boundary := boundaryNatTrans S sq
  coconeIso I := coconeDerivedIso S sq I
  coconeIso_naturality f := (coconeDerivedUnit S sq).naturality f
  comparison_eq I :=
    (Functor.rightDerived_fac_app (derivedSectionsObj S sq.X₄) (derivedSectionsUnit S sq.X₄)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) (coconeDerivedObj S sq)
      (Functor.whiskerRight (cSquareNatTrans S sq) DerivedCategory.Q ≫
        coconeDerivedUnit S sq) I).symm
  projection_eq I :=
    (Functor.rightDerived_fac_app (coconeDerivedObj S sq) (coconeDerivedUnit S sq)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      ((derivedSectionsData S).biprodFunctor sq)
      (Functor.whiskerRight (coconeFstNatTrans S sq) DerivedCategory.Q ≫
        (derivedSectionsData S).biprodComparisonNatTrans sq) I).symm
  boundary_eq I := (Category.assoc _ _ _).trans
    (Functor.rightDerived_fac_app (derivedSectionsObj S sq.X₁) (derivedSectionsUnit S sq.X₁)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (coconeDerivedObj S sq ⋙ shiftFunctor (DerivedCategory B) (1 : ℤ))
      (Functor.whiskerRight (coconeBoundaryNatTrans S sq) DerivedCategory.Q ≫
        Functor.whiskerLeft (coconeComplexFunctor S sq)
          (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom ≫
        Functor.whiskerRight (coconeDerivedUnit S sq)
          (shiftFunctor (DerivedCategory B) (1 : ℤ))) I).symm

end Construction

end Derived

end General

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{r}} (sq : Square C)

/-- The degreewise biproduct of the sections over the two middle corners of the square,
as a functor of the complex. -/
noncomputable def biprodComplexFunctor :
    CochainComplex (SheafOfModules.{v} R) ℤ ⥤ CochainComplex AddCommGrpCat.{v} ℤ :=
  General.biprodComplexFunctor (sectionsSystem R) sq

/-- The first map, as a natural transformation of functors of the complex. -/
noncomputable def firstMapNatTrans :
    sectionsComplex.{u, v} R sq.X₄ ⟶ biprodComplexFunctor sq :=
  General.firstMapNatTrans (sectionsSystem R) sq

/-- The signed second map, as a natural transformation of functors of the complex. -/
noncomputable def secondMapNatTrans :
    biprodComplexFunctor sq ⟶ sectionsComplex.{u, v} R sq.X₁ :=
  General.secondMapNatTrans (sectionsSystem R) sq

/-- The induced map of mapping cocones of an identity is the identity. -/
theorem mappingCoconeMap_id (I : CochainComplex (SheafOfModules.{v} R) ℤ) :
    mappingCoconeMap sq (𝟙 I) = 𝟙 (CochainComplex.mappingCocone (secondMap sq I)) :=
  General.mappingCoconeMap_id (sectionsSystem R) sq I

/-- The induced maps of mapping cocones compose. -/
theorem mappingCoconeMap_comp {I I' I'' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I')
    (g : I' ⟶ I'') :
    mappingCoconeMap sq (f ≫ g) = mappingCoconeMap sq f ≫ mappingCoconeMap sq g :=
  General.mappingCoconeMap_comp (sectionsSystem R) sq f g

/-- The mapping cocone of the signed second map, as a functor of the complex. -/
noncomputable def coconeComplexFunctor :
    CochainComplex (SheafOfModules.{v} R) ℤ ⥤ CochainComplex AddCommGrpCat.{v} ℤ :=
  General.coconeComplexFunctor (sectionsSystem R) sq

/-- The value of `biprodComplexFunctor` on a complex. -/
@[simp]
theorem biprodComplexFunctor_obj (I : CochainComplex (SheafOfModules.{v} R) ℤ) :
    (biprodComplexFunctor sq).obj I =
      ((sectionsComplex R sq.X₃).obj I ⊞ (sectionsComplex R sq.X₂).obj I) :=
  General.biprodComplexFunctor_obj (sectionsSystem R) sq I

/-- The value of `biprodComplexFunctor` on a morphism. -/
@[simp]
theorem biprodComplexFunctor_map {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    (biprodComplexFunctor sq).map f =
      biprod.map ((sectionsComplex R sq.X₃).map f) ((sectionsComplex R sq.X₂).map f) :=
  General.biprodComplexFunctor_map (sectionsSystem R) sq f

/-- The value of `coconeComplexFunctor` on a complex. -/
@[simp]
theorem coconeComplexFunctor_obj (I : CochainComplex (SheafOfModules.{v} R) ℤ) :
    (coconeComplexFunctor sq).obj I = CochainComplex.mappingCocone (secondMap sq I) :=
  General.coconeComplexFunctor_obj (sectionsSystem R) sq I

/-- The value of `coconeComplexFunctor` on a morphism. -/
@[simp]
theorem coconeComplexFunctor_map {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    (coconeComplexFunctor sq).map f = mappingCoconeMap sq f :=
  General.coconeComplexFunctor_map (sectionsSystem R) sq f

/-- The projection onto the sections over the third corner, as a natural transformation. -/
noncomputable def biprodFstNatTrans :
    biprodComplexFunctor.{u, v} (R := R) sq ⟶ sectionsComplex R sq.X₃ :=
  General.biprodFstNatTrans (sectionsSystem R) sq

/-- The projection onto the sections over the second corner, as a natural transformation. -/
noncomputable def biprodSndNatTrans :
    biprodComplexFunctor.{u, v} (R := R) sq ⟶ sectionsComplex R sq.X₂ :=
  General.biprodSndNatTrans (sectionsSystem R) sq

/-- The canonical map of complexes, as a natural transformation. -/
noncomputable def cSquareNatTrans :
    sectionsComplex.{u, v} R sq.X₄ ⟶ coconeComplexFunctor sq :=
  General.cSquareNatTrans (sectionsSystem R) sq

/-- The canonical map of complexes followed by the mapping-cocone projection is the first
map: this is the defining property of the lift. -/
theorem cSquare_comp_fst (I : CochainComplex (SheafOfModules.{v} R) ℤ) :
    cSquare sq I ≫ CochainComplex.mappingCocone.fst (secondMap sq I) = firstMap sq I :=
  General.cSquare_comp_fst (sectionsSystem R) sq I

/-- The induced map of mapping cocones is compatible with the first projections. -/
theorem mappingCoconeMap_comp_fst {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    mappingCoconeMap sq f ≫ CochainComplex.mappingCocone.fst (secondMap sq I') =
      CochainComplex.mappingCocone.fst (secondMap sq I) ≫
        biprod.map ((sectionsComplex R sq.X₃).map f) ((sectionsComplex R sq.X₂).map f) :=
  General.mappingCoconeMap_comp_fst (sectionsSystem R) sq f

/-- The mapping-cocone projection, as a natural transformation. -/
noncomputable def coconeFstNatTrans :
    coconeComplexFunctor.{u, v} (R := R) sq ⟶ biprodComplexFunctor sq :=
  General.coconeFstNatTrans (sectionsSystem R) sq

/-- The commutative square underlying the morphism of signed restriction arrows. -/
theorem secondMap_square {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    secondMap sq I ≫ (sectionsComplex R sq.X₁).map f =
      biprod.map ((sectionsComplex R sq.X₃).map f) ((sectionsComplex R sq.X₂).map f) ≫
        secondMap sq I' :=
  General.secondMap_square (sectionsSystem R) sq f

/-- The induced map of mapping cocones is the shift of the induced map of mapping cones. -/
theorem mappingCoconeMap_eq_shift_coneMap {I I' : CochainComplex (SheafOfModules.{v} R) ℤ}
    (f : I ⟶ I') :
    mappingCoconeMap sq f =
      (shiftFunctor (CochainComplex AddCommGrpCat.{v} ℤ) (-1 : ℤ)).map
        (CochainComplex.mappingCone.map (secondMap sq I) (secondMap sq I')
          (biprod.map ((sectionsComplex R sq.X₃).map f) ((sectionsComplex R sq.X₂).map f))
          ((sectionsComplex R sq.X₁).map f) (secondMap_square sq f)) :=
  General.mappingCoconeMap_eq_shift_coneMap (sectionsSystem R) sq f

/-- Naturality of the mapping-cone right inclusion followed by the shift comparison, in the
spelling in which both sides are compositions of maps of mapping cones. -/
theorem inr_comp_shiftComparison_naturality
    {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    (sectionsComplex R sq.X₁).map f ≫ CochainComplex.mappingCone.inr (secondMap sq I') ≫
        (shiftFunctorCompIsoId (CochainComplex AddCommGrpCat.{v} ℤ) (-1 : ℤ) 1 (by lia)).inv.app
          (CochainComplex.mappingCone (secondMap sq I')) =
      (CochainComplex.mappingCone.inr (secondMap sq I) ≫
          (shiftFunctorCompIsoId (CochainComplex AddCommGrpCat.{v} ℤ) (-1 : ℤ) 1 (by lia)).inv.app
            (CochainComplex.mappingCone (secondMap sq I))) ≫
        (shiftFunctor (CochainComplex AddCommGrpCat.{v} ℤ) (1 : ℤ)).map
          ((shiftFunctor (CochainComplex AddCommGrpCat.{v} ℤ) (-1 : ℤ)).map
            (CochainComplex.mappingCone.map (secondMap sq I) (secondMap sq I')
              (biprod.map ((sectionsComplex R sq.X₃).map f) ((sectionsComplex R sq.X₂).map f))
              ((sectionsComplex R sq.X₁).map f) (secondMap_square sq f))) :=
  General.inr_comp_shiftComparison_naturality (sectionsSystem R) sq f

/-- The boundary of the mapping-cocone triangle is natural in the complex. -/
theorem mappingCocone_triangle_mor₃_naturality
    {I I' : CochainComplex (SheafOfModules.{v} R) ℤ} (f : I ⟶ I') :
    (sectionsComplex R sq.X₁).map f ≫
        (CochainComplex.mappingCocone.triangle (secondMap sq I')).mor₃ =
      (CochainComplex.mappingCocone.triangle (secondMap sq I)).mor₃ ≫
        (shiftFunctor (CochainComplex AddCommGrpCat.{v} ℤ) (1 : ℤ)).map
          (mappingCoconeMap sq f) :=
  General.mappingCocone_triangle_mor₃_naturality (sectionsSystem R) sq f

/-- The mapping-cocone boundary, as a natural transformation. -/
noncomputable def coconeBoundaryNatTrans :
    sectionsComplex.{u, v} R sq.X₁ ⟶
      coconeComplexFunctor (R := R) sq ⋙
        shiftFunctor (CochainComplex AddCommGrpCat.{v} ℤ) (1 : ℤ) :=
  General.coconeBoundaryNatTrans (sectionsSystem R) sq

section Derived

attribute [local instance] HasDerivedCategory.standard sheafSections_obj_additive

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- A system of right derived section functors over the objects of the site, with the
canonical units and restriction maps.  This is `General.DerivedSectionsData` at the site's
system of sections functors. -/
abbrev DerivedSectionsData (R : Sheaf J RingCat.{r}) [HasSheafify J AddCommGrpCat.{v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}] :=
  General.DerivedSectionsData (sectionsSystem.{u, v} R)

/-- The descended canonical map and mapping-cocone maps of the square, specified by their
natural K-injective computations.  This is `General.DerivedCSquareData` at the site's system
of sections functors. -/
abbrev DerivedCSquareData := General.DerivedCSquareData (sectionsSystem.{u, v} R) sq

namespace DerivedCSquareData

variable {sq} (D : DerivedCSquareData (R := R) sq)

/-- Derived sections in the square construction. -/
noncomputable abbrev derivedSections (U : C) :
    DerivedCategory (SheafOfModules.{v} R) ⥤ DerivedCategory AddCommGrpCat.{v} :=
  D.sectionsData.functor.obj (op U)

/-- The canonical natural transformation on `D(𝒪)`. -/
noncomputable abbrev derivedCSquare : D.derivedSections sq.X₄ ⟶ D.coconeFunctor := D.comparison

/-- The property that the canonical map for a derived object is an isomorphism. -/
abbrev IsCSquareIso (K : DerivedCategory (SheafOfModules.{v} R)) : Prop :=
  IsIso (D.derivedCSquare.app K)

/-- The triangle on derived sections, with boundary obtained using the inverse of `c`. -/
@[stacks 0F16 "the canonical triangle on derived objects"]
noncomputable def cSquareTriangle (K : DerivedCategory (SheafOfModules.{v} R))
    [D.IsCSquareIso K] : Triangle (DerivedCategory AddCommGrpCat.{v}) :=
  General.DerivedCSquareData.cSquareTriangle D K

/-- The canonical condition on a derived object can be tested on any K-injective
representative. -/
@[stacks 0F16 "computation of the isomorphism condition"]
theorem isCSquareIso_iff_quasiIso (K : DerivedCategory (SheafOfModules.{v} R))
    (I : CochainComplex (SheafOfModules.{v} R) ℤ) [I.IsKInjective]
    (e : DerivedCategory.Q.obj I ≅ K) :
    D.IsCSquareIso K ↔ QuasiIso (cSquare sq I) :=
  General.DerivedCSquareData.isCSquareIso_iff_quasiIso D K I e

/-- Every derived morphism induces a unique morphism of the derived triangles with the given
three components. -/
@[stacks 0F16 "functoriality of the triangle in the derived object"]
theorem cSquareTriangle_functorial {K K' : DerivedCategory (SheafOfModules.{v} R)} (f : K ⟶ K')
    [D.IsCSquareIso K] [D.IsCSquareIso K'] :
    ∃! t : D.cSquareTriangle K ⟶ D.cSquareTriangle K',
      t.hom₁ = (D.derivedSections sq.X₄).map f ∧
        t.hom₂ = biprod.map ((D.derivedSections sq.X₃).map f)
          ((D.derivedSections sq.X₂).map f) ∧
        t.hom₃ = (D.derivedSections sq.X₁).map f :=
  General.DerivedCSquareData.cSquareTriangle_functorial D f

/-- **The derived-section triangle is distinguished**, for every derived object at which the
canonical map is invertible. -/
theorem cSquareTriangle_distinguished [IsGrothendieckAbelian.{v} (SheafOfModules.{v} R)]
    (K : DerivedCategory (SheafOfModules.{v} R)) [D.IsCSquareIso K] :
    D.cSquareTriangle K ∈ distTriang (DerivedCategory AddCommGrpCat.{v}) :=
  General.DerivedCSquareData.cSquareTriangle_distinguished D K

end DerivedCSquareData

/-- A quasi-isomorphism between K-injective complexes is inverted by degreewise sections
followed by the localization. -/
theorem invertsQuasiIso_sectionsComplex (U : C) :
    Stacks.Injectives.KInjectiveResolution.InvertsQuasiIsoOfIsKInjective
      (sectionsComplex.{u, v} R U ⋙ DerivedCategory.Q) :=
  General.invertsQuasiIso_complexFunctor (sectionsSystem R) U

/-- A quasi-isomorphism between K-injective complexes is inverted by the mapping cocone
followed by the localization. -/
theorem invertsQuasiIso_coconeComplexFunctor :
    Stacks.Injectives.KInjectiveResolution.InvertsQuasiIsoOfIsKInjective
      (coconeComplexFunctor.{u, v} (R := R) sq ⋙ DerivedCategory.Q) :=
  General.invertsQuasiIso_coconeComplexFunctor (sectionsSystem R) sq

section KInjectiveResolution

variable [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- **Every complex of sheaves of modules admits a K-injective resolution**, under `UnivLE`
between the universes of the site, of its homs, of the rings and of the modules. -/
theorem exists_kInjectiveResolution (K : CochainComplex (SheafOfModules.{v} R) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{v} R) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f := by
  have : IsGrothendieckAbelian.{v} (SheafOfModules.{v} R) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE R
  obtain ⟨NR⟩ := Stacks.Injectives.exists_functorial_quasiIso_isKInjective
    (SheafOfModules.{v} R)
  exact ⟨NR.functor.obj K, NR.inclusion.app K, NR.isKInjective K, NR.quasiIso K⟩

/-- **Every object of the derived category of sheaves of modules is represented by a
K-injective complex.** -/
theorem exists_kInjective_iso (K : DerivedCategory (SheafOfModules.{v} R)) :
    ∃ (I : CochainComplex (SheafOfModules.{v} R) ℤ) (_ : I.IsKInjective),
      Nonempty (DerivedCategory.Q.obj I ≅ K) := by
  have : IsGrothendieckAbelian.{v} (SheafOfModules.{v} R) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE R
  exact General.exists_kInjective_iso_of_isGrothendieckAbelian.{v} K

end KInjectiveResolution

section Construction

variable [IsGrothendieckAbelian.{v} (SheafOfModules.{v} R)]

/-- Degreewise sections followed by the localization has an unbounded right derived functor. -/
theorem hasRightDerivedFunctor_sectionsComplex (U : C) :
    (sectionsComplex.{u, v} R U ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (SheafOfModules.{v} R) (ComplexShape.up ℤ)) :=
  General.hasRightDerivedFunctor_complexFunctor (sectionsSystem R) U

/-- The derived sections functor over an object of the site. -/
noncomputable abbrev derivedSectionsObj (U : C) :
    DerivedCategory (SheafOfModules.{v} R) ⥤ DerivedCategory AddCommGrpCat.{v} :=
  General.derivedSectionsObj (sectionsSystem R) U

/-- The unit of the derived sections functor over an object of the site. -/
noncomputable abbrev derivedSectionsUnit (U : C) :
    sectionsComplex R U ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedSectionsObj.{u, v} (R := R) U :=
  General.derivedSectionsUnit (sectionsSystem R) U

/-- Derived sections, contravariantly functorial in the object of the site. -/
noncomputable def derivedSectionsFunctor :
    Cᵒᵖ ⥤ (DerivedCategory (SheafOfModules.{v} R) ⥤ DerivedCategory AddCommGrpCat.{v}) :=
  General.derivedSectionsFunctor (sectionsSystem R)

/-- The derived sections data assembled from the right derived section functors. -/
noncomputable def derivedSectionsData : DerivedSectionsData.{u, v} R :=
  General.derivedSectionsData (sectionsSystem R)

/-- The mapping cocone followed by the localization has an unbounded right derived functor. -/
theorem hasRightDerivedFunctor_coconeComplexFunctor :
    (coconeComplexFunctor.{u, v} (R := R) sq ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (SheafOfModules.{v} R) (ComplexShape.up ℤ)) :=
  General.hasRightDerivedFunctor_coconeComplexFunctor (sectionsSystem R) sq

/-- The right derived functor of the mapping cocone of the signed restriction map. -/
noncomputable abbrev coconeDerivedObj :
    DerivedCategory (SheafOfModules.{v} R) ⥤ DerivedCategory AddCommGrpCat.{v} :=
  General.coconeDerivedObj (sectionsSystem R) sq

/-- The unit of the right derived functor of the mapping cocone. -/
noncomputable abbrev coconeDerivedUnit :
    coconeComplexFunctor.{u, v} (R := R) sq ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coconeDerivedObj.{u, v} (R := R) sq :=
  General.coconeDerivedUnit (sectionsSystem R) sq

/-- The descended canonical map. -/
noncomputable def comparisonNatTrans :
    derivedSectionsObj.{u, v} (R := R) sq.X₄ ⟶ coconeDerivedObj.{u, v} (R := R) sq :=
  General.comparisonNatTrans (sectionsSystem R) sq

/-- The descended mapping-cocone projection, into the pointwise biproduct of the two middle
derived section functors. -/
noncomputable def projectionNatTrans (D : DerivedSectionsData.{u, v} R) :
    coconeDerivedObj.{u, v} (R := R) sq ⟶ D.biprodFunctor sq :=
  General.projectionNatTrans (sectionsSystem R) sq D

/-- The descended mapping-cocone boundary: the descent of the chain-level boundary followed by
the commutation of the localization functor with the shift and by the unit of the cocone's
derived functor. -/
noncomputable def boundaryNatTrans :
    derivedSectionsObj.{u, v} (R := R) sq.X₁ ⟶
      coconeDerivedObj.{u, v} (R := R) sq ⋙
        shiftFunctor (DerivedCategory AddCommGrpCat.{v}) (1 : ℤ) :=
  General.boundaryNatTrans (sectionsSystem R) sq

/-- A K-injective complex computes the derived functor of the mapping cocone. -/
theorem isIso_coconeDerivedUnit_app (I : CochainComplex (SheafOfModules.{v} R) ℤ)
    [I.IsKInjective] : IsIso ((coconeDerivedUnit.{u, v} (R := R) sq).app I) :=
  General.isIso_coconeDerivedUnit_app (sectionsSystem R) sq I

/-- The computation of the derived mapping cocone on a K-injective complex: the unit of its
derived functor there, as an isomorphism. -/
noncomputable def coconeDerivedIso (I : CochainComplex (SheafOfModules.{v} R) ℤ)
    [I.IsKInjective] :
    (coconeComplexFunctor.{u, v} (R := R) sq ⋙ DerivedCategory.Q).obj I ≅
      (DerivedCategory.Q ⋙ coconeDerivedObj.{u, v} (R := R) sq).obj I :=
  General.coconeDerivedIso (sectionsSystem R) sq I

/-- The forward map of `coconeDerivedIso` is the unit of the derived mapping cocone. -/
theorem coconeDerivedIso_hom (I : CochainComplex (SheafOfModules.{v} R) ℤ) [I.IsKInjective] :
    (coconeDerivedIso.{u, v} (R := R) sq I).hom =
      (coconeDerivedUnit.{u, v} (R := R) sq).app I :=
  General.coconeDerivedIso_hom (sectionsSystem R) sq I

/-- **The derived construction of [Stacks, Tag 0F16]**, assuming the category of sheaves of
modules Grothendieck abelian: the derived section functors of the four corners, the derived
functor of the mapping cocone, and the three descended natural transformations, each
identified on K-injective representatives with its chain-level construction. -/
noncomputable def derivedCSquareDataOfIsGrothendieckAbelian :
    DerivedCSquareData.{u, v} (R := R) sq :=
  General.derivedCSquareDataOfIsGrothendieckAbelian (sectionsSystem R) sq

omit [IsGrothendieckAbelian.{v} (SheafOfModules.{v} R)] in
/-- **The derived construction of the canonical map of a square**, under `UnivLE` between the
universes of the site, of its homs, of the rings and of the modules. -/
@[stacks 0F16 "the functorial derived construction and its K-injective computation"]
noncomputable def derivedCSquareData [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}] :
    DerivedCSquareData.{u, v} (R := R) sq :=
  have : IsGrothendieckAbelian.{v} (SheafOfModules.{v} R) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE R
  derivedCSquareDataOfIsGrothendieckAbelian.{u, v} (R := R) sq

omit [IsGrothendieckAbelian.{v} (SheafOfModules.{v} R)] in
/-- **The derived-section triangle is distinguished** at every derived object where the
canonical map is invertible, under `UnivLE` between the universes of the site, of its homs, of
the rings and of the modules. -/
@[stacks 0F16 "the triangle is distinguished"]
theorem cSquareTriangle_distinguished [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]
    (K : DerivedCategory (SheafOfModules.{v} R))
    [(derivedCSquareData.{u, v} (R := R) sq).IsCSquareIso K] :
    (derivedCSquareData.{u, v} (R := R) sq).cSquareTriangle K ∈
      distTriang (DerivedCategory AddCommGrpCat.{v}) :=
  have : IsGrothendieckAbelian.{v} (SheafOfModules.{v} R) :=
    SheafOfModules.isGrothendieckAbelian_of_univLE R
  (derivedCSquareData.{u, v} (R := R) sq).cSquareTriangle_distinguished K

end Construction

end Derived

end Stacks.MayerVietoris.CanonicalMapOfComplexes

end
