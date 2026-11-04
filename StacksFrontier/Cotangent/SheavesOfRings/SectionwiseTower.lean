module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Cotangent.SheavesOfRings.AffineCotangentRestriction
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseCotangentModuleComplex
public import StacksFrontier.Cotangent.Triangle.DisplayedTriangle

/-!
# The sectionwise maps of the fundamental triangle

Let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on a site. Over every object
`U` they restrict to ring maps `A(U) → B(U) → D(U)`, and the two displayed maps of the
fundamental triangle of these ring maps,

`L_{B(U)/A(U)} ⟶ L_{D(U)/A(U)}` and `L_{D(U)/A(U)} ⟶ L_{D(U)/B(U)}`,

are the functoriality maps of the cotangent complex for the two squares of the tower. This file
shows that they are compatible with the restriction maps, so that they form maps of complexes of
presheaves of modules between the sectionwise cotangent complexes
`CategoryTheory.Sheaf.sectionwiseCotangentModuleComplex`.

## Main definitions

* `CategoryTheory.Sheaf.sectionsTowerHom`: the map `B(U) ⟶ D(U)` of `A(U)`-algebras.
* `CategoryTheory.Sheaf.sectionwiseTowerBaseChangeMap`: the `B`-linear map
  `U ↦ (L_{B(U)/A(U)} ⟶ L_{D(U)/A(U)})`.
* `CategoryTheory.Sheaf.sectionwiseTowerChangeOfBaseMap`: the map
  `U ↦ (L_{D(U)/A(U)} ⟶ L_{D(U)/B(U)})`.
* `CategoryTheory.Sheaf.sectionwiseBaseChangedCotangentComplex`: the complex
  `U ↦ L_{B(U)/A(U)} ⊗_{B(U)} D(U)` of presheaves of `D`-modules.
* `CategoryTheory.Sheaf.sectionwiseTowerBaseChangeComplexMap`: the map
  `U ↦ (L_{B(U)/A(U)} ⊗_{B(U)} D(U) ⟶ L_{D(U)/A(U)})`.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- The map `B(U) ⟶ D(U)` of `A(U)`-algebras on sections over `U`. -/
noncomputable def sectionsTowerHom (U : Cᵒᵖ) :
    sectionsAlgebra J g U ⟶ sectionsAlgebra J (g ≫ h) U :=
  letI : Algebra (A.obj.obj U) (B.obj.obj U) := (sectionsMap J g U).toAlgebra
  letI : Algebra (A.obj.obj U) (D.obj.obj U) := (sectionsMap J (g ≫ h) U).toAlgebra
  CommAlgCat.ofHom { toRingHom := (h.hom.app U).hom, commutes' := fun _ => rfl }

/-- `D(U)`, read over `B(U)` through the map of sections, is the algebra of sections of `h`. -/
theorem algebraOver_sectionsTowerHom (U : Cᵒᵖ) :
    CommAlgCat.algebraOver (sectionsTowerHom J g h U) = sectionsAlgebra J h U :=
  rfl

/-- The morphism of presheaves of rings underlying `h`. -/
noncomputable abbrev towerRingMap :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj :=
  Functor.whiskerRight h.hom (forget₂ CommRingCat RingCat)

/-- The square `(id, h_U)` of the tower restricts along `U ⟶ V` in two ways, and the two
composite squares agree. -/
theorem idSquare_sectionsTowerHom_comp {U V : Cᵒᵖ} (k : U ⟶ V) :
    (CommAlgCat.idSquare (sectionsTowerHom J g h U)).comp (sectionsRestrictionSquare J (g ≫ h) k) =
      (sectionsRestrictionSquare J g k).comp (CommAlgCat.idSquare (sectionsTowerHom J g h V)) := by
  have hmap : (D.obj.map k).hom.comp (h.hom.app U).hom =
      (h.hom.app V).hom.comp (B.obj.map k).hom :=
    congrArg CommRingCat.Hom.hom (h.hom.naturality k).symm
  unfold CommAlgCat.idSquare sectionsRestrictionSquare CommAlgCat.AlgebraSquare.comp
  congr 1

/-- **The sectionwise first map of the fundamental triangle**: the maps
`L_{B(U)/A(U)} ⟶ L_{D(U)/A(U)}` induced by the squares `(id, h_U)`, as a `B`-linear map of
complexes of presheaves of modules. -/
noncomputable def sectionwiseTowerBaseChangeMap :
    sectionwiseCotangentModuleComplex J g ⟶
      ((PresheafOfModules.restrictScalars (towerRingMap J h)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (sectionwiseCotangentModuleComplex J (g ≫ h)) where
  f j :=
    { app U := (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
        (CommAlgCat.idSquare (sectionsTowerHom J g h U))).f j
      naturality {U V} k := by
        ext x
        exact (((CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp _ _
          (idSquare_sectionsTowerHom_comp J g h k).symm j x).symm).trans
          (CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp _ _ rfl j x)).symm }
  comm' i j _ := by
    refine PresheafOfModules.Hom.ext (funext fun U => ?_)
    exact (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
      (CommAlgCat.idSquare (sectionsTowerHom J g h U))).comm i j

/-- The square `(A(U) → B(U), id)` of the change of base ring restricts along `U ⟶ V` in two
ways, and the two composite squares agree. -/
theorem baseRingSquareTop_sectionsTowerHom_comp {U V : Cᵒᵖ} (k : U ⟶ V) :
    (CommAlgCat.baseRingSquareTop (sectionsTowerHom J g h U)).comp
        (sectionsRestrictionSquare J h k) =
      (sectionsRestrictionSquare J (g ≫ h) k).comp
        (CommAlgCat.baseRingSquareTop (sectionsTowerHom J g h V)) := by
  have hbase : (B.obj.map k).hom.comp (g.hom.app U).hom =
      (g.hom.app V).hom.comp (A.obj.map k).hom :=
    congrArg CommRingCat.Hom.hom (g.hom.naturality k).symm
  unfold CommAlgCat.baseRingSquareTop sectionsRestrictionSquare CommAlgCat.AlgebraSquare.comp
  congr 1

/-- **The sectionwise second map of the fundamental triangle**: the maps
`L_{D(U)/A(U)} ⟶ L_{D(U)/B(U)}` induced by the squares `(A(U) → B(U), id)` of the change of base
ring, as a map of complexes of presheaves of `D`-modules. -/
noncomputable def sectionwiseTowerChangeOfBaseMap :
    sectionwiseCotangentModuleComplex J (g ≫ h) ⟶ sectionwiseCotangentModuleComplex J h where
  f j :=
    { app U := (CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
        (CommAlgCat.baseRingSquareTop (sectionsTowerHom J g h U))).f j
      naturality {U V} k := by
        ext x
        exact (((CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp _ _
          (baseRingSquareTop_sectionsTowerHom_comp J g h k).symm j x).symm).trans
          (CommAlgCat.squareCotangentComplexMap_apply_of_eq_comp _ _ rfl j x)).symm }
  comm' i j _ := by
    refine PresheafOfModules.Hom.ext (funext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    exact ConcreteCategory.congr_hom
      ((CommAlgCat.squareCotangentComplexMap.{max u v w, max u v w, max u v w}
        (CommAlgCat.baseRingSquareTop (sectionsTowerHom J g h U))).comm i j) x

/-- Change of rings `- ⊗_B D` for presheaves of modules, along `h`. -/
noncomputable abbrev towerChangeOfRings :
    PresheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).obj ⥤
      PresheafOfModules.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj :=
  Stacks.PresheafOfModules.ChangeOfRings.changeOfRings h.hom

/-- The change-of-rings adjunction along `h`. -/
noncomputable abbrev towerChangeOfRingsAdjunction :
    towerChangeOfRings J h ⊣ PresheafOfModules.restrictScalars (towerRingMap J h) :=
  Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction h.hom

/-- Change of rings along `h` is additive, being a left adjoint. -/
instance : (towerChangeOfRings J h).Additive :=
  (towerChangeOfRingsAdjunction J h).left_adjoint_additive

/-- **The first vertex, sectionwise**: the complex of presheaves of `D`-modules
`U ↦ L_{B(U)/A(U)} ⊗_{B(U)} D(U)`, the degreewise change of rings along `h` of the sectionwise
cotangent complex of `A ⟶ B`. -/
noncomputable def sectionwiseBaseChangedCotangentComplex :
    CochainComplex (PresheafOfModules.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).obj) ℤ :=
  ((towerChangeOfRings J h).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (sectionwiseCotangentModuleComplex J g)

/-- **The sectionwise first map of the fundamental triangle**, `U ↦ (L_{B(U)/A(U)} ⊗ D(U) ⟶
L_{D(U)/A(U)})`: the transpose of `CategoryTheory.Sheaf.sectionwiseTowerBaseChangeMap` along the
change-of-rings adjunction. -/
noncomputable def sectionwiseTowerBaseChangeComplexMap :
    sectionwiseBaseChangedCotangentComplex J g h ⟶ sectionwiseCotangentModuleComplex J (g ≫ h) where
  f j := ((towerChangeOfRingsAdjunction J h).homEquiv _ _).symm
    ((sectionwiseTowerBaseChangeMap J g h).f j)
  comm' i j _ := by
    have h₁ := (towerChangeOfRingsAdjunction J h).homEquiv_naturality_right_symm
      ((sectionwiseTowerBaseChangeMap J g h).f i)
      ((sectionwiseCotangentModuleComplex J (g ≫ h)).d i j)
    have h₂ := (towerChangeOfRingsAdjunction J h).homEquiv_naturality_left_symm
      ((sectionwiseCotangentModuleComplex J g).d i j) ((sectionwiseTowerBaseChangeMap J g h).f j)
    refine h₁.symm.trans (Eq.trans ?_ h₂)
    exact congrArg ((towerChangeOfRingsAdjunction J h).homEquiv _ _).symm
      ((sectionwiseTowerBaseChangeMap J g h).comm i j)

end CategoryTheory.Sheaf

end
