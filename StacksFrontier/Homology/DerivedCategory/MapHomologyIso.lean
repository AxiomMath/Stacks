module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# An exact functor commutes with derived homology

For an exact functor `F` between abelian categories with derived categories, applying `F` on
derived categories and then taking `n`-th cohomology agrees with taking cohomology first. The
complex-level comparison is `CategoryTheory.Functor.mapHomologicalComplexHomologyIso`, lifted
through the localization `DerivedCategory.Q`.

That comparison is built by `CategoryTheory.Localization.liftNatIso` and therefore has **no
component formula**: its naturality is all a calculation can use. The three theorems below are
that naturality in the three readings a calculation meets — solved for the functor applied to a
cohomology map (`map_homologyFunctor_map`), solved for the cohomology of the functor's image
(`homologyFunctor_map_mapDerivedCategory_map`), and applied to a transformation into a model with
a commuting square whose vertical edges are the functor on derived categories
(`homologyFunctor_map_comp_eq_of_square`). None has any hypothesis beyond exactness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.DerivedCategoryHomology

/-- An exact functor commutes with the homology of complexes, degreewise: this is
`ShortComplex.mapHomologyIso` read as a natural isomorphism of homology functors. -/
noncomputable def mapHomologicalComplexHomologyIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {ι : Type*} (c : ComplexShape ι) (i : ι) :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c i ≅
      HomologicalComplex.homologyFunctor C c i ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc i).mapHomologyIso F)
    (fun φ => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C c i).map φ) F)

/-- An exact functor read on derived categories commutes with cohomology, degree by degree. -/
noncomputable def mapDerivedCategoryHomologyIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (i : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D i ≅
      DerivedCategory.homologyFunctor C i ⋙ F := by
  let Q := DerivedCategory.Q (C := C)
  let H := DerivedCategory.homologyFunctor D i
  let e : Q ⋙ (F.mapDerivedCategory ⋙ H) ≅
      Q ⋙ (DerivedCategory.homologyFunctor C i ⋙ F) :=
    (Functor.associator Q F.mapDerivedCategory H).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors H ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D i) ≪≫
      mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) i ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C i).symm F ≪≫
      Functor.associator _ _ _
  exact Localization.liftNatIso Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _ _ _ e

/-- **An exact functor applied to the degree-`i` cohomology of a morphism of derived categories.**
For `F` exact and `φ : K ⟶ L` in `D(C)`, `F` of `H^i(φ)` is `mapDerivedCategoryHomologyIso`
inverted at `K`, the degree-`i` cohomology of `F` read on derived categories applied to `φ`, and
the comparison at `L`.

`mapDerivedCategoryHomologyIso` is built by `CategoryTheory.Localization.liftNatIso` and so has no
component formula; its **naturality** is all a calculation can use, and this is that naturality
solved for the one factor a calculation meets — the exact functor applied to a cohomology map,
with the cohomology on the inside. There is no hypothesis on `φ`, on the degree or on the
objects. -/
theorem map_homologyFunctor_map
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (i : ℤ) {K L : DerivedCategory C} (φ : K ⟶ L) :
    F.map ((DerivedCategory.homologyFunctor C i).map φ) =
      (mapDerivedCategoryHomologyIso F i).inv.app K ≫
        (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategory.map φ) ≫
          (mapDerivedCategoryHomologyIso F i).hom.app L := by
  have h := (mapDerivedCategoryHomologyIso F i).hom.naturality φ
  simp only [Functor.comp_map] at h
  rw [h, ← Category.assoc, ← NatTrans.comp_app, (mapDerivedCategoryHomologyIso F i).inv_hom_id,
    NatTrans.id_app, Category.id_comp]

/-- **The degree-`i` cohomology of an exact functor's image of a morphism.** The reading of
`mapDerivedCategoryHomologyIso`'s naturality solved for the cohomology of the **image**, where
`map_homologyFunctor_map` solves it for the image of the cohomology. The two are the same
naturality square read in the two directions, and a calculation that meets the functor on the
outside needs this one.

`mapDerivedCategoryHomologyIso` is built by `CategoryTheory.Localization.liftNatIso` and so has no
component formula; its naturality is all that is used. There is no hypothesis on `φ`, on the
degree or on the objects. -/
theorem homologyFunctor_map_mapDerivedCategory_map
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (i : ℤ) {K L : DerivedCategory C} (φ : K ⟶ L) :
    (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategory.map φ) =
      (mapDerivedCategoryHomologyIso F i).hom.app K ≫
        F.map ((DerivedCategory.homologyFunctor C i).map φ) ≫
          (mapDerivedCategoryHomologyIso F i).inv.app L := by
  rw [map_homologyFunctor_map F i φ]
  simp

/-- **The degree-`i` cohomology of a square whose vertical edges are an exact functor read on
derived categories.** For `F` exact, a commuting square `m ≫ tL = tK ≫ F.mapDerivedCategory.map q`
in `D(D)`,

> `Hⁱ(m)` followed by `Hⁱ(tL)` is `Hⁱ(tK)` followed by `F` of `Hⁱ(q)` conjugated by
> `mapDerivedCategoryHomologyIso F i`.

This is the shape every step that carries a morphism across a model comparison with an exact
functor on top of it takes: the comparison's own naturality supplies the square, and the
conjugation is the only thing the exact functor contributes. The square is a **hypothesis** and
`q` is an **explicit** morphism rather than `Q.map c` for a functor `Q`, which matters in use: at
a composite `Q` the latter reading would force the composite spelling of `q` on the conclusion,
where the inner layer's own conjugation cannot be substituted for it.

There is no hypothesis on the objects, on the morphisms beyond the square, or on the degree. -/
theorem homologyFunctor_map_comp_eq_of_square
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (i : ℤ) {A B : DerivedCategory D} {A' B' : DerivedCategory C}
    {m : A ⟶ B} {tK : A ⟶ F.mapDerivedCategory.obj A'} {tL : B ⟶ F.mapDerivedCategory.obj B'}
    {q : A' ⟶ B'} (h : m ≫ tL = tK ≫ F.mapDerivedCategory.map q) :
    (DerivedCategory.homologyFunctor D i).map m ≫
        (DerivedCategory.homologyFunctor D i).map tL =
      (DerivedCategory.homologyFunctor D i).map tK ≫
        (mapDerivedCategoryHomologyIso F i).hom.app A' ≫
          F.map ((DerivedCategory.homologyFunctor C i).map q) ≫
            (mapDerivedCategoryHomologyIso F i).inv.app B' := by
  rw [← (DerivedCategory.homologyFunctor D i).map_comp, h,
    (DerivedCategory.homologyFunctor D i).map_comp,
    homologyFunctor_map_mapDerivedCategory_map F i q]

end StacksDraft.DerivedCategoryHomology
