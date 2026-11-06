module

public import StacksFrontier.Homology.Ext.CorepresentedHomComplex

/-!
# The comparison on the bounded below homotopy category

Let `A` be an abelian category and let `T : A ⥤ AddCommGrpCat` be an additive functor
corepresented by an object `Z`, the corepresentation being `e : Hom(Z, -) ≅ T`. There are two
functors on the homotopy category `K(A)` of cochain complexes in `A` that compute, in different
ways, the hypercohomology of `T`: the complex `L` may be pushed through `T` degreewise, sent to
the derived category of abelian groups and have its degree-`n` homology taken, or its image in
`D(A)` may be probed by morphisms out of `Z` placed in degree `0`. This file constructs the
natural transformation from the first to the second,

`Hⁿ(T(L)) ⟶ Hom_{D(A)}(Z[0], Q(L)⟦n⟧)`,

and shows that it is invertible at a K-injective complex.

## Main definitions

* `Stacks.Cohomology.Corepresented.homotopyHomologyFunctor`: `L ↦ Hⁿ(T(L))` on the homotopy
  category, universe-lifted.
* `Stacks.Cohomology.Corepresented.homotopyDerivedHomFunctor`: `L ↦ Hom_{D(A)}(Z[0], Q(L)⟦n⟧)`
  on the homotopy category, universe-lifted.
* `Stacks.Cohomology.Corepresented.homotopyComparison`: the natural transformation
  `Hⁿ(T(L)) ⟶ Hom_{D(A)}(Z[0], Q(L)⟦n⟧)` between the two.
* `Stacks.Cohomology.Corepresented.quotientCompHomotopyHomologyIso`,
  `Stacks.Cohomology.Corepresented.mapHomologyCompHomotopyHomIso`,
  `Stacks.Cohomology.Corepresented.homotopyHomCompQh`: the three natural transformations of
  functors on cochain complexes whose composite descends to `homotopyComparison`.
* `Stacks.Cohomology.Corepresented.singleQhQuotientIso`,
  `Stacks.Cohomology.Corepresented.qhQuotientShiftIso`: the isomorphisms of `D(A)` identifying
  `Z[0]` with `Qh` of its homotopy class, and `Qh` of the homotopy class of `L⟦n⟧` with the shift
  of `Qh` of the homotopy class of `L`.
* `Stacks.Cohomology.Corepresented.uliftNatTrans`: a family of additive maps between the values
  of two functors into `AddCommGrpCat` in different universes, natural on elements, as a natural
  transformation between their universe lifts.

## Main results

* `Stacks.Cohomology.Corepresented.isIso_homotopyComparison_app_quotient`: the comparison is
  invertible at a K-injective complex.
* `Stacks.Cohomology.Corepresented.qhQuotientShiftIso_hom_naturality`,
  `Stacks.Cohomology.Corepresented.qhHomMap_naturality`: naturality of `qhQuotientShiftIso` and
  of `qhHomMap` in the complex.
* `Stacks.Cohomology.Corepresented.bijective_qhHomMap`: `qhHomMap` is bijective at a K-injective
  complex.

## Implementation notes

* The three stages are statements about cochain complexes, so their composite is a natural
  transformation of functors precomposed with `HomotopyCategory.quotient`, descended to the
  homotopy category by `CategoryTheory.Quotient.natTransLift`.
* The homology of `T(L)` lies in `AddCommGrpCat.{v}` and the morphisms of `D(A)` in
  `AddCommGrpCat.{w}`; both sides are lifted to `AddCommGrpCat.{max v w}` by different
  universe-lift functors, which is why the third stage is built by `uliftNatTrans` rather than by
  whiskering.
* `DerivedCategory.Qh` is not exposed, so `HomotopyCategory.quotient A c ⋙ Qh = Q` does not hold
  definitionally; every passage between the two localization functors goes through
  `DerivedCategory.quotientCompQhIso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.Corepresented

universe w w' v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  (T : A ⥤ AddCommGrpCat.{v}) [T.Additive] [HasDerivedCategory.{w'} AddCommGrpCat.{v}]
  (Z : A) (e : preadditiveCoyoneda.obj (op Z) ≅ T) (n : ℤ)

/-- `L ↦ Hⁿ(T(L))` on the homotopy category: `T` applied degreewise, followed by the degree-`n`
homology in the derived category of `AddCommGrpCat.{v}`, lifted to `AddCommGrpCat.{max v w}`. -/
noncomputable abbrev homotopyHomologyFunctor :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ AddCommGrpCat.{max v w} :=
  T.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{v} n ⋙ AddCommGrpCat.uliftFunctor.{w, v}

/-- `L ↦ Hom_{D(A)}(Z[0], Q(L)⟦n⟧)` on the homotopy category, lifted to
`AddCommGrpCat.{max v w}`. -/
noncomputable abbrev homotopyDerivedHomFunctor :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ AddCommGrpCat.{max v w} :=
  DerivedCategory.Qh ⋙ shiftFunctor (DerivedCategory A) n ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj Z)) ⋙
      AddCommGrpCat.uliftFunctor.{v, w}

/-- On a cochain complex `L`, the homology of `T(L)` computed in the derived category of abelian
groups is the homology of the complex `T(L)` itself, naturally in `L`. -/
noncomputable def quotientCompHomotopyHomologyIso :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ homotopyHomologyFunctor T n ≅
      T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n ⋙
          AddCommGrpCat.uliftFunctor.{w, v} :=
  Functor.isoWhiskerRight (T.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      (DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v} n ⋙
        AddCommGrpCat.uliftFunctor.{w, v}) ≪≫
    Functor.isoWhiskerLeft (T.mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v})
        (DerivedCategory.homologyFunctor AddCommGrpCat.{v} n ⋙
          AddCommGrpCat.uliftFunctor.{w, v})) ≪≫
    Functor.isoWhiskerLeft (T.mapHomologicalComplex (ComplexShape.up ℤ))
      (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v} n)
        AddCommGrpCat.uliftFunctor.{w, v})

/-- The degree-`n` homology of `T` applied degreewise to a cochain complex `L` is the group of
morphisms `Z[0] ⟶ L⟦n⟧` in the homotopy category of `A`, naturally in `L`. -/
noncomputable def mapHomologyCompHomotopyHomIso :
    T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) n ⋙
          AddCommGrpCat.uliftFunctor.{w, v} ≅
      shiftFunctor (CochainComplex A ℤ) n ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        preadditiveCoyoneda.obj (op ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor A 0).obj Z))) ⋙ AddCommGrpCat.uliftFunctor.{w, v} :=
  NatIso.ofComponents
    (fun L => AddCommGrpCat.uliftFunctor.{w, v}.mapIso
      (corepresentedHomologyHomotopyIso T Z e L n))
    (fun {_ _} g => by
      have h := corepresentedHomologyHomotopyIso_hom_naturality T Z e g n
      dsimp only [Functor.comp_map, Functor.mapIso_hom]
      exact ((AddCommGrpCat.uliftFunctor.{w, v}.map_comp _ _).symm.trans
        (congrArg AddCommGrpCat.uliftFunctor.{w, v}.map h)).trans
        (AddCommGrpCat.uliftFunctor.{w, v}.map_comp _ _))

/-- The object `Z` placed in degree `0` inside `D(A)`, identified with the image under
`DerivedCategory.Qh` of the homotopy class of the single complex `Z[0]`. -/
noncomputable def singleQhQuotientIso :
    (DerivedCategory.singleFunctor A 0).obj Z ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj Z)) :=
  (DerivedCategory.singleFunctorIsoCompQ A 0).app Z ≪≫
    ((DerivedCategory.quotientCompQhIso A).app ((CochainComplex.singleFunctor A 0).obj Z)).symm

/-- The image under `DerivedCategory.Qh` of the homotopy class of `L⟦n⟧`, identified with the
`n`-fold shift in `D(A)` of the image of the homotopy class of `L`. -/
noncomputable def qhQuotientShiftIso (L : CochainComplex A ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (L⟦n⟧)) ≅
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L))⟦n⟧ :=
  DerivedCategory.Qh.mapIso
      (((HomotopyCategory.quotient A (ComplexShape.up ℤ)).commShiftIso n).app L) ≪≫
    (DerivedCategory.Qh.commShiftIso n).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)

omit [HasDerivedCategory.{w'} AddCommGrpCat.{v}] in
/-- `qhQuotientShiftIso` is natural in the complex: it intertwines the image under `Qh` of the
homotopy class of `g⟦n⟧` with the `n`-fold shift of the image of the homotopy class of `g`. -/
theorem qhQuotientShiftIso_hom_naturality {L L' : CochainComplex A ℤ} (g : L ⟶ L') :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧')) ≫
        (qhQuotientShiftIso (A := A) n L').hom =
      (qhQuotientShiftIso (A := A) n L).hom ≫
        (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g))⟦n⟧' := by
  dsimp only [qhQuotientShiftIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, ← DerivedCategory.Qh.map_comp,
    Functor.commShiftIso_hom_naturality (HomotopyCategory.quotient A (ComplexShape.up ℤ)) g n,
    DerivedCategory.Qh.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality DerivedCategory.Qh
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g) n, ← Category.assoc]

/-- The additive map `DerivedCategory.Qh` induces on morphisms out of the homotopy class of `Z[0]`
into that of `L⟦n⟧`, conjugated by `singleQhQuotientIso` and `qhQuotientShiftIso`. -/
noncomputable def qhHomMap (L : CochainComplex A ℤ) :
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj Z) ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (L⟦n⟧)) →+
    ((DerivedCategory.singleFunctor A 0).obj Z ⟶
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L))⟦n⟧) :=
  AddMonoidHom.mk' (fun f => (singleQhQuotientIso Z).hom ≫ DerivedCategory.Qh.map f ≫
      (qhQuotientShiftIso n L).hom)
    (fun f g => by
      rw [DerivedCategory.Qh.map_add, Preadditive.add_comp, Preadditive.comp_add])

omit [HasDerivedCategory.{w'} AddCommGrpCat.{v}] in
/-- The value of `qhHomMap` at a morphism. -/
theorem qhHomMap_apply (L : CochainComplex A ℤ)
    (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj Z) ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (L⟦n⟧)) :
    qhHomMap Z n L f =
      (singleQhQuotientIso Z).hom ≫ DerivedCategory.Qh.map f ≫ (qhQuotientShiftIso n L).hom :=
  rfl

omit [HasDerivedCategory.{w'} AddCommGrpCat.{v}] in
/-- `qhHomMap` is natural in the complex: postcomposition with the homotopy class of `g⟦n⟧`
before it agrees with postcomposition with the shifted image of the homotopy class of `g` after
it. -/
theorem qhHomMap_naturality {L L' : CochainComplex A ℤ} (g : L ⟶ L')
    (a : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj Z) ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (L⟦n⟧)) :
    qhHomMap Z n L' (a ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧')) =
      qhHomMap Z n L a ≫
        (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map g))⟦n⟧' := by
  rw [qhHomMap_apply, qhHomMap_apply, DerivedCategory.Qh.map_comp, Category.assoc,
    Category.assoc, qhQuotientShiftIso_hom_naturality n g]
  simp only [Category.assoc]

/-- A family of additive maps between the values of two functors into `AddCommGrpCat` in
different universes, natural on elements, as a natural transformation between their universe
lifts to `AddCommGrpCat.{max v w}`. -/
def uliftNatTrans {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{v})
    (G : C ⥤ AddCommGrpCat.{w}) (φ : ∀ X, F.obj X →+ G.obj X)
    (hφ : ∀ {X Y : C} (f : X ⟶ Y) (a : F.obj X), φ Y (F.map f a) = G.map f (φ X a)) :
    F ⋙ AddCommGrpCat.uliftFunctor.{w, v} ⟶ G ⋙ AddCommGrpCat.uliftFunctor.{v, w} where
  app X := AddCommGrpCat.ofHom
    (AddEquiv.ulift.symm.toAddMonoidHom.comp ((φ X).comp AddEquiv.ulift.toAddMonoidHom))
  naturality _ _ f := by
    ext a
    exact ULift.ext (hφ f a.down)

/-- The natural transformation pushing morphisms out of `Z[0]` in the homotopy category of `A`
into the derived category `D(A)` by `DerivedCategory.Qh`, given by `qhHomMap` at each complex. -/
noncomputable def homotopyHomCompQh :
    shiftFunctor (CochainComplex A ℤ) n ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        preadditiveCoyoneda.obj (op ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor A 0).obj Z))) ⋙ AddCommGrpCat.uliftFunctor.{w, v} ⟶
      HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        homotopyDerivedHomFunctor (A := A) Z n :=
  uliftNatTrans
    (shiftFunctor (CochainComplex A ℤ) n ⋙ HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
      preadditiveCoyoneda.obj (op ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor A 0).obj Z))))
    (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⋙
      shiftFunctor (DerivedCategory A) n ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj Z)))
    (qhHomMap Z n) (fun {_ _} g a => qhHomMap_naturality Z n g a)

/-- The comparison `Hⁿ(T(L)) ⟶ Hom_{D(A)}(Z[0], Q(L)⟦n⟧)` on the homotopy category, the descent
of the composite of `quotientCompHomotopyHomologyIso`, `mapHomologyCompHomotopyHomIso` and
`homotopyHomCompQh`. -/
noncomputable def homotopyComparison :
    homotopyHomologyFunctor T n ⟶ homotopyDerivedHomFunctor (A := A) Z n :=
  Quotient.natTransLift _ ((quotientCompHomotopyHomologyIso T n).hom ≫
    (mapHomologyCompHomotopyHomIso T Z e n).hom ≫ homotopyHomCompQh Z n)

/-- The comparison at the homotopy class of a cochain complex is the composite of the three
natural transformations at that complex. -/
theorem homotopyComparison_app_quotient (L : CochainComplex A ℤ) :
    (homotopyComparison T Z e n).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) =
      (quotientCompHomotopyHomologyIso T n).hom.app L ≫
        (mapHomologyCompHomotopyHomIso T Z e n).hom.app L ≫ (homotopyHomCompQh Z n).app L :=
  rfl

omit [HasDerivedCategory.{w'} AddCommGrpCat.{v}] in
/-- At a K-injective complex `L`, `qhHomMap` is bijective. -/
theorem bijective_qhHomMap (L : CochainComplex A ℤ) [L.IsKInjective] :
    Function.Bijective (qhHomMap Z n L) :=
  (Iso.homCongr (singleQhQuotientIso Z).symm (qhQuotientShiftIso n L)).bijective.comp
    (CochainComplex.IsKInjective.Qh_map_bijective _ (L⟦n⟧))

/-- The comparison is invertible at a K-injective complex. -/
instance isIso_homotopyComparison_app_quotient (L : CochainComplex A ℤ) [L.IsKInjective] :
    IsIso ((homotopyComparison T Z e n).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)) := by
  have hC : IsIso ((homotopyHomCompQh (A := A) Z n).app L) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨fun x y hxy => ?_, fun z => ?_⟩
    · exact ULift.ext ((bijective_qhHomMap Z n L).injective (congrArg ULift.down hxy))
    · obtain ⟨y, hy⟩ := (bijective_qhHomMap Z n L).surjective z.down
      exact ⟨ULift.up y, ULift.ext hy⟩
  rw [homotopyComparison_app_quotient]
  infer_instance

end Stacks.Cohomology.Corepresented

end
