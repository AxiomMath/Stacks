module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunctionUnit
public import StacksFrontier.Homology.Tor.IndependenceSquareLocalization

/-!
# Derived extension of scalars through a localization, and its cohomology

Two readings of derived extension of scalars that the affine reduction of Stacks 0DJ8 consumes.

*Through a localization.* For `A₂` a localization of `A` and `B` an `A₂`-algebra, derived
extension of scalars from `A` to `B` applied to an `A₂`-complex read over `A` is derived
extension of scalars from `A₂` to `B`:

`(N|_A) ⊗ᴸ_A B  ≅  N ⊗ᴸ_{A₂} B`.

This is the relative form of the idempotence of
`RingTheory.TorIndependence.restrictScalarsDerivedExtendIso`, obtained from it and the
scalar-tower composition isomorphism of derived extension of scalars.

*Cohomology of a flat extension.* For `f` flat, extension of scalars is exact, so derived
extension of scalars along `f` is the degreewise functor read on derived categories, and
therefore commutes with cohomology:

`H^n(K ⊗ᴸ_R T)  ≅  T ⊗_R H^n(K)`.

## Main definitions

* `RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso`: the first isomorphism.
* `RingTheory.TorIndependence.flatDerivedHomologyIso`: the second.

## Main results

* `RingTheory.TorIndependence.preservesColimits_totalDerivedExtensionScalars`: derived extension
  of scalars preserves colimits, being a left adjoint. This is the hypothesis the dévissage
  `StacksDraft.CompactDevissage.isIso_of_isIso_app_regularModule` asks of a functor out of
  `D(R)`, and it was not recorded anywhere.
* `RingTheory.TorIndependence.homology_derivedUnit_comp_flatDerivedHomologyIso_hom` and
  `RingTheory.TorIndependence.flatDerivedHomologyIso_inv_app_one_tmul`: **the value of
  `flatDerivedHomologyIso` on a generator.** The second says that the inverse of the comparison
  carries `1 ⊗ z` to the image of `z` under `H^n` of the unit `N ⟶ (N ⊗ᴸ_R T)|_R` of the derived
  change-of-rings adjunction, read through
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` for restriction of scalars; the first is
  the morphism-level identity it comes from. Only naturality and the `includeLeft`/`includeRight`
  equivariance of this comparison were recorded, and a diagram chase that meets it at a pure
  tensor cannot proceed on those.

## Implementation notes

The model of the derived category is a binder `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]` for
each ring, not `HasDerivedCategory.standard`: a statement proved at one model says nothing about
another, and the consumers of Stacks 0DJ8 work at a locally small model.

The flat case is `RingTheory.TorIndependence.flatDerivedExtensionScalarsIso` followed by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`; the `PreservesFiniteLimits` instance that
the second asks for is the one the first already needs, supplied by
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`.

*The value on a generator.* Both sides of the morphism-level identity are morphisms of functors
out of `D(R)`, so it is enough to prove it on the image of `DerivedCategory.Q`, which is
`CategoryTheory.Localization.natTrans_ext`. There the unit of the derived adjunction is the
degreewise unit, by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq`, and the
comparison with the degreewise action of extension of scalars is pinned down by
`RingTheory.TorIndependence.totalDerivedExtensionScalarsIsoMapDerivedCategory_app_comp_factors`;
what is left is a statement about `CategoryTheory.Functor.mapHomologicalComplexHomologyIso` and
the degreewise unit, which is the naturality of `CategoryTheory.ShortComplex.mapHomologyIso` in
the *functor* (`CategoryTheory.ShortComplex.homologyMap_mapNatTrans`) together with its
composition law (`CategoryTheory.ShortComplex.mapHomologyIso_comp_hom`). The reduction of a
component of `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at a complex is a
`CategoryTheory.Localization.liftNatTrans_app`, as for
`RingTheory.TorIndependence.restrictScalarsDerivedExtendIso_hom_app_Q`, and the whole chase is
run with every category, functor and morphism a variable, so that `rw` has only abstract
composites to match.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

universe u w v₁ v₂ u₁ u₂ t

namespace RingTheory.TorIndependence

section Degreewise

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- **The homology comparison of an adjoint pair of exact functors carries the degreewise unit to
the unit.** For `adj : L ⊣ R'` an adjunction of exact additive functors and `K` a homological
complex, the homology of the degreewise unit `K ⟶ R'(L(K))`, read through the comparisons of `R'`
and of `L` with homology, is the unit at `H^i(K)`.

Both comparisons are `CategoryTheory.ShortComplex.mapHomologyIso` at the short complex computing
`H^i(K)`; the identity is then the naturality of that isomorphism in the functor
(`CategoryTheory.ShortComplex.homologyMap_mapNatTrans`, at `adj.unit : 𝟭 ⟶ L ⋙ R'`) together
with its composition law. The comparison for the identity functor, which the naturality leaves
on the other side, is itself the identity: the composition law at `𝟭 ⋙ 𝟭` makes it idempotent,
and it is invertible. -/
private lemma mapHomologicalComplexHomologyIso_unit_comp (L : C ⥤ D) (R' : D ⥤ C)
    [L.Additive] [R'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (adj : L ⊣ R') {ι : Type t} (c : ComplexShape ι) (i : ι)
    (K : HomologicalComplex C c) :
    (HomologicalComplex.homologyFunctor C c i).map
          ((NatTrans.mapHomologicalComplex adj.unit c).app K) ≫
        (R'.mapHomologicalComplexHomologyIso c i).hom.app
            ((L.mapHomologicalComplex c).obj K) ≫
          R'.map ((L.mapHomologicalComplexHomologyIso c i).hom.app K) =
      adj.unit.app ((HomologicalComplex.homologyFunctor C c i).obj K) := by
  have : (L ⋙ R').PreservesHomology := Functor.preservesHomology_comp L R'
  set S := (HomologicalComplex.shortComplexFunctor C c i).obj K with hS
  have hid : (S.mapHomologyIso (𝟭 C)).hom = CategoryStruct.id S.homology := by
    have hsq : (S.mapHomologyIso (𝟭 C)).hom
        = (S.mapHomologyIso (𝟭 C)).hom ≫ (S.mapHomologyIso (𝟭 C)).hom :=
      ShortComplex.mapHomologyIso_comp_hom S (𝟭 C) (𝟭 C)
    exact ((cancel_epi (S.mapHomologyIso (𝟭 C)).hom).mp
      ((Category.comp_id _).trans hsq)).symm
  have key : ShortComplex.homologyMap (S.mapNatTrans adj.unit) =
      (S.mapHomologyIso (𝟭 C)).hom ≫ adj.unit.app S.homology ≫
        (S.mapHomologyIso (L ⋙ R')).inv :=
    ShortComplex.homologyMap_mapNatTrans S adj.unit
  have hcomp : (S.mapHomologyIso (L ⋙ R')).hom =
      ((S.map L).mapHomologyIso R').hom ≫ R'.map (S.mapHomologyIso L).hom :=
    ShortComplex.mapHomologyIso_comp_hom S L R'
  have hgoal : ShortComplex.homologyMap (S.mapNatTrans adj.unit) ≫
      (S.mapHomologyIso (L ⋙ R')).hom = adj.unit.app S.homology := by
    rw [key, hid]
    simp
  rw [hcomp] at hgoal
  exact hgoal

end Degreewise

section QLevel

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  [HasDerivedCategory.{w} C₁] [HasDerivedCategory.{w} C₂]

/-- **The homology comparison on the derived category, against the factorization of the
degreewise action.** At `Q.obj K`, the comparison
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` composed after the inverse of the
factorization `CategoryTheory.Functor.mapDerivedCategoryFactors` is the comparison on complexes,
read through the factorizations of the two homology functors. This is the form in which a
diagram chase meets it, the factorization being what the unit of a derived adjunction brings
with it.

The comparison is the one on complexes descended along `DerivedCategory.Q`, so its component at
`Q.obj K` is a `CategoryTheory.Localization.liftNatTrans_app`; the factorization then cancels
against the one that reduction produces. -/
private lemma mapDerivedCategoryHomologyIso_factors_inv_comp
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) (K : CochainComplex C₁ ℤ) :
    (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.inv.app K) ≫
        (F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
          F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app K) := by
  have hQ : (F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
            F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app K) := by
    simp only [Functor.mapDerivedCategoryHomologyIso, Functor.mapDerivedCategoryHomologyIsoAux,
      Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compLeft_iso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id,
      Localization.Lifting.compRight_iso]
    rfl
  rw [hQ, ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end QLevel

section Chase

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- **The homology of the unit of a derived adjunction, at a complex.** Let `adj : L ⊣ R'` be an
adjunction of exact additive functors, let `F : D(A) ⥤ D(B)` be a model of the left derived
functor of `L` with comparison `cmp` invertible at `P`, let `θ` be the unit of the derived
adjunction at `Q.obj P` — written out by hypothesis `h1` — and let `χ` identify `F` with the
degreewise action of `L` compatibly with the two comparisons, by hypothesis `h2`. Then the
homology of `θ`, read through the homology comparisons of `R'` and of `L`, is the unit of `adj`
at `H^n(Q.obj P)`.

Everything in sight is a variable, which is what makes the chase run: the derived unit is
expanded by `h1`, the two components of
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` are expanded at the complex, the
factorizations cancel, and what is left is
`RingTheory.TorIndependence.mapHomologicalComplexHomologyIso_unit_comp` conjugated by
`DerivedCategory.homologyFunctorFactors`. -/
private lemma homology_derivedUnit_app_Q
    (L : A ⥤ B) (R' : B ⥤ A) [L.Additive] [R'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    (adj : L ⊣ R') (n : ℤ) (F : DerivedCategory A ⥤ DerivedCategory B)
    (cmp : DerivedCategory.Q ⋙ F ⟶
      L.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (P : CochainComplex A ℤ) (hcmp : IsIso (cmp.app P))
    (θ : DerivedCategory.Q.obj P ⟶
      R'.mapDerivedCategory.obj (F.obj (DerivedCategory.Q.obj P)))
    (χ : F.obj (DerivedCategory.Q.obj P) ⟶
      L.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
    (h1 : θ = DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P) ≫
        R'.mapDerivedCategoryFactors.inv.app
            ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          R'.mapDerivedCategory.map (inv (cmp.app P)))
    (h2 : χ ≫ L.mapDerivedCategoryFactors.hom.app P = cmp.app P) :
    (DerivedCategory.homologyFunctor A n).map θ ≫
        (R'.mapDerivedCategoryHomologyIso n).hom.app (F.obj (DerivedCategory.Q.obj P)) ≫
          R'.map ((DerivedCategory.homologyFunctor B n).map χ ≫
            (L.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj P)) =
      adj.unit.app ((DerivedCategory.homologyFunctor A n).obj (DerivedCategory.Q.obj P)) := by
  have := hcmp
  have hχ : inv (cmp.app P) ≫ χ = L.mapDerivedCategoryFactors.inv.app P := by
    rw [← cancel_epi (cmp.app P), ← Category.assoc, IsIso.hom_inv_id, Category.id_comp,
      ← h2, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id χ).symm
  have hB : (DerivedCategory.homologyFunctor B n).map (inv (cmp.app P)) ≫
        (DerivedCategory.homologyFunctor B n).map χ ≫
          (L.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj P) =
      (DerivedCategory.homologyFunctorFactors B n).hom.app
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (L.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app P ≫
          L.map ((DerivedCategory.homologyFunctorFactors A n).inv.app P) := by
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hχ]
    exact mapDerivedCategoryHomologyIso_factors_inv_comp L n P
  have hA := mapDerivedCategoryHomologyIso_factors_inv_comp R' n
    ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have hu : (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app P =
      (NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app P := rfl
  have nρ := (R'.mapDerivedCategoryHomologyIso n).hom.naturality (inv (cmp.app P))
  dsimp only [Functor.comp_map] at nρ
  have nh : (DerivedCategory.homologyFunctor A n).map
          (DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app P)) ≫
        (DerivedCategory.homologyFunctorFactors A n).hom.app
          ((R'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) =
      (DerivedCategory.homologyFunctorFactors A n).hom.app P ≫
        (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).map
          ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app P) :=
    (DerivedCategory.homologyFunctorFactors A n).hom.naturality
      ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app P)
  have nu := adj.unit.naturality ((DerivedCategory.homologyFunctorFactors A n).inv.app P)
  dsimp only [Functor.id_map, Functor.comp_map] at nu
  rw [h1, hu, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.assoc, reassoc_of% nρ, reassoc_of% hA,
    ← CategoryTheory.Functor.map_comp, hB, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id_app_assoc, CategoryTheory.Functor.map_comp, reassoc_of% nh,
    reassoc_of% (mapHomologicalComplexHomologyIso_unit_comp L R' adj
      (ComplexShape.up ℤ) n P), ← nu, Iso.hom_inv_id_app_assoc]
  rfl

end Chase

section Localization

variable {A A₂ B : Type u} [CommRing A] [CommRing A₂] [CommRing B] [Algebra A A₂]
  (S : Submonoid A) [IsLocalization S A₂] (g : A₂ →+* B)
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} A₂)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

include S in
/-- **Derived extension of scalars through a localization.** For `A₂` a localization of `A` and
`B` an `A₂`-algebra, derived extension of scalars from `A` to `B`, applied to an `A₂`-complex read
over `A`, is derived extension of scalars from `A₂` to `B`.

Three steps: the scalar-tower composition isomorphism splits `- ⊗ᴸ_A B` as `- ⊗ᴸ_A A₂ ⊗ᴸ_{A₂} B`,
the idempotence `(-|_A) ⊗ᴸ_A A₂ ≅ -` of `restrictScalarsDerivedExtendIso` kills the first factor,
and the unitor removes the identity functor it leaves behind. -/
public def restrictScalarsDerivedExtendCompIso :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} (g.comp (algebraMap A A₂))).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} g).functor :=
  Functor.isoWhiskerLeft _
      (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) g).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictScalarsDerivedExtendIso.{u, w} S (A₂ := A₂))
      (totalDerivedExtensionScalars.{u, u, u} g).functor ≪≫
    Functor.leftUnitor _

end Localization

section Flat

variable {R T : Type u} [CommRing R] [CommRing T]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} T)]

/-- **Cohomology commutes with derived extension of scalars along a flat map.** For `f` flat,
extension of scalars is exact, so derived extension of scalars along `f` is the degreewise
functor read on derived categories, and an exact functor commutes with cohomology. -/
public def flatDerivedHomologyIso (f : R →+* T) (hf : f.Flat) (n : ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} T) n ≅
      DerivedCategory.homologyFunctor (ModuleCat.{u} R) n ⋙
        ModuleCat.extendScalars.{u, u, u} f :=
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  Functor.isoWhiskerRight (flatDerivedExtensionScalarsIso.{u, w} f hf) _ ≪≫
    (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategoryHomologyIso n

/-- **What `flatDerivedHomologyIso` does, as a morphism of functors.** For `f` flat the
comparison `H^n(K ⊗ᴸ_R T) ≅ T ⊗_R H^n(K)` is characterized by the unit of the derived
change-of-rings adjunction: the homology of the unit `N ⟶ (N ⊗ᴸ_R T)|_R`, read over `R` through
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` for restriction of scalars and then
through the comparison, is the underived unit `z ↦ 1 ⊗ z` at `H^n(N)`.

Both sides are morphisms of functors out of `D(R)`, so it suffices to check them on the image of
`DerivedCategory.Q`, where
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq` writes the
unit out degreewise. -/
public theorem homology_derivedUnit_comp_flatDerivedHomologyIso_hom (f : R →+* T) (hf : f.Flat)
    (n : ℤ) (N : DerivedCategory (ModuleCat.{u} R)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          ((@derivedExtensionScalarsAdjunction.{u, u, u, w, w} R T _ _ f _ _
            (totalDerivedExtensionScalars.{u, u, u} f).functor
            (totalDerivedExtensionScalars.{u, u, u} f).comparison
            (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).unit.app N) ≫
        ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryHomologyIso n).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj N) ≫
          (ModuleCat.restrictScalars.{u} f).map
            ((flatDerivedHomologyIso.{u, w} f hf n).hom.app N) =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj N) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  have key : Functor.whiskerRight
          (@derivedExtensionScalarsAdjunction.{u, u, u, w, w} R T _ _ f _ _
            (totalDerivedExtensionScalars.{u, u, u} f).functor
            (totalDerivedExtensionScalars.{u, u, u} f).comparison
            (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).unit
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n) ≫
        Functor.whiskerLeft (totalDerivedExtensionScalars.{u, u, u} f).functor
          ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryHomologyIso n).hom ≫
        Functor.whiskerRight (flatDerivedHomologyIso.{u, w} f hf n).hom
          (ModuleCat.restrictScalars.{u} f) =
      Functor.whiskerLeft (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n)
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) (fun P => ?_)
    have hid : (mapHomologicalComplexIsoOfExtendScalars f
          (ModuleCat.extendScalars.{u, u, u} f) (Iso.refl _)).hom.app P =
        CategoryStruct.id _ :=
      CategoryTheory.Functor.map_id _ _
    have hfac : (flatDerivedExtensionScalarsIso.{u, w} f hf).hom.app
            (DerivedCategory.Q.obj P) ≫
          (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app P =
        (totalDerivedExtensionScalars.{u, u, u} f).comparison.app P :=
      (totalDerivedExtensionScalarsIsoMapDerivedCategory_app_comp_factors f
        (ModuleCat.extendScalars.{u, u, u} f) (Iso.refl _) P).trans
        ((congrArg (fun z => (totalDerivedExtensionScalars.{u, u, u} f).comparison.app P ≫ z)
          hid).trans (Category.comp_id _))
    have hcmp : IsIso ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) :=
      hfac ▸ (inferInstance : IsIso
        ((flatDerivedExtensionScalarsIso.{u, w} f hf).hom.app (DerivedCategory.Q.obj P) ≫
          (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategoryFactors.hom.app P))
    have h1 := @derivedExtensionScalarsAdjunction_unit_app_eq.{u, u, u, w, w} R T _ _ f _ _
      (totalDerivedExtensionScalars.{u, u, u} f).functor
      (totalDerivedExtensionScalars.{u, u, u} f).comparison
      (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived P hcmp
    exact homology_derivedUnit_app_Q (ModuleCat.extendScalars.{u, u, u} f)
      (ModuleCat.restrictScalars.{u} f) (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f) n
      (totalDerivedExtensionScalars.{u, u, u} f).functor
      (totalDerivedExtensionScalars.{u, u, u} f).comparison P hcmp _ _ h1 hfac
  exact NatTrans.congr_app key N

/-- **The value of `flatDerivedHomologyIso` on a generator.** For `f` flat the inverse of the
comparison `H^n(K ⊗ᴸ_R T) ≅ T ⊗_R H^n(K)` carries `1 ⊗ z` to the image of `z` under `H^n` of the
unit `N ⟶ (N ⊗ᴸ_R T)|_R` of the derived change-of-rings adjunction, read over `R` through
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` for restriction of scalars.

Since every element of `T ⊗_R H^n(N)` is a sum of such generators, this determines the
comparison; it is `homology_derivedUnit_comp_flatDerivedHomologyIso_hom` read on an element. -/
public theorem flatDerivedHomologyIso_inv_app_one_tmul (f : R →+* T) (hf : f.Flat) (n : ℤ)
    (N : DerivedCategory (ModuleCat.{u} R))
    (z : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj N) :
    ((flatDerivedHomologyIso.{u, w} f hf n).app N).inv.hom ((1 : T) ⊗ₜ[R, f] z) =
      (((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryHomologyIso n).hom.app
            ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj N)).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          ((@derivedExtensionScalarsAdjunction.{u, u, u, w, w} R T _ _ f _ _
            (totalDerivedExtensionScalars.{u, u, u} f).functor
            (totalDerivedExtensionScalars.{u, u, u} f).comparison
            (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).unit.app N)).hom z) := by
  have hw := congrArg (fun φ => ModuleCat.Hom.hom φ z)
    (homology_derivedUnit_comp_flatDerivedHomologyIso_hom.{u, w} f hf n N)
  exact (congrArg (fun x => ((flatDerivedHomologyIso.{u, w} f hf n).app N).inv.hom x)
    hw.symm).trans (ModuleCat.inv_hom_apply _ _)

end Flat

section Colimits

variable {R T : Type u} [CommRing R] [CommRing T]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} T)]

/-- **Derived extension of scalars preserves colimits**, being a left adjoint: its right adjoint
is derived restriction of scalars, by the derived change-of-rings adjunction of Stacks 0GMT.

This is what a dévissage along the compact generator of `D(R)` —
`StacksDraft.CompactDevissage.isIso_of_isIso_app_regularModule` — asks of a functor out of
`D(R)`. -/
public theorem preservesColimits_totalDerivedExtensionScalars (f : R →+* T) :
    Limits.PreservesColimitsOfSize.{w, w} (totalDerivedExtensionScalars.{u, u, u} f).functor :=
  (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u, w, w}
    R T _ _ f _ _ (totalDerivedExtensionScalars.{u, u, u} f).functor
    (totalDerivedExtensionScalars.{u, u, u} f).comparison
    (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).leftAdjoint_preservesColimits

end Colimits

end RingTheory.TorIndependence

end
