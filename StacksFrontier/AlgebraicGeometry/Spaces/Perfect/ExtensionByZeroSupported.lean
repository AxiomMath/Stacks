module

public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# Extension by zero of objects supported on the closed complement of an elementary square

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`.  The stalk of the
extension by zero `f_!G` at a geometric point `x̄` of `Y` is the direct sum of the stalks of `G`
at the lifts of `x̄` (Equation 08GU).  This file draws the consequences of that formula for
supports, and specializes them to an elementary distinguished square `(U ⊆ X, j : V ⟶ X)` with
`T = |X| \ |U|`, where every geometric point over `T` has exactly one lift to `V`:

* the support of `f_!G` lies in `T` as soon as that of `G` lies in `f^{-1}T`;
* for `G` supported on `j^{-1}T` the unit `G ⟶ (j_!G)|_V` is an isomorphism — clause (2)(a) of
  Stacks 08GG — and `(j_!G)|_U = 0`;
* for `F` supported on `T` the counit `j_!(F|_V) ⟶ F` is an isomorphism.

All of these hold for modules and, by exactness of `j_!` and of restriction, degreewise for
objects of the derived categories.

## Main results

* `AlgebraicGeometry.Space.subsingleton_stalkSet_iff_isZero_sheafFiber`: the set-valued stalk of
  Stacks 04JY, through which `AlgebraicGeometry.Space.supportOfSheaf` is defined, is trivial
  exactly when the fibre at the point of the site of Stacks 04K0 vanishes.
* `AlgebraicGeometry.Space.supportOfSheaf_abelianEtaleExtensionByZero_subset` and
  `AlgebraicGeometry.Space.cohomologySupportedOn_etaleModuleLowerShriek_mapDerivedCategory`:
  Equation 08GU on supports, for sheaves and for derived objects.
* `isIso_etaleModuleLowerShriekAdjunction_unit_app_of_supportOfSheaf_subset` and
  `..._counit_app_...`, in the namespace `AlgebraicGeometry.Space`: the unit and counit of
  `f_! ⊣ f^*` on supported modules.
* `AlgebraicGeometry.Space.isIso_edsEtaleDerivedAdjunction_unit_app_of_cohomologySupportedOn`:
  **Stacks 08GG, clause (2)(a)**.
* `AlgebraicGeometry.Space.isIso_homologyFunctor_map_edsEtaleDerivedAdjunction_counit_app` and
  `AlgebraicGeometry.Space.isZero_edsDerivedRestrictOpen_shriek_of_cohomologySupportedOn`.
* `CategoryTheory.Adjunction.isIso_homologyFunctor_map_mapDerivedCategory_counit_app` and
  `..._unit_app`: the unit and counit of `CategoryTheory.Adjunction.mapDerivedCategory`, degree by
  degree.

## Implementation notes

The extension by zero is the one the library constructs,
`AlgebraicGeometry.Space.etaleModuleLowerShriek`, with its adjunction
`AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction`; on derived categories the adjunction
is `CategoryTheory.Adjunction.mapDerivedCategory` of it, both functors being exact (Stacks 03DJ).
The stalk computations are done on underlying abelian sheaves, at the points
`AlgebraicGeometry.Space.etaleSitePoint`, where Equation 08GU and Equation 08GT are available, and
are carried to modules through Tag 0798.  The source proves clause (2)(a) by a base change of the
square to `V`; at the level of stalks it is immediate, and that is the proof given here.

## References

* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 08GT](https://stacks.math.columbia.edu/tag/08GT)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u


namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- The degreewise counit of an adjunction of exact functors induces on the cohomology of a
complex in degree `i` the counit at that cohomology object, up to isomorphism. -/
theorem isIso_homologyFunctor_map_mapHomologicalComplex_counit_app (adj : F ⊣ G)
    (K : CochainComplex D ℤ) (i : ℤ)
    (hi : IsIso (adj.counit.app
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i).obj K))) :
    IsIso ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i).map
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K)) := by
  have : PreservesFiniteLimits (G ⋙ F) := comp_preservesFiniteLimits G F
  have : PreservesFiniteColimits (G ⋙ F) := comp_preservesFiniteColimits G F
  change IsIso (ShortComplex.homologyMap ((K.sc i).mapNatTrans adj.counit))
  rw [ShortComplex.homologyMap_mapNatTrans]
  have : IsIso (adj.counit.app (K.sc i).homology) := hi
  infer_instance

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- The degreewise unit of an adjunction of exact functors induces on the cohomology of a
complex in degree `i` the unit at that cohomology object, up to isomorphism. -/
theorem isIso_homologyFunctor_map_mapHomologicalComplex_unit_app (adj : F ⊣ G)
    (K : CochainComplex C ℤ) (i : ℤ)
    (hi : IsIso (adj.unit.app
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj K))) :
    IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).map
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K)) := by
  have : PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G
  have : PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G
  change IsIso (ShortComplex.homologyMap ((K.sc i).mapNatTrans adj.unit))
  rw [ShortComplex.homologyMap_mapNatTrans]
  have : IsIso (adj.unit.app (K.sc i).homology) := hi
  infer_instance

/-- **The counit of the derived adjunction, degree by degree.**  For an adjunction `F ⊣ G` of
exact functors and an object `X` of `D(D)`, the counit `F(G X) ⟶ X` of the induced adjunction
on derived categories is an isomorphism on `Hⁱ` as soon as the counit of `F ⊣ G` is an
isomorphism at `Hⁱ(X)`. -/
theorem isIso_homologyFunctor_map_mapDerivedCategory_counit_app (adj : F ⊣ G)
    (X : DerivedCategory D) (i : ℤ)
    (hi : IsIso (adj.counit.app ((DerivedCategory.homologyFunctor D i).obj X))) :
    IsIso ((DerivedCategory.homologyFunctor D i).map (adj.mapDerivedCategory.counit.app X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hK : IsIso (adj.counit.app
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i).obj K)) :=
    (NatTrans.isIso_app_iff_of_iso adj.counit
      (((DerivedCategory.homologyFunctor D i).mapIso e).symm ≪≫
        (DerivedCategory.homologyFunctorFactors D i).app K)).1 hi
  have hQ : IsIso ((DerivedCategory.homologyFunctor D i).map
      (DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K))) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors D i) _).2
      (isIso_homologyFunctor_map_mapHomologicalComplex_counit_app adj K i hK)
  have hc : IsIso ((DerivedCategory.homologyFunctor D i).map
      (adj.mapDerivedCategory.counit.app (DerivedCategory.Q.obj K))) := by
    rw [Adjunction.mapDerivedCategory, Adjunction.localization_counit_app]
    simp only [Functor.map_comp]
    infer_instance
  have hnat := adj.mapDerivedCategory.counit.naturality e.hom
  have hX : adj.mapDerivedCategory.counit.app X =
      (G.mapDerivedCategory ⋙ F.mapDerivedCategory).map e.inv ≫
        adj.mapDerivedCategory.counit.app (DerivedCategory.Q.obj K) ≫ e.hom := by
    rw [Functor.id_map] at hnat
    rw [← hnat, ← Category.assoc, ← Functor.map_comp, e.inv_hom_id, Functor.map_id,
      Category.id_comp]
  rw [hX]
  simp only [Functor.map_comp]
  infer_instance

/-- **The unit of the derived adjunction, degree by degree.**  For an adjunction `F ⊣ G` of
exact functors and an object `X` of `D(C)`, the unit `X ⟶ G(F X)` of the induced adjunction on
derived categories is an isomorphism on `Hⁱ` as soon as the unit of `F ⊣ G` is an isomorphism
at `Hⁱ(X)`. -/
theorem isIso_homologyFunctor_map_mapDerivedCategory_unit_app (adj : F ⊣ G)
    (X : DerivedCategory C) (i : ℤ)
    (hi : IsIso (adj.unit.app ((DerivedCategory.homologyFunctor C i).obj X))) :
    IsIso ((DerivedCategory.homologyFunctor C i).map (adj.mapDerivedCategory.unit.app X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have hK : IsIso (adj.unit.app
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i).obj K)) :=
    (NatTrans.isIso_app_iff_of_iso adj.unit
      (((DerivedCategory.homologyFunctor C i).mapIso e).symm ≪≫
        (DerivedCategory.homologyFunctorFactors C i).app K)).1 hi
  have hQ : IsIso ((DerivedCategory.homologyFunctor C i).map
      (DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K))) :=
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C i) _).2
      (isIso_homologyFunctor_map_mapHomologicalComplex_unit_app adj K i hK)
  have hc : IsIso ((DerivedCategory.homologyFunctor C i).map
      (adj.mapDerivedCategory.unit.app (DerivedCategory.Q.obj K))) := by
    rw [Adjunction.mapDerivedCategory, Adjunction.localization_unit_app]
    simp only [Functor.map_comp]
    infer_instance
  have hnat := adj.mapDerivedCategory.unit.naturality e.hom
  have hX : adj.mapDerivedCategory.unit.app X =
      e.inv ≫ adj.mapDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        (F.mapDerivedCategory ⋙ G.mapDerivedCategory).map e.hom := by
    rw [Functor.id_map] at hnat
    rw [← hnat, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [hX]
  simp only [Functor.map_comp]
  infer_instance

/-- **The unit of the derived adjunction is invertible** at an object of `D(C)` at all of whose
cohomology objects the unit of `F ⊣ G` is invertible. -/
theorem isIso_mapDerivedCategory_unit_app_of_forall (adj : F ⊣ G) (X : DerivedCategory C)
    (h : ∀ i, IsIso (adj.unit.app ((DerivedCategory.homologyFunctor C i).obj X))) :
    IsIso (adj.mapDerivedCategory.unit.app X) :=
  (DerivedCategory.isIso_iff _ _).2 fun i =>
    isIso_homologyFunctor_map_mapDerivedCategory_unit_app adj X i (h i)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The set-valued geometric stalk and the fibre at the point of the site agree on
vanishing.**  Both are filtered colimits of the same sections, over the small étale
neighbourhoods of `x̄` and over the elements of the geometric fibre respectively, and those two
index categories are isomorphic. -/
theorem subsingleton_stalkSet_iff_isZero_sheafFiber {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F)
    (G : Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}) :
    Subsingleton (stalkSet x (G.obj ⋙ forget AddCommGrpCat.{u})) ↔
      IsZero ((etaleSitePoint B S hS F x hF).sheafFiber.obj G) := by
  let p := etaleSitePoint B S hS F x hF
  let D := (Functor.Elements.π p.fiber).op ⋙ G.obj
  let e₀ : (D ⋙ forget AddCommGrpCat.{u}).ColimitType ≃
      stalkSet x (G.obj ⋙ forget AddCommGrpCat.{u}) :=
    { toFun := Quot.map
        (fun a => ⟨op ((fiberElementsToNeighborhood B S hS F x).obj a.1.unop), a.2⟩)
        (by
          rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
          exact ⟨((fiberElementsToNeighborhood B S hS F x).map f.unop).op, h⟩)
      invFun := Quot.map
        (fun a => ⟨op ((neighborhoodToFiberElements B S hS F x).obj a.1.unop), a.2⟩)
        (by
          rintro ⟨j, a⟩ ⟨k, b⟩ ⟨f, h⟩
          exact ⟨((neighborhoodToFiberElements B S hS F x).map f.unop).op, h⟩)
      left_inv := fun a => by induction a using Quot.inductionOn; rfl
      right_inv := fun a => by induction a using Quot.inductionOn; rfl }
  have hc := (Types.isColimit_iff_coconeTypesIsColimit _).1
    ⟨isColimitOfPreserves (forget AddCommGrpCat.{u}) (colimit.isColimit D)⟩
  let e : stalkSet x (G.obj ⋙ forget AddCommGrpCat.{u}) ≃ ToType (p.sheafFiber.obj G) :=
    e₀.symm.trans hc.equiv
  rw [isZero_addCommGrpCat_iff_subsingleton]
  exact e.subsingleton_congr

/-- A coproduct of zero abelian groups is zero. -/
theorem isZero_sigma_of_forall_isZero {I : Type u} (K : I → AddCommGrpCat.{u})
    (h : ∀ i, IsZero (K i)) : IsZero (∐ K) := by
  rw [IsZero.iff_id_eq_zero]
  exact Sigma.hom_ext _ _ fun i => (h i).eq_of_src _ _

/-- **Stacks 04KA through the points of the site.**  A point lies in the support of an abelian
sheaf exactly when the fibre of the sheaf at some geometric point above it is nonzero. -/
theorem mem_supportOfSheaf_iff_exists_not_isZero_sheafFiber (Z : AlgebraicSpaces B S hS)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u}) (pt : points B S hS Z.1) :
    pt ∈ supportOfSheaf B S hS Z.1 G ↔
      ∃ p : GeometricPoint B S hS Z.1, p.LiesOver pt ∧
        ¬ IsZero ((etaleSitePoint B S hS Z.1 p Z.2).sheafFiber.obj G) := by
  simp only [mem_supportOfSheaf_iff_exists, subsingleton_stalkSet_iff_isZero_sheafFiber B S hS Z.2]

/-- The fibre of an abelian sheaf at a geometric point whose image is outside the support
vanishes. -/
theorem isZero_sheafFiber_of_image_notMem_supportOfSheaf (Z : AlgebraicSpaces B S hS)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u}) (p : GeometricPoint B S hS Z.1)
    (hp : p.image ∉ supportOfSheaf B S hS Z.1 G) :
    IsZero ((etaleSitePoint B S hS Z.1 p Z.2).sheafFiber.obj G) := by
  by_contra h
  exact hp ((mem_supportOfSheaf_iff_exists_not_isZero_sheafFiber B S hS Z G _).2 ⟨p, rfl, h⟩)

/-- The support of an abelian sheaf is contained in that of an isomorphic sheaf. -/
private theorem supportOfSheaf_subset_of_isIso (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u}} (e : F ≅ G) :
    supportOfSheaf B S hS X F ⊆ supportOfSheaf B S hS X G :=
  supportOfSheaf_subset_of_mono B S hS X hX e.hom

section Etale

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- **Equation 08GU, on supports.**  If the support of an abelian sheaf `G` on `X` lies in the
inverse image of `T ⊆ |Y|` along an étale morphism `f : X ⟶ Y`, then the support of `f_!G`
lies in `T`: the stalk of `f_!G` at a geometric point is the direct sum of the stalks of `G` at
its lifts. -/
theorem supportOfSheaf_abelianEtaleExtensionByZero_subset
    (G : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) (T : Set (points B S hS Y.1))
    (hG : supportOfSheaf B S hS X.1 G ⊆ pointsMap B S hS X.1 f.hom ⁻¹' T) :
    supportOfSheaf B S hS Y.1 ((abelianEtaleExtensionByZero B S hS f hf).obj G) ⊆ T := by
  intro pt hpt
  obtain ⟨p, rfl, hp⟩ := (mem_supportOfSheaf_iff_exists_not_isZero_sheafFiber B S hS Y _ pt).1 hpt
  by_contra hT
  refine hp (IsZero.of_iso (isZero_sigma_of_forall_isZero _ fun t => ?_)
    (EtaleShriekStalk.stalkExtensionByZeroIso B S hS f hf p G))
  refine isZero_sheafFiber_of_image_notMem_supportOfSheaf B S hS X G _ fun h => hT ?_
  have h' := hG h
  rwa [Set.mem_preimage, ← geometricPointMap_image, geometricPointMap_liftGeometricPoint] at h'

/-- **The unit of extension by zero on stalks.**  At the point attached to a lift `t` of a
geometric point `x̄` of `Y`, the stalk of the unit `G ⟶ (f_!G)|_X`, followed by the
identifications of Equation 08GT and Equation 08GU, is the inclusion of the summand of `t`. -/
theorem sheafFiber_unit_comp_stalkExtensionByZeroIso (x : GeometricPoint B S hS Y.1)
    (t : GeometricPointLift B S hS f.hom x)
    (G : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :
    (liftSitePoint B S hS f t).sheafFiber.map
        ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).unit.app G) ≫
      (restrictionSheafFiberIso B S hS f hf t).hom.app
        ((abelianEtaleExtensionByZero B S hS f hf).obj G) ≫
      (EtaleShriekStalk.stalkExtensionByZeroIso B S hS f hf x G).hom =
    EtaleShriekStalk.liftedStalkι B S hS f x G t := by
  refine (liftSitePoint B S hS f t).presheafFiber_hom_ext fun W w => ?_
  refine ((liftSitePoint B S hS f t).toPresheafFiber_naturality_assoc
    ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).unit.app G).hom W w _).trans ?_
  have h := restrictionSheafFiberIso_toPresheafFiber B S hS f hf t
    ((abelianEtaleExtensionByZero B S hS f hf).obj G) W w
  exact (congrArg (fun k => ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).unit.app
      G).hom.app (op W) ≫ k) ((reassoc_of% h)
        (EtaleShriekStalk.stalkExtensionByZeroIso B S hS f hf x G).hom)).trans
    (EtaleShriekStalk.stalkExtensionByZeroIso_germ B S hS f hf x G W t w)

/-- A geometric point `ȳ` of `X` is a lift of its image `f(ȳ)`. -/
def selfLift (y : GeometricPoint B S hS X.1) :
    GeometricPointLift B S hS f.hom (geometricPointMap f.hom y) :=
  ⟨y.val.value, rfl⟩

/-- The geometric point attached to the lift `ȳ` of `f(ȳ)` is `ȳ`. -/
theorem liftGeometricPoint_selfLift (y : GeometricPoint B S hS X.1) :
    liftGeometricPoint B S hS f (selfLift B S hS f y) = y :=
  rfl

/-- **The unit of extension by zero of modules, on underlying abelian sheaves**, is the unit of
abelian extension by zero followed by the restriction of the comparison of Tag 0798. -/
theorem toSheaf_map_etaleModuleLowerShriekAdjunction_unit_app (M : Modules.{u, u} B S hS X.1 X.2) :
    (SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).map
        ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app M) =
      (abelianEtaleExtensionByZeroAdjunction B S hS f hf).unit.app
          ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj M) ≫
        (abelianEtaleRestriction B S hS f hf).map
          ((etaleModuleShriekForgetIso B S hS f hf).hom.app M) := by
  have h := (abelianEtaleExtensionByZeroAdjunction B S hS f hf).homEquiv_unit
    ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj M)
    ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj
      ((etaleModuleLowerShriek B S hS f hf).obj M))
    ((etaleModuleShriekForgetIso B S hS f hf).hom.app M)
  refine Eq.trans ?_ h
  exact (Equiv.apply_symm_apply _ _).symm

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

/-- The support of the module extension by zero, through Tag 0798. -/
theorem supportOfSheaf_toSheaf_etaleModuleLowerShriek_subset
    (M : Modules.{u, u} B S hS X.1 X.2) (T : Set (points B S hS Y.1))
    (hM : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj M) ⊆
      pointsMap B S hS X.1 f.hom ⁻¹' T) :
    supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj
      ((etaleModuleLowerShriek B S hS f hf).obj M)) ⊆ T :=
  (supportOfSheaf_subset_of_isIso B S hS Y.1 Y.2
    ((etaleModuleShriekForgetIso B S hS f hf).app M).symm).trans
    (supportOfSheaf_abelianEtaleExtensionByZero_subset B S hS f hf _ T hM)

/-- **The unit of extension by zero is invertible on modules supported over a set of points
with at most one lift.**  Let `f : X ⟶ Y` be étale and `T ⊆ |Y|` a set of points such that every
geometric point of `Y` over `T` has at most one lift to `X`.  If a sheaf of `𝒪_X`-modules `M` is
supported on `f^{-1}T`, then the unit `M ⟶ (f_!M)|_X` is an isomorphism.

At a geometric point `ȳ` of `X` over `f^{-1}T` the stalk of the unit is the inclusion of the
summand of `ȳ` into the stalk of Equation 08GU, which has only that summand; at any other
geometric point both stalks vanish, the target because `f_!M` is supported on `T`. -/
theorem isIso_etaleModuleLowerShriekAdjunction_unit_app_of_supportOfSheaf_subset
    (T : Set (points B S hS Y.1))
    (hT : ∀ x : GeometricPoint B S hS Y.1, x.image ∈ T →
      Subsingleton (GeometricPointLift B S hS f.hom x))
    (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj M) ⊆
      pointsMap B S hS X.1 f.hom ⁻¹' T) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS f hf).unit.app M) := by
  refine isIso_of_isIso_geometricModuleStalk B S hS X.1 X.2 (etaleRingSheaf B S hS X) _
    fun v => isIso_edsModuleStalk_of_isIso_sheafFiber B S hS _ v ?_
  set M' := (SheafOfModules.toSheaf (etaleRingSheaf B S hS X)).obj M
  have hmap := (congrArg (etaleSitePoint B S hS X.1 v X.2).sheafFiber.map
    (toSheaf_map_etaleModuleLowerShriekAdjunction_unit_app B S hS f hf M)).trans
      ((etaleSitePoint B S hS X.1 v X.2).sheafFiber.map_comp _ _)
  refine (congrArg IsIso hmap).mpr (@IsIso.comp_isIso _ _ _ _ _ _ _ ?_
    (Iso.isIso_hom ((etaleSitePoint B S hS X.1 v X.2).sheafFiber.mapIso
      ((abelianEtaleRestriction B S hS f hf).mapIso
        ((etaleModuleShriekForgetIso B S hS f hf).app M)))))
  set t := selfLift B S hS f v
  by_cases hx : (geometricPointMap f.hom v).image ∈ T
  · have := hT _ hx
    have : Unique (GeometricPointLift B S hS f.hom (geometricPointMap f.hom v)) :=
      uniqueOfSubsingleton t
    let e := (restrictionSheafFiberIso B S hS f hf t).app
        ((abelianEtaleExtensionByZero B S hS f hf).obj M') ≪≫
      EtaleShriekStalk.stalkExtensionByZeroIso B S hS f hf _ M'
    have h : (liftSitePoint B S hS f t).sheafFiber.map
        ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).unit.app M') =
        EtaleShriekStalk.liftedStalkι B S hS f (geometricPointMap f.hom v) M' t ≫ e.inv :=
      (Iso.eq_comp_inv e).2 (sheafFiber_unit_comp_stalkExtensionByZeroIso B S hS f hf _ t M')
    have : IsIso (EtaleShriekStalk.liftedStalkι B S hS f (geometricPointMap f.hom v) M' t) :=
      EtaleShriekStalk.isIso_sigma_ι_of_unique _ t
    exact (congrArg IsIso h).mpr (@IsIso.comp_isIso _ _ _ _ _ _ _ this (Iso.isIso_inv e))
  · refine isIso_of_source_target_iso_zero _
      (isZero_sheafFiber_of_image_notMem_supportOfSheaf B S hS X M' v fun h => hx (hM h)).isoZero
      (IsZero.of_iso ?_ ((restrictionSheafFiberIso B S hS f hf t).app
        ((abelianEtaleExtensionByZero B S hS f hf).obj M'))).isoZero
    exact isZero_sheafFiber_of_image_notMem_supportOfSheaf B S hS Y _ _ fun h =>
      hx (supportOfSheaf_abelianEtaleExtensionByZero_subset B S hS f hf M' T hM h)

/-- **The counit of extension by zero is invertible on modules supported on a set of points
with exactly one lift.**  Let `f : X ⟶ Y` be étale and `T ⊆ |Y|` a set of points such that every
geometric point of `Y` over `T` has exactly one lift to `X`.  If a sheaf of `𝒪_Y`-modules `N` is
supported on `T`, then the counit `f_!(N|_X) ⟶ N` is an isomorphism.

At a geometric point over `T` this is the counit formula of Equation 08GU with one summand; at
any other geometric point both stalks vanish, the source because `N|_X` is supported on
`f^{-1}T`. -/
theorem isIso_etaleModuleLowerShriekAdjunction_counit_app_of_supportOfSheaf_subset
    (T : Set (points B S hS Y.1))
    (hT : ∀ x : GeometricPoint B S hS Y.1, x.image ∈ T →
      Nonempty (Unique (GeometricPointLift B S hS f.hom x)))
    (N : Modules.{u, u} B S hS Y.1 Y.2)
    (hN : supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj N) ⊆
      T) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS f hf).counit.app N) := by
  refine isIso_of_isIso_geometricModuleStalk B S hS Y.1 Y.2 (etaleRingSheaf B S hS Y) _
    fun x => isIso_edsModuleStalk_of_isIso_sheafFiber B S hS _ x ?_
  refine isIso_sheafFiber_toSheaf_etaleModuleCounit B S hS f hf x N ?_
  set N' := (SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj N
  by_cases hx : x.image ∈ T
  · obtain ⟨hu⟩ := hT x hx
    exact EtaleShriekStalk.isIso_sheafFiber_counit_of_unique B S hS f hf x N'
  · refine isIso_of_source_target_iso_zero _
      (isZero_sheafFiber_of_image_notMem_supportOfSheaf B S hS Y _ x fun h => hx ?_).isoZero
      (isZero_sheafFiber_of_image_notMem_supportOfSheaf B S hS Y N' x fun h => hx (hN h)).isoZero
    refine supportOfSheaf_abelianEtaleExtensionByZero_subset B S hS f hf _ T ?_ h
    rw [supportOfSheaf_sheafPushforwardContinuous_smallEtalePostcomp]
    exact Set.preimage_mono hN

end Etale

section Derived

attribute [local instance] HasDerivedCategory.standard
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

/-- **Equation 08GU, for derived objects.**  Let `f : X ⟶ Y` be an étale morphism of algebraic
spaces and `T ⊆ |Y|`.  If `F` in `D(𝒪_X)` is supported on `f^{-1}T`, then `f_!F` is supported
on `T`: extension by zero is exact, so `Hⁱ(f_!F) = f_!Hⁱ(F)`, and the stalk formula applies. -/
theorem cohomologySupportedOn_etaleModuleLowerShriek_mapDerivedCategory
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (T : Set (points B S hS Y.1)) (F : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hF : CohomologySupportedOn B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T) F) :
    CohomologySupportedOn B S hS Y.1 Y.2 T
      ((etaleModuleLowerShriek B S hS f hf).mapDerivedCategory.obj F) := fun i =>
  (supportOfSheaf_subset_of_isIso B S hS Y.1 Y.2
    ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).mapIso
      (((etaleModuleLowerShriek B S hS f hf).mapDerivedCategoryHomologyIso i).app F))).trans
    (supportOfSheaf_toSheaf_etaleModuleLowerShriek_subset B S hS f hf _ T (hF i))

end Derived

section Square

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The adjunction `j_! ⊣ (-)|_V` of extension by zero along the étale morphism `j : V ⟶ X` of an
elementary distinguished square, on unbounded derived categories. -/
abbrev edsEtaleDerivedAdjunction :=
  Adjunction.mapDerivedCategory
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))

/-- **Stacks 08GG, clause (2)(a), on modules.**  For an elementary distinguished square
`(U ⊆ X, j : V ⟶ X)` and a sheaf of `𝒪_V`-modules `G` supported on `j^{-1}T`, `T = |X| \ |U|`,
the unit `G ⟶ (j_!G)|_V` is an isomorphism: a geometric point of `X` over `T` has exactly one
lift to `V`. -/
theorem isIso_edsEtale_unit_app_of_supportOfSheaf_subset
    (G : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)
    (hG : supportOfSheaf B S hS (edsEtale B S hS hsq).1
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).obj G) ⊆
        edsEtalePreimageComplementPoints B S hS hsq) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).unit.app G) :=
  isIso_etaleModuleLowerShriekAdjunction_unit_app_of_supportOfSheaf_subset B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) (edsComplementPoints B S hS Uo)
    (fun x hx => subsingleton_geometricPointLift_of_notMem_range_pointsMap B S hS W.2 Uo fV hsq x
      hx) G hG

/-- **The counit `j_!(F|_V) ⟶ F` of an elementary distinguished square is an isomorphism on a
module `F` supported on `T = |X| \ |U|`**: a geometric point of `X` over `T` has exactly one
lift to `V`. -/
theorem isIso_edsEtale_counit_app_of_supportOfSheaf_subset
    (F : Modules.{u, u} B S hS W.1 W.2)
    (hF : supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).obj F) ⊆
      edsComplementPoints B S hS Uo) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).counit.app F) :=
  isIso_etaleModuleLowerShriekAdjunction_counit_app_of_supportOfSheaf_subset B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq) (edsComplementPoints B S hS Uo)
    (fun x hx => ⟨unique_geometricPointLift_edsEtaleHom_of_notMem B S hS hsq x hx⟩) F hF

/-- **The restriction to `U` of the extension by zero of a module supported on `j^{-1}T`
vanishes**, `T = |X| \ |U|`: the extension by zero is supported on `T`, which `U` misses. -/
theorem isZero_edsOpen_restrict_shriek_of_supportOfSheaf_subset
    (G : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)
    (hG : supportOfSheaf B S hS (edsEtale B S hS hsq).1
      ((SheafOfModules.toSheaf (etaleRingSheaf B S hS (edsEtale B S hS hsq))).obj G) ⊆
        edsEtalePreimageComplementPoints B S hS hsq) :
    IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).obj ((etaleModuleLowerShriek B S hS
        (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).obj G)) := by
  refine isZero_of_supportOfSheaf_eq_empty B S hS _ _ (Set.eq_empty_of_forall_notMem fun y hy => ?_)
  rw [supportOfSheaf_toSheaf_etaleModulePullback] at hy
  exact supportOfSheaf_toSheaf_etaleModuleLowerShriek_subset B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq) G _ hG hy ⟨y, rfl⟩

/-- **Stacks 08GG, clause (2)(a).**  Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished
square of algebraic spaces and `T = |X| \ |U|`.  For an object `F` of `D(𝒪_V)` supported on
`j^{-1}T` the unit `F ⟶ (j_!F)|_V` of the derived adjunction `j_! ⊣ (-)|_V` is an
isomorphism.

Both functors are exact, so on cohomology the derived unit is the unit at `Hⁱ(F)`, which is an
isomorphism by the stalk computation of Equation 08GU, the square having exactly one lift of
each geometric point over `T`. -/
@[stacks 08GG "clause (2)(a): F ⟶ (j_!F)|_V is an isomorphism for F supported on j^{-1}T"]
theorem isIso_edsEtaleDerivedAdjunction_unit_app_of_cohomologySupportedOn
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsIso ((edsEtaleDerivedAdjunction B S hS hsq).unit.app F) :=
  Adjunction.isIso_mapDerivedCategory_unit_app_of_forall _ F fun i =>
    isIso_edsEtale_unit_app_of_supportOfSheaf_subset B S hS hsq _ (hF i)

/-- **The derived counit `j_!(E|_V) ⟶ E` is an isomorphism on `Hⁱ` as soon as `Hⁱ(E)` is
supported on `T = |X| \ |U|`.** -/
theorem isIso_homologyFunctor_map_edsEtaleDerivedAdjunction_counit_app
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) (i : ℤ)
    (hE : supportOfSheaf B S hS W.1 ((SheafOfModules.toSheaf (etaleRingSheaf B S hS W)).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).obj E)) ⊆
        edsComplementPoints B S hS Uo) :
    IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS W.1 W.2) i).map
      ((edsEtaleDerivedAdjunction B S hS hsq).counit.app E)) :=
  Adjunction.isIso_homologyFunctor_map_mapDerivedCategory_counit_app _ E i
    (isIso_edsEtale_counit_app_of_supportOfSheaf_subset B S hS hsq _ hE)

/-- **The restriction to `U` of `j_!F` vanishes for `F` in `D(𝒪_V)` supported on `j^{-1}T`.** -/
theorem isZero_edsDerivedRestrictOpen_shriek_of_cohomologySupportedOn
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (hF : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) F) :
    IsZero ((edsDerivedRestrictOpen B S hS hsq).obj ((etaleModuleLowerShriek B S hS
      (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)) := by
  refine DerivedCategory.isZero_of_forall_isZero_homology fun i => ?_
  refine IsZero.of_iso ?_ (((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategoryHomologyIso i).app _ ≪≫
    (etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).mapIso
      (((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategoryHomologyIso i).app F))
  exact isZero_edsOpen_restrict_shriek_of_supportOfSheaf_subset B S hS hsq _ (hF i)

end Square

end AlgebraicGeometry.Space
