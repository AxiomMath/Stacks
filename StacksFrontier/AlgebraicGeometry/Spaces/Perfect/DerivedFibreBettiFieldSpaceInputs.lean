module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiPointComparison

/-!
# Inputs for the independence of the fibre Betti numbers of the geometric point

The `i`-th Betti number of an object `E` of `D(𝒪_X)` at a geometric point `x̄` of an algebraic
space `X` is `AlgebraicGeometry.Space.geometricFibreBetti`. This file identifies it with the
dimension over `Γ(Spec κ(x̄), 𝒪)` of the global sections of `H^i(Lx̄^*E)` on the small étale site
of `Spec κ(x̄)`, and collects the facts about the spectrum of an algebraically closed field that
the comparison of two geometric points above one point of `|X|` consumes.

## Main results

* `AlgebraicGeometry.Space.geometricFibreBetti_eq_finrank_idChart`: the Betti number at `x̄` is
  `dim_{Γ(Spec κ(x̄))} Γ(Spec κ(x̄), H^i(Lx̄^*E))`.
* `AlgebraicGeometry.Space.homologyDerivedPullbackIsoOfIsFlat`: along a flat morphism the
  derived pullback is degreewise, so `H^i(Lf^*M) ≅ f^*H^i(M)`.
* `AlgebraicGeometry.Space.isFlat_fieldHom`: the morphism of algebraic spaces presented by a
  field-valued point of the space of a field spectrum is flat.
* `AlgebraicGeometry.Space.isField_geometricStalkRing_fieldValuedPointSpace`: the
  structure-sheaf fibre at a geometric point of the space of a field spectrum is a field.

## References

* [Stacks Project, Tag 0D1Y](https://stacks.math.columbia.edu/tag/0D1Y)
* [Stacks Project, Tag 04K3](https://stacks.math.columbia.edu/tag/04K3)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- Every derived category below is Mathlib's standard model, the one
`AlgebraicGeometry.Space.geometricFibreBetti` is stated at. -/
local instance (priority := 10000) standardDerivedModel (C : Type*) [Category* C] [Abelian C] :
    HasDerivedCategory C :=
  HasDerivedCategory.standard C

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The cohomology of a derived pullback along a flat morphism -/

section Flat

variable {X Y : AlgebraicSpaces B S hS}

/-- Degreewise pullback of `𝒪_Y`-modules, with source and target spelled as in `Lf^*`. -/
abbrev structureModulePullback (f : X ⟶ Y) :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ⥤
      SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) :=
  modulePullback B S hS f

/-- **The cohomology of a derived pullback along a flat morphism.** For a flat morphism
`f : X ⟶ Y` of algebraic spaces the derived pullback is degreewise pullback, because degreewise
pullback is then exact and both are left derived functors of it; so `H^i(Lf^*M) ≅ f^*H^i(M)`. -/
def homologyDerivedPullbackIsoOfIsFlat (f : X ⟶ Y) (hf : IsFlat B S hS f.hom) (i : ℤ)
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) i).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj M) ≅
      (structureModulePullback B S hS f).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) i).obj M) :=
  letI : PreservesFiniteLimits (structureModulePullback B S hS f) :=
    preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS f hf
  have _hleft : (structureModulePullback B S hS f).IsLeftAdjoint :=
    (modulePullbackAdjunction B S hS f).isLeftAdjoint
  letI : PreservesFiniteColimits (structureModulePullback B S hS f) := inferInstance
  have _hbip : PreservesBinaryBiproducts (structureModulePullback B S hS f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have _hadd : (structureModulePullback B S hS f).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  haveI : ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).Additive :=
    RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS f)
  have hF : (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules =
      structureModulePullback B S hS f :=
    congrArg (fun g : Stacks.Sheaves.RingedToposModules.RingedToposHom
        (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) => g.pullbackModules)
      (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
        (smallEtaleRingedToposHom B S hS f))
  let α := Functor.mapDerivedCategoryFactorsh (structureModulePullback B S hS f)
  haveI : (structureModulePullback B S hS f).mapDerivedCategory.IsLeftDerivedFunctor α.hom
      (smallEtaleModuleQuasiIso B S hS Y) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ α
  have eD : smallEtaleDerivedModulePullback B S hS f ≅
      (structureModulePullback B S hS f).mapDerivedCategory :=
    Functor.leftDerivedNatIso _ _ (smallEtaleDerivedModulePullbackComparison B S hS f) α.hom
      (smallEtaleModuleQuasiIso B S hS Y)
      (Functor.isoWhiskerRight
        (Stacks.Homology.mapHomotopyCategoryIso (eqToIso hF) (ComplexShape.up ℤ))
        DerivedCategory.Qh)
  (DerivedCategory.homologyFunctor _ i).mapIso (eD.app M) ≪≫
    ((structureModulePullback B S hS f).mapDerivedCategoryHomologyIso i).app M

end Flat

/-! ### The space of the spectrum of a field -/

section FieldSpace

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism presented by a field-valued point of a representable presheaf is the image
under the Yoneda embedding of the morphism of site objects that the point is. -/
theorem fieldHom_hom_eq_yoneda_map (p : FieldValuedPoint B S hS F)
    (z : FieldValuedPoint B S hS (fieldValuedPointSpace B S hS p).1) :
    (fieldHom B S hS (X := fieldValuedPointSpace B S hS p) z).hom = yoneda.map z.value :=
  yonedaEquiv.injective (by
    change yonedaEquiv (fieldMorphism B S hS (fieldValuedPointSpace B S hS p).1 z) = _
    rw [yonedaEquiv_fieldMorphism, yonedaEquiv_yoneda_map])

/-- The morphism of algebraic spaces presented by a morphism of spectra of fields is flat: the
target is a one-point integral scheme. -/
theorem isFlat_yoneda_map_fieldValuedPoint {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : FieldValuedPoint B S hS F) (q : FieldValuedPoint B S hS G)
    (κ : q.siteObject ⟶ p.siteObject) :
    IsFlat B S hS (yoneda.map κ) := by
  refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    _root_.AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget κ).2 ?_
  let _ : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) := by
    change Subsingleton (Spec (.of p.carrier)); infer_instance
  let _ : IsIntegral ((BigFppfOver.toScheme B S hS).obj p.siteObject) := by
    change IsIntegral (Spec (.of p.carrier)); infer_instance
  infer_instance

/-- The morphism of algebraic spaces presented by a field-valued point of the space of a field
spectrum is flat. -/
theorem isFlat_fieldHom (p : FieldValuedPoint B S hS F)
    (z : FieldValuedPoint B S hS (fieldValuedPointSpace B S hS p).1) :
    IsFlat B S hS (fieldHom B S hS (X := fieldValuedPointSpace B S hS p) z).hom := by
  rw [fieldHom_hom_eq_yoneda_map]
  exact isFlat_yoneda_map_fieldValuedPoint B S hS p z z.value

/-- The structure-sheaf fibre at a geometric point of the algebraic space of the spectrum of a
field is a field: it is the étale local ring, a strict henselization of a local ring of that
spectrum. -/
theorem isField_geometricStalkRing_fieldValuedPointSpace (p : FieldValuedPoint B S hS F)
    (z : GeometricPoint B S hS (fieldValuedPointSpace B S hS p).1) :
    IsField (geometricStalkRing B S hS (X := fieldValuedPointSpace B S hS p) z) :=
  (pointStalkRingEquiv B S hS (fieldValuedPointSpace B S hS p) z).isField
    (isField_etaleLocalRing_yoneda p.siteObject
      (fun x => _root_.AlgebraicGeometry.isField_stalk_Spec_field p.carrier x) z)

end FieldSpace

/-! ### The Betti numbers as dimensions of spaces of global sections -/

variable {X : AlgebraicSpaces B S hS}

/-- **The `i`-th Betti number of `E` at a geometric point `x̄` is `dim_{κ(x̄)} H^i(Lx̄^*E)`.** On
the spectrum of an algebraically closed field the fibre of a module at a geometric point is its
module of sections over the identity chart. -/
theorem geometricFibreBetti_eq_finrank_idChart
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (i : ℤ) (x : GeometricPoint B S hS X.1) :
    geometricFibreBetti B S hS E i x =
      Module.finrank
        ((ringedToposStructureRingSheaf B S hS (fieldValuedPointSpace B S hS x.val)).obj.obj
          (op (idChart B S hS x.val.siteObject)))
        (((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS
                (fieldValuedPointSpace B S hS x.val))) i).obj
            ((fieldPullback B S hS x.val).obj E)).val.obj
          (op (idChart B S hS x.val.siteObject))) := by
  have := x.property
  refine Eq.trans ((((Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (fieldValuedPointSpace B S hS x.val).1
        (tautologicalGeometricPoint B S hS x) (fieldValuedPointSpace B S hS x.val).2)
      (smallEtaleRingedTopos B S hS
        (fieldValuedPointSpace B S hS x.val)).O).mapDerivedCategoryHomologyIso i).app
    ((fieldPullback B S hS x.val).obj E)).toLinearEquiv.finrank_eq) ?_
  exact (finrank_idChart_eq_finrank_moduleStalk B S hS x.val
    (tautologicalGeometricPoint B S hS x)
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (fieldValuedPointSpace B S hS x.val))) i).obj
        ((fieldPullback B S hS x.val).obj E))).symm

end AlgebraicGeometry.Space

end
