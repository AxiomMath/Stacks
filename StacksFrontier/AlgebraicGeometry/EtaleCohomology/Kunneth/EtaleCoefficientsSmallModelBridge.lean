module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.RingedSiteHom
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingedToposSiteHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.RingedSiteHomTwoReadingsOfRingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorIsoCompositionDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorIsoOfIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness

/-!
# The two small models of the small étale ringed topos

Let `X` be a scheme and `Λ` a commutative ring. The development has two presentations of the
ringed topos `(X_étale, Λ̲)` as a ringed topos whose site, morphisms and ring sections share the
universe `u + 1`:

* `Stacks.EtaleCohomology.etaleRingedSite Λ X`, on the small model `AsSmall X.Etale`, through
  which the sheaves of `Λ`-modules `Stacks.EtaleCohomology.EtaleModules Λ X` and the results on
  them (the projection formula [Stacks, Tag 0F0G], the Künneth formula [Stacks, Tag 0F14]) are
  read on derived categories of modules over a ringed topos;
* `Stacks.EtaleCohomology.EtaleCoefficients.ringedTopos Λ X`, on the small model
  `SmallModel X.Etale`, on which the Künneth section of the étale cohomology chapter is
  formalized.

The two small models are equivalent to `X.Etale`, hence to each other, compatibly with the
topologies and with the constant structure sheaves. This file makes the comparison a morphism of
ringed topoi `ι_X` from the second presentation to the first (`smallModelHom`), shows that its
derived pullback is an equivalence of derived categories
(`isEquivalence_smallModelDerivedPullback`), and that `ι` commutes with the morphisms of ringed
topoi of a morphism of schemes `f : X ⟶ Y` up to an isomorphism compatible with the structure maps
(`fSharpCompatible_smallModelSquare`).
The derived pullbacks then commute by Stacks 0D6D, compatibly with Stacks 07A4, so the projection
maps of the two presentations are invertible at corresponding objects
(`isIso_projectionMap_smallModel_iff`).

## Main definitions

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `smallModelTopos Λ X`: the ringed topos of `etaleRingedSite Λ X`.
* `smallModelHom Λ X`: the comparison `ι_X : ringedTopos Λ' X ⟶ smallModelTopos Λ X`, with
  `Λ' = ULift Λ`.
* `smallModelDerivedPullback Λ X`: its derived pullback `D(smallModelTopos Λ X) ⥤ D(X_étale, Λ')`.
* `smallModelDerivedPullbackSquareIso Λ f`: `Lι_Y ⋙ f⁻¹ ≅ Lf^* ⋙ Lι_X`.

## Main results

* `isEquivalence_smallModelDerivedPullback`: `Lι_X` is an equivalence.
* `fSharpCompatible_smallModelSquare`: the 2-isomorphism `ι_Y ∘ f ≅ f ∘ ι_X` of morphisms of
  ringed topoi, and `tensorCompat_smallModelDerivedPullbackSquareIso`: the induced
  `Lι_Y ⋙ f⁻¹ ≅ Lf^* ⋙ Lι_X` is compatible with Stacks 07A4.
* `isIso_projectionMap_smallModel_iff` and `isIso_projectionFormulaMap_smallModel_iff`: the two
  variants of the projection map of `f` on the two presentations.
* `isFlat_smallModelHom_pullbackTopos_obj`, `isFlat_smallModelHomInv_pullbackTopos_obj`: the
  comparisons carry flat sheaves of modules to flat ones.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.RingedToposSiteHom (constantRingedTopos IsConstantFSharp constantHom
  isConstantFSharp_constantHom)

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

/-- Presheaves of commutative rings in the universe `u + 1` on `SmallModel X.Etale` admit a
sheafification. This and the next instance are local: instance search through the imports of this
file otherwise meets a generic instance whose universe it cannot pin. -/
local instance (priority := high) hasWeakSheafify_topology_commRingCat (X : Scheme.{u}) :
    HasWeakSheafify (topology X) CommRingCat.{u + 1} :=
  sheafToPresheaf_isRightAdjoint _ _

/-- Presheaves of commutative rings in the universe `u + 1` on `AsSmall X.Etale` admit a
sheafification. -/
local instance (priority := high) hasWeakSheafify_etaleSmallModelTopology_commRingCat
    (X : Scheme.{u}) : HasWeakSheafify (etaleSmallModelTopology.{u, 0} X) CommRingCat.{u + 1} :=
  sheafToPresheaf_isRightAdjoint _ _

/-! ### The comparison of the two small models -/

section Site

variable (X : Scheme.{u})

/-- The comparison of the two small models of the small étale site. -/
abbrev smallModelComparison : AsSmall.{u + 1} X.Etale ⥤ Site X :=
  AsSmall.down ⋙ fromEtale X

/-- The comparison in the other direction. -/
abbrev smallModelComparisonInv : Site X ⥤ AsSmall.{u + 1} X.Etale :=
  toEtale X ⋙ AsSmall.up

/-- The comparison of the two small models is continuous. -/
instance isContinuous_smallModelComparison :
    (smallModelComparison X).IsContinuous (etaleSmallModelTopology.{u, 0} X) (topology X) :=
  Functor.isContinuous_comp _ _ _ X.smallEtaleTopology _

/-- The comparison in the other direction is continuous. -/
instance isContinuous_smallModelComparisonInv :
    (smallModelComparisonInv X).IsContinuous (topology X) (etaleSmallModelTopology.{u, 0} X) :=
  Functor.isContinuous_comp _ _ _ X.smallEtaleTopology _

/-- The comparison of the two small models is representably flat. -/
instance representablyFlat_smallModelComparison : RepresentablyFlat (smallModelComparison X) := by
  haveI : (AsSmall.down : AsSmall.{u + 1} X.Etale ⥤ X.Etale).IsRightAdjoint :=
    (AsSmall.equiv : X.Etale ≌ AsSmall.{u + 1} X.Etale).toAdjunction.isRightAdjoint
  exact RepresentablyFlat.comp _ _

/-- The comparison in the other direction is representably flat. -/
instance representablyFlat_smallModelComparisonInv :
    RepresentablyFlat (smallModelComparisonInv X) := by
  haveI : (AsSmall.up : X.Etale ⥤ AsSmall.{u + 1} X.Etale).IsRightAdjoint :=
    (AsSmall.equiv : X.Etale ≌ AsSmall.{u + 1} X.Etale).symm.toAdjunction.isRightAdjoint
  exact RepresentablyFlat.comp _ _

/-- The comparison of the two small models is a morphism of sites. -/
theorem isMorphismOfSites_smallModelComparison :
    (smallModelComparison X).IsMorphismOfSites (etaleSmallModelTopology.{u, 0} X) (topology X) :=
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

/-- The comparison in the other direction is a morphism of sites. -/
theorem isMorphismOfSites_smallModelComparisonInv :
    (smallModelComparisonInv X).IsMorphismOfSites (topology X)
      (etaleSmallModelTopology.{u, 0} X) :=
  Functor.isMorphismOfSites_of_representablyFlat _ _ _

/-- The two comparisons compose to the identity of `SmallModel X.Etale`, up to the counit of
the equivalence with `X.Etale`. -/
def smallModelComparisonCounitIso :
    𝟭 (Site X) ≅ smallModelComparisonInv X ⋙ smallModelComparison X :=
  (equiv X).counitIso.symm

/-- The two comparisons compose to the identity of `AsSmall X.Etale`, up to the unit of the
equivalence of `SmallModel X.Etale` with `X.Etale`. -/
def smallModelComparisonUnitIso :
    𝟭 (AsSmall.{u + 1} X.Etale) ≅ smallModelComparison X ⋙ smallModelComparisonInv X :=
  NatIso.ofComponents
    (fun V => (AsSmall.up.{u, u + 1, u + 1} : X.Etale ⥤ AsSmall.{u + 1} X.Etale).mapIso
      ((equiv X).unitIso.app (AsSmall.down.obj V)))
    (fun {V W} g => by
      have := (equiv X).unitIso.hom.naturality (AsSmall.down.map g)
      exact congrArg (AsSmall.up.{u, u + 1, u + 1} : X.Etale ⥤ AsSmall.{u + 1} X.Etale).map this)

end Site

/-! ### The comparison as a morphism of ringed topoi -/

section Ringed

variable (Λ : Type) [CommRing Λ]

/-- The coefficient ring `ULift Λ` of the two presentations, as a commutative ring in the
universe `u + 1`. -/
abbrev smallModelCoefficients : CommRingCat.{u + 1} := CommRingCat.of (ULift.{u + 1} Λ)

/-- **The ringed topos `(X_étale, Λ̲)` on the small model `AsSmall X.Etale`**: the ringed site
`Stacks.EtaleCohomology.etaleRingedSite Λ X` read as a ringed topos. -/
abbrev smallModelTopos (X : Scheme.{u}) : RingedTopos.{u + 1, u + 1, u + 1} :=
  RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (etaleRingedSite.{u, 0} Λ X)

/-- **The comparison `ι_X : (X_étale, Λ̲) ⟶ (X_étale, Λ̲)` of the two small models**, from the
presentation on `SmallModel X.Etale` to the one on `AsSmall X.Etale`: the comparison functor
`AsSmall X.Etale ⥤ SmallModel X.Etale` with the structure map induced by the sheafification
unit. -/
def smallModelHom (X : Scheme.{u}) :
    RingedToposSiteHom (ringedTopos (ULift.{u + 1} Λ) X) (smallModelTopos Λ X) :=
  constantHom (R := smallModelCoefficients.{u} Λ) (JC := topology X)
    (JD := etaleSmallModelTopology.{u, 0} X) (smallModelComparison X)

/-- The comparison in the other direction. -/
def smallModelHomInv (X : Scheme.{u}) :
    RingedToposSiteHom (smallModelTopos Λ X) (ringedTopos (ULift.{u + 1} Λ) X) :=
  constantHom (R := smallModelCoefficients.{u} Λ) (JC := etaleSmallModelTopology.{u, 0} X)
    (JD := topology X) (smallModelComparisonInv X)

/-- The underlying functor of `smallModelHom Λ X` is `smallModelComparison X`. -/
theorem smallModelHom_u (X : Scheme.{u}) : (smallModelHom Λ X).u = smallModelComparison X :=
  rfl

/-- The structure map of `smallModelHom Λ X` is constant. -/
theorem isConstantFSharp_smallModelHom (X : Scheme.{u}) :
    IsConstantFSharp (R := smallModelCoefficients.{u} Λ) (JC := topology X)
      (JD := etaleSmallModelTopology.{u, 0} X) (smallModelHom Λ X) :=
  isConstantFSharp_constantHom _

/-- The structure map of `smallModelHomInv Λ X` is constant. -/
theorem isConstantFSharp_smallModelHomInv (X : Scheme.{u}) :
    IsConstantFSharp (R := smallModelCoefficients.{u} Λ)
      (JC := etaleSmallModelTopology.{u, 0} X) (JD := topology X) (smallModelHomInv Λ X) :=
  isConstantFSharp_constantHom _

/-- The underlying functor of `smallModelHom Λ X` is a morphism of sites. -/
theorem isMorphismOfSites_smallModelHom (X : Scheme.{u}) :
    (smallModelHom Λ X).u.IsMorphismOfSites (smallModelTopos Λ X).J
      (ringedTopos (ULift.{u + 1} Λ) X).J :=
  isMorphismOfSites_smallModelComparison X

/-- The structure map of the morphism of ringed topoi of a morphism of schemes, on the
presentation by `SmallModel X.Etale`, is constant. -/
theorem isConstantFSharp_ringedToposHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsConstantFSharp (R := smallModelCoefficients.{u} Λ) (JC := topology X)
      (JD := topology Y) (ringedToposHom (ULift.{u + 1} Λ) f) :=
  isConstantFSharp_constantHom (baseChange f)

/-- The structure map of the morphism of ringed topoi of a morphism of schemes, on the
presentation by `AsSmall X.Etale`, is constant. -/
theorem isConstantFSharp_etaleRingedSiteHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsConstantFSharp (R := smallModelCoefficients.{u} Λ)
      (JC := etaleSmallModelTopology.{u, 0} X) (JD := etaleSmallModelTopology.{u, 0} Y)
      (etaleRingedSiteHom.{u, 0} Λ f).toRingedToposSiteHom :=
  etaleRingedSiteFSharp_toSheafify.{u, 0} Λ f

end Ringed

/-! ### The comparison carries flatness -/

section Flat

variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The underlying functor of `smallModelHomInv Λ X` is a morphism of sites. -/
theorem isMorphismOfSites_smallModelHomInv :
    (smallModelHomInv Λ X).u.IsMorphismOfSites (ringedTopos (ULift.{u + 1} Λ) X).J
      (smallModelTopos Λ X).J :=
  isMorphismOfSites_smallModelComparisonInv X

/-- **The pullback along the comparison `ι_X` carries flat sheaves of modules on
`AsSmall X.Etale` to flat sheaves of modules on `SmallModel X.Etale`** (Stacks 05VD). -/
theorem isFlat_smallModelHom_pullbackTopos_obj
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (smallModelTopos Λ X).O) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (ringedTopos (ULift.{u + 1} Λ) X).O) ((smallModelHom Λ X).pullbackTopos.obj M) :=
  RingedToposSiteHom.pullbackPreservesIsFlat.{u + 1} (smallModelHom Λ X)
    (isMorphismOfSites_smallModelHom Λ X) M hM

/-- **The pullback along the comparison in the other direction carries flat sheaves of modules on
`SmallModel X.Etale` to flat sheaves of modules on `AsSmall X.Etale`** (Stacks 05VD). -/
theorem isFlat_smallModelHomInv_pullbackTopos_obj
    (M : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} Λ) X).O))
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (ringedTopos (ULift.{u + 1} Λ) X).O) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (smallModelTopos Λ X).O) ((smallModelHomInv Λ X).pullbackTopos.obj M) :=
  RingedToposSiteHom.pullbackPreservesIsFlat.{u + 1} (smallModelHomInv Λ X)
    (isMorphismOfSites_smallModelHomInv Λ X) M hM

end Flat

/-! ### The derived pullback along the comparison is an equivalence -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- The derived pullback along the comparison of the two small models exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_smallModelHom :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      (smallModelHom Λ X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy.{u + 1}
    (smallModelHom Λ X) (isMorphismOfSites_smallModelHom Λ X)

/-- **The derived pullback `Lι_X : D(smallModelTopos Λ X) ⥤ D(X_étale, ULift Λ)`** along the
comparison of the two small models. -/
abbrev smallModelDerivedPullback :
    DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O)) ⥤
      DerivedModules (ULift.{u + 1} Λ) X :=
  Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback (smallModelHom Λ X)

/-- The pullback of sheaves of modules along the comparison of the two small models is an
equivalence. -/
instance isEquivalence_smallModelHom_pullbackTopos :
    (smallModelHom Λ X).pullbackTopos.IsEquivalence :=
  RingedToposSiteHom.isEquivalence_pullbackTopos.{u + 1} (φ := smallModelHom Λ X)
    (ψ := smallModelHomInv Λ X) (isConstantFSharp_smallModelHom Λ X)
    (isConstantFSharp_smallModelHomInv Λ X) (smallModelComparisonCounitIso X)
    (smallModelComparisonUnitIso X)

/-- The pullback of sheaves of modules along the comparison of the two small models is
additive. -/
instance additive_smallModelHom_pullbackTopos : (smallModelHom Λ X).pullbackTopos.Additive :=
  RingedToposSiteHom.pullbackTopos_additive.{u + 1} (smallModelHom Λ X)

/-- **The derived pullback along the comparison is computed degreewise**: the pullback of sheaves
of modules is an equivalence, hence exact. -/
def smallModelDerivedPullbackMapIso :
    smallModelDerivedPullback Λ X ≅ (smallModelHom Λ X).pullbackTopos.mapDerivedCategory :=
  haveI : (smallModelHom Λ X).pullbackTopos.mapDerivedCategory.IsLeftDerivedFunctor
      (smallModelHom Λ X).pullbackTopos.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O)) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O)) (ComplexShape.up ℤ)) _
      (smallModelHom Λ X).pullbackTopos.mapDerivedCategoryFactorsh
  Functor.leftDerivedNatIso (smallModelDerivedPullback Λ X)
    (smallModelHom Λ X).pullbackTopos.mapDerivedCategory
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison
      (smallModelHom Λ X))
    (smallModelHom Λ X).pullbackTopos.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O)) (ComplexShape.up ℤ))
    (Iso.refl _)

/-- **The derived pullback along the comparison of the two small models is an equivalence of
derived categories.** -/
instance isEquivalence_smallModelDerivedPullback : (smallModelDerivedPullback Λ X).IsEquivalence :=
  haveI : (smallModelHom Λ X).pullbackTopos.asEquivalence.functor.Additive :=
    additive_smallModelHom_pullbackTopos Λ X
  haveI : (smallModelHom Λ X).pullbackTopos.asEquivalence.inverse.Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (smallModelHom Λ X).pullbackTopos.mapDerivedCategory.IsEquivalence :=
    (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence
      (smallModelHom Λ X).pullbackTopos.asEquivalence).isEquivalence_functor
  Functor.isEquivalence_of_iso (smallModelDerivedPullbackMapIso Λ X).symm

variable {Λ} {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The morphism of ringed topoi of a morphism of schemes on the presentation by
`AsSmall X.Etale`. -/
abbrev smallModelToposHom :
    RingedToposSiteHom (smallModelTopos Λ X) (smallModelTopos Λ Y) :=
  (etaleRingedSiteHom.{u, 0} Λ f).toRingedToposSiteHom

/-- The underlying functor of `smallModelToposHom f` is a morphism of sites. -/
theorem isMorphismOfSites_smallModelToposHom :
    (smallModelToposHom (Λ := Λ) f).u.IsMorphismOfSites (smallModelTopos Λ Y).J
      (smallModelTopos Λ X).J :=
  (etaleRingedSiteHom.{u, 0} Λ f).isMorphismOfSites_toRingedToposSiteHom

/-- **The square of comparisons and base changes**: the base change along `f` on
`AsSmall _.Etale` followed by the comparison for `X`, and the comparison for `Y` followed by the
base change along `f` on `SmallModel _.Etale`, through the unit of the equivalence of
`SmallModel Y.Etale` with `Y.Etale`. -/
def smallModelSquareIso :
    ((smallModelToposHom (Λ := Λ) f).comp (smallModelHom Λ X)).u ≅
      ((smallModelHom Λ Y).comp (ringedToposHom (ULift.{u + 1} Λ) f)).u :=
  NatIso.ofComponents
    (fun V => (fromEtale X).mapIso ((smallEtaleBaseChange f).mapIso
      ((equiv Y).unitIso.app (AsSmall.down.{u, u + 1, u + 1}.obj V))))
    (fun {V W} g => by
      have := (equiv Y).unitIso.hom.naturality (AsSmall.down.{u, u + 1, u + 1}.map g)
      change (fromEtale X).map ((smallEtaleBaseChange f).map
            (AsSmall.down.{u, u + 1, u + 1}.map g)) ≫
          (fromEtale X).map ((smallEtaleBaseChange f).map
            ((equiv Y).unitIso.hom.app (AsSmall.down.{u, u + 1, u + 1}.obj W))) =
        (fromEtale X).map ((smallEtaleBaseChange f).map
            ((equiv Y).unitIso.hom.app (AsSmall.down.{u, u + 1, u + 1}.obj V))) ≫
          (fromEtale X).map ((smallEtaleBaseChange f).map
            ((toEtale Y).map ((fromEtale Y).map (AsSmall.down.{u, u + 1, u + 1}.map g))))
      rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun t => (fromEtale X).map ((smallEtaleBaseChange f).map t)) this)

/-- **The comparisons of the two small models commute with the morphisms of ringed topoi of
`f`**: the isomorphism `smallModelSquareIso` of underlying functors carries the structure map of
one composite to that of the other, both being induced by the sheafification unit. -/
theorem fSharpCompatible_smallModelSquare :
    RingedToposSiteHom.FSharpCompatible
      ((smallModelHom Λ Y).comp (ringedToposHom (ULift.{u + 1} Λ) f))
      ((smallModelToposHom (Λ := Λ) f).comp (smallModelHom Λ X)) (smallModelSquareIso f) :=
  RingedToposSiteHom.fSharpCompatible_of_isConstantFSharp
    (RingedToposSiteHom.isConstantFSharp_comp (isConstantFSharp_ringedToposHom Λ f)
      (isConstantFSharp_smallModelHom Λ Y))
    (RingedToposSiteHom.isConstantFSharp_comp (isConstantFSharp_smallModelHom Λ X)
      (isConstantFSharp_etaleRingedSiteHom Λ f))
    (smallModelSquareIso f)

/-- The derived pullback along the morphism of ringed topoi of `f` on `AsSmall _.Etale`
exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_smallModelToposHom :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      (smallModelToposHom (Λ := Λ) f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ Y).O)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy.{u + 1}
    (smallModelToposHom (Λ := Λ) f) (isMorphismOfSites_smallModelToposHom f)

/-- The derived pullback along the composite through `Y` exists. -/
instance hasLeftDerivedFunctor_smallModelHom_comp :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      ((smallModelHom Λ Y).comp (ringedToposHom (ULift.{u + 1} Λ) f))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ Y).O)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy.{u + 1}
    _ (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_ringedToposHom _ f)
      (isMorphismOfSites_smallModelHom Λ Y))

/-- The derived pullback along the composite through `X` exists. -/
instance hasLeftDerivedFunctor_comp_smallModelHom :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      ((smallModelToposHom (Λ := Λ) f).comp (smallModelHom Λ X))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ Y).O)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy.{u + 1}
    _ (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_smallModelHom Λ X)
      (isMorphismOfSites_smallModelToposHom f))

/-- **The derived pullbacks along the comparisons commute with the inverse images along `f`**:
`Lι_Y ⋙ f⁻¹ ≅ L(f)^* ⋙ Lι_X`, by Stacks 0D6D for the two composites and the isomorphism of
derived pullbacks along the isomorphic composites. -/
def smallModelDerivedPullbackSquareIso :
    smallModelDerivedPullback Λ Y ⋙ pullback (ULift.{u + 1} Λ) f ≅
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback
          (smallModelToposHom (Λ := Λ) f) ⋙ smallModelDerivedPullback Λ X :=
  Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
      (ringedToposHom (ULift.{u + 1} Λ) f) (smallModelHom Λ Y)
      (isMorphismOfSites_ringedToposHom _ f) (isMorphismOfSites_smallModelHom Λ Y) ≪≫
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackIsoOfIso
      (fSharpCompatible_smallModelSquare f) ≪≫
    (Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
      (smallModelHom Λ X) (smallModelToposHom (Λ := Λ) f)
      (isMorphismOfSites_smallModelHom Λ X) (isMorphismOfSites_smallModelToposHom f)).symm

/-- The composition isomorphism of derived pullbacks is compatible with Stacks 07A4. -/
private theorem tensorCompat_derivedPullbackCompIso {A B C : RingedTopos.{u + 1, u + 1, u + 1}}
    (f : RingedToposSiteHom A B) (g : RingedToposSiteHom B C)
    [(Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf B.O)) (ComplexShape.up ℤ))]
    [(Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      g).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf C.O)) (ComplexShape.up ℤ))]
    [(Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
      (g.comp f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf C.O)) (ComplexShape.up ℤ))]
    (hf : f.u.IsMorphismOfSites B.J A.J) (hg : g.u.IsMorphismOfSites C.J B.J) :
    Stacks.Cohomology.AbstractKunnethMap.TensorCompat
      (Stacks.Cohomology.AbstractKunnethMap.compTensor
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso g hg).hom
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hf).hom)
      (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (g.comp f)
        (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ hf hg)).hom
      (Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
        f g hf hg).hom :=
  fun P Q => (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp
    f g hf hg P Q).trans (Category.assoc _ _ _).symm

open Stacks.Cohomology.AbstractKunnethMap (TensorCompat compTensor) in
/-- **`smallModelDerivedPullbackSquareIso` is compatible with Stacks 07A4**: it carries the
comparison of the composite `Lι_Y ⋙ f⁻¹` to that of `L(f)^* ⋙ Lι_X`. This is the composition law
of Stacks 07A4 along Stacks 0D6D on both sides, and the compatibility of Stacks 07A4 with the
isomorphism of derived pullbacks along isomorphic morphisms of ringed topoi. -/
theorem tensorCompat_smallModelDerivedPullbackSquareIso :
    TensorCompat
      (compTensor
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (smallModelHom Λ Y)
          (isMorphismOfSites_smallModelHom Λ Y)).hom
        (pullbackTensorIso (ULift.{u + 1} Λ) f).hom)
      (compTensor
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (smallModelToposHom (Λ := Λ) f)
          (isMorphismOfSites_smallModelToposHom f)).hom
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (smallModelHom Λ X)
          (isMorphismOfSites_smallModelHom Λ X)).hom)
      (smallModelDerivedPullbackSquareIso f).hom := by
  have h₂ : TensorCompat
      (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso
        ((smallModelHom Λ Y).comp (ringedToposHom (ULift.{u + 1} Λ) f))
        (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_ringedToposHom _ f)
          (isMorphismOfSites_smallModelHom Λ Y))).hom
      (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso
        ((smallModelToposHom (Λ := Λ) f).comp (smallModelHom Λ X))
        (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_smallModelHom Λ X)
          (isMorphismOfSites_smallModelToposHom f))).hom
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackIsoOfIso
        (fSharpCompatible_smallModelSquare f)).hom :=
    fun P Q =>
      Sheaves.DerivedPullback.derivedPullbackIsoOfIso_hom_app_comp_derivedPullbackTensorIso_hom_app
        (fSharpCompatible_smallModelSquare f) _ _ P Q
  exact (tensorCompat_derivedPullbackCompIso _ _ (isMorphismOfSites_ringedToposHom _ f)
      (isMorphismOfSites_smallModelHom Λ Y)).comp
    (h₂.comp (tensorCompat_derivedPullbackCompIso _ _ (isMorphismOfSites_smallModelHom Λ X)
      (isMorphismOfSites_smallModelToposHom f)).symm)

/-- **The projection maps of `f` on the two presentations are invertible at corresponding
objects.** For `E` on `AsSmall X.Etale` and `K` on `AsSmall Y.Etale`, the projection map
`K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)` of the presentation by `AsSmall _.Etale` is invertible exactly
when the projection map `Lι_Y K ⊗^L Rf_*(Lι_X E) ⟶ Rf_*(f⁻¹Lι_Y K ⊗^L Lι_X E)` on `D(-_étale, Λ)`
(`Stacks.EtaleCohomology.EtaleCoefficients.projectionMap`) is. -/
theorem isIso_projectionMap_smallModel_iff
    (E : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O)))
    (K : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ Y).O))) :
    IsIso (Stacks.Cohomology.AbstractKunnethMap.projectionMap
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (smallModelTopos Λ Y).O))
        (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (smallModelTopos Λ X).O))
        (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction
          (smallModelToposHom (Λ := Λ) f) (isMorphismOfSites_smallModelToposHom f))
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (smallModelToposHom (Λ := Λ) f)
          (isMorphismOfSites_smallModelToposHom f)).hom K E) ↔
      IsIso (projectionMap (ULift.{u + 1} Λ) f ((smallModelDerivedPullback Λ Y).obj K)
        ((smallModelDerivedPullback Λ X).obj E)) :=
  Stacks.Cohomology.AbstractKunnethMap.isIso_projectionMap_iff_of_tensorCompat _ _
    (smallModelDerivedPullbackSquareIso f)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (smallModelHom Λ Y)
      (isMorphismOfSites_smallModelHom Λ Y))
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (smallModelHom Λ X)
      (isMorphismOfSites_smallModelHom Λ X)) _ _
    (tensorCompat_smallModelDerivedPullbackSquareIso f) K E

/-- **The maps of Stacks 0B56 of `f` on the two presentations are invertible at corresponding
objects.** For `E` on `AsSmall X.Etale` and `K` on `AsSmall Y.Etale`, the map
`Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` of the presentation by `AsSmall _.Etale` is invertible exactly
when the one on `D(-_étale, ULift Λ)` is at `(Lι_X E, Lι_Y K)`. -/
theorem isIso_projectionFormulaMap_smallModel_iff
    (E : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ X).O)))
    (K : DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelTopos Λ Y).O))) :
    IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        (smallModelToposHom (Λ := Λ) f) (isMorphismOfSites_smallModelToposHom f) E K) ↔
      IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap
        (ringedToposHom (ULift.{u + 1} Λ) f) (isMorphismOfSites_ringedToposHom _ f)
        ((smallModelDerivedPullback Λ X).obj E) ((smallModelDerivedPullback Λ Y).obj K)) :=
  Stacks.Cohomology.AbstractKunnethMap.isIso_adjunctionTensorMap_iff_of_tensorCompat _ _
    (smallModelDerivedPullbackSquareIso f)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (smallModelHom Λ Y)
      (isMorphismOfSites_smallModelHom Λ Y))
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (smallModelHom Λ X)
      (isMorphismOfSites_smallModelHom Λ X)) _ _
    (tensorCompat_smallModelDerivedPullbackSquareIso f) E K

end Derived

end Stacks.EtaleCohomology.EtaleCoefficients

end
