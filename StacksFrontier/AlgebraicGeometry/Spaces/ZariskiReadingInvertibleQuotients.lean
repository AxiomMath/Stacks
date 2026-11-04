module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardTransport
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InvertibleQuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.RestrictionIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleTrivial

/-!
# Invertible quotients on a represented algebraic space and on its scheme

Let `T` be an object of the big fppf site over `S`, with scheme `T₀`, and let `N` be a
quasi-coherent `𝒪`-module on the small étale site of the represented algebraic space `T`.  Its
Zariski reading `R_T N` (the direct image along the inclusion of the Zariski opens of `T₀`) is a
quasi-coherent module on `T₀`, and `R_T` is an equivalence between quasi-coherent modules on the
two sites (Stacks 03DX).  This file shows that `R_T` matches the invertible quotients of `N` with
those of `R_T N`, on isomorphism classes, compatibly with base change along `τ : T' ⟶ T`.

## Main definitions

* `AlgebraicGeometry.Space.zariskiReadingInvertibleQuotient`: the Zariski reading
  `(R_T L, R_T q)` of an invertible quotient `q : N ⟶ L`.
* `AlgebraicGeometry.Space.invertibleQuotientClassZariskiEquiv`: the bijection of isomorphism
  classes of invertible quotients of `N` and of `R_T N`.
* `AlgebraicGeometry.Space.zariskiReadingUnitHomIso`: `𝒪_T ≅ R_T 𝒪`, induced by the structure
  map of the Zariski site of `T` into its small étale site.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom`: the base-change map
  `τ^*(R_T M) ⟶ R_{T'}(φ^* M)`, the mate of the identification `R_T ∘ φ_* ≅ τ_* ∘ R_{T'}`, and
  `AlgebraicGeometry.Space.zariskiReadingPullbackIso`, its inverse at a quasi-coherent `M`.

## Main results

* `AlgebraicGeometry.Space.isInvertible_zariskiReading` and
  `AlgebraicGeometry.Space.isInvertibleModule_zariskiAssociated`: invertibility passes in both
  directions, through tensor inverses.
* `AlgebraicGeometry.Space.isIso_zariskiReadingPullbackHom_app`: the base-change map is
  invertible at a quasi-coherent module.
* `AlgebraicGeometry.Space.invertibleQuotientClassZariskiEquiv_baseChange`: the bijection
  commutes with base change.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- A morphism `G L₁ ≅ G L₂` relating the images of two maps out of `N` gives, through the counit,
a morphism `L₁ ≅ L₂` relating the maps themselves. -/
theorem comp_inv_counit_comp_map_comp_counit {N L₁ L₂ : D} (hN : IsIso (adj.counit.app N))
    (h₁ : IsIso (adj.counit.app L₁)) (h₂ : IsIso (adj.counit.app L₂)) (q₁ : N ⟶ L₁)
    (q₂ : N ⟶ L₂) (α : G.obj L₁ ≅ G.obj L₂) (hα : G.map q₁ ≫ α.hom = G.map q₂) :
    q₁ ≫ ((asIso (adj.counit.app L₁)).symm ≪≫ F.mapIso α ≪≫ asIso (adj.counit.app L₂)).hom =
      q₂ := by
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom, asIso_hom]
  rw [← cancel_epi (adj.counit.app N), ← Category.assoc (adj.counit.app N),
    ← adj.counit_naturality q₁, Category.assoc, IsIso.hom_inv_id_assoc, ← F.map_comp_assoc, hα,
    adj.counit_naturality q₂]

/-- A map `G N ⟶ L` into an object at which the unit is invertible is the image of its transpose
precomposed with the inverse counit. -/
theorem comp_unit_eq_map_inv_counit_comp {N : D} {L : C} (hN : IsIso (adj.counit.app N))
    (q : G.obj N ⟶ L) :
    q ≫ adj.unit.app L = G.map (inv (adj.counit.app N) ≫ F.map q) := by
  rw [G.map_comp, ← adj.unit_naturality]
  congr 1
  rw [← cancel_mono (G.map (adj.counit.app N)), ← G.map_comp, IsIso.inv_hom_id, G.map_id,
    adj.right_triangle_components]
  rfl

section Transpose

variable {ℰ ℰ' 𝒵 𝒵' : Type*} [Category ℰ] [Category ℰ'] [Category 𝒵] [Category 𝒵']
  {φu : ℰ ⥤ ℰ'} {φl : ℰ' ⥤ ℰ} {τu : 𝒵 ⥤ 𝒵'} {τl : 𝒵' ⥤ 𝒵} {Z : ℰ ⥤ 𝒵} {Z' : ℰ' ⥤ 𝒵'}
  (adjφ : φu ⊣ φl) (adjτ : τu ⊣ τl) (σ : φl ⋙ Z ⟶ Z' ⋙ τl)

/-- The transposed comparison is natural. -/
theorem transposeComparison_naturality {N N' : ℰ} (f : N ⟶ N') :
    τu.map (Z.map f) ≫ transposeComparison adjφ adjτ σ N' =
      transposeComparison adjφ adjτ σ N ≫ Z'.map (φu.map f) := by
  simp only [transposeComparison]
  rw [← adjτ.homEquiv_naturality_left_symm, ← adjτ.homEquiv_naturality_right_symm]
  congr 1
  have hη := adjφ.unit.naturality f
  have hσ := σ.naturality (φu.map f)
  simp only [Functor.comp_map, Functor.id_map] at hη hσ
  rw [← Z.map_comp_assoc, hη, Z.map_comp, Category.assoc, hσ, Category.assoc]

/-- The transposed comparison, as a natural transformation. -/
@[simps]
def transposeComparisonNatTrans : Z ⋙ τu ⟶ φu ⋙ Z' where
  app N := transposeComparison adjφ adjτ σ N
  naturality _ _ f := transposeComparison_naturality adjφ adjτ σ f

variable {a : 𝒵 ⥤ ℰ} {a' : 𝒵' ⥤ ℰ'} (adja : a ⊣ Z) (adja' : a' ⊣ Z')

/-- `Adjunction.isIso_transposeComparison`, with its invertibility inputs as explicit
hypotheses. -/
theorem isIso_transposeComparison_of_isIso (hσ : IsIso σ) (N : ℰ)
    (h₁ : IsIso (adja.counit.app N)) (h₂ : IsIso (adja'.unit.app (τu.obj (Z.obj N)))) :
    IsIso (transposeComparison adjφ adjτ σ N) :=
  isIso_transposeComparison adjφ adjτ adja adja' σ N

end Transpose

section NatTransInv

variable {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (β : F ⟶ G)

/-- Naturality of the inverse of a natural transformation at two objects where it is invertible,
after an arbitrary map into the source. -/
theorem _root_.CategoryTheory.NatTrans.comp_map_comp_inv_app {N L : C} (f : N ⟶ L)
    (hN : IsIso (β.app N)) (hL : IsIso (β.app L)) {N' : D} (e : N' ⟶ G.obj N) :
    (e ≫ G.map f) ≫ inv (β.app L) = e ≫ inv (β.app N) ≫ F.map f := by
  rw [Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, β.naturality, IsIso.inv_hom_id_assoc]

end NatTransInv

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance 5000] SheafOfModules.instPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Reading

variable (T : BigFppfOver B S hS)

/-- The Zariski reading of an `𝒪`-module on the represented algebraic space. -/
abbrev zariskiReadingFunctor :=
  SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)

open Opposite in
/-- The structure map of the Zariski site of `T` into its small étale site is bijective on the
sections over every Zariski open. -/
theorem bijective_selfOpensStructureMap_hom_app (O : (chartScheme (idEtaleChart B S hS T)).Opens) :
    Function.Bijective ((selfOpensStructureMap B S hS T).hom.app (op O)) := by
  have h1 : Function.Bijective ((forget₂ CommRingCat RingCat).map (Scheme.Opens.topIso O).inv) :=
    ConcreteCategory.bijective_of_isIso _
  have h2 : Function.Bijective ((representedSchemeStructureSheaf B S hS T).obj.map
      ((representedSmallEtaleEquivalence B S hS T).counit.app
        (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property O)).op) :=
    ConcreteCategory.bijective_of_isIso _
  exact h2.comp h1

/-- **The Zariski reading of the structure sheaf**: the map `𝒪_T ⟶ R_T 𝒪` given on the
sections over a Zariski open by the structure map of the Zariski site of `T` into its small
étale site. -/
def zariskiReadingUnitHom :
    SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf ⟶
      (zariskiReadingFunctor T).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T))) :=
  SheafOfModules.unitToPushforwardObjUnit (selfOpensStructureMap B S hS T)

/-- The map `𝒪_T ⟶ R_T 𝒪` is an isomorphism, being bijective on sections. -/
theorem isIso_zariskiReadingUnitHom : IsIso (zariskiReadingUnitHom T) :=
  SheafOfModules.isIso_of_bijective_val_app' _ fun O =>
    bijective_selfOpensStructureMap_hom_app T O.unop

/-- `zariskiReadingUnitHom` as an isomorphism `𝒪_T ≅ R_T 𝒪`. -/
def zariskiReadingUnitHomIso :
    SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf ≅
      (zariskiReadingFunctor T).obj
        (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T))) :=
  @asIso _ _ _ _ (zariskiReadingUnitHom T) (isIso_zariskiReadingUnitHom T)

/-- The Zariski reading of the structure sheaf is the structure sheaf: the inverse of
`AlgebraicGeometry.Space.zariskiReadingUnitHomIso`. -/
def zariskiReadingUnitIso :
    (zariskiReadingFunctor T).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O))) ≅
      SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf :=
  (zariskiReadingUnitHomIso T).symm

/-- The identity-chart restriction is the Zariski reading. -/
def restrictToChartSchemeIdEtaleChartReadingIso
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    restrictToChartScheme B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) N
        (idEtaleChart B S hS T) ≅ (zariskiReadingFunctor T).obj N :=
  restrictToChartSchemeIdEtaleChartIso B S hS T N ≪≫ selfOpensPushforwardIso B S hS T N

/-- The Zariski reading of a tensor product of quasi-coherent modules is the tensor product of
the readings. -/
def zariskiReadingTensorIso
    (P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    (zariskiReadingFunctor T).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj P).obj Q) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj
          ((zariskiReadingFunctor T).obj P)).obj ((zariskiReadingFunctor T).obj Q) := by
  refine (zariskiReadingFunctor T).mapIso
      (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) P Q).symm ≪≫
    (restrictToChartSchemeIdEtaleChartReadingIso T (P ⊗ Q)).symm ≪≫
    restrictToChartSchemeIdEtaleChartTensorIso B S hS T P Q hP hQ ≪≫ ?_
  exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).mapIso
      (restrictToChartSchemeIdEtaleChartReadingIso T P)).app _ ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj
          ((zariskiReadingFunctor T).obj P)).mapIso
      (restrictToChartSchemeIdEtaleChartReadingIso T Q)

/-- **The Zariski reading of an invertible module is invertible.** -/
theorem isInvertible_zariskiReading
    (L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hL : IsInvertibleModule (yonedaSpace B S hS T) L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj T).presheaf
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 ((zariskiReadingFunctor T).obj L) := by
  refine (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp ?_
  refine Stacks.SheafOfModules.Picard.isInvertible_map_obj_of_tensorIsoOn
    (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).obj _
    ((BigFppfOver.toScheme B S hS).obj T).presheaf
    ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 (zariskiReadingFunctor T)
    (P := fun M => M.IsQuasicoherentOnSite)
    (fun M hM => isQuasicoherentOnSite_of_isInvertible B S hS (yonedaSpace B S hS T) M
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hM))
    (zariskiReadingUnitIso T) (fun P Q hP hQ => zariskiReadingTensorIso T P Q hP hQ) L hL

/-- The left adjoint of the Zariski reading: the associated module of Stacks 03DU, read on the
small étale site of the represented algebraic space. -/
abbrev zariskiAssociatedFunctor :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS T).functor

/-- The Zariski reading adjunction, with its left adjoint named. -/
abbrev zariskiReadingAdj : zariskiAssociatedFunctor T ⊣ zariskiReadingFunctor T :=
  zariskiReadingAdjunction T

/-- The associated module of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherentOnSite_zariskiAssociated (M : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hM : M.IsQuasicoherent) : ((zariskiAssociatedFunctor T).obj M).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T _).2
    (_root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent
      _ _ _ M hM)

/-- The counit of the Zariski reading adjunction at a quasi-coherent module, as an isomorphism. -/
def zariskiReadingCounitIso
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    (zariskiAssociatedFunctor T).obj ((zariskiReadingFunctor T).obj N) ≅ N :=
  haveI := isIso_zariskiReadingAdjunction_counit_app T N hN
  asIso ((zariskiReadingAdj T).counit.app N)

/-- The unit of the Zariski reading adjunction at a quasi-coherent module, as an isomorphism. -/
def zariskiReadingUnitIsoApp (M : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hM : M.IsQuasicoherent) :
    M ≅ (zariskiReadingFunctor T).obj ((zariskiAssociatedFunctor T).obj M) :=
  haveI := isIso_zariskiReadingAdjunction_unit_app T M hM
  asIso ((zariskiReadingAdj T).unit.app M)

/-- The Zariski reading reflects isomorphisms of quasi-coherent modules. -/
def isoOfZariskiReadingIso
    {N N' : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (hN' : N'.IsQuasicoherentOnSite)
    (e : (zariskiReadingFunctor T).obj N ≅ (zariskiReadingFunctor T).obj N') : N ≅ N' :=
  (zariskiReadingCounitIso T N hN).symm ≪≫ (zariskiAssociatedFunctor T).mapIso e ≪≫
    zariskiReadingCounitIso T N' hN'

/-- **The associated module of an invertible module is invertible**: a tensor inverse on the
scheme gives one on the represented algebraic space, since the Zariski reading is monoidal on
quasi-coherent modules and reflects their isomorphisms. -/
theorem isInvertibleModule_zariskiAssociated (L : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj T).presheaf
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 L) :
    IsInvertibleModule (yonedaSpace B S hS T) ((zariskiAssociatedFunctor T).obj L) := by
  obtain ⟨M, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit L).1
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL)
  have hMs : Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj T).presheaf
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2 M :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit M).2
      ⟨L, ⟨Stacks.SheafOfModules.tensorSheafBraiding _ _ M L ≪≫ e⟩⟩
  have hLq : L.IsQuasicoherent := @Stacks.Divisors.isQuasicoherent_of_isInvertible _ L hL
  have hMq : M.IsQuasicoherent := @Stacks.Divisors.isQuasicoherent_of_isInvertible _ M
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hMs)
  have hL' := isQuasicoherentOnSite_zariskiAssociated T L hLq
  have hM' := isQuasicoherentOnSite_zariskiAssociated T M hMq
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).2
    ⟨(zariskiAssociatedFunctor T).obj M,
      ⟨isoOfZariskiReadingIso T ?_ (SheafOfModules.isQuasicoherentOnSite_unit _) ?_⟩⟩
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) _ _)
      (@isQuasicoherentOnSite_tensorObj B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
        _ _ hL' hM')
  · refine zariskiReadingTensorIso T _ _ hL' hM' ≪≫ ?_ ≪≫ (zariskiReadingUnitIso T).symm
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).mapIso
      (zariskiReadingUnitIsoApp T L hLq).symm).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj T).zariskiRingedSite.toRingedTopos.O).obj L).mapIso
      (zariskiReadingUnitIsoApp T M hMq).symm ≪≫ e

variable {T} in
/-- **The Zariski reading of an invertible quotient**: a surjection `N ⟶ L` onto an invertible
module on the represented algebraic space read on the Zariski site of the scheme. -/
def zariskiReadingInvertibleQuotient
    {N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (Q : InvertibleQuotient (yonedaSpace B S hS T) N) :
    Stacks.Divisors.InvertibleQuotient ((BigFppfOver.toScheme B S hS).obj T)
      ((zariskiReadingFunctor T).obj N) where
  L := (zariskiReadingFunctor T).obj Q.L
  invertible := isInvertible_zariskiReading T Q.L Q.invertible
  q := (zariskiReadingFunctor T).map Q.q
  epi := epi_zariskiReading_map T Q.q Q.epi hN
    (isQuasicoherentOnSite_of_isInvertibleModule (yonedaSpace B S hS T) Q.L Q.invertible)

variable {T}

/-- The invertible module of an invertible quotient is quasi-coherent. -/
private theorem isQuasicoherentOnSite_invertibleQuotient_L {N}
    (Q : InvertibleQuotient (yonedaSpace B S hS T) N) : Q.L.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isInvertibleModule _ Q.L Q.invertible

/-- Two invertible quotients of a quasi-coherent module are equivalent exactly when their Zariski
readings are. -/
theorem zariskiReadingInvertibleQuotient_isEquivalent_iff
    {N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (Q R : InvertibleQuotient (yonedaSpace B S hS T) N) :
    (zariskiReadingInvertibleQuotient hN Q).IsEquivalent (zariskiReadingInvertibleQuotient hN R) ↔
      Q.IsEquivalent R := by
  have hQ := isQuasicoherentOnSite_invertibleQuotient_L Q
  have hR := isQuasicoherentOnSite_invertibleQuotient_L R
  constructor
  · rintro ⟨α, hα⟩
    exact ⟨isoOfZariskiReadingIso T hQ hR α,
      Adjunction.comp_inv_counit_comp_map_comp_counit (zariskiReadingAdj T)
        (isIso_zariskiReadingAdjunction_counit_app T N hN)
        (isIso_zariskiReadingAdjunction_counit_app T Q.L hQ)
        (isIso_zariskiReadingAdjunction_counit_app T R.L hR) Q.q R.q α hα⟩
  · rintro ⟨β, hβ⟩
    exact ⟨(zariskiReadingFunctor T).mapIso β,
      ((zariskiReadingFunctor T).map_comp Q.q β.hom).symm.trans
        (congrArg (zariskiReadingFunctor T).map hβ)⟩

/-- The invertible quotient on the represented algebraic space associated with an invertible
quotient of the Zariski reading. -/
def associatedInvertibleQuotient
    {N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite)
    (Q : Stacks.Divisors.InvertibleQuotient ((BigFppfOver.toScheme B S hS).obj T)
      ((zariskiReadingFunctor T).obj N)) :
    InvertibleQuotient (yonedaSpace B S hS T) N where
  L := (zariskiAssociatedFunctor T).obj Q.L
  invertible := isInvertibleModule_zariskiAssociated T Q.L Q.invertible
  q := (zariskiReadingCounitIso T N hN).inv ≫ (zariskiAssociatedFunctor T).map Q.q
  epi := by
    have : (zariskiAssociatedFunctor T).IsLeftAdjoint := (zariskiReadingAdj T).isLeftAdjoint
    have h : Epi ((zariskiAssociatedFunctor T).map Q.q) :=
      @Functor.map_epi _ _ _ _ _ (Functor.preservesEpimorphisms_of_isLeftAdjoint _) _ _ Q.q Q.epi
    exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _
      (Iso.isIso_inv (zariskiReadingCounitIso T N hN))) _ h

/-- The Zariski reading of the associated invertible quotient is the given one. -/
theorem isEquivalent_zariskiReadingInvertibleQuotient_associated
    {N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite)
    (Q : Stacks.Divisors.InvertibleQuotient ((BigFppfOver.toScheme B S hS).obj T)
      ((zariskiReadingFunctor T).obj N)) :
    Q.IsEquivalent (zariskiReadingInvertibleQuotient hN (associatedInvertibleQuotient hN Q)) :=
  ⟨zariskiReadingUnitIsoApp T Q.L
      (@Stacks.Divisors.isQuasicoherent_of_isInvertible _ Q.L Q.invertible),
    Adjunction.comp_unit_eq_map_inv_counit_comp (zariskiReadingAdj T)
      (isIso_zariskiReadingAdjunction_counit_app T N hN) Q.q⟩

variable (T) in
/-- **Invertible quotients of a quasi-coherent module on a represented algebraic space are the
invertible quotients of its Zariski reading**, on isomorphism classes. -/
def invertibleQuotientClassZariskiEquiv
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    InvertibleQuotientClass (yonedaSpace B S hS T) N ≃
      Stacks.Divisors.InvertibleQuotientClass ((BigFppfOver.toScheme B S hS).obj T)
        ((zariskiReadingFunctor T).obj N) :=
  Equiv.ofBijective
    (Quotient.map (zariskiReadingInvertibleQuotient hN)
      fun Q R h => (zariskiReadingInvertibleQuotient_isEquivalent_iff hN Q R).2 h)
    ⟨fun a b => Quotient.inductionOn₂ a b fun Q R h =>
        Quotient.sound ((zariskiReadingInvertibleQuotient_isEquivalent_iff hN Q R).1
          (Quotient.exact h)),
      fun c => Quotient.inductionOn c fun Q =>
        ⟨Quotient.mk _ (associatedInvertibleQuotient hN Q),
          Quotient.sound ((Stacks.Divisors.invertibleQuotientSetoid _ _).symm
            (isEquivalent_zariskiReadingInvertibleQuotient_associated hN Q))⟩⟩

/-- The equivalence `invertibleQuotientClassZariskiEquiv` sends the class of an invertible
quotient `Q` to the class of its Zariski reading `zariskiReadingInvertibleQuotient hN Q`. -/
@[simp]
theorem invertibleQuotientClassZariskiEquiv_mk
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) (Q : InvertibleQuotient (yonedaSpace B S hS T) N) :
    invertibleQuotientClassZariskiEquiv T N hN (Quotient.mk _ Q) =
      Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid _ _)
        (zariskiReadingInvertibleQuotient hN Q) :=
  rfl

end Reading

section BaseChange

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

variable {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)

/-- **The base-change map of the Zariski reading** along a morphism `τ : T' ⟶ T` of test
objects, `τ^*(R_T M) ⟶ R_{T'}(φ^* M)` for `φ` the morphism of represented algebraic spaces: the
transpose of the Zariski reading of the unit of `φ^* ⊣ φ_*` followed by the identification
`R_T ∘ φ_* ≅ τ_* ∘ R_{T'}` of sections over Zariski opens. -/
def zariskiReadingPullbackHom :
    zariskiReadingFunctor T ⋙ Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ) ⟶
      modulePullback B S hS (representedSpaceMap B S hS τ) ⋙ zariskiReadingFunctor T' :=
  Adjunction.transposeComparisonNatTrans (etaleModuleAdjunction (representedSpaceMap B S hS τ))
    (Stacks.RingedSpace.pullbackAdjunction (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)))
    (zariskiDirectImageNatTrans τ)

/-- The base-change map is the transpose of the Zariski reading of the unit followed by the
identification of sections of a direct image. -/
theorem zariskiReadingPullbackHom_app
    (M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (zariskiReadingPullbackHom τ).app M =
      Adjunction.transposeComparison (etaleModuleAdjunction (representedSpaceMap B S hS τ))
        (Stacks.RingedSpace.pullbackAdjunction
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ)))
        (zariskiDirectImageNatTrans τ) M :=
  rfl

/-- **The base-change map of the Zariski reading is invertible at a quasi-coherent module.** -/
theorem isIso_zariskiReadingPullbackHom_app
    (M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hM : M.IsQuasicoherentOnSite) : IsIso ((zariskiReadingPullbackHom τ).app M) :=
  Adjunction.isIso_transposeComparison_of_isIso _ _ _ (zariskiReadingAdjunction T)
    (zariskiReadingAdjunction T') (isIso_zariskiDirectImageNatTrans τ) M
    (isIso_zariskiReadingAdjunction_counit_app T M hM)
    (isIso_zariskiReadingAdjunction_unit_app T'
      ((Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj
        ((SheafOfModules.pushforward (selfOpensStructureMap B S hS T)).obj M))
      (Stacks.Modules.isQuasicoherent_pullback ((BigFppfOver.toScheme B S hS).map τ) _
        (isQuasicoherent_zariskiReading_piece T M hM)))

/-- The base-change isomorphism of the Zariski reading at a quasi-coherent module. -/
def zariskiReadingPullbackIso
    (M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hM : M.IsQuasicoherentOnSite) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ)).obj
        ((zariskiReadingFunctor T).obj M) ≅
      (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj M) :=
  @asIso _ _ _ _ ((zariskiReadingPullbackHom τ).app M) (isIso_zariskiReadingPullbackHom_app τ M hM)

/-- **The dictionary of invertible quotients commutes with base change**: pulling an invertible
quotient back along `φ` and reading it on `T'` is reading it on `T` and pulling back along `τ`,
through the base-change isomorphism of the Zariski reading. -/
theorem invertibleQuotientClassZariskiEquiv_baseChange
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    (N' : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
    (hN' : N'.IsQuasicoherentOnSite)
    (eN : N' ≅ (modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)
    (c : InvertibleQuotientClass (yonedaSpace B S hS T) N) :
    invertibleQuotientClassZariskiEquiv T' N' hN'
        (invertibleQuotientBaseChangeClass
          (representedSpaceMap B S hS τ : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T) eN c) =
      Stacks.ProjectiveBundleQuotients.baseChangeClass ((BigFppfOver.toScheme B S hS).map τ)
        ((zariskiReadingFunctor T').mapIso eN ≪≫ (zariskiReadingPullbackIso τ N hN).symm)
        (invertibleQuotientClassZariskiEquiv T N hN c) := by
  induction c using Quotient.ind with
  | _ Q =>
    have hQL := isQuasicoherentOnSite_invertibleQuotient_L Q
    exact Quotient.sound ⟨(zariskiReadingPullbackIso τ Q.L hQL).symm,
      (congrArg (· ≫ @inv _ _ _ _ ((zariskiReadingPullbackHom τ).app Q.L)
        (isIso_zariskiReadingPullbackHom_app τ Q.L hQL))
        ((zariskiReadingFunctor T').map_comp eN.hom
          ((modulePullback B S hS (representedSpaceMap B S hS τ)).map Q.q))).trans
      (NatTrans.comp_map_comp_inv_app (zariskiReadingPullbackHom τ) Q.q
        (isIso_zariskiReadingPullbackHom_app τ N hN) (isIso_zariskiReadingPullbackHom_app τ Q.L hQL)
        ((zariskiReadingFunctor T').map eN.hom))⟩

end BaseChange

end AlgebraicGeometry.Space

end
