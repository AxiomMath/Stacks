module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTerms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface

/-!
# Objects of `D_QCoh` of the small étale site as `ε^*` of K-flat complexes

Let `S` be a scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the comparison morphism of Stacks 08H7.
By Stacks 071Q every object `E` of `D_QCoh(S_étale, 𝒪)` is `ε^*A` for an object `A` of
`D_QCoh(𝒪_S)`, and by Stacks 06YS `A` is represented by a K-flat complex of `𝒪_S`-modules with
flat terms.  Since `ε^*` is exact, `ε^*A` is computed degreewise on that complex.  This file
records the resulting representative of `E`.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_kFlat_associatedModule_iso`: every object of
  `D_QCoh(S_étale, 𝒪)` is isomorphic to the class of `ε^*P` for a K-flat complex `P` of
  `𝒪_S`-modules with flat terms and quasi-coherent cohomology sheaves.
* `AlgebraicGeometry.SmallEtale.isKFlat_etalePullbackComplex`: Stacks 0G7E at `ε` — the pullback
  `ε^*P` of a K-flat complex with flat terms is K-flat.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_homology_etalePullbackComplex`: the
  cohomology sheaves of `ε^*C` are quasi-coherent when those of `C` are (Stacks 08H8, 03DV (2)).
* `AlgebraicGeometry.SmallEtale.exists_etalePullbackComplex_iso`: the representative above, read
  at the spelling `AlgebraicGeometry.RingedSite.Modules` of the small étale ringed site, with
  `ε^*` the pullback of modules along `ε` as a morphism of ringed topoi.

## Implementation notes

`ε^*` appears in two spellings: the associated-module functor
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, at which Stacks 071Q is stated, and the
pullback of modules along `ε` as a morphism of ringed topoi, at which Stacks 0G7E and the
comparison of total tensor complexes are stated.  `AlgebraicGeometry.SmallEtale.etalePullbackIso`
identifies them, through
`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom` and
`AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso`.

The derived categories are read at `CategoryTheory.HasDerivedCategory.standard`, at which both
the Zariski and the small étale module categories have their derived category in the universe
`u + 1`, the common universe Stacks 071Q asks for.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe w u

namespace AlgebraicGeometry.SmallEtale

section Representative

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{w} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **Every object of `D_QCoh(S_étale, 𝒪)` is `ε^*` of a K-flat complex.**  For an object `E` of
`D(S_étale, 𝒪)` with quasi-coherent cohomology sheaves there is a K-flat complex `P` of
`𝒪_S`-modules on the Zariski site, with flat terms and quasi-coherent cohomology sheaves, whose
degreewise associated module `ε^*P` represents `E`.

By Stacks 071Q, `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`, `E` is
`ε^*A` for an object `A` of `D_QCoh(𝒪_S)`; Stacks 06YS,
`Stacks.SheafOfModules.exists_kFlatResolution`, resolves a representative of `A` by a K-flat
complex with flat terms, and `ε^*` is computed degreewise, being exact. -/
theorem exists_kFlat_associatedModule_iso
    (E : (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).FullSubcategory) :
    ∃ P : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ,
      Stacks.SheafOfModules.IsKFlat S.zariskiRingedSite.O P ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := S.zariskiRingedSite.O) (P.X i)) ∧
      (∀ n : ℤ, SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
        ((HomologicalComplex.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf)
          (ComplexShape.up ℤ) n).obj P)) ∧
      Nonempty (DerivedCategory.Q.obj
        (((associatedModuleOfSheaf B S hS).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
          E.obj) := by
  have := derivedAssociatedModule_isEquivalence.{w} B S hS
  let A := (derivedAssociatedModule.{w} B S hS).objPreimage E
  let eA : (associatedModuleOfSheaf B S hS).mapDerivedCategory.obj A.obj ≅ E.obj :=
    (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).ι.mapIso
      ((derivedAssociatedModule.{w} B S hS).objObjPreimageIso E)
  let G : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ :=
    DerivedCategory.Q.objPreimage A.obj
  obtain ⟨P, p, hK, hflat, hqis, -⟩ := Stacks.SheafOfModules.exists_kFlatResolution
    S.zariskiRingedSite G
  let P' : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ := P
  let p' : P' ⟶ G := p
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := SheafOfModules.{u} S.ringCatSheaf) p').2 hqis
  let e₁ : DerivedCategory.Q.obj P' ≅ A.obj :=
    @asIso _ _ _ _ (DerivedCategory.Q.map p') hiso ≪≫ DerivedCategory.Q.objObjPreimageIso A.obj
  refine ⟨P', hK, hflat, fun n => ?_, ⟨?_⟩⟩
  · exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e₁.symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ n).app P') (A.property n)
  · exact ((associatedModuleOfSheaf B S hS).mapDerivedCategoryFactors.app P').symm ≪≫
      (associatedModuleOfSheaf B S hS).mapDerivedCategory.mapIso e₁ ≪≫ eA

end Representative

section Etale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `ε^*` on complexes, at the spelling of the small étale ringed site -/

attribute [local instance] HasDerivedCategory.standard


/-- The modules of the small étale ringed site of `S`, at the spelling the derived tensor product
is formed at. -/
abbrev EtaleModules := RingedSite.Modules.{u + 1, u, u} (smallEtaleRingedSite B S hS)

/-- `ε` as a morphism of ringed topoi, the shape Stacks 0G7E is stated for. -/
abbrev toZariskiHom :
    RingedToposHom (smallEtaleRingedSite B S hS).toRingedTopos S.zariskiRingedSite.toRingedTopos :=
  (toZariskiRingedSiteHom B S hS).toRingedToposHom

/-- `ε^*` on sheaves of modules: the pullback along `ε`, read as a morphism of ringed topoi. -/
abbrev etalePullback :
    SheafOfModules.{u} S.ringCatSheaf ⥤ EtaleModules B S hS :=
  (toZariskiHom B S hS).toModulesHom.pullbackModules

/-- `ε^*` is the associated-module functor of Stacks 03DU (4). -/
def etalePullbackIso : etalePullback B S hS ≅ associatedModuleOfSheaf B S hS :=
  eqToIso (congrArg (fun g : Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedSite B S hS).toRingedTopos S.zariskiRingedSite.toRingedTopos =>
        g.pullbackModules)
      (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom (toZariskiHom B S hS))) ≪≫
    pullbackModulesToZariskiIso B S hS

/-- `ε^*` is exact on the left, the associated-module functor being so (Stacks 08H8). -/
instance preservesFiniteLimits_etalePullback : PreservesFiniteLimits (etalePullback B S hS) :=
  @preservesFiniteLimits_of_natIso _ _ _ _ _ _ (etalePullbackIso B S hS).symm
    (preservesFiniteLimits_associatedModuleOfSheaf B S hS)

/-- `ε^*` is exact on the right, being a left adjoint. -/
instance preservesFiniteColimits_etalePullback : PreservesFiniteColimits (etalePullback B S hS) :=
  @preservesFiniteColimits_of_natIso _ _ _ _ _ _ (etalePullbackIso B S hS).symm
    (preservesFiniteColimits_associatedModuleOfSheaf B S hS)

/-- `ε^*` is additive. -/
instance additive_etalePullback : (etalePullback B S hS).Additive :=
  @Functor.additive_of_iso _ _ _ _ _ _ _ (additive_associatedModuleOfSheaf B S hS) _
    (etalePullbackIso B S hS).symm

/-- `ε^*` on cochain complexes, degreewise. -/
abbrev etalePullbackComplex :
    CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ ⥤ CochainComplex (EtaleModules B S hS) ℤ :=
  (etalePullback B S hS).mapHomologicalComplex (ComplexShape.up ℤ)


/-- **Each cohomology sheaf of `ε^*C` is quasi-coherent as soon as the corresponding cohomology
sheaf of `C` is.**  `ε^*` is exact, so it commutes with cohomology, and it preserves
quasi-coherence, Stacks 03DV (2). -/
theorem isQuasicoherentOnSite_homology_etalePullbackComplex
    (C : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ) (n : ℤ)
    (hC : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((HomologicalComplex.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf)
        (ComplexShape.up ℤ) n).obj C)) :
    ((HomologicalComplex.homologyFunctor (EtaleModules B S hS) (ComplexShape.up ℤ) n).obj
        ((etalePullbackComplex B S hS).obj C)).IsQuasicoherentOnSite := by
  have e : (HomologicalComplex.homologyFunctor (EtaleModules B S hS) (ComplexShape.up ℤ) n).obj
        ((etalePullbackComplex B S hS).obj C) ≅
      (associatedModuleOfSheaf B S hS).obj
        ((HomologicalComplex.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf)
          (ComplexShape.up ℤ) n).obj C) :=
    have e₁ : (HomologicalComplex.homologyFunctor (EtaleModules B S hS) (ComplexShape.up ℤ) n).obj
          ((etalePullbackComplex B S hS).obj C) ≅
        (etalePullback B S hS).obj
          ((HomologicalComplex.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf)
            (ComplexShape.up ℤ) n).obj C) :=
      (StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso
        (etalePullback B S hS) n).app C
    e₁ ≪≫ (etalePullbackIso B S hS).app _
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _ hC)

/-- **`ε^*` of a K-flat complex with flat terms is K-flat**: Stacks 0G7E at `ε`, which is stated
for a morphism of ringed topoi at free universes. -/
theorem isKFlat_etalePullbackComplex (C : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (hC : Stacks.SheafOfModules.IsKFlat S.zariskiRingedSite.O C)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := S.zariskiRingedSite.O) (C.X i)) :
    Stacks.SheafOfModules.IsKFlat (smallEtaleRingedSite B S hS).O
      ((etalePullbackComplex B S hS).obj C) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex
    (toZariskiHom B S hS) C hC hflat

/-- **A complex with quasi-coherent cohomology on `S_étale` is, in the derived category, `ε^*`
of a K-flat complex of `𝒪_S`-modules with flat terms and quasi-coherent cohomology.**

The class of `C` lies in `D_QCoh(S_étale, 𝒪)`, so by Stacks 071Q it is `ε^*A` for an object `A`
of `D_QCoh(𝒪_S)`; a K-flat resolution with flat terms of a representative of `A`, Stacks 06YS,
is the complex sought, `ε^*` being computed degreewise because it is exact. -/
theorem exists_etalePullbackComplex_iso (C : CochainComplex (EtaleModules B S hS) ℤ)
    (hC : ∀ n : ℤ, ((HomologicalComplex.homologyFunctor (EtaleModules B S hS)
      (ComplexShape.up ℤ) n).obj C).IsQuasicoherentOnSite) :
    ∃ C₁ : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ,
      Stacks.SheafOfModules.IsKFlat S.zariskiRingedSite.O C₁ ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := S.zariskiRingedSite.O) (C₁.X i)) ∧
      (∀ n : ℤ, SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
        ((HomologicalComplex.homologyFunctor (SheafOfModules.{u} S.ringCatSheaf)
          (ComplexShape.up ℤ) n).obj C₁)) ∧
      Nonempty (DerivedCategory.Q.obj ((etalePullbackComplex B S hS).obj C₁) ≅
        (DerivedCategory.Q.obj C : DerivedCategory (EtaleModules B S hS))) := by
  obtain ⟨C₁, hK, hflat, hq, ⟨e⟩⟩ := @exists_kFlat_associatedModule_iso.{u + 1} B S hS
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    ⟨(DerivedCategory.Q.obj C : DerivedCategory (EtaleModules B S hS)), fun n =>
      (qcohOnSite B S hS).prop_of_iso
        ((DerivedCategory.homologyFunctorFactors (EtaleModules B S hS) n).app C).symm (hC n)⟩
  refine ⟨C₁, hK, hflat, hq, ⟨?_⟩⟩
  let f₁ : (DerivedCategory.Q.obj ((etalePullbackComplex B S hS).obj C₁) :
        DerivedCategory (EtaleModules B S hS)) ≅
      (DerivedCategory.Q.obj
        (((associatedModuleOfSheaf B S hS).mapHomologicalComplex (ComplexShape.up ℤ)).obj C₁) :
        DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))) :=
    DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
      (fun i => (etalePullbackIso B S hS).app (C₁.X i))
      (fun i j _ => ((etalePullbackIso B S hS).hom.naturality (C₁.d i j)).symm))
  exact f₁ ≪≫ e

end Etale

end AlgebraicGeometry.SmallEtale

end
