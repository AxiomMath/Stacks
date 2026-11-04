module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.MixedHomTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.BaseChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.Derived
public import StacksFrontier.Homology.HomComplex.Evaluation.Iterated
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDerivedHom

/-!
# The étale vanishing bound on the model of `Spec R`

Let `R` be a Noetherian ring and `L` an object of `D(R)` of injective amplitude in `[a, b]`. For
every object `Y` of `D(𝒪_{Spec R})` with coherent cohomology vanishing below `m`, the derived
internal Hom `R𝓗om(ε^* Y, ε^* L̃)` on the equi-universe model of the small étale site of `Spec R`
has no cohomology above `b - m`.

On the small étale site itself, with the derived internal Hom in the raised module universe,
this is Stacks 0E50 (`AlgebraicGeometry.AffineEtaleDuality.isIso_comparison_app`): the internal
Hom is `ε^* R Hom_R(K, L)~`, and `R Hom_R(K, L)` lies in `D^{≤ b - m}`. The vanishing passes to
the model by `AlgebraicGeometry.RingedSite.Mixed.isZero_homology_derivedSheafHom_pull`.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_homology_modelSheafHom_of_injectiveAmplitude`: the derived
  internal Hom on the model has no cohomology above `b - m`.

## References

* [Stacks Project, Tag 0E50](https://stacks.math.columbia.edu/tag/0E50)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.SmallEtale

section Generic

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T)

/-- The functor of the inverse of `smallModelEquiv E T hT` is continuous from the model topology
to the topology of the small étale ringed site. -/
instance smallModelEquiv_symm_functor_isContinuous_ringedSite :
    (smallModelEquiv E T hT).symm.functor.IsContinuous (smallModelTopology E T hT)
      (smallEtaleRingedSite E T hT).J :=
  inferInstanceAs ((smallModelEquiv E T hT).inverse.IsContinuous (smallModelTopology E T hT)
    (topology E T hT))

/-- The inverse functor of the inverse of `smallModelEquiv E T hT` is continuous from the
topology of the small étale ringed site to the model topology. -/
instance smallModelEquiv_symm_inverse_isContinuous_ringedSite :
    (smallModelEquiv E T hT).symm.inverse.IsContinuous (smallEtaleRingedSite E T hT).J
      (smallModelTopology E T hT) :=
  inferInstanceAs ((smallModelEquiv E T hT).functor.IsContinuous (topology E T hT)
    (smallModelTopology E T hT))

/-- The model of the small étale site is the pullback of the small étale ringed site along the
comparison with its model. -/
theorem modelSite_eq_pull :
    modelSite E T hT = RingedSite.Mixed.pull (smallEtaleRingedSite E T hT)
      (smallModelTopology E T hT) (smallModelEquiv E T hT).symm := rfl

end Generic

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (E : BigEtaleSite.{u})
  (hX : E.Contains (Spec R))

open AlgebraicGeometry.AffineEtaleDuality in
/-- Let `L` have injective amplitude in `[a, b]` and let `Y` have coherent cohomology vanishing
below `m`. Then the derived internal Hom from the chart of `Y` to the chart of `L̃` on the model
site of `Spec R` has zero cohomology in every degree `j > b - m`. -/
theorem isZero_homology_modelSheafHom_of_injectiveAmplitude
    (L : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _)) (a b : ℤ)
    (hL : letI := HasDerivedCategory.standard (ModuleCat.{u} R)
      StacksDraft.InjectiveDimension.HasInjectiveAmplitude L a b)
    (m : ℤ) (Y : RingedSite.SchemeStdDerived (Spec R)) (hY : RingedSite.SchemeCoherent _ Y)
    (hYge : ∀ i : ℤ, i < m → IsZero ((RingedSite.schemeStdHomology _ i).obj Y))
    (j : ℤ) (hj : b - m < j) :
    IsZero ((RingedSite.stdHomology (modelSite E (Spec R) hX) j).obj
      (((RingedSite.stdSheafHom (modelSite E (Spec R) hX)).obj
        (op ((chartFunctor E (Spec R) hX).derived.obj Y))).obj
        ((chartFunctor E (Spec R) hX).derived.obj
          (letI := HasDerivedCategory.standard (ModuleCat.{u} R);
            letI : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _;
            (tilde.functor R).mapDerivedCategory.obj L)))) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
  let := HasDerivedCategory.standard (Mod R E hX)
  let := HasDerivedCategory.standard (SheafOfModules.{u + 1} (O R E hX))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (modelSite E (Spec R) hX).O))
  obtain ⟨K, ⟨eK⟩⟩ := StandardModel.exists_iso_mapDerivedCategory R Y fun n =>
    have := hY n; isQuasicoherent_of_isCoherent _
  have hKfin :
      ∀ n : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K) :=
    fun n => finite_homology_of_isCoherent_homology_tilde R K n
      (isCoherent_of_modulesIso ((DerivedCategory.homologyFunctor _ n).mapIso eK).symm (hY n))
  have hKge : K.IsGE m := (DerivedCategory.isGE_iff K m).2 fun i hi =>
    (StandardModel.isZero_homology_mapDerivedCategory_obj_iff R K i).1
      ((hYge i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso eK))
  have hle := StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := R)) K L m a b hKge hL
  have h₀ := DerivedCategory.isZero_of_isLE
    ((StacksDraft.DerivedHom.derivedHomAdjunction (R := R)).hom.obj (op K, L)) (b - m) j hj
  have hc := isIso_comparison_app R E hX K L hKfin ⟨a, b, hL⟩
  have hsrc : IsZero ((DerivedCategory.homologyFunctor _ j).obj
      ((sourceFunctor R E hX).obj (op K, L))) := by
    refine (((Up R E hX).map_isZero ((epsStar R E hX).map_isZero
      ((tilde.functor R).map_isZero h₀))).of_iso ?_)
    exact ((Up R E hX).mapDerivedCategoryHomologyIso j).app _ ≪≫
      (Up R E hX).mapIso (((epsStar R E hX).mapDerivedCategoryHomologyIso j).app _ ≪≫
        (epsStar R E hX).mapIso (((tilde.functor R).mapDerivedCategoryHomologyIso j).app _))
  have htgt : IsZero ((DerivedCategory.homologyFunctor _ j).obj
      ((targetFunctor R E hX).obj (op K, L))) :=
    hsrc.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso
      (@asIso _ _ _ _ ((comparison R E hX).app (op K, L)) hc)).symm
  let P := DerivedCategory.Q.objPreimage ((epsTD R E hX).obj K)
  let eP : DerivedCategory.Q.obj P ≅ (epsTD R E hX).obj K := DerivedCategory.Q.objObjPreimageIso _
  let M := DerivedCategory.Q.objPreimage ((epsTD R E hX).obj L)
  let eM : DerivedCategory.Q.obj M ≅ (epsTD R E hX).obj L := DerivedCategory.Q.objObjPreimageIso _
  have hQ : IsZero ((DerivedCategory.homologyFunctor _ j).obj
      (((RingedSite.Raised.mixedDerivedSheafHomBifunctor (smallEtaleRingedSite E (Spec R) hX)).obj
        (op (DerivedCategory.Q.obj P))).obj (DerivedCategory.Q.obj M))) :=
    htgt.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso
      (((RingedSite.Raised.mixedDerivedSheafHomBifunctor
        (smallEtaleRingedSite E (Spec R) hX)).mapIso eP.op).app _ ≪≫
        ((RingedSite.Raised.mixedDerivedSheafHomBifunctor (smallEtaleRingedSite E (Spec R) hX)).obj
          _).mapIso eM.symm).symm)
  have hY' := RingedSite.Mixed.isZero_homology_derivedSheafHom_pull
    (smallEtaleRingedSite E (Spec R) hX) (smallModelTopology E (Spec R) hX)
    (smallModelEquiv E (Spec R) hX).symm P M j hQ
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheaf E (Spec R) hX))
  let : (modelModulesEquiv E (Spec R) hX).functor.Additive :=
    inferInstanceAs (fromEtaleHom E (Spec R) hX).pushforwardTopos.Additive
  let Φ := (modelModulesEquiv E (Spec R) hX).functor
  let ι₁ : (chartFunctor E (Spec R) hX).derived.obj Y ≅
      DerivedCategory.Q.obj ((RingedSite.Mixed.pushC (smallEtaleRingedSite E (Spec R) hX)
        (smallModelTopology E (Spec R) hX) (smallModelEquiv E (Spec R) hX).symm).obj P) :=
    (chartDerivedIso E (Spec R) hX).app Y ≪≫
      (modelDerived E (Spec R) hX).functor.mapIso
        ((assocDerived E (Spec R) hX).mapIso eK.symm ≪≫ eP.symm) ≪≫
      Φ.mapDerivedCategoryFactors.app P
  let ι₂ : (chartFunctor E (Spec R) hX).derived.obj ((tilde.functor R).mapDerivedCategory.obj L) ≅
      DerivedCategory.Q.obj ((RingedSite.Mixed.pushC (smallEtaleRingedSite E (Spec R) hX)
        (smallModelTopology E (Spec R) hX) (smallModelEquiv E (Spec R) hX).symm).obj M) :=
    (chartDerivedIso E (Spec R) hX).app _ ≪≫
      (modelDerived E (Spec R) hX).functor.mapIso eM.symm ≪≫
      Φ.mapDerivedCategoryFactors.app M
  exact hY'.of_iso ((RingedSite.stdHomology (modelSite E (Spec R) hX) j).mapIso
    (((RingedSite.stdSheafHom (modelSite E (Spec R) hX)).mapIso ι₁.op).symm.app _ ≪≫
      ((RingedSite.stdSheafHom (modelSite E (Spec R) hX)).obj _).mapIso ι₂))

end AlgebraicGeometry.SmallEtale
