module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.RestrictionGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelPointTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnASliceGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessCriterionGeneral
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Coherent

/-!
# Perfectness of the direct image to the point from pseudo-coherence over the ring

Let `T` be an affine object of the big fppf site, `R = Γ(T, 𝒪_T)`, and `f : X ⟶ T` a flat
morphism from a quasi-compact and quasi-separated algebraic space, read as the morphism of ringed
topoi `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` of the spaces-étale model. For a perfect object `E` of
the model, `Rf_*E` has finite Tor dimension over the point
(`AlgebraicGeometry.Space.exists_hasTorAmplitude_derivedPushforward_spacesEtaleModelToBaseRing`).
So `Rf_*E` is perfect as soon as its image in `D(R)` is pseudo-coherent: that is the perfectness
criterion of Stacks 08G7 over the punctual ringed topos, the pseudo-coherence being carried from
`D(R)` to the point.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_global_derived_approximation`: a strictly
  perfect complex mapping to `E` in `D(O)`, isomorphically on cohomology above `m` and
  surjectively in degree `m`, makes `E` `m`-pseudo-coherent.
* `Space.isPseudoCoherentFrom_point_of_isPseudoCoherentFrom_pointDerivedEquiv`: an object over
  the point whose image in `D(R)` is `m`-pseudo-coherent is `m`-pseudo-coherent.
* `Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isPseudoCoherent`: `Rf_*E` is
  perfect over the point when its image in `D(R)` is pseudo-coherent.
* `Space.isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_moduleFinite_homology`: for
  `R` Noetherian, `Rf_*E` is perfect over the point when its cohomology modules are finite
  (Stacks 066E).

## References

* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.RingedSite

/-- An exact functor carries a morphism of `D(A)` which is invertible on cohomology above `m` and
surjective in degree `m` to one with the same properties, also after composing with isomorphisms. -/
private theorem isIso_and_epi_homology_map_comp_mapDerivedCategory
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : DerivedCategory A} {X' Y' : DerivedCategory B} (α : X ⟶ Y)
    (i : X' ⟶ F.mapDerivedCategory.obj X) (k : F.mapDerivedCategory.obj Y ⟶ Y')
    [IsIso i] [IsIso k] (m : ℤ)
    (hiso : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ m).map α)) :
    (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map
      (i ≫ F.mapDerivedCategory.map α ≫ k))) ∧
    Epi ((DerivedCategory.homologyFunctor _ m).map (i ≫ F.mapDerivedCategory.map α ≫ k)) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have : IsIso ((DerivedCategory.homologyFunctor _ j).map (F.mapDerivedCategory.map α)) := by
      refine (NatIso.isIso_map_iff
        (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F j) α).2 ?_
      have := hiso j hj
      exact inferInstanceAs (IsIso (F.map ((DerivedCategory.homologyFunctor _ j).map α)))
    simp only [Functor.map_comp]
    infer_instance
  · have : Epi ((DerivedCategory.homologyFunctor _ m).map (F.mapDerivedCategory.map α)) :=
      (StacksDraft.PseudoCoherence.epi_map_iff_of_natIso
        (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F m) α).2
        (F.map_epi _)
    simp only [Functor.map_comp]
    exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' this (IsIso.epi_of_iso _))

section GlobalApproximation

variable (X : RingedSite.{u, u, u})
variable [HasSheafify X.J AddCommGrpCat.{u}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hSliceDer : ∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory

/-- **A global strictly perfect approximation in the derived category gives pseudo-coherence.**
If a strictly perfect complex `P` of `O`-modules maps to `E` in `D(O)` by a morphism which is
invertible on cohomology in every degree `> m` and surjective in degree `m`, then `E` is
`m`-pseudo-coherent (Stacks 08FT): restricting to any object of the site keeps `P` strictly
perfect and the two properties of the morphism, restriction being exact. -/
theorem isPseudoCoherentFrom_of_global_derived_approximation
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)
    (β : DerivedCategory.Q.obj P ⟶ E)
    (hiso : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ m).map β)) :
    X.IsPseudoCoherentFrom E m := by
  classical
  let K := DerivedCategory.Q.objPreimage E
  let eK : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  refine X.isPseudoCoherentFrom_of_derived_approximation_general E m K eK (fun V => ?_)
  let F := SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
  have : PreservesFiniteLimits F :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have : PreservesFiniteColimits F :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  let β' := β ≫ eK.inv
  have hiso' : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map β') := by
    intro j hj
    have := hiso j hj
    rw [Functor.map_comp]
    infer_instance
  have hepi' : Epi ((DerivedCategory.homologyFunctor _ m).map β') := by
    rw [Functor.map_comp]
    exact epi_comp' hepi (IsIso.epi_of_iso _)
  have h := isIso_and_epi_homology_map_comp_mapDerivedCategory F β'
    (F.mapDerivedCategoryFactors.app P).inv (F.mapDerivedCategoryFactors.app K).hom m hiso' hepi'
  exact ⟨X.restrictComplex P V, X.isStrictlyPerfect_over_general V hP, _, h.1, h.2⟩

end GlobalApproximation

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory
attribute [local instance] hasCoproducts_derivedCategory_modules

attribute [local instance high] sheafTensor_additive_ringedSite sheafTensor_obj_additive_ringedSite
  hasMapBifunctor_sheafTensor_ringedSite

section Point

variable {R : Type u} [CommRing R]

/-- **`m`-pseudo-coherence passes from `D(R)` to the punctual ringed topos.** If the image in
`D(R)` of an object `K` of `D(pt, R)` is `m`-pseudo-coherent, that is approximated in degrees
`≥ m` by a bounded complex of finite free `R`-modules (Stacks 064Q), then `K` is
`m`-pseudo-coherent over the point (Stacks 08FT): the complex, carried to the point, is strictly
perfect. -/
theorem isPseudoCoherentFrom_point_of_isPseudoCoherentFrom_pointDerivedEquiv
    (K : DerivedCategory (pointRingedTopos (CommRingCat.of R)).Modules) (m : ℤ)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((pointDerivedEquiv (R := R)).functor.obj K) m) :
    (pointRingedTopos (CommRingCat.of R)).toRingedSite.IsPseudoCoherentFrom K m := by
  obtain ⟨P, ⟨⟨a, ha⟩, ⟨b, hb⟩, hff⟩, α, hiso, hepi⟩ := hK
  let e := baseRingPointModulesEquiv (R := R)
  have hbd : {n : ℤ | ¬ IsZero (P.X n)}.Finite := (Set.finite_Icc a b).subset fun n hn =>
    ⟨not_lt.1 fun h => hn (P.isZero_of_isStrictlyGE a n h),
      not_lt.1 fun h => hn (P.isZero_of_isStrictlyLE b n h)⟩
  have hunit : e.inverse.obj (ModuleCat.of R R) ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedTopos (CommRingCat.of R)).O) :=
    e.inverse.mapIso ((show ModuleCat.of R (Shrink.{u} R) ≅ ModuleCat.of R R from
        (Shrink.linearEquiv R R).toModuleIso).symm ≪≫
        baseRingPointModulesEquivUnitIso.symm) ≪≫ e.unitIso.symm.app _
  have hSP := Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective
    e.inverse hunit hbd (fun i => (hff i).1)
    (fun i => have := (hff i).2; inferInstance)
  let υ : e.inverse.mapDerivedCategory.obj ((pointDerivedEquiv (R := R)).functor.obj K) ≅ K :=
    ((pointDerivedEquiv (R := R)).unitIso.app K).symm
  let β : DerivedCategory.Q.obj ((e.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶ K :=
    (e.inverse.mapDerivedCategoryFactors.app P).inv ≫ e.inverse.mapDerivedCategory.map α ≫ υ.hom
  have h := RingedSite.isIso_and_epi_homology_map_comp_mapDerivedCategory e.inverse α
    (e.inverse.mapDerivedCategoryFactors.app P).inv υ.hom m hiso hepi
  exact RingedSite.isPseudoCoherentFrom_of_global_derived_approximation
    (pointRingedTopos (CommRingCat.of R)).toRingedSite K m _ hSP β h.1 h.2

end Point

section DirectImage

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}
  {T : BigFppfOver B S hS}

/-- **`Rf_*E` is perfect over the point once it is pseudo-coherent over `R`.** Let `T` be affine,
`R = Γ(T, 𝒪_T)` and `f : X ⟶ T` flat with `X` quasi-compact and quasi-separated, read as the
morphism `(X_{spaces,étale}, 𝒪_X) ⟶ (pt, R)` of the spaces-étale model, and let `E` be perfect.
If the image of `Rf_*E` in `D(R)` is pseudo-coherent, then `Rf_*E` is perfect over the punctual
ringed topos: it has Tor amplitude in some `[a, b]`
(`AlgebraicGeometry.Space.exists_hasTorAmplitude_derivedPushforward_spacesEtaleModelToBaseRing`)
and is `(a - 1)`-pseudo-coherent, so Stacks 08G7 applies. -/
theorem isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isPseudoCoherent
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E)
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj
        ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E))) :
    (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E) := by
  obtain ⟨a, b, hab, hamp⟩ :=
    exists_hasTorAmplitude_derivedPushforward_spacesEtaleModelToBaseRing B S hS hZ hXqc hXqs f
      hflat hT E hE
  exact Stacks.SheafOfModules.DerivedTensorProduct.torAmplitudePerfectnessCriterion_general
    (Z := (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite) _ _ a b hab hamp
    (isPseudoCoherentFrom_point_of_isPseudoCoherentFrom_pointDerivedEquiv _ (a - 1)
      ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
        _ 0).1.1 hpc (a - 1)))

/-- **`Rf_*E` is bounded above** for a perfect `E` on the spaces-étale model of a quasi-compact and
quasi-separated space: `E` lies in `D_QCoh`
(`AlgebraicGeometry.Space.derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace`)
and is bounded above, having finite Tor amplitude, and `Rf_*` is uniformly bounded above on
`D_QCoh`. -/
theorem exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing_of_isPerfect
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) {R : Type u} [CommRing R]
    (φ : R →+* modelGlobalFunctions B S hS X)
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E) :
    ∃ c : ℤ, ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X φ)).obj E).IsLE c := by
  obtain ⟨a, b, -, hamp⟩ := exists_hasTorAmplitude_of_isPerfect_spacesEtaleModel B S hS X hXqc E hE
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing B S hS X φ hZ hXqc
    hXqs
  have hEb : E.IsLE b :=
    Stacks.SheafOfModules.DerivedTensorProduct.isLE_of_hasTorAmplitude
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, u + 1}
        (spacesEtaleModelRingedTopos B S hS X).toRingedSite) E hamp
  exact ⟨b + N, hN E
    (derivedCategoryB_isQuasicoherentOnSite_of_isPerfect_of_isAlgebraicSpace B S hS X.1 X.2 _
      (isPerfect_spacesEtaleModelModulesEquiv_functor B S hS X E hE)) b
    (isLE_mapDerivedCategory_spacesEtaleModelModulesEquiv B S hS X E b hEb)⟩

/-- **`Rf_*E` is perfect over the point once its cohomology modules are finite, `R` Noetherian.**
Over a Noetherian ring a bounded-above object with finite cohomology modules is pseudo-coherent
(Stacks 066E), and `Rf_*E` is bounded above
(`exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing_of_isPerfect`). -/
theorem isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_moduleFinite_homology
    (hZ : B.Contains (⊤_ Scheme.{u})) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) [IsNoetherianRing (baseRing B S hS T)]
    (E : DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules)
    (hE : (spacesEtaleModelRingedTopos B S hS X).toRingedSite.IsPerfect E)
    (hfin : ∀ i : ℤ, Module.Finite (baseRing B S hS T)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing B S hS T)) i).obj
        ((pointDerivedEquiv (R := baseRing B S hS T)).functor.obj
          ((derivedPushforward
            (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E)))) :
    (pointRingedTopos (CommRingCat.of (baseRing B S hS T))).toRingedSite.IsPerfect
      ((derivedPushforward (spacesEtaleModelToBaseRing B S hS X (baseRingHomOfMap f))).obj E) := by
  obtain ⟨c, hc⟩ := exists_isLE_derivedPushforward_spacesEtaleModelToBaseRing_of_isPerfect B S hS
    hZ hXqc hXqs (baseRingHomOfMap f) E hE
  refine isPerfect_derivedPushforward_spacesEtaleModelToBaseRing_of_isPseudoCoherent B S hS hZ hXqc
    hXqs f hflat hT E hE ?_
  refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology _ 0
    (baseRing B S hS T)).2.1).2 ⟨⟨c, fun i hi => ?_⟩, hfin⟩
  exact ((baseRingPointModulesEquiv (R := baseRing B S hS T)).functor.map_isZero
    ((DerivedCategory.isLE_iff _ c).1 hc i hi)).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (baseRingPointModulesEquiv (R := baseRing B S hS T)).functor i).app _)

end DirectImage

end AlgebraicGeometry.Space

end
