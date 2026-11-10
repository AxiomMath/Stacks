module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantCoefficientsConservative
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FiniteTorDimension
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.UniformInterval

/-!
# Locally finite Tor dimension bounds the cohomology of an étale complex

An object of `D_ctf(X_étale, Λ)` is bounded: its cohomology sheaves vanish outside one interval.
This is what lets the bounded above constructible flat resolution of Tag 0960 be applied to it,
and it is the first step of the direction (1) ⟹ (2) of Tag 03TT.

Tor amplitude is read on the image of `K` over the constant coefficient ringed site (Tag 03TR), and
it is asked only on the members of a family covering the final object of the small étale site.

## Main results

* `Stacks.EtaleCohomology.isZero_homology_of_coversTop_hasTorAmplitude`: if the restriction of
  the image of `K` to each member of a family covering the final object of the small étale site
  has Tor amplitude in `[a, b]`, then the cohomology sheaves of `K` vanish outside `[a, b]`.
* `Stacks.EtaleCohomology.exists_interval_isZero_homology_of_locallyHasFiniteTorDimension`:
  **an object whose image has locally finite Tor dimension over the constant coefficient ringed
  site has cohomology sheaves concentrated in one interval**, when `X` is quasi-compact.

## References

* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe t u w r d

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  GrothendieckTopology.hasSheafify_addCommGrpCat
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [UnivLE.{u + 1, w}] [UnivLE.{u + 1, max (u + 1) w r}]
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
    (constantCoefficientRingedSite.{u, w, r} B X Λ))]
  [hSliceDerived : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))]
  [∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O) (ComplexShape.up ℤ)]

attribute [local instance 2000] Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

omit hSliceDerived
  [∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, max (u + 1) w r, max (u + 1) w r,
        max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O).obj M).Additive]
  [∀ (U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C)
    (K L : CochainComplex (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
      ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U).O) (ComplexShape.up ℤ)] in
/-- **Vanishing of a cohomology sheaf of the image over the constant coefficient ring sheaf is
vanishing of that cohomology sheaf.** -/
public theorem isZero_homology_of_isZero_homology_moduleSheafOverConstantCoefficients
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor
      (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, w, r} B X Λ)) n).obj
      ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K))) :
    IsZero ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) n).obj K) :=
  isZero_of_isZero_moduleSheafOverConstantCoefficients.{u, w, r} B X Λ _
    (h.of_iso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso.{_, _, _, _, _, d}
        (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ) n).app K).symm)

/-- **A covering family on each member of which the restricted image has Tor amplitude in
`[a, b]` bounds the cohomology sheaves of `K` to `[a, b]`.** -/
public theorem isZero_homology_of_coversTop_hasTorAmplitude
    (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    {ι : Type t} {V : ι → (constantCoefficientRingedSite.{u, w, r} B X Λ).C}
    (hV : (constantCoefficientRingedSite.{u, w, r} B X Λ).J.CoversTop V) (a b : ℤ)
    (hamp : ∀ j, Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude (T (V j))
      ((RingedSite.derivedRestriction.{u + 1, u, max (u + 1) w r, d}
        (constantCoefficientRingedSite.{u, w, r} B X Λ) (V j)).obj
        ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K))
      a b)
    (n : ℤ) (hn : n < a ∨ b < n) :
    IsZero ((DerivedCategory.homologyFunctor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) n).obj K) := by
  set E := (moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K
  have hzero : IsZero ((DerivedCategory.homologyFunctor
      (RingedSite.Modules.{u + 1, u, max (u + 1) w r}
        (constantCoefficientRingedSite.{u, w, r} B X Λ)) n).obj E) := by
    refine Stacks.SheafOfModules.isZero_of_coversTop hV _ fun j => ?_
    let : HasDerivedCategory.{d}
        (SheafOfModules.{max (u + 1) w r}
          ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
            (constantCoefficientRingedSite.{u, w, r} B X Λ).O).over (V j))) := hSliceDerived (V j)
    refine IsZero.of_iso ?_
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso.{_, _,
        _, _, d, d} (SheafOfModules.overFunctor.{max (u + 1) w r}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, max (u + 1) w r}
            (constantCoefficientRingedSite.{u, w, r} B X Λ).O) (V j)) n).app E).symm
    exact Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_of_hasTorAmplitude
      (T (V j)) _ (hamp j) (by simp only [Set.mem_Icc, not_and_or, not_le]; omega)
  exact isZero_homology_of_isZero_homology_moduleSheafOverConstantCoefficients.{u, w, r, d}
    B X Λ K n hzero

/-- **An object of locally finite Tor dimension over the constant coefficient ringed site has
cohomology sheaves concentrated in one interval**, when the underlying space of `X` is
quasi-compact. -/
public theorem exists_interval_isZero_homology_of_locallyHasFiniteTorDimension
    [CompactSpace X.obj]
    (T : ∀ U : (constantCoefficientRingedSite.{u, w, r} B X Λ).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, max (u + 1) w r, d}
        ((constantCoefficientRingedSite.{u, w, r} B X Λ).over U))
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)))
    (hK : Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension
      (X := constantCoefficientRingedSite.{u, w, r} B X Λ) T
      ((moduleSheafOverConstantCoefficientsFunctor.{u, w, r} B X Λ).mapDerivedCategory.obj K)) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)) n).obj K) := by
  open Stacks.SheafOfModules in
  obtain ⟨ι, -, V, f, a, b, hcov, hamp⟩ :=
    DerivedTensorProduct.exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension
      T _ hK (SmallEtale.final B X.obj X.property)
      (SmallEtale.isQuasiCompactObject_of_compactSpace B X.obj X.property _
        (inferInstanceAs (CompactSpace X.obj)))
  refine ⟨a, b, fun n hn => ?_⟩
  refine isZero_homology_of_coversTop_hasTorAmplitude.{_, u, w, r, d} B X Λ T K ?_ a b hamp n hn
  exact ((constantCoefficientRingedSite.{u, w, r} B X Λ).J.coversTop_iff_of_isTerminal
      (SmallEtale.final B X.obj X.property)
      (SmallEtale.finalIsTerminal B X.obj X.property) V).2
    ((Sieve.ofArrows_eq_ofObjects (SmallEtale.finalIsTerminal B X.obj X.property) V f) ▸ hcov)

end Stacks.EtaleCohomology

end
