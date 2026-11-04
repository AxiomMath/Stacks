module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorSupport

/-!
# Supports of complexes and of tensor products

Two support statements used in the proof of Stacks 08JR, where the coefficient complexes
`𝒢^• ⊗ f^*ℱ` are supported on the support of `𝒢^•`.

* At a point of a ringed site, the stalk of a tensor product `M ⊗ N` vanishes where the stalk of
  `M` does (Stacks 03EL at a point).
* On an algebraic space, a complex of modules whose terms are supported on `T ⊆ |X|` is supported
  on `T` in the sense of Stacks 08GF: the stalk functors at geometric points are exact.

Combined with the support of a derived tensor product
(`AlgebraicGeometry.Space.cohomologySupportedOn_smallEtaleDerivedTensor_of_left`) and the
identification `𝒢^• ⊗ f^*ℱ ≅ 𝒢^• ⊗^L Lf^*ℱ` for `𝒢^•` flat over the base, this gives the support
of the coefficient complexes.

## Main results

* `Stacks.isZero_sheafFiber_sheafTensor_of_left`.
* `AlgebraicGeometry.Space.cohomologySupportedOn_Q_obj_of_supportOfSheaf_X_subset`.

## References

* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})

/-- **The stalk of a tensor product vanishes where the stalk of its left factor does.** -/
theorem isZero_sheafFiber_sheafTensor_of_left
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hM : IsZero (Φ.sheafFiber.obj ((SheafOfModules.toSheaf _).obj M))) :
    IsZero (Φ.sheafFiber.obj ((SheafOfModules.toSheaf _).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj M).obj N))) := by
  have hM' : Subsingleton ((sheafModuleFiberOfCommRing Φ O).obj M) :=
    (AddCommGrpCat.isZero_iff_subsingleton).1 hM
  have hT : Subsingleton ((sheafModuleFiberOfCommRing Φ O).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj M).obj N)) := by
    have : Subsingleton ((((curriedTensor (ModuleCat.{w} (ringFiber Φ O.obj))).obj
        ((sheafModuleFiberOfCommRing Φ O).obj M)).obj
        ((sheafModuleFiberOfCommRing Φ O).obj N)) : Type w) := by
      show Subsingleton (TensorProduct _ _ _)
      infer_instance
    exact (tensorSheafModuleFiberIso Φ O M N).toLinearEquiv.toEquiv.subsingleton_congr.2 this
  exact (AddCommGrpCat.isZero_iff_subsingleton).2 hT

end Stacks

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X : AlgebraicSpaces B S hS)

/-- **A complex whose terms are supported on `T` has its cohomology supported on `T`.**  At a
geometric point over a point outside `T` the stalks of the terms vanish, and the stalk functor is
exact. -/
theorem cohomologySupportedOn_Q_obj_of_supportOfSheaf_X_subset
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (T : Set (points B S hS X.1))
    (hG : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ T) :
    CohomologySupportedOn.{u, u} B S hS X.1 X.2 T (DerivedCategory.Q.obj G) := by
  intro i x hx
  by_contra hxT
  refine (notMem_supportOfSheaf_iff_forall_isZero_sheafFiber B S hS X.1 X.2 _ x).2
    (fun p hp => ?_) hx
  let Φ := moduleSheafFiber B S hS X p
  refine IsZero.of_iso ?_ (Φ.mapIso ((DerivedCategory.homologyFunctorFactors _ i).app G) ≪≫
    ((G.sc i).mapHomologyIso Φ).symm)
  exact ShortComplex.isZero_homology_of_isZero_X₂ _
    (isZero_moduleSheafFiber_of_notMem B S hS X (G.X i) x (fun h => hxT (hG i h)) p hp)

end AlgebraicGeometry.Space

end
