module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkTensorMixed
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkColimits

/-!
# The support of `E ⊗^L 𝒢` lies in the support of `𝒢`

Let `X` be an algebraic space, `E` an object of `D(𝒪_X)` and `𝒢` a complex of `𝒪_X`-modules
each of whose terms has support in a subset `T ⊆ |X|`.  Then every cohomology sheaf of
`E ⊗^L_{𝒪_X} 𝒢` has support in `T`: `E ⊗^L 𝒢` is supported on `T` in the sense of Stacks 08GF.
This is the support clause of the proof of Stacks 0DKJ.

## Main results

* `Stacks.isZero_sheafFiber_sheafTensor_of_right`: at a point of a ringed site, the stalk of a
  tensor product vanishes when the stalk of its right factor does.
* `AlgebraicGeometry.Space.cohomologySupportedOn_derivedTensor`: the support clause.

## The proof

A K-flat complex `A` representing `E` computes `E ⊗^L 𝒢` as the total complex `Tot(A ⊗ 𝒢)`.  At a
geometric point `x̄` over a point outside `T` the stalk of every `𝒢^q` vanishes; the stalk of a
tensor product is the tensor product of the stalks (Stacks 03EL at a point), so the stalk of every
`A^p ⊗ 𝒢^q` vanishes; the stalk functor commutes with the direct sums forming the terms of the
total complex and is exact, so the stalk of every cohomology sheaf of `Tot(A ⊗ 𝒢)` vanishes.
Support being read on the stalks at geometric points (Stacks 04KA), that is the claim.  No
hypothesis on `E` is used.

## References

* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
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

/-- **The stalk of a tensor product vanishes where the stalk of its right factor does.**  The
stalk of `M ⊗ N` is `M_Φ ⊗ N_Φ` (`Stacks.tensorSheafModuleFiberIso`), and a tensor product with
a zero module is zero. -/
theorem isZero_sheafFiber_sheafTensor_of_right
    (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hN : IsZero (Φ.sheafFiber.obj ((SheafOfModules.toSheaf _).obj N))) :
    IsZero (Φ.sheafFiber.obj ((SheafOfModules.toSheaf _).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj M).obj N))) := by
  have : Subsingleton ((sheafModuleFiberOfCommRing Φ O).obj N) :=
    AddCommGrpCat.isZero_iff_subsingleton.1 hN
  have hT : Subsingleton ((sheafModuleFiberOfCommRing Φ O).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj M).obj N)) := by
    have : Subsingleton ((((curriedTensor (ModuleCat.{w} (ringFiber Φ O.obj))).obj
        ((sheafModuleFiberOfCommRing Φ O).obj M)).obj
        ((sheafModuleFiberOfCommRing Φ O).obj N)) : Type w) := by
      show Subsingleton (TensorProduct _ _ _)
      infer_instance
    exact (tensorSheafModuleFiberIso Φ O M N).toLinearEquiv.toEquiv.subsingleton_congr.2 this
  exact AddCommGrpCat.isZero_iff_subsingleton.2 hT

end Stacks

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The stalk at a point of the small étale site, read on the underlying abelian sheaf of a
module, as a functor on modules. -/
abbrev moduleSheafFiber (p : GeometricPoint B S hS X.1) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf _ ⋙ (etaleSitePoint B S hS X.1 p X.2).sheafFiber

/-- The stalk functor `moduleSheafFiber B S hS X p` preserves finite limits. -/
instance (p : GeometricPoint B S hS X.1) : PreservesFiniteLimits (moduleSheafFiber B S hS X p) := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  have h1 : PreservesFiniteLimits ((etaleSitePoint B S hS X.1 p X.2).sheafFiber
    (A := AddCommGrpCat.{u})) := inferInstance
  have h2 : PreservesFiniteLimits (SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
    inferInstance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h2 h1

/-- The stalk functor `moduleSheafFiber B S hS X p` preserves colimits indexed by categories in
the lowest universe. -/
instance (p : GeometricPoint B S hS X.1) :
    PreservesColimitsOfSize.{0, 0} (moduleSheafFiber B S hS X p) := by
  have h0 : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
    have hsize : PreservesColimitsOfSize.{max (u + 1) u, u}
        (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)) := inferInstance
    @preservesSmallestColimits_of_preservesColimits _ _ _ _ _ hsize
  have h1 : PreservesColimitsOfSize.{0, 0} ((etaleSitePoint B S hS X.1 p X.2).sheafFiber
      (A := AddCommGrpCat.{u})) :=
    have hsize : PreservesColimitsOfSize.{u, u} ((etaleSitePoint B S hS X.1 p X.2).sheafFiber
        (A := AddCommGrpCat.{u})) := inferInstance
    @preservesSmallestColimits_of_preservesColimits _ _ _ _ _ hsize
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ h0 h1

/-- The stalk functor `moduleSheafFiber B S hS X p` preserves finite colimits. -/
instance (p : GeometricPoint B S hS X.1) :
    PreservesFiniteColimits (moduleSheafFiber B S hS X p) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The stalk functor `moduleSheafFiber B S hS X p` is additive. -/
instance (p : GeometricPoint B S hS X.1) : (moduleSheafFiber B S hS X p).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The stalk of a module on `X` at a geometric point lying over a point outside its support
vanishes. -/
theorem isZero_moduleSheafFiber_of_notMem (M : Modules.{u, u} B S hS X.1 X.2)
    (x : points B S hS X.1) (hx : x ∉ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M))
    (p : GeometricPoint B S hS X.1) (hp : p.LiesOver x) :
    IsZero ((moduleSheafFiber B S hS X p).obj M) :=
  (notMem_supportOfSheaf_iff_forall_isZero_sheafFiber B S hS X.1 X.2 _ x).1 hx p hp

/-- **The support clause of Stacks 0DKJ.**  If every term of `𝒢` has support in `T`, then
`E ⊗^L_{𝒪_X} 𝒢` is supported on `T` (Stacks 08GF), for every object `E` of `D(𝒪_X)`. -/
theorem cohomologySupportedOn_derivedTensor
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (Z : Set (points B S hS X.1))
    (hG : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z) :
    CohomologySupportedOn.{u, u} B S hS X.1 X.2 Z
      ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)) := by
  intro i x hx
  by_contra hxZ
  obtain ⟨A, a, hA, hqa⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize
    (smallEtaleRingedSite B S hS X.1 X.2).O (DerivedCategory.Q.objPreimage E)
  let eA : DerivedCategory.Q.obj A ≅ E :=
    asIso (DerivedCategory.Q.map a) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  let Tot := ((Stacks.SheafOfModules.Tensor.tensorComplex
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj A).obj G
  let e : (DerivedCategory.homologyFunctor _ i).obj
      ((T.tensor.obj E).obj (DerivedCategory.Q.obj G)) ≅ Tot.homology i :=
    (DerivedCategory.homologyFunctor _ i).mapIso
        (((T.tensor.mapIso eA).app _).symm ≪≫ T.comparisonLeft A G hA) ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app Tot
  refine (notMem_supportOfSheaf_iff_forall_isZero_sheafFiber B S hS X.1 X.2 _ x).2
    (fun p hp => ?_) hx
  let Φ := moduleSheafFiber B S hS X p
  have hterm : IsZero (Φ.obj (Tot.X i)) := by
    have heq : Tot.X i = ∐ (((Stacks.SheafOfModules.Tensor.sheafTensor
        (smallEtaleRingedSite B S hS X.1 X.2).O).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj A |>.obj G).toGradedObject.mapObjFun
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) i := rfl
    rw [heq]
    refine IsZero.of_iso (Stacks.ShiftedSum.isZero_coproduct _
      fun j => ?_) (PreservesCoproduct.iso Φ _)
    obtain ⟨⟨p', q⟩, -⟩ := j
    exact Stacks.isZero_sheafFiber_sheafTensor_of_right (etaleSitePoint B S hS X.1 p X.2)
      (smallEtaleRingedSite B S hS X.1 X.2).O (A.X p') (G.X q)
      (isZero_moduleSheafFiber_of_notMem B S hS X (G.X q) x (fun h => hxZ (hG q h)) p hp)
  exact (IsZero.of_iso (ShortComplex.isZero_homology_of_isZero_X₂ _ hterm)
    ((Tot.sc i).mapHomologyIso Φ).symm).of_iso (Φ.mapIso e)

end AlgebraicGeometry.Space

end
