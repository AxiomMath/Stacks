module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfALocallyConstantComplex

/-!
# The derived pullback of a complex built from finite projective modules

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a morphism of
sites, `Λ` a ring and `Φ : Mod(Λ) ⥤ Mod(𝒪_D)` an additive right exact functor carrying `Λ` to
`𝒪_D`. For a bounded complex `C` of finite projective `Λ`-modules the complex `Φ(C)` is strictly
perfect, so its terms are flat and it is bounded above; hence the derived pullback is computed
termwise on it: `Lf^*(Φ C) ≅ f^*(Φ C)`.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedPullbackObjIsoOfFiniteProjective`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

universe u

namespace Stacks.Cohomology.DerivedPullbackOnRingedTopoi

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] HasDerivedCategory.standard

variable (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

include hmos in
/-- **The derived pullback of `Φ(C)` for a bounded complex `C` of finite projective modules is
computed termwise.** For an additive right exact functor `Φ` from `Λ`-modules to `𝒪_D`-modules
carrying `Λ` to `𝒪_D` and a bounded complex `C` of finite projective `Λ`-modules,
`Lf^* Q(Φ C) ≅ Q(f^*(Φ C))`. -/
def derivedPullbackObjIsoOfFiniteProjective {Λ : Type u} [Ring Λ]
    (Φ : ModuleCat.{u} Λ ⥤ _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [Φ.Additive] [PreservesFiniteColimits Φ]
    (e : Φ.obj (ModuleCat.of Λ Λ) ≅ _root_.SheafOfModules.unit _)
    (C : CochainComplex (ModuleCat.{u} Λ) ℤ) (b : ℤ) (hb : C.IsStrictlyLE b)
    (hbd : {i : ℤ | ¬ IsZero (C.X i)}.Finite)
    (hfin : ∀ i : ℤ, Module.Finite Λ (C.X i)) (hproj : ∀ i : ℤ, Module.Projective Λ (C.X i)) :
    (derivedPullback f).obj
        (DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :=
  have hΦ :
      CochainComplex.IsStrictlyLE ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero Φ (C.isZero_of_isStrictlyLE b i hi)
  derivedPullbackObjIsoOfFlat f hmos _ b hΦ
    (Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect (Y := Y.toRingedSite)
      (Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective Φ e
        hbd hfin hproj))

end Stacks.Cohomology.DerivedPullbackOnRingedTopoi

end
