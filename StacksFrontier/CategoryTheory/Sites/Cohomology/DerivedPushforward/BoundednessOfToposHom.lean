module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom

/-!
# Boundedness of `Lf^*` and `Rf_*` along a morphism of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi. The derived pullback
`Lf^*` carries `D^{≤ n}(𝒪')` into `D^{≤ n}(𝒪)`, and consequently the derived direct image
`Rf_*` carries `D^{≥ n}(𝒪)` into `D^{≥ n}(𝒪')`.

The first assertion is proved as for a morphism presented by sites
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.isLE_derivedPullback_obj_of_isMorphismOfSites`):
an object of `D^{≤ n}(𝒪')` is represented by a complex of flat modules strictly bounded above
by `n`, such a complex is K-flat with flat terms, so the canonical comparison of Stacks 06YY is
invertible on it, and its degreewise pullback is still strictly bounded above by `n`. The second
is the orthogonality argument through the adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6.

The exact-functor structure of `Rf_*` — the compatibility with the shift and the exactness of
triangles — is the one it inherits as the right adjoint of the exact functor `Lf^*`.

## Main results

* `DerivedCategory.isGE_obj_rightAdjoint_of_isLE_boundednessOfToposHom`: a right adjoint of a
  functor preserving boundedness above preserves boundedness below.
* `Stacks.Cohomology.DerivedPushforward.isLE_derivedPullbackOfToposHom_obj_boundednessOfToposHom`:
  `Lf^*` carries `D^{≤ n}(𝒪')` into `D^{≤ n}(𝒪)`.
* `RingedToposHom.isGE_derivedPushforward_obj_unconditional_boundednessOfToposHom`: `Rf_*`
  carries `D^{≥ n}(𝒪)` into `D^{≥ n}(𝒪')`.
* `derivedPushforwardCommShiftOfToposHomBoundednessOfToposHom`: the compatibility of `Rf_*` with
  the shift.
* `isTriangulated_derivedPushforward_ofToposHom_boundednessOfToposHom`: `Rf_*` is a triangulated
  functor.

The last two lie in the namespace `Stacks.Cohomology.DerivedPushforward`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)

universe u

namespace DerivedCategory

/-- **A right adjoint of a functor preserving boundedness above preserves boundedness below.**
`D^{≥ n}` is the right orthogonal of `D^{≤ n - 1}`, and a morphism from an object `L` of
`D^{≤ n - 1}` into `G E` is adjoint to a morphism `F L ⟶ E` with `F L` again in `D^{≤ n - 1}`,
hence zero. -/
theorem isGE_obj_rightAdjoint_of_isLE_boundednessOfToposHom {𝒞 𝒞' : Type*} [Category* 𝒞] [Abelian 𝒞]
    [HasDerivedCategory 𝒞] [Category* 𝒞'] [Abelian 𝒞'] [HasDerivedCategory 𝒞']
    {F : DerivedCategory 𝒞' ⥤ DerivedCategory 𝒞} {G : DerivedCategory 𝒞 ⥤ DerivedCategory 𝒞'}
    (adj : F ⊣ G) [F.PreservesZeroMorphisms]
    (hF : ∀ (L : DerivedCategory 𝒞') (n : ℤ), L.IsLE n → (F.obj L).IsLE n)
    (M : DerivedCategory 𝒞) (n : ℤ) (hM : M.IsGE n) : (G.obj M).IsGE n := by
  have := hM
  change DerivedCategory.TStructure.t.IsGE (G.obj M) n
  rw [DerivedCategory.TStructure.t.isGE_iff_orthogonal (n - 1) n (by omega)]
  intro L g hL
  have := hF L (n - 1) hL
  have hzero := DerivedCategory.TStructure.t.zero ((adj.homEquiv L M).symm g) (n - 1) n
    (by omega)
  have hz0 : (adj.homEquiv L M).symm 0 = 0 := by
    rw [Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
  exact (adj.homEquiv L M).symm.injective (hzero.trans hz0.symm)

end DerivedCategory

namespace Stacks.Cohomology.DerivedPushforward

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y)

/-- **The derived pullback along a morphism of ringed topoi preserves boundedness above.** If the
cohomology of `E` vanishes in degrees `> n`, so does that of `Lf^*E`. -/
theorem isLE_derivedPullbackOfToposHom_obj_boundednessOfToposHom
    (E : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))) (n : ℤ)
    (hE : E.IsLE n) : ((DerivedPullbackOfToposHom.derivedPullback f).obj E).IsLE n := by
  obtain ⟨K, hflat, hKLE, ⟨e⟩⟩ :=
    Stacks.Cohomology.DerivedPullbackOnRingedTopoi.exists_flatRepresentative_of_isLE
      Y.toRingedSite E n hE
  have hK : IsKFlat (Y := Y) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
    ⟨Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat Y.O K ⟨n, hKLE⟩ hflat, hflat⟩
  have hiso := DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app f
    (IsKFlat (Y := Y)) (fun M ↦ hasResolutions_isKFlat (Y := Y) M)
    (DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat f) _ hK
  have hpLE : CochainComplex.IsStrictlyLE
      ((f.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Functor.map_isZero f.toModulesHom.pullbackModules (K.isZero_of_isStrictlyLE n i hi)
  have := hpLE
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))).app
        ((f.toModulesHom.pullbackModules.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).symm ≪≫
      DerivedCategory.Qh.mapIso
        ((f.toModulesHom.pullbackModules.mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).app K).symm ≪≫
      (asIso ((DerivedPullbackOfToposHom.derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))).symm ≪≫
      (DerivedPullbackOfToposHom.derivedPullback f).mapIso
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)))).app K) ≪≫
      (DerivedPullbackOfToposHom.derivedPullback f).mapIso e) n

/-- The compatibility of `Rf_*` with the shift that it inherits as the right adjoint of `Lf^*`. -/
@[instance_reducible]
def derivedPushforwardCommShiftOfToposHomBoundednessOfToposHom :
    (derivedPushforward (X := X) (Y := Y) f).CommShift ℤ :=
  (derivedPullbackPushforwardAdjunctionOfToposHom f).rightAdjointCommShift ℤ

/-- **`Rf_*` is an exact functor of triangulated categories**, being the right adjoint of the
exact functor `Lf^*`. -/
theorem isTriangulated_derivedPushforward_ofToposHom_boundednessOfToposHom :
    letI := derivedPushforwardCommShiftOfToposHomBoundednessOfToposHom f
    (derivedPushforward (X := X) (Y := Y) f).IsTriangulated := by
  let := derivedPushforwardCommShiftOfToposHomBoundednessOfToposHom f
  let : (DerivedPullbackOfToposHom.derivedPullback f).IsTriangulated :=
    DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general f
  let : (derivedPullbackPushforwardAdjunctionOfToposHom f).CommShift ℤ :=
    (derivedPullbackPushforwardAdjunctionOfToposHom f).commShift_of_leftAdjoint ℤ
  exact (derivedPullbackPushforwardAdjunctionOfToposHom f).isTriangulated_rightAdjoint

end Stacks.Cohomology.DerivedPushforward

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Cohomology.DerivedPushforward

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y)

/-- **The derived direct image along a morphism of ringed topoi preserves boundedness below.**
`D^{≥ n}` is the right orthogonal of `D^{≤ n - 1}`, and a morphism from an object `L` of
`D^{≤ n - 1}` into `Rf_*E` is adjoint to a morphism `Lf^*L ⟶ E` with `Lf^*L` again in
`D^{≤ n - 1}`, hence zero. -/
theorem isGE_derivedPushforward_obj_unconditional_boundednessOfToposHom
    (M : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))) (n : ℤ)
    (hM : M.IsGE n) : ((derivedPushforward (X := X) (Y := Y) f).obj M).IsGE n :=
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_isTriangulated_general f
  DerivedCategory.isGE_obj_rightAdjoint_of_isLE_boundednessOfToposHom
    (derivedPullbackPushforwardAdjunctionOfToposHom f)
    (isLE_derivedPullbackOfToposHom_obj_boundednessOfToposHom f) M n hM

end AlgebraicGeometry.RingedToposHom

end
