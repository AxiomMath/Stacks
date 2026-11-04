module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralHigherDirectImage
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Higher direct images along a composite with an integral morphism

Let `π` be an integral morphism of schemes. Direct image `π_*` of abelian sheaves on the small
étale sites is exact ([Stacks, Tag 04C2]) and preserves injective objects, being right adjoint to
the exact inverse image. Consequently higher direct images along a composite with `π`, on
either side, are computed by `π_*` and the higher direct images of the other factor:

* for `h : X ⟶ Y` and `π : Y ⟶ Z`, `R^q(h ≫ π)_* ≅ π_* ∘ R^q h_*`, because an exact functor
  applied after a left exact one commutes with taking right derived functors;
* for `π : X ⟶ Y` and `h : Y ⟶ Z`, `R^q(π ≫ h)_* ≅ R^q h_* ∘ π_*`, because `π_*` carries an
  injective resolution of a sheaf to an injective resolution of its direct image.

These are the two cases of the relative Leray spectral sequence ([Stacks, Tag 0734]) for a
composite with an integral morphism in which the spectral sequence degenerates, since
`R^p π_* = 0` for `p > 0` ([Stacks, Tag 03QP]). Both are natural isomorphisms of functors in the
sheaf.

## Main definitions

* `CategoryTheory.NatIso.rightDerived` — transport of a right derived functor along an
  isomorphism of functors.
* `Stacks.EtaleCohomology.rightDerivedCompIntegralIso` — `R^q h_* ⋙ π_* ≅ R^q(h ≫ π)_*` for
  `π` integral.
* `Stacks.EtaleCohomology.integralCompRightDerivedIso` — `π_* ⋙ R^q h_* ≅ R^q(π ≫ h)_*` for
  `π` integral.

## Main results

* `Stacks.EtaleCohomology.smallEtalePushforwardAb_preservesHomology_of_isIntegralHom` — direct
  image along an integral morphism preserves homology.

## References

* [Stacks Project, Tag 0734](https://stacks.math.columbia.edu/tag/0734)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace CategoryTheory.NatIso

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasInjectiveResolutions C] {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- **Transport of a right derived functor along an isomorphism of functors.** An isomorphism
`F ≅ G` of additive functors induces an isomorphism `R^n F ≅ R^n G` of their right derived
functors. -/
def rightDerived (e : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

end CategoryTheory.NatIso

namespace Stacks.EtaleCohomology

/-- **Direct image of abelian sheaves along an integral morphism preserves homology.** -/
public theorem smallEtalePushforwardAb_preservesHomology_of_isIntegralHom {X Y : Scheme.{u}}
    (π : X ⟶ Y) [IsIntegralHom π] : (smallEtalePushforwardAb π).PreservesHomology := by
  have hra : (smallEtalePushforwardAb π).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb π⟩⟩
  have hfl : PreservesFiniteLimits (smallEtalePushforwardAb π) := inferInstance
  have hepi : (smallEtalePushforwardAb π).PreservesEpimorphisms :=
    smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom π
  exact Functor.preservesHomology_of_preservesEpis_and_kernels (smallEtalePushforwardAb π)

/-- **Higher direct images along `h ≫ π` with `π` integral.** For `h : X ⟶ Y` and an integral
`π : Y ⟶ Z`, the identification `h_* ⋙ π_* ≅ (h ≫ π)_*` of direct images induces
`R^q h_* ⋙ π_* ≅ R^q(h ≫ π)_*`, naturally in the sheaf. -/
public def rightDerivedCompIntegralIso {X Y Z : Scheme.{u}} (h : X ⟶ Y) (π : Y ⟶ Z)
    [IsIntegralHom π] (q : ℕ) :
    (smallEtalePushforwardAb h).rightDerived q ⋙ smallEtalePushforwardAb π ≅
      (smallEtalePushforwardAb (h ≫ π)).rightDerived q :=
  haveI := smallEtalePushforwardAb_preservesHomology_of_isIntegralHom π
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _
    (smallEtalePushforwardAbCompIso h π) q

/-- **Higher direct images along `π ≫ h` with `π` integral.** For an integral `π : X ⟶ Y` and
`h : Y ⟶ Z`, `π_* ⋙ R^q h_* ≅ R^q(π ≫ h)_*`, naturally in the sheaf. -/
public def integralCompRightDerivedIso {X Y Z : Scheme.{u}} (π : X ⟶ Y) [IsIntegralHom π]
    (h : Y ⟶ Z) (q : ℕ) :
    smallEtalePushforwardAb π ⋙ (smallEtalePushforwardAb h).rightDerived q ≅
      (smallEtalePushforwardAb (π ≫ h)).rightDerived q :=
  haveI : (smallEtalePushforwardAb π).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb π⟩⟩
  (NatIso.ofComponents
    (fun A ↦ (Stacks.RightDerivedComp.objIso (smallEtalePushforwardAb π) (injectiveResolution A)
      (fun n hn ↦ isZero_rightDerived_smallEtalePushforwardAb_of_isIntegralHom π A n hn)
      (smallEtalePushforwardAb h) q).symm)
    (fun {A B} g ↦ by
      rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
      exact (Stacks.RightDerivedComp.objIso_hom_naturality (smallEtalePushforwardAb π)
        (smallEtalePushforwardAb h) q
        (fun n hn ↦ isZero_rightDerived_smallEtalePushforwardAb_of_isIntegralHom π A n hn)
        (fun n hn ↦ isZero_rightDerived_smallEtalePushforwardAb_of_isIntegralHom π B n hn)
        g).symm)) ≪≫
    NatIso.rightDerived (smallEtalePushforwardAbCompIso π h) q

end Stacks.EtaleCohomology

end
