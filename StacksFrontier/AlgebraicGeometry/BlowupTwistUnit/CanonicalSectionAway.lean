module

public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionPairing
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierPullbackCorollaries
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedEmptySupport
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Locality

/-!
# The canonical section of a divisor twist is invertible away from the divisor

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor, with invertible sheaf `𝒪_X(D)` and
canonical section `1_D`. Multiplication by `1_D` is the morphism
`Stacks.Divisors.canonicalSectionHom D : 𝒪_X ⟶ 𝒪_X(D)`; this file proves that its inverse image
along the inclusion of an open disjoint from `D` is an isomorphism.

## The argument

The canonical section is paired with the ideal inclusion by the evaluation pairing:
contracting `𝒪_X(D) ⊗ ℐ_D` against `ℐ_D ⟶ 𝒪_X` is the pairing followed by multiplication by
`1_D` (`Stacks.Divisors.tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor`). The pairing
and the right unit constraint are isomorphisms, so multiplication by `1_D` is invertible on an
open exactly when the ideal inclusion `ℐ_D ⟶ 𝒪_X` is, by the naturality of the pullback tensor
comparison of [Stacks, Tag 01CD]
(`Stacks.AffineProjectionFormula.isIso_pullback_tensorSheaf_map`).

The ideal inclusion is invertible on an open `W` disjoint from `D` because the inverse image of
`ℐ_D` along `W.ι` is `ℐ_{D ∩ W}` — the pullback of an effective Cartier divisor is defined along
any morphism missing its support,
`Stacks.Divisors.isPullbackDefined_of_notMem_support_of_weaklyAssociated`, and then
`Stacks.Divisors.pullbackIdealSheafComapIso` identifies the two compatibly with the two
inclusions into the structure sheaf — and `D ∩ W` is empty, so its ideal inclusion is an
isomorphism (`Stacks.Divisors.Eta.isIso_idealSheafι_of_supportSet_eq_empty`).

## Main results

* `Stacks.BlowupTwistUnit.isIso_pullback_idealSheafInclusion_of_disjoint`: **the ideal inclusion
  `ℐ_D ⟶ 𝒪_X` becomes invertible on an open disjoint from `D`.**
* `Stacks.BlowupTwistUnit.isIso_pullback_canonicalSectionHom_of_disjoint`: **multiplication by
  the canonical section becomes invertible on an open disjoint from `D`.**

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace

open scoped CategoryTheory.Prod

universe u

namespace Stacks.BlowupTwistUnit

variable {X : Scheme.{u}} (D : X.IdealSheafData) (W : X.Opens)

/-- **The ideal inclusion `ℐ_D ⟶ 𝒪_X` of an effective Cartier divisor becomes invertible on an
open disjoint from the divisor.**

The pullback of the divisor to `W` is defined, because no point of `W` lies in its support, and
the inverse image of the ideal sheaf is the ideal sheaf of that pullback, compatibly with the two
inclusions into the structure sheaf. The pullback has empty support, so its ideal inclusion is an
isomorphism. -/
theorem isIso_pullback_idealSheafInclusion_of_disjoint
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hW : ∀ y : (W : Scheme.{u}), W.ι y ∉ D.supportSet) :
    IsIso ((pullbackFunctor W.ι.toLRSHom.toShHom).map
      (Stacks.Divisors.idealSheafInclusion D)) := by
  have hpd : Stacks.Divisors.IsPullbackDefined W.ι D :=
    Stacks.Divisors.isPullbackDefined_of_notMem_support_of_weaklyAssociated W.ι D ‹_›
      fun y _ ↦ hW y
  have hempty : IsIso (Stacks.Divisors.Eta.idealSheafι (D.comap W.ι)) :=
    Stacks.Divisors.Eta.isIso_idealSheafι_of_supportSet_eq_empty (D.comap W.ι)
      (Stacks.Divisors.Eta.supportSet_comap_eq_empty D W.ι hW)
  have hcompat := Stacks.Divisors.pullbackIdealSheafComapIso_hom_comp_idealSheafι W.ι D hpd
  have hkey : IsIso ((pullbackFunctor W.ι.toLRSHom.toShHom).map
      (Stacks.Divisors.Eta.idealSheafι D) ≫
      (modulePullbackObjUnitIso W.ι.toLRSHom.toShHom).hom) := by
    rw [show (pullbackFunctor W.ι.toLRSHom.toShHom).map
          (Stacks.Divisors.Eta.idealSheafι D) ≫
        (modulePullbackObjUnitIso W.ι.toLRSHom.toShHom).hom =
          (Stacks.Divisors.pullbackIdealSheafComapIso W.ι D hpd).hom ≫
            Stacks.Divisors.Eta.idealSheafι (D.comap W.ι) from hcompat.symm]
    exact IsIso.comp_isIso'
      (Stacks.Divisors.pullbackIdealSheafComapIso W.ι D hpd).isIso_hom hempty
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
    (modulePullbackObjUnitIso W.ι.toLRSHom.toShHom).isIso_hom hkey

/-- **Multiplication by the canonical section `1_D` becomes invertible on an open disjoint from
the divisor.**

The evaluation pairing identifies multiplication by `1_D` with the contraction of
`𝒪_X(D) ⊗ ℐ_D` against the ideal inclusion, up to two isomorphisms; the contraction becomes
invertible wherever the ideal inclusion does, by the naturality of the pullback tensor comparison
of [Stacks, Tag 01CD]. -/
theorem isIso_pullback_canonicalSectionHom_of_disjoint
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hW : ∀ y : (W : Scheme.{u}), W.ι y ∉ D.supportSet) :
    IsIso ((pullbackFunctor W.ι.toLRSHom.toShHom).map
      (Stacks.Divisors.canonicalSectionHom D)) := by
  have hι := isIso_pullback_idealSheafInclusion_of_disjoint D W hW
  have htensor : IsIso ((pullbackFunctor W.ι.toLRSHom.toShHom).map
      (Scheme.Modules.tensorLeftMap (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.idealSheafInclusion D))) := by
    have he : Scheme.Modules.tensorLeftMap (Stacks.Divisors.invertibleSheaf' D)
          (Stacks.Divisors.idealSheafInclusion D) =
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(X).presheaf, (X).IsSheaf⟩))).map
          ((𝟙 (Stacks.Divisors.invertibleSheaf' D) ×ₘ
            Stacks.Divisors.idealSheafInclusion D) :
              ((Stacks.Divisors.invertibleSheaf' D, Stacks.Divisors.negativeTwist' D) : _ × _) ⟶
                (Stacks.Divisors.invertibleSheaf' D,
                  SheafOfModules.unit (structureRingSheaf X.toRingedSpace))) := by
      refine Eq.symm (Eq.trans ?_ (Category.id_comp
        (Scheme.Modules.tensorLeftMap (Stacks.Divisors.invertibleSheaf' D)
          (Stacks.Divisors.idealSheafInclusion D))))
      exact congrArg (fun t => CategoryTheory.NatTrans.app t
          (Stacks.Divisors.negativeTwist' D) ≫
        Scheme.Modules.tensorLeftMap (Stacks.Divisors.invertibleSheaf' D)
          (Stacks.Divisors.idealSheafInclusion D))
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(X).presheaf, (X).IsSheaf⟩).map_id (Stacks.Divisors.invertibleSheaf' D))
    rw [he]
    exact Stacks.AffineProjectionFormula.isIso_pullback_tensorSheaf_map
      W.ι.toLRSHom.toShHom (Stacks.Divisors.invertibleSheaf' D)
      (Stacks.Divisors.idealSheafInclusion D) hι
  have hpair := Stacks.Divisors.tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor D
  have h1 : (pullbackFunctor W.ι.toLRSHom.toShHom).map
          (Stacks.SheafOfModules.Scheme.evaluationIso X
            (Stacks.Divisors.negativeTwist' D)).hom ≫
        (pullbackFunctor W.ι.toLRSHom.toShHom).map
          (Stacks.Divisors.canonicalSectionHom D) =
      (pullbackFunctor W.ι.toLRSHom.toShHom).map
          (Scheme.Modules.tensorLeftMap (Stacks.Divisors.invertibleSheaf' D)
            (Stacks.Divisors.idealSheafInclusion D)) ≫
        (pullbackFunctor W.ι.toLRSHom.toShHom).map
          (Scheme.Modules.tensorRightUnitor (Stacks.Divisors.invertibleSheaf' D)).hom :=
    (Functor.map_comp _ _ _).symm.trans
      ((congrArg ((pullbackFunctor W.ι.toLRSHom.toShHom).map) hpair.symm).trans
        (Functor.map_comp _ _ _))
  have h2 : IsIso ((pullbackFunctor W.ι.toLRSHom.toShHom).map
        (Stacks.SheafOfModules.Scheme.evaluationIso X
          (Stacks.Divisors.negativeTwist' D)).hom ≫
      (pullbackFunctor W.ι.toLRSHom.toShHom).map
        (Stacks.Divisors.canonicalSectionHom D)) := by
    rw [h1]
    exact IsIso.comp_isIso' htensor
      (((pullbackFunctor W.ι.toLRSHom.toShHom).mapIso
        (Scheme.Modules.tensorRightUnitor (Stacks.Divisors.invertibleSheaf' D))).isIso_hom)
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (((pullbackFunctor W.ι.toLRSHom.toShHom).mapIso
      (Stacks.SheafOfModules.Scheme.evaluationIso X
        (Stacks.Divisors.negativeTwist' D))).isIso_hom) h2

end Stacks.BlowupTwistUnit

end
