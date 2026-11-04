module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.BasisData
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistPsi

/-!
# Tag 01O3: the comparison of twists on the homogeneous sections

Let `g : S' ⟶ S`, `A` a quasi-coherent graded `𝒪_S`-algebra and
`h : Proj_{S'}(g^*A) ⟶ Proj_S(A)` the base change morphism of [Stacks, Tag 01O3]. The comparison
`h^*𝒪_{Proj_S(A)}(d) ≅ 𝒪_{Proj_{S'}(g^*A)}(d)` (`pulledTwistIso`) carries the inverse image of the
section `ψ(a)` of `𝒪(d)` attached to a homogeneous `a` of degree `d` over an open `V` of `S` to the
section `ψ(g^*a)` attached to its pullback.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso_hom_unitApp_psiU`.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.Tag07ZGTwist
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp hom_app_map map_map_homOfLE)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- The base change morphism lies over `g`: the part of `Proj_{S'}(g^*A)` over `g^{-1}(V)` is the
inverse image of the part of `Proj_S(A)` over `V`. -/
theorem baseChangeHom_preimage_toBase (V : S.Opens) :
    baseChangeHom A g ⁻¹ᵁ ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ V) =
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase ⁻¹ᵁ (g ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, baseChangeHom_comp_toBase, Scheme.Hom.comp_preimage]

/-- **[Stacks, Tag 01O3] on the homogeneous sections**: the comparison of twists carries the
inverse image along the base change morphism of `ψ(a)` to `ψ(g^*a)`. -/
theorem pulledTwistIso_hom_unitApp_psiU (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    Scheme.Modules.Hom.app ((pulledTwistIso A g).hom.app (d : ℤ))
        (baseChangeHom A g ⁻¹ᵁ
          ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ V))
        (unitApp (baseChangeHom A g) (relativeTwist A d)
          ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
      (relativeTwist (A.pullback g) d).presheaf.map
        (homOfLE (baseChangeHom_preimage_toBase A g V).le).op
        (psiU (A.pullback g) d (g ⁻¹ᵁ V) (unitApp g (A.piece (d : ℤ)) V a)) := by
  have hψ := Stacks.AlgebraicGeometry.TwistExistenceBasis.glueIso_psi (isBasis_baseChangeBasis g)
    (isAffineOpen_of_mem_baseChangeBasis g) (pulledBasisData A g)
    (Stacks.AlgebraicGeometry.TwistExistenceBasis.BasisTwistData.ofTwistData
      (GluedTwistAlgebra.twistDataOfGradedAlgebra (A.pullback g))) d
  have h1 := congrArg (fun φ => Scheme.Modules.Hom.app φ (g ⁻¹ᵁ V)
    (unitApp g (A.piece (d : ℤ)) V a)) hψ
  have hle : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase ⁻¹ᵁ
      (g ⁻¹ᵁ V) ≤ baseChangeHom A g ⁻¹ᵁ
        ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ V) :=
    (baseChangeHom_preimage_toBase A g V).ge
  have h2 : (pulledPsiB A g d).app (g ⁻¹ᵁ V) (unitApp g (A.piece (d : ℤ)) V a) =
      ((Scheme.Modules.pullback (baseChangeHom A g)).obj (relativeTwist A d)).presheaf.map
        (homOfLE hle).op (unitApp (baseChangeHom A g) (relativeTwist A d)
          ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ V)
          (psiU A d V a)) := by
    have e := Stacks.Conormal.pullbackSection_self g (A.piece (d : ℤ)) V a
    have e2 := basePsi_pullbackSection (M := A.piece (d : ℤ))
      (O := (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece (d : ℤ))
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase g
      (baseChangeHom A g) (baseChangeHom_comp_toBase A g)
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ d) V (g ⁻¹ᵁ V) le_rfl hle a
    rw [e] at e2
    exact e2
  have h3 := hom_app_map ((pulledTwistIso A g).hom.app (d : ℤ)) hle
    (unitApp (baseChangeHom A g) (relativeTwist A d)
      ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a))
  have key : (relativeTwist (A.pullback g) d).presheaf.map (homOfLE hle).op
      (Scheme.Modules.Hom.app ((pulledTwistIso A g).hom.app (d : ℤ)) _
        (unitApp (baseChangeHom A g) (relativeTwist A d)
          ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a))) =
      psiU (A.pullback g) d (g ⁻¹ᵁ V) (unitApp g (A.piece (d : ℤ)) V a) := by
    refine h3.symm.trans ?_
    refine (congrArg (fun z => Scheme.Modules.Hom.app ((pulledTwistIso A g).hom.app (d : ℤ)) _ z)
      h2.symm).trans ?_
    exact h1
  rw [← key, map_map_homOfLE _ (baseChangeHom_preimage_toBase A g V).le hle le_rfl]
  have hid : (homOfLE (le_refl (baseChangeHom A g ⁻¹ᵁ
      ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ V)))).op =
      𝟙 (op (baseChangeHom A g ⁻¹ᵁ
        ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase ⁻¹ᵁ V))) :=
    Subsingleton.elim _ _
  rw [hid, CategoryTheory.Functor.map_id]
  rfl

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
