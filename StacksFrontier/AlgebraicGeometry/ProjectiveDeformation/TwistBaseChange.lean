module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.ProjBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.PsiSections
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistAlgebra
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebraPullbackComp
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlgebraMap
public import StacksFrontier.AlgebraicGeometry.PullbackSections.UnitChase

/-!
# The maps of Serre twists of Tags 07ZJ and 01O3, as maps of graded algebras

For a homomorphism `ψ : A ⟶ B` of quasi-coherent graded `𝒪_S`-algebras invertible in all large
degrees, the isomorphism `Proj_S(B) ⟶ Proj_S(A)` of [Stacks, Tag 07ZJ] carries the Serre twists of
`Proj_S(A)` to those of `Proj_S(B)` (the map `θ` of [Stacks, Tag 07ZG] read on all of
`Proj_S(B)`), compatibly with the products: `projTwistHom`. Followed by the comparison of twists
of the base change morphism of [Stacks, Tag 01O3] this gives, for `g : S' ⟶ S` and
`ψ : g^*A ⟶ A'` invertible in all large degrees, the map of Serre twists along
`Proj_{S'}(A') ⟶ Proj_{S'}(g^*A) ⟶ Proj_S(A)`: `baseChangeTwistHom`.

Both carry the inverse image of the section `ψ(a)` of `𝒪(d)` attached to a homogeneous `a` to the
section attached to the image of `a`.

## Main definitions

* `…ProjectiveDeformation.projTwistHom`, `…ProjectiveDeformation.baseChangeTwistHom`.

## Main results

* `…projTwistHom_app_unitApp_psiU`, `…baseChangeTwistHom_app_unitApp_psiU`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 07ZJ](https://stacks.math.columbia.edu/tag/07ZJ)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGTwist Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_naturality unitApp_map
  hom_app_map map_map_homOfLE)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (psiU)

universe u


namespace Stacks.AlgebraicGeometry.ProjectiveDeformation

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`; see
-- `Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections`.
attribute [-instance] CategoryTheory.catToReflQuiver

open Stacks.AlgebraicGeometry.GradedAlgebraHomSections
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp

section Retract

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)
  (ρ : (relativeProj B).scheme ⟶ ψ.relativeMapDomain.toScheme)
  (hρ : ρ ≫ ψ.relativeMapDomain.ι = 𝟙 _)

/-- **The map of Serre twists along a section `ρ` of the inclusion of `U(ψ)`**, as a map of
`ℤ`-graded algebras `(ρ ≫ r_ψ)^*(⨁_d 𝒪_{Proj_S(A)}(d)) ⟶ ⨁_d 𝒪_{Proj_S(B)}(d)`: the map `θ` of
[Stacks, Tag 07ZG] pulled back along `ρ`. -/
def projTwistHomOf :
    Stacks.Conormal.gradedPullback (ρ ≫ relativeMapHom ψ) (twistAlgebra A) ⟶ twistAlgebra B :=
  (pullbackGradedAlgebraCompIso (twistAlgebra A) ρ (relativeMapHom ψ)).inv ≫
    Stacks.RingedSpace.pullbackGradedAlgebraMap ρ.toLRSHom.toShHom
      (relativeTwistAlgebraHom ψ) ≫
    (pullbackGradedAlgebraCompIso (twistAlgebra B) ρ ψ.relativeMapDomain.ι).hom ≫
    (pullbackGradedAlgebraCongrIso (twistAlgebra B) hρ).hom ≫
    (Stacks.Conormal.gradedPullbackId (twistAlgebra B)).toHom

/-- The degree-`n` component of `projTwistHomOf`. -/
theorem projTwistHomOf_app (n : ℤ) :
    (projTwistHomOf ψ ρ hρ).app n =
      (Scheme.Modules.pullbackComp ρ (relativeMapHom ψ)).inv.app (relativeTwist A n) ≫
        (Scheme.Modules.pullback ρ).map (relativeTwistMap ψ n) ≫
        (Scheme.Modules.pullbackComp ρ ψ.relativeMapDomain.ι).hom.app (relativeTwist B n) ≫
        (Scheme.Modules.pullbackCongr hρ).hom.app (relativeTwist B n) ≫
        (Scheme.Modules.pullbackId _).hom.app (relativeTwist B n) :=
  rfl

include hρ in
/-- `ρ ≫ r_ψ` lies over `S`, on the parts over an open of the base. -/
theorem retract_preimage_toBase_le (V : S.Opens) :
    (ρ ≫ relativeMapHom ψ) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      (relativeProj B).toBase ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, Category.assoc, relativeMapHom_comp_toBase, ← Category.assoc,
    hρ, Category.id_comp]

/-- **The map of Serre twists along a section of `U(ψ) ⊆ Proj_S(B)` on the homogeneous
sections**: it carries the inverse image of `ψ_A(a)` to the restriction of `ψ_B(ψ(a))`. -/
theorem projTwistHomOf_app_unitApp_psiU (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    Scheme.Modules.Hom.app ((projTwistHomOf ψ ρ hρ).app (d : ℤ))
        ((ρ ≫ relativeMapHom ψ) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        (unitApp (ρ ≫ relativeMapHom ψ) (relativeTwist A d)
          ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
      (relativeTwist B d).presheaf.map
        (homOfLE (retract_preimage_toBase_le ψ ρ hρ V)).op
        (psiU B d V ((ψ.app (d : ℤ)).app V a)) := by
  rw [projTwistHomOf_app]
  exact retract_chase ρ (relativeMapHom ψ) ψ.relativeMapDomain.ι hρ (relativeTwistMap ψ d)
    ((relativeProj A).toBase ⁻¹ᵁ V) ((relativeProj B).toBase ⁻¹ᵁ V)
    (relativeMapHom_preimage_toBase ψ V).le (psiU A d V a)
    (psiU B d V ((ψ.app (d : ℤ)).app V a)) (relativeTwistMap_unitApp_psiU ψ d V a)
    (retract_preimage_toBase_le ψ ρ hρ V)

end Retract

section General

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)
  (hψ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ.app (d : ℤ)))

/-- **The map of Serre twists of [Stacks, Tag 07ZJ]**, as a map of `ℤ`-graded algebras
`(Proj_S(B) ⟶ Proj_S(A))^*(⨁_d 𝒪_{Proj_S(A)}(d)) ⟶ ⨁_d 𝒪_{Proj_S(B)}(d)`: the map `θ` of
[Stacks, Tag 07ZG] read on all of `U(ψ) = Proj_S(B)`. -/
def projTwistHom :
    Stacks.Conormal.gradedPullback (projMapOfEventuallyIso ψ hψ) (twistAlgebra A) ⟶
      twistAlgebra B :=
  projTwistHomOf ψ (projRetract ψ hψ) (projRetract_comp_ι ψ hψ)

/-- `Proj_S(B) ⟶ Proj_S(A)` lies over `S`, on the parts over an open of the base. -/
theorem projMapOfEventuallyIso_preimage_toBase_le (V : S.Opens) :
    projMapOfEventuallyIso ψ hψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      (relativeProj B).toBase ⁻¹ᵁ V :=
  retract_preimage_toBase_le ψ (projRetract ψ hψ) (projRetract_comp_ι ψ hψ) V

/-- **The map of Serre twists of [Stacks, Tag 07ZJ] on the homogeneous sections**: it carries the
inverse image of `ψ_A(a)` to the restriction of `ψ_B(ψ(a))`. -/
theorem projTwistHom_app_unitApp_psiU (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    Scheme.Modules.Hom.app ((projTwistHom ψ hψ).app (d : ℤ))
        (projMapOfEventuallyIso ψ hψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        (unitApp (projMapOfEventuallyIso ψ hψ) (relativeTwist A d)
          ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
      (relativeTwist B d).presheaf.map
        (homOfLE (projMapOfEventuallyIso_preimage_toBase_le ψ hψ V)).op
        (psiU B d V ((ψ.app (d : ℤ)).app V a)) :=
  projTwistHomOf_app_unitApp_psiU ψ (projRetract ψ hψ) (projRetract_comp_ι ψ hψ) d V a

end General

section BaseChange

variable {S S' : Scheme.{u}} {A : SheafGradedAlgebra S} {g : S' ⟶ S} {A' : SheafGradedAlgebra S'}
  (ψ : SheafGradedAlgebraHom (A.pullback g) A')
  (hψ : ∀ᶠ d : ℕ in Filter.atTop, IsIso (ψ.app (d : ℤ)))

/-- **The map of Serre twists along `Proj_{S'}(A') ⟶ Proj_{S'}(g^*A) ⟶ Proj_S(A)`**: the comparison
of twists of the base change morphism of [Stacks, Tag 01O3] followed by the map of Serre twists of
[Stacks, Tag 07ZJ] for `ψ : g^*A ⟶ A'`, as a map of `ℤ`-graded algebras. -/
def baseChangeTwistHom :
    Stacks.Conormal.gradedPullback
        (projMapOfEventuallyIso ψ hψ ≫
          Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g)
        (twistAlgebra A) ⟶ twistAlgebra A' :=
  (pullbackGradedAlgebraCompIso (twistAlgebra A) (projMapOfEventuallyIso ψ hψ)
      (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g)).inv ≫
    Stacks.RingedSpace.pullbackGradedAlgebraMap (projMapOfEventuallyIso ψ hψ).toLRSHom.toShHom
      (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).hom ≫
    projTwistHom ψ hψ

/-- The composite lies over `g`, on the parts over an open of the base. -/
theorem baseChangeTwist_preimage_le (V : S.Opens) :
    (projMapOfEventuallyIso ψ hψ ≫
        Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g) ⁻¹ᵁ
        ((relativeProj A).toBase ⁻¹ᵁ V) ≤ (relativeProj A').toBase ⁻¹ᵁ (g ⁻¹ᵁ V) := by
  rw [Scheme.Hom.comp_preimage,
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom_preimage_toBase]
  exact projMapOfEventuallyIso_preimage_toBase_le ψ hψ (g ⁻¹ᵁ V)

/-- **The map of Serre twists along the base change on the homogeneous sections**: it carries the
inverse image of `ψ_A(a)` to the restriction of `ψ_{A'}(ψ(g^*a))`. -/
theorem baseChangeTwistHom_app_unitApp_psiU (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V)) :
    Scheme.Modules.Hom.app ((baseChangeTwistHom ψ hψ).app (d : ℤ))
        ((projMapOfEventuallyIso ψ hψ ≫
          Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g) ⁻¹ᵁ
            ((relativeProj A).toBase ⁻¹ᵁ V))
        (unitApp (projMapOfEventuallyIso ψ hψ ≫
          Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g)
          (relativeTwist A d) ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
      (relativeTwist A' d).presheaf.map (homOfLE (baseChangeTwist_preimage_le ψ hψ V)).op
        (psiU A' d (g ⁻¹ᵁ V)
          ((ψ.app (d : ℤ)).app (g ⁻¹ᵁ V) (unitApp g (A.piece (d : ℤ)) V a))) := by
  let pm := projMapOfEventuallyIso ψ hψ
  let bc := Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom A g
  let T' := relativeTwist (A.pullback g) d
  let b := unitApp g (A.piece (d : ℤ)) V a
  have hge := (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeHom_preimage_toBase
    A g V).le
  have hgp : pm ⁻¹ᵁ bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) ≤
      pm ⁻¹ᵁ ((relativeProj (A.pullback g)).toBase ⁻¹ᵁ (g ⁻¹ᵁ V)) := pm.preimage_mono hge
  have sB : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp pm bc).inv.app (relativeTwist A d))
      (pm ⁻¹ᵁ bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
      (unitApp (pm ≫ bc) (relativeTwist A d) ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
      unitApp pm ((Scheme.Modules.pullback bc).obj (relativeTwist A d))
        (bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        (unitApp bc (relativeTwist A d) ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) :=
    Scheme.Modules.pullbackComp_inv_unit pm bc (relativeTwist A d) _ (psiU A d V a)
  have sC : Scheme.Modules.Hom.app ((Scheme.Modules.pullback pm).map
      ((Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).hom.app (d : ℤ)))
      (pm ⁻¹ᵁ bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
      (unitApp pm ((Scheme.Modules.pullback bc).obj (relativeTwist A d))
        (bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
        (unitApp bc (relativeTwist A d) ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a))) =
      ((Scheme.Modules.pullback pm).obj T').presheaf.map (homOfLE hgp).op
        (unitApp pm T' ((relativeProj (A.pullback g)).toBase ⁻¹ᵁ (g ⁻¹ᵁ V))
          (psiU (A.pullback g) d (g ⁻¹ᵁ V) b)) :=
    (unitApp_naturality pm
      ((Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).hom.app (d : ℤ))
      (bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
      (unitApp bc (relativeTwist A d) ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a))).trans
      ((congrArg (unitApp pm T' (bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
        (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso_hom_unitApp_psiU
          A g d V a)).trans (unitApp_map pm T' hge (psiU (A.pullback g) d (g ⁻¹ᵁ V) b)))
  have hle3 := projMapOfEventuallyIso_preimage_toBase_le ψ hψ (g ⁻¹ᵁ V)
  have sD : Scheme.Modules.Hom.app ((projTwistHom ψ hψ).app (d : ℤ))
      (pm ⁻¹ᵁ bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
      (((Scheme.Modules.pullback pm).obj T').presheaf.map (homOfLE hgp).op
        (unitApp pm T' ((relativeProj (A.pullback g)).toBase ⁻¹ᵁ (g ⁻¹ᵁ V))
          (psiU (A.pullback g) d (g ⁻¹ᵁ V) b))) =
      (relativeTwist A' d).presheaf.map (homOfLE (baseChangeTwist_preimage_le ψ hψ V)).op
        (psiU A' d (g ⁻¹ᵁ V) ((ψ.app (d : ℤ)).app (g ⁻¹ᵁ V) b)) :=
    (hom_app_map ((projTwistHom ψ hψ).app (d : ℤ)) hgp _).trans
      ((congrArg ((relativeTwist A' d).presheaf.map (homOfLE hgp).op)
        (projTwistHom_app_unitApp_psiU ψ hψ d (g ⁻¹ᵁ V) b)).trans
        (map_map_homOfLE _ hgp hle3 (baseChangeTwist_preimage_le ψ hψ V) _))
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  refine (Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply _ _ _ _).trans ?_
  exact (congrArg (fun z => Scheme.Modules.Hom.app ((projTwistHom ψ hψ).app (d : ℤ))
      (pm ⁻¹ᵁ bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullback pm).map
        ((Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso A g).hom.app
          (d : ℤ))) (pm ⁻¹ᵁ bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) z)) sB).trans
    ((congrArg (fun z => Scheme.Modules.Hom.app ((projTwistHom ψ hψ).app (d : ℤ))
      (pm ⁻¹ᵁ bc ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)) z) sC).trans sD)

end BaseChange

end Stacks.AlgebraicGeometry.ProjectiveDeformation

end
