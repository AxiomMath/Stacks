module

public import StacksFrontier.AlgebraicGeometry.Morphism.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistTransport
public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.PsiSections

/-!
# Tag 07ZG: `θ` commutes with base change

For `g : S' ⟶ S` and a homomorphism `ψ : A ⟶ B` of quasi-coherent graded `𝒪_S`-algebras, the map
`θ_{g^*ψ}` of Tag 07ZG is the inverse image of `θ_ψ` along the restriction
`U(g^*ψ) ⟶ U(ψ)` of the base-change morphism of Tag 01O3, read through the comparisons of the
twists of Tag 01O3 (`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.pulledTwistIso`).

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeTwistAlgebraHom_pullback`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (twD Otw psiU)

universe u

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

variable {S : Scheme.{u}} {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

section PullbackInstance

/-- Restricting along two inclusions between equal opens is the identity. -/
theorem map_homOfLE_map_homOfLE {X : Scheme.{u}} (M : X.Modules) {O O' : X.Opens}
    (h₁ : O ≤ O') (h₂ : O' ≤ O) (x : M.val.obj (op O)) :
    M.val.map (homOfLE h₁).op (M.val.map (homOfLE h₂).op x) = x := by
  refine (PresheafOfModules.map_comp_apply M.val (homOfLE h₂).op (homOfLE h₁).op x).symm.trans ?_
  rw [show (homOfLE h₂).op ≫ (homOfLE h₁).op = 𝟙 (op O) from Subsingleton.elim _ _]
  exact PresheafOfModules.map_id_apply M.val (op O) x

/-- A comparison of twists given on the unit image of a section, read on a pulled-back section. -/
theorem chi_psiU_of_unitApp {X Y : Scheme.{u}} (c : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (χ : (Scheme.Modules.pullback c).obj M ⟶ N) {O : Y.Opens} {O' : X.Opens} (m : M.val.obj (op O))
    (n : N.val.obj (op O')) {e' : c ⁻¹ᵁ O ≤ O'}
    (h : Scheme.Modules.Hom.app χ (c ⁻¹ᵁ O)
        (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp c M O m) =
      N.presheaf.map (homOfLE e').op n) (hV : O' ≤ c ⁻¹ᵁ O) :
    χ.val.app (op O') (Scheme.Modules.pullbackSection c M O O' hV m) = n := by
  unfold Scheme.Modules.pullbackSection
  refine (PresheafOfModules.naturality_apply χ.val (homOfLE hV).op _).trans ?_
  refine (congrArg (N.val.map (homOfLE hV).op) h).trans ?_
  exact map_homOfLE_map_homOfLE N hV e' n

variable {S' : Scheme.{u}} (g : S' ⟶ S)

open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist in
/-- **The map `θ` of Tag 07ZG commutes with base change**: for `g : S' ⟶ S`, `θ_{g^*ψ}` is the
inverse image of `θ_ψ` along the restriction `U(g^*ψ) ⟶ U(ψ)` of the base-change morphism of
Tag 01O3, read through the comparisons of twists of Tag 01O3. -/
theorem relativeTwistAlgebraHom_pullback :
    transportTwistHom ψ (ψ.pullback g) (pulledTwistIso A g) (pulledTwistIso B g)
        ((baseChangeHom B g).resLE ψ.relativeMapDomain (ψ.pullback g).relativeMapDomain
          (baseChangeHom_preimage_relativeMapDomain ψ g).ge)
        (relativeMapHom_pullback_comp_baseChangeHom ψ g)
        (Scheme.Hom.resLE_comp_ι _ _) (relativeTwistAlgebraHom ψ) =
      relativeTwistAlgebraHom (ψ.pullback g) := by
  refine transportTwistHom_relativeTwistAlgebraHom ψ g (ψ.pullback g) _ _ _ _ _
    (baseChangeHom_comp_toBase A g) (baseChangeHom_comp_toBase B g)
    (fun d => Iso.refl _) (fun d => Iso.refl _) (fun d => ?_) ?_ ?_
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  all_goals
    intro d V a hV
    exact (chi_psiU_of_unitApp _ _ _ _ (pulledTwistIso_hom_unitApp_psiU _ g d V a) hV).trans
      (congrArg (psiU _ d _) (PresheafOfModules.map_id_apply _ _ _).symm)

end PullbackInstance

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
