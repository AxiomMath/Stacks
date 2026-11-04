module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeThetaData
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.RestrictIso

/-!
# The absolute comparison of twists over a member of the trivializing basis

Over a member `V` of the basis of affine opens of `S` trivializing `ℒ`, the comparison
`Proj ℬ(V) ≅ Proj 𝒜(V)` of Tag 02NC is `Proj.map ψ` for the comparison `ψ : 𝒜(V) ⟶ ℬ(V)` attached
to the chosen trivializing section, it is defined everywhere and every comparison map on twists of
Tag 01MY is an isomorphism. So the twists of `Proj 𝒜(V)`, restricted along it, are the twists of
`Proj ℬ(V)` (`Stacks.AlgebraicGeometry.ProjTwistCompare.restrictTwistIso`), multiplicatively and
compatibly with the homogeneous sections.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.absTwistIso`: the identification of the twists
  over a member of the trivializing basis.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.absTwistIso_mul`: it is multiplicative.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.isDegCompat_absTwistIso`: it carries
  homogeneous sections to homogeneous sections.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.ProjTwistSections AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- The chosen trivializing section at a member of the basis trivializes eventually every power. -/
theorem basisSection_eventually (V : trivializingOpens L) :
    ∀ᶠ d : ℕ in Filter.atTop, TrivializesPower L (V : S.Opens) (basisSection L V) d :=
  Filter.eventually_atTop.mpr ⟨1, fun d hd => basisSection_trivializesPower L V d hd⟩

/-- At a member `V` of the trivializing basis, `Proj.map` of the comparison `ψ : 𝒜(V) ⟶ ℬ(V)`
attached to the chosen trivializing section is an isomorphism. -/
instance isIso_projMap_basisSection (V : trivializingOpens L) :
    IsIso (AlgebraicGeometry.Proj.map (psiSectionAt L 𝒜 V (basisSection L V))
      (irrelevant_le_map_psiSectionAt L 𝒜 (basisSection_trivializesPower L V))) :=
  isIso_projMap_psiSectionAt L 𝒜 (basisSection_trivializesPower L V)

/-- **The identification of twists over a member of the trivializing basis**: the restriction of
`𝒪_{Proj 𝒜(V)}(n)` along `Proj ℬ(V) ≅ Proj 𝒜(V)` is `𝒪_{Proj ℬ(V)}(n)`. -/
def absTwistIso (V : trivializingOpens L) (n : ℤ) :
    (Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).obj
        (twistingSheaf (𝒜.grading (V : S.Opens)) n) ≅
      twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) n :=
  ProjTwistCompare.restrictTwistIso (𝒜.grading (V : S.Opens)) ((twist 𝒜 L).grading (V : S.Opens))
    (psiSectionAt L 𝒜 V (basisSection L V))
    (irrelevant_le_map_psiSectionAt L 𝒜 (basisSection_trivializesPower L V))
    (mapDomain_psiSectionAt_eq_top' L 𝒜 (basisSection_trivializesPower L V))
    (isIso_twistMap_psiSectionAt L 𝒜 (basisSection_eventually L V)) n

/-- `absTwistIso` is multiplicative. -/
theorem absTwistIso_mul (V : trivializingOpens L) (i j : ℤ)
    (W : (AlgebraicGeometry.Proj ((twist 𝒜 L).grading (V : S.Opens))).Opens)
    (a : ((Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).obj
      (twistingSheaf (𝒜.grading (V : S.Opens)) i)).val.obj (op W))
    (b : ((Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).obj
      (twistingSheaf (𝒜.grading (V : S.Opens)) j)).val.obj (op W)) :
    (absTwistIso L 𝒜 V (i + j)).hom.val.app (op W)
        (absoluteTwistProduct (𝒜.grading (V : S.Opens)) i j (basisComparison L 𝒜 V ''ᵁ W) a b) =
      absoluteTwistProduct ((twist 𝒜 L).grading (V : S.Opens)) i j W
        ((absTwistIso L 𝒜 V i).hom.val.app (op W) a)
        ((absTwistIso L 𝒜 V j).hom.val.app (op W) b) :=
  ProjTwistCompare.restrictTwistIso_mul _ _ _ _ _ _ i j W a b

/-- `absTwistIso` carries the homogeneous section of `a` to that of its image under the
comparison `ψ : 𝒜(V) ⟶ ℬ(V)`. -/
theorem isDegCompat_absTwistIso (V : trivializingOpens L) :
    IsDegCompat L 𝒜 V (absTwistIso L 𝒜 V) := by
  intro k a
  refine (ProjTwistCompare.restrictTwistIso_degreeSection _ _ _ _ _ _ k a ⊤).trans ?_
  refine (PresheafOfModules.map_eq_map _ _ (𝟙 _) _).trans ?_
  exact congr($((twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) (k : ℤ)).val.presheaf.map_id
    (op ⊤)) _)

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
