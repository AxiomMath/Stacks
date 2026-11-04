module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceModule
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaModuleChange

/-!
# The map `θ` of Stacks 0D2Z for an algebraic space `X`, on the scheme points of `U(ψ)`

Let `f : X ⟶ Y` be a morphism of algebraic spaces towards the algebraic space `Y` of
Situation 0849, `ℒ` an invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of
graded algebras, given, as in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjInvertibleSpace.lean`, by their restrictions to
the scheme points of `X`
(`AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction`; for a pair
`(ℒ, ψ)` on the small étale site of `X` this is `…InvertibleTwistingRestriction.ofUnitalHom`). At a
scheme point `x : T ⟶ X` the restriction `x^*ψ` has the map of graded algebras
`θ_x : r_x^*(⨁_d 𝒪(d)) ⟶ ⨁_d (x^*ℒ)^{⊗ d}|_{U(x^*ψ)}` of [Stacks, Tag 01O9]; it is the restriction
of `θ` to the scheme point `x`, the source's proof reducing everything to Tag 01O9 on the scheme
points.

This file proves that these restrictions are compatible: **for a morphism `τ : T' ⟶ T` of test
schemes, `θ_{x ∘ τ}` is the pullback of `θ_x` along `τ`**, read through the canonical
identifications of the sources and the targets.  This is the compatibility of the restrictions of
`θ` that the description of `θ` by its restrictions to the scheme points requires, and the last
assertion of clause (3) of the tag (`θ'` is the pullback of `θ`) for the square with
`Y' = X' = T'` and `f' = 𝟙_{T'}`.  Clause (3) for a square with a non-trivial `f' : X' ⟶ Y'` is
`AlgebraicGeometry.Space.RelativeProjSituation.invertibleTheta_baseChange_square`, at a scheme
point of the base.

The restriction `(x ∘ τ)^*ψ` is the pullback `τ^*(x^*ψ)` (the square twisting of the restriction
datum of Stacks 084A) read over `𝟙_{T'}` and transported along the identification
`τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`; accordingly `θ_{x ∘ τ}` is computed from `θ_x` by clause (3) of the
scheme case (`…RelativeProjSituation.invertibleTheta_baseChange_square`), the invariance of `θ`
under rereading the base morphism along an equality, and the invariance of `θ` under an
isomorphism of the invertible module (`…RelativeProjInvertibleMorphism.theta_congrModule`).

## Main results

* `…RelativeProjInvertibleMorphism.theta_eq_of_eq_congrBase_congrModule`: `θ` of a twisting which
  is another twisting read over an equal base morphism and transported along an isomorphism of
  the invertible modules.
* `…InvertibleTwistingRestriction.theta_map`: **`θ_{x ∘ τ}` is `θ_{τ^*(x^*ψ)}` transported along
  `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`**.
* `…InvertibleTwistingRestriction.theta_map_eq_pullback`: **`θ_{x ∘ τ}` is the pullback of `θ_x`
  along `τ`**, through canonical isomorphisms of graded algebras.
* `…InvertibleTwistingRestriction.theta_map_eq_pullback_ofUnitalHom`: the same for a pair `(ℒ, ψ)`
  on the small étale site of `X`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)

universe u m

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

/-! ### `θ` of a twisting reread over an equal base morphism and transported along `ℒ ≅ ℒ'` -/

section CongrBaseCongrModule

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {g g' : T ⟶ S} (h : g = g')
  {L L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L] [Stacks.Ample.IsInvertibleModule T L']
  (ψ : Twisting g (situationAlgebra A) 1 L) (e : L ≅ L')
  (χ : Twisting g' (situationAlgebra A) 1 L') (hχ : χ = (ψ.congrBase h).congrModule e)

include hχ in
/-- `U(χ) ⊆ U(ψ)` for `χ` the twisting `ψ` reread over `g = g'` and transported along `e`. -/
theorem coveringOpen_le_of_eq_congrBase_congrModule :
    (toGradedPowerMap χ).coveringOpen ≤ (toGradedPowerMap ψ).coveringOpen := by
  subst hχ
  subst h
  exact coveringOpen_congrModule_le ψ e

/-- `j ≫ r_ψ = r_χ` for `χ` the twisting `ψ` reread over `g = g'` and transported along `e`, with
`j : U(χ) ⟶ U(ψ)` the inclusion. -/
theorem homOfLE_globalMorphism_of_eq_congrBase_congrModule :
    T.homOfLE (coveringOpen_le_of_eq_congrBase_congrModule h ψ e χ hχ) ≫
        (toGradedPowerMap ψ).globalMorphism (relativeProj A) =
      (toGradedPowerMap χ).globalMorphism (relativeProj A) := by
  subst hχ
  subst h
  exact homOfLE_globalMorphism_congrModule ψ e

/-- **`θ` of a twisting `χ` which is `ψ` reread over an equal base morphism and transported along
`e : ℒ ≅ ℒ'`** is `θ_ψ` read along `j : U(χ) ⟶ U(ψ)` and `j ≫ r_ψ = r_χ`, followed by the
isomorphism of Laurent algebras induced by `e`. -/
theorem theta_eq_of_eq_congrBase_congrModule :
    (toGradedPowerMap χ).theta =
      (toGradedPowerMap ψ).thetaTransportHom e
        (coveringOpen_le_of_eq_congrBase_congrModule h ψ e χ hχ)
        (homOfLE_globalMorphism_of_eq_congrBase_congrModule h ψ e χ hχ) := by
  subst hχ
  subst h
  exact theta_congrModule ψ e

end CongrBaseCongrModule

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

variable {s : RelativeProjSituation.{u, m}}
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f)
  {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X)

/-- `U((x ∘ τ)^*ψ) ⊆ U(τ^*(x^*ψ))`: the two opens agree. -/
theorem coveringOpen_twisting_map_le :
    (toGradedPowerMap (R.twisting T' (yoneda.map τ ≫ x))).coveringOpen ≤
      (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting T x)
        ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ (yoneda_map_id_comp_assoc s f τ x))).coveringOpen :=
  coveringOpen_le_of_eq_congrBase_congrModule (CategoryTheory.Functor.map_id _ T') _
    (R.lineIso τ x) _ (R.twisting_map τ x)

/-- **`θ_{x ∘ τ}` is `θ_{τ^*(x^*ψ)}` transported along `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`**: the map `θ` of
Tag 01O9 for the restriction `(x ∘ τ)^*ψ` is the map for the pullback `τ^*(x^*ψ)` of the
restriction `x^*ψ` (the square twisting of Stacks 084A), read along the equal opens and followed
by the isomorphism of Laurent algebras induced by `R.lineIso τ x`. -/
theorem theta_map :
    (toGradedPowerMap (R.twisting T' (yoneda.map τ ≫ x))).theta =
      (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
          s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting T
            x)
          ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ (yoneda_map_id_comp_assoc s f τ x))).thetaTransportHom
        (R.lineIso τ x) (R.coveringOpen_twisting_map_le τ x)
        (homOfLE_globalMorphism_of_eq_congrBase_congrModule (CategoryTheory.Functor.map_id _ T') _
          (R.lineIso τ x) _ (R.twisting_map τ x)) :=
  theta_eq_of_eq_congrBase_congrModule (CategoryTheory.Functor.map_id _ T') _ (R.lineIso τ x) _
    (R.twisting_map τ x)

/-- **The restriction of `θ` to the scheme point `x ∘ τ` is the pullback along `τ` of its
restriction to `x`** (Stacks 0D2Z for an algebraic space `X`, on the scheme points of `U(ψ)`):
`θ_{x ∘ τ}` is `j^*θ_x` for the restriction `j : U((x ∘ τ)^*ψ) ⟶ U(x^*ψ)` of `τ`, read through the
identification of the sources (`…GradedAlgebraRestriction.squareThetaSourceIso`, then
`…GradedPowerMap.thetaTransportSourceIso`) and of the targets
(`…GradedAlgebraRestriction.squareThetaTargetIso`, then
`…GradedPowerMap.thetaTransportTargetIso` for `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`). -/
@[stacks 0D2Z "theta for X an algebraic space, on the scheme points of U(psi): for scheme points \
x : T -> X and x o tau, tau : T' -> T, the map theta_{x o tau} of Tag 01O9 for (x o tau)^*psi is \
the pullback along tau of theta_x, through the canonical isomorphisms of the sources \
r'^*((+)_d O(d)) and of the targets (+)_d ((x o tau)^*L)^d. This is the last assertion of \
clause (3) for the square with Y' = X' = T' and f' = id, that is, the compatibility of the \
restrictions of theta between scheme points"]
theorem theta_map_eq_pullback :
    (toGradedPowerMap (R.twisting T' (yoneda.map τ ≫ x))).theta =
      ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
          s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting T
            x)
          ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
          (yoneda_map_id_comp_assoc s f τ x))).thetaTransportSourceIso
        (R.coveringOpen_twisting_map_le τ x)
        (homOfLE_globalMorphism_of_eq_congrBase_congrModule (CategoryTheory.Functor.map_id _ T') _
          (R.lineIso τ x) _ (R.twisting_map τ x))).inv ≫
        pullbackGradedAlgebraMap
          (Scheme.homOfLE
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T')
            (R.coveringOpen_twisting_map_le τ x)).toLRSHom.toShHom
          ((s.quadrupleRestriction.squareThetaSourceIso s.shrink.contains_relativeProj_pointAlgebra
              s.shrink.space.property.isSheaf (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
              (yoneda_map_id_comp_assoc s f τ x)).inv ≫
            pullbackGradedAlgebraMap
              (Scheme.Hom.resLE
                ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ)
                (toGradedPowerMap (R.twisting T x)).coveringOpen
                (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
                  s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
                  (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
                  (yoneda_map_id_comp_assoc s f τ x))).coveringOpen
                (s.quadrupleRestriction.coveringOpen_squareTwisting
                  s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
                  (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
                  (yoneda_map_id_comp_assoc s f τ x)).le).toLRSHom.toShHom
              (toGradedPowerMap (R.twisting T x)).theta ≫
            (s.quadrupleRestriction.squareThetaTargetIso s.shrink.contains_relativeProj_pointAlgebra
              s.shrink.space.property.isSheaf (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
              (yoneda_map_id_comp_assoc s f τ x)).hom) ≫
        ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
          s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting T
            x)
          ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
          (yoneda_map_id_comp_assoc s f τ x))).thetaTransportTargetIso
          (R.lineIso τ x) (R.coveringOpen_twisting_map_le τ x)).hom := by
  refine (R.theta_map τ x).trans ?_
  unfold GradedPowerMap.thetaTransportHom
  rw [s.quadrupleRestriction.theta_baseChange_square s.shrink.contains_relativeProj_pointAlgebra
    s.shrink.space.property.isSheaf (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
    (yoneda_map_id_comp_assoc s f τ x)]
  rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction


namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)

/-- **The restriction of `θ` to the scheme point `x ∘ τ` is the pullback along `τ` of its
restriction to `x`**, for a pair `(ℒ, ψ)` on the small étale site of the algebraic space `X`:
`theta_map_eq_pullback` for the restriction datum `ofUnitalHom s f L ψ` of `(ℒ, ψ)`. -/
@[stacks 0D2Z "theta for an algebraic space X with an invertible O_X-module L on its small etale \
site and a homomorphism of graded algebras psi : f^*A -> (+)_n L^n, on the scheme points of \
U(psi): theta_{x o tau} is the pullback along tau of theta_x, through the canonical isomorphisms \
of the sources and of the targets"]
theorem theta_map_eq_pullback_ofUnitalHom :
    (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting T' (yoneda.map τ ≫ x))).theta =
      ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
          s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
          ((ofUnitalHom s f L ψ).twisting T x)
          ((yoneda.map τ ≫ x) ≫ f.hom) (𝟙 T') τ
          (yoneda_map_id_comp_assoc s f.hom τ x))).thetaTransportSourceIso
        ((ofUnitalHom s f L ψ).coveringOpen_twisting_map_le τ x)
        (homOfLE_globalMorphism_of_eq_congrBase_congrModule (CategoryTheory.Functor.map_id _ T') _
          ((ofUnitalHom s f L ψ).lineIso τ x) _ ((ofUnitalHom s f L ψ).twisting_map τ x))).inv ≫
        pullbackGradedAlgebraMap
          (Scheme.homOfLE
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).obj T')
            ((ofUnitalHom s f L ψ).coveringOpen_twisting_map_le τ x)).toLRSHom.toShHom
          ((s.quadrupleRestriction.squareThetaSourceIso s.shrink.contains_relativeProj_pointAlgebra
              s.shrink.space.property.isSheaf ((ofUnitalHom s f L ψ).twisting T x)
              ((yoneda.map τ ≫ x) ≫ f.hom) (𝟙 T') τ
              (yoneda_map_id_comp_assoc s f.hom τ x)).inv ≫
            pullbackGradedAlgebraMap
              (Scheme.Hom.resLE
                ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ)
                (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting T x)).coveringOpen
                (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
                  s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
                  ((ofUnitalHom s f L ψ).twisting T x) ((yoneda.map τ ≫ x) ≫ f.hom) (𝟙 T') τ
                  (yoneda_map_id_comp_assoc s f.hom τ x))).coveringOpen
                (s.quadrupleRestriction.coveringOpen_squareTwisting
                  s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
                  ((ofUnitalHom s f L ψ).twisting T x) ((yoneda.map τ ≫ x) ≫ f.hom) (𝟙 T') τ
                  (yoneda_map_id_comp_assoc s f.hom τ x)).le).toLRSHom.toShHom
              (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting T x)).theta ≫
            (s.quadrupleRestriction.squareThetaTargetIso s.shrink.contains_relativeProj_pointAlgebra
              s.shrink.space.property.isSheaf ((ofUnitalHom s f L ψ).twisting T x)
              ((yoneda.map τ ≫ x) ≫ f.hom) (𝟙 T') τ
              (yoneda_map_id_comp_assoc s f.hom τ x)).hom) ≫
        ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
          s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
          ((ofUnitalHom s f L ψ).twisting T x)
          ((yoneda.map τ ≫ x) ≫ f.hom) (𝟙 T') τ
          (yoneda_map_id_comp_assoc s f.hom τ x))).thetaTransportTargetIso
          ((ofUnitalHom s f L ψ).lineIso τ x)
          ((ofUnitalHom s f L ψ).coveringOpen_twisting_map_le τ x)).hom :=
  (ofUnitalHom s f L ψ).theta_map_eq_pullback τ x

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
