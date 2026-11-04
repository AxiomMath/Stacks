module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseThreeMorphism
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.TwistingInput
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwoProof
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUnit
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.TripleUnique

/-!
# Stacks Tag 01O9

The whole statement of [Stacks, Tag 01O9] in one declaration, `tag01O9`.

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `π : Proj_S(𝒜) ⟶ S` its relative
homogeneous spectrum (`…RelativeProjBridge.relativeProj`), `f : X ⟶ S` a morphism, `ℒ` an
invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_{d} ℒ^{⊗ d}` a homomorphism of graded
`𝒪_X`-algebras (`…RelativeProjQcohSheaf.Twisting f 𝒜 1 ℒ`). Write `P` for the datum of
[Stacks, Tag 01O8] it gives (`toGradedPowerMap ψ`). The objects of the tag are:

* `U(ψ)`: `P.coveringOpen`;
* `r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)`: `P.globalMorphism (relativeProj A)`;
* `θ : r^*(⨁_{d} 𝒪(d)) ⟶ ⨁_{d} ℒ^{⊗ d}|_{U(ψ)}`: `P.theta`, a homomorphism of `ℤ`-graded algebras
  whose components in degrees `d ≥ 0` form the map of graded algebras of the source
  (`GradedNonnegHom.ofHom P.theta`).

The triples `(U', r', θ')` among which the source characterizes `(U(ψ), r_{ℒ,ψ}, θ)` are
`Triple A ℒ`, with `θ'` graded in degrees `d ≥ 0` only, and properties (1), (2), (3) for them are
`Triple.IsClauseOne`, `Triple.IsClauseTwo`, `Triple.IsClauseThree`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S X : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : X ⟶ S}
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (ψ : Twisting f (situationAlgebra A) 1 L)

/-- **[Stacks, Tag 01O9].** For `ψ : f^*𝒜 ⟶ ⨁_{d} ℒ^{⊗ d}` with `ℒ` invertible, put
`P = toGradedPowerMap ψ`, `U(ψ) = P.coveringOpen`, `r = P.globalMorphism (relativeProj A)` and
`θ = P.theta`. Then:

1. `r` is a morphism over `S`: `r ≫ π = (U(ψ) ⊆ X) ≫ f`;
2. `θ` preserves the unit, and its components in degrees `d, e ≥ 0` are multiplicative, so that
   they form a map of graded algebras `r^*(⨁_{d ≥ 0} 𝒪(d)) ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}|_{U(ψ)}`;
3. **property (1)**: for every open `V ⊆ S`, `d ≥ 0` and `a ∈ 𝒜_d(V)`, `θ` carries the pullback
   along `r` of the section `ψ(a)` of `𝒪(d)` over `π^{-1}(V)` to `ψ(a)` restricted to
   `f^{-1}(V) ∩ U(ψ) = r^{-1}(π^{-1}(V))`;
4. **property (2)**: for every `d ≥ 1` and every open `W ⊆ X` on which
   `ψ_d : f^*𝒜_d|_W ⟶ ℒ^{⊗ d}|_W` is surjective, `W ⊆ U(ψ)` and `r|_W` is the morphism
   `W ⟶ Proj_S(𝒜)` which the representation of the functor of quadruples by `Proj_S(𝒜)` attaches
   to `(d, f|_W, ℒ^{⊗ d}|_W, ψ|_W)`;
5. **property (3)**, for the open and the morphism: for every affine open `V ⊆ S`, with
   `ψ' : 𝒜(V) ⟶ Γ_*(f^{-1}(V), ℒ)` the induced map, `U(ψ') = U(ψ) ∩ f^{-1}(V)` and `r`
   restricted along `U(ψ') ⟶ U(ψ)` is `i_V ∘ r_{ℒ, ψ'}`; and any morphism `U(ψ) ⟶ Proj_S(𝒜)` with
   that restriction property over every affine `V` is `r`;
6. the triple `(U(ψ), r, θ)` (with `θ` in degrees `d ≥ 0`) is `Triple.canonical P`, and it has
   properties (1), (2) and (3), property (3) including that `θ` restricted along
   `U(ψ') ⟶ U(ψ)` is the `θ'` of the induced map, read through `i_V`;
7. **the characterization**: every triple `(U', r', θ')` with properties (1), (2) and (3) is
   `(U(ψ), r, θ)`. -/
@[stacks 01O9 "the open U(psi), the morphism r_{L,psi} : U(psi) -> Proj_S(A) over S and the unital \
map of graded algebras theta : r^*(sum_d O(d)) -> sum_d L^d|_{U(psi)}; properties (1), (2) and (3) \
for them; and every triple (U', r', theta') with properties (1), (2) and (3) is \
(U(psi), r_{L,psi}, theta)"]
theorem tag01O9 :
    (toGradedPowerMap ψ).globalMorphism (relativeProj A) ≫ (relativeProj A).toBase
        = (toGradedPowerMap ψ).coveringOpen.ι ≫ f
      ∧ SheafOfModules.sectionsMap (((toGradedPowerMap ψ).theta).app 0)
          (Stacks.Conormal.gradedPullback ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
            (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra).one
        = (Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn L
            (toGradedPowerMap ψ).coveringOpen).one
      ∧ (∀ (d e : ℕ) (U : (toGradedPowerMap ψ).coveringOpen.toScheme.Opens)
          (x : ((Stacks.Conormal.gradedPullback
            ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
            (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra).piece (d : ℤ)).val.obj (op U))
          (y : ((Stacks.Conormal.gradedPullback
            ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
            (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra).piece (e : ℤ)).val.obj (op U)),
          (((toGradedPowerMap ψ).theta.app ((d : ℤ) + (e : ℤ))).val.app (op U)
              (((Stacks.Conormal.gradedPullback
                ((toGradedPowerMap ψ).globalMorphism (relativeProj A))
                (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra).mul d e).app (op U) x y))
            = ((Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn L
                (toGradedPowerMap ψ).coveringOpen).mul d e).app (op U)
                (((toGradedPowerMap ψ).theta.app d).val.app (op U) x)
                (((toGradedPowerMap ψ).theta.app e).val.app (op U) y))
      ∧ (∀ (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)),
          ((tensorPowerModule X L (d : ℤ)).restrict
            (toGradedPowerMap ψ).coveringOpen.ι).presheaf.map
              (eqToHom ((toGradedPowerMap ψ).toBase_preimage_eq V)).op
              (((toGradedPowerMap ψ).theta.app d).val.app
                (op ((toGradedPowerMap ψ).globalMorphism (relativeProj A) ⁻¹ᵁ
                  ((relativeProj A).toBase ⁻¹ᵁ V)))
                (Stacks.RingedSpace.pullbackUnit
                  ((toGradedPowerMap ψ).globalMorphism (relativeProj A)).toLRSHom.toShHom
                  ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece (d : ℤ))
                  (op ((relativeProj A).toBase ⁻¹ᵁ V))
                  (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ d).app V a)))
            = (tensorPowerModule X L (d : ℤ)).presheaf.map
                (homOfLE ((toGradedPowerMap ψ).coveringOpen.ι.image_preimage_le (f ⁻¹ᵁ V))).op
                ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L d).hom.app (f ⁻¹ᵁ V)
                  (valueSec ψ d V a)))
      ∧ (∀ {k : ℕ} (hk : 0 < k) (W : X.Opens) [Epi ((ψ.pullback W.ι).app (k : ℤ))],
          ∃ h : W ≤ (toGradedPowerMap ψ).coveringOpen,
            X.homOfLE h ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A)
              = F.classifyingMorphism A (F.mk (W.ι ≫ f) (by exact_mod_cast hk)
                  (restrictQuadruple ψ W k)))
      ∧ (∀ V : S.affineOpens,
          (f ⁻¹ᵁ V.1).ι ''ᵁ ((toGradedPowerMap ψ).affineDatum V.1).coveringOpen
              = (toGradedPowerMap ψ).coveringOpen ⊓ f ⁻¹ᵁ V.1
            ∧ ∀ j : (((toGradedPowerMap ψ).affineDatum V.1).coveringOpen).toScheme ⟶
                (toGradedPowerMap ψ).coveringOpen.toScheme,
              j ≫ (toGradedPowerMap ψ).coveringOpen.ι
                  = (((toGradedPowerMap ψ).affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι →
                j ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A)
                  = ((toGradedPowerMap ψ).affineDatum V.1).glued ≫ (relativeProj A).chart V.1 V.2)
      ∧ (∀ R : (toGradedPowerMap ψ).coveringOpen.toScheme ⟶ (relativeProj A).scheme,
          (∀ V : S.affineOpens,
            ∀ j : (((toGradedPowerMap ψ).affineDatum V.1).coveringOpen).toScheme ⟶
                (toGradedPowerMap ψ).coveringOpen.toScheme,
              j ≫ (toGradedPowerMap ψ).coveringOpen.ι
                  = (((toGradedPowerMap ψ).affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι →
                j ≫ R = ((toGradedPowerMap ψ).affineDatum V.1).glued
                  ≫ (relativeProj A).chart V.1 V.2) →
          R = (toGradedPowerMap ψ).globalMorphism (relativeProj A))
      ∧ Triple.canonical (toGradedPowerMap ψ)
          = ⟨(toGradedPowerMap ψ).coveringOpen,
              (toGradedPowerMap ψ).globalMorphism (relativeProj A),
              GradedNonnegHom.ofHom (toGradedPowerMap ψ).theta⟩
      ∧ Triple.IsTriple ψ (Triple.canonical (toGradedPowerMap ψ))
      ∧ (∀ t : Triple A L, Triple.IsTriple ψ t → t = Triple.canonical (toGradedPowerMap ψ)) :=
  ⟨(toGradedPowerMap ψ).globalMorphism_comp_toBase (relativeProj A),
    (toGradedPowerMap ψ).theta_map_one,
    fun d e U x y => (toGradedPowerMap ψ).theta.map_mul d e (op U) x y,
    fun V d a => (toGradedPowerMap ψ).theta_clauseOne V d a |>.trans
      (by rw [toGradedPowerMap_value]; rfl),
    fun hk W _ => clauseTwo ψ hk W,
    fun V => ⟨(toGradedPowerMap ψ).image_coveringOpen_affineDatum_eq V.2,
      (toGradedPowerMap ψ).comp_globalMorphism_eq (relativeProj A) V⟩,
    fun _ hR => (toGradedPowerMap ψ).eq_globalMorphism_of_clauseThree (relativeProj A) fun V =>
      hR V _ ((toGradedPowerMap ψ).affineDatumInclusion_ι V),
    rfl, Triple.isTriple_canonical ψ, fun _ h => Triple.eq_canonical h⟩

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
