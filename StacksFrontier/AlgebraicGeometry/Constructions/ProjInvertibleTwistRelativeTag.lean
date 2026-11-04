module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeCanonicalChart
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeClauseTwo
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeThetaUnique

/-!
# Tag 02NC: the relative homogeneous spectrum of a twist by an invertible module

Let `S` be a scheme, `𝒜 = ⨁_{d ≥ 0} 𝒜_d` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an invertible
`𝒪_S`-module and `ℬ = ⨁_{d ≥ 0} 𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}` (Tag 02NB), with
`π : P = Proj_S(𝒜) ⟶ S` and `π' : P' = Proj_S(ℬ) ⟶ S`. This file states Tag 02NC as one theorem
about the canonical isomorphism `g : P ⟶ P'` over `S`
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwistHom`) and the isomorphism of
`ℤ`-graded algebras `θ : g^*(⨁_n 𝒪_{P'}(n)) ≅ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistTheta`), with components
`θ_n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistThetaIso`).

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwist_tag`: `g` is an isomorphism over
  `S`, characterized by its restrictions to the trivializing charts, and `θ` is an isomorphism of
  graded algebras, characterized by the squares on sections of clause (2).

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist
open Stacks.AlgebraicGeometry.AffineOpenTensorSections
open Stacks.AlgebraicGeometry.RelativeTwistSections
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an invertible
`𝒪_S`-module and `ℬ = ⨁_d 𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}`, with `π : P = Proj_S(𝒜) ⟶ S` and
`π' : P' = Proj_S(ℬ) ⟶ S`. The canonical morphism `g = relativeTwistHom L 𝒜 : P ⟶ P'`:

* is an isomorphism, and a morphism over `S`: `π' ∘ g = π`;
* is canonical, with nothing chosen: `g⁻¹` restricts, over every affine open `V` of `S` and every
  section `x` of `ℒ` over `V` whose powers trivialize the powers of `ℒ` there, to the morphism of
  homogeneous spectra induced by the comparison `a ↦ a ⊗ x^d`, and it is the only isomorphism
  `P' ≅ P` over `S` doing so;
* (1) carries isomorphisms `θ_n = twistThetaIso L 𝒜 n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` for
  every `n : ℤ`, which fit together into the isomorphism of sheaves of `ℤ`-graded algebras
  `θ = twistTheta L 𝒜 : g^*(⨁_n 𝒪_{P'}(n)) ≅ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`, its component in degree
  `n` being `θ_n`; `θ` preserves the unit;
* (2) for every open `V ⊆ S` and every `n`, the square of the source commutes: the image under
  `θ_n` of the section of `𝒪_{P'}(n)` over `π'^{-1}V` given by `a ⊗ l ∈ ℬ_n(V)`
  (`a ∈ 𝒜_n(V)`, `l ∈ ℒ^{⊗ n}(V)`) is `ψ(a) ⊗ π^*l` over `π^{-1}V`;
* `θ` is canonical, with nothing chosen: it is the only homomorphism of sheaves of graded algebras
  `g^*(⨁_n 𝒪_{P'}(n)) ⟶ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` making the squares of (2) commute. -/
@[stacks 02NC "the canonical isomorphism g from Proj_S(A) to Proj_S(B) over S, with (1) the \
isomorphisms theta_n from g^*O_P'(n) to O_P(n) tensor pi^*L^n fitting together into an \
isomorphism of Z-graded algebras theta, and (2) the commuting diagrams on sections over every open \
V of S, theta being the unique such map"]
theorem relativeTwist_tag :
    IsIso (relativeTwistHom L 𝒜 : (relativeProj 𝒜).scheme ⟶ (relativeProj (twist 𝒜 L)).scheme) ∧
      relativeTwistHom L 𝒜 ≫ (relativeProj (twist 𝒜 L)).toBase = (relativeProj 𝒜).toBase ∧
      (relativeTwistIso L 𝒜).inv = relativeTwistHom L 𝒜 ∧
      (∀ (V : S.Opens) (hV : IsAffineOpen V) (x : (tp L 1).val.obj (op V))
          (hx : ∀ d : ℕ, 0 < d → TrivializesPower L V x d),
          (relativeProj (twist 𝒜 L)).chart V hV ≫ (relativeTwistIso L 𝒜).hom =
            projMap_psiSectionAt L 𝒜 hx ≫ (relativeProj 𝒜).chart V hV) ∧
      (∀ e : (relativeProj (twist 𝒜 L)).scheme ≅ (relativeProj 𝒜).scheme,
          (∀ (V : S.Opens) (hV : IsAffineOpen V) (x : (tp L 1).val.obj (op V))
              (hx : ∀ d : ℕ, 0 < d → TrivializesPower L V x d),
              (relativeProj (twist 𝒜 L)).chart V hV ≫ e.hom =
                projMap_psiSectionAt L 𝒜 hx ≫ (relativeProj 𝒜).chart V hV) →
            e.hom ≫ (relativeProj 𝒜).toBase = (relativeProj (twist 𝒜 L)).toBase →
            e = relativeTwistIso L 𝒜) ∧
      (∀ n : ℤ, (targetAlgebra L 𝒜).piece n =
        tensorMod (Tag07ZGTwist.relativeTwist 𝒜 n)
          ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n))) ∧
      (∀ n : ℤ, (twistTheta L 𝒜 :
          Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
              (Tag07ZGTwist.twistAlgebra (twist 𝒜 L)) ≅ targetAlgebra L 𝒜).hom.app n =
        (twistThetaIso L 𝒜 n :
          (Scheme.Modules.pullback (relativeTwistHom L 𝒜)).obj
              (Tag07ZGTwist.relativeTwist (twist 𝒜 L) n) ≅
            tensorMod (Tag07ZGTwist.relativeTwist 𝒜 n)
              ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n))).hom) ∧
      (∀ W : (relativeProj 𝒜).scheme.Opensᵒᵖ,
        ((twistTheta L 𝒜).hom.app 0).val.app W
            ((Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
              (Tag07ZGTwist.twistAlgebra (twist 𝒜 L))).one.eval W) =
          (targetAlgebra L 𝒜).one.eval W) ∧
      (∀ (n : ℕ) (V : S.Opens),
        (∀ (a : Γ(𝒜.piece (n : ℤ), V)) (l : Γ(tpMod L (n : ℤ), V)),
          thetaSections (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
              (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
              (twistThetaIso L 𝒜 n).hom V
              (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ n).val.app (op V)
                (gammaTmul (𝒜.piece (n : ℤ)) (tpMod L (n : ℤ)) V a l)) =
            gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 n)
              ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n))
              ((relativeProj 𝒜).toBase ⁻¹ᵁ V)
              (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ n).val.app (op V) a)
              (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj 𝒜).toBase).unit.app
                (tpMod L n)).val.app (op V) l)) ∧
        ∀ z : Γ(𝒜.piece (n : ℤ), V) ⊗[Γ(S, V)] Γ(tpMod L (n : ℤ), V),
          thetaSections (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
              (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
              (twistThetaIso L 𝒜 n).hom V
              (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ n).val.app (op V)
                (gammaTensorMap (𝒜.piece (n : ℤ)) (tpMod L (n : ℤ)) V z)) =
            lowerRoute (relativeProj 𝒜).toBase ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ n)
              V z) ∧
      (∀ α : Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
            (Tag07ZGTwist.twistAlgebra (twist 𝒜 L)) ⟶ targetAlgebra L 𝒜,
          (∀ (n : ℕ) (V : S.Opens) (a : Γ(𝒜.piece (n : ℤ), V)) (l : Γ(tpMod L (n : ℤ), V)),
            thetaSections (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
                (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜) (α.app (n : ℤ)) V
                (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ n).val.app (op V)
                  (gammaTmul (𝒜.piece (n : ℤ)) (tpMod L (n : ℤ)) V a l)) =
              gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 n)
                ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n))
                ((relativeProj 𝒜).toBase ⁻¹ᵁ V)
                (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ n).val.app (op V) a)
                (((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj 𝒜).toBase).unit.app
                  (tpMod L n)).val.app (op V) l)) →
          α = (twistTheta L 𝒜).hom) :=
  (fun hchart => ⟨isIso_relativeTwistHom L 𝒜, relativeTwistHom_comp_toBase L 𝒜, rfl, hchart,
    fun _ he hb => (existsUnique_relativeTwistIso_trivializesPower L 𝒜).unique ⟨he, hb⟩
      ⟨hchart, relativeTwistIso_hom_comp_toBase L 𝒜⟩, targetAlgebra_piece L 𝒜,
    twistTheta_hom_app L 𝒜, twistTheta_hom_app_zero_one L 𝒜,
    fun n V => twistTheta_clauseTwo L 𝒜 V n,
    fun _ hα => eq_twistTheta_hom_of_squareAt L 𝒜 fun n V => hα n V⟩)
    fun _ hV _ hx => chart_comp_relativeTwistIso_hom_of_trivializesPower L 𝒜 hV hx

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
