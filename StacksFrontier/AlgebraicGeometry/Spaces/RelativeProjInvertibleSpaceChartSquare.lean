module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSchemeTarget

/-!
# The factors of the square of the scheme factor `θ` of the chart maps of Stacks 0D2Z

The chart map `χ_w : w^*(r^*𝒪(d)) ⟶ w^*(ℒ^{⊗ d}|_{U(ψ)})` at a scheme point `w` of `U(ψ)`
(`…InvertibleTwistingRestriction.chartMap`) is a composite of three factors, the middle one being
the module attached (Stacks 03DX (2)) to `θ` of [Stacks, Tag 01O9] read along the section `c_w`
(`…InvertibleTwistingRestriction.chartSchemeTheta`).  Its square along a morphism `τ : T' ⟶ T` of
test schemes is, through
`AlgebraicGeometry.Space.modulePullback_map_functor_map_comp_eq_of_square`, the square of the maps
of quasi-coherent modules on the schemes, and that square is
`AlgebraicGeometry.Space.quasicoherentPullbackMap_comp_eq_of_theta_eq_of_factors` applied to the
comparison `…InvertibleTwistingRestriction.theta_map_eq_pullback_ofUnitalHom` of `θ`, to the
factorisation `…InvertibleTwistingRestriction.map_comp_chartLift` of `τ` through the loci, and to
the coherences `AlgebraicGeometry.Space.source_square_coherence_of_squareChain` and
`AlgebraicGeometry.Space.chartScheme_target_coherence` of the identifications of the sources and
of the targets.

This file provides the written-out values of the identifications that those two coherences are
instantiated at: the degree-`d` components of the target identification `thetaTargetIsoOfEq` and
of the source identification `thetaTransportSourceIso` of Tag 01O9, the decomposition of the
inverse of the canonical identification of Stacks 01ZR (2) into its two factors, and the
identification of the comparison `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ` of a restriction datum coming from a
pair `(ℒ, ψ)` on the small étale site with the comparison `pointLineIso` of the restrictions of
`ℒ` itself, and the value of `ρ` the target coherence is instantiated at.

## Main results

* `…RelativeProjInvertibleMorphism.thetaTargetIsoOfEq_hom_app`: the degree-`d` component of
  `j^*(⨁_d ℒ^{⊗ d}|_{U(ψ)}) ≅ ⨁_d (q^*ℒ)^{⊗ d}|_{U(χ₂)}` for `χ₂` the pullback `q^*ψ` reread over
  an equal morphism to the base, written out as the restriction read as an inverse image, the
  pseudofunctoriality of the inverse image along `j ≫ ι = ι' ≫ q`, and the comparison of the
  integral tensor powers of [Stacks, Tag 01CU].  This is the value of `S₄` that
  `AlgebraicGeometry.Space.chartScheme_target_coherence` asks for.
* `…RelativeProjInvertibleMorphism.GradedPowerMap.thetaTransportSourceIso_inv_app`: the degree-`d`
  component of the inverse of `j^*r_P^*(⨁_d 𝒪(d)) ≅ r'^*(⨁_d 𝒪(d))`, written out as the transport
  along `j ≫ r_P = r'` followed by the inverse comparison of Stacks 03LU.  This is the leading
  factor of the source identification in
  `AlgebraicGeometry.Space.source_square_coherence_of_squareChain`.
* `AlgebraicGeometry.Space.inv_canHom_eq`: the inverse of the canonical identification
  `q^*(g^*F) ≅ π^*F` of Stacks 01ZR (2) is the inverse transport along `q ≫ g = π` followed by the
  inverse comparison of Stacks 03LU.
* `…InvertibleTwistingRestriction.lineIso_eq_pointLineIso`: the comparison `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`
  of the restriction datum of a pair `(ℒ, ψ)` on the small étale site is
  `AlgebraicGeometry.Space.pointLineIso`.
* `…InvertibleTwistingRestriction.pointLaurentPiecePullbackHom_hom_eq`: the comparison
  `τ^*((x^*ℒ)^{⊗ d}) ⟶ ((x ∘ τ)^*ℒ)^{⊗ d}` of
  `AlgebraicGeometry.Space.pointLaurentPiecePullbackHom` is the comparison of the integral tensor
  powers under pullback followed by the comparison induced by `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`, read in
  the vocabulary of the restriction datum.  This is the value of `ρ` that
  `AlgebraicGeometry.Space.chartScheme_target_coherence` asks for.

## Implementation notes

Two spellings of the restriction `x^*ℒ` meet in this file: `…InvertibleTwistingRestriction.line`,
whose scheme is spelled through `s.site`, and `AlgebraicGeometry.Space.pointLine`, whose scheme is
spelled through `s.shrink.site` (the two agree, but neither family of `IsInvertibleModule`
instances is found at the other's spelling, so each occurrence has to be written at the spelling
whose instances resolve).  Reconciling them is cheap *one factor at a time* and far over the
per-declaration budget *across a composition*: the kernel compares a `≫` by unfolding the
composition of the two categories of modules, which is what makes the cost superlinear in the
number of factors.  Accordingly:

* `…InvertibleTwistingRestriction.lineIso_eq_pointLineIso` is proved by `CategoryTheory.Iso.ext`,
  not by `rfl`: the two isomorphisms are the same after one projection of the structure instance
  `…InvertibleTwistingRestriction.ofUnitalHom`, but comparing them as isomorphisms exhausts the
  per-declaration budget, while comparing their underlying morphisms does not.
* `AlgebraicGeometry.Space.pointLaurentPiecePullbackHom_hom` unfolds
  `AlgebraicGeometry.Space.pointLaurentPiecePullbackHom` with *every* occurrence at the `pointLine`
  spelling, so that it is `rfl` with nothing to reconcile.
* `…InvertibleTwistingRestriction.pointLaurentPiecePullbackHom_hom_eq` then moves to the
  `…InvertibleTwistingRestriction.line` spelling through `congrArg₂ (· ≫ ·)`, which hands the
  kernel the two factors separately.  Stated as a single `rfl` against
  `AlgebraicGeometry.Space.pointLaurentPiecePullbackHom`, or proved by one `congrArg` over the
  whole composite, it costs more than eight times the per-declaration budget — and that holds for
  both spellings of the scheme of the test objects, so the cost is the composition and not the
  spelling.
* `…LaurentCongr.congrIso_hom_congr` is what carries `lineIso_eq_pointLineIso` into the comparison
  of tensor powers; its two modules are fixed, so no spelling is reconciled inside the `congrArg`.

The same reconciliation is *not* yet affordable in the instance of
`AlgebraicGeometry.Space.chartScheme_target_coherence` that the square of
`…InvertibleTwistingRestriction.chartSchemeTheta` needs, and the obstruction has the same shape in
several places at once.  The scheme of the test objects reaches that coherence through `s.site`
(the generic square lemma reads it off the type of `τ`), while the data it is instantiated at —
`…GradedAlgebraRestriction.squareThetaTargetIso` and everything built from
`s.quadrupleRestriction` — reaches it through `s.shrink.site`; so each of `hS₄`, `hlam₀`, `hlam₁`
asks the kernel to reconcile the two spellings *inside* a composition of four to six factors, and
each of those exhausts the per-declaration budget on its own (removing one only moves the timeout
to the next).  Writing the coherence's conclusion out by hand as a statement is no better: the
hand-written chain re-does every reconciliation that the goal produced by the square lemma's
`refine` already carries, and does not fit even at eight times the budget.  What the shapes of
`chartScheme_target_coherence` and
`…RelativeProjInvertibleMorphism.squareChainIso_hom_app` suggest, and what is not done here, is to
restate the hypothesis-providing lemmas (`thetaTargetIsoOfEq_hom_app` above, and
`…GradedPowerMap.laurentOnSectionPieceIso_hom_eq`) with their factors as variables carrying their
values as equations, so that the match against the expected hypothesis is first order and each
reconciliation is isolated to a single factor.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open Stacks.AlgebraicGeometry.ProjChartIntPullbackMul (intPullIso)

universe u m

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

/-- **The comparison of the integral tensor powers induced by an isomorphism of invertible
modules depends only on that isomorphism**: equal isomorphisms `ℒ ≅ ℒ'` induce, in every integral
degree, the same comparison `ℒ^{⊗ d} ≅ ℒ'^{⊗ d}`.

The two modules are fixed, so that transporting a given equation of isomorphisms through
`congrArg` is type-correct with no comparison of the spellings of the modules; see the
implementation notes of this file. -/
theorem congrIso_hom_congr {T : Scheme.{u}} {L L' : T.Modules}
    [Stacks.Ample.IsInvertibleModule T L] [Stacks.Ample.IsInvertibleModule T L']
    {e e' : L ≅ L'} (he : e = e') (d : ℤ) :
    (congrIso e d).hom = (congrIso e' d).hom :=
  congrArg (fun z => (congrIso z d).hom) he

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

section PullbackOfEqApp

variable {S X W : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : X ⟶ S}
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (ψ : Twisting f (situationAlgebra A) 1 L) (q : W ⟶ X) {f₂ : W ⟶ S} (h : q ≫ f = f₂)
  {χ₂ : Twisting f₂ (situationAlgebra A) 1 ((pullbackFunctor (ringedSpaceHom q)).obj L)}
  (hχ : χ₂ = Twisting.congrBase h (ψ.pullback q))

/-- **The degree-`d` component of `thetaTargetIsoOfEq`, written out**: the restriction to `U(ψ)`
read as the inverse image along `ι`, the pseudofunctoriality of the inverse image along
`j ≫ ι_{U(ψ)} = ι_{U(χ₂)} ≫ q`, the comparison `q^*(ℒ^{⊗ d}) ≅ (q^*ℒ)^{⊗ d}` of the integral
tensor powers of [Stacks, Tag 01CU], and the restriction to `U(χ₂)` read back.

This is the shape in which `AlgebraicGeometry.Space.chartScheme_target_coherence` consumes the
identification of the targets. -/
theorem thetaTargetIsoOfEq_hom_app (d : ℤ) :
    (thetaTargetIsoOfEq ψ q h hχ).hom.app d =
      (Scheme.Modules.pullback (coveringOpenPullbackOfEq ψ q h hχ)).map
          ((Scheme.Modules.restrictFunctorIsoPullback (toGradedPowerMap ψ).coveringOpen.ι).hom.app
            (tensorPowerModule X L d)) ≫
        (Scheme.Modules.pullbackComp (coveringOpenPullbackOfEq ψ q h hχ)
            (toGradedPowerMap ψ).coveringOpen.ι).hom.app (tensorPowerModule X L d) ≫
        (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι q
            (coveringOpen_pullback_of_eq ψ q h hχ).le)).hom.app (tensorPowerModule X L d) ≫
        (Scheme.Modules.pullbackComp (toGradedPowerMap χ₂).coveringOpen.ι q).inv.app
            (tensorPowerModule X L d) ≫
        (Scheme.Modules.pullback (toGradedPowerMap χ₂).coveringOpen.ι).map
            (intPullIso q L d).hom ≫
        (Scheme.Modules.restrictFunctorIsoPullback
            (toGradedPowerMap χ₂).coveringOpen.ι).inv.app
          (tensorPowerModule W ((Scheme.Modules.pullback q).obj L) d) := by
  subst hχ
  subst h
  rfl

end PullbackOfEqApp

namespace GradedPowerMap

section TransportApp

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  (P : GradedPowerMap A f) {U₁ : T.Opens} (hU : U₁ ≤ P.coveringOpen)
  {r' : U₁.toScheme ⟶ (relativeProj A).scheme}
  (hr : T.homOfLE hU ≫ P.globalMorphism (relativeProj A) = r')

/-- **The degree-`d` component of the inverse of `thetaTransportSourceIso`, written out**: the
inverse transport along `j ≫ r_P = r'` followed by the inverse comparison of Stacks 03LU for the
inclusion `j : U₁ ⟶ U(P)` and `r_P`.

This is the leading factor of the source identification in
`AlgebraicGeometry.Space.source_square_coherence_of_squareChain`. -/
theorem thetaTransportSourceIso_inv_app (d : ℤ) :
    (P.thetaTransportSourceIso hU hr).inv.app d =
      (Scheme.Modules.pullbackCongr hr).inv.app (Otw A d) ≫
        (Scheme.Modules.pullbackComp (T.homOfLE hU)
          (P.globalMorphism (relativeProj A))).inv.app (Otw A d) :=
  rfl

end TransportApp

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace AlgebraicGeometry.Space

/-- **The inverse of the canonical identification of [Stacks, Tag 01ZR] (2)**: the inverse of
`q^*(g^*F) ≅ π^*F` along `q ≫ g = π` is the inverse transport along `q ≫ g = π` followed by the
inverse comparison of Stacks 03LU.  The form in which the inverse canonical identifications of
`AlgebraicGeometry.Space.canHom_squareChain_coherence` are read as the factors that
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.squareChainIso` is built from. -/
theorem inv_canHom_eq {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) (F : X.Modules) :
    inv (Stacks.AlgebraicGeometry.ModuleLimits.canHom q g pi hpi F) =
      (Scheme.Modules.pullbackCongr hpi).inv.app F ≫
        (Scheme.Modules.pullbackComp q g).inv.app F := by
  refine (IsIso.eq_inv_of_hom_inv_id ?_).symm
  show ((Scheme.Modules.pullbackComp q g).hom.app F ≫
      (Scheme.Modules.pullbackCongr hpi).hom.app F) ≫
    (Scheme.Modules.pullbackCongr hpi).inv.app F ≫
      (Scheme.Modules.pullbackComp q g).inv.app F = 𝟙 _
  rw [Category.assoc, ← Category.assoc ((Scheme.Modules.pullbackCongr hpi).hom.app F),
    Iso.hom_inv_id_app, Category.id_comp, Iso.hom_inv_id_app]

section PointLaurentPiecePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (L : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
  [hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedTopos B S hS X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O).property L]
  {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X.1)

/-- **The underlying morphism of the comparison `τ^*((x^*ℒ)^{⊗ d}) ⟶ ((x ∘ τ)^*ℒ)^{⊗ d}`**: the
comparison of the integral tensor powers of [Stacks, Tag 01CU] under pullback, followed by the
comparison induced by `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`.  This is
`AlgebraicGeometry.Space.pointLaurentPiecePullbackHom` with the full subcategory of the
quasi-coherent modules left behind. -/
theorem pointLaurentPiecePullbackHom_hom (d : ℤ) :
    (pointLaurentPiecePullbackHom L τ x d).hom =
      (intPullIso ((BigFppfOver.toScheme B S hS).map τ) (pointLine B S hS L T x) d).hom ≫
        (LaurentCongr.congrIso (pointLineIso L τ x) d).hom :=
  rfl

end PointLaurentPiecePullback

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

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
  {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
  (x : yoneda.obj T ⟶ X.1)

/-- **The comparison `τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ` of the restriction datum of a pair `(ℒ, ψ)` on the
small étale site of `X` is `AlgebraicGeometry.Space.pointLineIso`**: the two are the same after one
projection of the structure instance
`…InvertibleTwistingRestriction.ofUnitalHom`, but see the implementation notes of this file for
why the statement is proved through the underlying morphisms. -/
theorem lineIso_eq_pointLineIso :
    (ofUnitalHom s f L ψ).lineIso τ x = pointLineIso L τ x :=
  Iso.ext rfl

/-- **The comparison `τ^*((x^*ℒ)^{⊗ d}) ⟶ ((x ∘ τ)^*ℒ)^{⊗ d}` of
`AlgebraicGeometry.Space.pointLaurentPiecePullbackHom`, in the vocabulary of the restriction
datum of a pair `(ℒ, ψ)` on the small étale site of `X`**: the comparison `intPullIso` of the
integral tensor powers of [Stacks, Tag 01CU] under pullback, followed by the comparison induced by
`τ^*(x^*ℒ) ≅ (x ∘ τ)^*ℒ`.

This is the value of `ρ` that `AlgebraicGeometry.Space.chartScheme_target_coherence` asks for; see
the implementation notes of this file for why the two sides are compared one factor at a time. -/
theorem pointLaurentPiecePullbackHom_hom_eq (d : ℤ) :
    (pointLaurentPiecePullbackHom L τ x d).hom =
      (intPullIso ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)
          ((ofUnitalHom s f L ψ).line T x) d).hom ≫
        (LaurentCongr.congrIso ((ofUnitalHom s f L ψ).lineIso τ x) d).hom := by
  refine (pointLaurentPiecePullbackHom_hom L τ x d).trans (congrArg₂ (· ≫ ·) ?_ ?_)
  · rfl
  · exact LaurentCongr.congrIso_hom_congr
      (L := (pullbackFunctor (ringedSpaceHom
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ))).obj
        ((ofUnitalHom s f L ψ).line T x))
      (L' := (ofUnitalHom s f L ψ).line T' (yoneda.map τ ≫ x))
      (lineIso_eq_pointLineIso s f L ψ τ x).symm d

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
