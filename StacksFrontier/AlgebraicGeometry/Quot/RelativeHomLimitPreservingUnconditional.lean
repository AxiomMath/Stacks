module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreservingAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSystemModuleColimitQuasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08K4: the relative Hom functor is limit preserving

In Situation 08JT — a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S` and two
quasi-coherent `𝒪_X`-modules `F`, `G` — Stacks 08K4 asserts: if `F` is of finite presentation and
`f` is quasi-compact and quasi-separated, then `Hom(F, G)` is limit preserving.

## Main results

* `AlgebraicGeometry.Space.HomSituation.affineSpaceHomDescent`: the descent of morphisms from a
  module of finite presentation to a quasi-coherent module through a cofiltered limit of affine
  schemes of the site, on their represented algebraic spaces, in the shape the affine case
  consumes.
* `AlgebraicGeometry.Space.HomSituation.limitPreserving_affineSituation`: the affine case.
* `AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor`: **Stacks 08K4.**

## Implementation notes

The proof is the source's.  The change of base to a stage (Stacks 08JW) is
`AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor_of_stages`; the two charts
(Stacks 03H6) and the equalizer (Stacks 08K3) are
`AlgebraicGeometry.Space.HomSituation.limitPreserving_homFunctor_of_affineBase`; the affine case
is `AlgebraicGeometry.Space.HomSituation.limitPreserving_affineSituation`, which reads the relative
Hom functor on the represented fibre products of the site and lands in the descent of morphisms
through a limit of affine schemes into a quasi-coherent module — Stacks 01ZR (2), (3), which is
Algebra, Lemma 05LI on global sections — transported to the small étale sites of the represented
algebraic spaces.

"Limit preserving" is `AlgebraicGeometry.LimitPreserving` (Stacks 049J) along the
underlying-scheme functor of the test schemes over the base, with the index category in the
universe of the schemes, as for the other limit-preservation results of this development.

## References

* [Stacks Project, Tag 08K4](https://stacks.math.columbia.edu/tag/08K4)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 08JW](https://stacks.math.columbia.edu/tag/08JW)
* [Stacks Project, Tag 08K3](https://stacks.math.columbia.edu/tag/08K3)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism whose image under `L` is the conjugate of `φ` by `T` has `φ` for its conjugate. -/
theorem conjHom_eq_of_map_eq {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (T : P₂ ≅ P₁ ⋙ L) {M N : C}
    (φ' : P₁.obj M ⟶ P₁.obj N) (φ : P₂.obj M ⟶ P₂.obj N)
    (h : L.map φ' = T.inv.app M ≫ φ ≫ T.hom.app N) : Functor.conjHom T φ' = φ := by
  unfold Functor.conjHom
  rw [h]
  simp

attribute [local irreducible] modulePullback modulePullbackTriangle

section SpaceClauses

variable (B S hS) {I : Type u} [Category.{u} I] [IsCofiltered I] (V : I ⥤ BigFppfOver B S hS)
  (c : Cone V) (hV : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (k : I)
  (M N : (affineSpacePullbackSystem B S hS V c).C k)
  (hM : M.IsFinitePresentationOnSite) (hN : N.IsQuasicoherentOnSite)

include hV hc hM hN in
/-- The fullness clause into a quasi-coherent module on the represented spaces, with the given
morphism read as a conjugate. -/
theorem affineSpace_exists_conjHom_eq
    (φ : ((affineSpacePullbackSystem B S hS V c).pbL k).obj M ⟶
      ((affineSpacePullbackSystem B S hS V c).pbL k).obj N) :
    ∃ (j : I) (e : j ⟶ k) (φ' : ((affineSpacePullbackSystem B S hS V c).pb e).obj M ⟶
        ((affineSpacePullbackSystem B S hS V c).pb e).obj N),
      Functor.conjHom ((affineSpacePullbackSystem B S hS V c).comp e) φ' = φ := by
  obtain ⟨j, e, φ', h⟩ := affineSpacePullbackSystem_fullnessInto B S hS V c hV hc k M N hM hN φ
  exact ⟨j, e, φ', conjHom_eq_of_map_eq _ φ' φ h⟩

include hV hc hM hN in
/-- The faithfulness clause into a quasi-coherent module on the represented spaces, at a stage
over `k`. -/
theorem affineSpace_exists_map_eq {j : I} (e : j ⟶ k)
    (φ ψ : ((affineSpacePullbackSystem B S hS V c).pb e).obj M ⟶
      ((affineSpacePullbackSystem B S hS V c).pb e).obj N)
    (h : ((affineSpacePullbackSystem B S hS V c).pbL j).map φ =
      ((affineSpacePullbackSystem B S hS V c).pbL j).map ψ) :
    ∃ (j' : I) (e' : j' ⟶ j), ((affineSpacePullbackSystem B S hS V c).pb e').map φ =
      ((affineSpacePullbackSystem B S hS V c).pb e').map ψ :=
  affineSpacePullbackSystem_faithfulnessInto B S hS V c hV hc j _ _
    (isFinitePresentationOnSite_modulePullback B S hS _ M hM)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ N hN) φ ψ h

end SpaceClauses

/-- **The descent of morphisms through a cofiltered limit of affine schemes into a
quasi-coherent module, on the represented algebraic spaces**, in the spelling of
`AlgebraicGeometry.Space.HomSituation.AffineSpaceHomDescent`: this is
`AlgebraicGeometry.Space.affineSpacePullbackSystem_fullnessInto` and
`AlgebraicGeometry.Space.affineSpacePullbackSystem_faithfulnessInto`. -/
theorem affineSpaceHomDescent : AffineSpaceHomDescent B S hS :=
  fun V c hc hV _ k M N hM hN ↦
    ⟨affineSpace_exists_conjHom_eq B S hS V c hV hc k M N hM hN,
      fun _ e φ ψ h ↦ affineSpace_exists_map_eq B S hS V c hV hc k M N hM hN e φ ψ h⟩

/-- **The affine case of Stacks 08K4.** -/
theorem limitPreserving_affineSituation {U T₀ : BigFppfOver B S hS} (f₀ : U ⟶ T₀)
    (F G : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
      ((schemeSpaceFunctor B S hS).obj U).2)
    (hFq : F.IsQuasicoherentOnSite) (hGq : G.IsQuasicoherentOnSite)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (hF : F.IsFinitePresentationOnSite) :
    LimitPreserving.{u, u + 1, u, u} (affineSituation f₀ F G hFq hGq).testSchemeFunctor
      ((affineSituation f₀ F G hFq hGq).homFunctor (modulePushforwardCoherence B S hS)) :=
  limitPreserving_affineSituation_of_affineSpaceHomDescent f₀ F G hFq hGq
    affineSpaceHomDescent hU hT₀ hF

/-- **Stacks 08K4.**  In Situation 08JT, if `F` is of finite presentation and `f` is
quasi-compact and quasi-separated, then the relative Hom functor `Hom(F, G)` is limit
preserving: for every directed limit `T = lim T_i` of affine schemes over the base,
`Hom(F, G)(T) = colim Hom(F, G)(T_i)`. -/
@[stacks 08K4]
theorem limitPreserving_homFunctor (s : HomSituation B S hS)
    (hF : s.F.IsFinitePresentationOnSite) (hqc : IsQuasiCompact B S hS s.f.hom)
    (hqs : IsQuasiSeparated B S hS s.f.hom) :
    LimitPreserving.{u, u + 1, u, u} s.testSchemeFunctor
      (s.homFunctor (modulePushforwardCoherence B S hS)) := by
  refine s.limitPreserving_homFunctor_of_affineCase hF hqc hqs ?_
  intro U T₀ hU hT₀ fU F' G' hF'q hG'q hF'
  obtain ⟨f₀, rfl⟩ : ∃ f₀ : U ⟶ T₀, (schemeSpaceFunctor B S hS).map f₀ = fU :=
    ⟨Yoneda.fullyFaithful.preimage fU.hom,
      ObjectProperty.hom_ext _ (Yoneda.fullyFaithful.map_preimage _)⟩
  exact limitPreserving_affineSituation f₀ F' G' hF'q hG'q hU hT₀ hF'

end AlgebraicGeometry.Space.HomSituation

end
