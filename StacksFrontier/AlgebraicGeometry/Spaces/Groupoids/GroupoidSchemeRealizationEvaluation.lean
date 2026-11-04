module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Evaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealizationHom

/-!
# Full faithfulness of the realization of a morphism of groupoid schemes

`Stacks.Groupoids.GroupoidScheme.Hom.realization` realizes a morphism `φ : G ⟶ H` of groupoid
schemes as a morphism of groupoids in algebraic spaces. This file shows that the evaluated
functors of the realization, at every test object of the site, are full, respectively faithful,
when the evaluated functors of `φ` are, at every test scheme over `S`. This is the hypothesis
under which the 1-morphism of quotient stacks `[φ]` is fully faithful (Stacks 046S).

## Main results

* `Stacks.Groupoids.GroupoidScheme.Hom.realization_evaluation_faithful`: the evaluated functors
  of the realization are faithful when those of `φ` are.
* `Stacks.Groupoids.GroupoidScheme.Hom.realization_evaluation_full`: the evaluated functors of
  the realization are full when those of `φ` are.

## Implementation notes

A section over a test object of the presheaf represented by a scheme of the site is a morphism
of schemes over `S` from the test object (`AlgebraicGeometry.Space.yonedaSchemePointEquiv`), and
under that bijection the evaluated functor of the realization is the evaluated functor of `φ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

namespace Stacks.Groupoids.GroupoidScheme.Hom

variable {S : Scheme.{u}} {C : BigFppfSite.{u}} (hS : C.Contains S)
  {G H : GroupoidScheme S} (φ : Hom G H)
  (hUG : C.Contains G.objects.left) (hRG : C.Contains G.arrows.left)
  (hPG : C.Contains (pullback G.source G.target).left)
  (hUH : C.Contains H.objects.left) (hRH : C.Contains H.arrows.left)
  (hPH : C.Contains (pullback H.source H.target).left)

/-- **The evaluated functors of the realization of a morphism of groupoid schemes are faithful**
when those of the morphism of groupoid schemes are, at every test scheme over `S`. -/
theorem realization_evaluation_faithful
    (hfaith : ∀ T : Over S, (φ.evaluation T).Faithful) (T : (BigFppfOver C S hS)ᵒᵖ) :
    ((φ.realization C hS hUG hRG hPG hUH hRH hPH).toGroupoidHom.evaluation T).Faithful := by
  let RG := (G.realization C hS hUG hRG hPG).toGroupoidInFunctors
  let RH := (H.realization C hS hUH hRH hPH).toGroupoidInFunctors
  let eO := yonedaSchemePointEquiv C hS hUG T
  let eA := yonedaSchemePointEquiv C hS hRG T
  constructor
  intro x y m n hmn
  apply (RG.evaluationArrowEquiv T x y).injective
  apply Subtype.ext
  set a := (RG.evaluationArrowEquiv T x y m).1
  set b := (RG.evaluationArrowEquiv T x y n).1
  have hm := congrArg (fun k => (RH.evaluationArrowEquiv T _ _ k).1) hmn
  simp only [Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow] at hm
  have esrc : ∀ c : RG.arrows.obj T, eA c ≫ G.source = eO (RG.source.app T c) := fun c =>
    (yonedaSchemePointEquiv_map C hS hRG hUG G.source T c).symm
  have etgt : ∀ c : RG.arrows.obj T, eA c ≫ G.target = eO (RG.target.app T c) := fun c =>
    (yonedaSchemePointEquiv_map C hS hRG hUG G.target T c).symm
  let mk : (x ⟶ y) → G.EvaluationHom (eO x) (eO y) := fun k =>
    ⟨eA (RG.evaluationArrowEquiv T x y k).1,
      (esrc _).trans (congrArg eO (RG.evaluationArrowEquiv T x y k).2.1),
      (etgt _).trans (congrArg eO (RG.evaluationArrowEquiv T x y k).2.2)⟩
  have himg : (φ.evaluation ((siteToOver C hS).obj T.unop)).map (X := eO x) (Y := eO y) (mk m) =
      (φ.evaluation ((siteToOver C hS).obj T.unop)).map (X := eO x) (Y := eO y) (mk n) := by
    apply EvaluationHom.ext
    show eA a ≫ φ.mapArrows = eA b ≫ φ.mapArrows
    rw [← yonedaSchemePointEquiv_map C hS hRG hRH φ.mapArrows T a,
      ← yonedaSchemePointEquiv_map C hS hRG hRH φ.mapArrows T b]
    exact congrArg (yonedaSchemePointEquiv C hS hRH T) hm
  exact eA.injective (congrArg EvaluationHom.arrow
    ((hfaith ((siteToOver C hS).obj T.unop)).map_injective himg))

/-- **The evaluated functors of the realization of a morphism of groupoid schemes are full**
when those of the morphism of groupoid schemes are, at every test scheme over `S`. -/
theorem realization_evaluation_full
    (hfull : ∀ T : Over S, (φ.evaluation T).Full) (T : (BigFppfOver C S hS)ᵒᵖ) :
    ((φ.realization C hS hUG hRG hPG hUH hRH hPH).toGroupoidHom.evaluation T).Full := by
  let RG := (G.realization C hS hUG hRG hPG).toGroupoidInFunctors
  let RH := (H.realization C hS hUH hRH hPH).toGroupoidInFunctors
  let ψ := φ.realization C hS hUG hRG hPG hUH hRH hPH
  let eO := yonedaSchemePointEquiv C hS hUG T
  let eOH := yonedaSchemePointEquiv C hS hUH T
  let eA := yonedaSchemePointEquiv C hS hRG T
  let eAH := yonedaSchemePointEquiv C hS hRH T
  constructor
  intro x y m'
  set a' := (RH.evaluationArrowEquiv T _ _ m').1 with ha'
  have hsa' : RH.source.app T a' = ψ.toGroupoidHom.mapObjects.app T x :=
    (RH.evaluationArrowEquiv T _ _ m').2.1
  have hta' : RH.target.app T a' = ψ.toGroupoidHom.mapObjects.app T y :=
    (RH.evaluationArrowEquiv T _ _ m').2.2
  have hobj : ∀ z, eOH (ψ.toGroupoidHom.mapObjects.app T z) = eO z ≫ φ.mapObjects := fun z =>
    yonedaSchemePointEquiv_map C hS hUG hUH φ.mapObjects T z
  let m₀ : H.EvaluationHom (eO x ≫ φ.mapObjects) (eO y ≫ φ.mapObjects) :=
    ⟨eAH a', ((yonedaSchemePointEquiv_map C hS hRH hUH H.source T a').symm.trans
        (congrArg eOH hsa')).trans (hobj x),
      ((yonedaSchemePointEquiv_map C hS hRH hUH H.target T a').symm.trans
        (congrArg eOH hta')).trans (hobj y)⟩
  obtain ⟨n₀, hn₀⟩ := (hfull ((siteToOver C hS).obj T.unop)).map_surjective
    (X := eO x) (Y := eO y) m₀
  let a : RG.arrows.obj T := eA.symm n₀.arrow
  have hsa : RG.source.app T a = x :=
    eO.injective <| (yonedaSchemePointEquiv_map C hS hRG hUG G.source T a).trans <| by
      rw [Equiv.apply_symm_apply]
      exact n₀.source_eq
  have hta : RG.target.app T a = y :=
    eO.injective <| (yonedaSchemePointEquiv_map C hS hRG hUG G.target T a).trans <| by
      rw [Equiv.apply_symm_apply]
      exact n₀.target_eq
  refine ⟨(RG.evaluationArrowEquiv T x y).symm ⟨a, hsa, hta⟩, ?_⟩
  apply (RH.evaluationArrowEquiv T _ _).injective
  apply Subtype.ext
  rw [Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow, Equiv.apply_symm_apply, ← ha']
  exact eAH.injective <| (yonedaSchemePointEquiv_map C hS hRG hRH φ.mapArrows T a).trans <| by
    rw [Equiv.apply_symm_apply]
    exact congrArg EvaluationHom.arrow hn₀

end Stacks.Groupoids.GroupoidScheme.Hom

end
