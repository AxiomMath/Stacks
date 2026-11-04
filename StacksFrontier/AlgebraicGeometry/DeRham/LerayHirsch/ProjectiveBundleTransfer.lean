module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleFibreBasis
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle

/-!
# Transporting the projective bundle formula along an isomorphism over the base

For morphisms `p : P ⟶ X`, `g : X ⟶ S` and classes `ξ_i ∈ H^{n_i}_{dR}(P/S)`, the map
`⨁_i H^{k - n_i}_{dR}(X/S) ⟶ H^k_{dR}(P/S)`, `(a_i) ↦ ∑ ξ_i ∪ p^*a_i`, is bijective exactly when
the same map for `P' ≅ P` over `X` and the pulled back classes is: pullback along the
isomorphism is bijective, multiplicative and compatible with `p^*`.

This carries the projective bundle formula ([Stacks, Tag 0FMT]) between the two presentations
of the projective bundle of a finite locally free module: `Stacks.RelativeProj.projectiveBundle`,
in which Remark 0FUN is stated, and `Stacks.Chow.bundle`, in which the bundle objects of the
Chern class formalism (Tags 0FI5, 0FW9, 0FWB) are stated. Their comparison
`Stacks.RelativeProj.bundlePresentationIso` carries one tautological twist to the other, so the de
Rham first Chern classes correspond.

## Main results

* `Stacks.ProjectiveBundleDeRham.bijective_sum_cup_of_iso`: the transport.
* `Stacks.ProjectiveBundleDeRham.deRhamPullbackSquare_projectiveBundleChernClass`: the
  comparison of presentations carries `c₁^{dR}(𝒪_P(1))` to `c₁^{dR}` of `Stacks.Chow.bundleTwist`.

## References

* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase tautologicalDatumTwist
  isInvertible_tautologicalDatumTwist)
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.ProjectiveBundleDeRham

/-! ### Transport along an isomorphism over the base -/

section Transport

variable {P P' X S : Scheme.{u}} (p : P ⟶ X) (g : X ⟶ S) (ψ : P' ⟶ P) [IsIso ψ]

omit [IsIso ψ] in
/-- The square `(ψ, 𝟙 S)` from `P' ⟶ S` to `P ⟶ S`. -/
theorem transport_w {p' : P' ⟶ X} (hp : ψ ≫ p = p') : ψ ≫ (p ≫ g) = (p' ≫ g) ≫ 𝟙 S := by
  simp [← hp]

/-- Pullback of de Rham cohomology commutes with transport along equalities of degrees. -/
theorem deRhamPullbackSquare_eqToHom {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S')
    (f : X ⟶ S) (g : S' ⟶ S) (w : g' ≫ f = f' ≫ g) {m k : ℤ} (h : m = k)
    (x : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m) :
    Stacks.DeRhamBaseChange.deRhamPullbackSquare g' f' f g w k
        ((eqToHom (congrArg (SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))) h)).hom x) =
      (eqToHom (congrArg (SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras f')
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))) h)).hom
        (Stacks.DeRhamBaseChange.deRhamPullbackSquare g' f' f g w m x) := by
  subst h
  rfl

omit [IsIso ψ] in
/-- `ψ^* ∘ p^* = (ψ ≫ p)^*`. -/
theorem deRhamPullbackSquare_deRhamPullbackModule {p' : P' ⟶ X} (hp : ψ ≫ p = p') (m : ℤ)
    (a : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras g)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) m) :
    Stacks.DeRhamBaseChange.deRhamPullbackSquare ψ (p' ≫ g) (p ≫ g) (𝟙 S)
        (transport_w p g ψ hp) m (DeRhamKatzOdaCech.deRhamPullbackModule p g m a) =
      DeRhamKatzOdaCech.deRhamPullbackModule p' g m a := by
  subst hp
  exact (Stacks.DeRhamBaseChange.deRhamPullbackSquare_comp p (p ≫ g) g (𝟙 S) (by simp) ψ
    ((ψ ≫ p) ≫ g) (𝟙 S) (transport_w p g ψ rfl) (by simp) m a).trans
    (Stacks.DeRhamBaseChange.deRhamPullbackSquare_congr (f' := (ψ ≫ p) ≫ g) (f := g) rfl
      (Category.comp_id _) _ _ m a)

/-- **The projective bundle formula is invariant under isomorphism over the base**: if
`(a_i) ↦ ∑ ξ_i ∪ p^*a_i` is bijective in degree `k`, so is `(a_i) ↦ ∑ ψ^*ξ_i ∪ (ψ ≫ p)^*a_i` for
an isomorphism `ψ : P' ⟶ P` with `ψ ≫ p = p'`. -/
theorem bijective_sum_cup_of_iso {p' : P' ⟶ X} (hp : ψ ≫ p = p') {N : ℕ} (n : Fin N → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (p ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p ≫ g))) (n i : ℤ)) (k : ℤ)
    (h : Function.Bijective (fun a : ∀ i, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
      ∑ i, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (p ≫ g))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p ≫ g))))
          (add_sub_cancel (n i : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ (n i) (k - n i) (ξ i)
          (DeRhamKatzOdaCech.deRhamPullbackModule p g (k - n i) (a i))))) :
    Function.Bijective (fun a : ∀ i, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
      ∑ i, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (p' ≫ g))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p' ≫ g))))
          (add_sub_cancel (n i : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ (n i) (k - n i)
          (Stacks.DeRhamBaseChange.deRhamPullbackSquare ψ (p' ≫ g) (p ≫ g) (𝟙 S)
            (transport_w p g ψ hp) _ (ξ i))
          (DeRhamKatzOdaCech.deRhamPullbackModule p' g (k - n i) (a i)))) := by
  have e : (fun a : ∀ i, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
      ∑ i, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (p' ≫ g))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p' ≫ g))))
          (add_sub_cancel (n i : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ (n i) (k - n i)
          (Stacks.DeRhamBaseChange.deRhamPullbackSquare ψ (p' ≫ g) (p ≫ g) (𝟙 S)
            (transport_w p g ψ hp) _ (ξ i))
          (DeRhamKatzOdaCech.deRhamPullbackModule p' g (k - n i) (a i)))) =
      (Stacks.DeRhamBaseChange.deRhamPullbackSquare ψ (p' ≫ g) (p ≫ g) (𝟙 S)
        (transport_w p g ψ hp) k) ∘ (fun a : ∀ i, SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras g)
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras g)) (k - n i) =>
      ∑ i, (eqToHom (congrArg (SheafOfModules.deRhamCohomology
          (Scheme.Hom.deRhamAlgebras (p ≫ g))
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (p ≫ g))))
          (add_sub_cancel (n i : ℤ) k))).hom
        (SheafOfModules.deRhamCohomologyCup _ _ (n i) (k - n i) (ξ i)
          (DeRhamKatzOdaCech.deRhamPullbackModule p g (k - n i) (a i)))) := by
    funext a
    simp only [Function.comp_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [deRhamPullbackSquare_eqToHom (h := add_sub_cancel (n i : ℤ) k),
      Stacks.DeRhamBaseChange.deRhamPullbackSquare_cup,
      deRhamPullbackSquare_deRhamPullbackModule p g ψ hp]
  exact e ▸ (Stacks.DeRhamBaseChange.bijective_deRhamPullbackSquare_of_isIso ψ _ _ _ k).comp h

end Transport

/-! ### The two presentations of the projective bundle -/

section Presentations

variable {X S : Scheme.{u}} (g : X ⟶ S) (E : X.Modules) [E.IsQuasicoherent]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The comparison of presentations lies over the base. -/
theorem bundlePresentationIso_hom_comp_projectiveBundleToBase :
    (Stacks.RelativeProj.bundlePresentationIso E).hom ≫ projectiveBundleToBase X E =
      Stacks.Chow.bundleProj E :=
  Stacks.RelativeProj.bundlePresentationIso_hom_comp_toBase E

/-- **The comparison of presentations carries `c₁^{dR}(𝒪_P(1))` to the first Chern class of the
twist of `Stacks.Chow.bundle`.** -/
theorem deRhamPullbackSquare_projectiveBundleChernClass :
    Stacks.DeRhamBaseChange.deRhamPullbackSquare (Stacks.RelativeProj.bundlePresentationIso E).hom
        (Stacks.Chow.bundleProj E ≫ g) (projectiveBundleToBase X E ≫ g) (𝟙 S)
        (transport_w _ g _ (bundlePresentationIso_hom_comp_projectiveBundleToBase E)) _
        (DeRhamLerayHirsch.projectiveBundleChernClass g E) =
      Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard (Stacks.Chow.bundleProj E ≫ g)
        (Stacks.WeilCohomology.picardClassOf _ (Stacks.Chow.bundleTwist E)
          (Stacks.ProjectiveBundleSplitting.isInvertible_tautologicalTwist E
            (Stacks.Chow.bundlePieces E))) := by
  refine (congrArg (Stacks.DeRhamBaseChange.deRhamPullbackSquare
    (Stacks.RelativeProj.bundlePresentationIso E).hom (Stacks.Chow.bundleProj E ≫ g)
    (projectiveBundleToBase X E ≫ g) (𝟙 S)
    (transport_w _ g _ (bundlePresentationIso_hom_comp_projectiveBundleToBase E)) _)
      (projectiveBundleChernClass_eq_deRhamFirstChernClassPicard g E)).trans ?_
  refine (Stacks.DeRhamBaseChange.deRhamPullbackSquare_deRhamFirstChernClassPicard _ _ _ _ _
    (tautologicalDatumTwist E) (isInvertible_tautologicalDatumTwist E)).trans ?_
  refine congrArg (Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard _)
    (Stacks.WeilCohomology.picardClassOf_eq_of_iso _ _ _ _ _ ?_)
  exact (Scheme.Modules.pullbackComp (Stacks.RelativeProj.bundlePresentationIso E).hom
      (Stacks.RelativeProj.bundlePresentationIso E).inv).app _ ≪≫
    (Scheme.Modules.pullbackCongr (Stacks.RelativeProj.bundlePresentationIso E).hom_inv_id).app _ ≪≫
    (Scheme.Modules.pullbackId _).app _

end Presentations

end Stacks.ProjectiveBundleDeRham
