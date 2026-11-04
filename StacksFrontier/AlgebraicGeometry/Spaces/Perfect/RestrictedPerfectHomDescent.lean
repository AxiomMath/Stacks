module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectDescent

/-!
# Descent of morphisms between perfect objects in Situation 09RH

The induction of Stacks 08GP in the proof of Stacks 09RJ glues perfect objects across an
elementary distinguished square `(U ⊆ W, V ⟶ W)`; the gluing isomorphism on `U ×_W V` has to be
descended to a stage, so the property carried through the induction is the essential
surjectivity of Stacks 09RJ together with the full faithfulness of Stacks 09RI for perfect
objects. This file states the full faithfulness half.

For perfect `Eᵢ`, `Kᵢ` on a stage `Xᵢ`, the comparison
`colim_{j ≥ i} Hom(Lf_{ji}^*Eᵢ, Lf_{ji}^*Kᵢ) ⟶ Hom(Lfᵢ^*Eᵢ, Lfᵢ^*Kᵢ)` is a bijection: every
morphism at the limit comes from a stage, and two morphisms at stage `i` which agree at the limit
agree at a later stage. Quantifying over all perfect `Kᵢ` includes all their shifts, so this is
the full faithfulness in all degrees that the Mayer–Vietoris step of the induction (Stacks 08H9)
consumes.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation.stageProjectionDerivedPullbackIso`: the comparison
  `Lf_j^* ∘ Lf_{ji}^* ≅ Lfᵢ^*` of the factorisation `f_{ji} ∘ f_j = fᵢ`.
* `AlgebraicGeometry.Space.DescentSituation.PerfectHomsDescend`: the full faithfulness half of
  Stacks 09RI–09RJ for perfect objects.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.Space.DescentSituation

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **The comparison `Lf_j^* ∘ Lf_{ji}^* ≅ Lfᵢ^*`** on the models of the spaces-étale sites, for
`i ≤ j`, of the factorisation of the projection `fᵢ : X ⟶ Xᵢ` through `fⱼ` and the transition
morphism `f_{ji} : Xⱼ ⟶ Xᵢ`. -/
def stageProjectionDerivedPullbackIso {i j : I} (h : i ≤ j)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS ⟨D.system.obj (op i), D.algebraicSpace i⟩).O))) :
    (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op j)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op j), D.algebraicSpace j⟩))).obj
        ((derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj E) ≅
      (derivedPullback (spacesEtaleModelHom B S hS
        (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj E :=
  (spacesEtaleModelDerivedPullbackCompIso B S hS _ _).app E ≪≫
    eqToIso (congrArg (fun k => (derivedPullback (spacesEtaleModelHom B S hS k)).obj E)
      (ObjectProperty.hom_ext _ (D.limitCone.w (homOfLE h).op)))

/-- **The full faithfulness half of Stacks 09RI–09RJ for perfect objects** in a situation `D`:
for perfect objects `Eᵢ`, `Kᵢ` of `D(𝒪_{Xᵢ})` at a stage `i ≥ 0`, every morphism
`Lfᵢ^*Eᵢ ⟶ Lfᵢ^*Kᵢ` at the limit is `Lfⱼ^*ψ`, read through the comparisons
`AlgebraicGeometry.Space.DescentSituation.stageProjectionDerivedPullbackIso`, for some `j ≥ i`
and some `ψ : Lf_{ji}^*Eᵢ ⟶ Lf_{ji}^*Kᵢ`; and two morphisms `Eᵢ ⟶ Kᵢ` with the same image at
the limit have the same image at some stage `j ≥ i`.

For a directed index these two clauses say exactly that
`colim_{j ≥ i} Hom(Lf_{ji}^*Eᵢ, Lf_{ji}^*Kᵢ) ⟶ Hom(Lfᵢ^*Eᵢ, Lfᵢ^*Kᵢ)` is bijective (the second
clause applied at the stage `j` itself gives eventual injectivity out of every stage). -/
def PerfectHomsDescend : Prop :=
  ∀ (i : I) (_ : D.base ≤ i) (Eᵢ Kᵢ : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS ⟨D.system.obj (op i), D.algebraicSpace i⟩).O))),
    (spacesEtaleModelRingedSite B S hS ⟨D.system.obj (op i), D.algebraicSpace i⟩).IsPerfect Eᵢ →
    (spacesEtaleModelRingedSite B S hS ⟨D.system.obj (op i), D.algebraicSpace i⟩).IsPerfect Kᵢ →
    (∀ φ : (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ⟶
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Kᵢ,
      ∃ (j : I) (h : i ≤ j) (ψ : (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Eᵢ ⟶
          (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).obj Kᵢ),
        φ = (D.stageProjectionDerivedPullbackIso h Eᵢ).inv ≫
          (derivedPullback (spacesEtaleModelHom B S hS
            (ObjectProperty.homMk (D.limitCone.π.app (op j)) :
              (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
                ⟨D.system.obj (op j), D.algebraicSpace j⟩))).map ψ ≫
          (D.stageProjectionDerivedPullbackIso h Kᵢ).hom) ∧
    (∀ φ ψ : Eᵢ ⟶ Kᵢ,
      (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map φ =
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
            (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map ψ →
      ∃ (j : I) (h : i ≤ j),
        (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map φ =
          (derivedPullback (spacesEtaleModelHom B S hS
          (ObjectProperty.homMk (D.system.map (homOfLE h).op) :
            (⟨D.system.obj (op j), D.algebraicSpace j⟩ : AlgebraicSpaces B S hS) ⟶
              ⟨D.system.obj (op i), D.algebraicSpace i⟩))).map ψ)

end AlgebraicGeometry.Space.DescentSituation

end
