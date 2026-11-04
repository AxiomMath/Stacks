module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleUniversalHomeomorphism

/-!
# Finite étale covers descend along universal homeomorphisms

Let `g : Y' ⟶ Y` be a universal homeomorphism of schemes. Base change along `g` is an
equivalence between the small étale sites of `Y` and `Y'` (Stacks Tag 04DZ). This file adds the
finiteness half needed for finite étale covers: **an étale `Y`-scheme whose base change to `Y'` is
finite is itself finite**, so every finite étale cover of `Y'` is the base change of a finite
étale cover of `Y`. This is the essential surjectivity of the base-change functor
`FÉt_Y ⥤ FÉt_{Y'}` asserted in Stacks Tag 0BQN.

## Main results

* `AlgebraicGeometry.isFinite_of_isFinite_pullback_snd` — finiteness of an étale morphism descends
  along a universal homeomorphism.
* `AlgebraicGeometry.exists_finiteEtaleBaseChange_iso_of_universalHomeomorphism` — every finite
  étale cover of `Y'` is the base change of a finite étale cover of `Y`.

## Implementation notes

Finiteness is proper plus locally quasi-finite (Stacks Tag 02LS, Mathlib's
`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`). An étale morphism is locally of
finite type and locally quasi-finite, so only properness has to be descended. Universal closedness
descends along the surjection `W ×_Y Y' ⟶ W` (`UniversallyClosed.of_comp_surjective`), and
separatedness descends along the same surjective universally closed morphism
(`AlgebraicGeometry.isSeparated_of_surjective_universallyClosed`).
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {W Y Y' : Scheme.{u}}

/-- **Finiteness of an étale morphism descends along a universal homeomorphism.** -/
theorem isFinite_of_isFinite_pullback_snd (p : W ⟶ Y) [Etale p] (g : Y' ⟶ Y)
    [UniversalHomeomorphism g] [IsFinite (pullback.snd p g)] : IsFinite p := by
  have := Stacks.Etale.isIntegralHom_of_universalHomeomorphism g
  have := Stacks.Etale.isSeparated_of_universalHomeomorphism g
  have := Stacks.Etale.surjective_of_universalHomeomorphism g
  have hcomp : pullback.fst p g ≫ p = pullback.snd p g ≫ g := pullback.condition
  have : UniversallyClosed (pullback.fst p g ≫ p) := by
    rw [hcomp]
    infer_instance
  have : UniversallyClosed p := UniversallyClosed.of_comp_surjective (pullback.fst p g) p
  have : IsSeparated (pullback.fst p g ≫ p) := by
    rw [hcomp]
    infer_instance
  have : IsSeparated p := by
    let f : Over.mk (pullback.fst p g ≫ p) ⟶ Over.mk p := Over.homMk (pullback.fst p g)
    have : Surjective f.left := inferInstanceAs (Surjective (pullback.fst p g))
    have : UniversallyClosed f.left := inferInstanceAs (UniversallyClosed (pullback.fst p g))
    have : IsSeparated (Over.mk (pullback.fst p g ≫ p)).hom :=
      inferInstanceAs (IsSeparated (pullback.fst p g ≫ p))
    exact isSeparated_of_surjective_universallyClosed f
  have : IsProper p := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite p

/-- **Stacks Project, Tag 0BQN, essential surjectivity.** Let `g : Y' ⟶ Y` be a universal
homeomorphism. Every finite étale cover of `Y'` is isomorphic to the base change of a finite étale
cover of `Y`. -/
theorem exists_finiteEtaleBaseChange_iso_of_universalHomeomorphism (g : Y' ⟶ Y)
    [UniversalHomeomorphism g] (V : FiniteEtaleOver Y') :
    ∃ U : FiniteEtaleOver Y, Nonempty ((finiteEtaleBaseChange g).obj U ≅ V) := by
  have := Stacks.Etale.isIntegralHom_of_universalHomeomorphism g
  have := Stacks.Etale.universallyInjective_of_universalHomeomorphism g
  have := Stacks.Etale.surjective_of_universalHomeomorphism g
  let : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong (@Etale : MorphismProperty Scheme.{u}) g :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F : Y.Etale ⥤ Y'.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ g
  have : F.IsEquivalence := Stacks.Etale.etalePullback_isEquivalence g
  let V' : Y'.Etale := MorphismProperty.Over.mk ⊤ V.hom V.prop.2
  obtain ⟨Wt, ⟨e⟩⟩ : ∃ Wt : Y.Etale, Nonempty (F.obj Wt ≅ V') :=
    ⟨F.objPreimage V', ⟨F.objObjPreimageIso V'⟩⟩
  have hWt : Etale Wt.hom := Wt.prop
  let eL : pullback Wt.hom g ≅ V.left :=
    { hom := e.hom.left
      inv := e.inv.left
      hom_inv_id := congrArg (·.left) e.hom_inv_id
      inv_hom_id := congrArg (·.left) e.inv_hom_id }
  have hcomm : eL.hom ≫ V.hom = pullback.snd Wt.hom g := MorphismProperty.Over.w e.hom
  have hfin : IsFinite (pullback.snd Wt.hom g) := by
    have : IsFinite V.hom := V.prop.1
    have : IsIso eL.hom := ⟨eL.inv, eL.hom_inv_id, eL.inv_hom_id⟩
    rw [← hcomm]
    infer_instance
  let U : FiniteEtaleOver Y :=
    MorphismProperty.Over.mk ⊤ Wt.hom ⟨isFinite_of_isFinite_pullback_snd Wt.hom g, hWt⟩
  exact ⟨U, ⟨MorphismProperty.Over.isoMk eL hcomm⟩⟩

end AlgebraicGeometry
