module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.DerivedLimitBounded

/-!
# The derived limit of Situation 0DIK in `D_QCoh(𝒪_X)` is bounded above, from the affine case

In Situation [Stacks, Tag 0DIK] let `K = R lim_{D_QCoh(𝒪_X)}(Kₙ) = DQ_X(R lim_{D(𝒪_X)} Kₙ)`.
[Stacks, Tag 0DIL] says that `K` lies in `D⁻_QCoh(𝒪_X)`.  This file proves it from the affine
case of the coherator, `AlgebraicGeometry.Space.FlatSheafExistenceSituation.AffineCoheratorCase`,
exactly as `…FlatSheafExistenceSituation.derivedLimit_bounded_of_affineCase` proves
[Stacks, Tag 0CX5]. The affine case is proved as `AlgebraicGeometry.Space.affineCoheratorCase`,
and `…DerivedExistenceSystem.derivedLimit_isBoundedAbove` (in
`StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceBoundedLimit`) is the statement
with it discharged.

## Main definitions

* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.quasicoherentTower`: the tower `(Rjₙ,*
  Kₙ)` read
  in `D_QCoh(𝒪_X)`.

## Main results

* `…isAbsolutelySeparated`, `…isAbsolutelyQuasiSeparated`, `…isAffineHom_of_isAffineSpace`: the
  geometry of the situation, `X` being proper, hence separated, over the affine `Spec A`.
* `…derivedLimit_isBoundedAbove_of_affineCase`: [Stacks, Tag 0DIL], granted the affine case of the
  coherator.

## The proof

It is the source's.  `DQ_X` is a right adjoint, so it carries the derived limit
`L = R lim_{D(𝒪_X)} Kₙ` to a derived limit in `D_QCoh(𝒪_X)`
(`Stacks.Injectives.isDerivedLimit_map_rightAdjoint`); `L` has bounded-above affine cohomology
(`…exists_sectionsAmplitudeLE_of_isDerivedLimit`, from the uniform bound on the `Kₙ`, Nakayama and
the Milnor sequence); and the bounded cohomological dimension of `DQ_X` ([Stacks, Tag 0CSS],
`AlgebraicGeometry.Space.exists_coheratorBound_of_affineCase`) bounds the cohomology of `DQ_X(L)`.

## References

* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 0CSS](https://stacks.math.columbia.edu/tag/0CSS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **`X` is a separated algebraic space**: it is proper, hence separated, over the affine base
`Spec A`. -/
theorem isAbsolutelySeparated :
    IsAbsolutelySeparated D.B (limitBase D.system) D.containsLimitBase D.B.contains_terminal
      D.X.left.1 :=
  isAbsolutelySeparated_of_isSeparated_to_affine D.B (limitBase D.system) D.containsLimitBase
    D.B.contains_terminal _ D.isAffine_limitBaseObject D.X.hom.hom D.separated

/-- `X` is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated :
    IsAbsolutelyQuasiSeparated D.B (limitBase D.system) D.containsLimitBase D.B.contains_terminal
      D.X.left.1 :=
  isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated D.B (limitBase D.system)
    D.containsLimitBase D.B.contains_terminal _ D.isAbsolutelySeparated

/-- Every affine algebraic space étale over `X` maps to `X` by an affine morphism, `X` being
separated ([Stacks, Tag 08GB], part (4)). -/
theorem isAffineHom_of_isAffineSpace
    (V : SpacesEtale D.B (limitBase D.system) D.containsLimitBase D.X.left)
    (hV : IsAffineSpace D.B (limitBase D.system) D.containsLimitBase V.1.left.1) :
    IsAffineHom D.B (limitBase D.system) D.containsLimitBase V.1.hom.hom :=
  isAffineHom_of_isAffineSpace_source_of_isAbsolutelySeparated D.B (limitBase D.system)
    D.containsLimitBase D.B.contains_terminal _ hV D.isAbsolutelySeparated

/-- **The tower `(Rjₙ,* Kₙ)` read in `D_QCoh(𝒪_X)`.** -/
abbrev quasicoherentTower :
    ℕᵒᵖ ⥤ (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
      D.X.left).FullSubcategory :=
  (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).lift
    D.spaceTower fun n i => D.isQuasicoherentOnSite_homology_spaceTower n.unop i

/-- **[Stacks, Tag 0DIL], granted the affine case of the coherator.** In Situation 0DIK the
inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint `DQ_X`, the tower `(Rjₙ,* Kₙ)` has a derived
limit `L = R lim_{D(𝒪_X)} Kₙ`, and for every such `L` and every coherator `DQ_X`, `K = DQ_X(L)` is
a derived limit of the tower in `D_QCoh(𝒪_X)` whose cohomology sheaves vanish above some degree;
so every derived limit of the tower in `D_QCoh(𝒪_X)` lies in `D⁻_QCoh(𝒪_X)`. -/
theorem derivedLimit_isBoundedAbove_of_affineCase
    (haffine : FlatSheafExistenceSituation.AffineCoheratorCase D.B (limitBase D.system)
      D.containsLimitBase) :
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.IsLeftAdjoint ∧
    (∃ L, IsDerivedLimit D.spaceTower L) ∧
    (∀ (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
        (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
          D.X.left).FullSubcategory)
      (_ : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)
      (L : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left),
      IsDerivedLimit D.spaceTower L →
        (∃ _ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩,
          IsDerivedLimit D.quasicoherentTower (DQ.obj L)) ∧
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B (limitBase D.system) D.containsLimitBase
          D.X.left c ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
            D.X.left).ι.obj (DQ.obj L))) ∧
    ∀ (_ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩)
      (K : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory),
      IsDerivedLimit D.quasicoherentTower K →
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B (limitBase D.system) D.containsLimitBase
          D.X.left c ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
            D.X.left).ι.obj K) := by
  have hcor := spaceCoreflective_of_affineCase D.B.contains_terminal D.X.left
    D.isQuasiCompactSpace_X D.isAbsolutelyQuasiSeparated D.isAffineHom_of_isAffineSpace
    (fun Y hY => ⟨(haffine Y hY).1, (haffine Y hY).2.1⟩)
  have hadj := isLeftAdjoint_spaceQuasicoherentι_of_forall hcor
  have hL := D.exists_isDerivedLimit_spaceTower
  obtain ⟨a, ha⟩ := D.exists_sectionsAmplitudeLE_of_isDerivedLimit
  let P := spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left
  have hmain : ∀ (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase
        D.X.left ⥤ P.FullSubcategory) (_ : P.ι ⊣ DQ)
      (L : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left),
      IsDerivedLimit D.spaceTower L →
        (∃ _ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩,
          IsDerivedLimit D.quasicoherentTower (DQ.obj L)) ∧
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B (limitBase D.system) D.containsLimitBase
          D.X.left c (P.ι.obj (DQ.obj L)) := by
    intro DQ adj L hL
    let : DQ.CommShift ℤ := adj.rightAdjointCommShift ℤ
    let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
    have : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
    have : DQ.IsRightAdjoint := adj.isRightAdjoint
    have : DQ.IsTriangulated := adj.isTriangulated_rightAdjoint
    refine ⟨?_, ?_⟩
    · obtain ⟨h, hDL⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint DQ D.spaceTower L hL
      let e : D.spaceTower ⋙ DQ ≅ D.quasicoherentTower :=
        Functor.isoWhiskerRight (P.liftCompιIso D.spaceTower _).symm DQ ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (asIso adj.unit).symm ≪≫
          Functor.rightUnitor _
      have : HasProduct fun n : ℕ => (D.spaceTower ⋙ DQ).obj ⟨n⟩ := h
      have : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩ :=
        hasLimit_of_iso (F := Discrete.functor fun n : ℕ => (D.spaceTower ⋙ DQ).obj ⟨n⟩)
          (Discrete.natIso fun n => e.app ⟨n.as⟩)
      exact ⟨inferInstance, isDerivedLimit_of_iso e hDL⟩
    · obtain ⟨N, hN⟩ := exists_coheratorBound_of_affineCase adj D.B.contains_terminal
        D.isQuasiCompactSpace_X D.isAbsolutelyQuasiSeparated D.isAffineHom_of_isAffineSpace
        (fun Y hY => ⟨(haffine Y hY).2.1, (haffine Y hY).2.2⟩)
      let := spaceHasDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left
      let Q := spaceDerivedQ D.B (limitBase D.system) D.containsLimitBase D.X.left
      obtain ⟨I, g, hI, hg⟩ := exists_quasiIso_isKInjective_modules D.B (limitBase D.system)
        D.containsLimitBase D.X.left.1 D.X.left.2 (Q.objPreimage L)
      let eI : Q.obj I ≅ L := (asIso (Q.map g)).symm ≪≫ Q.objObjPreimageIso L
      exact ⟨a + N, (hN a I hI (ha L hL I hI eI)).of_iso ((DQ ⋙ P.ι).mapIso eI)⟩
  refine ⟨hadj, hL, hmain, fun hprod K hK => ?_⟩
  obtain ⟨L, hL'⟩ := hL
  obtain ⟨⟨h', hDL⟩, c, hle⟩ := hmain _ (Adjunction.ofIsLeftAdjoint P.ι) L hL'
  obtain ⟨e⟩ := nonempty_iso_of_isDerivedLimit hDL hK
  exact ⟨c, fun i hi => (hle i hi).of_iso ((spaceDerivedHomology D.B (limitBase D.system)
      D.containsLimitBase D.X.left i).mapIso (P.ι.mapIso e)).symm⟩

end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space
