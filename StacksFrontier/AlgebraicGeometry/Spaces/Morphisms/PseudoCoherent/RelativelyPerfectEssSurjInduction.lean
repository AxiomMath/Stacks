module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectEssSurjSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated

/-!
# The induction over the étale objects of `X₀` in the essential surjectivity of Stacks 0DKW

In Situation 0DKU, fix a quasi-compact quasi-separated algebraic space `X'` and `c : X' ⟶ Y₀`.
If every situation with the inverse system of `D` whose space over the chosen stage is affine over
`c` is essentially surjective, then so is every situation whose space over the chosen stage is
isomorphic to `X'` over `c`. The induction, in the sense of Stacks 08GP, is over the étale
`g : Y ⟶ X'`, for the property that every situation whose space over the chosen stage is
isomorphic to `Y` compatibly with `c` is essentially surjective.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.EssSurjOver`: the property of the induction.

## Main results

* `AlgebraicGeometry.Space.RelativeDescentSituation.isFinitePresentation_of_isEtale_of_qcqs`: an
  étale morphism from a quasi-compact quasi-separated algebraic space to a quasi-separated one is
  of finite presentation.
* `AlgebraicGeometry.Space.RelativeDescentSituation.essSurjOver_of_qcqs`: if every situation
  whose space over the chosen stage is affine over `c` is essentially surjective, then so is every
  situation whose space over the chosen stage is isomorphic to `X'` over `c`.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space.RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- An étale morphism from a quasi-compact quasi-separated algebraic space to a quasi-separated
one is of finite presentation. -/
theorem isFinitePresentation_of_isEtale_of_qcqs {U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (hUqc : IsQuasiCompactSpace B S hS U)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U) {g : U ⟶ X} (hg : IsEtale B S hS g) :
    IsFinitePresentation B S hS g :=
  ⟨isLocallyOfFinitePresentation_of_isEtale B S hS hg,
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hX hXqs hUqc g,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ hU hUqs g⟩

/-- **The property of the induction.** For `c : X' ⟶ Y₀` and `g : Y ⟶ X'`: every situation
with the inverse system of `D` whose space `F.X₀` over the chosen stage is isomorphic to `Y`
through `e`, with structure morphism `e ≫ g ≫ c`, is essentially surjective. -/
def EssSurjOver {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c : X' ⟶ D.Y.obj (op D.i₀))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : Y ⟶ X') : Prop :=
  ∀ (F : SourceData B S hS D.Y D.limitCone D.i₀) (e : F.X₀ ⟶ Y), IsIso e → F.p₀ = e ≫ g ≫ c →
    (D.withSource F).RelativelyPerfectEssentiallySurjective

/-- **The induction over the étale objects of a quasi-compact quasi-separated `X'`.** If every
situation with the inverse system of `D` whose space over the chosen stage is affine, with
structure morphism through `c : X' ⟶ Y₀`, is essentially surjective, then so is every
situation whose space over the chosen stage is isomorphic to `X'` over `c`. The inputs are
Stacks 0DKT (`h0DKT`), the étale locality of relative perfectness (`hloc`, a consequence of
Stacks 0DKQ) and full faithfulness of every situation (`hff`, clauses (4), (5) of Stacks 0DKW,
from Stacks 0DKV). -/
theorem essSurjOver_of_qcqs (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    (hloc : EtaleLocalRelativelyPerfect B S hS)
    (hff : ∀ D' : RelativeDescentSituation B S hS hZ I, D'.RelativelyPerfectFullyFaithful)
    (X' : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X'.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X'.1) (c : X'.1 ⟶ D.Y.obj (op D.i₀))
    (hleaf : ∀ F : SourceData B S hS D.Y D.limitCone D.i₀, IsAffineSpace B S hS F.X₀ →
      ∀ t : F.X₀ ⟶ X'.1, F.p₀ = t ≫ c → (D.withSource F).RelativelyPerfectEssentiallySurjective) :
    D.EssSurjOver c X'.1 (𝟙 X'.1) := by
  refine qcqs_induction_on_self B S hS hZ X' hqc hqs (D.EssSurjOver c) ?_ ?_
  · intro V hV F e he hp
    exact hleaf F (hV.of_iso (@asIso _ _ _ _ e he).symm) (e ≫ V.1.hom.hom)
      (hp.trans (Category.assoc _ _ _).symm)
  · intro W V U f hf hsq _ hWqs hUqc hVaff hPU hPV _ F e he hp
    let D' := D.withSource F
    have hF₀ : IsAbsolutelyQuasiSeparated B S hS hZ F.X₀ :=
      D'.initial_isAbsolutelyQuasiSeparated
    have hsq' : IsElementaryDistinguishedSquare B S hS D'.initialSource.2 (U.preimage e)
        (pullback.snd f e) :=
      isElementaryDistinguishedSquare_preimage B S hS W.1.left.2 F.initial_isAlgebraicSpace U f
        hsq e
    have hU₁ : IsIso (U.fromPreimage e) :=
      (Subfunctor.isPullback_preimage e U).isIso_fst_of_isIso
    have hP₁ : IsIso (pullbackPreimageιLift U f e) :=
      (isPullback_pullbackPreimageιLift U f e).isIso_fst_of_isIso
    have hVaff' : IsAffineSpace B S hS (pullback f e) :=
      hVaff.of_iso (asIso (pullback.fst f e)).symm
    have hUqc' : IsQuasiCompactSpace B S hS (U.preimage e).toFunctor :=
      isQuasiCompactSpace_of_iso B S hS (asIso (U.fromPreimage e)).symm hUqc
    have hUqs' : IsAbsolutelyQuasiSeparated B S hS hZ (U.preimage e).toFunctor :=
      isAbsolutelyQuasiSeparated_of_mono B S hS hZ hsq'.isOpenSubspace.1 (U.preimage e).ι
        inferInstance hF₀
    have hfpU : IsFinitePresentation B S hS (U.preimage e).ι :=
      isFinitePresentation_of_isEtale_of_qcqs hsq'.isOpenSubspace.1 F.initial_isAlgebraicSpace
        hF₀ hUqc' hUqs' (isEtale_edsOpenHom B S hS (W := D'.initialSource) hsq')
    have hfpV : IsFinitePresentation B S hS (pullback.snd f e) :=
      isFinitePresentation_of_isEtale_of_qcqs hsq'.isAlgebraicSpace F.initial_isAlgebraicSpace
        hF₀ hVaff'.isQuasiCompactSpace (hVaff'.isAbsolutelyQuasiSeparated B S hS hZ) hsq'.isEtale
    have hPalg := (edsInter B S hS (W := D'.initialSource) hsq').2
    have hPqc : IsQuasiCompactSpace B S hS
        (pullback (U.preimage e).ι (pullback.snd f e)) := by
      have hq : IsQuasiCompact B S hS
          (pullback.snd (U.preimage e).ι (pullback.snd f e)) :=
        isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback _ _)
          hfpU.2.1
      exact isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS _ hVaff' hq
    have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ
        (pullback (U.preimage e).ι (pullback.snd f e)) :=
      isAbsolutelyQuasiSeparated_of_mono B S hS hZ hPalg
        (pullback.snd (U.preimage e).ι (pullback.snd f e)) inferInstance
        (hVaff'.isAbsolutelyQuasiSeparated B S hS hZ)
    have hfpP : IsFinitePresentation B S hS
        (pullback.fst (U.preimage e).ι (pullback.snd f e) ≫ (U.preimage e).ι) :=
      isFinitePresentation_of_isEtale_of_qcqs hPalg F.initial_isAlgebraicSpace hF₀ hPqc hPqs
        (isEtale_edsInterHom B S hS (W := D'.initialSource) hsq')
    refine D'.relativelyPerfectEssentiallySurjective_of_eds hsq' hfpU hfpV hfpP h0DKT hloc ?_ ?_
      (hff _)
    · refine hPU (D'.edsOpenSource hsq' hfpU) (U.fromPreimage e) hU₁ ?_
      change (U.preimage e).ι ≫ F.p₀ = _
      rw [hp, ← Category.assoc, ← (Subfunctor.isPullback_preimage e U).w]
      simp only [Category.assoc]
    · refine hPV (D'.edsEtaleSource hsq' hfpV) (pullback.fst f e) inferInstance ?_
      change pullback.snd f e ≫ F.p₀ = _
      rw [hp, ← Category.assoc, ← pullback.condition, Category.assoc, ← Category.assoc f, hf]

end AlgebraicGeometry.Space.RelativeDescentSituation

end
