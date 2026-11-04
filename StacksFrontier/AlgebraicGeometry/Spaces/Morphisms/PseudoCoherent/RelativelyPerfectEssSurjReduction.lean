module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectBaseChangeStableProof
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectEssSurjInduction
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectEtaleLocalProof

/-!
# Reduction of the essential surjectivity in Stacks 0DKW to the affine case

In Situation 0DKU, essential surjectivity in Stacks 0DKW holds as soon as it holds for every
situation with the same inverse system whose space over the chosen stage is affine, with structure
morphism factoring through an étale morphism `V ⟶ Y₀` from an affine algebraic space.

All names below are in the namespace `AlgebraicGeometry.Space.RelativeDescentSituation`.

## Main definitions

* `EssSurjOverTarget`: for an étale `g : W ⟶ Y₀`, every situation with the inverse system of `D`
  whose space over the chosen stage is the base change `W ×_{Y₀} X₀`, with structure morphism
  through `g`, is essentially surjective.
* `RelativelyPerfectAffineEssentiallySurjective`: the affine case.

## Main results

* `relativelyPerfectEssentiallySurjective_of_affine`: essential surjectivity in Stacks 0DKW from
  the affine case.
* `relativelyPerfectColimit_of_held'`: Stacks 0DKW from full faithfulness and the affine case.

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

/-- For `g : W ⟶ Y₀`: every situation with the inverse system of `D` whose space `F.X₀` over the
chosen stage is the base change of `X₀ ⟶ Y₀` along `g` (through `v' : F.X₀ ⟶ W` and
`v : F.X₀ ⟶ X₀`), with structure morphism `v' ≫ g`, is essentially surjective. -/
def EssSurjOverTarget (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : W ⟶ D.Y.obj (op D.i₀)) :
    Prop :=
  ∀ (F : SourceData B S hS D.Y D.limitCone D.i₀) (v' : F.X₀ ⟶ W) (v : F.X₀ ⟶ D.X₀),
    IsPullback v' v g D.p₀ → F.p₀ = v' ≫ g → (D.withSource F).RelativelyPerfectEssentiallySurjective

/-- **The affine case of the essential surjectivity in Stacks 0DKW.**  Every situation with the
inverse system of `D` whose space over the chosen stage is affine, with structure morphism
factoring as `t ≫ w` through an étale morphism `w : V ⟶ Y₀` from an affine algebraic space `V`,
is essentially surjective. -/
def RelativelyPerfectAffineEssentiallySurjective : Prop :=
  ∀ F : SourceData B S hS D.Y D.limitCone D.i₀, IsAffineSpace B S hS F.X₀ →
    ∀ {V : AlgebraicSpaces B S hS} (w : V ⟶ D.initialTarget) (t : F.X₀ ⟶ V.1),
      IsAffineSpace B S hS V.1 → IsEtale B S hS w.hom → F.p₀ = t ≫ w.hom →
        (D.withSource F).RelativelyPerfectEssentiallySurjective

/-- **The reduction of essential surjectivity in Stacks 0DKW to the affine case.**  If every
situation with the inverse system of `D` whose space over the chosen stage is affine, with
structure morphism factoring through an étale morphism `V ⟶ Y₀` from an affine algebraic space, is
essentially surjective, then so is `D`, given Stacks 0DKT (`h0DKT`), the étale locality of
relative perfectness (`hloc`) and full faithfulness of every situation (`hff`). -/
theorem relativelyPerfectEssentiallySurjective_of_affine
    (h0DKT : RelativelyPerfectBaseChangeStable B S hS)
    (hloc : EtaleLocalRelativelyPerfect B S hS)
    (hff : ∀ D' : RelativeDescentSituation B S hS hZ I, D'.RelativelyPerfectFullyFaithful)
    (haff : D.RelativelyPerfectAffineEssentiallySurjective) :
    D.RelativelyPerfectEssentiallySurjective := by
  suffices key : D.EssSurjOverTarget D.initialTarget.1 (𝟙 _) from
    key D.sourceData D.p₀ (𝟙 D.X₀) (IsPullback.id_vert D.p₀) (Category.comp_id _).symm
  refine qcqs_induction_on_self B S hS hZ D.initialTarget (D.stage_isQuasiCompact D.i₀)
    (D.stage_isQuasiSeparated D.i₀) D.EssSurjOverTarget ?_ ?_
  · intro V hV F v' v sq hp
    have hFqc : IsQuasiCompactSpace B S hS F.X₀ :=
      isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS v' hV
        (isQuasiCompact_of_isPullback B S hS sq.flip D.initial_isFinitePresentation.2.1)
    refine D.essSurjOver_of_qcqs h0DKT hloc hff ⟨F.X₀, F.initial_isAlgebraicSpace⟩ hFqc
      (D.withSource F).initial_isAbsolutelyQuasiSeparated F.p₀ (fun F' hF' t ht ↦ ?_) F (𝟙 _)
      inferInstance (by simp)
    refine haff F' hF' (V := V.1.left) (ObjectProperty.homMk V.1.hom.hom) (t ≫ v') hV V.2 ?_
    rw [ht, hp, Category.assoc]
    rfl
  · intro W V U f hf hsq _ _ hUqc hVaff hPU hPV _ F v' v sq hp
    let D' := D.withSource F
    have hF₀ : IsAbsolutelyQuasiSeparated B S hS hZ F.X₀ := D'.initial_isAbsolutelyQuasiSeparated
    have hsq' : IsElementaryDistinguishedSquare B S hS D'.initialSource.2 (U.preimage v')
        (pullback.snd f v') :=
      isElementaryDistinguishedSquare_preimage B S hS W.1.left.2 F.initial_isAlgebraicSpace U f
        hsq v'
    have sqU : IsPullback (U.fromPreimage v') ((U.preimage v').ι ≫ v) (U.ι ≫ W.1.hom.hom)
        D.p₀ :=
      (Subfunctor.isPullback_preimage v' U).paste_vert sq
    have sqV : IsPullback (pullback.fst f v') (pullback.snd f v' ≫ v) V.1.hom.hom D.p₀ := by
      simpa only [hf] using (IsPullback.of_hasPullback f v').paste_vert sq
    have hfpp := D.initial_isFinitePresentation
    have hUqc' : IsQuasiCompactSpace B S hS (U.preimage v').toFunctor :=
      isQuasiCompactSpace_source_of_isQuasiCompact B S hS hsq.isOpenSubspace.1 hUqc
        (isQuasiCompact_of_isPullback B S hS sqU.flip hfpp.2.1)
    have hUqs' : IsAbsolutelyQuasiSeparated B S hS hZ (U.preimage v').toFunctor :=
      isAbsolutelyQuasiSeparated_of_mono B S hS hZ hsq'.isOpenSubspace.1 (U.preimage v').ι
        inferInstance hF₀
    have hfpU : IsFinitePresentation B S hS (U.preimage v').ι :=
      isFinitePresentation_of_isEtale_of_qcqs hsq'.isOpenSubspace.1 F.initial_isAlgebraicSpace
        hF₀ hUqc' hUqs' (isEtale_edsOpenHom B S hS (W := D'.initialSource) hsq')
    have hVqc' : IsQuasiCompact B S hS (pullback.fst f v') :=
      isQuasiCompact_of_isPullback B S hS sqV.flip hfpp.2.1
    have hVqs' : IsQuasiSeparated B S hS (pullback.fst f v') :=
      isQuasiSeparated_of_isPullback B S hS sqV.flip hfpp.2.2
    have hVaqs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ _
      hsq'.isAlgebraicSpace hVaff hVqs'
    have hfpV : IsFinitePresentation B S hS (pullback.snd f v') :=
      isFinitePresentation_of_isEtale_of_qcqs hsq'.isAlgebraicSpace F.initial_isAlgebraicSpace
        hF₀ (isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS _ hVaff hVqc')
        hVaqs hsq'.isEtale
    have hPalg := (edsInter B S hS (W := D'.initialSource) hsq').2
    have hPqc : IsQuasiCompactSpace B S hS (pullback (U.preimage v').ι (pullback.snd f v')) :=
      isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS
        (pullback.snd (U.preimage v').ι (pullback.snd f v') ≫ pullback.fst f v') hVaff
        (isQuasiCompact_comp B S hS hsq'.isAlgebraicSpace hVaff.isAlgebraicSpace _ _
          (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback _ _) hfpU.2.1) hVqc')
    have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ
        (pullback (U.preimage v').ι (pullback.snd f v')) :=
      isAbsolutelyQuasiSeparated_of_mono B S hS hZ hPalg
        (pullback.snd (U.preimage v').ι (pullback.snd f v')) inferInstance hVaqs
    have hfpP : IsFinitePresentation B S hS
        (pullback.fst (U.preimage v').ι (pullback.snd f v') ≫ (U.preimage v').ι) :=
      isFinitePresentation_of_isEtale_of_qcqs hPalg F.initial_isAlgebraicSpace hF₀ hPqc hPqs
        (isEtale_edsInterHom B S hS (W := D'.initialSource) hsq')
    refine D'.relativelyPerfectEssentiallySurjective_of_eds hsq' hfpU hfpV hfpP h0DKT hloc ?_ ?_
      (hff _)
    · refine hPU (D'.edsOpenSource hsq' hfpU) (U.fromPreimage v') ((U.preimage v').ι ≫ v) sqU ?_
      change (U.preimage v').ι ≫ F.p₀ = _
      rw [hp, ← Category.assoc, ← (Subfunctor.isPullback_preimage v' U).w, Category.assoc]
    · refine hPV (D'.edsEtaleSource hsq' hfpV) (pullback.fst f v') (pullback.snd f v' ≫ v) sqV ?_
      change pullback.snd f v' ≫ F.p₀ = _
      rw [hp, ← Category.assoc, ← pullback.condition, Category.assoc, hf]

/-- **Stacks 0DKW from full faithfulness and the affine case.**  If every situation with the
inverse system of `D` is fully faithful (`hff`) and the affine case of essential surjectivity
holds (`haff`), then `D.RelativelyPerfectColimit` holds. -/
theorem relativelyPerfectColimit_of_held'
    (hff : ∀ D' : RelativeDescentSituation B S hS hZ I, D'.RelativelyPerfectFullyFaithful)
    (haff : D.RelativelyPerfectAffineEssentiallySurjective) : D.RelativelyPerfectColimit :=
  D.relativelyPerfectColimit_of_halves (hff D)
    (D.relativelyPerfectEssentiallySurjective_of_affine (relativelyPerfectBaseChangeStable B S hS)
      (etaleLocalRelativelyPerfect B S hS) hff haff)

end AlgebraicGeometry.Space.RelativeDescentSituation

end
