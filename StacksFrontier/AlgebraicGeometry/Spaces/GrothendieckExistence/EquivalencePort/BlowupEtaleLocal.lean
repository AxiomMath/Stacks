module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.SchemeBlowupIsBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Being a blowup is étale local on the target, over a locally Noetherian base

Let `X` be an algebraic space over `S` with an étale presentation by a locally Noetherian scheme,
let `Z ⊆ X` be a closed subspace and let `b : X'' ⟶ X` be a morphism along which the inverse
image of `Z` is an effective Cartier divisor. If the base change of `b` along one surjective
étale morphism `a : T ⟶ X` is the blowup of `T` in the inverse image of `Z`, then `b` is the
blowup of `X` in `Z`.

The blowup `b' : X' ⟶ X` of `X` in `Z` exists (Stacks 085Q, with the size conditions on the
relative `Proj`s supplied by the Noetherian hypothesis), and the universal property of Stacks
085U gives a morphism `w : X'' ⟶ X'` over `X`. Its base change along `X' ×_X T ⟶ X'` is a
morphism over `T` between two blowups of `T` in the same centre — the base change of `b'` is
one by flat base change, the base change of `b` is one by hypothesis — hence an isomorphism, and
being an isomorphism is fppf local on the target (Stacks 041Y).

## Main results

* `AlgebraicGeometry.Space.C1573.bundledAtlasPresentation`: the presentation of an algebraic
  space by a given surjective étale chart and its kernel pair.
* `AlgebraicGeometry.Space.C1573.exists_isBlowupAlong_of_presentation_isLocallyNoetherian`: the
  blowup of an algebraic space with a locally Noetherian étale presentation in any closed
  subspace exists.
* `AlgebraicGeometry.Space.C1573.isBlowupAlong_of_isBlowupAlong_pullbackSnd`: being the blowup in
  a closed subspace is étale local on the target.

## References

* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open Stacks.Groupoids in
/-- **The presentation of an algebraic space by a given atlas** (Stacks 0263): a surjective
étale chart `a : V ⟶ X` and its kernel pair `V ×_X V`. -/
noncomputable def C1573.bundledAtlasPresentation (X : AlgebraicSpaces B S hS)
    {V : BigFppfOver B S hS}
    (a : yoneda.obj V ⟶ X.obj)
    (hasurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    Presentation B S hS X.obj X.property := by
  classical
  have hrel : MorphismProperty.relative yoneda
      (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) a := by
    simpa [MorphismProperty.presheaf] using haetale
  let hf : yoneda.relativelyRepresentable a := hrel.1
  let R := hf.pullback a
  let src : R ⟶ V := hf.snd a
  let tgt : R ⟶ V := yoneda.preimage (hf.fst a)
  have hkernel : IsPullback (yoneda.map tgt) (yoneda.map src) a a := by
    simpa [tgt, src] using hf.isPullback a
  have hsrc : PreRelation.source (prod.lift ((Over.post B.inclusion).map tgt)
      ((Over.post B.inclusion).map src)) = (Over.post B.inclusion).map src :=
    prod.lift_snd _ _
  have htgt : PreRelation.target (prod.lift ((Over.post B.inclusion).map tgt)
      ((Over.post B.inclusion).map src)) = (Over.post B.inclusion).map tgt :=
    prod.lift_fst _ _
  exact
    { U := V
      R := R
      target := tgt
      source := src
      isEtaleEquivalenceRelation :=
        { isEquivalenceRelation := by
            rw [htgt, hsrc]
            exact isEquivalenceRelation_of_isPullback B S hS a tgt src hkernel
          etale_source := by
            rw [hsrc]
            exact hrel.2 a (hf.fst a) (hf.snd a) (hf.isPullback a)
          etale_target := by
            rw [htgt]
            exact hrel.2 a (yoneda.map src) tgt (by simpa [tgt, src] using (hf.isPullback a).flip) }
      toSpace := a
      surjective := hasurj
      etale := haetale
      isPullback := hkernel }

/-- The chart of `bundledAtlasPresentation X a` is the source `V` of the atlas `a`. -/
@[simp]
theorem C1573.presentationOfAtlas_U (X : AlgebraicSpaces B S hS) {V : BigFppfOver B S hS}
    (a : yoneda.obj V ⟶ X.obj) (hasurj) (haetale) :
    (bundledAtlasPresentation X a hasurj haetale).U = V := rfl

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The blowup of an algebraic space with a locally Noetherian étale presentation exists**, in
every closed subspace. -/
theorem C1573.exists_isBlowupAlong_of_presentation_isLocallyNoetherian {X : AlgebraicSpaces B S hS}
    (P : Presentation B S hS X.obj X.property)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj P.U)]
    (Z : ClosedSubspaces B S hS X.obj) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X), IsBlowupAlong B S hS Z b := by
  have := etale_toScheme_map_presentation_source P
  have hR : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj P.R) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map P.source)
  have := etale_toScheme_map_presentationDoubleRho P
  have hRR : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (presentationDouble P)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).map (presentationDoubleFst P ≫ P.source))
  have hN := isCartesianOnAffineCharts_centreIdeal Z
  have hc := @contains_relativeProj_reesSituation_of_contains_of_isLocallyNoetherian
  exact ⟨_, _, isBlowupAlong_blowUpAlongHom' Z P
    (hc (contains_toScheme_obj _) (reesChartIdeal _ hN P))
    (hc (contains_toScheme_obj _) (reesRelationIdeal _ hN P))
    (hc (contains_toScheme_obj _) (reesDoubleIdeal _ hN P))⟩

/-- **Being the blowup in a closed subspace is étale local on the target.** Let `X` have a
locally Noetherian étale presentation, let `Z ⊆ X` be a closed subspace and let `b : X'' ⟶ X`
pull `Z` back to an effective Cartier divisor. If for one surjective étale `a : T ⟶ X` the base
change `X'' ×_X T ⟶ T` is the blowup of `T` in the inverse image of `Z`, then `b` is the blowup
of `X` in `Z`. -/
theorem C1573.isBlowupAlong_of_isBlowupAlong_pullbackSnd {X X'' T : AlgebraicSpaces B S hS}
    (P : Presentation B S hS X.obj X.property)
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj P.U)]
    (Z : ClosedSubspaces B S hS X.obj) (b : X'' ⟶ X) (hb : IsPullbackDefined B S hS b Z)
    (a : T ⟶ X) (hsurj : IsSurjective B S hS a.hom) (het : IsEtale B S hS a.hom)
    (hT : IsBlowupAlong B S hS (preimageClosedSubspace a Z) (pullback.snd b a)) :
    IsBlowupAlong B S hS Z b := by
  obtain ⟨X', b', hb'⟩ := exists_isBlowupAlong_of_presentation_isLocallyNoetherian P Z
  obtain ⟨w, hw, -⟩ := hb'.existsUnique_lift b hb
  change w ≫ b' = b at hw
  have hsq := (IsPullback.of_hasPullback b' a).flip
  have hfstE : IsEtale B S hS (pullback.fst b' a).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ hsq het
  have hfstS : IsSurjective B S hS (pullback.fst b' a).hom :=
    isSurjective_of_isPullback B S hS hsq hsurj
  have hb'T : IsBlowupAlong B S hS (preimageClosedSubspace a Z) (pullback.snd b' a) :=
    IsBlowupAlong.of_isPullback_of_isFlat hsq (isFlat_of_isEtale B S hS hfstE) Z _ rfl hb'
  have hQ := IsPullback.of_hasPullback w (pullback.fst b' a)
  have hpaste : IsPullback (pullback.fst w (pullback.fst b' a))
      (pullback.snd w (pullback.fst b' a) ≫ pullback.snd b' a) b a := by
    rw [← hw]
    exact hQ.paste_vert (IsPullback.of_hasPullback b' a)
  have hQT : IsBlowupAlong B S hS (preimageClosedSubspace a Z)
      (pullback.snd w (pullback.fst b' a) ≫ pullback.snd b' a) := by
    have h := hT.of_iso_over (hpaste.isoPullback)
    rwa [IsPullback.isoPullback_hom_snd] at h
  have hiso : IsIso (pullback.snd w (pullback.fst b' a)) :=
    (AlgebraicGeometry.Space.IsBlowupAlong.C1573.isIso_of_comp_eq (hb := hb'T)) hQT _ rfl
  have hwiso : IsIso w := by
    have key := prop_iff_pullbackSnd_of_fppf.{u, 0} B S hS (MorphismProperty.isomorphisms _) w
      (pullback.fst b' a) hfstS (isFlat_of_isEtale B S hS hfstE)
      (isLocallyOfFinitePresentation_of_isEtale B S hS hfstE)
    exact key.mpr hiso
  rw [← hw]
  exact hb'.of_iso_over (asIso w)

end AlgebraicGeometry.Space

end
