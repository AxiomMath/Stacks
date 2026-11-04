module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionSpaceQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The projection onto the quotient of a free action is surjective and étale

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `G` be an abstract group
acting freely on `X` by a natural pointwise action.  Tag 071S says that the quotient sheaf
`X/G` is again an algebraic space; this file adds that the projection `q : X ⟶ X/G` is
*surjective and étale*.

The argument is the one that proves Tag 071S, read one step further.  At a surjective étale
chart `φ : U ⟶ X` the relation `R = ∐_{g ∈ G} U ×_{φ, X, g • φ} U` is the kernel pair of the
composite `U ⟶ X/G`, and both `U ⟶ X/G` and `U ⟶ U/R` are the coequalizer of the two
projections of `R`; so `X/G ≅ U/R` compatibly with the two maps out of `U`.  The quotient map
of an étale equivalence relation is surjective and étale by Tag 02WW, hence so is `U ⟶ X/G`,
and the projection `X ⟶ X/G` inherits both properties from it by Tag 0AHD, `φ` being
surjective and étale.

## Main results

* `AlgebraicGeometry.Space.isChartSurjective_and_isChartEtale_twistQuotientChart`: the composite
  `U ⟶ X ⟶ X/G` of a surjective étale chart with the projection is surjective and étale after
  every representable base change.
* `AlgebraicGeometry.Space.isSurjective_toOrbitQuotient` and
  `AlgebraicGeometry.Space.isEtale_toOrbitQuotient`: the projection `X ⟶ X/G` is surjective
  and étale.

## Implementation notes

The comparison `U/R ≅ X/G` is not exported: it depends on the chart, while the two conclusions
about `X ⟶ X/G` do not.  It is built inside
`AlgebraicGeometry.Space.isChartSurjective_and_isChartEtale_twistQuotientChart` from the two
coforks, exactly as in the proof of Tag 071S, and used only to transport the two conclusions of
Tag 02WW across.

Freeness is `AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`, as in Tag 071S: freeness on the
points over the test objects whose underlying scheme is nonempty.  Asking for a cancellative
action over every test object would force `G` to be trivial.

This module is deliberately self-contained and narrow: it is the one fact about a free quotient
that the sign-twist development of Section 69.6 needs and that Tag 071S stops just short of.

## References

* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Type u} [Group G]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [∀ T, MulAction G (X.obj T)]
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- The composite `U ⟶ X ⟶ X/G` of a surjective étale chart with the projection is locally
surjective. -/
private theorem isLocallySurjective_twistQuotientChart
    (hnat : IsNaturalAction B S hS G X) {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hsurj : IsChartSurjective φ) (hetale : IsChartEtale φ) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (twistQuotientChart hnat φ) := by
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) φ :=
    isLocallySurjective_of_surjective_etale B S hS φ hsurj hetale
  have := isLocallySurjective_toOrbitQuotient B S hS G X hnat
  exact Presheaf.isLocallySurjective_comp (BigFppfOver.topology B S hS) φ
    (toOrbitQuotient B S hS G X hnat)

/-- **The quotient `X/G` is the quotient of a chart by the relation of Tag 071S**, compatibly
with the two maps out of the chart: both `U ⟶ X/G` and `U ⟶ U/R` are the coequalizer of the
two projections of `R`, so the unique comparison between the two targets carries one to the
other. -/
theorem isChartSurjective_and_isChartEtale_twistQuotientChart
    (hnat : IsNaturalAction B S hS G X)
    (hfree : IsFreeOnNonemptyPoints B S hS G X)
    {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)
    (hrep : yoneda.relativelyRepresentable φ)
    (hsurj : IsChartSurjective φ) (hetale : IsChartEtale φ) :
    IsChartSurjective (twistQuotientChart hnat φ) ∧
      IsChartEtale (twistQuotientChart hnat φ) := by
  set s := twistRelationSource hnat φ hrep hfree
  set t := twistRelationTarget hnat φ hrep hfree
  have : IsEtaleEquivalenceRelation (relation B S hS s t) :=
    isEtaleEquivalenceRelation_twistRelation hnat φ hrep hfree hetale
  let RF : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj (twistRelation hnat φ hrep hfree), BigFppfOver.isSheaf_yoneda_obj B S hS _⟩
  let UF : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj U, BigFppfOver.isSheaf_yoneda_obj B S hS U⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let qf : UF ⟶ orbitQuotientSheaf B S hS G X hnat := ⟨twistQuotientChart hnat φ⟩
  let pf : UF ⟶ Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t) := ⟨quotientMap B S hS s t⟩
  have hsq := isPullback_twistRelation hnat φ hrep hfree
  have hsq' := quotientMap_isPullback B S hS s t
  have hcq := Sheaf.isColimitCoforkOfKernelPair tf sf qf (Sheaf.hom_ext hsq.w)
    (fun V x y hxy => Limits.Types.exists_of_isPullback (hsq.app (Opposite.op V)) x y hxy)
    (isLocallySurjective_twistQuotientChart hnat φ hsurj hetale)
  have hcp := Sheaf.isColimitCoforkOfKernelPair tf sf pf (Sheaf.hom_ext hsq'.w)
    (fun V x y hxy => Limits.Types.exists_of_isPullback (hsq'.app (Opposite.op V)) x y hxy)
    (isLocallySurjective_of_surjective_etale B S hS _
      (quotientMap_surjective_unconditional B S hS s t)
      (quotientMap_etale_unconditional B S hS s t))
  let e := IsColimit.coconePointUniqueUpToIso hcp hcq
  have hfac : pf ≫ e.hom = qf := by
    simpa using IsColimit.comp_coconePointUniqueUpToIso_hom hcp hcq WalkingParallelPair.one
  have hfac' : quotientMap B S hS s t ≫ e.hom.hom = twistQuotientChart hnat φ := by
    simpa using congrArg (fun z : UF ⟶ orbitQuotientSheaf B S hS G X hnat => z.hom) hfac
  rw [← hfac']
  exact ⟨MorphismProperty.RespectsIso.postcomp
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      e.hom.hom _ (quotientMap_surjective_unconditional B S hS s t),
    MorphismProperty.RespectsIso.postcomp
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      e.hom.hom _ (quotientMap_etale_unconditional B S hS s t)⟩

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- A morphism from a representable presheaf to an algebraic space is relatively
representable, the diagonal of an algebraic space being representable. -/
theorem relativelyRepresentable_of_isAlgebraicSpace_target
    (hX : IsAlgebraicSpace B S hS X) {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X) :
    yoneda.relativelyRepresentable φ := by
  have hall : ∀ (V : BigFppfOver B S hS) (ξ : X.obj (Opposite.op V)),
      yoneda.relativelyRepresentable (yonedaEquiv.symm ξ) :=
    ((yoneda_relativelyRepresentable_diag_tfae_bigFppfOver B S hS X).out 1 2).mp
      hX.diagonal_representable
  simpa using hall U (yonedaEquiv φ)

/-- **The projection onto the quotient of a free action is surjective.** A surjective étale
chart of `X` composed with the projection is surjective, by Tag 02WW through the comparison of
`X/G` with the quotient of the chart by the relation of Tag 071S, so the projection itself is
surjective on points. -/
theorem isSurjective_toOrbitQuotient
    (hnat : IsNaturalAction B S hS G X) (hX : IsAlgebraicSpace B S hS X)
    (hfree : IsFreeOnNonemptyPoints B S hS G X) :
    IsSurjective B S hS (toOrbitQuotient B S hS G X hnat) := by
  obtain ⟨U, φ, hsurj, hetale⟩ := hX.exists_atlas
  have hcomp : Function.Surjective (pointsMap B S hS (yoneda.obj U)
      (φ ≫ toOrbitQuotient B S hS G X hnat)) :=
    isSurjective_of_presheafSurjective B S hS _
      (isChartSurjective_and_isChartEtale_twistQuotientChart hnat hfree φ
        (relativelyRepresentable_of_isAlgebraicSpace_target hX φ) hsurj hetale).1
  rw [pointsMap_comp] at hcomp
  exact hcomp.of_comp

/-- **The projection onto the quotient of a free action is étale.** A surjective étale chart of
`X` composed with the projection is étale, by Tag 02WW through the comparison of `X/G` with the
quotient of the chart by the relation of Tag 071S; the projection itself is then étale by
Tag 0AHD, the chart being surjective and étale. -/
theorem isEtale_toOrbitQuotient
    (hnat : IsNaturalAction B S hS G X) (hX : IsAlgebraicSpace B S hS X)
    (hfree : IsFreeOnNonemptyPoints B S hS G X) :
    IsEtale B S hS (toOrbitQuotient B S hS G X hnat) := by
  obtain ⟨U, φ, hsurj, hetale⟩ := hX.exists_atlas
  exact isEtale_of_comp_surjective_isEtale B S hS (isAlgebraicSpace_yoneda B S hS U) hX
    (isAlgebraicSpace_orbitQuotientSheaf_of_isFreeOnNonemptyPoints hnat hX hfree) φ
    (φ ≫ toOrbitQuotient B S hS G X hnat) (toOrbitQuotient B S hS G X hnat) rfl
    (isSurjective_of_presheafSurjective B S hS _ hsurj)
    (isEtale_of_presheaf_etale B S hS hetale)
    (isEtale_of_presheaf_etale B S hS
      (isChartSurjective_and_isChartEtale_twistQuotientChart hnat hfree φ
        (relativelyRepresentable_of_isAlgebraicSpace_target hX φ) hsurj hetale).2)

end AlgebraicGeometry.Space

end
