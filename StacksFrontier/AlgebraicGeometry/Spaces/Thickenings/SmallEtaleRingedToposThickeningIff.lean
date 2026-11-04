module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleRingedToposChartSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleRingedToposThickeningConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesAffineDensity

/-!
# Thickenings of algebraic spaces are the thickenings of their small étale ringed topoi

**Stacks 0D16.** Let `S` be a scheme and `i : Z ⟶ Z'` a morphism of algebraic spaces over `S`.
Then `i` is a thickening of algebraic spaces (Stacks 05ZJ, in the morphism form
`AlgebraicGeometry.Space.IsThickeningHom`) if and only if the morphism of small étale ringed topoi
`i_small : (Sh(Z_étale), 𝒪_Z) ⟶ (Sh(Z'_étale), 𝒪_{Z'})` of Stacks 03G8 is a thickening of ringed
topoi in the sense of Stacks 08M6 (`Deformation.ToposThickening.IsThickening`: the direct image is
an equivalence of topoi and the structure map is surjective with locally nilpotent kernel).

(1) ⇒ (2) is `AlgebraicGeometry.Space.isThickening_smallEtaleRingedToposHom_of_isThickeningHom`.

(2) ⇒ (1).  The source's proof shows that `i` is affine using Serre's criterion (Stacks 07V6),
remarking that a proof avoiding it surely exists; this file gives one.  The morphism of reductions
`c : Z_red ⟶ Z'_red` is an isomorphism of small étale ringed topoi, hence an isomorphism of
algebraic spaces (`AlgebraicGeometry.Space.isIso_spaceReductionMap_of_isThickening`, which rests
on Stacks 04KL over a base).  So over an affine scheme `T ⟶ Z'` the base change of `i` has an
affine thickening, the base change of `Z'_red`, and is therefore affine: `i` is affine
(`AlgebraicGeometry.Space.isAffineHom_of_isIso_spaceReductionMap`).  Over an affine étale chart
`V` of `Z'` the structure map is then a surjection `Γ(V) ⟶ Γ(Z ×_{Z'} V)` by faithfully flat
descent (`AlgebraicGeometry.Space.surjective_appTop_snd_of_isLocallySurjective_fSharp`), so the
base change of `i` over `V` is a closed immersion of affine schemes, and it is surjective because
`i` is (`Z'_red ⟶ Z'` factors through `i`).  Being a thickening is local on the target for the
étale topology (Stacks 0BPI), and the affine étale charts of `Z'` cover it.

## Main results

* `AlgebraicGeometry.Space.isThickeningHom_of_isThickening_smallEtaleRingedToposHom`:
  (2) ⇒ (1).
* `AlgebraicGeometry.Space.isThickeningHom_iff_isThickening_smallEtaleRingedToposHom`:
  **Stacks 0D16**.

## References

* [Stacks Project, Tag 0D16](https://stacks.math.columbia.edu/tag/0D16)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 08M6](https://stacks.math.columbia.edu/tag/08M6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism whose small étale ringed topos morphism is a thickening is surjective on points:
the thickening `Z'_red ⟶ Z'` factors through it. -/
theorem isSurjective_of_isThickening_smallEtaleRingedToposHom {Z Z' : AlgebraicSpaces B S hS}
    {i : Z ⟶ Z'} (hi : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i)) :
    IsSurjective B S hS i.hom := by
  have hc := isIso_spaceReductionMap_of_isThickening hi
  have heq : spaceReductionι Z' = inv (spaceReductionMap i) ≫ spaceReductionι Z ≫ i := by
    rw [← spaceReductionMap_comp i, IsIso.inv_hom_id_assoc]
  have h := (isThickeningHom_spaceReductionι Z').surjective_pointsMap
  rw [heq] at h
  change Function.Surjective (pointsMap B S hS _
    ((inv (spaceReductionMap i) ≫ spaceReductionι Z).hom ≫ i.hom)) at h
  rw [pointsMap_comp] at h
  exact h.of_comp

/-- Over an affine étale chart of the target, the base change of a morphism whose small étale
ringed topos morphism is a thickening is a thickening. -/
theorem isThickeningHom_pullback_snd_of_isThickening {Z Z' : AlgebraicSpaces B S hS}
    {i : Z ⟶ Z'} (hi : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i))
    {W : BigFppfOver B S hS} [hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (b : yoneda.obj W ⟶ Z'.1) (hb : IsEtale B S hS b) :
    IsThickeningHom B S hS (pullback.snd i (ObjectProperty.homMk b : schemeSpace W ⟶ Z')) := by
  rw [isThickeningHom_iff_isClosedImmersion_and_isSurjective]
  have hc := isIso_spaceReductionMap_of_isThickening hi
  have hpre := presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS Z.2 Z'.2
    (isAffineHom_of_isIso_spaceReductionMap i hc)
  have haff : ∀ V : SmallEtale B S hS Z'.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj (hpre.1.pullback V.obj.hom)) := by
    intro V hV
    have := hV
    have : AlgebraicGeometry.IsAffineHom
        ((BigFppfOver.toScheme B S hS).map (hpre.1.snd V.obj.hom)) := hpre.2.property_snd _
    exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (hpre.1.snd V.obj.hom))
  let V : SmallEtale B S hS Z'.1 :=
    ⟨CostructuredArrow.mk b, (isEtale_iff_presheaf_of_yoneda B S hS b).1 hb⟩
  have hsurjV := surjective_appTop_snd_of_isLocallySurjective_fSharp i hpre.1 hi.2.1 haff V hW
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hpre.1.pullback b)) := haff V hW
  have hciS : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hpre.1.snd b)) :=
    AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine _ hsurjV
  have hpb := IsPullback.of_hasPullback i (ObjectProperty.homMk b : schemeSpace W ⟶ Z')
  have sq := AlgebraicSpaces.isPullback_hom B S hS hpb
  have sq' := hpre.1.isPullback b
  refine ⟨?_, ?_⟩
  · have h1 : IsClosedImmersion B S hS (yoneda.map (hpre.1.snd b)) :=
      (presheaf_yoneda_map_iff B S hS (P := @AlgebraicGeometry.IsClosedImmersion.{u})
        inferInstance (hpre.1.snd b)).2 hciS
    have he := sq.isoIsPullback_hom_snd _ _ sq'
    rw [← he]
    let Q := MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    let _ : Q.RespectsIso := inferInstance
    exact MorphismProperty.RespectsIso.precomp Q _ _ h1
  · exact (surjectiveMorphismProperty B S hS).of_isPullback hpb
      (isSurjective_of_isThickening_smallEtaleRingedToposHom hi)

/-- **Stacks 0D16, (2) ⇒ (1).**  If the morphism of small étale ringed topoi of `i` is a
thickening of ringed topoi, then `i` is a thickening of algebraic spaces. -/
theorem isThickeningHom_of_isThickening_smallEtaleRingedToposHom {Z Z' : AlgebraicSpaces B S hS}
    {i : Z ⟶ Z'} (hi : Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i)) :
    IsThickeningHom B S hS i := by
  obtain ⟨W, b, hWaff, hbEt, -, hcov⟩ := exists_isEtaleCovering_affine B S hS Z'.1 Z'.2
  rw [isThickeningHom_iff_of_isFpqcCovering B S hS i (fun x => schemeSpace (W x))
    (fun x => (ObjectProperty.homMk (b x) : schemeSpace (W x) ⟶ Z'))
    (isFpqcCovering_of_isEtaleCovering B S hS _ _ hcov)]
  intro x
  have := hWaff x
  exact isThickeningHom_pullback_snd_of_isThickening hi (b x) (hbEt x)

/-- **Stacks 0D16.**  Let `S` be a scheme and `i : Z ⟶ Z'` a morphism of algebraic spaces over
`S`.  Then `i` is a thickening of algebraic spaces (Stacks 05ZJ, Definition 05ZK: a closed
immersion identifying `Z` with a closed subspace of `Z'` having the same points, here in the
morphism form `AlgebraicGeometry.Space.IsThickeningHom`) if and only if the associated morphism
`i_small : (Sh(Z_étale), 𝒪_Z) ⟶ (Sh(Z'_étale), 𝒪_{Z'})` of ringed topoi (Stacks 03G8,
`AlgebraicGeometry.Space.smallEtaleRingedToposHom`) is a thickening in the sense of Stacks 08M6
(`Deformation.ToposThickening.IsThickening`). -/
@[stacks 0D16]
theorem isThickeningHom_iff_isThickening_smallEtaleRingedToposHom
    {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z') :
    IsThickeningHom B S hS i ↔
      Deformation.ToposThickening.IsThickening.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS i) :=
  ⟨isThickening_smallEtaleRingedToposHom_of_isThickeningHom,
    isThickeningHom_of_isThickening_smallEtaleRingedToposHom⟩

end AlgebraicGeometry.Space

end
