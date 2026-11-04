module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Defs
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteSchemeDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber

/-!
# Quasi-compact separated étale descent along a flat surjective quasi-compact morphism

Along a surjective flat quasi-compact morphism `f : X ⟶ S` every descent datum whose
underlying `X`-scheme is separated and locally quasi-finite is effective; this is
[Stacks, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8). A descended scheme of such a
datum then has every property of morphisms which is fpqc local on the base and holds for the
underlying scheme of the datum, because the one-member family `{f}` is an fpqc covering. Applied to
étaleness, quasi-compactness and separatedness this gives
`AlgebraicGeometry.QcSepEtaleEffective` for a surjective flat quasi-compact morphism, together
with the two further properties of the descended scheme.

## Main results

* `AlgebraicGeometry.DescentDatum.Descended.property_base_hom_of_flat`: the descended scheme of
  a datum along a surjective flat quasi-compact morphism has every fpqc-local property of the
  underlying scheme of the datum.
* `AlgebraicGeometry.qcSepEtaleEffective_of_flat`: **quasi-compact separated étale descent data
  are effective along a surjective flat quasi-compact morphism.**
* `AlgebraicGeometry.exists_descended_etale_quasiCompact_isSeparated_of_flat`: the same, with
  the descended scheme recorded as quasi-compact and separated over the base as well.

## Implementation notes

The effectivity input is
`AlgebraicGeometry.DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite`, whose hypotheses
are separatedness, local quasi-finiteness and local finite type of the underlying scheme; an étale
morphism has the last two, so only separatedness is a real hypothesis, and quasi-compactness of the
underlying scheme is not needed for effectivity, only for the descended scheme to be
quasi-compact over the base.

The transport of a property from the underlying scheme to the descended scheme uses
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd` for the fpqc precoverage
against the one-member covering `AlgebraicGeometry.Scheme.Hom.singleton_mem_fpqcPrecoverage`, and
then the pullback square of the descended scheme to identify that single base change with the
underlying scheme of the datum.

## References

* [Stacks Project, Tag 02KQ](https://stacks.math.columbia.edu/tag/02KQ)
* [Stacks Project, Tag 02KU](https://stacks.math.columbia.edu/tag/02KU)
* [Stacks Project, Tag 02VN](https://stacks.math.columbia.edu/tag/02VN)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

variable {S X : Scheme.{u}}

namespace DescentDatum

/-- **A descended scheme inherits every fpqc-local property of the underlying scheme of the
datum**, along a surjective flat quasi-compact morphism. -/
theorem Descended.property_base_hom_of_flat {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.fpqcPrecoverage] {f : X ⟶ S} [Surjective f] [Flat f]
    [QuasiCompact f] {D : DescentDatum f} (Q : D.Descended) (hP : P D.over.hom) :
    P Q.base.hom := by
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    f.singleton_mem_fpqcPrecoverage ?_
  rintro U g _ ⟨⟩
  rw [← Q.isPullback.flip.isoPullback_hom_snd] at hP
  exact (P.cancel_left_of_respectsIso _ _).mp hP

end DescentDatum

/-- **A separated étale descent datum along a surjective flat quasi-compact morphism carries a
descended scheme which is étale over the base**, and which is quasi-compact and separated over
the base as soon as the datum's underlying scheme is. -/
theorem exists_descended_etale_quasiCompact_isSeparated_of_flat (f : X ⟶ S) [Surjective f]
    [Flat f] [QuasiCompact f] (D : DescentDatum f) (hD : Etale D.over.hom)
    (hqc : QuasiCompact D.over.hom) (hsep : IsSeparated D.over.hom) :
    ∃ Q : D.Descended, Etale Q.base.hom ∧ QuasiCompact Q.base.hom ∧ IsSeparated Q.base.hom := by
  have := hD
  obtain ⟨Q⟩ := DescentDatum.nonempty_descended_of_isEffective
    (DescentDatum.isEffective_of_isSeparated_of_locallyQuasiFinite D hsep inferInstance
      inferInstance)
  exact ⟨Q, Q.property_base_hom_of_flat (P := @Etale) hD,
    Q.property_base_hom_of_flat (P := @QuasiCompact) hqc,
    Q.property_base_hom_of_flat (P := @IsSeparated) hsep⟩

/-- **Quasi-compact separated étale descent data are effective along a surjective flat
quasi-compact morphism.** -/
theorem qcSepEtaleEffective_of_flat (f : X ⟶ S) [Surjective f] [Flat f] [QuasiCompact f] :
    QcSepEtaleEffective f := fun D hD hqc hsep =>
  (exists_descended_etale_quasiCompact_isSeparated_of_flat f D hD hqc hsep).imp fun _ h => h.1

end AlgebraicGeometry

end
