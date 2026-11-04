module

public import Mathlib.CategoryTheory.Generator.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.CardinalGeneratedSmall
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Grothendieck
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.GabberSubmodule

/-!
# Quasi-coherent modules on a scheme form a Grothendieck abelian category

For a scheme `X`, the abelian category `QCoh(𝒪_X)` of quasi-coherent `𝒪_X`-modules has a
separator, and is therefore a Grothendieck abelian category.  This is the second assertion of
[Stacks, Tag 077P].

## Main results

* `AlgebraicGeometry.quasicoherent_hasSeparator`: `QCoh(𝒪_X)` has a separator.
* `AlgebraicGeometry.quasicoherentModules_isGrothendieckAbelian`: the Grothendieck property.

## Implementation notes

The three axioms other than the separator — local smallness, filtered colimits and their
exactness — are
`AlgebraicGeometry.quasicoherentModules_isGrothendieckAbelian_of_hasSeparator`, which reduces
the tag to the separator; all that is added here is the separator.

The separating family is the quasi-coherent, `cardinalBound X`-generated modules.  It is
essentially small by [Stacks, Tag 077M]
(`AlgebraicGeometry.CardinalGenerated.essentiallySmall_isCardinalGenerated`) and it is
separating by `Stacks.AlgebraicGeometry.Coherator.exists_isCardinalGenerated_mem`: every local
section of a quasi-coherent module `A` is the image of a section of such a submodule of `A`, so
two morphisms out of `A` which agree after composition with every map from the family agree on
every section.  A coproduct of a small set of representatives is then a separator, by
`CategoryTheory.isSeparator_sigma`.

Note that the family is shown to be separating *without* the colimit assertion of
[Stacks, Tag 077N]: `CategoryTheory.ObjectProperty.IsSeparating` asks only that the maps from
the family into an object be jointly epimorphic in the weak sense of its definition, which is a
statement about sections, not about a diagram.  Tag 077N — that the bounded quasi-coherent
subobjects form a filtered system whose canonical cocone is colimiting — is still open, and no
attribute for it is carried here.

## References

* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
* [Stacks Project, Tag 077M](https://stacks.math.columbia.edu/tag/077M)
* [Stacks Project, Tag 077L](https://stacks.math.columbia.edu/tag/077L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.CardinalGeneration
open Stacks.AlgebraicGeometry.Coherator

universe u

namespace AlgebraicGeometry

/-- **The quasi-coherent modules on a scheme have a separator.**

The quasi-coherent, `cardinalBound X`-generated modules form an essentially small family by
[Stacks, Tag 077M], and that family is separating: by
`Stacks.AlgebraicGeometry.Coherator.exists_isCardinalGenerated_mem` every local section of a
quasi-coherent module `A` is the image of a section of such a submodule of `A`, so two
morphisms out of `A` which agree after composition with all maps from the family agree on
every section.  A coproduct of a small set of representatives is a separator. -/
theorem quasicoherent_hasSeparator (X : Scheme.{u}) :
    HasSeparator (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory := by
  classical
  let C := (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory
  let P : ObjectProperty (X.Modules) := fun M ↦
    M.IsQuasicoherent ∧
      SheafOfModules.IsCardinalGenerated (R := X.ringCatSheaf) M (cardinalBound X)
  let G : ObjectProperty (X.Modules) := fun M ↦
    SheafOfModules.IsCardinalGenerated (R := X.ringCatSheaf) M (cardinalBound X)
  have : ObjectProperty.EssentiallySmall.{u} G :=
    AlgebraicGeometry.CardinalGenerated.essentiallySmall_isCardinalGenerated
      (X.toLocallyRingedSpace.toRingedSpace) (cardinalBound X)
  have : ObjectProperty.EssentiallySmall.{u} P :=
    ObjectProperty.EssentiallySmall.of_le (P := P) (Q := G) fun _ hM ↦ hM.2
  obtain ⟨Q, hQsmall, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u} P
  let Qc : ObjectProperty C := fun M ↦ Q M.obj
  have hQcSmall : ObjectProperty.Small.{u} Qc := by
    apply small_of_injective (f := fun M : Subtype Qc ↦ (⟨M.1.obj, M.2⟩ : Subtype Q))
    intro M N h
    apply Subtype.ext
    apply ObjectProperty.FullSubcategory.ext
    exact congrArg Subtype.val h
  let P' : ObjectProperty C := fun M ↦ P M.obj
  have hP'sep : P'.IsSeparating := by
    intro A B f g hfg
    refine ObjectProperty.hom_ext _ (Scheme.Modules.hom_ext _ _ fun U ↦ ?_)
    ext z
    obtain ⟨H, hHqc, hHcard, φ, -, w, hw⟩ := exists_isCardinalGenerated_mem A.obj z
    have hcomp := hfg ⟨H, hHqc⟩ ⟨hHqc, hHcard⟩
      (ObjectProperty.homMk (P := SheafOfModules.isQuasicoherent X.ringCatSheaf) φ)
    have hcomp' := congrArg (fun t : (⟨H, hHqc⟩ : C) ⟶ B ↦ t.hom) hcomp
    have hw' := congrArg (fun t : H ⟶ B.obj ↦ t.app U w) hcomp'
    subst hw
    exact hw'
  have hRsep : (Qc.isoClosure).IsSeparating :=
    ObjectProperty.IsSeparating.of_le hP'sep (by
      intro M hM
      obtain ⟨Y, hY, ⟨e⟩⟩ := hPQ M.obj hM
      exact ⟨⟨Y, (hQP Y hY).1⟩, hY,
        ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).isoMk e⟩⟩)
  let β := Shrink.{u} (Subtype Qc)
  let f : β → C := fun b ↦ ((equivShrink.{u} (Subtype Qc)).symm b).1
  have hQcSep : Qc.IsSeparating := by
    intro A B f g hfg
    apply hRsep f g
    intro Y hY k
    rcases hY with ⟨Z, hZ, ⟨e⟩⟩
    have h := hfg Z hZ (e.inv ≫ k)
    simpa [Category.assoc] using congrArg (fun t ↦ e.hom ≫ t) h
  have hOf : Qc ≤ ObjectProperty.ofObj f := by
    intro A hA
    apply (ObjectProperty.ofObj_iff f A).2
    refine ⟨equivShrink.{u} (Subtype Qc) ⟨A, hA⟩, ?_⟩
    simp [f]
  have : HasColimitsOfShape (Discrete β) (X.Modules) := inferInstance
  have : HasCoproduct f := by infer_instance
  exact ⟨∐ f, (isSeparator_sigma f).2 (ObjectProperty.IsSeparating.of_le hQcSep hOf)⟩

/-- **The category of quasi-coherent modules on a scheme is Grothendieck abelian.**  This is
the second assertion of [Stacks, Tag 077P]: the separator above together with the reduction
`AlgebraicGeometry.quasicoherentModules_isGrothendieckAbelian_of_hasSeparator`. -/
@[stacks 077P "grothendieck_qcoh"]
instance quasicoherentModules_isGrothendieckAbelian (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u}
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  have := quasicoherent_hasSeparator X
  quasicoherentModules_isGrothendieckAbelian_of_hasSeparator X

end AlgebraicGeometry

end
