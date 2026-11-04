module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaIntegralHom

/-!
# Finite morphisms out of a locally finite coproduct

Let `q i : Y i ⟶ S` be a family of morphisms of schemes with common target. This file shows that
the induced morphism `∐ Y ⟶ S` is affine, and is finite when each `q i` is, as soon as the family
of images `Set.range (q i)` is *locally finite* in `S`: every point of `S` has a neighbourhood met
by only finitely many of them.

Some such hypothesis is needed, since neither property is local at the source: an infinite
coproduct of copies of `𝟙 S` is not affine over `S`, the preimage of a nonempty affine open being
an infinite disjoint union of nonempty affines.

## Main results

* `AlgebraicGeometry.isAffineHom_sigmaDesc_of_locallyFinite`: a locally finite coproduct of
  affine morphisms with common target is affine.
* `AlgebraicGeometry.isIntegralHom_sigmaDesc_of_locallyFinite`: a locally finite coproduct of
  integral morphisms with common target is integral.
* `AlgebraicGeometry.isFinite_sigmaDesc_of_locallyFinite`: a locally finite coproduct of finite
  morphisms with common target is finite. Since a closed immersion is finite, this covers a
  locally finite family of closed subschemes.

## Implementation notes

The quasi-compactness bridge is `AlgebraicGeometry.finite_preimage_ne_bot_of_locallyFinite`: an
affine open `U` of `S` is quasi-compact, so by `LocallyFinite.finite_nonempty_inter_compact` only
finitely many members of the family meet it, which is the local-finiteness hypothesis in the form
`AlgebraicGeometry.isIntegralHom_sigmaDesc` takes it.

Affineness is then checked over an affine open `U` of `S` directly: its preimage in `∐ Y` is the
supremum of the images `Sigma.ι Y i ''ᵁ (q i ⁻¹ᵁ U)`, which are pairwise disjoint by
`AlgebraicGeometry.disjoint_opensRange_sigmaι` and each affine, and all but finitely many empty,
so `AlgebraicGeometry.IsAffineOpen.biSup_of_disjoint` applies.

Finiteness is obtained from `AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`
rather than through properness: integrality of the coproduct morphism is
`AlgebraicGeometry.isIntegralHom_sigmaDesc`, and `LocallyOfFiniteType` is local at the source, so
it passes to the coproduct with no finiteness hypothesis at all. Its
`AlgebraicGeometry.IsZariskiLocalAtSource` instance has to be supplied with its ring-map property
explicit, since instance search does not find it with that property a metavariable.

The index type is required to live in the same universe as the schemes, where
`AlgebraicGeometry.sigmaMk` identifies the underlying space of the coproduct with the disjoint
union.

## References

* [Stacks Project, Tag 01WG](https://stacks.math.columbia.edu/tag/01WG) for finite morphisms.
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {ι : Type u} {Y : ι → Scheme.{u}} {S : Scheme.{u}} (q : ∀ i, Y i ⟶ S)

/-- A locally finite family of morphisms to `S` has only finitely many members whose preimage of
a given affine open of `S` is nonempty. -/
theorem finite_preimage_ne_bot_of_locallyFinite
    (hlf : LocallyFinite fun i ↦ Set.range (q i)) (U : S.Opens) (hU : IsAffineOpen U) :
    {i : ι | (q i ⁻¹ᵁ U) ≠ ⊥}.Finite := by
  refine (hlf.finite_nonempty_inter_compact hU.isCompact).subset fun i hi ↦ ?_
  obtain ⟨y, hy⟩ := (Opens.ne_bot_iff_nonempty (q i ⁻¹ᵁ U)).mp hi
  exact ⟨q i y, ⟨y, rfl⟩, hy⟩

/-- A coproduct of affine morphisms to a common target is affine, provided the family of images
is locally finite. -/
theorem isAffineHom_sigmaDesc_of_locallyFinite [∀ i, IsAffineHom (q i)]
    (hlf : LocallyFinite fun i ↦ Set.range (q i)) :
    IsAffineHom (Sigma.desc q) := by
  classical
  constructor
  intro U hU
  set O : ι → (∐ Y).Opens := fun i ↦ Sigma.ι Y i ''ᵁ (q i ⁻¹ᵁ U) with hO
  set s : Set ι := {i | (Set.range (q i) ∩ (U : Set S)).Nonempty} with hs
  have hfin : s.Finite := hlf.finite_nonempty_inter_compact hU.isCompact
  have haff : ∀ i, IsAffineOpen (O i) := fun i ↦
    (hU.preimage (q i)).image_of_isOpenImmersion (Sigma.ι Y i)
  have hdisj : s.Pairwise (Function.onFun Disjoint O) := fun i _ j _ hij ↦
    (disjoint_opensRange_sigmaι Y i j hij).mono
      (Scheme.Hom.image_le_opensRange _ _) (Scheme.Hom.image_le_opensRange _ _)
  have heq : Sigma.desc q ⁻¹ᵁ U = ⨆ i ∈ s, O i := by
    ext x
    obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk Y).surjective x
    simp only [Opens.coe_iSup, Set.mem_iUnion, sigmaMk_mk]
    constructor
    · intro hx
      have hy : q i y ∈ U := by simpa [← Scheme.Hom.comp_apply] using hx
      exact ⟨i, ⟨q i y, ⟨y, rfl⟩, hy⟩, ⟨y, hy, rfl⟩⟩
    · rintro ⟨j, -, y', hy', hxy⟩
      show (Sigma.desc q) (Sigma.ι Y i _) ∈ U
      rw [← hxy]
      show (Sigma.desc q) (Sigma.ι Y j y') ∈ U
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      exact hy'
  rw [heq]
  exact IsAffineOpen.biSup_of_disjoint hfin (fun i _ ↦ haff i) hdisj

/-- A coproduct of integral morphisms to a common target is integral, provided the family of
images is locally finite.

This is `AlgebraicGeometry.isIntegralHom_sigmaDesc` with its local-finiteness hypothesis in
topological form.

See [Stacks, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM) for integral morphisms. -/
theorem isIntegralHom_sigmaDesc_of_locallyFinite [∀ i, IsIntegralHom (q i)]
    (hlf : LocallyFinite fun i ↦ Set.range (q i)) :
    IsIntegralHom (Sigma.desc q) :=
  isIntegralHom_sigmaDesc q (finite_preimage_ne_bot_of_locallyFinite q hlf)

/-- A coproduct of finite morphisms to a common target is finite, provided the family of images
is locally finite: every point of the target has a neighbourhood met by only finitely many of
them.

Since a closed immersion is finite, this applies to a locally finite family of closed subschemes
of a scheme.

See [Stacks, Tag 01WG](https://stacks.math.columbia.edu/tag/01WG) for finite morphisms. -/
theorem isFinite_sigmaDesc_of_locallyFinite [∀ i, IsFinite (q i)]
    (hlf : LocallyFinite fun i ↦ Set.range (q i)) :
    IsFinite (Sigma.desc q) := by
  have hint : IsIntegralHom (Sigma.desc q) := isIntegralHom_sigmaDesc_of_locallyFinite q hlf
  have hlocal : IsZariskiLocalAtSource @LocallyOfFiniteType :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  have hft : LocallyOfFiniteType (Sigma.desc q) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) fun i ↦ inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨hint, hft⟩

end AlgebraicGeometry

end
