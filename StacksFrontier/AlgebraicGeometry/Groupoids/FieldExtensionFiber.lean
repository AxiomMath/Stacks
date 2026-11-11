module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# Homogeneity of a groupoid scheme over a field

For a groupoid scheme whose object scheme is the spectrum of a field `k`, any two points of its
arrow scheme are carried to one another, after extending `k`, by an isomorphism between two base
changes of the arrow scheme along the source map.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.Groupoids.GroupoidScheme.exists_fieldExtension_sourceFiber_iso_mapping_points` gives
  the field extension, the two lifted points, and the isomorphism carrying one to the other.

## Implementation notes

The identification of the object scheme with `Spec k` is expressed by an isomorphism, and the
source fibre after extension to `k'` is represented by a scheme pullback equipped with its
canonical object of the over-category of `Spec k'`; so the isomorphism in the conclusion is
literally an isomorphism over `Spec k'`.

Tag 04LP is declared in the source to be the special case `U = Spec k` of parts (1) and (2) of
Tag 02YF, and that is what is proved here.  Tag 02YF produces a field `k'` carrying *two*
embeddings of the residue field of the base point — one induced by the target map and one by the
source map of a chosen arrow — and an isomorphism between the two corresponding base changes.
The displayed diagram of 04LP writes both base changes as `R ×_{s, Spec k} Spec k'`, which
tacitly identifies the two embeddings; since `U` has a single point both embeddings are
`k`-algebra structures on `k'`, but the argument of 02YF does not make them equal, so the two
base changes are kept apart here and the conclusion is an isomorphism between them rather than
an automorphism of one.

This is the corrected form of Tag 04LP.  As printed, with one base change on both sides, the
statement is false: `Stacks.Groupoids.not_groupoidOnFieldHomogeneousStatement` refutes it with
the coarse groupoid of `Spec ℚ(T)` over `Spec ℚ` (see
`StacksFrontier/AlgebraicGeometry/Groupoids/FieldExtensionCounterexample.lean`).

The chosen arrow is obtained from the upper cartesian square of the composition diagram
(Tag 02YE): its first projection is the first point and its composite is the second.  The two
base changes are then exhibited by pasting the pullback square of the second projection along
`Spec k' ⟶ R` onto the two lower cartesian squares, which avoids the scheme-theoretic fibre
machinery entirely: the fibre of the source map over the unique point of `U` is all of `R`.

## References

* [Stacks Project, Tag 02YE](https://stacks.math.columbia.edu/tag/02YE)
* [Stacks Project, Tag 02YF](https://stacks.math.columbia.edu/tag/02YF)
* [Stacks Project, Tag 04LP](https://stacks.math.columbia.edu/tag/04LP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids.GroupoidScheme

/-- A cartesian square stays cartesian after composing both maps into the corner with a
monomorphism. -/
private alias isPullback_comp_mono := CategoryTheory.isPullback_comp_mono

/-- A cartesian square over `Spec K` whose corner is identified with `Spec k` stays cartesian
along the `k`-algebra structure on `K` induced by the composite map `Spec K ⟶ Spec k`. -/
private theorem exists_algebra_isPullback_spec_map {k K : Type u} [Field k] [Field K]
    {P X Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Spec (.of K)} {f : X ⟶ Z}
    {g : Spec (.of K) ⟶ Z} (e : Z ≅ Spec (.of k)) (h : IsPullback fst snd f g) :
    ∃ γ : Algebra k K, IsPullback fst snd (f ≫ e.hom)
      (Spec.map (CommRingCat.ofHom (@algebraMap k K _ _ γ))) := by
  refine ⟨(Spec.preimage (g ≫ e.hom)).hom.toAlgebra, ?_⟩
  convert isPullback_comp_mono h e.hom
  exact Spec.map_preimage (g ≫ e.hom)

/-- If the object scheme of a groupoid scheme is the spectrum of a field `k`, then any two
points of its arrow scheme lift, after a field extension `k'/k`, to points of two base changes
of the arrow scheme along the source map which are carried to one another by an isomorphism
over `Spec k'`.

The two base changes are taken along the two `k`-algebra structures on `k'` that Tag 02YF
produces, namely the ones induced by the target and by the source of a chosen arrow.  This is
the corrected form of Tag 04LP: the printed form, an automorphism of a single base change, is
false (`Stacks.Groupoids.not_groupoidOnFieldHomogeneousStatement`). -/
@[stacks 04LP "corrected form: the printed statement, with one base change on both sides of the
isomorphism, is false (refuted by Stacks.Groupoids.not_groupoidOnFieldHomogeneousStatement);
this is what its proof via 02YF (1), (2) establishes, with two embeddings of k into k'"]
theorem exists_fieldExtension_sourceFiber_iso_mapping_points
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (e : G.objects.left ≅ Spec (.of k))
    (r r' : G.arrows.left) :
    let s : G.arrows.left ⟶ Spec (.of k) := G.source.left ≫ e.hom
    ∃ (k' : Type u) (_ : Field k') (α β : Algebra k k'),
      let gt : Spec (.of k') ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (@algebraMap k k' _ _ α))
      let gs : Spec (.of k') ⟶ Spec (.of k) :=
        Spec.map (CommRingCat.ofHom (@algebraMap k k' _ _ β))
      let P : Scheme.{u} := pullback s gt
      let P' : Scheme.{u} := pullback s gs
      let POver : Over (Spec (.of k')) := Over.mk (pullback.snd s gt)
      let POver' : Over (Spec (.of k')) := Over.mk (pullback.snd s gs)
      ∃ (r₁ : P) (r₂ : P') (φ : POver ≅ POver'),
        φ.hom.left.base r₁ = r₂ ∧
          (pullback.fst s gt).base r₁ = r ∧
          (pullback.fst s gs).base r₂ = r' := by
  intro s
  rw [show s = G.source.left ≫ e.hom from rfl]
  -- Since `G.objects.left` has a single point, the two arrows have the same target.
  have ht : G.target.left.base r = G.target.left.base r' := by
    have h1 : e.hom.base (G.target.left.base r) = e.hom.base (G.target.left.base r') :=
      Subsingleton.elim _ _
    have h2 : ((G.target.left ≫ e.hom) ≫ e.inv).base r =
        ((G.target.left ≫ e.hom) ≫ e.inv).base r' := by
      simp only [Scheme.Hom.comp_apply]
      exact congrArg _ h1
    rwa [Category.assoc, e.hom_inv_id, Category.comp_id] at h2
  -- The upper cartesian square of the composition diagram supplies a composable pair whose
  -- first projection is `r` and whose composite is `r'`.
  have hupper : IsPullback (pullback.fst G.source G.target).left G.comp.left
      G.target.left G.target.left := by
    simpa using (target_comp_isPullback G).map (Over.forget S)
  obtain ⟨ξ, hfst, hcomp⟩ := Scheme.exists_preimage_of_isPullback hupper r r' ht
  -- Its second projection is the arrow `q` through which the comparison is made.
  set pr₁ := (pullback.snd G.source G.target).left
  set q : G.arrows.left := pr₁.base ξ
  set w : Spec (G.arrows.left.residueField q) ⟶ G.arrows.left :=
    G.arrows.left.fromSpecResidueField q with hwdef
  -- The two lower cartesian squares, pasted with the pullback of `pr₁` along `w`.
  have hA : IsPullback (pullback.fst G.source G.target).left pr₁
      G.source.left G.target.left := by
    simpa using (IsPullback.of_hasPullback G.source G.target).map (Over.forget S)
  have hB : IsPullback G.comp.left pr₁ G.source.left G.source.left := by
    simpa using (comp_source_isPullback G).map (Over.forget S)
  have hwpb : IsPullback (pullback.fst pr₁ w) (pullback.snd pr₁ w) pr₁ w :=
    IsPullback.of_hasPullback _ _
  obtain ⟨α, hT⟩ :=
    exists_algebra_isPullback_spec_map (K := G.arrows.left.residueField q) e
      (hwpb.paste_horiz hA)
  obtain ⟨β, hS⟩ :=
    exists_algebra_isPullback_spec_map (K := G.arrows.left.residueField q) e
      (hwpb.paste_horiz hB)
  -- A point of the pasted apex lying over `ξ`.
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hwpb ξ
    (default : Spec (G.arrows.left.residueField q))
    (by rw [hwdef, Scheme.fromSpecResidueField_apply])
  refine ⟨G.arrows.left.residueField q, inferInstance, α, β,
    hT.isoPullback.hom.base z, hS.isoPullback.hom.base z,
    Over.isoMk (hT.isoPullback.symm ≪≫ hS.isoPullback) ?_, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Over.mk_hom, Category.assoc,
      IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_inv_snd]
  · simp only [Over.isoMk_hom_left, Iso.trans_hom, Iso.symm_hom, ← Scheme.Hom.comp_apply,
      Iso.hom_inv_id_assoc]
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_fst, Scheme.Hom.comp_apply, hz]
    exact hfst
  · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_hom_fst, Scheme.Hom.comp_apply, hz]
    exact hcomp

end Stacks.Groupoids.GroupoidScheme

end
