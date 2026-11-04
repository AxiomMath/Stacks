module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcEffectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcFamilyEffective
public import StacksFrontier.AlgebraicGeometry.Descent.DescentDataReindex
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentDatumInvariantOpen

/-!
# Effective descent for disjoint unions of spectra of Artinian rings

Let `f : X ⟶ S` be a quasi-compact, flat, surjective morphism of schemes and let `(V, φ)` be a
descent datum relative to `X/S`.  If `V` is a disjoint union of spectra of Artinian rings then
`(V, φ)` is effective.

## Main definitions

* `AlgebraicGeometry.DescentDatum.relatedPoints` is the set of points of `V` reachable from a
  given one through the gluing isomorphism.

## Main results

* `AlgebraicGeometry.isAffineHom_of_isLocallyArtinian`: a morphism out of a finite locally
  Artinian scheme is affine.
* `AlgebraicGeometry.DescentDatum.equivalence_relatedPoints`: reachability is an equivalence
  relation on the points of `V`.
* `AlgebraicGeometry.DescentDatum.isCompact_relatedPoints`: over a quasi-compact morphism each
  reachability class is quasi-compact.
* `AlgebraicGeometry.DescentDatum.isEffective_of_iso_sigma_spec_isArtinianRing`: a descent
  datum relative to a quasi-compact, flat, surjective morphism whose scheme is a disjoint union
  of spectra of Artinian rings is effective.

## Implementation notes

The source passes to the cartesian morphism of simplicial schemes attached to `(V, φ)` and uses
the equivalence relation on the points of its degree-zero part.  Here the relation is read off
the datum itself, through the groupoid scheme attached to it by
`AlgebraicGeometry.descentDatumToEquivariant`: its target map is the first projection of
`V ×_S X` and its source map is the second projection of `X ×_S V` after `φ`, so the relation
on points induced by a groupoid scheme is exactly reachability through `φ`, and it is an
equivalence relation by Stacks 022Q. A class is quasi-compact because it is the image of a
fibre of the first projection, which is a base change of `f`.

The decomposition of `V` into the pieces cut out by the classes is not formed: a disjoint union
of spectra of Artinian rings is locally Artinian, hence discrete, so each class is an open
subscheme invariant under `φ` — invariance being exactly that a class is a union of classes —
and quasi-compact plus discrete makes it finite.  A morphism out of a finite locally Artinian
scheme is affine, so the restricted datum is effective by Stacks 0245 and the datum itself is
effective because effectivity is local on `V`, which is Stacks 0AP4.

## References

* [Stacks Project, Tag 024I](https://stacks.math.columbia.edu/tag/024I)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 01SI](https://stacks.math.columbia.edu/tag/01SI)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 022Q](https://stacks.math.columbia.edu/tag/022Q)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

/-! ### Affine morphisms out of a finite locally Artinian scheme -/

/-- A morphism out of a finite locally Artinian scheme is affine: the inverse image of an open
is again finite and locally Artinian, hence affine. -/
lemma isAffineHom_of_isLocallyArtinian {Y Z : Scheme.{u}} [IsLocallyArtinian Y] [Finite Y]
    (g : Y ⟶ Z) : IsAffineHom g := by
  refine ⟨fun U _ ↦ ?_⟩
  have : Finite (g ⁻¹ᵁ U) := .of_injective Subtype.val Subtype.val_injective
  exact (inferInstance : IsAffine (g ⁻¹ᵁ U))

/-- A scheme isomorphic to a disjoint union of spectra of Artinian rings is locally
Artinian. -/
lemma isLocallyArtinian_of_iso_sigma_spec {Y : Scheme.{u}} {ι : Type u}
    (A : ι → CommRingCat.{u}) (hA : ∀ i, IsArtinianRing (A i))
    (e : Y ≅ ∐ fun i ↦ Spec (A i)) : IsLocallyArtinian Y := by
  rw [isLocallyArtinian_iff_openCover ((sigmaOpenCover fun i ↦ Spec (A i)).pushforwardIso e.inv)]
  exact fun i ↦ Scheme.isLocallyArtinianScheme_Spec.2 (hA i)

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-! ### The points reachable through the gluing isomorphism -/

variable (D : DescentDatum f)

/-- The set of points of `V` reachable from `v` through the gluing isomorphism: the images
under `φ` followed by the projection to `V` of the points of `V ×_S X` lying over `v`. -/
def relatedPoints (v : D.over.left) : Set D.over.left :=
  {v' | ∃ z : ↥(pullback (D.over.hom ≫ f) f),
    pullback.fst (D.over.hom ≫ f) f z = v ∧
      pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom z) = v'}

private lemma mem_relatedPoints_iff (v v' : D.over.left) :
    v' ∈ D.relatedPoints v ↔ Function.SourceTargetRel
      (equivariantActionGroupoid (descentDatumToEquivariant D)).source.left.base
      (equivariantActionGroupoid (descentDatumToEquivariant D)).target.left.base v v' := by
  constructor
  · rintro ⟨z, hz₁, hz₂⟩
    have hez : (descentDatumGroupoidArrowsIso D).hom
        ((descentDatumGroupoidArrowsIso D).inv.base z) = z :=
      (Scheme.homeoOfIso (descentDatumGroupoidArrowsIso D)).apply_symm_apply z
    refine ⟨(descentDatumGroupoidArrowsIso D).inv.base z, ?_, ?_⟩
    · exact (descentDatumGroupoid_target_left_apply D
        ((descentDatumGroupoidArrowsIso D).inv.base z)).trans
        ((congrArg (fun w ↦ pullback.fst (D.over.hom ≫ f) f w) hez).trans hz₁)
    · exact (descentDatumGroupoid_source_left_apply D
        ((descentDatumGroupoidArrowsIso D).inv.base z)).trans
        ((congrArg (fun w ↦ pullback.snd f (D.over.hom ≫ f)
          (D.transitionPullbackIso.hom w)) hez).trans hz₂)
  · rintro ⟨r, hr₁, hr₂⟩
    refine ⟨(descentDatumGroupoidArrowsIso D).hom.base r, ?_, ?_⟩
    · exact (descentDatumGroupoid_target_left_apply D r).symm.trans hr₁
    · exact (descentDatumGroupoid_source_left_apply D r).symm.trans hr₂

/-- **Reachability through the gluing isomorphism is an equivalence relation on the points of
`V`.** The two projections of the groupoid scheme of the datum form a pre-equivalence relation,
so Stacks 022Q applies. -/
theorem equivalence_relatedPoints :
    Equivalence (fun v v' : D.over.left ↦ v' ∈ D.relatedPoints v) := by
  have hpre : Equivalence (Function.SourceTargetRel
      (equivariantActionGroupoid (descentDatumToEquivariant D)).source.left.base
      (equivariantActionGroupoid (descentDatumToEquivariant D)).target.left.base) := by
    have h := AlgebraicGeometry.PreRelation.equivalence_sourceTargetRel
      (groupoidPreRelation (equivariantActionGroupoid (descentDatumToEquivariant D)))
      (groupoidPreRelation_isPreEquivalenceRelation
        (equivariantActionGroupoid (descentDatumToEquivariant D)))
    have hs : (groupoidPreRelation
        (equivariantActionGroupoid (descentDatumToEquivariant D))).source.left =
          (equivariantActionGroupoid (descentDatumToEquivariant D)).source.left := by
      simp [Stacks.Groupoids.PreRelation.source]
    have ht : (groupoidPreRelation
        (equivariantActionGroupoid (descentDatumToEquivariant D))).target.left =
          (equivariantActionGroupoid (descentDatumToEquivariant D)).target.left := by
      simp [Stacks.Groupoids.PreRelation.target]
    rwa [hs, ht] at h
  exact ⟨fun v ↦ (D.mem_relatedPoints_iff v v).2 (hpre.refl v),
    fun {v v'} h ↦ (D.mem_relatedPoints_iff v' v).2
      (hpre.symm ((D.mem_relatedPoints_iff v v').1 h)),
    fun {v v' v''} h h' ↦ (D.mem_relatedPoints_iff v v'').2
      (hpre.trans ((D.mem_relatedPoints_iff v v').1 h)
        ((D.mem_relatedPoints_iff v' v'').1 h'))⟩

/-- **Each reachability class is quasi-compact**, for `f` quasi-compact: it is the image of the
fibre over `v` of the first projection of `V ×_S X`, which is a base change of `f`. -/
theorem isCompact_relatedPoints [QuasiCompact f] (v : D.over.left) :
    IsCompact (D.relatedPoints v) := by
  have hset : D.relatedPoints v = Set.range
      ((pullback.fst (D.over.hom ≫ f) f).fiberι v ≫ D.transitionPullbackIso.hom ≫
        pullback.snd f (D.over.hom ≫ f)) := by
    ext v'
    constructor
    · rintro ⟨z, hz₁, hz₂⟩
      obtain ⟨w, rfl⟩ : z ∈ Set.range ((pullback.fst (D.over.hom ≫ f) f).fiberι v) := by
        rwa [(pullback.fst (D.over.hom ≫ f) f).range_fiberι]
      exact ⟨w, by simpa using hz₂⟩
    · rintro ⟨w, rfl⟩
      refine ⟨(pullback.fst (D.over.hom ≫ f) f).fiberι v w, ?_, ?_⟩
      · have : (pullback.fst (D.over.hom ≫ f) f).fiberι v w ∈
            Set.range ((pullback.fst (D.over.hom ≫ f) f).fiberι v) := ⟨w, rfl⟩
        rwa [(pullback.fst (D.over.hom ≫ f) f).range_fiberι] at this
      · simp
  rw [hset]
  exact isCompact_range (Scheme.Hom.continuous _)

/-- A reachability class, as an open subscheme of `V`, for `V` discrete. -/
private def relatedOpens [DiscreteTopology D.over.left] (v : D.over.left) :
    D.over.left.Opens :=
  ⟨D.relatedPoints v, isOpen_discrete _⟩

/-- **A reachability class is invariant under the gluing isomorphism**: being a class, it is a
union of classes. -/
private lemma isTransitionInvariant_relatedOpens [DiscreteTopology D.over.left]
    (v : D.over.left) : D.IsTransitionInvariant (D.relatedOpens v) := by
  refine D.isTransitionInvariant_of_le _ ?_
  rintro z ⟨y, hy, rfl⟩
  exact D.equivalence_relatedPoints.trans hy ⟨y, rfl, rfl⟩

/-! ### The example case -/

/-- Let `f : X ⟶ S` be a quasi-compact, flat, surjective morphism of schemes and let `(V, φ)` be a
descent datum relative to `X/S`. If `V` is a disjoint union of spectra of Artinian rings then
`(V, φ)` is effective. -/
@[stacks 024I "effectivity of a datum carried by a disjoint union of Artinian spectra"]
theorem isEffective_of_iso_sigma_spec_isArtinianRing [QuasiCompact f] [Flat f] [Surjective f]
    (D : DescentDatum f)
    (hV : ∃ (ι : Type u) (A : ι → CommRingCat.{u}), (∀ i, IsArtinianRing (A i)) ∧
      Nonempty (D.over.left ≅ ∐ fun i ↦ Spec (A i))) :
    DescentData.IsEffective D := by
  obtain ⟨ι, A, hA, ⟨e⟩⟩ := hV
  have : IsLocallyArtinian D.over.left := isLocallyArtinian_of_iso_sigma_spec A hA e
  refine isEffective_of_forall_exists_restrictOpen D fun v ↦
    ⟨D.relatedOpens v, D.isTransitionInvariant_relatedOpens v,
      D.equivalence_relatedPoints.refl v, ?_⟩
  have : CompactSpace (D.relatedOpens v) :=
    isCompact_iff_compactSpace.mp (D.isCompact_relatedPoints v)
  have : Finite (D.relatedOpens v) := finite_of_compact_of_discrete
  have haff : IsAffineHom ((D.relatedOpens v).ι ≫ D.over.hom) :=
    isAffineHom_of_isLocallyArtinian _
  exact isEffective_of_isAffineHom _ haff

end DescentDatum

end AlgebraicGeometry

end

end
