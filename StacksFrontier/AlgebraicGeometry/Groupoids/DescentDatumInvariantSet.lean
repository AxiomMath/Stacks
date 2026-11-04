module

public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentDatumInvariantOpen

/-!
# Set-theoretically invariant subsets of a descent datum

Let `f : X ⟶ S` be a morphism of schemes and let `D` be a descent datum relative to `f`, with
underlying scheme `V` over `X` and gluing isomorphism `φ : V ×_S X ≅ X ×_S V`. A subset `E` of
`V` is invariant when `φ(E ×_S X) = X ×_S E` as subsets. On opens this is
`AlgebraicGeometry.DescentDatum.IsTransitionInvariant`; the set-level notion also applies to an
intersection of quasi-compact opens, which in general is not open.

## Main definitions

* `AlgebraicGeometry.DescentDatum.IsTransitionInvariantSet` is invariance of an arbitrary
  subset of `V` under the gluing isomorphism, stated as the equality of subsets
  `φ(E ×_S X) = X ×_S E`.

## Main results

* `AlgebraicGeometry.DescentDatum.isTransitionInvariant_iff_isTransitionInvariantSet` : for an
  open subset the two notions agree.
* `AlgebraicGeometry.DescentDatum.isTransitionInvariantSet_of_subset` : the inclusion
  `φ(E ×_S X) ⊆ X ×_S E` already implies the equality.
* `AlgebraicGeometry.isTransitionInvariantSet_of_isInvariantSet` and
  `AlgebraicGeometry.isInvariantSet_of_isTransitionInvariantSet` : a subset of `V` is invariant
  under the groupoid of `D` exactly when it is invariant under the gluing isomorphism;
  `AlgebraicGeometry.isTransitionInvariantSet_iff_isInvariantSet` is the equivalence.
* `AlgebraicGeometry.exists_isTransitionInvariant_isTransitionInvariantSet_descentDatum` : for
  `f` flat and quasi-compact with `X` affine and `V` ind-quasi-affine over `X`, every
  quasi-compact open `W₀` of `V` is contained in an open `W` with `φ(W ×_S X) = X ×_S W`, which
  in turn is contained in an intersection `E` of a nonempty family of quasi-compact opens with
  `φ(E ×_S X) = X ×_S E` set-theoretically.
* `AlgebraicGeometry.exists_mem_isTransitionInvariant_isTransitionInvariantSet_descentDatum` :
  the same statement for a point of `V` in place of `W₀`.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APA](https://stacks.math.columbia.edu/tag/0APA)
* [Stacks Project, Tag 0APB](https://stacks.math.columbia.edu/tag/0APB)
* [Stacks Project, Tag 03LO](https://stacks.math.columbia.edu/tag/03LO)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The inverse of a scheme isomorphism undoes the isomorphism on points. -/
private theorem iso_inv_hom_apply {A B : Scheme.{u}} (e : A ≅ B) (y : A) : e.inv (e.hom y) = y :=
  (Scheme.homeoOfIso e).symm_apply_apply y

/-- A scheme isomorphism undoes its inverse on points. -/
private theorem iso_hom_inv_apply {A B : Scheme.{u}} (e : A ≅ B) (y : B) : e.hom (e.inv y) = y :=
  (Scheme.homeoOfIso e).apply_symm_apply y

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (E : Set D.over.left)

/-! ### Invariance of an arbitrary subset -/

/-- A subset `E` of the scheme `V` underlying a descent datum is *invariant* when the gluing
isomorphism `φ : V ×_S X ≅ X ×_S V` carries `E ×_S X` onto `X ×_S E`. -/
def IsTransitionInvariantSet : Prop :=
  ⇑D.transitionPullbackIso.hom '' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) =
    ⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E

/-- Invariance of a subset, as the equality of subsets it is defined to be. -/
lemma isTransitionInvariantSet_def (hE : D.IsTransitionInvariantSet E) :
    ⇑D.transitionPullbackIso.hom '' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) =
      ⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E := hE

/-- For an open subset, invariance of the subset is invariance of the open. -/
lemma isTransitionInvariant_iff_isTransitionInvariantSet (W : D.over.left.Opens) :
    D.IsTransitionInvariant W ↔ D.IsTransitionInvariantSet (W : Set D.over.left) := by
  rw [IsTransitionInvariant, IsTransitionInvariantSet, ← SetLike.coe_set_eq]
  rfl

/-- Invariance of a subset, read forwards: `φ` carries a point of `E ×_S X` to a point of
`X ×_S E`. -/
lemma mem_of_isTransitionInvariantSet (hE : D.IsTransitionInvariantSet E)
    (z : ↥(pullback (D.over.hom ≫ f) f)) (hz : pullback.fst (D.over.hom ≫ f) f z ∈ E) :
    pullback.snd f (D.over.hom ≫ f) (D.transitionPullbackIso.hom z) ∈ E := by
  rw [← Set.mem_preimage, ← D.isTransitionInvariantSet_def E hE]
  exact ⟨z, hz, rfl⟩

/-- Invariance of a subset, read backwards: `φ⁻¹` carries a point of `X ×_S E` to a point of
`E ×_S X`. -/
lemma mem_of_isTransitionInvariantSet' (hE : D.IsTransitionInvariantSet E)
    (z : ↥(pullback f (D.over.hom ≫ f))) (hz : pullback.snd f (D.over.hom ≫ f) z ∈ E) :
    pullback.fst (D.over.hom ≫ f) f (D.transitionPullbackIso.inv z) ∈ E := by
  have h : z ∈ ⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E := hz
  rw [← D.isTransitionInvariantSet_def E hE] at h
  obtain ⟨y, hy, rfl⟩ := h
  rwa [iso_inv_hom_apply]

/-! ### The inclusion implies the equality -/

/-- **One inclusion suffices.**  If the gluing isomorphism carries `E ×_S X` *into* `X ×_S E`,
then it carries it *onto* `X ×_S E`. -/
theorem isTransitionInvariantSet_of_subset
    (hle : ⇑D.transitionPullbackIso.hom '' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) :
    D.IsTransitionInvariantSet E := by
  have hswap : ∀ y : ↥(pullback f (D.over.hom ≫ f)), pullback.fst (D.over.hom ≫ f) f
      ((pullbackSymmetry f (D.over.hom ≫ f)).hom y) = pullback.snd f (D.over.hom ≫ f) y :=
    fun y ↦ by rw [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst]
  refine Set.Subset.antisymm hle fun z hz ↦ ?_
  have hz' : pullback.fst (D.over.hom ≫ f) f
      ((pullbackSymmetry f (D.over.hom ≫ f)).hom z) ∈ E := by rwa [hswap]
  have hmem : pullback.snd f (D.over.hom ≫ f)
      (D.transitionPullbackIso.hom ((pullbackSymmetry f (D.over.hom ≫ f)).hom z)) ∈ E :=
    hle ⟨_, hz', rfl⟩
  refine ⟨D.transitionPullbackIso.inv z, ?_, ?_⟩
  · show pullback.fst (D.over.hom ≫ f) f (D.transitionPullbackIso.inv z) ∈ E
    rw [D.transitionPullbackIso_inv_eq]
    simpa only [Scheme.Hom.comp_apply, hswap] using hmem
  · exact iso_hom_inv_apply _ z

end DescentDatum

/-! ### Invariance of a subset: the groupoid and the gluing isomorphism agree -/

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-- **A subset invariant under the groupoid of a descent datum is invariant under the gluing
isomorphism.** Invariance under the groupoid is the one-sided condition
`Stacks.Groupoids.IsInvariantSet`. -/
theorem isTransitionInvariantSet_of_isInvariantSet (E : Set D.over.left)
    (hE : IsInvariantSet (equivariantActionGroupoid (descentDatumToEquivariant D)) E) :
    D.IsTransitionInvariantSet E := by
  refine D.isTransitionInvariantSet_of_subset E ?_
  rintro z ⟨y, hy, rfl⟩
  set r := (descentDatumGroupoidArrowsIso D).inv.base y with hr
  have hey : (descentDatumGroupoidArrowsIso D).hom r = y := iso_hom_inv_apply _ y
  have hT : (equivariantActionGroupoid (descentDatumToEquivariant D)).target.left.base r ∈ E := by
    rwa [descentDatumGroupoid_target_left_apply, hey]
  have hS : (equivariantActionGroupoid (descentDatumToEquivariant D)).source.left.base r ∈ E :=
    (Set.ext_iff.mp (GroupoidScheme.source_preimage_eq_target_preimage
      (equivariantActionGroupoid (descentDatumToEquivariant D)) hE) r).mpr hT
  rwa [descentDatumGroupoid_source_left_apply, hey] at hS

/-- If `E` is invariant under the gluing isomorphism, then for an arrow `r` of the groupoid of
`D`, given as a point of the fibre product, the target of `r` lies in `E` when its source does. -/
private lemma mem_of_isTransitionInvariantSet_source (E : Set D.over.left)
    (hE : D.IsTransitionInvariantSet E)
    (r : (pullback (structureMap f D.over) (pairTarget f)).left)
    (hr : (equivariantActionGroupoid (descentDatumToEquivariant D)).source.left.base r ∈ E) :
    (equivariantActionGroupoid (descentDatumToEquivariant D)).target.left.base r ∈ E := by
  rw [descentDatumGroupoid_source_left_apply] at hr
  rw [descentDatumGroupoid_target_left_apply]
  have h := D.mem_of_isTransitionInvariantSet' E hE _ hr
  rwa [iso_inv_hom_apply] at h

/-- **A subset invariant under the gluing isomorphism of a descent datum is invariant under the
groupoid of the datum.** -/
theorem isInvariantSet_of_isTransitionInvariantSet (E : Set D.over.left)
    (hE : D.IsTransitionInvariantSet E) :
    IsInvariantSet (equivariantActionGroupoid (descentDatumToEquivariant D)) E :=
  mem_of_isTransitionInvariantSet_source D E hE

/-- **Invariance of a subset under the groupoid of a descent datum and invariance under its
gluing isomorphism are the same condition.** -/
theorem isTransitionInvariantSet_iff_isInvariantSet (E : Set D.over.left) :
    D.IsTransitionInvariantSet E ↔
      IsInvariantSet (equivariantActionGroupoid (descentDatumToEquivariant D)) E :=
  ⟨isInvariantSet_of_isTransitionInvariantSet D E,
    isTransitionInvariantSet_of_isInvariantSet D E⟩

/-! ### Invariant opens inside invariant intersections of quasi-compact opens -/

/-- Let `f : X ⟶ S` be flat and quasi-compact with `X` affine,
and let `D` be a descent datum relative to `f` whose underlying scheme `V` is ind-quasi-affine
over `X`.  Then every quasi-compact open `W₀` of `V` is contained in an open `W` with
`φ(W ×_S X) = X ×_S W`, which in turn is contained in a subset `E` which is the intersection of
a nonempty family of quasi-compact opens and satisfies `φ(E ×_S X) = X ×_S E`
set-theoretically. -/
theorem exists_isTransitionInvariant_isTransitionInvariantSet_descentDatum
    [IsAffine X] [Flat f] [QuasiCompact f] [IsIndQuasiAffineHom D.over.hom]
    (W₀ : D.over.left.Opens) (hW₀ : IsCompact (W₀ : Set D.over.left)) :
    ∃ (W : D.over.left.Opens) (E : Set D.over.left) (I : Type u) (_ : Nonempty I)
        (U : I → Set D.over.left),
      D.IsTransitionInvariant W ∧
        (∀ i, IsOpen (U i) ∧ IsCompact (U i)) ∧
          E = ⋂ i, U i ∧
            D.IsTransitionInvariantSet E ∧
              (W₀ : Set D.over.left) ⊆ (W : Set D.over.left) ∧
                (W : Set D.over.left) ⊆ E := by
  have : IsIndQuasiAffine D.over.left := isIndQuasiAffine_of_isIndQuasiAffineHom_hom D.over
  obtain ⟨W, W', hWinv, hW'cpt, hW₀W, hWW'⟩ :=
    exists_isInvariantOpen_isCompact_between_descentDatumGroupoid D W₀ hW₀
  obtain ⟨I, hI, U, hU, hEeq⟩ :=
    GroupoidScheme.target_image_source_preimage_eq_iInter_compact_open
      (equivariantActionGroupoid (descentDatumToEquivariant D)) W' hW'cpt
  exact ⟨W, _, I, hI, U, isTransitionInvariant_of_isInvariantOpen D W hWinv, hU, hEeq,
    isTransitionInvariantSet_of_isInvariantSet D _
      (GroupoidScheme.isInvariantSet_target_image_source_preimage _ _),
    hW₀W, hWW'.trans (GroupoidScheme.subset_target_image_source_preimage _ _)⟩

/-- Let `f : X ⟶ S` be flat and quasi-compact with `X` affine, and let `D` be a descent datum
relative to `f` whose underlying scheme `V` is ind-quasi-affine over `X`. Then every point of `V`
lies in an open `W` invariant under the gluing isomorphism, contained in a set-theoretically
invariant intersection `E` of a nonempty family of quasi-compact opens. -/
theorem exists_mem_isTransitionInvariant_isTransitionInvariantSet_descentDatum
    [IsAffine X] [Flat f] [QuasiCompact f] [IsIndQuasiAffineHom D.over.hom]
    (v : D.over.left) :
    ∃ (W : D.over.left.Opens) (E : Set D.over.left) (I : Type u) (_ : Nonempty I)
        (U : I → Set D.over.left),
      D.IsTransitionInvariant W ∧
        (∀ i, IsOpen (U i) ∧ IsCompact (U i)) ∧
          E = ⋂ i, U i ∧
            D.IsTransitionInvariantSet E ∧ v ∈ W ∧ (W : Set D.over.left) ⊆ E := by
  obtain ⟨W₀, hW₀aff, hvW₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := D.over.left) (x := v) (U := ⊤) trivial
  obtain ⟨W, E, I, hI, U, hWinv, hU, hEeq, hEinv, hW₀W, hWE⟩ :=
    exists_isTransitionInvariant_isTransitionInvariantSet_descentDatum D
      (W₀ : D.over.left.Opens) hW₀aff.isCompact
  exact ⟨W, E, I, hI, U, hWinv, hU, hEeq, hEinv, hW₀W hvW₀, hWE⟩

end AlgebraicGeometry

end

end
