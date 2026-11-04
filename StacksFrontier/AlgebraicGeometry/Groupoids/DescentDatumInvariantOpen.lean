module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.TransitionSwap
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentDatumGroupoid
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ConstructingInvariantOpens

/-!
# Invariant opens of the groupoid of a descent datum are invariant opens of the datum

Let `f : X ⟶ S` be a morphism of schemes and let `D` be a descent datum relative to `f`, with
underlying scheme `V` over `X` and gluing isomorphism `φ : V ×_S X ≅ X ×_S V`. An open of `V` is
invariant under the groupoid scheme `G' = (V, V ×_{X,t} (X ×_S X), s', t', c')` attached to `D`
exactly when it is invariant under `φ`.

## Main definitions

* `AlgebraicGeometry.descentDatumGroupoidArrowsIso` identifies the scheme of arrows of the
  groupoid of a descent datum with the literal fibre product `V ×_S X`.

## Main results

* `AlgebraicGeometry.descentDatumGroupoid_target_left_apply` and
  `AlgebraicGeometry.descentDatumGroupoid_source_left_apply` compute the target and the source
  of an arrow of `G'` on points: along
  `AlgebraicGeometry.descentDatumGroupoidArrowsIso` the target is the first projection of
  `V ×_S X` and the source is the second projection of `X ×_S V` after applying `φ`.
* `AlgebraicGeometry.isTransitionInvariant_of_isInvariantOpen`: **an open of `V` invariant
  under the groupoid of `D` is invariant under the gluing isomorphism of `D`.**
* `AlgebraicGeometry.isInvariantOpen_of_isTransitionInvariant` is the converse, and
  `AlgebraicGeometry.isTransitionInvariant_iff_isInvariantOpen` the resulting equivalence.
* `AlgebraicGeometry.exists_isTransitionInvariant_isCompact_between_descentDatum`: for `f` flat
  and quasi-compact with `X` affine and `V` ind-quasi-affine over `X`, every quasi-compact open
  of `V` is contained in an open invariant under the gluing isomorphism of `D`, which in turn is
  contained in a quasi-compact open.

## Implementation notes

The object scheme of `G'` is `V` and its target map is the first projection of
`V ×_{X,t} (X ×_S X)`, but that fibre product is formed in `CategoryTheory.Over S`, where it is
not the fibre product of the underlying schemes. `AlgebraicGeometry.descentDatumGroupoidArrowsIso`
is the composite of `AlgebraicGeometry.pairTargetPullbackIso`, which rewrites
`V ×_{X,t} (X ×_S X)` as the binary product `V ×_S X` of `Over S`, and
`CategoryTheory.Over.prodLeftIsoPullback`, which rewrites that binary product as the literal
fibre product.

The arrow scheme of `G'` is
`CategoryTheory.Limits.pullback (AlgebraicGeometry.structureMap f D.over)
(AlgebraicGeometry.pairTarget f)` definitionally but not syntactically, and rewriting inside a
goal stated with `(AlgebraicGeometry.equivariantActionGroupoid _).arrows` leaves the goal
ill-typed at `implicit` transparency. The isomorphism and the two `apply` lemmas are therefore
stated with the fibre product written out, and `AlgebraicGeometry.descentDatumGroupoid_arrows`
records the identification; the invariance statements use the groupoid spelling.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 0APB](https://stacks.math.columbia.edu/tag/0APB)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f)

/-! ### The arrow scheme of the groupoid of a descent datum -/

/-- The object scheme of the groupoid of a descent datum is the scheme `V` the datum is carried
by, viewed over `S`. -/
lemma descentDatumGroupoid_objects :
    (equivariantActionGroupoid (descentDatumToEquivariant D)).objects =
      (Over.map f).obj D.over := rfl

/-- The arrow scheme of the groupoid of a descent datum is the fibre product
`V ×_{X,t} (X ×_S X)`, formed in `CategoryTheory.Over S`. -/
lemma descentDatumGroupoid_arrows :
    (equivariantActionGroupoid (descentDatumToEquivariant D)).arrows =
      pullback (structureMap f D.over) (pairTarget f) := rfl

/-- **The arrow scheme of the groupoid of a descent datum is `V ×_S X`.**  The scheme
underlying the fibre product `V ×_{X,t} (X ×_S X)` of `CategoryTheory.Over S` is the literal
fibre product `V ×_S X`: the comparison is
`AlgebraicGeometry.pairTargetPullbackIso` followed by
`CategoryTheory.Over.prodLeftIsoPullback`. -/
def descentDatumGroupoidArrowsIso :
    (pullback (structureMap f D.over) (pairTarget f)).left ≅ pullback (D.over.hom ≫ f) f :=
  (Over.forget S).mapIso (pairTargetPullbackIso (structureMap f D.over)) ≪≫
    Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)

/-- `AlgebraicGeometry.descentDatumGroupoidArrowsIso` is the composite of the two
comparisons. -/
lemma descentDatumGroupoidArrowsIso_hom :
    (descentDatumGroupoidArrowsIso D).hom =
      (pairTargetPullbackIso (structureMap f D.over)).hom.left ≫
        (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).hom := rfl

/-! ### The source and target maps of the groupoid, on the fibre product -/

/-- The target map of the groupoid of a descent datum is the first projection of `V ×_S X`,
read through `AlgebraicGeometry.descentDatumGroupoidArrowsIso`. -/
lemma descentDatumGroupoidArrowsIso_hom_comp_fst :
    (descentDatumGroupoidArrowsIso D).hom ≫ pullback.fst (D.over.hom ≫ f) f =
      (pullback.fst (structureMap f D.over) (pairTarget f)).left := by
  rw [descentDatumGroupoidArrowsIso_hom, Category.assoc, D.prodLeftIso_hom_pullbackFst,
    ← Over.comp_left, pairTargetPullbackIso_hom_comp_fst]

/-- The target map of the groupoid of a descent datum, transported to `V ×_S X`: it is the
first projection. -/
lemma descentDatumGroupoid_target_left :
    (equivariantActionGroupoid (descentDatumToEquivariant D)).target.left =
      (descentDatumGroupoidArrowsIso D).hom ≫ pullback.fst (D.over.hom ≫ f) f :=
  (descentDatumGroupoidArrowsIso_hom_comp_fst D).symm

/-- **The source map of the groupoid of a descent datum is the gluing isomorphism.**  Read
through `AlgebraicGeometry.descentDatumGroupoidArrowsIso`, it is `φ` followed by the projection
of `X ×_S V` to `V`. -/
lemma descentDatumGroupoid_source_left :
    (equivariantActionGroupoid (descentDatumToEquivariant D)).source.left =
      (descentDatumGroupoidArrowsIso D).hom ≫ D.transitionPullbackIso.hom ≫
        pullback.snd f (D.over.hom ≫ f) := by
  have hsrc :
      (pullback.lift (pullback.fst (structureMap f D.over) (pairTarget f))
          (pullback.snd (structureMap f D.over) (pairTarget f)) pullback.condition ≫
        (descentDatumDescentIso D).hom ≫
          pullback.snd (pairSource f) (structureMap f D.over)) =
      (pairTargetPullbackIso (structureMap f D.over)).hom ≫ D.transition.hom.left ≫
        prod.snd := by
    rw [pullback.lift_fst_snd, Category.id_comp]
    simp only [descentDatumDescentIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      DescentDatum.transitionIso_hom, pairSourcePullbackIso_inv_comp_snd]
  have hΦ : D.transitionPullbackIso.hom =
      (Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f)).inv ≫
        D.transition.hom.left.left ≫
          (Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over)).hom := rfl
  refine (congrArg Over.Hom.left hsrc).trans ?_
  rw [descentDatumGroupoidArrowsIso_hom, hΦ, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc]
  simp only [Over.comp_left, Category.assoc, D.prodLeftIso_hom_pullbackSnd]

/-- The target of an arrow of the groupoid of a descent datum, on points: it is the point of
`V` of the corresponding point of `V ×_S X`. -/
lemma descentDatumGroupoid_target_left_apply
    (r : (pullback (structureMap f D.over) (pairTarget f)).left) :
    (equivariantActionGroupoid (descentDatumToEquivariant D)).target.left.base r =
      pullback.fst (D.over.hom ≫ f) f ((descentDatumGroupoidArrowsIso D).hom r) := by
  rw [descentDatumGroupoid_target_left]
  exact Scheme.Hom.comp_apply _ _ r

/-- The source of an arrow of the groupoid of a descent datum, on points: it is the point of
`V` obtained by applying the gluing isomorphism to the corresponding point of `V ×_S X`. -/
lemma descentDatumGroupoid_source_left_apply
    (r : (pullback (structureMap f D.over) (pairTarget f)).left) :
    (equivariantActionGroupoid (descentDatumToEquivariant D)).source.left.base r =
      pullback.snd f (D.over.hom ≫ f)
        (D.transitionPullbackIso.hom ((descentDatumGroupoidArrowsIso D).hom r)) := by
  rw [descentDatumGroupoid_source_left]
  exact (Scheme.Hom.comp_apply _ _ r).trans (Scheme.Hom.comp_apply _ _ _)

/-! ### Invariance of an open: the two notions agree -/

/-- **An open invariant under the groupoid of a descent datum is invariant under the gluing
isomorphism.** -/
theorem isTransitionInvariant_of_isInvariantOpen (W : D.over.left.Opens)
    (hW : IsInvariantOpen (equivariantActionGroupoid (descentDatumToEquivariant D)) W) :
    D.IsTransitionInvariant W := by
  refine D.isTransitionInvariant_of_le W ?_
  rintro z ⟨y, hy, rfl⟩
  set r := (descentDatumGroupoidArrowsIso D).inv.base y
  have hey : (descentDatumGroupoidArrowsIso D).hom r = y := Scheme.inv_hom_apply _ y
  have hT : (equivariantActionGroupoid (descentDatumToEquivariant D)).target.left.base r ∈
      (W : Set D.over.left) := by
    rwa [descentDatumGroupoid_target_left_apply, hey]
  have hS : (equivariantActionGroupoid (descentDatumToEquivariant D)).source.left.base r ∈
      (W : Set D.over.left) :=
    (Set.ext_iff.mp (GroupoidScheme.source_preimage_eq_target_preimage
      (equivariantActionGroupoid (descentDatumToEquivariant D)) hW) r).mpr hT
  rwa [descentDatumGroupoid_source_left_apply, hey] at hS

/-- If an open `W` is invariant under the gluing isomorphism of a descent datum and an arrow `r`
of its groupoid, spelled as a point of the fibre product, has source in `W`, then its target lies
in `W`. -/
private lemma mem_of_isTransitionInvariant_source (W : D.over.left.Opens)
    (hW : D.IsTransitionInvariant W)
    (r : (pullback (structureMap f D.over) (pairTarget f)).left)
    (hr : (equivariantActionGroupoid (descentDatumToEquivariant D)).source.left.base r ∈
      (W : Set D.over.left)) :
    (equivariantActionGroupoid (descentDatumToEquivariant D)).target.left.base r ∈
      (W : Set D.over.left) := by
  rw [descentDatumGroupoid_source_left_apply] at hr
  rw [descentDatumGroupoid_target_left_apply]
  have h := D.mem_of_isTransitionInvariant' W hW _ hr
  rwa [Scheme.hom_inv_apply] at h

/-- **An open invariant under the gluing isomorphism of a descent datum is invariant under the
groupoid of the datum.**  The converse of
`AlgebraicGeometry.isTransitionInvariant_of_isInvariantOpen`. -/
theorem isInvariantOpen_of_isTransitionInvariant (W : D.over.left.Opens)
    (hW : D.IsTransitionInvariant W) :
    IsInvariantOpen (equivariantActionGroupoid (descentDatumToEquivariant D)) W :=
  mem_of_isTransitionInvariant_source D W hW

/-- **Invariance of an open under the groupoid of a descent datum and invariance under its
gluing isomorphism are the same condition.** -/
theorem isTransitionInvariant_iff_isInvariantOpen (W : D.over.left.Opens) :
    D.IsTransitionInvariant W ↔
      IsInvariantOpen (equivariantActionGroupoid (descentDatumToEquivariant D)) W :=
  ⟨isInvariantOpen_of_isTransitionInvariant D W,
    isTransitionInvariant_of_isInvariantOpen D W⟩

/-! ### Invariant opens between quasi-compact opens -/

/-- Let `f : X ⟶ S` be flat and quasi-compact with `X` affine, and let `D` be a descent datum
relative to `f` whose underlying scheme `V` is ind-quasi-affine over `X`.  Then every
quasi-compact open of `V` is contained in an open invariant under the gluing isomorphism of
`D`, which in turn is contained in a quasi-compact open. -/
theorem exists_isTransitionInvariant_isCompact_between_descentDatum
    [IsAffine X] [Flat f] [QuasiCompact f] [IsIndQuasiAffineHom D.over.hom]
    (W : D.over.left.Opens) (hW : IsCompact (W : Set D.over.left)) :
    ∃ V W' : D.over.left.Opens, D.IsTransitionInvariant V ∧
      IsCompact (W' : Set D.over.left) ∧
        (W : Set D.over.left) ⊆ (V : Set D.over.left) ∧
          (V : Set D.over.left) ⊆ (W' : Set D.over.left) := by
  obtain ⟨V, W', hVinv, hW'compact, hWV, hVW'⟩ :=
    exists_isInvariantOpen_isCompact_between_descentDatumGroupoid D W hW
  exact ⟨V, W', isTransitionInvariant_of_isInvariantOpen D V hVinv, hW'compact, hWV, hVW'⟩

end AlgebraicGeometry

end
