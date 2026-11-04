module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowEtale
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowRank0BFG
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowTangent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.IsoInvariance
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.MiracleFlatEtale
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multiplication by an integer on an abelian variety is étale exactly for invertible integers

Let `k` be a field and let `A` be a nonzero abelian variety over `k`.  Then multiplication by an
integer `d` on `A` is étale if and only if `d` is invertible in `k`.  Nonzeroness is the
positivity of the topological Krull dimension of the underlying scheme, and it is not
decoration: over the zero abelian variety every `[d]` is étale, including `[0]` in
characteristic `p`.

## Main results

* `Stacks.Groupoids.etaleAt_zpow_id_identity_of_isUnit`: multiplication by an invertible integer
  is étale at the identity.
* `Stacks.Groupoids.etaleAt_iff_of_isIso_square_self`: étaleness of an endomorphism at a point
  is invariant along a commuting square of isomorphisms.
* `Stacks.Groupoids.etaleAt_zpow_id_translation`: the étale locus of multiplication by `d` is
  invariant under translation by a point of the group.
* `Stacks.Groupoids.etale_zpow_id_of_isUnit`: multiplication by an invertible integer on an
  abelian variety is étale.
* `Stacks.Groupoids.etale_zpow_id_iff_isUnit_intCast`: **Stacks Tag 0BFH.**

## Implementation notes

The source proof deduces étaleness at the identity from finite local freeness of `[d]`
(Tag 0BFG), whose only role there is to supply flatness.  Flatness is available without it.
Multiplication by `d` fixes the identity, so in
`AlgebraicGeometry.etaleAt_of_unramifiedAt_of_ringKrullDim_eq` the source and target local rings
at the identity are the same local ring, its required equality of Krull dimensions is the
fixed-point equality, and both rings are regular because an abelian variety is smooth over its
ground field (Tag 0BFC).  So unramifiedness at the identity — the derivative computation of
Tag 0BF5, carried out in `StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowTangent` — already gives
étaleness there, by miracle flatness rather than by the degree theory of Tag 0BFG.

Étaleness then spreads from the identity to every point as in the source.  Multiplication by `d`
is a homomorphism, so it commutes with translation by a point up to translation by the `d`-th
power of that point, and translations are isomorphisms; hence the étale locus is
translation-invariant.  Over an algebraically closed field a point outside that locus can be
taken closed, because the complement of the locus is closed and the underlying space is a
Jacobson space, and a closed point is then rational, so it is the image of the identity under a
translation — a contradiction.  The general case descends from the algebraic closure along
Tag 0476, whose hypothesis is that one of the two sides is flat; the flat side here is the field
extension, not `[d]`, which is exactly what is not known in advance.

## References

* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 0BF5](https://stacks.math.columbia.edu/tag/0BF5)
* [Stacks Project, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G)
* [Stacks Project, Tag 0476](https://stacks.math.columbia.edu/tag/0476)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

/-- **Multiplication by an invertible integer is étale at the identity.** Multiplication by `d`
fixes the identity, so the source and target local rings there are the same ring, and it is
regular because an abelian variety is smooth over its ground field; miracle flatness then
upgrades unramifiedness at the identity, which is the derivative computation of Tag 0BF5, to
étaleness. -/
theorem etaleAt_zpow_id_identity_of_isUnit (k : Type u) [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A] (s : Spec (.of k)) (d : ℤ)
    (hd : IsUnit ((d : ℤ) : k)) :
    AlgebraicGeometry.EtaleAt (((𝟙 A : A ⟶ A) ^ d).left) ((η[A]).left s) := by
  have := smooth_hom A
  have := isLocallyNoetherian_left A
  have : LocallyOfFiniteType (((𝟙 A : A ⟶ A) ^ d).left ≫ A.hom) :=
    ((𝟙 A : A ⟶ A) ^ d).w.symm ▸ inferInstance
  have : LocallyOfFiniteType (((𝟙 A : A ⟶ A) ^ d).left) :=
    locallyOfFiniteType_of_comp (((𝟙 A : A ⟶ A) ^ d).left) A.hom
  have : IsRegularLocalRing (A.left.presheaf.stalk ((η[A]).left s)) :=
    isRegularLocalRing_stalk_of_smooth_over_field A.hom ((η[A]).left s)
  have : IsRegularLocalRing
      (A.left.presheaf.stalk ((((𝟙 A : A ⟶ A) ^ d).left).base ((η[A]).left s))) :=
    isRegularLocalRing_stalk_of_smooth_over_field A.hom _
  exact AlgebraicGeometry.etaleAt_of_unramifiedAt_of_ringKrullDim_eq
    (((𝟙 A : A ⟶ A) ^ d).left) ((η[A]).left s)
    (unramifiedAt_zpow_id_identity_of_isUnit k A s d hd)
    (congrArg (fun y : A.left => ringKrullDim (A.left.presheaf.stalk y))
      (zpow_id_fixes_identity A s d).symm)

/-- **Étaleness of an endomorphism at a point is invariant along a commuting square of
isomorphisms.** If `u ≫ f = f ≫ v` with `u` and `v` isomorphisms, then `f` is étale at `u x`
exactly when it is étale at `x`. -/
theorem etaleAt_iff_of_isIso_square_self {X : Scheme.{u}} (f u v : X ⟶ X) [IsIso u] [IsIso v]
    (hcomm : u ≫ f = f ≫ v) (x : X) :
    AlgebraicGeometry.EtaleAt f (u.base x) ↔ AlgebraicGeometry.EtaleAt f x := by
  have hinvcomm : f ≫ inv v = inv u ≫ f := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← hcomm, IsIso.inv_hom_id_assoc]
  have hx : (inv u).base (u.base x) = x := by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  refine ⟨fun h => ?_, fun h => AlgebraicGeometry.etaleAt_of_isIso_square u v hcomm.symm h⟩
  simpa only [hx] using AlgebraicGeometry.etaleAt_of_isIso_square (inv u) (inv v) hinvcomm h

/-- Multiplication by `d` commutes with translation by a point of the group, up to translation
by the `d`-th power of that point: `[d]` is a homomorphism. -/
alias zpow_id_translation_commutes := zpow_translation_commutes

/-- Translation by a point sends the identity to that point. -/
theorem mulRight_identity_point {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (point : 𝟙_ (Over S) ⟶ G) (s : S) :
    (GrpObj.mulRight point).hom.left ((η[G]).left s) = point.left s := by
  have h : η[G] ≫ (GrpObj.mulRight point).hom = point := by
    show η[G] ≫ ((𝟙 G : G ⟶ G) * (toUnit G ≫ point)) = point
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, MonObj.one_eq_one]
    have hunit : toUnit (𝟙_ (Over S)) = 𝟙 _ := toUnit_unique _ _
    rw [hunit, Category.id_comp, one_mul]
  exact congrArg (fun morphism : S ⟶ G.left => morphism s) (congrArg Over.Hom.left h)

/-- **The étale locus of multiplication by `d` is translation-invariant.** -/
theorem etaleAt_zpow_id_translation {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]
    (point : 𝟙_ (Over S) ⟶ G) (d : ℤ) (x : G.left) :
    AlgebraicGeometry.EtaleAt (((𝟙 G : G ⟶ G) ^ d).left)
        ((GrpObj.mulRight point).hom.left x) ↔
      AlgebraicGeometry.EtaleAt (((𝟙 G : G ⟶ G) ^ d).left) x := by
  have : IsIso (GrpObj.mulRight point).hom.left :=
    ((Over.forget S).mapIso (GrpObj.mulRight point)).isIso_hom
  have : IsIso (GrpObj.mulRight (point ^ d)).hom.left :=
    ((Over.forget S).mapIso (GrpObj.mulRight (point ^ d))).isIso_hom
  refine etaleAt_iff_of_isIso_square_self _ (GrpObj.mulRight point).hom.left
    (GrpObj.mulRight (point ^ d)).hom.left ?_ x
  simpa only [Over.comp_left] using
    congrArg Over.Hom.left (zpow_id_translation_commutes G point d)

/-- **Multiplication by an invertible integer on an abelian variety over an algebraically closed
field is étale.** The étale locus is open, translation-invariant and contains the identity; a
point outside it can be taken closed, hence rational, and translated to the identity. -/
@[sga "3 XV 1.3" "special case"]
theorem etale_zpow_id_of_isAlgClosed_of_isUnit (k : Type u) [Field k] [IsAlgClosed k]
    (A : Over (Spec (.of k))) [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ)
    (hd : IsUnit ((d : ℤ) : k)) :
    Etale (((𝟙 A : A ⟶ A) ^ d).left) := by
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  have := LocallyOfFiniteType.jacobsonSpace A.hom
  rw [AlgebraicGeometry.etale_iff_forall_etaleAt]
  intro x
  by_contra hx
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (show {y : A.left |
      AlgebraicGeometry.EtaleAt (((𝟙 A : A ⟶ A) ^ d).left) y}ᶜ.Nonempty from ⟨x, hx⟩)
    (AlgebraicGeometry.isOpen_setOf_etaleAt _).isClosed_compl.isLocallyClosed
  let point : 𝟙_ (Over (Spec (.of k))) ⟶ A := Over.homMk
    ((pointEquivClosedPoint A.hom).symm ⟨y, hyclosed⟩).1
    ((pointEquivClosedPoint A.hom).symm ⟨y, hyclosed⟩).2
  have hpoint : point.left (IsLocalRing.closedPoint k) = y :=
    congrArg Subtype.val ((pointEquivClosedPoint A.hom).apply_symm_apply ⟨y, hyclosed⟩)
  exact hy ((mulRight_identity_point A point (IsLocalRing.closedPoint k)).trans hpoint ▸
    (etaleAt_zpow_id_translation A point d _).mpr
    (etaleAt_zpow_id_identity_of_isUnit k A _ d hd))

/-- **Multiplication by an invertible integer on an abelian variety is étale.** The statement
over the algebraic closure descends along Tag 0476, whose flat morphism here is the field
extension; the projection from the base change is surjective, so every point is reached. -/
theorem etale_zpow_id_of_isUnit (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    [AlgebraicGeometry.IsAbelianVariety k A] (d : ℤ) (hd : IsUnit ((d : ℤ) : k)) :
    Etale (((𝟙 A : A ⟶ A) ^ d).left) := by
  let Ω := AlgebraicClosure k
  let base : Spec (.of Ω) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let F := Over.pullback base
  let A' := F.obj A
  let : GrpObj A' := AlgebraicGeometry.grpObjPullbackObj A
  have : AlgebraicGeometry.IsAbelianVariety Ω A' :=
    AlgebraicGeometry.isAbelianVariety_pullbackObj A
  let original : A.left ⟶ A.left := ((𝟙 A : A ⟶ A) ^ d).left
  let shifted : A'.left ⟶ A'.left := ((𝟙 A' : A' ⟶ A') ^ d).left
  let projection : A'.left ⟶ A.left := pullback.fst A.hom base
  have hbase := (IsPullback.of_hasPullback A.hom base).flip
  have hmap : F.map ((𝟙 A : A ⟶ A) ^ d) = (𝟙 A' : A' ⟶ A') ^ d := by
    have h := map_zpow (F.homMonoidHom (X := A) (M := A)) (𝟙 A) d
    change F.map ((𝟙 A : A ⟶ A) ^ d) = (F.map (𝟙 A : A ⟶ A)) ^ d at h
    rw [h, F.map_id]
  have hmapLeft : shifted = (F.map ((𝟙 A : A ⟶ A) ^ d)).left :=
    (congrArg Over.Hom.left hmap).symm
  have hcomm : shifted ≫ projection = projection ≫ original := by
    rw [hmapLeft]
    dsimp [F, Over.pullback, projection, original]
    exact pullback.lift_fst _ _ _
  have hcommBase : shifted ≫ A'.hom = A'.hom := ((𝟙 A' : A' ⟶ A') ^ d).w
  have hpull : IsPullback shifted projection projection original := by
    apply IsPullback.of_right (t := hbase)
    · show IsPullback (shifted ≫ A'.hom) projection base (original ≫ A.hom)
      rw [hcommBase, show original ≫ A.hom = A.hom from ((𝟙 A : A ⟶ A) ^ d).w]
      exact hbase
    · exact hcomm
  have : LocallyOfFinitePresentation original := locallyOfFinitePresentation_zpow_id_left A d
  have hflatBase : Flat base := by
    rw [AlgebraicGeometry.Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective base := ⟨Function.surjective_to_subsingleton _⟩
  have hflatProjection : Flat projection :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
      hbase hflatBase
  have : Surjective projection :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      hbase inferInstance
  rw [AlgebraicGeometry.etale_iff_forall_etaleAt]
  intro x
  obtain ⟨x', hx'⟩ := projection.surjective x
  exact hx' ▸ (AlgebraicGeometry.etaleAt_iff_of_isPullback hpull.flip
    (Or.inr hflatProjection) x').mpr
    ((AlgebraicGeometry.etale_iff_forall_etaleAt _).mp
      (etale_zpow_id_of_isAlgClosed_of_isUnit Ω A' d
        (by simpa only [map_intCast] using hd.map (algebraMap k Ω))) x')

/-- **Stacks Project, Tag 0BFH.** Let `k` be a field and let `A` be a nonzero abelian variety
over `k`.  Then `[d] : A → A` is étale if and only if `d` is invertible in `k`.

Nonzeroness is the positivity of the topological Krull dimension, and it is used: it is what
makes the relative tangent space at the identity nonzero, so that multiplication by `d` on that
space is injective only for `d` invertible.  If `k` has characteristic `p` and `p` divides `d`
then the derivative of `[d]` at the identity vanishes, and `[d]` is not étale. -/
@[stacks 0BFH]
theorem etale_zpow_id_iff_isUnit_intCast (k : Type u) [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [AlgebraicGeometry.IsAbelianVariety k A] (hA : 0 < topologicalKrullDim A.left)
    (d : ℤ) :
    Etale (((𝟙 A : A ⟶ A) ^ d).left) ↔ IsUnit ((d : ℤ) : k) := by
  refine ⟨fun h => ?_, etale_zpow_id_of_isUnit k A d⟩
  exact (unramifiedAt_zpow_id_identity_iff_isUnit k A hA (IsLocalRing.closedPoint k) d).mp
    ((AlgebraicGeometry.etaleAt_iff_smoothAt_and_unramifiedAt _ _).mp
      ((AlgebraicGeometry.etale_iff_forall_etaleAt _).mp h _)).2

end Stacks.Groupoids

end
