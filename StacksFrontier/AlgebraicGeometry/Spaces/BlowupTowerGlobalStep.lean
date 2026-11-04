module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAtClosedPointExistenceUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTowerEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding

/-!
# A global blowing up at a closed point restricting to a prescribed local one

Let `S` be a scheme, let `X` be a decent algebraic space over `S`, let `x₁, …, xₙ ∈ |X|` be
pairwise distinct closed points and let `(Uᵢ, uᵢ) → (X, xᵢ)` be the elementary étale
neighborhoods chosen in Stacks 0BH9, that is a term `D : ClosedPointNeighborhoods B S hS n`.

`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_preimage_closedPointSubspace` restricts
a blowing up at a closed point of a space `Z` over `X` lying over `xᵢ` to a blowing up of
`Z ×_X Uᵢ` at a closed point lying over `uᵢ`.  This file runs that step **backwards**, which is
what the inductive step of the "if" direction of Stacks 0BHF asks for: a closed point of
`Z ×_X Uᵢ` lying over `uᵢ` is the inverse image of a closed point of `Z` lying over `xᵢ`, and
the blowing up of `Z` at that point restricts to the blowing up of `Z ×_X Uᵢ` at the given
point.

## Main results

* `Space.ClosedPointNeighborhoods.exists_closedPoint_preimage_closedPointSubspace`:
  a closed point `z` of `Z ×_X Uᵢ` lying over `uᵢ` is carried by the projection to a closed point
  `w` of `Z` lying over `xᵢ`, and the inverse image of the reduced closed subspace on `{w}` is
  the reduced closed subspace on `{z}`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_isBlowupAtClosedPoint_restricting`:
  for such a `z` there is a blowing up of `Z` at a closed point lying over `xᵢ` whose base
  change along `Z ×_X Uᵢ ⟶ Z` is the blowing up at `z`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_blowupTower_step`: the same, phrased
  as the extension of a tower of blowings up over `X` with centres over `{x₁, …, xₙ}` by one
  step performing a prescribed local blowing up.
* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.isIso_of_ne_of_isBlowupAtClosedPoint`: the
  base change to `Uᵢ` of a blowing up at a closed point lying over `x_j` with `j ≠ i` is an
  isomorphism, so a step taken for one index leaves the other neighborhoods untouched.

## Implementation notes

### Why the projection carries the point to a closed point

The projection `p : P = Z ×_X Uᵢ ⟶ Z` is étale, so it is not a closed map and the image of a
closed point need not be closed.  What makes `p z` closed is that `z` lies in the fibre over
`xᵢ`: writing `A = g⁻¹{xᵢ} ⊆ Z` for the inverse image of the subspace `{xᵢ}` along the
structure morphism `g : Z ⟶ X`, the morphism `Uᵢ ⟶ X` carries the inverse image of `{xᵢ}`
isomorphically onto it — the second standing hypothesis of Stacks 0BGY, which is
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isIso_fromPreimage_pointSubspace` — and that
is inherited by the base change, so `p` carries the inverse image of `A` isomorphically onto
`A`.  The point `z` lies in that inverse image, because the reduced closed subspace on `{z}`
has image point `xᵢ` in `X` and so factors through `{xᵢ}` by Stacks 03JJ.  Both `A ⊆ Z` and its
inverse image in `P` are closed subspaces, their point maps are closed embeddings by
Stacks 0ABJ and 04CD, and `{z}` is closed; transporting along the isomorphism and pushing
forward along the closed embedding `|A| ⟶ |Z|` gives `{p z}` closed.

The identification of the inverse image of the centre is then
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_preimage_closedPointSubspace` applied
to `p z`: it produces *some* closed point of `P` over `uᵢ` cutting out that inverse image, and
that point is `z`, because the reduced closed subspace on `{z}` is contained in the inverse
image and two reduced closed subspaces on single points are nested only when the points agree.

### What this does and does not supply for Stacks 0BHF

The inductive step of the source's "if" direction needs three things at each stage: the
existence of the blowing up of an intermediate space at a closed point, the transport of a
closed point of the local fibre to the global space, and the identification of the top of the
assembled global tower with the given `Y`.  The first is
`AlgebraicGeometry.Space.exists_isBlowupAtClosedPoint_unconditional`; the second is this file;
the third is the fullness of the functor `F` of Stacks 0BHA, the half of Stacks 0BHB the source
omits ("We omit the proof of fully faithfulness"), proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ModificationsAtClosedPointsFullyFaithful.lean`.  The
induction itself is in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupTowerGlobalConverse.lean`; nothing here is a
statement of Stacks 0BHF, so no `@[stacks 0BHF]` attribute is attached.

Of the two forms of the step, it is
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_isBlowupAtClosedPoint_restricting` and
not `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_blowupTower_step` that the
induction consumes: the latter hides the global centre `w` and the fact that the new step is the
blowing up at it, and
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.isIso_of_ne_of_isBlowupAtClosedPoint` needs
both in order to say that the step leaves the other neighborhoods untouched.

## References

* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
* [Stacks Project, Tag 0BHA](https://stacks.math.columbia.edu/tag/0BHA)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 085V](https://stacks.math.columbia.edu/tag/085V)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The reduced closed subspace on a closed set `T` of `Y` lies in the inverse image of a closed
subspace `A` of `X` along `f : Y ⟶ X` as soon as `f` carries its points into the points of `A`. -/
theorem reducedClosedSubspace_le_preimage_of_range_subset
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {T : Set (points B S hS Y)} (hT : IsClosed T)
    {A : Subfunctor X} (hA : IsClosedSubspace B S hS A) (f : Y ⟶ X)
    (h : Set.range (pointsMap B S hS _ ((reducedClosedSubspace B S hS Y hY T hT).ι ≫ f)) ⊆
      Set.range (pointsMap B S hS A.toFunctor A.ι)) :
    reducedClosedSubspace B S hS Y hY T hT ≤ A.preimage f := by
  obtain ⟨m, hm⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hX
    (isAlgebraicSpace_reducedClosedSubspace B S hS Y hY T hT) A hA
    (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS Y hY T hT) _).2 h
  have h' := Subfunctor.range_comp_le
    ((Subfunctor.isPullback_preimage f A).lift m (reducedClosedSubspace B S hS Y hY T hT).ι hm)
    (A.preimage f).ι
  rwa [(Subfunctor.isPullback_preimage f A).lift_snd m _ hm, Subfunctor.range_ι,
    Subfunctor.range_ι] at h'

/-- A closed point `z` lies in the subspace `A` as soon as the reduced closed subspace on `{z}`
does. -/
private theorem exists_pointsMap_ι_eq_of_range_ι_le {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {z : points B S hS Y} (hz : IsClosed ({z} : Set _))
    {A : Subfunctor Y}
    (hle : Subfunctor.range (reducedClosedSubspace B S hS Y hY {z} hz).ι ≤ A) :
    ∃ a, pointsMap B S hS A.toFunctor A.ι a = z := by
  obtain ⟨c, hc⟩ : z ∈ Set.range (pointsMap B S hS _
      (reducedClosedSubspace B S hS Y hY {z} hz).ι) := by
    rw [range_pointsMap_ι_reducedClosedSubspace]
    rfl
  exact ⟨pointsMap B S hS _ (Subfunctor.lift _ hle) c, by
    rw [← pointsMap_comp_apply, Subfunctor.lift_ι, hc]⟩

/-- A point mapping to a closed point under a monomorphism is closed. -/
theorem isClosed_singleton_of_pointsMap_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) [Mono f] {x : points B S hS F} {y : points B S hS G}
    (hy : IsClosed ({y} : Set (points B S hS G))) (hxy : pointsMap B S hS F f x = y) :
    IsClosed ({x} : Set (points B S hS F)) := by
  have hpre : ({x} : Set (points B S hS F)) = pointsMap B S hS F f ⁻¹' {y} := by
    ext x'
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ hxy, fun h => pointsMap_injective_of_mono B S hS f (h.trans hxy.symm)⟩
  rw [hpre]
  exact hy.preimage (continuous_pointsMap B S hS f)

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-! ### Transporting a closed point of the local fibre to the global space -/

/-- The base change of a blowing up at a closed point `w` of `Z` along `Z ×_X Uᵢ ⟶ Z` is a
blowing up along the inverse image of the centre. -/
private theorem isBlowupAlong_preimage_of_isPullback_toSpaceHom
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {Z Z' P P' : AlgebraicSpaces B S hS} {i : Fin n}
    {g : Z ⟶ D.space} {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q g (D.toSpaceHom i)) {w : points B S hS Z.obj}
    {hw : IsClosed ({w} : Set (points B S hS Z.obj))} {b : Z' ⟶ Z}
    (hb : IsBlowupAtClosedPoint B S hS w hw b) {r : P' ⟶ P} {s : P' ⟶ Z'}
    (sqr : IsPullback r s p b) :
    IsBlowupAlong B S hS (preimageClosedSubspace p (closedPointSubspace B S hS w hw)) r :=
  isBlowupAlong_preimage_of_isBlowupAtClosedPoint (isFlat_of_isEtale B S hS
    (isEtale_of_isPullback B S hS q p (D.toSpaceHom i) g sq.flip (D.isEtale_toSpaceHom i))) hb sqr

/-- If `P = Z ×_X Uᵢ` and `z` is a closed point of `P` whose image in `Z` lies over `xᵢ`, then
the image of `z` in `Z` is closed. -/
theorem isClosed_singleton_pointsMap_of_isPullback {Z P : AlgebraicSpaces B S hS}
    {i : Fin n} {g : Z ⟶ D.space} {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q g (D.toSpaceHom i)) {z : points B S hS P.obj}
    (hz : IsClosed ({z} : Set (points B S hS P.obj)))
    (hgw : pointsMap B S hS Z.obj g.hom (pointsMap B S hS P.obj p.hom z) = D.point i) :
    IsClosed ({pointsMap B S hS P.obj p.hom z} : Set (points B S hS Z.obj)) := by
  have hAcl : IsClosedSubspace B S hS ((D.pointSubspace i).preimage g.hom) :=
    isClosedSubspace_preimage B S hS g.hom (D.pointSubspace i) D.space.property Z.property
      (D.isClosedSubspace_pointSubspace i)
  have hAPcl : IsClosedSubspace B S hS
      (((D.pointSubspace i).preimage g.hom).preimage p.hom) :=
    isClosedSubspace_preimage B S hS p.hom _ Z.property P.property hAcl
  have hIso : IsIso (((D.pointSubspace i).preimage g.hom).fromPreimage p.hom) :=
    Subfunctor.isIso_fromPreimage_of_le_preimage (AlgebraicSpaces.isPullback_hom B S hS sq)
      (D.pointSubspace i) (D.isIso_fromPreimage_pointSubspace i) _ le_rfl
  have hle : Subfunctor.range (reducedClosedSubspace B S hS P.obj P.property {z} hz).ι ≤
      ((D.pointSubspace i).preimage g.hom).preimage p.hom := by
    rw [Subfunctor.range_ι, ← Subfunctor.preimage_comp]
    refine reducedClosedSubspace_le_preimage_of_range_subset D.space.property P.property hz
      (D.isClosedSubspace_pointSubspace i) _ ?_
    rw [D.range_pointsMap_ι_pointSubspace i]
    rintro y ⟨c, rfl⟩
    rw [pointsMap_comp_apply, pointsMap_comp_apply,
      pointsMap_ι_reducedClosedSubspace_singleton z hz c]
    exact Set.mem_singleton_iff.2 hgw
  obtain ⟨a, hztz⟩ := exists_pointsMap_ι_eq_of_range_ι_le P.property hz hle
  have hmonoAP : Mono (((D.pointSubspace i).preimage g.hom).preimage p.hom).ι :=
    mono_of_isClosedImmersion B S hS _ hAPcl.2
  have hwtclosed := isClosed_singleton_of_pointsMap_eq
    (inv (((D.pointSubspace i).preimage g.hom).fromPreimage p.hom))
    (x := pointsMap B S hS _ (((D.pointSubspace i).preimage g.hom).fromPreimage p.hom) a)
    (isClosed_singleton_of_pointsMap_eq _ hz hztz)
    (by rw [← pointsMap_comp_apply, IsIso.hom_inv_id, pointsMap_id, id_eq])
  have hce : Topology.IsClosedEmbedding
      (pointsMap B S hS ((D.pointSubspace i).preimage g.hom).toFunctor
        ((D.pointSubspace i).preimage g.hom).ι) :=
    ⟨isEmbedding_pointsMap_of_isImmersion B S hS Z.property _
        (isImmersion_of_isClosedImmersion B S hS hAcl.2),
      isClosed_range_pointsMap_of_isClosedImmersion B S hS Z.property _ hAcl.2⟩
  have himg := hce.isClosedMap _ hwtclosed
  rwa [Set.image_singleton, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι,
    pointsMap_comp_apply, hztz] at himg

/-- **A closed point of `Z ×_X Uᵢ` lying over `uᵢ` is the inverse image of a closed point of `Z`
lying over `xᵢ`.**

Let `p : P ⟶ Z`, `q : P ⟶ Uᵢ` exhibit `P = Z ×_X Uᵢ` over a morphism `g : Z ⟶ X`, and let `z`
be a closed point of `P` with `q z = uᵢ`.  Then `w = p z` is a closed point of `Z` with
`g w = xᵢ`, and the inverse image along `p` of the reduced closed subspace on `{w}` is the
reduced closed subspace on `{z}`.

This is the converse of
`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_preimage_closedPointSubspace`; see the
implementation notes of this file for why `{p z}` is closed. -/
theorem exists_closedPoint_preimage_closedPointSubspace {Z P : AlgebraicSpaces B S hS}
    {i : Fin n} {g : Z ⟶ D.space} {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q g (D.toSpaceHom i)) {z : points B S hS P.obj}
    (hz : IsClosed ({z} : Set (points B S hS P.obj)))
    (hzq : pointsMap B S hS P.obj q.hom z = D.neighborhoodPoint i) :
    ∃ (w : points B S hS Z.obj) (hw : IsClosed ({w} : Set (points B S hS Z.obj))),
      pointsMap B S hS Z.obj g.hom w = D.point i ∧
        (closedPointSubspace B S hS w hw).1.preimage p.hom =
          (closedPointSubspace B S hS z hz).1 := by
  classical
  have hw0 : p.hom ≫ g.hom = q.hom ≫ (D.toSpaceHom i).hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
      sq.w]
  have hgw : pointsMap B S hS Z.obj g.hom (pointsMap B S hS P.obj p.hom z) = D.point i := by
    have hmp : pointsMap B S hS (D.neighborhoodSpace i).obj (D.toSpaceHom i).hom
        (D.neighborhoodPoint i) = D.point i := (D.neighborhood i).map_point
    have h := pointsMap_apply_comm B S hS hw0 z
    rwa [hzq, hmp] at h
  have hwclosed := D.isClosed_singleton_pointsMap_of_isPullback sq hz hgw
  refine ⟨pointsMap B S hS P.obj p.hom z, hwclosed, hgw, ?_⟩
  obtain ⟨w', hw', -, hw'pre⟩ := D.exists_preimage_closedPointSubspace sq hwclosed hgw
  have hcps : (closedPointSubspace B S hS (pointsMap B S hS P.obj p.hom z) hwclosed).1 =
      reducedClosedSubspace B S hS Z.obj Z.property
        {pointsMap B S hS P.obj p.hom z} hwclosed := rfl
  have hle : Subfunctor.range (reducedClosedSubspace B S hS P.obj P.property {z} hz).ι ≤
      (closedPointSubspace B S hS w' hw').1 := by
    rw [Subfunctor.range_ι, ← hw'pre]
    refine reducedClosedSubspace_le_preimage_of_range_subset Z.property P.property hz
      (closedPointSubspace B S hS (pointsMap B S hS P.obj p.hom z) hwclosed).2 _ ?_
    rw [hcps, range_pointsMap_ι_reducedClosedSubspace]
    rintro y ⟨c, rfl⟩
    rw [pointsMap_comp_apply, pointsMap_ι_reducedClosedSubspace_singleton z hz c]
    rfl
  have hmem : z ∈ Set.range (pointsMap B S hS (closedPointSubspace B S hS w' hw').1.toFunctor
      (closedPointSubspace B S hS w' hw').1.ι) :=
    exists_pointsMap_ι_eq_of_range_ι_le P.property hz hle
  have hcps' : (closedPointSubspace B S hS w' hw').1 =
      reducedClosedSubspace B S hS P.obj P.property {w'} hw' := rfl
  rw [hcps', range_pointsMap_ι_reducedClosedSubspace] at hmem
  obtain rfl : z = w' := hmem
  exact hw'pre

/-! ### The global blowing up restricting to a prescribed local one -/

/-- **The blowing up of `Z` at a closed point over `xᵢ` realizing a prescribed blowing up of
`Z ×_X Uᵢ` at a closed point over `uᵢ`.**

Let `p : P ⟶ Z`, `q : P ⟶ Uᵢ` exhibit `P = Z ×_X Uᵢ` over `g : Z ⟶ X`, and let `z` be a closed
point of `P` with `q z = uᵢ`.  Then there is a closed point `w` of `Z` lying over `xᵢ` and a
blowing up `b : Z' ⟶ Z` of `Z` at `w`, whose base change along `p` is the blowing up of `P`
at `z`.

The blowing up exists by `AlgebraicGeometry.Space.exists_isBlowupAtClosedPoint_unconditional`;
its base change is a blowing up in the inverse image of the centre by Stacks 085S, and that
inverse image is the reduced closed subspace on `{z}` by
`Space.ClosedPointNeighborhoods.exists_closedPoint_preimage_closedPointSubspace`. -/
theorem exists_isBlowupAtClosedPoint_restricting
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] {Z P : AlgebraicSpaces B S hS}
    {i : Fin n} {g : Z ⟶ D.space} {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q g (D.toSpaceHom i)) {z : points B S hS P.obj}
    (hz : IsClosed ({z} : Set (points B S hS P.obj)))
    (hzq : pointsMap B S hS P.obj q.hom z = D.neighborhoodPoint i) :
    ∃ (w : points B S hS Z.obj) (hw : IsClosed ({w} : Set (points B S hS Z.obj)))
      (Z' : AlgebraicSpaces B S hS) (b : Z' ⟶ Z),
      pointsMap B S hS Z.obj g.hom w = D.point i ∧
        IsBlowupAtClosedPoint B S hS w hw b ∧
        ∀ {P' : AlgebraicSpaces B S hS} {r : P' ⟶ P} {s : P' ⟶ Z'},
          IsPullback r s p b → IsBlowupAtClosedPoint B S hS z hz r := by
  obtain ⟨w, hw, hgw, hpre⟩ := D.exists_closedPoint_preimage_closedPointSubspace sq hz hzq
  obtain ⟨Z', b, hb⟩ := exists_isBlowupAtClosedPoint_unconditional w hw
  refine ⟨w, hw, Z', b, hgw, hb, ?_⟩
  intro P' r s sqr
  have hblow := D.isBlowupAlong_preimage_of_isPullback_toSpaceHom sq hb sqr
  refine isBlowupAtClosedPoint_of_isBlowupAlong ?_
  have he : preimageClosedSubspace p (closedPointSubspace B S hS w hw) =
      closedPointSubspace B S hS z hz := Subtype.ext hpre
  rw [← he]
  exact hblow

/-- **Extending a tower of blowings up over `X` by a step performing a prescribed local blowing
up.**

Let `t` be a tower of blowings up over `X` with top `Z` and centres over `{x₁, …, xₙ}`, let
`p : P ⟶ Z`, `q : P ⟶ Uᵢ` exhibit `P = Z ×_X Uᵢ` over the structure morphism of the tower, and
let `z` be a closed point of `P` lying over `uᵢ`.  Then `t` extends by one step `b : Z' ⟶ Z`,
again with centres over `{x₁, …, xₙ}`, whose base change along `p` is the blowing up of `P`
at `z`.

This is the step of the induction of the source's "if" direction of Stacks 0BHF which builds the
global tower; what it does not supply is the identification of the top of the completed tower
with the given `Y`, which is the fullness of the functor `F` of Stacks 0BHA. -/
theorem exists_blowupTower_step [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (i : Fin n) {Z P : AlgebraicSpaces B S hS} (t : BlowupTower B S hS D.space Z)
    (hcent : t.CentersOver (Set.range D.point)) {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q t.proj (D.toSpaceHom i)) {z : points B S hS P.obj}
    (hz : IsClosed ({z} : Set (points B S hS P.obj)))
    (hzq : pointsMap B S hS P.obj q.hom z = D.neighborhoodPoint i) :
    ∃ (Z' : AlgebraicSpaces B S hS) (b : Z' ⟶ Z) (t' : BlowupTower B S hS D.space Z'),
      t'.CentersOver (Set.range D.point) ∧ t'.length = t.length + 1 ∧
        t'.proj = b ≫ t.proj ∧
        ∀ {P' : AlgebraicSpaces B S hS} {r : P' ⟶ P} {s : P' ⟶ Z'},
          IsPullback r s p b → IsBlowupAtClosedPoint B S hS z hz r := by
  obtain ⟨w, hw, Z', b, hgw, hb, hrest⟩ :=
    D.exists_isBlowupAtClosedPoint_restricting sq hz hzq
  refine ⟨Z', b, .step t b w hw hb, ?_, ?_, ?_, ?_⟩
  · rw [BlowupTower.centersOver_step]
    exact ⟨hcent, i, hgw.symm⟩
  · rw [BlowupTower.length_step]
  · rw [BlowupTower.proj_step]
  · exact hrest

/-- **A step taken over `x_j` leaves the `i`th neighborhood untouched, for `j ≠ i`.**  The base
change along `Z ×_X Uᵢ ⟶ Z` of the blowing up of `Z` at a closed point lying over `x_j` with
`j ≠ i` is an isomorphism.

No point of `Uᵢ` lies over `x_j`, by the shrinking condition of Stacks 0BH9, so the inverse
image of the centre has no points; it is then an effective Cartier divisor and the base-changed
blowing up is an isomorphism by Stacks 085V. -/
theorem isIso_of_ne_of_isBlowupAtClosedPoint {Z Z' P P' : AlgebraicSpaces B S hS} {i j : Fin n}
    (hij : i ≠ j) {g : Z ⟶ D.space} {p : P ⟶ Z} {q : P ⟶ D.neighborhoodSpace i}
    (sq : IsPullback p q g (D.toSpaceHom i)) {w : points B S hS Z.obj}
    {hw : IsClosed ({w} : Set (points B S hS Z.obj))}
    (hwj : pointsMap B S hS Z.obj g.hom w = D.point j) {b : Z' ⟶ Z}
    (hb : IsBlowupAtClosedPoint B S hS w hw b) {r : P' ⟶ P} {s : P' ⟶ Z'}
    (sqr : IsPullback r s p b) : IsIso r := by
  have hempty := D.isEmpty_points_preimage_closedPointSubspace hij sq (hz := hw) hwj
  have hblow := D.isBlowupAlong_preimage_of_isPullback_toSpaceHom sq hb sqr
  exact hblow.isIso_of_isEffectiveCartierDivisor
    (isEffectiveCartierDivisor_of_isEmpty_points B S hS _ _ hempty)

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space

end
