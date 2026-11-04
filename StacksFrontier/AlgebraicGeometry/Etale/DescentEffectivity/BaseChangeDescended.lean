module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Defs

/-!
# Base change of a scheme descending a descent datum

Let `a : X ⟶ S` be a morphism of schemes, let `D` be a descent datum relative to `X / S` and
let `U` be a scheme over `S` descending it, in the sense of
`AlgebraicGeometry.DescentDatum.Descended`: a projection `V ⟶ U` exhibiting `V` as `X ×_S U`
and equalising the two legs of the gluing isomorphism. Pulling the whole picture back along a
commutative square makes `S' ×_S U` a scheme descending the pulled-back datum.

The projection of the base change is written out, rather than obtained from an abstract
isomorphism with a canonical descent datum: its two components are the projection of `U` base
changed and the structure morphism of the pulled-back datum.

## Main definitions

* `AlgebraicGeometry.DescentDatum.Descended.pullbackSquare`: **the base change along a
  commutative square of a scheme descending a descent datum.**
* `AlgebraicGeometry.DescentDatum.Descended.changeDatum`: the special case of the cartesian
  square over a morphism of the base, a scheme descending
  `AlgebraicGeometry.DescentDatum.changeDatum`.
* `AlgebraicGeometry.DescentDatum.Descended.ofDatumIso` and
  `AlgebraicGeometry.DescentDatum.Descended.ofBaseIso`: transport of a descended scheme along an
  isomorphism of descent data, respectively along an isomorphism of the descended scheme.
* `AlgebraicGeometry.DescentDatum.Descended.compareOfFullyFaithful` and
  `AlgebraicGeometry.DescentDatum.Descended.compareIsoOfFullyFaithful`: the comparison of two
  schemes descending one datum, for a fully faithful étale descent functor.

## Main results

* `AlgebraicGeometry.DescentDatum.Descended.pullbackSquareProj_comp_fst` and
  `...pullbackSquareProj_comp_snd`: the two components of the projection of the base change.
* `AlgebraicGeometry.DescentDatum.Descended.proj_comp_compareOfFullyFaithful` and
  `...eq_compareOfFullyFaithful`: the comparison is the unique morphism over the base compatible
  with the two projections, and `...isIso_compareOfFullyFaithful` that it is an isomorphism.

## Implementation notes

The invariance of the base-changed projection under the gluing isomorphism is the only point
with content, and it is read off the three equations that
`AlgebraicGeometry.DescentData.PullbackFunctor` carries: the pulled-back gluing isomorphism is
the original one conjugated by the induced maps of the self-fibre products, and those maps have
prescribed components. Composed with the projection onto the descended scheme the conjugation
turns the invariance of the original projection into the invariance of the new one; composed
with the projection onto `S'` both sides are the structure morphism, so there is nothing to
prove there.

The comparison of two descended schemes already exists for a surjective flat quasi-compact
morphism, where the projections are epimorphisms
(`AlgebraicGeometry.DescentDatum.Descended.compare`). Along an integral morphism they are not,
and the comparison has to come from full faithfulness of the étale descent functor instead;
`AlgebraicGeometry.DescentDatum.Descended.existsUnique_hom_comp_proj_eq` supplies it.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum.Descended

/-! ### Base change along a commutative square -/

section PullbackSquare

variable {S S' X X' : Scheme.{u}} {a : X ⟶ S} {a' : X' ⟶ S'} {h : S' ⟶ S} {p : X' ⟶ X}
  {comm : p ≫ a = a' ≫ h} (P : DescentData.PullbackFunctor a a' h p comm) {D : DescentDatum a}
  (Q : D.Descended)

include comm in
/-- The projection of the datum's scheme onto the descended scheme and the structure morphism
of the base change agree over `S`. -/
lemma pullbackSquare_cond :
    (pullback.fst D.over.hom p ≫ Q.proj) ≫ Q.base.hom = (pullback.snd D.over.hom p ≫ a') ≫ h := by
  rw [Category.assoc, Q.proj_comp_base_hom, ← Category.assoc, pullback.condition, Category.assoc,
    comm, ← Category.assoc]

/-- **The projection of the base change of a descended scheme along a commutative square**: on
the descended scheme it is the projection of the datum, on `S'` it is the structure morphism. -/
def pullbackSquareProj : (pullbackSquareDatum P D).over.left ⟶ pullback Q.base.hom h :=
  (P.objIso D).hom.left ≫ pullback.lift (pullback.fst D.over.hom p ≫ Q.proj)
    (pullback.snd D.over.hom p ≫ a') (pullbackSquare_cond (comm := comm) Q)

/-- The structure morphism of the pulled-back datum, read through the identification of its
scheme with the base change. -/
@[reassoc]
lemma objIso_hom_left_comp_snd :
    (P.objIso D).hom.left ≫ pullback.snd D.over.hom p = (pullbackSquareDatum P D).over.hom :=
  Over.w (P.objIso D).hom

/-- The component on the descended scheme of the projection of the base change is the
projection of the datum composed with the projection `Q.proj`. -/
@[reassoc]
lemma pullbackSquareProj_comp_fst :
    pullbackSquareProj P Q ≫ pullback.fst Q.base.hom h =
      (P.objIso D).hom.left ≫ pullback.fst D.over.hom p ≫ Q.proj := by
  rw [pullbackSquareProj, Category.assoc, pullback.lift_fst]

/-- The component on `S'` of the projection of the base change is the structure morphism of the
pulled-back datum followed by `a'`. -/
@[reassoc]
lemma pullbackSquareProj_comp_snd :
    pullbackSquareProj P Q ≫ pullback.snd Q.base.hom h =
      (pullbackSquareDatum P D).over.hom ≫ a' := by
  rw [pullbackSquareProj, Category.assoc, pullback.lift_snd, ← Category.assoc,
    objIso_hom_left_comp_snd]

/-- **The base change along a commutative square of a scheme descending a descent datum.** -/
def pullbackSquare : (pullbackSquareDatum P D).Descended where
  base := (Over.pullback h).obj Q.base
  proj := pullbackSquareProj P Q
  isPullback := by
    refine (IsPullback.paste_vert_iff (IsPullback.of_hasPullback Q.base.hom h).flip
      (pullbackSquareProj_comp_snd P Q).symm).mp ?_
    have hbig : IsPullback (pullback.snd D.over.hom p)
        (pullback.fst D.over.hom p ≫ Q.proj) (p ≫ a) Q.base.hom :=
      (IsPullback.of_hasPullback D.over.hom p).flip.paste_vert Q.isPullback
    refine hbig.of_iso' ((Over.forget X').mapIso (P.objIso D)) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp [comm]) (by simp)
    · simpa using objIso_hom_left_comp_snd (P := P) (D := D)
    · simpa using (pullbackSquareProj_comp_fst P Q).symm
  proj_invariant := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullbackSquareProj_comp_fst]
      rw [← reassoc_of% (P.targetMap_snd D), ← reassoc_of% (P.sourceMap_fst D),
        reassoc_of% (P.gluing D), Q.proj_invariant]
    · simp only [Category.assoc, pullbackSquareProj_comp_snd]
      rw [reassoc_of% ((pullbackSquareDatum P D).gluingPullbackIso_hom_snd () ()),
        pullback.condition]

/-- The descended scheme of the base change is the pullback of `Q.base` along `h`. -/
@[simp]
lemma pullbackSquare_base : (pullbackSquare P Q).base = (Over.pullback h).obj Q.base := rfl

/-- The projection of the base change is `pullbackSquareProj`. -/
@[simp]
lemma pullbackSquare_proj : (pullbackSquare P Q).proj = pullbackSquareProj P Q := rfl

/-- The base change of an étale descended scheme is étale over `S'`. -/
instance etale_pullbackSquare_base_hom [Etale Q.base.hom] :
    Etale (pullbackSquare P Q).base.hom := by
  change Etale (pullback.snd Q.base.hom h)
  infer_instance

end PullbackSquare

/-! ### Transport along isomorphisms -/

section Transport

variable {S X : Scheme.{u}} {f : X ⟶ S} {D E : DescentDatum f}

/-- **A scheme descending a descent datum descends every isomorphic datum.** -/
def ofDatumIso (Q : D.Descended) (e : E ≅ D) : E.Descended where
  base := Q.base
  proj := (e.hom.hom ()).left ≫ Q.proj
  isPullback := by
    refine Q.isPullback.of_iso'
      ((Over.forget X).mapIso ((DescentData.evaluation ()).mapIso e))
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp) (by simp)
    simp
  proj_invariant := Q.comp_proj_invariant e.hom

/-- Transport along an isomorphism of descent data does not change the descended scheme. -/
@[simp]
lemma ofDatumIso_base (Q : D.Descended) (e : E ≅ D) : (Q.ofDatumIso e).base = Q.base := rfl

/-- The projection of the transported descended scheme is the isomorphism of data followed by
`Q.proj`. -/
@[simp]
lemma ofDatumIso_proj (Q : D.Descended) (e : E ≅ D) :
    (Q.ofDatumIso e).proj = (e.hom.hom ()).left ≫ Q.proj := rfl

/-- **A scheme descending a descent datum may be replaced by an isomorphic scheme over the
base.** -/
def ofBaseIso (Q : D.Descended) {B : Over S} (b : Q.base ≅ B) : D.Descended where
  base := B
  proj := Q.proj ≫ b.hom.left
  isPullback := by
    refine Q.isPullback.of_iso' (Iso.refl _) (Iso.refl _)
      ((Over.forget S).mapIso b).symm (Iso.refl _) (by simp) ?_ (by simp) ?_
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, Functor.mapIso_inv,
        Over.forget_map, Category.assoc]
      rw [← Over.comp_left, b.hom_inv_id, Over.id_left, Category.comp_id]
    · simp
  proj_invariant := by
    rw [reassoc_of% Q.proj_invariant]

/-- The descended scheme of `Q.ofBaseIso b` is the target `B` of `b`. -/
@[simp]
lemma ofBaseIso_base (Q : D.Descended) {B : Over S} (b : Q.base ≅ B) :
    (Q.ofBaseIso b).base = B := rfl

/-- The projection of `Q.ofBaseIso b` is `Q.proj` followed by `b`. -/
@[simp]
lemma ofBaseIso_proj (Q : D.Descended) {B : Over S} (b : Q.base ≅ B) :
    (Q.ofBaseIso b).proj = Q.proj ≫ b.hom.left := rfl

end Transport

/-! ### Base change along a morphism of the base -/

section ChangeDatum

variable {S X T : Scheme.{u}} {f : X ⟶ S} {D : DescentDatum f} (Q : D.Descended) (g : T ⟶ S)

/-- **The base change along a morphism of the base of a scheme descending a descent datum.** -/
abbrev changeDatum : (D.changeDatum g).Descended :=
  pullbackSquare (changePullbackFunctor f g) Q

end ChangeDatum

/-! ### Comparing two descended schemes through full faithfulness -/

section Compare

variable {S X : Scheme.{u}} {f : X ⟶ S} {D : DescentDatum f}
  (hff : (etaleDescentFunctor f).FullyFaithful) (Q Q' Q'' : D.Descended)
  [Etale Q.base.hom] [Etale Q'.base.hom] [Etale Q''.base.hom]

/-- **The comparison of two schemes descending one datum**, for a fully faithful étale descent
functor: the unique morphism over the base compatible with the two projections. -/
def compareOfFullyFaithful : Q.base ⟶ Q'.base :=
  (existsUnique_hom_comp_proj_eq hff Q Q').choose

/-- The comparison morphism carries the projection of `Q` to the projection of `Q'`. -/
@[reassoc]
lemma proj_comp_compareOfFullyFaithful :
    Q.proj ≫ (compareOfFullyFaithful hff Q Q').left = Q'.proj :=
  (existsUnique_hom_comp_proj_eq hff Q Q').choose_spec.1

/-- Every morphism over the base carrying the projection of `Q` to the projection of `Q'` is the
comparison morphism. -/
lemma eq_compareOfFullyFaithful {e : Q.base ⟶ Q'.base} (he : Q.proj ≫ e.left = Q'.proj) :
    e = compareOfFullyFaithful hff Q Q' :=
  (existsUnique_hom_comp_proj_eq hff Q Q').choose_spec.2 e he

/-- The comparison of a descended scheme with itself is the identity. -/
@[simp]
lemma compareOfFullyFaithful_self : compareOfFullyFaithful hff Q Q = 𝟙 _ :=
  (eq_compareOfFullyFaithful hff Q Q (by rw [Over.id_left, Category.comp_id])).symm

/-- The comparison morphisms compose: comparing `Q` with `Q'` and then `Q'` with `Q''` is
comparing `Q` with `Q''`. -/
@[reassoc (attr := simp)]
lemma compareOfFullyFaithful_comp :
    compareOfFullyFaithful hff Q Q' ≫ compareOfFullyFaithful hff Q' Q'' =
      compareOfFullyFaithful hff Q Q'' :=
  eq_compareOfFullyFaithful hff Q Q'' (e := compareOfFullyFaithful hff Q Q' ≫
    compareOfFullyFaithful hff Q' Q'') (by
      rw [Over.comp_left, ← Category.assoc, proj_comp_compareOfFullyFaithful,
        proj_comp_compareOfFullyFaithful])

/-- The comparison morphism of two descended schemes is an isomorphism. -/
instance isIso_compareOfFullyFaithful : IsIso (compareOfFullyFaithful hff Q Q') :=
  ⟨compareOfFullyFaithful hff Q' Q,
    by rw [compareOfFullyFaithful_comp hff Q Q' Q, compareOfFullyFaithful_self],
    by rw [compareOfFullyFaithful_comp hff Q' Q Q', compareOfFullyFaithful_self]⟩

/-- **Two schemes descending one datum are isomorphic over the base**, for a fully faithful
étale descent functor. -/
def compareIsoOfFullyFaithful : Q.base ≅ Q'.base :=
  asIso (compareOfFullyFaithful hff Q Q')

/-- The forward morphism of `compareIsoOfFullyFaithful` is `compareOfFullyFaithful`. -/
@[simp]
lemma compareIsoOfFullyFaithful_hom :
    (compareIsoOfFullyFaithful hff Q Q').hom = compareOfFullyFaithful hff Q Q' := rfl

end Compare

end DescentDatum.Descended

end AlgebraicGeometry

end
