module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Descent

/-!
# Rigidity of a descended scheme under étale descent

Let `f : X ⟶ S` be a morphism of schemes and let `(V, φ)` be a descent datum relative to `X/S`.
A scheme `U` over `S` descending `(V, φ)` carries an isomorphism of `(V, φ)` with the canonical
descent datum of `U`, so two descended schemes which are étale over `S` have isomorphic
canonical data. If the étale descent functor of `f` is full, that isomorphism of data comes from
a morphism `U ⟶ U'` over `S`; if it is faithful, a morphism over `S` compatible with the two
projections is unique.

This is the étale counterpart of `AlgebraicGeometry.DescentDatum.Descended.compare`, which
obtains the same comparison from `f` being surjective, flat and quasi-compact. Here nothing is
asked of `f` beyond the behaviour of its étale descent functor.

## Main definitions

* `AlgebraicGeometry.DescentData.objIsoCanonical` and
  `AlgebraicGeometry.DescentData.isoCanonical`: the isomorphism of a descent datum with the
  canonical datum of a scheme exhibiting it as a fibre product by an invariant projection. This
  is the isomorphism underlying the effectivity criterion
  `AlgebraicGeometry.DescentData.isEffective_of_isPullback`.
* `AlgebraicGeometry.DescentDatum.Descended.canonicalIso`: the isomorphism of a descent datum
  with the canonical datum of a scheme descending it.

## Main results

* `AlgebraicGeometry.DescentData.canonicalProjection_naturality`: the projection of a canonical
  descent datum onto the scheme it is built from is natural.
* `AlgebraicGeometry.existsUnique_canonicalFunctor_map_eq_of_etale`: a morphism between the
  canonical data of two schemes étale over `S` is the canonical datum of exactly one morphism
  of schemes over `S`, when the étale descent functor is fully faithful.
* `AlgebraicGeometry.canonicalFunctor_map_injective_of_etale`: two morphisms of schemes étale
  over `S` with the same canonical datum are equal, when the étale descent functor is faithful.
* `AlgebraicGeometry.DescentDatum.Descended.existsUnique_hom_comp_proj_eq`: **two schemes
  descending one descent datum, étale over `S`, are uniquely isomorphic over `S`** — there is
  exactly one morphism over `S` compatible with the two projections.
* `AlgebraicGeometry.DescentDatum.Descended.eq_of_proj_comp_eq`: faithfulness alone makes such a
  morphism unique.

## Implementation notes

The effectivity criterion produces its witnessing isomorphism and then forgets it;
`isoCanonical` is that isomorphism, kept. Its construction is the one the criterion uses: the
fibre-product square identifies the scheme of the datum with `X ×_S U` over `X`, and the
compatibility of that identification with the two gluing isomorphisms is checked on the three
components of the target fibre product, two of them formal and the third the invariance of the
projection.

Full faithfulness is used through `CategoryTheory.ObjectProperty.FullSubcategory`: the étale
descent functor is the lift of the canonical functor to the descent data with étale underlying
scheme, so a morphism of its values is a morphism of the underlying canonical data, and
`AlgebraicGeometry.Scheme.Etale.forgetFullyFaithful` turns a morphism of schemes over `S`
between étale objects into a morphism of the small étale site. Uniqueness of the comparison
needs only faithfulness, which is why it is stated separately: on a triple overlap that is all
the hypothesis of [Stacks, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM) provides.

The comparison is unique only among morphisms *over `S`*: compatibility with the projections
pins a morphism down after composing with the projection of the source, and the projection is
an epimorphism only under hypotheses on `f` which are not available here.

## References

* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 0BTI](https://stacks.math.columbia.edu/tag/0BTI)
* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

namespace DescentData

variable {S X : Scheme.{u}}

/-- The projection of a canonical descent datum onto the scheme it is built from is natural in
that scheme. -/
@[reassoc]
lemma canonicalProjection_naturality (f : X ⟶ S) {U U' : Over S} (h : U ⟶ U') :
    (((canonicalFunctor f).map h).hom ()).left ≫ canonicalProjection f U' =
      canonicalProjection f U ≫ h.left := by
  have hlift : ((Over.pullback f).map h).left ≫ pullback.fst U'.hom f =
      pullback.fst U.hom f ≫ h.left := pullback.lift_fst _ _ _
  have key : ((canonicalObjIso f U).hom.left ≫ ((Over.pullback f).map h).left) ≫
        pullback.fst U'.hom f =
      ((((canonicalFunctor f).map h).hom ()).left ≫ (canonicalObjIso f U').hom.left) ≫
        pullback.fst U'.hom f := by
    refine congrArg (fun k ↦ k ≫ pullback.fst U'.hom f) ?_
    rw [← Over.comp_left, ← Over.comp_left]
    exact congrArg Over.Hom.left ((canonicalPullbackFunctor f).map ((trivialFunctor S).map h))
  rw [Category.assoc, Category.assoc, hlift] at key
  change (((canonicalFunctor f).map h).hom ()).left ≫
      ((canonicalObjIso f U').hom.left ≫ pullback.fst U'.hom f) =
    ((canonicalObjIso f U).hom.left ≫ pullback.fst U.hom f) ≫ h.left
  rw [Category.assoc]
  exact key.symm

section Criterion

variable {a : X ⟶ S} {D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ a)}
  (U : Over S) (φ : (D.obj ()).left ⟶ U.left) (hpb : IsPullback φ (D.obj ()).hom U.hom a)

/-- The scheme of a descent datum exhibited as `X ×_S U` by a projection onto `U`, identified
with the scheme of the canonical descent datum of `U`. -/
def objIsoCanonical : D.obj () ≅ ((canonicalFunctor a).obj U).obj () :=
  Over.isoMk hpb.isoPullback
      (by simpa only [Over.pullback_obj_hom] using hpb.isoPullback_hom_snd) ≪≫
    (canonicalObjIso a U).symm

/-- That identification carries the projection of the canonical datum to the given one. -/
@[reassoc]
lemma objIsoCanonical_hom_left_comp_canonicalProjection :
    (objIsoCanonical U φ hpb).hom.left ≫ canonicalProjection a U = φ := by
  have hcancel : (canonicalObjIso a U).inv.left ≫ (canonicalObjIso a U).hom.left =
      𝟙 ((Over.pullback a).obj U).left := by
    rw [← Over.comp_left, (canonicalObjIso a U).inv_hom_id, Over.id_left]
  change (Over.isoMk hpb.isoPullback _ ≪≫ (canonicalObjIso a U).symm).hom.left ≫
    (canonicalObjIso a U).hom.left ≫ pullback.fst U.hom a = φ
  rw [Iso.trans_hom, Over.comp_left, Iso.symm_hom, Category.assoc,
    ← Category.assoc ((canonicalObjIso a U).inv.left), hcancel, Category.id_comp]
  simpa only [Over.isoMk_hom_left] using hpb.isoPullback_hom_fst

variable (hinv : (D.gluingPullbackIso () ()).hom ≫
  pullback.snd a ((D.obj ()).hom ≫ a) ≫ φ = pullback.fst ((D.obj ()).hom ≫ a) a ≫ φ)

include hinv in
/-- The identification of the scheme of the datum with the scheme of the canonical datum is
compatible with the two gluing isomorphisms. The three components of the target fibre product
are checked separately: two of them are the base components of a gluing isomorphism and the
third is the invariance of the projection. -/
lemma srcPullbackMap_comp_objIsoCanonical :
    srcPullbackMap (objIsoCanonical U φ hpb).hom ≫
        (((canonicalFunctor a).obj U).gluingPullbackIso () ()).hom =
      (D.gluingPullbackIso () ()).hom ≫ tgtPullbackMap (objIsoCanonical U φ hpb).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, gluingPullbackIso_hom_fst', srcPullbackMap_fst_assoc,
      Category.assoc, tgtPullbackMap_fst, gluingPullbackIso_hom_fst',
      Over.w (objIsoCanonical U φ hpb).hom]
  · refine canonical_hom_ext a U ?_ ?_
    · rw [Category.assoc, Category.assoc, canonicalFunctor_gluingPullbackIso_hom_snd_projection,
        srcPullbackMap_fst_assoc, objIsoCanonical_hom_left_comp_canonicalProjection,
        Category.assoc, Category.assoc, tgtPullbackMap_snd_assoc,
        objIsoCanonical_hom_left_comp_canonicalProjection, hinv]
    · rw [Category.assoc, Category.assoc, gluingPullbackIso_hom_snd, srcPullbackMap_snd,
        Category.assoc, Category.assoc, tgtPullbackMap_snd_assoc,
        Over.w (objIsoCanonical U φ hpb).hom, gluingPullbackIso_hom_snd]

include hinv in
/-- **The isomorphism with a canonical descent datum** which the effectivity criterion
`AlgebraicGeometry.DescentData.isEffective_of_isPullback` produces: a descent datum exhibited as
`X ×_S U` by an invariant projection onto `U` is the canonical datum of `U`. -/
def isoCanonical : (canonicalFunctor a).obj U ≅ D :=
  (isoOfGluingPullback (objIsoCanonical U φ hpb)
    (srcPullbackMap_comp_objIsoCanonical U φ hpb hinv)).symm

/-- The component of the inverse of that isomorphism is the identification of the schemes. -/
lemma isoCanonical_inv_hom (i : Unit) :
    (isoCanonical U φ hpb hinv).inv.hom i = (objIsoCanonical U φ hpb).hom := rfl

/-- The component of that isomorphism carries the given projection to the projection of the
canonical datum. -/
@[reassoc]
lemma isoCanonical_hom_hom_left_comp :
    ((isoCanonical U φ hpb hinv).hom.hom ()).left ≫ φ = canonicalProjection a U := by
  have h : ((isoCanonical U φ hpb hinv).hom.hom ()).left ≫
      (objIsoCanonical U φ hpb).hom.left = 𝟙 _ := by
    rw [← Over.comp_left, ← isoCanonical_inv_hom U φ hpb hinv (), ← DescentData.comp_hom,
      (isoCanonical U φ hpb hinv).hom_inv_id, DescentData.id_hom, Over.id_left]
  simpa only [Category.assoc, objIsoCanonical_hom_left_comp_canonicalProjection,
    Category.id_comp] using h =≫ canonicalProjection a U

end Criterion

end DescentData

/-! ### Comparing two descended schemes through étale descent -/

namespace DescentDatum.Descended

variable {S X : Scheme.{u}} {f : X ⟶ S} {D : DescentDatum f}

/-- **The isomorphism of a descent datum with the canonical datum of a scheme descending it.** -/
def canonicalIso (Q : D.Descended) : (DescentData.canonicalFunctor f).obj Q.base ≅ D :=
  DescentData.isoCanonical Q.base Q.proj Q.isPullback.flip Q.proj_invariant

/-- The component of that isomorphism carries the projection of the descended scheme to the
projection of the canonical datum. -/
@[reassoc]
lemma canonicalIso_hom_hom_left_comp_proj (Q : D.Descended) :
    (Q.canonicalIso.hom.hom ()).left ≫ Q.proj = DescentData.canonicalProjection f Q.base :=
  DescentData.isoCanonical_hom_hom_left_comp _ _ _ _

/-- The component of the inverse carries the projection of the canonical datum to the projection
of the descended scheme. -/
@[reassoc]
lemma canonicalIso_inv_hom_left_comp_canonicalProjection (Q : D.Descended) :
    (Q.canonicalIso.inv.hom ()).left ≫ DescentData.canonicalProjection f Q.base = Q.proj :=
  DescentData.objIsoCanonical_hom_left_comp_canonicalProjection _ _ _

/-- The two components of that isomorphism are mutually inverse. -/
@[reassoc (attr := simp)]
lemma canonicalIso_inv_hom_left_comp_hom_hom_left (Q : D.Descended) :
    (Q.canonicalIso.inv.hom ()).left ≫ (Q.canonicalIso.hom.hom ()).left = 𝟙 _ := by
  rw [← Over.comp_left, ← DescentData.comp_hom, Q.canonicalIso.inv_hom_id,
    DescentData.id_hom, Over.id_left]

/-- **A morphism over `S` compatible with the two projections has the comparison of the two
canonical data as its canonical datum.** -/
lemma canonicalFunctor_map_eq_of_proj_comp_eq (Q Q' : D.Descended) {e : Q.base ⟶ Q'.base}
    (he : Q.proj ≫ e.left = Q'.proj) :
    (DescentData.canonicalFunctor f).map e = (Q.canonicalIso ≪≫ Q'.canonicalIso.symm).hom := by
  refine DescentData.hom_ext fun i ↦ ?_
  cases i
  refine Over.OverMorphism.ext ?_
  refine DescentData.canonical_hom_ext f Q'.base ?_ ?_
  · rw [DescentData.canonicalProjection_naturality, Iso.trans_hom, DescentData.comp_hom,
      Over.comp_left, Category.assoc, Iso.symm_hom,
      Q'.canonicalIso_inv_hom_left_comp_canonicalProjection,
      ← Q.canonicalIso_hom_hom_left_comp_proj, Category.assoc, he]
  · exact (Over.w _).trans (Over.w _).symm

end DescentDatum.Descended

/-! ### Full faithfulness of the étale descent functor -/

variable {S X : Scheme.{u}}

/-- Faithfulness of the étale descent functor makes the canonical functor faithful on morphisms
between schemes étale over `S`. -/
private theorem canonicalFunctor_map_injective_of_faithful (g : X ⟶ S)
    (hfaith : (etaleDescentFunctor g).Faithful) {A B : Over S} [Etale A.hom] [Etale B.hom]
    {h h' : A ⟶ B}
    (heq : (DescentData.canonicalFunctor g).map h = (DescentData.canonicalFunctor g).map h') :
    h = h' := by
  let A' : S.Etale := Scheme.Etale.mk A.hom
  let B' : S.Etale := Scheme.Etale.mk B.hom
  have hι : ∀ k : A' ⟶ B', (IsEtaleDescentData g).ι.map ((etaleDescentFunctor g).map k) =
      (DescentData.canonicalFunctor g).map ((Scheme.Etale.forget S).map k) := fun _ ↦ rfl
  have hk : (Scheme.Etale.forget S).map
      ((Scheme.Etale.forgetFullyFaithful S).preimage (X := A') (Y := B') h) = h :=
    (Scheme.Etale.forgetFullyFaithful S).map_preimage _
  have hk' : (Scheme.Etale.forget S).map
      ((Scheme.Etale.forgetFullyFaithful S).preimage (X := A') (Y := B') h') = h' :=
    (Scheme.Etale.forgetFullyFaithful S).map_preimage _
  have hstep : (etaleDescentFunctor g).map
      ((Scheme.Etale.forgetFullyFaithful S).preimage (X := A') (Y := B') h) =
      (etaleDescentFunctor g).map
        ((Scheme.Etale.forgetFullyFaithful S).preimage (X := A') (Y := B') h') :=
    (IsEtaleDescentData g).ι.map_injective (by rwa [hι, hι, hk, hk'])
  rw [← hk, ← hk', (etaleDescentFunctor g).map_injective hstep]

/-- **A morphism between the canonical data of two schemes étale over `S` is the canonical datum
of exactly one morphism of schemes over `S`,** when the étale descent functor of `g : X ⟶ S` is
fully faithful. -/
theorem existsUnique_canonicalFunctor_map_eq_of_etale (g : X ⟶ S)
    (hff : (etaleDescentFunctor g).FullyFaithful) {A B : Over S} [Etale A.hom] [Etale B.hom]
    (ψ : (DescentData.canonicalFunctor g).obj A ⟶ (DescentData.canonicalFunctor g).obj B) :
    ∃! h : A ⟶ B, (DescentData.canonicalFunctor g).map h = ψ := by
  have hfaith := hff.faithful
  let φ : (etaleDescentFunctor g).obj (Scheme.Etale.mk A.hom) ⟶
      (etaleDescentFunctor g).obj (Scheme.Etale.mk B.hom) := ObjectProperty.homMk ψ
  refine ⟨(Scheme.Etale.forget S).map (hff.preimage φ), ?_, fun h' hh' ↦ ?_⟩
  · exact congrArg (IsEtaleDescentData g).ι.map (hff.map_preimage φ)
  · exact canonicalFunctor_map_injective_of_faithful g hfaith
      (hh'.trans (congrArg (IsEtaleDescentData g).ι.map (hff.map_preimage φ)).symm)

/-- **Two morphisms of schemes étale over `S` with the same canonical datum are equal,** when the
étale descent functor of `g : X ⟶ S` is faithful. -/
theorem canonicalFunctor_map_injective_of_etale (g : X ⟶ S)
    (hfaith : (etaleDescentFunctor g).Faithful) {A B : Over S} [Etale A.hom] [Etale B.hom]
    {h h' : A ⟶ B}
    (heq : (DescentData.canonicalFunctor g).map h = (DescentData.canonicalFunctor g).map h') :
    h = h' :=
  canonicalFunctor_map_injective_of_faithful g hfaith heq

namespace DescentDatum.Descended

variable {f : X ⟶ S} {D : DescentDatum f}

/-- **Two schemes descending one descent datum, étale over `S`, are uniquely isomorphic over
`S`.** If the étale descent functor of `f` is fully faithful, there is exactly one morphism over
`S` between the two descended schemes compatible with the two projections. -/
theorem existsUnique_hom_comp_proj_eq (hff : (etaleDescentFunctor f).FullyFaithful)
    (Q Q' : D.Descended) [Etale Q.base.hom] [Etale Q'.base.hom] :
    ∃! e : Q.base ⟶ Q'.base, Q.proj ≫ e.left = Q'.proj := by
  obtain ⟨e, he, huniq⟩ := existsUnique_canonicalFunctor_map_eq_of_etale f hff
    (Q.canonicalIso ≪≫ Q'.canonicalIso.symm).hom
  refine ⟨e, ?_, fun e' he' ↦ huniq e' (Q.canonicalFunctor_map_eq_of_proj_comp_eq Q' he')⟩
  change Q.proj ≫ e.left = Q'.proj
  have h := congrArg (fun k ↦ (k.hom ()).left ≫ DescentData.canonicalProjection f Q'.base) he
  simp only [Iso.trans_hom, DescentData.comp_hom, Over.comp_left, Iso.symm_hom,
    Category.assoc, Q'.canonicalIso_inv_hom_left_comp_canonicalProjection,
    DescentData.canonicalProjection_naturality] at h
  rw [← Q.canonicalIso_hom_hom_left_comp_proj, Category.assoc] at h
  rw [← Category.id_comp (Q.proj ≫ e.left), ← Q.canonicalIso_inv_hom_left_comp_hom_hom_left,
    Category.assoc, h, ← Category.assoc,
    Q.canonicalIso_inv_hom_left_comp_hom_hom_left, Category.id_comp]

/-- **A morphism over `S` compatible with the two projections is unique**, when the étale descent
functor of `f` is faithful. This is the uniqueness half of
`AlgebraicGeometry.DescentDatum.Descended.existsUnique_hom_comp_proj_eq`, and faithfulness is
all it needs. -/
theorem eq_of_proj_comp_eq (hfaith : (etaleDescentFunctor f).Faithful)
    (Q Q' : D.Descended) [Etale Q.base.hom] [Etale Q'.base.hom] {e e' : Q.base ⟶ Q'.base}
    (he : Q.proj ≫ e.left = Q'.proj) (he' : Q.proj ≫ e'.left = Q'.proj) : e = e' :=
  canonicalFunctor_map_injective_of_etale f hfaith
    ((Q.canonicalFunctor_map_eq_of_proj_comp_eq Q' he).trans
      (Q.canonicalFunctor_map_eq_of_proj_comp_eq Q' he').symm)

end DescentDatum.Descended

end AlgebraicGeometry

end

end
