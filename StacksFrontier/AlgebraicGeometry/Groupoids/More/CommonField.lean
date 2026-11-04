module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Groupoids.FieldExtensionEvaluation
public import StacksCore.Tactic.StacksAttribute

/-!
# A common field for the source fibres of two arrows

Two arrows `r`, `r'` of a groupoid scheme which have the same target are the first projection
and the composite of a single point of the scheme of composable pairs.  The second projection
of that point is an arrow from the source of `r'` to the source of `r`, and its residue field
receives both residue fields through the source and target maps.  Base changing the fibres of
the source map over the sources of `r` and `r'` to that common field makes them isomorphic, and
the isomorphism can be chosen to carry a point above `r` to a point above `r'`.

## Main results

* `AlgebraicGeometry.exists_composable_point_with_comp` supplies the point of the scheme of
  composable pairs and records the source and target of its second projection.
* `AlgebraicGeometry.exists_common_field_fiber_iso` gives the common field and the isomorphism
  between the two base-changed source fibres.
* `AlgebraicGeometry.exists_common_field_fiber_iso_mapping_point` chooses the common field,
  fibre isomorphism and compatible point together.

## Implementation notes

Points of objects and morphisms of the over-category are expressed through their underlying
schemes and scheme morphisms.  The base change of a fibre to a field `K` is represented as a
pullback over the spectrum of the residue field, and the resulting schemes are regarded as
objects over `Spec K`, so the isomorphisms asserted here also respect their structure
morphisms to `Spec K`.  Saying that a point lies over an arrow means that its image under the
first pullback projection is that arrow.

## References

* [Stacks Project, Tag 02YF](https://stacks.math.columbia.edu/tag/02YF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Two arrows with the same target are respectively the first projection and the composite
of a point of the scheme of composable arrows.  The second projection goes from the source of
the second arrow to the source of the first arrow. -/
public lemma exists_composable_point_with_comp {S : Scheme.{u}}
    (G : GroupoidScheme S) (r r' : G.arrows.left)
    (h : G.target.left r = G.target.left r') :
    ∃ ξ : (pullback G.source G.target).left,
      (pullback.fst G.source G.target).left ξ = r ∧
        G.comp.left ξ = r' ∧
        G.target.left ((pullback.snd G.source G.target).left ξ) = G.source.left r ∧
        G.source.left ((pullback.snd G.source G.target).left ξ) = G.source.left r' := by
  have hp := (GroupoidScheme.target_comp_isPullback G).map (Over.forget S)
  obtain ⟨ξ, hfst, hcomp⟩ := Scheme.exists_preimage_of_isPullback hp r r' h
  change (pullback.fst G.source G.target).left ξ = r at hfst
  change G.comp.left ξ = r' at hcomp
  refine ⟨ξ, hfst, hcomp, ?_, ?_⟩
  · have hpull := congrArg (fun f ↦ f.left ξ)
        (pullback.condition (f := G.source) (g := G.target))
    change G.source.left ((pullback.fst G.source G.target).left ξ) =
      G.target.left ((pullback.snd G.source G.target).left ξ) at hpull
    rw [hfst] at hpull
    exact hpull.symm
  · have hs := congrArg (fun f ↦ f.left ξ) G.source_comp
    change G.source.left (G.comp.left ξ) =
      G.source.left ((pullback.snd G.source G.target).left ξ) at hs
    rw [hcomp] at hs
    exact hs.symm

/-- The fibre of the second leg of a cartesian square over a point of its base is the base
change of the fibre of the first leg along the induced map of residue fields, as objects over
the spectrum of the residue field of the point. -/
@[reducible] private noncomputable def fiberBaseChangeIso
    {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y) :
    Over.mk (snd.fiberToSpecResidueField y) ≅
      Over.mk (pullback.snd (f.fiberToSpecResidueField (g y))
        (Spec.map (g.residueFieldMap y))) := by
  let h' := isPullback_fiberToSpecResidueField_of_isPullback h y
  let hc := (IsPullback.of_hasPullback
    (f.fiberToSpecResidueField (g y)) (Spec.map (g.residueFieldMap y))).flip
  exact Over.isoMk (h'.flip.isoIsPullback _ _ hc)
    (h'.flip.isoIsPullback_hom_fst _ _ hc)

/-- Composing `fiberBaseChangeIso` with the first projection of the base-changed fibre is the
comparison morphism of fibres induced by the cartesian square. -/
private lemma fiberBaseChangeIso_hom_left_comp_fst
    {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y) :
    (fiberBaseChangeIso h y).hom.left ≫
        pullback.fst (f.fiberToSpecResidueField (g y)) (Spec.map (g.residueFieldMap y)) =
      pullback.map snd (Y.fromSpecResidueField y) f (Z.fromSpecResidueField (g y)) fst
        (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp) :=
  (isPullback_fiberToSpecResidueField_of_isPullback h y).flip.isoIsPullback_hom_snd _ _
    ((IsPullback.of_hasPullback (f.fiberToSpecResidueField (g y))
      (Spec.map (g.residueFieldMap y))).flip)

/-- The inclusion of the base-changed fibre of the first leg of a cartesian square into the
source of that leg factors `fiberBaseChangeIso` through the inclusion of the fibre of the
second leg. -/
private lemma fiberBaseChangeIso_fiberι
    {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y) :
    (fiberBaseChangeIso h y).hom.left ≫
        pullback.fst (f.fiberToSpecResidueField (g y))
          (Spec.map (g.residueFieldMap y)) ≫ f.fiberι (g y) =
      snd.fiberι y ≫ fst := by
  rw [← Category.assoc, fiberBaseChangeIso_hom_left_comp_fst h y]
  simp only [Scheme.Hom.fiberι, pullback.map]
  exact pullback.lift_fst _ _ _

/-- The square of the pullback of `source` and `target`, on the level of underlying schemes. -/
private lemma isPullback_left_fst_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback (pullback.fst G.source G.target).left
      (pullback.snd G.source G.target).left G.source.left G.target.left := by
  simpa using (IsPullback.of_hasPullback G.source G.target).map (Over.forget S)

/-- The composition square of a groupoid scheme, on the level of underlying schemes. -/
private lemma isPullback_left_comp_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback G.comp.left (pullback.snd G.source G.target).left
      G.source.left G.source.left := by
  simpa using (GroupoidScheme.comp_source_isPullback G).map (Over.forget S)

/-- If two arrows in a groupoid scheme have the same target, then the fibres of the source
map over their sources become isomorphic after extending both residue fields to a common
field. -/
@[stacks 02YF "common_field"]
public theorem exists_common_field_fiber_iso {S : Scheme.{u}}
    (G : GroupoidScheme S) (r r' : G.arrows.left)
    (h : G.target.left r = G.target.left r') :
    ∃ (K : Type u) (_ : Field K)
      (_ : Algebra (G.objects.left.residueField (G.source.left r)) K)
      (_ : Algebra (G.objects.left.residueField (G.source.left r')) K),
      Nonempty
        (Over.mk (pullback.snd
          (G.source.left.fiberToSpecResidueField (G.source.left r))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (G.objects.left.residueField (G.source.left r)) K)))) ≅
        Over.mk (pullback.snd
          (G.source.left.fiberToSpecResidueField (G.source.left r'))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (G.objects.left.residueField (G.source.left r')) K))))) := by
  obtain ⟨ξ, _, _, htarget, hsource⟩ := exists_composable_point_with_comp G r r' h
  let q := (pullback.snd G.source G.target).left ξ
  rw [← htarget, ← hsource]
  let _ := (G.target.left.residueFieldMap q).hom.toAlgebra
  let _ := (G.source.left.residueFieldMap q).hom.toAlgebra
  exact ⟨G.arrows.left.residueField q, inferInstance, inferInstance, inferInstance,
    ⟨(fiberBaseChangeIso (isPullback_left_fst_snd G) q).symm ≪≫
    fiberBaseChangeIso (isPullback_left_comp_snd G) q⟩⟩

/-- The common field and source-fibre isomorphism for two arrows with the same target can be
chosen so that the isomorphism carries a point above the first arrow to a point above the
second. -/
@[stacks 02YF "point_compatible"]
public theorem exists_common_field_fiber_iso_mapping_point {S : Scheme.{u}}
    (G : GroupoidScheme S) (r r' : G.arrows.left)
    (h : G.target.left r = G.target.left r') :
    ∃ (K : Type u) (_ : Field K)
      (_ : Algebra (G.objects.left.residueField (G.source.left r)) K)
      (_ : Algebra (G.objects.left.residueField (G.source.left r')) K),
      let g : Spec (.of K) ⟶ Spec (.of (G.objects.left.residueField (G.source.left r))) :=
        Spec.map (CommRingCat.ofHom
          (algebraMap (G.objects.left.residueField (G.source.left r)) K))
      let g' : Spec (.of K) ⟶ Spec (.of (G.objects.left.residueField (G.source.left r'))) :=
        Spec.map (CommRingCat.ofHom
          (algebraMap (G.objects.left.residueField (G.source.left r')) K))
      let P : Scheme.{u} :=
        pullback (G.source.left.fiberToSpecResidueField (G.source.left r)) g
      let _P' : Scheme.{u} :=
        pullback (G.source.left.fiberToSpecResidueField (G.source.left r')) g'
      let POver : Over (Spec (.of K)) := Over.mk
        (pullback.snd (G.source.left.fiberToSpecResidueField (G.source.left r)) g)
      let POver' : Over (Spec (.of K)) := Over.mk
        (pullback.snd (G.source.left.fiberToSpecResidueField (G.source.left r')) g')
      ∃ (x : P) (e : POver ≅ POver'),
        ((pullback.fst
            (G.source.left.fiberToSpecResidueField (G.source.left r)) g) ≫
              G.source.left.fiberι (G.source.left r)).base x = r ∧
          ((pullback.fst
            (G.source.left.fiberToSpecResidueField (G.source.left r')) g') ≫
              G.source.left.fiberι (G.source.left r')).base (e.hom.left.base x) = r' := by
  obtain ⟨ξ, hfst, hcomp, htarget, hsource⟩ := exists_composable_point_with_comp G r r' h
  let q := (pullback.snd G.source G.target).left ξ
  change G.target.left q = G.source.left r at htarget
  change G.source.left q = G.source.left r' at hsource
  rw [← htarget, ← hsource]
  let K := G.arrows.left.residueField q
  let _ : Algebra (G.objects.left.residueField (G.target.left q)) K :=
    (G.target.left.residueFieldMap q).hom.toAlgebra
  let _ : Algebra (G.objects.left.residueField (G.source.left q)) K :=
    (G.source.left.residueFieldMap q).hom.toAlgebra
  refine ⟨K, inferInstance, inferInstance, inferInstance, ?_⟩
  let e₁ := fiberBaseChangeIso (isPullback_left_fst_snd G) q
  let e₂ := fiberBaseChangeIso (isPullback_left_comp_snd G) q
  let y := (pullback.snd G.source G.target).left.asFiber ξ
  have hmap₂ := fiberBaseChangeIso_fiberι (isPullback_left_comp_snd G) q
  refine ⟨e₁.hom.left.base y, e₁.symm ≪≫ e₂, ?_, ?_⟩
  · show ((e₁.hom.left ≫
        pullback.fst (G.source.left.fiberToSpecResidueField (G.target.left q))
          (Spec.map (G.target.left.residueFieldMap q)) ≫
        G.source.left.fiberι (G.target.left q)).base) y = r
    rw [fiberBaseChangeIso_fiberι (isPullback_left_fst_snd G) q]
    show (pullback.fst G.source G.target).left
      ((pullback.snd G.source G.target).left.fiberι q y) = r
    rw [Scheme.Hom.fiberι_asFiber]
    exact hfst
  · show ((e₁.inv.left ≫ e₂.hom.left ≫
        pullback.fst (G.source.left.fiberToSpecResidueField (G.source.left q))
          (Spec.map (G.source.left.residueFieldMap q)) ≫
        G.source.left.fiberι (G.source.left q)).base) (e₁.hom.left.base y) = r'
    simp only at hmap₂ ⊢
    rw [hmap₂]
    have hcanc : e₁.inv.left.base (e₁.hom.left.base y) = y := by
      show (e₁.hom.left ≫ e₁.inv.left).base y = y
      simp
    show G.comp.left ((pullback.snd G.source G.target).left.fiberι q
      (e₁.inv.left.base (e₁.hom.left.base y))) = r'
    rw [hcanc, Scheme.Hom.fiberι_asFiber]
    exact hcomp

end AlgebraicGeometry
