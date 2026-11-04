module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.SetTheory.Cardinal.ENat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSitePoint
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Point.ConservativeFamily

/-!
# Exactness on the small étale site of an algebraic space is detected on geometric stalks

A map of sheaves of sets on the small étale site of an algebraic space is injective exactly
when every one of its maps on geometric stalks is injective, and locally surjective exactly
when every one of them is surjective.  A short complex of sheaves of abelian groups is exact
exactly when its sequence of geometric stalks is exact at every geometric point.  This is
Stacks 04K5.

The geometric stalk functors themselves are exact — they preserve finite limits and finite
colimits, for presheaves and for sheaves, of sets and of abelian groups — and the set-valued
ones commute with arbitrary colimits; sheafification does not change a geometric stalk.  This
is Stacks 04K1, and it is where the fibre functor at the point of the site of Stacks 04K0 does
the work: it is a restriction followed by a filtered colimit, so it is exact by construction,
and `pointStalkIso` transports that to the geometric stalk.

## Main results

* `AlgebraicGeometry.Space.injective_iff_stalkSetMap_injective`,
* `AlgebraicGeometry.Space.surjective_iff_stalkSetMap_surjective`,
* `AlgebraicGeometry.Space.exact_iff_stalk_exact`.
* `AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePoint`,
  `AlgebraicGeometry.Space.isConservativeFamily_etaleSitePoint` and
  `AlgebraicGeometry.Space.hasConservativeFamily_smallEtale`: the geometric points are a
  conservative family of points of the small étale site, so that site has enough points.
  This is the form in which Stacks 04KH and 073C cite the theorem; it is not one of the
  theorem's own clauses and is therefore untagged.
* `AlgebraicGeometry.Space.presheafAbelianStalk_preservesFiniteLimits` and
  `…_preservesFiniteColimits`: the geometric stalk of a presheaf of abelian groups is exact,
  and `AlgebraicGeometry.Space.sheafAbelianStalk_preservesFiniteLimits` and
  `…_preservesFiniteColimits` the same for sheaves.
* `AlgebraicGeometry.Space.stalkSetMap_toSheafify_isIso`: sheafification does not change a
  geometric stalk.
* `AlgebraicGeometry.Space.residueField_mk_le_size`: a residue field of a scheme is no larger
  than the scheme, and `AlgebraicGeometry.Space.exists_geo_lift_at_chart_point`: every point
  of an étale scheme chart of an algebraic space is hit by a lift of some geometric point of
  the space.
* `AlgebraicGeometry.Space.presheafSetStalk_preservesFiniteLimits`,
  `…_preservesFiniteColimits`, `…_preservesColimits` and their three `sheafSetStalk`
  counterparts: the geometric stalk of a presheaf or sheaf of sets is exact and commutes with
  arbitrary colimits.  These are the four parts of Stacks 04K1.

## Implementation notes

Both set-valued statements run on the same two ingredients.  The first is that the geometric
stalks see enough of the site: a sieve over an étale chart which admits, above *every point*
of the chart, a member through which that point lifts is a covering sieve
(`smallEtale_sieve_of_pointwise_covering`).  This is where the size bookkeeping of the big
fppf site enters — the family of all members of the sieve is indexed by a type one universe
up, so it is replaced by a combinatorially equivalent chosen covering family through
`AlgebraicGeometry.Space.exists_chosen_etaleCovering`, and the members are étale over the
chart by `AlgebraicGeometry.Space.etale_of_comp_etale_chart`.  The second is that every point
of an étale chart is the image of a point of a geometric point's lift
(`exists_geo_lift_at_chart_point`): the algebraic closure of the residue field at that point
is small enough to lie in the site, because the residue field is a subquotient-sized
invariant of the chart and the chart is in the site, so it defines a geometric point of the
algebraic space lifting to the chart.

Injectivity is then: the equalizer sieve of two sections with the same germ everywhere is
covering, so the two sections agree because the sheaf is separated.  Local surjectivity is
the image sieve of a section being covering, which is the definition, and in the forward
direction a germ is lifted by the point of the site of Stacks 04K0.

Exactness is not reduced to the set-valued statements.  Instead the family of *sheaf* fibre
functors at the geometric points is shown to be jointly faithful — again by the two
ingredients above, applied to the underlying presheaves of sets — so a short complex of
sheaves of abelian groups is exact as soon as each of its images is, because exactness is the
vanishing of homology and the family detects a vanishing object.  The passage from the fibre
functor of the point of the site to the geometric stalk functor of Stacks 04JY is
`pointStalkIso`, stated for an arbitrary target with colimits of the size of the site and
natural in the presheaf.

Sheaves of abelian groups on the small étale site form an abelian category as soon as the
presheaves of abelian groups there are sheafifiable, so the exactness clause needs that for
sections in `max (u + 1) w`, the universe its stalks live in.  It is not assumed but proved,
in the file-local instance `hasSheafify_smallEtale_addCommGrpCat`:
`AlgebraicGeometry.Space.SmallEtale.instHasSheafify` fixes the sections at `u` and does not
reach this universe, but the site has its objects in `Type (u + 1)` and its morphisms in
`Type u`, so it is essentially small at `max (u + 1) w` too, and there the coefficients lie in
the universe of the small model and Mathlib's sheafification applies.

The geometric stalk of a sheaf of sets is a quotient colimit
(`AlgebraicGeometry.Space.stalkSet`) and not a categorical one, so that no smallness
hypothesis on the neighbourhood category is needed at the universe of the sections; the
filtered-colimit calculus used for it is `CategoryTheory.Functor.ιColimitType_eq_iff_of_isFiltered`
and its relatives, whose filteredness hypothesis is Stacks 04K0 through
`AlgebraicGeometry.Space.isCofiltered_smallEtaleNeighborhood`.

Conservativity of the family of geometric points is *not* deduced from the three statements
above.  It is `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mk'` — a map of
sheaves of sets is an isomorphism as soon as, for every point of the family, every sieve
through which the point's lifts all factor is covering — fed the first ingredient directly.
Going through injectivity and surjectivity instead would force a comparison between the
quotient stalk `AlgebraicGeometry.Space.stalkSet`, which lives one universe above the site,
and `CategoryTheory.GrothendieckTopology.Point.presheafFiber`, which lives in the universe of
the sections; `mk'` needs no such comparison.

## References

* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04K1](https://stacks.math.columbia.edu/tag/04K1)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- The residue field at a point of a scheme is no larger than the scheme, because the
spectrum of that residue field maps to the scheme by a quasi-compact monomorphism. -/
theorem residueField_mk_le_size (T : Scheme.{u}) (z : T) :
    Cardinal.mk (T.residueField z) ≤ T.size := by
  have hs : (Spec (T.residueField z)).size ≤ T.size :=
    Scheme.size_le_of_mono_quasiCompact (T.fromSpecResidueField z)
  rw [Scheme.size_Spec] at hs
  exact (le_max_right _ _).trans hs

/-- Every point of an étale scheme chart of an algebraic space is hit by a lift of some
geometric point of the space: take the algebraic closure of the residue field there, which
is still small enough to be an object of the big fppf site. -/
theorem exists_geo_lift_at_chart_point (U : SmallEtale B S hS X)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj U)) :
    ∃ (x : GeometricPoint B S hS X), ∃ p : GeometricFiber B S hS X x U,
      ∃ z' : (BigFppfOver.toScheme B S hS).obj x.val.siteObject,
        ((BigFppfOver.toScheme B S hS).map p.1) z' = z := by
  let T := (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj U)
  let K := T.residueField z
  have hT : T.size < B.cutoff := (SmallEtale.toOver B S hS X).obj U |>.left.property
  have hKsize : Cardinal.mk K ≤ T.size := residueField_mk_le_size T z
  let _ : Field K := inferInstance
  let L := AlgebraicClosure K
  have hLcard : Cardinal.mk L ≤ T.size := by
    calc
      Cardinal.mk L ≤ max (Cardinal.mk K) Cardinal.aleph0 :=
        Algebra.IsAlgebraic.cardinalMk_le_max _ _
      _ = max Cardinal.aleph0 (Cardinal.mk K) := max_comm _ _
      _ ≤ T.size := max_le (Scheme.aleph0_le_size T) hKsize
  have hLsize : (Spec (.of L)).size ≤ T.size := by
    rw [Scheme.size_Spec]
    exact max_le (Scheme.aleph0_le_size T) hLcard
  have hL : B.Contains (Spec (.of L)) := hLsize.trans_lt hT
  let _ : Field L := inferInstance
  let _ : IsAlgClosed L := inferInstance
  let a : K →+* L := algebraMap K L
  let g : Spec (.of L) ⟶ Spec K := Scheme.Spec.map (CommRingCat.ofHom a).op
  let Tsite := (SmallEtale.toOver B S hS X).obj U
  let H : Spec (.of L) ⟶ T := g ≫ T.fromSpecResidueField z
  let b : Spec (.of L) ⟶ S := by
    change Spec (.of L) ⟶ (B.inclusion.obj (B.obj hS))
    exact H ≫ B.inclusion.map Tsite.hom
  let m : (B.obj hL) ⟶ Tsite.left := B.inclusion.preimage
    (show B.inclusion.obj (B.obj hL) ⟶ B.inclusion.obj Tsite.left from H)
  let qval : FieldValuedPoint B S hS (yoneda.obj Tsite) := {
    carrier := L
    contained := hL
    toBase := b
    value := Over.homMk m (by
      apply B.inclusion.map_injective
      simp only [m, Functor.map_comp, Functor.map_preimage]
      rfl) }
  let qF := FieldValuedPoint.map B S hS (yoneda.obj Tsite) U.obj.hom qval
  let x : GeometricPoint B S hS X := ⟨qF, by change IsAlgClosed L; infer_instance⟩
  let p : GeometricFiber B S hS X x U := ⟨qval.value, rfl⟩
  let z' : (BigFppfOver.toScheme B S hS).obj x.val.siteObject := by
    change Spec (.of L)
    exact default
  refine ⟨x, p, z', ?_⟩
  have hp : (BigFppfOver.toScheme B S hS).map p.1 = H := by
    dsimp [p, qval, m]
    change B.inclusion.map (B.inclusion.preimage
      (show B.inclusion.obj (B.obj hL) ⟶ B.inclusion.obj Tsite.left from H)) = H
    rw [Functor.map_preimage]
  rw [hp]
  have hz' : z' = (default : Spec (.of L)) := rfl
  rw [hz']
  change T.fromSpecResidueField z
    ((Scheme.Spec.map (CommRingCat.ofHom a).op) (default : Spec (.of L))) = z
  have hg : (Scheme.Spec.map (CommRingCat.ofHom a).op)
      (default : Spec (.of L)) = (default : Spec (T.residueField z)) := by
    let _ : Unique (Spec (T.residueField z)) := inferInstance
    exact (inferInstance : Unique (Spec (T.residueField z))).uniq _
  rw [hg]
  exact T.fromSpecResidueField_apply z (default : Spec (T.residueField z))

/-- The sections of a presheaf over the small étale neighbourhoods of a geometric point, pulled
back along the equivalence with the elements of the geometric fibre, are the sections over the
charts of those elements. -/
private noncomputable def neighborhoodSectionsIso {A : Type w} [Category A]
    (P : (SmallEtale B S hS X)ᵒᵖ ⥤ A) (x : GeometricPoint B S hS X) :
    (neighborhoodFiberElementsEquiv B S hS X x).symm.op.functor ⋙
        SmallEtaleNeighborhood.sections (x := x) P ≅
      (CategoryOfElements.π (geometricFiber B S hS X x)).op ⋙ P :=
  NatIso.ofComponents (fun j => Iso.refl _) (by
    intro j j' g
    change P.map
      (((neighborhoodFiberElementsEquiv B S hS X x).symm.op.functor.map g).unop.hom).op ≫ 𝟙 _ =
        𝟙 _ ≫ P.map g.unop.val.op
    simp only [Category.comp_id, Category.id_comp]
    congr 1)

include hX

/-- The diagram shape of the geometric stalk — the opposite of the small étale
neighbourhoods — is filtered, by Stacks 04K0. -/
private theorem smallEtaleNeighborhood_isFiltered (x : GeometricPoint B S hS X) :
    IsFiltered (SmallEtaleNeighborhood x)ᵒᵖ :=
  have := isCofiltered_smallEtaleNeighborhood B S hS X hX x
  inferInstance

/-- The stalk at the point of the site of Stacks 04K0 is the geometric stalk of Stacks 04JY,
for coefficients in any category with colimits of the size of the site: both are a colimit of
the same sections, over the elements of the geometric fibre and over the small étale
neighbourhoods respectively. -/
private noncomputable def pointStalkIso {A : Type w} [Category A]
    [HasColimitsOfSize.{u, u} A] (P : (SmallEtale B S hS X)ᵒᵖ ⥤ A)
    (x : GeometricPoint B S hS X)
    [HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ A] :
    (etaleSitePoint B S hS X x hX).presheafFiber.obj P ≅ (stalkFunctor A x).obj P := by
  have : HasColimitsOfShape (geometricFiber B S hS X x).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (etaleSitePoint B S hS X x hX).fiber.Elementsᵒᵖ A)
  let e := (neighborhoodFiberElementsEquiv B S hS X x).symm.op
  change colimit ((CategoryOfElements.π (geometricFiber B S hS X x)).op ⋙ P) ≅
    colimit (SmallEtaleNeighborhood.sections (x := x) P)
  exact HasColimit.isoOfEquivalence e (neighborhoodSectionsIso B S hS X P x)

/-- `pointStalkIso` is natural in the presheaf. -/
private theorem pointStalkIso_naturality {A : Type w} [Category A]
    [HasColimitsOfSize.{u, u} A] (P Q : (SmallEtale B S hS X)ᵒᵖ ⥤ A)
    (x : GeometricPoint B S hS X)
    [HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ A] (f : P ⟶ Q) :
    (pointStalkIso B S hS X hX P x).hom ≫ (stalkFunctor A x).map f =
      (etaleSitePoint B S hS X x hX).presheafFiber.map f ≫
        (pointStalkIso B S hS X hX Q x).hom := by
  have : HasColimitsOfShape (geometricFiber B S hS X x).Elementsᵒᵖ A :=
    inferInstanceAs (HasColimitsOfShape (etaleSitePoint B S hS X x hX).fiber.Elementsᵒᵖ A)
  let e := (neighborhoodFiberElementsEquiv B S hS X x).symm.op
  let dP := (CategoryOfElements.π (geometricFiber B S hS X x)).op ⋙ P
  let dQ := (CategoryOfElements.π (geometricFiber B S hS X x)).op ⋙ Q
  let nP := neighborhoodSectionsIso B S hS X P x
  let nQ := neighborhoodSectionsIso B S hS X Q x
  let π := (CategoryOfElements.π (geometricFiber B S hS X x)).op
  let tP : dP ⟶ dQ := Functor.whiskerLeft π f
  let ν : (SmallEtaleNeighborhood x)ᵒᵖ ⥤ (SmallEtale B S hS X)ᵒᵖ := {
    obj := fun U => Opposite.op U.unop.chart
    map := fun g => g.unop.hom.op
    map_id := by intro U; simp
    map_comp := by intro U V W g h; simp }
  let tN : SmallEtaleNeighborhood.sections (x := x) P ⟶
      SmallEtaleNeighborhood.sections (x := x) Q := Functor.whiskerLeft ν f
  have hsquare : Functor.whiskerLeft e.functor tN ≫ nQ.hom = nP.hom ≫ tP := by
    ext k
    have hchart : (e.functor.obj k).unop.chart = (π.obj k).unop := by
      cases k with
      | op p =>
        cases p with
        | mk U y => rfl
    have hobj : Opposite.op (e.functor.obj k).unop.chart = π.obj k :=
      congrArg Opposite.op hchart
    cases hobj
    change f.app _ ≫ 𝟙 _ = 𝟙 _ ≫ f.app _
    simp
  apply colimit.hom_ext
  rintro ⟨j⟩
  let j' := Opposite.op j
  let k := (e.functor ⋙ e.inverse).obj j'
  change colimit.ι dP j' ≫ (HasColimit.isoOfEquivalence e nP).hom ≫ colim.map tN =
    colimit.ι dP j' ≫ colim.map tP ≫ (HasColimit.isoOfEquivalence e nQ).hom
  have hsq := congrArg (fun α => α.app k) hsquare
  have hs : tN.app (e.functor.obj k) ≫ nQ.hom.app k = nP.hom.app k ≫ tP.app k := by
    simpa only [Functor.whiskerLeft_app, NatTrans.comp_app] using hsq
  have hsq' : nP.inv.app k ≫ tN.app (e.functor.obj k) = tP.app k ≫ nQ.inv.app k := by
    calc
      _ = nP.inv.app k ≫ (tN.app (e.functor.obj k) ≫ nQ.hom.app k) ≫ nQ.inv.app k := by
        rw [Category.assoc, Iso.hom_inv_id_app]; exact congrArg _ (Category.comp_id _).symm
      _ = nP.inv.app k ≫ (nP.hom.app k ≫ tP.app k) ≫ nQ.inv.app k := by rw [hs]
      _ = _ := by simp [Category.assoc]
  have ht := tP.naturality (e.unit.app j')
  have ht' : dP.map (e.unit.app j') ≫ tP.app k =
      tP.app j' ≫ dQ.map (e.unit.app j') := ht
  have hIsoP : colimit.ι dP j' ≫ (HasColimit.isoOfEquivalence e nP).hom =
      dP.map (e.unit.app j') ≫ nP.inv.app k ≫
        colimit.ι (SmallEtaleNeighborhood.sections (x := x) P) (e.functor.obj k) :=
    HasColimit.ι_isoOfEquivalence_hom e nP j'
  have hMapP := colimit.ι_map tN (e.functor.obj k)
  have hIsoQ : colimit.ι dQ j' ≫ (HasColimit.isoOfEquivalence e nQ).hom =
      dQ.map (e.unit.app j') ≫ nQ.inv.app k ≫
        colimit.ι (SmallEtaleNeighborhood.sections (x := x) Q) (e.functor.obj k) :=
    HasColimit.ι_isoOfEquivalence_hom e nQ j'
  have hMapQ := colimit.ι_map tP j'
  calc
    _ = dP.map (e.unit.app j') ≫ nP.inv.app k ≫ tN.app (e.functor.obj k) ≫
        colimit.ι (SmallEtaleNeighborhood.sections (x := x) Q) (e.functor.obj k) := by
      calc
        _ = (colimit.ι dP j' ≫ (HasColimit.isoOfEquivalence e nP).hom) ≫ colim.map tN := by
          simp only [Category.assoc]
        _ = (dP.map (e.unit.app j') ≫ nP.inv.app k ≫
            colimit.ι (SmallEtaleNeighborhood.sections (x := x) P) (e.functor.obj k)) ≫
            colim.map tN := by rw [hIsoP]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun g => dP.map (e.unit.app j') ≫ nP.inv.app k ≫ g) hMapP
    _ = dP.map (e.unit.app j') ≫ (nP.inv.app k ≫ tN.app (e.functor.obj k)) ≫
        colimit.ι (SmallEtaleNeighborhood.sections (x := x) Q) (e.functor.obj k) := by
      simp [Category.assoc]
    _ = dP.map (e.unit.app j') ≫ (tP.app k ≫ nQ.inv.app k) ≫
        colimit.ι (SmallEtaleNeighborhood.sections (x := x) Q) (e.functor.obj k) := by
      rw [hsq']
    _ = (dP.map (e.unit.app j') ≫ tP.app k) ≫ nQ.inv.app k ≫
        colimit.ι (SmallEtaleNeighborhood.sections (x := x) Q) (e.functor.obj k) := by
      simp [Category.assoc]
    _ = (tP.app j' ≫ dQ.map (e.unit.app j')) ≫ nQ.inv.app k ≫
        colimit.ι (SmallEtaleNeighborhood.sections (x := x) Q) (e.functor.obj k) := by
      rw [ht']
    _ = tP.app j' ≫ colimit.ι dQ j' ≫ (HasColimit.isoOfEquivalence e nQ).hom := by
      simpa only [Category.assoc] using (congrArg (fun g => tP.app j' ≫ g) hIsoQ).symm
    _ = _ := by
      simpa only [Category.assoc] using
        (congrArg (fun g => g ≫ (HasColimit.isoOfEquivalence e nQ).hom) hMapQ).symm

/-- A map of presheaves of sets which is injective on sections over every étale chart is
injective on every geometric stalk: the stalk is a filtered colimit, so two germs agree only
if their representatives already agree over a common refinement. -/
private theorem stalkSetMap_injective_of_components
    {P Q : (SmallEtale B S hS X)ᵒᵖ ⥤ Type w} (x : GeometricPoint B S hS X) (α : P ⟶ Q)
    (hα : ∀ U, Function.Injective (α.app (Opposite.op U))) :
    Function.Injective (stalkSetMap x α) := by
  intro a b hab
  induction a using Quot.inductionOn with
  | _ a =>
    induction b using Quot.inductionOn with
    | _ b =>
      have := smallEtaleNeighborhood_isFiltered B S hS X hX x
      change (SmallEtaleNeighborhood.sections (x := x) Q).ιColimitType
          a.1 (α.app (Opposite.op a.1.unop.chart) a.2) =
        (SmallEtaleNeighborhood.sections (x := x) Q).ιColimitType
          b.1 (α.app (Opposite.op b.1.unop.chart) b.2) at hab
      obtain ⟨k, f, g, h⟩ :=
        (Functor.ιColimitType_eq_iff_of_isFiltered
          (F := SmallEtaleNeighborhood.sections (x := x) Q)
          (j := a.1) (j' := b.1)
          (x := α.app (Opposite.op a.1.unop.chart) a.2)
          (y := α.app (Opposite.op b.1.unop.chart) b.2)).mp hab
      apply Functor.ιColimitType_eq_of_map_eq_map
        (F := SmallEtaleNeighborhood.sections (x := x) P) a.2 b.2 f g
      apply hα k.unop.chart
      simpa [SmallEtaleNeighborhood.sections] using h

omit hX in
/-- A sieve over an étale chart which, above every point of the chart, contains a morphism
that point lifts through is a covering sieve of the small étale topology.

This is the smallness-free covering criterion for the small étale site of an algebraic space.
The criterion of the same shape supplied by a conservative family of points,
`ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem`, asks the index type
of the family to be `Small` at the universe of the sections; the objects of this site live one
universe above its morphisms and its sections, so that hypothesis is not available here.  The
criterion below needs no smallness: the family of all members of the sieve, indexed one
universe up, is replaced by a combinatorially equivalent chosen covering family through
`AlgebraicGeometry.Space.exists_chosen_etaleCovering`.

Public so that consumers outside this module can discharge a covering obligation on this site
from a pointwise statement about the chart.  Note that the hypothesis is about points of the
chart *scheme*, not about points of the site. -/
theorem smallEtale_sieve_of_pointwise_covering (U : SmallEtale B S hS X)
    (R : Sieve U)
    (hR : ∀ z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj U),
      ∃ (V : SmallEtale B S hS X) (g : V ⟶ U), R g ∧
        ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj V),
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X).map g) z' = z) :
    R ∈ SmallEtale.topology B S hS X U := by
  classical
  let I : Type (u + 1) := ULift.{1} (Σ V : SmallEtale B S hS X, {g : V ⟶ U // R g})
  let E : PreZeroHypercover.{u + 1} ((SmallEtale.toOver B S hS X).obj U).left := {
    I₀ := I
    X i := ((SmallEtale.toOver B S hS X).obj i.down.1).left
    f i := ((SmallEtale.toOver B S hS X).map i.down.2.1).left }
  let Ecov : Covering B.Schemes := ⟨((SmallEtale.toOver B S hS X).obj U).left, E⟩
  have hEt : _root_.AlgebraicGeometry.IsEtaleCovering Ecov := by
    change (Ecov.2.map B.inclusion).presieve₀ ∈
      AlgebraicGeometry.Scheme.etalePrecoverage (B.inclusion.obj Ecov.1)
    change Presieve.ofArrows _ _ ∈
      AlgebraicGeometry.Scheme.precoverage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (B.inclusion.obj Ecov.1)
    rw [AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff
      (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}))]
    constructor
    · intro z
      obtain ⟨V, g, hg, z', hz'⟩ := hR z
      refine ⟨ULift.up ⟨V, ⟨g, hg⟩⟩, z', ?_⟩
      change ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X).map g)) z' = z
      simpa [E, Ecov] using hz'
    · intro i
      let g := i.down.2.1
      let cg := (SmallEtale.inclusion B S hS X).map g
      have hχ : yoneda.map cg.left ≫ U.obj.hom =
          ((SmallEtale.inclusion B S hS X).obj i.down.1).hom := cg.w
      have : _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X).map g)) :=
        etale_of_comp_etale_chart B S hS i.down.1.property U.property hχ
      exact this
  obtain ⟨E', hCover, hComb⟩ := exists_chosen_etaleCovering B Ecov hEt
  rcases hCover with ⟨hCoverFppf, hCoverEt⟩
  rcases E' with ⟨E'target, E'family⟩
  change (∃ htarget : ((SmallEtale.toOver B S hS X).obj U).left = E'target,
    PreZeroHypercover.CombinatoriallyEquivalent (htarget ▸ E) E'family) at hComb
  obtain ⟨htarget, hComb⟩ := hComb
  cases htarget
  obtain ⟨β, hXβ, hfβ⟩ := hComb.2
  let Esite : PreZeroHypercover U := {
    I₀ := E'family.I₀
    X i := (β i).down.1
    f i := (β i).down.2.1 }
  have hpre : Esite.presieve₀ ∈ SmallEtale.precoverage B S hS X U := by
    rw [SmallEtale.mem_precoverage_iff]
    refine ⟨Esite, rfl, ?_⟩
    change B.etaleCovering ⟨
      (SmallEtale.toOver B S hS X ⋙ BigFppfOver.forget B S hS).obj U,
      Esite.map (SmallEtale.toOver B S hS X ⋙ BigFppfOver.forget B S hS)⟩
    have hmap : (Esite.map (SmallEtale.toOver B S hS X ⋙
        BigFppfOver.forget B S hS)).presieve₀ = E'family.presieve₀ := by
      apply PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent
      refine ⟨⟨fun i => i, ?_, ?_⟩, ⟨fun i => i, ?_, ?_⟩⟩
      · intro i
        exact (hXβ i).symm
      · intro i
        change E.f (β i) = eqToHom (hXβ i).symm ≫ E'family.f i
        rw [hfβ i]
        simp
      · intro i
        exact hXβ i
      · intro i
        exact hfβ i
    have hmapScheme :
        ((Esite.map (SmallEtale.toOver B S hS X ⋙
          BigFppfOver.forget B S hS)).presieve₀).map B.inclusion =
        (E'family.presieve₀).map B.inclusion :=
      congrArg (fun Q : Presieve _ => Q.map B.inclusion) hmap
    constructor
    · change IsFppfCovering
        ⟨(SmallEtale.toOver B S hS X ⋙ BigFppfOver.forget B S hS).obj U,
          Esite.map (SmallEtale.toOver B S hS X ⋙ BigFppfOver.forget B S hS)⟩ ∧
        Cardinal.mk Esite.I₀ ≤ B.coveringBound
      constructor
      · change (Esite.map (SmallEtale.toOver B S hS X ⋙
            BigFppfOver.forget B S hS)).presieve₀ ∈
            AlgebraicGeometry.Scheme.fppfPrecoverage.comap B.inclusion _
        rw [Precoverage.mem_comap_iff, hmapScheme]
        exact hCoverFppf.1
      · simpa [Esite] using hCoverFppf.2
    · change ((Esite.map (SmallEtale.toOver B S hS X ⋙
          BigFppfOver.forget B S hS)).map B.inclusion).presieve₀ ∈
          AlgebraicGeometry.Scheme.etalePrecoverage
          (B.inclusion.obj ((SmallEtale.toOver B S hS X ⋙
            BigFppfOver.forget B S hS).obj U))
      rw [PreZeroHypercover.presieve₀_map, hmapScheme]
      change (E'family.map B.inclusion).presieve₀ ∈
        AlgebraicGeometry.Scheme.etalePrecoverage
          (B.inclusion.obj ((SmallEtale.toOver B S hS X ⋙
            BigFppfOver.forget B S hS).obj U)) at hCoverEt
      simpa only [PreZeroHypercover.presieve₀_map] using hCoverEt
  have hgen : Sieve.generate Esite.presieve₀ ∈ SmallEtale.topology B S hS X U :=
    Precoverage.generate_mem_toGrothendieck hpre
  apply (SmallEtale.topology B S hS X).superset_covering ?_ hgen
  rw [Sieve.generate_le_iff]
  rintro V g ⟨i⟩
  exact (β i).down.2.2

/-- A sieve over an étale chart is covering as soon as, for every geometric point and every lift
of it to the chart, some lift of the point to a member of the sieve factors through that lift. -/
private theorem smallEtale_sieve_of_geometric_lifts (U : SmallEtale B S hS X) (R : Sieve U)
    (h : ∀ (x : GeometricPoint B S hS X) (p : (etaleSitePoint B S hS X x hX).fiber.obj U),
      ∃ (V : SmallEtale B S hS X) (g : V ⟶ U), R g ∧
        ∃ q : (etaleSitePoint B S hS X x hX).fiber.obj V,
          (etaleSitePoint B S hS X x hX).fiber.map g q = p) :
    R ∈ SmallEtale.topology B S hS X U := by
  apply smallEtale_sieve_of_pointwise_covering B S hS X U R
  intro z
  obtain ⟨x, p, z', hz⟩ := exists_geo_lift_at_chart_point B S hS X U z
  obtain ⟨V, g, hg, q, hq⟩ := h x p
  refine ⟨V, g, hg, (BigFppfOver.toScheme B S hS).map q.1 z', ?_⟩
  have hm : q.1 ≫ (SmallEtale.toOver B S hS X).map g = p.1 := congrArg Subtype.val hq
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hm]
  exact hz

/-! ### Injectivity and surjectivity of maps of sheaves of sets -/

/-- **Stacks 04K5.** A map of sheaves of sets on the small étale site of an algebraic space
is injective on sections over every étale chart exactly when it is injective on every
geometric stalk. -/
@[stacks 04K5 "injectivity", sga "4 VIII 3.6" "injectivity clause"]
theorem injective_iff_stalkSetMap_injective
    {F G : Sheaf (SmallEtale.topology B S hS X) (Type w)} (a : F ⟶ G) :
    (∀ U : SmallEtale B S hS X, Function.Injective (a.hom.app (Opposite.op U))) ↔
      ∀ x : GeometricPoint B S hS X, Function.Injective (stalkSetMap x a.hom) := by
  constructor
  · intro ha x
    exact stalkSetMap_injective_of_components B S hS X hX x a.hom (fun U => ha U)
  · intro ha U s t hst
    let R : Sieve U := Presheaf.equalizerSieve (F := F.obj) s t
    have hcover : R ∈ SmallEtale.topology B S hS X U := by
      apply smallEtale_sieve_of_geometric_lifts B S hS X hX
      intro x p
      let N : SmallEtaleNeighborhood x := ⟨U, p.1, p.2⟩
      let j : (SmallEtaleNeighborhood x)ᵒᵖ := Opposite.op N
      let d := SmallEtaleNeighborhood.sections (x := x) F.obj
      have hstalk : stalkSetMap x a.hom (d.ιColimitType j s) =
          stalkSetMap x a.hom (d.ιColimitType j t) := by
        rw [stalkSetMap_ι, stalkSetMap_ι]
        exact congrArg (fun q =>
          (SmallEtaleNeighborhood.sections (x := x) G.obj).ιColimitType j q) hst
      have hsrc := ha x hstalk
      have := smallEtaleNeighborhood_isFiltered B S hS X hX x
      obtain ⟨k, f, hEq⟩ :=
        (Functor.ιColimitType_eq_iff_of_isFiltered' (F := d) (j := j) s t).mp hsrc
      let g : k.unop.chart ⟶ U := f.unop.hom
      refine ⟨k.unop.chart, g, ?_, ⟨k.unop.point, k.unop.point_comp⟩,
        Subtype.ext ?_⟩
      · change (F.obj.map g.op) s = (F.obj.map g.op) t
        simpa [g, d, SmallEtaleNeighborhood.sections] using hEq
      · change k.unop.point ≫ (SmallEtale.toOver B S hS X).map g = p.1
        simpa [N, g] using f.unop.point_comp
    apply (((isSheaf_iff_isSheaf_of_type
      (SmallEtale.topology B S hS X) F.obj).1 F.property).isSeparated R hcover).ext
    intro V g hg
    exact hg

/-- **Stacks 04K5.** A map of sheaves of sets on the small étale site of an algebraic space
is locally surjective exactly when it is surjective on every geometric stalk. -/
@[stacks 04K5 "surjectivity", sga "4 VIII 3.6" "surjectivity clause"]
theorem surjective_iff_stalkSetMap_surjective
    {F G : Sheaf (SmallEtale.topology B S hS X) (Type w)} (a : F ⟶ G) :
    Sheaf.IsLocallySurjective a ↔
      ∀ x : GeometricPoint B S hS X, Function.Surjective (stalkSetMap x a.hom) := by
  constructor
  · intro ha x
    let d := SmallEtaleNeighborhood.sections (x := x) F.obj
    let e := SmallEtaleNeighborhood.sections (x := x) G.obj
    intro y
    obtain ⟨N, b, hb⟩ := e.ιColimitType_jointly_surjective y
    let Φ := etaleSitePoint B S hS X x hX
    have : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X) a.hom := ha
    have hR := Presheaf.imageSieve_mem (SmallEtale.topology B S hS X) a.hom b
    let hp : Φ.fiber.obj N.unop.chart := ⟨N.unop.point, N.unop.point_comp⟩
    obtain ⟨V, g, hg, p', hp'⟩ := Φ.jointly_surjective _ hR hp
    let N' : SmallEtaleNeighborhood x := ⟨V, p'.1, p'.2⟩
    let s := Presheaf.localPreimage a.hom b g hg
    have hs : a.hom.app (Opposite.op V) s = G.obj.map g.op b :=
      Presheaf.app_localPreimage a.hom b g hg
    let r : N' ⟶ N.unop := ⟨g, congrArg Subtype.val hp'⟩
    refine ⟨d.ιColimitType (Opposite.op N') s, ?_⟩
    rw [← hb, stalkSetMap_ι]
    apply Functor.ιColimitType_eq_of_map_eq_map (F := e)
      (j := Opposite.op N') (j' := N) (f := 𝟙 _) (f' := Opposite.op r)
    simpa [e, N', SmallEtaleNeighborhood.sections, r] using hs
  · intro h
    refine ⟨?_⟩
    intro U b
    let R := Presheaf.imageSieve a.hom b
    apply smallEtale_sieve_of_geometric_lifts B S hS X hX
    intro x p
    let N : SmallEtaleNeighborhood x := ⟨U, p.1, p.2⟩
    let e := SmallEtaleNeighborhood.sections (x := x) G.obj
    let d := SmallEtaleNeighborhood.sections (x := x) F.obj
    obtain ⟨sClass, hs⟩ := h x (e.ιColimitType (Opposite.op N) b)
    obtain ⟨j, s, rfl⟩ := d.ιColimitType_jointly_surjective sClass
    have := smallEtaleNeighborhood_isFiltered B S hS X hX x
    obtain ⟨k, f, g, heq⟩ :=
      (Functor.ιColimitType_eq_iff_of_isFiltered (F := e) (j := j) (j' := Opposite.op N)
        (x := (a.hom.app (Opposite.op j.unop.chart)) s) (y := b)).mp hs
    let m : k.unop.chart ⟶ U := g.unop.hom
    refine ⟨k.unop.chart, m, ?_, ⟨k.unop.point, k.unop.point_comp⟩,
      Subtype.ext ?_⟩
    · change ∃ s₀, a.hom.app (Opposite.op k.unop.chart) s₀ = G.obj.map m.op b
      refine ⟨(F.obj.map f.unop.hom.op) s, ?_⟩
      have hnat := congrArg (fun q => q s) (a.hom.naturality f.unop.hom.op)
      change a.hom.app (Opposite.op k.unop.chart) ((F.obj.map f.unop.hom.op) s) =
        G.obj.map f.unop.hom.op (a.hom.app (Opposite.op j.unop.chart) s) at hnat
      calc
        a.hom.app (Opposite.op k.unop.chart) ((F.obj.map f.unop.hom.op) s) =
            G.obj.map f.unop.hom.op (a.hom.app (Opposite.op j.unop.chart) s) := hnat
        _ = G.obj.map m.op b := heq
    · change k.unop.point ≫ (SmallEtale.toOver B S hS X).map m = p.1
      simpa [N, m] using g.unop.point_comp

/-! ### Exactness of sequences of sheaves of abelian groups -/

/-- The sheaf fibre functors at the geometric points of an algebraic space are jointly
faithful on sheaves of abelian groups: two maps with the same germ at every geometric point
agree on a covering sieve of each chart, hence agree. -/
private theorem pointSheafFiber_jointlyFaithful :
    JointlyFaithful (fun x : GeometricPoint B S hS X =>
      (etaleSitePoint B S hS X x hX).sheafFiber (A := AddCommGrpCat.{max (u + 1) w})) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max (u + 1) w}) :=
    preservesFilteredColimitsOfSize_shrink.{u, max (u + 1) w, u, max (u + 1) w}
      (forget AddCommGrpCat.{max (u + 1) w})
  constructor
  intro F G f g hfg
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  let P := G.obj ⋙ forget AddCommGrpCat
  let R : Sieve U.unop := Presheaf.equalizerSieve (F := P)
    ((f.hom.app U).hom s) ((g.hom.app U).hom s)
  have hR : R ∈ SmallEtale.topology B S hS X U.unop := by
    apply smallEtale_sieve_of_geometric_lifts B S hS X hX
    intro x p
    let pt := etaleSitePoint B S hS X x hX
    let q : pt.fiber.obj U.unop := p
    have heq : pt.toPresheafFiber U.unop q G.obj ((f.hom.app U).hom s) =
        pt.toPresheafFiber U.unop q G.obj ((g.hom.app U).hom s) := by
      have h := ConcreteCategory.congr_hom (hfg x) (pt.toPresheafFiber U.unop q F.obj s)
      change pt.presheafFiber.map f.hom (pt.toPresheafFiber U.unop q F.obj s) =
        pt.presheafFiber.map g.hom (pt.toPresheafFiber U.unop q F.obj s) at h
      simpa only [GrothendieckTopology.Point.toPresheafFiber_naturality_apply] using h
    obtain ⟨V, m, q', hq', hsections⟩ := (pt.toPresheafFiber_eq_iff' U.unop q _ _).1 heq
    exact ⟨V, m, hsections, q', hq'⟩
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS X) P :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose (SmallEtale.topology B S hS X) (forget AddCommGrpCat)).obj G).property
  exact (hsheaf.isSeparated R hR).ext (fun _ _ hg => hg)

/-- `pointStalkIso` as an isomorphism between the sheaf fibre functor at the point of the
site of Stacks 04K0 and the geometric stalk functor of Stacks 04JY, on sheaves of abelian
groups. -/
private noncomputable def pointSheafStalkIso (x : GeometricPoint B S hS X) :
    (etaleSitePoint B S hS X x hX).sheafFiber (A := AddCommGrpCat.{max (u + 1) w}) ≅
      sheafToPresheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{max (u + 1) w} ⋙
        stalkFunctor AddCommGrpCat.{max (u + 1) w} x :=
  NatIso.ofComponents (fun F => pointStalkIso B S hS X hX F.obj x)
    (fun f => (pointStalkIso_naturality B S hS X hX _ _ x f.hom).symm)

/-- **The fibre at the point of Stacks 04K0 is the geometric stalk of Stacks 04JY**, on sheaves
of abelian groups: the sheaf fibre functor at the point of the small étale site attached to a
geometric point is isomorphic to the geometric stalk functor.

This is the only identification in the development of the fibre at the point of Stacks 04K0
with the geometric stalk, and the fibre is what the module stalk of `Stacks.sheafModuleFiber`
forgets to, so anything comparing a stalk of modules with a stalk of abelian sheaves passes
through it.  `@[no_expose]`: the body is the private plumbing `pointStalkIso` and its
naturality; what a consumer needs is the isomorphism. -/
@[no_expose, sga "4½ Arcata 2.3.2" "more general"]
noncomputable def sheafFiberGeometricStalkIso (x : GeometricPoint B S hS X) :
    (etaleSitePoint B S hS X x hX).sheafFiber (A := AddCommGrpCat.{max (u + 1) w}) ≅
      sheafToPresheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{max (u + 1) w} ⋙
        stalkFunctor AddCommGrpCat.{max (u + 1) w} x :=
  pointSheafStalkIso B S hS X hX x

omit hX in
/-- Presheaves of abelian groups with sections in `max (u + 1) w` have sheafifications on the
small étale site of an algebraic space.

`AlgebraicGeometry.Space.SmallEtale.instHasSheafify` is the same statement for sections in the
universe `u` of the schemes, and does not apply here: it asks the coefficient category to have
its morphisms in `u`, which for `AddCommGrpCat.{m}` forces `m = u`.  The objects of the small
étale site lie in `Type (u + 1)` and its morphisms in `Type u`, so the site is essentially
small at `max (u + 1) w` as well — not by its small model at `u`, but by
`CategoryTheory.essentiallySmallSelf` — and at that level the coefficients sit in the universe
of the small model, where Mathlib's sheafification applies.

It is `local` because its coefficient universe `max (u + 1) w` is not an instance head that
unifies with a bare `u`: offered to a goal about `AddCommGrpCat.{u}` on the same site, instance
search does not reject it but gets stuck solving `u =?= max (u + 1) ?w`. -/
local instance hasSheafify_smallEtale_addCommGrpCat :
    HasSheafify (SmallEtale.topology B S hS X) AddCommGrpCat.{max (u + 1) w} := by
  let _ : EssentiallySmall.{max (u + 1) w} (SmallEtale B S hS X) :=
    essentiallySmallSelf.{w, u, u + 1} _
  let _ : HasSheafify ((equivSmallModel.{max (u + 1) w}
        (SmallEtale B S hS X)).inverse.inducedTopology (SmallEtale.topology B S hS X))
      AddCommGrpCat.{max (u + 1) w} := inferInstance
  exact hasSheafifyEssentiallySmallSite.{u, _, u + 1, _, max (u + 1) w} _ _

/-- **Stacks 04K5.** A short complex of sheaves of abelian groups on the small étale site of
an algebraic space is exact exactly when its sequence of geometric stalks is exact at every
geometric point. -/
@[stacks 04K5 "exactness"]
theorem exact_iff_stalk_exact
    (T : ShortComplex (Sheaf (SmallEtale.topology B S hS X)
      AddCommGrpCat.{max (u + 1) w})) :
    T.Exact ↔ ∀ x : GeometricPoint B S hS X,
      let Φ := sheafToPresheaf (SmallEtale.topology B S hS X)
        AddCommGrpCat.{max (u + 1) w} ⋙ stalkFunctor AddCommGrpCat.{max (u + 1) w} x
      ∀ b : Φ.obj T.X₂,
        ((Φ.map T.g).hom b = 0 ↔ ∃ a : Φ.obj T.X₁, (Φ.map T.f).hom a = b) := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) w} :=
    AB5OfSize_shrink.{u, u, max (u + 1) w, max (u + 1) w} _
  let Ψ := fun x : GeometricPoint B S hS X =>
    (etaleSitePoint B S hS X x hX).sheafFiber (A := AddCommGrpCat.{max (u + 1) w})
  have hex : T.Exact ↔ ∀ x, (T.map (Ψ x)).Exact := by
    constructor
    · intro h x
      exact h.map (Ψ x)
    · intro h
      rw [T.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
      apply (pointSheafFiber_jointlyFaithful B S hS X hX).map_injective
      intro x
      have hz : IsZero ((Ψ x).obj T.homology) :=
        (Iso.isZero_iff (T.mapHomologyIso (Ψ x))).1
          ((T.map (Ψ x)).exact_iff_isZero_homology.1 (h x))
      exact hz.eq_of_src _ _
  rw [hex]
  apply forall_congr'
  intro x
  let Φ := sheafToPresheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{max (u + 1) w} ⋙
    stalkFunctor AddCommGrpCat.{max (u + 1) w} x
  let e : Ψ x ≅ Φ := pointSheafStalkIso B S hS X hX x
  have : PreservesFiniteLimits Φ := preservesFiniteLimits_of_natIso e
  have : Φ.PreservesZeroMorphisms := by infer_instance
  rw [ShortComplex.exact_iff_of_iso (T.mapNatIso e), ShortComplex.ab_exact_iff]
  apply forall_congr'
  intro b
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨a, rfl⟩
    exact ConcreteCategory.congr_hom (T.map Φ).zero a
  · intro h
    exact h.1

/-! ### The small étale site has enough points -/

/-- **The geometric points are a conservative family.** A map of sheaves of sets on the small
étale site of an algebraic space which is an isomorphism on the fibre at every geometric point
is an isomorphism, in Mathlib's `ObjectProperty` shape.

Deliberately untagged.  The source does not state this separately: it is the "`X_étale` has
enough points" consequence of Theorem 04K5 which Stacks 04KH and 073C cite the theorem for,
and the theorem's own three clauses are the three statements above. -/
theorem isConservativeFamilyOfPoints_etaleSitePoint :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj
        (fun x : GeometricPoint B S hS X => etaleSitePoint B S hS X x hX)) := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro U R hR
  apply smallEtale_sieve_of_geometric_lifts B S hS X hX
  intro x p
  have hmem := ObjectProperty.ofObj_apply
    (fun y : GeometricPoint B S hS X => etaleSitePoint B S hS X y hX) x
  obtain ⟨V, g, hg, q, hq⟩ := hR ⟨etaleSitePoint B S hS X x hX, hmem⟩ p
  exact ⟨V, g, hg, q, hq⟩

/-- The geometric points of an algebraic space are a conservative family of points of its
small étale site, in the indexed shape of Stacks 00YK (1). -/
theorem isConservativeFamily_etaleSitePoint :
    (SmallEtale.topology B S hS X).IsConservativeFamily
      (fun x : GeometricPoint B S hS X => etaleSitePoint B S hS X x hX) :=
  (GrothendieckTopology.isConservativeFamily_iff_ofObj _).2
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X hX)

/-- The small étale site of an algebraic space has enough points, in the sense of
Stacks 00YK (2): the geometric points are a conservative family. -/
theorem hasConservativeFamily_smallEtale :
    (SmallEtale.topology B S hS X).HasConservativeFamily.{u} :=
  GrothendieckTopology.IsConservativeFamily.hasConservativeFamily
    (isConservativeFamily_etaleSitePoint B S hS X hX)

/-! ### Exactness of the geometric stalk functors -/

/-- `pointStalkIso` as an isomorphism of functors on presheaves, for coefficients in any
category with colimits of the size of the site. -/
private noncomputable def pointPresheafStalkIso {A : Type v} [Category A]
    [HasColimitsOfSize.{u, u} A] (x : GeometricPoint B S hS X)
    [HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ A] :
    (etaleSitePoint B S hS X x hX).presheafFiber (A := A) ≅ stalkFunctor A x :=
  NatIso.ofComponents (fun P ↦ pointStalkIso B S hS X hX P x)
    (fun f ↦ (pointStalkIso_naturality B S hS X hX _ _ x f).symm)

omit hX in
/-- The small étale neighbourhoods of a geometric point index colimits wherever the elements
of the geometric fibre do, the two categories being equivalent. -/
private theorem hasColimitsOfShape_neighborhood (x : GeometricPoint B S hS X)
    {A : Type v} [Category A]
    [HasColimitsOfShape (geometricFiber B S hS X x).Elementsᵒᵖ A] :
    HasColimitsOfShape (SmallEtaleNeighborhood x)ᵒᵖ A :=
  hasColimitsOfShape_of_equivalence (neighborhoodFiberElementsEquiv B S hS X x).op.symm

/-- The categorical colimit over the small étale neighbourhoods and the quotient colimit
`AlgebraicGeometry.Space.stalkSet` compute the same stalk of a presheaf of sets, naturally in
the presheaf. -/
private noncomputable def stalkCatSetIso (x : GeometricPoint B S hS X) :
    stalkFunctor (Type (max (u + 1) w)) x ≅ stalkSetFunctor x := by
  refine NatIso.ofComponents
    (fun P ↦ Equiv.toIso (Types.colimitEquivColimitType
      (SmallEtaleNeighborhood.sections (x := x) P))) ?_
  intro P Q α
  apply colimit.hom_ext
  intro U
  change colimit.ι (SmallEtaleNeighborhood.sections (x := x) P) U ≫
      (stalkFunctor (Type (max (u + 1) w)) x).map α ≫
        (Types.colimitEquivColimitType
          (SmallEtaleNeighborhood.sections (x := x) Q)).toIso.hom =
    colimit.ι (SmallEtaleNeighborhood.sections (x := x) P) U ≫
      (Types.colimitEquivColimitType
        (SmallEtaleNeighborhood.sections (x := x) P)).toIso.hom ≫
          (stalkSetFunctor x).map α
  rw [← Category.assoc, stalkFunctor_ι_map, Category.assoc]
  apply ConcreteCategory.hom_ext
  intro a
  change Types.colimitEquivColimitType (SmallEtaleNeighborhood.sections (x := x) Q)
      ((colimit.ι (SmallEtaleNeighborhood.sections (x := x) Q) U)
        (α.app (Opposite.op U.unop.chart) a)) =
    (stalkSetFunctor x).map α
      (Types.colimitEquivColimitType (SmallEtaleNeighborhood.sections (x := x) P)
        ((colimit.ι (SmallEtaleNeighborhood.sections (x := x) P) U) a))
  rw [Types.colimitEquivColimitType_apply]
  conv_rhs => rw [Types.colimitEquivColimitType_apply]
  rfl

/-- Raising the values of a presheaf of sets to a larger universe. -/
private noncomputable def liftSetPresheafFunctor :
    ((SmallEtale B S hS X)ᵒᵖ ⥤ Type w) ⥤
      ((SmallEtale B S hS X)ᵒᵖ ⥤ Type (max (u + 1) w)) :=
  (Functor.whiskeringRight _ _ _).obj (uliftFunctor.{u + 1, w})

/-- Raising the values of a diagram of sets to a larger universe does not change its quotient
colimit. -/
private noncomputable def liftColimitTypeEquiv {J : Type (u + 1)} [Category.{u} J]
    (P : J ⥤ Type w) :
    (P ⋙ uliftFunctor.{u + 1, w}).ColimitType ≃ P.ColimitType := by
  classical
  refine
    { toFun := Quot.lift (fun z ↦ P.ιColimitType z.1 z.2.down) ?_
      invFun := Quot.lift
        (fun z ↦ (P ⋙ uliftFunctor.{u + 1, w}).ιColimitType z.1 (ULift.up z.2)) ?_
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨i, a⟩ ⟨j, b⟩ ⟨f, h⟩
    exact Quot.sound ⟨f, congrArg ULift.down h⟩
  · rintro ⟨i, a⟩ ⟨j, b⟩ ⟨f, h⟩
    exact Quot.sound ⟨f, congrArg ULift.up h⟩
  · rintro ⟨i, a⟩
    rfl
  · rintro ⟨i, a⟩
    rfl

/-- The set-valued stalk functor is unchanged by raising the values of its argument to a
larger universe. -/
private noncomputable def stalkSetLiftIso (x : GeometricPoint B S hS X) :
    stalkSetFunctor x ≅
      liftSetPresheafFunctor.{u, w} B S hS X ⋙ stalkSetFunctor x := by
  refine NatIso.ofComponents (fun P ↦ Equiv.toIso (liftColimitTypeEquiv
    (SmallEtaleNeighborhood.sections (x := x) P)).symm) ?_
  intro P Q α
  apply ConcreteCategory.hom_ext
  intro z
  obtain ⟨U, a, rfl⟩ :=
    (SmallEtaleNeighborhood.sections (x := x) P).ιColimitType_jointly_surjective z
  rfl

/-- The fibre at the point of the site of Stacks 04K0 of a presheaf of sets, with its values
raised to the universe of the site, is the set-valued geometric stalk of Stacks 04JY. -/
private noncomputable def pointSetStalkIso (x : GeometricPoint B S hS X) :
    liftSetPresheafFunctor.{u, w} B S hS X ⋙
        (etaleSitePoint B S hS X x hX).presheafFiber (A := Type (max (u + 1) w)) ≅
      stalkSetFunctor x :=
  (Functor.isoWhiskerLeft _ (pointPresheafStalkIso B S hS X hX
      (A := Type (max (u + 1) w)) x)).trans
    ((Functor.isoWhiskerLeft _ (stalkCatSetIso B S hS X x)).trans
      (stalkSetLiftIso B S hS X x).symm)

omit hX in
/-- The fibre of a point of a site at set-valued presheaves preserves finite limits: it is a
restriction followed by a filtered colimit of sets. -/
private theorem pointFiber_preservesFiniteLimits {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} (p : J.Point.{u}) :
    PreservesFiniteLimits (p.presheafFiber (A := Type (max (u + 1) w))) := by
  change PreservesFiniteLimits
    ((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op ⋙
      colim (J := p.fiber.Elementsᵒᵖ) (C := Type (max (u + 1) w)))
  exact comp_preservesFiniteLimits _ _

omit hX in
/-- The fibre of a point of a site at set-valued presheaves preserves all colimits. -/
private theorem pointFiber_preservesColimits {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} (p : J.Point.{u}) :
    PreservesColimits (p.presheafFiber (A := Type (max (u + 1) w))) := by
  change PreservesColimits
    ((Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π p.fiber).op ⋙
      colim (J := p.fiber.Elementsᵒᵖ) (C := Type (max (u + 1) w)))
  exact comp_preservesColimits _ _

/-- **Stacks 04K1, part (1).** The geometric stalk of a presheaf of abelian groups on the
small étale site is left exact. -/
@[stacks 04K1 "part (1): finite limits"]
theorem presheafAbelianStalk_preservesFiniteLimits (x : GeometricPoint B S hS X) :
    PreservesFiniteLimits (stalkFunctor AddCommGrpCat.{max (u + 1) w} x) := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) w} :=
    AB5OfSize_shrink.{u, u, max (u + 1) w, max (u + 1) w} _
  have := hasColimitsOfShape_neighborhood B S hS X x
    (A := AddCommGrpCat.{max (u + 1) w})
  have : PreservesFiniteLimits ((etaleSitePoint B S hS X x hX).presheafFiber
    (A := AddCommGrpCat.{max (u + 1) w})) := inferInstance
  exact preservesFiniteLimits_of_natIso (pointPresheafStalkIso B S hS X hX x)

/-- **Stacks 04K1, part (1).** The geometric stalk of a presheaf of abelian groups on the
small étale site is right exact. -/
@[stacks 04K1 "part (1): finite colimits"]
theorem presheafAbelianStalk_preservesFiniteColimits (x : GeometricPoint B S hS X) :
    PreservesFiniteColimits (stalkFunctor AddCommGrpCat.{max (u + 1) w} x) := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) w} :=
    AB5OfSize_shrink.{u, u, max (u + 1) w, max (u + 1) w} _
  have := hasColimitsOfShape_neighborhood B S hS X x
    (A := AddCommGrpCat.{max (u + 1) w})
  have : PreservesColimitsOfSize.{u, u} ((etaleSitePoint B S hS X x hX).presheafFiber
    (A := AddCommGrpCat.{max (u + 1) w})) := inferInstance
  have : PreservesFiniteColimits ((etaleSitePoint B S hS X x hX).presheafFiber
      (A := AddCommGrpCat.{max (u + 1) w})) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  exact preservesFiniteColimits_of_natIso (pointPresheafStalkIso B S hS X hX x)

/-- **Stacks 04K1, part (2).** Sheafification does not change the geometric stalk of a
presheaf of sets: the comparison induced by the unit of sheafification is an isomorphism. -/
@[stacks 04K1 "part (2): sheafification comparison"]
theorem stalkSetMap_toSheafify_isIso (x : GeometricPoint B S hS X)
    (P : (SmallEtale B S hS X)ᵒᵖ ⥤ Type (max (u + 1) w)) :
    IsIso ((stalkSetFunctor x).map
      ((SmallEtale.topology B S hS X).toSheafify P)) := by
  let J := SmallEtale.topology B S hS X
  let T := Type (max (u + 1) w)
  have hW : J.W (J.toSheafify P) := by
    have hη : J.W (CategoryTheory.toSheafify J P) := J.W_toSheafify P
    have hη' : IsIso ((presheafToSheaf J T).map (CategoryTheory.toSheafify J P)) :=
      (GrothendieckTopology.W_iff_isIso_map_of_adjunction J
        (sheafificationAdjunction J T) _).1 hη
    have hfac : J.toSheafify P ≫ (plusPlusIsoSheafify J T P).hom =
        CategoryTheory.toSheafify J P :=
      toSheafify_plusPlusIsoSheafify_hom J T P
    have hiso : IsIso ((presheafToSheaf J T).map (J.toSheafify P)) := by
      have hmap : (presheafToSheaf J T).map (J.toSheafify P) =
          (presheafToSheaf J T).map (CategoryTheory.toSheafify J P) ≫
            (asIso ((presheafToSheaf J T).map (plusPlusIsoSheafify J T P).hom)).inv := by
        rw [← hfac, Functor.map_comp]
        simp
      rw [hmap]
      infer_instance
    exact (GrothendieckTopology.W_iff_isIso_map_of_adjunction J
      (sheafificationAdjunction J T) _).2 hiso
  have hp : IsIso ((etaleSitePoint B S hS X x hX).presheafFiber.map (J.toSheafify P)) :=
    (etaleSitePoint B S hS X x hX).W_isInvertedBy_presheafFiber _ hW
  exact (NatIso.isIso_map_iff
    ((pointPresheafStalkIso B S hS X hX (A := T) x).trans
      (stalkCatSetIso B S hS X x)) (J.toSheafify P)).1 hp

/-- **Stacks 04K1, part (3).** The geometric stalk of a sheaf of abelian groups on the small
étale site is left exact. -/
@[stacks 04K1 "part (3): finite limits"]
theorem sheafAbelianStalk_preservesFiniteLimits (x : GeometricPoint B S hS X) :
    PreservesFiniteLimits
      (sheafToPresheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{max (u + 1) w} ⋙
        stalkFunctor AddCommGrpCat.{max (u + 1) w} x) := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) w} :=
    AB5OfSize_shrink.{u, u, max (u + 1) w, max (u + 1) w} _
  have := hasColimitsOfShape_neighborhood B S hS X x
    (A := AddCommGrpCat.{max (u + 1) w})
  have : PreservesFiniteLimits ((etaleSitePoint B S hS X x hX).sheafFiber
    (A := AddCommGrpCat.{max (u + 1) w})) := inferInstance
  exact preservesFiniteLimits_of_natIso (Functor.isoWhiskerLeft _
    (pointPresheafStalkIso B S hS X hX (A := AddCommGrpCat.{max (u + 1) w}) x))

/-- **Stacks 04K1, part (3).** The geometric stalk of a sheaf of abelian groups on the small
étale site is right exact. -/
@[stacks 04K1 "part (3): finite colimits"]
theorem sheafAbelianStalk_preservesFiniteColimits (x : GeometricPoint B S hS X) :
    PreservesFiniteColimits
      (sheafToPresheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{max (u + 1) w} ⋙
        stalkFunctor AddCommGrpCat.{max (u + 1) w} x) := by
  have : AB5OfSize.{u, u} AddCommGrpCat.{max (u + 1) w} :=
    AB5OfSize_shrink.{u, u, max (u + 1) w, max (u + 1) w} _
  have := hasColimitsOfShape_neighborhood B S hS X x
    (A := AddCommGrpCat.{max (u + 1) w})
  have hcomp : PreservesFiniteColimits
      (sheafToPresheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{max (u + 1) w} ⋙
        (etaleSitePoint B S hS X x hX).presheafFiber
          (A := AddCommGrpCat.{max (u + 1) w})) := by
    change PreservesFiniteColimits ((etaleSitePoint B S hS X x hX).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) w}))
    infer_instance
  exact @preservesFiniteColimits_of_natIso _ _ _ _ _ _
    (Functor.isoWhiskerLeft _
      (pointPresheafStalkIso B S hS X hX (A := AddCommGrpCat.{max (u + 1) w}) x)) hcomp

/-- **Stacks 04K1, part (4).** The geometric stalk of a presheaf of sets on the small étale
site preserves finite limits. -/
@[stacks 04K1 "part (4): presheaf sets, finite limits"]
theorem presheafSetStalk_preservesFiniteLimits (x : GeometricPoint B S hS X) :
    PreservesFiniteLimits
      (stalkSetFunctor x : ((SmallEtale B S hS X)ᵒᵖ ⥤ Type w) ⥤ Type (max (u + 1) w)) := by
  have : PreservesFiniteLimits (liftSetPresheafFunctor.{u, w} B S hS X) := by
    dsimp [liftSetPresheafFunctor]
    infer_instance
  have : PreservesFiniteLimits ((etaleSitePoint B S hS X x hX).presheafFiber
    (A := Type (max (u + 1) w))) := pointFiber_preservesFiniteLimits _
  exact preservesFiniteLimits_of_natIso (pointSetStalkIso B S hS X hX x)

/-- **Stacks 04K1, part (4).** The geometric stalk of a presheaf of sets on the small étale
site preserves finite colimits. -/
@[stacks 04K1 "part (4): presheaf sets, finite colimits"]
theorem presheafSetStalk_preservesFiniteColimits (x : GeometricPoint B S hS X) :
    PreservesFiniteColimits
      (stalkSetFunctor x : ((SmallEtale B S hS X)ᵒᵖ ⥤ Type w) ⥤ Type (max (u + 1) w)) := by
  have : PreservesFiniteColimits (liftSetPresheafFunctor.{u, w} B S hS X) := by
    dsimp [liftSetPresheafFunctor]
    infer_instance
  have : PreservesColimits ((etaleSitePoint B S hS X x hX).presheafFiber
    (A := Type (max (u + 1) w))) := pointFiber_preservesColimits _
  exact preservesFiniteColimits_of_natIso (pointSetStalkIso B S hS X hX x)

/-- **Stacks 04K1, part (4).** The geometric stalk of a presheaf of sets on the small étale
site commutes with arbitrary colimits of presheaves. -/
@[stacks 04K1 "part (4): presheaf sets, colimits"]
theorem presheafSetStalk_preservesColimits (x : GeometricPoint B S hS X) :
    PreservesColimitsOfSize.{w, w}
      (stalkSetFunctor x : ((SmallEtale B S hS X)ᵒᵖ ⥤ Type w) ⥤ Type (max (u + 1) w)) := by
  have : PreservesColimitsOfSize.{w, w} (liftSetPresheafFunctor.{u, w} B S hS X) := by
    dsimp [liftSetPresheafFunctor]
    infer_instance
  have : PreservesColimitsOfSize.{w, w} ((etaleSitePoint B S hS X x hX).presheafFiber
      (A := Type (max (u + 1) w))) := by
    change PreservesColimitsOfSize.{w, w}
      ((Functor.whiskeringLeft _ _ _).obj
        (CategoryOfElements.π (etaleSitePoint B S hS X x hX).fiber).op ⋙
        colim (J := (etaleSitePoint B S hS X x hX).fiber.Elementsᵒᵖ)
          (C := Type (max (u + 1) w)))
    exact comp_preservesColimits _ _
  exact preservesColimits_of_natIso (pointSetStalkIso B S hS X hX x)

/-- **Stacks 04K1, part (4).** The geometric stalk of a sheaf of sets on the small étale site
preserves finite limits. -/
@[stacks 04K1 "part (4): sheaves of sets, finite limits"]
theorem sheafSetStalk_preservesFiniteLimits (x : GeometricPoint B S hS X) :
    PreservesFiniteLimits
      (sheafToPresheaf (SmallEtale.topology B S hS X) (Type w) ⋙ stalkSetFunctor x) := by
  have := presheafSetStalk_preservesFiniteLimits B S hS X hX x
  exact comp_preservesFiniteLimits _ _

/-- **Stacks 04K1, part (4).** The geometric stalk of a sheaf of sets on the small étale site
preserves finite colimits. -/
@[stacks 04K1 "part (4): sheaves of sets, finite colimits"]
theorem sheafSetStalk_preservesFiniteColimits (x : GeometricPoint B S hS X) :
    PreservesFiniteColimits
      (sheafToPresheaf (SmallEtale.topology B S hS X) (Type (max (u + 1) w)) ⋙
        stalkSetFunctor x) := by
  have hp : PreservesFiniteColimits
      (sheafToPresheaf (SmallEtale.topology B S hS X) (Type (max (u + 1) w)) ⋙
        (etaleSitePoint B S hS X x hX).presheafFiber (A := Type (max (u + 1) w))) := by
    change PreservesFiniteColimits ((etaleSitePoint B S hS X x hX).sheafFiber
      (A := Type (max (u + 1) w)))
    infer_instance
  exact preservesFiniteColimits_of_natIso (Functor.isoWhiskerLeft _
    ((pointPresheafStalkIso B S hS X hX (A := Type (max (u + 1) w)) x).trans
      (stalkCatSetIso B S hS X x)))

/-- **Stacks 04K1, part (4).** The geometric stalk of a sheaf of sets on the small étale site
commutes with arbitrary colimits of sheaves. -/
@[stacks 04K1 "part (4): sheaves of sets, colimits", sga "4 VIII 3.5" "3.5 a)"]
theorem sheafSetStalk_preservesColimits (x : GeometricPoint B S hS X) :
    PreservesColimitsOfSize.{max (u + 1) w, max (u + 1) w}
      (sheafToPresheaf (SmallEtale.topology B S hS X) (Type (max (u + 1) w)) ⋙
        stalkSetFunctor x) := by
  have hp : PreservesColimitsOfSize.{max (u + 1) w, max (u + 1) w}
      (sheafToPresheaf (SmallEtale.topology B S hS X) (Type (max (u + 1) w)) ⋙
        (etaleSitePoint B S hS X x hX).presheafFiber (A := Type (max (u + 1) w))) := by
    change PreservesColimitsOfSize.{max (u + 1) w, max (u + 1) w}
      ((etaleSitePoint B S hS X x hX).sheafFiber (A := Type (max (u + 1) w)))
    infer_instance
  exact preservesColimits_of_natIso (Functor.isoWhiskerLeft _
    ((pointPresheafStalkIso B S hS X hX (A := Type (max (u + 1) w)) x).trans
      (stalkCatSetIso B S hS X x)))

end AlgebraicGeometry.Space

end
