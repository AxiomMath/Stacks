module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.OverField
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Finiteness of the relation fibres of an algebraic space above a point

Let `F` be a presheaf on the big fppf site of a scheme `S`, let `f : h_U ⟶ F` be an étale
chart of it by a scheme `U` and let `R = U ×_F U` be the associated relation. Stacks 03JU
compares four finiteness conditions at a point `x` of `|F|`: that the fibre of
`|R| → |U| ×_{|F|} |U|` above one pair of points of `U` over `x` is finite, that the same
holds for every chart and every such pair, that `x` has a field-valued representative whose
two self-intersection projections are étale and quasi-compact, and that `x` has a
monomorphic field-valued representative.

This file defines those four conditions and proves the equivalences between them for an
algebraic space `F`, with the exception of the implication from (3) to (4), which rests on the
quotient of `Spec k ×_F Spec k` by its étale equivalence relation and is in
`StacksFrontier/AlgebraicGeometry/Spaces/MonomorphicFieldRepresentative.lean`.

## Main definitions

* `AlgebraicGeometry.Space.HasFiniteRelationFiber` says that the relation fibre of an étale
  chart above a pair of points of the chart is finite.
* `AlgebraicGeometry.Space.HasFiniteRelationFiberAt` and
  `AlgebraicGeometry.Space.HasFiniteRelationFiberAtEveryEtaleChart` are conditions (1) and
  (2) of Stacks 03JU.
* `AlgebraicGeometry.Space.fieldMorphism` is the morphism to `F` presented by a field-valued
  point, and `AlgebraicGeometry.Space.HasEtaleQuasiCompactFieldRepresentative` and
  `AlgebraicGeometry.Space.HasMonomorphicFieldRepresentative` are conditions (3) and (4).

## Main results

The names below all live in the namespace `AlgebraicGeometry.Space`, which is omitted here
because several of them are too long to spell with it.

* `hasFiniteRelationFiberAt_iff_everyEtaleChart` is the equivalence of conditions (1) and (2),
  and `hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative`
  the equivalence of (2) and (3). Their substantial halves are
  `hasEtaleQuasiCompactFieldRepresentative_of_hasFiniteRelationFiberAt` and
  `hasFiniteRelationFiberAtEveryEtaleChart_of_hasEtaleQuasiCompactFieldRepresentative`, and
  `hasFiniteRelationFiberAtEveryEtaleChart_of_hasFiniteRelationFiberAt` is their composite.
* `hasEtaleQuasiCompactFieldRepresentative_of_hasMonomorphicFieldRepresentative` and
  `hasFiniteRelationFiberAtEveryEtaleChart_of_hasMonomorphicFieldRepresentative` are
  condition (4) implies (3) and hence (2). The converse implication from (3) to (4) needs the
  quotient of `Spec k ×_F Spec k` by its étale equivalence relation, so it is proved
  separately in `StacksFrontier/AlgebraicGeometry/Spaces/MonomorphicFieldRepresentative.lean`,
  which cannot be imported here; the resulting equivalence of conditions (3) and (4) is
  `hasEtaleQuasiCompactFieldRepresentative_iff_hasMonomorphicFieldRepresentative` there.
* `exists_etale_chart_point_of_point`: every point of an algebraic space lies in the image of
  some étale chart.
* `fieldMorphism_map`, `fieldMorphism_yoneda` and
  `pointsMap_fieldMorphism_tautologicalPoint`: the morphism presented by a field-valued point
  recovers the point and is compatible with morphisms of presheaves.
* `mono_fieldMorphism_schemePointRepresentative`: the canonical field-valued representative
  above a point of a scheme is presented by a monomorphism.

## Implementation notes

Points of a presheaf are the equivalence classes of field-valued points of Tag 03BU, so the
relation fibre above a pair `(a, b)` is literally the fibre of the pair of maps on point
classes induced by the two projections of the presheaf pullback `h_U ×_F h_U`; no separate
model of `|R| → |U| ×_{|F|} |U|` is needed. Étaleness of the chart is
`AlgebraicGeometry.Space.IsEtale` of Tag 03FR, while in condition (3) étaleness *and*
quasi-compactness of the self-intersection projections are tested after representable base
change, that is through `CategoryTheory.MorphismProperty.presheaf` of the inverse image of
the infimum of Mathlib's `AlgebraicGeometry.Etale` and `AlgebraicGeometry.QuasiCompact`.
Note that this is not `AlgebraicGeometry.Space.IsEtale` and not
`AlgebraicGeometry.Space.IsQuasiCompact`: those two are the algebraic-space conditions of
Tags 03FR and 03HE, whereas the source asks here only for the representable base changes of
the two projections out of `Spec k ×_F Spec k`.

The spectrum of a field representing a point is the Yoneda image of its
`AlgebraicGeometry.Space.FieldValuedPoint.siteObject`, and `fieldMorphism` is the
corresponding morphism under `CategoryTheory.yonedaEquiv`.

The source argues with the scheme `u ×_F u'` for two points `u`, `u'` of a chart. Here `u` is
the canonical field-valued representative
`AlgebraicGeometry.Space.schemePointRepresentative` above a point of the chart, which is
presented by the monomorphism from the spectrum of the residue field, so that `u ×_F u'` is
the base change of the étale chart along a monomorphism. That makes it a
monomorphism into a scheme étale over a field, hence an open immersion followed by an étale
morphism, which is where the étaleness and quasi-compactness of the projections of
condition (3) come from. The finiteness bookkeeping is carried out on the point sets of
Tag 03BU rather than on the underlying topological spaces, using that a quasi-compact étale
morphism has finite fibres.

## References

* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Conditions (1) and (2): finiteness of a relation fibre -/

/-- The relation fibre of a chart `f : h_U ⟶ F` above a pair `(a, b)` of points of `h_U` is
finite: there are finitely many points of `h_U ×_F h_U` whose two projections are `a` and
`b`. This is the finiteness condition appearing in conditions (1) and (2) of Stacks 03JU. -/
def HasFiniteRelationFiber (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (a b : points B S hS (yoneda.obj U)) : Prop :=
  {r : points B S hS (pullback f f) |
    pointsMap B S hS (pullback f f) (pullback.fst f f) r = a ∧
    pointsMap B S hS (pullback f f) (pullback.snd f f) r = b}.Finite

/-- **Stacks 03JU, condition (1).** Some étale chart of `F` has two points above `x` with
finite relation fibre. -/
def HasFiniteRelationFiberAt (x : points B S hS F) : Prop :=
  ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (a b : points B S hS (yoneda.obj U)),
    IsEtale B S hS f ∧
    pointsMap B S hS (yoneda.obj U) f a = x ∧
    pointsMap B S hS (yoneda.obj U) f b = x ∧
    HasFiniteRelationFiber B S hS F U f a b

/-- **Stacks 03JU, condition (2).** Every pair of points above `x` in every étale chart of
`F` has finite relation fibre. -/
def HasFiniteRelationFiberAtEveryEtaleChart (x : points B S hS F) : Prop :=
  ∀ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (a b : points B S hS (yoneda.obj U)),
    IsEtale B S hS f →
    pointsMap B S hS (yoneda.obj U) f a = x →
    pointsMap B S hS (yoneda.obj U) f b = x →
    HasFiniteRelationFiber B S hS F U f a b

/-! ### Conditions (3) and (4): field-valued representatives -/

/-- The morphism to `F` presented by a field-valued point, out of the Yoneda image of the
object of the site the point is defined on. -/
noncomputable abbrev fieldMorphism (p : FieldValuedPoint B S hS F) :
    yoneda.obj p.siteObject ⟶ F :=
  yonedaEquiv.symm p.value

/-- **Stacks 03JU, condition (3).** Some field-valued representative of `x` has étale and
quasi-compact self-intersection projections, both tested after representable base change. -/
def HasEtaleQuasiCompactFieldRepresentative (x : points B S hS F) : Prop :=
  ∃ p : FieldValuedPoint B S hS F,
    p.class B S hS F = x ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)))
      (pullback.fst (fieldMorphism B S hS F p) (fieldMorphism B S hS F p)) ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))
      (BigFppfOver.toScheme B S hS)))
      (pullback.snd (fieldMorphism B S hS F p) (fieldMorphism B S hS F p))

/-- **Stacks 03JU, condition (4).** Some field-valued representative of `x` presents it by a
monomorphism from the spectrum of a field. -/
def HasMonomorphicFieldRepresentative (x : points B S hS F) : Prop :=
  ∃ p : FieldValuedPoint B S hS F,
    p.class B S hS F = x ∧ Mono (fieldMorphism B S hS F p)

/-! ### Elementary properties -/

/-- The morphism presented by a field-valued point recovers its section of `F`. -/
theorem yonedaEquiv_fieldMorphism (p : FieldValuedPoint B S hS F) :
    yonedaEquiv (fieldMorphism B S hS F p) = p.value :=
  Equiv.apply_symm_apply _ _

/-- The identity of `p.siteObject`, viewed as a field-valued point of the presheaf
represented by `p.siteObject`. -/
noncomputable abbrev FieldValuedPoint.tautologicalPoint (p : FieldValuedPoint B S hS F) :
    FieldValuedPoint B S hS (yoneda.obj p.siteObject) where
  carrier := p.carrier
  field := p.field
  contained := p.contained
  toBase := p.toBase
  value := 𝟙 p.siteObject

/-- The morphism presented by a field-valued point recovers its class as a point of `|F|`:
it sends the tautological point of `h_{p.siteObject}` to `p`. -/
theorem pointsMap_fieldMorphism_tautologicalPoint (p : FieldValuedPoint B S hS F) :
    pointsMap B S hS (yoneda.obj p.siteObject) (fieldMorphism B S hS F p)
        ((p.tautologicalPoint B S hS F).class B S hS (yoneda.obj p.siteObject)) =
      p.class B S hS F := by
  rw [pointsMap_class]
  congr 1
  obtain ⟨carrier, contained, toBase, value⟩ := p
  simp only [FieldValuedPoint.map, FieldValuedPoint.mk.injEq, heq_eq_eq, true_and]
  exact yonedaEquiv_fieldMorphism B S hS F _

/-- A chart whose relation has at most one point has all its relation fibres finite. -/
theorem hasFiniteRelationFiber_of_subsingleton (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ F) (hf : Subsingleton (points B S hS (pullback f f)))
    (a b : points B S hS (yoneda.obj U)) :
    HasFiniteRelationFiber B S hS F U f a b :=
  Set.Finite.subset Set.finite_univ (Set.subset_univ _)

/-- **Stacks 03JU, (2) implies (1).** Condition (2) gives condition (1) as soon as some
étale chart of `F` has a point above `x`.

This is the formal half of the equivalence of (1) and (2); the substance of that equivalence
is the converse, that one chart with finite relation fibre forces every chart to have one. -/
theorem hasFiniteRelationFiberAt_of_everyEtaleChart {x : points B S hS F}
    (h : HasFiniteRelationFiberAtEveryEtaleChart B S hS F x) (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ F) (hf : IsEtale B S hS f)
    (a : points B S hS (yoneda.obj U)) (ha : pointsMap B S hS (yoneda.obj U) f a = x) :
    HasFiniteRelationFiberAt B S hS F x :=
  ⟨U, f, a, a, hf, ha, ha, h U f a a hf ha ha⟩

/-! ### The presenting morphism of a field-valued point -/

/-- The morphism presented by the image of a field-valued point along a morphism of
presheaves is the morphism it presents followed by that morphism. -/
theorem fieldMorphism_map {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G)
    (p : FieldValuedPoint B S hS F) :
    fieldMorphism B S hS G (FieldValuedPoint.map B S hS F α p) =
      fieldMorphism B S hS F p ≫ α := by
  show yonedaEquiv.symm (α.app _ p.value) = yonedaEquiv.symm p.value ≫ α
  apply yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply, yonedaEquiv_comp]

/-- A field-valued point of a represented presheaf `h_U` is literally a morphism of the site
from a field spectrum to `U`; this is that morphism. -/
noncomputable abbrev FieldValuedPoint.siteHom {U : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (yoneda.obj U)) : p.siteObject ⟶ U :=
  p.value

/-- On a represented presheaf the morphism presented by a field-valued point is the Yoneda
image of the underlying morphism of the site. -/
theorem fieldMorphism_yoneda {U : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    fieldMorphism B S hS (yoneda.obj U) p = yoneda.map p.siteHom := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_fieldMorphism, yonedaEquiv_yoneda_map]

/-- On a represented presheaf, the morphism presented by the image of a field-valued point
along a morphism out of that presheaf is the Yoneda image of its site morphism followed by
that morphism. -/
theorem fieldMorphism_map_yoneda {V : BigFppfOver B S hS} (α : yoneda.obj V ⟶ F)
    (r : FieldValuedPoint B S hS (yoneda.obj V)) :
    fieldMorphism B S hS F (FieldValuedPoint.map B S hS (yoneda.obj V) α r) =
      yoneda.map r.siteHom ≫ α :=
  (fieldMorphism_map B S hS (yoneda.obj V) α r).trans
    (congrArg (· ≫ α) (fieldMorphism_yoneda B S hS r))

/-- The same identity with the two morphisms of the site composed before applying Yoneda. -/
theorem yoneda_map_siteHom_comp {V W : BigFppfOver B S hS}
    (r : FieldValuedPoint B S hS (yoneda.obj V)) (g : V ⟶ W) (α : yoneda.obj W ⟶ F) :
    yoneda.map (r.siteHom ≫ g) ≫ α =
      fieldMorphism B S hS F
        (FieldValuedPoint.map B S hS (yoneda.obj V) (yoneda.map g ≫ α) r) :=
  ((congrArg (· ≫ α) (yoneda.map_comp r.siteHom g)).trans (Category.assoc _ _ _)).trans
    (fieldMorphism_map_yoneda B S hS F (yoneda.map g ≫ α) r).symm

/-- The identity above, with the composite recognised through any morphism equal to it. -/
private theorem yoneda_map_siteHom_comp' {V W : BigFppfOver B S hS}
    (r : FieldValuedPoint B S hS (yoneda.obj V)) (g : V ⟶ W) (α : yoneda.obj W ⟶ F)
    (β : yoneda.obj V ⟶ F) (hβ : yoneda.map g ≫ α = β) :
    yoneda.map (r.siteHom ≫ g) ≫ α =
      fieldMorphism B S hS F (FieldValuedPoint.map B S hS (yoneda.obj V) β r) := by
  subst hβ
  exact yoneda_map_siteHom_comp B S hS F r g α

/-- The spectrum of the field of definition of a field-valued point has at most one point. -/
theorem subsingleton_toScheme_siteObject (p : FieldValuedPoint B S hS F) :
    Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) := by
  show Subsingleton (Spec (CommRingCat.of p.carrier))
  infer_instance

/-- The spectrum of the field of definition of a field-valued point has finitely many
points. -/
theorem finite_toScheme_siteObject (p : FieldValuedPoint B S hS F) :
    Finite ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
  have := subsingleton_toScheme_siteObject B S hS F p
  Finite.of_subsingleton

/-- A representable presheaf whose representing scheme has finitely many points has finitely
many points. -/
theorem finite_points_yoneda (U : BigFppfOver B S hS)
    (h : Finite ((BigFppfOver.toScheme B S hS).obj U)) :
    Finite (points B S hS (yoneda.obj U)) :=
  have := h
  Finite.of_injective _ (injective_pointsToScheme B S hS U)

/-! ### The canonical representative above a point of an étale chart -/

/-- The morphism of schemes underlying the canonical field-valued representative above a
point of the representing scheme is the morphism from the spectrum of the residue field at
that point. -/
theorem toScheme_map_siteHom_schemePointRepresentative (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    (BigFppfOver.toScheme B S hS).map (schemePointRepresentative B S hS U x).siteHom =
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x := by
  let Z := (BigFppfOver.toScheme B S hS).obj U
  let kobj : B.Schemes := B.obj (B.residueField_spec_contains U.left.property x)
  show B.inclusion.map (B.inclusion.preimage (X := kobj) (Y := U.left)
    (Z.fromSpecResidueField x)) = Z.fromSpecResidueField x
  rw [B.inclusion.map_preimage]

/-- The morphism of schemes underlying the canonical field-valued representative above a
point of the representing scheme is a monomorphism. -/
theorem mono_toScheme_map_siteHom_schemePointRepresentative (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    Mono ((BigFppfOver.toScheme B S hS).map
      (schemePointRepresentative B S hS U x).siteHom) := by
  have h : Mono (((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x) :=
    inferInstance
  rw [← toScheme_map_siteHom_schemePointRepresentative] at h
  exact h

/-- The canonical field-valued representative above a point of the representing scheme is
presented by a monomorphism of the site. -/
theorem mono_siteHom_schemePointRepresentative (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    Mono (schemePointRepresentative B S hS U x).siteHom :=
  Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS)
    (mono_toScheme_map_siteHom_schemePointRepresentative B S hS U x)

/-- The canonical field-valued representative above a point of the representing scheme
presents it by a monomorphism of presheaves. -/
theorem mono_fieldMorphism_schemePointRepresentative (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    Mono (fieldMorphism B S hS (yoneda.obj U) (schemePointRepresentative B S hS U x)) := by
  have := mono_siteHom_schemePointRepresentative B S hS U x
  rw [fieldMorphism_yoneda]
  exact Functor.map_mono yoneda _

/-- The canonical field-valued representative above the scheme point of a point of a
represented presheaf represents that very point. -/
theorem class_schemePointRepresentative_pointsToScheme (U : BigFppfOver B S hS)
    (a : points B S hS (yoneda.obj U)) :
    (schemePointRepresentative B S hS U (pointsToScheme B S hS U a)).class
        B S hS (yoneda.obj U) = a :=
  Quot.inductionOn a (schemePointRepresentative_class B S hS U)

/-! ### Monomorphisms into a scheme étale over a field -/

/-- A monomorphism into a scheme étale over the spectrum of a field is an open immersion.
Such a scheme is a disjoint union of spectra of fields by Stacks 03PC, and a monomorphism into
a disjoint union of spectra of fields is the inclusion of a subfamily of its components by
Stacks 03DP. -/
@[sga "3 XI 3.10" "special case"]
private theorem isOpenImmersion_of_mono_of_etale_over_field {k : Type u} [Field k]
    {E T : Scheme.{u}} (f : E ⟶ Spec (.of k)) (hf : AlgebraicGeometry.Etale f) (g : T ⟶ E)
    (hg : Mono g) : _root_.AlgebraicGeometry.IsOpenImmersion g := by
  have := hf
  have := hg
  obtain ⟨I, K, _, _, _, _, e, -⟩ :=
    (etale_iff_iso_coproduct_spectra_finite_separable k f).mp hf
  have : Mono (g ≫ e.hom) := inferInstance
  obtain ⟨J, eT, hfac⟩ := exists_iso_coproduct_spec_of_mono K (g ≫ e.hom)
  have hinc : _root_.AlgebraicGeometry.IsOpenImmersion
      (Sigma.desc fun j : J ↦ Sigma.ι (fun i : I ↦ Spec (.of (K i))) j.1) := by
    apply isOpenImmersion_sigmaDesc
    intro i j hij
    simpa [Function.onFun_apply, disjoint_iff, TopologicalSpace.Opens.ext_iff] using
      disjoint_opensRange_sigmaι (fun i : I ↦ Spec (.of (K i))) i.1 j.1
        fun h ↦ hij (Subtype.ext h)
  have hcomp : eT.hom ≫ (Sigma.desc fun j : J ↦
      Sigma.ι (fun i : I ↦ Spec (.of (K i))) j.1) ≫ e.inv = g := by
    rw [← Category.assoc, hfac, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [← hcomp]
  infer_instance

/-- A monomorphism with finitely many points into a scheme étale over the spectrum of a field
composes with the structure morphism to an étale quasi-compact morphism: the monomorphism is
an open immersion, hence étale, and a scheme with finitely many points is quasi-compact. -/
private theorem etale_and_quasiCompact_comp_of_mono_of_etale_over_field {k : Type u} [Field k]
    {E T : Scheme.{u}} (f : E ⟶ Spec (.of k)) (hf : AlgebraicGeometry.Etale f) (g : T ⟶ E)
    (hg : Mono g) (hT : Finite T) :
    AlgebraicGeometry.Etale (g ≫ f) ∧ AlgebraicGeometry.QuasiCompact (g ≫ f) := by
  have := hf
  have := hg
  have := hT
  have : _root_.AlgebraicGeometry.IsOpenImmersion g :=
    isOpenImmersion_of_mono_of_etale_over_field f hf g hg
  have : AlgebraicGeometry.Etale g := inferInstance
  have : CompactSpace T := inferInstance
  exact ⟨AlgebraicGeometry.Etale.etale_comp g f, inferInstance⟩

/-! ### Étale quasi-compact morphisms of presheaves -/

/-- Étaleness together with quasi-compactness of morphisms of schemes, read as a property of
morphisms of presheaves on the big fppf site of `S` by testing it on every representable base
change. This is the property of the two self-intersection projections in condition (3) of
Stacks 03JU. -/
private abbrev etaleQuasiCompactPresheaf :
    MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.inverseImage
    ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))
    (BigFppfOver.toScheme B S hS)).presheaf

private theorem etaleQuasiCompact_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})) :=
  MorphismProperty.IsStableUnderBaseChange.inf
    (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}))
    (Q := (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))

private theorem etaleQuasiCompact_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      ((@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})) :=
  have := AlgebraicGeometry.etale_isStableUnderComposition.{u}
  MorphismProperty.IsStableUnderComposition.inf
    (P := (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}))
    (Q := (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}))

attribute [local instance] etaleQuasiCompact_isStableUnderBaseChange
  etaleQuasiCompact_isStableUnderComposition

private instance etaleQuasiCompactPresheaf_isStableUnderBaseChange :
    (etaleQuasiCompactPresheaf B S hS).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

private instance etaleQuasiCompactPresheaf_isStableUnderComposition :
    (etaleQuasiCompactPresheaf B S hS).IsStableUnderComposition :=
  have := inverseImage_isStableUnderComposition B S hS
    etaleQuasiCompact_isStableUnderComposition.{u}
  MorphismProperty.relative_isStableUnderComposition _

/-- A morphism of the site whose underlying morphism of schemes is étale and quasi-compact is
étale and quasi-compact after Yoneda. -/
private theorem etaleQuasiCompactPresheaf_yoneda_map {U V : BigFppfOver B S hS} (φ : U ⟶ V)
    (h : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map φ) ∧
      AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map φ)) :
    etaleQuasiCompactPresheaf B S hS (yoneda.map φ) :=
  (presheaf_yoneda_map_iff B S hS etaleQuasiCompact_isStableUnderBaseChange.{u} φ).2 h

/-- Every fibre of a quasi-compact étale morphism of schemes is finite: an étale morphism is
locally quasi-finite by Stacks 03II. -/
private theorem finite_preimage_singleton_of_etale_of_quasiCompact {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : AlgebraicGeometry.Etale f) (hq : AlgebraicGeometry.QuasiCompact f)
    (y : Y) : (f ⁻¹' {y}).Finite :=
  have := hf
  have := hq
  have := (AlgebraicGeometry.locallyQuasiFinite_of_etale f).2
  f.finite_preimage_singleton y

/-- A morphism of presheaves which is étale and quasi-compact after every representable base
change has finite fibres on points. -/
private theorem finite_pointFiber_of_etaleQuasiCompactPresheaf
    {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : G ⟶ H)
    (hf : etaleQuasiCompactPresheaf B S hS f) (b : points B S hS H) :
    (pointsMap B S hS G f ⁻¹' {b}).Finite := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep b
  have ht := hf.property_snd (fieldMorphism B S hS H p)
  have hsub := subsingleton_toScheme_siteObject B S hS H p
  have hfinite : Finite ((BigFppfOver.toScheme B S hS).obj
      (hf.rep.pullback (fieldMorphism B S hS H p))) := by
    have hh := finite_preimage_singleton_of_etale_of_quasiCompact
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd (fieldMorphism B S hS H p)))
      ht.1 ht.2 (IsLocalRing.closedPoint p.carrier)
    exact Set.finite_univ_iff.1 (hh.subset fun z _ ↦ Subsingleton.elim _ _)
  have := finite_points_yoneda B S hS
    (hf.rep.pullback (fieldMorphism B S hS H p)) hfinite
  refine (Set.finite_range (pointsMap B S hS
    (yoneda.obj (hf.rep.pullback (fieldMorphism B S hS H p)))
    (hf.rep.fst (fieldMorphism B S hS H p)))).subset fun a ha ↦ ?_
  obtain ⟨r, hr, -⟩ := exists_points_of_isPullback B S hS
    (hf.rep.isPullback (fieldMorphism B S hS H p)) a
    ((p.tautologicalPoint B S hS H).class B S hS (yoneda.obj p.siteObject))
    (ha.trans (pointsMap_fieldMorphism_tautologicalPoint B S hS H p).symm)
  exact ⟨r, hr⟩

/-- The source of a morphism of presheaves which is étale and quasi-compact after every
representable base change has finitely many points as soon as the target does. -/
private theorem finite_points_of_etaleQuasiCompactPresheaf
    {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : G ⟶ H)
    (hf : etaleQuasiCompactPresheaf B S hS f) (hH : Finite (points B S hS H)) :
    Finite (points B S hS G) :=
  have := hH
  Finite.of_finite_univ ((Set.toFinite (Set.univ : Set (points B S hS H))).preimage'
    fun b _ ↦ finite_pointFiber_of_etaleQuasiCompactPresheaf B S hS f hf b)

/-! ### Changing the two legs of a fibre product -/

section PullbackChange

variable {C : Type*} [Category C]

/-- A property of morphisms stable under isomorphisms transfers along an isomorphism of the
source. -/
private theorem mem_of_iso_source (P : MorphismProperty C) [P.RespectsIso] {A A' D : C}
    (e : A ≅ A') (f : A ⟶ D) (g : A' ⟶ D) (he : e.hom ≫ g = f) (hf : P f) : P g :=
  (MorphismProperty.arrow_mk_iso_iff P
    (Arrow.isoMk e (Iso.refl D) (by simpa using he))).1 hf

variable [HasPullbacks C]

/-- For a self-fibre product, the second projection has an isomorphism-stable property as soon
as the first does. -/
private theorem pullback_snd_self_mem (P : MorphismProperty C) [P.RespectsIso] {A K : C}
    (f : A ⟶ K) (h : P (pullback.fst f f)) : P (pullback.snd f f) :=
  mem_of_iso_source P (pullbackSymmetry f f) (pullback.fst f f) (pullback.snd f f) (by simp) h

/-- Precomposing the first leg of a fibre product square exhibits the comparison morphism as
a base change of that leg. -/
private theorem isPullback_pullbackMap_left {A G H K : C} (i : A ⟶ G) (f : G ⟶ K) (g : H ⟶ K)
    (e₁ : (i ≫ f) ≫ 𝟙 K = i ≫ f) (e₂ : g ≫ 𝟙 K = 𝟙 H ≫ g) :
    IsPullback (pullback.map (i ≫ f) g f g i (𝟙 H) (𝟙 K) e₁ e₂)
      (pullback.fst (i ≫ f) g) (pullback.fst f g) i := by
  have hsnd : pullback.map (i ≫ f) g f g i (𝟙 H) (𝟙 K) e₁ e₂ ≫ pullback.snd f g =
      pullback.snd (i ≫ f) g := by simp [pullback.map, pullback.lift_snd]
  refine IsPullback.of_right (t := (IsPullback.of_hasPullback f g).flip) ?_ ?_
  · rw [hsnd]
    exact (IsPullback.of_hasPullback (i ≫ f) g).flip
  · simp [pullback.map, pullback.lift_fst]

/-- Precomposing the second leg of a fibre product square exhibits the comparison morphism as
a base change of that leg. -/
private theorem isPullback_pullbackMap_right {A G H K : C} (j : A ⟶ H) (f : G ⟶ K) (g : H ⟶ K)
    (e₁ : f ≫ 𝟙 K = 𝟙 G ≫ f) (e₂ : (j ≫ g) ≫ 𝟙 K = j ≫ g) :
    IsPullback (pullback.map f (j ≫ g) f g (𝟙 G) j (𝟙 K) e₁ e₂)
      (pullback.snd f (j ≫ g)) (pullback.snd f g) j := by
  have hfst : pullback.map f (j ≫ g) f g (𝟙 G) j (𝟙 K) e₁ e₂ ≫ pullback.fst f g =
      pullback.fst f (j ≫ g) := by simp [pullback.map, pullback.lift_fst]
  refine IsPullback.of_right (t := IsPullback.of_hasPullback f g) ?_ ?_
  · rw [hfst]
    exact IsPullback.of_hasPullback f (j ≫ g)
  · simp [pullback.map, pullback.lift_snd]

/-- Precomposing both legs of a fibre product square by monomorphisms gives a monomorphic
comparison morphism. -/
private theorem mono_pullbackMap {A A' D D' K : C} (i : A' ⟶ A) (j : D' ⟶ D)
    (hi : Mono i) (hj : Mono j) (f : A ⟶ K) (g : D ⟶ K) :
    Mono (pullback.map (i ≫ f) (j ≫ g) f g i j (𝟙 K) (by simp) (by simp)) := by
  have := hi
  have := hj
  refine ⟨fun a b hab ↦ pullback.hom_ext ?_ ?_⟩
  · refine (cancel_mono i).1 ?_
    simpa only [pullback.map, Category.assoc, pullback.lift_fst] using
      congrArg (fun k ↦ k ≫ pullback.fst f g) hab
  · refine (cancel_mono j).1 ?_
    simpa only [pullback.map, Category.assoc, pullback.lift_snd] using
      congrArg (fun k ↦ k ≫ pullback.snd f g) hab

/-- Precomposing the two legs of a fibre product square by morphisms with a base-change and
composition stable property keeps the first projection in that property. -/
private theorem pullback_fst_comp_mem (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    [P.IsStableUnderComposition] {A A' D D' K : C} (i : A' ⟶ A) (j : D' ⟶ D) (f : A ⟶ K)
    (g : D ⟶ K) (h : P (pullback.fst f g)) (hj : P j) :
    P (pullback.fst (i ≫ f) (j ≫ g)) := by
  have h₁ := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := P) (isPullback_pullbackMap_left i f g (by simp) (by simp)) h
  have h₂ := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := P) (isPullback_pullbackMap_right j (i ≫ f) g (by simp) (by simp)).flip hj
  convert P.comp_mem _ _ h₂ h₁ using 1
  simp [pullback.map, pullback.lift_fst]

end PullbackChange

/-- Precomposing the two legs of a fibre product of presheaves by morphisms which are étale
and quasi-compact after every representable base change keeps the point set finite. -/
private theorem finite_points_pullback_comp
    {A A' D D' K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : A' ⟶ A) (j : D' ⟶ D) (f : A ⟶ K)
    (g : D ⟶ K) (hi : etaleQuasiCompactPresheaf B S hS i)
    (hj : etaleQuasiCompactPresheaf B S hS j)
    (hfg : Finite (points B S hS (pullback f g))) :
    Finite (points B S hS (pullback (i ≫ f) (j ≫ g))) :=
  finite_points_of_etaleQuasiCompactPresheaf B S hS _
    (MorphismProperty.pullbackMap (P := etaleQuasiCompactPresheaf B S hS) hi hj rfl rfl) hfg

/-- Flipping the two legs of a fibre product of presheaves preserves finiteness of the point
set. -/
private theorem finite_points_pullback_symm
    {A D K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : A ⟶ K) (b : D ⟶ K)
    (h : Finite (points B S hS (pullback a b))) :
    Finite (points B S hS (pullback b a)) := by
  have := h
  refine Finite.of_surjective (pointsMap B S hS _ (pullbackSymmetry a b).hom) fun c ↦ ?_
  refine ⟨pointsMap B S hS _ (pullbackSymmetry a b).inv c, ?_⟩
  rw [← Function.comp_apply (f := pointsMap B S hS _ (pullbackSymmetry a b).hom),
    ← pointsMap_comp, Iso.inv_hom_id, pointsMap_id, id_eq]

/-- The point set of a fibre product of presheaves depends only on the two morphisms. -/
private theorem finite_points_pullback_congr
    {A D K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (c c' : A ⟶ K) (d d' : D ⟶ K)
    (hc : c = c') (hd : d = d') (h : Finite (points B S hS (pullback c d))) :
    Finite (points B S hS (pullback c' d')) := by
  subst hc hd
  exact h

/-- If the fibre product of the two precomposed legs has finitely many points, then the
relation fibre of the original fibre product above the two images is finite. -/
private theorem finite_relationFiber_of_finite_points_pullback_comp
    {A D G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : A ⟶ G) (j : D ⟶ H) (f : G ⟶ K)
    (g : H ⟶ K) (a : points B S hS A) (b : points B S hS D)
    (hfin : Finite (points B S hS (pullback (i ≫ f) (j ≫ g)))) :
    {r : points B S hS (pullback f g) |
      pointsMap B S hS _ (pullback.fst f g) r = pointsMap B S hS A i a ∧
      pointsMap B S hS _ (pullback.snd f g) r = pointsMap B S hS D j b}.Finite := by
  have := hfin
  obtain ⟨m₁, hm₁snd, sq₁⟩ : ∃ m₁ : pullback (i ≫ f) g ⟶ pullback f g,
      m₁ ≫ pullback.snd f g = pullback.snd (i ≫ f) g ∧
      IsPullback m₁ (pullback.fst (i ≫ f) g) (pullback.fst f g) i :=
    ⟨pullback.map (i ≫ f) g f g i (𝟙 H) (𝟙 K) (by simp) (by simp),
      by simp [pullback.map, pullback.lift_snd],
      isPullback_pullbackMap_left i f g _ _⟩
  obtain ⟨m₂, sq₂⟩ : ∃ m₂ : pullback (i ≫ f) (j ≫ g) ⟶ pullback (i ≫ f) g,
      IsPullback m₂ (pullback.snd (i ≫ f) (j ≫ g)) (pullback.snd (i ≫ f) g) j :=
    ⟨pullback.map (i ≫ f) (j ≫ g) (i ≫ f) g (𝟙 A) j (𝟙 K) (by simp) (by simp),
      isPullback_pullbackMap_right j (i ≫ f) g _ _⟩
  refine (Set.finite_range (pointsMap B S hS _ (m₂ ≫ m₁))).subset fun r hr ↦ ?_
  obtain ⟨r₁, h₁, -⟩ := exists_points_of_isPullback B S hS sq₁ r a hr.1
  have h₁b : pointsMap B S hS _ (pullback.snd (i ≫ f) g) r₁ = pointsMap B S hS D j b := by
    rw [← hm₁snd, pointsMap_comp, Function.comp_apply, h₁, hr.2]
  obtain ⟨r₂, h₂, -⟩ := exists_points_of_isPullback B S hS sq₂ r₁ b h₁b
  exact ⟨r₂, by rw [pointsMap_comp, Function.comp_apply, h₂, h₁]⟩

/-- Precomposing the two legs of a fibre product of presheaves by monomorphisms whose sources
have at most one point bounds its point set by one relation fibre. -/
private theorem finite_points_of_mono_pullbackMap
    {A A' D D' K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : A' ⟶ A) (j : D' ⟶ D) (f : A ⟶ K)
    (g : D ⟶ K) (m : pullback (i ≫ f) (j ≫ g) ⟶ pullback f g) (hm : Mono m)
    (hmfst : m ≫ pullback.fst f g = pullback.fst (i ≫ f) (j ≫ g) ≫ i)
    (hmsnd : m ≫ pullback.snd f g = pullback.snd (i ≫ f) (j ≫ g) ≫ j)
    (a : points B S hS A') (b : points B S hS D')
    (hA : Subsingleton (points B S hS A')) (hD : Subsingleton (points B S hS D'))
    (h : {r : points B S hS (pullback f g) |
      pointsMap B S hS _ (pullback.fst f g) r = pointsMap B S hS A' i a ∧
      pointsMap B S hS _ (pullback.snd f g) r = pointsMap B S hS D' j b}.Finite) :
    Finite (points B S hS (pullback (i ≫ f) (j ≫ g))) := by
  have := hm
  have := hA
  have := hD
  refine Finite.of_finite_univ
    ((h.preimage fun _ _ _ _ he ↦ pointsMap_injective_of_mono B S hS m he).subset
      fun r _ ↦ ⟨?_, ?_⟩)
  · rw [← Function.comp_apply (f := pointsMap B S hS _ (pullback.fst f g)), ← pointsMap_comp,
      hmfst, pointsMap_comp, Function.comp_apply,
      Subsingleton.elim (pointsMap B S hS _ (pullback.fst (i ≫ f) (j ≫ g)) r) a]
  · rw [← Function.comp_apply (f := pointsMap B S hS _ (pullback.snd f g)), ← pointsMap_comp,
      hmsnd, pointsMap_comp, Function.comp_apply,
      Subsingleton.elim (pointsMap B S hS _ (pullback.snd (i ≫ f) (j ≫ g)) r) b]

/-- A finite relation fibre of a chart above the classes of two monomorphically presented
field-valued points of that chart bounds the point set of the fibre product of their
presenting morphisms. -/
private theorem finite_points_pullback_fieldMorphism_comp (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ F) (p q : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : Mono (fieldMorphism B S hS (yoneda.obj U) p))
    (hq : Mono (fieldMorphism B S hS (yoneda.obj U) q))
    (h : HasFiniteRelationFiber B S hS F U f (p.class B S hS (yoneda.obj U))
      (q.class B S hS (yoneda.obj U))) :
    Finite (points B S hS (pullback (fieldMorphism B S hS (yoneda.obj U) p ≫ f)
      (fieldMorphism B S hS (yoneda.obj U) q ≫ f))) :=
  finite_points_of_mono_pullbackMap B S hS
    (fieldMorphism B S hS (yoneda.obj U) p) (fieldMorphism B S hS (yoneda.obj U) q) f f
    (pullback.map (fieldMorphism B S hS (yoneda.obj U) p ≫ f)
      (fieldMorphism B S hS (yoneda.obj U) q ≫ f) f f
      (fieldMorphism B S hS (yoneda.obj U) p) (fieldMorphism B S hS (yoneda.obj U) q)
      (𝟙 F) (by simp) (by simp))
    (mono_pullbackMap (fieldMorphism B S hS (yoneda.obj U) p)
      (fieldMorphism B S hS (yoneda.obj U) q) hp hq f f)
    (by simp [pullback.map, pullback.lift_fst]) (by simp [pullback.map, pullback.lift_snd])
    ((p.tautologicalPoint B S hS (yoneda.obj U)).class B S hS (yoneda.obj p.siteObject))
    ((q.tautologicalPoint B S hS (yoneda.obj U)).class B S hS (yoneda.obj q.siteObject))
    (subsingleton_points_yoneda_siteObject B S hS p)
    (subsingleton_points_yoneda_siteObject B S hS q)
    (by rwa [pointsMap_fieldMorphism_tautologicalPoint,
      pointsMap_fieldMorphism_tautologicalPoint])

/-! ### Étale quasi-compactness of the self-intersection projections -/

/-- A morphism of the site out of the spectrum of a residue field of its source, followed by
an étale morphism to a field spectrum of the site, is étale and quasi-compact after every
representable base change. -/
private theorem etaleQuasiCompactPresheaf_siteHom_comp
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS G)
    (R : BigFppfOver B S hS) (s : R ⟶ p.siteObject)
    (hs : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map s))
    (r : (BigFppfOver.toScheme B S hS).obj R) :
    etaleQuasiCompactPresheaf B S hS
      (yoneda.map ((schemePointRepresentative B S hS R r).siteHom ≫ s)) := by
  refine etaleQuasiCompactPresheaf_yoneda_map B S hS _ ?_
  rw [Functor.map_comp]
  exact etale_and_quasiCompact_comp_of_mono_of_etale_over_field
    ((BigFppfOver.toScheme B S hS).map s) hs
    ((BigFppfOver.toScheme B S hS).map (schemePointRepresentative B S hS R r).siteHom)
    (mono_toScheme_map_siteHom_schemePointRepresentative B S hS R r)
    (finite_toScheme_siteObject B S hS (yoneda.obj R)
      (schemePointRepresentative B S hS R r))

/-- A morphism between two represented presheaves which is étale and quasi-compact after every
representable base change comes from a morphism of the site with those properties. -/
private theorem etale_and_quasiCompact_of_isPullback_fst
    {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U R : BigFppfOver B S hS}
    {f : yoneda.obj U ⟶ H} {g : G ⟶ H} (s : R ⟶ U) (t : yoneda.obj R ⟶ G)
    (sq : IsPullback (yoneda.map s) t f g)
    (h : etaleQuasiCompactPresheaf B S hS (pullback.fst f g)) :
    AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map s) ∧
      AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map s) :=
  h.property (𝟙 _) sq.isoPullback.hom s
    (IsPullback.of_horiz_isIso ⟨by simp [sq.isoPullback_hom_fst]⟩)

/-- The fibre product of two morphisms out of represented presheaves into an algebraic space is
represented by an object of the site. -/
private theorem exists_isPullback_yoneda_map (hF : IsAlgebraicSpace B S hS F)
    {A V : BigFppfOver B S hS} (a : yoneda.obj A ⟶ F) (b : yoneda.obj V ⟶ F) :
    ∃ (P : BigFppfOver B S hS) (s : P ⟶ A) (t : P ⟶ V),
      IsPullback (yoneda.map s) (yoneda.map t) a b := by
  set hrep := hF.diagonal_representable.of_diag a
  refine ⟨hrep.pullback b, yoneda.preimage (hrep.fst b), hrep.snd b, ?_⟩
  simpa using hrep.isPullback b

/-- The first projection of the fibre product of the presenting morphisms of two field-valued
points of an algebraic space is étale and quasi-compact after every representable base change,
as soon as the second of them factors as a monomorphism of the site through an étale chart and
the fibre product has finitely many points.

This is the step in the proof of Stacks 03JU which makes `Spec k ×_X Spec k'` étale and
quasi-compact over `Spec k`: that fibre product is the base change of an étale morphism along
a monomorphism, hence a monomorphism into a scheme étale over a field. -/
private theorem etaleQuasiCompactPresheaf_pullback_fst_fieldMorphism
    (hF : IsAlgebraicSpace B S hS F) (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (p q : FieldValuedPoint B S hS F) (i : q.siteObject ⟶ U) (hmi : Mono i)
    (hi : fieldMorphism B S hS F q = yoneda.map i ≫ f)
    (hfin : Finite (points B S hS (pullback (fieldMorphism B S hS F p)
      (fieldMorphism B S hS F q)))) :
    etaleQuasiCompactPresheaf B S hS
      (pullback.fst (fieldMorphism B S hS F p) (fieldMorphism B S hS F q)) := by
  have := hmi
  have := hfin
  set a := fieldMorphism B S hS F p
  set b := fieldMorphism B S hS F q
  obtain ⟨T, s, t, hT⟩ := exists_isPullback_yoneda_map B S hS F hF a b
  obtain ⟨W, w, z, hW⟩ := exists_isPullback_yoneda_map B S hS F hF a f
  set ℓ := hW.lift (yoneda.map s) (yoneda.map (t ≫ i))
    (by simpa [Functor.map_comp, ← hi, Category.assoc] using hT.w) with hℓ
  set j : T ⟶ W := yoneda.preimage ℓ with hjdef
  have hjw : j ≫ w = s := by
    refine yoneda.map_injective ?_
    simp [hjdef, hℓ]
  have hjz : j ≫ z = t ≫ i := by
    refine yoneda.map_injective ?_
    simp [hjdef, hℓ]
  have hmj : Mono j := by
    refine ⟨fun α β hab ↦ yoneda.map_injective (hT.hom_ext ?_ ?_)⟩
    · have hh := congrArg (fun k ↦ yoneda.map (k ≫ w)) hab
      simpa [Functor.map_comp, hjw, Category.assoc] using hh
    · have hh := congrArg (fun k ↦ k ≫ z) hab
      have ht : α ≫ t = β ≫ t := (cancel_mono i).1 (by
        simpa [Category.assoc, hjz] using hh)
      simpa [Functor.map_comp] using congrArg (fun k ↦ yoneda.map k) ht
  have hwE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map w) :=
    hf.property a (yoneda.map z) w hW.flip
  have hfinT : Finite ((BigFppfOver.toScheme B S hS).obj T) := by
    have : Finite (points B S hS (yoneda.obj T)) :=
      Finite.of_injective _ (pointsMap_injective_of_mono B S hS hT.isoPullback.hom)
    exact Finite.of_surjective _ (surjective_pointsToScheme B S hS T)
  have hs := etale_and_quasiCompact_comp_of_mono_of_etale_over_field
    ((BigFppfOver.toScheme B S hS).map w) hwE
    ((BigFppfOver.toScheme B S hS).map j) (Functor.map_mono _ j) hfinT
  rw [← Functor.map_comp, hjw] at hs
  exact mem_of_iso_source (etaleQuasiCompactPresheaf B S hS) hT.isoPullback
    (yoneda.map s) (pullback.fst a b) hT.isoPullback_hom_fst
    (etaleQuasiCompactPresheaf_yoneda_map B S hS s hs)

/-! ### The equivalences of Stacks 03JU -/

/-- Condition (3) at a field-valued representative can be checked after replacing its
presenting morphism by any two morphisms equal to it. -/
private theorem hasEtaleQuasiCompactFieldRepresentative_of_eq (x : points B S hS F)
    (p : FieldValuedPoint B S hS F) (hp : p.class B S hS F = x)
    (c d : yoneda.obj p.siteObject ⟶ F)
    (hc : c = fieldMorphism B S hS F p) (hd : d = fieldMorphism B S hS F p)
    (hfst : etaleQuasiCompactPresheaf B S hS (pullback.fst c d)) :
    HasEtaleQuasiCompactFieldRepresentative B S hS F x := by
  subst hc hd
  exact ⟨p, hp, hfst, pullback_snd_self_mem (etaleQuasiCompactPresheaf B S hS) _ hfst⟩

/-- The passage from condition (1) to condition (3) of Stacks 03JU, with the two field-valued
points above `x` already presented by monomorphisms of the site through the chart. -/
private theorem hasEtaleQuasiCompactFieldRepresentative_of_mono_siteHom
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ F)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (p q : FieldValuedPoint B S hS F) (ip : p.siteObject ⟶ U) (iq : q.siteObject ⟶ U)
    (hmp : Mono ip) (hmq : Mono iq)
    (hip : fieldMorphism B S hS F p = yoneda.map ip ≫ f)
    (hiq : fieldMorphism B S hS F q = yoneda.map iq ≫ f)
    (hp : p.class B S hS F = x) (hq : q.class B S hS F = x)
    (a : yoneda.obj p.siteObject ⟶ F) (b : yoneda.obj q.siteObject ⟶ F)
    (hap : a = fieldMorphism B S hS F p) (hbq : b = fieldMorphism B S hS F q)
    (hab : Finite (points B S hS (pullback a b))) :
    HasEtaleQuasiCompactFieldRepresentative B S hS F x := by
  subst hap hbq
  have hba := finite_points_pullback_symm B S hS
    (fieldMorphism B S hS F p) (fieldMorphism B S hS F q) hab
  have hfst := etaleQuasiCompactPresheaf_pullback_fst_fieldMorphism B S hS F hF U f hf
    p q iq hmq hiq hab
  have hsnd := etaleQuasiCompactPresheaf_pullback_fst_fieldMorphism B S hS F hF U f hf
    q p ip hmp hip hba
  obtain ⟨P, s, t, sq⟩ := exists_isPullback_yoneda_map B S hS F hF
    (fieldMorphism B S hS F p) (fieldMorphism B S hS F q)
  have ht := etale_and_quasiCompact_of_isPullback_fst B S hS t (yoneda.map s) sq.flip hsnd
  obtain ⟨c, hc, -⟩ := exists_points_of_isPullback B S hS sq
    ((p.tautologicalPoint B S hS F).class B S hS (yoneda.obj p.siteObject))
    ((q.tautologicalPoint B S hS F).class B S hS (yoneda.obj q.siteObject))
    (by rw [pointsMap_fieldMorphism_tautologicalPoint,
      pointsMap_fieldMorphism_tautologicalPoint, hp, hq])
  refine hasEtaleQuasiCompactFieldRepresentative_of_eq B S hS F x
    (FieldValuedPoint.map B S hS (yoneda.obj P) (yoneda.map s ≫ fieldMorphism B S hS F p)
      (schemePointRepresentative B S hS P (pointsToScheme B S hS _ c))) ?_
    (yoneda.map ((schemePointRepresentative B S hS P
      (pointsToScheme B S hS _ c)).siteHom ≫ s) ≫ fieldMorphism B S hS F p)
    (yoneda.map ((schemePointRepresentative B S hS P
      (pointsToScheme B S hS _ c)).siteHom ≫ t) ≫ fieldMorphism B S hS F q) ?_ ?_ ?_
  · rw [← pointsMap_class, class_schemePointRepresentative_pointsToScheme,
      pointsMap_comp, Function.comp_apply, hc,
      pointsMap_fieldMorphism_tautologicalPoint, hp]
  · exact yoneda_map_siteHom_comp B S hS F _ s (fieldMorphism B S hS F p)
  · exact yoneda_map_siteHom_comp' B S hS F _ t (fieldMorphism B S hS F q) _ sq.w.symm
  · exact pullback_fst_comp_mem (etaleQuasiCompactPresheaf B S hS) _ _
      (fieldMorphism B S hS F p) (fieldMorphism B S hS F q) hfst
      (etaleQuasiCompactPresheaf_siteHom_comp B S hS q _ t ht.1
        (pointsToScheme B S hS _ c))

/-- **Stacks 03JU, (1) implies (3).** A point with one finite relation fibre in one étale
chart has a field-valued representative whose self-intersection projections are étale and
quasi-compact.

Two points `u` and `u'` of the chart above `x` are presented by the spectra of their residue
fields, and `u ×_X u'` is then the base change of the étale chart along a monomorphism, hence
étale and quasi-compact over each of `u` and `u'`. The representative is the one presented by
a point of `u ×_X u'` above `x`. -/
theorem hasEtaleQuasiCompactFieldRepresentative_of_hasFiniteRelationFiberAt
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (h : HasFiniteRelationFiberAt B S hS F x) :
    HasEtaleQuasiCompactFieldRepresentative B S hS F x := by
  obtain ⟨U, f, a, b, hf, ha, hb, hfinite⟩ := h
  exact hasEtaleQuasiCompactFieldRepresentative_of_mono_siteHom B S hS F hF x U f
    (presheaf_etale_of_isEtale B S hS hf)
    (FieldValuedPoint.map B S hS (yoneda.obj U) f
      (schemePointRepresentative B S hS U (pointsToScheme B S hS U a)))
    (FieldValuedPoint.map B S hS (yoneda.obj U) f
      (schemePointRepresentative B S hS U (pointsToScheme B S hS U b)))
    (schemePointRepresentative B S hS U (pointsToScheme B S hS U a)).siteHom
    (schemePointRepresentative B S hS U (pointsToScheme B S hS U b)).siteHom
    (mono_siteHom_schemePointRepresentative B S hS U _)
    (mono_siteHom_schemePointRepresentative B S hS U _)
    ((fieldMorphism_map B S hS (yoneda.obj U) f _).trans
      (congrArg (· ≫ f) (fieldMorphism_yoneda B S hS _)))
    ((fieldMorphism_map B S hS (yoneda.obj U) f _).trans
      (congrArg (· ≫ f) (fieldMorphism_yoneda B S hS _)))
    (by rwa [← pointsMap_class, class_schemePointRepresentative_pointsToScheme])
    (by rwa [← pointsMap_class, class_schemePointRepresentative_pointsToScheme])
    (fieldMorphism B S hS (yoneda.obj U)
      (schemePointRepresentative B S hS U (pointsToScheme B S hS U a)) ≫ f)
    (fieldMorphism B S hS (yoneda.obj U)
      (schemePointRepresentative B S hS U (pointsToScheme B S hS U b)) ≫ f)
    (fieldMorphism_map B S hS (yoneda.obj U) f _).symm
    (fieldMorphism_map B S hS (yoneda.obj U) f _).symm
    (finite_points_pullback_fieldMorphism_comp B S hS F U f _ _
      (mono_fieldMorphism_schemePointRepresentative B S hS U _)
      (mono_fieldMorphism_schemePointRepresentative B S hS U _)
      (by rwa [class_schemePointRepresentative_pointsToScheme,
        class_schemePointRepresentative_pointsToScheme]))

/-- **Stacks 03JU, (3) implies (2).** If a point has a field-valued representative whose
self-intersection projections are étale and quasi-compact, then every pair of points above it
in every étale chart has finite relation fibre.

Given a chart `ψ : h_W ⟶ X` and two points `w`, `w'` of `W` above `x`, both lift to the fibre
product of `ψ` with the representative, whose residue fields are finite separable over the
field of the representative. The relation fibre above `(w, w')` is then dominated by the point
set of `Spec k ×_X Spec k`, which is finite. -/
theorem hasFiniteRelationFiberAtEveryEtaleChart_of_hasEtaleQuasiCompactFieldRepresentative
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (h : HasEtaleQuasiCompactFieldRepresentative B S hS F x) :
    HasFiniteRelationFiberAtEveryEtaleChart B S hS F x := by
  obtain ⟨p, hp, hfst, -⟩ := h
  intro U f a b hf ha hb
  set fp := fieldMorphism B S hS F p
  obtain ⟨P, w, z, sq⟩ := exists_isPullback_yoneda_map B S hS F hF fp f
  have hw : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map w) :=
    (presheaf_etale_of_isEtale B S hS hf).property fp (yoneda.map z) w sq.flip
  have key : ∀ y : points B S hS (yoneda.obj U), pointsMap B S hS _ f y = x →
      ∃ r : FieldValuedPoint B S hS (yoneda.obj P),
        etaleQuasiCompactPresheaf B S hS (yoneda.map (r.siteHom ≫ w)) ∧
        pointsMap B S hS _ (yoneda.map (r.siteHom ≫ z))
          ((r.tautologicalPoint B S hS (yoneda.obj P)).class B S hS (yoneda.obj r.siteObject)) =
            y := by
    intro y hy
    obtain ⟨c, -, hc⟩ := exists_points_of_isPullback B S hS sq
      ((p.tautologicalPoint B S hS F).class B S hS (yoneda.obj p.siteObject)) y
      (by rw [pointsMap_fieldMorphism_tautologicalPoint, hp, hy])
    refine ⟨schemePointRepresentative B S hS P (pointsToScheme B S hS _ c),
      etaleQuasiCompactPresheaf_siteHom_comp B S hS p _ w hw _, ?_⟩
    rw [Functor.map_comp, pointsMap_comp, Function.comp_apply, ← fieldMorphism_yoneda,
      pointsMap_fieldMorphism_tautologicalPoint, class_schemePointRepresentative_pointsToScheme,
      hc]
  obtain ⟨r, hr, hra⟩ := key a ha
  obtain ⟨r', hr', hrb⟩ := key b hb
  have hsub := subsingleton_points_yoneda_siteObject B S hS p
  have hfinfp : Finite (points B S hS (pullback fp fp)) :=
    finite_points_of_etaleQuasiCompactPresheaf B S hS _ hfst Finite.of_subsingleton
  have hcomm {V : BigFppfOver B S hS} (t : V ⟶ P) :
      yoneda.map (t ≫ z) ≫ f = yoneda.map (t ≫ w) ≫ fp := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, sq.w]
  have hfinpb : Finite (points B S hS
      (pullback (yoneda.map (r.siteHom ≫ z) ≫ f) (yoneda.map (r'.siteHom ≫ z) ≫ f))) :=
    finite_points_pullback_congr B S hS _ _ _ _ (hcomm r.siteHom).symm (hcomm r'.siteHom).symm
      (finite_points_pullback_comp B S hS _ _ fp fp hr hr' hfinfp)
  have hfin := finite_relationFiber_of_finite_points_pullback_comp B S hS
    (yoneda.map (r.siteHom ≫ z)) (yoneda.map (r'.siteHom ≫ z)) f f
    ((r.tautologicalPoint B S hS (yoneda.obj P)).class B S hS (yoneda.obj r.siteObject))
    ((r'.tautologicalPoint B S hS (yoneda.obj P)).class B S hS (yoneda.obj r'.siteObject))
    hfinpb
  show {y : points B S hS (pullback f f) |
    pointsMap B S hS _ (pullback.fst f f) y = a ∧
    pointsMap B S hS _ (pullback.snd f f) y = b}.Finite
  simpa only [hra, hrb] using hfin

/-- Every point of an algebraic space over `S` lies in the image of some étale chart of it,
by Stacks 03H5 applied to an étale atlas. -/
theorem exists_etale_chart_point_of_point (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) :
    ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F) (a : points B S hS (yoneda.obj U)),
      IsEtale B S hS f ∧ pointsMap B S hS (yoneda.obj U) f a = x := by
  obtain ⟨U, f, hsurj, hetale⟩ := hF.exists_atlas
  obtain ⟨a, ha⟩ := (surjective_iff_surjective_pointsMap B S hS F hF U f).1 hsurj x
  exact ⟨U, f, a, isEtale_of_presheaf_etale B S hS hetale, ha⟩

/-- **Stacks 03JU, (1) implies (2).** If some étale chart of an algebraic space has two points
above `x` with finite relation fibre, then every pair of points above `x` in every étale chart
has finite relation fibre. -/
theorem hasFiniteRelationFiberAtEveryEtaleChart_of_hasFiniteRelationFiberAt
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (h : HasFiniteRelationFiberAt B S hS F x) :
    HasFiniteRelationFiberAtEveryEtaleChart B S hS F x :=
  hasFiniteRelationFiberAtEveryEtaleChart_of_hasEtaleQuasiCompactFieldRepresentative
    B S hS F hF x
    (hasEtaleQuasiCompactFieldRepresentative_of_hasFiniteRelationFiberAt B S hS F hF x h)

/-- **Stacks 03JU, conditions (1) and (2).** For a point of an algebraic space over `S`,
finiteness of one relation fibre in one étale chart is equivalent to finiteness of every
relation fibre in every étale chart. -/
@[stacks 03JU "conditions (1) and (2)"]
theorem hasFiniteRelationFiberAt_iff_everyEtaleChart (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) :
    HasFiniteRelationFiberAt B S hS F x ↔
      HasFiniteRelationFiberAtEveryEtaleChart B S hS F x := by
  refine ⟨hasFiniteRelationFiberAtEveryEtaleChart_of_hasFiniteRelationFiberAt B S hS F hF x,
    fun h ↦ ?_⟩
  obtain ⟨U, f, a, hetale, hax⟩ := exists_etale_chart_point_of_point B S hS F hF x
  exact hasFiniteRelationFiberAt_of_everyEtaleChart B S hS F h U f hetale a hax

/-- **Stacks 03JU, conditions (2) and (3).** For a point of an algebraic space over `S`,
finiteness of every relation fibre in every étale chart is equivalent to having a field-valued
representative with étale quasi-compact self-intersection projections. -/
@[stacks 03JU "conditions (2) and (3)"]
theorem hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    HasFiniteRelationFiberAtEveryEtaleChart B S hS F x ↔
      HasEtaleQuasiCompactFieldRepresentative B S hS F x := by
  refine ⟨fun h ↦ ?_,
    hasFiniteRelationFiberAtEveryEtaleChart_of_hasEtaleQuasiCompactFieldRepresentative
      B S hS F hF x⟩
  obtain ⟨U, f, a, hetale, hax⟩ := exists_etale_chart_point_of_point B S hS F hF x
  exact hasEtaleQuasiCompactFieldRepresentative_of_hasFiniteRelationFiberAt B S hS F hF x
    (hasFiniteRelationFiberAt_of_everyEtaleChart B S hS F h U f hetale a hax)

/-- **Stacks 03JU, (4) implies (3).** A monomorphic field-valued representative has étale and
quasi-compact self-intersection projections: both of them are isomorphisms. -/
theorem hasEtaleQuasiCompactFieldRepresentative_of_hasMonomorphicFieldRepresentative
    (x : points B S hS F) (h : HasMonomorphicFieldRepresentative B S hS F x) :
    HasEtaleQuasiCompactFieldRepresentative B S hS F x := by
  obtain ⟨p, hp, hmono⟩ := h
  have hiso : ∀ {G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : G ⟶ H), IsIso g →
      etaleQuasiCompactPresheaf B S hS g := by
    intro G H g _
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda g, fun _ _ _ fst snd hpb ↦ ?_⟩
    have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
    have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map _
    exact ⟨inferInstance, inferInstance⟩
  have := hmono
  exact ⟨p, hp, hiso _ inferInstance, hiso _ inferInstance⟩

/-- **Stacks 03JU, (4) implies (2).** If a point of an algebraic space over `S` has a
monomorphic field-valued representative, then every pair of points above it in every étale
chart has finite relation fibre. -/
theorem hasFiniteRelationFiberAtEveryEtaleChart_of_hasMonomorphicFieldRepresentative
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (h : HasMonomorphicFieldRepresentative B S hS F x) :
    HasFiniteRelationFiberAtEveryEtaleChart B S hS F x :=
  hasFiniteRelationFiberAtEveryEtaleChart_of_hasEtaleQuasiCompactFieldRepresentative
    B S hS F hF x
    (hasEtaleQuasiCompactFieldRepresentative_of_hasMonomorphicFieldRepresentative
      B S hS F x h)

end AlgebraicGeometry.Space

end
