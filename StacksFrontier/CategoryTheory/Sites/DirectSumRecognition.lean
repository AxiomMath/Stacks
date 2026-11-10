module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact

/-!
# Recognising a direct sum of sheaves of abelian groups

Let `D : Discrete ι ⥤ Sheaf J AddCommGrpCat` be a family of sheaves of abelian groups on a site
and let `e` be a cocone on it. Suppose that every coprojection `e.ι.app ⟨k⟩` admits a retraction
`p k`, that distinct coprojections are orthogonal to these retractions, and that every section of
the vertex is, locally on a covering sieve, the finite sum of the images under the coprojections of
its own components. Then `e` is a colimit cocone, i.e. the vertex *is* the direct sum of the
family.

## Main results

* `Stacks.Sites.DirectSumRecognition.isColimit_of_retractions_of_locally_finite_sum`: the
  recognition criterion itself.

## Implementation notes

`StacksFrontier.CategoryTheory.Sites.QuasiCompact.AbelianSections` proves the same mathematics as
`exists_finset_sum_eq_of_isQuasiCompactObject` below, as
`Stacks.Sites.preservesColimitsOfShape_discrete_sheafSections_of_isQuasiCompactObject`; it states
it as preservation of colimits by the sections functor and keeps every helper private, whereas
the support argument consuming it here needs the elementwise form, one section at a time. The
two should be deduplicated, with the elementwise form derived from the categorical one.

The sections which are *globally* a finite sum of the images of their own components form a
subpresheaf `A` of the vertex; the local hypothesis says precisely that the sheafification of `A`
inside the vertex is everything. Given a competing cocone `q`, the value of the induced morphism
on a section `x` of `A` is the (finite) sum of the images under the legs of `q` of the components
of `x`, written as a `finsum` so that no choice of a witnessing finite index set has to be made;
sheafifying this morphism and using that the underlying presheaf of sets of `q.pt` is separated
gives the morphism `e.pt ⟶ q.pt` and its uniqueness.

No existence hypothesis on coproducts or on sheafification is needed, and the four universes
involved are independent: the subpresheaf is built inside the vertex rather than by sheafifying a
presheaf, and the sheaf condition for the underlying presheaf of sets is transferred along
`CategoryTheory.GrothendieckTopology.HasSheafCompose.isSheaf`, whose instance for a forgetful
functor only needs that functor to be corepresentable.

The coprojections of the cocone are named `leg` rather than used as `e.ι.app ⟨k⟩` throughout, so
that their target is the vertex itself and not the value at `⟨k⟩` of the constant functor at it:
the latter mentions the summation index, which stops the element type of a finite sum of sections
from being inferred.
-/

@[expose] public section

universe w v t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.DirectSumRecognition

attribute [local instance] Classical.propDecidable

variable {C : Type u} [Category.{t} C] {J : GrothendieckTopology C} {ι : Type w}

/-! ### Generalities on sheaves of abelian groups -/

/-- The underlying presheaf of sets of a sheaf of abelian groups is a sheaf of sets. -/
public lemma underlying_isSheaf (F : Sheaf J AddCommGrpCat.{v}) :
    Presieve.IsSheaf J (F.obj ⋙ forget AddCommGrpCat.{v}) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf _ F.property

/-- Two sections of a sheaf of abelian groups which agree after restriction along every arrow of
a covering sieve are equal. -/
public lemma hom_ext_of_sieve (F : Sheaf J AddCommGrpCat.{v}) {W : C} {R : Sieve W}
    (hR : R ∈ J W) {x y : F.obj.obj (op W)}
    (hxy : ∀ ⦃V : C⦄ (a : V ⟶ W), R a → F.obj.map a.op x = F.obj.map a.op y) : x = y :=
  ((underlying_isSheaf F).isSeparated R hR).ext fun _ a ha => hxy a ha

/-- The coprojection of a cocone at `k`, with the vertex itself as target. -/
public def leg (F : Discrete ι ⥤ Sheaf J AddCommGrpCat.{v}) (c : Cocone F) (k : ι) :
    F.obj ⟨k⟩ ⟶ c.pt :=
  c.ι.app ⟨k⟩

/-- A coprojection commutes with restriction. -/
public lemma leg_naturality (F : Discrete ι ⥤ Sheaf J AddCommGrpCat.{v}) (c : Cocone F) (k : ι)
    {X Y : Cᵒᵖ} (g : X ⟶ Y) (y : (F.obj ⟨k⟩).obj.obj X) :
    (leg F c k).hom.app Y ((F.obj ⟨k⟩).obj.map g y)
      = c.pt.obj.map g ((leg F c k).hom.app X y) :=
  NatTrans.naturality_apply (leg F c k).hom g y

/-- Restriction of a finite sum of images of sections of the summands. -/
public lemma map_sum_leg (F : Discrete ι ⥤ Sheaf J AddCommGrpCat.{v}) (c : Cocone F)
    {X Y : Cᵒᵖ} (g : X ⟶ Y) (S : Finset ι) (υ : ∀ k : ι, (F.obj ⟨k⟩).obj.obj X) :
    c.pt.obj.map g (∑ k ∈ S, (leg F c k).hom.app X (υ k))
      = ∑ k ∈ S, (leg F c k).hom.app Y ((F.obj ⟨k⟩).obj.map g (υ k)) := by
  rw [map_sum (c.pt.obj.map g).hom]
  exact Finset.sum_congr rfl fun k _ => (leg_naturality F c k g (υ k)).symm

variable {D : Discrete ι ⥤ Sheaf J AddCommGrpCat.{v}}

/-- Sectionwise form of an identity between composites of morphisms of sheaves. -/
private lemma hom_app_comp_eq {A B E : Sheaf J AddCommGrpCat.{v}} {f : A ⟶ B} {g : B ⟶ E}
    {k : A ⟶ E} (h : f ≫ g = k) (X : Cᵒᵖ) (y : A.obj.obj X) :
    g.hom.app X (f.hom.app X y) = k.hom.app X y :=
  congrArg (fun f : A ⟶ E => f.hom.app X y) h

/-- Retractions orthogonal to the other coprojections read off a component of a finite sum. -/
private lemma sum_comp_of_mem {c : Cocone D} {p : ∀ k : ι, c.pt ⟶ D.obj ⟨k⟩}
    (hself : ∀ k : ι, leg D c k ≫ p k = 𝟙 (D.obj ⟨k⟩))
    (hne : ∀ k j : ι, k ≠ j → leg D c k ≫ p j = 0) (X : Cᵒᵖ) (T : Finset ι)
    (υ : ∀ k : ι, (D.obj ⟨k⟩).obj.obj X) {j : ι} (hj : j ∈ T) :
    (p j).hom.app X (∑ k ∈ T, (leg D c k).hom.app X (υ k)) = υ j := by
  rw [map_sum ((p j).hom.app X).hom, Finset.sum_eq_single_of_mem j hj fun k _ hkj => by
    simpa using hom_app_comp_eq (hne k j hkj) X (υ k)]
  simpa using hom_app_comp_eq (hself j) X (υ j)

/-- Retractions orthogonal to the other coprojections vanish on a sum over a set missing `j`. -/
private lemma sum_comp_of_notMem {c : Cocone D} {p : ∀ k : ι, c.pt ⟶ D.obj ⟨k⟩}
    (hne : ∀ k j : ι, k ≠ j → leg D c k ≫ p j = 0) (X : Cᵒᵖ) (T : Finset ι)
    (υ : ∀ k : ι, (D.obj ⟨k⟩).obj.obj X) {j : ι} (hj : j ∉ T) :
    (p j).hom.app X (∑ k ∈ T, (leg D c k).hom.app X (υ k)) = 0 := by
  rw [map_sum ((p j).hom.app X).hom]
  exact Finset.sum_eq_zero fun k hk => by
    simpa using hom_app_comp_eq (hne k j (ne_of_mem_of_not_mem hk hj)) X (υ k)

/-- The hypotheses of the recognition criterion, bundled: a family of retractions of the
coprojections of a cocone `e` on a discrete diagram of sheaves of abelian groups, orthogonal to
the other coprojections, such that every section of the vertex is locally a finite sum of the
coprojections. -/
private structure Setup (e : Cocone D) where
  /-- The retraction of the coprojection at `k`. -/
  p : ∀ k : ι, e.pt ⟶ D.obj ⟨k⟩
  /-- Each coprojection is split by its own retraction. -/
  hself : ∀ k : ι, e.ι.app ⟨k⟩ ≫ p k = 𝟙 (D.obj ⟨k⟩)
  /-- Distinct coprojections and retractions are orthogonal. -/
  hne : ∀ k j : ι, k ≠ j → e.ι.app ⟨k⟩ ≫ p j = 0
  /-- Every section of the vertex is locally a finite sum of the coprojections. -/
  hloc : ∀ (V : C) (x : e.pt.obj.obj (op V)), ∃ R ∈ J V,
    ∀ ⦃V' : C⦄ (a : V' ⟶ V), R a → ∃ T : Finset ι,
      e.pt.obj.map a.op x = ∑ k ∈ T, (e.ι.app ⟨k⟩).hom.app (op V')
        ((p k).hom.app (op V') (e.pt.obj.map a.op x))

variable {e : Cocone D}

/-! ### Reading off the components of a finite sum -/

/-- Sectionwise form of the retraction identity. -/
private lemma proj_leg_self (h : Setup e) (k : ι) (X : Cᵒᵖ) (y : (D.obj ⟨k⟩).obj.obj X) :
    (h.p k).hom.app X ((leg D e k).hom.app X y) = y := by
  simpa using hom_app_comp_eq (f := leg D e k) (h.hself k) X y

/-! ### The subpresheaf of global finite sums -/

/-- Restriction of a section which is a finite sum of the images of its own components is again
one, with the same index set. -/
private lemma map_witness (h : Setup e) {X Y : Cᵒᵖ} (g : X ⟶ Y) {x : e.pt.obj.obj X}
    {T : Finset ι} (hx : x = ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X x)) :
    e.pt.obj.map g x
      = ∑ k ∈ T, (leg D e k).hom.app Y ((h.p k).hom.app Y (e.pt.obj.map g x)) := by
  calc e.pt.obj.map g x
      = e.pt.obj.map g (∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X x)) := by rw [← hx]
    _ = ∑ k ∈ T, (leg D e k).hom.app Y ((D.obj ⟨k⟩).obj.map g ((h.p k).hom.app X x)) :=
        map_sum_leg D e g T _
    _ = ∑ k ∈ T, (leg D e k).hom.app Y ((h.p k).hom.app Y (e.pt.obj.map g x)) :=
        Finset.sum_congr rfl fun k _ => by rw [NatTrans.naturality_apply (h.p k).hom g x]

/-- The subpresheaf of sections which are the finite sum, over some finite set of indices, of the
images under the coprojections of their own components. -/
private def sumSubfunctor (h : Setup e) : Subfunctor (e.pt.obj ⋙ forget AddCommGrpCat.{v}) where
  obj X := {x | ∃ T : Finset ι, x = ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X x)}
  map {X Y} g := by
    rintro x ⟨T, hT⟩
    exact ⟨T, map_witness h g hT⟩

/-- A retraction outside a witnessing index set kills the section. -/
private lemma proj_eq_zero_of_notMem (h : Setup e) {X : Cᵒᵖ} {x : e.pt.obj.obj X} {T : Finset ι}
    (hx : x = ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X x)) {j : ι} (hj : j ∉ T) :
    (h.p j).hom.app X x = 0 := by
  rw [hx]
  exact sum_comp_of_notMem h.hne X T _ hj

/-- A witnessing index set may be enlarged. -/
private lemma sum_over_superset (h : Setup e) {X : Cᵒᵖ} {x : e.pt.obj.obj X} {T T' : Finset ι}
    (hTT : T ⊆ T') (hx : x = ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X x)) :
    x = ∑ k ∈ T', (leg D e k).hom.app X ((h.p k).hom.app X x) := by
  refine hx.trans (Finset.sum_subset hTT fun k _ hk => ?_)
  rw [proj_eq_zero_of_notMem h hx hk]
  exact map_zero _

/-- Two sections witnessed by the same index set have their sum witnessed by it too. -/
private lemma add_witness (h : Setup e) {X : Cᵒᵖ} {x y : e.pt.obj.obj X} {T : Finset ι}
    (hx : x = ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X x))
    (hy : y = ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X y)) :
    x + y = ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X (x + y)) := by
  have hsplit : ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X (x + y))
      = (∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X x))
        + ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X y) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [map_add]
  rw [hsplit, ← hx, ← hy]

/-- The subpresheaf of global finite sums is stable under addition. -/
private lemma add_mem_sumSubfunctor (h : Setup e) {X : Cᵒᵖ} {x y : e.pt.obj.obj X}
    (hx : x ∈ (sumSubfunctor h).obj X) (hy : y ∈ (sumSubfunctor h).obj X) :
    x + y ∈ (sumSubfunctor h).obj X := by
  obtain ⟨T, hT⟩ := hx
  obtain ⟨T', hT'⟩ := hy
  exact ⟨T ∪ T', add_witness h (sum_over_superset h (Finset.subset_union_left : T ⊆ T ∪ T') hT)
    (sum_over_superset h (Finset.subset_union_right : T' ⊆ T ∪ T') hT')⟩

/-- The image of a section of a summand is a global finite sum. -/
private lemma leg_mem_sumSubfunctor (h : Setup e) (j : ι) (X : Cᵒᵖ)
    (y : (D.obj ⟨j⟩).obj.obj X) :
    (leg D e j).hom.app X y ∈ (sumSubfunctor h).obj X :=
  ⟨{j}, by rw [Finset.sum_singleton, proj_leg_self h j X y]⟩

/-- The local hypothesis says precisely that the sieve on which a section is a global finite sum
is a covering sieve. -/
private lemma sieveOfSection_mem (h : Setup e) (X : Cᵒᵖ) (x : e.pt.obj.obj X) :
    (sumSubfunctor h).sieveOfSection x ∈ J X.unop := by
  obtain ⟨R, hR, hRx⟩ := h.hloc X.unop x
  exact J.superset_covering (fun _ a ha => hRx a ha) hR

/-- Every section of the vertex lies in the sheafification of the subpresheaf of global finite
sums: that subpresheaf is dense. -/
private lemma mem_sheafify (h : Setup e) (X : Cᵒᵖ) (x : e.pt.obj.obj X) :
    x ∈ ((sumSubfunctor h).sheafify J).obj X :=
  sieveOfSection_mem h X x

/-! ### The value of the induced morphism -/

/-- The candidate value at a section of the vertex of the morphism induced into the vertex of a
competing cocone `q`. -/
private noncomputable def val (h : Setup e) (q : Cocone D) (X : Cᵒᵖ) (x : e.pt.obj.obj X) :
    q.pt.obj.obj X :=
  ∑ᶠ k : ι, (leg D q k).hom.app X ((h.p k).hom.app X x)

private lemma val_def (h : Setup e) (q : Cocone D) (X : Cᵒᵖ) (x : e.pt.obj.obj X) :
    val h q X x = ∑ᶠ k : ι, (leg D q k).hom.app X ((h.p k).hom.app X x) := rfl

/-- On a section witnessed by `T`, the candidate value is the finite sum over `T`. -/
private lemma val_eq_sum (h : Setup e) (q : Cocone D) {X : Cᵒᵖ} {x : e.pt.obj.obj X}
    {T : Finset ι} (hx : x = ∑ k ∈ T, (leg D e k).hom.app X ((h.p k).hom.app X x)) :
    val h q X x = ∑ k ∈ T, (leg D q k).hom.app X ((h.p k).hom.app X x) := by
  rw [val_def]
  refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
  by_contra hkT
  refine hk ?_
  change (leg D q k).hom.app X ((h.p k).hom.app X x) = 0
  rw [proj_eq_zero_of_notMem h hx (Finset.mem_coe.not.mp hkT), map_zero]

/-- The candidate value is additive on the subpresheaf of global finite sums. -/
private lemma val_add (h : Setup e) (q : Cocone D) {X : Cᵒᵖ} {x y : e.pt.obj.obj X}
    (hx : x ∈ (sumSubfunctor h).obj X) (hy : y ∈ (sumSubfunctor h).obj X) :
    val h q X (x + y) = val h q X x + val h q X y := by
  obtain ⟨T, hT⟩ := hx
  obtain ⟨T', hT'⟩ := hy
  have hx' := sum_over_superset h (Finset.subset_union_left : T ⊆ T ∪ T') hT
  have hy' := sum_over_superset h (Finset.subset_union_right : T' ⊆ T ∪ T') hT'
  rw [val_eq_sum h q (add_witness h hx' hy'), val_eq_sum h q hx', val_eq_sum h q hy',
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by simp only [map_add]

/-- The candidate value is natural on the subpresheaf of global finite sums. -/
private lemma val_map (h : Setup e) (q : Cocone D) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    {x : e.pt.obj.obj X} (hx : x ∈ (sumSubfunctor h).obj X) :
    val h q Y (e.pt.obj.map g x) = q.pt.obj.map g (val h q X x) := by
  obtain ⟨T, hT⟩ := hx
  rw [val_eq_sum h q (map_witness h g hT), val_eq_sum h q hT,
    map_sum_leg D q g T fun k => (h.p k).hom.app X x]
  exact Finset.sum_congr rfl fun k _ => by rw [NatTrans.naturality_apply (h.p k).hom g x]

/-- The candidate value sends the image of a section of a summand to its image under the
corresponding coprojection of `q`. -/
private lemma val_leg (h : Setup e) (q : Cocone D) (j : ι) (X : Cᵒᵖ)
    (y : (D.obj ⟨j⟩).obj.obj X) :
    val h q X ((leg D e j).hom.app X y) = (leg D q j).hom.app X y := by
  have hw : (leg D e j).hom.app X y = ∑ k ∈ ({j} : Finset ι),
      (leg D e k).hom.app X ((h.p k).hom.app X ((leg D e j).hom.app X y)) := by
    rw [Finset.sum_singleton, proj_leg_self h j X y]
  rw [val_eq_sum h q hw, Finset.sum_singleton, proj_leg_self h j X y]

/-- The candidate value, as a morphism of presheaves of types out of the subpresheaf of global
finite sums. -/
private noncomputable def toVal (h : Setup e) (q : Cocone D) :
    (sumSubfunctor h).toFunctor ⟶ q.pt.obj ⋙ forget AddCommGrpCat.{v} where
  app X := ↾fun s => val h q X s.1
  naturality {X Y} g := by
    ext s
    exact val_map h q g s.2

/-! ### The induced morphism -/

/-- The descent of `toVal` along the sheafification of the subpresheaf of global finite sums. -/
private noncomputable def liftVal (h : Setup e) (q : Cocone D) :
    ((sumSubfunctor h).sheafify J).toFunctor ⟶ q.pt.obj ⋙ forget AddCommGrpCat.{v} :=
  (sumSubfunctor h).sheafifyLift (toVal h q) (underlying_isSheaf q.pt)

/-- The value of the induced morphism at a section of the vertex. -/
private noncomputable def descFun (h : Setup e) (q : Cocone D) (X : Cᵒᵖ)
    (x : e.pt.obj.obj X) : q.pt.obj.obj X :=
  (liftVal h q).app X ⟨x, mem_sheafify h X x⟩

/-- On the subpresheaf of global finite sums the induced morphism is the candidate value. -/
private lemma descFun_of_mem (h : Setup e) (q : Cocone D) {X : Cᵒᵖ} {x : e.pt.obj.obj X}
    (hx : x ∈ (sumSubfunctor h).obj X) :
    descFun h q X x = val h q X x :=
  ConcreteCategory.congr_hom
    (congr_app ((sumSubfunctor h).to_sheafifyLift (toVal h q) (underlying_isSheaf q.pt)) X)
    ⟨x, hx⟩

/-- The induced morphism commutes with restriction. -/
private lemma descFun_map (h : Setup e) (q : Cocone D) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (x : e.pt.obj.obj X) :
    descFun h q Y (e.pt.obj.map g x) = q.pt.obj.map g (descFun h q X x) :=
  NatTrans.naturality_apply (liftVal h q) g
    (⟨x, mem_sheafify h X x⟩ : ((sumSubfunctor h).sheafify J).toFunctor.obj X)

/-- The induced morphism is additive. -/
private lemma descFun_add (h : Setup e) (q : Cocone D) (X : Cᵒᵖ) (x y : e.pt.obj.obj X) :
    descFun h q X (x + y) = descFun h q X x + descFun h q X y := by
  refine hom_ext_of_sieve q.pt (J.intersection_covering (sieveOfSection_mem h X x)
    (sieveOfSection_mem h X y)) fun V a ha => ?_
  have hax : e.pt.obj.map a.op x ∈ (sumSubfunctor h).obj (op V) := ha.1
  have hay : e.pt.obj.map a.op y ∈ (sumSubfunctor h).obj (op V) := ha.2
  calc q.pt.obj.map a.op (descFun h q X (x + y))
      = descFun h q (op V) (e.pt.obj.map a.op (x + y)) := (descFun_map h q a.op (x + y)).symm
    _ = descFun h q (op V) (e.pt.obj.map a.op x + e.pt.obj.map a.op y) := by
        rw [map_add (e.pt.obj.map a.op).hom]
    _ = val h q (op V) (e.pt.obj.map a.op x + e.pt.obj.map a.op y) :=
        descFun_of_mem h q (add_mem_sumSubfunctor h hax hay)
    _ = val h q (op V) (e.pt.obj.map a.op x) + val h q (op V) (e.pt.obj.map a.op y) :=
        val_add h q hax hay
    _ = descFun h q (op V) (e.pt.obj.map a.op x)
          + descFun h q (op V) (e.pt.obj.map a.op y) := by
        rw [descFun_of_mem h q hax, descFun_of_mem h q hay]
    _ = q.pt.obj.map a.op (descFun h q X x) + q.pt.obj.map a.op (descFun h q X y) := by
        rw [descFun_map h q a.op x, descFun_map h q a.op y]
    _ = q.pt.obj.map a.op (descFun h q X x + descFun h q X y) :=
        (map_add (q.pt.obj.map a.op).hom _ _).symm

/-- The morphism of sheaves of abelian groups induced on the vertex of a competing cocone. -/
private noncomputable def desc (h : Setup e) (q : Cocone D) : e.pt ⟶ q.pt :=
  ⟨{ app X := AddCommGrpCat.ofHom (AddMonoidHom.mk' (descFun h q X) (descFun_add h q X))
     naturality {X Y} g := by
       ext x
       exact descFun_map h q g x }⟩

/-- The induced morphism factors the coprojections of the competing cocone. -/
private lemma leg_comp_desc (h : Setup e) (q : Cocone D) (j : ι) :
    e.ι.app ⟨j⟩ ≫ desc h q = q.ι.app ⟨j⟩ := by
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  ext X y
  exact (descFun_of_mem h q (leg_mem_sumSubfunctor h j X y)).trans (val_leg h q j X y)

/-- The induced morphism is the only one factoring the coprojections of the competing cocone. -/
private lemma desc_uniq (h : Setup e) (q : Cocone D) (m : e.pt ⟶ q.pt)
    (hm : ∀ j : ι, e.ι.app ⟨j⟩ ≫ m = q.ι.app ⟨j⟩) : m = desc h q := by
  have hml : ∀ (k : ι) (Y : Cᵒᵖ) (y : (D.obj ⟨k⟩).obj.obj Y),
      m.hom.app Y ((leg D e k).hom.app Y y) = (leg D q k).hom.app Y y := fun k Y y =>
    hom_app_comp_eq (hm k) Y y
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  ext X x
  change m.hom.app X x = descFun h q X x
  refine hom_ext_of_sieve q.pt (sieveOfSection_mem h X x) fun V a ha => ?_
  obtain ⟨T, hT⟩ := ha
  have hT' : e.pt.obj.map a.op x = ∑ k ∈ T, (leg D e k).hom.app (op V)
      ((h.p k).hom.app (op V) (e.pt.obj.map a.op x)) := hT
  calc q.pt.obj.map a.op (m.hom.app X x)
      = m.hom.app (op V) (e.pt.obj.map a.op x) :=
        (NatTrans.naturality_apply m.hom a.op x).symm
    _ = m.hom.app (op V) (∑ k ∈ T, (leg D e k).hom.app (op V)
          ((h.p k).hom.app (op V) (e.pt.obj.map a.op x))) := by rw [← hT']
    _ = ∑ k ∈ T, (leg D q k).hom.app (op V)
          ((h.p k).hom.app (op V) (e.pt.obj.map a.op x)) := by
        rw [map_sum (m.hom.app (op V)).hom]
        exact Finset.sum_congr rfl fun k _ => hml k (op V) _
    _ = val h q (op V) (e.pt.obj.map a.op x) := (val_eq_sum h q hT').symm
    _ = descFun h q (op V) (e.pt.obj.map a.op x) := (descFun_of_mem h q ⟨T, hT'⟩).symm
    _ = q.pt.obj.map a.op (descFun h q X x) := descFun_map h q a.op x

/-- The cocone of the setup is a colimit cocone. -/
private noncomputable def isColimitOfSetup (h : Setup e) : IsColimit e where
  desc q := desc h q
  fac q j := leg_comp_desc h q j.as
  uniq q m hm := desc_uniq h q m fun j => hm ⟨j⟩

/-! ### The recognition criterion -/

/-- **A recognition criterion for a direct sum of sheaves of abelian groups.** A cocone over a
discrete diagram of sheaves of abelian groups whose coprojections admit retractions `p`,
orthogonal to the other coprojections, and whose vertex is locally a finite sum of the
coprojections, is a colimit cocone. -/
theorem isColimit_of_retractions_of_locally_finite_sum
    {C : Type u} [Category.{t} C] {J : GrothendieckTopology C}
    {ι : Type w} {D : Discrete ι ⥤ Sheaf J AddCommGrpCat.{v}} (e : Cocone D)
    (p : ∀ k : ι, e.pt ⟶ D.obj ⟨k⟩)
    (hself : ∀ k : ι, e.ι.app ⟨k⟩ ≫ p k = 𝟙 (D.obj ⟨k⟩))
    (hne : ∀ k j : ι, k ≠ j → e.ι.app ⟨k⟩ ≫ p j = 0)
    (hloc : ∀ (V : C) (x : e.pt.obj.obj (op V)), ∃ R ∈ J V,
      ∀ ⦃V' : C⦄ (a : V' ⟶ V), R a → ∃ T : Finset ι,
        e.pt.obj.map a.op x = ∑ k ∈ T, (e.ι.app ⟨k⟩).hom.app (op V')
          ((p k).hom.app (op V') (e.pt.obj.map a.op x))) :
    Nonempty (IsColimit e) :=
  ⟨isColimitOfSetup ⟨p, hself, hne, hloc⟩⟩

/-! ### The projections of a direct sum, and finite sums over a quasi-compact object -/

section Projections

variable {C : Type u} [Category.{t} C] {J : GrothendieckTopology C} {ι : Type w}
  (D : Discrete ι ⥤ Sheaf J AddCommGrpCat.{v}) (c : Cocone D)

/-- The cocone on a discrete diagram whose leg at `⟨j⟩` is the identity and whose other legs
are zero. -/
public noncomputable def projectionCocone (j : ι) : Cocone D where
  pt := D.obj ⟨j⟩
  ι := Discrete.natTrans fun k => if h : k.as = j then D.map (Discrete.eqToHom h) else 0

/-- The canonical projection of a direct sum onto the summand indexed by `j`. -/
public noncomputable def projection (hc : IsColimit c) (j : ι) : c.pt ⟶ D.obj ⟨j⟩ :=
  hc.desc (projectionCocone D j)

/-- The composite of a coprojection with a projection, computed on the projection cocone. -/
private lemma leg_comp_projection (hc : IsColimit c) (k j : ι) :
    leg D c k ≫ projection D c hc j =
      if h : k = j then D.map (Discrete.eqToHom h) else 0 :=
  hc.fac (projectionCocone D j) (Discrete.mk k)

/-- The projection undoes the coprojection at the same index. -/
public lemma leg_comp_projection_self (hc : IsColimit c) (j : ι) :
    leg D c j ≫ projection D c hc j = 𝟙 (D.obj ⟨j⟩) := by
  simp [leg_comp_projection]

/-- The projection kills the coprojection at a different index. -/
public lemma leg_comp_projection_ne (hc : IsColimit c) {k j : ι} (hkj : k ≠ j) :
    leg D c k ≫ projection D c hc j = 0 := by
  simp [leg_comp_projection, hkj]

/-- Sectionwise form of `leg_comp_projection_self`. -/
public lemma projection_leg_self (hc : IsColimit c) (j : ι) (X : Cᵒᵖ)
    (y : (D.obj ⟨j⟩).obj.obj X) :
    (projection D c hc j).hom.app X ((leg D c j).hom.app X y) = y := by
  simpa using hom_app_comp_eq (leg_comp_projection_self D c hc j) X y

/-- Sectionwise form of `leg_comp_projection_ne`. -/
public lemma projection_leg_ne (hc : IsColimit c) {k j : ι} (hkj : k ≠ j) (X : Cᵒᵖ)
    (y : (D.obj ⟨k⟩).obj.obj X) :
    (projection D c hc j).hom.app X ((leg D c k).hom.app X y) = 0 := by
  simpa using hom_app_comp_eq (leg_comp_projection_ne D c hc hkj) X y

/-- A projection reads off the corresponding component of a finite subsum. -/
public lemma projection_sum_of_mem (hc : IsColimit c) (X : Cᵒᵖ) (S : Finset ι)
    (υ : ∀ j : ι, (D.obj ⟨j⟩).obj.obj X) {k : ι} (hk : k ∈ S) :
    (projection D c hc k).hom.app X (∑ j ∈ S, (leg D c j).hom.app X (υ j)) = υ k :=
  sum_comp_of_mem (leg_comp_projection_self D c hc) (fun _ _ => leg_comp_projection_ne D c hc)
    X S υ hk

/-- A section of the direct sum which is, locally on a covering sieve, a sum over one fixed
finite index set is globally that sum, with its coefficients read off by the projections. -/
public lemma eq_sum_projection_of_locally (hc : IsColimit c) {U : C}
    (s : c.pt.obj.obj (op U)) (S : Finset ι) {R : Sieve U} (hR : R ∈ J U)
    (h : ∀ ⦃V : C⦄ (a : V ⟶ U), R a → ∃ υ : ∀ j : ι, (D.obj ⟨j⟩).obj.obj (op V),
      c.pt.obj.map a.op s = ∑ j ∈ S, (leg D c j).hom.app (op V) (υ j)) :
    s = ∑ j ∈ S, (leg D c j).hom.app (op U) ((projection D c hc j).hom.app (op U) s) := by
  refine hom_ext_of_sieve c.pt hR fun V a ha => ?_
  obtain ⟨υ, hυ⟩ := h a ha
  rw [map_sum_leg D c a.op S fun j => (projection D c hc j).hom.app (op U) s, hυ]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  rw [← NatTrans.naturality_apply (projection D c hc j).hom a.op s, hυ,
    projection_sum_of_mem D c hc (op V) S υ hj]

end Projections

/-! ### Sections over a quasi-compact object -/

section QcGeneralities

variable {C : Type u} [Category.{t} C] {J : GrothendieckTopology C}

/-- Two sections of a sheaf of abelian groups which agree after restriction along every member of
a covering family of morphisms with fixed target are equal. -/
public lemma hom_ext_of_cover (F : Sheaf J AddCommGrpCat.{v}) {W : C}
    (𝒱 : PreZeroHypercover.{max u t} W) (h𝒱 : 𝒱.sieve₀ ∈ J W) {x y : F.obj.obj (op W)}
    (h : ∀ b, F.obj.map (𝒱.f b).op x = F.obj.map (𝒱.f b).op y) : x = y :=
  𝒱.ext_of_isSeparatedFor
    (Presieve.isSeparatedFor_iff_generate.2 ((underlying_isSheaf F).isSeparated _ h𝒱)) h

/-- Sieve form of **Stacks 090H**: a covering sieve `R` of a quasi-compact object `W` contains a
family `𝒲` of morphisms to `W`, indexed by a finite type, which is refined by a covering family
`𝒱` of `W`. -/
private lemma exists_cover_factoring {W : C} (hW : J.IsQuasiCompactObject W) {R : Sieve W}
    (hR : R ∈ J W) :
    ∃ (𝒲 : PreZeroHypercover.{max u t} W) (_ : Finite 𝒲.I₀) (_ : ∀ b, R (𝒲.f b))
      (𝒱 : PreZeroHypercover.{max u t} W) (_ : 𝒱.Hom 𝒲), 𝒱.sieve₀ ∈ J W := by
  obtain ⟨𝒱, φ, h𝒱, hfin⟩ := hW R.arrows.preZeroHypercover (by
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← PreZeroHypercover.presieve₀,
      Presieve.presieve₀_preZeroHypercover, Sieve.generate_sieve]
    exact hR)
  exact ⟨R.arrows.preZeroHypercover.restrictIndex (fun r : Set.range φ.s₀ => r.1),
    hfin.to_subtype, fun r => r.1.2, 𝒱,
    { s₀ := fun b => ⟨φ.s₀ b, b, rfl⟩, h₀ := φ.h₀, w₀ := φ.w₀ }, h𝒱⟩

end QcGeneralities

section QcLegs

variable {C : Type u} [Category.{t} C] {J : GrothendieckTopology C} {ι : Type w}
  (D : Discrete ι ⥤ Sheaf J AddCommGrpCat.{v}) (c : Cocone D) (hc : IsColimit c)

/-- A projection outside the support of a finite subsum vanishes on it. -/
public lemma projection_sum_of_notMem (X : Cᵒᵖ) (S : Finset ι)
    (υ : ∀ j : ι, (D.obj ⟨j⟩).obj.obj X) {k : ι} (hk : k ∉ S) :
    (projection D c hc k).hom.app X (∑ j ∈ S, (leg D c j).hom.app X (υ j)) = 0 :=
  sum_comp_of_notMem (fun _ _ => leg_comp_projection_ne D c hc) X S υ hk

end QcLegs

/-! ### The subpresheaf of finite subsums and its sheafification -/

section Subsheaf

variable {C : Type u} [Category.{t} C] {J : GrothendieckTopology C} {ι : Type w}
  (D : Discrete ι ⥤ Sheaf J AddCommGrpCat.{v}) (c : Cocone D)

/-- Extending the family of a finite subsum by zero over a larger finite set does not change the
subsum. -/
private lemma sum_eq_sum_of_subset (X : Cᵒᵖ) {S S' : Finset ι} (hSS : S ⊆ S')
    (σ υ : ∀ j : ι, (D.obj ⟨j⟩).obj.obj X) {x : c.pt.obj.obj X}
    (hx : x = ∑ j ∈ S, (leg D c j).hom.app X (σ j))
    (h₁ : ∀ j ∈ S, υ j = σ j) (h₂ : ∀ j ∈ S', j ∉ S → υ j = 0) :
    x = ∑ j ∈ S', (leg D c j).hom.app X (υ j) := by
  refine hx.trans ((Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset hSS fun j hj hjn => ?_))
  · rw [h₁ j hj]
  · rw [h₂ j hj hjn]
    exact map_zero _

/-- The sections over an object which are a finite sum of images of sections of the summands, as
an additive subgroup. -/
private def finiteSumSubgroup (X : Cᵒᵖ) : AddSubgroup (c.pt.obj.obj X) where
  carrier := {x | ∃ (S : Finset ι) (υ : ∀ j : ι, (D.obj ⟨j⟩).obj.obj X),
    x = ∑ j ∈ S, (leg D c j).hom.app X (υ j)}
  zero_mem' := ⟨∅, fun _ => 0, by simp⟩
  add_mem' := by
    rintro x y ⟨S, σ, hx⟩ ⟨S', σ', hy⟩
    refine ⟨S ∪ S', fun j => (if j ∈ S then σ j else 0) + (if j ∈ S' then σ' j else 0), ?_⟩
    have e1 : x = ∑ j ∈ S ∪ S', (leg D c j).hom.app X (if j ∈ S then σ j else 0) :=
      sum_eq_sum_of_subset D c X Finset.subset_union_left σ _ hx
        (fun j hj => ite_eq_left hj) (fun j _ hjn => ite_eq_right hjn)
    have e2 : y = ∑ j ∈ S ∪ S', (leg D c j).hom.app X (if j ∈ S' then σ' j else 0) :=
      sum_eq_sum_of_subset D c X Finset.subset_union_right σ' _ hy
        (fun j hj => ite_eq_left hj) (fun j _ hjn => ite_eq_right hjn)
    rw [e1, e2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (map_add _ _ _).symm
  neg_mem' := by
    rintro x ⟨S, σ, hx⟩
    refine ⟨S, fun j => -σ j, ?_⟩
    rw [hx, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => (map_neg _ _).symm

/-- The subpresheaf of sections which are a finite sum of images of sections of the summands. -/
private def finiteSumSubfunctor : Subfunctor (c.pt.obj ⋙ forget AddCommGrpCat.{v}) where
  obj X := {x | x ∈ finiteSumSubgroup D c X}
  map {X Y} g := by
    rintro x ⟨S, σ, hx⟩
    refine ⟨S, fun j => (D.obj ⟨j⟩).obj.map g (σ j), ?_⟩
    change c.pt.obj.map g x = _
    rw [hx]
    exact map_sum_leg D c g S σ

/-- Membership in the subpresheaf of finite subsums, unfolded. -/
private lemma exists_sum_of_sieveOfSection {X : Cᵒᵖ} (x : c.pt.obj.obj X) {Y : C}
    (g : Y ⟶ X.unop) (hg : (finiteSumSubfunctor D c).sieveOfSection x g) :
    ∃ (S : Finset ι) (υ : ∀ j : ι, (D.obj ⟨j⟩).obj.obj (op Y)),
      c.pt.obj.map g.op x = ∑ j ∈ S, (leg D c j).hom.app (op Y) (υ j) := hg

/-- The sections over an object which are *locally* a finite sum of images of sections of the
summands, as an additive subgroup. -/
private def localSumSubgroup (X : Cᵒᵖ) : AddSubgroup (c.pt.obj.obj X) where
  carrier := ((finiteSumSubfunctor D c).sheafify J).obj X
  zero_mem' := (finiteSumSubfunctor D c).le_sheafify J X (finiteSumSubgroup D c X).zero_mem
  add_mem' := by
    intro x y hx hy
    apply J.superset_covering _ (J.intersection_covering hx hy)
    intro Y f hf
    change c.pt.obj.map f.op (x + y) ∈ finiteSumSubgroup D c (op Y)
    rw [map_add]
    exact (finiteSumSubgroup D c (op Y)).add_mem hf.1 hf.2
  neg_mem' := by
    intro x hx
    apply J.superset_covering _ hx
    intro Y f hf
    change c.pt.obj.map f.op (-x) ∈ finiteSumSubgroup D c (op Y)
    rw [map_neg]
    exact (finiteSumSubgroup D c (op Y)).neg_mem hf

/-- The presheaf of abelian groups of sections locally a finite subsum. -/
private def localSumPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (localSumSubgroup D c X)
  map {X Y} g := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨c.pt.obj.map g s.1,
        ((finiteSumSubfunctor D c).sheafify J).map g s.2⟩
      map_zero' := by ext; exact map_zero _
      map_add' := fun s s' => by ext; exact map_add _ _ _ }
  map_id X := by
    ext s
    change c.pt.obj.map (𝟙 X) s.1 = s.1
    exact congrArg (fun k => k s.1) (c.pt.obj.map_id X)
  map_comp {X Y Z} g h := by
    ext s
    change c.pt.obj.map (g ≫ h) s.1 = c.pt.obj.map h (c.pt.obj.map g s.1)
    exact congrArg (fun k => k s.1) (c.pt.obj.map_comp g h)

/-- The underlying presheaf of sets of `localSumPresheaf` is the sheafification of the subpresheaf
of finite subsums. -/
private def localSumUnderlyingIso :
    localSumPresheaf D c ⋙ forget AddCommGrpCat.{v} ≅
      ((finiteSumSubfunctor D c).sheafify J).toFunctor :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun s => ⟨s.1, s.2⟩
        invFun := fun s => ⟨s.1, s.2⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl })
    fun _ => by ext s; rfl

/-- The sheaf of sections locally a finite subsum. -/
private def localSumSheaf : Sheaf J AddCommGrpCat.{v} :=
  ⟨localSumPresheaf D c,
    Presheaf.isSheaf_of_isSheaf_comp J _ (forget AddCommGrpCat.{v})
      ((Presheaf.isSheaf_of_iso_iff (localSumUnderlyingIso D c)).2
        ((isSheaf_iff_isSheaf_of_type J _).mpr
          ((finiteSumSubfunctor D c).sheafify_isSheaf (underlying_isSheaf c.pt))))⟩

/-- The inclusion of the sheaf of sections locally a finite subsum into the direct sum. -/
private def localSumInclusion : localSumSheaf D c ⟶ c.pt :=
  ⟨{ app X := AddCommGrpCat.ofHom (localSumSubgroup D c X).subtype
     naturality {X Y} g := by ext s; rfl }⟩

/-- Every image of a section of a summand is a finite subsum, hence locally one. -/
private lemma leg_app_mem_localSumSubgroup (j : ι) (X : Cᵒᵖ) (y : (D.obj ⟨j⟩).obj.obj X) :
    (leg D c j).hom.app X y ∈ localSumSubgroup D c X := by
  refine (finiteSumSubfunctor D c).le_sheafify J X ?_
  refine ⟨{j}, Function.update (fun k => (0 : (D.obj ⟨k⟩).obj.obj X)) j y, ?_⟩
  rw [Finset.sum_singleton, Function.update_self]

/-- The factorisation of a leg of the cocone through the sheaf of sections locally a finite
subsum. -/
private def legLift (j : ι) : D.obj ⟨j⟩ ⟶ localSumSheaf D c :=
  ⟨{ app X := AddCommGrpCat.ofHom
       { toFun := fun y => ⟨(leg D c j).hom.app X y, leg_app_mem_localSumSubgroup D c j X y⟩
         map_zero' := by ext; exact map_zero _
         map_add' := fun y z => by ext; exact map_add _ _ _ }
     naturality {X Y} g := by
       ext y
       exact Subtype.ext (leg_naturality D c j g y) }⟩

private lemma legLift_comp (j : ι) :
    legLift D c j ≫ localSumInclusion D c = leg D c j := by
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  ext X y
  rfl

/-- **The subsheaf of sections locally a finite subsum is everything.** Its inclusion into the
direct sum is split by the morphism the universal property of the colimit produces out of the
factorisations of the legs. -/
private lemma mem_localSumSubgroup (hc : IsColimit c) (X : Cᵒᵖ) (x : c.pt.obj.obj X) :
    x ∈ localSumSubgroup D c X := by
  obtain ⟨r, hr⟩ : ∃ r : c.pt ⟶ localSumSheaf D c, r ≫ localSumInclusion D c = 𝟙 c.pt := by
    refine ⟨hc.desc (Cocone.mk (localSumSheaf D c)
      (Discrete.natTrans fun k => legLift D c k.as)), hc.hom_ext fun k => ?_⟩
    rw [← Category.assoc, hc.fac, Category.comp_id]
    exact legLift_comp D c k.as
  have h1 : (localSumInclusion D c).hom.app X (r.hom.app X x) = x := by
    simpa using hom_app_comp_eq hr X x
  have h2 : (r.hom.app X x).1 ∈ localSumSubgroup D c X := (r.hom.app X x).2
  rwa [show (r.hom.app X x).1 = x from h1] at h2

end Subsheaf

/-- **The elementwise form of Stacks 0935 part (2) for sheaves of abelian groups.** Let `D` be a
family of sheaves of
abelian groups on a site, indexed by a discrete category, and let `c` be a colimiting cocone on
it, i.e. a direct sum of the family. Over a quasi-compact object `W` of the site (Stacks 090H),
every section of the direct sum is a *finite* sum of images of sections of the summands. -/
theorem exists_finset_sum_eq_of_isQuasiCompactObject
    {C : Type u} [Category.{t} C] (J : GrothendieckTopology C)
    {ι : Type w} (D : Discrete ι ⥤ Sheaf J AddCommGrpCat.{v})
    (c : Cocone D) (hc : IsColimit c)
    (W : C) (hW : J.IsQuasiCompactObject W)
    (s : c.pt.obj.obj (op W)) :
    ∃ (S : Finset ι) (t : ∀ j : ι, (D.obj ⟨j⟩).obj.obj (op W)),
      s = ∑ j ∈ S, (c.ι.app ⟨j⟩).hom.app (op W) (t j) := by
  -- the sieve on which `s` is a finite subsum is covering
  have hRmem : (finiteSumSubfunctor D c).sieveOfSection s ∈ J W :=
    mem_localSumSubgroup D c hc (op W) s
  -- quasi-compactness refines it to a covering factoring through finitely many of its members
  obtain ⟨𝒲, hfinite, hRW, 𝒱, φ, h𝒱⟩ := exists_cover_factoring hW hRmem
  have : Fintype 𝒲.I₀ := Fintype.ofFinite 𝒲.I₀
  choose T σ hσ using fun b : 𝒲.I₀ =>
    exists_sum_of_sieveOfSection D c s (𝒲.f b) (hRW b)
  refine ⟨Finset.univ.biUnion T, fun j => (projection D c hc j).hom.app (op W) s, ?_⟩
  refine hom_ext_of_cover c.pt 𝒱 h𝒱 fun b => ?_
  -- the restriction of `s` along the `b`-th member of the refinement, as a finite subsum
  have hres : c.pt.obj.map (𝒱.f b).op s =
      ∑ j ∈ T (φ.s₀ b), (leg D c j).hom.app (op (𝒱.X b))
        ((D.obj ⟨j⟩).obj.map (φ.h₀ b).op (σ (φ.s₀ b) j)) := by
    have e1 : c.pt.obj.map (𝒱.f b).op s
        = c.pt.obj.map (φ.h₀ b).op (c.pt.obj.map (𝒲.f (φ.s₀ b)).op s) := by
      rw [← φ.w₀ b, op_comp]
      exact ConcreteCategory.congr_hom (c.pt.obj.map_comp _ _) s
    rw [e1, hσ (φ.s₀ b)]
    exact map_sum_leg D c (φ.h₀ b).op (T (φ.s₀ b)) (σ (φ.s₀ b))
  -- the components of that restriction are read off by the projections
  have hcomp : ∀ j : ι, (D.obj ⟨j⟩).obj.map (𝒱.f b).op
        ((projection D c hc j).hom.app (op W) s) =
      (projection D c hc j).hom.app (op (𝒱.X b))
        (∑ k ∈ T (φ.s₀ b), (leg D c k).hom.app (op (𝒱.X b))
          ((D.obj ⟨k⟩).obj.map (φ.h₀ b).op (σ (φ.s₀ b) k))) := fun j => by
    rw [← hres]
    exact (NatTrans.naturality_apply (projection D c hc j).hom (𝒱.f b).op s).symm
  refine (sum_eq_sum_of_subset D c (op (𝒱.X b))
    (Finset.subset_biUnion_of_mem T (Finset.mem_univ (φ.s₀ b)))
    (fun j => (D.obj ⟨j⟩).obj.map (φ.h₀ b).op (σ (φ.s₀ b) j))
    (fun j => (D.obj ⟨j⟩).obj.map (𝒱.f b).op ((projection D c hc j).hom.app (op W) s))
    hres ?_ ?_).trans (map_sum_leg D c (𝒱.f b).op (Finset.univ.biUnion T)
      (fun j => (projection D c hc j).hom.app (op W) s)).symm
  · intro j hj
    rw [hcomp j, projection_sum_of_mem D c hc _ _ _ hj]
  · intro j _ hjn
    rw [hcomp j, projection_sum_of_notMem D c hc _ _ _ hjn]


end Stacks.Sites.DirectSumRecognition

end
