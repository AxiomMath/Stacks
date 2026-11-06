module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints

/-!
# The support of a sheaf on the small étale site

Let `B` be a big étale site containing a scheme `S`. The *support* of an abelian sheaf on the
small étale site of `S` is the set of points of `S` over which some geometric point has nonzero
stalk. For a general abelian sheaf this set need not be closed, but for a sheaf of rings it is:
a ring is zero exactly when its unit is zero, so the support of a sheaf of rings is the support
of the unit section over `S` itself, and the support of a section is closed.

## Main definitions

* `AlgebraicGeometry.SmallEtale.supportSheaf` — the support of an abelian sheaf on the small
  étale site.

## Main results

* `AlgebraicGeometry.SmallEtale.supportSheaf_eq_supportSection_one` — the support of the
  additive sheaf underlying a sheaf of rings is the support of its unit section over `S`.
* `AlgebraicGeometry.SmallEtale.isClosed_supportSheaf` — the support of a sheaf of rings on the
  small étale site is closed.

## Implementation notes

Over a fixed point `x` of `S` the two conditions "the stalk at some geometric point over `x` is
nonzero" and "`x` lies outside the zero locus of the unit section" are equivalent for every
geometric point over `x`, so the existential in the definition of the support collapses as soon
as one geometric point over `x` is exhibited; that is what `GeometricPoint.ofPoint` provides.

## References

* [Stacks Project, Tag 04FU](https://stacks.math.columbia.edu/tag/04FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [UnivLE.{u, v}]

/-- The support of an abelian sheaf on the small étale site of `S`: the set of points of `S`
over which some geometric point has nonzero stalk. -/
public def supportSheaf (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    [∀ t : GeometricPoint S, HasColimit (etaleStalkDiagram B S hS t F.obj)] : Set S :=
  {x | ∃ t : GeometricPoint S, t.LiesOver x ∧ ¬ IsZero (etaleStalk B S hS t F.obj)}

section

variable (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
  [∀ t : GeometricPoint S, HasColimit (etaleStalkDiagram B S hS t F.obj)]

/-- The canonical lift of a geometric point of `S` to the final object of the small étale
site. -/
public def finalLift (t : GeometricPoint S) :
    (geometricPointFiber B S hS t).obj (SmallEtale.final B S hS) :=
  ⟨t.hom, by
    change t.hom ≫ B.inclusion.map (𝟙 (B.obj S hS)) = t.hom
    simp⟩

/-- A germ over the final object vanishes exactly when the geometric point lands in the zero
locus of the section. -/
public theorem etaleGerm_final_eq_zero_iff (t : GeometricPoint S)
    (σ : F.obj.obj (op (SmallEtale.final B S hS))) :
    etaleGerm B S hS t F.obj (SmallEtale.final B S hS) (finalLift B S hS t) σ = 0 ↔
      (finalLift B S hS t).1 default ∈
        (zeroOpen B S hS F (SmallEtale.final B S hS) σ :
          Set ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS))) := by
  refine ⟨fun hgerm => ?_, fun hmem =>
    etaleGerm_eq_zero_of_notMem_supportSection B S hS t F _ (finalLift B S hS t) σ
      (by simpa only [supportSection, Set.mem_compl_iff, not_not] using hmem)⟩
  obtain ⟨W, j, q, hq, hzero⟩ := (etaleGerm_eq_zero_iff B S hS t F.obj _ _ σ).1 hgerm
  refine (map_eq_zero_iff_range_subset_zeroOpen B S hS F _ σ W j).1 hzero ⟨q.1 default, ?_⟩
  have hcomp : q.1 ≫ (SmallEtale.toScheme B S hS).map j = (finalLift B S hS t).1 :=
    congrArg Subtype.val hq
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun k : t.source ⟶ (SmallEtale.toScheme B S hS).obj
      (SmallEtale.final B S hS) => k default) hcomp

end

section Ring

variable (F : Sheaf (SmallEtale.topology B S hS) RingCat.{v})

/-- The additive sheaf underlying a sheaf of rings on the small étale site. -/
public abbrev toAddCommGrp : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v} :=
  (sheafCompose (SmallEtale.topology B S hS) (forget₂ RingCat.{v} AddCommGrpCat.{v})).obj F

variable [∀ t : GeometricPoint S,
    HasColimit (etaleStalkDiagram B S hS t (toAddCommGrp B S hS F).obj)]

/-- If the germ of the unit section vanishes, the stalk of the underlying additive sheaf is
zero. -/
public theorem isZero_etaleStalk_of_etaleGerm_one_eq_zero (t : GeometricPoint S)
    (hone : etaleGerm B S hS t (toAddCommGrp B S hS F).obj (SmallEtale.final B S hS)
      (finalLift B S hS t) (1 : F.obj.obj (op (SmallEtale.final B S hS))) = 0) :
    IsZero (etaleStalk B S hS t (toAddCommGrp B S hS F).obj) := by
  obtain ⟨W, j, q, _, hzero⟩ :=
    (etaleGerm_eq_zero_iff B S hS t (toAddCommGrp B S hS F).obj _ _ _).1 hone
  have hW : (1 : F.obj.obj (op W)) = 0 := by
    change (F.obj.map j.op).hom
      (1 : F.obj.obj (op (SmallEtale.final B S hS))) = 0 at hzero
    simpa using hzero
  have hall : ∀ a : ↑(etaleStalk B S hS t (toAddCommGrp B S hS F).obj), a = 0 := by
    intro a
    obtain ⟨W', q', b, rfl⟩ :=
      exists_etaleGerm_eq B S hS t (toAddCommGrp B S hS F).obj a
    obtain ⟨k, m, m', -⟩ := IsCofilteredOrEmpty.cone_objs
      (C := (geometricPointFiber B S hS t).Elements) (.mk q) (.mk q')
    have hk : (1 : F.obj.obj (op k.obj)) = 0 := by
      simpa using congrArg (fun z => (F.obj.map (m.hom).op).hom z) hW
    exact (etaleGerm_eq_zero_iff B S hS t (toAddCommGrp B S hS F).obj _ _ b).2
      ⟨k.obj, m'.hom, k.val, m'.map_val, eq_zero_of_zero_eq_one hk.symm _⟩
  have : Subsingleton ↑(etaleStalk B S hS t (toAddCommGrp B S hS F).obj) :=
    ⟨fun g g' => by rw [hall g, hall g']⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- A stalk of the additive sheaf underlying a sheaf of rings vanishes exactly when the germ of
the unit section does: a ring is zero precisely when its unit is zero. -/
public theorem isZero_etaleStalk_iff_etaleGerm_one_eq_zero (t : GeometricPoint S) :
    IsZero (etaleStalk B S hS t (toAddCommGrp B S hS F).obj) ↔
      etaleGerm B S hS t (toAddCommGrp B S hS F).obj (SmallEtale.final B S hS)
          (finalLift B S hS t) (1 : F.obj.obj (op (SmallEtale.final B S hS))) = 0 := by
  refine ⟨fun hz => ?_, isZero_etaleStalk_of_etaleGerm_one_eq_zero B S hS F t⟩
  have := AddCommGrpCat.subsingleton_of_isZero hz
  exact Subsingleton.elim _ _

/-- The support of the additive sheaf underlying a sheaf of rings is the support of its unit
section over `S`. -/
public theorem supportSheaf_eq_supportSection_one :
    supportSheaf B S hS (toAddCommGrp B S hS F) =
      supportSection B S hS (toAddCommGrp B S hS F) (SmallEtale.final B S hS)
        (1 : F.obj.obj (op (SmallEtale.final B S hS))) := by
  ext x
  have key : ∀ t : GeometricPoint S, t.LiesOver x →
      (¬ IsZero (etaleStalk B S hS t (toAddCommGrp B S hS F).obj) ↔
        x ∈ supportSection B S hS (toAddCommGrp B S hS F) (SmallEtale.final B S hS)
          (1 : F.obj.obj (op (SmallEtale.final B S hS)))) := by
    intro t ht
    rw [isZero_etaleStalk_iff_etaleGerm_one_eq_zero,
      etaleGerm_final_eq_zero_iff B S hS (toAddCommGrp B S hS F) t
        (1 : F.obj.obj (op (SmallEtale.final B S hS))),
      show (finalLift B S hS t).1 default = x from ht]
    exact Iff.rfl
  exact ⟨fun ⟨t, ht, hnz⟩ => (key t ht).1 hnz, fun hx => ⟨GeometricPoint.ofPoint S x,
    GeometricPoint.ofPoint_liesOver S x, (key _ (GeometricPoint.ofPoint_liesOver S x)).2 hx⟩⟩

/-- **Stacks 04FU.** The support of a sheaf of rings on the small étale site is closed: a ring
is zero exactly when its unit is zero, so the support of a sheaf of rings is the support of its
unit section, which is closed. -/
@[stacks 04FU]
public theorem isClosed_supportSheaf :
    IsClosed (supportSheaf B S hS (toAddCommGrp B S hS F)) := by
  rw [supportSheaf_eq_supportSection_one]
  exact isClosed_supportSection B S hS _ _ _

end Ring

end SmallEtale

end AlgebraicGeometry
