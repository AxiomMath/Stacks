module

public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackUnion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedStackClosedSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# The union of open substacks is the locus of its set of points (Stacks 05UQ)

The open substack of an algebraic stack cut out by the set of points lying in a member of a
family of open substacks is the union of that family.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.isUnion_pointsWithin`: the locus of the set of points lying
  in a member of a family of open substacks is the union of the family.

## References

* [Stacks Project, Tag 05UQ](https://stacks.math.columbia.edu/tag/05UQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace OpenSubstack

end OpenSubstack

/-! ### The existence of the union -/

/-- A section of a presheaf representing the base change of a full-subcategory inclusion along a
scheme-valued point exists over an object of the site exactly when the property holds at the
value of the point there. -/
private theorem nonempty_section_iff_subcategory
    {C : Type*} [Category C] {D : Type*} [Category D] {A : Type*} [Category A]
    (p : C ⥤ D) (r : A ⥤ D) (P : ObjectProperty C) (hP : P.IsClosedUnderIsomorphisms)
    (y : A ⥤ C) (hy : y ⋙ p = r) (F : Aᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst r (P.ι ⋙ p) p y P.ι)
      (presheafOfCategories (F ⋙ typeToCat)).p) (a : A) :
    Nonempty (F.obj (Opposite.op a)) ↔ P (y.obj a) := by
  constructor
  · rintro ⟨s⟩
    let b := e.inv.functor.obj ⟨a, Discrete.mk s⟩
    have hb : b.x = a := Functor.congr_obj e.inv.w ⟨a, Discrete.mk s⟩
    exact hP.of_iso (b.iso.symm ≪≫ y.mapIso (eqToIso hb)) b.y.property
  · intro ha
    let b : TwoFibreProductOver r (P.ι ⋙ p) p y P.ι :=
      { base := r.obj a
        x := a
        y := ⟨y.obj a, ha⟩
        hx := rfl
        hy := Functor.congr_obj hy a
        iso := Iso.refl _
        vertical := by
          have h := Functor.congr_obj hy a
          dsimp at h
          rw [← h]
          exact IsHomLift.id rfl }
    let s := e.hom.functor.obj b
    have hs : s.base = a := Functor.congr_obj e.hom.w b
    exact ⟨F.map (eqToHom hs.symm).op s.fiber.as⟩

/-- A morphism of the site lies in the image of the structural morphism of **Stacks 04SG** of an
algebraic space over `T` exactly when that space has a section over the morphism, read in the
site of `T`. -/
private theorem range_algebraicSpaceMap_iff_nonempty
    (T : BigFppfOver B S hS)
    (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B T.left.1 T.left.2 F)
    {V : BigFppfOver B S hS} (f : V ⟶ T) :
    f ∈ (Subfunctor.range (algebraicSpaceMap B S hS T
        ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj
          ⟨F, hF⟩)).hom).obj (Opposite.op V) ↔
      Nonempty (F.obj (Opposite.op (Over.mk f.left))) := by
  set e := (spacesOverSmallerBaseFunctorForgetIso B T.left.1 S T.left.2 hS T.hom).app ⟨F, hF⟩
    with he
  constructor
  · rintro ⟨s, hs⟩
    set t := e.hom.app (Opposite.op V) s with ht
    have ht' : Over.homMk t.val.fst t.property = f := by
      rw [← spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B T.left.1 S T.left.2 hS
        T.hom ⟨F, hF⟩ (Opposite.op V) t, ht, he]
      show (((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj
        ⟨F, hF⟩).1.hom).app (Opposite.op V)
        ((e.inv.app (Opposite.op V)) ((e.hom.app (Opposite.op V)) s)) = f
      rw [Iso.hom_inv_id_app_apply]
      exact hs
    have ht2 : t.val.fst = f.left := congrArg (fun g => g.left) ht'
    exact ⟨F.map (eqToHom (congrArg (fun g => Over.mk g) ht2).symm).op t.val.snd⟩
  · rintro ⟨s⟩
    refine ⟨e.inv.app (Opposite.op V) ⟨⟨f.left, s⟩, Over.w f⟩, ?_⟩
    refine (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B T.left.1 S T.left.2 hS
      T.hom ⟨F, hF⟩ (Opposite.op V) ⟨⟨f.left, s⟩, Over.w f⟩).trans ?_
    exact Over.OverMorphism.ext rfl

/-- **The base change of an open substack along a scheme-valued point is an open subspace.** For
an open substack `U` of `𝒳` and a scheme-valued point `y` of `𝒳` with values in `T`, the
subfunctor of `yoneda T` cut out by `U` is an open subspace of `T`. -/
private noncomputable def basePullbackOpen {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : OpenSubstack 𝒳) (T : BigFppfOver B S hS)
    (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map T.hom) :
    {V : Subfunctor (yoneda.obj T) // Space.IsOpenSubspace B S hS V} :=
  ⟨Subfunctor.range (algebraicSpaceMap B S hS T
      ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj
        ⟨(U.isOpenImmersion.1 T y hy).choose,
          (U.isOpenImmersion.1 T y hy).choose_spec.1⟩)).hom,
    Space.isOpenSubspace_subfunctorRange B S hS
      ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj
        ⟨(U.isOpenImmersion.1 T y hy).choose,
          (U.isOpenImmersion.1 T y hy).choose_spec.1⟩).property
      (U.isOpenImmersion.2 T y hy _ _ (U.isOpenImmersion.1 T y hy).choose_spec.2)⟩

/-- Membership in that open subspace: a morphism of the site lies in it exactly when the
restriction of the point along it lands in the open substack. -/
private theorem mem_basePullbackOpen_iff {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : OpenSubstack 𝒳) (T : BigFppfOver B S hS)
    (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map T.hom)
    {V : BigFppfOver B S hS} (f : V ⟶ T) :
    f ∈ (basePullbackOpen U T y hy).val.obj (Opposite.op V) ↔
      U.property (y.obj (Over.mk f.left)) :=
  (range_algebraicSpaceMap_iff_nonempty T _ (U.isOpenImmersion.1 T y hy).choose_spec.1 f).trans
    (nonempty_section_iff_subcategory 𝒳.val.val.p (Over.map T.hom) U.property U.strictlyFull
      y hy _ (U.isOpenImmersion.1 T y hy).choose_spec.2.some (Over.mk f.left))

/-- The open subspace of `yoneda (p.obj x)` cut out by an open substack at the scheme-valued
point named by an object `x` of `𝒳`. -/
private noncomputable def objectPullbackOpen {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : OpenSubstack 𝒳) (x : 𝒳.val.val.obj) :
    {V : Subfunctor (yoneda.obj (𝒳.val.val.p.obj x)) //
      Space.IsOpenSubspace B S hS V} :=
  basePullbackOpen U (𝒳.val.val.p.obj x)
    (fibrePoint B S hS 𝒳.val (𝒳.val.val.p.obj x) ⟨x, rfl⟩)
    (fibrePoint_comp B S hS 𝒳.val (𝒳.val.val.p.obj x) ⟨x, rfl⟩)

/-- Membership in the open subspace cut out at the 2-Yoneda point of `x`: a morphism `f` lies in
it exactly when some object of the substack maps to `x` over `f`. -/
private theorem mem_objectPullbackOpen_iff {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : OpenSubstack 𝒳) (x : 𝒳.val.val.obj)
    {V : BigFppfOver B S hS} (f : V ⟶ 𝒳.val.val.p.obj x) :
    f ∈ (objectPullbackOpen U x).val.obj (Opposite.op V) ↔
      ∃ (z : 𝒳.val.val.obj) (g : z ⟶ x),
        U.property z ∧ 𝒳.val.val.p.IsHomLift f g := by
  have hiff : f ∈ (objectPullbackOpen U x).val.obj (Opposite.op V) ↔
      U.property ((fibrePoint B S hS 𝒳.val (𝒳.val.val.p.obj x) ⟨x, rfl⟩).obj
        (Over.mk f.left)) :=
    mem_basePullbackOpen_iff U _ _ _ f
  rw [hiff]
  have := U.strictlyFull
  let k := Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.property (𝒳.val.val.p.obj x)
    ⟨x, rfl⟩ (Over.mk f)
  have hd : k.y ≅
      (fibrePoint B S hS 𝒳.val (𝒳.val.val.p.obj x) ⟨x, rfl⟩).obj (Over.mk f.left) :=
    (Functor.TwoYoneda.liftFunctor 𝒳.val.val.p 𝒳.val.property (𝒳.val.val.p.obj x)
      ⟨x, rfl⟩).mapIso
      ((Over.iteratedSliceEquiv (𝒳.val.val.p.obj x)).unitIso.app (Over.mk f))
  constructor
  · exact fun hz => ⟨k.y, k.φ, U.property.prop_of_iso hd.symm hz, k.isStronglyCartesian.toIsHomLift⟩
  · rintro ⟨z, g, hz, hg⟩
    have := hg
    have := 𝒳.val.property.isStronglyCartesian_homLift f g
    have : 𝒳.val.val.p.IsStronglyCartesian f k.φ := k.isStronglyCartesian
    exact U.property.prop_of_iso
      (Functor.IsStronglyCartesian.domainIsoOfBaseIso 𝒳.val.val.p
        (g := Iso.refl V) (Category.id_comp f).symm k.φ g ≪≫ hd) hz

/-- The identity lies in the open subspace cut out at the 2-Yoneda point of `x` exactly when `x`
itself lies in the open substack. -/
private theorem mem_objectPullbackOpen_id_iff {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : OpenSubstack 𝒳) (x : 𝒳.val.val.obj) :
    𝟙 (𝒳.val.val.p.obj x) ∈
        (objectPullbackOpen U x).val.obj (Opposite.op (𝒳.val.val.p.obj x)) ↔
      U.property x := by
  rw [mem_objectPullbackOpen_iff]
  have := U.strictlyFull
  constructor
  · rintro ⟨z, g, hz, hg⟩
    have := hg
    have := 𝒳.val.property.isStronglyCartesian_homLift (𝟙 (𝒳.val.val.p.obj x)) g
    have := Functor.IsStronglyCartesian.isIso_of_base_isIso
      𝒳.val.val.p (𝟙 (𝒳.val.val.p.obj x)) g
    exact U.property.prop_of_iso (asIso g) hz
  · exact fun hx => ⟨x, 𝟙 x, hx, IsHomLift.id rfl⟩

/-- An open subspace of a representable presheaf on the big fppf site of `S` is represented by an
open subscheme of the representing object, with the expected factorization criterion. -/
private theorem exists_openImmersion_representation {T : BigFppfOver B S hS}
    (U : Subfunctor (yoneda.obj T)) (hU : Space.IsOpenSubspace B S hS U) :
    ∃ (V : BigFppfOver B S hS) (v : V ⟶ T),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) ∧
      ∀ (Y : BigFppfOver B S hS) (g : Y ⟶ T),
        g ∈ U.obj (Opposite.op Y) ↔ ∃ a : Y ⟶ V, a ≫ v = g := by
  let h := hU.2.rep
  let V := h.pullback (𝟙 (yoneda.obj T))
  let v := h.snd (𝟙 (yoneda.obj T))
  let α := h.fst (𝟙 (yoneda.obj T))
  have : IsIso α := (h.isPullback (𝟙 (yoneda.obj T))).isIso_fst_of_isIso
  have hv : α ≫ U.ι = yoneda.map v := (h.w (𝟙 (yoneda.obj T))).trans (Category.comp_id _)
  refine ⟨V, v, hU.2.property_snd (𝟙 (yoneda.obj T)), fun Y g => ?_⟩
  constructor
  · intro hg
    let a : Y ⟶ V := (inv α).app (Opposite.op Y) ⟨g, hg⟩
    refine ⟨a, ?_⟩
    have heq := congrArg (fun t => t.app (Opposite.op Y) a) hv
    change (α.app (Opposite.op Y) a).val = a ≫ v at heq
    rw [← heq]
    show (α.app (Opposite.op Y) ((inv α).app (Opposite.op Y) ⟨g, hg⟩)).val = g
    have hcancel := congrArg (fun t => t.app (Opposite.op Y) ⟨g, hg⟩)
      (IsIso.inv_hom_id α)
    exact congrArg Subtype.val hcancel
  · rintro ⟨a, rfl⟩
    have heq := congrArg (fun t => t.app (Opposite.op Y) a) hv
    change (α.app (Opposite.op Y) a).val = a ≫ v at heq
    rw [← heq]
    exact (α.app (Opposite.op Y) a).property

/-- A morphism of the site whose image on points lies in the range of an open immersion of the
site factors through it. -/
private theorem exists_factorization_of_range_subset {V Y T : BigFppfOver B S hS} (v : V ⟶ T)
    (g : Y ⟶ T)
    (hv : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v))
    (h : Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map v)) :
    ∃ a : Y ⟶ V, a ≫ v = g := by
  have := hv
  let l := _root_.AlgebraicGeometry.IsOpenImmersion.lift
    ((BigFppfOver.toScheme B S hS).map v)
    ((BigFppfOver.toScheme B S hS).map g) h
  let a : Y.left ⟶ V.left := ObjectProperty.homMk l
  have ha : a ≫ v.left = g.left :=
    ObjectProperty.hom_ext _ (_root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ h)
  exact ⟨Over.homMk a (by rw [← Over.w v, ← Category.assoc, ha, Over.w g]),
    Over.OverMorphism.ext ha⟩

/-- **An open substack containing one field-valued point contains every field-valued point it
dominates.** -/
private theorem openSubstack_property_of_field_hom {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (U : OpenSubstack 𝒳) (p q : FieldValuedPoint B S hS 𝒳.val.val)
    (g : p.obj ⟶ q.obj) (hp : U.property p.obj) : U.property q.obj := by
  let D := BigFppfOver.toScheme B S hS
  let R := objectPullbackOpen U q.obj
  obtain ⟨V, v, hv, hV⟩ := exists_openImmersion_representation R.val R.property
  have hg : 𝒳.val.val.p.map g ∈
      R.val.obj (Opposite.op (𝒳.val.val.p.obj p.obj)) :=
    (mem_objectPullbackOpen_iff U q.obj _).mpr ⟨p.obj, g, hp, IsHomLift.map _ _⟩
  obtain ⟨a, ha⟩ := (hV _ _).mp hg
  let ep := D.mapIso (eqToIso p.over) ≪≫ p.isSpec
  let eq := D.mapIso (eqToIso q.over) ≪≫ q.isSpec
  have hsub : Subsingleton (D.obj (𝒳.val.val.p.obj q.obj)) :=
    Function.Injective.subsingleton eq.hom.homeomorph.injective
  let t := ep.inv (IsLocalRing.closedPoint p.carrier)
  have hrange : Set.range (D.map (𝟙 (𝒳.val.val.p.obj q.obj))) ⊆ Set.range (D.map v) :=
    fun _ _ => ⟨D.map a t, hsub.elim _ _⟩
  obtain ⟨b, hb⟩ := exists_factorization_of_range_subset v (𝟙 _) hv hrange
  exact (mem_objectPullbackOpen_id_iff U q.obj).mp ((hV _ _).mpr ⟨b, hb⟩)

/-- Every point of the scheme underlying the base of an object of `𝒳` is seen by a field-valued
point of `𝒳` mapping to that object. -/
private theorem exists_fieldValuedPoint_over_point {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (x : 𝒳.val.val.obj)
    (t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) :
    ∃ (q : FieldValuedPoint B S hS 𝒳.val.val) (g : q.obj ⟶ x)
      (s : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj q.obj)),
      (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map g) s = t := by
  let D := BigFppfOver.toScheme B S hS
  let T := 𝒳.val.val.p.obj x
  let K := Spec ((D.obj T).residueField t)
  let f := (D.obj T).fromSpecResidueField t
  have : QuasiCompact f := by
    rw [quasiCompact_iff_forall_isAffineOpen]
    exact fun W _ => (Set.toFinite (f ⁻¹' (W : Set (D.obj T)))).isCompact
  have hK : B.Contains K := Scheme.size_lt_of_mono_quasiCompact f T.left.property
  let V : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (f ≫ T.hom.hom) : B.obj hK ⟶ B.obj hS)
  let a : V ⟶ T := Over.homMk (ObjectProperty.homMk f) rfl
  obtain ⟨z, g, hg⟩ := 𝒳.val.property.exists_lift a x rfl
  let h := IsHomLift.domain_eq 𝒳.val.val.p a g
  let e : D.obj (𝒳.val.val.p.obj z) ≅ K := D.mapIso (eqToIso h)
  let q : FieldValuedPoint B S hS 𝒳.val.val :=
    { carrier := (D.obj T).residueField t
      base := 𝒳.val.val.p.obj z
      isSpec := e
      obj := z
      «over» := rfl }
  refine ⟨q, g, e.inv (IsLocalRing.closedPoint ((D.obj T).residueField t)), ?_⟩
  have hmap : 𝒳.val.val.p.map g = eqToHom h ≫ a := by
    simpa using IsHomLift.fac' 𝒳.val.val.p a g
  rw [hmap, D.map_comp]
  show f (e.hom (e.inv _)) = t
  simp [f, Scheme.fromSpecResidueField_apply]

/-! ### The union -/

/-- The set of points of `|𝒳|` lying in some member of a family of open substacks. -/
private def familyPointSet {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) : Set (points B S hS 𝒳.val.val 𝒳.val.property) :=
  ⋃ i, Set.range (pointsMap B S hS
    (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val.val
    (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val.property
    𝒳.val.property
    (fullSubcategoryInclusion 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).hom.hom)

/-- Membership in `AlgebraicGeometry.Stack.familyPointSet`: a point of `|𝒳|` lies in it exactly
when some field-valued point representing it has its object in a member of the family. -/
private theorem mem_familyPointSet_iff {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) (c : points B S hS 𝒳.val.val 𝒳.val.property) :
    c ∈ familyPointSet 𝒰 ↔
      ∃ (i : I) (q : FieldValuedPoint B S hS 𝒳.val.val),
        (𝒰 i).property q.obj ∧ pointClass B S hS 𝒳.val.val 𝒳.val.property q = c := by
  rw [familyPointSet, Set.mem_iUnion]
  constructor
  · rintro ⟨i, y, rfl⟩
    induction y using Quotient.inductionOn with
    | h q =>
      exact ⟨i, fieldValuedPointMap B S hS _
        (fullSubcategoryInclusion 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).hom.hom q,
        q.obj.property, rfl⟩
  · rintro ⟨i, q, hq, rfl⟩
    exact ⟨i, pointClass B S hS _ _
      { carrier := q.carrier
        field := q.field
        base := q.base
        isSpec := q.isSpec
        obj := ⟨q.obj, hq⟩
        «over» := q.over }, rfl⟩

/-- The set of points lying in some member of the family is open. -/
private theorem isOpen_familyPointSet {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) :
    @IsOpen _ (pointTopology B S hS 𝒳.val) (familyPointSet 𝒰) := by
  let _ := pointTopology B S hS 𝒳.val
  refine isOpen_iUnion fun i => ?_
  let _ := pointTopology B S hS
    (fullSubcategoryAlgebraicStack 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic).val
  exact (AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion B S hS
    (fullSubcategoryInclusion 𝒳 (𝒰 i).property (𝒰 i).isAlgebraic)
    (𝒰 i).isOpenImmersion).isOpen_range

/-- Every member of the family is contained in the locus of a set of points which is exactly the
set of classes of field-valued points lying in a member. -/
private theorem le_pointsWithin_of_mem_iff {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) {Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property)}
    (hΩ : ∀ c, c ∈ Ω ↔ ∃ (i : I) (q : FieldValuedPoint B S hS 𝒳.val.val),
      (𝒰 i).property q.obj ∧ pointClass B S hS 𝒳.val.val 𝒳.val.property q = c)
    (i : I) :
    (𝒰 i).property ≤ pointsWithin 𝒳 Ω := by
  have := (𝒰 i).strictlyFull
  intro x hx q φ
  exact (hΩ _).2
    ⟨i, q, prop_of_isHomLift B S hS (𝒰 i).isAlgebraic (𝒳.val.val.p.map φ) φ
      (IsHomLift.map _ _) hx, rfl⟩

/-- Let `Ω` be a set of points of `|𝒳|` consisting exactly of the classes of the field-valued
points of `𝒳` whose object lies in a member of the family. Then the locus
`AlgebraicGeometry.Stack.pointsWithin` of `Ω` is the union of the family: it contains every
member, and every object of it lies, over a covering sieve, in a member. -/
@[stacks 05UQ "the union of the family is the locus of the set of points lying in a member"]
theorem OpenSubstack.isUnion_pointsWithin {𝒳 : AlgebraicStacks.{u, w} B S hS} {I : Type*}
    (𝒰 : I → OpenSubstack 𝒳) {Ω : Set (points B S hS 𝒳.val.val 𝒳.val.property)}
    (hΩ : ∀ c, c ∈ Ω ↔ ∃ (i : I) (q : FieldValuedPoint B S hS 𝒳.val.val),
      (𝒰 i).property q.obj ∧ pointClass B S hS 𝒳.val.val 𝒳.val.property q = c) :
    OpenSubstack.IsUnion 𝒳 𝒰 (pointsWithin 𝒳 Ω) := by
  classical
  have hfib : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  refine ⟨le_pointsWithin_of_mem_iff 𝒰 hΩ, ?_⟩
  rintro T ⟨x, rfl⟩ hx
  let D := BigFppfOver.toScheme B S hS
  choose V v hv hV using fun i => exists_openImmersion_representation
    (objectPullbackOpen (𝒰 i) x).val (objectPullbackOpen (𝒰 i) x).property
  have hc : ∀ t : D.obj (𝒳.val.val.p.obj x), ∃ i s, D.map (v i) s = t := by
    intro t
    obtain ⟨q, g, s, hs⟩ := exists_fieldValuedPoint_over_point x t
    obtain ⟨i, r, hr, hrq⟩ := (hΩ _).1 (hx q g)
    obtain ⟨w₀, ⟨f₁⟩, ⟨f₂⟩⟩ := (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val
      𝒳.val.property r q).1 hrq
    have := (𝒰 i).strictlyFull
    have hw₀ : (𝒰 i).property w₀.obj :=
      prop_of_isHomLift B S hS (𝒰 i).isAlgebraic (𝒳.val.val.p.map f₁) f₁
        (IsHomLift.map _ _) hr
    have hq : (𝒰 i).property q.obj :=
      openSubstack_property_of_field_hom (𝒰 i) w₀ q f₂ hw₀
    have hg := (mem_objectPullbackOpen_iff (𝒰 i) x (𝒳.val.val.p.map g)).mpr
      ⟨q.obj, g, hq, IsHomLift.map _ _⟩
    obtain ⟨a, ha⟩ := (hV i _ _).mp hg
    refine ⟨i, D.map a s, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← D.map_comp, ha]
    exact hs
  choose idx pt hpt using hc
  refine ⟨Sieve.ofArrows (fun t : D.obj (𝒳.val.val.p.obj x) => V (idx t))
      (fun t => v (idx t)), ?_, ?_⟩
  · exact BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS
      (fun t => v (idx t)) (fun t => hv (idx t)) (fun t => ⟨t, pt t, hpt t⟩)
  · rintro Y f ⟨Z, a, b, ⟨t⟩, hab⟩
    have hfmem := (hV (idx t) _ f).mpr ⟨a, hab⟩
    obtain ⟨z, g, hz, hg⟩ := (mem_objectPullbackOpen_iff _ _ _).mp hfmem
    refine ⟨idx t, ?_⟩
    have := (𝒰 (idx t)).strictlyFull
    have := hg
    have := 𝒳.val.property.isStronglyCartesian_homLift f g
    have : 𝒳.val.val.p.IsStronglyCartesian f
        (Functor.IsPreFibered.pullbackMap
          (show 𝒳.val.val.p.obj x = 𝒳.val.val.p.obj x from rfl) f) :=
      𝒳.val.property.isStronglyCartesian_homLift f _
    exact (𝒰 (idx t)).property.prop_of_iso
      (Functor.IsStronglyCartesian.domainIsoOfBaseIso 𝒳.val.val.p
        (g := Iso.refl _) (Category.id_comp f).symm
        (Functor.IsPreFibered.pullbackMap
          (show 𝒳.val.val.p.obj x = 𝒳.val.val.p.obj x from rfl) f) g) hz

end AlgebraicGeometry.Stack

end
