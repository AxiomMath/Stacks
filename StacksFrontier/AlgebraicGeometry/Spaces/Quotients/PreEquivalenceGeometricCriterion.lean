module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.LargeFieldLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.CoarseQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.SetTheoreticEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.PreRelationTestPoints

/-!
# A geometric criterion for a set-theoretic pre-equivalence relation

Let `j : R ⟶ U ×_B U` be a pre-relation of algebraic spaces over an algebraic space `B`. The
three maps to `U ×_B U` attached to a relation — the diagonal of `U`, the flip of `j`, and the
endpoints of a composable pair of arrows of `j` — have images on topological points, and `j`
is a set-theoretic pre-equivalence relation exactly when its own image on points contains all
three. Each containment is also a statement about arrows over an algebraically closed field,
and so the condition is equivalent to the relation cut out on `U(k)` by the arrows *already
present* in `R(k)` being an equivalence relation, for every algebraically closed field `k` in
the site above one uniform cardinal bound. When the source and the target of `j` are locally
of finite type no bound is needed: every algebraically closed field in the site will do.

## Main definitions

* `AlgebraicGeometry.Space.PreRelation.ContainsRelationImages` is the conjunction of the three
  image containments on topological points.

## Main results

* `AlgebraicGeometry.Space.isSetTheoreticPreEquivalenceRelation_iff_containsRelationImages`:
  the set-theoretic pre-equivalence condition is exactly the three containments.
* `AlgebraicGeometry.Space.containsRelationImages_iff_exists_geometricRel_equivalence`: the
  three containments hold exactly when the relation of actual arrows over `k` is an
  equivalence relation for every algebraically closed `k` above a uniform bound.
* `AlgebraicGeometry.Space.isSetTheoreticPreEquivalenceRelation_iff_geometricRel_equivalence`:
  for a pre-relation whose source and target are locally of finite type the bound can be
  dropped.

## Implementation notes

The relation of actual arrows is `AlgebraicGeometry.Space.PreRelation.GeometricRel`, already
available next to the set-theoretic relation of **Stacks 0490**; the difference between the
two is precisely that the latter allows an extension of the field. A pre-relation of algebraic
spaces is read in the slice of presheaves by `AlgebraicGeometry.Space.presheafPreRelation`,
which is where those two relations and the condition of **Stacks 0490** live; the two
characterisation lemmas below restate them through the endpoint maps of the original
pre-relation.

"Above a uniform bound" means above one cardinal strictly below the size cutoff of the site,
uniformly in the geometric point of the base. The bound has to be strictly below the cutoff:
every field whose spectrum is an object of the site has cardinality below the cutoff, so a
bound at the cutoff would be met by no field at all and the condition would be vacuous. The
bound produced by the proof is the invariant `sup {ℵ₀, |κ(v)|}` of a scheme atlas of `R`,
which is the hypothesis under which an arrow over an extension field descends to the field
itself.

The finite-type hypothesis on the source of the pre-relation is carried by the statement of
the last result, as in the source, but is not used: the three image containments already give
an arrow over the field once the target map alone is locally of finite type, because that is
what makes the relevant pullback projection locally of finite type.

Sections of an algebraic space over `B` at an object of the site are handled throughout
through `AlgebraicGeometry.Space.representableOver` and
`AlgebraicGeometry.Space.testPointOver`: a section in a fibre of the structure morphism is the
same datum as a morphism over `B` out of a representable algebraic space, and the universal
properties of the product and of a pullback apply to the latter.

## References

* [Stacks Project, Tag 0491](https://stacks.math.columbia.edu/tag/0491)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {site : BigFppfSite.{u}} {S : Scheme.{u}} {hS : site.Contains S}
  {B : AlgebraicSpaces site S hS}

/-! ### Sections and morphisms in the slice over an algebraic space -/

/-- The value of a composite of morphisms over `B` on a section is the composite of the
values. -/
theorem comp_left_hom_app {X Y Z : Over B} (f : X ⟶ Y) (g : Y ⟶ Z)
    {T : BigFppfOver site S hS} (v : X.left.obj.obj (Opposite.op T)) :
    g.left.hom.app (Opposite.op T) (f.left.hom.app (Opposite.op T) v) =
      (f ≫ g).left.hom.app (Opposite.op T) v := by
  simp only [Over.comp_left, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply]

/-- The value of a morphism over `B` which is known to be a composite. -/
private theorem left_hom_app_of_eq_comp {X Y Z : Over B} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (hfg : f ≫ g = h) {T : BigFppfOver site S hS} (v : X.left.obj.obj (Opposite.op T)) :
    g.left.hom.app (Opposite.op T) (f.left.hom.app (Opposite.op T) v) =
      h.left.hom.app (Opposite.op T) v :=
  (comp_left_hom_app f g v).trans
    (congrArg (fun m : X ⟶ Z ↦ m.left.hom.app (Opposite.op T) v) hfg)

/-- Restriction along an identity of the site does nothing to a section. -/
private theorem map_id_app {F : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    {T : BigFppfOver site S hS} (v : F.obj (Opposite.op T)) : F.map (𝟙 T).op v = v := by
  simp

/-- Restriction along a composite of morphisms of the site. -/
private theorem map_comp_app {F : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    {T₁ T₂ T₃ : BigFppfOver site S hS} (f : T₂ ⟶ T₃) (g : T₁ ⟶ T₂)
    (v : F.obj (Opposite.op T₃)) : F.map g.op (F.map f.op v) = F.map (g ≫ f).op v := by
  rw [op_comp, F.map_comp]
  rfl

/-- A morphism over `B` carries a section to one with the same image in the base. -/
theorem base_left_hom_app {X Y : Over B} (f : X ⟶ Y) {T : BigFppfOver site S hS}
    (v : X.left.obj.obj (Opposite.op T)) :
    Y.hom.hom.app (Opposite.op T) (f.left.hom.app (Opposite.op T) v) =
      X.hom.hom.app (Opposite.op T) v := by
  have h := congrArg (fun k : X.left.obj ⟶ B.obj ↦ k.app (Opposite.op T) v) (over_w_hom f)
  simpa only [NatTrans.comp_app, types_comp_apply] using h

/-- Naturality of a morphism of presheaves at the section of a field-valued point. -/
private theorem map_app_fieldValuedPoint {F G : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ G) (p : FieldValuedPoint site S hS F) {T : BigFppfOver site S hS}
    (f : T ⟶ p.siteObject) :
    α.app (Opposite.op T) (F.map f.op p.value) =
      G.map f.op (α.app (Opposite.op p.siteObject) p.value) :=
  congrArg (fun z ↦ z p.value) (α.naturality f.op)

/-- Yoneda transport of a section along a morphism over `B`. -/
private theorem symm_comp_left_hom {X Y : Over B} (g : X ⟶ Y) {T : BigFppfOver site S hS}
    (v : X.left.obj.obj (Opposite.op T)) :
    yonedaEquiv.symm v ≫ g.left.hom =
      yonedaEquiv.symm (g.left.hom.app (Opposite.op T) v) :=
  yonedaEquiv_symm_naturality_right T g.left.hom v

/-- A section of `X` in the fibre of the structure morphism over a point of the base, read as
a morphism over `B` out of the representable algebraic space of the test object. -/
private noncomputable def sectionOver {X : Over B} {T : BigFppfOver site S hS}
    {b : yoneda.obj T ⟶ B.obj} (v : X.left.obj.obj (Opposite.op T))
    (hv : X.hom.hom.app (Opposite.op T) v = yonedaEquiv b) :
    representableOver (B := B) T b ⟶ X :=
  testPointOver ⟨yonedaEquiv.symm v,
    (yonedaEquiv_symm_naturality_right T X.hom.hom v).trans
      ((congrArg yonedaEquiv.symm hv).trans (yonedaEquiv.symm_apply_apply b))⟩

/-- Reading a section at a test object as a morphism over `B` is compatible with postcomposing
a morphism over `B`. -/
theorem left_hom_app_yonedaEquiv {X Y : Over B} {T : BigFppfOver site S hS}
    {b : yoneda.obj T ⟶ B.obj} (m : representableOver (B := B) T b ⟶ X) (g : X ⟶ Y) :
    g.left.hom.app (Opposite.op T) (yonedaEquiv m.left.hom) =
      yonedaEquiv (m ≫ g).left.hom := rfl

/-- The first projection of the image of a section under the diagonal is that section. -/
private theorem diag_left_hom_app_fst (U : Over B) {T : BigFppfOver site S hS}
    (v : U.left.obj.obj (Opposite.op T)) :
    (prod.fst : U ⨯ U ⟶ U).left.hom.app (Opposite.op T)
      ((diag U).left.hom.app (Opposite.op T) v) = v := by
  rw [comp_left_hom_app]
  simp

/-- The second projection of the image of a section under the diagonal is that section. -/
private theorem diag_left_hom_app_snd (U : Over B) {T : BigFppfOver site S hS}
    (v : U.left.obj.obj (Opposite.op T)) :
    (prod.snd : U ⨯ U ⟶ U).left.hom.app (Opposite.op T)
      ((diag U).left.hom.app (Opposite.op T) v) = v := by
  rw [comp_left_hom_app]
  simp

/-- Two sections of `U ×_B U` with the same two projections are equal. -/
private theorem prod_value_ext {U : Over B} {T : BigFppfOver site S hS}
    (s t : (U ⨯ U : Over B).left.obj.obj (Opposite.op T))
    (hfst : (prod.fst : U ⨯ U ⟶ U).left.hom.app (Opposite.op T) s =
      (prod.fst : U ⨯ U ⟶ U).left.hom.app (Opposite.op T) t)
    (hsnd : (prod.snd : U ⨯ U ⟶ U).left.hom.app (Opposite.op T) s =
      (prod.snd : U ⨯ U ⟶ U).left.hom.app (Opposite.op T) t) :
    s = t := by
  have hs : (U ⨯ U : Over B).hom.hom.app (Opposite.op T) s =
      yonedaEquiv (yonedaEquiv.symm
        ((U ⨯ U : Over B).hom.hom.app (Opposite.op T) s)) :=
    (Equiv.apply_symm_apply yonedaEquiv _).symm
  have ht : (U ⨯ U : Over B).hom.hom.app (Opposite.op T) t =
      yonedaEquiv (yonedaEquiv.symm
        ((U ⨯ U : Over B).hom.hom.app (Opposite.op T) s)) :=
    ((base_left_hom_app (prod.fst : U ⨯ U ⟶ U) t).symm.trans
      ((congrArg (U.hom.hom.app (Opposite.op T)) hfst).symm.trans
        (base_left_hom_app (prod.fst : U ⨯ U ⟶ U) s))).trans hs
  have hmor : sectionOver (X := U ⨯ U) s hs = sectionOver (X := U ⨯ U) t ht := by
    refine prod.hom_ext ?_ ?_ <;> refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
    · show yonedaEquiv.symm s ≫ (prod.fst : U ⨯ U ⟶ U).left.hom =
        yonedaEquiv.symm t ≫ (prod.fst : U ⨯ U ⟶ U).left.hom
      exact (symm_comp_left_hom (prod.fst : U ⨯ U ⟶ U) s).trans
        ((congrArg yonedaEquiv.symm hfst).trans
          (symm_comp_left_hom (prod.fst : U ⨯ U ⟶ U) t).symm)
    · show yonedaEquiv.symm s ≫ (prod.snd : U ⨯ U ⟶ U).left.hom =
        yonedaEquiv.symm t ≫ (prod.snd : U ⨯ U ⟶ U).left.hom
      exact (symm_comp_left_hom (prod.snd : U ⨯ U ⟶ U) s).trans
        ((congrArg yonedaEquiv.symm hsnd).trans
          (symm_comp_left_hom (prod.snd : U ⨯ U ⟶ U) t).symm)
  refine yonedaEquiv.symm.injective
    (congrArg (fun m : representableOver (B := B) T
      (yonedaEquiv.symm ((U ⨯ U : Over B).hom.hom.app (Opposite.op T) s)) ⟶ U ⨯ U ↦
      m.left.hom) hmor)

/-- Two sections with the same image in `Y` come from one section of the pullback. -/
private theorem exists_pullback_section {X Y Z : Over B} (f : X ⟶ Y) (g : Z ⟶ Y)
    {T : BigFppfOver site S hS} (u : X.left.obj.obj (Opposite.op T))
    (w : Z.left.obj.obj (Opposite.op T))
    (h : f.left.hom.app (Opposite.op T) u = g.left.hom.app (Opposite.op T) w) :
    ∃ p : (pullback f g).left.obj.obj (Opposite.op T),
      (pullback.fst f g).left.hom.app (Opposite.op T) p = u ∧
        (pullback.snd f g).left.hom.app (Opposite.op T) p = w := by
  have hu : X.hom.hom.app (Opposite.op T) u =
      yonedaEquiv (yonedaEquiv.symm (X.hom.hom.app (Opposite.op T) u)) :=
    (Equiv.apply_symm_apply yonedaEquiv _).symm
  have hw : Z.hom.hom.app (Opposite.op T) w =
      yonedaEquiv (yonedaEquiv.symm (X.hom.hom.app (Opposite.op T) u)) :=
    ((base_left_hom_app g w).symm.trans
      ((congrArg (Y.hom.hom.app (Opposite.op T)) h).symm.trans (base_left_hom_app f u))).trans hu
  have hcomm : sectionOver u hu ≫ f = sectionOver w hw ≫ g := by
    refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_)
    change yonedaEquiv.symm u ≫ f.left.hom = yonedaEquiv.symm w ≫ g.left.hom
    exact (symm_comp_left_hom f u).trans
      ((congrArg yonedaEquiv.symm h).trans (symm_comp_left_hom g w).symm)
  refine ⟨yonedaEquiv (pullback.lift _ _ hcomm).left.hom, ?_, ?_⟩
  · exact (left_hom_app_yonedaEquiv _ (pullback.fst f g)).trans
      ((congrArg (fun m ↦ yonedaEquiv m.left.hom) (pullback.lift_fst _ _ hcomm)).trans
        (Equiv.apply_symm_apply yonedaEquiv u))
  · exact (left_hom_app_yonedaEquiv _ (pullback.snd f g)).trans
      ((congrArg (fun m ↦ yonedaEquiv m.left.hom) (pullback.lift_snd _ _ hcomm)).trans
        (Equiv.apply_symm_apply yonedaEquiv w))

/-! ### Geometric representatives over arbitrarily large fields -/

/-- The invariant `sup {ℵ₀, |κ(x)|}` of a scheme is at most its size. -/
theorem aleph0_sup_iSup_residueField_le_size (X : Scheme.{u}) :
    Cardinal.aleph0 ⊔ (⨆ x : X, Cardinal.mk (X.residueField x)) ≤ X.size := by
  by_cases hX : IsEmpty X
  · have := hX
    simp [Scheme.aleph0_le_size]
  · have : Nonempty X := not_isEmpty_iff.mp hX
    exact sup_le (Scheme.aleph0_le_size X) (ciSup_le fun x ↦ residueField_size_le X x)

/-- Every point of a presheaf on the big fppf site over `S` is the image of a geometric point
whose field is larger than any prescribed cardinal below the size cutoff of the site.

Adjoining to a geometric representative that many indeterminates, passing to the fraction
field and taking an algebraic closure produces such a field; the successor of the prescribed
cardinal is still below the cutoff because the cutoff is a strong limit. -/
private theorem exists_geometricPoint_image_eq_of_lt_mk
    (F : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u) (x : points site S hS F) (κ : Cardinal.{u})
    (hκ : κ < site.cutoff) :
    ∃ p : GeometricPoint site S hS F, p.image = x ∧ κ < Cardinal.mk p.val.carrier := by
  classical
  obtain ⟨p₀, hp₀⟩ := exists_geometricRepresentative site S hS F x
  have hp₀cutoff : Cardinal.mk p₀.val.carrier < site.cutoff := by
    have hsize : (Spec (.of p₀.val.carrier)).size < site.cutoff := p₀.val.contained
    rw [Scheme.size_Spec] at hsize
    exact (le_max_right _ _).trans_lt hsize
  set κ' : Cardinal.{u} :=
    max (max Cardinal.aleph0 κ) (Cardinal.mk p₀.val.carrier) with hκ'def
  set ν : Cardinal.{u} := Order.succ κ' with hνdef
  set ι : Type u := ν.ord.ToType with hιdef
  set L : Type u := AlgebraicClosure (FractionRing (MvPolynomial ι p₀.val.carrier)) with hLdef
  have hκ' : κ' < site.cutoff :=
    max_lt (max_lt site.aleph0_lt_cutoff hκ) hp₀cutoff
  have hν : ν < site.cutoff :=
    (Order.succ_le_of_lt (Cardinal.cantor κ')).trans_lt (site.cutoff_isStrongPrelimit hκ')
  have hνaleph : Cardinal.aleph0 ≤ ν :=
    ((le_max_left Cardinal.aleph0 κ).trans (le_max_left _ _)).trans (Order.le_succ κ')
  have hιmk : Cardinal.mk ι = ν := Cardinal.mk_ord_toType ν
  have hbase : Cardinal.mk p₀.val.carrier ≤ ν := (le_max_right _ _).trans (Order.le_succ κ')
  have hLcard : Cardinal.mk L ≤ ν := by
    have hpoly : Cardinal.mk (MvPolynomial ι p₀.val.carrier) ≤ ν :=
      MvPolynomial.cardinalMk_le_max.trans
        (by rw [hιmk]; exact max_le (max_le hbase le_rfl) hνaleph)
    have hfrac : Cardinal.mk (FractionRing (MvPolynomial ι p₀.val.carrier)) ≤ ν := by
      rw [FractionRing.cardinalMk]; exact hpoly
    exact (Algebra.IsAlgebraic.cardinalMk_le_max _ _).trans (max_le hfrac hνaleph)
  have hνleL : ν ≤ Cardinal.mk L := by
    have hg : Function.Injective fun i : ι ↦
        (algebraMap (FractionRing (MvPolynomial ι p₀.val.carrier)) L)
          ((algebraMap (MvPolynomial ι p₀.val.carrier)
            (FractionRing (MvPolynomial ι p₀.val.carrier)))
            (MvPolynomial.X i : MvPolynomial ι p₀.val.carrier)) := by
      intro i₁ i₂ hij
      refine MvPolynomial.X_injective (R := p₀.val.carrier) ?_
      refine (IsFractionRing.injective (MvPolynomial ι p₀.val.carrier)
        (FractionRing (MvPolynomial ι p₀.val.carrier))).eq_iff.mp ?_
      exact (RingHom.injective
        (algebraMap (FractionRing (MvPolynomial ι p₀.val.carrier)) L)).eq_iff.mp hij
    simpa only [hιmk] using Cardinal.mk_le_of_injective hg
  have hκlarge : κ < Cardinal.mk L :=
    (lt_of_le_of_lt ((le_max_right Cardinal.aleph0 κ).trans (le_max_left _ _))
      (Order.lt_succ κ')).trans_le hνleL
  have hLsite : site.Contains (Spec (.of L)) := by
    have hsize : (Spec (.of L)).size ≤ ν := by
      rw [Scheme.size_Spec]; exact max_le hνaleph hLcard
    exact hsize.trans_lt hν
  set g : Spec (.of L) ⟶ Spec (.of p₀.val.carrier) :=
    Spec.map (CommRingCat.ofHom (algebraMap p₀.val.carrier L)) with hgdef
  set e : site.obj hLsite ⟶ site.obj p₀.val.contained := site.inclusion.preimage
    (show site.inclusion.obj (site.obj hLsite) ⟶
      site.inclusion.obj (site.obj p₀.val.contained) from g) with hedef
  have hew : e ≫ (⟨p₀.val.toBase⟩ : site.obj p₀.val.contained ⟶ site.obj hS) =
      (⟨g ≫ p₀.val.toBase⟩ : site.obj hLsite ⟶ site.obj hS) := by
    apply site.inclusion.map_injective
    rw [site.inclusion.map_comp, hedef, Functor.map_preimage]
    rfl
  set eOver :
      (Over.mk (⟨g ≫ p₀.val.toBase⟩ : site.obj hLsite ⟶ site.obj hS) :
        BigFppfOver site S hS) ⟶ p₀.val.siteObject := Over.homMk e hew with heOverdef
  set q : FieldValuedPoint site S hS F :=
    { carrier := L
      contained := hLsite
      toBase := g ≫ p₀.val.toBase
      value := F.map eOver.op p₀.val.value } with hqdef
  have hclass : q.class site S hS F = p₀.val.class site S hS F :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension site S hS F
      ⟨q, FieldValuedPoint.dominates_refl site S hS F q, ⟨eOver, rfl⟩⟩
  exact ⟨⟨q, inferInstance⟩, hclass.trans hp₀, hκlarge⟩

/-! ### Common extensions with commuting paths -/

/-- Two field-valued points dominated by a third have a common extension through which the
two domination morphisms become equal. -/
private theorem exists_commonExtension_comp_eq {F : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (p q r : FieldValuedPoint site S hS F) (f : p.siteObject ⟶ q.siteObject)
    (hf : F.map f.op q.value = p.value) (g : r.siteObject ⟶ q.siteObject)
    (hg : F.map g.op q.value = r.value) :
    ∃ (c : FieldValuedPoint site S hS F) (eP : c.siteObject ⟶ p.siteObject)
      (eR : c.siteObject ⟶ r.siteObject),
      F.map eP.op p.value = c.value ∧ F.map eR.op r.value = c.value ∧ eP ≫ f = eR ≫ g := by
  have hpa : f.left.hom ≫ q.toBase = p.toBase := congrArg (fun k ↦ k.hom) (Over.w f)
  have hrb : g.left.hom ≫ q.toBase = r.toBase := congrArg (fun k ↦ k.hom) (Over.w g)
  obtain ⟨Ω, instΩ, hΩ, ca, cb, key⟩ :=
    exists_fieldSpec_common site (K := p.carrier) (L := r.carrier) (M := q.carrier)
      p.contained r.contained f.left.hom g.left.hom
  have hbase : cb ≫ r.toBase = ca ≫ p.toBase := by
    rw [← hrb, ← hpa, ← Category.assoc, ← Category.assoc, key]
  set eP : (Over.mk (⟨ca ≫ p.toBase⟩ : site.obj hΩ ⟶ site.obj hS) : BigFppfOver site S hS) ⟶
    p.siteObject := Over.homMk (⟨ca⟩ : site.obj hΩ ⟶ site.obj p.contained)
      (by ext; rfl) with hePdef
  set eR : (Over.mk (⟨ca ≫ p.toBase⟩ : site.obj hΩ ⟶ site.obj hS) : BigFppfOver site S hS) ⟶
    r.siteObject := Over.homMk (⟨cb⟩ : site.obj hΩ ⟶ site.obj r.contained)
      (by ext; exact hbase) with heRdef
  have hpath : eP ≫ f = eR ≫ g := by ext; exact key
  refine ⟨{ carrier := Ω, contained := hΩ, toBase := ca ≫ p.toBase
            value := F.map eP.op p.value }, eP, eR, rfl, ?_, hpath⟩
  show F.map eR.op r.value = F.map eP.op p.value
  rw [← hf, ← hg, ← types_comp_apply (F.map g.op) (F.map eR.op),
    ← types_comp_apply (F.map f.op) (F.map eP.op), ← F.map_comp, ← F.map_comp,
    ← op_comp, ← op_comp, hpath]

/-! ### Points of a pullback, and lifting along an image containment -/

/-- A field-valued point of a presheaf, restricted along a morphism of the site into its site
object. -/
private noncomputable def restrictFieldValuedPoint
    {F G : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (q : FieldValuedPoint site S hS F)
    (p : FieldValuedPoint site S hS G) (f : q.siteObject ⟶ p.siteObject) :
    FieldValuedPoint site S hS G where
  carrier := q.carrier
  field := q.field
  contained := q.contained
  toBase := q.toBase
  value := G.map f.op p.value

/-- If a point of `F` is carried to the class of a field-valued point of `G`, then some
field-valued point of `F` has its value carried to a restriction of that section. -/
private theorem exists_fieldValuedPoint_of_pointsMap_eq
    {F G : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) (a : points site S hS F)
    (q : FieldValuedPoint site S hS G)
    (h : pointsMap site S hS F α a = q.class site S hS G) :
    ∃ (r : FieldValuedPoint site S hS F) (f : r.siteObject ⟶ q.siteObject),
      α.app (Opposite.op r.siteObject) r.value = G.map f.op q.value := by
  obtain ⟨p, hp⟩ := Quot.exists_rep a
  have h' : (FieldValuedPoint.map site S hS F α p).class site S hS G =
      q.class site S hS G := by
    rw [← pointsMap_class site S hS F α p]
    exact (congrArg (pointsMap site S hS F α) hp).trans h
  obtain ⟨c, ⟨f, hf⟩, ⟨g, hg⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff site S hS G
      (FieldValuedPoint.map site S hS F α p) q).1 h'
  exact ⟨restrictFieldValuedPoint c p f, g,
    (map_app_fieldValuedPoint α p f).trans (hf.trans hg.symm)⟩

/-- A pullback projection is surjective on points as soon as the image on points of the other
leg is contained in the image of the leg being pulled back. -/
private theorem isSurjective_pullback_snd_of_range_subset {X Y Z : Over B} (f : X ⟶ Y)
    (g : Z ⟶ Y)
    (hrange : Set.range (pointsMap site S hS Z.left.obj g.left.hom) ⊆
      Set.range (pointsMap site S hS X.left.obj f.left.hom)) :
    IsSurjective site S hS (pullback.snd f.left g.left).hom := by
  intro a
  refine Quot.inductionOn a ?_
  intro p
  obtain ⟨aX, haX⟩ := hrange ⟨p.class site S hS Z.left.obj,
    pointsMap_class site S hS Z.left.obj g.left.hom p⟩
  obtain ⟨r, t, hvalue⟩ := exists_fieldValuedPoint_of_pointsMap_eq f.left.hom aX
    (FieldValuedPoint.map site S hS Z.left.obj g.left.hom p) haX
  set pZ : FieldValuedPoint site S hS Z.left.obj := restrictFieldValuedPoint r p t
    with hpZdef
  have hpullValue : f.left.hom.app (Opposite.op r.siteObject) r.value =
      g.left.hom.app (Opposite.op r.siteObject) pZ.value :=
    hvalue.trans (map_app_fieldValuedPoint g.left.hom p t).symm
  have hXv : X.hom.hom.app (Opposite.op r.siteObject) r.value =
      yonedaEquiv (yonedaEquiv.symm
        (X.hom.hom.app (Opposite.op r.siteObject) r.value)) :=
    (Equiv.apply_symm_apply yonedaEquiv _).symm
  have hZv : Z.hom.hom.app (Opposite.op r.siteObject) pZ.value =
      yonedaEquiv (yonedaEquiv.symm
        (X.hom.hom.app (Opposite.op r.siteObject) r.value)) :=
    ((base_left_hom_app g (T := r.siteObject) pZ.value).symm.trans
      ((congrArg (Y.hom.hom.app (Opposite.op r.siteObject)) hpullValue).symm.trans
        (base_left_hom_app f (T := r.siteObject) r.value))).trans hXv
  set intoX : representableOver (B := B) r.siteObject
    (yonedaEquiv.symm (X.hom.hom.app (Opposite.op r.siteObject) r.value)) ⟶ X :=
    sectionOver r.value hXv with hintoXdef
  set intoZ : representableOver (B := B) r.siteObject
    (yonedaEquiv.symm (X.hom.hom.app (Opposite.op r.siteObject) r.value)) ⟶ Z :=
    sectionOver pZ.value hZv with hintoZdef
  have hcomm : intoX.left ≫ f.left = intoZ.left ≫ g.left := by
    refine ObjectProperty.hom_ext _ ?_
    show yonedaEquiv.symm r.value ≫ f.left.hom = yonedaEquiv.symm pZ.value ≫ g.left.hom
    exact (symm_comp_left_hom f (T := r.siteObject) r.value).trans
      ((congrArg yonedaEquiv.symm hpullValue).trans
        (symm_comp_left_hom g (T := r.siteObject) pZ.value).symm)
  set pP : FieldValuedPoint site S hS (pullback f.left g.left).obj :=
    { carrier := r.carrier
      field := r.field
      contained := r.contained
      toBase := r.toBase
      value := yonedaEquiv (pullback.lift intoX.left intoZ.left hcomm).hom } with hpPdef
  have hw : (pullback.snd f.left g.left).hom.app (Opposite.op r.siteObject) pP.value =
      pZ.value := by
    have hlift := congrArg
      (fun m : (representableOver (B := B) r.siteObject
        (yonedaEquiv.symm (X.hom.hom.app (Opposite.op r.siteObject) r.value))).left ⟶ Z.left ↦
        yonedaEquiv m.hom)
      (pullback.lift_snd intoX.left intoZ.left hcomm)
    refine hlift.trans ?_
    exact Equiv.apply_symm_apply yonedaEquiv pZ.value
  refine ⟨pP.class site S hS (pullback f.left g.left).obj, ?_⟩
  rw [pointsMap_class]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension site S hS Z.left.obj
    ⟨pZ, ⟨𝟙 _, ?_⟩, ⟨t, rfl⟩⟩
  show Z.left.obj.map (𝟙 pZ.siteObject).op
    ((pullback.snd f.left g.left).hom.app (Opposite.op r.siteObject) pP.value) = pZ.value
  rw [op_id, Z.left.obj.map_id]
  exact hw

/-- Over an algebraically closed field, a point of `Z` lifts along a morphism `f : X ⟶ Y`
which is locally of finite type, provided the image on points of `g : Z ⟶ Y` is contained in
that of `f`. -/
theorem exists_lift_of_lft_of_range_subset {X Y Z : Over B} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsLocallyOfFiniteType site S hS f.left.hom)
    (hrange : Set.range (pointsMap site S hS Z.left.obj g.left.hom) ⊆
      Set.range (pointsMap site S hS X.left.obj f.left.hom))
    (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S)
    (z : Z.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))) :
    ∃ x : X.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)),
      f.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) x =
        g.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) z := by
  have hπ : IsLocallyOfFiniteType site S hS (pullback.snd f.left g.left).hom :=
    (isLocallyOfFiniteType_isStableUnderBaseChange site S hS).of_isPullback
      (IsPullback.of_hasPullback f.left g.left) hf
  obtain ⟨w, hw⟩ :=
    (isSurjective_iff_surjective_app_isAlgClosed site S hS
        (pullback f.left g.left).property Z.left.property
        (pullback.snd f.left g.left).hom hπ).1
      (isSurjective_pullback_snd_of_range_subset f g hrange) k hk b z
  refine ⟨(pullback.fst f.left g.left).hom.app
    (Opposite.op (fieldObject (hS := hS) k hk b)) w, ?_⟩
  have hsquare := congrArg
    (fun m : pullback f.left g.left ⟶ Y.left ↦
      m.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) w)
    (pullback.condition (f := f.left) (g := g.left))
  refine Eq.trans ?_ (congrArg
    (g.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b))) hw)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply]
    using hsquare

/-! ### The relations of Stacks 0490 through the endpoint maps -/

variable {R U : Over B}

/-- The first projection of the image of a composable pair under the composed relation is the
target of its first arrow. -/
private theorem composedRelation_fst_app (j : PreRelation R U) {T : BigFppfOver site S hS}
    (c : (pullback j.source j.target).left.obj.obj (Opposite.op T)) :
    (prod.fst : U ⨯ U ⟶ U).left.hom.app (Opposite.op T)
        ((composedRelation j).left.hom.app (Opposite.op T) c) =
      j.target.left.hom.app (Opposite.op T)
        ((pullback.fst j.source j.target).left.hom.app (Opposite.op T) c) :=
  (left_hom_app_of_eq_comp (prod.lift_fst (pullback.fst j.source j.target ≫ j.target)
    (pullback.snd j.source j.target ≫ j.source)) c).trans (comp_left_hom_app _ _ c).symm

/-- The second projection of the image of a composable pair under the composed relation is the
source of its second arrow. -/
private theorem composedRelation_snd_app (j : PreRelation R U) {T : BigFppfOver site S hS}
    (c : (pullback j.source j.target).left.obj.obj (Opposite.op T)) :
    (prod.snd : U ⨯ U ⟶ U).left.hom.app (Opposite.op T)
        ((composedRelation j).left.hom.app (Opposite.op T) c) =
      j.source.left.hom.app (Opposite.op T)
        ((pullback.snd j.source j.target).left.hom.app (Opposite.op T) c) :=
  (left_hom_app_of_eq_comp (prod.lift_snd (pullback.fst j.source j.target ≫ j.target)
    (pullback.snd j.source j.target ≫ j.source)) c).trans (comp_left_hom_app _ _ c).symm

/-- The two arrows of a composable pair match in the middle, and the three relevant endpoints
lie over the image of the pair in the base. -/
private theorem pullback_section_facts (j : PreRelation R U) {T : BigFppfOver site S hS}
    (c : (pullback j.source j.target).left.obj.obj (Opposite.op T)) :
    j.source.left.hom.app (Opposite.op T)
        ((pullback.fst j.source j.target).left.hom.app (Opposite.op T) c) =
      j.target.left.hom.app (Opposite.op T)
        ((pullback.snd j.source j.target).left.hom.app (Opposite.op T) c) ∧
    U.hom.hom.app (Opposite.op T) (j.source.left.hom.app (Opposite.op T)
        ((pullback.snd j.source j.target).left.hom.app (Opposite.op T) c)) =
      (pullback j.source j.target).hom.hom.app (Opposite.op T) c ∧
    U.hom.hom.app (Opposite.op T) (j.target.left.hom.app (Opposite.op T)
        ((pullback.snd j.source j.target).left.hom.app (Opposite.op T) c)) =
      (pullback j.source j.target).hom.hom.app (Opposite.op T) c ∧
    U.hom.hom.app (Opposite.op T) (j.target.left.hom.app (Opposite.op T)
        ((pullback.fst j.source j.target).left.hom.app (Opposite.op T) c)) =
      (pullback j.source j.target).hom.hom.app (Opposite.op T) c :=
  ⟨by rw [comp_left_hom_app, comp_left_hom_app, pullback.condition],
    (base_left_hom_app j.source _).trans (base_left_hom_app (pullback.snd j.source j.target) c),
    (base_left_hom_app j.target _).trans (base_left_hom_app (pullback.snd j.source j.target) c),
    (base_left_hom_app j.target _).trans (base_left_hom_app (pullback.fst j.source j.target) c)⟩

/-- The set-theoretic relation of **Stacks 0490** attached to a pre-relation of algebraic
spaces, written through the endpoint maps of that pre-relation. -/
private theorem setTheoreticRel_presheafPreRelation_iff (j : PreRelation R U) (k : Type u)
    [Field k] (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β}) :
    (presheafPreRelation j).SetTheoreticRel k hk b β x y ↔
      ∃ (r : FieldValuedPoint site S hS R.left.obj)
        (f : r.siteObject ⟶ fieldObject (hS := hS) k hk b),
        j.source.left.hom.app (Opposite.op r.siteObject) r.value =
            U.left.obj.map f.op x.1 ∧
          j.target.left.hom.app (Opposite.op r.siteObject) r.value =
            U.left.obj.map f.op y.1 := by
  have hsrc := presheafPreRelation_source_left j
  have htgt := presheafPreRelation_target_left j
  constructor
  · rintro ⟨r, f, hs, ht⟩
    rw [hsrc] at hs
    rw [htgt] at ht
    exact ⟨r, f, hs, ht⟩
  · rintro ⟨r, f, hs, ht⟩
    rw [← hsrc] at hs
    rw [← htgt] at ht
    exact ⟨r, f, hs, ht⟩

/-- The relation of actual arrows attached to a pre-relation of algebraic spaces, written
through the endpoint maps of that pre-relation. -/
private theorem geometricRel_presheafPreRelation_iff (j : PreRelation R U) (k : Type u)
    [Field k] (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β}) :
    (presheafPreRelation j).GeometricRel k hk b β x y ↔
      ∃ r : R.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)),
        j.source.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) r = x.1 ∧
          j.target.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) r = y.1 := by
  have hsrc := presheafPreRelation_source_left j
  have htgt := presheafPreRelation_target_left j
  constructor
  · rintro ⟨r, hs, ht⟩
    rw [hsrc] at hs
    rw [htgt] at ht
    exact ⟨r, hs, ht⟩
  · rintro ⟨r, hs, ht⟩
    rw [← hsrc] at hs
    rw [← htgt] at ht
    exact ⟨r, hs, ht⟩

/-! ### Pairs of points of `U` over a field-valued point of the base -/

/-- A point of `U` in the fibre over a section of the base, read as a morphism over `B` out of
the representable algebraic space of the corresponding object of the site. -/
private noncomputable def fibrePoint {k : Type u} [Field k]
    {hk : site.Contains (Spec (.of k))} {b : Spec (.of k) ⟶ S}
    {β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))} (U : Over B)
    (x : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β}) :
    representableOver (B := B) (fieldObject (hS := hS) k hk b) (yonedaEquiv.symm β) ⟶ U :=
  sectionOver x.1 (x.2.trans (Equiv.apply_symm_apply yonedaEquiv β).symm)

/-- The field-valued point of `U ×_B U` given by a pair of points of `U` in one fibre. -/
private noncomputable def pairFieldPoint (U : Over B) (k : Type u) [Field k]
    (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β}) :
    FieldValuedPoint site S hS (U ⨯ U : Over B).left.obj where
  carrier := k
  contained := hk
  toBase := b
  value := yonedaEquiv (prod.lift (fibrePoint U x) (fibrePoint U y)).left.hom

private theorem pairFieldPoint_fst (U : Over B) (k : Type u) [Field k]
    (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β}) :
    (prod.fst : U ⨯ U ⟶ U).left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b))
        (pairFieldPoint U k hk b β x y).value = x.1 := by
  refine (left_hom_app_yonedaEquiv (prod.lift (fibrePoint U x) (fibrePoint U y))
    (prod.fst : U ⨯ U ⟶ U)).trans ?_
  rw [prod.lift_fst]
  exact Equiv.apply_symm_apply yonedaEquiv x.1

private theorem pairFieldPoint_snd (U : Over B) (k : Type u) [Field k]
    (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β}) :
    (prod.snd : U ⨯ U ⟶ U).left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b))
        (pairFieldPoint U k hk b β x y).value = y.1 := by
  refine (left_hom_app_yonedaEquiv (prod.lift (fibrePoint U x) (fibrePoint U y))
    (prod.snd : U ⨯ U ⟶ U)).trans ?_
  rw [prod.lift_snd]
  exact Equiv.apply_symm_apply yonedaEquiv y.1

/-- A point of a presheaf mapping to `U ×_B U` is the class of a field-valued point of
`U ×_B U` as soon as the two projections of its value agree with the restrictions of the two
projections of that point. -/
private theorem pointsMap_eq_of_prod_components {F : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ (U ⨯ U : Over B).left.obj) (r : FieldValuedPoint site S hS F)
    (q : FieldValuedPoint site S hS (U ⨯ U : Over B).left.obj)
    (f : r.siteObject ⟶ q.siteObject) {x y : U.left.obj.obj (Opposite.op q.siteObject)}
    (hfst : (prod.fst : U ⨯ U ⟶ U).left.hom.app (Opposite.op r.siteObject)
        (α.app (Opposite.op r.siteObject) r.value) = U.left.obj.map f.op x)
    (hsnd : (prod.snd : U ⨯ U ⟶ U).left.hom.app (Opposite.op r.siteObject)
        (α.app (Opposite.op r.siteObject) r.value) = U.left.obj.map f.op y)
    (hx : (prod.fst : U ⨯ U ⟶ U).left.hom.app (Opposite.op q.siteObject) q.value = x)
    (hy : (prod.snd : U ⨯ U ⟶ U).left.hom.app (Opposite.op q.siteObject) q.value = y) :
    pointsMap site S hS F α (r.class site S hS F) =
      q.class site S hS (U ⨯ U : Over B).left.obj := by
  have hval : α.app (Opposite.op r.siteObject) r.value =
      (U ⨯ U : Over B).left.obj.map f.op q.value :=
    prod_value_ext _ _
      ((hfst.trans (congrArg _ hx.symm)).trans
        (map_app_fieldValuedPoint (prod.fst : U ⨯ U ⟶ U).left.hom q f).symm)
      ((hsnd.trans (congrArg _ hy.symm)).trans
        (map_app_fieldValuedPoint (prod.snd : U ⨯ U ⟶ U).left.hom q f).symm)
  rw [pointsMap_class]
  exact FieldValuedPoint.class_eq_class_of_hasCommonExtension site S hS _
    ⟨FieldValuedPoint.map site S hS F α r,
      FieldValuedPoint.dominates_refl site S hS _ _, ⟨f, hval.symm⟩⟩

/-- A section over the object of the site of a field-valued point of the base whose two
projections are a prescribed pair of points of the fibre is the pair itself, on points. -/
private theorem pointsMap_eq_pairFieldPoint {F : (BigFppfOver site S hS)ᵒᵖ ⥤ Type u}
    (α : F ⟶ (U ⨯ U : Over B).left.obj) {k : Type u} [Field k]
    {hk : site.Contains (Spec (.of k))} {b : Spec (.of k) ⟶ S}
    {β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))}
    (w : F.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β})
    (hfst : (prod.fst : U ⨯ U ⟶ U).left.hom.app
        (Opposite.op (fieldObject (hS := hS) k hk b))
        (α.app (Opposite.op (fieldObject (hS := hS) k hk b)) w) = x.1)
    (hsnd : (prod.snd : U ⨯ U ⟶ U).left.hom.app
        (Opposite.op (fieldObject (hS := hS) k hk b))
        (α.app (Opposite.op (fieldObject (hS := hS) k hk b)) w) = y.1) :
    pointsMap site S hS F α
        ((⟨k, hk, b, w⟩ : FieldValuedPoint site S hS F).class site S hS F) =
      (pairFieldPoint U k hk b β x y).class site S hS (U ⨯ U : Over B).left.obj :=
  pointsMap_eq_of_prod_components α ⟨k, hk, b, w⟩ (pairFieldPoint U k hk b β x y)
    (𝟙 (fieldObject (hS := hS) k hk b))
    (hfst.trans (map_id_app x.1).symm) (hsnd.trans (map_id_app y.1).symm)
    (pairFieldPoint_fst U k hk b β x y) (pairFieldPoint_snd U k hk b β x y)

/-- An arrow of the pre-relation present over the field exhibits the pair of its endpoints as
a point in the image of `j`. -/
private theorem pointsMap_eq_pairFieldPoint_of_geometricRel (j : PreRelation R U) (k : Type u)
    [Field k] (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β})
    (hxy : ∃ r : R.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)),
      j.source.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) r = x.1 ∧
        j.target.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) r = y.1) :
    ∃ r : FieldValuedPoint site S hS R.left.obj,
      pointsMap site S hS R.left.obj j.left.hom (r.class site S hS R.left.obj) =
        (pairFieldPoint U k hk b β y x).class site S hS (U ⨯ U : Over B).left.obj := by
  obtain ⟨v, hs, ht⟩ := hxy
  exact ⟨⟨k, hk, b, v⟩, pointsMap_eq_pairFieldPoint j.left.hom v y x
    ((comp_left_hom_app j (prod.fst : U ⨯ U ⟶ U) v).trans ht)
    ((comp_left_hom_app j (prod.snd : U ⨯ U ⟶ U) v).trans hs)⟩

/-- The image of a point of `U` under the diagonal is the pair of that point with itself. -/
private theorem pointsMap_diag_eq_pairFieldPoint (k : Type u) [Field k]
    (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β}) :
    pointsMap site S hS U.left.obj (diag U).left.hom
        ((⟨k, hk, b, x.1⟩ : FieldValuedPoint site S hS U.left.obj).class
          site S hS U.left.obj) =
      (pairFieldPoint U k hk b β x x).class site S hS (U ⨯ U : Over B).left.obj :=
  pointsMap_eq_pairFieldPoint (diag U).left.hom x.1 x x
    (diag_left_hom_app_fst U x.1) (diag_left_hom_app_snd U x.1)

/-- If a point of `R` goes under `j` to the pair `(y, x)` of points of `U` in one fibre, then
`x` and `y` are related by the set-theoretic relation. -/
private theorem setTheoreticRel_of_pointsMap_eq (j : PreRelation R U) (k : Type u) [Field k]
    (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β})
    (a : points site S hS R.left.obj)
    (h : pointsMap site S hS R.left.obj j.left.hom a =
      (pairFieldPoint U k hk b β y x).class site S hS (U ⨯ U : Over B).left.obj) :
    (presheafPreRelation j).SetTheoreticRel k hk b β x y := by
  obtain ⟨r, f, hv⟩ := exists_fieldValuedPoint_of_pointsMap_eq j.left.hom a _ h
  exact (setTheoreticRel_presheafPreRelation_iff j k hk b β x y).2 ⟨r, f,
    ((comp_left_hom_app j (prod.snd : U ⨯ U ⟶ U) r.value).symm.trans (congrArg _ hv)).trans
      ((map_app_fieldValuedPoint (prod.snd : U ⨯ U ⟶ U).left.hom _ f).trans
        (congrArg (U.left.obj.map f.op) (pairFieldPoint_snd U k hk b β y x))),
    ((comp_left_hom_app j (prod.fst : U ⨯ U ⟶ U) r.value).symm.trans (congrArg _ hv)).trans
      ((map_app_fieldValuedPoint (prod.fst : U ⨯ U ⟶ U).left.hom _ f).trans
        (congrArg (U.left.obj.map f.op) (pairFieldPoint_fst U k hk b β y x)))⟩

/-- A section of `R` over the field whose image under `j` has projections `x` and `y` relates
`x` to `y` by the relation of actual arrows. -/
private theorem geometricRel_of_app_eq (j : PreRelation R U) (k : Type u) [Field k]
    (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β})
    (v : R.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    {z : (U ⨯ U : Over B).left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))}
    (hv : j.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = z)
    (hsnd : (prod.snd : U ⨯ U ⟶ U).left.hom.app
      (Opposite.op (fieldObject (hS := hS) k hk b)) z = x.1)
    (hfst : (prod.fst : U ⨯ U ⟶ U).left.hom.app
      (Opposite.op (fieldObject (hS := hS) k hk b)) z = y.1) :
    (presheafPreRelation j).GeometricRel k hk b β x y :=
  (geometricRel_presheafPreRelation_iff j k hk b β x y).2
    ⟨v, (comp_left_hom_app j (prod.snd : U ⨯ U ⟶ U) v).symm.trans ((congrArg _ hv).trans hsnd),
      (comp_left_hom_app j (prod.fst : U ⨯ U ⟶ U) v).symm.trans ((congrArg _ hv).trans hfst)⟩

/-- A section of `R` over the field with endpoints `x` and `y` relates them after an extension
of the field. -/
private theorem setTheoreticRel_of_app_eq (j : PreRelation R U) (k : Type u) [Field k]
    (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β})
    (v : R.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (hs : j.source.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = x.1)
    (ht : j.target.left.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = y.1) :
    (presheafPreRelation j).SetTheoreticRel k hk b β x y :=
  (setTheoreticRel_presheafPreRelation_iff j k hk b β x y).2
    ⟨⟨k, hk, b, v⟩, 𝟙 (fieldObject (hS := hS) k hk b),
      hs.trans (map_id_app x.1).symm, ht.trans (map_id_app y.1).symm⟩

/-- An arrow of the pre-relation over a field is a section of `R` whose image under `j` has the
projections `y` and `x`; as a point of `R` it maps to the pair `(y, x)`. -/
private theorem pointsMap_eq_of_source_target (j : PreRelation R U)
    (r : FieldValuedPoint site S hS R.left.obj)
    (q : FieldValuedPoint site S hS (U ⨯ U : Over B).left.obj) (f : r.siteObject ⟶ q.siteObject)
    {x y : U.left.obj.obj (Opposite.op q.siteObject)}
    (hs : j.source.left.hom.app (Opposite.op r.siteObject) r.value = U.left.obj.map f.op x)
    (ht : j.target.left.hom.app (Opposite.op r.siteObject) r.value = U.left.obj.map f.op y)
    (hsnd : (prod.snd : U ⨯ U ⟶ U).left.hom.app (Opposite.op q.siteObject) q.value = x)
    (hfst : (prod.fst : U ⨯ U ⟶ U).left.hom.app (Opposite.op q.siteObject) q.value = y) :
    pointsMap site S hS R.left.obj j.left.hom (r.class site S hS R.left.obj) =
      q.class site S hS (U ⨯ U : Over B).left.obj :=
  pointsMap_eq_of_prod_components j.left.hom r q f
    ((comp_left_hom_app j (prod.fst : U ⨯ U ⟶ U) r.value).symm.trans ht)
    ((comp_left_hom_app j (prod.snd : U ⨯ U ⟶ U) r.value).symm.trans hs) hfst hsnd

/-! ### Comparing the two relations over a field -/

/-- An arrow present over the field is in particular an arrow after an extension of it. -/
private theorem setTheoreticRel_of_geometricRel (j : PreRelation R U) (k : Type u) [Field k]
    (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β})
    (hxy : (presheafPreRelation j).GeometricRel k hk b β x y) :
    (presheafPreRelation j).SetTheoreticRel k hk b β x y := by
  obtain ⟨r, hs, ht⟩ := (geometricRel_presheafPreRelation_iff j k hk b β x y).1 hxy
  exact setTheoreticRel_of_app_eq j k hk b β x y r hs ht

/-- Over an algebraically closed field larger than every residue field of a scheme atlas of
`R`, an arrow of the pre-relation available after an extension of the field is already
available over the field itself. -/
private theorem geometricRel_of_setTheoreticRel_of_large (j : PreRelation R U)
    (V : BigFppfOver site S hS) (pV : yoneda.obj V ⟶ R.left.obj)
    (hpVsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme site S hS))) pV)
    (hpVetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme site S hS))) pV)
    (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S)
    (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)))
    (hlarge : Cardinal.aleph0 ⊔
      ⨆ v : (BigFppfOver.toScheme site S hS).obj V,
        Cardinal.mk (((BigFppfOver.toScheme site S hS).obj V).residueField v) <
          Cardinal.mk k)
    (x y : {v : U.left.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b)) //
      U.hom.hom.app (Opposite.op (fieldObject (hS := hS) k hk b)) v = β})
    (hxy : (presheafPreRelation j).SetTheoreticRel k hk b β x y) :
    (presheafPreRelation j).GeometricRel k hk b β x y := by
  obtain ⟨p, f, hs, ht⟩ := (setTheoreticRel_presheafPreRelation_iff j k hk b β x y).1 hxy
  have hpoint : pointsMap site S hS R.left.obj j.left.hom (p.class site S hS R.left.obj) =
      (pairFieldPoint U k hk b β y x).class site S hS (U ⨯ U : Over B).left.obj := by
    exact pointsMap_eq_of_source_target j p _ f hs ht (pairFieldPoint_snd U k hk b β y x)
      (pairFieldPoint_fst U k hk b β y x)
  obtain ⟨z, hz, -⟩ := exists_lift_of_large_field site S hS R.left.property
    (U ⨯ U : Over B).left.property j.left.hom V pV hpVsurj hpVetale k hk b hlarge
    (p.class site S hS R.left.obj) (pairFieldPoint U k hk b β y x).value hpoint
  exact geometricRel_of_app_eq j k hk b β x y z hz (pairFieldPoint_snd U k hk b β y x)
    (pairFieldPoint_fst U k hk b β y x)

/-! ### The three image containments -/

/-- **Stacks 0491, part (2).** A pre-relation *contains the relation images* when its image on
topological points contains the images of the diagonal of `U`, of the flip of the pre-relation
and of the endpoint map on composable pairs of arrows. -/
@[stacks 0491 "part (2): the three image containments"]
noncomputable abbrev PreRelation.ContainsRelationImages (j : PreRelation R U) : Prop :=
  Set.range (pointsMap site S hS U.left.obj (diag U).left.hom) ⊆
      Set.range (pointsMap site S hS R.left.obj j.left.hom) ∧
    Set.range (pointsMap site S hS R.left.obj (flippedRelation j).left.hom) ⊆
      Set.range (pointsMap site S hS R.left.obj j.left.hom) ∧
    Set.range (pointsMap site S hS (pullback j.source j.target).left.obj
        (composedRelation j).left.hom) ⊆
      Set.range (pointsMap site S hS R.left.obj j.left.hom)

/-- **Stacks 0491, parts (1) and (2).** A pre-relation is a set-theoretic pre-equivalence
relation exactly when its image on points contains the images of the diagonal, of the flip and
of the endpoint map on composable pairs. -/
@[stacks 0491 "parts (1) and (2)"]
theorem isSetTheoreticPreEquivalenceRelation_iff_containsRelationImages
    (j : PreRelation R U) :
    IsSetTheoreticPreEquivalenceRelation (presheafPreRelation j) ↔
      j.ContainsRelationImages := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro - ⟨a, rfl⟩
      obtain ⟨p, hp⟩ := exists_geometricRepresentative site S hS U.left.obj a
      have : IsAlgClosed p.val.carrier := p.property
      obtain ⟨r', f, hs, ht⟩ := (setTheoreticRel_presheafPreRelation_iff j p.val.carrier
          p.val.contained p.val.toBase
          (U.hom.hom.app (Opposite.op p.val.siteObject) p.val.value) _ _).1
        ((h p.val.carrier p.val.contained p.val.toBase
          (U.hom.hom.app (Opposite.op p.val.siteObject) p.val.value)).refl
          ⟨p.val.value, rfl⟩)
      refine ⟨r'.class site S hS R.left.obj, ?_⟩
      rw [← hp]
      refine Eq.trans ?_
        (pointsMap_class site S hS U.left.obj (diag U).left.hom p.val).symm
      exact pointsMap_eq_of_source_target j r' _ f hs ht (diag_left_hom_app_snd U p.val.value)
        (diag_left_hom_app_fst U p.val.value)
    · rintro - ⟨a, rfl⟩
      obtain ⟨p, hp⟩ := exists_geometricRepresentative site S hS R.left.obj a
      have : IsAlgClosed p.val.carrier := p.property
      obtain ⟨r', f, hs, ht⟩ := (setTheoreticRel_presheafPreRelation_iff j p.val.carrier
          p.val.contained p.val.toBase
          (R.hom.hom.app (Opposite.op p.val.siteObject) p.val.value) _ _).1
        ((h p.val.carrier p.val.contained p.val.toBase
            (R.hom.hom.app (Opposite.op p.val.siteObject) p.val.value)).symm
          (setTheoreticRel_of_app_eq j p.val.carrier p.val.contained p.val.toBase _
            ⟨_, base_left_hom_app j.source p.val.value⟩
            ⟨_, base_left_hom_app j.target p.val.value⟩ p.val.value rfl rfl))
      refine ⟨r'.class site S hS R.left.obj, ?_⟩
      rw [← hp]
      refine Eq.trans ?_
        (pointsMap_class site S hS R.left.obj (flippedRelation j).left.hom p.val).symm
      exact pointsMap_eq_of_source_target j r' _ f hs ht
        (left_hom_app_of_eq_comp (prod.lift_snd j.source j.target) p.val.value)
        (left_hom_app_of_eq_comp (prod.lift_fst j.source j.target) p.val.value)
    · rintro - ⟨a, rfl⟩
      obtain ⟨p, hp⟩ :=
        exists_geometricRepresentative site S hS (pullback j.source j.target).left.obj a
      have : IsAlgClosed p.val.carrier := p.property
      set c := p.val with hcdef
      set v₁ := (pullback.fst j.source j.target).left.hom.app
        (Opposite.op c.siteObject) c.value with hv₁def
      set v₂ := (pullback.snd j.source j.target).left.hom.app
        (Opposite.op c.siteObject) c.value with hv₂def
      set β := (pullback j.source j.target).hom.hom.app
        (Opposite.op c.siteObject) c.value with hβdef
      obtain ⟨hmid, hx, hy, hw⟩ := pullback_section_facts j c.value
      have hrel₂ := setTheoreticRel_of_app_eq j c.carrier c.contained c.toBase β ⟨_, hx⟩ ⟨_, hy⟩
        v₂ rfl rfl
      have hrel₁ := setTheoreticRel_of_app_eq j c.carrier c.contained c.toBase β ⟨_, hy⟩ ⟨_, hw⟩
        v₁ hmid rfl
      obtain ⟨r', f, hs, ht⟩ := (setTheoreticRel_presheafPreRelation_iff j c.carrier
        c.contained c.toBase β _ _).1 ((h c.carrier c.contained c.toBase β).trans hrel₂ hrel₁)
      refine ⟨r'.class site S hS R.left.obj, ?_⟩
      rw [← hp]
      refine Eq.trans ?_ (pointsMap_class site S hS (pullback j.source j.target).left.obj
        (composedRelation j).left.hom c).symm
      exact pointsMap_eq_of_source_target j r' _ f hs ht (composedRelation_snd_app j c.value)
        (composedRelation_fst_app j c.value)
  · intro h k _ _ hk b β
    refine ⟨fun x ↦ ?_, fun {x y} hxy ↦ ?_, fun {x y z} hxy hyz ↦ ?_⟩
    · obtain ⟨a, ha⟩ := h.1 ⟨(⟨k, hk, b, x.1⟩ :
        FieldValuedPoint site S hS U.left.obj).class site S hS U.left.obj, rfl⟩
      exact setTheoreticRel_of_pointsMap_eq j k hk b β x x a
        (ha.trans (pointsMap_diag_eq_pairFieldPoint k hk b β x))
    · obtain ⟨p, f, hs, ht⟩ := (setTheoreticRel_presheafPreRelation_iff j k hk b β x y).1 hxy
      have hflip : pointsMap site S hS R.left.obj (flippedRelation j).left.hom
          (p.class site S hS R.left.obj) =
            (pairFieldPoint U k hk b β x y).class site S hS (U ⨯ U : Over B).left.obj :=
        pointsMap_eq_of_prod_components (flippedRelation j).left.hom p _ f
          ((left_hom_app_of_eq_comp (prod.lift_fst j.source j.target) p.value).trans hs)
          ((left_hom_app_of_eq_comp (prod.lift_snd j.source j.target) p.value).trans ht)
          (pairFieldPoint_fst U k hk b β x y) (pairFieldPoint_snd U k hk b β x y)
      obtain ⟨a, ha⟩ := h.2.1 ⟨p.class site S hS R.left.obj, rfl⟩
      exact setTheoreticRel_of_pointsMap_eq j k hk b β y x a (ha.trans hflip)
    · obtain ⟨pXY, fXY, hXS, hYT⟩ :=
        (setTheoreticRel_presheafPreRelation_iff j k hk b β x y).1 hxy
      obtain ⟨pYZ, fYZ, hYS, hZT⟩ :=
        (setTheoreticRel_presheafPreRelation_iff j k hk b β y z).1 hyz
      obtain ⟨c, ga, gd, hga, hgd, hpath⟩ := exists_commonExtension_comp_eq
        (FieldValuedPoint.map site S hS R.left.obj j.target.left.hom pXY)
        (⟨k, hk, b, y.1⟩ : FieldValuedPoint site S hS U.left.obj)
        (FieldValuedPoint.map site S hS R.left.obj j.source.left.hom pYZ)
        fXY hYT.symm fYZ hYS.symm
      have hsrc : j.source.left.hom.app (Opposite.op c.siteObject)
          (R.left.obj.map gd.op pYZ.value) = c.value :=
        (map_app_fieldValuedPoint j.source.left.hom pYZ gd).trans hgd
      have htgt : j.target.left.hom.app (Opposite.op c.siteObject)
          (R.left.obj.map ga.op pXY.value) = c.value :=
        (map_app_fieldValuedPoint j.target.left.hom pXY ga).trans hga
      obtain ⟨pv, hpfst, hpsnd⟩ := exists_pullback_section j.source j.target _ _
        (hsrc.trans htgt.symm)
      set cp : FieldValuedPoint site S hS (pullback j.source j.target).left.obj :=
        ⟨c.carrier, c.contained, c.toBase, pv⟩ with hcpdef
      have hcomposed : pointsMap site S hS (pullback j.source j.target).left.obj
          (composedRelation j).left.hom (cp.class site S hS _) =
            (pairFieldPoint U k hk b β z x).class site S hS (U ⨯ U : Over B).left.obj :=
        pointsMap_eq_of_prod_components (composedRelation j).left.hom cp _ (gd ≫ fYZ)
          ((composedRelation_fst_app j pv).trans
            ((congrArg (j.target.left.hom.app (Opposite.op c.siteObject)) hpfst).trans
              (((map_app_fieldValuedPoint j.target.left.hom pYZ gd).trans
                (congrArg (U.left.obj.map gd.op) hZT)).trans (map_comp_app fYZ gd z.1))))
          ((composedRelation_snd_app j pv).trans
            ((congrArg (j.source.left.hom.app (Opposite.op c.siteObject)) hpsnd).trans
              (((map_app_fieldValuedPoint j.source.left.hom pXY ga).trans
                (congrArg (U.left.obj.map ga.op) hXS)).trans
                ((map_comp_app fXY ga x.1).trans
                  (congrArg (fun m : _ ⟶ (fieldObject (hS := hS) k hk b) ↦
                    U.left.obj.map m.op x.1) hpath)))))
          (pairFieldPoint_fst U k hk b β z x) (pairFieldPoint_snd U k hk b β z x)
      obtain ⟨aOut, haOut⟩ := h.2.2 ⟨cp.class site S hS _, rfl⟩
      exact setTheoreticRel_of_pointsMap_eq j k hk b β x z aOut (haOut.trans hcomposed)

/-- The three image containments follow from the relation of actual arrows being an
equivalence relation over every algebraically closed field above a bound below the cutoff:
a point of any of the three sources is represented by a geometric point over such a field. -/
private theorem containsRelationImages_of_geometricRel_equivalence (j : PreRelation R U)
    (κ : Cardinal.{u}) (hκ : κ < site.cutoff)
    (hlarge : ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
      (b : Spec (.of k) ⟶ S)
      (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))),
      κ < Cardinal.mk k → Equivalence ((presheafPreRelation j).GeometricRel k hk b β)) :
    j.ContainsRelationImages := by
  refine ⟨?_, ?_, ?_⟩
  · rintro - ⟨aU, rfl⟩
    obtain ⟨p, hp, hcard⟩ := exists_geometricPoint_image_eq_of_lt_mk U.left.obj aU κ hκ
    have : IsAlgClosed p.val.carrier := p.property
    obtain ⟨rR, hmap⟩ := pointsMap_eq_pairFieldPoint_of_geometricRel j p.val.carrier
      p.val.contained p.val.toBase
      (U.hom.hom.app (Opposite.op p.val.siteObject) p.val.value)
      ⟨p.val.value, rfl⟩ ⟨p.val.value, rfl⟩
      ((geometricRel_presheafPreRelation_iff j p.val.carrier p.val.contained p.val.toBase
          (U.hom.hom.app (Opposite.op p.val.siteObject) p.val.value) _ _).1
        ((hlarge p.val.carrier p.val.contained p.val.toBase
          (U.hom.hom.app (Opposite.op p.val.siteObject) p.val.value) hcard).refl
          ⟨p.val.value, rfl⟩))
    refine ⟨rR.class site S hS R.left.obj, hmap.trans ?_⟩
    rw [← hp]
    exact (pointsMap_diag_eq_pairFieldPoint p.val.carrier p.val.contained p.val.toBase
      (U.hom.hom.app (Opposite.op p.val.siteObject) p.val.value) ⟨p.val.value, rfl⟩).symm
  · rintro - ⟨aR, rfl⟩
    obtain ⟨p, hp, hcard⟩ := exists_geometricPoint_image_eq_of_lt_mk R.left.obj aR κ hκ
    have : IsAlgClosed p.val.carrier := p.property
    set r := p.val with hrdef
    set β := R.hom.hom.app (Opposite.op r.siteObject) r.value with hβdef
    have hx : U.hom.hom.app (Opposite.op r.siteObject)
        (j.source.left.hom.app (Opposite.op r.siteObject) r.value) = β :=
      base_left_hom_app j.source r.value
    have hy : U.hom.hom.app (Opposite.op r.siteObject)
        (j.target.left.hom.app (Opposite.op r.siteObject) r.value) = β :=
      base_left_hom_app j.target r.value
    obtain ⟨rR, hmap⟩ := pointsMap_eq_pairFieldPoint_of_geometricRel j r.carrier r.contained
      r.toBase β ⟨_, hy⟩ ⟨_, hx⟩
      ((geometricRel_presheafPreRelation_iff j r.carrier r.contained r.toBase β _ _).1
        ((hlarge r.carrier r.contained r.toBase β hcard).symm
          ((geometricRel_presheafPreRelation_iff j r.carrier r.contained r.toBase β
            ⟨_, hx⟩ ⟨_, hy⟩).2 ⟨r.value, rfl, rfl⟩)))
    refine ⟨rR.class site S hS R.left.obj, hmap.trans ?_⟩
    rw [← hp]
    refine Eq.trans ?_
      (pointsMap_class site S hS R.left.obj (flippedRelation j).left.hom r).symm
    exact (pointsMap_eq_pairFieldPoint (flippedRelation j).left.hom r.value ⟨_, hx⟩ ⟨_, hy⟩
      (left_hom_app_of_eq_comp (prod.lift_fst j.source j.target) r.value)
      (left_hom_app_of_eq_comp (prod.lift_snd j.source j.target) r.value)).symm
  · rintro - ⟨aP, rfl⟩
    obtain ⟨p, hp, hcard⟩ := exists_geometricPoint_image_eq_of_lt_mk
      (pullback j.source j.target).left.obj aP κ hκ
    have : IsAlgClosed p.val.carrier := p.property
    set c := p.val with hcdef
    set v₁ := (pullback.fst j.source j.target).left.hom.app
      (Opposite.op c.siteObject) c.value with hv₁def
    set v₂ := (pullback.snd j.source j.target).left.hom.app
      (Opposite.op c.siteObject) c.value with hv₂def
    set β := (pullback j.source j.target).hom.hom.app
      (Opposite.op c.siteObject) c.value with hβdef
    obtain ⟨hmid, hx, hy, hw⟩ := pullback_section_facts j c.value
    obtain ⟨rR, hmap⟩ := pointsMap_eq_pairFieldPoint_of_geometricRel j c.carrier c.contained
      c.toBase β ⟨_, hx⟩ ⟨_, hw⟩
      ((geometricRel_presheafPreRelation_iff j c.carrier c.contained c.toBase β _ _).1
        ((hlarge c.carrier c.contained c.toBase β hcard).trans
          ((geometricRel_presheafPreRelation_iff j c.carrier c.contained c.toBase β
            ⟨_, hx⟩ ⟨_, hy⟩).2 ⟨v₂, rfl, rfl⟩)
          ((geometricRel_presheafPreRelation_iff j c.carrier c.contained c.toBase β
            ⟨_, hy⟩ ⟨_, hw⟩).2 ⟨v₁, hmid, rfl⟩)))
    refine ⟨rR.class site S hS R.left.obj, hmap.trans ?_⟩
    rw [← hp]
    refine Eq.trans ?_ (pointsMap_class site S hS (pullback j.source j.target).left.obj
      (composedRelation j).left.hom c).symm
    exact (pointsMap_eq_pairFieldPoint (composedRelation j).left.hom c.value ⟨_, hw⟩ ⟨_, hx⟩
      (composedRelation_fst_app j c.value) (composedRelation_snd_app j c.value)).symm

/-- **Stacks 0491, parts (2) and (3).** The three image containments hold exactly when the
relation cut out by the arrows already present over `k` is an equivalence relation for every
algebraically closed field `k` in the site above one cardinal strictly below the size cutoff
of the site. -/
@[stacks 0491 "parts (2) and (3)"]
theorem containsRelationImages_iff_exists_geometricRel_equivalence (j : PreRelation R U) :
    j.ContainsRelationImages ↔
      ∃ κ : Cardinal.{u}, κ < site.cutoff ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k]
        (hk : site.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S)
        (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))),
        κ < Cardinal.mk k → Equivalence ((presheafPreRelation j).GeometricRel k hk b β) := by
  constructor
  · intro himages
    obtain ⟨V, pV, hpVsurj, hpVetale⟩ := R.left.property.exists_atlas
    refine ⟨Cardinal.aleph0 ⊔ ⨆ v : (BigFppfOver.toScheme site S hS).obj V,
        Cardinal.mk (((BigFppfOver.toScheme site S hS).obj V).residueField v),
      (aleph0_sup_iSup_residueField_le_size
        ((BigFppfOver.toScheme site S hS).obj V)).trans_lt V.left.property, ?_⟩
    intro k _ _ hk b β hlarge
    have hpre :=
      (isSetTheoreticPreEquivalenceRelation_iff_containsRelationImages j).2 himages k hk b β
    have key := geometricRel_of_setTheoreticRel_of_large j V pV hpVsurj hpVetale k hk b β hlarge
    exact ⟨fun x ↦ key x x (hpre.refl x),
      fun {x y} hxy ↦ key y x (hpre.symm (setTheoreticRel_of_geometricRel j k hk b β x y hxy)),
      fun {x y z} hxy hyz ↦ key x z (hpre.trans (setTheoreticRel_of_geometricRel j k hk b β x y hxy)
        (setTheoreticRel_of_geometricRel j k hk b β y z hyz))⟩
  · rintro ⟨κ, hκ, hlarge⟩
    exact containsRelationImages_of_geometricRel_equivalence j κ hκ hlarge

/-- **Stacks 0491, part (4).** For a pre-relation whose source and target are locally of
finite type no cardinal bound is needed: the set-theoretic pre-equivalence condition is
equivalent to the relation of actual arrows being an equivalence relation over *every*
algebraically closed field in the site. -/
@[stacks 0491 "part (4)"]
theorem isSetTheoreticPreEquivalenceRelation_iff_geometricRel_equivalence
    (j : PreRelation R U) (_hs : IsLocallyOfFiniteType site S hS j.source.left.hom)
    (ht : IsLocallyOfFiniteType site S hS j.target.left.hom) :
    IsSetTheoreticPreEquivalenceRelation (presheafPreRelation j) ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (hk : site.Contains (Spec (.of k)))
        (b : Spec (.of k) ⟶ S)
        (β : B.obj.obj (Opposite.op (fieldObject (hS := hS) k hk b))),
        Equivalence ((presheafPreRelation j).GeometricRel k hk b β) := by
  constructor
  · intro h k _ _ hk b β
    have himages :=
      (isSetTheoreticPreEquivalenceRelation_iff_containsRelationImages j).1 h
    have hj : IsLocallyOfFiniteType site S hS j.left.hom :=
      isLocallyOfFiniteType_of_comp site S hS R.left.property (U ⨯ U : Over B).left.property
        U.left.property j.left.hom (prod.fst : U ⨯ U ⟶ U).left.hom ht
    refine ⟨fun x ↦ ?_, fun {x y} hxy ↦ ?_, fun {x y z} hxy hyz ↦ ?_⟩
    · obtain ⟨v, hv⟩ := exists_lift_of_lft_of_range_subset j (diag U) hj himages.1 k hk b x.1
      exact geometricRel_of_app_eq j k hk b β x x v hv (diag_left_hom_app_snd U x.1)
        (diag_left_hom_app_fst U x.1)
    · obtain ⟨u, hus, hut⟩ := (geometricRel_presheafPreRelation_iff j k hk b β x y).1 hxy
      obtain ⟨v, hv⟩ := exists_lift_of_lft_of_range_subset j (flippedRelation j) hj
        himages.2.1 k hk b u
      exact geometricRel_of_app_eq j k hk b β y x v hv
        ((left_hom_app_of_eq_comp (prod.lift_snd j.source j.target) u).trans hut)
        ((left_hom_app_of_eq_comp (prod.lift_fst j.source j.target) u).trans hus)
    · obtain ⟨u, hus, hut⟩ := (geometricRel_presheafPreRelation_iff j k hk b β x y).1 hxy
      obtain ⟨w, hws, hwt⟩ := (geometricRel_presheafPreRelation_iff j k hk b β y z).1 hyz
      obtain ⟨pv, hpfst, hpsnd⟩ :=
        exists_pullback_section j.source j.target w u (hws.trans hut.symm)
      obtain ⟨v, hv⟩ := exists_lift_of_lft_of_range_subset j (composedRelation j) hj
        himages.2.2 k hk b pv
      exact geometricRel_of_app_eq j k hk b β x z v hv
        ((composedRelation_snd_app j pv).trans ((congrArg _ hpsnd).trans hus))
        ((composedRelation_fst_app j pv).trans ((congrArg _ hpfst).trans hwt))
  · intro h
    refine (isSetTheoreticPreEquivalenceRelation_iff_containsRelationImages j).2
      (containsRelationImages_of_geometricRel_equivalence j 0
        (Cardinal.aleph0_pos.trans site.aleph0_lt_cutoff) ?_)
    intro k _ _ hk b β _
    exact h k hk b β

end AlgebraicGeometry.Space

end
