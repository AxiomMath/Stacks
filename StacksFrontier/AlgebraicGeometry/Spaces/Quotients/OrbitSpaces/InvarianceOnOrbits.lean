module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.OrbitSpaces.OrbitSeparation
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafCondition

/-!
# Set-theoretic invariance is constancy on orbits

Fix a scheme `S` in a big fppf site `B` and a presheaf `Z` on the big fppf site of `S`, and
let `j : R ⟶ U ×_Z U` be a pre-relation. A morphism `φ : U ⟶ X` to an algebraic space is
set-theoretically invariant under `j` — it identifies the two endpoints of every arrow of
`j` between points over an algebraically closed field — exactly when, over every
algebraically closed field over the base, the induced map on points is constant on the
orbits of `j`.

The two conditions differ only in that an orbit is cut out by chains of arrows which are
allowed to appear after an extension of the field. Invariance is applied over an algebraic
closure of that extension, which is again a field of the site, and the resulting equality of
sections descends to the original field because the spectrum of a field extension is a
one-element fpqc covering and an algebraic space is separated for every fpqc covering.

## Main results

* `AlgebraicGeometry.Space.isSetTheoreticallyInvariant_iff_eq_of_mem_orbit`: **Stacks
  048W**, set-theoretic invariance is constancy on orbits.
* `AlgebraicGeometry.Space.eq_comp_of_weaklyEquivalent`: a set-theoretically invariant
  morphism is constant on weak orbits, which need no field extension.

## Implementation notes

The codomain `X` carries `AlgebraicGeometry.IsAlgebraicSpace`, as in the source, where every
object in sight is an algebraic space over the base. It is used exactly once, through
`AlgebraicGeometry.IsAlgebraicSpace.isSeparatedFor_fpqc`: an equality of sections of `X` over
an algebraic closure of an extension field has to be brought back to the original field, and
a field extension is not an fppf covering, only an fpqc one. The base `Z` and the two
objects `R`, `U` of `CategoryTheory.Over Z` stay arbitrary presheaves, matching
`AlgebraicGeometry.Space.IsSetTheoreticallyInvariant` and
`AlgebraicGeometry.Space.PreRelation.orbit`.

The algebraically closed extension of a field-valued point is its algebraic closure; the
spectrum of an algebraic extension stays inside the size cutoff of the site, so the
resulting point is again a field-valued point, and a geometric point because the closure is
algebraically closed.

## References

* [Stacks Project, Tag 048W](https://stacks.math.columbia.edu/tag/048W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : Over Z}
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The algebraic closure of a field-valued point -/

/-- The spectrum of an algebraic closure of the field of a field-valued point is again an
object of the site: an algebraic extension does not increase cardinality past the cutoff. -/
theorem contains_spec_algClosure (q : FieldValuedPoint B S hS Z) :
    B.Contains (Spec (.of (AlgebraicClosure q.carrier))) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit q.contained
    (by
      calc Cardinal.mk (AlgebraicClosure q.carrier)
          ≤ max (Cardinal.mk q.carrier) Cardinal.aleph0 :=
            Algebra.IsAlgebraic.cardinalMk_le_max q.carrier (AlgebraicClosure q.carrier)
        _ = max Cardinal.aleph0 (Cardinal.mk q.carrier) := max_comm _ _)

/-- The field extension from the field of a field-valued point to its algebraic closure. -/
noncomputable abbrev algClosureSpecMap (q : FieldValuedPoint B S hS Z) :
    Spec (.of (AlgebraicClosure q.carrier)) ⟶ Spec (.of q.carrier) :=
  Spec.map (CommRingCat.ofHom (algebraMap q.carrier (AlgebraicClosure q.carrier)))

/-- The object of the site given by the algebraic closure of the field of a field-valued
point, over the base through the point's own structure morphism. -/
noncomputable abbrev algClosureSiteObject (q : FieldValuedPoint B S hS Z) :
    BigFppfOver B S hS :=
  Over.mk (⟨algClosureSpecMap q ≫ q.toBase⟩ :
    B.obj (contains_spec_algClosure q) ⟶ B.obj hS)

/-- The field extension to the algebraic closure, as a morphism of the objects of the
site. -/
noncomputable def algClosureHom (q : FieldValuedPoint B S hS Z) :
    algClosureSiteObject q ⟶ q.siteObject B S hS Z :=
  Over.homMk (⟨algClosureSpecMap q⟩ :
    B.obj (contains_spec_algClosure q) ⟶ B.obj q.contained) rfl

/-- The restriction of a field-valued point to an algebraic closure of its field. -/
noncomputable def algClosurePoint (q : FieldValuedPoint B S hS Z) :
    FieldValuedPoint B S hS Z where
  carrier := AlgebraicClosure q.carrier
  contained := contains_spec_algClosure q
  toBase := algClosureSpecMap q ≫ q.toBase
  value := Z.map (algClosureHom q).op q.value

/-- The algebraic closure of a field-valued point is a geometric point. -/
private noncomputable def algClosureGeometricPoint (q : FieldValuedPoint B S hS Z) :
    GeometricPoint B S hS Z :=
  ⟨algClosurePoint q, AlgebraicClosure.isAlgClosed q.carrier⟩

/-- The field extension to the algebraic closure, read as a morphism out of the object of the
site cut out by the resulting field-valued point. -/
private noncomputable abbrev algClosureArrow (q : FieldValuedPoint B S hS Z) :
    (algClosurePoint q).siteObject B S hS Z ⟶ q.siteObject B S hS Z :=
  algClosureHom q

/-- Restrict a point of `U` over a field-valued point of `Z` to the algebraic closure of
that field. -/
private noncomputable def extendTestPoint (q : FieldValuedPoint B S hS Z)
    (x : TestPoint (q.siteObject B S hS Z) (yonedaEquiv.symm q.value) U) :
    TestPoint ((algClosurePoint q).siteObject B S hS Z)
      (yonedaEquiv.symm (algClosurePoint q).value) U :=
  ⟨yoneda.map (algClosureArrow q) ≫ x.1, by
    rw [Category.assoc, x.2]
    exact yonedaEquiv_symm_naturality_left (algClosureArrow q) Z q.value⟩

private theorem extendTestPoint_val (q : FieldValuedPoint B S hS Z)
    (x : TestPoint (q.siteObject B S hS Z) (yonedaEquiv.symm q.value) U) :
    (extendTestPoint q x).1 = yoneda.map (algClosureArrow q) ≫ x.1 := rfl

/-- An arrow of a pre-relation between two points over a field-valued point restricts to an
arrow between their restrictions to the algebraic closure of that field. -/
private theorem rel_algClosure (j : PreRelation R U) (q : FieldValuedPoint B S hS Z)
    {x y : TestPoint (q.siteObject B S hS Z) (yonedaEquiv.symm q.value) U}
    (h : j.Rel (yonedaEquiv.symm q.value) x y) :
    j.Rel (yonedaEquiv.symm (algClosurePoint q).value)
      (extendTestPoint q x) (extendTestPoint q y) := by
  obtain ⟨r, hrt, hrs⟩ := h
  refine ⟨⟨yoneda.map (algClosureArrow q) ≫ r.1, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, r.2]
    exact yonedaEquiv_symm_naturality_left (algClosureArrow q) Z q.value
  · rw [extendTestPoint_val, Category.assoc, hrt]
  · rw [extendTestPoint_val, Category.assoc, hrs]

/-- Weak equivalence of two points over a field-valued point passes to their restrictions to
the algebraic closure of that field. -/
private theorem weaklyEquivalent_algClosure (j : PreRelation R U)
    (q : FieldValuedPoint B S hS Z)
    {x y : TestPoint (q.siteObject B S hS Z) (yonedaEquiv.symm q.value) U}
    (h : j.WeaklyEquivalent q x y) :
    j.WeaklyEquivalent (algClosurePoint q) (extendTestPoint q x) (extendTestPoint q y) := by
  change Relation.EqvGen (j.Rel (yonedaEquiv.symm q.value)) x y at h
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (rel_algClosure j q hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- A morphism of field spectra occurring between two objects of the site cut out by
field-valued points is a one-element fpqc covering. -/
theorem singleton_mem_fpqc_of_fieldValuedPointHom
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p q : FieldValuedPoint B S hS G)
    (α : p.siteObject B S hS G ⟶ q.siteObject B S hS G) :
    Presieve.singleton α ∈
      Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) (q.siteObject B S hS G) := by
  rw [Precoverage.mem_comap_iff, Presieve.map_singleton]
  exact fpqc_singleton_of_fieldSpecHom (K := q.carrier) (L := p.carrier)
    ((BigFppfOver.toScheme B S hS).map α)

/-! ### Set-theoretic invariance and orbits -/

/-- A set-theoretically invariant morphism takes the same value at two points of `U` over a
geometric point of `Z` which are joined by a chain of arrows of the pre-relation over the
field of that geometric point. -/
theorem eq_comp_of_weaklyEquivalent (j : PreRelation R U) (φ : U.left ⟶ X)
    (hφ : IsSetTheoreticallyInvariant j φ) (p : GeometricPoint B S hS Z)
    {x y : TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U}
    (h : j.WeaklyEquivalent p.val x y) : x.1 ≫ φ = y.1 ≫ φ := by
  change Relation.EqvGen (j.Rel (yonedaEquiv.symm p.val.value)) x y at h
  induction h with
  | rel a b hab => exact hφ p a b hab
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A morphism from `U` to an algebraic space is set-theoretically invariant under a
pre-relation if and only if, for every algebraically closed field over the base, the induced map
on the points of `U` over that field is constant on the orbits of the pre-relation. -/
@[stacks 048W]
theorem isSetTheoreticallyInvariant_iff_eq_of_mem_orbit (hX : IsAlgebraicSpace B S hS X)
    (j : PreRelation R U) (φ : U.left ⟶ X) :
    IsSetTheoreticallyInvariant j φ ↔
      ∀ (p : GeometricPoint B S hS Z)
        (x y : TestPoint (p.val.siteObject B S hS Z) (yonedaEquiv.symm p.val.value) U),
        y ∈ j.orbit p x → x.1 ≫ φ = y.1 ≫ φ := by
  constructor
  · intro hφ p x y hy
    obtain ⟨q, f, -, x', y', hx, hy', hweak⟩ := hy
    have heq : (extendTestPoint q x').1 ≫ φ = (extendTestPoint q y').1 ≫ φ :=
      eq_comp_of_weaklyEquivalent j φ hφ (algClosureGeometricPoint q)
        (weaklyEquivalent_algClosure j q hweak)
    have hxα : yoneda.map (algClosureArrow q ≫ f) ≫ x.1 = (extendTestPoint q x').1 := by
      rw [extendTestPoint_val, hx, Functor.map_comp, Category.assoc]
    have hyα : yoneda.map (algClosureArrow q ≫ f) ≫ y.1 = (extendTestPoint q y').1 := by
      rw [extendTestPoint_val, hy', Functor.map_comp, Category.assoc]
    have hres : yoneda.map (algClosureArrow q ≫ f) ≫ x.1 ≫ φ =
        yoneda.map (algClosureArrow q ≫ f) ≫ y.1 ≫ φ := by
      rw [← Category.assoc, ← Category.assoc, hxα, hyα]
      exact heq
    apply yonedaEquiv.injective
    refine Presieve.isSeparatedFor_singleton.1 (hX.isSeparatedFor_fpqc
      (singleton_mem_fpqc_of_fieldValuedPointHom (algClosurePoint q) p.val
        (algClosureArrow q ≫ f))) ?_
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    exact congrArg yonedaEquiv hres
  · intro h p x y hrel
    exact h p x y ⟨p.val, 𝟙 _, by simp, x, y, by simp, by simp,
      Relation.EqvGen.rel _ _ hrel⟩

end AlgebraicGeometry.Space

end
