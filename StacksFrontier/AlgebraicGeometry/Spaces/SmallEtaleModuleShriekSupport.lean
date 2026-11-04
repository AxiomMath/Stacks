module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleShriekForgetStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareSndLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtensionByZeroSupported
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The support of an extension by zero along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`, and let `T` be a
subset of `|Y|`.  If an object `K` of `D(𝒪_X)` is supported on `|f|⁻¹T` in the sense of
Stacks 08GF, then its extension by zero `f_!K` is supported on `T`.

Equation 08GU computes the stalk of `f_!𝒢` at a geometric point `x̄` of `Y` as the direct sum,
over the lifts of `x̄` to `X`, of the stalks of `𝒢` at those lifts.  A lift maps to `x̄` under
`AlgebraicGeometry.Space.geometricPointMap`, so its image point maps to the image point of `x̄`;
if that image point is outside `T` then the lift's image point is outside `|f|⁻¹T`, hence
outside the support of `𝒢`, so every summand vanishes and with it the stalk.

## Main definitions

* `AlgebraicGeometry.Space.stalkSetEquivPresheafFiber`: the set-valued geometric stalk of
  Stacks 04JY at a geometric point is the fibre of the presheaf at the point of the small étale
  site attached to it.

## Main results

* `AlgebraicGeometry.Space.subsingleton_presheafFiber_iff_subsingleton_stalkSet`: the fibre of a
  presheaf of sets at that point is a subsingleton exactly when the geometric stalk is.
* `AlgebraicGeometry.Space.isZero_sheafFiber_iff_subsingleton_stalkSet`: the stalk of an abelian
  sheaf at the point of the small étale site determined by a geometric point is a zero object
  exactly when the set-valued geometric stalk of Stacks 04JY is a subsingleton.
* `AlgebraicGeometry.Space.notMem_supportOfSheaf_iff_forall_isZero_sheafFiber`: a point of `|F|`
  is outside the support of an abelian sheaf exactly when the stalk at every geometric point over
  it vanishes.
* `AlgebraicGeometry.Space.cohomologySupportedOn_mapDerivedCategory_etaleModuleLowerShriek`: the
  extension by zero of an object of `D(𝒪_X)` supported on `|f|⁻¹T` is supported on `T`.

## Implementation notes

The stalk is taken at coefficients in `AddCommGrpCat.{u}`, the universe of the sections of the
structure sheaf.  The small étale neighbourhoods of a geometric point form a category whose
objects lie in `Type (u + 1)`, so `AddCommGrpCat.{u}` has no colimits of that shape; the fibre at
the point of the site is instead a colimit over the elements of the geometric fibre, which needs
no smallness hypothesis, and the two indexings are identified by
`AlgebraicGeometry.Space.neighborhoodFiberElementsEquiv`.

`T` is an arbitrary subset of `|Y|`: neither closedness nor any finiteness is assumed.

## References

* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre at the point of the site and the set-valued geometric stalk -/

section Bridge

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The set-valued geometric stalk of Stacks 04JY at a geometric point is the fibre of the
presheaf at the point of the small étale site attached to it, at the universe of the sections of
the structure sheaf. -/
@[sga "4½ Arcata 2.3.2" "more general"]
def stalkSetEquivPresheafFiber (x : GeometricPoint B S hS F)
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :
    stalkSet x P ≃ (etaleSitePoint B S hS F x hF).presheafFiber.obj P :=
  letI D := (CategoryOfElements.π (etaleSitePoint B S hS F x hF).fiber).op ⋙ P
  (Equiv.ofBijective _ (Functor.bijective_colimitTypePrecomp
      (neighborhoodFiberElementsEquiv B S hS F x).functor.op D)).trans
    (Types.colimitEquivColimitType D).symm

/-- The fibre of a presheaf of sets at the point of the small étale site attached to a geometric
point is a subsingleton exactly when the set-valued geometric stalk of Stacks 04JY is. -/
theorem subsingleton_presheafFiber_iff_subsingleton_stalkSet (x : GeometricPoint B S hS F)
    (P : (SmallEtale B S hS F)ᵒᵖ ⥤ Type u) :
    Subsingleton ((etaleSitePoint B S hS F x hF).presheafFiber.obj P) ↔
      Subsingleton (stalkSet x P) :=
  (stalkSetEquivPresheafFiber B S hS F hF x P).subsingleton_congr.symm

/-- The stalk of an abelian sheaf at the point of the small étale site determined by a geometric
point vanishes exactly when the set-valued geometric stalk of Stacks 04JY is a subsingleton, at
the universe of the sections of the structure sheaf. -/
theorem isZero_sheafFiber_iff_subsingleton_stalkSet (x : GeometricPoint B S hS F)
    (A : Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}) :
    IsZero ((etaleSitePoint B S hS F x hF).sheafFiber.obj A) ↔
      Subsingleton (stalkSet x (A.obj ⋙ forget AddCommGrpCat.{u})) := by
  rw [isZero_addCommGrpCat_iff_subsingleton]
  refine Iff.trans ?_ (subsingleton_presheafFiber_iff_subsingleton_stalkSet B S hS F hF x
    (A.obj ⋙ forget AddCommGrpCat.{u}))
  exact (((etaleSitePoint B S hS F x hF).presheafFiberCompIso
    (forget AddCommGrpCat.{u})).app A.obj).symm.toEquiv.subsingleton_congr

/-- A point of `|F|` is outside the support of an abelian sheaf, in the sense of Stacks 04KA,
exactly when the stalk at the point of the small étale site of every geometric point over it
vanishes. -/
theorem notMem_supportOfSheaf_iff_forall_isZero_sheafFiber
    (A : Sheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u}) (y : points B S hS F) :
    y ∉ supportOfSheaf B S hS F A ↔
      ∀ p : GeometricPoint B S hS F, p.LiesOver y →
        IsZero ((etaleSitePoint B S hS F p hF).sheafFiber.obj A) := by
  simp only [mem_supportOfSheaf_iff_exists, not_exists, not_and, not_not]
  exact forall_congr' fun p => imp_congr_right fun _ =>
    (isZero_sheafFiber_iff_subsingleton_stalkSet B S hS F hF p A).symm

end Bridge

/-! ### The support of an extension by zero -/

section Shriek

attribute [local instance] HasDerivedCategory.standard

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- Applying a morphism of presheaves to a field-valued point whose section has been replaced by
one lying over it returns the original point. -/
private theorem fieldValuedPoint_map_lift (q : FieldValuedPoint B S hS Y.1)
    (w : X.1.obj (op (FieldValuedPoint.siteObject B S hS Y.1 q)))
    (hw : f.hom.app (op (FieldValuedPoint.siteObject B S hS Y.1 q)) w = q.value) :
    FieldValuedPoint.map B S hS X.1 f.hom
        { carrier := q.carrier, field := q.field, contained := q.contained,
          toBase := q.toBase, value := w } = q := by
  obtain ⟨c, cont, tb, v⟩ := q
  revert w hw
  simp only [FieldValuedPoint.siteObject]
  intro w hw
  rw [← hw]
  rfl

/-- If an object `K` of `D(𝒪_X)` is supported on `|f|⁻¹T` in the sense of Stacks 08GF, then its
extension by zero along the étale morphism `f` is supported on `T`. -/
@[stacks 08GU "the support of an extension by zero of an object of the derived category"]
theorem cohomologySupportedOn_mapDerivedCategory_etaleModuleLowerShriek
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (T : Set (points B S hS Y.1))
    (hK : CohomologySupportedOn B S hS X.1 X.2 (pointsMap B S hS X.1 f.hom ⁻¹' T) K) :
    CohomologySupportedOn B S hS Y.1 Y.2 T
      ((etaleModuleLowerShriek B S hS f hf).mapDerivedCategory.obj K) := by
  intro i
  have he := ((etaleModuleLowerShriek B S hS f hf).mapDerivedCategoryHomologyIso i).app K
  have h2 : supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).obj
            ((etaleModuleLowerShriek B S hS f hf).mapDerivedCategory.obj K))) =
      supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf (etaleRingSheaf B S hS Y)).obj
          ((etaleModuleLowerShriek B S hS f hf).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj K))) :=
    supportOfSheaf_eq_of_iso B S hS Y he
  exact h2.subset.trans
    (supportOfSheaf_toSheaf_etaleModuleLowerShriek_subset B S hS f hf _ T (hK i))

end Shriek

end AlgebraicGeometry.Space

end
