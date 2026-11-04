module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.LocalProperties.Reduced
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedBaseChange
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Products of geometrically reduced schemes

A fibre product over a field with a geometrically reduced factor is reduced: at every point
above a geometrically reduced point of one factor, and globally when the other factor is
reduced. The product of two geometrically reduced schemes is geometrically reduced, and over a
perfect field the product of two reduced schemes is reduced.

## Main results

* `AlgebraicGeometry.isReduced_stalk_pullback_of_isGeometricallyReducedAt` gives reducedness of
  the local ring of the product at each point above a geometrically reduced point.
* `AlgebraicGeometry.isReduced_pullback`: a product over a field is reduced when its first
  factor is geometrically reduced and its second factor is reduced.
* `AlgebraicGeometry.geometricallyReduced_pullback_over_field`: the product over a field of two
  geometrically reduced schemes is geometrically reduced.
* `AlgebraicGeometry.isReduced_pullback_over_perfectField`: the product over a perfect field of
  two reduced schemes is reduced.

## Implementation notes

Schemes over the field are represented by their structure morphisms to its spectrum, and their
product over the field by Mathlib's categorical pullback, whose structure morphism is either
projection followed by the corresponding structure morphism. Reducedness at a point is stated
as reducedness of the corresponding stalk.

## References

* [Stacks Project, Tag 035Z](https://stacks.math.columbia.edu/tag/035Z)
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

universe u

/-- A product with a reduced scheme is reduced at every point above a geometrically reduced
point of the other factor. -/
@[stacks 035Z "reduced_at_points_over_x", ega "IV 4.6.1" "more general", ega "IV 4.6.12" "partial"]
public theorem isReduced_stalk_pullback_of_isGeometricallyReducedAt
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (x : X)
    (hX : IsGeometricallyReducedAt f x) [IsReduced Y]
    (z : (pullback f g : Scheme)) (hz : pullback.fst f g z = x) :
    _root_.IsReduced ((pullback f g).presheaf.stalk z) := by
  subst x
  let pX : pullback f g ⟶ X := pullback.fst f g
  let pY : pullback f g ⟶ Y := pullback.snd f g
  let R := (Spec (.of k)).presheaf.stalk (f.base (pX.base z))
  let A := X.presheaf.stalk (pX.base z)
  let B := Y.presheaf.stalk (pY.base z)
  let C := (pullback f g).presheaf.stalk z
  let : Algebra k R := StructureSheaf.stalkAlgebra k (f.base (pX.base z))
  let : Algebra R A := (f.stalkMap (pX.base z)).hom.toAlgebra
  let hq : (pX ≫ f).base z = (pY ≫ g).base z :=
    congrArg (fun m : pullback f g ⟶ Spec (.of k) => m.base z) pullback.condition
  let : Algebra R B :=
    ((eqToHom (congrArg (Spec (.of k)).presheaf.stalk hq)) ≫
      g.stalkMap (pY.base z)).hom.toAlgebra
  let : Algebra k A := ((f.stalkMap (pX.base z)).hom.comp
    (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base (pX.base z))))).toAlgebra
  let : Algebra k B := ((algebraMap R B).comp (algebraMap k R)).toAlgebra
  let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' rfl
  have hgeom : Algebra.IsGeometricallyReduced k A :=
    (isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk f
      (pullback.fst f g z)).mp hX
  have haux := BaseChangeStalk.pullback_stalk_isLocalization f g z
  change ∃ φ : TensorProduct R A B →+* C, _ ∧ _ ∧
    (let : Algebra (TensorProduct R A B) C := φ.toAlgebra
     ∃ M : Submonoid (TensorProduct R A B), IsLocalization M C) at haux
  obtain ⟨φ, _, _, M, hM⟩ := haux
  have hqclosed : f.base (pX.base z) = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have halg : Function.Bijective (algebraMap k R) := by
    let eR : R ≅ .of k :=
      (Spec (.of k)).presheaf.stalkCongr (Inseparable.of_eq hqclosed) ≪≫
        stalkClosedPointIso (.of k)
    have heq : (algebraMap k R) = eR.inv.hom := by
      ext s
      show (StructureSheaf.toStalk k (f.base (pX.base z))).hom s = _
      dsimp only [eR, Iso.trans_inv]
      rw [stalkClosedPointIso_inv]
      show (StructureSheaf.toStalk k (f.base (pX.base z))).hom s =
        (StructureSheaf.toStalk k (IsLocalRing.closedPoint k) ≫
          (Spec (.of k)).presheaf.stalkSpecializes (Inseparable.of_eq hqclosed).le).hom s
      exact congrArg
        (fun h : .of k ⟶ (Spec (.of k)).presheaf.stalk (f.base (pX.base z)) => h.hom s)
        (StructureSheaf.toStalk_stalkSpecializes (R := k) (Inseparable.of_eq hqclosed).le).symm
    exact heq ▸ ConcreteCategory.bijective_of_isIso eR.inv
  let : TensorProduct.CompatibleSMul k R A B := ⟨fun r a b ↦ by
    obtain ⟨s, rfl⟩ := halg.2 r
    rw [IsScalarTower.algebraMap_smul R s a, IsScalarTower.algebraMap_smul R s b,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul]⟩
  have : _root_.IsReduced (TensorProduct k A B) := isReduced_of_injective
    (Algebra.TensorProduct.comm k A B).toRingHom (Algebra.TensorProduct.comm k A B).injective
  have : _root_.IsReduced (TensorProduct R A B) := isReduced_of_injective
    (Algebra.TensorProduct.equivOfCompatibleSMul k R R A B).toRingHom
    (Algebra.TensorProduct.equivOfCompatibleSMul k R R A B).injective
  let : Algebra (TensorProduct R A B) C := φ.toAlgebra
  let : IsLocalization M C := hM
  apply isReduced_localizationPreserves M C
  simpa only [R, A, B, pX, pY, Scheme.Hom.comp_apply] using
    (inferInstance : _root_.IsReduced (TensorProduct R A B))

/-- The fibre product of a geometrically reduced scheme and a reduced scheme over a field is
reduced. -/
@[stacks 035Z "reduced_product", ega "IV 4.6.1" "(b) ⇒ (a)"]
public theorem isReduced_pullback
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [GeometricallyReduced f] [IsReduced Y] :
    IsReduced (pullback f g) :=
  @AlgebraicGeometry.isReduced_of_isReduced_stalk _ fun z ↦
    isReduced_stalk_pullback_of_isGeometricallyReducedAt f g _
      ((geometricallyReduced_iff_forall_isGeometricallyReducedAt f).mp inferInstance _) z rfl

/-- Comparison of the product of two base changes with the base change of the product. -/
private noncomputable def baseChangeProductIso {S X Y T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : T ⟶ S) :
    pullback (pullback.snd f h) (pullback.snd g h) ≅
      pullback (pullback.fst f g ≫ f) h :=
  (pullbackLeftPullbackSndIso f h (pullback.snd g h)) ≪≫
    pullback.congrHom rfl pullback.condition.symm ≪≫
    (pullbackAssoc f g g h).symm ≪≫
    pullback.congrHom pullback.condition.symm rfl

/-- The fibre product over a field of two geometrically reduced schemes is geometrically
reduced. -/
@[stacks 035Z "geometrically_reduced_product", ega "IV 4.6.5"]
public theorem geometricallyReduced_pullback_over_field
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [GeometricallyReduced f] [GeometricallyReduced g] :
    GeometricallyReduced (pullback.fst f g ≫ f) := by
  rw [geometricallyReduced_iff,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let h : Spec (.of K) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k K))
  have : GeometricallyReduced (pullback.snd f h) :=
    (geometricallyReduced_iff_baseChange_fieldExtension k K f).mp inferInstance
  have : GeometricallyReduced (pullback.snd g h) :=
    (geometricallyReduced_iff_baseChange_fieldExtension k K g).mp inferInstance
  have : IsReduced (pullback g h) := inferInstance
  exact ObjectProperty.prop_of_iso _ (baseChangeProductIso f g h)
    (isReduced_pullback (pullback.snd f h) (pullback.snd g h))

/-- The fibre product of two reduced schemes over a perfect field is reduced. -/
@[stacks 035Z "perfect_field_reduced_product",
  ega "IV 4.6.1" "special case",
  sga "3 VIA 0.2" "partial"]
public theorem isReduced_pullback_over_perfectField
    {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsReduced X] [IsReduced Y] :
    IsReduced (pullback f g) := by
  let := geometricallyReduced_of_isReduced f
  let := geometricallyReduced_of_isReduced g
  exact (geometricallyReduced_pullback_over_field f g).geometrically_isReduced
    (𝟙 _) (𝟙 _) (pullback.fst f g ≫ f) .of_id_fst

end AlgebraicGeometry
