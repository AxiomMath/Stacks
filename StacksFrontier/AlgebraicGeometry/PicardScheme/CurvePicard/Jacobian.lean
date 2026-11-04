module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponentProper
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.GroupScheme
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Jacobian of a smooth projective curve over a separably closed field

Let `X` be a smooth projective curve over a separably closed field `k`. The degree-zero points of
the Picard functor form a subgroup functor, represented by the degree-zero component
`Pic^0_{X/k}` of the Picard scheme ([Stacks, Tag 0B9Z]); so `Pic^0_{X/k}` is a group scheme over
`k` (clause (3) of [Stacks, Tag 0BA0]), the **Jacobian** of `X`. It is an abelian variety
(Definition [Stacks, Tag 03RO]): it is smooth over `k` (it is open in the Picard scheme, which is
covered by opens of the smooth `Hilb^g_{X/k}`), proper (separated as a group scheme over a field,
[Stacks, Tag 047L], and universally closed, being isomorphic to `Pic^g_{X/k}`, the image of the
proper `Hilb^g_{X/k}` under the surjective Abel map), irreducible (same reason), hence
geometrically integral over the separably closed field `k` ([Stacks, Tag 020J]).

## Main definitions

* `Stacks.PicardFunctor.degreeZeroGrpFunctor`: the degree-zero points, as a presheaf of groups.
* `Stacks.PicardFunctor.jacobianGrp`: the Jacobian, a group object in schemes over `k`.

## Main results

* `Stacks.PicardFunctor.isAbelianVariety_jacobian`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable]

/-- **The degree-zero points of the Picard functor form a subgroup.** -/
def degreeZeroAddSubgroup (T : BigFppfOver B (Spec (.of k)) hk) :
    AddSubgroup ((picardFunctor B hX hk f).obj (op T)) where
  carrier := (curveDegreeSubfunctor B hX hk f σ hσ 0).obj (op T)
  zero_mem' t := by
    change fibreEuler _ _ _ _ _ _ _ _ _ _ - fibreEuler _ _ _ _ _ _ _ _ _ _ = 0
    exact sub_self _
  add_mem' {a b} ha hb t := by
    change curveFibreDegree B hX hk f σ hσ T (a + b) t = 0
    rw [curveFibreDegree, fibreDegree_add]
    exact (congrArg₂ (· + ·) (ha t) (hb t)).trans (add_zero 0)
  neg_mem' {a} ha t := by
    change curveFibreDegree B hX hk f σ hσ T (-a) t = 0
    have h := fibreDegree_add B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
      T (-a) a t
    rw [neg_add_cancel] at h
    have h0 : curveFibreDegree B hX hk f σ hσ T 0 t = 0 := sub_self _
    have ha' := ha t
    simp only [curveFibreDegree] at h0 ha' ⊢
    change fibreDegree _ _ _ _ _ _ _ _ _ _ = 0 at ha'
    omega

/-- Restriction of degree-zero points along a morphism of test schemes, as a homomorphism. -/
def degreeZeroMap {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T) :
    degreeZeroAddSubgroup B hX hk f σ hσ T →+ degreeZeroAddSubgroup B hX hk f σ hσ T' where
  toFun x := ⟨(picardFunctor B hX hk f).map g.op x.1,
    (curveDegreeSubfunctor B hX hk f σ hσ 0).map g.op x.2⟩
  map_zero' := Subtype.ext (picardFunctor_map_zero B hX hk f g)
  map_add' x y := Subtype.ext (picardFunctor_map_add B hX hk f g x.1 y.1)

/-- **The degree-zero points of the Picard functor, as a presheaf of groups** (written
multiplicatively). -/
def degreeZeroGrpFunctor : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (Multiplicative (degreeZeroAddSubgroup B hX hk f σ hσ T.unop))
  map {T T'} g := GrpCat.ofHom (degreeZeroMap B hX hk f σ hσ g.unop).toMultiplicative
  map_id T := by
    ext x
    exact Subtype.ext (FunctorToTypes.map_id_apply (picardFunctor B hX hk f) _)
  map_comp g g' := by
    ext x
    exact Subtype.ext (FunctorToTypes.map_comp_apply (picardFunctor B hX hk f) g g' _)

/-- The underlying presheaf of sets of the degree-zero group presheaf is the degree-zero
subfunctor. -/
def degreeZeroGrpFunctorForgetIso :
    degreeZeroGrpFunctor B hX hk f σ hσ ⋙ forget GrpCat ≅
      (curveDegreeSubfunctor B hX hk f σ hσ 0).toFunctor :=
  NatIso.ofComponents (fun T => Equiv.toIso
    { toFun := fun x => ⟨(Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2⟩
      invFun := fun y => Multiplicative.ofAdd
        (⟨y.1, y.2⟩ : degreeZeroAddSubgroup B hX hk f σ hσ T.unop)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })
    (fun _ => rfl)

/-- **`Pic^0_{X/k}` represents the degree-zero group presheaf.** -/
def degreeZeroGrpRepresentableBy :
    (degreeZeroGrpFunctor B hX hk f σ hσ ⋙ forget GrpCat).RepresentableBy
      (picardSchemeDegreeComponent B hX hk f σ hσ 0) :=
  (degreeComponentRepresentableBy B hX hk f σ hσ 0).ofIso
    (degreeZeroGrpFunctorForgetIso B hX hk f σ hσ).symm

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- **The group object structure of `Pic^0_{X/k}`** in the big fppf site over `k`. -/
@[instance_reducible]
def jacobianGrpObj : GrpObj (picardSchemeDegreeComponent B hX hk f σ hσ 0) :=
  GrpObj.ofRepresentableBy _ (degreeZeroGrpFunctor B hX hk f σ hσ)
    (degreeZeroGrpRepresentableBy B hX hk f σ hσ)

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- **The Jacobian `Pic^0_{X/k}` of the curve**, as a group object in schemes over `k`. -/
def jacobianGrp : Grp (Over (Spec (.of k))) :=
  haveI := preservesFiniteProducts_overPost_bigFppfInclusion B (Spec (.of k)) hk
  letI := jacobianGrpObj B hX hk f σ hσ
  (Over.post B.inclusion).mapGrp.obj (Grp.mk (picardSchemeDegreeComponent B hX hk f σ hσ 0))

/-- The structure morphism of the Jacobian `jacobianGrp` to `Spec k` is the image under the
inclusion of the big fppf site of the structure morphism of `Pic^0_{X/k}`. -/
theorem jacobianGrp_X_hom :
    (jacobianGrp B hX hk f σ hσ).X.hom =
      B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom :=
  rfl

variable [IsSepClosed k]

include σ hσ in
/-- **The Jacobian of a smooth projective curve over a separably closed field is an abelian
variety** (Definition [Stacks, Tag 03RO]): a proper, geometrically integral group scheme. -/
@[sga "2 XII 5.11" "(6), special case", sga "6 XII 1.2" "special case"]
theorem isAbelianVariety_jacobian :
    IsAbelianVariety k (jacobianGrp B hX hk f σ hσ).X := by
  set J := (jacobianGrp B hX hk f σ hσ).X
  have hhom : J.hom = B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom := rfl
  obtain ⟨hUC, hcpt, hirr⟩ := universallyClosed_picardSchemeDegreeComponent_zero B hX hk f σ hσ
  have : CompactSpace J.left := hcpt
  have : IrreducibleSpace J.left := hirr
  have : SmoothOfRelativeDimension (genus (B.inclusion.map f)) J.hom :=
    smoothOfRelativeDimension_picardSchemeDegreeComponent B hX hk f σ hσ 0
  have : Smooth J.hom := SmoothOfRelativeDimension.smooth (genus (B.inclusion.map f)) _
  have : UniversallyClosed J.hom := hUC
  have : CompactSpace (Spec (.of k)) := inferInstance
  have : QuasiCompact J.hom := (quasiCompact_iff_compactSpace J.hom).2 hcpt
  have : J.left.IsSeparated := isSeparated_of_groupScheme_over_field (jacobianGrp B hX hk f σ hσ)
  have : IsSeparated (J.hom ≫ terminal.from _) := by
    rw [Subsingleton.elim (J.hom ≫ terminal.from _) (terminal.from J.left)]
    infer_instance
  have : IsSeparated J.hom := IsSeparated.of_comp J.hom (terminal.from _)
  have : IsProper J.hom := ⟨⟩
  have : IsReduced J.left := isReduced_of_smooth J.hom
  have : IsIntegral J.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : GeometricallyIrreducible J.hom :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k J.left J.hom
  have : GeometricallyIntegral J.hom := Stacks.AbelMap.geometricallyIntegral_of_smooth J.hom
  exact { toIsProperVariety := { }, toGeometricallyIntegral := inferInstance }

end Stacks.PicardFunctor

end
