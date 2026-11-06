module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.FibreDegreeAdditive
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.GroupScheme
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Clopen
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# `Pic⁰` of a curve is an open and closed subgroup scheme

Let `X` be a smooth projective geometrically irreducible curve over a field `k` with a rational
point, whose Picard functor is representable. The fibre degree is additive
(`Stacks.PicardFunctor.fibreDegree_add`), so the degree-zero points form a subgroup of every
value of the Picard functor, and these subgroups make up a presheaf of groups
`Stacks.PicardFunctor.fibreDegreeZeroGrpFunctor`. It is represented by the degree-zero component
`Pic⁰_{X/k}`, which therefore carries a group object structure for which its inclusion into the
Picard group scheme is a homomorphism. Carried to schemes over `k`, this is
`Stacks.PicardFunctor.picardDegreeZeroSubgroup`, an open subgroup scheme of the Picard group
scheme `Stacks.PicardFunctor.picardGrp`, whose inclusion is also a closed immersion
(`Stacks.PicardFunctor.picardDegreeZeroClosedSubgroup`): clause (3) of [Stacks, Tag 0BA0].

## Main definitions

* `Stacks.PicardFunctor.fibreDegreeZeroGrpFunctor`: the presheaf of degree-zero subgroups.
* `Stacks.PicardFunctor.picardDegreeZeroSubgroup`: `Pic⁰_{X/k}` as an `OpenSubgroupScheme` of the
  Picard group scheme.
* `Stacks.PicardFunctor.picardDegreeZeroClosedSubgroup`: the same as a `ClosedSubgroupScheme`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe w v u

namespace Stacks.PicardFunctor

/-! ### Homomorphisms between represented presheaves of groups -/

section GroupObject

variable {C : Type v} [Category.{u} C] [CartesianMonoidalCategory C]

/-- The identification of a represented presheaf of groups with the morphisms into the
representing group object is multiplicative. -/
theorem homEquiv'_mul_ofRepresentableBy {A : C} (F : Cᵒᵖ ⥤ GrpCat.{w})
    (α : (F ⋙ forget _).RepresentableBy A) {Y : C} (a b : Y ⟶ A) :
    letI := GrpObj.ofRepresentableBy A F α
    α.homEquiv' (a * b) = α.homEquiv' a * α.homEquiv' b := by
  let := GrpObj.ofRepresentableBy A F α
  show α.homEquiv' (lift a b ≫
    α.homEquiv'.symm (α.homEquiv' (fst A A) * α.homEquiv' (snd A A))) = _
  rw [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, ← α.homEquiv'_comp,
    ← α.homEquiv'_comp, lift_fst, lift_snd]

/-- The identification of a represented presheaf of groups with the morphisms into the
representing group object preserves the unit. -/
theorem homEquiv'_one_ofRepresentableBy {A : C} (F : Cᵒᵖ ⥤ GrpCat.{w})
    (α : (F ⋙ forget _).RepresentableBy A) {Y : C} :
    letI := GrpObj.ofRepresentableBy A F α
    α.homEquiv' (1 : Y ⟶ A) = 1 := by
  let := GrpObj.ofRepresentableBy A F α
  show α.homEquiv' (toUnit Y ≫ α.homEquiv'.symm 1) = 1
  rw [α.homEquiv'_comp, Equiv.apply_symm_apply, map_one]

/-- **A morphism between representing objects which induces a homomorphism of the represented
presheaves of groups is a homomorphism of group objects.** -/
theorem isMonHom_of_representableBy {A A' : C} (F G : Cᵒᵖ ⥤ GrpCat.{w})
    (αF : (F ⋙ forget _).RepresentableBy A) (αG : (G ⋙ forget _).RepresentableBy A')
    (τ : F ⟶ G) (j : A ⟶ A')
    (hj : ∀ {Y : C} (ψ : Y ⟶ A), αG.homEquiv' (ψ ≫ j) = τ.app (op Y) (αF.homEquiv' ψ)) :
    letI := GrpObj.ofRepresentableBy A F αF
    letI := GrpObj.ofRepresentableBy A' G αG
    IsMonHom j := by
  let := GrpObj.ofRepresentableBy A F αF
  let := GrpObj.ofRepresentableBy A' G αG
  have h1 : (1 : 𝟙_ C ⟶ A) ≫ j = 1 := by
    apply αG.homEquiv'.injective
    rw [hj, homEquiv'_one_ofRepresentableBy, map_one, homEquiv'_one_ofRepresentableBy]
  have hm : ∀ {Y : C} (a b : Y ⟶ A), (a * b) ≫ j = (a ≫ j) * (b ≫ j) := by
    intro Y a b
    apply αG.homEquiv'.injective
    rw [hj, homEquiv'_mul_ofRepresentableBy, map_mul, ← hj, ← hj,
      homEquiv'_mul_ofRepresentableBy]
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one, h1]
  · rw [MonObj.mul_eq_mul (M := A), hm, Hom.mul_def]
    congr 1
    ext <;> simp

end GroupObject

/-! ### The presheaf of degree-zero subgroups -/

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]

/-- The restriction maps of the Picard functor, as homomorphisms. -/
def picardMapAddHom {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T) :
    (picardFunctor B hX hk f).obj (op T) →+ (picardFunctor B hX hk f).obj (op T') where
  toFun := (picardFunctor B hX hk f).map g.op
  map_zero' := picardFunctor_map_zero B hX hk f g
  map_add' := picardFunctor_map_add B hX hk f g

/-- **The degree-zero subgroup of a value of the Picard functor**: the points of degree zero on
every fibre. -/
def fibreDegreeZeroAddSubgroup (T : BigFppfOver B (Spec (.of k)) hk) :
    AddSubgroup ((picardFunctor B hX hk f).obj (op T)) where
  carrier := {ξ | ∀ t, curveFibreDegree B hX hk f σ hσ T ξ t = 0}
  add_mem' {ξ ζ} hξ hζ t := by
    rw [curveFibreDegree, fibreDegree_add, ← curveFibreDegree, ← curveFibreDegree, hξ, hζ,
      add_zero]
  zero_mem' t := fibreDegree_zero B hX hk f σ hσ _ T t
  neg_mem' {ξ} hξ t := by
    rw [curveFibreDegree, fibreDegree_neg, ← curveFibreDegree, hξ, neg_zero]

/-- A point lies in the degree-zero subgroup if and only if it has degree zero on every fibre. -/
theorem mem_degreeZeroAddSubgroup {T : BigFppfOver B (Spec (.of k)) hk}
    (ξ : (picardFunctor B hX hk f).obj (op T)) :
    ξ ∈ fibreDegreeZeroAddSubgroup B hX hk f σ hσ T ↔
      ∀ t, curveFibreDegree B hX hk f σ hσ T ξ t = 0 :=
  Iff.rfl

/-- The restriction maps of the Picard functor send points of degree zero to points of degree
zero. -/
theorem picardFunctor_map_mem_degreeZeroAddSubgroup {T T' : BigFppfOver B (Spec (.of k)) hk}
    (g : T' ⟶ T) {ξ : (picardFunctor B hX hk f).obj (op T)}
    (hξ : ξ ∈ fibreDegreeZeroAddSubgroup B hX hk f σ hσ T) :
    (picardFunctor B hX hk f).map g.op ξ ∈ fibreDegreeZeroAddSubgroup B hX hk f σ hσ T' := by
  intro t
  rw [curveFibreDegree, fibreDegree_map, ← curveFibreDegree]
  exact hξ _

/-- The restriction maps between degree-zero subgroups. -/
def fibreDegreeZeroMap {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T) :
    fibreDegreeZeroAddSubgroup B hX hk f σ hσ T →+ fibreDegreeZeroAddSubgroup B hX hk f σ hσ T' :=
  ((picardMapAddHom B hX hk f g).comp
    (fibreDegreeZeroAddSubgroup B hX hk f σ hσ T).subtype).codRestrict _
      fun ξ => picardFunctor_map_mem_degreeZeroAddSubgroup B hX hk f σ hσ g ξ.2

/-- **The presheaf of degree-zero subgroups of the Picard functor**, read multiplicatively. -/
def fibreDegreeZeroGrpFunctor : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj T := GrpCat.of (Multiplicative (fibreDegreeZeroAddSubgroup B hX hk f σ hσ T.unop))
  map {T T'} g := GrpCat.ofHom (fibreDegreeZeroMap B hX hk f σ hσ g.unop).toMultiplicative
  map_id T := by
    ext ξ
    exact Subtype.ext ((picardFunctor B hX hk f).map_id_apply _ _)
  map_comp {T T' T''} g g' := by
    ext ξ
    exact Subtype.ext ((picardFunctor B hX hk f).map_comp_apply g g' _)

/-- The inclusion of the presheaf of degree-zero subgroups into the Picard functor read as a
presheaf of groups. -/
def degreeZeroGrpFunctorι :
    fibreDegreeZeroGrpFunctor B hX hk f σ hσ ⟶ picardGrpFunctor B hX hk f where
  app T := GrpCat.ofHom (((picardFunctorAddEquiv B hX hk f T.unop).toAddMonoidHom.comp
    (fibreDegreeZeroAddSubgroup B hX hk f σ hσ T.unop).subtype).toMultiplicative)
  naturality {T T'} g := by
    ext ξ
    exact (ConcreteCategory.congr_hom
      ((picardFunctorIsoPicardAddFunctor B hX hk f).hom.naturality g) ξ.toAdd.1)

/-! ### `Pic⁰_{X/k}` represents the degree-zero subgroups -/

section Representable

variable [(picardFunctor B hX hk f).IsRepresentable]

omit [GeometricallyIrreducible (B.inclusion.map f)] in
/-- A morphism into `Pic^d_{X/k}`, followed by the inclusion, classifies a point of degree `d`. -/
theorem curveFibreDegree_picardHomEquiv_comp_ι {d : ℤ} {T : BigFppfOver B (Spec (.of k)) hk}
    (ψ : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ d) :
    ∀ t, curveFibreDegree B hX hk f σ hσ T
      (picardHomEquiv B hX hk f (ψ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d)) t = d :=
  (exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ _ d).1 ⟨ψ, rfl⟩

/-- The morphism into `Pic⁰_{X/k}` classifying a point of degree zero. -/
def degreeZeroLift {T : BigFppfOver B (Spec (.of k)) hk} (ξ : (picardFunctor B hX hk f).obj (op T))
    (hξ : ∀ t, curveFibreDegree B hX hk f σ hσ T ξ t = 0) :
    T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0 :=
  ((exists_comp_picardSchemeDegreeComponentι_iff B hX hk f σ hσ
    ((picardHomEquiv B hX hk f).symm ξ) 0).2
    (by rw [Equiv.apply_symm_apply]; exact hξ)).choose

omit [GeometricallyIrreducible (B.inclusion.map f)] in
/-- The morphism into `Pic⁰_{X/k}` classifying a point of degree zero, followed by the inclusion
into `Pic_{X/k}`, is the morphism classifying that point. -/
@[reassoc]
theorem degreeZeroLift_ι {T : BigFppfOver B (Spec (.of k)) hk}
    (ξ : (picardFunctor B hX hk f).obj (op T))
    (hξ : ∀ t, curveFibreDegree B hX hk f σ hσ T ξ t = 0) :
    degreeZeroLift B hX hk f σ hσ ξ hξ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ 0 =
      (picardHomEquiv B hX hk f).symm ξ :=
  Exists.choose_spec (p := fun g => g ≫ _ = _) _

/-- **`Pic⁰_{X/k}` represents the presheaf of degree-zero subgroups**: a morphism
`T ⟶ Pic⁰_{X/k}` is the same as a point of `Pic_{X/k}(T)` of degree zero on every fibre. -/
def degreeZeroRepresentableBy :
    (fibreDegreeZeroGrpFunctor B hX hk f σ hσ ⋙ forget _).RepresentableBy
      (picardSchemeDegreeComponent B hX hk f σ hσ 0) where
  homEquiv {T} :=
    { toFun := fun ψ => Multiplicative.ofAdd
        ⟨picardHomEquiv B hX hk f (ψ ≫ picardSchemeDegreeComponentι B hX hk f σ hσ 0),
          curveFibreDegree_picardHomEquiv_comp_ι B hX hk f σ hσ ψ⟩
      invFun := fun ξ => degreeZeroLift B hX hk f σ hσ ξ.toAdd.1 ξ.toAdd.2
      left_inv := fun ψ => by
        rw [← cancel_mono (picardSchemeDegreeComponentι B hX hk f σ hσ 0)]
        refine (degreeZeroLift_ι B hX hk f σ hσ _ _).trans ?_
        exact (picardHomEquiv B hX hk f).symm_apply_apply _
      right_inv := fun ξ => by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        change picardHomEquiv B hX hk f (degreeZeroLift B hX hk f σ hσ ξ.toAdd.1 ξ.toAdd.2 ≫ _) = _
        exact (congrArg (picardHomEquiv B hX hk f)
          (degreeZeroLift_ι B hX hk f σ hσ _ ξ.toAdd.2)).trans (Equiv.apply_symm_apply _ _) }
  homEquiv_comp {T T'} g ψ := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change picardHomEquiv B hX hk f ((g ≫ ψ) ≫ _) =
      (picardFunctor B hX hk f).map g.op (picardHomEquiv B hX hk f (ψ ≫ _))
    rw [Category.assoc, (picardFunctor B hX hk f).representableBy.homEquiv_comp]

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- **The group object structure of `Pic⁰_{X/k}`** in the big fppf site over `k`, from the
presheaf of degree-zero subgroups it represents. -/
@[instance_reducible]
def degreeZeroGrpObj : GrpObj (picardSchemeDegreeComponent B hX hk f σ hσ 0) :=
  GrpObj.ofRepresentableBy _ (fibreDegreeZeroGrpFunctor B hX hk f σ hσ)
    (degreeZeroRepresentableBy B hX hk f σ hσ)

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- **The inclusion `Pic⁰_{X/k} ⟶ Pic_{X/k}` is a homomorphism of group objects.** -/
theorem isMonHom_picardDegreeComponentι :
    letI := picardGrpObj B hX hk f
    letI := degreeZeroGrpObj B hX hk f σ hσ
    IsMonHom (picardSchemeDegreeComponentι B hX hk f σ hσ 0) :=
  isMonHom_of_representableBy _ _ (degreeZeroRepresentableBy B hX hk f σ hσ)
    (picardGrpRepresentableBy B hX hk f) (degreeZeroGrpFunctorι B hX hk f σ hσ) _ fun _ => rfl

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- **`Pic⁰_{X/k}` as a group scheme over `k`.** -/
def picardDegreeZeroGrp : Grp (Over (B.inclusion.obj (B.obj hk))) :=
  haveI := preservesFiniteProducts_overPost_bigFppfInclusion B (Spec (.of k)) hk
  letI := degreeZeroGrpObj B hX hk f σ hσ
  (Over.post B.inclusion).mapGrp.obj (Grp.mk (picardSchemeDegreeComponent B hX hk f σ hσ 0))

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- The inclusion of `Pic⁰_{X/k}` into the Picard group scheme, as a homomorphism of group
schemes over `k`. -/
def picardDegreeZeroGrpι : picardDegreeZeroGrp B hX hk f σ hσ ⟶ picardGrp B hX hk f :=
  haveI := preservesFiniteProducts_overPost_bigFppfInclusion B (Spec (.of k)) hk
  letI := picardGrpObj B hX hk f
  letI := degreeZeroGrpObj B hX hk f σ hσ
  haveI := isMonHom_picardDegreeComponentι B hX hk f σ hσ
  (Over.post B.inclusion).mapGrp.map (Grp.homMk (picardSchemeDegreeComponentι B hX hk f σ hσ 0))

/-- The underlying morphism of schemes of the inclusion of `Pic⁰_{X/k}` is the open immersion of
the degree-zero locus. -/
theorem picardDegreeZeroGrpι_hom_left :
    (picardDegreeZeroGrpι B hX hk f σ hσ).hom.hom.left = (picardDegreeLocus B hX hk f σ hσ 0).ι :=
  inclusion_map_picardSchemeDegreeComponentι B hX hk f σ hσ 0

/-- **Stacks Project, Tag 0BA0, clause (3), the open half: `Pic⁰_{X/k}` is an open subgroup scheme
of the Picard group scheme.** -/
def picardDegreeZeroSubgroup : OpenSubgroupScheme (picardGrp B hX hk f) :=
  ⟨picardDegreeZeroGrp B hX hk f σ hσ, picardDegreeZeroGrpι B hX hk f σ hσ, by
    rw [picardDegreeZeroGrpι_hom_left]
    exact (inferInstance : IsOpenImmersion (picardDegreeLocus B hX hk f σ hσ 0).ι)⟩

/-- The underlying morphism of schemes of the inclusion of the open subgroup scheme `Pic⁰_{X/k}`
is the open immersion of the degree-zero locus. -/
theorem picardDegreeZeroSubgroup_ι_hom_left :
    (picardDegreeZeroSubgroup B hX hk f σ hσ).ι.hom.hom.left =
      (picardDegreeLocus B hX hk f σ hσ 0).ι :=
  picardDegreeZeroGrpι_hom_left B hX hk f σ hσ

/-- The image of `Pic⁰_{X/k}` in the Picard scheme is the degree-zero locus. -/
theorem range_picardDegreeZeroSubgroup_ι :
    Set.range (picardDegreeZeroSubgroup B hX hk f σ hσ).ι.hom.hom.left.base =
      (picardDegreeLocus B hX hk f σ hσ 0 : Set (picardScheme B hX hk f)) := by
  rw [picardDegreeZeroSubgroup_ι_hom_left]
  exact Scheme.Opens.range_ι _

/-- The inclusion of `Pic⁰_{X/k}` into the Picard group scheme is a closed immersion. -/
theorem isClosedImmersion_picardDegreeZeroSubgroup_ι :
    IsClosedImmersion (picardDegreeZeroSubgroup B hX hk f σ hσ).ι.hom.hom.left :=
  (picardDegreeZeroSubgroup B hX hk f σ hσ).isClosedImmersion_of_isClosed_range (by
    rw [range_picardDegreeZeroSubgroup_ι]
    exact (isClopen_picardDegreeLocus B hX hk f σ hσ 0).isClosed)

/-- **Stacks Project, Tag 0BA0, clause (3), the closed half: `Pic⁰_{X/k}` is a closed subgroup
scheme of the Picard group scheme**, on the same carrier and inclusion as
`Stacks.PicardFunctor.picardDegreeZeroSubgroup`. -/
def picardDegreeZeroClosedSubgroup : ClosedSubgroupScheme (picardGrp B hX hk f) :=
  (picardDegreeZeroSubgroup B hX hk f σ hσ).toClosedSubgroupScheme (by
    rw [range_picardDegreeZeroSubgroup_ι]
    exact (isClopen_picardDegreeLocus B hX hk f σ hσ 0).isClosed)

end Representable

end Stacks.PicardFunctor
