module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPoints
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionPoints
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension

/-!
# The group of points of the Jacobian over a field

Let `X` be a pointed smooth projective curve over a field `k` whose Picard functor is
representable, and `J = Pic^0_{X/k}` its Jacobian (`Stacks.PicardFunctor.jacobianGrp`). For a
field extension `K/k` with `Spec K` in the site, the group of `K`-points of the base change
`J_K` is the degree-zero Picard group of `X_K`, and the group of rational points of `J` is the
degree-zero Picard group of `X`, as groups:

`J_K(K) = Hom_k(Spec K, J) = Hom_site(Spec K, Pic^0) = Pic^0_{X/k}(Spec K) = Pic^0(X_K)`.

The first step is the adjunction between base change and composition with `Spec K ⟶ Spec k`,
the second is full faithfulness of the comparison of the site with schemes over `k`, the third is
the representability of the degree-zero group presheaf (`Stacks.PicardFunctor.jacobianGrpObj`),
the last is `Stacks.PicardFunctor.degreeZeroFieldAddEquiv`. Each step is additive, the group
structures being those of the group objects, for the cartesian monoidal structures with which
the Jacobian was built. For the rational points, `X_k = X ×_k Spec k ≅ X` and the degree is
unchanged by the ground field extension `k/k` (dimensions of cohomology are, Tag 02KH).

These identifications are compatible with base change of points
(`Stacks.Groupoids.pointBaseChange`) and pullback of line bundles along `X_K ⟶ X`.

## Main definitions

* `Stacks.PicardFunctor.jacobianFieldPointsAddEquiv`: `J_K(K) ≃+ Pic^0(X_K)`.
* `Stacks.PicardFunctor.jacobianPointsAddEquiv`: `J(k) ≃+ Pic^0(X)`.

## Main results

* `Stacks.PicardCurve.picardDegree_schemePullbackClass_of_isPullback`: the degree of a line
  bundle on a proper curve is unchanged by extension of the ground field.
* `Stacks.PicardFunctor.jacobianFieldPointsAddEquiv_pointBaseChange`: the compatibility square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u

/-! ### The degree is unchanged by extension of the ground field -/

namespace Stacks.PicardCurve

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k'] {Z Z' : Scheme.{u}}
  {g' : Z' ⟶ Z} {f' : Z' ⟶ Spec (.of k')} {fZ : Z ⟶ Spec (.of k)}

/-- **The Euler characteristic of a Picard class is unchanged by extension of the ground
field**: cohomology dimensions are ([Stacks, Tag 02KH]). -/
theorem classEuler_schemePullbackClass_of_isPullback
    (h : IsPullback g' f' fZ (Spec.map (CommRingCat.ofHom (algebraMap k k')))) [IsProper fZ]
    (y : Stacks.Picard.ofScheme Z) :
    classEuler f' (Stacks.Picard.schemePullbackClass g' y) = classEuler fZ y := by
  obtain ⟨e⟩ := nonempty_rep_schemePullbackClass_iso g' y
  simp only [classEuler, finrank_cohomologyOverField_eq_of_iso k' f' e,
    finrank_cohomologyOverField_baseChange_field k k' g' f' fZ h]

/-- The degree of a Picard class is the difference of its Euler characteristic and that of `0`. -/
private theorem classEuler_sub_zero_eq_picardDegree {K : Type u} [Field K] {Z : Scheme.{u}}
    (fZ : Z ⟶ Spec (.of K)) [IsProper fZ] [IsCurve K fZ] (hdim : topologicalKrullDim Z ≤ 1)
    (y : Stacks.Picard.ofScheme Z) :
    classEuler fZ y - classEuler fZ 0 =
      picardDegree K fZ hdim (Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace y) := by
  have h1 := classEuler_sub_eq_picardDegree fZ hdim y
  have h2 := classEuler_sub_eq_picardDegree fZ hdim 0
  rw [map_zero, map_zero] at h2
  omega

/-- **The degree of a line bundle on a proper curve is unchanged by extension of the ground
field.** -/
theorem picardDegree_schemePullbackClass_of_isPullback
    (h : IsPullback g' f' fZ (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    [IsProper fZ] [IsCurve k fZ] [IsProper f'] [IsCurve k' f']
    (hdim : topologicalKrullDim Z ≤ 1) (hdim' : topologicalKrullDim Z' ≤ 1)
    (y : Stacks.Picard.ofScheme Z) :
    picardDegree k' f' hdim' (Stacks.GluePicard.picardModelAddEquiv Z'.toRingedSpace
        (Stacks.Picard.schemePullbackClass g' y)) =
      picardDegree k fZ hdim (Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace y) := by
  have h1 := classEuler_sub_zero_eq_picardDegree f' hdim' (Stacks.Picard.schemePullbackClass g' y)
  have h3 := classEuler_sub_zero_eq_picardDegree fZ hdim y
  have e1 := classEuler_schemePullbackClass_of_isPullback h y
  have e0 := classEuler_schemePullbackClass_of_isPullback h (0 : Stacks.Picard.ofScheme Z)
  rw [Stacks.PicardFunctor.schemePullbackClass_zero] at e0
  omega

end Stacks.PicardCurve

/-! ### Points of group schemes over `k` at `Spec K` -/

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]
  (A : Over (Spec (.of k))) [GrpObj A]

/-- The point of `(Spec K)_K` over `Spec K` given by the diagonal. -/
def fieldDiagonal : 𝟙_ (Over (Spec (.of K))) ⟶
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  Over.homMk (pullback.lift (𝟙 _) (𝟙 _) rfl) (pullback.lift_snd _ _ _)

omit [GrpObj A] in
/-- The first component of the base change of `z : Spec K ⟶ A`, precomposed with the diagonal,
is `z`. -/
theorem fieldDiagonal_comp_map_left_fst
    (z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) :
    (fieldDiagonal K ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
        z).left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) = z.left := by
  change pullback.lift (𝟙 _) (𝟙 _) rfl ≫ pullback.lift
    (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ z.left)
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) _ ≫
    pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) = z.left
  rw [pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]

/-- The morphism `Spec K ⟶ A` over `k` given by the first component of a `K`-point of `A_K`. -/
def homOfFieldPoint
    (y : 𝟙_ (Over (Spec (.of K))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A :=
  Over.homMk
    (y.left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (by
      have h : y.left ≫ pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
          𝟙 _ := Over.w y
      change (y.left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≫
        A.hom = Spec.map (CommRingCat.ofHom (algebraMap k K))
      rw [Category.assoc, pullback.condition, reassoc_of% h])

/-- **`K`-points of `A_K` are morphisms `Spec K ⟶ A` over `k`**, as groups: `z` goes to the
diagonal followed by the base change of `z`. -/
def fieldPointsMulEquiv :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A) ≃*
      (𝟙_ (Over (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj A) :=
  MulEquiv.mk'
    { toFun := fun z => fieldDiagonal K ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map z
      invFun := homOfFieldPoint K A
      left_inv := fun z => Over.OverMorphism.ext (fieldDiagonal_comp_map_left_fst K A z)
      right_inv := fun y => by
        have h : y.left ≫ pullback.snd A.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
            𝟙 _ := Over.w y
        refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
        · exact fieldDiagonal_comp_map_left_fst K A _
        · exact (Over.w (fieldDiagonal K ≫
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
              (homOfFieldPoint K A y))).trans h.symm }
    (fun z z' => by
      change _ ≫ (Over.pullback _).map (z * z') = (_ ≫ _) * (_ ≫ _)
      rw [Functor.map_mul, MonObj.comp_mul])

/-- The structure morphism `Spec K ⟶ Spec k`, as a morphism to the unit of schemes over `k`. -/
def fieldStructureHom :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ 𝟙_ (Over (Spec (.of k))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) (Category.comp_id _)

/-- **Base change of points, read on morphisms from `Spec K`**: the point `p_K` corresponds to
`Spec K ⟶ Spec k ⟶ A`. -/
theorem fieldPointsMulEquiv_homMk_comp (p : Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    fieldPointsMulEquiv K A (fieldStructureHom K ≫ p.toMul) = (pointBaseChange A K p).toMul := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · refine (fieldDiagonal_comp_map_left_fst K A _).trans ?_
    rw [pointBaseChange_left_fst]
    rfl
  · exact (Over.w (fieldPointsMulEquiv K A
        (fieldStructureHom K ≫ p.toMul))).trans (pointBaseChange_left_snd A K p).symm

/-- `Spec k ⟶ Spec k` induced by `algebraMap k k` is the identity. -/
theorem specMap_algebraMap_self :
    Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

/-- **Rational points of `A` are morphisms `Spec k ⟶ A` over `k`**, for the structure morphism
`Spec k ⟶ Spec k` of `algebraMap k k`, as groups: precomposition with an isomorphism. -/
def selfFieldPointsMulEquiv :
    (𝟙_ (Over (Spec (.of k))) ⟶ A) ≃*
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k))) ⟶ A) :=
  MulEquiv.mk'
    { toFun := fun p => fieldStructureHom k ≫ p
      invFun := fun z => Over.homMk (U := 𝟙_ (Over (Spec (.of k))))
        (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k)))) (𝟙 _)
        (by simp) ≫ z
      left_inv := fun p => by
        ext
        simp [fieldStructureHom]
      right_inv := fun z => by
        ext
        simp [fieldStructureHom] }
    (fun p p' => MonObj.comp_mul (fieldStructureHom k) p p')

end Stacks.Groupoids

namespace AlgebraicGeometry

/-- **Pullback of line bundles** `Pic(Z) ⟶ Pic(Z')` along `g : Z' ⟶ Z`, in the spelling
`AlgebraicGeometry.schemePicard` of `Pic`. -/
def schemePicardPullbackHom {Z Z' : Scheme.{u}} (g : Z' ⟶ Z) : schemePicard Z →+ schemePicard Z' :=
  ((Stacks.GluePicard.picardModelAddEquiv Z'.toRingedSpace).toAddMonoidHom.comp
    (Stacks.Picard.schemePullbackClassHom g)).comp
    (Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace).symm.toAddMonoidHom

/-- Pullback of line bundles is computed on the class of the pullback of a representative. -/
theorem schemePicardPullbackHom_picardModelAddEquiv {Z Z' : Scheme.{u}} (g : Z' ⟶ Z)
    (y : Stacks.Picard.ofScheme Z) :
    schemePicardPullbackHom g (Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace y) =
      Stacks.GluePicard.picardModelAddEquiv Z'.toRingedSpace
        (Stacks.Picard.schemePullbackClass g y) := by
  simp [schemePicardPullbackHom]

end AlgebraicGeometry

namespace Stacks.PicardCurve

variable {k k' : Type u} [Field k] [Field k'] {Z Z' : Scheme.{u}}
  {f' : Z' ⟶ Spec (.of k')} {fZ : Z ⟶ Spec (.of k)} [IsProper fZ] [IsProper f']
  [IsCurve k fZ] [IsCurve k' f']
  {hdim : topologicalKrullDim Z ≤ 1} {hdim' : topologicalKrullDim Z' ≤ 1}

/-- An additive equivalence of Picard groups of proper curves preserving degrees restricts to
the degree-zero subgroups. -/
def picardDegreeZeroAddEquivOfDegree (e : schemePicard Z ≃+ schemePicard Z')
    (he : ∀ x, picardDegree k' f' hdim' (e x) = picardDegree k fZ hdim x) :
    picardDegreeZero k fZ hdim ≃+ picardDegreeZero k' f' hdim' where
  toFun x := ⟨e x, (mem_picardDegreeZero_iff _ _ _ _).2
    ((he x).trans ((mem_picardDegreeZero_iff _ _ _ _).1 x.2))⟩
  invFun y := ⟨e.symm y, (mem_picardDegreeZero_iff _ _ _ _).2 (by
    rw [← he, e.apply_symm_apply]
    exact (mem_picardDegreeZero_iff _ _ _ _).1 y.2)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add e x.1 y.1)

end Stacks.PicardCurve

/-! ### The Jacobian -/

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable]
  (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K)))

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- **Morphisms of test schemes into `Pic^0_{X/k}` are degree-zero points of the Picard
functor**, as groups. -/
def degreeZeroHomAddEquiv (T : BigFppfOver B (Spec (.of k)) hk) :
    letI := jacobianGrpObj B hX hk f σ hσ
    Additive (T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0) ≃+
      degreeZeroAddSubgroup B hX hk f σ hσ T :=
  letI := jacobianGrpObj B hX hk f σ hσ
  AddEquiv.mk' (Additive.toMul.trans ((degreeZeroGrpRepresentableBy B hX hk f σ hσ).homEquiv'.trans
      (Multiplicative.toAdd : Multiplicative (degreeZeroAddSubgroup B hX hk f σ hσ T) ≃ _)))
    (fun ψ ψ' => by
      change Multiplicative.toAdd ((degreeZeroGrpRepresentableBy B hX hk f σ hσ).homEquiv'
        (CartesianMonoidalCategory.lift ψ.toMul ψ'.toMul ≫
          (degreeZeroGrpRepresentableBy B hX hk f σ hσ).homEquiv'.symm
            ((degreeZeroGrpRepresentableBy B hX hk f σ hσ).homEquiv'
                (CartesianMonoidalCategory.fst _ _) *
              (degreeZeroGrpRepresentableBy B hX hk f σ hσ).homEquiv'
                (CartesianMonoidalCategory.snd _ _)))) = _
      rw [Functor.RepresentableBy.homEquiv'_comp, Equiv.apply_symm_apply, map_mul,
        ← Functor.RepresentableBy.homEquiv'_comp, ← Functor.RepresentableBy.homEquiv'_comp,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
      rfl)

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts in
/-- The identification of morphisms into `Pic^0_{X/k}` with degree-zero points is natural. -/
theorem degreeZeroHomAddEquiv_comp {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    (ψ : T ⟶ picardSchemeDegreeComponent B hX hk f σ hσ 0) :
    letI := jacobianGrpObj B hX hk f σ hσ
    degreeZeroHomAddEquiv B hX hk f σ hσ T' (Additive.ofMul (g ≫ ψ)) =
      degreeZeroMap B hX hk f σ hσ g (degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul ψ)) :=
  Subtype.ext (congrArg (fun x => (Multiplicative.toAdd x).1)
    ((degreeZeroGrpRepresentableBy B hX hk f σ hσ).homEquiv_comp g ψ))

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- **Morphisms from a test scheme to the Jacobian over `k` are morphisms to `Pic^0` in the
site**, as groups: the comparison functor is fully faithful and monoidal. -/
def jacobianHomAddEquiv (T : BigFppfOver B (Spec (.of k)) hk) :
    Additive ((Over.post (X := B.obj hk) B.inclusion).obj T ⟶ (jacobianGrp B hX hk f σ hσ).X) ≃+
      degreeZeroAddSubgroup B hX hk f σ hσ T :=
  haveI := preservesFiniteProducts_overPost_bigFppfInclusion B (Spec (.of k)) hk
  letI := jacobianGrpObj B hX hk f σ hσ
  ((fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk).homMulEquiv
    (X := T) (M := picardSchemeDegreeComponent B hX hk f σ hσ 0)).symm.toAdditive.trans
    (degreeZeroHomAddEquiv B hX hk f σ hσ T)

attribute [local instance] CartesianMonoidalCategory.ofHasFiniteProducts
  Functor.Monoidal.ofChosenFiniteProducts in
/-- The identification of morphisms into the Jacobian with degree-zero points is natural in the
test scheme. -/
theorem jacobianHomAddEquiv_comp {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    (ψ : (Over.post (X := B.obj hk) B.inclusion).obj T ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj (picardSchemeDegreeComponent B hX hk f σ hσ 0)) :
    jacobianHomAddEquiv B hX hk f σ hσ T'
        (Additive.ofMul ((Over.post (X := B.obj hk) B.inclusion).map g ≫ ψ)) =
      degreeZeroMap B hX hk f σ hσ g (jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul ψ)) := by
  let hF := fullyFaithful_overPost_bigFppfInclusion B (Spec (.of k)) hk
  have hpre : hF.preimage ((Over.post (X := B.obj hk) B.inclusion).map g ≫ ψ) =
      g ≫ hF.preimage ψ :=
    hF.map_injective (by rw [hF.map_preimage, Functor.map_comp, hF.map_preimage])
  change degreeZeroHomAddEquiv B hX hk f σ hσ T'
      (Additive.ofMul (hF.preimage ((Over.post (X := B.obj hk) B.inclusion).map g ≫ ψ))) =
    degreeZeroMap B hX hk f σ hσ g
      (degreeZeroHomAddEquiv B hX hk f σ hσ T (Additive.ofMul (hF.preimage ψ)))
  rw [hpre]
  exact degreeZeroHomAddEquiv_comp B hX hk f σ hσ g _

/-- **`J_K(K) ≃+ Pic^0(X_K)`**: the group of `K`-points of the base change `J_K` of the Jacobian
is the degree-zero Picard group of `X_K`. -/
def jacobianFieldPointsAddEquiv :
    Additive (𝟙_ (Over (Spec (.of K))) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
        (jacobianGrp B hX hk f σ hσ).X) ≃+
      picardDegreeZero K (fieldCurve B hX hk f K hK)
        (topologicalKrullDim_fieldCurve_le B hX hk f K hK) :=
  (Stacks.Groupoids.fieldPointsMulEquiv K (jacobianGrp B hX hk f σ hσ).X).symm.toAdditive.trans
    ((jacobianHomAddEquiv B hX hk f σ hσ (fieldObj B hk K hK)).trans
      (degreeZeroFieldAddEquiv B hX hk f σ hσ K hK))

/-- `J(k) ≃+ Pic^0(X_k)`, for `X_k = X ×_k Spec k`. -/
def jacobianPointsAddEquivFieldSelf :
    Additive (𝟙_ (Over (Spec (.of k))) ⟶ (jacobianGrp B hX hk f σ hσ).X) ≃+
      picardDegreeZero k (fieldCurve B hX hk f k hk)
        (topologicalKrullDim_fieldCurve_le B hX hk f k hk) :=
  (Stacks.Groupoids.selfFieldPointsMulEquiv (jacobianGrp B hX hk f σ hσ).X).toAdditive.trans
    ((jacobianHomAddEquiv B hX hk f σ hσ (fieldObj B hk k hk)).trans
      (degreeZeroFieldAddEquiv B hX hk f σ hσ k hk))

/-- The projection `X_k = X ×_k Spec k ⟶ X` is an isomorphism, `Spec k ⟶ Spec k` being the
identity. -/
instance isIso_fieldSelfFst :
    IsIso (pullback.fst (B.inclusion.map f) (B.inclusion.map (fieldObj B hk k hk).hom)) := by
  have : IsIso (B.inclusion.map (fieldObj B hk k hk).hom) := by
    change IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k)))
    rw [Stacks.Groupoids.specMap_algebraMap_self]
    infer_instance
  infer_instance

/-- `X_k = X ×_k Spec k ≅ X`. -/
def fieldSelfIso : baseChange B hX hk f (fieldObj B hk k hk) ≅ B.inclusion.obj (B.obj hX) :=
  asIso (pullback.fst (B.inclusion.map f) (B.inclusion.map (fieldObj B hk k hk).hom))

/-- **`Pic^0(X) ≃+ Pic^0(X_k)`**, pulling back along `X_k ≅ X`: the degree is unchanged by the
ground field extension `k/k`. -/
def picardDegreeZeroFieldSelfAddEquiv (hdim : topologicalKrullDim X ≤ 1) :
    picardDegreeZero k (B.inclusion.map f) hdim ≃+
      picardDegreeZero k (fieldCurve B hX hk f k hk)
        (topologicalKrullDim_fieldCurve_le B hX hk f k hk) :=
  Stacks.PicardCurve.picardDegreeZeroAddEquivOfDegree
    ((Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm.trans
      ((Stacks.Picard.schemePullbackClassAddEquiv (fieldSelfIso B hX hk f)).trans
        (Stacks.GluePicard.picardModelAddEquiv
          (baseChange B hX hk f (fieldObj B hk k hk)).toRingedSpace)))
    (fun x => (Stacks.PicardCurve.picardDegree_schemePullbackClass_of_isPullback
      (isPullback_fieldCurve B hX hk f k hk) hdim
      (topologicalKrullDim_fieldCurve_le B hX hk f k hk)
      ((Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace).symm x)).trans
        (congrArg (picardDegree k (B.inclusion.map f) hdim) (AddEquiv.apply_symm_apply _ x)))

/-- **`J(k) ≃+ Pic^0(X)`**: the group of rational points of the Jacobian is the degree-zero
Picard group of `X`. -/
def jacobianPointsAddEquiv (hdim : topologicalKrullDim X ≤ 1) :
    Additive (𝟙_ (Over (Spec (.of k))) ⟶ (jacobianGrp B hX hk f σ hσ).X) ≃+
      picardDegreeZero k (B.inclusion.map f) hdim :=
  (jacobianPointsAddEquivFieldSelf B hX hk f σ hσ).trans
    (picardDegreeZeroFieldSelfAddEquiv B hX hk f hdim).symm

/-! ### Compatibility with base change -/

/-- The morphism of test schemes `Spec K ⟶ Spec k` over `k`. -/
def fieldObjHom : fieldObj B hk K hK ⟶ fieldObj B hk k hk :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (by
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k)) =
          Spec.map (CommRingCat.ofHom (algebraMap k K))
      rw [Stacks.Groupoids.specMap_algebraMap_self, Category.comp_id])

/-- `Spec K ⟶ Spec k`, as a morphism to the unit, factors through `Spec k ⟶ Spec k`. -/
theorem fieldStructureHom_eq_comp :
    Stacks.Groupoids.fieldStructureHom (k := k) K =
      (Over.post (X := B.obj hk) B.inclusion).map (fieldObjHom B hk K hK) ≫
        Stacks.Groupoids.fieldStructureHom k := by
  ext
  simp only [Stacks.Groupoids.fieldStructureHom, fieldObjHom, Over.homMk_left]
  exact ((congrArg (fun g => Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ g)
    Stacks.Groupoids.specMap_algebraMap_self).trans (Category.comp_id _)).symm

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] in
/-- `Pic_{X/k}(Spec K) ≅ Pic(X_K)` sends the image of a class of `Pic(X_K)` to that class. -/
theorem picardFieldAddEquiv_toPicardFunctorHom (z : picardAt B hX hk f (fieldObj B hk K hK)) :
    picardFieldAddEquiv B hX hk f σ hσ K hK (toPicardFunctorHom B hX hk f (fieldObj B hk K hK) z) =
      Stacks.GluePicard.picardModelAddEquiv
        (baseChange B hX hk f (fieldObj B hk K hK)).toRingedSpace z := by
  simp only [picardFieldAddEquiv, AddEquiv.trans_apply]
  exact congrArg _ ((picardAddEquivOfSubsingleton B hX hk f σ hσ
    (isIso_c_of_isCurve B hX hk f σ hσ) (fieldObj B hk K hK)).symm_apply_apply z)

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] in
/-- **Restriction of points of the Picard functor along `Spec K ⟶ Spec L` is pullback of line
bundles along `X_K ⟶ X_L`.** -/
theorem picardFieldAddEquiv_map (L : Type u) [Field L] [Algebra k L]
    (hL : B.Contains (Spec (.of L))) (g : fieldObj B hk K hK ⟶ fieldObj B hk L hL)
    (ξ : (picardFunctor B hX hk f).obj (op (fieldObj B hk L hL))) :
    picardFieldAddEquiv B hX hk f σ hσ K hK ((picardFunctor B hX hk f).map g.op ξ) =
      schemePicardPullbackHom (baseChangeMap B hX hk f g)
        (picardFieldAddEquiv B hX hk f σ hσ L hL ξ) := by
  obtain ⟨z, rfl⟩ := (bijective_toPicardFunctorHom_of_subsingleton B hX hk f σ hσ
    (isIso_c_of_isCurve B hX hk f σ hσ) (fieldObj B hk L hL)).2 ξ
  rw [picardFunctor_map_toPicardFunctorHom, picardFieldAddEquiv_toPicardFunctorHom,
    picardFieldAddEquiv_toPicardFunctorHom, schemePicardPullbackHom_picardModelAddEquiv]

/-- **The compatibility square** of the identifications `J(k) ≃+ Pic^0(X)` and
`J_K(K) ≃+ Pic^0(X_K)` with base change of points (`Stacks.Groupoids.pointBaseChange`) and
pullback of line bundles along the projection `X_K ⟶ X`. -/
theorem jacobianFieldPointsAddEquiv_pointBaseChange (hdim : topologicalKrullDim X ≤ 1)
    (p : Additive (𝟙_ (Over (Spec (.of k))) ⟶ (jacobianGrp B hX hk f σ hσ).X)) :
    (jacobianFieldPointsAddEquiv B hX hk f σ hσ K hK
        (Stacks.Groupoids.pointBaseChange (jacobianGrp B hX hk f σ hσ).X K p)).1 =
      schemePicardPullbackHom
        (pullback.fst (B.inclusion.map f) (B.inclusion.map (fieldObj B hk K hK).hom))
        (jacobianPointsAddEquiv B hX hk f σ hσ hdim p).1 := by
  have h₁ : (Stacks.Groupoids.fieldPointsMulEquiv K (jacobianGrp B hX hk f σ hσ).X).symm
      (Stacks.Groupoids.pointBaseChange (jacobianGrp B hX hk f σ hσ).X K p).toMul =
        (Over.post (X := B.obj hk) B.inclusion).map (fieldObjHom B hk K hK) ≫
          (Stacks.Groupoids.fieldStructureHom k ≫ p.toMul) := by
    rw [← Stacks.Groupoids.fieldPointsMulEquiv_homMk_comp, MulEquiv.symm_apply_apply,
      fieldStructureHom_eq_comp B hk K hK]
    exact Category.assoc _ _ _
  have hbc : baseChangeMap B hX hk f (fieldObjHom B hk K hK) =
      pullback.fst (B.inclusion.map f) (B.inclusion.map (fieldObj B hk K hK).hom) ≫
        (fieldSelfIso B hX hk f).inv := by
    rw [Iso.eq_comp_inv]
    simp [baseChangeMap, fieldSelfIso]
  set ξ := jacobianHomAddEquiv B hX hk f σ hσ (fieldObj B hk k hk)
    (Additive.ofMul (Stacks.Groupoids.fieldStructureHom k ≫ p.toMul))
  set w : schemePicard (baseChange B hX hk f (fieldObj B hk k hk)) :=
    (degreeZeroFieldAddEquiv B hX hk f σ hσ k hk ξ).1
  have hL : (jacobianFieldPointsAddEquiv B hX hk f σ hσ K hK
      (Stacks.Groupoids.pointBaseChange (jacobianGrp B hX hk f σ hσ).X K p)).1 =
      schemePicardPullbackHom (baseChangeMap B hX hk f (fieldObjHom B hk K hK)) w := by
    change (degreeZeroFieldAddEquiv B hX hk f σ hσ K hK
      (jacobianHomAddEquiv B hX hk f σ hσ (fieldObj B hk K hK) (Additive.ofMul
        ((Stacks.Groupoids.fieldPointsMulEquiv K (jacobianGrp B hX hk f σ hσ).X).symm
          (Stacks.Groupoids.pointBaseChange (jacobianGrp B hX hk f σ hσ).X K p).toMul)))).1 = _
    rw [h₁]
    erw [jacobianHomAddEquiv_comp]
    exact picardFieldAddEquiv_map B hX hk f σ hσ K hK k hk (fieldObjHom B hk K hK) ξ.1
  have hR : (jacobianPointsAddEquiv B hX hk f σ hσ hdim p).1 =
      Stacks.GluePicard.picardModelAddEquiv (B.inclusion.obj (B.obj hX)).toRingedSpace
        (Stacks.Picard.schemePullbackClass (fieldSelfIso B hX hk f).inv
          ((Stacks.GluePicard.picardModelAddEquiv
            (baseChange B hX hk f (fieldObj B hk k hk)).toRingedSpace).symm w)) := rfl
  refine hL.trans (Eq.trans ?_ (congrArg (schemePicardPullbackHom
    (pullback.fst (B.inclusion.map f) (B.inclusion.map (fieldObj B hk K hK).hom))) hR).symm)
  rw [schemePicardPullbackHom_picardModelAddEquiv, Stacks.Picard.schemePullbackClass_comp,
    ← hbc, ← schemePicardPullbackHom_picardModelAddEquiv, AddEquiv.apply_symm_apply]

end Stacks.PicardFunctor

end
