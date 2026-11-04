module

public import StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesLimitPreservingUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProductObjects

/-!
# Limit preservation of `PolarizedCurves ⟶ 𝒞urves`, and smoothness of its base changes

`PolarizedCurves = 𝒫olarized ×_{𝒮paces'_{fp, flat, proper}} 𝒞urves` (Stacks 0DPY), so the
projection `PolarizedCurves ⟶ 𝒞urves` is the base change of forgetting the polarization
`𝒫olarized ⟶ 𝒮paces'_{fp, flat, proper}` (Stacks 0D3Y). Both `𝒫olarized` (Stacks 0D43) and
`𝒮paces'_{fp, flat, proper}` (Stacks 0D1I) are limit preserving in the sense of Stacks 07XL, so the
forgetful 1-morphism is limit preserving on objects (Stacks 06CU), and so is its base change
(Stacks 06CV). With formal smoothness on objects
(`StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesSmooth`), this proves that the base
changes of `PolarizedCurves ⟶ 𝒞urves` along scheme points are smooth, by the infinitesimal lifting
criterion (Stacks 0DP0): the second assertion of Stacks 0D5C.

## Main definitions

* `AlgebraicGeometry.C1783.spacesSmall`,
  `AlgebraicGeometry.C1783.polarizedSmall`: small models of
  `𝒮paces'_{fp, flat, proper}` and `𝒫olarized`.
* `AlgebraicGeometry.C1783.forgetPolarizationSmall`,
  `AlgebraicGeometry.C1783.curvesToSpacesSmall`: the cospan.
* `AlgebraicGeometry.C1783.polarizedCurvesSmallComparison`: the small
  model of PolarizedCurves mapped to the base change of the small models.

## Main results

* `AlgebraicGeometry.C1783.isLimitPreservingOnObjects_of_full_of_exists_isHomLift_id`:
  a full 1-morphism essentially surjective on fibres is limit preserving on objects.
* `AlgebraicGeometry.C1783.isLimitPreservingOnObjects_polarizedCurvesSmallToCurvesSmall`:
  `PolarizedCurves ⟶ 𝒞urves` is limit preserving on objects.
* `AlgebraicGeometry.C1783.hasPropertyOnSomeSmoothDiagram_baseChange_polarizedCurvesSmall`:
  **the second assertion of Stacks 0D5C**: the base change of `PolarizedCurves ⟶ 𝒞urves` along a
  scheme point, being algebraic, is smooth.

## Implementation notes

The cancellation statement turning limit preservation of `𝒫olarized` and
`𝒮paces'_{fp, flat, proper}` into limit preservation on objects of the forgetful 1-morphism
(`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_of_toTerminalCFG`) is stated in the
2-category of categories fibred in groupoids whose morphisms lie in the universe of the schemes,
so the argument runs on small models: `𝒫olarized` already has its morphisms there, and
`𝒮paces'_{fp, flat, proper}` is shrunk (`CategoryTheory.BasedCategory.shrinkHoms`). The small
model of PolarizedCurves is not literally the base change of the small models, but the comparison
is full and essentially surjective on fibres, which is all that limit preservation on objects
needs.

Nothing here is registered.

## References

* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CV](https://stacks.math.columbia.edu/tag/06CV)
* [Stacks Project, Tag 0DP0](https://stacks.math.columbia.edu/tag/0DP0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w₀ u

namespace AlgebraicGeometry.C1783

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### Small models of `𝒫olarized` and `𝒮paces'_{fp, flat, proper}` -/

/-- The hom types of `𝒮paces'_{fp, flat, proper}` are `u`-small. -/
theorem locallySmall_cartesianProperFlatSpaces :
    LocallySmall.{u} (CartesianProperFlatSpaces B integerBase hZ) where
  hom_small X Y := by
    have : Small.{u} (X.obj.obj.left.obj ⟶ Y.obj.obj.left.obj) := small_hom_presheaf _ _
    let F : (X ⟶ Y) →
        (X.obj.obj.left.obj ⟶ Y.obj.obj.left.obj) × (X.obj.obj.right ⟶ Y.obj.obj.right) :=
      fun f => (f.1.hom.left.hom, f.1.hom.right)
    exact small_of_injective (f := F) fun f g h => WideSubcategory.hom_ext _ <|
      ObjectProperty.hom_ext _ <| Comma.hom_ext _ _
        (ObjectProperty.hom_ext _ (congrArg Prod.fst h)) (congrArg Prod.snd h)

/-- The hom types of `𝒮paces'_{fp, flat, proper}`, read as a category over the site, are
`u`-small. -/
theorem locallySmall_cartesianProperFlatFiberedCategory_obj :
    LocallySmall.{u} (cartesianProperFlatFiberedCategory B integerBase hZ).val.obj :=
  locallySmall_cartesianProperFlatSpaces B hZ

attribute [local instance] locallySmall_cartesianProperFlatSpaces
  locallySmall_cartesianProperFlatFiberedCategory_obj locallySmall_curveFamily

/-- **The small model of `𝒮paces'_{fp, flat, proper}`**, with morphisms in the universe of the
site. -/
def spacesSmall : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  ⟨(cartesianProperFlatFiberedCategory B integerBase hZ).val.shrinkHoms,
    BasedCategory.isFiberedInGroupoids_shrinkHoms _
      (cartesianProperFlatFiberedCategory B integerBase hZ).property⟩

/-- The small model of `𝒮paces'_{fp, flat, proper}` is limit preserving (Stacks 0D1I). -/
private theorem isLimitPreserving_spacesSmall :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B integerBase hZ (spacesSmall B hZ) :=
  Stack.isLimitPreserving_of_equivalenceOver B integerBase hZ (spacesSmall B hZ)
    (cartesianProperFlatFiberedCategory B integerBase hZ)
    (BasedCategory.shrinkHomsEquivalenceOver.{u}
      (cartesianProperFlatFiberedCategory B integerBase hZ).val).symm
    (isLimitPreserving_cartesianProperFlatFiberedCategory B integerBase hZ)

/-- **The small model of `𝒫olarized`**: polarized families over the big fppf site of `Spec ℤ`,
with their own morphisms. -/
def polarizedSmall : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (polarizedProjection B ⋙ schemeOverIntegers B))
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)

omit hZ in
/-- The projection of `AlgebraicGeometry.polarizedStackUnconditional` over `Spec ℤ` is the
projection of the polarized families read over `Spec ℤ`. -/
theorem polarizedSliceProjection_eq :
    polarizedSliceProjection B B.contains_integerBase
        (isTerminal_obj_specULiftZ B B.contains_integerBase) =
      polarizedProjection B ⋙ schemeOverIntegers B := by
  rw [schemeOverIntegers_eq_equivalenceOfIsTerminal_inverse]
  rfl

/-- The small model of `𝒫olarized` is limit preserving (Stacks 0D43). -/
private theorem isLimitPreserving_polarizedSmall :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B integerBase hZ
      (polarizedSmall B hZ) := by
  have h := isLimitPreservingPolarizedUnconditional B B.contains_integerBase
    (isTerminal_obj_specULiftZ B B.contains_integerBase)
  have key : ∀ (F G : PolarizedFamily B ⥤ BigFppfOver B integerBase hZ) (hFG : F = G)
      (hF : F.IsFiberedInGroupoids) (hG : G.IsFiberedInGroupoids),
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B integerBase hZ
        (CatFiberedInGroupoids.mk (BasedCategory.ofFunctor F) hF) →
      Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B integerBase hZ
        (CatFiberedInGroupoids.mk (BasedCategory.ofFunctor G) hG) := by
    rintro F G rfl hF hG h
    exact h
  exact key _ _ (polarizedSliceProjection_eq B) _ _ h

/-! ### The forgetful 1-morphisms on the small models -/

/-- Shrinking the hom types and coming back, followed by `cartesianProperFlatProjection`. -/
theorem shrinkHoms_functor_comp_inverse_comp_cartesianProperFlatProjection :
    ShrinkHoms.functor.{u} (CartesianProperFlatSpaces B integerBase hZ) ⋙
        (ShrinkHoms.inverse.{u} (CartesianProperFlatSpaces B integerBase hZ) ⋙
          cartesianProperFlatProjection B integerBase hZ) =
      cartesianProperFlatProjection B integerBase hZ := by
  have h := BasedCategory.shrinkHoms_functor_comp_inverse.{u}
    (cartesianProperFlatFiberedCategory B integerBase hZ).val
  exact (Functor.assoc _ _ _).symm.trans
    ((congrArg (· ⋙ cartesianProperFlatProjection B integerBase hZ) h).trans (Functor.id_comp _))

/-- **Forgetting the polarization**, on the small models (Stacks 0D3Y). -/
def forgetPolarizationSmall : polarizedSmall B hZ ⟶ spacesSmall B hZ :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := forgetPolarization B ⋙
        ShrinkHoms.functor.{u} (CartesianProperFlatSpaces B integerBase hZ)
      w := by
        change forgetPolarization B ⋙ (ShrinkHoms.functor.{u} _ ⋙
          (ShrinkHoms.inverse.{u} _ ⋙ cartesianProperFlatProjection B integerBase hZ)) = _
        rw [shrinkHoms_functor_comp_inverse_comp_cartesianProperFlatProjection]
        rfl }

/-- **The inclusion of `𝒞urves` into `𝒮paces'_{fp, flat, proper}`**, on the small models
(Stacks 0D50). -/
def curvesToSpacesSmall : curvesSmall B hZ ⟶ spacesSmall B hZ :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := ShrinkHoms.inverse.{u} (CurveFamily B hZ) ⋙ curvesToCartesianProperFlat B hZ ⋙
        ShrinkHoms.functor.{u} (CartesianProperFlatSpaces B integerBase hZ)
      w := by
        change ShrinkHoms.inverse.{u} (CurveFamily B hZ) ⋙ curvesToCartesianProperFlat B hZ ⋙
          (ShrinkHoms.functor.{u} _ ⋙
            (ShrinkHoms.inverse.{u} _ ⋙ cartesianProperFlatProjection B integerBase hZ)) = _
        rw [shrinkHoms_functor_comp_inverse_comp_cartesianProperFlatProjection]
        rfl }

/-! ### Limit preservation on objects -/

/-- **Forgetting the polarization is limit preserving on objects** (Stacks 06CU), on the small
models: `𝒫olarized` is limit preserving (Stacks 0D43), so its structure morphism is limit
preserving on objects, and `𝒮paces'_{fp, flat, proper}` is limit preserving (Stacks 0D1I). -/
private theorem isLimitPreservingOnObjects_forgetPolarizationSmall :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B integerBase hZ
      (polarizedSmall B hZ) (spacesSmall B hZ) (forgetPolarizationSmall B hZ) :=
  Stack.isLimitPreservingOnObjects_of_toTerminalCFG B integerBase hZ _ _ _
    (Stack.isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B integerBase hZ _
      (isLimitPreserving_polarizedSmall B hZ))
    (isLimitPreserving_spacesSmall B hZ)

/-- The base change of forgetting the polarization along the inclusion of `𝒞urves`, on the small
models, is limit preserving on objects (Stacks 06CV). -/
private theorem isLimitPreservingOnObjects_twoFibreProductSnd_forgetPolarizationSmall :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B integerBase hZ
      (BigFppfOver.twoFibreProduct.{u, u, u} B integerBase hZ (polarizedSmall B hZ)
        (spacesSmall B hZ) (curvesSmall B hZ) (forgetPolarizationSmall B hZ)
        (curvesToSpacesSmall B hZ))
      (curvesSmall B hZ)
      (BigFppfOver.twoFibreProductSnd.{u, u, u} B integerBase hZ (polarizedSmall B hZ)
        (spacesSmall B hZ) (curvesSmall B hZ) (forgetPolarizationSmall B hZ)
        (curvesToSpacesSmall B hZ)) :=
  BigFppfOver.isLimitPreservingOnObjects_baseChange.{u, u, u} B integerBase hZ _ _ _ _ _
    (isLimitPreservingOnObjects_forgetPolarizationSmall B hZ)

/-! ### Limit preservation on objects of a fibrewise equivalence -/

section Equivalence

universe v w

variable {S : Scheme.{u}} {hS : B.Contains S}

omit hZ in
/-- A morphism lies over `g` for a functor equal to a composite as soon as its image does. -/
private theorem isHomLift_of_comp_eq {𝒳 𝒴 𝒞 : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒞]
    {F : 𝒳 ⥤ 𝒴} {P : 𝒴 ⥤ 𝒞} {Q : 𝒳 ⥤ 𝒞} (hFPQ : F ⋙ P = Q) {R T : 𝒞} (g : R ⟶ T) {x y : 𝒳}
    (φ : x ⟶ y) (h : P.IsHomLift g (F.map φ)) : Q.IsHomLift g φ := by
  subst hFPQ
  exact isHomLift_comp_of_isHomLift F P g φ h

omit hZ in
/-- **A full 1-morphism which is essentially surjective on fibres is limit preserving on objects**
(Stacks 06CU). Given an object `x` over the limit `T` and a cartesian comparison `γ` of its image
with an object `y` at a stage `Tᵢ`, take an object `x'` over `Tᵢ` whose image is identified with
`y` by a vertical morphism `v`; the comparison `γ ≫ v⁻¹` is the image of a morphism `x ⟶ x'`,
which is cartesian since every morphism of a category fibred in groupoids is. -/
private theorem isLimitPreservingOnObjects_of_full_of_exists_isHomLift_id
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (e : 𝒳 ⟶ 𝒴)
    [(CatFiberedInGroupoids.homFunctor e).Full]
    (hess : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.obj), 𝒴.val.p.obj y = U →
      ∃ (x : 𝒳.val.obj) (_ : 𝒳.val.p.obj x = U)
          (t : (CatFiberedInGroupoids.homFunctor e).obj x ⟶ y),
        𝒴.val.p.IsHomLift (𝟙 U) t) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒳 𝒴 e := by
  intro I _ _ D c hc i y x γ hγ
  let inc := BigAffineFppf.inclusion B S hS
  let F := CatFiberedInGroupoids.homFunctor e
  have hFcomp : F ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p e
  obtain ⟨x', hx', t, ht⟩ := hess (inc.obj (D.obj i)) y.1 y.2
  have := ht
  have : IsIso t := by
    have := 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 (inc.obj (D.obj i))) t
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := 𝒴.val.p)
      (f := 𝟙 (inc.obj (D.obj i))) t
  have := hγ.toIsHomLift
  have htinv : 𝒴.val.p.IsHomLift (𝟙 (inc.obj (D.obj i))) (inv t) := by
    have h := IsHomLift.inv 𝒴.val.p (𝟙 (inc.obj (D.obj i))) t
    rwa [IsIso.inv_id] at h
  let δ : x.1 ⟶ x' := F.preimage (γ ≫ inv t)
  have hδ : F.map δ = γ ≫ inv t := F.map_preimage _
  have hFδ : 𝒴.val.p.IsHomLift (inc.map (c.π.app i)) (F.map δ) := by
    rw [hδ]
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ 𝒴.val.p _ _ _ _ _ _ γ _ _ _ htinv
  have hδlift : 𝒳.val.p.IsHomLift (inc.map (c.π.app i)) δ :=
    isHomLift_of_comp_eq hFcomp _ δ hFδ
  have htD : 𝒴.val.p.IsHomLift (inc.map (D.map (𝟙 i))) t := by
    rw [D.map_id, CategoryTheory.Functor.map_id]
    exact ht
  refine ⟨i, 𝟙 i, ⟨x', hx'⟩, x, δ, 𝟙 x.1, t, ?_, ?_, inferInstance, ?_, ?_⟩
  · exact 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift _ δ
  · exact IsHomLift.id x.2
  · exact 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift _ t
  · rw [hδ, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]

end Equivalence

/-! ### The small model of PolarizedCurves as a base change of the small models -/

section Comparison

variable (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)

attribute [local instance] locallySmall_polarizedCurves

/-- The objects of the base change of forgetting the polarization along the inclusion of
`𝒞urves`, on the small models. -/
abbrev PolarizedCurveSmallObj :=
  TwoFibreProductOver (polarizedSmall B hZ).val.p (curvesSmall B hZ).val.p (spacesSmall B hZ).val.p
    (CatFiberedInGroupoids.homFunctor (forgetPolarizationSmall B hZ))
    (CatFiberedInGroupoids.homFunctor (curvesToSpacesSmall B hZ))

omit h3Z in
/-- A morphism of the polarized side lies over `g` once it does after raising the hom universe. -/
theorem isHomLift_polarizedSmall_down {x y : PolarizedFamilyUp B}
    {R T : BigFppfOver B integerBase hZ}
    (g : R ⟶ T) (φ : x ⟶ y) (h : (polarizedProjectionOver B hZ).IsHomLift g φ) :
    (polarizedSmall B hZ).val.p.IsHomLift g φ.down :=
  IsHomLift.of_fac' _ _ _ (IsHomLift.domain_eq (polarizedProjectionOver B hZ) g φ)
    (IsHomLift.codomain_eq (polarizedProjectionOver B hZ) g φ)
    (IsHomLift.fac' (polarizedProjectionOver B hZ) g φ)

/-- The comparison on objects: the same polarized family, family of curves and identification. -/
def polarizedCurvesSmallComparisonObj (W : (polarizedCurvesSmall B hZ h3Z).val.obj) :
    PolarizedCurveSmallObj B hZ where
  base := (ShrinkHoms.fromShrinkHoms W).base
  x := ULiftHom.objDown.{u + 1, u + 1} (ShrinkHoms.fromShrinkHoms W).x
  y := ShrinkHoms.toShrinkHoms (ShrinkHoms.fromShrinkHoms W).y
  hx := (ShrinkHoms.fromShrinkHoms W).hx
  hy := (ShrinkHoms.fromShrinkHoms W).hy
  iso := (ShrinkHoms.functor.{u} (CartesianProperFlatSpaces B integerBase hZ)).mapIso
    (ShrinkHoms.fromShrinkHoms W).iso
  vertical := isHomLift_shrinkHomsFunctor_map (cartesianProperFlatProjection B integerBase hZ) _ _
    (ShrinkHoms.fromShrinkHoms W).vertical

omit B hZ h3Z in
/-- A commutative square, read through the shrunk hom types. -/
private theorem shrinkHomsFunctor_map_comp_eq.{w, v, t} {C : Type t} [Category.{v} C]
    [LocallySmall.{w} C] {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ W} {k : X ⟶ Z} {l : Z ⟶ W}
    (h : f ≫ g = k ≫ l) :
    (ShrinkHoms.functor.{w} C).map f ≫ (ShrinkHoms.functor.{w} C).map g =
      (ShrinkHoms.functor.{w} C).map k ≫ (ShrinkHoms.functor.{w} C).map l := by
  rw [← Functor.map_comp, h, Functor.map_comp]

/-- The comparison on morphisms. -/
def polarizedCurvesSmallComparisonMap {W W' : (polarizedCurvesSmall B hZ h3Z).val.obj}
    (φ : W ⟶ W') :
    polarizedCurvesSmallComparisonObj B hZ h3Z W ⟶
      polarizedCurvesSmallComparisonObj B hZ h3Z W' where
  hbase := ((ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map φ).hbase
  a := ((ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map φ).a.down
  b := (ShrinkHoms.functor.{u} (CurveFamily B hZ)).map
    ((ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map φ).b
  ha := isHomLift_polarizedSmall_down B hZ _ _
    ((ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map φ).ha
  hb := isHomLift_shrinkHomsFunctor_map (curvesProjectionOver B hZ) _ _
    ((ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map φ).hb
  w := by
    let ψ := (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map φ
    have e1 : (curvesToCartesianProperFlat B hZ).map
        ((ShrinkHoms.inverse.{u} (CurveFamily B hZ)).map
          ((ShrinkHoms.functor.{u} (CurveFamily B hZ)).map ψ.b)) =
        (curvesToCartesianProperFlat B hZ).map ψ.b :=
      congrArg (curvesToCartesianProperFlat B hZ).map
        (shrinkHomsInverse_map_functor_map.{u} (C := CurveFamily B hZ) ψ.b)
    exact (shrinkHomsFunctor_map_comp_eq.{u} (C := CartesianProperFlatSpaces B integerBase hZ)
      ψ.w).trans
      (congrArg (_ ≫ (ShrinkHoms.functor.{u} (CartesianProperFlatSpaces B integerBase hZ)).map ·)
        e1.symm)

/-- The comparison functor from the small model of PolarizedCurves to the base change of the small
models. -/
def polarizedCurvesSmallComparisonFunctor :
    (polarizedCurvesSmall B hZ h3Z).val.obj ⥤ PolarizedCurveSmallObj B hZ where
  obj := polarizedCurvesSmallComparisonObj B hZ h3Z
  map := polarizedCurvesSmallComparisonMap B hZ h3Z
  map_id W := TwoFibreProductOver.Hom.ext'
    (congrArg (fun ψ => ψ.a.down)
      ((ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map_id W))
    ((congrArg (fun ψ :
          (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).obj W ⟶
          (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).obj W =>
          (ShrinkHoms.functor.{u} (CurveFamily B hZ)).map (TwoFibreProductOver.Hom.b ψ))
      ((ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map_id W)).trans
      ((ShrinkHoms.functor.{u} (CurveFamily B hZ)).map_id _))
  map_comp {W _ W''} φ φ' := TwoFibreProductOver.Hom.ext'
    (congrArg (fun ψ => ψ.a.down)
      ((ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map_comp φ φ'))
    ((congrArg (fun ψ :
          (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).obj W ⟶
          (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).obj W'' =>
          (ShrinkHoms.functor.{u} (CurveFamily B hZ)).map (TwoFibreProductOver.Hom.b ψ))
      ((ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map_comp
        φ φ')).trans
      ((ShrinkHoms.functor.{u} (CurveFamily B hZ)).map_comp _ _))

/-- **The small model of PolarizedCurves is the base change of the small models**: the comparison
1-morphism. -/
def polarizedCurvesSmallComparison :
    polarizedCurvesSmall B hZ h3Z ⟶
      BigFppfOver.twoFibreProduct.{u, u, u} B integerBase hZ (polarizedSmall B hZ)
        (spacesSmall B hZ) (curvesSmall B hZ) (forgetPolarizationSmall B hZ)
        (curvesToSpacesSmall B hZ) :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := polarizedCurvesSmallComparisonFunctor B hZ h3Z
      w := rfl }

/-- The preimage of a morphism under the comparison functor. -/
def polarizedCurvesSmallComparisonPreimage {W W' : (polarizedCurvesSmall B hZ h3Z).val.obj}
    (g : polarizedCurvesSmallComparisonObj B hZ h3Z W ⟶
      polarizedCurvesSmallComparisonObj B hZ h3Z W') :
    (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).obj W ⟶
      (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).obj W' where
  hbase := g.hbase
  a := ULift.up g.a
  b := (ShrinkHoms.inverse.{u} (CurveFamily B hZ)).map g.b
  ha := isHomLift_comp_of_isHomLift (ULiftHom.down : PolarizedFamilyUp B ⥤ PolarizedFamily B)
    (polarizedSmall B hZ).val.p _ (ULift.up g.a) g.ha
  hb := (isHomLift_shrinkHomsInverse_comp_iff (curvesProjectionOver B hZ) _ g.b).1 g.hb
  w := (ShrinkHoms.functor.{u} (CartesianProperFlatSpaces B integerBase hZ)).map_injective
    (((ShrinkHoms.functor.{u} (CartesianProperFlatSpaces B integerBase hZ)).map_comp _ _).trans
      (g.w.trans
        ((ShrinkHoms.functor.{u} (CartesianProperFlatSpaces B integerBase hZ)).map_comp _ _).symm))

/-- The comparison functor from the small model of PolarizedCurves to the base change of the small
models is full. -/
instance : (polarizedCurvesSmallComparisonFunctor B hZ h3Z).Full where
  map_surjective {W W'} g := by
    let ψ := polarizedCurvesSmallComparisonPreimage B hZ h3Z g
    refine ⟨(ShrinkHoms.functor.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map ψ, ?_⟩
    have hψ : (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map
        ((ShrinkHoms.functor.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).map ψ) = ψ :=
      shrinkHomsInverse_map_functor_map.{u} ψ
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · exact congrArg (fun χ => χ.a.down) hψ
    · exact (congrArg (fun χ :
            (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).obj W ⟶
            (ShrinkHoms.inverse.{u} (polarizedCurvesFiberedCategory B hZ h3Z).val.obj).obj W' =>
          (ShrinkHoms.functor.{u} (CurveFamily B hZ)).map (TwoFibreProductOver.Hom.b χ)) hψ).trans
        (shrinkHomsFunctor_map_inverse_map.{u} (C := CurveFamily B hZ) g.b)

/-- Every object of the base change of the small models is, up to a vertical morphism, the image
of an object of the small model of PolarizedCurves. -/
private theorem exists_polarizedCurvesSmallComparison_obj (U : BigFppfOver B integerBase hZ)
    (y : PolarizedCurveSmallObj B hZ) (hy : y.base = U) :
    ∃ (x : (polarizedCurvesSmall B hZ h3Z).val.obj)
      (_ : (polarizedCurvesSmall B hZ h3Z).val.p.obj x = U)
      (t : polarizedCurvesSmallComparisonObj B hZ h3Z x ⟶ y),
      (TwoFibreProductOver.structureFunctor _ _ _ _ _).IsHomLift (𝟙 U) t := by
  subst hy
  let W0 : (polarizedCurvesFiberedCategory B hZ h3Z).val.obj :=
    { base := y.base
      x := ULiftHom.objUp.{u + 1, u + 1} y.x
      y := ShrinkHoms.fromShrinkHoms y.y
      hx := y.hx
      hy := y.hy
      iso := (ShrinkHoms.inverse.{u} (CartesianProperFlatSpaces B integerBase hZ)).mapIso y.iso
      vertical := (isHomLift_shrinkHomsInverse_comp_iff
        (cartesianProperFlatProjection B integerBase hZ) _ y.iso.hom).1 y.vertical }
  let t : polarizedCurvesSmallComparisonObj B hZ h3Z (ShrinkHoms.toShrinkHoms W0) ⟶ y :=
    { hbase := 𝟙 y.base
      a := 𝟙 y.x
      b := 𝟙 y.y
      ha := IsHomLift.id y.hx
      hb := IsHomLift.id y.hy
      w := (congrArg (· ≫ y.iso.hom) (CategoryTheory.Functor.map_id
          (CatFiberedInGroupoids.homFunctor (forgetPolarizationSmall B hZ)) y.x)).trans
        ((Category.id_comp _).trans
          ((shrinkHomsFunctor_map_inverse_map.{u} (C := CartesianProperFlatSpaces B integerBase hZ)
            y.iso.hom).symm.trans
            ((Category.comp_id _).symm.trans
              (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id
                (CatFiberedInGroupoids.homFunctor (curvesToSpacesSmall B hZ)) y.y).symm)))) }
  exact ⟨ShrinkHoms.toShrinkHoms W0, rfl, t,
    IsHomLift.map (TwoFibreProductOver.structureFunctor _ _ _ _ _) t⟩

/-- The comparison from the small model of PolarizedCurves to the base change of the small models
is limit preserving on objects: it is full and essentially surjective on fibres. -/
private theorem isLimitPreservingOnObjects_polarizedCurvesSmallComparison :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B integerBase hZ
      (polarizedCurvesSmall B hZ h3Z)
      (BigFppfOver.twoFibreProduct.{u, u, u} B integerBase hZ (polarizedSmall B hZ)
        (spacesSmall B hZ) (curvesSmall B hZ) (forgetPolarizationSmall B hZ)
        (curvesToSpacesSmall B hZ))
      (polarizedCurvesSmallComparison B hZ h3Z) := by
  have : (CatFiberedInGroupoids.homFunctor (polarizedCurvesSmallComparison B hZ h3Z)).Full :=
    inferInstanceAs (polarizedCurvesSmallComparisonFunctor B hZ h3Z).Full
  exact isLimitPreservingOnObjects_of_full_of_exists_isHomLift_id B _
    (fun U y hy => exists_polarizedCurvesSmallComparison_obj B hZ h3Z U y hy)

/-- **`PolarizedCurves ⟶ 𝒞urves` is limit preserving on objects** (Stacks 06CU), on the small
models: it is, up to the comparison of
`AlgebraicGeometry.C1783.polarizedCurvesSmallComparison`, the base change
of forgetting the polarization along the inclusion of `𝒞urves` (Stacks 06CV), and forgetting the
polarization is limit preserving on objects because `𝒫olarized` (Stacks 0D43) and
`𝒮paces'_{fp, flat, proper}` (Stacks 0D1I) are limit preserving. -/
private theorem isLimitPreservingOnObjects_polarizedCurvesSmallToCurvesSmall :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B integerBase hZ
      (polarizedCurvesSmall B hZ h3Z)
      (curvesSmall B hZ) (polarizedCurvesSmallToCurvesSmall B hZ h3Z) :=
  BigFppfOver.isLimitPreservingOnObjects_comp B integerBase hZ _ _ _
    (polarizedCurvesSmallComparison B hZ h3Z) _
    (isLimitPreservingOnObjects_polarizedCurvesSmallComparison B hZ h3Z)
    (isLimitPreservingOnObjects_twoFibreProductSnd_forgetPolarizationSmall B hZ)

end Comparison

/-! ### Smoothness of the base changes -/

variable (h3Z : (polarizedProjection B ⋙ schemeOverIntegers B).IsFiberedInGroupoids)

/-- **The base changes of `PolarizedCurves ⟶ 𝒞urves` are smooth** (the second assertion of
Stacks 0D5C, in the form consumed by
`AlgebraicGeometry.polarizedCurvesToCurves_isAlgebraic_smooth_surjective`): the base change
along a scheme point, an algebraic stack by `halg`, is smooth over the scheme. By Stacks 0DP0 it is
enough that it is formally smooth on objects (Stacks 0DPJ, through
`AlgebraicGeometry.C1783.isFormallySmoothOnObjects_baseChange_polarizedCurvesSmall`)
and locally of finite presentation, which follows from limit preservation on objects of
`PolarizedCurves ⟶ 𝒞urves`
(`AlgebraicGeometry.C1783.isLimitPreservingOnObjects_polarizedCurvesSmallToCurvesSmall`). -/
theorem hasPropertyOnSomeSmoothDiagram_baseChange_polarizedCurvesSmall
    (Z : BigFppfOver B integerBase hZ)
    (z : BigFppfOver B Z.left.1 Z.left.2 ⥤ (curvesSmall B hZ).val.obj)
    (hz : z ⋙ (curvesSmall B hZ).val.p = Over.map Z.hom)
    (halg : Stack.IsAlgebraicStack.{u, w₀} B integerBase hZ
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Stack.schemeSliceMap B integerBase hZ Z z hz)
        (polarizedCurvesSmallToCurvesSmall B hZ h3Z)).pt.val) :
    Stack.HasPropertyOnSomeSmoothDiagram B integerBase hZ
      (fun _ _ h => Space.IsSmooth B integerBase hZ h)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (Stack.schemeSliceMap B integerBase hZ Z z hz)
        (polarizedCurvesSmallToCurvesSmall B hZ h3Z)).fst :=
  hasPropertyOnSomeSmoothDiagram_baseChange_polarizedCurvesSmall_of_isLimitPreservingOnObjects B hZ
    h3Z (isLimitPreservingOnObjects_polarizedCurvesSmallToCurvesSmall B hZ h3Z) Z z hz halg

end AlgebraicGeometry.C1783
