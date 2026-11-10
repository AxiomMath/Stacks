module

public import Mathlib.Algebra.Polynomial.Laurent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionInSitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.Additive
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.Multiplicative
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOfRelativeDimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceOver
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackChart
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionAtFiniteTypePoint
public import StacksFrontier.Topology.Dimension.TwoPointSpace
public import StacksFrontier.Examples.Stacks.ClassifyingStackSmoothCovering

/-!
# The quotient stack `[𝔸¹/𝔾ₘ]` and the classifying stack `[Spec k/𝔾ₘ]` (Stacks 0DRK)

Stacks Remark 0DRK contrasts the dimension `dim_x(𝒳)` of an algebraic stack at a point (Stacks
0AFN) with the topological quantity `dim_x |𝒳|`. Over a field `k`, let `𝔾ₘ` act on `𝔸¹` by
multiplication. Then `|[𝔸¹/𝔾ₘ]|` has two points, the images of the two orbits `{0}` and
`𝔸¹ ∖ {0}`, the first a specialisation of the second, so `|[𝔸¹/𝔾ₘ]|` has Krull dimension one;
but `dim_x [𝔸¹/𝔾ₘ] = 0` at both points. The classifying stack `[Spec k/𝔾ₘ]` has a unique point,
at which its dimension is `-1`.

Everything is computed on the tautological chart `U ⟶ [U/R]` of the action groupoid
(`AlgebraicGeometry.Stack.quotientChart`). Its source map `𝔾ₘ × U ⟶ U` is the base change of
`𝔾ₘ ⟶ Spec k`, which is smooth of relative dimension one, so the chart is smooth of relative
dimension one, and the dimension formula of Stacks 0DRJ gives `dim_x = dim_u(U) - 1`, which is
`1 - 1 = 0` for `U = 𝔸¹` and `0 - 1 = -1` for `U = Spec k`. The points of `[𝔸¹/𝔾ₘ]` are the
quotient of `|𝔸¹|` by the relation of Stacks 04XJ: a field-valued point with nonzero coordinate
`λ` is carried to `1` by `λ⁻¹ ∈ 𝔾ₘ`, while an arrow of the action groupoid starting at a point
of the zero locus ends there. The chart is open on points (Stacks 04XL), so `|[𝔸¹/𝔾ₘ]|` carries
the quotient topology: the image of `1` is open because its preimage is `𝔸¹ ∖ {0}`, and the image
of `0` is not, because `{0}` is not open in `𝔸¹`, which has dimension one there.

## Main definitions

* `Stacks.Examples.AffineLineQuotient.scalingModObj`: the scaling action of `𝔾ₘ` on `𝔸¹`, on the
  big fppf site.
* `Stacks.Examples.AffineLineQuotient.affineLineQuotientStack`: the quotient stack `[𝔸¹/𝔾ₘ]`.

## Main results

* `Stacks.Examples.AffineLineQuotient.isAlgebraicStack_affineLineQuotientStack`: `[𝔸¹/𝔾ₘ]` is an
  algebraic stack.
* `Stacks.Examples.AffineLineQuotient.affineLineQuotientStack_points_dimension`: **Stacks 0DRK**
  for `[𝔸¹/𝔾ₘ]`.
* `Stacks.Examples.AffineLineQuotient.classifyingStack_multiplicativeGroup_dimension`:
  **Stacks 0DRK** for `[Spec k/𝔾ₘ]`.

## Implementation notes

`AlgebraicGeometry.Stack.dimensionAtPoint` is defined on objects of the 2-category of algebraic
stacks of Stacks 03YP, whose morphisms are `u`-small, while a quotient stack is a stackification
with larger morphisms. The two statements therefore assert that the quotient stack is equivalent
over the site to such an object (`AlgebraicGeometry.Stack.AlgebraicStacks.smallModel`) and then
compute for *every* object equivalent to it, so that the answer does not depend on the small model.

The group is the multiplicative group algebraic space
`AlgebraicGeometry.Space.multiplicativeGroupSpace` of Stacks 043J, and the affine line is the
additive group scheme of Stacks 022V; the classifying stack is
`AlgebraicGeometry.Stack.classifyingStack`, the quotient of the trivial action on the base.

## References

* [Stacks Project, Tag 0DRK](https://stacks.math.columbia.edu/tag/0DRK)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 04XJ](https://stacks.math.columbia.edu/tag/04XJ)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u w

namespace Stacks.Examples.AffineLineQuotient

/-! ### `𝔸¹` and `𝔾ₘ` are smooth of relative dimension one -/

/-- The polynomial ring in one variable is standard smooth of relative dimension one. -/
theorem isStandardSmoothOfRelativeDimension_polynomialC (R : Type*) [CommRing R] :
    (Polynomial.C : R →+* Polynomial R).IsStandardSmoothOfRelativeDimension 1 := by
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 R (MvPolynomial PUnit.{1} R) :=
    (Algebra.SubmersivePresentation.mvPolynomial.{0} R PUnit).isStandardSmoothOfRelativeDimension
      (by simp [Algebra.Presentation.dimension])
  have h : Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (n := 1)
      (MvPolynomial.uniqueAlgEquiv R PUnit.{1})
  rwa [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at h

/-- The Laurent polynomial ring in one variable is standard smooth of relative dimension one:
it is the localization of the polynomial ring at the variable. -/
theorem isStandardSmoothOfRelativeDimension_laurentC (R : Type*) [CommRing R] :
    (LaurentPolynomial.C : R →+* LaurentPolynomial R).IsStandardSmoothOfRelativeDimension 1 := by
  have h2 : (algebraMap (Polynomial R) (LaurentPolynomial R)).IsStandardSmoothOfRelativeDimension
      0 := RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway Polynomial.X
  have := RingHom.IsStandardSmoothOfRelativeDimension.comp h2
    (isStandardSmoothOfRelativeDimension_polynomialC R)
  have heq : (algebraMap (Polynomial R) (LaurentPolynomial R)).comp Polynomial.C =
      LaurentPolynomial.C := by
    ext a
    simp [LaurentPolynomial.algebraMap_eq_toLaurent]
  rw [heq] at this
  simpa using this

/-- The affine line over the integers is smooth of relative dimension one. -/
@[sga "3 I 4.4.4" "special case"]
instance smoothOfRelativeDimension_additiveGroup :
    SmoothOfRelativeDimension 1 (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  change SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom Polynomial.C))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    (isStandardSmoothOfRelativeDimension_polynomialC _)

/-- The multiplicative group over the integers is smooth of relative dimension one. -/
@[sga "3 I 4.4.4" "special case"]
instance smoothOfRelativeDimension_multiplicativeGroup :
    SmoothOfRelativeDimension 1 (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  change SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom LaurentPolynomial.C))
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    (isStandardSmoothOfRelativeDimension_laurentC _)

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

/-- The affine line over `S`, as an object of the site, is smooth of relative dimension one
over `S`. -/
instance smoothOfRelativeDimension_additiveGroupSiteObject :
    SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme C S hS).map
      (Over.mkIdTerminal.from (Space.additiveGroupSiteObject C S hS))) := by
  have h : Over.mkIdTerminal.from (Space.additiveGroupSiteObject C S hS) =
      Over.homMk (Space.additiveGroupSiteObject C S hS).hom :=
    Over.mkIdTerminal.hom_ext _ _
  rw [h]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
    (IsPullback.of_hasPullback _ _) inferInstance

/-- The multiplicative group over `S`, as an object of the site, is smooth of relative
dimension one over `S`. -/
instance smoothOfRelativeDimension_multiplicativeGroupSiteObject :
    SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme C S hS).map
      (Over.mkIdTerminal.from (Space.multiplicativeGroupSiteObject C S hS))) := by
  have h : Over.mkIdTerminal.from (Space.multiplicativeGroupSiteObject C S hS) =
      Over.homMk (Space.multiplicativeGroupSiteObject C S hS).hom :=
    Over.mkIdTerminal.hom_ext _ _
  rw [h]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
    (IsPullback.of_hasPullback _ _) inferInstance

/-! ### The scaling action of `𝔾ₘ` on `𝔸¹` -/

/-- The scheme underlying an object of the site. -/
noncomputable abbrev underlyingScheme (T : BigFppfOver C S hS) : Scheme.{u} :=
  ((Space.toSchemeOver C S hS).obj T).left

/-- The points of `𝔾ₘ,S` over an object `T` of the site are the units of `Γ(T, 𝒪_T)`, as a
group (Stacks 022U). -/
noncomputable def unitsEquiv (T : BigFppfOver C S hS) :
    (Space.multiplicativeGroupPointsOnSite C S hS).obj (Opposite.op T) ≃*
      (Γ(underlyingScheme C S hS T, ⊤))ˣ :=
  ((baseChangePointsIsoGlobalUnits S).app
    (Opposite.op ((Space.toSchemeOver C S hS).obj T))).groupIsoToMulEquiv

/-- The points of `𝔸¹_S` over an object `T` of the site are the global sections of `𝒪_T`
(Stacks 022V). -/
noncomputable def sectionEquiv (T : BigFppfOver C S hS) :
    (T ⟶ Space.additiveGroupSiteObject C S hS) ≃ Γ(underlyingScheme C S hS T, ⊤) :=
  (((Functor.FullyFaithful.ofFullyFaithful C.inclusion).over (X := C.obj hS)).homEquiv).trans
    ((additiveGroupBaseChangeRepresentableBy S).homEquiv)

/-- `Stacks.Examples.AffineLineQuotient.unitsEquiv` is natural in the object of the site. -/
theorem unitsEquiv_naturality {T U : (BigFppfOver C S hS)ᵒᵖ} (f : T ⟶ U)
    (g : (Space.multiplicativeGroupPointsOnSite C S hS).obj T) :
    ((unitsEquiv C S hS U.unop
        ((Space.multiplicativeGroupPointsOnSite C S hS ⋙ forget GrpCat).map f g) :
        (Γ(underlyingScheme C S hS U.unop, ⊤))ˣ) : Γ(underlyingScheme C S hS U.unop, ⊤)) =
      (Scheme.Γ.map ((Space.toSchemeOver C S hS).map f.unop).left.op).hom
        (unitsEquiv C S hS T.unop g : Γ(underlyingScheme C S hS T.unop, ⊤)) :=
  congrArg Units.val (ConcreteCategory.congr_hom
    ((baseChangePointsIsoGlobalUnits S).hom.naturality
      ((Space.toSchemeOver C S hS).map f.unop).op) g)

/-- `Stacks.Examples.AffineLineQuotient.sectionEquiv` is natural in the object of the site. -/
theorem sectionEquiv_naturality {T U : BigFppfOver C S hS} (f : T ⟶ U)
    (x : U ⟶ Space.additiveGroupSiteObject C S hS) :
    sectionEquiv C S hS T (f ≫ x) =
      (Scheme.Γ.map ((Space.toSchemeOver C S hS).map f).left.op).hom (sectionEquiv C S hS U x) := by
  change (additiveGroupBaseChangeRepresentableBy S).homEquiv
      ((Space.toSchemeOver C S hS).map (f ≫ x)) = _
  rw [Functor.map_comp]
  exact (additiveGroupBaseChangeRepresentableBy S).homEquiv_comp _ _

/-- The scaling action `(λ, x) ↦ λx` of `𝔾ₘ` on `𝔸¹`, as a morphism of presheaves on the site
out of the product of their functors of points. -/
noncomputable def scalingSMulHom :
    (Space.multiplicativeGroupPointsOnSite C S hS ⋙ forget GrpCat) ⊗
        yoneda.obj (Space.additiveGroupSiteObject C S hS) ⟶
      yoneda.obj (Space.additiveGroupSiteObject C S hS) where
  app T := ↾fun p : (Space.multiplicativeGroupPointsOnSite C S hS ⋙ forget GrpCat).obj T ×
      (yoneda.obj (Space.additiveGroupSiteObject C S hS)).obj T =>
    (sectionEquiv C S hS T.unop).symm
      ((unitsEquiv C S hS T.unop p.1 : Γ(underlyingScheme C S hS T.unop, ⊤)) *
        sectionEquiv C S hS T.unop p.2)
  naturality := by
    intro T U f
    ext p
    change (sectionEquiv C S hS U.unop).symm
        ((unitsEquiv C S hS U.unop
          ((Space.multiplicativeGroupPointsOnSite C S hS ⋙ forget GrpCat).map f p.1) :
            Γ(underlyingScheme C S hS U.unop, ⊤)) *
          sectionEquiv C S hS U.unop (f.unop ≫ p.2)) =
      f.unop ≫ (sectionEquiv C S hS T.unop).symm
        ((unitsEquiv C S hS T.unop p.1 : Γ(underlyingScheme C S hS T.unop, ⊤)) *
          sectionEquiv C S hS T.unop p.2)
    apply (sectionEquiv C S hS U.unop).injective
    rw [Equiv.apply_symm_apply, sectionEquiv_naturality, sectionEquiv_naturality,
      Equiv.apply_symm_apply, unitsEquiv_naturality]
    exact (map_mul _ _ _).symm

/-- **The scaling action of `𝔾ₘ` on `𝔸¹`**, as an action of the functor of points of `𝔾ₘ,S` on
the functor of points of `𝔸¹_S` over the big fppf site of `S`: a unit `λ` of `Γ(T, 𝒪_T)` sends
a section `x` to `λx`. -/
noncomputable instance scalingModObj :
    ModObj (Space.multiplicativeGroupPointsOnSite C S hS ⋙ forget GrpCat)
      (yoneda.obj (Space.additiveGroupSiteObject C S hS)) where
  smul := scalingSMulHom C S hS
  one_smul := by
    ext T x
    change (sectionEquiv C S hS T.unop).symm
        ((unitsEquiv C S hS T.unop 1 : Γ(underlyingScheme C S hS T.unop, ⊤)) *
          sectionEquiv C S hS T.unop x.2) = x.2
    rw [map_one, Units.val_one, one_mul, Equiv.symm_apply_apply]
  mul_smul := by
    ext T x
    change (sectionEquiv C S hS T.unop).symm
        ((unitsEquiv C S hS T.unop (x.1.1 * x.1.2) : Γ(underlyingScheme C S hS T.unop, ⊤)) *
          sectionEquiv C S hS T.unop x.2) =
      (sectionEquiv C S hS T.unop).symm
        ((unitsEquiv C S hS T.unop x.1.1 : Γ(underlyingScheme C S hS T.unop, ⊤)) *
          sectionEquiv C S hS T.unop ((sectionEquiv C S hS T.unop).symm
            ((unitsEquiv C S hS T.unop x.1.2 : Γ(underlyingScheme C S hS T.unop, ⊤)) *
              sectionEquiv C S hS T.unop x.2)))
    apply (sectionEquiv C S hS T.unop).symm.injective.eq_iff.mpr
    rw [Equiv.apply_symm_apply, map_mul (unitsEquiv C S hS T.unop), Units.val_mul, mul_assoc]

/-! ### Group spaces over the base smooth of relative dimension one -/

/-- **The projection `F ×_S Q ⟶ F` from the restriction of an algebraic space to a presheaf `Q`
represented by an object of the site smooth of relative dimension `d` over `S` is smooth of
relative dimension `d`**: it is the base change of the structure morphism of that object. -/
theorem isSmoothOfRelativeDimension_prod_fst {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace C S hS F) (Q : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    {a : BigFppfOver C S hS} (r : Q.RepresentableBy a) (d : ℕ)
    [SmoothOfRelativeDimension d
      ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from a))] :
    Space.IsSmoothOfRelativeDimension C S hS d (prod.fst : F ⨯ Q ⟶ F) := by
  have hbase := Space.isSmoothOfRelativeDimension_prod_fst_yoneda_obj C S hS a d hF
  have hprod : IsAlgebraicSpace C S hS (F ⨯ yoneda.obj a) :=
    isAlgebraicSpace_of_iso C S hS (prod.braiding F (yoneda.obj a))
      (Space.isAlgebraicSpace_prod_yoneda_obj a hF)
  let e : (F ⨯ Q) ≅ (F ⨯ yoneda.obj a) := prod.mapIso (Iso.refl F) r.toIso.symm
  have hsrc : IsAlgebraicSpace C S hS (F ⨯ Q) := isAlgebraicSpace_of_iso C S hS e hprod
  have hcomp : e.hom ≫ (prod.fst : F ⨯ yoneda.obj a ⟶ F) = (prod.fst : F ⨯ Q ⟶ F) := by
    simp [e]
  have : (Space.smoothOfRelativeDimensionProperty C S hS d).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let e' : (⟨F ⨯ Q, hsrc⟩ : AlgebraicSpaces C S hS) ≅ ⟨F ⨯ yoneda.obj a, hprod⟩ :=
    ObjectProperty.isoMk _ e
  have h2 := ((Space.smoothOfRelativeDimensionProperty C S hS d).cancel_left_of_respectsIso e'.hom
    (ObjectProperty.homMk (prod.fst : F ⨯ yoneda.obj a ⟶ F) :
      (⟨F ⨯ yoneda.obj a, hprod⟩ : AlgebraicSpaces C S hS) ⟶ ⟨F, hF⟩)).2 hbase
  change Space.IsSmoothOfRelativeDimension C S hS d (e.hom ≫ prod.fst) at h2
  rwa [← hcomp]

/-- **The restriction `B ×_S Q ⟶ B` of a presheaf `Q` represented by an object of the site smooth
of relative dimension `d` over `S` is smooth of relative dimension `d`.** -/
theorem isSmoothOfRelativeDimension_overStar {F : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace C S hS F) (Q : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u)
    {a : BigFppfOver C S hS} (r : Q.RepresentableBy a) (d : ℕ)
    [SmoothOfRelativeDimension d
      ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from a))] :
    Space.IsSmoothOfRelativeDimension C S hS d ((Space.overStar C S hS F).obj Q).hom := by
  have hhom : ((Space.overStar C S hS F).obj Q).hom = (prod.fst : F ⨯ Q ⟶ F) := by
    simp only [Space.overStar, Over.star_obj_hom]
    rfl
  rw [hhom]
  exact isSmoothOfRelativeDimension_prod_fst C S hS hF Q r d

/-- **The source map of the action groupoid of a group smooth of relative dimension `d` is
smooth of relative dimension `d`**: it is the second projection `G ×_B X ⟶ X`, the base change of
`G ⟶ B`. -/
theorem isSmoothOfRelativeDimension_groupoidOfAction_source (B : AlgebraicSpaces C S hS)
    (G X : Over B.obj) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace C S hS G.left) (hX : IsAlgebraicSpace C S hS X.left) (d : ℕ)
    (hGd : Space.IsSmoothOfRelativeDimension C S hS d G.hom) :
    Space.IsSmoothOfRelativeDimension C S hS d
      (Space.groupoidOfAction B G X hG hX).groupoid.source.hom :=
  (Space.smoothOfRelativeDimensionProperty C S hS d).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (ObjectProperty.homMk G.hom : (⟨G.left, hG⟩ : AlgebraicSpaces C S hS) ⟶ B)
      (ObjectProperty.homMk X.hom : (⟨X.left, hX⟩ : AlgebraicSpaces C S hS) ⟶ B)) hGd

/-! ### The quotient stack `[𝔸¹/𝔾ₘ]` -/

/-- The multiplicative group `𝔾ₘ` over the base, as a group object of presheaves over it. -/
noncomputable abbrev multiplicativeGroupOver : Over (Space.terminalSpace C S hS).obj :=
  Space.groupOverStar C S hS (Space.terminalSpace C S hS).obj
    (Space.multiplicativeGroupPointsOnSite C S hS)

/-- The affine line `𝔸¹` over the base, as an object of presheaves over it acted on by `𝔾ₘ`. -/
noncomputable abbrev affineLineOver : Over (Space.terminalSpace C S hS).obj :=
  Space.objectOverStar C S hS (Space.terminalSpace C S hS).obj
    (yoneda.obj (Space.additiveGroupSiteObject C S hS))

/-- The multiplicative group `𝔾ₘ` over the base is an algebraic space. -/
theorem isAlgebraicSpace_multiplicativeGroupOver :
    IsAlgebraicSpace C S hS (multiplicativeGroupOver C S hS).left :=
  Space.isAlgebraicSpace_groupOverStar C S hS _ (Space.terminalSpace C S hS).property _
    (Space.pointsOnSiteRepresentableBy C S hS _ _)

/-- The affine line `𝔸¹` over the base is an algebraic space. -/
theorem isAlgebraicSpace_affineLineOver :
    IsAlgebraicSpace C S hS (affineLineOver C S hS).left :=
  Space.isAlgebraicSpace_objectOverStar C S hS _ (Space.terminalSpace C S hS).property _
    (Functor.RepresentableBy.yoneda _)

/-- The action groupoid `(𝔸¹, 𝔾ₘ × 𝔸¹, pr₂, a, m)` of the scaling action (Stacks 0444). -/
noncomputable abbrev scalingGroupoid :
    GroupoidInAlgebraicSpaces C S hS (Space.terminalSpace C S hS) :=
  (Space.groupoidOfAction (Space.terminalSpace C S hS) (multiplicativeGroupOver C S hS)
    (affineLineOver C S hS) (isAlgebraicSpace_multiplicativeGroupOver C S hS)
    (isAlgebraicSpace_affineLineOver C S hS)).groupoid

/-- **The quotient stack `[𝔸¹/𝔾ₘ]`** over `S` of the scaling action of the multiplicative group
on the affine line (Stacks 044Q). -/
noncomputable abbrev affineLineQuotientStack : BasedCategory (BigFppfOver C S hS) :=
  Space.quotientStackOfPointsAction C S hS (Space.terminalSpace C S hS)
    (Space.multiplicativeGroupPointsOnSite C S hS)
    (yoneda.obj (Space.additiveGroupSiteObject C S hS))
    (Space.pointsOnSiteRepresentableBy C S hS _ _) (Functor.RepresentableBy.yoneda _)

/-- `𝔾ₘ` is smooth of relative dimension one over the base. -/
theorem isSmoothOfRelativeDimension_multiplicativeGroupOver :
    Space.IsSmoothOfRelativeDimension C S hS 1 (multiplicativeGroupOver C S hS).hom :=
  isSmoothOfRelativeDimension_overStar C S hS (Space.terminalSpace C S hS).property _
    (Space.pointsOnSiteRepresentableBy C S hS _ _) 1

/-- `𝔸¹` is smooth of relative dimension one over the base. -/
theorem isSmoothOfRelativeDimension_affineLineOver :
    Space.IsSmoothOfRelativeDimension C S hS 1 (affineLineOver C S hS).hom :=
  isSmoothOfRelativeDimension_overStar C S hS (Space.terminalSpace C S hS).property _
    (Functor.RepresentableBy.yoneda _) 1

/-- The source map of the scaling groupoid is smooth of relative dimension one. -/
theorem isSmoothOfRelativeDimension_scalingGroupoid_source :
    Space.IsSmoothOfRelativeDimension C S hS 1 (scalingGroupoid C S hS).source.hom :=
  isSmoothOfRelativeDimension_groupoidOfAction_source C S hS _ _ _ _ _ 1
    (isSmoothOfRelativeDimension_multiplicativeGroupOver C S hS)

/-- **`[𝔸¹/𝔾ₘ]` is an algebraic stack** (Stacks 04TK): `𝔾ₘ` is smooth over the base. -/
theorem isAlgebraicStack_affineLineQuotientStack :
    Stack.IsAlgebraicStack.{u, w} C S hS (affineLineQuotientStack C S hS) :=
  Stack.isAlgebraicStack_quotientStackOfAction _ _ _ _ _
    (isSmoothOfRelativeDimension_multiplicativeGroupOver C S hS).1

/-! ### Points of `𝔸¹` and of the scaling groupoid -/

/-- A point `Spec K ⟶ X` from a field lies in the non-vanishing locus of a global function
exactly when the function pulls back to a nonzero element. -/
theorem mem_basicOpen_iff_appTop_ne_zero {K : Type u} [Field K] {X : Scheme.{u}}
    (φ : Spec (.of K) ⟶ X) (f : Γ(X, ⊤)) (y : Spec (.of K)) :
    φ y ∈ X.basicOpen f ↔ φ.appTop f ≠ 0 := by
  change y ∈ φ ⁻¹ᵁ X.basicOpen f ↔ _
  rw [Scheme.preimage_basicOpen]
  constructor
  · intro h h0
    change y ∈ (Spec (CommRingCat.of K)).basicOpen (φ.appTop f) at h
    rw [h0, Scheme.basicOpen_zero] at h
    exact h
  · intro h
    have hne : (Spec (.of K)).basicOpen (φ.app ⊤ f) ≠ ⊥ := by
      rwa [Ne, basicOpen_eq_bot_iff]
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    rwa [Subsingleton.elim z y] at hz

/-- The coordinate function of the affine line over `S`. -/
noncomputable def coordinate :
    Γ(underlyingScheme C S hS (Space.additiveGroupSiteObject C S hS), ⊤) :=
  (Scheme.Γ.map (pullback.fst (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from S)).op).hom additiveCoordinate

/-- The global section attached to a point of `𝔸¹_S` is the pullback of the coordinate. -/
theorem sectionEquiv_eq_appTop (T : BigFppfOver C S hS)
    (x : T ⟶ Space.additiveGroupSiteObject C S hS) :
    sectionEquiv C S hS T x =
      ((Space.toSchemeOver C S hS).map x).left.appTop (coordinate C S hS) := by
  change (additiveGroupBaseChangeRepresentableBy S).homEquiv ((Space.toSchemeOver C S hS).map x) = _
  refine (additiveGroupBaseChangeRepresentableBy_apply S _).trans ?_
  simp only [additiveGroupPointSection, coordinate]
  rfl

/-- The identification of `𝔸¹` over the base with the functor of points of `𝔸¹_S`. -/
noncomputable abbrev lineIso :
    (affineLineOver C S hS).left ≅ yoneda.obj (Space.additiveGroupSiteObject C S hS) :=
  Space.terminalSpaceProdIso C S hS _

/-- The global section attached to a point of `𝔸¹` over the base. -/
noncomputable def lineSection (T : BigFppfOver C S hS)
    (x : (affineLineOver C S hS).left.obj (Opposite.op T)) : Γ(underlyingScheme C S hS T, ⊤) :=
  sectionEquiv C S hS T ((lineIso C S hS).hom.app (Opposite.op T) x)

/-- `Stacks.Examples.AffineLineQuotient.lineSection` is a bijection. -/
theorem lineSection_injective (T : BigFppfOver C S hS) :
    Function.Injective (lineSection C S hS T) := by
  intro x y h
  simpa using congrArg ((lineIso C S hS).inv.app (Opposite.op T))
    ((sectionEquiv C S hS T).injective h)

/-- `Stacks.Examples.AffineLineQuotient.lineSection` is natural. -/
theorem lineSection_naturality {T U : BigFppfOver C S hS} (f : T ⟶ U)
    (x : (affineLineOver C S hS).left.obj (Opposite.op U)) :
    lineSection C S hS T ((affineLineOver C S hS).left.map f.op x) =
      (Scheme.Γ.map ((Space.toSchemeOver C S hS).map f).left.op).hom (lineSection C S hS U x) := by
  rw [lineSection, lineSection, NatTrans.naturality_apply]
  exact sectionEquiv_naturality C S hS f _

attribute [local instance] Space.pointTopology

/-- The points of `𝔸¹` over the base are the points of the scheme `𝔸¹_S` (Stacks 03BX). -/
noncomputable def lineHomeomorph :
    Space.points C S hS (affineLineOver C S hS).left ≃ₜ
      underlyingScheme C S hS (Space.additiveGroupSiteObject C S hS) :=
  (Space.pointsHomeomorphOfIso C S hS (lineIso C S hS)).trans
    (Space.schemePointsHomeomorph C S hS _)

/-- The zero locus of the coordinate of `𝔸¹_S`. -/
def zeroLocus : Set (underlyingScheme C S hS (Space.additiveGroupSiteObject C S hS)) :=
  ((underlyingScheme C S hS (Space.additiveGroupSiteObject C S hS)).basicOpen
    (coordinate C S hS) : Set _)ᶜ

/-- The zero locus of the coordinate of `𝔸¹` is closed. -/
theorem isClosed_zeroLocus : IsClosed (zeroLocus C S hS) :=
  (TopologicalSpace.Opens.isOpen _).isClosed_compl

/-- A field-valued point of `𝔸¹` lies over the zero locus exactly when its section vanishes. -/
theorem lineHomeomorph_class_mem_zeroLocus_iff
    (p : Space.FieldValuedPoint C S hS (affineLineOver C S hS).left) :
    lineHomeomorph C S hS (p.class C S hS _) ∈ zeroLocus C S hS ↔
      lineSection C S hS (p.siteObject C S hS _) p.value = 0 := by
  have h := mem_basicOpen_iff_appTop_ne_zero
    ((BigFppfOver.toScheme C S hS).map ((lineIso C S hS).hom.app _ p.value) :
      Spec (.of p.carrier) ⟶ underlyingScheme C S hS (Space.additiveGroupSiteObject C S hS))
    (coordinate C S hS) (IsLocalRing.closedPoint p.carrier)
  rw [lineSection, sectionEquiv_eq_appTop]
  exact h.not.trans not_not

/-- The global sections of the spectrum of a field form a field: a nonzero section is a unit. -/
theorem isUnit_of_ne_zero_Γ_Spec {K : Type u} [Field K] {a : Γ(Spec (.of K), ⊤)} (ha : a ≠ 0) :
    IsUnit a := by
  have e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  have hb : e a ≠ 0 := by rwa [ne_eq, map_eq_zero_iff e e.injective]
  simpa using (hb.isUnit.map e.symm)

/-- The global sections of the spectrum of a field form a nontrivial ring. -/
theorem one_ne_zero_Γ_Spec {K : Type u} [Field K] : (1 : Γ(Spec (.of K), ⊤)) ≠ 0 := by
  have e := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  intro h
  simpa using congrArg e h

/-! ### Field-valued points of the arrow space -/

/-- The unit by which a point of `𝔾ₘ × 𝔸¹` acts. -/
noncomputable def arrowUnit (T : BigFppfOver C S hS)
    (v : (scalingGroupoid C S hS).arrows.obj.obj (Opposite.op T)) :
    (Γ(underlyingScheme C S hS T, ⊤))ˣ :=
  unitsEquiv C S hS T ((pullback.fst (multiplicativeGroupOver C S hS).hom
    (affineLineOver C S hS).hom ≫ (prod.snd : (Space.terminalSpace C S hS).obj ⨯ _ ⟶
      (Space.multiplicativeGroupPointsOnSite C S hS ⋙ forget GrpCat))).app _ v)

/-- **The coordinate of the target of a point of `𝔾ₘ × 𝔸¹` is the coordinate of its source
scaled by the unit it carries**: the target map is the scaling action. -/
theorem lineSection_target_eq (T : BigFppfOver C S hS)
    (v : (scalingGroupoid C S hS).arrows.obj.obj (Opposite.op T)) :
    lineSection C S hS T ((scalingGroupoid C S hS).target.hom.app _ v) =
      arrowUnit C S hS T v *
        lineSection C S hS T ((scalingGroupoid C S hS).source.hom.app _ v) := by
  have h := congrArg (fun φ => φ.app (Opposite.op T) v)
    (Space.smul_objectOverStar_left_comp_snd C S hS (Space.terminalSpace C S hS).obj
      (Space.multiplicativeGroupPointsOnSite C S hS)
      (yoneda.obj (Space.additiveGroupSiteObject C S hS)))
  change sectionEquiv C S hS T ((γ[multiplicativeGroupOver C S hS,
    affineLineOver C S hS].left ≫ prod.snd).app _ v) = _
  rw [h]
  change sectionEquiv C S hS T ((sectionEquiv C S hS T).symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The point of `𝔾ₘ` over the base with a prescribed unit. -/
noncomputable def groupElement (T : BigFppfOver C S hS) (c : (Γ(underlyingScheme C S hS T, ⊤))ˣ) :
    (multiplicativeGroupOver C S hS).left.obj (Opposite.op T) :=
  yonedaEquiv (prod.lift ((Space.baseTerminal_yonedaIsTerminal C S hS).from _)
    (yonedaEquiv.symm ((unitsEquiv C S hS T).symm c)))

/-- The point of `𝔾ₘ × 𝔸¹` with a prescribed unit and source. -/
noncomputable def arrowElement (T : BigFppfOver C S hS) (c : (Γ(underlyingScheme C S hS T, ⊤))ˣ)
    (x : (affineLineOver C S hS).left.obj (Opposite.op T)) :
    (scalingGroupoid C S hS).arrows.obj.obj (Opposite.op T) :=
  yonedaEquiv (pullback.lift (yonedaEquiv.symm (groupElement C S hS T c)) (yonedaEquiv.symm x)
    ((Space.baseTerminal_yonedaIsTerminal C S hS).hom_ext _ _))

/-- The source of the point `arrowElement T c x` of `𝔾ₘ × 𝔸¹` is `x`. -/
theorem source_app_arrowElement (T : BigFppfOver C S hS) (c : (Γ(underlyingScheme C S hS T, ⊤))ˣ)
    (x : (affineLineOver C S hS).left.obj (Opposite.op T)) :
    (scalingGroupoid C S hS).source.hom.app _ (arrowElement C S hS T c x) = x := by
  let L := pullback.lift (f := (multiplicativeGroupOver C S hS).hom)
    (g := (affineLineOver C S hS).hom) (yonedaEquiv.symm (groupElement C S hS T c))
    (yonedaEquiv.symm x) ((Space.baseTerminal_yonedaIsTerminal C S hS).hom_ext _ _)
  have h3 : L ≫ pullback.snd (multiplicativeGroupOver C S hS).hom (affineLineOver C S hS).hom =
      yonedaEquiv.symm x := pullback.lift_snd _ _ _
  exact ((yonedaEquiv_comp L _).symm.trans (congrArg yonedaEquiv h3)).trans
    (Equiv.apply_symm_apply _ _)

/-- The unit of the point `arrowElement T c x` of `𝔾ₘ × 𝔸¹` is `c`. -/
theorem arrowUnit_arrowElement (T : BigFppfOver C S hS) (c : (Γ(underlyingScheme C S hS T, ⊤))ˣ)
    (x : (affineLineOver C S hS).left.obj (Opposite.op T)) :
    arrowUnit C S hS T (arrowElement C S hS T c x) = c := by
  let L := pullback.lift (f := (multiplicativeGroupOver C S hS).hom)
    (g := (affineLineOver C S hS).hom) (yonedaEquiv.symm (groupElement C S hS T c))
    (yonedaEquiv.symm x) ((Space.baseTerminal_yonedaIsTerminal C S hS).hom_ext _ _)
  let M := prod.lift ((Space.baseTerminal_yonedaIsTerminal C S hS).from (yoneda.obj T))
    ((yonedaEquiv (F := Space.multiplicativeGroupPointsOnSite C S hS ⋙ forget GrpCat)).symm
      ((unitsEquiv C S hS T).symm c))
  let p₂ : (Space.terminalSpace C S hS).obj ⨯ _ ⟶
      (Space.multiplicativeGroupPointsOnSite C S hS ⋙ forget GrpCat) := prod.snd
  have h3 : L ≫ pullback.fst (multiplicativeGroupOver C S hS).hom (affineLineOver C S hS).hom ≫
      p₂ = M ≫ p₂ := by
    have h6 : L ≫ pullback.fst (multiplicativeGroupOver C S hS).hom (affineLineOver C S hS).hom =
        yonedaEquiv.symm (groupElement C S hS T c) := pullback.lift_fst _ _ _
    have h7 : (yonedaEquiv.symm (groupElement C S hS T c) : yoneda.obj T ⟶ _) = M :=
      Equiv.symm_apply_apply _ _
    exact (Category.assoc _ _ _).symm.trans (by rw [h6, h7]; rfl)
  have h4 : M ≫ p₂ = (yonedaEquiv (F := Space.multiplicativeGroupPointsOnSite C S hS ⋙
      forget GrpCat)).symm ((unitsEquiv C S hS T).symm c) := prod.lift_snd _ _
  have h5 : (pullback.fst (multiplicativeGroupOver C S hS).hom (affineLineOver C S hS).hom ≫
      p₂).app _ (arrowElement C S hS T c x) = (unitsEquiv C S hS T).symm c :=
    ((yonedaEquiv_comp L _).symm.trans (congrArg yonedaEquiv (h3.trans h4))).trans
      (Equiv.apply_symm_apply _ _)
  change unitsEquiv C S hS T _ = c
  rw [h5, MulEquiv.apply_symm_apply]

/-- The point of `𝔸¹` over the base with a prescribed global section. -/
noncomputable def linePoint (T : BigFppfOver C S hS) (a : Γ(underlyingScheme C S hS T, ⊤)) :
    (affineLineOver C S hS).left.obj (Opposite.op T) :=
  (lineIso C S hS).inv.app (Opposite.op T) ((sectionEquiv C S hS T).symm a)

/-- The global section of the point `linePoint T a` of `𝔸¹` is `a`. -/
@[simp]
theorem lineSection_linePoint (T : BigFppfOver C S hS) (a : Γ(underlyingScheme C S hS T, ⊤)) :
    lineSection C S hS T (linePoint C S hS T a) = a := by
  simp [lineSection, linePoint]

/-! ### The two points of `[𝔸¹/𝔾ₘ]` -/

section Field

variable {k : Type u} [Field k] (hk : C.Contains (Spec (.of k)))

/-- The base `Spec k`, as an object of its own big fppf site. -/
noncomputable abbrev baseObject : BigFppfOver C (Spec (.of k)) hk :=
  Over.mk (⟨𝟙 (Spec (.of k))⟩ : C.obj hk ⟶ C.obj hk)

/-- The `k`-valued point of `𝔸¹_k` with a prescribed coordinate. -/
noncomputable def rationalPoint (a : Γ(underlyingScheme C (Spec (.of k)) hk (baseObject C hk), ⊤)) :
    Space.FieldValuedPoint C (Spec (.of k)) hk (affineLineOver C (Spec (.of k)) hk).left where
  carrier := k
  contained := hk
  toBase := 𝟙 _
  value := linePoint C (Spec (.of k)) hk (baseObject C hk) a

/-- **A field-valued point of `𝔸¹_k` whose coordinate is the pullback of a rational coordinate
`a` is the rational point `a`.** -/
theorem class_eq_class_rationalPoint
    (p : Space.FieldValuedPoint C (Spec (.of k)) hk (affineLineOver C (Spec (.of k)) hk).left)
    (a : Γ(underlyingScheme C (Spec (.of k)) hk (baseObject C hk), ⊤))
    (h : lineSection C (Spec (.of k)) hk (p.siteObject C (Spec (.of k)) hk _) p.value =
      (Scheme.Γ.map ((Space.toSchemeOver C (Spec (.of k)) hk).map
        (Over.homMk ⟨p.toBase⟩ (by ext; rfl) :
          p.siteObject C (Spec (.of k)) hk _ ⟶ baseObject C hk)).left.op).hom a) :
    p.class C (Spec (.of k)) hk _ = (rationalPoint C hk a).class C (Spec (.of k)) hk _ := by
  refine (Space.FieldValuedPoint.class_eq_class_iff C (Spec (.of k)) hk _ _ _).2
    ⟨p, Space.FieldValuedPoint.dominates_refl C (Spec (.of k)) hk _ p,
      ⟨Over.homMk ⟨p.toBase⟩ (by ext; rfl), ?_⟩⟩
  apply lineSection_injective
  rw [lineSection_naturality, h]
  exact congrArg _ (lineSection_linePoint C (Spec (.of k)) hk (baseObject C hk) a)

variable (𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
  (e : StacksRepresentableCFG.EquivalenceOver
    (affineLineQuotientStack C (Spec (.of k)) hk).p 𝒳.val.val.p)

/-- The map `|𝔸¹| ⟶ |𝒳|` induced by the chart of an algebraic stack presented as `[𝔸¹/𝔾ₘ]`. -/
noncomputable abbrev chartPointsMap :
    Space.points C (Spec (.of k)) hk (affineLineOver C (Spec (.of k)) hk).left →
      Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property :=
  Stack.spacePointMap C (Spec (.of k)) hk _ 𝒳.val
    (Stack.quotientChart (scalingGroupoid C (Spec (.of k)) hk) 𝒳 e).hom.hom

/-- The image in `|𝒳|` of the origin of `𝔸¹`. -/
noncomputable abbrev originPoint : Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property :=
  chartPointsMap C hk 𝒳 e ((rationalPoint C hk 0).class C (Spec (.of k)) hk _)

/-- The image in `|𝒳|` of the point `1` of `𝔸¹`. -/
noncomputable abbrev unitPoint : Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property :=
  chartPointsMap C hk 𝒳 e ((rationalPoint C hk 1).class C (Spec (.of k)) hk _)

/-- The rational point `a` of `𝔸¹` lies over the zero locus exactly when `a = 0`. -/
theorem lineHomeomorph_rationalPoint_mem_zeroLocus_iff
    (a : Γ(underlyingScheme C (Spec (.of k)) hk (baseObject C hk), ⊤)) :
    lineHomeomorph C (Spec (.of k)) hk ((rationalPoint C hk a).class C (Spec (.of k)) hk _) ∈
      zeroLocus C (Spec (.of k)) hk ↔ a = 0 := by
  rw [lineHomeomorph_class_mem_zeroLocus_iff]
  exact iff_of_eq (congrArg (· = 0) (lineSection_linePoint C (Spec (.of k)) hk _ a))

/-- **Every point of `𝔸¹` on the zero locus maps to the origin of `[𝔸¹/𝔾ₘ]`, and every other
point maps to the image of `1`**: a point with nonzero coordinate `λ` is moved to `1` by
`λ⁻¹ ∈ 𝔾ₘ`. -/
theorem chartPointsMap_eq (u : Space.points C (Spec (.of k)) hk
      (affineLineOver C (Spec (.of k)) hk).left) :
    (lineHomeomorph C (Spec (.of k)) hk u ∈ zeroLocus C (Spec (.of k)) hk →
        chartPointsMap C hk 𝒳 e u = originPoint C hk 𝒳 e) ∧
      (lineHomeomorph C (Spec (.of k)) hk u ∉ zeroLocus C (Spec (.of k)) hk →
        chartPointsMap C hk 𝒳 e u = unitPoint C hk 𝒳 e) := by
  induction u using Quot.ind with
  | mk p =>
  rw [show Quot.mk _ p = p.class C (Spec (.of k)) hk _ from rfl,
    lineHomeomorph_class_mem_zeroLocus_iff]
  constructor
  · intro h0
    rw [class_eq_class_rationalPoint C hk p 0 (h0.trans (map_zero _).symm)]
  · intro hne
    obtain ⟨c₀, hc₀⟩ := isUnit_of_ne_zero_Γ_Spec (K := p.carrier) hne
    obtain ⟨K, contained, toBase, value⟩ := p
    let ρ : Space.FieldValuedPoint C (Spec (.of k)) hk
        (scalingGroupoid C (Spec (.of k)) hk).arrows.obj :=
      { carrier := K, contained := contained, toBase := toBase
        value := arrowElement C (Spec (.of k)) hk _ c₀⁻¹ value }
    have hs : Space.FieldValuedPoint.map C (Spec (.of k)) hk _
        (scalingGroupoid C (Spec (.of k)) hk).source.hom ρ =
        ⟨K, contained, toBase, value⟩ := by
      simp only [Space.FieldValuedPoint.map, ρ]
      congr 1
      exact source_app_arrowElement C (Spec (.of k)) hk _ _ _
    have ht : lineSection C (Spec (.of k)) hk _
        (Space.FieldValuedPoint.map C (Spec (.of k)) hk _
          (scalingGroupoid C (Spec (.of k)) hk).target.hom ρ).value = 1 := by
      change lineSection C (Spec (.of k)) hk _
        ((scalingGroupoid C (Spec (.of k)) hk).target.hom.app _ ρ.value) = 1
      rw [lineSection_target_eq, source_app_arrowElement, arrowUnit_arrowElement]
      exact (congrArg (fun z => ((c₀⁻¹ : (Γ(Spec (.of K), ⊤))ˣ) : Γ(Spec (.of K), ⊤)) * z)
        hc₀.symm).trans (Units.inv_mul c₀)
    have hrel := (Stack.spacePointMap_quotientChart_eq_iff (scalingGroupoid C (Spec (.of k)) hk)
      𝒳 e (Space.FieldValuedPoint.class C (Spec (.of k)) hk _ ⟨K, contained, toBase, value⟩)
      ((Space.FieldValuedPoint.map C (Spec (.of k)) hk _
          (scalingGroupoid C (Spec (.of k)) hk).target.hom ρ).class C (Spec (.of k)) hk _)).2
      ⟨ρ.class C (Spec (.of k)) hk _, by rw [Space.pointsMap_class, hs],
        Space.pointsMap_class C (Spec (.of k)) hk _ _ ρ⟩
    exact hrel.trans <| congrArg (chartPointsMap C hk 𝒳 e) (class_eq_class_rationalPoint C hk
      (Space.FieldValuedPoint.map C (Spec (.of k)) hk _
        (scalingGroupoid C (Spec (.of k)) hk).target.hom ρ) 1 (ht.trans (map_one _).symm))

/-- **The origin and the image of `1` are distinct points of `[𝔸¹/𝔾ₘ]`**: an arrow of the
scaling groupoid starting at a point of the zero locus ends on the zero locus. -/
theorem originPoint_ne_unitPoint : originPoint C hk 𝒳 e ≠ unitPoint C hk 𝒳 e := by
  intro h
  obtain ⟨r, hs, ht⟩ := (Stack.spacePointMap_quotientChart_eq_iff
    (scalingGroupoid C (Spec (.of k)) hk) 𝒳 e _ _).1 h
  induction r using Quot.ind with
  | mk ρ =>
  rw [show Quot.mk _ ρ = ρ.class C (Spec (.of k)) hk _ from rfl, Space.pointsMap_class] at hs ht
  have h00 := (lineHomeomorph_rationalPoint_mem_zeroLocus_iff C hk 0).2 rfl
  rw [← hs] at h00
  have h0 := (lineHomeomorph_class_mem_zeroLocus_iff C (Spec (.of k)) hk
    (Space.FieldValuedPoint.map C (Spec (.of k)) hk _
      (scalingGroupoid C (Spec (.of k)) hk).source.hom ρ)).1 h00
  have h1 : lineHomeomorph C (Spec (.of k)) hk
      ((Space.FieldValuedPoint.map C (Spec (.of k)) hk _
        (scalingGroupoid C (Spec (.of k)) hk).target.hom ρ).class C (Spec (.of k)) hk _) ∈
      zeroLocus C (Spec (.of k)) hk := by
    refine (lineHomeomorph_class_mem_zeroLocus_iff C (Spec (.of k)) hk _).2 ?_
    change lineSection C (Spec (.of k)) hk _
      ((scalingGroupoid C (Spec (.of k)) hk).target.hom.app _ ρ.value) = 0
    rw [lineSection_target_eq, show lineSection C (Spec (.of k)) hk _
      ((scalingGroupoid C (Spec (.of k)) hk).source.hom.app _ ρ.value) = 0 from h0, mul_zero]
  rw [ht, lineHomeomorph_rationalPoint_mem_zeroLocus_iff] at h1
  exact one_ne_zero_Γ_Spec (K := k) h1

/-! ### The topology of `[𝔸¹/𝔾ₘ]` -/

/-- `𝔸¹_k` has dimension one at each of its points (Stacks 0B9D). -/
theorem topologicalKrullDimAt_affineLine
    (z : underlyingScheme C (Spec (.of k)) hk (Space.additiveGroupSiteObject C (Spec (.of k)) hk)) :
    topologicalKrullDimAt _ z = 1 :=
  topologicalKrullDimAt_eq_one_of_smoothOfRelativeDimension_one (k := k)
    (f := (BigFppfOver.toScheme C (Spec (.of k)) hk).map
      (Over.mkIdTerminal.from (Space.additiveGroupSiteObject C (Spec (.of k)) hk))) z

/-- The zero locus of the coordinate of `𝔸¹_k` is the origin. -/
theorem zeroLocus_eq_singleton : zeroLocus C (Spec (.of k)) hk =
    {lineHomeomorph C (Spec (.of k)) hk ((rationalPoint C hk 0).class C (Spec (.of k)) hk _)} := by
  ext y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨u, rfl⟩ := (lineHomeomorph C (Spec (.of k)) hk).surjective y
    induction u using Quot.ind with
    | mk p =>
    rw [show Quot.mk _ p = p.class C (Spec (.of k)) hk _ from rfl,
      lineHomeomorph_class_mem_zeroLocus_iff] at hy
    rw [Set.mem_singleton_iff, show Quot.mk _ p = p.class C (Spec (.of k)) hk _ from rfl,
      class_eq_class_rationalPoint C hk p 0 (hy.trans (map_zero _).symm)]
  · rw [Set.mem_singleton_iff] at hy
    rw [hy, lineHomeomorph_rationalPoint_mem_zeroLocus_iff]

/-- The origin of `𝔸¹_k` is not an open point: `𝔸¹_k` has dimension one there. -/
theorem not_isOpen_zeroLocus : ¬ IsOpen (zeroLocus C (Spec (.of k)) hk) := by
  intro h
  rw [zeroLocus_eq_singleton] at h
  have := topologicalKrullDimAt_eq_zero_of_isOpen_singleton h
  rw [topologicalKrullDimAt_affineLine] at this
  exact one_ne_zero this

attribute [local instance] Stack.pointTopology

/-- **`[𝔸¹/𝔾ₘ]` has exactly two points**, the origin and the image of `1`. -/
theorem eq_originPoint_or_eq_unitPoint (x : Stack.points C (Spec (.of k)) hk 𝒳.val.val
      𝒳.val.property) :
    x = originPoint C hk 𝒳 e ∨ x = unitPoint C hk 𝒳 e := by
  obtain ⟨u, rfl⟩ := Stack.surjective_spacePointMap_quotientChart
    (scalingGroupoid C (Spec (.of k)) hk) 𝒳 e x
  by_cases hu : lineHomeomorph C (Spec (.of k)) hk u ∈ zeroLocus C (Spec (.of k)) hk
  · exact Or.inl ((chartPointsMap_eq C hk 𝒳 e u).1 hu)
  · exact Or.inr ((chartPointsMap_eq C hk 𝒳 e u).2 hu)

/-- The preimage of `originPoint` under `|𝔸¹| ⟶ |𝒳|` is the zero locus. -/
theorem chartPointsMap_preimage_originPoint :
    chartPointsMap C hk 𝒳 e ⁻¹' {originPoint C hk 𝒳 e} =
      lineHomeomorph C (Spec (.of k)) hk ⁻¹' zeroLocus C (Spec (.of k)) hk := by
  ext u
  refine ⟨fun hu => ?_, fun hu => (chartPointsMap_eq C hk 𝒳 e u).1 hu⟩
  by_contra h
  exact originPoint_ne_unitPoint C hk 𝒳 e ((Set.mem_singleton_iff.1 hu).symm.trans
    ((chartPointsMap_eq C hk 𝒳 e u).2 h))

/-- The preimage of `unitPoint` under `|𝔸¹| ⟶ |𝒳|` is the complement of the zero locus. -/
theorem chartPointsMap_preimage_unitPoint :
    chartPointsMap C hk 𝒳 e ⁻¹' {unitPoint C hk 𝒳 e} =
      lineHomeomorph C (Spec (.of k)) hk ⁻¹' (zeroLocus C (Spec (.of k)) hk)ᶜ := by
  ext u
  refine ⟨fun hu h => ?_, fun hu => (chartPointsMap_eq C hk 𝒳 e u).2 hu⟩
  exact originPoint_ne_unitPoint C hk 𝒳 e (((chartPointsMap_eq C hk 𝒳 e u).1 h).symm.trans
    (Set.mem_singleton_iff.1 hu))

/-- The source morphism `𝔾ₘ × 𝔸¹ ⟶ 𝔸¹` of the scaling groupoid over `Spec k` is smooth. -/
theorem isSmooth_scalingGroupoid_source :
    Space.IsSmooth C (Spec (.of k)) hk (scalingGroupoid C (Spec (.of k)) hk).source.hom :=
  (isSmoothOfRelativeDimension_scalingGroupoid_source C (Spec (.of k)) hk).1

/-- The image of `1` is an open point of `[𝔸¹/𝔾ₘ]`, and the origin is not. -/
theorem isOpen_unitPoint_and_not_isOpen_originPoint :
    IsOpen ({unitPoint C hk 𝒳 e} : Set _) ∧ ¬ IsOpen ({originPoint C hk 𝒳 e} : Set _) := by
  have hq : Topology.IsQuotientMap (chartPointsMap C hk 𝒳 e) :=
    Stack.isQuotientMap_spacePointMap_quotientChart
      (scalingGroupoid C (Spec (.of k)) hk) 𝒳 e (isSmooth_scalingGroupoid_source C hk)
  refine ⟨?_, fun h => ?_⟩
  · refine hq.isOpen_preimage.1 ?_
    rw [chartPointsMap_preimage_unitPoint]
    exact (isClosed_zeroLocus C (Spec (.of k)) hk).isOpen_compl.preimage
      (lineHomeomorph C (Spec (.of k)) hk).continuous
  · have h' := hq.isOpen_preimage.2 h
    rw [chartPointsMap_preimage_originPoint] at h'
    apply not_isOpen_zeroLocus C hk
    rw [← (lineHomeomorph C (Spec (.of k)) hk).image_preimage (zeroLocus C (Spec (.of k)) hk)]
    exact (lineHomeomorph C (Spec (.of k)) hk).isOpenMap _ h'

/-! ### The dimension of `[𝔸¹/𝔾ₘ]` -/

/-- **`𝔸¹_k` has dimension one at each of its points**, as an algebraic space (Stacks 04N5):
over a field the dimension at a point is the relative dimension of the structure morphism
there (Stacks 0D4M), and `𝔸¹_k ⟶ Spec k` is smooth of relative dimension one. -/
theorem dimensionAtPoint_affineLineOver
    (t : Space.points C (Spec (.of k)) hk (affineLineOver C (Spec (.of k)) hk).left) :
    Space.dimensionAtPoint C (Spec (.of k)) hk _ (isAlgebraicSpace_affineLineOver C _ hk) t =
      ((1 : ℕ) : WithBot ℕ∞) :=
  (Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint C (Spec (.of k)) hk
    (isAlgebraicSpace_affineLineOver C _ hk) (rationalPoint C hk 0)
    (affineLineOver C (Spec (.of k)) hk).hom t ((1 : ℕ) : ℕ∞)).1
    ((isSmoothOfRelativeDimension_affineLineOver C (Spec (.of k)) hk).2 t)

/-- `𝔸¹_k` is locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_affineLineOver :
    Space.HasEtaleLocalProperty C (Spec (.of k)) hk (affineLineOver C (Spec (.of k)) hk).left
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z) := by
  refine (Space.exists_atlas_iff_of_representable C (Spec (.of k)) hk _ _ _
    (lineIso C (Spec (.of k)) hk)).2 ?_
  have : Smooth (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ))) :=
    SmoothOfRelativeDimension.smooth 1 _
  change IsLocallyNoetherian (pullback (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from (Spec (.of k))))
  infer_instance

include e in
/-- **`[𝔸¹/𝔾ₘ]` has dimension `0` at each of its points**: the chart `𝔸¹ ⟶ [𝔸¹/𝔾ₘ]` has relative
dimension `dim 𝔾ₘ = 1` and `𝔸¹` has dimension one, so Stacks 0DRJ gives `1 - 1 = 0`. -/
theorem dimensionAtPoint_eq_zero (h𝒳 : Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳)
    (x : Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property) :
    Stack.dimensionAtPoint C (Spec (.of k)) hk 𝒳 h𝒳 x = 0 := by
  obtain ⟨t, rfl⟩ := Stack.surjective_spacePointMap_quotientChart
    (scalingGroupoid C (Spec (.of k)) hk) 𝒳 e x
  rw [← Stack.pointsMap_stackPointOfSpacePoint_quotientChart,
    Stack.dimensionAtPoint_quotientChart (scalingGroupoid C (Spec (.of k)) hk) 𝒳 e h𝒳 1
      (isSmoothOfRelativeDimension_scalingGroupoid_source C (Spec (.of k)) hk) t]
  exact (congrArg (fun d => Stack.dimensionSubNat d 1)
    (dimensionAtPoint_affineLineOver C hk t)).trans rfl

end Field

/-- **Stacks 0DRK, the example `[𝔸¹/𝔾ₘ]`.** Over a field `k`, let `[𝔸¹/𝔾ₘ]` be the quotient stack
of the multiplicative group acting on the affine line by multiplication. It is an algebraic stack,
equivalent over the site to an object `𝒳` of the 2-category of algebraic stacks, and for every
such `𝒳`:
* `|𝒳|` has exactly two points `x₀ ≠ x₁`, and `x₀` is a specialisation of `x₁` (they are the
  images of the two orbits `{0}` and `𝔸¹ ∖ {0}`);
* `|𝒳|` has Krull dimension `1` as a topological space;
* `𝒳` is locally Noetherian, and `dim_x(𝒳) = 0` (Stacks 0AFN) at both points `x`. -/
@[stacks 0DRK "the example [A¹/Gₘ] over a field: |𝒳| has two points, one a specialisation of the \
other, |𝒳| has Krull dimension 1, and dim_x(𝒳) = 0 at both points"]
theorem affineLineQuotientStack_points_dimension {k : Type u} [Field k]
    (hk : C.Contains (Spec (.of k))) :
    (∃ 𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (affineLineQuotientStack C (Spec (.of k)) hk).p 𝒳.val.val.p)) ∧
    ∀ (𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
      (_e : StacksRepresentableCFG.EquivalenceOver
        (affineLineQuotientStack C (Spec (.of k)) hk).p 𝒳.val.val.p),
      letI := Stack.pointTopology C (Spec (.of k)) hk 𝒳.val
      (∃ x₀ x₁ : Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property,
        x₀ ≠ x₁ ∧ (∀ x, x = x₀ ∨ x = x₁) ∧ x₁ ⤳ x₀) ∧
      topologicalKrullDim (Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property) = 1 ∧
      Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳 ∧
      ∀ (h𝒳 : Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳) x,
        Stack.dimensionAtPoint C (Spec (.of k)) hk 𝒳 h𝒳 x = 0 := by
  refine ⟨Stack.exists_algebraicStacks_equivalenceOver C (Spec (.of k)) hk
    (isAlgebraicStack_affineLineQuotientStack C (Spec (.of k)) hk), fun 𝒳 e => ?_⟩
  let := Stack.pointTopology C (Spec (.of k)) hk 𝒳.val
  obtain ⟨h1, h0⟩ := isOpen_unitPoint_and_not_isOpen_originPoint C hk 𝒳 e
  obtain ⟨hspec, hdim⟩ := specializes_and_topologicalKrullDim_eq_one
    (originPoint_ne_unitPoint C hk 𝒳 e) (eq_originPoint_or_eq_unitPoint C hk 𝒳 e) h1 h0
  exact ⟨⟨_, _, originPoint_ne_unitPoint C hk 𝒳 e, eq_originPoint_or_eq_unitPoint C hk 𝒳 e,
      hspec⟩, hdim,
    Stack.isLocallyNoetherianStack_of_quotientChart (scalingGroupoid C (Spec (.of k)) hk) 𝒳 e
      (isSmooth_scalingGroupoid_source C hk)
      (hasEtaleLocalProperty_isLocallyNoetherian_affineLineOver C hk),
    fun h𝒳 x => dimensionAtPoint_eq_zero C hk 𝒳 e h𝒳 x⟩

/-! ### The classifying stack `[Spec k/𝔾ₘ]` -/

section Classifying

variable {k : Type u} [Field k] (hk : C.Contains (Spec (.of k)))

/-- The multiplicative group over `k`, as a group algebraic space over `Spec k`. -/
noncomputable abbrev multiplicativeGroupOverField :
    Space.GroupAlgebraicSpace C (Spec (.of k)) hk
      (Space.terminalSpace C (Spec (.of k)) hk).obj
      (Space.terminalSpace C (Spec (.of k)) hk).property :=
  Space.multiplicativeGroupSpace C (Spec (.of k)) hk _
    (Space.terminalSpace C (Spec (.of k)) hk).property

/-- The action groupoid of the trivial action of `𝔾ₘ` on `Spec k`, whose quotient stack is the
classifying stack. -/
noncomputable abbrev classifyingGroupoid :
    GroupoidInAlgebraicSpaces C (Spec (.of k)) hk (Space.terminalSpace C (Spec (.of k)) hk) :=
  letI : ModObj (multiplicativeGroupOverField C hk).obj.X
      (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  (Space.groupoidOfAction (Space.terminalSpace C (Spec (.of k)) hk)
    (multiplicativeGroupOverField C hk).obj.X
    (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj))
    (multiplicativeGroupOverField C hk).property
    (Space.terminalSpace C (Spec (.of k)) hk).property).groupoid

/-- The classifying stack of `𝔾ₘ` over `k` is the quotient stack of `classifyingGroupoid`. -/
theorem classifyingStack_val :
    (Stack.classifyingStack C hk (multiplicativeGroupOverField C hk)).val =
      Stack.quotientStack (classifyingGroupoid C hk) := rfl

/-- `𝔾ₘ` is smooth of relative dimension one over `Spec k`. -/
private theorem isSmoothOfRelativeDimension_multiplicativeGroupOverField :
    Space.IsSmoothOfRelativeDimension C (Spec (.of k)) hk 1
      (multiplicativeGroupOverField C hk).obj.X.hom :=
  isSmoothOfRelativeDimension_prod_fst C (Spec (.of k)) hk
    (Space.terminalSpace C (Spec (.of k)) hk).property _
    (Space.pointsOnSiteRepresentableBy C (Spec (.of k)) hk _ _) 1

/-- The source morphism of `classifyingGroupoid` is smooth of relative dimension `1`. -/
theorem isSmoothOfRelativeDimension_classifyingGroupoid_source :
    Space.IsSmoothOfRelativeDimension C (Spec (.of k)) hk 1
      (classifyingGroupoid C hk).source.hom :=
  let : ModObj (multiplicativeGroupOverField C hk).obj.X
      (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  isSmoothOfRelativeDimension_groupoidOfAction_source C (Spec (.of k)) hk _ _ _ _ _ 1
    (isSmoothOfRelativeDimension_multiplicativeGroupOverField C hk)

/-- **The classifying stack `[Spec k/𝔾ₘ]` is an algebraic stack** (Stacks 04TK). -/
theorem isAlgebraicStack_classifyingStack :
    Stack.IsAlgebraicStack.{u, w} C (Spec (.of k)) hk
      (Stack.classifyingStack C hk (multiplicativeGroupOverField C hk)).val :=
  let : ModObj (multiplicativeGroupOverField C hk).obj.X
      (𝟙_ (Over (Space.terminalSpace C (Spec (.of k)) hk).obj)) :=
    ModObj.trivialAction _ _
  Stack.isAlgebraicStack_quotientStackOfAction _ _ _ _ _
    (isSmoothOfRelativeDimension_multiplicativeGroupOverField C hk).1

/-- `Spec k` has a single point. -/
instance subsingleton_points_classifyingGroupoid_objects :
    Subsingleton (Space.points C (Spec (.of k)) hk (classifyingGroupoid C hk).objects.obj) :=
  haveI : Subsingleton (Spec (.of k)) := inferInstance
  @Equiv.subsingleton _ _ (Space.pointsEquivScheme C (Spec (.of k)) hk (baseObject C hk)) this

/-- `Spec k` has dimension `0` at its point. -/
theorem dimensionAtPoint_classifyingGroupoid_objects
    (t : Space.points C (Spec (.of k)) hk (classifyingGroupoid C hk).objects.obj) :
    Space.dimensionAtPoint C (Spec (.of k)) hk _ (classifyingGroupoid C hk).objects.property t =
      ((0 : ℕ) : WithBot ℕ∞) := by
  have h := Space.isSmoothOfRelativeDimension_yoneda_map C (Spec (.of k)) hk
    (𝟙 (baseObject C hk)) 0
  rw [CategoryTheory.Functor.map_id] at h
  exact (Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint C (Spec (.of k)) hk
    (classifyingGroupoid C hk).objects.property (rationalPoint C hk 0)
    (𝟙 _) t ((0 : ℕ) : ℕ∞)).1 (h.2 t)

variable (𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
  (e : StacksRepresentableCFG.EquivalenceOver
    (Stack.classifyingStack C hk (multiplicativeGroupOverField C hk)).val.p 𝒳.val.val.p)

include e in
/-- `[Spec k/𝔾ₘ]` is locally Noetherian. -/
theorem isLocallyNoetherianStack_classifyingStack :
    Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳 :=
  Stack.isLocallyNoetherianStack_of_quotientChart (classifyingGroupoid C hk) 𝒳 e
    (isSmoothOfRelativeDimension_classifyingGroupoid_source C hk).1
    ((Space.exists_atlas_iff_of_representable C (Spec (.of k)) hk _ _ (baseObject C hk)
      (Iso.refl _)).2 (inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))))

end Classifying

/-- **Stacks 0DRK, the example `[Spec k/𝔾ₘ]`.** Over a field `k` the classifying stack
`[Spec k/𝔾ₘ]` of the multiplicative group is an algebraic stack, equivalent over the site to an
object `𝒳` of the 2-category of algebraic stacks, and for every such `𝒳`, which is locally
Noetherian, `|𝒳|` has a unique point, at which `dim_x(𝒳) = -1` (Stacks 0AFN). -/
@[stacks 0DRK "the example [Spec k/Gₘ]: the classifying stack has a unique point, at which its \
dimension is -1"]
theorem classifyingStack_multiplicativeGroup_dimension {k : Type u} [Field k]
    (hk : C.Contains (Spec (.of k))) :
    (∃ 𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk,
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (Stack.classifyingStack C hk (multiplicativeGroupOverField C hk)).val.p 𝒳.val.val.p)) ∧
    ∀ (𝒳 : Stack.AlgebraicStacks.{u, w} C (Spec (.of k)) hk)
      (_e : StacksRepresentableCFG.EquivalenceOver
        (Stack.classifyingStack C hk (multiplicativeGroupOverField C hk)).val.p 𝒳.val.val.p),
      Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳 ∧
      ∃ x : Stack.points C (Spec (.of k)) hk 𝒳.val.val 𝒳.val.property,
        (∀ y, y = x) ∧
        ∀ h𝒳 : Stack.IsLocallyNoetherianStack.{u, w} C (Spec (.of k)) hk 𝒳,
          Stack.dimensionAtPoint C (Spec (.of k)) hk 𝒳 h𝒳 x = ((-1 : ℤ) : EInt) := by
  refine ⟨Stack.exists_algebraicStacks_equivalenceOver C (Spec (.of k)) hk
    (isAlgebraicStack_classifyingStack C hk), fun 𝒳 e => ?_⟩
  let t : Space.points C (Spec (.of k)) hk (classifyingGroupoid C hk).objects.obj :=
    (Space.pointsEquivScheme C (Spec (.of k)) hk (baseObject C hk)).symm
      (IsLocalRing.closedPoint k)
  refine ⟨isLocallyNoetherianStack_classifyingStack C hk 𝒳 e,
    Stack.spacePointMap C (Spec (.of k)) hk _ 𝒳.val
      (Stack.quotientChart (classifyingGroupoid C hk) 𝒳 e).hom.hom t, fun y => ?_, fun h𝒳 => ?_⟩
  · obtain ⟨s, rfl⟩ := Stack.surjective_spacePointMap_quotientChart (classifyingGroupoid C hk) 𝒳 e y
    rw [Subsingleton.elim s t]
  · refine (congrArg (Stack.dimensionAtPoint C (Spec (.of k)) hk 𝒳 h𝒳)
      (Stack.pointsMap_stackPointOfSpacePoint_quotientChart (classifyingGroupoid C hk) 𝒳 e
        t).symm).trans ?_
    rw [Stack.dimensionAtPoint_quotientChart (classifyingGroupoid C hk) 𝒳 e h𝒳 1
        (isSmoothOfRelativeDimension_classifyingGroupoid_source C hk) t,
      dimensionAtPoint_classifyingGroupoid_objects]
    rfl

end Stacks.Examples.AffineLineQuotient

end
