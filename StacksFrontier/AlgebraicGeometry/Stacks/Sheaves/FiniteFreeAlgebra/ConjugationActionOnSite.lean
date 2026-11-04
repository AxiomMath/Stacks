module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceChartModels
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.StructureConstantsSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UnitFixingGroupSpace

/-!
# The conjugation action on the big fppf site

The conjugation action `a(g, m) = g⁻¹ ∘ m ∘ (g ⊗ g)` named in Stacks 05YQ, of the unit-fixing
group on the free `d`-dimensional algebra structures is, in the column-matrix convention, a *right*
action: `a(h, a(g, m)) = a(g * h, m)`. The left action it determines, `g • m = a(g⁻¹, m)`, is
what `CategoryTheory.ModObj` records, and this file assembles it into an action of the functor
of points of the unit-fixing group scheme `G_S` on the functor of points of the scheme `X_S` of
structure constants, on the big fppf site over `S`.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints`: the left action `g • x`
  determined by the right action `a` named in Stacks 05YQ.
* `AlgebraicGeometry.Space.unitFixingMatrixEquiv` and
  `AlgebraicGeometry.Space.structureConstantsPointEquiv`: the identifications of the two
  functors of points on the site with unit-fixing matrices and with points of the scheme of
  structure constants.
* `AlgebraicGeometry.Space.conjugationSMulHom` and
  `AlgebraicGeometry.Space.conjugationModObj`: the action, as a morphism of presheaves out of
  the product and as a `CategoryTheory.ModObj`.
* `AlgebraicGeometry.Space.structureConstantsQuotientStack`: the quotient stack `[X/G]` of the
  conjugation action.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints_one`,
  `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints_mul` and
  `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints_naturality`: the left action laws.
* `AlgebraicGeometry.Space.isStackInGroupoids_structureConstantsQuotientStack`: `[X/G]` is a
  stack in groupoids over the big fppf site.

## References

* [Stacks Project, Tag 05YP](https://stacks.math.columbia.edu/tag/05YP)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

/-- The left action of the unit-fixing group on the points of the scheme of structure constants
determined by the right action `a(g, m) = g⁻¹ ∘ m ∘ (g ⊗ g)` named in **Stacks 05YQ**. -/
noncomputable def leftConjugationOnPoints {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u})
    (g : UnitFixingMatrix Γ(T, ⊤) d) (x : T ⟶ scheme.{u} d) :
    T ⟶ scheme.{u} d :=
  conjugationOnPoints laws T g⁻¹ x

/-- The identity matrix acts as the identity. -/
theorem leftConjugationOnPoints_one {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u}) (x : T ⟶ scheme.{u} d) :
    leftConjugationOnPoints laws T 1 x = x := by
  rw [leftConjugationOnPoints, inv_one, conjugationOnPoints_one]

/-- `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints` is a left action. -/
theorem leftConjugationOnPoints_mul {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) (T : Scheme.{u})
    (g h : UnitFixingMatrix Γ(T, ⊤) d) (x : T ⟶ scheme.{u} d) :
    leftConjugationOnPoints laws T (g * h) x =
      leftConjugationOnPoints laws T g (leftConjugationOnPoints laws T h x) := by
  rw [leftConjugationOnPoints, leftConjugationOnPoints, leftConjugationOnPoints,
    mul_inv_rev, conjugationOnPoints_mul]

/-- `AlgebraicGeometry.FiniteFreeAlgebra.leftConjugationOnPoints` commutes with base change. -/
theorem leftConjugationOnPoints_naturality {d : ℕ} [NeZero d]
    (laws : ConjugationPreservesAlgebraLaws.{u} d) {T U : Scheme.{u}} (f : T ⟶ U)
    (g : UnitFixingMatrix Γ(U, ⊤) d) (x : U ⟶ scheme.{u} d) :
    leftConjugationOnPoints laws T (UnitFixingMatrix.map f.appTop.hom g) (f ≫ x) =
      f ≫ leftConjugationOnPoints laws U g x := by
  rw [leftConjugationOnPoints, leftConjugationOnPoints,
    show (UnitFixingMatrix.map f.appTop.hom g)⁻¹ =
        UnitFixingMatrix.map f.appTop.hom g⁻¹ from
      (map_inv (UnitFixingMatrix.mapMonoidHom f.appTop.hom) g).symm,
    conjugationOnPoints_naturality]

end AlgebraicGeometry.FiniteFreeAlgebra

namespace AlgebraicGeometry.Space

open AlgebraicGeometry.FiniteFreeAlgebra

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- The points of the unit-fixing group scheme `G_S` over an object `T` of the big fppf site are
the unit-fixing invertible matrices over `Γ(T, 𝒪_T)`, as a group. -/
noncomputable def unitFixingMatrixEquiv (T : BigFppfOver 𝒞 S hS) :
    (unitFixingPointsOnSite 𝒞 S hS d).obj (Opposite.op T) ≃*
      UnitFixingMatrix Γ(siteScheme 𝒞 S hS T, ⊤) d :=
  ((unitFixingBaseChangeGroupPointsIso d S).app
    (Opposite.op ((toSchemeOver 𝒞 S hS).obj T))).groupIsoToMulEquiv

/-- The points of the scheme `X_S` of structure constants over an object `T` of the big fppf
site are the morphisms of schemes from `T` to the scheme of structure constants. -/
noncomputable def structureConstantsPointEquiv (T : BigFppfOver 𝒞 S hS) :
    (T ⟶ structureConstantsSiteObject 𝒞 S hS d) ≃
      (siteScheme 𝒞 S hS T ⟶ scheme.{u} d) :=
  (((Functor.FullyFaithful.ofFullyFaithful 𝒞.inclusion).over (X := 𝒞.obj hS)).homEquiv).trans
    (structureConstantsBaseChangeHomEquiv d S ((toSchemeOver 𝒞 S hS).obj T))

/-- `AlgebraicGeometry.Space.structureConstantsPointEquiv` is natural: restricting a point of
`X_S` along a morphism of the site is precomposition of the corresponding scheme morphism. -/
theorem structureConstantsPointEquiv_naturality {T U : BigFppfOver 𝒞 S hS} (f : T ⟶ U)
    (x : U ⟶ structureConstantsSiteObject 𝒞 S hS d) :
    structureConstantsPointEquiv 𝒞 S hS d T (f ≫ x) =
      ((toSchemeOver 𝒞 S hS).map f).left ≫ structureConstantsPointEquiv 𝒞 S hS d U x := by
  change ((toSchemeOver 𝒞 S hS).map (f ≫ x)).left ≫ _ = _
  rw [Functor.map_comp]
  exact Category.assoc _ _ _

/-- `AlgebraicGeometry.Space.unitFixingMatrixEquiv` is natural in the object of the site. -/
theorem unitFixingMatrixEquiv_naturality {T U : (BigFppfOver 𝒞 S hS)ᵒᵖ} (f : T ⟶ U)
    (g : (unitFixingPointsOnSite 𝒞 S hS d).obj T) :
    unitFixingMatrixEquiv 𝒞 S hS d U.unop
        ((unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat).map f g) =
      UnitFixingMatrix.map
        (Scheme.Γ.map ((toSchemeOver 𝒞 S hS).map f.unop).left.op).hom
        (unitFixingMatrixEquiv 𝒞 S hS d T.unop g) :=
  ConcreteCategory.congr_hom
    ((unitFixingBaseChangeGroupPointsIso d S).hom.naturality
      ((toSchemeOver 𝒞 S hS).map f.unop).op) g

/-- The conjugation action, as a morphism of presheaves out of the product of the functor of
points of `G_S` and the functor of points of `X_S`. -/
noncomputable def conjugationSMulHom :
    (unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat) ⊗
        yoneda.obj (structureConstantsSiteObject 𝒞 S hS d) ⟶
      yoneda.obj (structureConstantsSiteObject 𝒞 S hS d) where
  app T := ↾fun p : (unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat).obj T ×
      (yoneda.obj (structureConstantsSiteObject 𝒞 S hS d)).obj T =>
    (structureConstantsPointEquiv 𝒞 S hS d T.unop).symm
      (leftConjugationOnPoints conjugationPreservesAlgebraLaws (siteScheme 𝒞 S hS T.unop)
        (unitFixingMatrixEquiv 𝒞 S hS d T.unop p.1)
        (structureConstantsPointEquiv 𝒞 S hS d T.unop p.2))
  naturality := by
    intro T U f
    ext p
    change (structureConstantsPointEquiv 𝒞 S hS d U.unop).symm
        (leftConjugationOnPoints conjugationPreservesAlgebraLaws (siteScheme 𝒞 S hS U.unop)
          (unitFixingMatrixEquiv 𝒞 S hS d U.unop
            ((unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat).map f p.1))
          (structureConstantsPointEquiv 𝒞 S hS d U.unop (f.unop ≫ p.2))) =
      f.unop ≫ (structureConstantsPointEquiv 𝒞 S hS d T.unop).symm
        (leftConjugationOnPoints conjugationPreservesAlgebraLaws (siteScheme 𝒞 S hS T.unop)
          (unitFixingMatrixEquiv 𝒞 S hS d T.unop p.1)
          (structureConstantsPointEquiv 𝒞 S hS d T.unop p.2))
    apply (structureConstantsPointEquiv 𝒞 S hS d U.unop).injective
    simp only [Equiv.apply_symm_apply, structureConstantsPointEquiv_naturality,
      unitFixingMatrixEquiv_naturality]
    exact leftConjugationOnPoints_naturality _ _ _ _

/-- **Part of Stacks Project, Tag 05YQ.** The conjugation action of the unit-fixing group on free
`d`-dimensional algebra structures, as an action of the functor of points of `G_S` on the
functor of points of `X_S` over the big fppf site over `S`. -/
noncomputable instance conjugationModObj :
    ModObj (unitFixingPointsOnSite 𝒞 S hS d ⋙ forget GrpCat)
      (yoneda.obj (structureConstantsSiteObject 𝒞 S hS d)) where
  smul := conjugationSMulHom 𝒞 S hS d
  one_smul := by
    ext T x
    change (structureConstantsPointEquiv 𝒞 S hS d T.unop).symm
        (leftConjugationOnPoints conjugationPreservesAlgebraLaws (siteScheme 𝒞 S hS T.unop)
          (unitFixingMatrixEquiv 𝒞 S hS d T.unop 1)
          (structureConstantsPointEquiv 𝒞 S hS d T.unop x.2)) = x.2
    rw [map_one, leftConjugationOnPoints_one, Equiv.symm_apply_apply]
  mul_smul := by
    ext T x
    change (structureConstantsPointEquiv 𝒞 S hS d T.unop).symm
        (leftConjugationOnPoints conjugationPreservesAlgebraLaws (siteScheme 𝒞 S hS T.unop)
          (unitFixingMatrixEquiv 𝒞 S hS d T.unop (x.1.1 * x.1.2))
          (structureConstantsPointEquiv 𝒞 S hS d T.unop x.2)) =
      (structureConstantsPointEquiv 𝒞 S hS d T.unop).symm
        (leftConjugationOnPoints conjugationPreservesAlgebraLaws (siteScheme 𝒞 S hS T.unop)
          (unitFixingMatrixEquiv 𝒞 S hS d T.unop x.1.1)
          (structureConstantsPointEquiv 𝒞 S hS d T.unop
            ((structureConstantsPointEquiv 𝒞 S hS d T.unop).symm
              (leftConjugationOnPoints conjugationPreservesAlgebraLaws
                (siteScheme 𝒞 S hS T.unop)
                (unitFixingMatrixEquiv 𝒞 S hS d T.unop x.1.2)
                (structureConstantsPointEquiv 𝒞 S hS d T.unop x.2)))))
    rw [Equiv.apply_symm_apply, map_mul, leftConjugationOnPoints_mul]

/-- The functor of points of an object of the big fppf site is represented by that object. -/
noncomputable def yonedaRepresentableBy (T : BigFppfOver 𝒞 S hS) :
    (yoneda.obj T).RepresentableBy T where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- **Part of Stacks Project, Tag 05YQ.** The quotient stack `[X/G]` of the conjugation action
of the unit-fixing subgroup `G ⊆ GL_d` on the scheme `X` of structure constants of free
`d`-dimensional algebras, over an algebraic space `B` over `S`; the source's `[X/G]` is the case
where `B` is the base itself. -/
noncomputable abbrev structureConstantsQuotientStack (B : AlgebraicSpaces 𝒞 S hS) :
    BasedCategory (BigFppfOver 𝒞 S hS) :=
  quotientStackOfPointsAction 𝒞 S hS B (unitFixingPointsOnSite 𝒞 S hS d)
    (yoneda.obj (structureConstantsSiteObject 𝒞 S hS d))
    (pointsOnSiteRepresentableBy 𝒞 S hS (unitFixingSiteObject 𝒞 S hS d)
      (unitFixingSiteObjectGrpObj 𝒞 S hS d))
    (yonedaRepresentableBy 𝒞 S hS (structureConstantsSiteObject 𝒞 S hS d))

/-- **Part of Stacks Project, Tag 05YQ.** The quotient stack `[X/G]` is a stack in groupoids
over the big fppf site. -/
theorem isStackInGroupoids_structureConstantsQuotientStack (B : AlgebraicSpaces 𝒞 S hS) :
    Functor.IsStackInGroupoids (structureConstantsQuotientStack 𝒞 S hS d B).p
      (BigFppfOver.topology 𝒞 S hS) :=
  isStackInGroupoids_quotientStackOfPointsAction 𝒞 S hS B _ _ _ _

end AlgebraicGeometry.Space

end
