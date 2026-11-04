module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Scheme

/-!
# The scheme of structure constants as an object of the big fppf site

The scheme `X` of Stacks 05YM, whose points over a scheme `T` are the free `d`-dimensional
algebra structures on `Γ(T, 𝒪_T)^{⊕d}`, is affine over the integers with a coordinate ring that
is a quotient of a polynomial ring in finitely many variables over `ℤ`, hence countable. So `X`
lies in every big fppf site, its base change `X_S` lies in the big fppf site of `S`, and over an
algebraic space `B` over `S` the product `B ×_S X_S` is an algebraic space.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.structureConstantsOver` and
  `AlgebraicGeometry.FiniteFreeAlgebra.structureConstantsBaseChange`: the scheme of structure
  constants over the integers and its base change `X_S` to a scheme `S`.
* `AlgebraicGeometry.FiniteFreeAlgebra.structureConstantsBaseChangeHomEquiv`: points of `X_S`
  over a scheme `T` over `S` are morphisms `T ⟶ X` of schemes.
* `AlgebraicGeometry.Space.structureConstantsSiteObject`: `X_S` read as an object of the big
  fppf site over `S`.
* `AlgebraicGeometry.Space.structureConstantsSpaceOver`: the algebraic space `B ×_S X_S` over an
  algebraic space `B` over `S`, as an object of the slice of presheaves over `B`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.structureConstantsBaseChangePoints`: the points of `X_S`
  over a scheme `T` over `S` are the free `d`-dimensional algebras over `Γ(T, 𝒪_T)`, naturally in
  `T` (`AlgebraicGeometry.FiniteFreeAlgebra.structureConstantsBaseChangePoints_naturality`).
* `AlgebraicGeometry.Space.contains_structureConstantsScheme` and
  `AlgebraicGeometry.Space.contains_structureConstantsBaseChange`: `X` and `X_S` lie in the big
  fppf site.
* `AlgebraicGeometry.Space.isAlgebraicSpace_structureConstantsSpaceOver`: `B ×_S X_S` is an
  algebraic space over `S`.

## References

* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable (d : ℕ) [NeZero d]

/-- The scheme of structure constants, as a scheme over the integers. -/
@[stacks 05YM "the scheme of structure constants over the integers"]
noncomputable abbrev structureConstantsOver : Over (Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  Over.mk (specULiftZIsTerminal.from (scheme.{u} d))

/-- The scheme `X_S` of structure constants over a scheme `S`, obtained by base change from the
integers. -/
@[stacks 05YM "the scheme of structure constants over a general base"]
noncomputable abbrev structureConstantsBaseChange (S : Scheme.{u}) : Over S :=
  (Over.pullback (specULiftZIsTerminal.from S)).obj (structureConstantsOver.{u} d)

/-- Points of `X_S` over a scheme `T` over `S` are morphisms `T ⟶ X` of schemes. -/
noncomputable def structureConstantsBaseChangeHomEquiv (S : Scheme.{u}) (T : Over S) :
    (T ⟶ structureConstantsBaseChange.{u} d S) ≃ (T.left ⟶ scheme.{u} d) where
  toFun f := f.left ≫ pullback.fst (specULiftZIsTerminal.from (scheme.{u} d))
    (specULiftZIsTerminal.from S)
  invFun f := Over.homMk
    (pullback.lift f T.hom (IsTerminal.hom_ext specULiftZIsTerminal _ _))
    (pullback.lift_snd _ _ _)
  left_inv f := Over.OverMorphism.ext <|
    pullback.hom_ext (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans f.w.symm)
  right_inv _ := pullback.lift_fst _ _ _

/-- The points of `X_S` over a scheme `T` over `S` are the free `d`-dimensional algebras over
`Γ(T, 𝒪_T)`. -/
@[stacks 05YM "the points of the scheme of structure constants over a general base"]
noncomputable def structureConstantsBaseChangePoints (S : Scheme.{u}) (T : Over S) :
    (T ⟶ structureConstantsBaseChange.{u} d S) ≃ FiniteFreeAlgebra Γ(T.left, ⊤) d :=
  (structureConstantsBaseChangeHomEquiv d S T).trans ((representation.{u} d).equiv T.left)

/-- `AlgebraicGeometry.FiniteFreeAlgebra.structureConstantsBaseChangePoints` is natural in the
scheme over `S`: restricting a point along `f` extends the scalars of its structure constants
along the induced map of global sections. -/
@[stacks 05YM "the points of the scheme of structure constants over a general base"]
theorem structureConstantsBaseChangePoints_naturality (S : Scheme.{u}) {T U : Over S}
    (f : T ⟶ U) (x : U ⟶ structureConstantsBaseChange.{u} d S) :
    FiniteFreeAlgebra.map f.left.appTop.hom
        (structureConstantsBaseChangePoints d S U x) =
      structureConstantsBaseChangePoints d S T (f ≫ x) := by
  show FiniteFreeAlgebra.map f.left.appTop.hom
      ((representation.{u} d).equiv U.left
        (structureConstantsBaseChangeHomEquiv d S U x)) = _
  rw [(representation.{u} d).naturality f.left (structureConstantsBaseChangeHomEquiv d S U x)]
  rfl

end AlgebraicGeometry.FiniteFreeAlgebra

namespace AlgebraicGeometry.Space

open AlgebraicGeometry.FiniteFreeAlgebra

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- The scheme of structure constants belongs to every big fppf site. -/
theorem contains_structureConstantsScheme : 𝒞.Contains (scheme.{u} d) := by
  have : Countable (MvPolynomial (CoeffIndex d) ℤ) :=
    Cardinal.mk_le_aleph0_iff.mp <| MvPolynomial.cardinalMk_le_max.trans <|
      max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl
  have : Countable (universalRing d) := Ideal.Quotient.mk_surjective.countable
  show (Spec (CommRingCat.of (ULift.{u} (universalRing d)))).size < 𝒞.cutoff
  rw [Scheme.size_Spec]
  exact max_lt 𝒞.aleph0_lt_cutoff (Cardinal.mk_le_aleph0.trans_lt 𝒞.aleph0_lt_cutoff)

/-- The scheme `X_S` of structure constants over `S` belongs to the big fppf site of `S`. -/
theorem contains_structureConstantsBaseChange (hS : 𝒞.Contains S) :
    𝒞.Contains (structureConstantsBaseChange.{u} d S).left :=
  Scheme.size_pullback_lt _ _ (contains_structureConstantsScheme 𝒞 d) hS

/-- The scheme `X_S` of structure constants over `S`, read as an object of the big fppf site
over `S`. -/
@[stacks 05YM "the scheme of structure constants as an object of the site"]
noncomputable def structureConstantsSiteObject : BigFppfOver 𝒞 S hS :=
  Over.mk (ObjectProperty.homMk (structureConstantsBaseChange.{u} d S).hom
    (X := 𝒞.obj (contains_structureConstantsBaseChange 𝒞 S d hS)) (Y := 𝒞.obj hS))

/-- The algebraic space `B ×_S X_S` over an algebraic space `B` over `S`, as an object of the
slice of presheaves on the big fppf site over `B`. -/
@[stacks 05YM "the scheme of structure constants as an object over an algebraic space"]
noncomputable def structureConstantsSpaceOver (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) :
    Over B :=
  Over.mk (prod.fst : B ⨯ yoneda.obj (structureConstantsSiteObject 𝒞 S hS d) ⟶ B)

/-- The presheaf underlying `B ×_S X_S` is an algebraic space over `S`. -/
@[stacks 05YM "the scheme of structure constants as an object over an algebraic space"]
theorem isAlgebraicSpace_structureConstantsSpaceOver (B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 S hS B) :
    IsAlgebraicSpace 𝒞 S hS
      (B ⨯ yoneda.obj (structureConstantsSiteObject 𝒞 S hS d)) :=
  isAlgebraicSpace_of_iso 𝒞 S hS
    (prod.braiding B (yoneda.obj (structureConstantsSiteObject 𝒞 S hS d)))
    (isAlgebraicSpace_prod_yoneda_obj (structureConstantsSiteObject 𝒞 S hS d) hB)

end AlgebraicGeometry.Space

end
