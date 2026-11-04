module

public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceTransitivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ComparisonCoefficients

/-!
# The base-changed chart of Stacks 04I6, in the coordinates of a presentation of the original

Step (3) of the proof of [Stacks Project, Tag 04I6] produces a comparison
`g⁻¹h_V ⟶ h_{X ×_Y V}`, where `V` is an étale chart of `Y` and `X ×_Y V` is the corresponding
chart of `X`.  Its values are produced as *solutions* of the system of equations `P` presenting
`V` over `Y`, so to read a value as a section of `h_{X ×_Y V}` one needs the sections of
`h_{X ×_Y V}` described as solutions of a system.

The route taken here is the universal property of the fibre product rather than base change of
the presentation.  For a chart `U` of `X`,

`Hom_{X_étale}(U, X ×_Y V) ≅ {morphisms of schemes U ⟶ V over Y}`

— `AlgebraicGeometry.SmallEtale.baseChangeHomEquiv` — and the right-hand side is already described
as a solution set by `Stacks.EtaleCohomology.homOverEquivSolutions`, *read at the chart `U`
regarded as a scheme over `Y` through `X`*.  Composing gives
`AlgebraicGeometry.SmallEtale.baseChangeHomEquivSolutions`, whose coefficient ring map is

`Γ(Y, ⊤) --f^♯--> Γ(X, ⊤) --restrict--> Γ(U, ⊤)`.

That is exactly the coefficient map of
`AlgebraicGeometry.isSolution_comparisonCoord_globalSectionsMap` once `f` is the morphism of
schemes whose ring map on global functions is
`AlgebraicGeometry.RingedToposHom.globalSectionsMap`, which is how the source's first paragraph
chooses `f`.  So **no base change of a standard presentation is needed**: the statement
`A ⊗_B B[x]/(P) = A[x]/(P^φ)`, which earlier notes in this directory recorded as an outstanding
prerequisite of step (3), is not required — the `Γ(Y, ⊤)`-coefficients never have to be pushed
into `Γ(X, ⊤)` inside the presentation, because `homOverEquivSolutions` takes the coefficient
ring map as a parameter and `U` is a scheme over `Y`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.baseChangeHomEquiv` — **the universal property of the
  base-changed chart, in site form**: morphisms of the small étale site of `X` from `U` into
  `X ×_Y V` are morphisms of schemes `U ⟶ V` commuting over `Y`.
* `AlgebraicGeometry.SmallEtale.baseChangeHomEquivSolutions` — the same hom-set as the solutions
  over `Γ(U, ⊤)` of the system presenting `V` over `Y`.

## Main results

* `AlgebraicGeometry.SmallEtale.isPullback_baseChangeStructureHom` — the defining cartesian
  square, with its legs spelled as the structure morphisms of the charts.
* `AlgebraicGeometry.SmallEtale.appTop_schemeStructureHom_comp_inclusion_map` — the coefficient
  ring map of `baseChangeHomEquivSolutions` factors as the ring map of `f` on global functions
  followed by restriction to `U`.

## What this does not do

Nothing here carries a `@[stacks 04I6]` tag.  What remains of step (3) after this file is the
assembly, and it is proved: the per-chart comparison is natural in `U`
(`AlgebraicGeometry.comparisonSheafHom`) and in `V`
(`AlgebraicGeometry.comparisonSheafHom_naturality_chart`), it is an isomorphism by the stalk
computation of `AlgebraicGeometry.isIso_comparisonSheafHom`, and the passage along Stacks 04HR
(`AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`) transports the isomorphism
of *direct images* rather than the comparison — the comparison is never produced at a non-affine
chart.  The tag is `AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_isLocallyRinged` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineExistence.lean`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (V : SmallEtale B Y.obj Y.property) (U : SmallEtale B X.obj X.property)

/-- The projection `X ×_Y V ⟶ V` of the base-changed chart, as a morphism of schemes between the
underlying schemes of the two charts.

This is `CategoryTheory.Limits.pullback.fst` of the big étale site, carried to schemes by
`B.inclusion`; it is a `def` rather than an `abbrev` so that its type is the one the statements
below want, with source and target spelled through
`AlgebraicGeometry.SmallEtale.toScheme`. -/
def baseChangeProj :
    (SmallEtale.toScheme B X.obj X.property).obj ((smallEtaleBaseChange B f).obj V) ⟶
      (SmallEtale.toScheme B Y.obj Y.property).obj V :=
  B.inclusion.map (pullback.fst V.obj.hom f)

/-- **The base-changed chart is a fibre product, with its legs spelled as structure morphisms.**
The projection of `X ×_Y V` to `V` and the structure morphism of `X ×_Y V` as a chart of `X` form
a cartesian square over the structure morphism of `V` and over `f`.

This is `AlgebraicGeometry.SmallEtale.isPullback_smallEtaleBaseChange` with its first leg
recognised as `AlgebraicGeometry.SmallEtale.baseChangeProj` and its second and third as
`AlgebraicGeometry.SmallEtale.schemeStructureHom`. -/
theorem isPullback_baseChangeStructureHom :
    IsPullback (baseChangeProj B f V)
      (schemeStructureHom B X.obj X.property ((smallEtaleBaseChange B f).obj V))
      (schemeStructureHom B Y.obj Y.property V) (B.inclusion.map f) :=
  isPullback_smallEtaleBaseChange B f V

/-- **The universal property of the base-changed chart, in site form.**  A morphism of the small
étale site of `X` from a chart `U` into `X ×_Y V` is exactly a morphism of schemes from `U` to
`V` making the triangle over `Y` commute, `Y`-morphisms being taken with `U` regarded as a scheme
over `Y` through its structure morphism to `X` followed by `f`. -/
def baseChangeHomEquiv :
    (U ⟶ (smallEtaleBaseChange B f).obj V) ≃
      {m : (SmallEtale.toScheme B X.obj X.property).obj U ⟶
            (SmallEtale.toScheme B Y.obj Y.property).obj V //
        m ≫ schemeStructureHom B Y.obj Y.property V =
          schemeStructureHom B X.obj X.property U ≫ B.inclusion.map f} where
  toFun a :=
    ⟨(SmallEtale.toScheme B X.obj X.property).map a ≫ baseChangeProj B f V, by
      rw [Category.assoc, (isPullback_baseChangeStructureHom B f V).w, ← Category.assoc,
        toScheme_map_comp_structure B a]⟩
  invFun m :=
    (homEquivOver B X.obj X.property U ((smallEtaleBaseChange B f).obj V)).symm
      ⟨(isPullback_baseChangeStructureHom B f V).lift m.1
          (schemeStructureHom B X.obj X.property U) m.2,
        (isPullback_baseChangeStructureHom B f V).lift_snd _ _ m.2⟩
  left_inv a := by
    refine (homEquivOver B X.obj X.property U
      ((smallEtaleBaseChange B f).obj V)).injective (Subtype.ext ?_)
    exact (isPullback_baseChangeStructureHom B f V).hom_ext
      ((isPullback_baseChangeStructureHom B f V).lift_fst _ _ _)
      (((isPullback_baseChangeStructureHom B f V).lift_snd _ _ _).trans
        (toScheme_map_comp_structure B a).symm)
  right_inv m := by
    refine Subtype.ext ?_
    exact (isPullback_baseChangeStructureHom B f V).lift_fst _ _ m.2

/-- The underlying morphism of `baseChangeHomEquiv B f V U a` is the composite of `a`, viewed
as a morphism of schemes, with the projection `baseChangeProj B f V`. -/
@[simp]
theorem baseChangeHomEquiv_apply_coe (a : U ⟶ (smallEtaleBaseChange B f).obj V) :
    (baseChangeHomEquiv B f V U a).1 =
      (SmallEtale.toScheme B X.obj X.property).map a ≫ baseChangeProj B f V :=
  rfl

/-- The ring map on global functions of the structure morphism of `U` *over `Y`* is the ring map
of `f` followed by restriction to `U`: these are the coefficients of the system presenting `V`,
read over `Γ(U, ⊤)`. -/
theorem appTop_schemeStructureHom_comp_inclusion_map :
    (schemeStructureHom B X.obj X.property U ≫ B.inclusion.map f).appTop.hom =
      (schemeStructureHom B X.obj X.property U).appTop.hom.comp
        (B.inclusion.map f).appTop.hom := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]

/-- **The sections of the representable sheaf of the base-changed chart, as a solution set.**
For an affine chart `V` of `Y` with a standard presentation
`Γ(V, ⊤) = Γ(Y, ⊤)[x₁, …, xₙ]/(P₁, …, Pₙ)`, the morphisms of the small étale site of `X` from a
chart `U` into `X ×_Y V` are exactly the tuples `a : Fin n → Γ(U, ⊤)` solving the system `P` with
its coefficients pushed along the structure map of `U` over `Y`.

This is the description of the comparison's target that step (3) of the proof of
[Stacks Project, Tag 04I6] needs, and it is obtained without any base change of the presentation:
the coefficient ring map is a parameter of `Stacks.EtaleCohomology.homOverEquivSolutions`, and by
`AlgebraicGeometry.SmallEtale.appTop_schemeStructureHom_comp_inclusion_map` it is the ring map of
`f` on global functions followed by restriction to `U` — which is exactly the coefficient map of
`AlgebraicGeometry.isSolution_comparisonCoord_globalSectionsMap` when `f` is chosen, as in the
source's first paragraph, so that its ring map on global functions is
`AlgebraicGeometry.RingedToposHom.globalSectionsMap`. -/
def baseChangeHomEquivSolutions [_root_.AlgebraicGeometry.IsAffine Y.obj]
    [_root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)] {n : ℕ}
    {P : Fin n → MvPolynomial (Fin n) Γ(Y.obj, ⊤)}
    (pres : Stacks.EtaleCohomology.StandardPresentationOver
      ((SmallEtale.toScheme B Y.obj Y.property).obj V)
      (schemeStructureHom B Y.obj Y.property V) P) :
    (U ⟶ (smallEtaleBaseChange B f).obj V) ≃
      {a : Fin n → Γ((SmallEtale.toScheme B X.obj X.property).obj U, ⊤) //
        MvPolynomial.IsSolution P
          (schemeStructureHom B X.obj X.property U ≫ B.inclusion.map f).appTop.hom a} :=
  (baseChangeHomEquiv B f V U).trans
    (Stacks.EtaleCohomology.homOverEquivSolutions
      ((SmallEtale.toScheme B X.obj X.property).obj U)
      ((SmallEtale.toScheme B Y.obj Y.property).obj V)
      (schemeStructureHom B Y.obj Y.property V)
      (schemeStructureHom B X.obj X.property U ≫ B.inclusion.map f) P pres)

end AlgebraicGeometry.SmallEtale

end
