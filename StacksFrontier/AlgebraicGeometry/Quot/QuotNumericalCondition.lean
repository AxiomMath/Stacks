module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertNumericalQuotFibreProduct
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorModel

/-!
# `Quot^P_{F/X/B}` as a subfunctor of the Quot functor

Let `f : X ⟶ B` be a separated morphism of algebraic spaces of finite presentation, `F` a
quasi-coherent `𝒪_X`-module, and fix the data of Situation 0DNC: a set `I`, perfect objects
`E_i ∈ D(𝒪_X)` and `P : I → ℤ`.  Remark 0DP6 defines `Quot^P_{F/X/B}` as the fibre product
`Quot_{F/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`
(`AlgebraicGeometry.Space.QuotSituation.numericalQuot`).  Since `Coh^P_{X/B}` is a full
subcategory of `Coh_{X/B}`, closed under the morphisms of `Coh_{X/B}` as soon as the functions
`χ_i(t) = χ(K_i ⊗^𝐋 κ(t))` are compatible with pullback, the fibre product is the subfunctor of
the Quot presheaf of the quotients `F_T ⟶ 𝒬` whose object `(T, 𝒬)` of `Coh_{X/B}` lies in
`Coh^P_{X/B}`.

The properties of `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` asserted by Remark 0DP6 are deduced by base
change from those of `Coh^P_{X/B} ⟶ Coh_{X/B}` (Lemmas 0DND, 0DNE and Example 0DNF): a flat
closed immersion when the `χ_i` are locally constant, an open and closed immersion when moreover
`I` is finite, or every object of `Coh_{X/B}` is locally pulled back from one over a locally
Noetherian test scheme.  A model of `Quot^P_{F/X/B}` in the universe of the site is then an
algebraic space as soon as a model of `Quot_{F/X/B}` is.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.numericalQuotCondition`: `Quot^P_{F/X/B}` as a
  subfunctor of the Quot presheaf.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.mem_numericalQuotCondition_iff_exists_numericalQuot`:
  a quotient lies in the subfunctor exactly when it lifts to the fibre product
  `AlgebraicGeometry.Space.QuotSituation.numericalQuot`.
* `QuotSituation.relative_closedImmersion_flat_numericalQuotCondition_of_isLocallyConstant`: the
  flat closed immersion, and its open and closed variants
  `relative_openImmersion_closedImmersion_numericalQuotCondition_of_finite` and
  `relative_openImmersion_closedImmersion_numericalQuotCondition_of_noetherianDescent`.
* `AlgebraicGeometry.Space.QuotSituation.isAlgebraicSpace_subfunctorModel_numericalQuotCondition`:
  models of `Quot^P_{F/X/B}` are algebraic spaces when a model of `Quot_{F/X/B}` is.
* `AlgebraicGeometry.Space.QuotSituation.numericalQuotCondition_eq_top_of_isEmpty`: for the empty
  index set `Quot^P_{F/X/B}` is all of `Quot_{F/X/B}`.

## Implementation notes

On a big fppf site, whose schemes are bounded in size by the cutoff `κ` of the site, the
algebraicity of `Quot^P_{F/X/B}` fails for an arbitrary quasi-coherent `F`, for the reason the
first assertion of Stacks 09TU does: for the empty index set `Quot^P_{F/X/B} = Quot_{F/X/B}`, and
for `X = B = Spec K`, `K` separably closed, and `F` free of rank `κ + 1`, the Quot functor has at
least `2 ^ κ` points over `Spec K` while an algebraic space over `Spec K` has fewer than `κ`.

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space.QuotSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotSituation B S hS) (N : NumericalSituation.{u, v, u} B S hS D.toCoherentSituation)

/-- **`Quot^P_{F/X/B}`** as a subfunctor of the Quot presheaf: the quotients `F_T ⟶ 𝒬` whose
object `(T, 𝒬)` of `Coh_{X/B}` has `χ_i(t) = P(i)` for all `i ∈ I` and all `t ∈ |T|`.  It is a
subfunctor because the numerical invariants are compatible with pullback, `hbc`. -/
def numericalQuotCondition
    (hbc : ∀ {A' A : CoherentObject D.toCoherentSituation} (φ : CoherentHom A' A) (i : N.I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t)) :
    Subfunctor D.quotSitePresheaf :=
  D.quotCondition N.HasNumericalInvariants
    (CoherentSituation.numerical_points_of_hom (χ := N.numericalEuler) N.P hbc)

variable {N}
  (hbc : ∀ {A' A : CoherentObject D.toCoherentSituation} (φ : CoherentHom A' A) (i : N.I)
    (t : points B S hS (yoneda.obj A'.T.left)),
    N.numericalEuler A' i t = N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))

/-- The numerical invariants `χ_i = P i` are inherited along the morphisms of `Coh_{X/B}`. -/
private theorem hasNumericalInvariants_of_hom
    (hbc : ∀ {A' A : CoherentObject D.toCoherentSituation} (φ : CoherentHom A' A) (i : N.I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    {A' A : CoherentObject D.toCoherentSituation} :
    CoherentHom A' A → N.HasNumericalInvariants A → N.HasNumericalInvariants A' :=
  fun φ => CoherentSituation.numerical_points_of_hom (χ := N.numericalEuler) N.P hbc φ

/-- A quotient lies in `Quot^P_{F/X/B}` exactly when its object of `Coh_{X/B}` lies in
`Coh^P_{X/B}`. -/
theorem mem_numericalQuotCondition_iff {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : D.quotSitePresheaf.obj T) :
    x ∈ (D.numericalQuotCondition N hbc).obj T ↔ N.HasNumericalInvariants x.cohObject :=
  Iff.rfl

/-- **The subfunctor is the fibre product of Remark 0DP6.**  A quotient `F_T ⟶ 𝒬` lies in the
subfunctor `Quot^P_{F/X/B}` exactly when it lifts to the 2-fibre product
`Quot_{F/X/B} ×_{Coh_{X/B}} Coh^P_{X/B}`, whose projection to `Quot_{F/X/B}` is fully faithful
(`AlgebraicGeometry.Space.QuotSituation.full_numericalQuotToQuot`,
`AlgebraicGeometry.Space.QuotSituation.faithful_numericalQuotToQuot`). -/
theorem mem_numericalQuotCondition_iff_exists_numericalQuot {T : (BigFppfOver B S hS)ᵒᵖ}
    (x : D.quotSitePresheaf.obj T) :
    x ∈ (D.numericalQuotCondition N hbc).obj T ↔
      ∃ P : D.NumericalQuotObjects N, P.x = QuotFamilyOver.toQuotObjects x :=
  (D.exists_numericalQuot_x_eq_toQuotObjects_iff N
    (hasNumericalInvariants_of_hom D hbc) x).symm

/-- `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is a flat closed immersion as soon as the numerical
invariants `χ_i` are locally constant. -/
theorem relative_closedImmersion_flat_numericalQuotCondition_of_isLocallyConstant
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} ⊓ @Flat.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (D.numericalQuotCondition N hbc).ι :=
  D.relative_closedImmersion_flat_quotCondition_ι_of_isFlatClosedCondition
    (hasNumericalInvariants_of_hom D hbc)
    (N.isFlatClosedCondition_hasNumericalInvariants hbc hlc)

/-- `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is an open and closed immersion for a finite index set as
soon as the numerical invariants `χ_i` are locally constant. -/
theorem relative_openImmersion_closedImmersion_numericalQuotCondition_of_finite [Finite N.I]
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (D.numericalQuotCondition N hbc).ι :=
  D.relative_openImmersion_closedImmersion_quotCondition_ι_of_isOpenAndClosedCondition
    (hasNumericalInvariants_of_hom D hbc)
    (N.isOpenAndClosedCondition_hasNumericalInvariants hbc hlc)

/-- `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is an open and closed immersion, for any index set, as soon as
the numerical invariants `χ_i` are locally constant and every object of `Coh_{X/B}` is, near every
point of its test scheme, pulled back from an object over a locally Noetherian test scheme. -/
theorem relative_openImmersion_closedImmersion_numericalQuotCondition_of_noetherianDescent
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i))
    (hloc : ∀ (A : CoherentObject D.toCoherentSituation) (t : A.testScheme),
      ∃ (A' A₀ : CoherentObject D.toCoherentSituation) (p : CoherentHom A' A)
        (_ : CoherentHom A' A₀) (t' : A'.testScheme),
        p.baseScheme t' = t ∧ IsOpenMap p.baseScheme ∧ IsLocallyNoetherian A₀.testScheme) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} ⊓
        @_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (D.numericalQuotCondition N hbc).ι :=
  D.relative_openImmersion_closedImmersion_quotCondition_ι_of_isOpenAndClosedCondition
    (hasNumericalInvariants_of_hom D hbc)
    (N.isOpenAndClosedCondition_hasNumericalInvariants_of_noetherianDescent hbc hlc hloc)

/-- **Models of `Quot^P_{F/X/B}` are algebraic spaces when a model of `Quot_{F/X/B}` is**, as soon
as the numerical invariants `χ_i` are locally constant: the inclusion is a flat closed immersion,
so Stacks 02WY applies. -/
theorem isAlgebraicSpace_subfunctorModel_numericalQuotCondition
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i))
    (M : QuotSitePresheafModel D) (hM : IsAlgebraicSpace B S hS M.presheaf)
    (F : D.SubfunctorModel (D.numericalQuotCondition N hbc)) :
    IsAlgebraicSpace B S hS F.presheaf :=
  D.isAlgebraicSpace_subfunctorModel_quotCondition_of_isFlatClosedCondition
    (hasNumericalInvariants_of_hom D hbc)
    (N.isFlatClosedCondition_hasNumericalInvariants hbc hlc) M hM F

/-- **For the empty index set, `Quot^P_{F/X/B}` is all of `Quot_{F/X/B}`**: there is no condition
to impose. -/
theorem numericalQuotCondition_eq_top_of_isEmpty [IsEmpty N.I] :
    D.numericalQuotCondition N hbc = ⊤ := by
  ext T x
  simp only [Subfunctor.top_obj, Set.mem_univ, iff_true]
  exact fun i => isEmptyElim i

end AlgebraicGeometry.Space.QuotSituation

end
