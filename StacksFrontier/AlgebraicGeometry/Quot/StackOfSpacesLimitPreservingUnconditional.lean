module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SiteConventionAlgebraicLimit

/-!
# The stack `Spaces'_{fp, flat, proper}` is limit preserving

The stack `p'_{fp, flat, proper} : Spaces'_{fp, flat, proper} ⟶ Sch_fppf` of Stacks 0D1D is limit
preserving in the sense of Stacks 07XL (Stacks 0D1I).

The reduction of the statement to Stacks 07SK (algebraic spaces of finite presentation over
`T = lim Tᵢ` form the colimit of those over the `Tᵢ`) and to the descent of flatness (Stacks 08K0)
and properness (Stacks 08K1) through the limit is
`AlgebraicGeometry.isLimitPreserving_cartesianProperFlatFiberedCategory_of_descent`. Its five
inputs hold under the convention of Section 70.2 (tag 07SD), which asks nothing of the size of the
index:

* `AlgebraicGeometry.Space.modelsDescendUnderConvention`,
  `AlgebraicGeometry.Space.morphismsDescendUnderConvention` and
  `AlgebraicGeometry.Space.equalitiesDescendUnderConvention`: the three parts of Stacks 07SK, from
  `AlgebraicGeometry.Space.exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits`,
  `AlgebraicGeometry.Space.exists_morphism_after_baseChange_of_siteContainsBaseChangeLimits` and
  `AlgebraicGeometry.Space.eventually_eq_of_baseChange_eq_of_siteContainsBaseChangeLimits`, the
  limit being an algebraic space by Stacks 07SF under the convention;
* `AlgebraicGeometry.Space.propertyDescendsUnderConvention_isFlat` and
  `AlgebraicGeometry.Space.propertyDescendsUnderConvention_isProper`: Stacks 08K0 and 08K1 in the
  case `Y₀ = B₀` of Situation 084W, from
  `Space.MorphismDescentSituation.exists_isFlat_mapAt_of_siteContainsBaseChangeLimits` and
  `Space.MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`.

## Main results

* `AlgebraicGeometry.isLimitPreserving_cartesianProperFlatFiberedCategory`: the stack of
  finitely presented, flat and proper families of algebraic spaces is limit preserving.

## Implementation notes

The base of the stack in Stacks 0D1I is `Sch_fppf`, the big fppf site of `Spec(ℤ)`; as for Stacks
0D1D and 0D1E, the base here is the big fppf site of an arbitrary scheme `S` of the site, which
recovers `Sch_fppf` at `S = Spec(ℤ)`. The index categories of Stacks 07XL are taken in the scheme
universe, the smallness of the directed sets of Stacks 07XL.

## References

* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 08K0](https://stacks.math.columbia.edu/tag/08K0)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 07SK, essential surjectivity, under the convention of Section 70.2**, in the form
`AlgebraicGeometry.Space.ModelsDescendUnderConvention`. -/
theorem modelsDescendUnderConvention : ModelsDescendUnderConvention B S hS hZ :=
  fun _ _ _ D hD hA hQc hQs hconv Y hY hFp =>
    exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits B S hS hZ D hD hA hQc hQs
      hconv (isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD hA hQc)
      Y hY hFp

/-- **Stacks 07SK, fullness, under the convention of Section 70.2**, in the form
`AlgebraicGeometry.Space.MorphismsDescendUnderConvention`. -/
theorem morphismsDescendUnderConvention : MorphismsDescendUnderConvention B S hS hZ :=
  fun _ _ _ D hD hA hQc hQs hconv i Yᵢ Zᵢ hY hZ' hYfp hZfp f =>
    exists_morphism_after_baseChange_of_siteContainsBaseChangeLimits B S hS hZ D hD hA hQc hQs
      hconv (isAlgebraicSpace_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD hA hQc)
      i Yᵢ Zᵢ hY hZ' hYfp hZfp f

/-- **Stacks 07SK, faithfulness, under the convention of Section 70.2**, in the form
`AlgebraicGeometry.Space.EqualitiesDescendUnderConvention`. -/
theorem equalitiesDescendUnderConvention : EqualitiesDescendUnderConvention B S hS hZ :=
  fun _ _ _ D hD hA hQc _ hconv i Yᵢ Zᵢ hY hZ' hYfp hZfp f g hfg =>
    eventually_eq_of_baseChange_eq_of_siteContainsBaseChangeLimits B S hS D hD hA hQc
      hconv i Yᵢ Zᵢ hY hZ' hYfp hZfp f g hfg

variable {B S hS hZ} in
/-- **Descent of a property to the distinguished stage, from Situation 084W.** If a base-change
stable property `P` descends through the limit in every Situation 084W under the convention of
Section 70.2, given `H` of the morphism at the distinguished stage, then it does so in the form
`AlgebraicGeometry.Space.PropertyDescendsUnderConvention P H`: the morphism `f₀ : X₀ ⟶ B_{i₀}` is
the situation with `Y₀ = B_{i₀}` and structure morphism the identity, whose base changes to the
limit and to the stages agree with those of the proposition up to the isomorphisms
`B ×_{B_{i₀}} B_{i₀} ≅ B` and `B_i ×_{B_{i₀}} B_{i₀} ≅ B_i`. -/
theorem propertyDescendsUnderConvention_of_situation
    {P H : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop}
    (hP : StackOfSpacesLimit.BaseChangeStable P)
    (hsit : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (D : MorphismDescentSituation B S hS hZ I), SiteContainsBaseChangeLimits B S hS D.base →
        P D.mapLimit → H D.map₀ → ∃ (i : I) (hi : D.initial ≤ i), P (D.mapAt i hi)) :
    PropertyDescendsUnderConvention B S hS hZ P H := by
  intro I _ _ _ base hb haff hlim hconv i₀ X₀ f₀ hX₀ hqc hqs hXqc hXqs hPL hH
  let D : MorphismDescentSituation B S hS hZ I :=
    { base := base
      base_isAlgebraicSpace := hb
      transition_affine := haff
      limit_isAlgebraicSpace := hlim
      initial := i₀
      source₀ := X₀
      target₀ := base.obj (op i₀)
      sourceToBase := f₀
      targetToBase := 𝟙 _
      map₀ := f₀
      map₀_over := Category.comp_id _
      source₀_isAlgebraicSpace := hX₀
      target₀_isAlgebraicSpace := hb i₀
      base₀_quasiCompact := hqc
      base₀_quasiSeparated := hqs
      source₀_quasiCompact := hXqc
      source₀_quasiSeparated := hXqs
      target₀_quasiCompact := hqc
      target₀_quasiSeparated := hqs }
  have hfstIso : ∀ {A C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : A ⟶ C),
      IsIso (pullback.fst a (𝟙 C)) := fun a =>
    (IsPullback.of_hasPullback a (𝟙 _)).isIso_fst_of_isIso
  have hlimP : P D.mapLimit := by
    have : IsIso (X := D.targetLimit) (Y := limit base)
        (pullback.fst (limit.π base (op i₀)) (𝟙 (base.obj (op i₀)))) :=
      hfstIso (limit.π base (op i₀))
    exact hP (g' := 𝟙 D.sourceLimit) (f := pullback.fst (limit.π base (op i₀)) f₀)
      (g := pullback.fst (limit.π base (op i₀)) (𝟙 (base.obj (op i₀))))
      D.sourceLimit_isAlgebraicSpace D.sourceLimit_isAlgebraicSpace
      D.targetLimit_isAlgebraicSpace hlim
      (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans D.mapLimit_fst.symm⟩) hPL
  obtain ⟨i, hi, hPi⟩ := hsit I D hconv hlimP hH
  refine ⟨i, hi, ?_⟩
  have : IsIso (X := D.targetAt i hi) (Y := base.obj (op i))
      (pullback.fst (base.map (homOfLE hi).op) (𝟙 (base.obj (op i₀)))) :=
    hfstIso (base.map (homOfLE hi).op)
  have : IsIso (X := base.obj (op i)) (Y := D.targetAt i hi)
      (inv (X := D.targetAt i hi) (Y := base.obj (op i))
        (pullback.fst (base.map (homOfLE hi).op) (𝟙 (base.obj (op i₀))))) :=
    IsIso.inv_isIso
  exact hP (g' := 𝟙 (D.sourceAt i hi)) (f := D.mapAt i hi)
    (g := inv (X := D.targetAt i hi) (Y := base.obj (op i))
      (pullback.fst (base.map (homOfLE hi).op) (𝟙 (base.obj (op i₀)))))
    (D.sourceAt_isAlgebraicSpace i hi) (D.sourceAt_isAlgebraicSpace i hi) (hb i)
    (D.targetAt_isAlgebraicSpace i hi)
    (IsPullback.of_horiz_isIso
      ⟨(Category.id_comp _).trans ((IsIso.eq_comp_inv _).mpr (D.mapAt_fst i hi))⟩) hPi

/-- **Stacks 08K0, flatness, for a morphism to the distinguished stage, under the convention of
Section 70.2**, in the form `AlgebraicGeometry.Space.PropertyDescendsUnderConvention`. -/
theorem propertyDescendsUnderConvention_isFlat :
    PropertyDescendsUnderConvention B S hS hZ (fun f => IsFlat B S hS f)
      (fun f => IsLocallyOfFinitePresentation B S hS f) :=
  propertyDescendsUnderConvention_of_situation StackOfSpacesLimit.baseChangeStable_isFlat
    fun _ _ _ _ D hconv hP hH => D.exists_isFlat_mapAt_of_siteContainsBaseChangeLimits hconv hP hH

/-- **Stacks 08K1 for a morphism to the distinguished stage, under the convention of
Section 70.2**, in the form `AlgebraicGeometry.Space.PropertyDescendsUnderConvention`. -/
theorem propertyDescendsUnderConvention_isProper :
    PropertyDescendsUnderConvention B S hS hZ (fun f => IsProper B S hS f)
      (fun f => IsLocallyOfFiniteType B S hS f) :=
  propertyDescendsUnderConvention_of_situation StackOfSpacesLimit.baseChangeStable_isProper
    fun _ _ _ _ D hconv hP hH => D.exists_isProper_mapAt_of_siteContainsBaseChangeLimits hconv hP hH

end Space

/-- The stack `p'_{fp, flat, proper} : Spaces'_{fp, flat, proper} ⟶ Sch_fppf` of finitely
presented, flat and proper families of algebraic spaces is limit preserving (Stacks 07XL): for
every directed inverse system of affine schemes `Tᵢ` of the site with limit `T` in the site, base
change is an equivalence from the colimit of the fibre categories over the `Tᵢ` to the fibre
category over `T`.

The base is the big fppf site of an arbitrary scheme `S` of the site, which recovers `Sch_fppf` at
`S = Spec(ℤ)`; the index categories are those of the scheme universe, the smallness of the directed
sets of Stacks 07XL. -/
@[stacks 0D1I "over the big fppf site of an arbitrary base scheme `S`; the source's `Sch_fppf` is \
`S = Spec(ℤ)`"]
theorem isLimitPreserving_cartesianProperFlatFiberedCategory
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B S hS
      (cartesianProperFlatFiberedCategory B S hS) :=
  isLimitPreserving_cartesianProperFlatFiberedCategory_of_descent B S hS
    (Space.modelsDescendUnderConvention B S hS B.contains_terminal)
    (Space.morphismsDescendUnderConvention B S hS B.contains_terminal)
    (Space.equalitiesDescendUnderConvention B S hS B.contains_terminal)
    (Space.propertyDescendsUnderConvention_isFlat B S hS B.contains_terminal)
    (Space.propertyDescendsUnderConvention_isProper B S hS B.contains_terminal)

end AlgebraicGeometry

end
