module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverAffineFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.QuasicoherentDerivedTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsTerminalBase
public import StacksFrontier.CategoryTheory.Triangulated.CoreflectionGeneratorBijective

/-!
# The proof of Stacks 0D3F, from a generator of `D_QCoh(𝒪_X)` and its product property

Let `R` be a ring, `X` a quasi-compact and quasi-separated algebraic space, `f : X ⟶ Spec(R)` flat
and `(M_n)` an inverse system of `R`-modules with surjective transition maps.  Write
`Φ = 𝒪_X ⊗_R -`.  Stacks 0D3F asserts that the canonical map `Φ(lim M_n) ⟶ lim Φ(M_n)` induces a
bijection on maps out of every object of `D_QCoh(𝒪_X)`.

The source's proof has three parts.  Reduction to a generator: `D_QCoh(𝒪_X)` is coreflective in
`D(𝒪_X)` (Stacks 0CR4) and has a perfect generator `P` (Stacks 09IY), so it suffices to test
against the shifts of `P`.  Reduction to products: both rows of the comparison
`lim ⟶ ∏ ⟶ ∏` are short exact (flatness of `f` and surjectivity of the transition maps), and
the ordinary product of quasi-coherent modules is the derived product, so by the five lemma it
suffices that `M ↦ Hom(P[k], Φ(M))` carry `∏ M_n` to the product of the `Hom(P[k], Φ(M_n))`.
The product property itself: `Hom(P[k], Φ(M)) = H^{-k}(RΓ(X, P^∨) ⊗^L_R M)` (Stacks 08IN), and
`RΓ(X, P^∨)` is perfect for `f` proper, flat and of finite presentation (Stacks 0CTM), so this
functor commutes with products (Stacks 0CYB).

This file proves the first two parts, with the generator and its product property as the inputs.

## Main results

* `AlgebraicGeometry.Space.bijective_comp_single_limitComparison_baseRingTensorModule`: given a
  generator `G` of `D_QCoh(𝒪_X)` such that `M ↦ Hom(G[k], Φ(M))` carries `∏ M_n` to a product for
  every `k`, composition with `Φ(lim M_n) ⟶ lim Φ(M_n)` in degree zero is bijective on maps out
  of every object of `D_QCoh(𝒪_X)`.

## References

* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 09IY](https://stacks.math.columbia.edu/tag/09IY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck CategoryTheory.Limits.hasProduct_comp_obj

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The proof of Stacks 0D3F, given the generator and its product property.** Let `X` be a
quasi-compact and quasi-separated algebraic space, `f : X ⟶ Spec(R)` flat with `R = Γ(T, 𝒪_T)` for
an affine `T`, and `(M_n)` an inverse system of `R`-modules with surjective transition maps; write
`Φ = 𝒪_X ⊗_R -`.  Let `G` be a weak triangulated generator of `D_QCoh(𝒪_X)` such that, for every
`k`, every family of maps `G[k] ⟶ Φ(M_n)` in degree zero comes from exactly one map
`G[k] ⟶ Φ(∏ M_n)` by composing with the images of the projections.  Then composition with the
canonical map `Φ(lim M_n) ⟶ lim Φ(M_n)`, placed in degree zero, is bijective on maps out of every
object `E` of `D_QCoh(𝒪_X)`.

In the source the generator is the perfect generator of Stacks 09IY and the product property is
Stacks 08IN, 0CTM and 0CYB applied to it, for `f` proper, flat and of finite presentation. -/
theorem bijective_comp_single_limitComparison_baseRingTensorModule
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ =>
      (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (Msys.obj ⟨n⟩)]
    [HasLimit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f))]
    (G : (qcohDerivedProp B S hS X).FullSubcategory)
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator)
    (hGprod : ∀ k : ℤ, Function.Bijective
      (fun a : G.obj⟦k⟧ ⟶ (DerivedCategory.singleFunctor _ 0).obj
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj
            (∏ᶜ fun n : ℕ => Msys.obj ⟨n⟩)) =>
        fun n : ℕ => a ≫ (DerivedCategory.singleFunctor _ 0).map
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).map
            (Pi.π (fun n : ℕ => Msys.obj ⟨n⟩) n))))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : qcohDerivedProp B S hS X E) :
    Function.Bijective
      (fun a : E ⟶ (DerivedCategory.singleFunctor _ 0).obj
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (limit Msys)) =>
        a ≫ (DerivedCategory.singleFunctor _ 0).map
          (limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f)))) := by
  have := isLeftAdjoint_qcohDerivedProp_ι_of_qcqs B S hS hZ X hXqc hXqs
  let Φ := baseRingTensorModule B S hS X (baseRingHomOfMap f)
  let A : (qcohDerivedProp B S hS X).FullSubcategory :=
    ⟨(DerivedCategory.singleFunctor _ 0).obj (Φ.obj (limit Msys)),
      derivedCategoryB_singleFunctor_obj B S hS X.1 X.2 _
        (isQuasicoherentOnSite_baseRingTensorModule B S hS X _ _)⟩
  have hrow := bijective_comp_single_limitComparison Φ Msys
    (shortExact_map_inverseLimitSequence_baseRingTensorModule f hflat hT Msys hsurj)
    (shortExact_inverseLimitSequence_baseRingTensorModule B S hS X _ Msys hsurj) G.obj
    (fun k => bijective_comp_single_piComparison_baseRingTensorModule B S hS X _ Msys _
      (hGprod k))
  exact (Adjunction.ofIsLeftAdjoint (qcohDerivedProp B S hS X).ι)
    |>.bijective_comp_of_bijective_comp_generator_shift G hG (A := A)
    ((DerivedCategory.singleFunctor _ 0).map (limit.post Msys Φ))
    (fun n => (Pretriangulated.bijective_comp_iff_of_source_iso
      (((qcohDerivedProp B S hS X).ι.commShiftIso n).app G).symm _).1 (hrow n)) ⟨E, hE⟩

/-- An algebraic space of finite presentation over an affine scheme is quasi-compact and
quasi-separated: the affine target is quasi-compact and separated (Stacks 06G5). -/
theorem qcqs_of_isFinitePresentation_schemeSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hfp : IsFinitePresentation B S hS f.hom) :
    IsQuasiCompactSpace B S hS X.1 ∧ IsAbsolutelyQuasiSeparated B S hS hZ X.1 :=
  have hTaff : IsAffineSpace B S hS (schemeSpace T).1 := isAffineSpace_yoneda B S hS T hT
  qcqs_of_isFinitePresentation B S hS hZ X.2 (schemeSpace T).2 hTaff.isQuasiCompactSpace
    (isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ (schemeSpace T).1
      (isAbsolutelySeparated_of_isAffineSpace B S hS hZ hTaff)) hfp

/-- `AlgebraicGeometry.Space.bijective_comp_single_limitComparison_baseRingTensorModule` for
`f : X ⟶ Spec(R)` of finite presentation, which makes `X` quasi-compact and quasi-separated. -/
theorem bijective_comp_single_limitComparison_baseRingTensorModule_of_isFinitePresentation
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (f : X ⟶ schemeSpace T) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (Msys : ℕᵒᵖ ⥤ ModuleCat.{u} (baseRing B S hS T))
    (hsurj : ∀ n : ℕ, Function.Surjective (Msys.map (homOfLE (Nat.le_succ n)).op))
    [HasProduct fun n : ℕ =>
      (baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (Msys.obj ⟨n⟩)]
    [HasLimit (Msys ⋙ baseRingTensorModule B S hS X (baseRingHomOfMap f))]
    (G : (qcohDerivedProp B S hS X).FullSubcategory)
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator)
    (hGprod : ∀ k : ℤ, Function.Bijective
      (fun a : G.obj⟦k⟧ ⟶ (DerivedCategory.singleFunctor _ 0).obj
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj
            (∏ᶜ fun n : ℕ => Msys.obj ⟨n⟩)) =>
        fun n : ℕ => a ≫ (DerivedCategory.singleFunctor _ 0).map
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).map
            (Pi.π (fun n : ℕ => Msys.obj ⟨n⟩) n))))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : qcohDerivedProp B S hS X E) :
    Function.Bijective
      (fun a : E ⟶ (DerivedCategory.singleFunctor _ 0).obj
          ((baseRingTensorModule B S hS X (baseRingHomOfMap f)).obj (limit Msys)) =>
        a ≫ (DerivedCategory.singleFunctor _ 0).map
          (limit.post Msys (baseRingTensorModule B S hS X (baseRingHomOfMap f)))) :=
  have hqcqs := qcqs_of_isFinitePresentation_schemeSpace hZ f hT hfp
  bijective_comp_single_limitComparison_baseRingTensorModule hZ f hflat hT hqcqs.1 hqcqs.2 Msys
    hsurj G hG hGprod E hE

end AlgebraicGeometry.Space

end
