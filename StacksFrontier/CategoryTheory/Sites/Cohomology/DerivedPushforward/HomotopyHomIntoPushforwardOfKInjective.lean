module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.OrdinaryAndDerivedCounit
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms into the direct image of a K-injective complex see no difference between `K` and `D`

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi, let `I` be a K-injective
complex of `𝒪_C`-modules and let `P` be an object of the unbounded homotopy category of
`𝒪_D`-modules at which the comparison `Lf^* ⟶ f^*` of Tag 06YY is invertible — for instance a
bounded above complex of flat `𝒪_D`-modules. This file proves that localization

`Hom_{K(𝒪_D)}(P, f_* I) ⟶ Hom_{D(𝒪_D)}(P, f_* I)`

is **bijective**, although `f_* I` is not K-injective: Stacks 093Y needs `f` flat and is false
in general.

The reason is the adjunction. Transposing along the degreewise `f^* ⊣ f_*` identifies the
left-hand side with `Hom_{K(𝒪_C)}(f^* P, I)`, which localization identifies with
`Hom_{D(𝒪_C)}(f^* P, I)` because `I` *is* K-injective; and the right-hand side is identified
with the same group by the derived adjunction `Lf^* ⊣ Rf_*` of Stacks 07A6, after `Rf_*(I)` has
been replaced by `f_* I` — legitimate because `I` is K-injective — and `Lf^* P` by `f^* P`,
which is the hypothesis on `P`. That the two identifications agree is Stacks 0FPI together with
the naturality of the comparison, and is `derivedAdjunction_homEquiv_symm_qh_map` below.

## Main results

* `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction_homEquiv_symm_qh_map`: the
  square relating the derived transposition to the degreewise one, out of Stacks 0FPI.
* `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.bijective_qh_map_pushforward_of_isKInjective`:
  the bijectivity.

## Implementation notes

No tag: the statement is not an enumerated assertion of the source. It is the step on which the
unrestricted Stacks 0D6H turns, `Γ(V, -)` being corepresented by `j_{V!} 𝒪_V`
(`Stacks.Sites.ExtensionByZero.sectionsOverObjectHomologyAddEquiv`), so that the content of
0D6H's clause is exactly a bijectivity of this shape.

The hypothesis on `P` is carried as the invertibility of the comparison rather than as
K-flatness, because that is what the proof uses and because
`isIso_derivedPullbackComparison_app_of_boundedAbove_of_flat` (in the namespace
`Stacks.Sheaves.RingedToposDerivedPullback`) supplies it for a bounded above complex of flat
modules — which is what the single complex `(j_{V!} 𝒪_V)[0]` is, by Stacks 03EV.

`hmos` is the library's spelling of *morphism of ringed topoi*, exactly as in the Stacks
07A6, 0FPI, 0D6D and 0D6E statements of this chain; see the implementation notes of
`OrdinaryAndDerivedCounit.lean`.

## References

* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

include hmos in
/-- **The derived transposition is the degreewise one.** For `g : P ⟶ f_* K` in the unbounded
homotopy category of `𝒪_D`-modules, transposing `Q(g)` followed by the comparison
`f_* K ⟶ Rf_* K` along the derived adjunction `Lf^* ⊣ Rf_*` gives the comparison
`Lf^* P ⟶ f^* P` followed by the localization of the degreewise transpose of `g`.

The proof is Stacks 0FPI applied at `K`, preceded by the naturality of the comparison
`Lf^* ⟶ f^*` at `g`. -/
theorem derivedAdjunction_homEquiv_symm_qh_map
    (P : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    (g : P ⟶ (f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) :
    ((derivedAdjunction f hmos).homEquiv (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj K)).symm
        (DerivedCategory.Qh.map g ≫ (derivedPushforwardUnit f).app K) =
      (derivedPullbackComparison f).app P ≫ DerivedCategory.Qh.map
        (((homotopyPullbackPushforwardAdjunction f).homEquiv P K).symm g) := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    derivedAdjunction_counit_fac f hmos K, Adjunction.homEquiv_counit, Functor.map_comp,
    ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ DerivedCategory.Qh.map
    ((homotopyPullbackPushforwardAdjunction f).counit.app K))
    ((derivedPullbackComparison f).naturality g)

/-- Postcomposition with the comparison `f_* K ⟶ Rf_* K`, which is invertible when `K` is the
image of a K-injective complex. -/
noncomputable def postcompDerivedPushforwardUnitEquiv
    (P : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))
    [IsIso ((derivedPushforwardUnit f).app K)] :
    (DerivedCategory.Qh.obj P ⟶
        DerivedCategory.Qh.obj
          ((f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K)) ≃
      (DerivedCategory.Qh.obj P ⟶ (derivedPushforward f).obj (DerivedCategory.Qh.obj K)) where
  toFun q := q ≫ (derivedPushforwardUnit f).app K
  invFun r := r ≫ inv ((derivedPushforwardUnit f).app K)
  left_inv q := by simp
  right_inv r := by simp

/-- Precomposition with the comparison `Lf^* P ⟶ f^* P`, which is invertible at the `P` of
`bijective_qh_map_pushforward_of_isKInjective`. -/
noncomputable def precompDerivedPullbackComparisonEquiv
    (P : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [IsIso ((derivedPullbackComparison f).app P)] :
    (DerivedCategory.Qh.obj ((f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) ⟶
        Z) ≃
      ((derivedPullback f).obj (DerivedCategory.Qh.obj P) ⟶ Z) where
  toFun h := (derivedPullbackComparison f).app P ≫ h
  invFun k := inv ((derivedPullbackComparison f).app P) ≫ k
  left_inv h := by simp
  right_inv k := by simp

include hmos in
/-- **Localization is bijective on morphisms into the direct image of a K-injective complex.**
If `I` is a K-injective complex of `𝒪_C`-modules and the comparison `Lf^* ⟶ f^*` of Tag 06YY is
invertible at `P`, then

`Hom_{K(𝒪_D)}(P, f_* I) ⟶ Hom_{D(𝒪_D)}(P, f_* I)`

is bijective. Note that `f_* I` is *not* assumed K-injective: that is Stacks 093Y, which needs
`f` flat and is false in general.

Both sides are identified with `Hom(f^* P, I)` — the left by the degreewise adjunction, the
right by the derived one after the two comparisons have been inverted — and the two
identifications agree by `derivedAdjunction_homEquiv_symm_qh_map`, which is Stacks 0FPI. -/
theorem bijective_qh_map_pushforward_of_isKInjective
    (P : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    [IsIso ((derivedPullbackComparison f).app P)]
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective) :
    Function.Bijective (DerivedCategory.Qh.map :
      (P ⟶ (f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (ComplexShape.up ℤ)).obj I)) → _) := by
  have := hI
  have := isIso_derivedPushforwardUnit_app_of_isKInjective f I hI
  set Iq := (HomotopyCategory.quotient
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ)).obj I with hIq
  let F : (DerivedCategory.Qh.obj P ⟶ DerivedCategory.Qh.obj
        ((f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj Iq)) → _ :=
    fun q => ((derivedAdjunction f hmos).homEquiv (DerivedCategory.Qh.obj P)
      (DerivedCategory.Qh.obj Iq)).symm (q ≫ (derivedPushforwardUnit f).app Iq)
  have hu : Function.Bijective F :=
    (((derivedAdjunction f hmos).homEquiv (DerivedCategory.Qh.obj P)
      (DerivedCategory.Qh.obj Iq)).symm.bijective).comp
        (postcompDerivedPushforwardUnitEquiv f P Iq).bijective
  refine (Function.Bijective.of_comp_iff' hu _).1 ?_
  have hfun : F ∘ DerivedCategory.Qh.map =
      (precompDerivedPullbackComparisonEquiv f P (DerivedCategory.Qh.obj Iq)) ∘
        (DerivedCategory.Qh.map :
          ((f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj P ⟶ Iq) → _) ∘
        ((homotopyPullbackPushforwardAdjunction f).homEquiv P Iq).symm :=
    funext fun g => derivedAdjunction_homEquiv_symm_qh_map f hmos P Iq g
  exact hfun ▸ ((precompDerivedPullbackComparisonEquiv f P
      (DerivedCategory.Qh.obj Iq)).bijective.comp
    ((CochainComplex.IsKInjective.Qh_map_bijective
      ((f.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj P) I).comp
      ((homotopyPullbackPushforwardAdjunction f).homEquiv P Iq).symm.bijective))

end Stacks.Cohomology.DerivedPullbackOnRingedTopoi

end
