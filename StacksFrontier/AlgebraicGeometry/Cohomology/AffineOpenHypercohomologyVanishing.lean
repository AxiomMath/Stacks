module

public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineOpenHypercohomologyEdge
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.DerivedSectionsUnderlyingGroups
public import StacksFrontier.CategoryTheory.Sites.Modules.SectionsOverObjectDerivedCategory

/-!
# Vanishing of hypercohomology over an affine open, and the Hom groups it kills

Let `X` be a scheme, let `E` be an object of `D(𝒪_X)` all of whose cohomology sheaves are
quasi-coherent, and let `U` be an affine open of `X`.  If `H^q(E) = 0` then the degree-`q`
hypercohomology of `E` over `U` vanishes, in the abelian-group-valued spelling of derived
sections; consequently every morphism `j_{U!} 𝒪_U ⟶ E⟦q⟧` of `D(𝒪_X)`, and every morphism out of
a direct sum of copies of `j_{U!} 𝒪_U`, is zero.

## Main results

* `AlgebraicGeometry.isZero_homology_derivedSectionsOverObject_of_isAffineOpen`: if `H^q(E) = 0`
  then `H^q(RΓ(U, E)) = 0` in `Ab`, for `U` affine and `E` with quasi-coherent cohomology.
* `AlgebraicGeometry.subsingleton_hom_singleExtensionByZeroUnit_of_isAffineOpen`: if
  `H^q(E) = 0` then every morphism `j_{U!} 𝒪_U ⟶ E⟦q⟧` is zero.
* `AlgebraicGeometry.subsingleton_hom_cofan_singleExtensionByZeroUnit_of_isAffineOpen`: if
  `H^q(E) = 0` then every morphism from a coproduct of copies of `j_{U!} 𝒪_U` to `E⟦q⟧` is zero.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.HypercohomologyEdge.evaluation_additive

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (E : DerivedCategory X.Modules)

/-- **Hypercohomology over an affine open vanishes where the cohomology sheaf does.**  For an
object of `D(𝒪_X)` with quasi-coherent cohomology and an affine open `U`, if `H^q(E) = 0` then
`H^q(RΓ(U, E)) = 0`, in the abelian-group-valued spelling of derived sections. -/
theorem isZero_homology_derivedSectionsOverObject_of_isAffineOpen
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj E).IsQuasicoherent)
    (U : X.Opens) (hU : U ∈ X.affineOpens) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor X.Modules q).obj E)) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject
        X.zariskiRingedSite U).obj E)) := by
  refine IsZero.of_iso ?_
    ((Stacks.Cohomology.HypercohomologyEdge.homologyDerivedSectionsForgetModuleIso
      X.zariskiRingedSite U q).app E)
  exact Functor.map_isZero
    (Stacks.Cohomology.HypercohomologyEdge.forgetSectionsModule X.zariskiRingedSite U)
    (IsZero.of_iso
      (Functor.map_isZero (SheafOfModules.evaluation X.ringCatSheaf (op U)) hq)
      (affineOpenHypercohomologyIso X E hE U hU q))

/-- **Morphisms from `j_{U!} 𝒪_U` vanish over an affine open.**  If `H^q(E) = 0` then every
morphism `j_{U!} 𝒪_U ⟶ E⟦q⟧` of `D(𝒪_X)` is zero, for `U` affine and `E` with quasi-coherent
cohomology. -/
theorem subsingleton_hom_singleExtensionByZeroUnit_of_isAffineOpen
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj E).IsQuasicoherent)
    (U : X.Opens) (hU : U ∈ X.affineOpens) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor X.Modules q).obj E)) :
    Subsingleton
      (Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnit X.zariskiRingedSite U ⟶ E⟦q⟧) :=
  Stacks.Sites.ExtensionByZero.subsingleton_hom_singleExtensionByZeroUnit_of_isZero
    X.zariskiRingedSite U E q
    (isZero_homology_derivedSectionsOverObject_of_isAffineOpen X E hE U hU q hq)

/-- **Morphisms from `(j_{U!} 𝒪_U)^{⊕t}` vanish over an affine open.**  If `H^q(E) = 0` then every
morphism from a direct sum of copies of `j_{U!} 𝒪_U` into `E⟦q⟧` is zero, for any index type,
the direct sum being given as a colimiting cofan `c`. -/
theorem subsingleton_hom_cofan_singleExtensionByZeroUnit_of_isAffineOpen
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj E).IsQuasicoherent)
    (U : X.Opens) (hU : U ∈ X.affineOpens) (q : ℤ)
    (hq : IsZero ((DerivedCategory.homologyFunctor X.Modules q).obj E)) {ι : Type*}
    (c : Cofan (fun _ : ι =>
      Stacks.Sites.ExtensionByZero.singleExtensionByZeroUnit X.zariskiRingedSite U))
    (hc : IsColimit c) :
    Subsingleton (c.pt ⟶ E⟦q⟧) :=
  Stacks.Sites.ExtensionByZero.subsingleton_hom_cofan_singleExtensionByZeroUnit_of_isZero
    X.zariskiRingedSite U c hc E q
    (isZero_homology_derivedSectionsOverObject_of_isAffineOpen X E hE U hU q hq)

end AlgebraicGeometry

end
