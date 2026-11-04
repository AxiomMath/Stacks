module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafPowersEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso

/-!
# The conormal algebra commutes with étale localization of the ambient space

Let `i : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `φ : U ⟶ X` be étale and let

```
Z_U --p--> Z
|i_U       |i
U  --φ-->  X
```

be the cartesian square it induces, so that `Z_U = U ×_X Z` and `i_U` is the base change of `i`.
The conormal algebra `𝒞_{Z/X,*}` of [Stacks, Tag 09RN] restricts to the conormal algebra of the
base change:

`𝒞_{Z/X,*}|_{Z_U} = p^*𝒞_{Z/X,*} ≅ 𝒞_{Z_U/U,*}`,

degree by degree. For `i` an immersion and `U` a scheme this is [Stacks, Tag 09RR].

The degree-`n` piece of `𝒞_{Z/X,*}` is `i^*(𝓘ⁿ)` for `𝓘` the kernel ideal sheaf of `i`, so the
identification is the composite of three steps. The square identifies `p^*i^*` with `i_U^*φ^*`;
along the étale morphism `φ` the inverse image of modules is étale restriction
([Stacks, Tag 03LW]); and the étale restriction of `𝓘ⁿ` is the `n`-th power of the kernel ideal
sheaf of `i_U` on the nose.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackSquareCompIso`: for a commutative square of algebraic
  spaces, the comparison `p^*i^* ≅ i_U^*φ^*` of the two inverse images around it.
* `AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso`: the canonical isomorphism
  `p^*(𝒞_{Z/X,*})_n ≅ (𝒞_{Z_U/U,*})_n` in each degree.

## Main results

* `AlgebraicGeometry.Space.etaleModulePullback_kernelIdealSheafZPow_eq`: the powers of the kernel
  ideal sheaf commute with étale localization of the target, as an equality of `𝒪_U`-modules.
* `AlgebraicGeometry.Space.conormalAlgebra_piece_one_etaleRestriction`: in degree one the two
  pieces being compared are the inverse images of the two kernel ideal sheaves.

## Implementation notes

`AlgebraicGeometry.Space.conormalAlgebra` is defined for an arbitrary morphism of algebraic
spaces, as the inverse image of the graded algebra of the powers of its kernel ideal sheaf, and
the statements below hold in that generality. Likewise `U` is an arbitrary algebraic space étale
over `X`: postcomposition with `φ` is a functor of small étale sites by [Stacks, Tag 03LP].

The comparison is degreewise: the three steps are comparisons of inverse-image functors of sheaves
of modules.

Every intermediate functor and object is named, with its type written out: a metavariable left in
a `CategoryTheory.Functor.comp` position drives the unifier through the choice principle hidden in
the pullback of modules.

## References

* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Z ZU : AlgebraicSpaces B S hS}

/-! ### The comparison of the two inverse images around a commutative square -/

/-- **The two inverse images around a commutative square agree.** For a commutative square
`i_U ≫ φ = p ≫ i` of algebraic spaces, the inverse image along `i` followed by the inverse image
along `p` is canonically isomorphic to the inverse image along `φ` followed by the inverse image
along `i_U`, through the composition comparisons `AlgebraicGeometry.Space.modulePullbackCompIso`
of [Stacks, Tag 03LU]. -/
noncomputable def modulePullbackSquareCompIso (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) :
    modulePullback B S hS i ⋙ modulePullback B S hS p ≅
      modulePullback B S hS φ ⋙ modulePullback B S hS iU :=
  modulePullbackCompIso B S hS p i ≪≫
    eqToIso (congrArg (fun k : ZU ⟶ X ↦ modulePullback B S hS k) hsq.symm) ≪≫
    (modulePullbackCompIso B S hS iU φ).symm

/-! ### The powers of the kernel ideal sheaf of a base change -/

/-- **The powers of the kernel ideal sheaf commute with étale localization of the target.** For a
cartesian square

```
Z_U --p--> Z
|i_U       |i
U  --φ-->  X
```

of algebraic spaces with `φ` étale, the étale restriction along `φ` of the `n`-th power of the
kernel ideal sheaf of `i` is the `n`-th power of the kernel ideal sheaf of `i_U`. -/
theorem etaleModulePullback_kernelIdealSheafZPow_eq (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (etaleModulePullback.{u, u} B S hS φ hφ).obj
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules =
      (kernelIdealSheafZPow B S hS iU n).toSheafOfModules :=
  etaleModulePullback_idealSheafZPow_eq B S hS φ hφ (kernelIdealSheaf B S hS i)
    (kernelIdealSheaf B S hS iU)
    (fun W ↦ kernelIdealSheaf_baseChange_obj B S hS p iU i φ sq hφ W) n

/-! ### The conormal algebra of a base change -/

/-- Let `i : Z ⟶ X` be a morphism of algebraic spaces, let `φ : U ⟶ X` be étale and let
`Z_U = U ×_X Z` with projections `p : Z_U ⟶ Z` and `i_U : Z_U ⟶ U`. Then the inverse image along
`p` of the degree-`n` piece of the conormal algebra of `i` is the degree-`n` piece of the conormal
algebra of `i_U`:

`(𝒞_{Z/X,*}|_{Z_U})_n = p^*(𝒞_{Z/X,*})_n ≅ (𝒞_{Z_U/U,*})_n`.

The isomorphism is the square comparison `p^*i^* ≅ i_U^*φ^*` of
`AlgebraicGeometry.Space.modulePullbackSquareCompIso`, then the inverse image along `i_U` of the
identification of `φ^*` with étale restriction of [Stacks Project, Tag 03LW], then the equality
`𝓘ⁿ|_U = 𝓘_Uⁿ` of the powers of the kernel ideal sheaves. -/
@[stacks 09RR "the conormal algebra of an etale localisation, in each degree"]
noncomputable def conormalAlgebraEtaleRestrictionPieceIso (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (sq : IsPullback p iU i φ) (hφ : IsEtale B S hS φ.hom) (n : ℤ) :
    (modulePullback B S hS p).obj ((conormalAlgebra B S hS i).piece n) ≅
      (conormalAlgebra B S hS iU).piece n :=
  let 𝓘 : Modules.{u, u} B S hS X.1 X.2 :=
    (kernelIdealSheafZPow B S hS i n).toSheafOfModules
  let e₂ : (modulePullback B S hS p).obj ((modulePullback B S hS i).obj 𝓘) ≅
      (modulePullback B S hS iU).obj ((modulePullback B S hS φ).obj 𝓘) :=
    (modulePullbackSquareCompIso B S hS p iU i φ sq.w.symm).app 𝓘
  let e₃ : (modulePullback B S hS iU).obj ((modulePullback B S hS φ).obj 𝓘) ≅
      (modulePullback B S hS iU).obj ((etaleModulePullback.{u, u} B S hS φ hφ).obj 𝓘) :=
    (modulePullback B S hS iU).mapIso
      ((modulePullbackIsoEtaleModulePullback B S hS φ hφ).app 𝓘)
  let e₄ : (modulePullback B S hS iU).obj ((etaleModulePullback.{u, u} B S hS φ hφ).obj 𝓘) ≅
      (modulePullback B S hS iU).obj
        (kernelIdealSheafZPow B S hS iU n).toSheafOfModules :=
    (modulePullback B S hS iU).mapIso
      (eqToIso (etaleModulePullback_kernelIdealSheafZPow_eq B S hS p iU i φ sq hφ n))
  e₂ ≪≫ e₃ ≪≫ e₄

/-- The degree-one pieces of the conormal algebras of `i : Z ⟶ X` and of `i_U : Z_U ⟶ U` are the
inverse images of their kernel ideal sheaves. -/
theorem conormalAlgebra_piece_one_etaleRestriction (iU : ZU ⟶ U) (i : Z ⟶ X) :
    (conormalAlgebra B S hS i).piece 1 =
        (modulePullback B S hS i).obj (kernelIdealSheaf B S hS i).toSheafOfModules ∧
      (conormalAlgebra B S hS iU).piece 1 =
        (modulePullback B S hS iU).obj (kernelIdealSheaf B S hS iU).toSheafOfModules :=
  ⟨conormalAlgebra_piece_one B S hS i, conormalAlgebra_piece_one B S hS iU⟩

end AlgebraicGeometry.Space

end
