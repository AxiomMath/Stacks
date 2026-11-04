module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# Restriction to an open on which a derived module is concentrated in one degree

Let `E` be an object of the derived category of sheaves of modules on a scheme `X` and let
`f : U ⟶ X` be an open immersion. If the cohomology sheaves of `E` vanish on `U` in every degree
other than `i`, then the restriction of `E` to `U` is its own degree-`i` cohomology sheaf placed in
degree `i`.

This is the half of [stacks 0BDK] that concerns the shape of a derived module on the locus where
it is concentrated in one degree, with the locus given as an open subscheme and the concentration
given as the vanishing of the restricted cohomology sheaves.

## Main results

* `AlgebraicGeometry.Scheme.Modules.homologyFunctor_mapDerivedCategory_restrictFunctor_iso`: the
  cohomology sheaves of the restriction of `E` to `U` are the restrictions of the cohomology
  sheaves of `E`.
* `AlgebraicGeometry.Scheme.Modules.nonempty_iso_singleFunctor_homologyFunctor_restrict`: on such
  an open, the restriction of `E` is its degree-`i` cohomology sheaf placed in degree `i`.

## References

* [The Stacks Project, Lemma 36.31.3 (0BDK)](https://stacks.math.columbia.edu/tag/0BDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The cohomology sheaves of the restriction of a derived module to an open subscheme are the
restrictions of its cohomology sheaves. -/
public def homologyFunctor_mapDerivedCategory_restrictFunctor_iso (j : ℤ) :
    (restrictFunctor f).mapDerivedCategory ⋙ DerivedCategory.homologyFunctor X.Modules j ≅
      DerivedCategory.homologyFunctor Y.Modules j ⋙ restrictFunctor f :=
  (restrictFunctor f).mapDerivedCategoryHomologyFunctorIso j

/-- Let `E` be an object of the derived category of sheaves of modules on a scheme `Y`, let
`f : X ⟶ Y` be an open immersion and let `i` be an integer. If every cohomology sheaf of `E` in a
degree other than `i` restricts to zero on `X`, then the restriction of `E` to `X` is isomorphic to
its degree-`i` cohomology sheaf placed in degree `i`. -/
public theorem nonempty_iso_singleFunctor_homologyFunctor_restrict
    (E : DerivedCategory Y.Modules) (i : ℤ)
    (hE : ∀ j : ℤ, j ≠ i →
      IsZero ((restrictFunctor f).obj ((DerivedCategory.homologyFunctor Y.Modules j).obj E))) :
    Nonempty ((restrictFunctor f).mapDerivedCategory.obj E ≅
      (DerivedCategory.singleFunctor X.Modules i).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj
          ((restrictFunctor f).mapDerivedCategory.obj E))) :=
  DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero _ i fun j hj ↦
    IsZero.of_iso (hE j hj) ((homologyFunctor_mapDerivedCategory_restrictFunctor_iso f j).app E)

end AlgebraicGeometry.Scheme.Modules

end
