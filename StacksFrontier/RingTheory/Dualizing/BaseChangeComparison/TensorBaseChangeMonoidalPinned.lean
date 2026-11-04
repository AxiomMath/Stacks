module

public import StacksFrontier.Homology.Tor.BaseChangeTensorMonoidalIso
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeCanonicalValue

/-!
# The [stacks 068I] candidate at a K-flat pair, with its chain isomorphism pinned

`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` evaluates the [stacks 068I] candidate at a pair of
localizations of K-flat complexes, but only up to an *existentially quantified* chain isomorphism
`e` of total complexes, constrained by `CochainComplex.DerivedTensor.IsTensorBaseChangeIso`.  A
consumer that has to compare the value against a named comparison -- the monoidality isomorphism
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of [stacks 068I], which is what the
[stacks 0E1W] side of the keystone of Chapter 47 is written in -- cannot use the value in that
shape: eliminating the existential leaves a chain isomorphism about which only the summand
formula is known.

`CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom` removes
that obstruction, the summand formula determining the comparison; but it is available only where
the two rings and their modules share one universe, because that is the generality in which
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` is defined.  This file performs the
substitution there, so that at equal universes the value of the [stacks 068I] candidate carries
the monoidality isomorphism itself and no existential.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.  What this file changes is that the
chain isomorphism in the value of the candidate is a named one at equal universes.

## Main results

* `Dualizing.tensorBaseChangeMor_comp_eq_monoidalIso` -- the value of the [stacks 068I] candidate
  at a pair of localizations of K-flat complexes over two rings in one universe, with the chain
  isomorphism of total complexes pinned to
  `CochainComplex.ExtendScalars.extendScalarsMonoidalIso`.
* `Dualizing.tensorBaseChangeMor_comp_eq_monoidalIso_of_kFlat` -- the same with the K-flatness of
  the degreewise base change discharged from [stacks 06Y1], so the value carries no hypothesis
  beyond the K-flatness of the two complexes.
* `Dualizing.tensorBaseChangeMor_comp_eq_of_isTensorBaseChangeIso` -- the value at **independent**
  ring universes, against any isomorphism of total complexes satisfying the summand formula.  The
  monoidality isomorphism is defined only over two rings in one universe, so the pinning above
  does not reach the keystone, whose [stacks 068I] morphism is read at `R -> R'` with
  `A (x)_R R'` in a third universe; there the standard isomorphism arrives from the scalar lift,
  by `CochainComplex.DerivedTensor.isTensorBaseChangeIso_transport`, and this is the form that
  takes it.

## Implementation notes

The K-flatness of the degreewise base change of the second complex is taken as a hypothesis
rather than produced: `CochainComplex.DerivedTensor.IsKFlat` is a proposition, so the equation
asserted at the hypothesis given by the caller is the same type as the equation asserted at the
one `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` supplies, and no transport is needed.

No `@[stacks]` attribute is placed here: the identification of the [stacks 068I] morphism with
the lax monoidal structure map of derived base change is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars
open CochainComplex.ExtendScalars

attribute [local instance] HasDerivedCategory.standard

universe u uR uA uM

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
  (D : TotalDerivedExtensionScalars.{u, u, u, u + 1, u + 1} f)
  (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]

include hF in
/-- **The [stacks 068I] candidate at a K-flat pair, with the monoidality isomorphism itself.**

`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` with its existentially quantified chain isomorphism
replaced, by
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom`, by
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`: the summand formula the existential
carries determines the comparison, and the monoidality isomorphism satisfies it.

So over two rings in one universe the [stacks 068I] candidate `μ'`, followed by the two factors
identifying `F (Q K ⊗ᴸ_R Q L)` with the class of the degreewise base change of the total tensor
complex, is the [stacks 0A63] tensor of two components of `comparison`, the K-flat comparison of
[stacks 0A63] over `A`, and the localization of the monoidality isomorphism of degreewise
extension of scalars.

This is the shape in which the [stacks 0E1W] side of the keystone meets the candidate: the
chain-level map of [stacks 0E1W] is written in `extendScalarsMonoidalIso` by
`Stacks.DerivedHom.BaseChangeIso.uncurry_homComplexChangeOfRingsMap`, so with the existential
gone the two sides speak one vocabulary. -/
theorem tensorBaseChangeMor_comp_eq_monoidalIso
    (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsKFlat.{u, u} K) (hL : IsKFlat.{u, u} L)
    (hFL : IsKFlat.{u, u} ((extensionOfScalarsCochain.{u, u, u} f).obj L)) :
    tensorBaseChangeMor.{u, u, u} f F comparison D (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) ≫
        F.map (derivedTensor_comparison.{u, u} R K L hL).hom ≫
        comparison.app (tensorComplex.{u, u} K L) =
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.map
          ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
              ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
              (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{u, u, u} f).obj K),
                DerivedCategory.Q.obj ((extensionOfScalarsCochain.{u, u, u} f).obj L)))) ≫
        (derivedTensor_comparison.{u, u} A
            ((extensionOfScalarsCochain.{u, u, u} f).obj K)
            ((extensionOfScalarsCochain.{u, u, u} f).obj L) hFL).hom ≫
        DerivedCategory.Q.map (extendScalarsMonoidalIso f K L).hom := by
  obtain ⟨hFL', e, he, hval⟩ :=
    tensorBaseChangeMor_comp_eq_q_obj.{u, u, u} f D F comparison K L hK hL
  rw [IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom f K L he] at hval
  exact hval

include hF in
/-- **The same with the K-flatness of the base change discharged.**

`Dualizing.tensorBaseChangeMor_comp_eq_monoidalIso` at the K-flatness of the degreewise base
change supplied by [stacks 06Y1],
`CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`, so that the value of the
[stacks 068I] candidate at a pair of localizations of K-flat complexes over two rings in one
universe carries no hypothesis beyond the K-flatness of the two complexes. -/
theorem tensorBaseChangeMor_comp_eq_monoidalIso_of_kFlat
    (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsKFlat.{u, u} K) (hL : IsKFlat.{u, u} L) :
    tensorBaseChangeMor.{u, u, u} f F comparison D (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) ≫
        F.map (derivedTensor_comparison.{u, u} R K L hL).hom ≫
        comparison.app (tensorComplex.{u, u} K L) =
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} A).tensor.map
          ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
              ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                DerivedCategory (ModuleCat.{u} A) × DerivedCategory (ModuleCat.{u} A)) ⟶
              (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{u, u, u} f).obj K),
                DerivedCategory.Q.obj ((extensionOfScalarsCochain.{u, u, u} f).obj L)))) ≫
        (derivedTensor_comparison.{u, u} A
            ((extensionOfScalarsCochain.{u, u, u} f).obj K)
            ((extensionOfScalarsCochain.{u, u, u} f).obj L)
            (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f L hL)).hom ≫
        DerivedCategory.Q.map (extendScalarsMonoidalIso f K L).hom :=
  tensorBaseChangeMor_comp_eq_monoidalIso.{u} f D F comparison K L hK hL
    (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f L hL)

section IndependentUniverses

variable {R' : Type uR} {A' : Type uA} [CommRing R'] [CommRing A'] (f : R' →+* A')
  (D : TotalDerivedExtensionScalars.{uR, max uR uA uM, uA} f)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R') ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A'))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R') (ComplexShape.up ℤ))]

/-- **The [stacks 068I] candidate at a K-flat pair, at independent ring universes, against any
standard chain isomorphism.**  `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` evaluates the
candidate only up to an existentially quantified isomorphism of total complexes; this states the
same value for *every* isomorphism satisfying the summand formula
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso`, the existential being eliminated by the
uniqueness `CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq`, which holds at
independent universes for the two rings.

`Dualizing.tensorBaseChangeMor_comp_eq_monoidalIso` pins the same existential to
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`, but only over two rings in **one**
universe, because that is the only generality in which the monoidality isomorphism is defined.
The keystone `Dualizing.TensorComparisonCompatibility` carries the candidate at `R → R'` with
`A ⊗_R R'` in a third universe, where the equal-universe form does not apply; what is available
there is a standard isomorphism carried across the scalar lift by
`CochainComplex.DerivedTensor.isTensorBaseChangeIso_transport`, and this is the form that
accepts it.

The K-flatness of the degreewise base change is a hypothesis rather than a product, for the
reason recorded above: `CochainComplex.DerivedTensor.IsKFlat` is a proposition, so the equation
asserted at the caller's proof is the same type as the one asserted at the proof the existential
supplies. -/
theorem tensorBaseChangeMor_comp_eq_of_isTensorBaseChangeIso
    (K L : CochainComplex (ModuleCat.{max uR uA uM} R') ℤ)
    (hK : IsKFlat.{uR, max uR uA uM} K) (hL : IsKFlat.{uR, max uR uA uM} L)
    (hFL : IsKFlat.{uA, max uR uA uM}
      ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L))
    {e : tensorComplex.{uA, max uR uA uM}
        ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj
        (tensorComplex.{uR, max uR uA uM} K L)}
    (he : IsTensorBaseChangeIso.{uR, uA, max uR uA uM} f K L e) :
    tensorBaseChangeMor.{uR, uA, uM} f F comparison D (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) ≫
        F.map (derivedTensor_comparison.{uR, max uR uA uM} R' K L hL).hom ≫
        comparison.app (tensorComplex.{uR, max uR uA uM} K L) =
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uA, max uR uA uM,
            max uR uA uM + 1} A').tensor.map
          ((CategoryTheory.Prod.mkHom (comparison.app K) (comparison.app L) :
              ((F.obj (DerivedCategory.Q.obj K), F.obj (DerivedCategory.Q.obj L)) :
                DerivedCategory (ModuleCat.{max uR uA uM} A') ×
                  DerivedCategory (ModuleCat.{max uR uA uM} A')) ⟶
              (DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                  max uR uA uM} f).obj K),
                DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA,
                  max uR uA uM} f).obj L)))) ≫
        (derivedTensor_comparison.{uA, max uR uA uM} A'
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj K)
            ((extensionOfScalarsCochain.{uR, uA, max uR uA uM} f).obj L) hFL).hom ≫
        DerivedCategory.Q.map e.hom := by
  obtain ⟨hFL', e', he', hval⟩ :=
    tensorBaseChangeMor_comp_eq_q_obj.{uR, uA, uM} f D F comparison K L hK hL
  rw [IsTensorBaseChangeIso.hom_eq.{uR, uA, max uR uA uM} f K L he' he] at hval
  exact hval

end IndependentUniverses

end Dualizing

end
