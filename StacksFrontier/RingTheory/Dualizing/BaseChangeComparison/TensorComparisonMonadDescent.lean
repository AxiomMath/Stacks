module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareActionUnit
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionTensorComparison
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonReduction

/-!
# The tensor-comparison obligation has to be checked only at restrictions from `D(A)`

`Dualizing.TensorComparisonCompatibility` — the one remaining input of
`Dualizing.KFlatAlgebraActionEq`, and with it of [stacks 0E2A] — is an equation read at a variable
object `X` of `D(R)`.  `Dualizing.tensorComparisonCompatibility_of_kFlat` reduces the objects it
has to be read at to the classes of K-flat complexes of `R`-modules.  This file reduces them
differently, and the two reductions compose:

**the obligation at `X` follows from the obligation at `(Ff X)|_R`**, unconditionally.

`(Ff X)|_R` is the value at `X` of the monad of derived extension and restriction of scalars along
`R → A`, which the projection formula `Dualizing.derivedExtendRestrictScalarsTensorIso` identifies
with `X ⊗ᴸ_R A`.  So it suffices to prove the keystone at the restriction to `R` of an object of
`D(A)` — where, unlike at a general object of `D(R)`, the comparison
`Dualizing.restrictionBaseChangeIsoGeneral` of [stacks 0661] identifies the base change
`baseChangeR ((Ff X)|_R)` with a restriction `(baseChangeA (Ff X))|_{R'}`, and both the `A`-action
and the `A ⊗_R R'`-action used in the proof of [stacks 0E2A] are available on the nose.

All the content is in
`StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareActionUnit`, where it is proved for an
arbitrary square of adjunctions with projection formulas on its horizontal edges: `Tens'` applied
to `Lg` of the unit is a split monomorphism, retracted by
`Stacks.CategoryTheory.BaseChange.unitRetraction`, and the comparison across the square at `X`
factors through its own value at `Rf (Lf X)` and that retraction.  Nothing about rings, modules or
derived categories enters, and nothing is assumed invertible.

The descent is **not** reversible: `Tens'` applied to `Lg` of the unit is split monic but not
invertible, so the obligation at the monad is strictly the stronger statement.  That is what makes
this a reduction rather than a restatement.

**What is not done here.** `Dualizing.TensorComparisonCompatibility` is not proved and no tag
loses its conditional caveat.  What changes is the class of objects the obligation has to be
checked at: the classes of K-flat complexes of `R`-modules by
`Dualizing.tensorComparisonCompatibility_of_kFlat`, and now the restrictions of objects of `D(A)`,
which may be combined — `Dualizing.tensorComparisonCompatibility_of_kFlat_restrict_extend` asks
for it only at `(Ff (Q K))|_R` for `K` a K-flat complex of `R`-modules, an object whose class is
that of the complex `(A ⊗_R K)|_R` of `R`-modules.

## Main definitions

* `Dualizing.tensorDerivedBaseChangeAlgebra` — tensoring with the base change of the algebra, as a
  transformation of endofunctors of `D(R')`.  Its component at `Y` is the right-hand side of the
  obligation at an object with `baseChangeR X` replaced by `Y`; the obligation's right-hand side
  is therefore a component of a natural transformation, which is what the descent consumes.

## Main results

* `Dualizing.tensorComparisonCompatibility_of_restrict_extend` — **the obligation at `X` from the
  obligation at `(Ff X)|_R`.**
* `Dualizing.tensorComparisonCompatibility_of_kFlat_restrict_extend` — the two reductions
  composed: the obligation at every object of `D(R)` from the obligation at `(Ff (Q K))|_R` for
  `K` a K-flat complex of `R`-modules.

## Implementation notes

The instantiation is an `exact` against the abstract statement with no rewriting: the four
projection-formula and square isomorphisms are the ones `Dualizing.TensorComparisonCompatibility`
is written with, the mate condition is `Dualizing.derivedBaseChangeSquareIso_mate_eq'` — which is
unconditional — and the two transformations are
`Dualizing.tensorDerivedBaseChangeAlgebra` and `Dualizing.derivedTensorBaseChangeSquare`, whose
components are the obligation's two sides definitionally. `Dualizing.derivedTensorBaseChangeSquare`
supplies the naturality of the lax monoidal structure map in its first variable, which is the only
property of it the descent uses.

`Dualizing.TensorComparisonCompatibility` is a `def` whose body is the equation, so the idiom
`replace h : _ = _ := h` and `show _ = _` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonReduction` moves between
the two rather than unfolding it.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

namespace Dualizing

universe uR uA uRp v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

include hA hR in
/-- **Tensoring with the base change of the algebra, as a transformation of endofunctors of
`D(R')`.**  The bifunctor of [stacks 0A63] over `R'`, curried and flipped, applied to
`Dualizing.derivedBaseChangeAlgebraIso`: its component at `Y` is the tensoring of the identity of
`Y` with that isomorphism, which at `Y = baseChangeR X` is the right-hand side of
`Dualizing.TensorComparisonCompatibility`.

The obligation's right-hand side is therefore a component of a natural transformation of the two
endofunctors `- ⊗ᴸ_{R'} baseChangeR A[0]` and `- ⊗ᴸ_{R'} A'[0]`, which is what
`Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_of_monad` consumes; the target is
the projection formula's target over `R' → A ⊗_R R'`, which is that second endofunctor by
definition. -/
def tensorDerivedBaseChangeAlgebra :
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
        max v uR uA uRp + 1} R').tensorAt
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
      derivedExtendRestrictScalarsTensorFunctor.{uRp, max uA uRp, max v uR}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom :=
  ((Functor.curry.obj (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').tensor).flip).map
    (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA comparisonA hA).hom

include hf hA hR hi in
/-- **The obligation at `X` follows from the obligation at `(Ff X)|_R`.**  This is
`Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_of_monad` at the base-change
square of the Tor-independent pair `R → A`, `R → R'`: the two adjunctions are derived extension of
scalars along `R → A` and along `R' → A ⊗_R R'`, the two projection formulas are the two instances
of `Dualizing.derivedExtendRestrictScalarsTensorIso`, the comparison of the two composites around
the square is `Dualizing.derivedBaseChangeSquareIso`, the mate is
`Dualizing.restrictionBaseChangeIsoGeneral` by `Dualizing.derivedBaseChangeSquareIso_mate_eq'`, the
lax structure map is `Dualizing.derivedTensorBaseChangeSquare` and the transformation of the two
tensor endofunctors is `Dualizing.tensorDerivedBaseChangeAlgebra`.

So the keystone has to be proved only at objects restricted from `D(A)`.  Nothing is assumed:
neither K-flatness of a representative of `X`, nor invertibility of anything beyond the four
isomorphisms the obligation is already written with. -/
theorem tensorComparisonCompatibility_of_restrict_extend
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (h : TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai
      ((ModuleCat.restrictScalars.{max v uR uA uRp}
        (algebraMap R A)).mapDerivedCategory.obj (Ff.obj X))) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X := by
  replace h : _ = _ := h
  change _ = _
  exact Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_of_monad
    (derivedExtensionScalarsAdjunction.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtensionScalarsAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
      Fi alphai)
    (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA comparisonA hA)
    (derivedBaseChangeSquareIso_mate_eq' hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai)
    (tensorDerivedBaseChangeAlgebra hTor baseChangeR comparisonR baseChangeA comparisonA)
    (derivedTensorBaseChangeSquare.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
      (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) X h

include hf hA hR hi in
/-- **The two reductions of the obligation's object variable, composed.**  The obligation holds at
every object of `D(R)` as soon as it holds at `(Ff (Q K))|_R` for every K-flat complex `K` of
`R`-modules.

`Dualizing.tensorComparisonCompatibility_of_kFlat` restricts the objects to the classes of K-flat
complexes, and `Dualizing.tensorComparisonCompatibility_of_restrict_extend` moves each of those
onto the monad.  The resulting object is the class of `(A ⊗_R K)|_R`: for a K-flat `K` the
comparison `alphaf` is invertible at `K` (`Dualizing.isIso_alphaf_app_of_kFlat`), so `Ff (Q K)` is
the class of the termwise extension of scalars, and restriction of scalars commutes with the
localization. -/
theorem tensorComparisonCompatibility_of_kFlat_restrict_extend
    (h : ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
        Ff alphaf Fi alphai
        ((ModuleCat.restrictScalars.{max v uR uA uRp}
          (algebraMap R A)).mapDerivedCategory.obj (Ff.obj (DerivedCategory.Q.obj K))))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X :=
  tensorComparisonCompatibility_of_kFlat hTor baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai
    (fun K hK => tensorComparisonCompatibility_of_restrict_extend hTor baseChangeR comparisonR
      baseChangeA comparisonA Ff alphaf Fi alphai (DerivedCategory.Q.obj K) (h K hK)) X

end Dualizing

end
