module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareLift

/-!
# The projection formula at the two edges of the tensor-product square

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareLift` proves the
projection formula at the two ring maps of a pushout square

```
S --g--> T
|        |
p        w
v        v
S' --h-> T'
```

at four independent ring universes, as
`Dualizing.derivedExtendRestrictScalarsTensorIso_square`.  The keystone
`Dualizing.TensorComparisonCompatibility` reads the projection formula at the square

```
R ---→ A
|      |
v      v
R' --→ A ⊗_R R'
```

and this file carries the pairing to it.

The square is a pushout square outright: `MilnorPatching.tensorPushout` says so of
`R → A`, `R → R'`, `A → A ⊗_R R'`, `R' → A ⊗_R R'`, with no Tor independence and no flatness,
and the top edge `A → A ⊗_R R'` is `Algebra.TensorProduct.includeLeftRingHom` on the nose.

**The universes are the reason this file exists.**
`Dualizing.derivedExtendRestrictScalarsTensorIso` carries a module-universe parameter, and the
keystone is stated with the two components

`Dualizing.derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}` at `R → A` and
`Dualizing.derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}` at
`R' → A ⊗_R R'`,

whereas `Dualizing.derivedExtendRestrictScalarsTensorIso_square`, whose four rings sit in the
four universes `uS`, `uT`, `uSp`, `uTp` with one module universe `max v uS uT uSp uTp`, states
them at `max v uSp uTp` and `max v uS uT`.  Substituting the square's rings gives
`max v uA uRp` and `max v uR uA`, and neither can be made to read `max v uRp` or `max v uR`:
`uT` is `uA`, and no instantiation removes it.  The two spellings of one component have the same
type and are **not** definitionally equal — the transport data of the scalar lift is `no_expose`,
so nothing unfolds — and the keystone's spelling is the one the eleven objective tags depend on.

What is carried across is therefore not the statement of
`Dualizing.derivedExtendRestrictScalarsTensorIso_square` but its proof: every input of
`Stacks.CategoryTheory.comp_eq_of_chain_pairing` that mentions a projection formula is available
at the keystone's spelling —
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing` at
`.{max v uRp, uR, uA}` for the near edge, and
`Dualizing.liftSquareRetraction_comp` with `Dualizing.liftSquarePrefixTransported_comp` at
`.{max v uR, uRp, max uA uRp}` for the far edge — and the remaining inputs, which concern only
the lifted square, are indifferent to the split.

## Main definitions

* `Dualizing.tensorSquareConjugateTail`, `Dualizing.tensorSquareConjugate`,
  `Dualizing.tensorSquareConjugatedFormula` — the right-hand side of the pairing at the
  tensor-product square, in the keystone's spelling.  They mirror
  `Dualizing.liftSquareConjugateTail`, `Dualizing.liftSquareConjugate` and
  `Dualizing.liftSquareConjugatedFormula`, nested one inside the next for the reason recorded
  there: the per-declaration heartbeat budget does not hold the conjugation at once, and each is
  right-associated and ends with the next, so the nesting regroups nothing.

## Main results

* `Dualizing.kFlat_extendScalars_algebraMapR'` — [stacks 06Y1] at `R → R'` in the spelling the
  far edge of the square asks for.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_square_tensorProduct` — **the pairing at the
  tensor-product square**, with both projection formulas in the keystone's spelling.

## Implementation notes

The square's commutation `A → A ⊗_R R' ← R'` is `Algebra.TensorProduct.tmul_one_eq_one_tmul`,
and `MilnorPatching.IsPushoutSquare` does not use its commutation argument, so the proof
`MilnorPatching.tensorPushout` carries one proof of it supplies the other.

**What is not done here.**  `Dualizing.TensorComparisonCompatibility` is not proved and no tag
loses its conditional caveat.  What this file provides is the pairing of the square stated at
the spelling the keystone reads it in, which matters: using
`Dualizing.derivedExtendRestrictScalarsTensorIso_square` at this square produces an equation
about a *different* term of the same type, and the gap is not definitional.

The hypothesis `h` of `Dualizing.tensorComparisonCompatibility_of_kFlat_tail` reads, at a K-flat
resolution `b : A[0] ≅ Q P` and a K-flat `K`,

`Θ.inv (Ff (Q K)) ≫ Res_h(γ.hom (Q K)) ≫ pf'.hom (Bp (Q K))
  = Bp(pf.hom (Q K)) ≫ Bp(1 ⊗ b.hom) ≫ μ'⁻¹ ≫ (1 ⊗ (Bp b.inv ≫ alg))`,

and the theorem of this file reads

`Bp(pf.hom (Q K)) ≫ Bp(tail) ≫ βp = tensorSquareConjugatedFormula`,

whose left-hand side begins with the right-hand side's first factor.  So `h` follows from a
single morphism `u` out of the formula's target together with two equations:

* the **tail residue** `Bp(tail) ≫ βp ≫ u = Bp(1 ⊗ b.hom) ≫ μ'⁻¹ ≫ (1 ⊗ (Bp b.inv ≫ alg))`,
  which carries the transport tail of the scalar lift at `R → A` and the comparison of the model
  against the lifted edge onto the [stacks 068I] morphism, the resolution factor and the base
  change of the algebra.  Its ingredients are proved:
  `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` for the [stacks 068I] morphism at independent
  ring universes, `CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq` to pin its
  existential chain isomorphism, `CochainComplex.DerivedTensor.isTensorBaseChangeIso_transport`
  to carry that isomorphism to `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` over the
  lifted edge — which is the factor `Dualizing.tensorSquareConjugateTail` ends with — and
  `Dualizing.derivedBaseChangeAlgebraIso_hom_eq_single` with
  `Dualizing.pushoutAlgebraIsoComplex_hom_eq_single` for the algebra.
* the **square residue** `tensorSquareConjugatedFormula ≫ u = Θ.inv (Ff (Q K)) ≫ Res_h(γ.hom (Q K))
  ≫ pf'.hom (Bp (Q K))`, which identifies the two *derived* comparisons of the square with the
  *chain-level* comparisons of the lifted square that
  `Dualizing.tensorSquareConjugate` carries.  Here
  `Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj` with
  `Dualizing.pushoutBaseChange_inv_eq_derivedBaseChangeComparison` evaluates `Θ.inv` against the
  pushout comparison, `Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj` evaluates `γ.hom`,
  and `Dualizing.isIso_comparisonR_app_of_kFlat` moves `pf'.hom` between `Bp (Q K)` and
  `Q (R' ⊗_R K)`, which is where the two sides read it.  What has no available input is the
  transport of the two *derived* square comparisons across the scalar lift: the formula reads
  them at the lifted square and through `Dualizing.liftSquareRetraction`, and nothing relates
  that reading to the models' own comparisons.

No `@[stacks]` attribute is placed here: the obligation of
`Dualizing.TensorComparisonCompatibility` is still open, so nothing in this file covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor
open StacksDraft.DerivedHom
open scoped TensorProduct

namespace Dualizing

universe uR uA uRp v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

section TensorProductSquare

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- **The tensor-product square commutes.**  Both composites `R → A → A ⊗_R R'` and
`R → R' → A ⊗_R R'` are the structure map of `A ⊗_R R'` as an `R`-algebra: on `r` the first is
`r ⊗ₜ 1` and the second `1 ⊗ₜ r`. -/
theorem tensorProductSquareComm :
    (Algebra.TensorProduct.includeLeftRingHom :
          A →+* TensorProduct R A R').comp (algebraMap R A) =
      (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom.comp (algebraMap R R') :=
  RingHom.ext (fun r => Algebra.TensorProduct.tmul_one_eq_one_tmul r)

/-- **[Stacks 06Y1] at `R → R'`, in the spelling the far edge of the square asks for.**  The
degreewise extension of scalars along `R → R'` of a K-flat complex of `R`-modules is K-flat, with
the module universe written `max v uR uA uRp` rather than `max v uR uA`.  The two are the same
universe, and `Dualizing.kFlat_extendScalars_algebraMapR` states the other one;
`CochainComplex.KFlat` carries the module universe as a parameter of its own, so the two
statements are not interchangeable. -/
theorem kFlat_extendScalars_algebraMapR'
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA uRp} K) :
    CochainComplex.KFlat.{uRp, max v uR uA uRp}
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uR, uRp, max v uA uRp}
    (algebraMap R R') K hK

variable
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

/-- **The far edge of the tensor-product square, followed by the two comparisons after it.**
`Dualizing.liftSquareConjugateTail` at the tensor-product square, with the projection formula at
`R' → A ⊗_R R'` in the keystone's spelling `.{uRp, max uA uRp, max v uR}`: the retraction of the
transport prefix, the component of the independent-universe projection formula at the class of
`R' ⊗_R K`, the transported transport tail, the lifted algebra in the tensor factor, and the
monoidality of degreewise extension of scalars along the lifted left edge. -/
def tensorSquareConjugateTail
    [Fi.IsLeftDerivedFunctor alphai
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hKp : CochainComplex.KFlat.{uRp, max v uR uA uRp}
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  let ESp := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uRp,
    max v uR uA uRp} R'
  let g' : ULift.{max v uR uA uRp} R →+* ULift.{max v uR uA uRp} A :=
    (ULift.ringEquiv.symm.toRingHom.comp (algebraMap R A)).comp ULift.ringEquiv.toRingHom
  let p' : ULift.{max v uR uA uRp} R →+* ULift.{max v uR uA uRp} R' :=
    (ULift.ringEquiv.symm.toRingHom.comp (algebraMap R R')).comp ULift.ringEquiv.toRingHom
  let w' : ULift.{max v uR uA uRp} A →+* ULift.{max v uR uA uRp} (TensorProduct R A R') :=
    (ULift.ringEquiv.symm.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom :
        A →+* TensorProduct R A R')).comp ULift.ringEquiv.toRingHom
  let h' : ULift.{max v uR uA uRp} R' →+* ULift.{max v uR uA uRp} (TensorProduct R A R') :=
    (ULift.ringEquiv.symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).comp ULift.ringEquiv.toRingHom
  let comm' := uliftSquareComm.{v, uR, uA, uRp, max uA uRp} (algebraMap R A) (algebraMap R R')
    (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A R')
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
    tensorProductSquareComm
  let hp' := uliftIsPushoutSquare.{v, uR, uA, uRp, max uA uRp} (algebraMap R A)
    (algebraMap R R')
    (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A R')
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
    tensorProductSquareComm MilnorPatching.tensorPushout comm'
  let Kt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uR uA uRp} R ≃+* R).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let Ep' := (ModuleCat.extendScalars.{max v uR uA uRp, max v uR uA uRp,
    max v uR uA uRp} p').mapHomologicalComplex (ComplexShape.up ℤ)
  let L := ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
    (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let Bcg := (CochainComplex.singleFunctor
      (ModuleCat.{max v uR uA uRp} (ULift.{max v uR uA uRp} R)) 0).obj
    ((ModuleCat.restrictScalars g').obj
      (ModuleCat.of (ULift.{max v uR uA uRp} A) (ULift.{max v uR uA uRp} A)))
  let X := Ep'.obj Kt
  let θ := uliftExtendScalarsCommUpApp.{max v uA, uR, uRp} (algebraMap R R') K
  liftSquareRetraction.{max v uR, uRp, max uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai L hKp X θ ≫
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
        (DerivedCategory.Q.obj L) ≫
      liftSquareTailTransported.{max v uR, uRp, max uA uRp}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom L hKp X θ ≫
        (DerivedCategory.Q ⋙ ESp.inverse).map
          ((pushoutAlgebraIsoComplex g' p' w' h' comm' hp').inv ▷ X) ≫
          (DerivedCategory.Q ⋙ ESp.inverse).map
            (CochainComplex.ExtendScalars.extendScalarsMonoidalIso p' Bcg Kt).hom

/-- **The projection formula at `R' → A ⊗_R R'`, conjugated by the four comparisons of the lifted
tensor-product square.**  `Dualizing.liftSquareConjugate` at the tensor-product square: the
pushout comparison of the lifted square, the identification of its two extensions of scalars
along the diagonal, and then `Dualizing.tensorSquareConjugateTail`. -/
def tensorSquareConjugate
    [Fi.IsLeftDerivedFunctor alphai
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hKp : CochainComplex.KFlat.{uRp, max v uR uA uRp}
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  let ESp := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uRp,
    max v uR uA uRp} R'
  let g' : ULift.{max v uR uA uRp} R →+* ULift.{max v uR uA uRp} A :=
    (ULift.ringEquiv.symm.toRingHom.comp (algebraMap R A)).comp ULift.ringEquiv.toRingHom
  let p' : ULift.{max v uR uA uRp} R →+* ULift.{max v uR uA uRp} R' :=
    (ULift.ringEquiv.symm.toRingHom.comp (algebraMap R R')).comp ULift.ringEquiv.toRingHom
  let w' : ULift.{max v uR uA uRp} A →+* ULift.{max v uR uA uRp} (TensorProduct R A R') :=
    (ULift.ringEquiv.symm.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom :
        A →+* TensorProduct R A R')).comp ULift.ringEquiv.toRingHom
  let h' : ULift.{max v uR uA uRp} R' →+* ULift.{max v uR uA uRp} (TensorProduct R A R') :=
    (ULift.ringEquiv.symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).comp ULift.ringEquiv.toRingHom
  let comm' := uliftSquareComm.{v, uR, uA, uRp, max uA uRp} (algebraMap R A) (algebraMap R R')
    (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A R')
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
    tensorProductSquareComm
  let hp' := uliftIsPushoutSquare.{v, uR, uA, uRp, max uA uRp} (algebraMap R A)
    (algebraMap R R')
    (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A R')
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
    tensorProductSquareComm MilnorPatching.tensorPushout comm'
  let Kt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uR uA uRp} R ≃+* R).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  (DerivedCategory.Q ⋙ ESp.inverse).map
      ((pushoutBaseChangeComplex g' p' w' h' comm' hp').inv.app
        (((ModuleCat.extendScalars.{max v uR uA uRp, max v uR uA uRp,
          max v uR uA uRp} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj Kt)) ≫
    (DerivedCategory.Q ⋙ ESp.inverse).map
        (((ModuleCat.restrictScalars.{max v uR uA uRp} h').mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((extendScalarsSquareIsoComplex g' p' w' h' comm').inv.app Kt)) ≫
      tensorSquareConjugateTail.{uR, uA, uRp, v} Fi alphai K hKp

variable
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

/-- **The right-hand side of the pairing at the tensor-product square.**
`Dualizing.liftSquareConjugatedFormula` at the tensor-product square: the transport prefix of the
independent-universe projection formula at `R → A` and the factor after it, both base changed
along `R → R'`, the comparison morphism of the model `baseChangeR` at the chain-level source of
the projection formula at the lifted edge, and then `Dualizing.tensorSquareConjugate`. -/
def tensorSquareConjugatedFormula
    [Ff.IsLeftDerivedFunctor alphaf
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
    [Fi.IsLeftDerivedFunctor alphai
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hKp : CochainComplex.KFlat.{uRp, max v uR uA uRp}
      (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  let g' : ULift.{max v uR uA uRp} R →+* ULift.{max v uR uA uRp} A :=
    (ULift.ringEquiv.symm.toRingHom.comp (algebraMap R A)).comp ULift.ringEquiv.toRingHom
  let Kt := ((ModuleCat.restrictScalars
      (ULift.ringEquiv : ULift.{max v uR uA uRp} R ≃+* R).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  baseChangeR.map (liftTransportPrefix.{max v uRp, uR, uA} (algebraMap R A) Ff alphaf K) ≫
    baseChangeR.map (liftTransportFactors.{max v uRp, uR, uA} (algebraMap R A) K) ≫
      (liftedBaseChangeComparison.{max v uA, uR, uRp} (algebraMap R R')
            baseChangeR comparisonR).app
          ((CochainComplex.extendScalarsLarge g' ⋙
            CochainComplex.restrictScalarsLarge g').obj Kt) ≫
        tensorSquareConjugate.{uR, uA, uRp, v} Fi alphai K hKp

/-- **The projection formula at the two edges of the tensor-product square, in the keystone's
spelling.**  For arbitrary models `Ff`, `Fi` of derived extension of scalars along `R → A` and
`R' → A ⊗_R R'` and an arbitrary model `baseChangeR` of derived base change along `R → R'` with
only a comparison morphism: the base change along `R → R'` of the component of
`Dualizing.derivedExtendRestrictScalarsTensorIso` at `R → A`, read at the class of a K-flat
complex `K` and against the transport tail of the scalar lift, is
`Dualizing.tensorSquareConjugatedFormula`.

This is `Dualizing.derivedExtendRestrictScalarsTensorIso_square` at the tensor-product square,
re-run rather than instantiated: the square's rings force `uT` to be `uA`, so the statement
there spells the two projection formulas at `max v uA uRp` and `max v uR uA` while the keystone
spells them at `max v uRp` and `max v uR`.  Every input of
`Stacks.CategoryTheory.comp_eq_of_chain_pairing` that mentions a projection formula is available
at either spelling, and the rest concern only the lifted square. -/
theorem derivedExtendRestrictScalarsTensorIso_square_tensorProduct
    [Ff.IsLeftDerivedFunctor alphaf
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
    [Fi.IsLeftDerivedFunctor alphai
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA uRp} K) :
    let g' : ULift.{max v uR uA uRp} R →+* ULift.{max v uR uA uRp} A :=
      (ULift.ringEquiv.symm.toRingHom.comp (algebraMap R A)).comp ULift.ringEquiv.toRingHom
    let Kt := ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA uRp} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    let Bcg := (CochainComplex.singleFunctor
        (ModuleCat.{max v uR uA uRp} (ULift.{max v uR uA uRp} R)) 0).obj
      ((ModuleCat.restrictScalars g').obj
        (ModuleCat.of (ULift.{max v uR uA uRp} A) (ULift.{max v uR uA uRp} A)))
    baseChangeR.map ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
            (algebraMap R A) Ff alphaf).hom.app (DerivedCategory.Q.obj K)) ≫
        baseChangeR.map (liftTransportTail.{max v uRp, uR, uA} (algebraMap R A) K hK) ≫
          (liftedBaseChangeComparison.{max v uA, uR, uRp} (algebraMap R R')
              baseChangeR comparisonR).app
            ((MonoidalCategory.tensorLeft Bcg).obj Kt) =
      tensorSquareConjugatedFormula.{uR, uA, uRp, v} Fi alphai Ff alphaf baseChangeR comparisonR
        K (kFlat_extendScalars_algebraMapR'.{uR, uA, uRp, v} K hK) := by
  intro g' Kt Bcg
  exact Stacks.CategoryTheory.comp_eq_of_chain_pairing _ _ _ _
    (liftedBaseChangeComparison.{max v uA, uR, uRp} (algebraMap R R') baseChangeR comparisonR)
    ((extendRestrictScalarsComplexIso g').hom.app Kt) _ _ _ _ _
    (extendRestrictScalarsComplexIso_square.{max v uR uA uRp} _ _ _ _
      (uliftSquareComm.{v, uR, uA, uRp, max uA uRp} (algebraMap R A) (algebraMap R R')
        (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A R')
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom tensorProductSquareComm)
      (uliftIsPushoutSquare.{v, uR, uA, uRp, max uA uRp} (algebraMap R A) (algebraMap R R')
        (Algebra.TensorProduct.includeLeftRingHom : A →+* TensorProduct R A R')
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom tensorProductSquareComm
        MilnorPatching.tensorPushout _) _)
    _ _ _ _
    (derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing.{max v uRp, uR, uA}
      (algebraMap R A) Ff alphaf K hK)
    _ _ _ _
    (liftSquareRetraction_comp.{max v uR, uRp, max uA uRp} _ Fi alphai _ _ _
      (uliftExtendScalarsCommUpApp.{max v uA, uR, uRp} (algebraMap R R') K))
    (liftSquarePrefixTransported_comp.{max v uR, uRp, max uA uRp} _ Fi alphai _ _ _ _)

end TensorProductSquare

end Dualizing

end
