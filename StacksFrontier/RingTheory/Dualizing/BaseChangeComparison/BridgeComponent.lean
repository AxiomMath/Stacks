module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.UnitBridgeTranspose

/-!
# The bridge of Stacks 0E2A, component by component

`Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel` is the identification of
[stacks 0E2A] between restriction of the derived coextension `RHom_R(A, -)` of [stacks 0A70] and
the derived internal Hom out of the algebra.  It is built as
`CategoryTheory.Adjunction.rightAdjointUniq`, so nothing in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Tensor` says what its components
are; the only equation recorded about it,
`Dualizing.homEquiv_symm_algebraAction`, speaks about the bridge *preceded by the unit of*
[stacks 0A70], which is the shape the keystone obligation
`Dualizing.UnitBridgeCompatibility` reads it in.

This file records the component itself.  Uniqueness of right adjoints has a defining equation —
`CategoryTheory.Adjunction.homEquiv_symm_rightAdjointUniq_hom_app`: the transpose of the
component along the second adjunction is the counit of the first — and here the first adjunction
is a composite of [stacks 0GMT] with [stacks 0A70], whose counit `CategoryTheory.Adjunction`
computes, while the second is the tensor--Hom adjunction of [stacks 0A63] transported along the
projection formula, whose Hom equivalence is the structure field of the [stacks 0A63] bundle.
So the component is an outright transpose of a three-factor composite.

**What this settles about pinning the bridge at a K-flat complex.**  The composite the component
transposes has the projection formula `Dualizing.derivedExtendRestrictScalarsTensorIso` evaluated
at `RHom_R(A, X)|_R`, *not* at `X`.  The projection formula is pinned down at the class of a
K-flat complex by
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj`, so a K-flatness hypothesis on a
representative of `X` buys nothing here: it is a hypothesis about the wrong argument.  The same
is true of the form the obligation uses, `Dualizing.homEquiv_symm_algebraAction`, where the
projection formula is evaluated at `W|_R`: K-flatness of a complex `X` of `A`-modules does not
make `X|_R` K-flat over `R` — for `X` the algebra in degree zero that is flatness of `A` over
`R` — and the library has no lemma that produces one from the other.

## Main results

* `CategoryTheory.Adjunction.rightAdjointUniq_comp_ofNatIsoLeft_hom_app` — the component of the
  comparison of the two right adjoints of `L ⋙ Rr`, where the second right adjoint comes from an
  adjunction `Tens ⊣ Hm` and an identification `pf : L ⋙ Rr ≅ Tens` of the left adjoints: it is
  the transpose along `Tens ⊣ Hm` of the inverse of `pf`, the counit of `L ⊣ Rr` and the counit
  of `Rr ⊣ H`.  This is the companion of
  `CategoryTheory.Adjunction.homEquiv_isoLeft_comp_counit`, which computes the same comparison
  after the unit of `Rr ⊣ H`.
* `Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel_hom_app` — **the component of the
  bridge of [stacks 0E2A]**: at an object `X` of `D(R)` it is the transpose, under the
  tensor--Hom adjunction of [stacks 0A63] over `R`, of the inverse projection formula at
  `RHom_R(A, X)|_R`, the restricted counit of [stacks 0GMT] at `RHom_R(A, X)`, and the counit of
  [stacks 0A70] at `X`.

## Implementation notes

The abstract lemma is proved from
`CategoryTheory.Adjunction.homEquiv_symm_rightAdjointUniq_hom_app` by transposing both sides, then
rewriting the Hom equivalence of `CategoryTheory.Adjunction.ofNatIsoLeft` and the counit of
`CategoryTheory.Adjunction.comp`.  Its specialization is then `exact`:
`Dualizing.derivedCoextendRestrictScalars_adj` is a composite of the two adjunctions by definition,
and `Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel` is
`CategoryTheory.Adjunction.rightAdjointUniq` of it against the transported tensor--Hom adjunction,
but neither identity is syntactic, so `rw` does not fire across it while definitional unification
does — the obstruction recorded in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.UnitBridgeTranspose`.

No `@[stacks]` attribute is placed here: this is a computation about one factor of
[stacks 0E2A], which is registered on `Dualizing.isIso_derivedHomBaseChange_app_iff_diagonal`.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA v

namespace CategoryTheory.Adjunction

/-- **The comparison of two right adjoints, componentwise.**  Let `adj1 : L ⊣ Rr` and
`adj2 : Rr ⊣ H`, so that `H ⋙ Rr` is right adjoint to `L ⋙ Rr`, let `adjT : Tens ⊣ Hm` be a
second adjunction and let `pf : L ⋙ Rr ≅ Tens` identify the two left adjoints.  Then the
component at `X` of the canonical isomorphism `H ⋙ Rr ≅ Hm` is the transpose along `adjT` of

`Tens (Rr (H X)) ⟶ Rr (L (Rr (H X))) ⟶ Rr (H X) ⟶ X`,

the inverse of `pf`, the counit of `adj1` and the counit of `adj2`.

This is the companion of `CategoryTheory.Adjunction.homEquiv_isoLeft_comp_counit`, which computes
the same isomorphism after `Rr` applied to the unit of `adj2`; here nothing precedes it, and the
counit of `adj2` appears instead. -/
theorem rightAdjointUniq_comp_ofNatIsoLeft_hom_app {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {Rr : D ⥤ C} {H : C ⥤ D} {Tens Hm : C ⥤ C}
    (adj1 : L ⊣ Rr) (adj2 : Rr ⊣ H) (adjT : Tens ⊣ Hm) (pf : L ⋙ Rr ≅ Tens) (X : C) :
    (rightAdjointUniq (adj1.comp adj2) (adjT.ofNatIsoLeft pf.symm)).hom.app X =
      adjT.homEquiv (Rr.obj (H.obj X)) X
        (pf.inv.app (Rr.obj (H.obj X)) ≫
          Rr.map (adj1.counit.app (H.obj X)) ≫ adj2.counit.app X) := by
  have h := homEquiv_symm_rightAdjointUniq_hom_app (adj1.comp adj2)
    (adjT.ofNatIsoLeft pf.symm) X
  have h2 := (Equiv.symm_apply_eq _).mp h
  rw [homEquiv_ofNatIsoLeft_apply, comp_counit_app] at h2
  exact h2

end CategoryTheory.Adjunction

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]

/-- **The component of the bridge of [stacks 0E2A].**  At an object `X` of `D(R)` the
identification of `RHom_R(A, X)|_R` with the derived internal Hom `RHom_R(A, X)` out of the
algebra is the transpose, under the tensor--Hom adjunction of [stacks 0A63] over `R`, of

`RHom_R(A, X)|_R ⊗ᴸ_R A ⟶ (F (RHom_R(A, X)|_R))|_R ⟶ RHom_R(A, X)|_R ⟶ X`

— the inverse projection formula `Dualizing.derivedExtendRestrictScalarsTensorIso` at
`RHom_R(A, X)|_R`, the restricted counit of derived extension of scalars of [stacks 0GMT] at
`RHom_R(A, X)`, and the counit of the derived restriction/Hom adjunction of [stacks 0A70] at `X`.

The bridge is `CategoryTheory.Adjunction.rightAdjointUniq` of the composite of [stacks 0GMT] with
[stacks 0A70] against the tensor--Hom adjunction transported along the projection formula, so this
is `CategoryTheory.Adjunction.rightAdjointUniq_comp_ofNatIsoLeft_hom_app` read in that vocabulary.

Note where the projection formula is evaluated: at `RHom_R(A, X)|_R`, not at `X`.  A K-flatness
hypothesis on a representative of `X` therefore does not pin this component down, and neither does
one on a representative of `W` in the form `Dualizing.homEquiv_symm_algebraAction` that the
keystone obligation uses, where the projection formula sits at `W|_R`. -/
theorem derivedHomRestrictScalarsInternalHomIsoOfModel_hom_app
    (X : DerivedCategory (ModuleCat.{max v uR uA} R)) :
    (derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, v} f F comparison).hom.app X =
      ((derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).homEquiv
          ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj
            ((derivedHom.{uR, v, uA} f).obj X))
          (derivedAlgebraSingle.{uR, uA, v} f) X).symm
        ((derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).inv.app
            ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj
              ((derivedHom.{uR, v, uA} f).obj X)) ≫
          (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map
              ((derivedExtensionScalarsAdjunction.{uR, uA, v} f F comparison).counit.app
                ((derivedHom.{uR, v, uA} f).obj X)) ≫
            (derivedHomAdjunction.{uR, uA, v} f).counit.app X) := by
  have h := Adjunction.rightAdjointUniq_comp_ofNatIsoLeft_hom_app
    (derivedExtensionScalarsAdjunction.{uR, uA, v} f F comparison)
    (derivedHomAdjunction.{uR, uA, v} f)
    ((derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensorHomAdjunctionAt
      (derivedAlgebraSingle.{uR, uA, v} f))
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison) X
  rw [DerivedHomAdjunction.homEquiv_tensorHomAdjunctionAt] at h
  exact h

end Dualizing

end
