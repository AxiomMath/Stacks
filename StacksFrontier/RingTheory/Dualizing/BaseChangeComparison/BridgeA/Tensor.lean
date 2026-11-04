module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Basic
import StacksFrontier.Homology.HomComplex.RHom.BaseChange
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelRestrictScalars
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ProjectionFormula
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.Invertibility

/-!
# Restricting derived extension of scalars is derived tensoring with the algebra

Let `f : R → A` be a homomorphism of commutative rings. Extension of scalars along `f`, followed
by restriction of scalars back to `R`, is tensoring with `A` over `R`; the derived form of that
statement is the projection formula for a ring map, and it is the one input
`Dualizing.derivedHomRestrictScalarsInternalHomIso` needs.

The statement is available in the library at equal ring universes and for the tensor bifunctor of
the K-flat model over the ring itself. This file lifts it to independent ring and module universes
and to the tensor bifunctor of `derivedHomAdjunctionOverRing`, with which Stacks 0A63, Stacks 0E1W
and Stacks 0E1X are stated. Both rings are replaced by their universe lifts, which live in one and
the same universe, the equal-universe statement is applied there, and the result is carried back
along the derived restriction-of-scalars equivalences induced by `ULift.ringEquiv`. The
identification of derived extensions of scalars across the lift is uniqueness of left adjoints, by
Stacks 0GMT; the identification of the two restrictions is
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso`.
## Main definitions

* `Dualizing.derivedExtendRestrictScalarsTensorIso` — the projection formula at independent
  universes: derived extension of scalars along `f`, followed by derived restriction of scalars,
  is derived tensoring with the algebra.
* `Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel`,
  `Dualizing.derivedHomRestrictScalarsInternalHomIsoCanonical` — the bridge of Stacks 0E2A,
  unconditionally: restriction of derived coextension of scalars is derived internal Hom out of
  the algebra, for an arbitrary model of derived extension of scalars and for the canonical one.
* `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse`,
  `Dualizing.extendRestrictScalarsComplexIso`, `Dualizing.derivedAlgebraSingleLiftIso` — the
  equal-universe projection formula, its chain-level counterpart, and the object-level
  identification of the lifted algebra.

## Main results

* `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app` and
  `…_hom_app_of_iso` — the equal-universe projection formula on a K-flat representative, and the
  same computation carried along an arbitrary isomorphism onto a K-flat representative.
* `Dualizing.kFlat_restrictScalars_uliftRingEquiv` — the universe lift of a K-flat complex is
  K-flat.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app` — the component of the projection
  formula at an arbitrary object, as the composite of the seven whiskerings that define it.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` — the component at the class of
  a K-flat complex, with the one derived-functor factor computed, so that every factor is a
  transport along a universe lift or a chain-level map.

## Implementation notes

`CategoryTheory.Functor.curryObjSwapFlip` exchanges the two ways of fixing one argument of a
bifunctor precomposed with the swap, and `CategoryTheory.Functor.flipObjConjugate` identifies a
partial application of a bifunctor conjugated by an equivalence with the conjugate of the partial
application; the tensor product of `derivedHomAdjunctionOverRing` is such a conjugate.

The equal-universe projection formula, its chain-level counterpart and the object-level
identification of the lifted algebra are `private` in
`StacksFrontier.Homology.HomComplex.RHom.BaseChange`; each is given a public name here, carrying
`@[no_expose]`.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open scoped ChangeOfRings

universe uR uA uS uT v w

namespace CategoryTheory.Functor

/-- Fixing the first argument of a bifunctor precomposed with the swap is the same as fixing its
second argument. -/
def curryObjSwapFlip {C : Type*} {D : Type*} [Category* C] [Category* D] (G : C × C ⥤ D)
    (L : C) :
    (Functor.curry.obj (CategoryTheory.Prod.swap C C ⋙ G)).obj L ≅
      (Functor.curry.obj G).flip.obj L :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp)

/-- A partial application of a bifunctor conjugated by an equivalence is the conjugate of the
partial application at the transported object. -/
def flipObjConjugate {C : Type*} {D : Type*} [Category* C] [Category* D] (e : C ≌ D)
    (G : C × C ⥤ C) (L : D) :
    (Functor.curry.obj (e.inverse.prod e.inverse ⋙ G ⋙ e.functor)).flip.obj L ≅
      e.inverse ⋙ (Functor.curry.obj G).flip.obj (e.inverse.obj L) ⋙ e.functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; simp)

end CategoryTheory.Functor

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] extendScalarsAdditiveOfRingHom

/-- **The projection formula for a ring map, at equal ring and module universes.** Derived
extension of scalars along `g : S → T`, followed by derived restriction of scalars, is derived
tensoring with the algebra `T` viewed as a degree-zero complex of `S`-modules, for the tensor
bifunctor of the K-flat model over `S` itself. -/
@[no_expose]
noncomputable def derivedExtendRestrictScalarsTensorIsoEqualUniverse {S T : Type uS} [CommRing S]
    [CommRing T] (g : S →+* T)
    (G : DerivedCategory (ModuleCat.{uS} S) ⥤ DerivedCategory (ModuleCat.{uS} T))
    (β : DerivedCategory.Q ⋙ G ⟶ CochainComplex.extendScalarsLarge g ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{uS} S) (ComplexShape.up ℤ))] :
    G ⋙ (ModuleCat.restrictScalars.{uS} g).mapDerivedCategory ≅
      (Functor.curry.obj (DerivedInternalHom.Model.tensor S)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{uS} S) 0).obj
          ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T))) :=
  Stacks.DerivedHom.BaseChangeIso.derivedExtensionRestrictionIso g G β

/-- **The termwise projection formula.** Extending scalars along `g : S → T` and restricting back
is, in each degree, tensoring with `T` over `S`; as a complex, it is tensoring with the
degree-zero complex `T`. -/
@[no_expose]
noncomputable def extendRestrictScalarsComplexIso {S T : Type uS} [CommRing S] [CommRing T]
    (g : S →+* T) :
    CochainComplex.extendScalarsLarge g ⋙ CochainComplex.restrictScalarsLarge g ≅
      CategoryTheory.MonoidalCategory.tensorLeft
        ((CochainComplex.singleFunctor (ModuleCat.{uS} S) 0).obj
          ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T))) :=
  Stacks.DerivedHom.BaseChangeIso.extensionRestrictionComplexIso g

/-- **On a K-flat representative, the equal-universe projection formula is the termwise tensor
comparison.** The component of `Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse` at
the class of a K-flat complex `K` is: the comparison morphism of the left-derived functor at `K`,
restricted to `S`; the identification of derived restriction of scalars with termwise restriction;
the termwise projection formula `Dualizing.extendRestrictScalarsComplexIso`; and the inverse of
the tensor comparison of the K-flat model, which is available because `K` is K-flat. -/
theorem derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app {S T : Type uS} [CommRing S]
    [CommRing T] (g : S →+* T)
    (G : DerivedCategory (ModuleCat.{uS} S) ⥤ DerivedCategory (ModuleCat.{uS} T))
    (β : DerivedCategory.Q ⋙ G ⟶ CochainComplex.extendScalarsLarge g ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{uS} S) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{uS} S) ℤ) (hK : K.KFlat) :
    (derivedExtendRestrictScalarsTensorIsoEqualUniverse g G β).hom.app
        (DerivedCategory.Q.obj K) =
      (ModuleCat.restrictScalars.{uS} g).mapDerivedCategory.map (β.app K) ≫
        ((ModuleCat.restrictScalars.{uS} g).mapDerivedCategoryFactors.app
          ((CochainComplex.extendScalarsLarge g).obj K)).hom ≫
        DerivedCategory.Q.map ((extendRestrictScalarsComplexIso g).hom.app K) ≫
        ((DerivedInternalHom.Model.adjunction S).tensorIso
          ((CochainComplex.singleFunctor (ModuleCat.{uS} S) 0).obj
            ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T))) K hK).inv :=
  Stacks.DerivedHom.BaseChangeIso.derivedExtensionRestrictionIso_hom_app g G β K hK

/-- **The equal-universe projection formula at an arbitrary object with a K-flat representative.**
`Dualizing.derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app` computes the component at
the class of a K-flat complex; this carries that computation along any isomorphism `ψ` from an
arbitrary object `Y`. -/
theorem derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app_of_iso {S T : Type uS}
    [CommRing S] [CommRing T] (g : S →+* T)
    (G : DerivedCategory (ModuleCat.{uS} S) ⥤ DerivedCategory (ModuleCat.{uS} T))
    (β : DerivedCategory.Q ⋙ G ⟶ CochainComplex.extendScalarsLarge g ⋙ DerivedCategory.Q)
    [G.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{uS} S) (ComplexShape.up ℤ))]
    (Y : DerivedCategory (ModuleCat.{uS} S))
    (K : CochainComplex (ModuleCat.{uS} S) ℤ) (hK : K.KFlat)
    (ψ : Y ≅ DerivedCategory.Q.obj K) :
    (derivedExtendRestrictScalarsTensorIsoEqualUniverse g G β).hom.app Y =
      (G ⋙ (ModuleCat.restrictScalars.{uS} g).mapDerivedCategory).map ψ.hom ≫
        ((ModuleCat.restrictScalars.{uS} g).mapDerivedCategory.map (β.app K) ≫
          ((ModuleCat.restrictScalars.{uS} g).mapDerivedCategoryFactors.app
            ((CochainComplex.extendScalarsLarge g).obj K)).hom ≫
          DerivedCategory.Q.map ((extendRestrictScalarsComplexIso g).hom.app K) ≫
          ((DerivedInternalHom.Model.adjunction S).tensorIso
            ((CochainComplex.singleFunctor (ModuleCat.{uS} S) 0).obj
              ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T))) K hK).inv) ≫
        ((Functor.curry.obj (DerivedInternalHom.Model.tensor S)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{uS} S) 0).obj
            ((ModuleCat.restrictScalars g).obj (ModuleCat.of T T)))).map ψ.inv := by
  rw [← derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app g G β K hK, ← Category.assoc,
    (derivedExtendRestrictScalarsTensorIsoEqualUniverse g G β).hom.naturality ψ.hom,
    Category.assoc, ← Functor.map_comp, ψ.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- **The universe lift of a K-flat complex is K-flat.** Restriction of scalars along
`ULift.ringEquiv : ULift S ≃+* S` carries a K-flat complex of `S`-modules to a K-flat complex of
`ULift S`-modules, both in the same module universe. -/
theorem kFlat_restrictScalars_uliftRingEquiv {S : Type uS} [CommRing S]
    (K : CochainComplex (ModuleCat.{max w uS} S) ℤ)
    (hK : CochainComplex.KFlat.{uS, w} K) :
    CochainComplex.KFlat.{max w uS, max w uS}
      (((ModuleCat.restrictScalars
          (ULift.ringEquiv : ULift.{max w uS} S ≃+* S).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) := by
  let e : ULift.{max w uS} S ≃+* S := ULift.ringEquiv
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso
    ((CategoryTheory.MonoidalCategory.tensorLeft M).mapIso
      ((NatIso.mapHomologicalComplex
        ((ModuleCat.extendRestrictScalarsAdj.{max w uS} e.symm.toRingHom).leftAdjointUniq
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max w uS} e).toAdjunction)
        (ComplexShape.up ℤ)).app K))
    (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uS, max w uS, w}
      e.symm.toRingHom K hK M hM)

/-- The transport of the algebra `T`, as a degree-zero complex of `S`-modules, along the
universe-lift equivalence over `S` is the degree-zero complex `ULift T` over the lifted base
ring. -/
@[no_expose]
noncomputable def derivedAlgebraSingleLiftIso {S : Type uS} {T : Type uT} [CommRing S]
    [CommRing T] (g : S →+* T) :
    (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uS, max uS uT w}
        S).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max uS uT w} S) 0).obj
          ((ModuleCat.restrictScalars g).obj (ModuleCat.of T (ULift.{max uS w} T)))) ≅
      (DerivedCategory.singleFunctor
          (ModuleCat.{max uS uT w} (ULift.{max uS uT w} S)) 0).obj
        ((ModuleCat.restrictScalars
            ((ULift.ringEquiv.symm.toRingHom.comp g).comp ULift.ringEquiv.toRingHom :
              ULift.{max uS uT w} S →+* ULift.{max uS uT w} T)).obj
          (ModuleCat.of (ULift.{max uS uT w} T) (ULift.{max uS uT w} T))) :=
  Stacks.DerivedHom.BaseChangeIso.modelScalarCoefficientIso.{uS, uT, w} g

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The projection formula for a ring map, at independent ring and module universes.** Derived
extension of scalars along `f : R → A`, followed by derived restriction of scalars, is derived
tensoring with the algebra `A` viewed as a degree-zero complex of `R`-modules, for the tensor
bifunctor of the fixed tensor--Hom adjunction of Stacks 0A63. The extension functor may be any
model with the total-left-derived universal property. -/
noncomputable def derivedExtendRestrictScalarsTensorIso
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))] :
    F ⋙ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory ≅
      derivedExtendRestrictScalarsTensorFunctor.{uR, uA, v} f := by
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max v uR uA} A
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let U := (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory
  let V := (ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategory
  let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
    Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{max v uR uA,
    max v uR uA, max v uR uA} f'
      (HomologicalComplex.zero :
        CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} A)) ℤ)
  let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, v}
    f F comparison
  let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{
    max v uR uA, max v uR uA, max v uR uA} _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
  let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
    (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
  let c := @derivedExtendRestrictScalarsTensorIsoEqualUniverse.{max v uR uA} _ _ _ _ f' T.B
    T.alphaB T.isLeftDerivedB
  let i := derivedAlgebraSingleLiftIso.{uR, uA, max v uA} f
  exact Functor.isoWhiskerLeft F (Functor.leftUnitor U).symm ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerRight S.unitIso U) ≪≫
    Functor.isoWhiskerRight eF.symm (S.inverse ⋙ U) ≪≫
    Functor.isoWhiskerLeft (E.functor ⋙ T.B) δ ≪≫
    Functor.isoWhiskerLeft E.functor (Functor.isoWhiskerRight c E.inverse) ≪≫
    Functor.isoWhiskerLeft E.functor (Functor.isoWhiskerRight
      ((Functor.curry.mapIso
          (DerivedInternalHom.Model.adjunction
            (ULift.{max v uR uA} R)).toDerivedHomAdjunction.tensorSymmetry).app _ ≪≫
        Functor.curryObjSwapFlip _ _ ≪≫
        ((Functor.curry.obj
          (DerivedInternalHom.Model.tensor (ULift.{max v uR uA} R))).flip.mapIso i).symm)
      E.inverse) ≪≫
    (Functor.flipObjConjugate
      (uliftDerivedEquivalence.{uR, max v uR uA, max v uR uA, max v uR uA + 1,
        max v uR uA + 1} R)
      (DerivedInternalHom.Model.tensor (ULift.{max v uR uA} R))
      (derivedAlgebraSingle.{uR, uA, v} f)).symm

/-- **The component of the projection formula, unfolded.** The isomorphism
`Dualizing.derivedExtendRestrictScalarsTensorIso` is a composite of seven whiskerings, and its
component at an object `X` of `D(R)` is the composite of the unit of the universe-lift equivalence
over `A`, the identification `eF` of the two derived extensions of scalars across the lift
(uniqueness of left adjoints, Stacks 0GMT), the identification `δ` of the two derived restrictions
(`Stacks.DerivedHom.BaseChange.scalarRestrictionIso`), the equal-universe projection formula `c`,
and the object-level identification `i` of the lifted algebra. -/
theorem derivedExtendRestrictScalarsTensorIso_hom_app
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (X : DerivedCategory (ModuleCat.{max v uR uA} R)) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max v uR uA} A
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let U := (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategory
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
      Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{max v uR uA,
      max v uR uA, max v uR uA} f'
        (HomologicalComplex.zero :
          CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} A)) ℤ)
    let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, v}
      f F comparison
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{
      max v uR uA, max v uR uA, max v uR uA} _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let c := @derivedExtendRestrictScalarsTensorIsoEqualUniverse.{max v uR uA} _ _ _ _ f' T.B
      T.alphaB T.isLeftDerivedB
    let i := derivedAlgebraSingleLiftIso.{uR, uA, max v uA} f
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).hom.app X =
      (Functor.leftUnitor U).inv.app (F.obj X) ≫
        U.map (S.unitIso.hom.app (F.obj X)) ≫
          U.map (S.inverse.map (eF.inv.app X)) ≫
            δ.hom.app (T.B.obj (E.functor.obj X)) ≫
              E.inverse.map (c.hom.app (E.functor.obj X)) ≫
                E.inverse.map
                    (((Functor.curry.mapIso
                        (DerivedInternalHom.Model.adjunction
                          (ULift.{max v uR uA} R)).toDerivedHomAdjunction.tensorSymmetry).app
                          ((DerivedCategory.singleFunctor
                            (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
                            ((ModuleCat.restrictScalars f').obj
                              (ModuleCat.of (ULift.{max v uR uA} A)
                                (ULift.{max v uR uA} A)))) ≪≫
                      Functor.curryObjSwapFlip _ _ ≪≫
                      ((Functor.curry.obj
                        (DerivedInternalHom.Model.tensor
                          (ULift.{max v uR uA} R))).flip.mapIso i).symm).hom.app
                      (E.functor.obj X)) ≫
                  (Functor.flipObjConjugate
                    (uliftDerivedEquivalence.{uR, max v uR uA, max v uR uA, max v uR uA + 1,
                      max v uR uA + 1} R)
                    (DerivedInternalHom.Model.tensor (ULift.{max v uR uA} R))
                    (derivedAlgebraSingle.{uR, uA, v} f)).inv.app X := by
  rfl

/-- **The characterizing equation of the projection formula on a K-flat representative.** For a
K-flat complex `K` of `R`-modules, the component of
`Dualizing.derivedExtendRestrictScalarsTensorIso` at the class of `K` is the composite of
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app` in which the one derived-functor factor
has been computed: the comparison morphism `T.alphaB` of the lifted derived extension of scalars
at the lifted complex `Kt`, the identification of derived restriction of scalars with termwise
restriction, the termwise projection formula
`Dualizing.extendRestrictScalarsComplexIso`, and the tensor comparison of the K-flat model, which
applies because `Kt` is K-flat by `Dualizing.kFlat_restrictScalars_uliftRingEquiv`. -/
theorem derivedExtendRestrictScalarsTensorIso_hom_app_q_obj
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA} K) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max v uR uA} A
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let U := (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategory
    let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse :=
      Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{max v uR uA,
      max v uR uA, max v uR uA} f'
        (HomologicalComplex.zero :
          CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} A)) ℤ)
    let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, v}
      f F comparison
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{
      max v uR uA, max v uR uA, max v uR uA} _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
    let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
      (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
    let i := derivedAlgebraSingleLiftIso.{uR, uA, max v uA} f
    let Bc := (CochainComplex.singleFunctor
      (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
      ((ModuleCat.restrictScalars f').obj
        (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
    let Bd := (DerivedCategory.singleFunctor
      (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
      ((ModuleCat.restrictScalars f').obj
        (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
    let Kt := ((ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    let ψ : E.functor.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj Kt :=
      (ModuleCat.restrictScalars
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+*
          R).toRingHom).mapDerivedCategoryFactors.app K
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).hom.app
        (DerivedCategory.Q.obj K) =
      (Functor.leftUnitor U).inv.app (F.obj (DerivedCategory.Q.obj K)) ≫
        U.map (S.unitIso.hom.app (F.obj (DerivedCategory.Q.obj K))) ≫
          U.map (S.inverse.map (eF.inv.app (DerivedCategory.Q.obj K))) ≫
            δ.hom.app (T.B.obj (E.functor.obj (DerivedCategory.Q.obj K))) ≫
              E.inverse.map
                  ((T.B ⋙ V).map ψ.hom ≫
                    (V.map (T.alphaB.app Kt) ≫
                      ((ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategoryFactors.app
                        ((CochainComplex.extendScalarsLarge f').obj Kt)).hom ≫
                      DerivedCategory.Q.map
                        ((extendRestrictScalarsComplexIso f').hom.app Kt) ≫
                      ((DerivedInternalHom.Model.adjunction
                        (ULift.{max v uR uA} R)).tensorIso Bc Kt
                          (kFlat_restrictScalars_uliftRingEquiv.{uR, max v uA} K hK)).inv) ≫
                    ((Functor.curry.obj (DerivedInternalHom.Model.tensor
                      (ULift.{max v uR uA} R))).obj Bd).map ψ.inv) ≫
                E.inverse.map
                    (((Functor.curry.mapIso
                        (DerivedInternalHom.Model.adjunction
                          (ULift.{max v uR uA} R)).toDerivedHomAdjunction.tensorSymmetry).app Bd ≪≫
                      Functor.curryObjSwapFlip _ _ ≪≫
                      ((Functor.curry.obj
                        (DerivedInternalHom.Model.tensor
                          (ULift.{max v uR uA} R))).flip.mapIso i).symm).hom.app
                      (E.functor.obj (DerivedCategory.Q.obj K))) ≫
                  (Functor.flipObjConjugate
                    (uliftDerivedEquivalence.{uR, max v uR uA, max v uR uA, max v uR uA + 1,
                      max v uR uA + 1} R)
                    (DerivedInternalHom.Model.tensor (ULift.{max v uR uA} R))
                    (derivedAlgebraSingle.{uR, uA, v} f)).inv.app (DerivedCategory.Q.obj K) := by
  intro E S f' U V δ T a a' eF i Bc Bd Kt ψ
  rw [derivedExtendRestrictScalarsTensorIso_hom_app.{uR, uA, v} f F comparison,
    @derivedExtendRestrictScalarsTensorIsoEqualUniverse_hom_app_of_iso.{max v uR uA}
      _ _ _ _ f' T.B T.alphaB T.isLeftDerivedB
      (E.functor.obj (DerivedCategory.Q.obj K)) Kt
      (kFlat_restrictScalars_uliftRingEquiv.{uR, max v uA} K hK) ψ]

/-- **The bridge of Stacks 0E2A, unconditionally.** Restriction of scalars along `f : R → A`,
applied to the derived coextension `RHom_R(A, -)` of Stacks 0A70, is the derived internal Hom out
of the algebra `A` viewed as a degree-zero complex of `R`-modules, at independent ring and module
universes. -/
noncomputable def derivedHomRestrictScalarsInternalHomIsoOfModel
    (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))] :
    derivedCoextendRestrictScalarsFunctor.{uR, uA, v} f ≅
      derivedInternalHomAlgebraFunctor.{uR, uA, v} f :=
  derivedHomRestrictScalarsInternalHomIso.{uR, uA, v} f F comparison
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison)

/-- **The bridge of Stacks 0E2A at the canonical model.** The same identification as
`Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel`, with the derived extension of scalars
taken to be the model of Stacks 06Y6 computed by K-flat resolutions. -/
noncomputable def derivedHomRestrictScalarsInternalHomIsoCanonical :
    derivedCoextendRestrictScalarsFunctor.{uR, uA, v} f ≅
      derivedInternalHomAlgebraFunctor.{uR, uA, v} f :=
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{uR, uA, v} f
    (HomologicalComplex.zero : CochainComplex (ModuleCat.{max v uR uA} A) ℤ)
  @derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, v} R A _ _ f T.B T.alphaB
    T.isLeftDerivedB

end Dualizing

end
