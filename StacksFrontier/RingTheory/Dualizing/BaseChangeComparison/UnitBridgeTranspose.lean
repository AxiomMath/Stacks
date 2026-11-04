module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionKFlat

/-!
# The keystone obligation with the derived-Hom base-change morphism of Stacks 0E1X removed

`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.AlgebraActionKFlat` reduces the
projection-formula compatibility of [stacks 0E2A] to `Dualizing.UnitBridgeCompatibility`, an
equation between two morphisms

`baseChangeA(W)|_{R'} ⟶ RHom_{R'}(A ⊗ᴸ_R R', (W|_R) ⊗ᴸ_R R')`

of `D(R')`.  Of its factors one is still a mate: the derived-Hom base-change morphism `δ` of
[stacks 0E1X], which occurs once, on the right-hand side.  This file removes it.

`δ` is *defined* as an adjoint transpose: `Stacks.DerivedHom.ExtensionOfScalars`
`.derivedHomBaseChange_homEquiv` says its transpose under the extension-of-scalars adjunction of
[stacks 0GMT] is derived Hom applied to the unit of that adjunction, followed by the
change-of-rings isomorphism of [stacks 0E1W].  So transposing the whole obligation over
[stacks 0GMT] eliminates it — the only preparation needed is that the source of the two morphisms
be a derived base change, which it is: the comparison `Dualizing.restrictionBaseChangeIsoGeneral`
of [stacks 0661] identifies `baseChangeA(W)|_{R'}` with `(W|_R) ⊗ᴸ_R R'`, and precomposing with
its inverse is a bijection on morphisms out of it.

In the transposed form the obligation is an equation in `D(R)` between two morphisms

`W|_R ⟶ (RHom_{R'}(A ⊗ᴸ_R R', (W|_R) ⊗ᴸ_R R'))|_R`,

whose factors are the two units of the derived restriction/Hom adjunction of [stacks 0A70], the
unit of [stacks 0GMT] along `R → R'`, the two bridges
`Dualizing.derivedHomRestrictScalarsInternalHomIsoOfModel` of [stacks 0E2A], the comparison of
[stacks 0661], the base change `Dualizing.derivedBaseChangeAlgebraIso` of the algebra, and the
isomorphism of [stacks 0E1W].  Both transpositions used are bijections, so the reduction is an
`Iff` and nothing is weakened.

**What this settles about the lax monoidal structure map.**  `Dualizing.derivedTensorBaseChange`
— the map `μ` whose invertibility `…BaseChangeComparison.TensorBaseChangeBridge` reduces to one
equation — is built out of `δ` as a double transpose
(`Dualizing.derivedTensorBaseChange_eq`), and `δ` is the primitive of the two.  The reduction of
`…BaseChangeComparison.AlgebraActionKFlat` already removed `μ` from the obligation; the reduction
here removes `δ` as well.  So neither `μ` nor the morphism it is built from occurs in the
remaining equation, and `IsIso μ` is not a hypothesis that can discharge it: there is no
occurrence of `μ` to cancel against.  Invertibility of `μ` remains worth having for its own sake,
but it is not a route to [stacks 0E2A].

**What is not done here.** The transposed equation is not proved, so
`Dualizing.KFlatAlgebraActionEq` — the hypothesis `hAct` carried by the library's [stacks 0BZM]
and [stacks 0BZN] — remains open, and no tag loses its conditional caveat.  What the equation now
needs is the chain-level characterizations of its remaining factors at K-flat complexes:
`RingTheory.TorIndependence.derivedBaseChangeComparison_snd_app_eq` for [stacks 0661] and
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`
for the unit of [stacks 0GMT] are available, and so is the isomorphism of [stacks 0E1W], in both
directions:
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` pins its
components at a K-flat/K-injective pair and
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective` pins the
inverse components, with every factor there read in the direction that inverts nothing.  What is
not pinned at that level are the two bridges of [stacks 0E2A].

## Main results

* `Dualizing.homEquiv_map_comp_derivedHomBaseChange` — **the elimination of [stacks 0E1X]**: the
  transpose over [stacks 0GMT] of `F(u)` followed by `δ_{K,M}` is `u` followed by derived Hom
  applied to the unit of [stacks 0GMT] and the isomorphism of [stacks 0E1W].  Naturality of the
  Hom equivalence in its source variable and the defining transpose of `δ` are the whole proof.
* `Dualizing.unitBridgeCompatibility_iff_unitTranspose` — **the reduction**:
  `Dualizing.UnitBridgeCompatibility` holds at an object precisely when its transpose over
  [stacks 0GMT], taken after the comparison of [stacks 0661], does; and in that transpose the
  morphism of [stacks 0E1X] does not occur.

## Implementation notes

`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`'s `hom` field is definitionally equal but
not syntactically equal to `Stacks.DerivedHom.ScalarTransportedInternalHom.hom` — the field is
reached through a definition that is not exposed — and `rw` will not fire across the gap, while
`exact` crosses it.  The same obstruction is why the cancellation of the comparison of
[stacks 0661] against its inverse is done through a `have` quantified over the trailing morphism
rather than by rewriting with `CategoryTheory.Iso.inv_hom_id_app_assoc`.

`Eq.congr_right` is what lets the right-hand side of
`Dualizing.UnitBridgeCompatibility` stay implicit: the goal it leaves is the computation of that
side's transpose alone, with the side itself supplied by unification.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp uM v

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

section Mate

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- **The derived-Hom base-change morphism of [stacks 0E1X], eliminated by its own transpose.**
For `u : X ⟶ RHom_R(K, M)` the transpose, under the extension-of-scalars adjunction of
[stacks 0GMT] along `f : R → A`, of

`F X ⟶ F (RHom_R(K, M)) ⟶ RHom_A(F K, F M)`

— the model `F` applied to `u`, followed by the morphism `δ_{K,M}` of [stacks 0E1X] — is `u`
followed by derived Hom applied to the unit of [stacks 0GMT] at `M` and the change-of-rings
isomorphism of [stacks 0E1W].  Nothing survives of `δ` but that unit.

The proof is the naturality of the Hom equivalence in its source variable together with
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_homEquiv`, which is the defining
property of `δ`: it *is* that transpose. -/
theorem homEquiv_map_comp_derivedHomBaseChange
    (X K M : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (u : X ⟶ (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.obj
      (Opposite.op K, M)) :
    (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).homEquiv X _
        (F.map u ≫ Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F
          comparison K M) =
      u ≫ (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.map
            ((𝟙 (Opposite.op K),
              (derivedExtensionScalarsAdjunction.{uR, uA, uM} f F comparison).unit.app M) :
              (Opposite.op K, M) ⟶
                (Opposite.op K,
                  (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
                    (F.obj M))) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).hom.app (Opposite.op K, F.obj M) :=
  (Adjunction.homEquiv_naturality_left _ _ _).trans
    (congrArg (u ≫ ·)
      (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_homEquiv.{uR, uA, uM}
        f F comparison K M))

end Mate

section Square

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)))
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)))

variable
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]

variable
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The keystone obligation with [stacks 0E1X] removed.**
`Dualizing.UnitBridgeCompatibility` holds at an object `W` of `D(A)` if and only if the two
morphisms, precomposed with the inverse of the comparison of [stacks 0661] and transposed over
the extension-of-scalars adjunction of [stacks 0GMT] along `R → R'`, agree as morphisms

`W|_R ⟶ (RHom_{R'}(A ⊗ᴸ_R R', (W|_R) ⊗ᴸ_R R'))|_R`

of `D(R)`.  Precomposition with an isomorphism and the Hom equivalence of [stacks 0GMT] are both
bijections, so this is an equivalence and the obligation is not weakened.

The right-hand side of the transposed equation is computed outright by
`Dualizing.homEquiv_map_comp_derivedHomBaseChange`: the derived-Hom base-change morphism of
[stacks 0E1X] is replaced by the unit of [stacks 0GMT] and the isomorphism of [stacks 0E1W].
Since `Dualizing.derivedTensorBaseChange` is built from that morphism, the obligation now
mentions neither it nor the lax monoidal structure map. -/
theorem unitBridgeCompatibility_iff_unitTranspose
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp} A)) :
    UnitBridgeCompatibility hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
        comparisonA isLeftDerivedA Ff alphaf Fi alphai W ↔
      (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
            comparisonR).homEquiv
          ((ModuleCat.restrictScalars.{max v uR uA uRp}
            (algebraMap R A)).mapDerivedCategory.obj W) _
          ((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR
              baseChangeA comparisonA isLeftDerivedA).inv.app W ≫
            ((((ModuleCat.restrictScalars
                          (Algebra.TensorProduct.includeRight :
                            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
                        ((derivedHomAdjunction.{uRp, max uA uRp, max v uR}
                          (Algebra.TensorProduct.includeRight :
                            R' →ₐ[R] TensorProduct R A R').toRingHom).unit.app
                          (baseChangeA.obj W)) ≫
                      (derivedHomRestrictScalarsInternalHomIsoOfModel.{uRp, max uA uRp, max v uR}
                          (Algebra.TensorProduct.includeRight :
                            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
                        ((ModuleCat.restrictScalars
                            (Algebra.TensorProduct.includeRight :
                              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                          (baseChangeA.obj W))) ≫
                    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                        max v uR uA uRp + 1} R').hom.map
                      ((𝟙 (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                              (Algebra.TensorProduct.includeRight :
                                R' →ₐ[R] TensorProduct R A R').toRingHom)),
                          (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR
                            isLeftDerivedR baseChangeA comparisonA isLeftDerivedA).hom.app W) :
                        (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                            (Algebra.TensorProduct.includeRight :
                              R' →ₐ[R] TensorProduct R A R').toRingHom),
                          ((ModuleCat.restrictScalars
                              (Algebra.TensorProduct.includeRight :
                                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                            (baseChangeA.obj W))) ⟶
                          (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                              (Algebra.TensorProduct.includeRight :
                                R' →ₐ[R] TensorProduct R A R').toRingHom),
                            (baseChangeR.obj
                              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                                (algebraMap R A)).mapDerivedCategory.obj W))))) ≫
                  (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                      max v uR uA uRp + 1} R').hom.map
                    (((derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
                            baseChangeA comparisonA isLeftDerivedA).hom.op,
                        𝟙 (baseChangeR.obj
                          ((ModuleCat.restrictScalars.{max v uR uA uRp}
                            (algebraMap R A)).mapDerivedCategory.obj W))) :
                      (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                          (Algebra.TensorProduct.includeRight :
                            R' →ₐ[R] TensorProduct R A R').toRingHom),
                        (baseChangeR.obj
                          ((ModuleCat.restrictScalars.{max v uR uA uRp}
                            (algebraMap R A)).mapDerivedCategory.obj W))) ⟶
                        (Opposite.op (baseChangeR.obj
                            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))),
                          (baseChangeR.obj
                            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                              (algebraMap R A)).mapDerivedCategory.obj W)))))) =
        ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.map
              ((derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).unit.app W) ≫
            (derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, max v uRp}
                (algebraMap R A) Ff alphaf).hom.app
              ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj W)) ≫
          (derivedHomAdjunctionOverRing.{uR, max v uR uA uRp, max v uR uA uRp + 1} R).hom.map
              ((𝟙 (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))),
                  (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R')
                      baseChangeR comparisonR).unit.app
                    ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj W)) :
                (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)),
                    (ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj W) ⟶
                  (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)),
                    (ModuleCat.restrictScalars.{max v uR uA uRp}
                        (algebraMap R R')).mapDerivedCategory.obj
                      (baseChangeR.obj
                        ((ModuleCat.restrictScalars.{max v uR uA uRp}
                          (algebraMap R A)).mapDerivedCategory.obj W)))) ≫
            (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uRp, max v uA}
                (algebraMap R R') baseChangeR comparisonR).hom.app
              (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)),
                baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj W)) := by
  refine Iff.trans (cancel_epi ((restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR
    isLeftDerivedR baseChangeA comparisonA isLeftDerivedA).inv.app W)).symm
    (Iff.trans ((derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R')
      baseChangeR comparisonR).homEquiv _ _).injective.eq_iff.symm ?_)
  have hcanc : ∀ (Z : DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
      (g : baseChangeR.obj ((ModuleCat.restrictScalars.{max v uR uA uRp}
          (algebraMap R A)).mapDerivedCategory.obj W) ⟶ Z),
      (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
            comparisonA isLeftDerivedA).inv.app W ≫
          (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
            comparisonA isLeftDerivedA).hom.app W ≫ g = g := by
    intro Z g
    rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  refine Eq.congr_right (Eq.trans (congrArg (fun z =>
      (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
        comparisonR).homEquiv _ _ z) (hcanc _ _)) ?_)
  exact homEquiv_map_comp_derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
    comparisonR _ _ _ _

end Square

end Dualizing

end
