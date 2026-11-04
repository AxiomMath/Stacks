module

public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.BaseChangeMap
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ProjectionFormula
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelCriterion
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.Invertibility

/-!
# Detecting derived Hom base change by the tensor--Hom diagonal

Stacks 0A6A gives four sufficient conditions for the derived-Hom base-change morphism
`RHom_R(K, M) ⊗ᴸ_R A ⟶ RHom_A(K ⊗ᴸ_R A, M ⊗ᴸ_R A)` of Stacks 0E1X to be invertible, and each is
established by exhibiting the tensor--Hom diagonal of Stacks 0BYN as invertible. The proof of
Stacks 0E2A needs the converse as well: it asserts that the base-change morphism of Stacks 0E29 is
invertible *exactly when* a tensor--Hom diagonal is, and the half that is not Stacks 0A6A is the
implication from the base-change morphism back to the diagonal.

This file records that the criterion behind Stacks 0A6A is an equivalence. The mechanism is already
present in the proof of Stacks 0A6A: restriction of scalars along the ring map carries the adjoint
transpose of the base-change morphism to a composite whose only non-invertible factor is the
diagonal, and derived restriction of scalars is conservative. Both steps are reversible, so the
one-directional chain of Stacks 0A6A becomes an equivalence with no new mathematics -- only with
the equation stated as an equation rather than consumed in one direction.

This file also supplies the two objects in which Stacks 0E2A phrases its diagonal: an algebra
regarded as a degree-zero derived module over its base ring in an independently chosen module
universe, and the tensor--Hom diagonal of the canonical derived tensor--Hom adjunction over the
ring itself, which is available at a module universe independent of the ring universe where
`StacksDraft.DerivedHom.derivedTensorHomDiagonal` is not.

## Main definitions

* `Dualizing.derivedAlgebraAsModule` -- an algebra as a degree-zero derived module over its base
  ring, in a chosen module universe.
* `Dualizing.derivedTensorHomDiagonalOverRing` -- the tensor--Hom diagonal
  `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` of `derivedHomAdjunctionOverRing`, at a module universe
  independent of the ring universe.

## Main results

* `Dualizing.derivedTensorHomDiagonalOverRing_homEquiv` -- the diagonal is the morphism whose
  adjoint transpose is associativity followed by evaluation.
* `Dualizing.isIso_derivedHomBaseChange_iff_derivedTensorHomDiagonal` -- the criterion behind
  Stacks 0A6A, as an equivalence: the derived-Hom base-change morphism of Stacks 0E1X is invertible
  if and only if the corresponding tensor--Hom diagonal is.

## Implementation notes

The diagonal in the conclusion of the criterion is the one appearing in the proof of Stacks 0A6A:
`StacksDraft.DerivedHom.derivedTensorHomDiagonal` is defined only when the module universe equals
the ring universe, so the statement transports along the scalar equivalence of Stacks 0E1W, exactly
as Stacks 0A6A does. The algebra enters as the restriction of scalars of `ULift A` over `A`, which
is the spelling used in the statement of Stacks 0A6A.

The two definitions of the first section mention no comparison morphism and are stated for an
arbitrary derived-category model. The criterion itself is stated for the standard model, because
the base-change morphism of Stacks 0E1X and the comparison isomorphisms of the proof of Stacks
0A6A that it is compared against are constructed only there.

The three intermediate steps are stated privately, since they mention the model comparison
isomorphism of the proof of Stacks 0A6A, which is private to that file and reached here by
`import all`; a private name may not occur in a public statement.

## References

* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0BYN](https://stacks.math.columbia.edu/tag/0BYN)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings
open CochainComplex
open StacksDraft.DerivedHom
open StacksDraft.DerivedHom.DerivedInternalHom.Model

universe uR uA uM u v wR

namespace Dualizing

section Diagonal

/-- An algebra, viewed as a degree-zero module over its base ring in a chosen module universe. -/
public def derivedAlgebraAsModule {R : Type uR} {S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    [HasDerivedCategory.{wR} (ModuleCat.{max v uR u} R)] :
    DerivedCategory (ModuleCat.{max v uR u} R) :=
  (DerivedCategory.singleFunctor (ModuleCat.{max v uR u} R) 0).obj
    (ModuleCat.of R (ULift.{max v uR u} S))

/-- The canonical derived tensor--Hom diagonal `K ⊗ᴸ RHom(M, L) ⟶ RHom(M, K ⊗ᴸ L)` for a
commutative ring with modules in an independently chosen universe. It is the transpose, under the
adjunction of Stacks 0A63, of associativity followed by evaluation. -/
public def derivedTensorHomDiagonalOverRing {R : Type uR} [CommRing R]
    [HasDerivedCategory.{wR} (ModuleCat.{max uR v} R)]
    (K L M : DerivedCategory (ModuleCat.{max uR v} R)) :
    (derivedHomAdjunctionOverRing R).tensor.obj
      (K, (derivedHomAdjunctionOverRing R).hom.obj (Opposite.op M, L)) ⟶
    (derivedHomAdjunctionOverRing R).hom.obj
      (Opposite.op M, (derivedHomAdjunctionOverRing R).tensor.obj (K, L)) := by
  let d := derivedHomAdjunctionOverRing R
  exact (d.homEquiv _ M (d.tensor.obj (K, L))).symm
    ((d.tensorAssoc K (d.hom.obj (Opposite.op M, L)) M).hom ≫
      d.tensor.map (𝟙 K,
        d.homEquiv (d.hom.obj (Opposite.op M, L)) M L
          (𝟙 (d.hom.obj (Opposite.op M, L)))))

/-- The adjoint transpose of the diagonal is associativity followed by evaluation in the second
tensor factor. This is the characterization that determines the diagonal uniquely. -/
public theorem derivedTensorHomDiagonalOverRing_homEquiv {R : Type uR} [CommRing R]
    [HasDerivedCategory.{wR} (ModuleCat.{max uR v} R)]
    (K L M : DerivedCategory (ModuleCat.{max uR v} R)) :
    let d := derivedHomAdjunctionOverRing R
    d.homEquiv _ M (d.tensor.obj (K, L))
        (derivedTensorHomDiagonalOverRing.{uR, v} K L M) =
      (d.tensorAssoc K (d.hom.obj (Opposite.op M, L)) M).hom ≫
        d.tensor.map (𝟙 K, d.evaluation M L) :=
  (derivedHomAdjunctionOverRing R).homEquiv _ M _
    |>.apply_symm_apply _

end Diagonal

section ModelCriterion

attribute [local instance] HasDerivedCategory.standard

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
variable (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
  (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]

/-- A morphism is invertible iff a morphism intertwined with it by isomorphisms is. -/
private theorem isIso_iff_of_comp_eq {C : Type*} [Category C] {X Y X' Y' : C}
    (u : X' ≅ X) (v : Y' ≅ Y) (d : X ⟶ Y) (d' : X' ⟶ Y') (h : u.hom ≫ d = d' ≫ v.hom) :
    IsIso d ↔ IsIso d' :=
  (isIso_comp_left_iff u.hom d).symm.trans
    ((Iff.of_eq (congrArg IsIso h)).trans (isIso_comp_right_iff d' v.hom))

/-- Restriction of scalars along `f` carries the adjoint transpose of the unit-induced comparison
to a composite whose only possibly non-invertible factor is the tensor--Hom diagonal. This is the
equation inside the proof of Stacks 0A6A, isolated so that it can be read in both directions. -/
private theorem restrict_modelUnitComparison_eq_diagonal
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    let U := (ModuleCat.restrictScalars f).mapDerivedCategory
    let B := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
    let H := (Functor.curry.obj (hom R)).obj (Opposite.op (DerivedCategory.Q.obj K))
    let e := Stacks.DerivedHom.BaseChangeIso.modelRestrictionHomIso f F α (DerivedCategory.Q.obj K)
    let b := (Stacks.DerivedHom.BaseChangeIso.scalarAdjunctionWithUnitComparison f F α).1
    let proj := Stacks.DerivedHom.BaseChangeIso.derivedExtensionRestrictionIso f F α
    U.map ((b.homEquiv _ _).symm (H.map (b.unit.app M) ≫ e.hom.app (F.obj M))) =
      proj.hom.app (H.obj M) ≫ diagonal B M (DerivedCategory.Q.obj K) ≫
        H.map (proj.inv.app M) ≫ e.hom.app (F.obj M) := by
  let U := (ModuleCat.restrictScalars f).mapDerivedCategory
  let B := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  let G := (Functor.curry.obj (tensor R)).obj B
  let H := (Functor.curry.obj (hom R)).obj (Opposite.op (DerivedCategory.Q.obj K))
  let J := (Functor.curry.obj (hom A)).obj (Opposite.op (F.obj (DerivedCategory.Q.obj K)))
  let e := Stacks.DerivedHom.BaseChangeIso.modelRestrictionHomIso f F α (DerivedCategory.Q.obj K)
  let b := (Stacks.DerivedHom.BaseChangeIso.scalarAdjunctionWithUnitComparison f F α).1
  let proj := Stacks.DerivedHom.BaseChangeIso.derivedExtensionRestrictionIso f F α
  let δ : H ⋙ G ⟶ G ⋙ H :=
    { app L := diagonal B L (DerivedCategory.Q.obj K)
      naturality {L L'} g := StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural.2.1 g }
  have hlin : G.map (e.hom.app (F.obj M)) ≫ proj.inv.app (U.obj (J.obj (F.obj M))) ≫
      U.map (b.counit.app (J.obj (F.obj M))) =
    δ.app (U.obj (F.obj M)) ≫
      H.map (proj.inv.app (U.obj (F.obj M)) ≫ U.map (b.counit.app (F.obj M))) ≫
        e.hom.app (F.obj M) := by
    obtain ⟨I, q, hq, hI⟩ :=
      CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage (F.obj M))
    let := hq
    let := hI
    let i : DerivedCategory.Q.obj I ≅ F.obj M :=
      (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso (F.obj M)
    exact Stacks.DerivedHom.BaseChangeIso.unitComparison_linear_of_iso b H J e.hom G proj δ i
      (Stacks.DerivedHom.BaseChangeIso.modelComparison_linear_on_injective f F α K hK I)
  exact Stacks.DerivedHom.BaseChangeIso.restrict_unitComparison_eq b H J e.hom G proj δ M hlin

/-- Derived restriction of scalars is conservative, as an equivalence. -/
private theorem isIso_mapDerivedCategory_restrictScalars_iff
    {X Y : DerivedCategory (ModuleCat.{u} A)} (g : X ⟶ Y) :
    IsIso ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.map g) ↔ IsIso g :=
  ⟨fun _ => Stacks.DerivedHom.BaseChangeIso.isIso_of_mapDerivedCategory
    (ModuleCat.restrictScalars.{u, u, u} f) g, fun _ => inferInstance⟩

/-- At a K-flat representative, the unit-induced comparison is invertible exactly when the
tensor--Hom diagonal is. -/
private theorem isIso_modelUnitComparison_iff_diagonal_of_kFlat
    (a : F ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((a.homEquiv _ _).symm
      ((hom R).map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (DerivedCategory.Q.obj K)))
        (a.unit.app M)) ≫
        (Stacks.DerivedHom.BaseChangeIso.modelRestrictionHomIso f F α
          (DerivedCategory.Q.obj K)).hom.app (F.obj M))) ↔
    IsIso (diagonal
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) M (DerivedCategory.Q.obj K)) := by
  let H := (Functor.curry.obj (hom R)).obj (Opposite.op (DerivedCategory.Q.obj K))
  let J := (Functor.curry.obj (hom A)).obj (Opposite.op (F.obj (DerivedCategory.Q.obj K)))
  let e := Stacks.DerivedHom.BaseChangeIso.modelRestrictionHomIso f F α (DerivedCategory.Q.obj K)
  let b := (Stacks.DerivedHom.BaseChangeIso.scalarAdjunctionWithUnitComparison f F α).1
  let proj := Stacks.DerivedHom.BaseChangeIso.derivedExtensionRestrictionIso f F α
  refine (Stacks.DerivedHom.BaseChangeIso.isIso_unitComparison_iff a b H J e.hom M).trans ?_
  refine (isIso_mapDerivedCategory_restrictScalars_iff f
    ((b.homEquiv _ _).symm (H.map (b.unit.app M) ≫ e.hom.app (F.obj M)))).symm.trans ?_
  rw [restrict_modelUnitComparison_eq_diagonal f F α K hK M, isIso_comp_left_iff,
    isIso_comp_right_iff]

/-- The unit-induced comparison is invertible at an arbitrary object exactly when the tensor--Hom
diagonal is. The K-flat hypothesis is removed by a K-flat resolution, using that both sides are
invariant under isomorphisms of the first argument. -/
private theorem isIso_modelUnitComparison_iff_diagonal
    (a : F ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory)
    (K M : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((a.homEquiv _ _).symm
      ((hom R).map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op K)) (a.unit.app M)) ≫
        (Stacks.DerivedHom.BaseChangeIso.modelRestrictionHomIso f F α K).hom.app (F.obj M))) ↔
    IsIso (diagonal
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) M K) := by
  let B := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution (DerivedCategory.Q.objPreimage K)
  have := hp
  let k : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  refine (Stacks.DerivedHom.BaseChangeIso.isIso_modelUnitComparison_iff_of_iso
    f F α a k M).trans ?_
  refine (isIso_modelUnitComparison_iff_diagonal_of_kFlat f F α a P hP M).trans ?_
  let hR := (Functor.curry.obj (hom R)).mapIso k.op
  exact isIso_iff_of_comp_eq ((tensor R).mapIso ((Iso.refl B).prod (hR.app M)))
    (hR.app ((tensor R).obj (B, M))) _ _
    (StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural.2.2 (K := B) (L := M) k.hom)

end ModelCriterion

section Criterion

attribute [local instance] HasDerivedCategory.standard

/-- **The criterion behind Stacks 0A6A, as an equivalence.** The derived-Hom base-change morphism
`RHom_R(K, M) ⊗ᴸ_R A ⟶ RHom_A(K ⊗ᴸ_R A, M ⊗ᴸ_R A)` of Stacks 0E1X is invertible if and only if the
tensor--Hom diagonal of Stacks 0BYN at the algebra, the target and the source is. Stacks 0A6A is
the implication from right to left, applied in four cases; the converse is the half that the proof
of Stacks 0E2A needs. -/
public theorem isIso_derivedHomBaseChange_iff_derivedTensorHomDiagonal
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K M : DerivedCategory (ModuleCat.{max uR uA uM} R)),
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM}
        f F comparison K M) ↔
      (let E :=
         Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA uM} R
       IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
         (E.functor.obj
           ((DerivedCategory.singleFunctor (ModuleCat.{max uR uA uM} R) 0).obj
             ((ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max uR uM} A)))))
         (E.functor.obj M) (E.functor.obj K)) : Prop) := by
  intro F comparison hF K M
  let E :=
    (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max uR uA uM} R).functor
  let B₀ := (DerivedCategory.singleFunctor (ModuleCat.{max uR uA uM} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max uR uM} A)))
  refine Iff.trans
    (@Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange_iff_model.{uR, uA, uM} R A _ _ f
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
      F comparison hF K M) ?_
  let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
    (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
      (ULift.{max uR uA uM} A)) ℤ)
  let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{
    max uR uA uM, max uR uA uM, max uR uA uM} _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
  refine Iff.trans
    (isIso_modelUnitComparison_iff_diagonal f' T.B T.alphaB a' (E.obj K) (E.obj M)) ?_
  let i := Stacks.DerivedHom.BaseChangeIso.modelScalarCoefficientIso.{uR, uA, uM} f
  let H := StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
  let D := StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)
  exact isIso_iff_of_comp_eq (D.mapIso (i.prod (Iso.refl _)))
    (H.mapIso ((Iso.refl (Opposite.op (E.obj K))).prod (D.mapIso (i.prod (Iso.refl _))))) _ _
    (StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural.1
      (L := E.obj M) (M := E.obj K) i.hom)

end Criterion

end Dualizing

end
