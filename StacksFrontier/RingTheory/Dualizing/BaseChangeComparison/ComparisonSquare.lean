module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.MateSquare
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMate

/-!
# Both transposes of the comparison square of Stacks 0E2A

`Dualizing.isIso_derivedHomBaseChange_app_of_isPerfect_of_mateSquare` reduces Stacks 0BZP, and
`Dualizing.isIso_derivedHomBaseChange_app_of_flat_of_mateSquare` the flat case of Stacks 0BZM, to
one equation: the restriction along `R' → A ⊗_R R'` of the base-change morphism of Stacks 0E29 is,
under the two identifications `Dualizing.mateSourceIso` and `Dualizing.mateTargetIso`, the
derived-Hom base-change morphism of Stacks 0E1X. This file transposes both sides of that equation
under the tensor--Hom adjunction of Stacks 0A63 over `R'` and computes each transpose, so that the
equation becomes a compatibility between the two projection formulas — one at `R → A`, one at
`R' → A ⊗_R R'` — the lax monoidal structure map of derived base change, the base change of the
algebra, and the comparison of Stacks 0661. Neither transpose mentions the morphism of
Stacks 0E29, the morphism of Stacks 0E1X, or either bridge.

The common mechanism is that both identifications are built from
`Dualizing.derivedHomRestrictScalarsInternalHomIso`, which is an `Adjunction.rightAdjointUniq`;
its transpose is therefore computed by `Adjunction.homEquiv_symm_rightAdjointUniq_hom_app`, and
what comes out is the inverse of the identification of the *left* adjoints — the projection
formula `Dualizing.derivedExtendRestrictScalarsTensorIso` — followed by the counit of derived
extension of scalars and the evaluation counit of Stacks 0A70. All of that is carried out for an
arbitrary derived tensor--Hom adjunction and an arbitrary pair of adjunctions, since none of it is
particular to modules.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_rightAdjointUniq_hom_app` and
  `.tensorAt_map_comp_homEquiv_rightAdjointUniq_hom_app` — the transpose of a bridge isomorphism
  obtained from uniqueness of right adjoints, with and without a morphism in front.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_map_comp_rightAdjointUniq_comp_hom_map` —
  the abstract form of the left-hand transpose, with the triangle identity of the transposed
  morphism as a hypothesis.
* `homEquiv_comp_rightAdjointUniq_comp_homEquiv_symm_app`, in the same namespace — the abstract
  form of the right-hand transpose, in which the internal-Hom comparison becomes the lax tensor
  comparison of
  `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate`.
* `Dualizing.homEquiv_restrictScalars_derivedHomBaseChange_comp_targetIso` — the left-hand
  transpose of the square of Stacks 0E2A.
* `Dualizing.homEquiv_sourceIso_comp_derivedHomBaseChange` — the right-hand transpose.
* `Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility` — the
  square itself, from the equality of the two transposes.

## Implementation notes

The two models of derived extension of scalars appearing in the bridges are arguments, so the
statements below are not tied to the canonical model that
`Dualizing.derivedHomRestrictScalarsInternalHomIsoCanonical`, hence `Dualizing.mateSourceIso` and
`Dualizing.mateTargetIso`, happen to use; the conclusion of
`Dualizing.restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility` is in the
shape that `Dualizing.isIso_derivedHomBaseChange_app_of_comparison` consumes, which takes the two
identifications as arguments, so no instantiation at the canonical model is needed.

Source and target of several composites here are definitionally but not syntactically equal —
`(d.homAt L).obj M` against `d.hom.obj (op L, M)`, `(d.tensorAt L).obj X` against
`d.tensor.obj (X, L)`, and the `@[no_expose]` crossing of
`StacksDraft.DerivedHom.derivedHomAdjunction`. Across such a crossing `rw` fails, because its
motive is type-checked at `implicit` transparency; the steps below are therefore chained with
`Eq.trans` and `congrArg`, which elaborate at default transparency.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open scoped ChangeOfRings

universe uR uA uRp v v' w w' u₁ v₁

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

section Abstract

variable {R : Type uR} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)

/-- Tensoring with a fixed object on the right, read off the bifunctor. -/
theorem tensorAt_map (L : DerivedCategory (ModuleCat.{v} R))
    {X Y : DerivedCategory (ModuleCat.{v} R)} (a : X ⟶ Y) :
    (d.tensorAt L).map a = d.tensor.map ((a, 𝟙 L) : (X, L) ⟶ (Y, L)) :=
  rfl

/-- The transpose of a morphism into an internal Hom is tensoring followed by evaluation. -/
theorem homEquiv_eq_tensor_map_comp_evaluation
    (K L M : DerivedCategory (ModuleCat.{v} R)) (a : K ⟶ d.hom.obj (Opposite.op L, M)) :
    d.homEquiv K L M a =
      d.tensor.map ((a, 𝟙 L) : (K, L) ⟶ (d.hom.obj (Opposite.op L, M), L)) ≫
        d.evaluation L M := by
  have h := d.homEquiv_naturality_left a (𝟙 (d.hom.obj (Opposite.op L, M)))
  rw [Category.comp_id] at h
  exact h

/-- The transpose of `tensorHomAdjunctionAt` is the transpose of the tensor--Hom adjunction. -/
theorem tensorHomAdjunctionAt_homEquiv_symm_apply
    (L K M : DerivedCategory (ModuleCat.{v} R)) (a : K ⟶ (d.homAt L).obj M) :
    ((d.tensorHomAdjunctionAt L).homEquiv K M).symm a = d.homEquiv K L M a :=
  (d.homEquiv_eq_tensor_map_comp_evaluation K L M a).symm

end Abstract

section Bridge

variable {R : Type uR} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)
  {𝒟 : Type u₁} [Category.{v₁} 𝒟]
  {Ex : DerivedCategory (ModuleCat.{v} R) ⥤ 𝒟}
  {U : 𝒟 ⥤ DerivedCategory (ModuleCat.{v} R)}
  {Hm : DerivedCategory (ModuleCat.{v} R) ⥤ 𝒟}
  (aExt : Ex ⊣ U) (aHom : U ⊣ Hm)
  {L : DerivedCategory (ModuleCat.{v} R)}
  (tensorIso : Ex ⋙ U ≅ d.tensorAt L)

/-- **The transpose of a bridge isomorphism.** Let `Ex ⊣ U` and `U ⊣ Hm` be adjunctions and let
`tensorIso` identify `Ex ⋙ U` with the derived tensor product by a fixed object `L`. Then
`Hm ⋙ U` is identified with the derived internal Hom out of `L` by uniqueness of right adjoints,
and the transpose of that identification under the tensor--Hom adjunction is the inverse of
`tensorIso` followed by the two counits. -/
theorem homEquiv_rightAdjointUniq_hom_app (M : DerivedCategory (ModuleCat.{v} R)) :
    d.homEquiv (U.obj (Hm.obj M)) L M
        ((Adjunction.rightAdjointUniq (aExt.comp aHom)
          ((d.tensorHomAdjunctionAt L).ofNatIsoLeft tensorIso.symm)).hom.app M) =
      tensorIso.inv.app (U.obj (Hm.obj M)) ≫
        U.map (aExt.counit.app (Hm.obj M)) ≫ aHom.counit.app M := by
  have key := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app (aExt.comp aHom)
    ((d.tensorHomAdjunctionAt L).ofNatIsoLeft tensorIso.symm) M
  rw [Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    d.tensorHomAdjunctionAt_homEquiv_symm_apply, Adjunction.comp_counit_app] at key
  rw [← key]
  exact (Iso.inv_hom_id_app_assoc tensorIso _ _).symm

/-- `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_rightAdjointUniq_hom_app` with a
morphism tensored in front, moved across `tensorIso` by naturality. -/
theorem tensorAt_map_comp_homEquiv_rightAdjointUniq_hom_app
    {X M : DerivedCategory (ModuleCat.{v} R)} (w : X ⟶ U.obj (Hm.obj M)) :
    (d.tensorAt L).map w ≫
        d.homEquiv (U.obj (Hm.obj M)) L M
          ((Adjunction.rightAdjointUniq (aExt.comp aHom)
            ((d.tensorHomAdjunctionAt L).ofNatIsoLeft tensorIso.symm)).hom.app M) =
      tensorIso.inv.app X ≫
        U.map (Ex.map w ≫ aExt.counit.app (Hm.obj M)) ≫ aHom.counit.app M := by
  rw [d.homEquiv_rightAdjointUniq_hom_app aExt aHom tensorIso M, ← Category.assoc,
    tensorIso.inv.naturality w]
  simp

/-- **The transpose of a morphism into a bridge, transported along an identification of the
tensor factor.** This is the shape in which the restricted morphism of Stacks 0E29 meets the
target identification of Stacks 0E2A: the hypothesis `hc` is the triangle identity defining that
morphism. -/
theorem homEquiv_map_comp_rightAdjointUniq_comp_hom_map
    {N : 𝒟} {M : DerivedCategory (ModuleCat.{v} R)} (τ : N ⟶ Hm.obj M)
    {Y : DerivedCategory (ModuleCat.{v} R)} (θ : Y ≅ L) (c : U.obj N ⟶ M)
    (hc : U.map τ ≫ aHom.counit.app M = c) :
    d.homEquiv (U.obj N) Y M
        (U.map τ ≫ (Adjunction.rightAdjointUniq (aExt.comp aHom)
              ((d.tensorHomAdjunctionAt L).ofNatIsoLeft tensorIso.symm)).hom.app M ≫
            d.hom.map ((θ.hom.op, 𝟙 M) :
              (Opposite.op L, M) ⟶ (Opposite.op Y, M))) =
      d.tensor.map ((𝟙 (U.obj N), θ.hom) : (U.obj N, Y) ⟶ (U.obj N, L)) ≫
        tensorIso.inv.app (U.obj N) ≫ U.map (aExt.counit.app N) ≫ c := by
  have hswap : d.tensor.map ((U.map τ, 𝟙 Y) :
          (U.obj N, Y) ⟶ (U.obj (Hm.obj M), Y)) ≫
        d.tensor.map ((𝟙 (U.obj (Hm.obj M)), θ.hom) :
          (U.obj (Hm.obj M), Y) ⟶ (U.obj (Hm.obj M), L)) =
      d.tensor.map ((𝟙 (U.obj N), θ.hom) : (U.obj N, Y) ⟶ (U.obj N, L)) ≫
        d.tensor.map ((U.map τ, 𝟙 L) : (U.obj N, L) ⟶ (U.obj (Hm.obj M), L)) := by
    rw [d.tensor_map_comp, d.tensor_map_comp]
    congr 1
    simp
  refine Eq.trans (d.homEquiv_naturality_left (U.map τ) _) ?_
  refine Eq.trans (congrArg (fun z => d.tensor.map ((U.map τ, 𝟙 Y) :
      (U.obj N, Y) ⟶ (U.obj (Hm.obj M), Y)) ≫ z)
    (d.homEquiv_dinaturality θ.hom ((Adjunction.rightAdjointUniq (aExt.comp aHom)
      ((d.tensorHomAdjunctionAt L).ofNatIsoLeft tensorIso.symm)).hom.app M))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ d.homEquiv (U.obj (Hm.obj M)) L M
    ((Adjunction.rightAdjointUniq (aExt.comp aHom)
      ((d.tensorHomAdjunctionAt L).ofNatIsoLeft tensorIso.symm)).hom.app M)) hswap) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun z => d.tensor.map ((𝟙 (U.obj N), θ.hom) :
      (U.obj N, Y) ⟶ (U.obj N, L)) ≫ z) ?_
  refine Eq.trans (d.tensorAt_map_comp_homEquiv_rightAdjointUniq_hom_app aExt aHom tensorIso
    (U.map τ)) ?_
  refine congrArg (fun z => tensorIso.inv.app (U.obj N) ≫ z) ?_
  refine Eq.trans (congrArg (fun z => U.map z ≫ aHom.counit.app M)
    (aExt.counit.naturality τ)) ?_
  refine Eq.trans (congrArg (fun z => z ≫ aHom.counit.app M) (U.map_comp _ _)) ?_
  exact (Category.assoc _ _ _).trans (congrArg (fun z => U.map (aExt.counit.app N) ≫ z) hc)

end Bridge

section SourceTranspose

variable {R : Type uR} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  {R' : Type uRp} [CommRing R'] [HasDerivedCategory.{w'} (ModuleCat.{v'} R')]
  (d : DerivedHomAdjunction R) (d' : DerivedHomAdjunction R')
  {F : DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v'} R')}
  {Gr : DerivedCategory (ModuleCat.{v'} R') ⥤ DerivedCategory (ModuleCat.{v} R)}
  (a : F ⊣ Gr) (m : d.hom ⟶ F.op.prod F ⋙ d'.hom ⋙ Gr)
  {𝒟 : Type u₁} [Category.{v₁} 𝒟]
  {Ex : DerivedCategory (ModuleCat.{v} R) ⥤ 𝒟}
  {U : 𝒟 ⥤ DerivedCategory (ModuleCat.{v} R)}
  {Hm : DerivedCategory (ModuleCat.{v} R) ⥤ 𝒟}
  (aExt : Ex ⊣ U) (aHom : U ⊣ Hm)
  {L : DerivedCategory (ModuleCat.{v} R)}
  (tensorIso : Ex ⋙ U ≅ d.tensorAt L)

/-- **The transpose of the composite of a bridge with an internal-Hom comparison.** The mate of
`m` at `(L, K)`, preceded by `F` applied to the bridge isomorphism and by an arbitrary morphism
`u`, becomes under the tensor--Hom adjunction over `R'` the lax tensor comparison, preceded by
`u` and followed by `F` applied to the inverse of the left-adjoint identification and to the two
counits. -/
theorem homEquiv_comp_rightAdjointUniq_comp_homEquiv_symm_app
    (K : DerivedCategory (ModuleCat.{v} R))
    {X : DerivedCategory (ModuleCat.{v'} R')} (u : X ⟶ F.obj (U.obj (Hm.obj K))) :
    d'.homEquiv X (F.obj L) (F.obj K)
        ((u ≫ F.map ((Adjunction.rightAdjointUniq (aExt.comp aHom)
              ((d.tensorHomAdjunctionAt L).ofNatIsoLeft tensorIso.symm)).hom.app K)) ≫
          (a.homEquiv ((d.homAt L).obj K)
              (d'.hom.obj (Opposite.op (F.obj L), F.obj K))).symm
            (m.app (Opposite.op L, K))) =
      d'.tensor.map ((u, 𝟙 (F.obj L)) :
          (X, F.obj L) ⟶ (F.obj (U.obj (Hm.obj K)), F.obj L)) ≫
        laxTensorOfHomMate d d' a m (U.obj (Hm.obj K)) L ≫
          F.map (tensorIso.inv.app (U.obj (Hm.obj K)) ≫
            U.map (aExt.counit.app (Hm.obj K)) ≫ aHom.counit.app K) := by
  have hnat := laxTensorOfHomMate_naturality d d' a m
    ((Adjunction.rightAdjointUniq (aExt.comp aHom)
      ((d.tensorHomAdjunctionAt L).ofNatIsoLeft tensorIso.symm)).hom.app K) (𝟙 L)
  rw [CategoryTheory.Functor.map_id] at hnat
  refine Eq.trans (congrArg (d'.homEquiv X (F.obj L) (F.obj K)) (Category.assoc _ _ _)) ?_
  refine Eq.trans (d'.homEquiv_naturality_left u _) ?_
  refine Eq.trans (congrArg (fun z => d'.tensor.map ((u, 𝟙 (F.obj L)) :
      (X, F.obj L) ⟶ (F.obj (U.obj (Hm.obj K)), F.obj L)) ≫ z)
    ((d'.homEquiv_naturality_left _ _).trans
      (congrArg (fun z => d'.tensor.map ((F.map ((Adjunction.rightAdjointUniq (aExt.comp aHom)
          ((d.tensorHomAdjunctionAt L).ofNatIsoLeft tensorIso.symm)).hom.app K), 𝟙 (F.obj L)) :
          (F.obj (U.obj (Hm.obj K)), F.obj L) ⟶ (F.obj ((d.homAt L).obj K), F.obj L)) ≫ z)
        (homEquiv_laxTensorOfHomMate d d' a m L K)))) ?_
  refine congrArg (fun z => d'.tensor.map ((u, 𝟙 (F.obj L)) :
      (X, F.obj L) ⟶ (F.obj (U.obj (Hm.obj K)), F.obj L)) ≫ z) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ F.map (d.evaluation L K)) hnat) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun z => laxTensorOfHomMate d d' a m (U.obj (Hm.obj K)) L ≫ z) ?_
  refine Eq.trans (F.map_comp _ _).symm (congrArg F.map ?_)
  exact (d.homEquiv_eq_tensor_map_comp_evaluation _ L K _).symm.trans
    (d.homEquiv_rightAdjointUniq_hom_app aExt aHom tensorIso K)

end SourceTranspose

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] extendScalarsAdditiveOfRingHom

section Bridge

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤ DerivedCategory (ModuleCat.{max v uR uA} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]

/-- The transpose of the bridge of Stacks 0E2A, with a morphism in front. -/
theorem tensorAt_map_comp_homEquiv_bridge
    {X M : DerivedCategory (ModuleCat.{max v uR uA} R)}
    (w : X ⟶ (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj
      ((derivedHom.{uR, v, uA} f).obj M)) :
    ((derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensorAt
          (derivedAlgebraSingle.{uR, uA, v} f)).map w ≫
        (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).homEquiv
          ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj
            ((derivedHom.{uR, v, uA} f).obj M))
          (derivedAlgebraSingle.{uR, uA, v} f) M
          ((derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, v} f F
            comparison).hom.app M) =
      (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).inv.app X ≫
        (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map
            (F.map w ≫
              (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, v}
                f F comparison).counit.app ((derivedHom.{uR, v, uA} f).obj M)) ≫
          (derivedHomAdjunction.{uR, uA, v} f).counit.app M :=
  DerivedHomAdjunction.tensorAt_map_comp_homEquiv_rightAdjointUniq_hom_app _ _ _ _ w

/-- The transpose of the bridge of Stacks 0E2A: it is the inverse projection formula followed by
the counit of derived extension of scalars and the evaluation counit of Stacks 0A70. -/
theorem homEquiv_bridge (M : DerivedCategory (ModuleCat.{max v uR uA} R)) :
    (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).homEquiv
        ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj
          ((derivedHom.{uR, v, uA} f).obj M))
        (derivedAlgebraSingle.{uR, uA, v} f) M
        ((derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, v} f F
          comparison).hom.app M) =
      (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).inv.app
          ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.obj
            ((derivedHom.{uR, v, uA} f).obj M)) ≫
        (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory.map
            ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, v}
              f F comparison).counit.app ((derivedHom.{uR, v, uA} f).obj M)) ≫
          (derivedHomAdjunction.{uR, uA, v} f).counit.app M :=
  DerivedHomAdjunction.homEquiv_rightAdjointUniq_hom_app _ _ _ _ M

end Bridge

section Square

attribute [local instance] Algebra.TensorProduct.rightAlgebra

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

/-- **The transpose of the right-hand side of the comparison square of Stacks 0E2A.** The
derived-Hom base-change morphism of Stacks 0E1X, preceded by the source identification, becomes
under the tensor--Hom adjunction of Stacks 0A63 over `R'` the lax monoidal structure map of
derived base change, preceded by the restriction/base-change identification of Stacks 0661 and
followed by the base change of the projection formula and of the two counits over `R → A`. -/
theorem homEquiv_sourceIso_comp_derivedHomBaseChange
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').homEquiv
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
          (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)))
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
        (baseChangeR.obj K)
        (((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
              comparisonA isLeftDerivedA).hom.app K ≫
            baseChangeR.map
              ((derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, max v uRp}
                (algebraMap R A) Ff alphaf).hom.app K)) ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap
            R R')
            baseChangeR comparisonR
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          (((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
                comparisonA isLeftDerivedA).hom.app K,
              𝟙 (baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj
                    ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          baseChangeR.map
            ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).inv.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map
                ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR,
                    uA, max v uRp} (algebraMap R A) Ff alphaf).counit.app
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K) :=
  DerivedHomAdjunction.homEquiv_comp_rightAdjointUniq_comp_homEquiv_symm_app
    (derivedHomAdjunctionOverRing.{uR, max v uR uA uRp, max v uR uA uRp + 1} R)
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R')
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uRp, max v uA}
      (algebraMap R R') baseChangeR comparisonR)
    (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate.{uR, uRp, max v uA}
      (algebraMap R R') baseChangeR comparisonR)
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, max v uRp}
      (algebraMap R A) Ff alphaf)
    (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A))
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
    K _

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

/-- **The transpose of the left-hand side of the comparison square of Stacks 0E2A.** The
restriction along `R' → A ⊗_R R'` of the morphism of Stacks 0E29, followed by the target
identification, becomes under the tensor--Hom adjunction of Stacks 0A63 over `R'` the base change
of the algebra, the inverse projection formula over `R' → A ⊗_R R'`, the counit of derived
extension of scalars there, and the derived base change of the evaluation counit over `R → A`. -/
theorem homEquiv_restrictScalars_derivedHomBaseChange_comp_targetIso
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').homEquiv
        ((ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
          (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)))
        (baseChangeR.obj (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))
        (baseChangeR.obj K)
        ((ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
            ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
              baseChangeA comparisonA isLeftDerivedA).app K) ≫
          ((derivedHomRestrictScalarsInternalHomIsoOfModel.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
              (baseChangeR.obj K) ≫
            (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                max v uR uA uRp + 1} R').hom.map
              (((derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
                      baseChangeA comparisonA isLeftDerivedA).hom.op,
                  𝟙 (baseChangeR.obj K)) :
                (Opposite.op (derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                    (Algebra.TensorProduct.includeRight :
                      R' →ₐ[R] TensorProduct R A R').toRingHom),
                  baseChangeR.obj K) ⟶
                  (Opposite.op (baseChangeR.obj
                      (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))),
                    baseChangeR.obj K)))) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((𝟙 ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
                baseChangeA comparisonA isLeftDerivedA).hom) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                  (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
        (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).inv.app
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
          (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uRp,
                  max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
            ((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
                  comparisonA isLeftDerivedA).hom.app K ≫
              baseChangeR.map
                ((derivedHomAdjunction.{uR, uA, max v uRp}
                  (algebraMap R A)).counit.app K)) :=
  DerivedHomAdjunction.homEquiv_map_comp_rightAdjointUniq_comp_hom_map
    (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R')
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uRp, max uA uRp,
      max v uR} (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    (derivedHomAdjunction.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom)
    (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
    ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K)
    (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
      comparisonA isLeftDerivedA)
    _
    (restrictScalars_map_derivedHomBaseChange_app_comp_counit hTor baseChangeR comparisonR
      isLeftDerivedR baseChangeA comparisonA isLeftDerivedA K)

/-- **The comparison square of Stacks 0E2A, reduced to a compatibility of the two projection
formulas.** The hypothesis `hProj` is the equality of the two transposes computed by
`Dualizing.homEquiv_restrictScalars_derivedHomBaseChange_comp_targetIso` and by
`Dualizing.homEquiv_sourceIso_comp_derivedHomBaseChange`. It mentions neither the morphism of
Stacks 0E29, nor the one of Stacks 0E1X, nor either bridge of Stacks 0E2A: only the lax monoidal
structure map of derived base change, the two projection formulas at `R → A` and at
`R' → A ⊗_R R'`, the base change of the algebra, the counits of derived extension of scalars and
the restriction/base-change identification of Stacks 0661 occur in it.

Combined with `Dualizing.isIso_derivedHomBaseChange_app_of_comparison` this gives Stacks 0BZP and
the flat case of Stacks 0BZM. -/
theorem restrictScalars_map_derivedHomBaseChange_app_eq_of_projectionCompatibility
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hProj :
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          ((𝟙 ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
                baseChangeA comparisonA isLeftDerivedA).hom) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              ((ModuleCat.restrictScalars
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                  (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) ≫
        (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).inv.app
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
              (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
          (ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uRp,
                  max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).counit.app
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))) ≫
            ((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
                  comparisonA isLeftDerivedA).hom.app K ≫
              baseChangeR.map
                ((derivedHomAdjunction.{uR, uA, max v uRp}
                  (algebraMap R A)).counit.app K)) =
      (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp, max v uR uA uRp + 1} R').tensor.map
          (((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
                comparisonA isLeftDerivedA).hom.app K,
              𝟙 (baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) :
            ((ModuleCat.restrictScalars
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.obj
                (baseChangeA.obj ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
              baseChangeR.obj
                (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj
                  ((ModuleCat.restrictScalars.{max v uR uA uRp}
                      (algebraMap R A)).mapDerivedCategory.obj
                    ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)),
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))) ≫
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
            ((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory.obj
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K))
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          baseChangeR.map
            ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff
                  alphaf).inv.app
                ((ModuleCat.restrictScalars.{max v uR uA uRp}
                    (algebraMap R A)).mapDerivedCategory.obj
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (algebraMap R A)).mapDerivedCategory.map
                ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR,
                    uA, max v uRp} (algebraMap R A) Ff alphaf).counit.app
                  ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).obj K)) ≫
              (derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K)) :
    (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
        ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
          baseChangeA comparisonA isLeftDerivedA).app K) =
      ((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA
              comparisonA isLeftDerivedA).app K ≪≫
          baseChangeR.mapIso
            ((derivedHomRestrictScalarsInternalHomIsoOfModel.{uR, uA, max v uRp}
              (algebraMap R A) Ff alphaf).app K)).hom ≫
        Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap R
          R')
            baseChangeR comparisonR
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) K ≫
          ((derivedHomRestrictScalarsInternalHomIsoOfModel.{uRp, max uA uRp, max v uR}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).app
              (baseChangeR.obj K) ≪≫
            (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                max v uR uA uRp + 1} R').hom.mapIso
              (Iso.prod
                (Iso.op (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR isLeftDerivedR
                  baseChangeA comparisonA isLeftDerivedA))
                (Iso.refl (baseChangeR.obj K)))).inv := by
  have h := ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
      max v uR uA uRp + 1} R').homEquiv _ _ _).injective
    ((homEquiv_restrictScalars_derivedHomBaseChange_comp_targetIso hTor baseChangeR comparisonR
        isLeftDerivedR baseChangeA comparisonA isLeftDerivedA Fi alphai K).trans
      (hProj.trans (homEquiv_sourceIso_comp_derivedHomBaseChange hTor baseChangeR comparisonR
        isLeftDerivedR baseChangeA comparisonA isLeftDerivedA Ff alphaf K).symm))
  exact ((Iso.eq_comp_inv _).2 h).trans (Category.assoc _ _ _)

end Square

end Dualizing

end
