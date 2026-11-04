module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Basic

/-!
# The derived-Hom base-change map is the mate of a tensor comparison

Let `f : R → A` be a homomorphism of commutative rings and let `F : D(R) ⥤ D(A)` be a model of
derived extension of scalars. The derived-Hom base-change map of Stacks 0E1X is a morphism

`F(RHom_R(L, K)) ⟶ RHom_A(F L, F K)`

in `D(A)`. This file exhibits it as the mate, under the tensor--Hom adjunctions of Stacks 0A63
over `R` and over `A`, of a *lax monoidal structure map* for `F`

`μ_{X,Y} : F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)`,

and records the equation that identifies the two. That equation is what makes the base-change map
computable: it rewrites `RHom`-base change as a tensor comparison followed by evaluation, which is
the form needed to attack the one remaining commuting square of Stacks 0E2A
(the `hComparison` hypothesis of
`Dualizing.isIso_derivedHomBaseChange_app_of_isPerfect_of_mateSquare`).

The construction is carried out for an arbitrary adjunction and an arbitrary comparison of
internal-Hom bifunctors, and then specialized; the general statements are the ones that carry the
mathematics.

## Main definitions

* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomUnit` — the coevaluation
  `K ⟶ RHom(L, K ⊗ᴸ L)` of a derived tensor--Hom adjunction, i.e. the unit of
  `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomAdjunctionAt`.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate` — for an adjunction
  `F ⊣ G` and a comparison `m` of the two internal-Hom bifunctors, the induced lax tensor
  comparison `F X ⊗ᴸ F Y ⟶ F (X ⊗ᴸ Y)`.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMateSquare` — the same with the
  second argument fixed, as a natural transformation of endofunctor composites.
* `Dualizing.derivedTensorBaseChange` — the lax monoidal structure map `μ` of derived base change,
  in the tensor vocabulary of Stacks 0A63.
* `Dualizing.derivedTensorBaseChangeSquare` — `μ` with its second argument fixed.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomUnit_comp_map_evaluation`,
  `.tensorHomUnit_naturality` — the triangle identity and the bivariant naturality of
  coevaluation.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_laxTensorOfHomMate` — the abstract
  identification: the transpose of `m` at `(L, K)` is the lax tensor comparison followed by
  `F` applied to evaluation.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_naturality` — the lax tensor
  comparison is natural in both variables.
* `Dualizing.derivedTensorBaseChange_mate` — **the identification for derived base change.**
  The transpose of the base-change map of Stacks 0E1X under the tensor--Hom adjunction over `A`
  is `μ` followed by `F` applied to evaluation over `R`.
* `Dualizing.derivedTensorBaseChange_mate_symm` — the same equation solved for the base-change
  map itself.
* `Dualizing.derivedTensorBaseChange_naturality` — `μ` is natural in both variables.

## Implementation notes

`μ` is *not* built from the monoidality of derived base change of Stacks 068I
(`CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso`). That statement is phrased for
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral` data, of which the library has no
instance at independent ring and module universes, whereas the tensor bifunctor of Stacks 0A63 is
`StacksDraft.DerivedHom.DerivedHomAdjunction.transport`ed along `uliftDerivedEquivalence`; the two
vocabularies are still unbridged. Instead `μ` is obtained from data that *is* available at these
universes: the coevaluation of Stacks 0A63 over `R`, the unit of the adjunction of Stacks 0GMT,
and the change-of-rings isomorphism of Stacks 0E1W — the last two packaged as
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate`. Concretely `μ_{X,Y}` is the
  transpose over `A` of the
transpose over `f` of

`X ⟶ RHom_R(Y, X ⊗ᴸ_R Y) ⟶ Res RHom_A(F Y, F(X ⊗ᴸ_R Y))`.

So `μ` is canonical.  It is also invertible:
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeStrong` proves `μ`
invertible outright — `Dualizing.isIso_derivedTensorBaseChange`, with
`Dualizing.derivedTensorBaseChangeSection` as an explicit two-sided inverse — with no appeal to
Stacks 068I and no K-flat representative; its only input is that the change-of-rings isomorphism
of Stacks 0E1W is an isomorphism, which it is unconditionally.  What a bridge to Stacks 068I would
still buy is a *chain-level value* for `μ`, not its invertibility.

The internal-Hom bifunctor of `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` is
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom` on the nose
(`Dualizing.derivedHomAdjunctionOverRing_hom_eq`), which is what lets the statements below mix the
0A63 vocabulary with the 0E1W/0E1X one with no comparison map. The module universe is taken above
both ring universes, as it is in `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange`.

The abstract counterpart `Stacks.DerivedHom.ExtensionOfScalars.internalHomBaseChange` — the mate of
`Stacks.DerivedHom.ExtensionOfScalars.tensorLeftComparison` for a lax monoidal functor between
  closed monoidal categories —
is not usable here: `D(R)` carries no `MonoidalCategory` instance in these universes, which is the
whole reason the tensor--Hom adjunction of Stacks 0A63 is a bundled datum rather than a typeclass.

## References

* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open scoped ChangeOfRings

universe uR uA uM v v' w w'

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

section Coevaluation

variable {R : Type uR} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R)

/-- The coevaluation `K ⟶ RHom(L, K ⊗ᴸ L)` of a derived tensor--Hom adjunction: the transpose of
the identity of `K ⊗ᴸ L`. It is the unit of
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomAdjunctionAt`, whose counit is
`StacksDraft.DerivedHom.DerivedHomAdjunction.evaluation`. -/
noncomputable def tensorHomUnit (K L : DerivedCategory (ModuleCat.{v} R)) :
    K ⟶ d.hom.obj (Opposite.op L, d.tensor.obj (K, L)) :=
  (d.homEquiv K L (d.tensor.obj (K, L))).symm (𝟙 _)

/-- Coevaluation is the unit of the tensor--Hom adjunction at a fixed object. -/
theorem tensorHomUnit_eq_unit (K L : DerivedCategory (ModuleCat.{v} R)) :
    d.tensorHomUnit K L = (d.tensorHomAdjunctionAt L).unit.app K :=
  rfl

/-- Evaluation is the counit of the tensor--Hom adjunction at a fixed object. -/
theorem evaluation_eq_counit (L M : DerivedCategory (ModuleCat.{v} R)) :
    d.evaluation L M = (d.tensorHomAdjunctionAt L).counit.app M :=
  rfl

/-- The triangle identity of the tensor--Hom adjunction, read in the raw bifunctor spelling:
coevaluation out of `RHom(L, M)`, followed by `RHom(L, -)` applied to evaluation, is the
identity. -/
@[reassoc]
theorem tensorHomUnit_comp_map_evaluation (L M : DerivedCategory (ModuleCat.{v} R)) :
    d.tensorHomUnit (d.hom.obj (Opposite.op L, M)) L ≫
        d.hom.map ((𝟙 (Opposite.op L), d.evaluation L M) :
          (Opposite.op L, d.tensor.obj (d.hom.obj (Opposite.op L, M), L)) ⟶
            (Opposite.op L, M)) = 𝟙 _ :=
  (d.tensorHomAdjunctionAt L).right_triangle_components M

/-- Coevaluation is natural covariantly in the tensor factor and contravariantly in the
internal-Hom source; the two appear on opposite sides of the equation because the same object
plays both roles. -/
@[reassoc]
theorem tensorHomUnit_naturality
    {X X' Y Y' : DerivedCategory (ModuleCat.{v} R)} (x : X ⟶ X') (y : Y ⟶ Y') :
    d.tensorHomUnit X Y ≫
        d.hom.map ((𝟙 (Opposite.op Y), d.tensor.map ((x, y) : (X, Y) ⟶ (X', Y'))) :
          (Opposite.op Y, d.tensor.obj (X, Y)) ⟶ (Opposite.op Y, d.tensor.obj (X', Y'))) =
      x ≫ d.tensorHomUnit X' Y' ≫ d.hom.map ((y.op, 𝟙 (d.tensor.obj (X', Y'))) :
        (Opposite.op Y', d.tensor.obj (X', Y')) ⟶ (Opposite.op Y, d.tensor.obj (X', Y'))) := by
  apply (d.homEquiv X Y (d.tensor.obj (X', Y'))).injective
  rw [d.homEquiv_naturality_right, d.homEquiv_naturality_left, d.homEquiv_dinaturality,
    tensorHomUnit, tensorHomUnit]
  simp only [AddEquiv.apply_symm_apply, Category.id_comp]
  rw [Category.comp_id, ← d.tensor.map_comp]
  congr 1
  simp

end Coevaluation

section Mate

variable {R : Type uR} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  {A : Type uA} [CommRing A] [HasDerivedCategory.{w'} (ModuleCat.{v'} A)]
  (d : DerivedHomAdjunction R) (d' : DerivedHomAdjunction A)
  {F : DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v'} A)}
  {G : DerivedCategory (ModuleCat.{v'} A) ⥤ DerivedCategory (ModuleCat.{v} R)}
  (a : F ⊣ G)
  (m : d.hom ⟶ F.op.prod F ⋙ d'.hom ⋙ G)

/-- Naturality of a comparison `m` of internal-Hom bifunctors at a morphism `(u, v)`. -/
private theorem mate_naturality {Y Y' K K' : DerivedCategory (ModuleCat.{v} R)}
    (u : Opposite.op Y' ⟶ Opposite.op Y) (v : K ⟶ K') :
    m.app (Opposite.op Y', K) ≫ G.map (d'.hom.map
        ((F.op.map u, F.map v) : (Opposite.op (F.obj Y'), F.obj K) ⟶
          (Opposite.op (F.obj Y), F.obj K'))) =
      d.hom.map ((u, v) : (Opposite.op Y', K) ⟶ (Opposite.op Y, K')) ≫
        m.app (Opposite.op Y, K') :=
  (m.naturality ((u, v) : (Opposite.op Y', K) ⟶ (Opposite.op Y, K'))).symm

/-- The lax tensor comparison induced by a comparison `m` of internal-Hom bifunctors along an
adjunction `F ⊣ G`: the transpose over `A` of the transpose along `a` of coevaluation followed by
`m`. -/
noncomputable def laxTensorOfHomMate (X Y : DerivedCategory (ModuleCat.{v} R)) :
    d'.tensor.obj (F.obj X, F.obj Y) ⟶ F.obj (d.tensor.obj (X, Y)) :=
  d'.homEquiv (F.obj X) (F.obj Y) (F.obj (d.tensor.obj (X, Y)))
    ((a.homEquiv X (d'.hom.obj (Opposite.op (F.obj Y), F.obj (d.tensor.obj (X, Y))))).symm
      (d.tensorHomUnit X Y ≫ m.app (Opposite.op Y, d.tensor.obj (X, Y))))

/-- **The mate identity.** The transpose along `a` of the component of `m` at `(L, K)` — i.e. the
induced comparison `F (RHom(L, K)) ⟶ RHom(F L, F K)` — becomes, after transposing over `A`, the
lax tensor comparison followed by `F` applied to evaluation. -/
theorem homEquiv_laxTensorOfHomMate (L K : DerivedCategory (ModuleCat.{v} R)) :
    d'.homEquiv (F.obj (d.hom.obj (Opposite.op L, K))) (F.obj L) (F.obj K)
        ((a.homEquiv (d.hom.obj (Opposite.op L, K))
            (d'.hom.obj (Opposite.op (F.obj L), F.obj K))).symm
          (m.app (Opposite.op L, K))) =
      laxTensorOfHomMate d d' a m (d.hom.obj (Opposite.op L, K)) L ≫
        F.map (d.evaluation L K) := by
  have hkey : (a.homEquiv (d.hom.obj (Opposite.op L, K))
        (d'.hom.obj (Opposite.op (F.obj L), F.obj K))).symm (m.app (Opposite.op L, K)) =
      (a.homEquiv (d.hom.obj (Opposite.op L, K))
          (d'.hom.obj (Opposite.op (F.obj L),
            F.obj (d.tensor.obj (d.hom.obj (Opposite.op L, K), L))))).symm
          (d.tensorHomUnit (d.hom.obj (Opposite.op L, K)) L ≫
            m.app (Opposite.op L, d.tensor.obj (d.hom.obj (Opposite.op L, K), L))) ≫
        d'.hom.map ((𝟙 (Opposite.op (F.obj L)), F.map (d.evaluation L K)) :
          (Opposite.op (F.obj L),
              F.obj (d.tensor.obj (d.hom.obj (Opposite.op L, K), L))) ⟶
            (Opposite.op (F.obj L), F.obj K)) := by
    apply (a.homEquiv (d.hom.obj (Opposite.op L, K))
      (d'.hom.obj (Opposite.op (F.obj L), F.obj K))).injective
    rw [Equiv.apply_symm_apply, a.homEquiv_naturality_right, Equiv.apply_symm_apply]
    have hn := mate_naturality d d' m (𝟙 (Opposite.op L)) (d.evaluation L K)
    simp only [CategoryTheory.Functor.map_id, Functor.op_map, unop_id, op_id] at hn
    rw [Category.assoc, hn, ← Category.assoc, d.tensorHomUnit_comp_map_evaluation,
      Category.id_comp]
  rw [hkey, d'.homEquiv_naturality_right]
  rfl

/-- The lax tensor comparison is natural in both variables. -/
@[reassoc]
theorem laxTensorOfHomMate_naturality
    {X X' Y Y' : DerivedCategory (ModuleCat.{v} R)} (x : X ⟶ X') (y : Y ⟶ Y') :
    d'.tensor.map ((F.map x, F.map y) : (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y')) ≫
        laxTensorOfHomMate d d' a m X' Y' =
      laxTensorOfHomMate d d' a m X Y ≫
        F.map (d.tensor.map ((x, y) : (X, Y) ⟶ (X', Y'))) := by
  have hsplit : d'.tensor.map ((F.map x, F.map y) :
        (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y')) =
      d'.tensor.map ((𝟙 (F.obj X), F.map y) : (F.obj X, F.obj Y) ⟶ (F.obj X, F.obj Y')) ≫
        d'.tensor.map ((F.map x, 𝟙 (F.obj Y')) :
          (F.obj X, F.obj Y') ⟶ (F.obj X', F.obj Y')) := by
    rw [← d'.tensor.map_comp]
    congr 1
    simp
  have hm₁ := mate_naturality d d' m y.op (𝟙 (d.tensor.obj (X', Y')))
  have hm₂ := mate_naturality d d' m (𝟙 (Opposite.op Y))
    (d.tensor.map ((x, y) : (X, Y) ⟶ (X', Y')))
  simp only [CategoryTheory.Functor.map_id, Functor.op_map, Quiver.Hom.unop_op, unop_id, op_id]
    at hm₁ hm₂
  rw [hsplit, laxTensorOfHomMate, laxTensorOfHomMate, Category.assoc,
    ← d'.homEquiv_naturality_left, ← d'.homEquiv_dinaturality,
    ← d'.homEquiv_naturality_right]
  refine congrArg _ ?_
  apply (a.homEquiv X (d'.hom.obj (Opposite.op (F.obj Y),
    F.obj (d.tensor.obj (X', Y'))))).injective
  rw [a.homEquiv_naturality_right, a.homEquiv_naturality_left, a.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [Category.assoc, hm₁, hm₂]
  simp only [← Category.assoc, d.tensorHomUnit_naturality]

/-- The lax tensor comparison with its second argument fixed, as a natural transformation
`F ⋙ (- ⊗ᴸ F Y) ⟶ (- ⊗ᴸ Y) ⋙ F`. This is the square of functors of which the internal-Hom
comparison induced by `m` is the mate; the identity exhibiting that is
`StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_laxTensorOfHomMate`. -/
noncomputable def laxTensorOfHomMateSquare (Y : DerivedCategory (ModuleCat.{v} R)) :
    F ⋙ d'.tensorAt (F.obj Y) ⟶ d.tensorAt Y ⋙ F where
  app X := laxTensorOfHomMate d d' a m X Y
  naturality {X X'} x := by
    have h := laxTensorOfHomMate_naturality d d' a m x (𝟙 Y)
    rwa [CategoryTheory.Functor.map_id] at h

end Mate

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- **The lax monoidal structure map of derived base change**, in the tensor vocabulary of
Stacks 0A63: the canonical morphism `F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)` for a model `F` of derived
extension of scalars along `f : R → A`.

It is `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate` for the adjunction of
Stacks 0GMT and the change-of-rings comparison
  `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate` of
Stacks 0E1W, so it takes no monoidality input: concretely it is the transpose over `A` of the
transpose along `f` of the coevaluation `X ⟶ RHom_R(Y, X ⊗ᴸ_R Y)` followed by that comparison. -/
noncomputable def derivedTensorBaseChange
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.obj
        (F.obj X, F.obj Y) ⟶
      F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
        (X, Y)) :=
  DerivedHomAdjunction.laxTensorOfHomMate
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R)
    (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A)
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
      f F comparison)
    (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate.{uR, uA, uM} f F comparison) X Y

/-- `Dualizing.derivedTensorBaseChange` is natural in both variables. -/
@[reassoc]
theorem derivedTensorBaseChange_naturality
    {X X' Y Y' : DerivedCategory (ModuleCat.{max uR uA uM} R)} (x : X ⟶ X') (y : Y ⟶ Y') :
    (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensor.map
          ((F.map x, F.map y) : (F.obj X, F.obj Y) ⟶ (F.obj X', F.obj Y')) ≫
        derivedTensorBaseChange.{uR, uA, uM} f F comparison X' Y' =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ≫
        F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.map
          ((x, y) : (X, Y) ⟶ (X', Y'))) :=
  DerivedHomAdjunction.laxTensorOfHomMate_naturality _ _ _ _ x y

/-- `Dualizing.derivedTensorBaseChange` with its second argument fixed, as a natural
transformation of endofunctor composites. -/
noncomputable def derivedTensorBaseChangeSquare
    (Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    F ⋙ (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).tensorAt
        (F.obj Y) ⟶
      (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensorAt Y ⋙ F :=
  DerivedHomAdjunction.laxTensorOfHomMateSquare
    (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R)
    (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A)
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
      f F comparison)
    (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate.{uR, uA, uM} f F comparison) Y

/-- **The derived-Hom base-change map of Stacks 0E1X is the mate of
`Dualizing.derivedTensorBaseChange`.** Transposing it under the tensor--Hom adjunction of
Stacks 0A63 over `A` gives the lax monoidal structure map of derived base change followed by `F`
applied to the evaluation morphism of Stacks 0A63 over `R`. -/
theorem derivedTensorBaseChange_mate
    (L K : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
        (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.obj
          (Opposite.op L, K))) (F.obj L) (F.obj K)
        (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison L K)
          =
      derivedTensorBaseChange.{uR, uA, uM} f F comparison
          ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.obj
            (Opposite.op L, K)) L ≫
        F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).evaluation
          L K) :=
  DerivedHomAdjunction.homEquiv_laxTensorOfHomMate _ _ _ _ L K

/-- `Dualizing.derivedTensorBaseChange_mate` solved for the base-change map of Stacks 0E1X: it is
the transpose of the lax monoidal structure map of derived base change followed by `F` applied to
evaluation. -/
theorem derivedTensorBaseChange_mate_symm
    (L K : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison L K =
      ((derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
        (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.obj
          (Opposite.op L, K))) (F.obj L) (F.obj K)).symm
        (derivedTensorBaseChange.{uR, uA, uM} f F comparison
            ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).hom.obj
              (Opposite.op L, K)) L ≫
          F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).evaluation
            L K)) :=
  (AddEquiv.eq_symm_apply _).mpr (derivedTensorBaseChange_mate.{uR, uA, uM} f F comparison L K)

end Dualizing

end
