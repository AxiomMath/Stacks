module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaEvaluation

/-!
# The owed coherence of [stacks 0E2H] is one evaluation compatibility

`Dualizing.ProjectionFormula.ProjCounitCompat` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit` -- the compatibility of
the
projection formula `Dualizing.ProjectionFormula.derivedProjNatIso` with the counit of
[stacks 0GMT] and with the lax monoidal structure map `μ` of derived base change -- is the first
of the three things the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionTag` records [stacks 0E2H] as owing, the
other two being the associativity of `μ` and the descent of the `B ⊗[A] B`-diagonal to the
`A ⊗[R] A`-internal one.  It is also the hinge among them:
`Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_canonical` turns the second into a
coherence with no projection formula in it, granted `ProjCounitCompat` at the three pairs that
coherence mentions the projection formula at.

Before this file `ProjCounitCompat` was reduced in two ways, each of which still asked for the
equation at *two* varying arguments: `Dualizing.ProjectionFormula.projCounitCompat_of_kFlat`
asks for it at the class of a K-flat complex of `A`-modules and the class of an arbitrary
complex of `B`-modules, and `Dualizing.ProjectionFormula.projCounitCompat_iff_inv_eq` asks for
the identification of the inverse projection formula with
`Dualizing.ProjectionFormula.canonicalProjInv` at every object of `D(B)`.

This file removes the second argument altogether.  Writing `i_*` for derived restriction of
scalars, `Ext` for the model `E`, `ω` for the inverse projection formula
`derivedProjNatIso_N.inv.app` and `ev` for the evaluation of the tensor--Hom adjunction of
[stacks 0A63], the whole of `ProjCounitCompat` at `N` is the single family of equations

`ω_{RHom_B(Ext N, W)} ≫ i_*(ev_B) = (0E1W_{N,W} ⊗ᴸ_A 𝟙_N) ≫ ev_A`,

of morphisms `i_*RHom_B(Ext N, W) ⊗ᴸ_A N ⟶ i_*W`, where `0E1W` is the component
`Dualizing.ProjectionFormula.homRestrictComponent` of the change-of-rings isomorphism of
[stacks 0E1W].  **That is: the owed coherence says exactly that the projection formula and
[stacks 0E1W] are mates** under the two tensor--Hom adjunctions.

## Why one argument suffices

The reduction is the other triangle identity of the tensor--Hom adjunction.  A natural
transformation `Λ : i_*(-) ⊗ᴸ_A N ⟶ i_*(- ⊗ᴸ_B M)` is recovered from its own component at an
internal Hom:

`Λ_G = (i_*(coev_{G,M}) ⊗ᴸ_A 𝟙_N) ≫ Λ_{RHom_B(M, G ⊗ᴸ_B M)} ≫ i_*(ev_{M, G ⊗ᴸ_B M})`,

because naturality at the coevaluation `coev_{G,M} : G ⟶ RHom_B(M, G ⊗ᴸ_B M)` moves `Λ_G` to the
front and leaves `i_*` of `(coev ⊗ᴸ_B 𝟙_M) ≫ ev`, which is the identity.  That is
`Dualizing.ProjectionFormula.natTrans_app_eq_coevaluation`, and the triangle identity it uses is
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensor_map_tensorHomUnit_comp_evaluation` -- the one
of the two that the library had not named, the other being
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomUnit_comp_map_evaluation`.

Applied to `Λ = ω` and `M = Ext N`, it turns the evaluation compatibility above into a closed
formula for `ω_G` at every `G`: coevaluation followed by [stacks 0E1W], tensored and evaluated,
which is the transpose `Dualizing.ProjectionFormula.canonicalProjInv_eq` computes for
`canonicalProjInv`.  So the two agree at every object of `D(B)` at once.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensor_map_tensorHomUnit_comp_evaluation` -- the
  triangle identity `(coev_{X,Y} ⊗ᴸ 𝟙_Y) ≫ ev_{Y, X ⊗ᴸ Y} = 𝟙`.
* `Dualizing.ProjectionFormula.natTrans_app_eq_coevaluation` -- a transformation of
  projection-formula shape is recovered from its component at an internal Hom.
* `Dualizing.ProjectionFormula.projCounitCompat_of_eval` -- **the reduction**: the evaluation
  compatibility at every object of `D(B)` gives `Dualizing.ProjectionFormula.ProjCounitCompat`
  at `N`.
* `Dualizing.ProjectionFormula.eval_of_projCounitCompat` -- the converse, so the reduction loses
  nothing: `Dualizing.ProjectionFormula.canonicalProjInv_comp_restrict_evaluation` is the
  unconditional half, and the owed coherence is precisely the same equation with the projection
  formula in place of `canonicalProjInv`.
* `Dualizing.ProjectionFormula.homRestrictComponent_naturality` and
  `Dualizing.ProjectionFormula.homRestrictNatTrans` -- the component of [stacks 0E1W] at a fixed
  object of `D(A)`, as a natural transformation of functors of the object of `D(B)`.
* `Dualizing.ProjectionFormula.projEvalLeft`, `Dualizing.ProjectionFormula.projEvalRight` -- the
  two sides of the evaluation compatibility as natural transformations.  Each is a composite of
  two whiskerings, one of them of the counit of
  `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomAdjunctionAt`, so no naturality square is
  proved by hand.
* `Dualizing.ProjectionFormula.projCounitCompat_of_eval_rep` -- the compatibility at the class of
  every cochain complex of `B`-modules suffices.
* `Dualizing.ProjectionFormula.projEval_app_eq_of_iso` -- it is invariant under an isomorphism of
  the object of `D(B)`.
* `Dualizing.ProjectionFormula.projCounitCompat_of_eval_kFlat` -- **the sharpest form**: the
  compatibility at the class of a K-flat complex of `A`-modules and the class of an arbitrary
  complex of `B`-modules gives `Dualizing.ProjectionFormula.ProjCounitCompat` at *every* object
  of `D(A)`.
* `Dualizing.ProjectionFormula.projEvalRight_app_eq_homEquiv` and
  `Dualizing.ProjectionFormula.projCounitCompat_of_mate` -- **the owed coherence as a mate
  identity**: the right-hand side is the [stacks 0A63] transpose of the component of
  [stacks 0E1W], so the whole coherence says that the projection formula and [stacks 0E1W] are
  mates.
* `Dualizing.ProjectionFormula.isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_eval` --
  **the handoff**: the invertibility that [stacks 0E2H] needs, on the mate identity at
  representatives and `Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat`, in which
  no projection formula occurs.  The three pairs that
  `Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_canonical` needs the coherence at
  are all covered, since the mate identity at representatives gives it at every object of `D(A)`
  and at every object of `D(B)`.

## What is owed after this file

The equation above, and nothing else: no `μ`, no counit of [stacks 0GMT] and no invertibility.
`Dualizing.ProjectionFormula.projCounitCompat_of_eval_kFlat` is the sharpest form: both sides are
natural in the object of `D(B)`, so the equation may be checked at the class of a complex, and
`Dualizing.ProjectionFormula.projCounitCompat_of_kFlat` then lets the object of `D(A)` be the
class of a K-flat complex.  `Dualizing.ProjectionFormula.projEval_app_eq_of_iso` lets the object
of `D(B)` be moved along an isomorphism as well, so with
`StacksDraft.DerivedHom.exists_isKInjective_model` it may be taken to be the scalar transport of
the class of a K-injective complex -- the situation in which every factor has a value at
representatives: the inverse projection formula by
`Dualizing.ProjectionFormula.derivedProjNatIso_inv_app_Q`, the evaluation of [stacks 0A63] by
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_evaluation_eq_model`, and the component of
[stacks 0E1W] by
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective_Q`.

The chain-level statement of the same shape is already in the library, and is the candidate
witness: `Stacks.DerivedHom.BaseChangeIso.restrictedEvaluation_eq_tensorHom_evaluationMor` of
`StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorHom` says that the restricted
evaluation `(𝟙_{Z|_A} ⊗ₘ η_K) ≫ ρ_{Z, B ⊗_A K} ≫ (ev_B)|_A` is the chain-level [stacks 0E1W]
comparison `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` tensored with the identity,
followed by evaluation over `A`, where `ρ` is
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor`.  Two things stand between that and the
equation above, and neither is stated anywhere: that `(𝟙 ⊗ₘ η_K) ≫ ρ` is the inverse of the
chain-level projection formula
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso`, which is a degreewise
`TensorProduct` computation; and the descent of both sides to the vocabulary of [stacks 0A63],
whose tensor and internal Hom are transported along
`StacksDraft.DerivedHom.uliftDerivedEquivalence`.

No `@[stacks]` attribute is placed here: nothing in this file is unconditional about a tag, and
the identities it proves belong to the tags of the morphisms they are about.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

universe ur uv uw

/-- **The other triangle identity of the tensor--Hom adjunction of [stacks 0A63].**
Coevaluation `X ⟶ RHom(Y, X ⊗ᴸ Y)` tensored with the identity of `Y`, followed by evaluation, is
the identity of `X ⊗ᴸ Y`.  The companion
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomUnit_comp_map_evaluation` is the other one. -/
theorem tensor_map_tensorHomUnit_comp_evaluation {R : Type ur} [CommRing R]
    [HasDerivedCategory.{uw} (ModuleCat.{uv} R)] (d : DerivedHomAdjunction R)
    (X Y : DerivedCategory (ModuleCat.{uv} R)) :
    d.tensor.map ((d.tensorHomUnit X Y, 𝟙 Y) :
        (X, Y) ⟶ (d.hom.obj (Opposite.op Y, d.tensor.obj (X, Y)), Y)) ≫
        d.evaluation Y (d.tensor.obj (X, Y)) =
      𝟙 (d.tensor.obj (X, Y)) := by
  rw [← d.homEquiv_eq_tensor_map_comp_evaluation]
  exact (d.homEquiv X Y (d.tensor.obj (X, Y))).apply_symm_apply (𝟙 _)

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Dualizing.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

universe u v

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Tensoring on the right with a fixed object, on a morphism. -/
theorem tensorRight_map (R : Type u) [CommRing R]
    (M : DerivedCategory (ModuleCat.{max u v} R))
    {X Y : DerivedCategory (ModuleCat.{max u v} R)} (f : X ⟶ Y) :
    (tensorRightDerived.{u, v} R M).map f =
      (derivedHomAdjunctionOverRing.{u, v, max u v + 1} R).tensor.map
        (X := (X, M)) (Y := (Y, M)) (f, 𝟙 M) :=
  rfl

/-- **A transformation of projection-formula shape is recovered from its component at an internal
Hom.**  For a functor `i_* : D(B) ⥤ D(A)`, objects `N` of `D(A)` and `M` of `D(B)` and a natural
transformation `Λ : i_*(-) ⊗ᴸ_A N ⟶ i_*(- ⊗ᴸ_B M)`,

`Λ_G = (i_*(coev_{G,M}) ⊗ᴸ_A 𝟙_N) ≫ Λ_{RHom_B(M, G ⊗ᴸ_B M)} ≫ i_*(ev_{M, G ⊗ᴸ_B M})`.

Naturality of `Λ` at the coevaluation `G ⟶ RHom_B(M, G ⊗ᴸ_B M)` of [stacks 0A63] brings `Λ_G` to
the front, and what is left of the other two factors is `i_*` of
`(coev_{G,M} ⊗ᴸ_B 𝟙_M) ≫ ev_{M, G ⊗ᴸ_B M}`, the identity by
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensor_map_tensorHomUnit_comp_evaluation`.

So such a transformation is determined by its composite with evaluation at the objects
`RHom_B(M, -)`, which is what reduces the coherence of
`Dualizing.ProjectionFormula.ProjCounitCompat` to one argument. -/
theorem natTrans_app_eq_coevaluation
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (M : DerivedCategory (ModuleCat.{max u v} B))
    (Λ : iStar ⋙ tensorRightDerived.{u, v} A N ⟶ tensorRightDerived.{u, v} B M ⋙ iStar)
    (G : DerivedCategory (ModuleCat.{max u v} B)) :
    Λ.app G =
      (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (X := (iStar.obj G, N))
          (Y := (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.obj
            (Opposite.op M,
              (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj (G, M))), N))
          (iStar.map ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensorHomUnit G M),
            𝟙 N) ≫
        Λ.app ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).hom.obj
            (Opposite.op M,
              (derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj (G, M))) ≫
          iStar.map ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).evaluation M
            ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj (G, M))) := by
  have hnat := Λ.naturality
    ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensorHomUnit G M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [tensorRight_map] at hnat
  rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, tensorRight_map,
    DerivedHomAdjunction.tensor_map_tensorHomUnit_comp_evaluation]
  simp

/-- **The owed coherence of [stacks 0E2H] from one evaluation compatibility.**  Writing `i_*` for
derived restriction of scalars, `Ext` for the model `E` and `ω` for the inverse projection formula
`derivedProjNatIso_N.inv.app`, suppose that for every object `W` of `D(B)`

`ω_{RHom_B(Ext N, W)} ≫ i_*(ev_B) = (0E1W_{N,W} ⊗ᴸ_A 𝟙_N) ≫ ev_A`

as morphisms `i_*RHom_B(Ext N, W) ⊗ᴸ_A N ⟶ i_*W`, with `0E1W` the component
`Dualizing.ProjectionFormula.homRestrictComponent` of the change-of-rings isomorphism of
[stacks 0E1W].  Then `Dualizing.ProjectionFormula.ProjCounitCompat` holds at `N`.

The hypothesis is the equation that
`Dualizing.ProjectionFormula.canonicalProjInv_comp_restrict_evaluation` proves unconditionally
for `Dualizing.ProjectionFormula.canonicalProjInv`, so this says: the projection formula is the
canonical projection morphism as soon as it has the same evaluation compatibility, and that is
one equation in one variable rather than the two the earlier reductions asked for.  The
determination is `Dualizing.ProjectionFormula.natTrans_app_eq_coevaluation` at `M = Ext N`; the
rest is `Dualizing.ProjectionFormula.canonicalProjInv_eq` read backwards. -/
theorem projCounitCompat_of_eval (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (h : ∀ W : DerivedCategory (ModuleCat.{max u v} B),
      (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
              (Opposite.op (E.functor.obj N), W)) ≫
          (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).evaluation
              (E.functor.obj N) W) =
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
            (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
                ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                  (Opposite.op (E.functor.obj N), W)), N))
            (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).hom.obj
                (Opposite.op N,
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W), N))
            (homRestrictComponent.{u, v} φ E N W, 𝟙 N) ≫
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).evaluation N
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  rw [projCounitCompat_iff_inv_eq.{u, v} φ E adj N]
  intro G
  rw [canonicalProjInv_eq.{u, v} φ E N G,
    DerivedHomAdjunction.homEquiv_eq_tensor_map_comp_evaluation,
    natTrans_app_eq_coevaluation.{u, max u v}
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory N (E.functor.obj N)
      (derivedProjNatIso.{u, max u v} φ E _ adj N).inv G,
    h ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
      (G, E.functor.obj N)),
    ← Category.assoc, DerivedHomAdjunction.tensor_map_comp, Category.comp_id]

/-- **The reduction of `Dualizing.ProjectionFormula.projCounitCompat_of_eval` loses nothing.**
`Dualizing.ProjectionFormula.ProjCounitCompat` at `N` implies the evaluation compatibility that
lemma assumes: by `Dualizing.ProjectionFormula.projCounitCompat_iff_inv_eq` the inverse
projection formula is `Dualizing.ProjectionFormula.canonicalProjInv`, which has that
compatibility unconditionally by
`Dualizing.ProjectionFormula.canonicalProjInv_comp_restrict_evaluation`.

So the owed coherence and the displayed equation are the same statement, and the one-variable
form is the sharper shape of it. -/
theorem eval_of_projCounitCompat (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (h : ProjCounitCompat.{u, v} φ E adj N)
    (W : DerivedCategory (ModuleCat.{max u v} B)) :
    (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
            (Opposite.op (E.functor.obj N), W)) ≫
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).evaluation
            (E.functor.obj N) W) =
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
                (Opposite.op (E.functor.obj N), W)), N))
          (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).hom.obj
              (Opposite.op N,
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W), N))
          (homRestrictComponent.{u, v} φ E N W, 𝟙 N) ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).evaluation N
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W) := by
  rw [(projCounitCompat_iff_inv_eq.{u, v} φ E adj N).mp h]
  exact canonicalProjInv_comp_restrict_evaluation.{u, v} φ E N W

/-! ### The evaluation compatibility is a question about representatives -/

/-- The naturality of the change-of-rings isomorphism of [stacks 0E1W] in its covariant variable,
read with the internal Hom of the tensor--Hom adjunction of [stacks 0A63] rather than with the
transported bifunctor its own statement uses. -/
theorem homRestrictComponent_naturality (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    {W W' : DerivedCategory (ModuleCat.{max u v} B)} (k : W ⟶ W') :
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.map
            (X := (Opposite.op (E.functor.obj N), W))
            (Y := (Opposite.op (E.functor.obj N), W'))
            (𝟙 (Opposite.op (E.functor.obj N)), k)) ≫
        homRestrictComponent.{u, v} φ E N W' =
      homRestrictComponent.{u, v} φ E N W ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).hom.map
          (X := (Opposite.op N,
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W))
          (Y := (Opposite.op N,
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W'))
          (𝟙 (Opposite.op N),
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map k) := by
  have hnat := (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{u, u, v} φ
    E.functor (modelComparison.{u, v} φ E)).inv.naturality
    ((𝟙 (Opposite.op N), k) :
      ((Opposite.op N, W) :
          (DerivedCategory (ModuleCat.{max u v} A))ᵒᵖ ×
            DerivedCategory (ModuleCat.{max u v} B)) ⟶ (Opposite.op N, W'))
  simp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.op_map, unop_id,
    CategoryTheory.Functor.map_id, op_id] at hnat
  exact hnat

/-- **The component of [stacks 0E1W] at a fixed object of `D(A)`, as a natural transformation.**
`Dualizing.ProjectionFormula.homRestrictComponent` at `N`, read as a transformation
`i_*RHom_B(Ext N, -) ⟶ RHom_A(N, i_*(-))` of functors of the object of `D(B)`. -/
noncomputable def homRestrictNatTrans (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homAt (E.functor.obj N) ⋙
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⟶
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⋙
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homAt N where
  app W := homRestrictComponent.{u, v} φ E N W
  naturality _ _ k := homRestrictComponent_naturality.{u, v} φ E N k

/-- **The left-hand side of the evaluation compatibility**, as a natural transformation in the
object of `D(B)`: the inverse projection formula at an internal Hom, followed by derived
restriction of the evaluation of [stacks 0A63] over `B`.  Both factors are whiskerings of
transformations that are already natural -- the second being the counit of
`StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomAdjunctionAt`, which is evaluation by
`StacksDraft.DerivedHom.DerivedHomAdjunction.evaluation_eq_counit` -- so no naturality square is
proved by hand. -/
noncomputable def projEvalLeft (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homAt (E.functor.obj N) ⋙
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⋙
          tensorRightDerived.{u, max u v} A N ⟶
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory :=
  Functor.whiskerLeft
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homAt (E.functor.obj N))
      (derivedProjNatIso.{u, max u v} φ E _ adj N).inv ≫
    Functor.whiskerRight
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensorHomAdjunctionAt
        (E.functor.obj N)).counit
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory

/-- **The right-hand side of the evaluation compatibility**, as a natural transformation in the
object of `D(B)`: the component of [stacks 0E1W] tensored with the identity of `N`, followed by
the evaluation of [stacks 0A63] over `A`. -/
noncomputable def projEvalRight (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).homAt (E.functor.obj N) ⋙
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⋙
          tensorRightDerived.{u, max u v} A N ⟶
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory :=
  Functor.whiskerRight (homRestrictNatTrans.{u, v} φ E N)
      (tensorRightDerived.{u, max u v} A N) ≫
    Functor.whiskerLeft (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorHomAdjunctionAt N).counit

/-- **The owed coherence of [stacks 0E2H] is a question about representatives.**  Both sides of
the evaluation compatibility of `Dualizing.ProjectionFormula.projCounitCompat_of_eval` are natural
in the object of `D(B)` -- they are
`Dualizing.ProjectionFormula.projEvalLeft` and `Dualizing.ProjectionFormula.projEvalRight` -- so by
uniqueness of transformations descending along the localization functor it is enough to check the
equation at the class of every cochain complex of `B`-modules. -/
theorem projCounitCompat_of_eval_rep (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (h : ∀ J : CochainComplex (ModuleCat.{max u v} B) ℤ,
      (projEvalLeft.{u, v} φ E adj N).app (DerivedCategory.Q.obj J) =
        (projEvalRight.{u, v} φ E N).app (DerivedCategory.Q.obj J)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  have key : projEvalLeft.{u, v} φ E adj N = projEvalRight.{u, v} φ E N :=
    Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} B) (ComplexShape.up ℤ)) h
  exact projCounitCompat_of_eval.{u, v} φ E adj N fun W => NatTrans.congr_app key W

/-- **The owed coherence of [stacks 0E2H] at every object, from the evaluation compatibility at
representatives.**  `Dualizing.ProjectionFormula.projCounitCompat_of_eval_rep` turns the
evaluation compatibility at the class of a K-flat complex of `A`-modules into
`Dualizing.ProjectionFormula.ProjCounitCompat` there, and
`Dualizing.ProjectionFormula.projCounitCompat_of_kFlat` carries that to every object of `D(A)`.

So the whole of the first coherence of [stacks 0E2H] rests on one equation, between two morphisms
`i_*RHom_B(Ext Q(P), Q(J)) ⊗ᴸ_A Q(P) ⟶ i_*Q(J)`, at the class of a K-flat complex `P` of
`A`-modules and the class of an arbitrary complex `J` of `B`-modules -- the situation in which
the projection formula has a value at representatives,
`Dualizing.ProjectionFormula.derivedProjNatIso_hom_app_Q`, and the change-of-rings isomorphism of
[stacks 0E1W] has one,
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective_Q`. -/
theorem projCounitCompat_of_eval_kFlat (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P →
      ∀ J : CochainComplex (ModuleCat.{max u v} B) ℤ,
        (projEvalLeft.{u, v} φ E adj (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj J) =
          (projEvalRight.{u, v} φ E (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj J))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N :=
  projCounitCompat_of_kFlat.{u, v} φ E adj
    (fun P hP L =>
      projCounitCompat_of_eval_rep.{u, v} φ E adj (DerivedCategory.Q.obj P) (h P hP)
        (DerivedCategory.Q.obj L))
    N

/-- **The evaluation compatibility is invariant under an isomorphism of the object of `D(B)`.**
Both sides are natural in that object and the target functor is derived restriction of scalars, so
an isomorphism `W ≅ W'` carries the equation at `W'` to the equation at `W`.

With `StacksDraft.DerivedHom.exists_isKInjective_model` this lets the object be taken to be the
scalar transport of the class of a **K-injective** complex, which is the form in which the
internal Hom of [stacks 0A63] has a value at representatives. -/
theorem projEval_app_eq_of_iso (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    {W W' : DerivedCategory (ModuleCat.{max u v} B)} (e : W ≅ W')
    (h : (projEvalLeft.{u, v} φ E adj N).app W' = (projEvalRight.{u, v} φ E N).app W') :
    (projEvalLeft.{u, v} φ E adj N).app W = (projEvalRight.{u, v} φ E N).app W := by
  have : IsIso ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map e.hom) :=
    ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.mapIso e).isIso_hom
  rw [← cancel_mono ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map e.hom),
    ← (projEvalLeft.{u, v} φ E adj N).naturality e.hom,
    ← (projEvalRight.{u, v} φ E N).naturality e.hom, h]

/-! ### The owed coherence as a mate identity -/

/-- **The right-hand side of the evaluation compatibility is a transpose.**  The component of
[stacks 0E1W] tensored with the identity of `N` and evaluated over `A` is, by
`StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_eq_tensor_map_comp_evaluation`, the
transpose over [stacks 0A63] of that component. -/
theorem projEvalRight_app_eq_homEquiv (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W : DerivedCategory (ModuleCat.{max u v} B)) :
    (projEvalRight.{u, v} φ E N).app W =
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
            (Opposite.op (E.functor.obj N), W))) N
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
        (homRestrictComponent.{u, v} φ E N W) :=
  ((derivedHomAdjunctionOverRing.{u, max u v,
      max u v + 1} A).homEquiv_eq_tensor_map_comp_evaluation
    ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
        (Opposite.op (E.functor.obj N), W))) N
    ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
    (homRestrictComponent.{u, v} φ E N W)).symm

/-- **The owed coherence of [stacks 0E2H] is a mate identity.**  Writing `i_*` for derived
restriction of scalars, `Ext` for the model `E` and `ω` for the inverse projection formula
`derivedProjNatIso_N.inv.app`, suppose that for every object `W` of `D(B)` the transpose over
[stacks 0A63] of

`i_*RHom_B(Ext N, W) ⊗ᴸ_A N --ω--> i_*(RHom_B(Ext N, W) ⊗ᴸ_B Ext N) --i_*(ev_B)--> i_*W`

is the component `Dualizing.ProjectionFormula.homRestrictComponent` of the change-of-rings
isomorphism of [stacks 0E1W] at `(N, W)`.  Then
`Dualizing.ProjectionFormula.ProjCounitCompat` holds at `N`.

**This is the smallest shape the first of the three residues of [stacks 0E2H] has:** the
projection formula and [stacks 0E1W] are mates under the two tensor--Hom adjunctions.  One
transposition, one variable, no `μ`, no counit of [stacks 0GMT], no invertibility and nothing
existential.  The converse holds too, by
`Dualizing.ProjectionFormula.eval_of_projCounitCompat` and
`Dualizing.ProjectionFormula.projEvalRight_app_eq_homEquiv`. -/
theorem projCounitCompat_of_mate (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (h : ∀ W : DerivedCategory (ModuleCat.{max u v} B),
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
              (Opposite.op (E.functor.obj N), W))) N
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)).symm
          ((projEvalLeft.{u, v} φ E adj N).app W) =
        homRestrictComponent.{u, v} φ E N W) :
    ProjCounitCompat.{u, v} φ E adj N := by
  refine projCounitCompat_of_eval.{u, v} φ E adj N fun W => ?_
  change (projEvalLeft.{u, v} φ E adj N).app W = (projEvalRight.{u, v} φ E N).app W
  rw [projEvalRight_app_eq_homEquiv.{u, v} φ E N W, ← h W]
  exact (AddEquiv.apply_symm_apply _ _).symm

/-! ### What the first identification of [stacks 0E2H] now costs -/

/-- **The invertibility that [stacks 0E2H] needs, on the mate identity at representatives and the
coherence of the lax monoidal structure map.**  This is
`Dualizing.ProjectionFormula.isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_canonical`
with its first input -- `Dualizing.ProjectionFormula.ProjCounitCompat` at every object of `D(A)`
-- replaced by the evaluation compatibility at the class of a K-flat complex of `A`-modules and
the class of an arbitrary complex of `B`-modules, which
`Dualizing.ProjectionFormula.projCounitCompat_of_eval_kFlat` shows suffices.

So the first identification of [stacks 0E2H] rests on exactly two things: one equation between
two morphisms of `D(A)` at representatives, and
`Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat`, in which no projection formula
occurs.  The three pairs at which
`Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_canonical` needs the coherence are all
covered, since `projCounitCompat_of_eval_kFlat` gives it at *every* object of `D(A)` and
`Dualizing.ProjectionFormula.ProjCounitCompat` is the statement at every object of `D(B)`. -/
theorem isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_eval (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (Y X : DerivedCategory (ModuleCat.{max u v} A))
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P →
      ∀ J : CochainComplex (ModuleCat.{max u v} B) ℤ,
        (projEvalLeft.{u, v} φ E adj (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj J) =
          (projEvalRight.{u, v} φ E (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj J))
    (hC : CanonicalProjTensorBaseChangeCompat.{u, v} φ E Y
      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
        ((Dualizing.derivedHom.{u, max u v, u} φ).obj X)))
    (hdiag : IsIso (Dualizing.derivedTensorHomDiagonalOverRing.{u, max u v} Y X
      (restrictedAlgebra.{u, max u v}
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))) :
    IsIso ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
      ((derivedTensorHomDiagonalAlongRingHom.{u, max u v} φ E _ adj Y).app X)) :=
  isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_canonical.{u, v} φ E adj Y X
    (projCounitCompat_of_eval_kFlat.{u, v} φ E adj h) hC hdiag

end Dualizing.ProjectionFormula

end
