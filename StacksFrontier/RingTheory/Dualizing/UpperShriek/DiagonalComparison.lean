module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.ModelCriterion
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RestrictedCoextension

/-!
# The diagonal along a ring map, restricted, is the internal diagonal at the algebra

This is **Comparison I** of the residue of [stacks 0E2H], in the shape the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeComposition` states it: that derived restriction of
scalars along `φ : A →+* B` carries the `B`-linear tensor--Hom diagonal
`Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom` to the single-ring tensor--Hom
diagonal `Dualizing.derivedTensorHomDiagonalOverRing` of `D(A)` at the algebra.

The two sides live in different categories before any comparison is made, and the identifications
that bring them together are the projection formula
`Dualizing.ProjectionFormula.derivedProjNatIso` on the source and
`Dualizing.ProjectionFormula.restrictCoextendInternalHomIso` -- restricted derived coextension of
scalars is the internal Hom out of the algebra -- on the target.  With those in place the
comparison is a commuting square of morphisms of `D(A)`; no invertibility is asserted, and none is
used.

## Main results

* `Dualizing.ProjectionFormula.restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal` --
  **Comparison I**, as that square.
* `Dualizing.ProjectionFormula.isIso_restrict_derivedTensorHomDiagonalAlongRingHom` -- hence the
  restricted diagonal along `φ` is invertible as soon as the single-ring diagonal at the algebra
  is.  This is the implication [stacks 0E2H] needs: the invertibility of the single-ring diagonal
  is `Dualizing.isIso_derivedTensorHomDiagonal_diagonal_composite`, which carries nothing.

## What the square costs

Both results take one hypothesis, written out rather than named: that the projection formula is
**linear for the action of the algebra**.  Writing `T = i_*(1_B)` for the algebra as an object of
`D(A)` and `a` for `Dualizing.ProjectionFormula.restrictedAction`, it says that

`a_{G ⊗ᴸ_B Ext Y} ≫ proj_G = (proj_G ≫ swap) ⊗ 𝟙_T ≫ assoc ≫ (𝟙_Y ⊗ a_G) ≫ swap`

as morphisms `i_*(G ⊗ᴸ_B Ext Y) ⊗ᴸ_A T ⟶ i_*G ⊗ᴸ_A Y`, which is exactly the statement that the
isomorphism `i_*(G ⊗ᴸ_B Ext Y) ≅ i_*G ⊗ᴸ_A Y` of the projection formula is a map of `B`-modules.
Nothing else is assumed: in particular no K-flatness, no Tor-amplitude bound and no choice of
representative, all of which the proof below avoids by working through the two adjunctions alone.

`StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparisonBridge` relates this hypothesis to
the compatibility of the projection formula with the counit of [stacks 0GMT] named in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit`,
`Dualizing.ProjectionFormula.ProjCounitCompat`.  The relation is an implication and not an
identification: cancelling the algebra action off both sides
(`Dualizing.ProjectionFormula.restrictedAction_comp_derivedProj_iff`) leaves the restricted counit
against the projection formula, and `ProjCounitCompat` accounts for that only together with one
further coherence, `Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat`, in which no counit
occurs.

## Implementation notes

The proof transposes the whole square over [stacks 0A63].  On the left the transpose of the
comparison is `Dualizing.ProjectionFormula.homEquiv_restrictCoextendInternalHomIso` and the
transpose of the diagonal along `φ` is
`Dualizing.ProjectionFormula.restrict_derivedTensorHomDiagonalAlongRingHom_comp_counit`, so the
left-hand side becomes the algebra action followed by the projection formula and the counit of
[stacks 0A70].  On the right the transpose of the single-ring diagonal is associativity followed
by evaluation, `Dualizing.derivedTensorHomDiagonalOverRing_homEquiv`, and
`Dualizing.ProjectionFormula.tensor_restrictCoextendInternalHomIso_comp_evaluation` turns that
evaluation into the same action and counit.  What is then left between the two sides is precisely
the linearity hypothesis; the counit of [stacks 0A70] cancels on both sides because the symmetry is
natural.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

universe u v

namespace Dualizing.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **The action of the algebra on a restricted object.**  For `G` in `D(B)`, the `A`-module
`i_*G` carries an action of the algebra, `i_*G ⊗ᴸ_A B ⟶ i_*G`: the inverse of
`Dualizing.ProjectionFormula.restrictExtendIso` identifies the source with `i_*(Ext(i_*G))`, and
the counit of [stacks 0GMT] then lands it in `i_*G`. -/
noncomputable def restrictedAction (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) (adjE : E.functor ⊣ iStar)
    (G : DerivedCategory (ModuleCat.{max u v} B)) :
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
        (iStar.obj G, restrictedAlgebra.{u, v} iStar) ⟶ iStar.obj G :=
  (restrictExtendIso.{u, v} φ E iStar adj).inv.app (iStar.obj G) ≫
    iStar.map (adjE.counit.app G)

/-- **The comparison against evaluation.**  Tensoring
`Dualizing.ProjectionFormula.restrictCoextendInternalHomIso` with the algebra and evaluating is the
action of the algebra followed by the counit of [stacks 0A70].  This is
`Dualizing.ProjectionFormula.homEquiv_restrictCoextendInternalHomIso` with the transposition
carried out. -/
theorem tensor_restrictCoextendInternalHomIso_comp_evaluation (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) (adjE : E.functor ⊣ iStar)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (X := (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X),
            restrictedAlgebra.{u, v} iStar))
          (Y := ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
              (Opposite.op (restrictedAlgebra.{u, v} iStar), X),
            restrictedAlgebra.{u, v} iStar))
          ((restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app X,
            𝟙 (restrictedAlgebra.{u, v} iStar)) ≫
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).evaluation
          (restrictedAlgebra.{u, v} iStar) X =
      restrictedAction.{u, v} φ E iStar adj adjE ((Dualizing.derivedHom.{u, v, u} φ).obj X) ≫
        adj.counit.app X := by
  have e := (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv_naturality_left
    ((restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app X)
    (𝟙 (((Functor.curry.obj (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom).obj
      (Opposite.op (restrictedAlgebra.{u, v} iStar))).obj X))
  rw [Category.comp_id] at e
  dsimp only [restrictedAction]
  rw [Category.assoc, ← homEquiv_restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE X]
  exact e.symm

/-- **Comparison I of [stacks 0E2H].**  Derived restriction of scalars along `φ : A →+* B` carries
the `B`-linear tensor--Hom diagonal along `φ` at `Y`,
`Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom`, to the single-ring tensor--Hom
diagonal `Dualizing.derivedTensorHomDiagonalOverRing` of `D(A)` at `(Y, X, B[0])`: the square
built from the projection formula on the source and
`Dualizing.ProjectionFormula.restrictCoextendInternalHomIso` on the target commutes.  The two
symmetries are there only because the diagonal along `φ` tensors `Y` on the right and the
single-ring diagonal tensors it on the left.

The hypothesis is that the projection formula is linear for the action of the algebra; see the
module documentation for why that is the whole cost, and for its relation to
`Dualizing.ProjectionFormula.ProjCounitCompat`. -/
theorem restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) (adjE : E.functor ⊣ iStar)
    (Y X : DerivedCategory (ModuleCat.{max u v} A))
    (hlin : restrictedAction.{u, v} φ E iStar adj adjE
            ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
              ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y)) ≫
          (derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app
            ((Dualizing.derivedHom.{u, v, u} φ).obj X) =
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
                ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y)),
              restrictedAlgebra.{u, v} iStar))
            (Y := ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
                (Y, iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)),
              restrictedAlgebra.{u, v} iStar))
            ((derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app
                ((Dualizing.derivedHom.{u, v, u} φ).obj X) ≫
              ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
                (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)) Y).hom,
              𝟙 (restrictedAlgebra.{u, v} iStar)) ≫
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorAssoc
            Y (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X))
            (restrictedAlgebra.{u, v} iStar)).hom ≫
          (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (Y, (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
                (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X),
                  restrictedAlgebra.{u, v} iStar)))
            (Y := (Y, iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)))
            (𝟙 Y, restrictedAction.{u, v} φ E iStar adj adjE
              ((Dualizing.derivedHom.{u, v, u} φ).obj X)) ≫
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
            Y (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X))).hom) :
    iStar.map ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X) ≫
        (restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app
          ((tensorRightDerived.{u, v} A Y).obj X) =
      (derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app
          ((Dualizing.derivedHom.{u, v, u} φ).obj X) ≫
        ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
          (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)) Y).hom ≫
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (X := (Y, iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)))
          (Y := (Y, (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
            (Opposite.op (restrictedAlgebra.{u, v} iStar), X)))
          (𝟙 Y, (restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app X) ≫
        Dualizing.derivedTensorHomDiagonalOverRing.{u, v} Y X
          (restrictedAlgebra.{u, v} iStar) ≫
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
          (𝟙 (Opposite.op (restrictedAlgebra.{u, v} iStar)),
            ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap Y X).hom) := by
  apply ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv
    (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
      ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y)))
    (restrictedAlgebra.{u, v} iStar)
    ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj (X, Y))).injective
  simp only [← Category.assoc]
  rw [(derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv_naturality_right]
  rw [(derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv_naturality_left]
  rw [(derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv_naturality_left]
  dsimp only [Functor.comp_obj]
  have hv : ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).homEquiv
        (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj
          ((tensorRightDerived.{u, v} A Y).obj X)))
        (restrictedAlgebra.{u, v} iStar)
        ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj (X, Y)))
      ((restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app
        ((tensorRightDerived.{u, v} A Y).obj X)) =
      (restrictExtendIso.{u, v} φ E iStar adj).inv.app
          (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj
            ((tensorRightDerived.{u, v} A Y).obj X))) ≫
        iStar.map (adjE.counit.app ((Dualizing.derivedHom.{u, v, u} φ).obj
          ((tensorRightDerived.{u, v} A Y).obj X))) ≫
          adj.counit.app ((tensorRightDerived.{u, v} A Y).obj X) :=
    homEquiv_restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE
      ((tensorRightDerived.{u, v} A Y).obj X)
  rw [hv]
  have hd := Dualizing.derivedTensorHomDiagonalOverRing_homEquiv.{u, v} (R := A) Y X
    (restrictedAlgebra.{u, v} iStar)
  dsimp only at hd
  rw [hd]
  simp only [Category.assoc]
  have hp : (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
        (X := (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
            ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y)),
          restrictedAlgebra.{u, v} iStar))
        (Y := (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj
            ((tensorRightDerived.{u, v} A Y).obj X)), restrictedAlgebra.{u, v} iStar))
        (iStar.map ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X),
          𝟙 (restrictedAlgebra.{u, v} iStar)) ≫
      (restrictExtendIso.{u, v} φ E iStar adj).inv.app
        (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj
          ((tensorRightDerived.{u, v} A Y).obj X))) =
      (restrictExtendIso.{u, v} φ E iStar adj).inv.app
          (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
            ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y))) ≫
        iStar.map (E.functor.map
          (iStar.map ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X))) :=
    (restrictExtendIso.{u, v} φ E iStar adj).inv.naturality
      (iStar.map ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X))
  have hc : iStar.map (E.functor.map
          (iStar.map ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X))) ≫
        iStar.map (adjE.counit.app ((Dualizing.derivedHom.{u, v, u} φ).obj
          ((tensorRightDerived.{u, v} A Y).obj X))) =
      iStar.map (adjE.counit.app ((derivedHomAdjunctionOverRing.{u, v,
          max u v + 1} B).tensor.obj
          ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y))) ≫
        iStar.map ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X) := by
    rw [← iStar.map_comp, ← iStar.map_comp]
    exact congrArg iStar.map (adjE.counit.naturality
      ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X))
  rw [reassoc_of% hp, reassoc_of% hc,
    restrict_derivedTensorHomDiagonalAlongRingHom_comp_counit.{u, v} φ E iStar adj Y X]
  dsimp only [Functor.flip_obj_map, Functor.curry_obj_map_app, Prod.mkHom]
  have hact : (restrictExtendIso.{u, v} φ E iStar adj).inv.app
        (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
          ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y))) ≫
      iStar.map (adjE.counit.app
        ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
          ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y))) =
      restrictedAction.{u, v} φ E iStar adj adjE
        ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
          ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y)) := rfl
  simp only at hlin
  rw [reassoc_of% hact, reassoc_of% hlin]
  have hsplit : ∀ {K₁ K₂ K₃ L₁ L₂ L₃ : DerivedCategory (ModuleCat.{max u v} A)}
      {f₁ : K₁ ⟶ K₂} {g₁ : K₂ ⟶ K₃} {h₁ : K₁ ⟶ K₃} (f₂ : L₁ ⟶ L₂) (g₂ : L₂ ⟶ L₃)
      {h₂ : L₁ ⟶ L₃}, f₁ ≫ g₁ = h₁ → f₂ ≫ g₂ = h₂ →
      (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (X := (K₁, L₁)) (Y := (K₃, L₃)) (h₁, h₂) =
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (K₁, L₁)) (Y := (K₂, L₂)) (f₁, f₂) ≫
          (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (K₂, L₂)) (Y := (K₃, L₃)) (g₁, g₂) := by
    rintro _ _ _ _ _ _ _ _ _ f₂ g₂ _ rfl rfl
    exact ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor_map_comp _ _ _ _).symm
  simp only [hsplit (𝟙 _) (𝟙 _) rfl (Category.comp_id _), Category.assoc]
  rw [(derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorAssoc_naturality_assoc (𝟙 Y)
      (show iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X) ⟶
          (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
            (Opposite.op (restrictedAlgebra.{u, v} iStar), X) from
        (restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app X)
      (𝟙 (restrictedAlgebra.{u, v} iStar)),
    ← reassoc_of% hsplit
      ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
        (X := (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X),
          restrictedAlgebra.{u, v} iStar))
        (Y := ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
            (Opposite.op (restrictedAlgebra.{u, v} iStar), X),
          restrictedAlgebra.{u, v} iStar))
        ((restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app X,
          𝟙 (restrictedAlgebra.{u, v} iStar)))
      ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).evaluation
        (restrictedAlgebra.{u, v} iStar) X) (Category.comp_id _) rfl,
    tensor_restrictCoextendInternalHomIso_comp_evaluation.{u, v} φ E iStar adj adjE X,
    hsplit (restrictedAction.{u, v} φ E iStar adj adjE
      ((Dualizing.derivedHom.{u, v, u} φ).obj X)) (adj.counit.app X) (Category.comp_id _) rfl]
  simp only [Category.assoc]
  rw [(derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap_naturality (𝟙 Y)
    (show iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X) ⟶ X from adj.counit.app X)]

/-- **Invertibility passes from the single-ring diagonal to the diagonal along `φ`.**  Under the
same linearity hypothesis as
`Dualizing.ProjectionFormula.restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal`, the
restriction of the diagonal along `φ` is an isomorphism as soon as the single-ring tensor--Hom
diagonal of `D(A)` at `(Y, X, B[0])` is.  Every other factor of the square is invertible: the
projection formula and the symmetries by construction, and
`Dualizing.ProjectionFormula.restrictCoextendInternalHomIso` because it compares two right
adjoints of isomorphic functors. -/
theorem isIso_restrict_derivedTensorHomDiagonalAlongRingHom (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) (adjE : E.functor ⊣ iStar)
    (Y X : DerivedCategory (ModuleCat.{max u v} A))
    (hlin : restrictedAction.{u, v} φ E iStar adj adjE
            ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
              ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y)) ≫
          (derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app
            ((Dualizing.derivedHom.{u, v, u} φ).obj X) =
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
                ((Dualizing.derivedHom.{u, v, u} φ).obj X, E.functor.obj Y)),
              restrictedAlgebra.{u, v} iStar))
            (Y := ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
                (Y, iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)),
              restrictedAlgebra.{u, v} iStar))
            ((derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app
                ((Dualizing.derivedHom.{u, v, u} φ).obj X) ≫
              ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
                (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)) Y).hom,
              𝟙 (restrictedAlgebra.{u, v} iStar)) ≫
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorAssoc
            Y (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X))
            (restrictedAlgebra.{u, v} iStar)).hom ≫
          (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (Y, (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
                (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X),
                  restrictedAlgebra.{u, v} iStar)))
            (Y := (Y, iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)))
            (𝟙 Y, restrictedAction.{u, v} φ E iStar adj adjE
              ((Dualizing.derivedHom.{u, v, u} φ).obj X)) ≫
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
            Y (iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X))).hom)
    (hdiag : IsIso (Dualizing.derivedTensorHomDiagonalOverRing.{u, v} Y X
      (restrictedAlgebra.{u, v} iStar))) :
    IsIso (iStar.map ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X)) := by
  have hswapTensor : IsIso ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
      (X := (Y, iStar.obj ((Dualizing.derivedHom.{u, v, u} φ).obj X)))
      (Y := (Y, (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.obj
        (Opposite.op (restrictedAlgebra.{u, v} iStar), X)))
      (𝟙 Y, (restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app X)) :=
    ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.mapIso
      ((Iso.refl Y).prod
        ((restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).app X))).isIso_hom
  have hswapHom : IsIso ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.map
      (X := (Opposite.op (restrictedAlgebra.{u, v} iStar),
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj (Y, X)))
      (Y := (Opposite.op (restrictedAlgebra.{u, v} iStar),
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj (X, Y)))
      (𝟙 (Opposite.op (restrictedAlgebra.{u, v} iStar)),
        ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap Y X).hom)) :=
    ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).hom.mapIso
      ((Iso.refl (Opposite.op (restrictedAlgebra.{u, v} iStar))).prod
        ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap Y X))).isIso_hom
  have := hswapTensor
  have := hswapHom
  have := hdiag
  have hcomp : IsIso
      (iStar.map ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X) ≫
        (restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app
          ((tensorRightDerived.{u, v} A Y).obj X)) := by
    rw [restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal.{u, v} φ E iStar adj adjE Y X
      hlin]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((restrictCoextendInternalHomIso.{u, v} φ E iStar adj adjE).hom.app
      ((tensorRightDerived.{u, v} A Y).obj X))

end Dualizing.ProjectionFormula

end
