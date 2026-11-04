module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeTranspose
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaComponent

/-!
# The projection formula against the two counits of change of rings

Let `φ : A →+* B` be a homomorphism of commutative rings, write `i_*` for derived restriction of
scalars `D(B) ⥤ D(A)`, `Ext` for a model of derived extension of scalars `D(A) ⥤ D(B)` and
`RHom_A(B, -) : D(A) ⥤ D(B)` for derived coextension of scalars.  Two counits are in play, and
this file is about the projection formula
`Dualizing.ProjectionFormula.derivedProjNatIso` against each of them.

## The counit of restriction ⊣ coextension

`Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom` — the `B`-linear tensor--Hom
diagonal `Y ⊗ᴸ_A RHom_A(B, -) ⟶ RHom_A(B, Y ⊗ᴸ_A -)` along `φ` — is by construction the transpose
over [stacks 0A70] of a composite whose only non-elementary factor is the projection formula.
Composing its restriction with the counit of that adjunction therefore removes the transposition:

* `Dualizing.ProjectionFormula.restrict_derivedTensorHomDiagonalAlongRingHom_comp_counit` —
  `i_*(diagonal) ≫ ε = projection formula ≫ (ε ⊗ 𝟙)`;
* `Dualizing.ProjectionFormula.eq_derivedTensorHomDiagonalAlongRingHom_iff` — and that equation
  *characterises* the diagonal: a morphism of `D(B)` satisfies it exactly when it is the diagonal.
  So an identification of the restricted diagonal with another one may be proved by checking the
  other one against the projection formula and the counit, with the diagonal along `φ` no longer
  mentioned.

## The counit of extension ⊣ restriction

The first of the two coherences that the diagonal comparison of [stacks 0E2H] rests on -- the
second being `Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat` of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparisonBridge` -- is the compatibility
of the projection formula with the counit `ε` of [stacks 0GMT] and with the lax monoidal
structure map `μ = Dualizing.derivedTensorBaseChange` of derived base change, namely

`μ_{i_*G, N} ≫ Ext(derivedProjNatIso_N.inv.app G) ≫ ε_{G ⊗ᴸ_B Ext N} = ε_G ⊗ᴸ_B 𝟙_{Ext N}`

as morphisms `Ext(i_*G) ⊗ᴸ_B Ext N ⟶ G ⊗ᴸ_B Ext N`.  That is
`Dualizing.ProjectionFormula.ProjCounitCompat`, named here for the first time, and

* `Dualizing.ProjectionFormula.projCounitCompat_iff` **transposes `μ` away.**  Both `μ` and the
  derived-Hom base-change morphism of [stacks 0E1X] that `μ` is a double transpose of disappear:
  what is left is a closed formula for the *inverse* projection formula
  `derivedProjNatIso_N.inv.app G` as a transpose, over [stacks 0A63] and [stacks 0GMT], of the
  counit, read backwards through the change-of-rings isomorphism of [stacks 0E1W].  The
  transposition is `Dualizing.derivedTensorBaseChange_comp_eq_iff`; what this file adds is that
  the left-hand transpose of the equation above is the inverse projection formula itself, because
  the morphism it transposes is `Ext` of that followed by `ε`.

So the owed coherence is an identity between two named morphisms, with no existential and no
invertibility statement: the projection formula on one side, [stacks 0E1W] and the counit on the
other.

* `Dualizing.ProjectionFormula.projCounitCompatAt_iff_inv_eq` carries that transposition out
  against the *inverse* of the lax monoidal structure map instead, which is available because the
  structure map is invertible (`Dualizing.isIso_derivedTensorBaseChange`).  Then [stacks 0E1W]
  disappears too, and what is left is the identification of the inverse projection formula with
  `Dualizing.ProjectionFormula.canonicalProjInv`, the projection morphism that [stacks 0GMT] and
  that invertibility produce on their own.  That is the recognizable form of the residue: a
  morphism built from a K-flat representative agrees with one built from the two adjunctions.

## The owed coherence is a chain-level statement

Both sides of the equation are natural in both variables, and that is enough to reduce it to
representatives:

* `Dualizing.ProjectionFormula.projCounitCompat_of_rep` — in the object of `D(B)` the two sides are
  the natural transformations `Dualizing.ProjectionFormula.projCounitLeft` and
  `Dualizing.ProjectionFormula.projCounitRight`, so by uniqueness of transformations descending
  along the localization functor the compatibility at every object follows from the compatibility
  at the class of every cochain complex of `B`-modules;
* `Dualizing.ProjectionFormula.projCounitCompatAt_of_iso` — in the object of `D(A)` the equation is
  invariant under isomorphism, naturality of the projection formula in that variable being
  bifunctoriality, `Dualizing.ProjectionFormula.derivedProjBifunctorNatIso`;
* `Dualizing.ProjectionFormula.projCounitCompat_of_kFlat` — hence it is enough to prove the
  equation at the class of a **K-flat** complex of `A`-modules and the class of an arbitrary
  complex of `B`-modules.  That is exactly the situation in which every factor has a value at
  representatives: the projection formula by
  `Dualizing.ProjectionFormula.derivedProjNatIso_hom_app_Q`, the counit by
  `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq`, and the
  lax monoidal structure map through its mate characterisation
  `Dualizing.derivedTensorBaseChange_comp_map`.  So what the coherence still needs is a pasting of
  chain-level comparisons, and nothing else.

## The coherence in one variable: it is a mate identity

`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMate` removes the object of `D(B)`
from the obligation altogether.  Both sides of `ProjCounitCompatAt` are natural in it, and the
other triangle identity of the tensor--Hom adjunction of [stacks 0A63] recovers a transformation
of this shape from its component at an internal Hom
(`Dualizing.ProjectionFormula.natTrans_app_eq_coevaluation`), so the whole of `ProjCounitCompat`
at `N` is the single family of equations

`ω_{RHom_B(Ext N, W)} ≫ i_*(ev_B) = (0E1W_{N,W} ⊗ᴸ_A 𝟙_N) ≫ ev_A`

with `ω` the inverse projection formula and `0E1W` the component
`Dualizing.ProjectionFormula.homRestrictComponent` above — that is, the statement that the
projection formula and [stacks 0E1W] are **mates** under the two tensor--Hom adjunctions.  That
is `Dualizing.ProjectionFormula.projCounitCompat_of_eval` and, with the transposition carried
out, `Dualizing.ProjectionFormula.projCounitCompat_of_mate`;
`Dualizing.ProjectionFormula.eval_of_projCounitCompat` is the converse, so nothing is lost, the
unconditional half being
`Dualizing.ProjectionFormula.canonicalProjInv_comp_restrict_evaluation`.  There are no two
varying arguments left: `Dualizing.ProjectionFormula.projCounitCompat_of_eval_kFlat` asks for
that one equation at the class of a K-flat complex of `A`-modules and the class of an arbitrary
complex of `B`-modules and gives `ProjCounitCompat` at *every* object of `D(A)`, and
`Dualizing.ProjectionFormula.isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_eval` is the
invertibility [stacks 0E2H] needs on that equation together with the coherence of the structure
map.

## Implementation notes

`Dualizing.ProjectionFormula.modelComparison` and
`Dualizing.ProjectionFormula.homRestrictComponent` exist only to spell two terms at the type their
consumers state them at.  The first is the comparison of a
`CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars` written with the codomain
`(ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q` that
the base-change framework of [stacks 0E1X] uses, so that the left-derived instance is found by
instance search rather than being defeq to it.  The second is the component of [stacks 0E1W] with
the transported internal-Hom bifunctor
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom` replaced by the internal Hom of
[stacks 0A63]; the two agree, but only after unfolding a definition the module system does not
expose, so the identification is made once here instead of inside a large composite.

The projection-formula definitions are used at the module universe `max u v`, which forces the
universe arguments `.{u, max u v}` throughout this section: `Dualizing.derivedTensorBaseChange`
spells the tensor--Hom adjunction of [stacks 0A63] as
`derivedHomAdjunctionOverRing.{u, max u v, max u v + 1}`, and
`Dualizing.ProjectionFormula.tensorRightDerived.{u, v}` would spell it
`derivedHomAdjunctionOverRing.{u, v, max u v + 1}` — the same category, a different term.

No `@[stacks]` attribute is placed here: these are identities between morphisms belonging to
[stacks 0E9L] and [stacks 0E1X], whose tags sit where those are constructed.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars

universe u v

namespace Dualizing.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-! ### The counit step -/

/-- The transpose over [stacks 0A70] of a morphism, read as a composite with the counit. -/
private theorem map_comp_counit {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {Rt : D ⥤ C} (adj : L ⊣ Rt) (U : C) (V : D) (h : U ⟶ Rt.obj V) :
    L.map h ≫ adj.counit.app V = (adj.homEquiv U V).symm h := by
  simp [Adjunction.homEquiv_counit]

/-- A morphism recovered from its transpose over the counit. -/
private theorem homEquiv_map_comp_counit {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {Rt : D ⥤ C} (adj : L ⊣ Rt) (U : C) (V : D) (h : U ⟶ Rt.obj V) :
    adj.homEquiv U V (L.map h ≫ adj.counit.app V) = h := by
  rw [map_comp_counit, Equiv.apply_symm_apply]

/-- **The diagonal along a ring homomorphism, restricted and composed with the counit.**  For
`φ : A →+* B`, derived restriction of scalars applied to
`Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom` at `X`, followed by the counit
of [stacks 0A70] at `X ⊗ᴸ_A Y`, is the projection formula at `RHom_A(B, X)` followed by that
counit tensored with the identity of `Y`.

The diagonal is the transpose over [stacks 0A70] of exactly that composite
(`Dualizing.ProjectionFormula.homEquiv_derivedProjDiagonalTranspose`), so this is that
characterisation with the transposition carried out. -/
theorem restrict_derivedTensorHomDiagonalAlongRingHom_comp_counit (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (Y X : DerivedCategory (ModuleCat.{max u v} A)) :
    iStar.map ((derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X) ≫
        adj.counit.app ((tensorRightDerived.{u, v} A Y).obj X) =
      (derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app
          ((Dualizing.derivedHom.{u, v, u} φ).obj X) ≫
        (tensorRightDerived.{u, v} A Y).map (adj.counit.app X) := by
  rw [← homEquiv_derivedProjDiagonalTranspose.{u, v} φ E iStar adj Y X,
    map_comp_counit adj, Equiv.symm_apply_apply]
  rfl

/-- **The diagonal along a ring homomorphism is the unique morphism with that restriction.**  A
morphism `h : RHom_A(B, X) ⊗ᴸ_B (Y ⊗ᴸ_A B) ⟶ RHom_A(B, X ⊗ᴸ_A Y)` of `D(B)` whose restriction of
scalars composed with the counit of [stacks 0A70] is the projection formula followed by that
counit in the first tensor factor is
`Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom` at `X`, and conversely.

This is the shape in which the diagonal along `φ` can be identified with another morphism without
mentioning it: produce the candidate, restrict it, and check it against the projection formula and
the counit. -/
theorem eq_derivedTensorHomDiagonalAlongRingHom_iff (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ)
    (Y X : DerivedCategory (ModuleCat.{max u v} A))
    (h : (Dualizing.derivedHom.{u, v, u} φ ⋙
          tensorRightDerived.{u, v} B (E.functor.obj Y)).obj X ⟶
        (tensorRightDerived.{u, v} A Y ⋙ Dualizing.derivedHom.{u, v, u} φ).obj X) :
    iStar.map h ≫ adj.counit.app ((tensorRightDerived.{u, v} A Y).obj X) =
        (derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app
            ((Dualizing.derivedHom.{u, v, u} φ).obj X) ≫
          (tensorRightDerived.{u, v} A Y).map (adj.counit.app X) ↔
      h = (derivedTensorHomDiagonalAlongRingHom.{u, v} φ E iStar adj Y).app X := by
  rw [← restrict_derivedTensorHomDiagonalAlongRingHom_comp_counit.{u, v} φ E iStar adj Y X,
    map_comp_counit adj, map_comp_counit adj]
  exact (adj.homEquiv _ _).symm.apply_eq_iff_eq

/-! ### The owed compatibility with the counit -/

/-- The comparison of a total derived extension-of-scalars model, at the type the base-change
framework of [stacks 0E1X] states its hypotheses at. -/
noncomputable def modelComparison (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ) :
    DerivedCategory.Q ⋙ E.functor ⟶
      (ModuleCat.extendScalars.{u, u, max u v} φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  E.comparison

/-- The functor of a total derived extension-of-scalars model is the left derived functor of
extension of scalars on complexes, with respect to the quasi-isomorphisms, via
`modelComparison`. -/
instance modelComparison_isLeftDerived (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ) :
    E.functor.IsLeftDerivedFunctor (modelComparison.{u, v} φ E)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) :=
  E.isLeftDerived

/-- The adjunction of [stacks 0GMT] -- derived extension of scalars is left adjoint to derived
restriction of scalars -- at a total derived extension-of-scalars model. -/
noncomputable abbrev modelAdjunction (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ) :
    E.functor ⊣ (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory :=
  derivedExtensionScalarsAdjunction.{u, u, v} φ E.functor (modelComparison.{u, v} φ E)

/-- **[stacks 0E1W] at a single pair, in the vocabulary of [stacks 0A63].**  The
change-of-rings isomorphism for derived Hom is stated with the transported internal-Hom
bifunctor `Stacks.DerivedHom.ScalarTransportedInternalHom.hom`; this is its component at one
pair, read with the internal Hom of the tensor--Hom adjunction of [stacks 0A63] instead. -/
noncomputable def homRestrictComponent (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W : DerivedCategory (ModuleCat.{max u v} B)) :
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
        ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
          max u v + 1} B).hom.obj (Opposite.op (E.functor.obj N), W)) ⟶
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
          max u v + 1} A).hom.obj
        (Opposite.op N, (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W) :=
  (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{u, u, v} φ E.functor
    (modelComparison.{u, v} φ E)).inv.app (Opposite.op N, W)

/-- **The compatibility of the projection formula with the counit of extension of scalars**,
named.  Writing `Ext` for the model `E`, `i_*` for derived restriction of scalars, `μ` for the lax
monoidal structure map `Dualizing.derivedTensorBaseChange` of derived base change and `ε` for the
counit of [stacks 0GMT], this asserts

`μ_{i_*G, N} ≫ Ext(derivedProjNatIso_N.inv.app G) ≫ ε_{G ⊗ᴸ_B Ext N} = ε_G ⊗ᴸ_B 𝟙_{Ext N}`

at `G`, as morphisms `Ext(i_*G) ⊗ᴸ_B Ext N ⟶ G ⊗ᴸ_B Ext N`.

Nothing about `N` or `G` is assumed, and no invertibility is asserted: both sides are named
morphisms.  See the module documentation for why this is the coherence the diagonal comparison of
[stacks 0E2H] rests on. -/
def ProjCounitCompatAt (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (G : DerivedCategory (ModuleCat.{max u v} B)) : Prop :=
  Dualizing.derivedTensorBaseChange.{u, u, v} φ E.functor (modelComparison.{u, v} φ E)
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) N ≫
      (E.functor.map ((derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app G) ≫
        (modelAdjunction.{u, v} φ E).counit.app
          ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).obj G)) =
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
        max u v + 1} B).tensor.map
      (X := (E.functor.obj ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G),
        E.functor.obj N))
      (Y := (G, E.functor.obj N))
      ((modelAdjunction.{u, v} φ E).counit.app G, 𝟙 (E.functor.obj N))

/-- **The compatibility of the projection formula with the counit of extension of scalars**, at
every object of `D(B)`.  See `Dualizing.ProjectionFormula.ProjCounitCompatAt`. -/
def ProjCounitCompat (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) : Prop :=
  ∀ G : DerivedCategory (ModuleCat.{max u v} B), ProjCounitCompatAt.{u, v} φ E adj N G

/-- **The owed compatibility, with the lax monoidal structure map transposed away.**
`Dualizing.ProjectionFormula.ProjCounitCompat` holds exactly when the *inverse* projection formula
`derivedProjNatIso_N.inv.app G` is the transpose over [stacks 0A63] of the transpose over
[stacks 0GMT] of the counit of [stacks 0GMT] tensored with the identity, read backwards through the
change-of-rings isomorphism of [stacks 0E1W].

Neither the lax monoidal structure map `μ` nor the derived-Hom base-change morphism of
[stacks 0E1X] that it is a double transpose of occurs on the right: the transposition
`Dualizing.derivedTensorBaseChange_comp_eq_iff` removes both, and the left-hand transpose it
produces is the inverse projection formula itself, since the morphism being transposed is `Ext` of
that followed by the counit. -/
theorem projCounitCompat_iff (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N ↔
      ∀ G : DerivedCategory (ModuleCat.{max u v} B),
        (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app G =
          (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
                max u v + 1} A).homEquiv
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) N
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
                ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).obj G))
            ((modelAdjunction.{u, v} φ E).homEquiv
                ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) _
                (((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
                      max u v + 1} B).homEquiv
                    (E.functor.obj
                      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G))
                    (E.functor.obj N)
                    ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).obj G)).symm
                  ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
                      max u v + 1} B).tensor.map
                    (X := (E.functor.obj
                        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G),
                      E.functor.obj N))
                    (Y := (G, E.functor.obj N))
                    ((modelAdjunction.{u, v} φ E).counit.app G, 𝟙 (E.functor.obj N)))) ≫
              homRestrictComponent.{u, v} φ E N
                ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).obj G)) := by
  refine forall_congr' fun G => ?_
  refine (Dualizing.derivedTensorBaseChange_comp_eq_iff.{u, u, v} φ E.functor
    (modelComparison.{u, v} φ E) _ N _ _ _).trans ?_
  exact Iff.of_eq (congrArg (fun z => z = _)
    (homEquiv_map_comp_counit (modelAdjunction.{u, v} φ E) _ _ _))

/-! ### The owed compatibility as an identification of two projection morphisms -/

/-- **The canonical projection morphism.**  Writing `Ext` for the model `E`, `i_*` for derived
restriction of scalars, `η` and `ε` for the unit and the counit of [stacks 0GMT] and `ν` for
`Dualizing.derivedTensorBaseChangeSection` -- the inverse of the lax monoidal structure map `μ` of
derived base change -- this is the composite

`i_*G ⊗ᴸ_A N --η--> i_*Ext(i_*G ⊗ᴸ_A N) --i_*ν--> i_*(Ext(i_*G) ⊗ᴸ_B Ext N) --i_*(ε_G ⊗ 𝟙)-->
i_*(G ⊗ᴸ_B Ext N)`.

This is the projection morphism the two adjunctions produce on their own.  It is built from
[stacks 0GMT] and the invertibility of `Dualizing.derivedTensorBaseChange` alone: neither
[stacks 0A70] nor any K-flat representative enters, and it does not depend on the adjunction of
[stacks 0A70] that `Dualizing.ProjectionFormula.derivedProjNatIso` is constructed with. -/
noncomputable def canonicalProjInv (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (G : DerivedCategory (ModuleCat.{max u v} B)) :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G, N) ⟶
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
        ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).obj G) :=
  (modelAdjunction.{u, v} φ E).unit.app
      ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
          max u v + 1} A).tensor.obj
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G, N)) ≫
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
      (Dualizing.derivedTensorBaseChangeSection.{u, u, v} φ E.functor (modelComparison.{u, v} φ E)
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) N ≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
            max u v + 1} B).tensor.map
          (X := (E.functor.obj ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G),
            E.functor.obj N))
          (Y := (G, E.functor.obj N))
          ((modelAdjunction.{u, v} φ E).counit.app G, 𝟙 (E.functor.obj N)))

/-- **The owed compatibility says that the projection formula is the canonical projection
morphism.**  `Dualizing.ProjectionFormula.ProjCounitCompatAt` holds at `(N, G)` exactly when the
inverse of the projection formula there is
`Dualizing.ProjectionFormula.canonicalProjInv`.

This is `Dualizing.ProjectionFormula.projCounitCompat_iff` with the transposition carried out
against the *inverse* of the lax monoidal structure map rather than against the change-of-rings
isomorphism of [stacks 0E1W]: the structure map is invertible,
`Dualizing.isIso_derivedTensorBaseChange`, so the equation `μ ≫ ψ = ε ⊗ 𝟙` is `ψ = ν ≫ (ε ⊗ 𝟙)`,
and transposing that over [stacks 0GMT] leaves the projection formula on the left and the
canonical morphism on the right.  So what the coherence owes is an identification of two
morphisms with the same source and target, one built from a K-flat representative and one from
the two adjunctions. -/
theorem projCounitCompatAt_iff_inv_eq (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (G : DerivedCategory (ModuleCat.{max u v} B)) :
    ProjCounitCompatAt.{u, v} φ E adj N G ↔
      (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app G =
        canonicalProjInv.{u, v} φ E N G := by
  dsimp only [ProjCounitCompatAt, canonicalProjInv]
  rw [← Adjunction.homEquiv_unit, map_comp_counit (modelAdjunction.{u, v} φ E)]
  rw [← Equiv.symm_apply_eq]
  exact (Iso.eq_inv_comp
    ⟨_, _, Dualizing.derivedTensorBaseChange_comp_derivedTensorBaseChangeSection ..,
      Dualizing.derivedTensorBaseChangeSection_comp_derivedTensorBaseChange ..⟩).symm

/-- **The owed compatibility, as an identification of two projection morphisms**, at every object
of `D(B)`.  See `Dualizing.ProjectionFormula.projCounitCompatAt_iff_inv_eq`. -/
theorem projCounitCompat_iff_inv_eq (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N ↔
      ∀ G : DerivedCategory (ModuleCat.{max u v} B),
        (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app G =
          canonicalProjInv.{u, v} φ E N G :=
  forall_congr' fun G => projCounitCompatAt_iff_inv_eq.{u, v} φ E adj N G

/-! ### Reduction of the owed compatibility to representatives -/

/-- Tensoring on the right with a fixed object, on a morphism. -/
private theorem tensorRightDerived_map (R : Type u) [CommRing R]
    (M : DerivedCategory (ModuleCat.{max u v} R))
    {X Y : DerivedCategory (ModuleCat.{max u v} R)} (f : X ⟶ Y) :
    (tensorRightDerived.{u, v} R M).map f =
      (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, v, max u v + 1} R).tensor.map
        (X := (X, M)) (Y := (Y, M)) (f, 𝟙 M) :=
  rfl

/-- The left-hand side of `Dualizing.ProjectionFormula.ProjCounitCompatAt`, as a natural
transformation in the object of `D(B)`. -/
noncomputable def projCounitLeft (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⋙ E.functor ⋙
        tensorRightDerived.{u, max u v} B (E.functor.obj N) ⟶
      tensorRightDerived.{u, max u v} B (E.functor.obj N) where
  app G :=
    Dualizing.derivedTensorBaseChange.{u, u, v} φ E.functor (modelComparison.{u, v} φ E)
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) N ≫
      (E.functor.map ((derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app G) ≫
        (modelAdjunction.{u, v} φ E).counit.app
          ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).obj G))
  naturality G G' g := by
    have h1 := Dualizing.derivedTensorBaseChange_naturality.{u, u, v} φ E.functor
      (modelComparison.{u, v} φ E)
      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map g) (𝟙 N)
    rw [CategoryTheory.Functor.map_id] at h1
    have h2 := (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.naturality g
    have h3 := (modelAdjunction.{u, v} φ E).counit.naturality
      ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).map g)
    dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_map, Functor.id_obj] at h1 h2 h3 ⊢
    rw [tensorRightDerived_map] at h2
    simp only [Category.assoc]
    rw [tensorRightDerived_map, reassoc_of% h1, ← Functor.map_comp_assoc, h2,
      Functor.map_comp, Category.assoc, h3]

/-- The right-hand side of `Dualizing.ProjectionFormula.ProjCounitCompatAt`, as a natural
transformation in the object of `D(B)`: the counit of [stacks 0GMT] tensored with the identity. -/
noncomputable def projCounitRight (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⋙ E.functor ⋙
        tensorRightDerived.{u, max u v} B (E.functor.obj N) ⟶
      tensorRightDerived.{u, max u v} B (E.functor.obj N) :=
  Functor.whiskerRight (modelAdjunction.{u, v} φ E).counit
    (tensorRightDerived.{u, max u v} B (E.functor.obj N))

/-- **The owed compatibility is a question about representatives.**  Both sides of
`Dualizing.ProjectionFormula.ProjCounitCompatAt` are natural in the object of `D(B)`, so by
uniqueness of transformations descending along the localization functor the compatibility at every
object follows from the compatibility at the class of every cochain complex of `B`-modules. -/
theorem projCounitCompat_of_rep (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (h : ∀ L : CochainComplex (ModuleCat.{max u v} B) ℤ,
      ProjCounitCompatAt.{u, v} φ E adj N (DerivedCategory.Q.obj L)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  have key : projCounitLeft.{u, v} φ E adj N = projCounitRight.{u, v} φ E N :=
    Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} B) (ComplexShape.up ℤ)) (fun L => h L)
  exact fun G => NatTrans.congr_app key G

/-- **The owed compatibility is invariant under an isomorphism of the object of `D(A)`.**  Both
sides of `Dualizing.ProjectionFormula.ProjCounitCompatAt` are natural in that object: the lax
monoidal structure map by `Dualizing.derivedTensorBaseChange_naturality`, the projection formula
because it is the component of the bifunctorial form
`Dualizing.ProjectionFormula.derivedProjBifunctorNatIso`, and the counit of [stacks 0GMT] by its
own naturality. -/
theorem projCounitCompatAt_of_iso (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    {N N' : DerivedCategory (ModuleCat.{max u v} A)} (e : N ≅ N')
    (G : DerivedCategory (ModuleCat.{max u v} B))
    (h : ProjCounitCompatAt.{u, v} φ E adj N' G) :
    ProjCounitCompatAt.{u, v} φ E adj N G := by
  have h1 := Dualizing.derivedTensorBaseChange_naturality.{u, u, v} φ E.functor
    (modelComparison.{u, v} φ E)
    (𝟙 ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G)) e.hom
  rw [CategoryTheory.Functor.map_id] at h1
  have h2 : (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
          max u v + 1} A).tensor.map
          (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G, N))
          (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G, N'))
          (𝟙 ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G), e.hom) ≫
        (derivedProjNatIso.{u, max u v} φ E _ adj N').inv.app G =
      (derivedProjNatIso.{u, max u v} φ E _ adj N).inv.app G ≫
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
              max u v + 1} B).tensor.map
            (X := (G, E.functor.obj N)) (Y := (G, E.functor.obj N'))
            (𝟙 G, E.functor.map e.hom)) :=
    NatTrans.congr_app ((derivedProjBifunctorNatIso.{u, max u v} φ E
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj).inv.naturality e.hom) G
  have h3 : E.functor.map ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
              max u v + 1} B).tensor.map
            (X := (G, E.functor.obj N)) (Y := (G, E.functor.obj N'))
            (𝟙 G, E.functor.map e.hom))) ≫
        (modelAdjunction.{u, v} φ E).counit.app
          ((tensorRightDerived.{u, max u v} B (E.functor.obj N')).obj G) =
      (modelAdjunction.{u, v} φ E).counit.app
          ((tensorRightDerived.{u, max u v} B (E.functor.obj N)).obj G) ≫
        (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
            max u v + 1} B).tensor.map
          (X := (G, E.functor.obj N)) (Y := (G, E.functor.obj N'))
          (𝟙 G, E.functor.map e.hom) :=
    (modelAdjunction.{u, v} φ E).counit.naturality _
  have : IsIso ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
      max u v + 1} B).tensor.map
      (X := (G, E.functor.obj N)) (Y := (G, E.functor.obj N'))
      (𝟙 G, E.functor.map e.hom)) :=
    ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
      max u v + 1} B).tensor.mapIso ((Iso.refl G).prod (E.functor.mapIso e))).isIso_hom
  dsimp only [ProjCounitCompatAt] at h ⊢
  rw [← cancel_mono ((StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, max u v,
      max u v + 1} B).tensor.map
      (X := (G, E.functor.obj N)) (Y := (G, E.functor.obj N'))
      (𝟙 G, E.functor.map e.hom))]
  simp only [Category.assoc]
  rw [← h3, ← Functor.map_comp_assoc, ← h2, Functor.map_comp, Category.assoc,
    ← reassoc_of% h1, h, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp

/-- **The owed compatibility is a chain-level statement.**  It holds at every object of `D(A)` and
every object of `D(B)` as soon as it holds at the class of a K-flat complex of `A`-modules and the
class of an arbitrary complex of `B`-modules -- which is exactly the situation in which the
projection formula has a value at representatives,
`Dualizing.ProjectionFormula.derivedProjNatIso_hom_app_Q`. -/
theorem projCounitCompat_of_kFlat (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (h : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      CochainComplex.DerivedTensor.IsKFlat.{u, max u v} P →
      ∀ L : CochainComplex (ModuleCat.{max u v} B) ℤ,
        ProjCounitCompatAt.{u, v} φ E adj (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L))
    (N : DerivedCategory (ModuleCat.{max u v} A)) :
    ProjCounitCompat.{u, v} φ E adj N := by
  obtain ⟨P, sP, hP, -, hsP, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, max u v}
    (DerivedCategory.Q.objPreimage N)
  intro G
  exact projCounitCompatAt_of_iso.{u, v} φ E adj
    (asIso (DerivedCategory.Q.map sP) ≪≫ DerivedCategory.Q.objObjPreimageIso N).symm G
    (projCounitCompat_of_rep.{u, v} φ E adj (DerivedCategory.Q.obj P)
      (h P ((CochainComplex.DerivedTensor.isKFlat_iff_kFlat.{u, max u v} P).mpr hP)) G)

end Dualizing.ProjectionFormula

end
