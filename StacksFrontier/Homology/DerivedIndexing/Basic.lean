module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# The two indexings of the right derived functors agree

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, with `𝒜` having enough
injectives. There are two higher right derived functors of `F` available:

* Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived F n`, the degree-`n` homology of
  `F` applied to a chosen injective resolution read as a cochain complex indexed by `ℕ`; and
* the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus F i`, the degree-`i` homology of
  `RF(X[0])` in the bounded below derived category.

This file identifies them in the degrees where both are defined, and converts the long exact
sequence of the second into one for the first.

## Main results

* `Stacks.DerivedIndexing.rightDerivedIso`: the natural isomorphism
  `F.rightDerived n ≅ F.rightDerivedPlus (n : ℤ)` for `n : ℕ`.
* `Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`,
  `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`: vanishing transports both ways.
* `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`: **Mathlib's `ℕ`-indexed
  right derived functors form a cohomological `δ`-functor** ([Stacks, Tag 010Q],
  `CategoryTheory.DeltaFunctor`) — the long exact sequence
  `0 ⟶ R ⁰F(A) ⟶ R ⁰F(B) ⟶ R ⁰F(C) ⟶ R ¹F(A) ⟶ ⋯` of a short exact sequence of `𝒜`, with
  connecting morphisms natural in the sequence, and no hypothesis beyond additivity of `F` and
  enough injectives in `𝒜`.
* `Stacks.DerivedIndexing.singleDeltaFunctorStructure`,
  `Stacks.DerivedIndexing.derivedDeltaFunctorStructure`: the `δ`-functor structures
  ([Stacks, Tag 0150]) on `A ↦ A[0] : 𝒜 ⥤ D⁺(𝒜)` and on `A ↦ RF(A[0]) : 𝒜 ⥤ D⁺(ℬ)`, which is
  the datum [Stacks, Tag 05TE] quantifies over in this repository.
* `Stacks.DerivedIndexing.deltaFunctorOfNatIso`: a cohomological `δ`-functor transported along
  a family of natural isomorphisms; of independent use.
* `Stacks.DerivedIndexing.rightDerivedPlusIsoRes`,
  `Stacks.DerivedIndexing.rightDerivedIsoRes`: the two halves of the comparison, each
  identifying one of the derived functors with the homology of `F` applied to the chosen
  injective resolution, extended by zero to a complex indexed by `ℤ`.
* `Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans`,
  `Stacks.DerivedIndexing.rightDerivedPlusNatTrans`: the morphism `RF₁ ⟶ RF₂` of right derived
  functors on bounded below derived categories induced by a natural transformation
  `τ : F₁ ⟶ F₂`, and the resulting morphism `R ⁿF₁ ⟶ R ⁿF₂` of `ℤ`-indexed higher right derived
  functors.
* `Stacks.DerivedIndexing.rightDerivedIso_hom_naturality`: **the comparison of the two
  indexings is natural in the functor variable** — Mathlib's `CategoryTheory.NatTrans.rightDerived
  τ n`, computed on chosen injective resolutions, corresponds under `rightDerivedIso` to
  `rightDerivedPlusNatTrans τ n`, produced by the universal property of right derivation. This
  is what lets a construction made by one of the two routes be recognised in the other.

## Implementation notes

**The shape of the comparison.** Both sides are computed from the *same* chosen injective
resolution, so the comparison is a composite of isomorphisms through the common value
`H ⁿ(F(I))`, where `I = (injectiveResolution X).cochainComplex` is Mathlib's extension by zero
of `(injectiveResolution X).cocomplex` to a cochain complex indexed by `ℤ`
(`CategoryTheory.InjectiveResolution.cochainComplex`). Everything is natural in `X` because
`CategoryTheory.injectiveResolutions` is a functor into the homotopy category and because the
quasi-isomorphism `X[0] ⟶ I` is natural there: `InjectiveResolution.Hom.ι'_comp_hom'` is an
honest commuting square of complexes, and `resUnit` is its image under the quotient functor.
The `ℤ`-side then runs through the unit of `RF`, invertible at `I` by the Mathlib instance for
bounded below complexes with injective terms, and the `ℕ`-side through the two compatibilities
of extension by zero proved in `Stacks.DerivedIndexing.Extend`.

**Reassociation of functor composites.** `(E ⋙ G) ⋙ H` and `E ⋙ (G ⋙ H)` are definitionally
equal but are *not* unifiable as applications of `Functor.comp`: that constant carries universe
arguments for the intermediate category, and the two groupings instantiate them differently, so
a `Iso.trans` chain with metavariables in the middle fails. The chains are therefore cut into
the one-step definitions `zStep₁`-`zStep₅` and `nStep₁`, `nStep₂`, each with its source and
target written out: with no metavariables left, the remaining check is a concrete definitional
equality and succeeds.

**Transparency.** Three places need a term-mode proof because a tactic proof would build a goal
that is not type-correct at `implicit` transparency — the identification
`DerivedCategory.Plus.ι.obj ((Plus.singleFunctor C 0).obj X) = (DerivedCategory.singleFunctor
C 0).obj X` passes only through semireducible definitions. These are the naturality of `resUnit`
(a `congrArg`/`Eq.trans` chain over the commuting square), `ι_map_singleδPlus` (where `rw
[Category.assoc]` fails on exactly that ill-typed motive, and a `congrArg`/`Eq.trans` chain with
the `Functor.map_preimage` step named in a `have` replaces it), and the `comm₃` component of
`singleTrianglePlus_distinguished`. This is what
the `backward.isDefEq.respectTransparency false` pragma is covering in
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective.lean` and in
Mathlib's `Mathlib/CategoryTheory/Abelian/RightDerived.lean`; that pragma is not used here.
For the same reason `ι_map_singleδPlus` opens with
`dsimp only [singleδPlus]`: `Functor.map_preimage` cannot be rewritten under the semireducible
wrapper.

**Local instances.** `commShiftRightDerivedFunctorPlus`,
`natTransCommShiftRightDerivedFunctorPlusUnit` and `isTriangulated_rightDerivedFunctorPlus` are
re-exported from
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective.lean` and made
local instances, in a section
containing only the declarations that consume them.
Mathlib supplies the commutation with the shift for a `totalRightDerived` as an
instance, but `Functor.rightDerivedFunctorPlus` is a definition that instance search does not
unfold, which is why the three wrappers exist.

**Indexing arithmetic.** `((n : ℕ) : ℤ) + 1` and `((n + 1 : ℕ) : ℤ)` are equal by `rfl`, so the
degree shift in the connecting morphisms needs no cast lemma.

## What is not done

* No comparison is offered in negative degrees: `F.rightDerivedPlus i` for `i < 0` has no
  `ℕ`-indexed counterpart (it vanishes, by
  `CategoryTheory.Functor.isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits`).
* `rightDerivedIso` is not shown to be compatible with `Functor.toRightDerivedZero` or with the
  shift; no component of it is computed in closed form, and no `simp` lemma describes
  `rightDerivedIso.hom.app X`. Compatibility with `CategoryTheory.NatTrans.rightDerived` **is**
  proved, as `rightDerivedIso_hom_naturality`.
* Nothing *here* compares `rightDerivedIso` with the *edge* morphisms of a composite of two
  functors; that is a separate question from the naturality proved in this file, because an edge
  morphism is not of the form `NatTrans.rightDerived τ n` for a transformation `τ` of functors
  on the source category. For the **first** edge morphism it is now done, in
  `StacksFrontier.Homology.DerivedIndexing.Composite`: `Stacks.DerivedIndexing.rightDerivedPlusEdge`
  is the comparison `R ⁱG(F ℱ) ⟶ R ⁱ(G ∘ F)(ℱ)` built from the composition isomorphism
  `R(G ∘ F) ≅ RG ∘ RF` on bounded below derived categories, and
  `Stacks.DerivedIndexing.edge_comp_rightDerivedIso` identifies
  `Stacks.Cohomology.RightDerivedEdge.edge` with it.
* **For the *second* edge morphism it is now done as well.** The counterpart of
  `Stacks.DerivedIndexing.edge_comp_rightDerivedIso` for
  `Stacks.Cohomology.RightDerivedCoEdge.secondEdge` — the co-edge `R ⁿ(Q ∘ P) ⟶ Q ∘ R ⁿP` of
  `StacksFrontier.Algebra.Homology.RightDerivedCoEdge` — is
  `Stacks.DerivedIndexing.secondEdge_comp_rightDerivedIso`, and the property it establishes is
  named `Stacks.DerivedIndexing.IsIndexedCoEdge` in
  `StacksDraft.Homology.DerivedIndexing.CoEdge` and proved of
  `Stacks.DerivedIndexing.coedge` in
  `StacksDraft.Homology.DerivedIndexing.CoEdgeIndexed`
  (`Stacks.DerivedIndexing.isIndexedCoEdge_coedge`). The family itself,
  `Stacks.DerivedIndexing.coedge` in
  `StacksDraft.Homology.DerivedIndexing.CoEdgeConstruction`, is built from
  `Stacks.DerivedIndexing.rightDerivedPlusCompIso` together with the comparison
  `H ⁱ(RQ Z) ⟶ Q(H ⁱ Z)` for `Z` in `D⁺(ℬ)` — which is
  `Stacks.DerivedIndexing.plusCoEdge`, an instance of
  `Stacks.PlusDerivedFunctor.homologyEdge`
  (`StacksDraft.Algebra.Homology.DerivedCategory.PlusDerivedFunctorHomologyEdge`), the bounded
  below counterpart of the unbounded `Stacks.DerivedFunctor.homologyEdge`. The bounded below
  construction had to be redone rather than transported, because no comparison between
  `CategoryTheory.Functor.rightDerivedFunctorPlus` and
  `CategoryTheory.Functor.totalRightDerived` is available ([Stacks, Tag 05T5] is formalized in
  `StacksFrontier.Algebra.Homology.DerivedCategory.BoundedDerivedFunctorComparison` as a statement
  about right derived *values*, not as a natural isomorphism of functors). The proof runs
  through the statement (★) of
  `StacksDraft.Homology.DerivedIndexing.CoEdgeConstruction` — the `D⁺` comparison read along
  the class of a bounded below complex is
  `Stacks.Cohomology.RightDerivedCoEdge.homologyToMapHomology`
  (`Stacks.DerivedIndexing.plusHomologyCoEdge_app_eq`) — composed with the extension by zero
  (`Stacks.DerivedIndexing.homologyToMapHomology_extend`), the identification of `RP(X[0])` with
  the class of that extension (`Stacks.DerivedIndexing.resDerivedIso`,
  `Stacks.DerivedIndexing.rightDerivedPlusIsoRes`) and the composition isomorphism
  (`Stacks.DerivedIndexing.rightDerivedPlusCompIso_hom_app_comp_resDerivedIso`); both halves
  land on the comparison `H ⁿ(Q -) ⟶ Q(H ⁿ -)` at `P` applied to the chosen extended injective
  resolution. The consumer is
  `Stacks.ComparingTopologies.higherDirectImageComparison`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/ChangeOfTopology/HigherDirectImages.lean`),
  defined as `Stacks.Cohomology.RightDerivedEdge.edge` followed by
  `Stacks.Cohomology.RightDerivedCoEdge.secondEdge`: both factors now have their indexed
  description, which is what input (iii) of the first assertion of [Stacks, Tag 0EZF] was
  blocked on. Input (iii) itself — that `derivedComparisonBaseChange` induces that composite on
  cohomology sheaves in degrees at most `n` — is still to be assembled, as recorded in the tag
  string of
  `Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition_of_singleCoveringDescent`
  in the file `VanishingConditionAllDegrees.lean` of the directory
  `StacksFrontier/CategoryTheory/Sites/Cohomology/ChangeOfTopology/`.
  The universe constraint is the one `edge_comp_rightDerivedIso` carries: `HasDerivedCategory.{w}`
  for both source categories.
* Universality of the `ℕ`-indexed `δ`-functor (the second half of [Stacks, Tag 05TE]) is not
  transported; only part (1), the long exact sequence, is.
* No stacks attribute is attached anywhere in this file: this is general homological
  algebra, and the nearby tags belong to other chapters.
-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape

namespace Stacks.DerivedIndexing

universe v v' u u'

section Transport

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Abelian C] [Abelian D]

/-! ### Transport of the long exact sequence -/

/-- **Transport of a cohomological `δ`-functor along natural isomorphisms.** If `E` is a
cohomological `δ`-functor (Stacks 010Q) and `G ⁿ ≅ E ⁿ` for every `n`, then the family `G` is
again a cohomological `δ`-functor, with connecting morphisms conjugated by the isomorphisms. -/
noncomputable def deltaFunctorOfNatIso (E : CategoryTheory.DeltaFunctor C D) (G : ℕ → C ⥤ D)
    (e : ∀ n, E.functor n ≅ G n) : CategoryTheory.DeltaFunctor C D :=
  have hG : ∀ n, (G n).Additive := fun n ↦ Functor.additive_of_iso (e n)
  { functor := G
    additive := hG
    δ := fun {S} hS n ↦ (e n).inv.app S.X₃ ≫ E.δ hS n ≫ (e (n + 1)).hom.app S.X₁
    map_g_δ := fun {S} hS n ↦ by
      rw [← Category.assoc, (e n).inv.naturality S.g, Category.assoc,
        ← Category.assoc ((E.functor n).map S.g), E.map_g_δ hS n, zero_comp, comp_zero]
    δ_map_f := fun {S} hS n ↦ by
      rw [Category.assoc, Category.assoc, ← (e (n + 1)).hom.naturality S.f,
        ← Category.assoc (E.δ hS n), E.δ_map_f hS n, zero_comp, comp_zero]
    mono_map_f := fun {S} hS ↦ by
      have h0 : (G 0).map S.f =
          (e 0).inv.app S.X₁ ≫ (E.functor 0).map S.f ≫ (e 0).hom.app S.X₂ := by
        rw [← Category.assoc, ← (e 0).inv.naturality S.f, Category.assoc, Iso.inv_hom_id_app,
          Category.comp_id]
      have := E.mono_map_f hS
      rw [h0]
      infer_instance
    exact_map := fun {S} hS n ↦
      ShortComplex.exact_of_iso (S.mapNatIso (e n)) (E.exact_map hS n)
    exact_δ₁ := fun {S} hS n ↦
      ShortComplex.exact_of_iso (ShortComplex.isoMk ((e n).app S.X₂) ((e n).app S.X₃)
        ((e (n + 1)).app S.X₁) (by simp) (by simp)) (E.exact_δ₁ hS n)
    exact_δ₂ := fun {S} hS n ↦
      ShortComplex.exact_of_iso (ShortComplex.isoMk ((e n).app S.X₃) ((e (n + 1)).app S.X₁)
        ((e (n + 1)).app S.X₂) (by simp) (by simp)) (E.exact_δ₂ hS n)
    δ_naturality := fun {S T} hS hT φ n ↦ by
      simp only [Category.assoc]
      rw [← Category.assoc, (e n).inv.naturality φ.τ₃]
      simp only [Category.assoc]
      rw [← Category.assoc ((E.functor n).map φ.τ₃), E.δ_naturality hS hT φ n]
      simp only [Category.assoc]
      rw [(e (n + 1)).hom.naturality φ.τ₁] }

@[simp]
lemma deltaFunctorOfNatIso_functor (E : CategoryTheory.DeltaFunctor C D) (G : ℕ → C ⥤ D)
    (e : ∀ n, E.functor n ≅ G n) (n : ℕ) : (deltaFunctorOfNatIso E G e).functor n = G n := rfl


end Transport

section SingleDelta

open Pretriangulated

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {S : ShortComplex C}

/-- The connecting morphism `X₃[0] ⟶ X₁[0]⟦1⟧` of a short exact sequence, read in the bounded
below derived category. -/
noncomputable def singleδPlus (hS : S.ShortExact) :
    (DerivedCategory.Plus.singleFunctor C 0).obj S.X₃ ⟶
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Plus.ι.preimage (hS.singleδ ≫
    (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))

/-- The defining property of `singleδPlus`: it is `hS.singleδ`, read through the inclusion of
the bounded below derived category and its commutation with the shift. -/
lemma ι_map_singleδPlus (hS : S.ShortExact) :
    DerivedCategory.Plus.ι.map (singleδPlus hS) ≫
        (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) = hS.singleδ := by
  have h1 : DerivedCategory.Plus.ι.map (singleδPlus hS) =
      hS.singleδ ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) :=
    DerivedCategory.Plus.ι.map_preimage _
  exact (congrArg (fun w ↦ w ≫ (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)) h1).trans
    ((Category.assoc hS.singleδ _ _).trans
      ((congrArg (fun w ↦ hS.singleδ ≫ w)
        (Iso.inv_hom_id_app (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ))
          ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁))).trans (Category.comp_id _)))

/-- The triangle `A[0] ⟶ B[0] ⟶ C[0] ⟶ A[0]⟦1⟧` of a short exact sequence is distinguished in
the bounded below derived category. -/
lemma singleTrianglePlus_distinguished (hS : S.ShortExact) :
    Triangle.mk ((DerivedCategory.Plus.singleFunctor C 0).map S.f)
        ((DerivedCategory.Plus.singleFunctor C 0).map S.g) (singleδPlus hS) ∈
      distTriang (DerivedCategory.Plus C) := by
  rw [← DerivedCategory.Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _
    (Triangle.isoMk _ _ ((DerivedCategory.Plus.singleFunctorιIso C 0).app S.X₁)
      ((DerivedCategory.Plus.singleFunctorιIso C 0).app S.X₂)
      ((DerivedCategory.Plus.singleFunctorιIso C 0).app S.X₃) ?_ ?_ ?_)
  · exact (DerivedCategory.Plus.singleFunctorιIso C 0).hom.naturality S.f
  · exact (DerivedCategory.Plus.singleFunctorιIso C 0).hom.naturality S.g
  · change (DerivedCategory.Plus.ι.map (singleδPlus hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)) ≫
        (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
          (𝟙 ((DerivedCategory.singleFunctor C 0).obj S.X₁)) =
      𝟙 ((DerivedCategory.singleFunctor C 0).obj S.X₃) ≫ hS.singleδ
    exact (congrArg (fun w ↦ (DerivedCategory.Plus.ι.map (singleδPlus hS) ≫
          (DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
            ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁)) ≫ w)
        (CategoryTheory.Functor.map_id (shiftFunctor (DerivedCategory C) (1 : ℤ))
          ((DerivedCategory.singleFunctor C 0).obj S.X₁))).trans
      ((Category.comp_id _).trans ((ι_map_singleδPlus hS).trans (Category.id_comp _).symm))

/-- **The `δ`-functor structure on `X ↦ X[0] : 𝒜 ⥤ D⁺(𝒜)`** ([Stacks, Tag 0150]): the bounded
below form of `CategoryTheory.ShortComplex.ShortExact.singleTriangle`. -/
noncomputable def singleDeltaFunctorStructure :
    Functor.DeltaFunctorStructure C (DerivedCategory.Plus C)
      (DerivedCategory.Plus.singleFunctor C 0) where
  δ hS := singleδPlus hS
  distinguished hS := singleTrianglePlus_distinguished hS
  δ_naturality {S₁ S₂} h₁ h₂ φ := by
    apply DerivedCategory.Plus.ι.map_injective
    rw [Functor.map_comp, Functor.map_comp, ← cancel_mono
      ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S₂.X₁)),
      Category.assoc, Category.assoc, Functor.commShiftIso_hom_naturality,
      ← Category.assoc, ι_map_singleδPlus h₁, ι_map_singleδPlus h₂]
    exact (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ).comm₃

end SingleDelta

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
  [EnoughInjectives C]

/-- The descent of a morphism to the chosen injective resolutions, packaged as a morphism of
injective resolutions. -/
noncomputable def descHom {X Y : C} (f : X ⟶ Y) :
    InjectiveResolution.Hom (injectiveResolution X) (injectiveResolution Y) f where
  hom := InjectiveResolution.desc f _ _
  ι_f_zero_comp_hom_f_zero := by
    simpa using InjectiveResolution.desc_commutes_zero f (injectiveResolution Y)
      (injectiveResolution X)

/-- The chosen injective resolution, extended by zero to a complex indexed by `ℤ` and read in
the homotopy category. -/
noncomputable def resH : C ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  injectiveResolutions C ⋙ embeddingUpNat.extendHomotopyFunctor C

lemma resH_obj (X : C) : resH.obj X =
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (injectiveResolution X).cochainComplex := rfl

/-- The canonical map from `X` placed in degree `0` to its extended injective resolution. -/
noncomputable def resUnit : HomotopyCategory.singleFunctor C 0 ⟶ resH where
  app X := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (injectiveResolution X).ι'
  naturality {X Y} f :=
    have h : (injectiveResolution X).ι' ≫ (descHom f).hom' =
        (CochainComplex.singleFunctor C 0).map f ≫ (injectiveResolution Y).ι' :=
      InjectiveResolution.Hom.ι'_comp_hom' (descHom f)
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map h.symm).trans
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_comp _ _))

lemma resH_obj_mem (X : C) : HomotopyCategory.plus C (resH.obj X) := by
  rw [resH_obj, HomotopyCategory.plus_quotient_obj_iff]
  exact ⟨0, inferInstance⟩

/-- The extended injective resolution, read in the bounded below homotopy category. -/
noncomputable def resPlus : C ⥤ HomotopyCategory.Plus C :=
  (HomotopyCategory.plus C).lift resH resH_obj_mem

/-- `resPlus` followed by the inclusion of the bounded below complexes is `resH`. -/
noncomputable def resPlusCompιIso :
    resPlus ⋙ HomotopyCategory.Plus.ι C ≅ (resH : C ⥤ HomotopyCategory C (ComplexShape.up ℤ)) :=
  Iso.refl _

instance injective_resPlus_obj_X (X : C) (n : ℤ) : Injective ((resPlus.obj X).obj.as.X n) :=
  inferInstanceAs (Injective ((injectiveResolution X).cochainComplex.X n))

section

variable [HasDerivedCategory C]

instance isIso_Qh_map_resUnit_app (X : C) :
    IsIso (DerivedCategory.Qh.map (resUnit.app (C := C) X)) :=
  have h : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (injectiveResolution X).ι')) := by
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  h

instance isIso_whiskerRight_resUnit :
    IsIso (Functor.whiskerRight (resUnit (C := C)) DerivedCategory.Qh) :=
  have : ∀ X : C,
      IsIso ((Functor.whiskerRight (resUnit (C := C)) DerivedCategory.Qh).app X) :=
    fun X ↦ isIso_Qh_map_resUnit_app X
  NatIso.isIso_of_isIso_app _

/-- In the bounded below derived category, `X` placed in degree `0` is its extended injective
resolution. -/
noncomputable def singleIsoResPlusQh :
    DerivedCategory.Plus.singleFunctor C 0 ≅ resPlus ⋙ DerivedCategory.Plus.Qh :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (DerivedCategory.Plus.singleFunctorιIso C 0 ≪≫
      DerivedCategory.singleFunctorIsoCompQh C 0 ≪≫
      asIso (Functor.whiskerRight (resUnit (C := C)) DerivedCategory.Qh) ≪≫
      (Functor.isoWhiskerRight (resPlusCompιIso (C := C)) DerivedCategory.Qh).symm ≪≫
      (Functor.isoWhiskerLeft resPlus (DerivedCategory.Plus.QhCompιIsoιCompQh C)).symm)

end

section

variable [HasDerivedCategory D]

/-- Homology on the bounded below derived category, computed on the homotopy category. -/
noncomputable def plusHomologyIso (n : ℤ) :
    DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor D n ≅
      HomotopyCategory.Plus.ι D ⋙ HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n :=
  Functor.isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh D)
      (DerivedCategory.homologyFunctor D n) ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι D)
      (DerivedCategory.homologyFunctorFactorsh D n)

end

variable (F : C ⥤ D) [F.Additive] [HasDerivedCategory C] [HasDerivedCategory D]

instance isIso_whiskerLeft_resPlus_unit :
    IsIso (Functor.whiskerLeft resPlus F.rightDerivedFunctorPlusUnith) :=
  have : ∀ X : C,
      IsIso ((Functor.whiskerLeft resPlus F.rightDerivedFunctorPlusUnith).app X) :=
    fun X ↦ inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnith.app (resPlus.obj X)))
  NatIso.isIso_of_isIso_app _

/-- On the extended injective resolutions the unit of the right derived functor is invertible:
`F` computes `RF` there. -/
noncomputable def resDerivedIso :
    resPlus ⋙ F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      resPlus ⋙ DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus :=
  asIso (Functor.whiskerLeft resPlus F.rightDerivedFunctorPlusUnith)

/-- `F.mapHomotopyCategoryPlus` is induced by `F.mapHomotopyCategory`. -/
noncomputable def mapPlusCompιIso :
    F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ≅
      HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) :=
  Iso.refl _

section Steps

variable (n : ℤ)

/-- One step of the chain computing the `ℤ`-indexed right derived functor. -/
noncomputable def zStep₁ :
    F.rightDerivedPlus n ≅ resPlus ⋙ (DerivedCategory.Plus.Qh ⋙
      F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D n) :=
  Functor.isoWhiskerRight (singleIsoResPlusQh (C := C))
    (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D n)

/-- One step of the chain computing the `ℤ`-indexed right derived functor. -/
noncomputable def zStep₂ :
    resPlus ⋙ (DerivedCategory.Plus.Qh ⋙
        F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D n) ≅
      resPlus ⋙ (F.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor D n) :=
  Functor.isoWhiskerRight (resDerivedIso F).symm (DerivedCategory.Plus.homologyFunctor D n)

/-- One step of the chain computing the `ℤ`-indexed right derived functor. -/
noncomputable def zStep₃ :
    resPlus ⋙ (F.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor D n) ≅
      resPlus ⋙ (F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n) :=
  Functor.isoWhiskerLeft (resPlus ⋙ F.mapHomotopyCategoryPlus) (plusHomologyIso (D := D) n)

/-- One step of the chain computing the `ℤ`-indexed right derived functor. -/
noncomputable def zStep₄ :
    resPlus ⋙ (F.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι D ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n) ≅
      resPlus ⋙ (HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n) :=
  Functor.isoWhiskerLeft resPlus (Functor.isoWhiskerRight (mapPlusCompιIso F)
    (HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n))

/-- One step of the chain computing the `ℤ`-indexed right derived functor. -/
noncomputable def zStep₅ :
    resPlus ⋙ (HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n) ≅
      resH ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n :=
  Functor.isoWhiskerRight (resPlusCompιIso (C := C))
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n)

end Steps

/-- **The `ℤ`-indexed right derived functor on an injective resolution.** `R ⁿ F` is the
degree-`n` homology of `F` applied to the extended chosen injective resolution. -/
noncomputable def rightDerivedPlusIsoRes (n : ℤ) :
    F.rightDerivedPlus n ≅
      resH ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n :=
  zStep₁ F n ≪≫ zStep₂ F n ≪≫ zStep₃ F n ≪≫ zStep₄ F n ≪≫ zStep₅ F n

section NatSteps

variable (n : ℕ)

/-- One step of the chain computing the `ℕ`-indexed right derived functor. -/
noncomputable def nStep₁ :
    F.rightDerived n ≅ injectiveResolutions C ⋙ (F.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
      embeddingUpNat.extendHomotopyFunctor D ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)) :=
  Functor.isoWhiskerLeft (injectiveResolutions C)
    (Functor.isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℕ))
      (extendHomotopyHomologyNatIso embeddingUpNat
        (rfl : embeddingUpNat.f n = (n : ℤ))).symm)

/-- One step of the chain computing the `ℕ`-indexed right derived functor. -/
noncomputable def nStep₂ :
    injectiveResolutions C ⋙ (F.mapHomotopyCategory (ComplexShape.up ℕ) ⋙
        embeddingUpNat.extendHomotopyFunctor D ⋙
          HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)) ≅
      resH ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ) :=
  Functor.isoWhiskerLeft (injectiveResolutions C)
    (Functor.isoWhiskerRight (mapExtendHomotopyNatIso F embeddingUpNat)
      (HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)))

end NatSteps

/-- **Mathlib's `ℕ`-indexed right derived functor on an injective resolution.** -/
noncomputable def rightDerivedIsoRes (n : ℕ) :
    F.rightDerived n ≅
      resH ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ) :=
  nStep₁ F n ≪≫ nStep₂ F n

/-- **The comparison of the two indexings of the right derived functors.** -/
noncomputable def rightDerivedIso (n : ℕ) : F.rightDerived n ≅ F.rightDerivedPlus (n : ℤ) :=
  rightDerivedIsoRes F n ≪≫ (rightDerivedPlusIsoRes F (n : ℤ)).symm


section FunctorNaturality

/-- Two commuting squares pasted side by side. Stated in the shape in which the comparisons of
this file produce it: the left-hand vertical composite is bracketed as it comes out of
`Iso.trans`. -/
private lemma paste_squares {E : Type*} [Category* E] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : E}
    (a : X₁ ⟶ X₂) (b₁ : X₁ ⟶ Y₁) (b₂ : X₂ ⟶ Y₂) (a' : Y₁ ⟶ Y₂) (c₁ : Y₁ ⟶ Z₁)
    (c₂ : Y₂ ⟶ Z₂) (d : Z₁ ⟶ Z₂) (h₁ : a ≫ b₂ = b₁ ≫ a') (h₂ : a' ≫ c₂ = c₁ ≫ d) :
    a ≫ b₂ ≫ c₂ = (b₁ ≫ c₁) ≫ d := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Five commuting squares pasted side by side, in the shape in which the five-step comparison
`rightDerivedPlusIsoRes` produces it. -/
private lemma paste_squares₅ {E : Type*} [Category* E]
    {X₀ X₁ X₂ X₃ X₄ X₅ Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ : E}
    (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁) (v₂ : X₂ ⟶ Y₂) (v₃ : X₃ ⟶ Y₃) (v₄ : X₄ ⟶ Y₄)
    (v₅ : X₅ ⟶ Y₅)
    (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (a₃ : X₂ ⟶ X₃) (a₄ : X₃ ⟶ X₄) (a₅ : X₄ ⟶ X₅)
    (b₁ : Y₀ ⟶ Y₁) (b₂ : Y₁ ⟶ Y₂) (b₃ : Y₂ ⟶ Y₃) (b₄ : Y₃ ⟶ Y₄) (b₅ : Y₄ ⟶ Y₅)
    (h₁ : v₀ ≫ b₁ = a₁ ≫ v₁) (h₂ : v₁ ≫ b₂ = a₂ ≫ v₂) (h₃ : v₂ ≫ b₃ = a₃ ≫ v₃)
    (h₄ : v₃ ≫ b₄ = a₄ ≫ v₄) (h₅ : v₄ ≫ b₅ = a₅ ≫ v₅) :
    v₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) ≫ v₅ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅]
  simp only [Category.assoc]

/-- A commuting square with invertible horizontal edges, transported to the inverses. -/
lemma comm_of_comm_inv {E : Type*} [Category* E] {X₁ X₂ Y₁ Y₂ : E}
    (u₁ : X₁ ≅ Y₁) (u₂ : X₂ ≅ Y₂) (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    (h : u₁.hom ≫ g = f ≫ u₂.hom) : g ≫ u₂.inv = u₁.inv ≫ f := by
  rw [← cancel_epi u₁.hom, ← Category.assoc, h, Category.assoc, u₂.hom_inv_id,
    Category.comp_id, ← Category.assoc, u₁.hom_inv_id, Category.id_comp]

variable {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive] (τ : F₁ ⟶ F₂)

section NatIndexed

omit [HasDerivedCategory C] [HasDerivedCategory D]

/-- The transformation induced by `τ` on the degree-`n` homology of the functor applied termwise
to the chosen extended injective resolutions. Both `rightDerivedIsoRes` and
`rightDerivedPlusIsoRes` land here, so this is where the two indexings are compared. -/
noncomputable def resNatTrans (n : ℤ) :
    resH ⋙ F₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n ⟶
      resH ⋙ F₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n :=
  Functor.whiskerLeft resH (Functor.whiskerRight
    (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
    (HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n))

/-- The components of `resNatTrans`. -/
lemma resNatTrans_app (n : ℤ) (X : C) :
    (resNatTrans τ n).app X =
      (HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n).map
        ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app (resH.obj X)) := rfl

/-- The components of Mathlib's `ℕ`-indexed `CategoryTheory.NatTrans.rightDerived`: it is `τ`
applied termwise to the chosen injective resolution, read on homology. -/
lemma natTrans_rightDerived_app (n : ℕ) (X : C) :
    (NatTrans.rightDerived τ n).app X =
      (HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n).map
        ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℕ)).app
          ((injectiveResolutions C).obj X)) := rfl

/-- The components of the first step of the comparison of the `ℕ`-indexed derived functor with
the homology of the extended injective resolution. -/
lemma nStep₁_hom_app (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) :
    (nStep₁ F n).hom.app X =
      (extendHomotopyHomologyNatIso embeddingUpNat
          (rfl : embeddingUpNat.f n = (n : ℤ))).inv.app
        ((F.mapHomotopyCategory (ComplexShape.up ℕ)).obj
          ((injectiveResolutions C).obj X)) := rfl

/-- The components of the second step of that comparison. -/
lemma nStep₂_hom_app (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) :
    (nStep₂ F n).hom.app X =
      (HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)).map
        ((mapExtendHomotopyNatIso F embeddingUpNat).hom.app
          ((injectiveResolutions C).obj X)) := rfl

/-- **`rightDerivedIsoRes` is natural in the functor variable, componentwise.** -/
theorem rightDerivedIsoRes_hom_app_naturality (n : ℕ) (X : C) :
    (NatTrans.rightDerived τ n).app X ≫ (rightDerivedIsoRes F₂ n).hom.app X =
      (rightDerivedIsoRes F₁ n).hom.app X ≫ (resNatTrans τ (n : ℤ)).app X := by
  let RX := (injectiveResolutions C).obj X
  let tt := (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℕ)).app RX
  let Hn := HomotopyCategory.homologyFunctor D (ComplexShape.up ℕ) n
  let Hz := HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) (n : ℤ)
  let ez := extendHomotopyHomologyNatIso (A := D) embeddingUpNat
    (rfl : embeddingUpNat.f n = (n : ℤ))
  have h₁ : Hn.map tt ≫ ez.inv.app ((F₂.mapHomotopyCategory (ComplexShape.up ℕ)).obj RX) =
      ez.inv.app ((F₁.mapHomotopyCategory (ComplexShape.up ℕ)).obj RX) ≫
        Hz.map ((embeddingUpNat.extendHomotopyFunctor D).map tt) :=
    ez.inv.naturality tt
  have h₂ : Hz.map ((embeddingUpNat.extendHomotopyFunctor D).map tt) ≫
        Hz.map ((mapExtendHomotopyNatIso F₂ embeddingUpNat).hom.app RX) =
      Hz.map ((mapExtendHomotopyNatIso F₁ embeddingUpNat).hom.app RX) ≫
        Hz.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
          ((embeddingUpNat.extendHomotopyFunctor C).obj RX)) := by
    rw [← Hz.map_comp, ← Hz.map_comp]
    exact congrArg Hz.map
      (NatTrans.congr_app (mapExtendHomotopyNatIso_hom_natTrans τ embeddingUpNat) RX)
  exact paste_squares _ _ _ _ _ _ _ h₁ h₂

/-- **`rightDerivedIsoRes` is natural in the functor variable**: Mathlib's `ℕ`-indexed
`CategoryTheory.NatTrans.rightDerived` agrees, through the identification of `R ⁿF` with the
homology of `F` applied to the chosen extended injective resolution, with the transformation
induced by `τ` on that homology. -/
theorem rightDerivedIsoRes_hom_naturality (n : ℕ) :
    NatTrans.rightDerived τ n ≫ (rightDerivedIsoRes F₂ n).hom =
      (rightDerivedIsoRes F₁ n).hom ≫ resNatTrans τ (n : ℤ) :=
  NatTrans.ext (funext fun X ↦ rightDerivedIsoRes_hom_app_naturality τ n X)

end NatIndexed

/-- The morphism of right derived functors on bounded below derived categories induced by a
natural transformation of additive functors. It is the transformation produced by the universal
property of right derivation from `τ` applied degreewise. -/
noncomputable def rightDerivedFunctorPlusNatTrans :
    F₁.rightDerivedFunctorPlus ⟶ F₂.rightDerivedFunctorPlus :=
  Functor.rightDerivedNatTrans _ _ F₁.rightDerivedFunctorPlusUnith
    F₂.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C)
    (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans τ) DerivedCategory.Plus.Qh)

/-- The defining equation of `rightDerivedFunctorPlusNatTrans`: it is compatible with the units
of right derivation and with `τ` applied degreewise. -/
theorem rightDerivedFunctorPlusNatTrans_app (P : HomotopyCategory.Plus C) :
    F₁.rightDerivedFunctorPlusUnith.app P ≫
        (rightDerivedFunctorPlusNatTrans τ).app (DerivedCategory.Plus.Qh.obj P) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans τ).app P) ≫
        F₂.rightDerivedFunctorPlusUnith.app P :=
  Functor.rightDerivedNatTrans_app _ _ _ _ _ _ P

/-- **The `ℤ`-indexed counterpart of `CategoryTheory.NatTrans.rightDerived`**: the morphism
`R ⁿF₁ ⟶ R ⁿF₂` of higher right derived functors in the indexing of
`CategoryTheory.Functor.rightDerivedPlus`. -/
noncomputable def rightDerivedPlusNatTrans (n : ℤ) :
    F₁.rightDerivedPlus n ⟶ F₂.rightDerivedPlus n :=
  Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
    (Functor.whiskerRight (rightDerivedFunctorPlusNatTrans τ)
      (DerivedCategory.Plus.homologyFunctor D n))

/-- **`rightDerivedPlusIsoRes` is natural in the functor variable, componentwise.** -/
theorem rightDerivedPlusIsoRes_hom_app_naturality (n : ℤ) (X : C) :
    (rightDerivedPlusNatTrans τ n).app X ≫ (rightDerivedPlusIsoRes F₂ n).hom.app X =
      (rightDerivedPlusIsoRes F₁ n).hom.app X ≫ (resNatTrans τ n).app X := by
  let P := resPlus.obj X
  let Hp := DerivedCategory.Plus.homologyFunctor D n
  let Hz := HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) n
  let w := (Functor.mapHomotopyCategoryPlusNatTrans τ).app P
  let ρ := rightDerivedFunctorPlusNatTrans τ
  let s := (singleIsoResPlusQh (C := C)).hom.app X
  have h₁ : Hp.map (ρ.app ((DerivedCategory.Plus.singleFunctor C 0).obj X)) ≫
        Hp.map (F₂.rightDerivedFunctorPlus.map s) =
      Hp.map (F₁.rightDerivedFunctorPlus.map s) ≫
        Hp.map (ρ.app (DerivedCategory.Plus.Qh.obj P)) := by
    rw [← Hp.map_comp, ← Hp.map_comp]
    exact congrArg Hp.map (ρ.naturality s).symm
  have h₂ : Hp.map (ρ.app (DerivedCategory.Plus.Qh.obj P)) ≫
        Hp.map ((resDerivedIso F₂).inv.app X) =
      Hp.map ((resDerivedIso F₁).inv.app X) ≫
        Hp.map (DerivedCategory.Plus.Qh.map w) := by
    rw [← Hp.map_comp, ← Hp.map_comp]
    exact congrArg Hp.map (comm_of_comm_inv ((resDerivedIso F₁).app X)
      ((resDerivedIso F₂).app X) _ _ (rightDerivedFunctorPlusNatTrans_app τ P))
  have h₃ : Hp.map (DerivedCategory.Plus.Qh.map w) ≫
        (plusHomologyIso (D := D) n).hom.app (F₂.mapHomotopyCategoryPlus.obj P) =
      (plusHomologyIso (D := D) n).hom.app (F₁.mapHomotopyCategoryPlus.obj P) ≫
        Hz.map ((HomotopyCategory.Plus.ι D).map w) :=
    (plusHomologyIso (D := D) n).hom.naturality w
  have h₄ : Hz.map ((HomotopyCategory.Plus.ι D).map w) ≫
        Hz.map (𝟙 ((HomotopyCategory.Plus.ι D).obj (F₂.mapHomotopyCategoryPlus.obj P))) =
      Hz.map (𝟙 ((HomotopyCategory.Plus.ι D).obj (F₁.mapHomotopyCategoryPlus.obj P))) ≫
        Hz.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
          ((HomotopyCategory.Plus.ι C).obj P)) := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id,
      Category.id_comp]
    exact rfl
  have h₅ : Hz.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
          ((HomotopyCategory.Plus.ι C).obj P)) ≫
        (F₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Hz).map
          (𝟙 ((HomotopyCategory.Plus.ι C).obj P)) =
      (F₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ Hz).map
          (𝟙 ((HomotopyCategory.Plus.ι C).obj P)) ≫
        Hz.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app (resH.obj X)) := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact paste_squares₅ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅

/-- **`rightDerivedPlusIsoRes` is natural in the functor variable.** -/
theorem rightDerivedPlusIsoRes_hom_naturality (n : ℤ) :
    rightDerivedPlusNatTrans τ n ≫ (rightDerivedPlusIsoRes F₂ n).hom =
      (rightDerivedPlusIsoRes F₁ n).hom ≫ resNatTrans τ n :=
  NatTrans.ext (funext fun X ↦ rightDerivedPlusIsoRes_hom_app_naturality τ n X)

/-- **The comparison of the two indexings of the right derived functors is natural in the
functor variable.** For additive functors `F₁, F₂ : 𝒜 ⥤ ℬ` with `𝒜` having enough injectives
and `τ : F₁ ⟶ F₂`, Mathlib's `ℕ`-indexed `CategoryTheory.NatTrans.rightDerived τ n` corresponds,
under `Stacks.DerivedIndexing.rightDerivedIso`, to the morphism `rightDerivedPlusNatTrans τ n`
of `ℤ`-indexed right derived functors — hence to the degree-`n` homology of the morphism
`RF₁ ⟶ RF₂` of right derived functors on bounded below derived categories produced by the
universal property of right derivation. -/
theorem rightDerivedIso_hom_naturality (n : ℕ) :
    NatTrans.rightDerived τ n ≫ (rightDerivedIso F₂ n).hom =
      (rightDerivedIso F₁ n).hom ≫ rightDerivedPlusNatTrans τ (n : ℤ) := by
  exact paste_squares _ _ _ _ _ _ _ (rightDerivedIsoRes_hom_naturality τ n)
    (comm_of_comm_inv (rightDerivedPlusIsoRes F₁ (n : ℤ))
      (rightDerivedPlusIsoRes F₂ (n : ℤ)) (rightDerivedPlusNatTrans τ (n : ℤ))
      (resNatTrans τ (n : ℤ)) (rightDerivedPlusIsoRes_hom_naturality τ (n : ℤ)).symm)

end FunctorNaturality

/-! ### Transport of vanishing -/

/-- Vanishing of the `ℕ`-indexed right derived functor is vanishing of the `ℤ`-indexed one. -/
lemma isZero_rightDerived_obj_iff (n : ℕ) (X : C) :
    IsZero ((F.rightDerived n).obj X) ↔ IsZero ((F.rightDerivedPlus (n : ℤ)).obj X) :=
  ⟨fun h ↦ h.of_iso ((rightDerivedIso F n).app X).symm,
    fun h ↦ h.of_iso ((rightDerivedIso F n).app X)⟩

/-- Vanishing of the `ℤ`-indexed right derived functor in a degree that is a natural number is
vanishing of Mathlib's `ℕ`-indexed one. -/
lemma isZero_rightDerivedPlus_obj_iff {m : ℤ} {n : ℕ} (hmn : m = n) (X : C) :
    IsZero ((F.rightDerivedPlus m).obj X) ↔ IsZero ((F.rightDerived n).obj X) := by
  subst hmn
  exact (isZero_rightDerived_obj_iff F n X).symm

section Acyclic

-- Instance search would otherwise try to prove termwise injectivity of an unknown complex; the
-- cheap instance coming from `EnoughInjectives` is given precedence, as in
-- `StacksFrontier/AlgebraicGeometry/AffineCohomologyVanishing/AffineBase.lean` and
-- `StacksFrontier/Topology/Sheaves/Cohomology/Leray/BaseVanishingCollapse.lean`, two modules
-- that need this lemma's indexing comparison.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

omit [EnoughInjectives C] in
/-- **Right acyclicity read off Mathlib's `ℕ`-indexed right derived functors.** For a left exact
functor, an object is right acyclic exactly when all its higher right derived functors vanish
there: [Stacks, Tag 015C] part (2), read through `isZero_rightDerived_obj_iff`.

It lives here, with the comparison of the two indexings that its proof goes through, because the
two modules named above both need it, neither of which imports the other while both already
import this one. -/
lemma rightAcyclic_iff_forall_nat [EnoughInjectives C] [PreservesFiniteLimits F] (A : C) :
    F.rightAcyclic A ↔ ∀ n : ℕ, 0 < n → IsZero ((F.rightDerived n).obj A) := by
  rw [(F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus A).2 inferInstance]
  refine ⟨fun h n hn => ?_, fun h i hi => ?_⟩
  · exact (isZero_rightDerived_obj_iff F n A).2 (h n (by omega))
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hi)
    exact (isZero_rightDerived_obj_iff F n A).1 (h n (by omega))

end Acyclic



section DerivedDelta

export CategoryTheory.Functor (commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit isTriangulated_rightDerivedFunctorPlus)

attribute [local instance] commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit isTriangulated_rightDerivedFunctorPlus

/-- **The `δ`-functor structure on `A ↦ RF(A[0]) : 𝒜 ⥤ D⁺(ℬ)`** ([Stacks, Tag 0151] part (1)
applied to `singleDeltaFunctorStructure` and the exact functor `RF`). This is the input that
[Stacks, Tag 05TE] quantifies over. -/
noncomputable def derivedDeltaFunctorStructure :
    Functor.DeltaFunctorStructure C (DerivedCategory.Plus D)
      (DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus) :=
  (singleDeltaFunctorStructure (C := C)).comp F.rightDerivedFunctorPlus

end DerivedDelta

/-! ### The `ℕ`-indexed long exact sequence -/

section LongExactSequence

variable (h : Functor.DeltaFunctorStructure C (DerivedCategory.Plus D)
    (DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus))
  (δ : ∀ {S : ShortComplex C}, S.ShortExact → ∀ i : ℕ,
    (F.rightDerivedPlus i).obj S.X₃ ⟶ (F.rightDerivedPlus (i + 1)).obj S.X₁)
  (hδ : ∀ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ), δ hS i =
    (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ
      (Pretriangulated.Triangle.mk
        ((DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus).map S.f)
        ((DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus).map S.g)
        (h.δ hS)) i (i + 1) rfl)

/-- **The `ℤ`-indexed higher right derived functors as a cohomological `δ`-functor.** This is
part (1) of [Stacks, Tag 05TE] as proved in
`CategoryTheory.Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal`, packaged in the
`CategoryTheory.DeltaFunctor` structure of [Stacks, Tag 010Q]. -/
noncomputable def rightDerivedPlusDeltaFunctor : CategoryTheory.DeltaFunctor C D :=
  let H := (Functor.rightDerivedPlus_isDeltaFunctor_and_isUniversal F h δ hδ).1
  { functor := fun n ↦ F.rightDerivedPlus n
    additive := H.1
    δ := δ
    map_g_δ := fun hS n ↦ (H.2.2.2.1 hS n).choose
    δ_map_f := fun hS n ↦ (H.2.2.2.2.1 hS n).choose
    mono_map_f := H.2.1
    exact_map := fun hS n ↦ (H.2.2.1 hS n).choose_spec
    exact_δ₁ := fun hS n ↦ (H.2.2.2.1 hS n).choose_spec
    exact_δ₂ := fun hS n ↦ (H.2.2.2.2.1 hS n).choose_spec
    δ_naturality := fun hS hT φ n ↦ H.2.2.2.2.2 hS hT φ n }

@[simp]
lemma rightDerivedPlusDeltaFunctor_functor (n : ℕ) :
    (rightDerivedPlusDeltaFunctor F h δ hδ).functor n = F.rightDerivedPlus (n : ℤ) := rfl

/-- **Mathlib's `ℕ`-indexed higher right derived functors form a cohomological `δ`-functor**
([Stacks, Tag 010Q]): the long sequence
`0 ⟶ R ⁰F(A) ⟶ R ⁰F(B) ⟶ R ⁰F(C) ⟶ R ¹F(A) ⟶ ⋯` attached to a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` is exact, and its connecting morphisms are natural in the sequence. -/
noncomputable def rightDerivedDeltaFunctor : CategoryTheory.DeltaFunctor C D :=
  deltaFunctorOfNatIso (rightDerivedPlusDeltaFunctor F h δ hδ) (fun n ↦ F.rightDerived n)
    (fun n ↦ (rightDerivedIso F n).symm)

@[simp]
lemma rightDerivedDeltaFunctor_functor (n : ℕ) :
    (rightDerivedDeltaFunctor F h δ hδ).functor n = F.rightDerived n := rfl

/-- The canonical connecting morphism `R ⁱF(C) ⟶ R ⁱ⁺¹F(A)` of a short exact sequence: the one
the long exact homology sequence of `H ⁰` attaches to the `RF`-image of the distinguished
triangle of `derivedDeltaFunctorStructure`. -/
noncomputable def canonicalδ {S : ShortComplex C} (hS : S.ShortExact) (i : ℕ) :
    (F.rightDerivedPlus i).obj S.X₃ ⟶ (F.rightDerivedPlus (i + 1)).obj S.X₁ :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ
    (Pretriangulated.Triangle.mk
      ((DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus).map S.f)
      ((DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus).map S.g)
      ((derivedDeltaFunctorStructure F).δ hS)) i (i + 1) rfl

/-- **Mathlib's `ℕ`-indexed higher right derived functors form a cohomological `δ`-functor**
([Stacks, Tag 010Q]), with no hypothesis beyond additivity of `F` and enough injectives in its
source: the long sequence `0 ⟶ R ⁰F(A) ⟶ R ⁰F(B) ⟶ R ⁰F(C) ⟶ R ¹F(A) ⟶ ⋯` attached to a short
exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜` is exact, and its connecting morphisms are natural
in the sequence. -/
noncomputable def rightDerivedDeltaFunctorOfEnoughInjectives : CategoryTheory.DeltaFunctor C D :=
  rightDerivedDeltaFunctor F (derivedDeltaFunctorStructure F) (canonicalδ F) (fun _ _ ↦ rfl)

@[simp]
lemma rightDerivedDeltaFunctorOfEnoughInjectives_functor (n : ℕ) :
    (rightDerivedDeltaFunctorOfEnoughInjectives F).functor n = F.rightDerived n := rfl

end LongExactSequence

end Stacks.DerivedIndexing
