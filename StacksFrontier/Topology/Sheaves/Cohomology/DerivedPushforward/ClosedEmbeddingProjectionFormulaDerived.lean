module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaMate
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.TotalTensorComplexAlongAComposite
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAdjunctionTranspose
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula for a closed embedding, in the derived category

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose underlying continuous map is
a homeomorphism onto a closed subset.  This file proves [Stacks, Tag 0B55]: the
projection-formula morphism of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism for *arbitrary* `E ∈ D(𝒪_X)` and `K ∈ D(𝒪_Y)`.  There is no boundedness,
flatness, finiteness, quasi-coherence or support hypothesis on either complex, and no hypothesis
on `f` beyond the closed embedding.

## Main results

* `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding`:
  **[Stacks, Tag 0B55]** for an arbitrary morphism of ringed spaces which is a homeomorphism onto
  a closed subset.
* `projectionFormulaMap_eq_derivedModelIso`, in the namespace
  `Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes`:
  the identity that carries the whole content — on a complex representative `A^•` of `E` and a
  K-flat representative `B^•` of `K`, the morphism of [Stacks, Tag 0B53] *is* `Q` of the
  complex-level isomorphism `complexProjectionFormulaIso`, conjugated by the comparisons that
  compute the two derived functors and the derived tensor product on those representatives.

`Stacks.Cohomology.SupportedComplexes.isIso_projectionFormulaMap_closedSubsetInclusion_of_isClosed`
proves the same conclusion for the canonical inclusion of a closed subset carrying the
*restricted* structure sheaf, by a different argument (supports and stalks).  That statement is
the special case of this one in which the comorphism of `f` is a restriction; its interface is
unchanged by this file.

## The argument

The source's proof is a reduction to the level of complexes, and that reduction is what is
carried out here.  Three steps, of which only the second is not already in the library.

*Step 1: reduce to representatives.*  Invertibility of the projection-formula morphism depends on
each of its two arguments only through its isomorphism class, by
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_congr_left` and
`isIso_projectionFormulaMap_congr_right`, both of which are unconditional.  So it suffices to
treat `E = Q A^•` for an arbitrary complex `A^•` and `K = Q B^•` for a K-flat `B^•`, which exists
by [Stacks, Tag 06YF].  This is the **K-flat reduction** that
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaStalks` records as the missing input: at a
general pair `(E, K)` the counit of `f^* ⊣ f_*` is not invertible, so no formal argument is
available; on representatives every functor in sight becomes computable.

*Step 2: the morphism of [Stacks, Tag 0B53] on representatives.*  `projectionFormulaMap` is by
definition an adjoint transpose, so to identify it with a composite of comparisons it suffices to
verify the transposed equation, which is
`Stacks.AlgebraicGeometry.ProjectionFormula.eq_adjunctionTensorMap_of_map_comp_counit`.  The
transposed equation is pure arrow algebra once ten identities are available, and that algebra is
`map_comp_counit_of_fac` below, stated for an abstract adjunction and two abstract bifunctors.
The ten identities are, in order of use: the two instances of [Stacks, Tag 0FP1] at `A^•` and at
`Tot(A^• ⊗_{𝒪_X} f^*B^•)`
(`derivedCounit_pushforwardComparisonQ`, in the namespace
`Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces`);
[Stacks, Tag 0FP0] at the pair `(f_*A^•, B^•)`
(`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_toTensor_comm`), which carries
no K-flatness and is therefore available at `f_*A^•`, a complex that is never K-flat for a closed
embedding; the naturality of the comparison `Lf^*(Q-) ⟶ Q(f^*-)`; the naturality of the canonical
map from the derived tensor product to the ordinary total tensor complex and its agreement with
the K-flat comparison, which are the `toTensor_naturality` and `toTensor_eq_comparisonRight`
fields of [Stacks, Tag 06YU]; and the complex-level mate identity
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso_mate`.

*Step 3: the composite is invertible.*  Every factor of the composite produced by step 2 is an
isomorphism: the two K-flat comparisons of [Stacks, Tag 06YU] because `B^•` and `f^*B^•` are
K-flat — the latter by [Stacks, Tag 06YC] — the comparison `f_* ⟶ Rf_*` because `f_*` is exact
along a closed embedding ([Stacks, Tag 08KS], through
`Stacks.Cohomology.ClosedEmbeddingPushforward.isIso_derivedPushforwardUnit_app`), the comparison
`Lf^*(QB^•) ⟶ Q(f^*B^•)` because `B^•` is K-flat, and `complexProjectionFormulaIso` itself.

## Implementation notes

*Why the arrow algebra is a separate declaration in bare categories.*  The categories of modules
on a ringed space carry two spellings of their sheaf of rings and the pullback and pushforward
functors carry two spellings each, so a goal at the derived categories can contain two
definitionally equal but syntactically distinct instance paths for the very same functor — at
which point a rewrite cannot cross between them, because `rw` works only up to `instances`
transparency.  The composite that step 2 manipulates mixes the spellings coming from the
complex-level mate identity with those coming from [Stacks, Tag 0FP0].  `map_comp_counit_of_fac`
takes every morphism as an explicit binder, so the geometric instance is a single application
whose definitional equality check runs at default transparency and sees through the difference,
and all the rewriting happens in bare categories where there is only one spelling of anything.

*Why the two summand identities are separate declarations.*  The hypotheses `hϑ` and `hμ` of
`complexProjectionFormulaIso_mate` describe a morphism out of a total complex by what it does on
each summand.  Discharging them for the two concrete morphisms — the comparison of
[Stacks, Tag 01CD] on total complexes and the counit in the left tensor factor — is
`Stacks.Cohomology.DerivedPullbackTensor.ι_pullbackTensorComplexIsoOfIsIso_inv` and Mathlib's
`HomologicalComplex.ι_mapBifunctorMap` respectively, but in each case the statement has to be
written at the spelling the mate identity uses, and the transfer is by an ascribed-type `have`
discharged by term application rather than by a rewrite, for the reason above.

*Why the library options force the split into many top-level declarations.*  The option
`maxSynthPendingDepth` is set to `3`, so typeclass inference does strictly more work here than
under a bare invocation of the compiler, and the identity of step 2 assembled inside one proof
exceeds the elaboration budget.  Each piece below is elaborated on its own and is far below it.

## References

* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0FP0](https://stacks.math.columbia.edu/tag/0FP0)
* [Stacks Project, Tag 0FP1](https://stacks.math.columbia.edu/tag/0FP1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback
  derivedAdjunction)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct derivedTensorProductFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex comparisonAppIso
  derivedPullbackNatTrans derivedToTensorNatTrans pullbackTensorComplexNatIso
  derivedPullbackTensorIso derivedPullbackTensorIso_toTensor_comm
  ι_pullbackTensorComplexIsoOfIsIso_inv isIso_derivedPullbackNatTrans_app)
open Stacks.SheafOfModules.KFlatPullback (kFlat_modulePullback_unconditional)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex complexAdjunction)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ
  derivedCounit_pushforwardComparisonQ)
open Stacks.Cohomology.ClosedEmbeddingPushforward (isIso_derivedPushforwardUnit_app)
open Stacks.Cohomology.DerivedProjectionFormula (uncurry_map_id_left uncurry_map_id_right)
open scoped CategoryTheory.Prod

universe u

/-! ### The transposed identity, in the abstract

Everything the geometric computation does with arrows is here, in bare categories.  See the
module docstring for why. -/

section Abstract

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}

/-- **The left-hand side of the transposed projection formula, factored.**  For an adjunction
`L ⊣ R`, bifunctors `A` on `C` and `B` on `D` and a morphism of bifunctors
`α : A ⋙ L ⟶ (L × L) ⋙ B`, the comparison of [Stacks, Tag 079U] followed by the counit in the
left tensor factor, precomposed with `L` of the source comparison, is the four-fold composite on
the right.

The hypotheses are, in the geometric instance: `hcY` that the K-flat comparison of
[Stacks, Tag 06YU] inverts the canonical map to the ordinary total tensor complex, `hA` an
instance of [Stacks, Tag 0FP1], `hB` that a K-flat complex computes the derived pullback, `hv`
and `hm` the two properties of the canonical map to the ordinary total tensor complex, and
`hFP0` [Stacks, Tag 0FP0].

Every endpoint is an explicit binder.  That is what makes this usable at the derived categories of
modules on a ringed space, where the same functor has two spellings and a rewrite cannot cross
between them. -/
private lemma lhs_fac (adj : L ⊣ R)
    (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
    {G : D} {H Pc TotY : C} {QfA QfB TotX TotX' TotYf : D}
    (pA : Pc ⟶ R.obj G) (cY : TotY ⟶ A.obj (Pc, H)) (cY' : A.obj (Pc, H) ⟶ TotY)
    (lA : L.obj Pc ⟶ QfA) (lB : L.obj H ⟶ QfB) (eA : QfA ⟶ G) (dB : QfB ⟶ L.obj H)
    (tX : B.obj (QfA, QfB) ⟶ TotX) (tX' : B.obj (G, QfB) ⟶ TotX')
    (m : TotX ⟶ TotX') (v : TotX' ⟶ B.obj (G, L.obj H))
    (lT : L.obj TotY ⟶ TotYf) (th : TotYf ⟶ TotX)
    (hcY : cY ≫ cY' = 𝟙 TotY)
    (hA : L.map pA ≫ adj.counit.app G = lA ≫ eA)
    (hB : lB ≫ dB = 𝟙 (L.obj H))
    (hv : tX' ≫ v = B.map (𝟙 G ×ₘ dB))
    (hm : B.map (eA ×ₘ 𝟙 QfB) ≫ tX' = tX ≫ m)
    (hFP0 : α.app (Pc, H) ≫ B.map (lA ×ₘ lB) ≫ tX = L.map cY' ≫ lT ≫ th) :
    L.map (cY ≫ A.map (pA ×ₘ 𝟙 H)) ≫ α.app (R.obj G, H) ≫
        B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) = lT ≫ th ≫ m ≫ v := by
  have hnat : L.map (A.map (pA ×ₘ 𝟙 H)) ≫ α.app (R.obj G, H) =
      α.app (Pc, H) ≫ B.map (L.map pA ×ₘ L.map (𝟙 H)) := α.naturality (pA ×ₘ 𝟙 H)
  have hpair : (L.map pA ≫ adj.counit.app G) ×ₘ (𝟙 (L.obj H) ≫ 𝟙 (L.obj H)) =
      (lA ≫ eA) ×ₘ (lB ≫ dB) := by
    rw [hA, Category.id_comp, hB]
  have hcomb : B.map (L.map pA ×ₘ 𝟙 (L.obj H)) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) =
      B.map (lA ×ₘ lB) ≫ B.map (eA ×ₘ dB) :=
    ((B.map_comp _ _).symm.trans (congrArg B.map hpair)).trans (B.map_comp _ _)
  have hsplit0 : (eA ≫ 𝟙 G) ×ₘ (𝟙 QfB ≫ dB) = eA ×ₘ dB := by
    rw [Category.comp_id, Category.id_comp]
  have hsplit : B.map (eA ×ₘ dB) = B.map (eA ×ₘ 𝟙 QfB) ≫ B.map (𝟙 G ×ₘ dB) :=
    (congrArg B.map hsplit0).symm.trans (B.map_comp (eA ×ₘ 𝟙 QfB) (𝟙 G ×ₘ dB))
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, CategoryTheory.Functor.map_id, hcomb, hsplit, ← hv, reassoc_of% hm,
    reassoc_of% hFP0, ← Category.assoc (L.map cY), ← CategoryTheory.Functor.map_comp, hcY,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The right-hand side of the transposed projection formula, factored.**  `L` of the composite
of the complex-level projection formula with the comparison `f_* ⟶ Rf_*` and `R` of the target
comparison, followed by the counit of `L ⊣ R`, is the same four-fold composite.

The hypotheses are, in the geometric instance: `hmate` the complex-level mate identity, `hlam`
the naturality of the comparison `Lf^*(Q-) ⟶ Q(f^*-)` and `hN` the second instance of
[Stacks, Tag 0FP1].  No bifunctor occurs, which is what keeps this instance light. -/
private lemma rhs_fac (adj : L ⊣ R) {TotY Pn : C} {TotX TotX' TotYf QfN N : D}
    (m : TotX ⟶ TotX') (v : TotX' ⟶ N)
    (lT : L.obj TotY ⟶ TotYf) (th : TotYf ⟶ TotX) (qc : TotY ⟶ Pn) (pN : Pn ⟶ R.obj TotX')
    (lN : L.obj Pn ⟶ QfN) (eN : QfN ⟶ TotX') (cqn : TotYf ⟶ QfN)
    (hmate : th ≫ m = cqn ≫ eN)
    (hlam : L.map qc ≫ lN = lT ≫ cqn)
    (hN : L.map pN ≫ adj.counit.app TotX' = lN ≫ eN) :
    L.map (qc ≫ pN ≫ R.map v) ≫ adj.counit.app N = lT ≫ th ≫ m ≫ v := by
  have h1 : L.map pN ≫ L.map (R.map v) ≫ adj.counit.app N = lN ≫ eN ≫ v := by
    rw [map_comp_map_map_comp_counit adj pN v, hN, Category.assoc]
  have h2 : L.map qc ≫ lN ≫ eN ≫ v = lT ≫ th ≫ m ≫ v := by
    rw [← Category.assoc (L.map qc), hlam, Category.assoc, ← Category.assoc cqn, ← hmate,
      Category.assoc]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc, h1, h2]

/-- **The transposed form of the projection formula, as arrow algebra.**  Given the two
factorizations `lhs_fac` and `rhs_fac` through a common composite, and given that `σ` inverts the
source comparison, the composite `σ ≫ qc ≫ pN ≫ R v` satisfies the equation that
`Stacks.AlgebraicGeometry.ProjectionFormula.eq_adjunctionTensorMap_of_map_comp_counit` asks for,
hence *is* the abstract adjunction-tensor morphism at `(G, H)`. -/
private lemma map_comp_counit_of_fac (adj : L ⊣ R)
    (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)
    {G : D} {H Pc TotY Pn : C} {TotX TotX' TotYf : D}
    (pA : Pc ⟶ R.obj G) (σ : A.obj (R.obj G, H) ⟶ TotY) (cY : TotY ⟶ A.obj (Pc, H))
    (m : TotX ⟶ TotX') (v : TotX' ⟶ B.obj (G, L.obj H))
    (lT : L.obj TotY ⟶ TotYf) (th : TotYf ⟶ TotX) (qc : TotY ⟶ Pn) (pN : Pn ⟶ R.obj TotX')
    (hσ : σ ≫ cY ≫ A.map (pA ×ₘ 𝟙 H) = 𝟙 (A.obj (R.obj G, H)))
    (hlhs : L.map (cY ≫ A.map (pA ×ₘ 𝟙 H)) ≫ α.app (R.obj G, H) ≫
      B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) = lT ≫ th ≫ m ≫ v)
    (hrhs : L.map (qc ≫ pN ≫ R.map v) ≫ adj.counit.app (B.obj (G, L.obj H)) =
      lT ≫ th ≫ m ≫ v) :
    L.map (σ ≫ qc ≫ pN ≫ R.map v) ≫ adj.counit.app (B.obj (G, L.obj H)) =
      α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) := by
  calc L.map (σ ≫ qc ≫ pN ≫ R.map v) ≫ adj.counit.app (B.obj (G, L.obj H))
      = L.map σ ≫ L.map (qc ≫ pN ≫ R.map v) ≫ adj.counit.app (B.obj (G, L.obj H)) := by
        rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = L.map σ ≫ L.map (cY ≫ A.map (pA ×ₘ 𝟙 H)) ≫ α.app (R.obj G, H) ≫
          B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) := by rw [hrhs, hlhs]
    _ = α.app (R.obj G, H) ≫ B.map (adj.counit.app G ×ₘ 𝟙 (L.obj H)) := by
        rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hσ,
          CategoryTheory.Functor.map_id, Category.id_comp]

/-- A functor preserves an equation between two-fold composites. -/
private lemma map_comp_eq_map_comp (F : C ⥤ D) {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Z}
    {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

end Abstract

namespace Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

attribute [local instance] HasDerivedCategory.standard

-- `structureSheafRing` is `@[instance_reducible]`, so it unfolds at `implicit`
-- transparency already, but its reduct stops at an explicit-constructor projection while
-- `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`; these two Mathlib
-- definitions are the gap between them.
attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The two summand identities the mate identity asks for -/

/-- **The comparison of [Stacks, Tag 01CD] on total complexes, on a summand.**  This is the
hypothesis `hϑ` of `complexProjectionFormulaIso_mate` for the inverse of
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso`, which is the comparison
`Tot(f^*K^• ⊗_{𝒪_X} f^*L^•) ⟶ f^*Tot(K^• ⊗_{𝒪_Y} L^•)`.

It is `Stacks.Cohomology.DerivedPullbackTensor.ι_pullbackTensorComplexIsoOfIsIso_inv`, restated
with a trailing morphism bound and at the spelling of the summand inclusions that the mate
identity uses. -/
private lemma ιTotal_comp_pullbackTensorComplexNatIso_inv_app_comp
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (p q n : ℤ) (hpq : p + q = n)
    {Z : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X}
    (g : (StacksDraft.KFlat.modulePullback f).obj
        ((((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B).X n) ⟶ Z) :
    HomologicalComplex₂.ιTotal
          ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
            ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
            ((pullbackComplex f).obj B))
          (.up ℤ) p q n hpq ≫
        ((pullbackTensorComplexNatIso f).inv.app ((pushforwardComplex f).obj A, B)).f n ≫ g =
      (comparisonAppIso f ((StacksDraft.KFlat.modulePushforward f).obj (A.X p)) (B.X q)).inv ≫
        (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pushforwardComplex f).obj A)).obj B)
            (.up ℤ) p q n hpq) ≫ g := by
  have h : HomologicalComplex₂.ιTotal
        ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
          ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
          ((pullbackComplex f).obj B))
        (.up ℤ) p q n hpq ≫
      ((pullbackTensorComplexNatIso f).inv.app ((pushforwardComplex f).obj A, B)).f n =
    (comparisonAppIso f ((StacksDraft.KFlat.modulePushforward f).obj (A.X p)) (B.X q)).inv ≫
      (StacksDraft.KFlat.modulePullback f).map
        (HomologicalComplex₂.ιTotal
          ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
            ((pushforwardComplex f).obj A)).obj B)
          (.up ℤ) p q n hpq) :=
    ι_pullbackTensorComplexIsoOfIsIso_inv f ((pushforwardComplex f).obj A) B p q n hpq
  exact ((Category.assoc _ _ g).symm.trans (congrArg (· ≫ g) h)).trans (Category.assoc _ _ _)

/-- **The counit of `f^* ⊣ f_*` in the left tensor factor, on a summand.**  This is the hypothesis
`hμ` of `complexProjectionFormulaIso_mate` for

`Tot(f^*f_*A^• ⊗_{𝒪_X} f^*B^•) ⟶ Tot(A^• ⊗_{𝒪_X} f^*B^•)`,

the total complex of the counit in the left variable and the identity in the right.  It is
Mathlib's `HomologicalComplex.ι_mapBifunctorMap` with the identity in the second variable
removed. -/
private lemma ιTotal_comp_mapBifunctorMap_counit
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex₂.ιTotal
          ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
            ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
            ((pullbackComplex f).obj B))
          (.up ℤ) p q n hpq ≫
        (HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app A)
          (𝟙 ((pullbackComplex f).obj B)) (sheafTensor X.sheaf) (ComplexShape.up ℤ)).f n =
      ((sheafTensor X.sheaf).map
          ((modulePullbackPushforwardAdjunction f).counit.app (A.X p))).app
          ((StacksDraft.KFlat.modulePullback f).obj (B.X q)) ≫
        HomologicalComplex₂.ιTotal
          ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
            ((pullbackComplex f).obj B))
          (.up ℤ) p q n hpq := by
  have h := HomologicalComplex.ι_mapBifunctorMap ((complexAdjunction f).counit.app A)
    (𝟙 ((pullbackComplex f).obj B)) (sheafTensor X.sheaf) (ComplexShape.up ℤ) p q n hpq
  rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-! ### The complex-level mate identity, with the comparison inverted -/

/-- **The complex-level mate identity, read forwards.**  The comparison of [Stacks, Tag 01CD] on
total complexes `f^*Tot(f_*A^• ⊗_{𝒪_Y} B^•) ⟶ Tot(f^*f_*A^• ⊗_{𝒪_X} f^*B^•)`, followed by the
counit in the left tensor factor, is the pullback of `Φ` followed by the counit of `f^* ⊣ f_*`
on complexes, for any isomorphism of total complexes `Φ` whose summand formula `hΦ` is the
termwise projection-formula morphism.

This is `projectionFormulaTotalIso_mate` with its two summand hypotheses discharged and the
comparison moved to the other side; the comparison is invertible, being a component of a natural
isomorphism.  No hypothesis on `f` is used. -/
private lemma pullbackTensorComplexNatIso_hom_app_comp_mapBifunctorMap
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (Φ : ((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B ≅
        (pushforwardComplex f).obj
          (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)))
    (hΦ : ∀ (p q n : ℤ) (hpq : p + q = n),
      HomologicalComplex₂.ιTotal
            ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pushforwardComplex f).obj A)).obj B)
            (.up ℤ) p q n hpq ≫ Φ.hom.f n =
        Stacks.ProjectionFormula.projectionFormulaMap' f (A.X p) (B.X q) ≫
          (StacksDraft.KFlat.modulePushforward f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
                ((pullbackComplex f).obj B))
              (.up ℤ) p q n hpq)) :
    (pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B) ≫
        HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app A)
          (𝟙 ((pullbackComplex f).obj B)) (sheafTensor X.sheaf) (ComplexShape.up ℤ) =
      (pullbackComplex f).map Φ.hom ≫
        (complexAdjunction f).counit.app (((tensorComplex X.sheaf).obj A).obj
          ((pullbackComplex f).obj B)) := by
  have hmate := projectionFormulaTotalIso_mate f A B Φ hΦ
    ((pullbackTensorComplexNatIso f).inv.app ((pushforwardComplex f).obj A, B))
    (fun p q n hpq _ g =>
      ιTotal_comp_pullbackTensorComplexNatIso_inv_app_comp f A B p q n hpq g)
    (HomologicalComplex.mapBifunctorMap ((complexAdjunction f).counit.app A)
      (𝟙 ((pullbackComplex f).obj B)) (sheafTensor X.sheaf) (ComplexShape.up ℤ))
    (fun p q n hpq => ιTotal_comp_mapBifunctorMap_counit f A B p q n hpq)
  exact (congrArg ((pullbackTensorComplexNatIso f).hom.app
      ((pushforwardComplex f).obj A, B) ≫ ·) hmate.symm).trans
    (Iso.hom_inv_id_app_assoc (pullbackTensorComplexNatIso f)
      ((pushforwardComplex f).obj A, B) _)

/-! ### The comparison `f_* ⟶ Rf_*` is invertible along a closed embedding -/

/-- **`Q(f_*C^•) ⟶ Rf_*(QC^•)` is invertible** when `f` is a homeomorphism onto a closed subset.
The comparison is the unit of the derived pushforward with the two `Q` versus `Qh ∘ quotient`
bridges inserted at either end; the bridges are isomorphisms unconditionally and the unit is
invertible by `Stacks.Cohomology.ClosedEmbeddingPushforward.isIso_derivedPushforwardUnit_app`,
which is [Stacks, Tag 08KS]. -/
lemma isIso_pushforwardComparisonQ
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (Cx : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    IsIso (pushforwardComparisonQ f Cx) := by
  have h1 : IsIso (((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)).app
        ((pushforwardComplex f).obj Cx)).inv) := inferInstance
  have h2 := isIso_derivedPushforwardUnit_app f hf
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj Cx)
  -- `derivedPushforward` is stated at `SheafOfModules.{u} (structureSheafRing X)` while the
  -- bridge is stated at `KFlatDerivedPullback.Modules X`, which is
  -- `SheafOfModules (Tensor.ringSheaf X.sheaf)`; the two carry different `HasDerivedCategory`
  -- instances, definitionally equal only once the plain `def` `Tensor.ringSheaf` is unfolded,
  -- which instance search does not do.  `Functor.map_isIso` is therefore given as the term it
  -- is defined to be, whose elaboration identifies the two spellings.
  have h3 : IsIso ((derivedPushforward f).map
      (((DerivedCategory.quotientCompQhIso
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).app Cx).hom)) :=
    ((derivedPushforward f).mapIso ((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).app Cx)).isIso_hom
  dsimp only [pushforwardComparisonQ]
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3)

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### The two spellings of the ordinary total tensor complex

The canonical map from the derived tensor product to the ordinary total tensor complex has two
presentations in the library: the `toTensor` field of [Stacks, Tag 06YU], whose target is written
with `Stacks.SheafOfModules.Tensor.tensorComplex`, and
`Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans`, the same map read as a
morphism of functors on pairs, whose target is written with
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair`.  They are the same morphism by
`rfl`, but the two spellings of the target have to be reconciled, and that reconciliation is
expensive: carried out twice inside one declaration it exceeds the elaboration budget.  It is
therefore done once, here, and everything below is written at the `toTensor` presentation. -/

/-- The canonical map to the ordinary total tensor complex, in its two presentations. -/
private theorem derivedToTensorNatTrans_app_eq (Z : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (derivedToTensorNatTrans Z).app (K, L) =
      (canonicalDerivedTensorProduct Z.sheaf).toTensor K L := rfl


/-! ### The two endpoint comparisons, on representatives -/

variable (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
  (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
  (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
  (hB : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y B)

include hf hB

/-- **The source of the morphism of [Stacks, Tag 0B53], on representatives:**

`Q(Tot(f_*A^• ⊗_{𝒪_Y} B^•)) ≅ Rf_*(QA^•) ⊗^𝐋_{𝒪_Y} QB^•` for `B^•` K-flat.

The K-flat comparison of [Stacks, Tag 06YU] in the right tensor factor, then the comparison
`Q(f_*A^•) ⟶ Rf_*(QA^•)` in the left. -/
def sourceModelIso :
    DerivedCategory.Q.obj (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B) ≅
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) :=
  ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
      ((pushforwardComplex f).obj A) B hB).symm ≪≫
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).mapIso
      (Iso.prod (@asIso _ _ _ _ _ (isIso_pushforwardComparisonQ f hf A))
        (Iso.refl (DerivedCategory.Q.obj B)))

/-- **The target of the morphism of [Stacks, Tag 0B53], on representatives:**

`Q(Tot(A^• ⊗_{𝒪_X} f^*B^•)) ≅ QA^• ⊗^𝐋_{𝒪_X} Lf^*(QB^•)` for `B^•` K-flat.

The K-flat comparison of [Stacks, Tag 06YU] in the right tensor factor — `f^*B^•` is K-flat by
[Stacks, Tag 06YC] — then the comparison `Lf^*(QB^•) ⟶ Q(f^*B^•)` inverted, which is invertible
because `B^•` is K-flat. -/
def targetModelIso :
    DerivedCategory.Q.obj (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)) ≅
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
        (DerivedCategory.Q.obj A, (derivedPullback f).obj (DerivedCategory.Q.obj B)) :=
  ((canonicalDerivedTensorProduct X.sheaf).comparisonRight A ((pullbackComplex f).obj B)
      (kFlat_modulePullback_unconditional f B hB)).symm ≪≫
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).mapIso
      (Iso.prod (Iso.refl (DerivedCategory.Q.obj A))
        (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).symm)

/-- **The morphism of [Stacks, Tag 0B53] on representatives, as an isomorphism.**

`Rf_*(QA^•) ⊗^𝐋_{𝒪_Y} QB^• ≅ Rf_*(QA^• ⊗^𝐋_{𝒪_X} Lf^*(QB^•))` for `B^•` K-flat: the two endpoint
comparisons with `Q` of the complex-level projection formula
`complexProjectionFormulaIso` and the comparison `Q(f_*-) ⟶ Rf_*(Q-)` between them.

That this is the morphism of [Stacks, Tag 0B53] is
`projectionFormulaMap_eq_derivedModelIso`; it is stated as an isomorphism because that is what
makes [Stacks, Tag 0B55] follow. -/
def derivedModelIso :
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≅
      (derivedPushforward f).obj
        ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
          (DerivedCategory.Q.obj A, (derivedPullback f).obj (DerivedCategory.Q.obj B))) :=
  (sourceModelIso f hf A B hB).symm ≪≫
    DerivedCategory.Q.mapIso (complexProjectionFormulaIso f hf A B) ≪≫
    (@asIso _ _ _ _ _ (isIso_pushforwardComparisonQ f hf
      (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)))) ≪≫
    (derivedPushforward f).mapIso (targetModelIso f A B hB)

/-! ### The ten identities the arrow algebra consumes

Each is a separate top-level declaration with every endpoint written out.  Assembled inside one
proof they exhaust the elaboration budget: the library sets `maxSynthPendingDepth = 3`, so
typeclass inference does strictly more work here than under a bare invocation of the compiler. -/

omit hf hB in
/-- **[Stacks, Tag 0FP0] at the pair `(f_*A^•, B^•)`, in the `toTensor` presentation.**  This is
the hypothesis `hFP0` of `map_comp_counit_of_fac`.  It is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_toTensor_comm` with its two
occurrences of the canonical map to the ordinary total tensor complex rewritten by
`derivedToTensorNatTrans_app_eq`, which is why that reconciliation happens here and nowhere
else.  Note that it carries no K-flatness, which is what makes it usable at `f_*A^•`: that
complex is annihilated by the kernel ideal of `f^♯` and hence never K-flat. -/
private theorem derivedPullbackTensorIso_toTensor_comm_toTensor :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj ((pushforwardComplex f).obj A), DerivedCategory.Q.obj B) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app ((pushforwardComplex f).obj A) ×ₘ
              (derivedPullbackNatTrans f).app B) ≫
          (canonicalDerivedTensorProduct X.sheaf).toTensor
            ((pullbackComplex f).obj ((pushforwardComplex f).obj A))
            ((pullbackComplex f).obj B) =
      (derivedPullback f).map
          ((canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A) B) ≫
        (derivedPullbackNatTrans f).app
            (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B) ≫
          DerivedCategory.Q.map
            ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B)) :=
  derivedPullbackTensorIso_toTensor_comm f ((pushforwardComplex f).obj A) B

/-- **The source comparison is inverted by its own inverse.**  This is the hypothesis `hσ` of
`map_comp_counit_of_fac`, with the two factors of `sourceModelIso` written out. -/
private theorem sourceModelIso_inv_comp_comparisonRight_inv_comp :
    (sourceModelIso f hf A B hB).inv ≫
        ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
            ((pushforwardComplex f).obj A) B hB).inv ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
            (pushforwardComparisonQ f A ×ₘ 𝟙 (DerivedCategory.Q.obj B)) =
      𝟙 ((Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B)) :=
  (sourceModelIso f hf A B hB).inv_hom_id

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] hf in
/-- **The K-flat comparison of [Stacks, Tag 06YU] inverts the canonical map to the ordinary total
tensor complex**, on the pair `(f_*A^•, B^•)`.  This is the hypothesis `hcY` of
`map_comp_counit_of_fac`; it is the `toTensor_eq_comparisonRight` field of [Stacks, Tag 06YU],
available because `B^•` is K-flat. -/
private theorem comparisonRight_inv_comp_toTensor :
    ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
          ((pushforwardComplex f).obj A) B hB).inv ≫
        (canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A) B =
      𝟙 (DerivedCategory.Q.obj
        (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B)) := by
  rw [(canonicalDerivedTensorProduct Y.sheaf).toTensor_eq_comparisonRight
    ((pushforwardComplex f).obj A) B hB, Iso.inv_hom_id]

omit hf in
/-- **The left-hand side of the transposed identity, factored.**  This is `lhs_fac` at the
derived categories of modules on `X` and `Y`, for any `v` with the property `hv`. -/
private theorem lhs_fac_geom
    (v : DerivedCategory.Q.obj (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)) ⟶
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
        (DerivedCategory.Q.obj A, (derivedPullback f).obj (DerivedCategory.Q.obj B)))
    (hv : (canonicalDerivedTensorProduct X.sheaf).toTensor A ((pullbackComplex f).obj B) ≫ v =
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
        (𝟙 (DerivedCategory.Q.obj A) ×ₘ
          (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).inv))
    (hcY : ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
          ((pushforwardComplex f).obj A) B hB).inv ≫
        (canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A) B =
      𝟙 (DerivedCategory.Q.obj
        (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B)))
    (hm : (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          (DerivedCategory.Q.map ((complexAdjunction f).counit.app A) ×ₘ
            𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj B))) ≫
        (canonicalDerivedTensorProduct X.sheaf).toTensor A ((pullbackComplex f).obj B) =
      (canonicalDerivedTensorProduct X.sheaf).toTensor
          ((pullbackComplex f).obj ((pushforwardComplex f).obj A)) ((pullbackComplex f).obj B) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
          (sheafTensor X.sheaf) (ComplexShape.up ℤ)))
    (hFP0 : (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj ((pushforwardComplex f).obj A), DerivedCategory.Q.obj B) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app ((pushforwardComplex f).obj A) ×ₘ
              (derivedPullbackNatTrans f).app B) ≫
          (canonicalDerivedTensorProduct X.sheaf).toTensor
            ((pullbackComplex f).obj ((pushforwardComplex f).obj A))
            ((pullbackComplex f).obj B) =
      (derivedPullback f).map
          ((canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A) B) ≫
        (derivedPullbackNatTrans f).app
            (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B) ≫
          DerivedCategory.Q.map
            ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B))) :
    (derivedPullback f).map
          (((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
              ((pushforwardComplex f).obj A) B hB).inv ≫
            (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
              (pushforwardComparisonQ f A ×ₘ 𝟙 (DerivedCategory.Q.obj B))) ≫
        (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app
            ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((derivedAdjunction f).counit.app (DerivedCategory.Q.obj A) ×ₘ
              𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj B))) =
      (derivedPullbackNatTrans f).app
            (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B) ≫
          DerivedCategory.Q.map
              ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B)) ≫
            DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
                ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
                (sheafTensor X.sheaf) (ComplexShape.up ℤ)) ≫
              v :=
  lhs_fac (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (pA := pushforwardComparisonQ f A)
    (cY := ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
      ((pushforwardComplex f).obj A) B hB).inv)
    (cY' := (canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A) B)
    (lA := (derivedPullbackNatTrans f).app ((pushforwardComplex f).obj A))
    (lB := (derivedPullbackNatTrans f).app B)
    (eA := DerivedCategory.Q.map ((complexAdjunction f).counit.app A))
    (dB := (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).inv)
    (tX := (canonicalDerivedTensorProduct X.sheaf).toTensor
      ((pullbackComplex f).obj ((pushforwardComplex f).obj A)) ((pullbackComplex f).obj B))
    (tX' := (canonicalDerivedTensorProduct X.sheaf).toTensor A ((pullbackComplex f).obj B))
    (m := DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
      (sheafTensor X.sheaf) (ComplexShape.up ℤ)))
    (v := v)
    (lT := (derivedPullbackNatTrans f).app
      (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B))
    (th := DerivedCategory.Q.map
      ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B)))
    hcY (derivedCounit_pushforwardComparisonQ f A)
    (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).hom_inv_id hv hm hFP0

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] hf hB in
/-- **The canonical map to the ordinary total tensor complex is natural in the left factor.**
This is the hypothesis `hm` of `map_comp_counit_of_fac`: the `toTensor_naturality` field of
[Stacks, Tag 06YU] at the counit of `f^* ⊣ f_*` on complexes and the identity. -/
private theorem map_counit_comp_toTensor :
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          (DerivedCategory.Q.map ((complexAdjunction f).counit.app A) ×ₘ
            𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj B))) ≫
        (canonicalDerivedTensorProduct X.sheaf).toTensor A ((pullbackComplex f).obj B) =
      (canonicalDerivedTensorProduct X.sheaf).toTensor
          ((pullbackComplex f).obj ((pushforwardComplex f).obj A)) ((pullbackComplex f).obj B) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
          (sheafTensor X.sheaf) (ComplexShape.up ℤ)) := by
  have h := (canonicalDerivedTensorProduct X.sheaf).toTensor_naturality
    ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [uncurry_map_id_right]
  exact h

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] hB in
/-- **The complex-level mate identity, read in the derived category.**  This is the hypothesis
`hmate` of `map_comp_counit_of_fac`: `Q` of
`pullbackTensorComplexNatIso_hom_app_comp_mapBifunctorMap`. -/
private theorem map_pullbackTensorComplexNatIso_hom_app_comp_map_mapBifunctorMap :
    DerivedCategory.Q.map
          ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B)) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
          (sheafTensor X.sheaf) (ComplexShape.up ℤ)) =
      DerivedCategory.Q.map
          ((pullbackComplex f).map (complexProjectionFormulaIso f hf A B).hom) ≫
        DerivedCategory.Q.map ((complexAdjunction f).counit.app
          (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B))) :=
  map_comp_eq_map_comp DerivedCategory.Q
    (pullbackTensorComplexNatIso_hom_app_comp_mapBifunctorMap f A B
      (complexProjectionFormulaIso f hf A B) (ι_complexProjectionFormulaIso_hom f hf A B))

/-! ### The transposed identity

Assembled in three steps, each its own declaration: the two sides of the transposed equation are
factored separately through the common composite
`Lf^*(Q-) ⟶ Q(f^*-)`, the comparison of [Stacks, Tag 01CD] on total complexes, the counit in the
left tensor factor and the target comparison, and then matched. -/

omit hf in
/-- **The transposed form of the identity of step 2.**  Applying `Lf^*` to the composite of
comparisons `σ`, `Q Φ`, `Q(f_*-) ⟶ Rf_*(Q-)` and `Rf_* v` and following with the counit of
`Lf^* ⊣ Rf_*` gives the comparison of [Stacks, Tag 079U] followed by the counit in the left
tensor factor — which is exactly the equation that characterizes the morphism of
[Stacks, Tag 0B53].  Here `Φ` is any isomorphism of total complexes, `σ` inverts the source
comparison (`hσ`), `v` is the target comparison (`hv`), `hmate` is the mate identity for `Φ`
and `hcY`, `hm`, `hFP0` are the identities `hcY`, `hm`, `hFP0` of `lhs_fac`. -/
private theorem map_derivedModel_comp_counit
    (Φ : ((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B ≅
        (pushforwardComplex f).obj
          (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)))
    (σ : (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B))
    (v : DerivedCategory.Q.obj (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)) ⟶
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
        (DerivedCategory.Q.obj A, (derivedPullback f).obj (DerivedCategory.Q.obj B)))
    (hσ : σ ≫ ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
            ((pushforwardComplex f).obj A) B hB).inv ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
            (pushforwardComparisonQ f A ×ₘ 𝟙 (DerivedCategory.Q.obj B)) =
      𝟙 ((Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B)))
    (hmate : DerivedCategory.Q.map
          ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B)) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
          (sheafTensor X.sheaf) (ComplexShape.up ℤ)) =
      DerivedCategory.Q.map ((pullbackComplex f).map Φ.hom) ≫
        DerivedCategory.Q.map ((complexAdjunction f).counit.app
          (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B))))
    (hv : (canonicalDerivedTensorProduct X.sheaf).toTensor A ((pullbackComplex f).obj B) ≫ v =
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
        (𝟙 (DerivedCategory.Q.obj A) ×ₘ
          (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).inv))
    (hcY : ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
          ((pushforwardComplex f).obj A) B hB).inv ≫
        (canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A) B =
      𝟙 (DerivedCategory.Q.obj
        (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B)))
    (hm : (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          (DerivedCategory.Q.map ((complexAdjunction f).counit.app A) ×ₘ
            𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj B))) ≫
        (canonicalDerivedTensorProduct X.sheaf).toTensor A ((pullbackComplex f).obj B) =
      (canonicalDerivedTensorProduct X.sheaf).toTensor
          ((pullbackComplex f).obj ((pushforwardComplex f).obj A)) ((pullbackComplex f).obj B) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
          (sheafTensor X.sheaf) (ComplexShape.up ℤ)))
    (hFP0 : (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj ((pushforwardComplex f).obj A), DerivedCategory.Q.obj B) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app ((pushforwardComplex f).obj A) ×ₘ
              (derivedPullbackNatTrans f).app B) ≫
          (canonicalDerivedTensorProduct X.sheaf).toTensor
            ((pullbackComplex f).obj ((pushforwardComplex f).obj A))
            ((pullbackComplex f).obj B) =
      (derivedPullback f).map
          ((canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A) B) ≫
        (derivedPullbackNatTrans f).app
            (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B) ≫
          DerivedCategory.Q.map
            ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B))) :
    (derivedPullback f).map (σ ≫ DerivedCategory.Q.map Φ.hom ≫
          pushforwardComparisonQ f
              (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)) ≫
            (derivedPushforward f).map v) ≫
        (derivedAdjunction f).counit.app
          ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
            (DerivedCategory.Q.obj A, (derivedPullback f).obj (DerivedCategory.Q.obj B))) =
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app
          ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((derivedAdjunction f).counit.app (DerivedCategory.Q.obj A) ×ₘ
            𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj B))) :=
  map_comp_counit_of_fac (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (pA := pushforwardComparisonQ f A)
    (σ := σ)
    (cY := ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
      ((pushforwardComplex f).obj A) B hB).inv)
    (m := DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
      (sheafTensor X.sheaf) (ComplexShape.up ℤ)))
    (v := v)
    (lT := (derivedPullbackNatTrans f).app
      (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B))
    (th := DerivedCategory.Q.map
      ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B)))
    (qc := DerivedCategory.Q.map Φ.hom)
    (pN := pushforwardComparisonQ f
      (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)))
    hσ
    (lhs_fac_geom f A B hB v hv hcY hm hFP0)
    (rhs_fac (derivedAdjunction f) _ _ _ _ _ _ _ _ _ hmate
      ((derivedPullbackNatTrans f).naturality Φ.hom)
      (derivedCounit_pushforwardComparisonQ f
        (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B))))

/-- **The morphism of [Stacks, Tag 0B53] on representatives is the complex-level projection
formula.**  For an arbitrary complex `A^•` of `𝒪_X`-modules and a K-flat complex `B^•` of
`𝒪_Y`-modules, the canonical morphism

`Rf_*(QA^•) ⊗^𝐋_{𝒪_Y} QB^• ⟶ Rf_*(QA^• ⊗^𝐋_{𝒪_X} Lf^*(QB^•))`

of [Stacks, Tag 0B53] is `Q` of `complexProjectionFormulaIso`, conjugated by the comparisons that
compute the two derived functors and the derived tensor product on these representatives.  In
particular it is an isomorphism.

This is the K-flat reduction the derived statement of [Stacks, Tag 0B55] needs.  The morphism of
[Stacks, Tag 0B53] is an adjoint transpose, so the identity is proved by verifying the transposed
equation, which is `map_derivedModel_comp_counit`. -/
theorem projectionFormulaMap_eq_derivedModelIso :
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f
        (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B) =
      (derivedModelIso f hf A B hB).hom := by
  rw [Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_eq]
  exact Stacks.AlgebraicGeometry.ProjectionFormula.eq_adjunctionTensorMap_of_map_comp_counit
    (derivedAdjunction f) _ _ _ _ _ _ (map_derivedModel_comp_counit f A B hB
      (complexProjectionFormulaIso f hf A B) (sourceModelIso f hf A B hB).inv
      (targetModelIso f A B hB).hom (sourceModelIso_inv_comp_comparisonRight_inv_comp f hf A B hB)
      (map_pullbackTensorComplexNatIso_hom_app_comp_map_mapBifunctorMap f hf A B)
      (by rw [(canonicalDerivedTensorProduct X.sheaf).toTensor_eq_comparisonRight A
          ((pullbackComplex f).obj B) (kFlat_modulePullback_unconditional f B hB)]
          exact Iso.hom_inv_id_assoc _ _) (comparisonRight_inv_comp_toTensor f A B hB)
      (map_counit_comp_toTensor f A B) (derivedPullbackTensorIso_toTensor_comm_toTensor f A B))

/-- **[Stacks, Tag 0B55] on representatives.**  The morphism of [Stacks, Tag 0B53] is invertible
at `(QA^•, QB^•)` for an arbitrary complex `A^•` and a K-flat complex `B^•`. -/
theorem isIso_projectionFormulaMap_Q :
    IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f
      (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)) := by
  rw [projectionFormulaMap_eq_derivedModelIso f hf A B hB]
  exact (derivedModelIso f hf A B hB).isIso_hom

end Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

/-! ### [Stacks, Tag 0B55] -/

namespace Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **[Stacks, Tag 0B55].**  Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose
underlying continuous map is a homeomorphism onto a closed subset.  Then the projection-formula
morphism of [Stacks, Tag 0B53]

`Rf_*E ⊗^𝐋_{𝒪_Y} K ⟶ Rf_*(E ⊗^𝐋_{𝒪_X} Lf^*K)`

is an isomorphism for every `E` in `D(𝒪_X)` and every `K` in `D(𝒪_Y)`.

The proof is the source's: represent `E` by any complex and `K` by a K-flat complex, which is
possible by [Stacks, Tag 06YF], and transport invertibility along the two representations, which
is legitimate by
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_congr_left` and
`isIso_projectionFormulaMap_congr_right`.  On representatives the morphism is `Q` of the
complex-level projection formula up to isomorphism, which is
`projectionFormulaMap_eq_derivedModelIso` in the namespace
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes`. -/
@[stacks 0B55 "for an arbitrary morphism of ringed spaces whose underlying map is a \
homeomorphism onto a closed subset; the derived statement, with no boundedness, flatness, \
finiteness, quasi-coherence or support hypothesis on either complex"]
theorem isIso_projectionFormulaMap_of_isClosedEmbedding
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso (projectionFormulaMap f E K) := by
  obtain ⟨B, g, hB, -, hg, -⟩ := Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y
    (DerivedCategory.Q.objPreimage K)
  have hgiso : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hg
  have eK : DerivedCategory.Q.obj B ≅ K :=
    asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  rw [← isIso_projectionFormulaMap_congr_left f (DerivedCategory.Q.objObjPreimageIso E) K,
    ← isIso_projectionFormulaMap_congr_right f _ eK]
  exact Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.isIso_projectionFormulaMap_Q
    f hf (DerivedCategory.Q.objPreimage E) B hB

end Stacks.Cohomology.DerivedProjectionFormula

/-! ### The projection formula on representatives, for any complex-level projection formula

The statements above are proved for a closed embedding, where the complex-level projection
formula `complexProjectionFormulaIso` and the invertibility of `Q(f_*C^•) ⟶ Rf_*(QC^•)` are
available. The arrow algebra that turns them into the invertibility of the morphism of
[Stacks, Tag 0B53] on representatives uses nothing about `f` beyond those inputs. The
declarations below carry it out for an arbitrary morphism of ringed spaces, with the three inputs
as hypotheses: an isomorphism of total complexes `Φ` whose summand formula `hΦ` is the termwise
projection-formula morphism, and invertibility of the comparison `Q(f_*C^•) ⟶ Rf_*(QC^•)` at the
two complexes involved. For an affine morphism of schemes and quasi-coherent terms all three
inputs hold, which is how [Stacks, Tag 08I9] is proved in
`StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.AffineProjectionFormulaDerived`. -/

namespace Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The comparison `f_* ⟶ Rf_*` is invertible along a closed embedding -/


variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
  (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
  (Φ : ((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B ≅
      (pushforwardComplex f).obj
        (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)))
  (hΦ : ∀ (p q n : ℤ) (hpq : p + q = n),
    HomologicalComplex₂.ιTotal
          ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
            ((pushforwardComplex f).obj A)).obj B)
          (.up ℤ) p q n hpq ≫ Φ.hom.f n =
      Stacks.ProjectionFormula.projectionFormulaMap' f (A.X p) (B.X q) ≫
        (StacksDraft.KFlat.modulePushforward f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq))
  (hQA : IsIso (pushforwardComparisonQ f A))
  (hQT : IsIso (pushforwardComparisonQ f
    (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B))))
  (hB : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y B)

include hΦ hQA hQT hB

/-- **The source of the morphism of [Stacks, Tag 0B53], on representatives:**

`Q(Tot(f_*A^• ⊗_{𝒪_Y} B^•)) ≅ Rf_*(QA^•) ⊗^𝐋_{𝒪_Y} QB^•` for `B^•` K-flat.

The K-flat comparison of [Stacks, Tag 06YU] in the right tensor factor, then the comparison
`Q(f_*A^•) ⟶ Rf_*(QA^•)` in the left. -/
def sourceModelIsoOfIso :
    DerivedCategory.Q.obj (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B) ≅
      (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) :=
  ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
      ((pushforwardComplex f).obj A) B hB).symm ≪≫
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).mapIso
      (Iso.prod (@asIso _ _ _ _ _ hQA)
        (Iso.refl (DerivedCategory.Q.obj B)))

/-- **The target of the morphism of [Stacks, Tag 0B53], on representatives:**

`Q(Tot(A^• ⊗_{𝒪_X} f^*B^•)) ≅ QA^• ⊗^𝐋_{𝒪_X} Lf^*(QB^•)` for `B^•` K-flat.

The K-flat comparison of [Stacks, Tag 06YU] in the right tensor factor — `f^*B^•` is K-flat by
[Stacks, Tag 06YC] — then the comparison `Lf^*(QB^•) ⟶ Q(f^*B^•)` inverted, which is invertible
because `B^•` is K-flat. -/
def targetModelIsoOfIso :
    DerivedCategory.Q.obj (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)) ≅
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
        (DerivedCategory.Q.obj A, (derivedPullback f).obj (DerivedCategory.Q.obj B)) :=
  ((canonicalDerivedTensorProduct X.sheaf).comparisonRight A ((pullbackComplex f).obj B)
      (kFlat_modulePullback_unconditional f B hB)).symm ≪≫
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).mapIso
      (Iso.prod (Iso.refl (DerivedCategory.Q.obj A))
        (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).symm)

/-- **The morphism of [Stacks, Tag 0B53] on representatives, as an isomorphism.**

`Rf_*(QA^•) ⊗^𝐋_{𝒪_Y} QB^• ≅ Rf_*(QA^• ⊗^𝐋_{𝒪_X} Lf^*(QB^•))` for `B^•` K-flat: the two endpoint
comparisons with `Q` of the complex-level projection formula
`complexProjectionFormulaIso` and the comparison `Q(f_*-) ⟶ Rf_*(Q-)` between them.

That this is the morphism of [Stacks, Tag 0B53] is
`projectionFormulaMap_eq_derivedModelIso_of_iso`; it is stated as an isomorphism because that is
what makes [Stacks, Tag 0B55] follow. -/
def derivedModelIsoOfIso :
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≅
      (derivedPushforward f).obj
        ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
          (DerivedCategory.Q.obj A, (derivedPullback f).obj (DerivedCategory.Q.obj B))) :=
  (sourceModelIsoOfIso f A B hQA hB).symm ≪≫
    DerivedCategory.Q.mapIso (Φ) ≪≫
    (@asIso _ _ _ _ _ hQT) ≪≫
    (derivedPushforward f).mapIso (targetModelIsoOfIso f A B hB)

/-! ### The ten identities the arrow algebra consumes

Each is a separate top-level declaration with every endpoint written out.  Assembled inside one
proof they exhaust the elaboration budget: the library sets `maxSynthPendingDepth = 3`, so
typeclass inference does strictly more work here than under a bare invocation of the compiler. -/

omit hΦ hQA hQT hB in
/-- **[Stacks, Tag 0FP0] at the pair `(f_*A^•, B^•)`, in the `toTensor` presentation.**  This is
the hypothesis `hFP0` of `map_comp_counit_of_fac`.  It is
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_toTensor_comm` with its two
occurrences of the canonical map to the ordinary total tensor complex rewritten by
`derivedToTensorNatTrans_app_eq`, which is why that reconciliation happens here and nowhere
else.  Note that it carries no K-flatness, which is what makes it usable at `f_*A^•`: that
complex is annihilated by the kernel ideal of `f^♯` and hence never K-flat. -/
private theorem derivedPullbackTensorIso_toTensor_comm_toTensor_of_iso :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj ((pushforwardComplex f).obj A), DerivedCategory.Q.obj B) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app ((pushforwardComplex f).obj A) ×ₘ
              (derivedPullbackNatTrans f).app B) ≫
          (canonicalDerivedTensorProduct X.sheaf).toTensor
            ((pullbackComplex f).obj ((pushforwardComplex f).obj A))
            ((pullbackComplex f).obj B) =
      (derivedPullback f).map
          ((canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A) B) ≫
        (derivedPullbackNatTrans f).app
            (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B) ≫
          DerivedCategory.Q.map
            ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B)) :=
  derivedPullbackTensorIso_toTensor_comm_toTensor f A B

omit hΦ hQT in
/-- **The source comparison is inverted by its own inverse.**  This is the hypothesis `hσ` of
`map_comp_counit_of_fac`, with the two factors of `sourceModelIsoOfIso` written out. -/
private theorem sourceModelIso_inv_comp_comparisonRight_inv_comp_of_iso :
    (sourceModelIsoOfIso f A B hQA hB).inv ≫
        ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
            ((pushforwardComplex f).obj A) B hB).inv ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
            (pushforwardComparisonQ f A ×ₘ 𝟙 (DerivedCategory.Q.obj B)) =
      𝟙 ((Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).obj
        ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B)) :=
  (sourceModelIsoOfIso f A B hQA hB).inv_hom_id

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}] hΦ hQA hQT in
/-- **The K-flat comparison of [Stacks, Tag 06YU] inverts the canonical map to the ordinary total
tensor complex**, on the pair `(f_*A^•, B^•)`.  This is the hypothesis `hcY` of
`map_comp_counit_of_fac`; it is the `toTensor_eq_comparisonRight` field of [Stacks, Tag 06YU],
available because `B^•` is K-flat. -/
private theorem comparisonRight_inv_comp_toTensor_of_iso :
    ((canonicalDerivedTensorProduct Y.sheaf).comparisonRight
          ((pushforwardComplex f).obj A) B hB).inv ≫
        (canonicalDerivedTensorProduct Y.sheaf).toTensor ((pushforwardComplex f).obj A) B =
      𝟙 (DerivedCategory.Q.obj
        (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B)) :=
  comparisonRight_inv_comp_toTensor f A B hB

omit hΦ hQA hQT in
/-- **The target comparison, read off the canonical map to the ordinary total tensor complex.**
This is the hypothesis `hv` of `map_comp_counit_of_fac`: the canonical map of [Stacks, Tag 06YU]
at `(A^•, f^*B^•)` followed by `targetModelIsoOfIso` is the derived tensor product of the identity
with the inverse of the comparison `Lf^*(QB^•) ⟶ Q(f^*B^•)`. -/
private theorem toTensor_comp_targetModelIso_hom_of_iso :
    (canonicalDerivedTensorProduct X.sheaf).toTensor A ((pullbackComplex f).obj B) ≫
        (targetModelIsoOfIso f A B hB).hom =
      (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
        (𝟙 (DerivedCategory.Q.obj A) ×ₘ
          (@asIso _ _ _ _ _ (isIso_derivedPullbackNatTrans_app f B hB)).inv) := by
  rw [(canonicalDerivedTensorProduct X.sheaf).toTensor_eq_comparisonRight A
    ((pullbackComplex f).obj B) (kFlat_modulePullback_unconditional f B hB)]
  exact Iso.hom_inv_id_assoc _ _

omit [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    hΦ hQA hQT hB in
/-- **The canonical map to the ordinary total tensor complex is natural in the left factor.**
This is the hypothesis `hm` of `map_comp_counit_of_fac`: the `toTensor_naturality` field of
[Stacks, Tag 06YU] at the counit of `f^* ⊣ f_*` on complexes and the identity. -/
private theorem map_counit_comp_toTensor_of_iso :
    (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          (DerivedCategory.Q.map ((complexAdjunction f).counit.app A) ×ₘ
            𝟙 (DerivedCategory.Q.obj ((pullbackComplex f).obj B))) ≫
        (canonicalDerivedTensorProduct X.sheaf).toTensor A ((pullbackComplex f).obj B) =
      (canonicalDerivedTensorProduct X.sheaf).toTensor
          ((pullbackComplex f).obj ((pushforwardComplex f).obj A)) ((pullbackComplex f).obj B) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
          (sheafTensor X.sheaf) (ComplexShape.up ℤ)) :=
  map_counit_comp_toTensor f A B

omit hQA hQT hB in
/-- **The complex-level mate identity, read in the derived category.**  This is the hypothesis
`hmate` of `map_comp_counit_of_fac`: `Q` of
`pullbackTensorComplexNatIso_hom_app_comp_mapBifunctorMap`. -/
private theorem map_pullbackTensorComplexNatIso_hom_app_comp_map_mapBifunctorMap_of_iso :
    DerivedCategory.Q.map
          ((pullbackTensorComplexNatIso f).hom.app ((pushforwardComplex f).obj A, B)) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexAdjunction f).counit.app A) (𝟙 ((pullbackComplex f).obj B))
          (sheafTensor X.sheaf) (ComplexShape.up ℤ)) =
      DerivedCategory.Q.map
          ((pullbackComplex f).map (Φ).hom) ≫
        DerivedCategory.Q.map ((complexAdjunction f).counit.app
          (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B))) :=
  map_comp_eq_map_comp DerivedCategory.Q
    (pullbackTensorComplexNatIso_hom_app_comp_mapBifunctorMap f A B Φ hΦ)

/-! ### The transposed identity

Assembled in three steps, each its own declaration: the two sides of the transposed equation are
factored separately through the common composite
`Lf^*(Q-) ⟶ Q(f^*-)`, the comparison of [Stacks, Tag 01CD] on total complexes, the counit in the
left tensor factor and the target comparison, and then matched. -/

omit hΦ hQA hQT in
omit hQT in
/-- **The transposed form of the identity of step 2.**  Applying `Lf^*` to the composite of
comparisons `derivedModelIsoOfIso` and following with the counit of `Lf^* ⊣ Rf_*` gives the
comparison of [Stacks, Tag 079U] followed by the counit in the left tensor factor — which is
exactly the equation that characterizes the morphism of [Stacks, Tag 0B53]. -/
private theorem map_derivedModel_comp_counit_of_iso
    (hΦ : ∀ (p q n : ℤ) (hpq : p + q = n),
      HomologicalComplex₂.ιTotal
            ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pushforwardComplex f).obj A)).obj B)
            (.up ℤ) p q n hpq ≫ Φ.hom.f n =
        Stacks.ProjectionFormula.projectionFormulaMap' f (A.X p) (B.X q) ≫
          (StacksDraft.KFlat.modulePushforward f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
                ((pullbackComplex f).obj B))
              (.up ℤ) p q n hpq))
    (hQA : IsIso (pushforwardComparisonQ f A)) :
    (derivedPullback f).map ((sourceModelIsoOfIso f A B hQA hB).inv ≫
          DerivedCategory.Q.map (Φ).hom ≫
          pushforwardComparisonQ f
              (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)) ≫
            (derivedPushforward f).map (targetModelIsoOfIso f A B hB).hom) ≫
        (derivedAdjunction f).counit.app
          ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
            (DerivedCategory.Q.obj A, (derivedPullback f).obj (DerivedCategory.Q.obj B))) =
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f).app
          ((derivedPushforward f).obj (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map
          ((derivedAdjunction f).counit.app (DerivedCategory.Q.obj A) ×ₘ
            𝟙 ((derivedPullback f).obj (DerivedCategory.Q.obj B))) :=
  map_derivedModel_comp_counit f A B hB Φ (sourceModelIsoOfIso f A B hQA hB).inv
    (targetModelIsoOfIso f A B hB).hom
    (sourceModelIso_inv_comp_comparisonRight_inv_comp_of_iso f A B hQA hB)
    (map_pullbackTensorComplexNatIso_hom_app_comp_map_mapBifunctorMap_of_iso f A B Φ hΦ)
    (toTensor_comp_targetModelIso_hom_of_iso f A B hB)
    (comparisonRight_inv_comp_toTensor_of_iso f A B hB) (map_counit_comp_toTensor_of_iso f A B)
    (derivedPullbackTensorIso_toTensor_comm_toTensor_of_iso f A B)

/-- **The morphism of [Stacks, Tag 0B53] on representatives is the complex-level projection
formula.**  For an arbitrary complex `A^•` of `𝒪_X`-modules and a K-flat complex `B^•` of
`𝒪_Y`-modules, the canonical morphism

`Rf_*(QA^•) ⊗^𝐋_{𝒪_Y} QB^• ⟶ Rf_*(QA^• ⊗^𝐋_{𝒪_X} Lf^*(QB^•))`

of [Stacks, Tag 0B53] is `Q` of `complexProjectionFormulaIso`, conjugated by the comparisons that
compute the two derived functors and the derived tensor product on these representatives.  In
particular it is an isomorphism.

This is the K-flat reduction the derived statement of [Stacks, Tag 0B55] needs.  The morphism of
[Stacks, Tag 0B53] is an adjoint transpose, so the identity is proved by verifying the transposed
equation, which is `map_derivedModel_comp_counit_of_iso`. -/
theorem projectionFormulaMap_eq_derivedModelIso_of_iso :
    Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f
        (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B) =
      (derivedModelIsoOfIso f A B Φ hQA hQT hB).hom := by
  rw [Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_eq]
  exact Stacks.AlgebraicGeometry.ProjectionFormula.eq_adjunctionTensorMap_of_map_comp_counit
    (derivedAdjunction f) _ _ _ _ _ _ (map_derivedModel_comp_counit_of_iso f A B Φ hB hΦ hQA)

/-- **[Stacks, Tag 0B55] on representatives.**  The morphism of [Stacks, Tag 0B53] is invertible
at `(QA^•, QB^•)` for an arbitrary complex `A^•` and a K-flat complex `B^•`. -/
theorem isIso_projectionFormulaMap_Q_of_iso :
    IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f
      (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)) := by
  rw [projectionFormulaMap_eq_derivedModelIso_of_iso f A B Φ hΦ hQA hQT hB]
  exact (derivedModelIsoOfIso f A B Φ hQA hQT hB).isIso_hom

end Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

end
