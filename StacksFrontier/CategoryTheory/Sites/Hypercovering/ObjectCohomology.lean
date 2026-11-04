module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexOver

/-!
# Čech cohomology of a hypercovering of an object

Let `C` be a site with fibre products, let `X` be an object of `C` and let `K` be a hypercovering
of `X`. The Čech cohomology of `K` with coefficients in a sheaf `F` of abelian groups is the
cohomology of the complex of sections `SectionsOver.sectionsComplex` of Tag 01GX. This file
identifies its degree-zero part with the group of sections of `F` on `X`, for every abelian sheaf
`F`, and shows that it vanishes in positive degrees when `F` is injective.

## Main results

* `nonempty_zerothCechCohomologyIsoSections`: **Tag 01GV**, the existence half — degree-zero Čech
  cohomology of a hypercovering is isomorphic to the group of sections of the coefficient sheaf on
  the covered object. The canonical identification, inverse to the map induced by the
  augmentation and natural in the sheaf, is `zerothCechCohomologyIsoSections` in
  `Hypercovering/ObjectCohomologyZeroNatural.lean`.
* `cechCohomologyOver_isZero_of_injective`: the positive-degree half of **Tag 01GW** — the Čech
  cohomology of an injective abelian sheaf on a hypercovering vanishes in positive degrees. The
  full statement of Tag 01GW, which adds the degree-zero identification, is
  `cechCohomologyOverIsoOfInjective` in `Hypercovering/ObjectCohomologyZeroNatural.lean`.

## Implementation notes

Čech cohomology is the cohomology of the alternating coface complex obtained by evaluating the
sheaf on the simplicial formal coproduct. The equality asserted by the source is expressed as the
existence of an isomorphism in `AddCommGrpCat`, the two sides being built from independently
chosen sheafifications and products.

Both proofs go through Tag 01GX, which identifies the complex of sections with the complex of
morphisms out of the associated complex of free abelian sheaves, and then through Tag 01GF, which
computes the homology sheaves of that complex. For Tag 01GV the degree-zero step needs that
`Hom(-, F)` preserves the relevant left homology datum, which holds because the incoming
differential vanishes in degree zero; for Tag 01GW it needs only that `Hom(-, F)` is exact, which
is injectivity of `F`.

The degree-zero identification of Tag 01GW is Tag 01GV, which applies to any abelian sheaf and
needs no injectivity, so it is not reproved here. The two halves are assembled into the single
`p`-indexed statement of Tag 01GW by `cechCohomologyOverIsoOfInjective` in
`Hypercovering/ObjectCohomologyZeroNatural.lean`, which is where the canonical degree-zero
isomorphism lives.

Sheafification of `AddCommGrpCat.{max u v w}`-valued presheaves is not a hypothesis of either
tag — the complex of sections is defined without it — so each proof that needs it supplies it
from `hasSheafify_addCommGrpCat`, which obtains it from a small model of the site.

## References

* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GW](https://stacks.math.columbia.edu/tag/01GW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The degree-zero cohomology of the Hom complex of Tag 01GX, for a simplicial
semi-representable object over `X`, is the group of morphisms out of the degree-zero homology
sheaf of the associated simplicial presheaf. -/
noncomputable def homFreeAbelianSheafComplexOverHomologyZeroIso
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max u v w}] {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (F : Sheaf J AddCommGrpCat.{max u v w}) :
    (SectionsOver.homFreeAbelianSheafComplex J K F).homology 0 ≅
      AddCommGrpCat.of
        (SimplicialObject.sheafHomology J
          (SectionsOver.associatedSimplicialPresheaf.{w} K) 0 ⟶ F) := by
  let S := (SimplicialObject.freeAbelianSheafComplexFunctor J).obj
    (SectionsOver.associatedSimplicialPresheaf.{w} K)
  let Y := preadditiveYonedaObj F
  let M := ((Y.mapHomologicalComplex (ComplexShape.up ℕ)).obj S.op)
  let Forget := forget₂ (ModuleCat (End F)) AddCommGrpCat
  let U := ((Forget.mapHomologicalComplex (ComplexShape.up ℕ)).obj M)
  change U.homology 0 ≅ AddCommGrpCat.of (S.homology 0 ⟶ F)
  have : PreservesLimits Y := by infer_instance
  have : Functor.PreservesZeroMorphisms Y := by infer_instance
  have hf : (S.op.sc 0).f = 0 := by
    simp only [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor']
    rfl
  have hpres (h : (S.op.sc 0).LeftHomologyData) : h.IsPreservedBy Y := by
    refine ⟨?_, ?_⟩
    · infer_instance
    · have hzero : h.f' = 0 := by
        apply (cancel_mono h.i).1
        rw [h.f'_i, hf]
        simp
      rw [hzero]
      infer_instance
  have : Y.PreservesLeftHomologyOf (S.op.sc 0) := ⟨hpres⟩
  let eU : U.homology 0 ≅ Forget.obj (M.homology 0) := by
    calc
      U.homology 0 ≅ U.cycles 0 := (CochainComplex.isoHomologyπ₀ U).symm
      _ ≅ Forget.obj (M.cycles 0) := by
        have : Forget.PreservesHomology := Functor.preservesHomologyOfExact Forget
        change ((M.sc 0).map Forget).cycles ≅ Forget.obj (M.sc 0).cycles
        exact (M.sc 0).mapCyclesIso Forget
      _ ≅ Forget.obj (M.homology 0) := Forget.mapIso (CochainComplex.isoHomologyπ₀ M)
  let eM : M.homology 0 ≅ Y.obj (Opposite.op (S.homology 0)) := by
    calc
      M.homology 0 ≅ M.cycles 0 := (CochainComplex.isoHomologyπ₀ M).symm
      _ ≅ Y.obj (S.op.cycles 0) := by
        change ((S.op.sc 0).map Y).cycles ≅ Y.obj ((S.op.sc 0).cycles)
        exact (S.op.sc 0).mapCyclesIso Y
      _ ≅ Y.obj (S.op.homology 0) := Y.mapIso (CochainComplex.isoHomologyπ₀ S.op)
      _ ≅ Y.obj (Opposite.op (S.homology 0)) := Y.mapIso (S.homologyOp 0)
  exact eU.trans (Forget.mapIso eM)

/-- Morphisms from the free abelian presheaf on a representable presheaf to a presheaf of abelian
groups are the sections of that presheaf on the representing object. -/
noncomputable def freeEvaluationHomAddEquiv {X : C} (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    ((uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w}) ⟶ F) ≃+ F.obj (op X) :=
  let P := uliftYoneda.{max u w}.obj X
  let e := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv P F).trans
    (uliftYonedaEquiv.{max u w} (F := F ⋙ forget AddCommGrpCat))
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := fun _ _ ↦ rfl }

/-- **Stacks Project, Tag 01GV**, the existence half. Degree-zero Čech cohomology of a
hypercovering is isomorphic to the group of sections of the coefficient sheaf on the covered
object.

This asserts only that some isomorphism exists. The canonical one, inverse to the map induced by
the augmentation of the Čech complex and natural in the sheaf, is
`zerothCechCohomologyIsoSections`. -/
@[stacks 01GV "some isomorphism Ȟ⁰(K, 𝓕) ≅ 𝓕(X) exists"]
theorem nonempty_zerothCechCohomologyIsoSections (J : Pretopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    Nonempty ((SectionsOver.sectionsComplex J.toGrothendieck K F).homology 0 ≅
      F.obj.obj (op X)) := by
  apply Nonempty.intro
  let J' := J.toGrothendieck
  letI : HasSheafify J' AddCommGrpCat.{max u v w} := hasSheafify_addCommGrpCat.{w} J'
  have eSections : (SectionsOver.sectionsComplex J' K F).homology 0 ≅
      (SectionsOver.homFreeAbelianSheafComplex J' K F).homology 0 :=
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) 0).mapIso
      (SectionsOver.sectionsComplexIsoHomFreeAbelianSheafComplex J' K F)
  let eHomFree := homFreeAbelianSheafComplexOverHomologyZeroIso J' K F
  have eGFHom : AddCommGrpCat.of
      (SimplicialObject.sheafHomology J' (SectionsOver.associatedSimplicialPresheaf.{w} K) 0 ⟶
        F) ≅
        AddCommGrpCat.of
          ((presheafToSheaf J' AddCommGrpCat.{max u v w}).obj
            (uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w}) ⟶ F) := by
    let Y := preadditiveYonedaObj F
    let Forget := forget₂ (ModuleCat (End F)) AddCommGrpCat
    change Forget.obj (Y.obj (Opposite.op (SimplicialObject.sheafHomology J'
        (SectionsOver.associatedSimplicialPresheaf.{w} K) 0))) ≅
      Forget.obj (Y.obj (Opposite.op
        ((presheafToSheaf J' AddCommGrpCat.{max u v w}).obj
          (uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w}))))
    exact Forget.mapIso
      (Y.mapIso (sheafHomologyZeroIso_of_isHypercovering J K hK).op.symm)
  have eAdj : AddCommGrpCat.of
      ((presheafToSheaf J' AddCommGrpCat.{max u v w}).obj
        (uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w}) ⟶ F) ≅
        AddCommGrpCat.of (F.obj.obj (op X)) :=
    (((sheafificationAdjunction J' AddCommGrpCat.{max u v w}).homAddEquiv
        (uliftYoneda.{max u w}.obj X ⋙ AddCommGrpCat.free.{max u v w}) F).trans
      (freeEvaluationHomAddEquiv (X := X) F.obj)).toAddCommGrpIso
  exact eSections.trans (eHomFree.trans (eGFHom.trans eAdj))

/-- **Stacks Project, Tag 01GW (positive degrees).** The positive-degree Čech cohomology of an
injective abelian sheaf on a hypercovering vanishes.

Sheafification, which the statement does not need, is supplied inside the proof from
`hasSheafify_addCommGrpCat`. -/
@[stacks 01GW "positive degrees"]
theorem cechCohomologyOver_isZero_of_injective (J : Pretopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering J K)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) [Injective I]
    (p : ℕ) (hp : 0 < p) :
    IsZero ((SectionsOver.sectionsComplex J.toGrothendieck K I).homology p) := by
  let _ : HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w} :=
    hasSheafify_addCommGrpCat.{w} J.toGrothendieck
  let S : ChainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) ℕ :=
    (SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).obj
      (SectionsOver.associatedSimplicialPresheaf.{w} K)
  have hS : IsZero (S.homology p) :=
    isZero_sheafHomology_of_isHypercovering J K hK p hp
  have hSop : IsZero (S.op.homology p) := IsZero.of_iso hS.op (S.homologyOp p)
  have hExactOp : S.op.ExactAt p :=
    (HomologicalComplex.exactAt_iff_isZero_homology S.op p).2 hSop
  let G := preadditiveYonedaObj I
  let M : HomologicalComplex (ModuleCat (End I)) (ComplexShape.up ℕ) :=
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj S.op)
  have hME : M.ExactAt p := ShortComplex.Exact.map hExactOp G
  let U : CochainComplex AddCommGrpCat.{max u v w} ℕ :=
    ((forget₂ (ModuleCat (End I)) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj M
  let Forget := forget₂ (ModuleCat (End I)) AddCommGrpCat
  let : Forget.PreservesHomology := Functor.preservesHomologyOfExact Forget
  have hUE : U.ExactAt p := ShortComplex.Exact.map hME Forget
  exact IsZero.of_iso ((HomologicalComplex.exactAt_iff_isZero_homology U p).1 hUE)
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).mapIso
      (SectionsOver.sectionsComplexIsoHomFreeAbelianSheafComplex J.toGrothendieck K I))

end Stacks.CategoryTheory.Hypercovering

end
