module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaSummands

/-!
# The complex-level projection formula is the transpose of the termwise comparison

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose underlying map is a
homeomorphism onto a closed subset.
`Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes.complexProjectionFormulaIso` is the
isomorphism of complexes `Tot(f_*A^• ⊗_{𝒪_Y} B^•) ≅ f_* Tot(A^• ⊗_{𝒪_X} f^*B^•)`.  This file
proves the identity that identifies it with the complex-level transpose of the comparison of
[Stacks, Tag 01CD]:

`ϑ ≫ f^*(complexProjectionFormulaIso) ≫ ε = μ`,

where `ϑ` is the comparison `Tot(f^*f_*A^• ⊗_{𝒪_X} f^*B^•) ⟶ f^*Tot(f_*A^• ⊗_{𝒪_Y} B^•)` of
[Stacks, Tag 01CD] on total complexes, `ε` is the counit of `f^* ⊣ f_*` on complexes, and `μ` is
the counit of `f^* ⊣ f_*` in the left tensor factor.  This is the complex-level half of the mate
computation that the derived statement of [Stacks, Tag 0B55] needs.

## Main results

* `projectionFormulaTotalIso_mate`: the identity above for an *arbitrary* isomorphism of total
  complexes `Φ : Tot(f_*A^• ⊗_{𝒪_Y} B^•) ≅ f_* Tot(A^• ⊗_{𝒪_X} f^*B^•)` whose restriction to
  each summand is the termwise projection-formula morphism.  Nothing about `f` is used: the
  closed embedding enters only through the existence of such a `Φ`, so the same identity also
  serves the affine case of [Stacks, Tag 08I9].
* `complexProjectionFormulaIso_mate`: the identity above, at
  `Φ = complexProjectionFormulaIso f hf A B`.

## Implementation notes

*Why `ϑ` and `μ` are parameters with summand descriptions rather than the comparisons
themselves.*  Both comparisons are available in the library, but writing either of them into
this statement forces the elaborator to re-derive the tensor bifunctor's instances at a spelling
fixed by the other factors, and the resulting composite carries two different category instances
— at which point not even associativity of composition is available to a rewrite.  Taking the two
morphisms as parameters constrained only by what they do on each summand of the total complex
removes every such choice from the statement: the hypotheses `hϑ` and `hμ` mention only summand
inclusions, which are stated as `HomologicalComplex₂.ιTotal` of an explicitly written bicomplex.
A consumer supplies the comparisons and discharges `hϑ` and `hμ` from their own summand formulas.

*Why the trailing morphism is bound in `hϑ`.*  The proof rewrites `hϑ` at a position which is
followed by two further factors, and the rewrite must not depend on reassociating across the
boundary where `ϑ` lands: `ϑ` has target a complex in the degreewise-pullback spelling while the
summand inclusion before it lives in the total-complex spelling, and the two are identified only
by unfolding a semireducible definition.  Binding the trailing morphism `g` in `hϑ`, with its
source written as the goal spells it, makes the rewrite match syntactically and removes the need
for `CategoryTheory.Category.assoc` at that point entirely.  The same consideration is why the
source of `ϑ` and `μ` is written as `HomologicalComplex₂.total` of a bicomplex and not as
`Stacks.SheafOfModules.Tensor.tensorComplex`, which is a semireducible definition.

*What the proof is.*  Summand by summand it is the termwise statement
`map_projectionFormulaMap'_comp_counit`, that the ordinary projection-formula morphism is the
transpose of the comparison of [Stacks, Tag 01CD] followed by the counit in the left tensor
factor.  That holds for every morphism of ringed spaces and by definition, the ordinary
projection-formula morphism being an instance of the abstract adjunction-tensor morphism.  So the
content of this file is entirely that `Tot` is compatible with taking transposes termwise, and no
new mathematics enters.

## References

* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.ProjectionFormula
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex comparisonAppIso)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex complexAdjunction
  complexAdjunction_counit_app_f)
open scoped CategoryTheory.Prod

universe u

/-! ### The transpose of a composite, in the abstract -/

section Abstract

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}

/-- **Pushing a morphism of the target through the transpose.**  For an adjunction `L ⊣ R`, a
morphism `u : S ⟶ R T` and a morphism `v : T ⟶ N`, applying `L` to `u`, then `L` of `R` of `v`,
then the counit at `N`, is the transpose of `u` followed by `v`.

Every endpoint is an explicit binder.  That is what makes this usable at the categories of
modules on a ringed space, where the same category and the same functors have two spellings and
a rewrite cannot cross between them: the consumer applies this by `exact`, whose definitional
equality check sees through the difference, instead of rewriting with naturality of the counit,
whose pattern must match the spelling in the goal. -/
lemma map_comp_map_map_comp_counit (adj : L ⊣ R) {S : C} {T N : D}
    (u : S ⟶ R.obj T) (v : T ⟶ N) :
    L.map u ≫ L.map (R.map v) ≫ adj.counit.app N =
      (L.map u ≫ adj.counit.app T) ≫ v := by
  rw [Category.assoc]
  exact congrArg (L.map u ≫ ·) (adj.counit_naturality v)

end Abstract

namespace Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

-- `structureSheafRing` is `@[instance_reducible]`, so it unfolds at `implicit`
-- transparency already, but its reduct stops at an explicit-constructor projection while
-- `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`; these two Mathlib
-- definitions, and `Tensor.ringSheaf` itself — a plain `def`, hence semireducible — are the gap
-- between them.
attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The two summand identities, as separate declarations

Each is stated with every endpoint written out and is elaborated on its own.  Kept out of the
body of `complexProjectionFormulaIso_mate` deliberately: the library's build configuration sets
`maxSynthPendingDepth = 3`, so typeclass inference does strictly more work here than under a
bare invocation of the compiler, and the two identities together inside one proof exceed the
elaboration budget.  Split in this way each one is far below it. -/
/-- **The pullback of a summand inclusion, followed by the pullback of an isomorphism of total
complexes given on summands by the termwise projection-formula morphism, is the pullback of that
termwise morphism followed by the pullback of the pushforward of the summand inclusion.**

This is the hypothesis `hΦ` with the functor applied and a trailing morphism bound, so that a
consumer may rewrite with it at a position followed by further factors without needing to
reassociate across the boundary where the two spellings of the tensor complex meet. -/
private lemma map_ιTotal_comp_map_hom_comp
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
        projectionFormulaMap' f (A.X p) (B.X q) ≫
          (StacksDraft.KFlat.modulePushforward f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
                ((pullbackComplex f).obj B))
              (.up ℤ) p q n hpq))
    (p q n : ℤ) (hpq : p + q = n)
    {Z : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X} (g : _ ⟶ Z) :
    (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pushforwardComplex f).obj A)).obj B)
            (.up ℤ) p q n hpq) ≫
        (StacksDraft.KFlat.modulePullback f).map (Φ.hom.f n) ≫ g =
      (StacksDraft.KFlat.modulePullback f).map (projectionFormulaMap' f (A.X p) (B.X q)) ≫
        (StacksDraft.KFlat.modulePullback f).map
          ((StacksDraft.KFlat.modulePushforward f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
                A).obj ((pullbackComplex f).obj B))
              (.up ℤ) p q n hpq)) ≫ g := by
  rw [← Category.assoc,
    ((StacksDraft.KFlat.modulePullback f).map_comp
      (HomologicalComplex₂.ιTotal
        ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
          ((pushforwardComplex f).obj A)).obj B)
        (.up ℤ) p q n hpq)
      (Φ.hom.f n)).symm,
    hΦ p q n hpq]
  exact (congrArg (· ≫ g) ((StacksDraft.KFlat.modulePullback f).map_comp _ _)).trans
    (Category.assoc _ _ _)

/-- **On each summand, the pullback of `Φ` followed by the counit is the comparison of
[Stacks, Tag 01CD] followed by the counit in the left tensor factor.**

This is the summand form of the mate identity.  It is the termwise
`map_projectionFormulaMap'_comp_counit` transported along `map_ιTotal_comp_map_hom_comp`. -/
private lemma ιTotal_comp_map_hom_comp_counit
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
        projectionFormulaMap' f (A.X p) (B.X q) ≫
          (StacksDraft.KFlat.modulePushforward f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
                ((pullbackComplex f).obj B))
              (.up ℤ) p q n hpq))
    (p q n : ℤ) (hpq : p + q = n) :
    (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pushforwardComplex f).obj A)).obj B)
            (.up ℤ) p q n hpq) ≫
        (StacksDraft.KFlat.modulePullback f).map (Φ.hom.f n) ≫
          (modulePullbackPushforwardAdjunction f).counit.app
            ((((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)).X n) =
      (comparisonAppIso f ((StacksDraft.KFlat.modulePushforward f).obj (A.X p)) (B.X q)).hom ≫
        ((sheafTensor X.sheaf).map
            ((modulePullbackPushforwardAdjunction f).counit.app (A.X p))).app
            ((StacksDraft.KFlat.modulePullback f).obj (B.X q)) ≫
          HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq := by
  rw [map_ιTotal_comp_map_hom_comp f A B Φ hΦ p q n hpq]
  exact ((map_comp_map_map_comp_counit (modulePullbackPushforwardAdjunction f) _ _).trans
    (congrArg (· ≫ _)
      (map_projectionFormulaMap'_comp_counit f (A.X p) (B.X q)))).trans
    (Category.assoc _ _ _)

/-- **An isomorphism of total complexes given on summands by the termwise projection-formula
morphism is the transpose of the termwise comparison.**

Let `Φ : Tot(f_*A^• ⊗_{𝒪_Y} B^•) ≅ f_* Tot(A^• ⊗_{𝒪_X} f^*B^•)` be any isomorphism whose
restriction to the `(p, q)` summand is `Stacks.ProjectionFormula.projectionFormulaMap'` at
`A^p` and `B^q` followed by `f_*` of the summand inclusion on the other side; that is the
hypothesis `hΦ`.  Let `ϑ` be the comparison of [Stacks, Tag 01CD] on total complexes,
`Tot(f^*f_*A^• ⊗_{𝒪_X} f^*B^•) ⟶ f^*Tot(f_*A^• ⊗_{𝒪_Y} B^•)`, described on each summand by
`hϑ`, and let `μ` be the counit of `f^* ⊣ f_*` in the left tensor factor, described on each
summand by `hμ`.  Then `ϑ`, followed by the degreewise pullback of `Φ` and then the counit of
`f^* ⊣ f_*` on complexes, is `μ`.

Both sides are morphisms out of a total complex, so they agree as soon as they agree on every
summand, and there the statement is the termwise `map_projectionFormulaMap'_comp_counit`
together with naturality of the counit.  No hypothesis on `f` is used anywhere: everything
particular to the morphism is in `hΦ`. -/
theorem projectionFormulaTotalIso_mate
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
        projectionFormulaMap' f (A.X p) (B.X q) ≫
          (StacksDraft.KFlat.modulePushforward f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
                ((pullbackComplex f).obj B))
              (.up ℤ) p q n hpq))
    (ϑ : HomologicalComplex₂.total
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
              ((pullbackComplex f).obj B)) (.up ℤ) ⟶
        (pullbackComplex f).obj
          (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B))
    (hϑ : ∀ (p q n : ℤ) (hpq : p + q = n)
        {Z : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X}
        (g : (StacksDraft.KFlat.modulePullback f).obj
            ((((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B).X n) ⟶ Z),
      HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq ≫ ϑ.f n ≫ g =
        (comparisonAppIso f ((StacksDraft.KFlat.modulePushforward f).obj (A.X p)) (B.X q)).inv ≫
          (StacksDraft.KFlat.modulePullback f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
                ((pushforwardComplex f).obj A)).obj B)
              (.up ℤ) p q n hpq) ≫ g)
    (μ : HomologicalComplex₂.total
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
              ((pullbackComplex f).obj B)) (.up ℤ) ⟶
        ((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B))
    (hμ : ∀ (p q n : ℤ) (hpq : p + q = n),
      HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq ≫ μ.f n =
        ((sheafTensor X.sheaf).map
            ((modulePullbackPushforwardAdjunction f).counit.app (A.X p))).app
            ((StacksDraft.KFlat.modulePullback f).obj (B.X q)) ≫
          HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq) :
    ϑ ≫ (pullbackComplex f).map Φ.hom ≫
        (complexAdjunction f).counit.app
          (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)) =
      μ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex₂.total.hom_ext (.up ℤ)
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_obj_X]
  rw [hμ p q n hpq, complexAdjunction_counit_app_f, hϑ p q n hpq]
  exact (congrArg
    ((comparisonAppIso f ((StacksDraft.KFlat.modulePushforward f).obj (A.X p)) (B.X q)).inv ≫ ·)
    (ιTotal_comp_map_hom_comp_counit f A B Φ hΦ p q n hpq)).trans
    (Iso.inv_hom_id_assoc _ _)

/-- **The complex-level projection formula is the transpose of the termwise comparison.**

Let `ϑ` be the comparison of [Stacks, Tag 01CD] on total complexes,
`Tot(f^*f_*A^• ⊗_{𝒪_X} f^*B^•) ⟶ f^*Tot(f_*A^• ⊗_{𝒪_Y} B^•)`, described on each summand by
`hϑ`, and let `μ` be the counit of `f^* ⊣ f_*` in the left tensor factor, described on each
summand by `hμ`.  Then `ϑ`, followed by the degreewise pullback of
`complexProjectionFormulaIso` and then the counit of `f^* ⊣ f_*` on complexes, is `μ`.

This is `projectionFormulaTotalIso_mate` at `Φ = complexProjectionFormulaIso f hf A B`, whose
summand formula is `ι_complexProjectionFormulaIso_hom`. -/
theorem complexProjectionFormulaIso_mate
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (ϑ : HomologicalComplex₂.total
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
              ((pullbackComplex f).obj B)) (.up ℤ) ⟶
        (pullbackComplex f).obj
          (((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B))
    (hϑ : ∀ (p q n : ℤ) (hpq : p + q = n)
        {Z : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X}
        (g : (StacksDraft.KFlat.modulePullback f).obj
            ((((tensorComplex Y.sheaf).obj ((pushforwardComplex f).obj A)).obj B).X n) ⟶ Z),
      HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq ≫ ϑ.f n ≫ g =
        (comparisonAppIso f ((StacksDraft.KFlat.modulePushforward f).obj (A.X p)) (B.X q)).inv ≫
          (StacksDraft.KFlat.modulePullback f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
                ((pushforwardComplex f).obj A)).obj B)
              (.up ℤ) p q n hpq) ≫ g)
    (μ : HomologicalComplex₂.total
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
              ((pullbackComplex f).obj B)) (.up ℤ) ⟶
        ((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B))
    (hμ : ∀ (p q n : ℤ) (hpq : p + q = n),
      HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq ≫ μ.f n =
        ((sheafTensor X.sheaf).map
            ((modulePullbackPushforwardAdjunction f).counit.app (A.X p))).app
            ((StacksDraft.KFlat.modulePullback f).obj (B.X q)) ≫
          HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj A).obj
              ((pullbackComplex f).obj B))
            (.up ℤ) p q n hpq) :
    ϑ ≫ (pullbackComplex f).map (complexProjectionFormulaIso f hf A B).hom ≫
        (complexAdjunction f).counit.app
          (((tensorComplex X.sheaf).obj A).obj ((pullbackComplex f).obj B)) =
      μ :=
  projectionFormulaTotalIso_mate f A B (complexProjectionFormulaIso f hf A B)
    (ι_complexProjectionFormulaIso_hom f hf A B) ϑ hϑ μ hμ

end Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

end
