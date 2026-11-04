module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Kernels
public import StacksFrontier.CategoryTheory.Limits.KernelCoproduct

/-!
# Direct sums and colimits of adequate functors

A direct sum of adequate module-valued functors on the commutative algebras over a ring is
adequate, and so is a colimit of adequate functors.

## Main results

* `AdequateFunctor.isAdequate_coproduct` is closure under arbitrary direct sums.
* `AdequateFunctor.isAdequate_colimit` is closure under arbitrary colimits.

## Implementation notes

The direct sum is the categorical coproduct and the colimit is the categorical colimit, each
retaining its canonical cocone and universal property.

The source works in a single universe. Here the values of the functors are taken in the
universe `max u v w` that already contains the base ring and the algebra carriers, which is
the universe in which adequacy presents a functor as a kernel; and the index type, resp. the
index category, is assumed small, resp. essentially small, relative to that universe. Both
smallness assumptions hold automatically for an index in any universe contained in
`max u v w`, in particular for every finite shape, and the direct sum of a family indexed by
a larger type need not exist.

The reduction of a general colimit to a direct sum is the one of the source: a colimit is a
cokernel of a map between two direct sums, which is adequate by Tag 06V2 once the two direct
sums are known to be adequate. The direct-sum case rests on exactness of coproducts of
module-valued functors, which `hasExactColimitsOfShape_moduleValuedFunctor` derives from the
corresponding axiom for abelian groups.

## References

* [Stacks Project, Tag 06V4](https://stacks.math.columbia.edu/tag/06V4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AdequateFunctor

universe i j k u v w

section Exactness

variable (A : Type u) [CommRing A]

/-- Coproducts of module-valued functors indexed by a type in the value universe are exact. -/
public lemma hasExactColimitsOfShape_moduleValuedFunctor (ι : Type w) :
    HasExactColimitsOfShape (Discrete ι) (ModuleValuedFunctor.{max u v w, v} A) :=
  let _ : AB4OfSize.{w} AddCommGrpCat.{max u v w} :=
    AB4OfSize_shrink.{w, max u v w} (C := AddCommGrpCat.{max u v w})
  let _ := AB4OfSize.ofShape (C := AddCommGrpCat.{max u v w}) ι
  HasExactColimitsOfShape.domain_of_functor (Discrete ι)
    (PresheafOfModules.toPresheaf.{max u v w} (algebraRingDiagram.{v} A))

/-- Extension of scalars commutes with all colimits of modules, of any shape: evaluating at an
algebra turns it into Mathlib's extension of scalars, which is a left adjoint, and colimits of
module-valued functors are detected by the evaluations. -/
public instance moduleExtensionFunctor_preservesColimitsOfShape (J : Type j) [Category.{k} J] :
    PreservesColimitsOfShape J (moduleExtensionFunctor.{max u v w, v} A) where
  preservesColimit {K} := { preserves := fun {c} hc => ⟨by
      apply PresheafOfModules.evaluationJointlyReflectsColimits
      intro X
      let _ : PreservesColimitsOfShape J
          (moduleExtensionFunctor.{max u v w, v} A ⋙
            PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X) :=
        preservesColimitsOfShape_of_natIso (moduleExtensionEvaluationIso A X).symm
      exact isColimitOfPreserves
        (moduleExtensionFunctor.{max u v w, v} A ⋙
          PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X) hc⟩ }

/-- The direct sum of a family of base-changed module maps agrees, under the comparison
isomorphisms for the two direct sums, with the base change of the direct sum of the maps. -/
public lemma sigma_map_moduleExtensionFunctor_map {J : Type (max u v w)}
    {M N : J → ModuleCat.{max u v w} A} (f : ∀ j, M j ⟶ N j) :
    Limits.Sigma.map (fun j => (moduleExtensionFunctor.{max u v w, v} A).map (f j)) ≫
        sigmaComparison (moduleExtensionFunctor.{max u v w, v} A) N =
      sigmaComparison (moduleExtensionFunctor.{max u v w, v} A) M ≫
        (moduleExtensionFunctor.{max u v w, v} A).map (Limits.Sigma.map f) := by
  apply colimit.hom_ext
  intro j
  obtain ⟨j⟩ := j
  show Sigma.ι _ j ≫ _ = Sigma.ι _ j ≫ _
  rw [Sigma.ι_map_assoc, ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc,
    ← (moduleExtensionFunctor.{max u v w, v} A).map_comp,
    ← (moduleExtensionFunctor.{max u v w, v} A).map_comp, Sigma.ι_map]

end Exactness

section Main

variable {A : Type u} [CommRing A]

/-- A direct sum of adequate module-valued functors, indexed by a type in the value universe,
is adequate. -/
private lemma isAdequate_coproduct_small {ι : Type (max u v w)}
    (F : ι → ModuleValuedFunctor.{max u v w, v} A)
    (hF : ∀ a, IsAdequate (𝟭 _) (F a)) :
    IsAdequate (𝟭 _) (∐ F) := by
  classical
  choose M N f he using fun a => (isAdequate_iff (F a)).mp (hF a)
  let _ : HasExactColimitsOfShape (Discrete ι) (ModuleValuedFunctor.{max u v w, v} A) :=
    hasExactColimitsOfShape_moduleValuedFunctor A ι
  let E := moduleExtensionFunctor.{max u v w, v} A
  let eM : E.obj (∐ M) ≅ ∐ (fun a => E.obj (M a)) := PreservesCoproduct.iso E M
  let eN : E.obj (∐ N) ≅ ∐ (fun a => E.obj (N a)) := PreservesCoproduct.iso E N
  let g : (∐ fun a => E.obj (M a)) ⟶ ∐ (fun a => E.obj (N a)) :=
    CategoryTheory.Limits.Sigma.map f
  refine (isAdequate_iff _).mpr ⟨∐ M, ∐ N, eM.hom ≫ g ≫ eN.inv, ⟨?_⟩⟩
  exact CategoryTheory.Limits.Sigma.mapIso (fun a => (he a).some) ≪≫ kernelSigmaMapIso f ≪≫
    (CategoryTheory.Limits.kernelCompMono g eN.inv).symm ≪≫
      (CategoryTheory.Limits.kernelIsIsoComp eM.hom (g ≫ eN.inv)).symm

/-- A colimit of adequate module-valued functors over a shape in the value universe is
adequate. -/
private lemma isAdequate_colimit_small {J : Type (max u v w)} [Category.{max u v w} J]
    (F : J ⥤ ModuleValuedFunctor.{max u v w, v} A)
    (hF : ∀ a, IsAdequate (𝟭 _) (F.obj a)) :
    IsAdequate (𝟭 _) (colimit F) := by
  let s : (∐ fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1) ⟶ ∐ F.obj :=
    CategoryTheory.Limits.Sigma.desc fun f =>
      F.map f.2 ≫ colimit.ι (Discrete.functor F.obj) ⟨f.1.2⟩
  let t : (∐ fun f : Σ p : J × J, p.1 ⟶ p.2 => F.obj f.1.1) ⟶ ∐ F.obj :=
    CategoryTheory.Limits.Sigma.desc fun f => colimit.ι (Discrete.functor F.obj) ⟨f.1.1⟩
  refine (isAdequate_cokernel (s - t) (isAdequate_coproduct_small _ fun _ => hF _)
    (isAdequate_coproduct_small F.obj hF)).of_iso ?_
  refine (colimit.isoColimitCocone (colimitCoconeOfCoequalizerAndCoproduct F)) ≪≫ ?_
  exact IsColimit.coconePointUniqueUpToIso
    (CategoryTheory.Preadditive.isColimitCokernelCoforkOfCofork
      (CategoryTheory.Limits.coequalizerIsCoequalizer s t))
    (CategoryTheory.Limits.colimit.isColimit (parallelPair (s - t) 0))

/-- **Stacks Lemma 06V4, direct sums.** A direct sum of adequate functors is adequate. -/
@[stacks 06V4 "direct sums"]
public lemma isAdequate_coproduct {ι : Type i} [Small.{max u v w} ι]
    (F : ι → ModuleValuedFunctor.{max u v w, v} A) [HasCoproduct F]
    (hF : ∀ a, IsAdequate (𝟭 _) (F a)) :
    IsAdequate (𝟭 _) (∐ F) := by
  let e : ι ≃ Shrink.{max u v w} ι := equivShrink ι
  have h : IsAdequate (𝟭 _) (∐ fun s => F (e.symm s)) :=
    isAdequate_coproduct_small _ (fun s => hF _)
  exact h.of_iso (CategoryTheory.Limits.Sigma.whiskerEquiv e (fun a => eqToIso (by simp [e])))

/-- **Stacks Lemma 06V4, colimits.** A colimit of adequate functors is adequate. -/
@[stacks 06V4 "colimits"]
public lemma isAdequate_colimit {J : Type j} [Category.{k} J]
    [EssentiallySmall.{max u v w} J]
    (F : J ⥤ ModuleValuedFunctor.{max u v w, v} A) [HasColimit F]
    (hF : ∀ a, IsAdequate (𝟭 _) (F.obj a)) :
    IsAdequate (𝟭 _) (colimit F) := by
  let e : J ≌ SmallModel.{max u v w} J := equivSmallModel.{max u v w} J
  exact (isAdequate_colimit_small (e.inverse ⋙ F) fun _ => hF _).of_iso
    (HasColimit.isoOfEquivalence e ((Functor.associator _ _ _).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor))

end Main

end AdequateFunctor

end
