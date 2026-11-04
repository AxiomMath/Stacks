module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHomCompletion
public import StacksFrontier.RingTheory.LocalCohomology.UniformCohomologyBound
public import StacksCore.Tactic.StacksAttribute

/-!
# Full faithfulness of the completion functor over a complete Noetherian base

**Stacks 0883.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, let
`f : X ⟶ Spec A` be proper and put `𝓘 = I · 𝒪_X`. Then completion

  `Coh(𝒪_X) ⥤ Coh(X, 𝓘)`

is fully faithful.

The source deduces this from two inputs. The first is Stacks 0882: for coherent `G`, `F` with
`H = SheafHom(G, F)` the inverse limit `lim_n H⁰(X, H / 𝓘ⁿ H)` is the morphism group
`Mor_{Coh(X, 𝓘)}(G^∧, F^∧)`; its ingredients are already available in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.InternalHomCompletion`. The second
is the theorem on formal functions over a complete base, Stacks 087U, in degree zero:
`H⁰(X, H) = lim_n H⁰(X, H / 𝓘ⁿ H)`. It enters the results below as the named hypothesis `hFF`;
it is discharged, and the tag 0883 registered, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFunctor/FullyFaithfulComplete.lean`,
so nothing here carries a tag attribute.

## Main definitions

* `Stacks.Algebraization.globalSectionsToLimit` — the comparison
  `H⁰(X, F) ⟶ lim_n H⁰(X, F / 𝓘ⁿ F)` of the theorem on formal functions in degree zero.
* `Stacks.Algebraization.globalSectionsLimitIso` — global sections commute with the inverse limit
  of a coherent adic system.

## Main results

* `Stacks.Algebraization.completionHomLimitEquiv_comp_completionToLimit` — a completion map
  `G^∧ ⟶ F^∧` is the map of systems determined by `G ⟶ F ⟶ lim_n F / 𝓘ⁿ F`.
* `Stacks.Algebraization.completionFunctor_map_bijective` — the completion functor is bijective on
  the morphisms from `G` to `F` as soon as `globalSectionsToLimit` is an isomorphism for
  `SheafHom(G, F)`.
* `Stacks.Algebraization.fullyFaithful_completionFunctor` — full faithfulness, with the theorem on
  formal functions in degree zero as the hypothesis `hFF`; the unconditional statement, which
  carries the tag, is `Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper`.

## Implementation notes

The chain of bijections is the source's: a morphism `G ⟶ F` is a global section of
`SheafHom(G, F)` (`internalHomSectionsTopMapAddEquiv`), the hypothesis carries that section into a
global section of the limit of the completion of `SheafHom(G, F)`, the comparison of 0882
(`completedSheafHomComparison`, an isomorphism by `isIso_completedSheafHomComparison`) carries it
into a global section of `SheafHom(G, lim_n F / 𝓘ⁿ F)`, i.e. a morphism `G ⟶ lim_n F / 𝓘ⁿ F`, and
such a morphism is a map of coherent adic systems `G^∧ ⟶ F^∧` (`completionHomLimitEquiv`). That
the composite is the functor's action on morphisms is `completionFunctor_map_eq`, assembled from
the identities `completionToLimit_completedSheafHomComparison`,
`internalHomSectionsTopEquiv_map` and `internalHomSectionsTopEquiv_mapAddEquiv` together with
`completionHomLimitEquiv_comp_completionToLimit`.

The two presentations of the category of modules on a scheme, `X.Modules` and
`SheafOfModules X.ringCatSheaf`, are kept apart by `coherentObj`, as in
`CompletionFunctor/Adjunction.lean`; the identities above are therefore chained in term mode with
`congrArg` rather than rewritten, since the rewrite motives are not type-correct at `implicit`
transparency.

The ideal sheaf `𝓘 = I · 𝒪_X` of the source is
`Stacks.Cohomology.FormalFunctions.baseIdealSheaf`, and local Noetherianity of `X` is not an extra
hypothesis: it follows from properness over the Noetherian base.

## References

* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.SheafOfModules.InternalHom

section Comparison

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The comparison of the theorem on formal functions in degree zero.** The canonical map from
the global sections of a coherent module to the inverse limit of the global sections of the terms
of its completion, induced by the projections `F ⟶ F / 𝓘ⁿ F`. -/
public noncomputable def globalSectionsToLimit :
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj F.obj ⟶
      limit (C := ModuleCat.{u} Γ(X, ⊤))
        (Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj F)) :=
  limit.lift _
    ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapCone
      (completionCone X I F))

/-- The comparison of the theorem on formal functions is normalized by the global sections of the
projections onto the terms of the completion. -/
public theorem globalSectionsToLimit_π (n : ℕᵒᵖ) :
    globalSectionsToLimit I F ≫
        limit.π (C := ModuleCat.{u} Γ(X, ⊤))
          (Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj F)) n =
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
        (completionProjection X I F n.unop) :=
  limit.lift_π _ n

/-- **Global sections commute with the inverse limit of a coherent adic system.** Evaluation at
the top open preserves the limit of the system, so its value on the limit sheaf is the limit of
the global sections. -/
public noncomputable def globalSectionsLimitIso :
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
        (limit (C := X.Modules) ((completionFunctor X I).obj F).obj) ≅
      limit (C := ModuleCat.{u} Γ(X, ⊤))
        (Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj F)) :=
  IsLimit.conePointUniqueUpToIso
    (@isLimitOfPreserves _ _ _ _ _ _ _
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)))
      (limit.cone ((completionFunctor X I).obj F).obj)
      (limit.isLimit ((completionFunctor X I).obj F).obj)
      (_root_.SheafOfModules.evaluationPreservesLimit _ (op (⊤ : X.Opens))))
    (limit.isLimit (C := ModuleCat.{u} Γ(X, ⊤))
      (Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj F)))

/-- The comparison of the theorem on formal functions is the global sections of the canonical map
into the limit sheaf, followed by the identification of global sections with the limit of global
sections. -/
public theorem globalSectionsToLimit_eq :
    globalSectionsToLimit I F =
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
          (completionToLimit X I F) ≫
        (globalSectionsLimitIso I F).hom := by
  refine limit.hom_ext
    (F := Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj F)) fun n => ?_
  have h1 : (globalSectionsLimitIso I F).hom ≫
      limit.π (C := ModuleCat.{u} Γ(X, ⊤))
        (Stacks.Coherent.globalSectionsSystem ((completionFunctor X I).obj F)) n =
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
        (limit.π ((completionFunctor X I).obj F).obj n) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ n
  exact (globalSectionsToLimit_π I F n).trans
    ((congrArg (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
        (completionToLimit_projection X I F n).symm).trans
      (((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map_comp
          (completionToLimit X I F) (limit.π ((completionFunctor X I).obj F).obj n)).trans
        ((congrArg (fun k => (_root_.SheafOfModules.evaluation X.ringCatSheaf
              (op (⊤ : X.Opens))).map (completionToLimit X I F) ≫ k) h1.symm).trans
          (Category.assoc _ _ _).symm)))

/-- If the comparison of the theorem on formal functions is an isomorphism, then so is the map
that the canonical map into the limit sheaf induces on global sections. -/
public theorem isIso_evaluation_completionToLimit (hFF : IsIso (globalSectionsToLimit I F)) :
    IsIso ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
      (completionToLimit X I F)) := by
  have h : globalSectionsToLimit I F ≫ (globalSectionsLimitIso I F).inv =
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
        (completionToLimit X I F) :=
    (congrArg (fun k => k ≫ (globalSectionsLimitIso I F).inv)
        (globalSectionsToLimit_eq I F)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (_root_.SheafOfModules.evaluation X.ringCatSheaf
              (op (⊤ : X.Opens))).map (completionToLimit X I F) ≫ k)
            (Iso.hom_inv_id (globalSectionsLimitIso I F))).trans
          (Category.comp_id _)))
  rw [← h]
  exact ((@asIso _ _ _ _ _ hFF) ≪≫ (globalSectionsLimitIso I F).symm).isIso_hom

/-- **A completion map is determined by the map into the limit.** The map of coherent adic systems
`G^∧ ⟶ F^∧` attached to the composite `G ⟶ F ⟶ lim_n F / 𝓘ⁿ F` is the completion of `G ⟶ F`.

Both sides are normalized by the projections `G ⟶ G / 𝓘ⁿ G`, which are epimorphisms. -/
public theorem completionHomLimitEquiv_comp_completionToLimit (g : G ⟶ F) :
    completionHomLimitEquiv (I := I) G ((completionFunctor X I).obj F)
        (g.hom ≫ completionToLimit X I F) =
      (completionFunctor X I).map g := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  have hepi := epi_completionProjection X I G n.unop
  refine (@cancel_epi _ _ _ _ _ (completionProjection X I G n.unop) hepi _ _).mp ?_
  have hL : completionProjection X I G n.unop ≫
      (completionHomLimitEquiv (I := I) G ((completionFunctor X I).obj F)
        (g.hom ≫ completionToLimit X I F)).hom.app n =
      (g.hom ≫ completionToLimit X I F) ≫
        limit.π ((completionFunctor X I).obj F).obj n :=
    completionProjection_homToAdicSystem G ((completionFunctor X I).obj F) _ n
  exact hL.trans
    (((Category.assoc _ _ _).trans
        (congrArg (fun k => g.hom ≫ k) (completionToLimit_projection X I F n))).trans
      (completionFunctor_map_quotient X I g n.unop).symm)

/-- **The chain of bijections of Stacks 0883 computes the functor on morphisms.** Read a morphism
`G ⟶ F` as a global section of `SheafHom(G, F)`, push it into the limit of the completion of
`SheafHom(G, F)`, apply the comparison of Stacks 0882 and read the result as a map of coherent
adic systems: the outcome is the completion of the morphism. -/
public theorem completionFunctor_map_eq (g : G ⟶ F) :
    completionHomLimitEquiv (I := I) G ((completionFunctor X I).obj F)
        (internalHomSectionsTopEquiv (coherentObj G)
          (limit (C := X.Modules) ((completionFunctor X I).obj F).obj)
          ((completionToLimit X I (internalHomCoherent X G F) ≫
              completedSheafHomComparison (I := I) G F).val.app (op (⊤ : X.Opens))
            (internalHomSectionsTopMapAddEquiv (coherentObj G) (coherentObj F) g.hom))) =
      (completionFunctor X I).map g :=
  (congrArg
      (fun ψ : (internalHomCoherent X G F).obj ⟶
          (sheafHomFunctor X (coherentObj G)).obj
            (limit (C := X.Modules) ((completionFunctor X I).obj F).obj) =>
        completionHomLimitEquiv (I := I) G ((completionFunctor X I).obj F)
          (internalHomSectionsTopEquiv (coherentObj G)
            (limit (C := X.Modules) ((completionFunctor X I).obj F).obj)
            (ψ.val.app (op (⊤ : X.Opens))
              (internalHomSectionsTopMapAddEquiv (coherentObj G) (coherentObj F) g.hom))))
      (completionToLimit_completedSheafHomComparison (I := I) G F)).trans
    ((congrArg
        (fun k : coherentObj G ⟶ limit (C := X.Modules) ((completionFunctor X I).obj F).obj =>
          completionHomLimitEquiv (I := I) G ((completionFunctor X I).obj F) k)
        ((internalHomSectionsTopEquiv_map (coherentObj G) (completionToLimit X I F)
            (internalHomSectionsTopMapAddEquiv (coherentObj G) (coherentObj F) g.hom)).trans
          (congrArg (fun k => k ≫ completionToLimit X I F)
            (internalHomSectionsTopEquiv_mapAddEquiv (coherentObj G) (coherentObj F)
              g.hom)))).trans
      (completionHomLimitEquiv_comp_completionToLimit I G F g))

/-- **Stacks 0883, the content.** Granted the theorem on formal functions in degree zero for the
internal hom `SheafHom(G, F)`, the completion functor is bijective on the morphisms from `G`
to `F`. -/
public theorem completionFunctor_map_bijective
    (hFF : IsIso (globalSectionsToLimit I (internalHomCoherent X G F))) :
    Function.Bijective
      ((completionFunctor X I).map :
        (G ⟶ F) → ((completionFunctor X I).obj G ⟶ (completionFunctor X I).obj F)) := by
  have hcmpE : IsIso ((completedSheafHomComparison (I := I) G F).val.app (op (⊤ : X.Opens))) :=
    show IsIso ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).map
        (completedSheafHomComparison (I := I) G F)) from
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).mapIso
        (@asIso _ _ _ _ (completedSheafHomComparison (I := I) G F)
          (isIso_completedSheafHomComparison G F))).isIso_hom
  have hsecE : IsIso ((completionToLimit X I (internalHomCoherent X G F)).val.app
      (op (⊤ : X.Opens))) :=
    isIso_evaluation_completionToLimit I (internalHomCoherent X G F) hFF
  have hcompBij : Function.Bijective
      ((completionToLimit X I (internalHomCoherent X G F) ≫
        completedSheafHomComparison (I := I) G F).val.app (op (⊤ : X.Opens))) :=
    ((@asIso _ _ _ _ _ hsecE) ≪≫ (@asIso _ _ _ _ _ hcmpE)).toLinearEquiv.bijective
  have hhom : Function.Bijective (fun g : G ⟶ F => g.hom) :=
    ⟨fun _ _ e => ObjectProperty.hom_ext _ e, fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
  refine (congrArg Function.Bijective (funext (completionFunctor_map_eq I G F))).mp ?_
  exact (completionHomLimitEquiv (I := I) G ((completionFunctor X I).obj F)).bijective.comp
    ((internalHomSectionsTopEquiv (coherentObj G)
        (limit (C := X.Modules) ((completionFunctor X I).obj F).obj)).bijective.comp
      (hcompBij.comp
        ((internalHomSectionsTopMapAddEquiv (coherentObj G) (coherentObj F)).bijective.comp
          hhom)))

end Comparison

/-- **The source's argument for Stacks 0883, over the theorem on formal functions.** Let `A` be
a Noetherian ring complete with respect to `I`, and let `f : X ⟶ Spec A` be proper. Granted the
theorem on formal functions of Stacks 087U in degree zero — the hypothesis `hFF`, that
`H⁰(X, H) ⟶ lim_n H⁰(X, H / 𝓘ⁿ H)` is an isomorphism for every coherent `H` — completion along
`𝓘 = I · 𝒪_X` is a fully faithful functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)`.

Nothing else is assumed: the proof is the source's, through Stacks 0882 for the internal hom.

**No `@[stacks 0883]` attribute here**: `hFF` is a hypothesis the tag does not have. It is
discharged, and the tag registered, by
`Stacks.Algebraization.fullyFaithful_completionFunctor_of_isProper` in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFunctor/FullyFaithfulComplete.lean`. -/
public theorem fullyFaithful_completionFunctor (A : Type u) [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (hFF : ∀ H : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
      letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
      IsIso (globalSectionsToLimit
        (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f) H)) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
    Nonempty (completionFunctor Y
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).FullyFaithful := by
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have hbij (G F : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf) :
      Function.Bijective
        ((completionFunctor Y (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).map :
          (G ⟶ F) →
            ((completionFunctor Y
                (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).obj G ⟶
              (completionFunctor Y
                (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).obj F)) :=
    completionFunctor_map_bijective _ G F (hFF (internalHomCoherent Y G F))
  let _ : (completionFunctor Y
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).Full :=
    { map_surjective := fun {G F} => (hbij G F).2 }
  let _ : (completionFunctor Y
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A J f)).Faithful :=
    { map_injective := fun {G F} => (hbij G F).1 }
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

end Stacks.Algebraization

end
