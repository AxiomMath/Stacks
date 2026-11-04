module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.BaseIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedRestrictModuleAdic

/-!
# Grothendieck existence for the algebraic space a proper scheme represents

Let `A` be a Noetherian ring complete with respect to an ideal `I` and let `U` be an object of the
big fppf site over `Spec A` with underlying scheme `T`.  The algebraic space `yoneda.obj U` carries
the sheaf of ideals `I · 𝒪` (`AlgebraicGeometry.Space.baseIdealSheaf`) and `T` carries the ideal
sheaf `I · 𝒪_T` (`Stacks.Cohomology.FormalFunctions.baseIdealSheaf`).  This file proves that the
two correspond across restriction to `T` — the hypothesis `hIbar` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedRestrictModuleAdic.lean` — and deduces
Grothendieck's existence theorem for `yoneda.obj U` from Stacks 088C for `T` when `T` is proper
over `Spec A`.

## Main results

* `AlgebraicGeometry.Space.selfOpensRingHom_comp_baseRingHom`: the structure ring maps from `A`
  agree.
* `AlgebraicGeometry.Space.map_selfOpensRingHom_baseIdealSheaf`: the two base ideals correspond.
* `AlgebraicGeometry.Space.isEquivalence_completionFunctor_yoneda_of_isProper`: **the completion
  functor of Stacks 08B4 on `yoneda.obj U` along `I · 𝒪` is an equivalence** for `T` proper over
  `Spec A`.  With `AlgebraicGeometry.Space.representedRestrictCompletionIso` it identifies, on a
  proper scheme read as an algebraic space, coherent adic systems with completions of coherent
  modules, compatibly with restriction to the scheme.

Nothing here carries a `stacks` attribute: the statement is the representable case of
Stacks 08BE, whose general case is not proved here, and its content is Stacks 088C, registered on
the scheme-level statement.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
* [Stacks Project, Tag 08BE](https://stacks.math.columbia.edu/tag/08BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A))) (U : BigFppfOver B (Spec (.of A)) hA)

/-- **The structure ring maps agree**: the scalars `A ⟶ Γ(T, ⊤) ⟶ Γ(T, O)` carried to the chart
`O` cuts out are the structure ring map `A ⟶ 𝒪(selfOpensFunctor O)` of that chart of the algebraic
space `yoneda.obj U` over `Spec A`. -/
theorem selfOpensRingHom_comp_baseRingHom
    (O : ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).Opens) :
    (selfOpensRingHom B (Spec (.of A)) hA U O).comp
        ((((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).presheaf.map
          (homOfLE le_top).op).hom.comp
          ((Scheme.ΓSpecIso (.of A)).inv ≫ (B.inclusion.map U.hom).appTop).hom) =
      chartBaseRingHom A (schemeSpace U)
        ((selfOpensFunctor B (Spec (.of A)) hA U).obj O) := by
  rw [selfOpensRingHom_eq_topIso B (Spec (.of A)) hA U O]
  ext a
  have key : (Scheme.ΓSpecIso (.of A)).inv ≫ (B.inclusion.map U.hom).appTop ≫
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).presheaf.map (homOfLE le_top).op ≫
        (Scheme.Opens.topIso O).inv =
      (Scheme.ΓSpecIso (.of A)).inv ≫ (O.ι ≫ B.inclusion.map U.hom).appTop := by
    have hpq : ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).presheaf.map
          (homOfLE le_top).op ≫ (Scheme.Opens.topIso O).inv = O.ι.appTop := by
      rw [Scheme.Opens.ι_appTop]
      exact (((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).presheaf.map_comp _ _).symm.trans
        (congrArg ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).presheaf.map
          (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))
    rw [Scheme.Hom.comp_appTop, hpq]
  exact congrArg (fun φ => φ.hom a) key

/-- **The base ideals correspond**: over an affine open `O` of the scheme `T` underlying `U`, the
ideal sheaf `I · 𝒪_T` generates the sheaf of ideals `I · 𝒪` of the algebraic space `yoneda.obj U`
on the chart `O` cuts out.  This is the hypothesis `hIbar` of
`AlgebraicGeometry.Space.representedRestrictAdic` and
`AlgebraicGeometry.Space.isEquivalence_completionFunctor_of_scheme` for the pair of base ideals. -/
theorem map_selfOpensRingHom_baseIdealSheaf
    (O : ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).affineOpens) :
    Ideal.map (selfOpensRingHom B (Spec (.of A)) hA U O.1)
        ((Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I (B.inclusion.map U.hom)).ideal O) =
      chartSectionIdeal B (Spec (.of A)) hA (yoneda.obj U)
        (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)
        (baseIdealSheaf A ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩ I)
        ((selfOpensFunctor B (Spec (.of A)) hA U).obj O.1) := by
  rw [Stacks.Cohomology.FormalFunctions.baseIdealSheaf_ideal,
    Stacks.Cohomology.FormalFunctions.baseIdeal, Ideal.map_map, Ideal.map_map]
  exact (congrArg (fun φ => Ideal.map φ I) ((RingHom.comp_assoc _ _ _).trans
    (selfOpensRingHom_comp_baseRingHom A B hA U O.1))).trans
    (baseIdealSheaf_obj_of_isAffine A
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩ I
      ((selfOpensFunctor B (Spec (.of A)) hA U).obj O.1) (O.2 : IsAffineOpen O.1)).symm

/-- **Grothendieck's existence theorem for the algebraic space represented by a proper scheme.**
Let `A` be a Noetherian ring complete with respect to an ideal `I`, and let `U` be an object of the
big fppf site over `Spec A` whose scheme `T` is proper over `Spec A`.  Then the completion functor
`Coh(yoneda.obj U) ⥤ Coh(yoneda.obj U, I · 𝒪)` of Stacks 08B4 is an equivalence.

This is Stacks 088C for `T` (`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper`)
carried to the represented algebraic space by
`AlgebraicGeometry.Space.isEquivalence_completionFunctor_of_scheme`, the two base ideals being
matched by `AlgebraicGeometry.Space.map_selfOpensRingHom_baseIdealSheaf`.  It is the case of a
representable algebraic space of Stacks 08BE, and is not registered against that tag. -/
theorem isEquivalence_completionFunctor_yoneda_of_isProper [IsNoetherianRing A]
    [IsAdicComplete I A]
    [_root_.AlgebraicGeometry.IsProper (representedStructureMorphism A B hA U)] :
    letI : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) :=
      LocallyOfFiniteType.isLocallyNoetherian (representedStructureMorphism A B hA U)
    (completionFunctor B (Spec (.of A)) hA (yoneda.obj U)
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)
      (Space.baseIdealSheaf A ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩ I)
      (isQuasicoherentOnSite_baseIdealSheaf A
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of A)) hA U⟩ I)).IsEquivalence := by
  let : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian (representedStructureMorphism A B hA U)
  have := Stacks.Algebraization.isEquivalence_completionFunctor_of_isProper A I
    (representedStructureMorphism A B hA U)
  exact isEquivalence_completionFunctor_of_scheme B (Spec (.of A)) hA U _ _
    (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I (representedStructureMorphism A B hA U))
    (map_selfOpensRingHom_baseIdealSheaf A I B hA U)

end AlgebraicGeometry.Space

end
