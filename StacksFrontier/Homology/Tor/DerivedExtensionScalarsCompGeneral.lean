module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsComp

/-!
# Derived extension of scalars along a composite, at an arbitrary model of the derived category

`StacksFrontier.Homology.Tor.DerivedExtensionScalarsComp` constructs the composition isomorphism
`T_f ⋙ T_g ≅ T_{g ∘ f}` for total derived extension of scalars along `f : R →+* S` and
`g : S →+* T`, together with its characterizing equation against the three comparisons with
degreewise extension of scalars. Every statement there is elaborated under
`attribute [local instance] HasDerivedCategory.standard`, so the standard model of each of the
three derived categories is part of its type, and none of it says anything about any other model.

This file constructs the same isomorphism, and proves the same characterizing equation, for an
arbitrary choice of `HasDerivedCategory` instances on the three categories of modules. The model
binders are written in the binder list of every declaration below.

The constructions and proofs are those of the base module, elaborated against the quantified
instances.

All declarations are in the namespace `StacksDraft.DerivedExtensionScalarsComp`.

## Main definitions

* `extensionScalarsComplexCompIsoGeneral`: the composition isomorphism for degreewise extension of
  scalars, read in the derived category.
* `derivedExtensionScalarsCompComparisonGeneral`: the comparison from the composite of the two
  derived functors to degreewise extension of scalars along `g ∘ f`.
* `derivedExtensionScalarsCompHomGeneral`: the canonical morphism `T_f ⋙ T_g ⟶ T_{g ∘ f}`.
* `derivedExtensionScalarsCompIsoGeneral`: the resulting natural isomorphism.

## Main results

* `derivedExtensionScalarsCompIsoGeneral_hom_app_comp_comparison`: the characterizing equation, at
  an arbitrary cochain complex.
* `derivedExtensionScalarsCompIsoGeneral_eqToIso_comp_comparison`: the same equation with the
  target presented along a homomorphism merely equal to `g ∘ f`.

## References

* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CochainComplex.DerivedExtensionScalars CochainComplex.KFlat

namespace StacksDraft.DerivedExtensionScalarsComp

universe u w

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)

/-- **Degreewise extension of scalars composes**, read in the derived category of `T`-modules at
an arbitrary model. This is `ModuleCat.extendScalarsComp` applied degreewise and localized. -/
def extensionScalarsComplexCompIsoGeneral [HasDerivedCategory.{w} (ModuleCat.{u} T)] :
    (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        extensionOfScalarsComplex.{u, u, u} g ≅
      extensionOfScalarsComplex.{u, u, u} (g.comp f) :=
  isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
      (ComplexShape.up ℤ)) DerivedCategory.Q

/-- The comparison from the composite of the two total derived extension-of-scalars functors to
degreewise extension of scalars along `g ∘ f`, at arbitrary models: the comparison for `f`, then
the comparison for `g`, then `extensionScalarsComplexCompIsoGeneral`. -/
def derivedExtensionScalarsCompComparisonGeneral [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] [HasDerivedCategory.{w} (ModuleCat.{u} T)] :
    DerivedCategory.Q ⋙ ((totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor) ⟶
      extensionOfScalarsComplex.{u, u, u} (g.comp f) :=
  whiskerRight (totalDerivedExtensionScalars.{u, u, u} f).comparison
      (totalDerivedExtensionScalars.{u, u, u} g).functor ≫
    whiskerLeft ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
      (totalDerivedExtensionScalars.{u, u, u} g).comparison ≫
    (extensionScalarsComplexCompIsoGeneral f g).hom

/-- The canonical morphism `T_f ⋙ T_g ⟶ T_{g ∘ f}` at arbitrary models, from the universal
property of the total left derived functor on the right. -/
def derivedExtensionScalarsCompHomGeneral [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] [HasDerivedCategory.{w} (ModuleCat.{u} T)] :
    (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor ⟶
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor :=
  (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.leftDerivedLift
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _
    (derivedExtensionScalarsCompComparisonGeneral f g)

/-- **The defining equation of the canonical morphism.** Composing it with the comparison of
`T_{g ∘ f}` returns the composite comparison, at every cochain complex. -/
theorem derivedExtensionScalarsCompHomGeneral_fac [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] [HasDerivedCategory.{w} (ModuleCat.{u} T)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtensionScalarsCompHomGeneral f g).app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P =
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (extensionScalarsComplexCompIsoGeneral f g).hom.app P :=
  (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.leftDerived_fac_app
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _
    (derivedExtensionScalarsCompComparisonGeneral f g) P

/-- **The canonical morphism is invertible**, at arbitrary models. On a K-flat complex all three
comparisons are invertible, hence so is the canonical morphism there by its defining equation; an
arbitrary object receives a quasi-isomorphism from a K-flat complex (Stacks 06YS), and naturality
transports invertibility along it. -/
instance isIso_derivedExtensionScalarsCompHomGeneral [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] [HasDerivedCategory.{w} (ModuleCat.{u} T)] :
    IsIso (derivedExtensionScalarsCompHomGeneral f g) := by
  have hα (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) :
      IsIso ((derivedExtensionScalarsCompHomGeneral f g).app (DerivedCategory.Q.obj P)) := by
    have := (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison_isIso_of_kFlat P hP
    have := (totalDerivedExtensionScalars.{u, u, u} f).comparison_isIso_of_kFlat P hP
    have hgP := (totalDerivedExtensionScalars.{u, u, u} g).comparison_isIso_of_kFlat
      (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (kFlat_baseChange f P hP)
    have he : IsIso ((extensionScalarsComplexCompIsoGeneral f g).hom.app P) := inferInstance
    rw [← isIso_comp_right_iff _
      ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P),
      derivedExtensionScalarsCompHomGeneral_fac]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hgP he)
  have key (X : DerivedCategory (ModuleCat.{u} R)) :
      IsIso ((derivedExtensionScalarsCompHomGeneral f g).app X) := by
    obtain ⟨P, p, hP, -, hp, -⟩ := exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage X)
    exact (NatTrans.isIso_app_iff_of_iso _
      (asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X)).mp (hα P hP)
  exact NatIso.isIso_of_isIso_app _

/-- **Derived extension of scalars composes**, at arbitrary models: `T_f ⋙ T_g ≅ T_{g ∘ f}`, by
the canonical morphism. -/
def derivedExtensionScalarsCompIsoGeneral [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] [HasDerivedCategory.{w} (ModuleCat.{u} T)] :
    (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor :=
  asIso (derivedExtensionScalarsCompHomGeneral f g)

/-- The underlying morphism of `derivedExtensionScalarsCompIsoGeneral` is the canonical one. -/
@[simp]
theorem derivedExtensionScalarsCompIsoGeneral_hom [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] [HasDerivedCategory.{w} (ModuleCat.{u} T)] :
    (derivedExtensionScalarsCompIsoGeneral f g).hom = derivedExtensionScalarsCompHomGeneral f g :=
  rfl

/-- **The characterizing equation of the composition isomorphism**, at arbitrary models. At every
cochain complex, composing it with the comparison of `T_{g ∘ f}` returns the comparison for `f`,
then the comparison for `g`, then the degreewise composition isomorphism. -/
theorem derivedExtensionScalarsCompIsoGeneral_hom_app_comp_comparison
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    [HasDerivedCategory.{w} (ModuleCat.{u} T)] (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtensionScalarsCompIsoGeneral f g).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison.app P =
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).comparison.app P) ≫
        (totalDerivedExtensionScalars.{u, u, u} g).comparison.app
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (extensionScalarsComplexCompIsoGeneral f g).hom.app P :=
  derivedExtensionScalarsCompHomGeneral_fac f g P

/-- **The characterizing equation, transported along an equation of ring homomorphisms**, at
arbitrary models. This is `derivedExtensionScalarsCompIsoGeneral_hom_app_comp_comparison` with
the target functor presented as derived extension of scalars along a homomorphism `φ` merely
*equal* to `b ∘ a`, which is how the germ map of a composite presents itself.

Proved by substituting the equation, after which the two `eqToHom`s are identities. -/
theorem derivedExtensionScalarsCompIsoGeneral_eqToIso_comp_comparison
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
    [HasDerivedCategory.{w} (ModuleCat.{u} T)]
    (a : R →+* S) (b : S →+* T) (φ : R →+* T) (h : φ = b.comp a)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (derivedExtensionScalarsCompIsoGeneral a b ≪≫
          eqToIso (congrArg
            (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor) h.symm)).hom.app
          (DerivedCategory.Q.obj C) ≫
        (totalDerivedExtensionScalars.{u, u, u} φ).comparison.app C =
      (totalDerivedExtensionScalars.{u, u, u} b).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} a).comparison.app C) ≫
        (totalDerivedExtensionScalars.{u, u, u} b).comparison.app
          (((ModuleCat.extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        (extensionScalarsComplexCompIsoGeneral a b).hom.app C ≫
        eqToHom (congrArg (fun ψ => (extensionOfScalarsComplex.{u, u, u} ψ).obj C) h.symm) := by
  subst h
  simp only [eqToIso_refl, Iso.trans_refl, eqToHom_refl]
  refine Eq.trans (derivedExtensionScalarsCompIsoGeneral_hom_app_comp_comparison a b C) ?_
  exact congrArg (fun t => (totalDerivedExtensionScalars.{u, u, u} b).functor.map
        ((totalDerivedExtensionScalars.{u, u, u} a).comparison.app C) ≫
      (totalDerivedExtensionScalars.{u, u, u} b).comparison.app
        (((ModuleCat.extendScalars a).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫ t)
    (Category.comp_id ((extensionScalarsComplexCompIsoGeneral a b).hom.app C)).symm

end StacksDraft.DerivedExtensionScalarsComp

end
