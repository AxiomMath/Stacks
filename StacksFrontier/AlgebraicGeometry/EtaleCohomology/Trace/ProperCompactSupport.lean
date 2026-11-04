module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison

/-!
# Compactly supported cohomology of a proper scheme

A proper morphism `f : X ⟶ Spec k` is its own compactification. Through it, the compactly
supported cohomology `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_!K)|_{X̄_k̄})` of Remark 03UI (2) is the
ordinary cohomology `RΓ(X_k̄, K|_{X_k̄})`, because extension by zero along the identity is the
identity.

## Main definitions

All names are in the namespace `Stacks.EtaleCohomology`.

* `smallEtaleComposeIdFunctorIso` — composition with `𝟙 X` on the small étale site is the identity.
* `etaleModuleExtensionByZeroIdMapCochainComplexPlusIso` — extension by zero along `𝟙 X`, on
  bounded below complexes, is the identity.
* `galoisCompactSupportCohomologyOfIsProperIso` — `RΓ_c(X_k̄, K) ≅ RΓ(X_k̄, K|_{X_k̄})` through
  that compactification.
* `galoisCompactSupportCohomologyGroupOfIsProperIso` — `H^i_c(X_k̄, K) ≅ H^i(X_k̄, K|_{X_k̄})`.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- Composition with the identity of `X`, on the small étale site of `X`, is the identity. -/
def smallEtaleComposeIdFunctorIso (X : Scheme.{u}) :
    Scheme.Etale.smallEtaleCompose (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents (fun W ↦ MorphismProperty.Over.isoMk (Iso.refl _) (by
    simp [Scheme.Etale.smallEtaleCompose_obj_hom]))
    (fun _ ↦ by apply MorphismProperty.Over.Hom.ext; simp; rfl)

attribute [local instance] HasDerivedCategory.standard

/-- Extension by zero along the identity, on bounded below complexes, is the identity. -/
def etaleModuleExtensionByZeroIdMapCochainComplexPlusIso (X : Scheme.{u})
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    (etaleModuleExtensionByZero.{u, r} Λ (𝟙 X)).mapCochainComplexPlus.obj K ≅ K :=
  ObjectProperty.isoMk _
    ((NatIso.mapHomologicalComplex (etaleModuleExtensionByZeroIdIso Λ X) _).app K.obj ≪≫
      (Functor.mapHomologicalComplexIdIso _ _).app K.obj)

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The compactly supported cohomology of a proper scheme is its cohomology**: through the
compactification of `X` by itself, `RΓ_c(X_k̄, K) = RΓ(X_k̄, K|_{X_k̄})`. -/
def galoisCompactSupportCohomologyOfIsProperIso
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    galoisCompactSupportCohomology.{u, r} Λ f (CompactificationOf.ofProper f) kbar K ≅
      (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk f) kbar)).obj
        (fieldBaseChangeRestriction.{u, r} Λ (Over.mk f) kbar K) :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk f) kbar)).mapIso
    (DerivedCategory.Plus.Q.mapIso
      ((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj (Over.mk f) kbar)).mapCochainComplexPlus.mapIso
          (etaleModuleExtensionByZeroIdMapCochainComplexPlusIso Λ X K)))

/-- **`H^i_c(X_k̄, K) = H^i(X_k̄, K|_{X_k̄})` for a proper scheme**, through its compactification
by itself. -/
def galoisCompactSupportCohomologyGroupOfIsProperIso
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) (i : ℤ) :
    galoisCompactSupportCohomologyGroup.{u, r} Λ f (CompactificationOf.ofProper f) kbar K i ≅
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).obj
        ((etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange (Over.mk f) kbar)).obj
          (fieldBaseChangeRestriction.{u, r} Λ (Over.mk f) kbar K)) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).mapIso
    (galoisCompactSupportCohomologyOfIsProperIso Λ f kbar K)

end Stacks.EtaleCohomology
