module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.FormalFunctionsAdicLimitUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable

/-!
# The theorem on formal functions for global sections

Stacks 08B0 in degree zero, read on global sections rather than on degree-zero cohomology: for a
proper algebraic space `X` over a Noetherian ring `A` complete with respect to an ideal `I` and a
coherent `𝒪_X`-module `F`, a global section of `F` is the same thing as a compatible family of
global sections of the quotients `F / Iⁿ F`.

## Main results

* `AlgebraicGeometry.Space.C1573.spaceCohomologyZeroIso`: `H⁰(X, -) ≅ Γ(X, -)`.
* `AlgebraicGeometry.Space.C1573.eq_of_sectionsMap_idealQuotientπ_eq` and
  `AlgebraicGeometry.Space.C1573.exists_sectionsMap_idealQuotientπ_eq`: injectivity and
  surjectivity of `Γ(X, F) ⟶ lim_n Γ(X, F / Iⁿ F)`.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.IntertwinedFiltration Stacks.IntertwinedFiltration.C1573
  Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space.C1573

attribute [local instance] hasInjectiveResolutions_modules

/-- **`H⁰ = Γ`** for modules on an algebraic space. -/
def spaceCohomologyZeroIso {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (X : AlgebraicSpaces B S hS) :
    spaceCohomology B S hS X 0 ≅
      globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
  haveI := preservesFiniteLimits_globalSectionsFunctor_ringUniverse.{u + 1, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  Functor.rightDerivedZeroIsoSelf _

section Situation

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : AlgebraicSpaces B (Spec (.of A)) hA} [IsNoetherianRing A]
  (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f.hom)
  (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
  (I : Ideal A)

variable (X) in
/-- The isomorphism `H⁰ ≅ Γ` as a map of types. -/
abbrev spaceCohomologyZeroEquiv (M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    (spaceCohomology B (Spec (.of A)) hA X 0).obj M ≃ M.sections :=
  ((spaceCohomologyZeroIso X).app M).toLinearEquiv.toEquiv

variable (X) in
omit [IsNoetherianRing A] in
/-- The bijection `spaceCohomologyZeroEquiv` is natural in the module. -/
theorem spaceCohomologyZeroEquiv_naturality {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (g : M ⟶ N) (x : (spaceCohomology B (Spec (.of A)) hA X 0).obj M) :
    spaceCohomologyZeroEquiv X N (((spaceCohomology B (Spec (.of A)) hA X 0).map g).hom x) =
      SheafOfModules.sectionsMap g (spaceCohomologyZeroEquiv X M x) :=
  congrArg (fun k => k.hom x) ((spaceCohomologyZeroIso X).hom.naturality g)

/-- `spaceCohomologyZeroEquiv.symm` intertwines `sectionsMap` with the map on `H⁰`. -/
private theorem spaceCohomologyZeroEquiv_symm_sectionsMap {B : BigFppfSite.{u}} {A : Type u}
    [CommRing A] {hA : B.Contains (Spec (.of A))} (X : AlgebraicSpaces B (Spec (.of A)) hA)
    {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2} (g : M ⟶ N) (s : M.sections) :
    (spaceCohomologyZeroEquiv X N).symm (SheafOfModules.sectionsMap g s) =
      ((spaceCohomology B (Spec (.of A)) hA X 0).map g).hom
        ((spaceCohomologyZeroEquiv X M).symm s) := by
  rw [Equiv.symm_apply_eq, spaceCohomologyZeroEquiv_naturality, Equiv.apply_symm_apply]

include hf in
/-- Two global sections of `F` whose images in every `Γ(X, F / Iⁿ F)` agree are equal. -/
theorem eq_of_sectionsMap_idealQuotientπ_eq [IsAdicComplete I A] {s s' : F.sections}
    (h : ∀ n, SheafOfModules.sectionsMap
        (idealQuotientπ (baseRingHom A B hA X.1 X.2) F (I ^ n)) s =
      SheafOfModules.sectionsMap (idealQuotientπ (baseRingHom A B hA X.1 X.2) F (I ^ n)) s') :
    s = s' := by
  have hb := (bijective_cohomologyToIdealQuotientLimit f hf F I 0).1
  refine (spaceCohomologyZeroEquiv X F).symm.injective (hb ?_)
  refine Subtype.ext (funext fun n => ?_)
  exact (spaceCohomologyZeroEquiv_symm_sectionsMap X _ s).symm.trans <|
    (congrArg _ (h n)).trans (spaceCohomologyZeroEquiv_symm_sectionsMap X _ s')

include hf in
/-- A compatible family of global sections of the quotients `F / Iⁿ F` is the image of a global
section of `F`. -/
theorem exists_sectionsMap_idealQuotientπ_eq [IsAdicComplete I A]
    (t : ∀ n, (idealQuotient (baseRingHom A B hA X.1 X.2) F (I ^ n)).sections)
    (ht : ∀ (m n : ℕ) (hmn : m ≤ n), SheafOfModules.sectionsMap
        (idealQuotientMap (baseRingHom A B hA X.1 X.2) F (Ideal.pow_le_pow_right hmn)) (t n) =
      t m) :
    ∃ s : F.sections, ∀ n, SheafOfModules.sectionsMap
        (idealQuotientπ (baseRingHom A B hA X.1 X.2) F (I ^ n)) s = t n := by
  have hb := (bijective_cohomologyToIdealQuotientLimit f hf F I 0).2
  obtain ⟨y, hy⟩ := hb ⟨fun n => (spaceCohomologyZeroEquiv X _).symm (t n), fun m n hmn =>
    (spaceCohomologyZeroEquiv_symm_sectionsMap X _ _).symm.trans (congrArg _ (ht m n hmn))⟩
  let y' : (spaceCohomology B (Spec (.of A)) hA X 0).obj F := y
  refine ⟨spaceCohomologyZeroEquiv X F y', fun n => ?_⟩
  have h1 := congrArg (fun z : cohomologyIdealQuotientLimit (baseRingHom A B hA X.1 X.2) F I 0 =>
    (z : ∀ k, cohomologyIdealQuotient (baseRingHom A B hA X.1 X.2) F I 0 k) n) hy
  change ((spaceCohomology B (Spec (.of A)) hA X 0).map
      (idealQuotientπ (baseRingHom A B hA X.1 X.2) F (I ^ n))).hom y' =
    (spaceCohomologyZeroEquiv X _).symm (t n) at h1
  refine (spaceCohomologyZeroEquiv X _).symm.injective ?_
  rw [spaceCohomologyZeroEquiv_symm_sectionsMap X, Equiv.symm_apply_apply, h1]

end Situation

end AlgebraicGeometry.Space.C1573

end
