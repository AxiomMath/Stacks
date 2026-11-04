module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.SectionUniverseLift

/-!
# Cohomology of an algebraic space in the universe of its structure sheaf

Let `X` be an algebraic space over `Spec A`, for a scheme in `Type u`. For an `𝒪_X`-module `M`
with sections in `Type u`, the universe of the structure sheaf, the cohomology over the base ring
(`AlgebraicGeometry.Space.cohomologyOverBase`) of its universe lift `M↑` is the universe lift of
the right derived functors of `Stacks.Cohomology.SiteModules.globalSectionsFunctor` at `M`:
`Hⁱ(X, M↑) ≅ Hⁱ(X, M)↑` as `A`-modules.

As an application, the additivity of the twisted Euler characteristics along a short exact
sequence of coherent modules on a proper algebraic space over a field (Stacks 0DN2 for the
twists) follows from the statements of Stacks 08AS and Stacks 072C in the universe of the
structure sheaf.

## Main results

* `AlgebraicGeometry.Space.hasSeparator_modules`: the `𝒪_X`-modules with sections in the
  universe of the structure sheaf have a separator.
* `AlgebraicGeometry.Space.cohomologyOverBaseUliftIso`: **`Hⁱ(X, M↑) ≅ Hⁱ(X, M)↑`** over the base
  ring.
* `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_uliftForPresentation_iff` and
  `AlgebraicGeometry.Space.isZero_cohomologyOverBase_uliftForPresentation_iff`: finiteness over
  the base ring and vanishing of the cohomology may be read in either universe.
* `AlgebraicGeometry.Space.hasAdditiveTwistedEuler_of_shortExact_of_moduleFinite_of_exists_isZero`:
  additivity of the twisted Euler characteristics, from finiteness of the cohomology of coherent
  modules and a uniform vanishing degree for the cohomology of quasi-coherent modules, both in the
  universe of the structure sheaf.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 0DN2](https://stacks.math.columbia.edu/tag/0DN2)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Stacks.Cohomology.SiteModules

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

section Instances

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The `𝒪_F`-modules on the small étale ringed site of an algebraic space, at the universe of
the structure rings, have a separator. -/
alias hasSeparator_modules := hasSeparator_modules_ringUniverse

end Instances

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

attribute [local instance] enoughInjectives_modules

/-- **Cohomology over the base ring of the universe lift of a module is the universe lift of
its cohomology.**  For an `𝒪_X`-module `M` with sections in the universe `u` of the structure
sheaf, `AlgebraicGeometry.Space.cohomologyOverBase` of its universe lift is, as an `A`-module,
the universe lift of the `i`-th right derived functor of global sections at `M`, with scalars
restricted along `AlgebraicGeometry.Space.baseRingHom`. -/
def cohomologyOverBaseUliftIso (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (i : ℕ) :
    cohomologyOverBase.{u, w} A B hA X hX
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M) i ≅
      (ModuleCat.uliftFunctor.{max (u + 1) w} A).obj
        ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M)) := by
  have := hasSeparator_modules B (Spec (.of A)) hA X hX
  have := site_hasSheafify_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J)
  have := moduleSheavesEnoughInjectives.{u + 1, u, u, w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
  exact (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).mapIso
    ((rightDerivedGlobalSectionsUliftIso.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
        i).app M).symm

/-- Finiteness over the base ring of the cohomology of the universe lift of a module is
finiteness of the cohomology of the module. -/
theorem moduleFinite_cohomologyOverBase_uliftForPresentation_iff
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (i : ℕ) :
    Module.Finite A (cohomologyOverBase.{u, w} A B hA X hX
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M) i) ↔
      Module.Finite A ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M)) := by
  rw [Module.Finite.equiv_iff (cohomologyOverBaseUliftIso.{u, w} A B hA X hX M i).toLinearEquiv]
  let N := (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
    (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M)
  let e : ((ModuleCat.uliftFunctor.{max (u + 1) w} A).obj N) ≃ₗ[A] N := ULift.moduleEquiv
  exact ⟨fun _ ↦ Module.Finite.equiv e, fun _ ↦ Module.Finite.equiv e.symm⟩

/-- Vanishing of the cohomology of the universe lift of a module is vanishing of the cohomology
of the module. -/
theorem isZero_cohomologyOverBase_uliftForPresentation_iff
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (i : ℕ) :
    IsZero (cohomologyOverBase.{u, w} A B hA X hX
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M) i) ↔
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M) := by
  rw [Iso.isZero_iff (cohomologyOverBaseUliftIso.{u, w} A B hA X hX M i),
    ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  let N := ((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M
  let e : ULift.{max (u + 1) w} N ≃ N := Equiv.ulift
  exact ⟨fun h ↦ @Equiv.subsingleton _ _ e.symm h, fun h ↦ @Equiv.subsingleton _ _ e h⟩

section Euler

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk)

/-- **Additivity of the twisted Euler characteristics, from the finiteness and the uniform
vanishing of cohomology.**  Let `0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of
`𝒪_X`-modules on a proper algebraic space over a field `k`, with `F₁` and `F₃` coherent, and
`L₁, …, L_r` invertible modules. Suppose that

* every coherent `𝒪_X`-module has cohomology of finite dimension over `k` in every degree
  (`hfin`, the statement of Stacks 08AS for `X ⟶ Spec k`), and
* there is a degree beyond which the cohomology of every quasi-coherent `𝒪_X`-module vanishes
  (`hvan`, the statement of Stacks 072C for `X`),

both for the cohomology of modules in the universe of the structure sheaf. Then
`χ(X, F₂ ⊗ L^{⊗ n}) = χ(X, F₁ ⊗ L^{⊗ n}) + χ(X, F₃ ⊗ L^{⊗ n})` for every integral tuple `n`. -/
theorem hasAdditiveTwistedEuler_of_shortExact_of_moduleFinite_of_exists_isZero {r : ℕ}
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    {Sc : ShortComplex (Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)} (hSc : Sc.ShortExact)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₁ L n)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₂ L n)]
    [∀ n : Fin r → ℤ, IsCoherent B (Spec (.of k)) hk X.1 X.2
      (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2 Sc.X₃ L n)]
    [hc₁ : IsCoherent B (Spec (.of k)) hk X.1 X.2 Sc.X₁]
    [hc₃ : IsCoherent B (Spec (.of k)) hk X.1 X.2 Sc.X₃]
    (hfin : ∀ (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
      [IsCoherent B (Spec (.of k)) hk X.1 X.2 F] (i : ℕ),
      Module.Finite k ((ModuleCat.restrictScalars (baseRingHom k B hk X.1 X.2)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).rightDerived i).obj F)))
    (hvan : ∃ N : ℕ, ∀ F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2,
      F.IsQuasicoherentOnSite → ∀ q, N ≤ q →
        IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).rightDerived q).obj F)) :
    HasAdditiveTwistedEuler.{u, w} k B hk X f hf Sc.X₁ Sc.X₂ Sc.X₃ L := by
  obtain ⟨N, hN⟩ := hvan
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf⟩
  have := fun n ↦ isCoherent_twistedModule B (Spec (.of k)) hk X.1 X.2 Sc.X₁ L n hc₁
  have := fun n ↦ isCoherent_twistedModule B (Spec (.of k)) hk X.1 X.2 Sc.X₃ L n hc₃
  refine hasAdditiveTwistedEuler_of_shortExact.{u, w} k B hk X f hf hSc L (fun _ ↦ N)
    (fun n i _ ↦ ?_) (fun n i _ ↦ ?_) (fun n i hi ↦ ?_) (fun n i hi ↦ ?_)
  iterate 2 exact (moduleFinite_cohomologyOverBase_uliftForPresentation_iff.{u, w}
    k B hk X.1 X.2 _ i).2 (hfin _ i)
  iterate 2 exact (isZero_cohomologyOverBase_uliftForPresentation_iff.{u, w}
    k B hk X.1 X.2 _ i).2 (hN _ inferInstance i hi)

end Euler

end AlgebraicGeometry.Space
