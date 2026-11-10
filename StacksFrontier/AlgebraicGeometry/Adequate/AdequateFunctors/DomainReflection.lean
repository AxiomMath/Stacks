module

public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseShortExact
public import StacksFrontier.Algebra.Module.Adequate.FiniteTypeDetection
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainRestriction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.Biproducts

/-!
# Restriction to a domain of algebras reflects isomorphisms of adequate functors

A module-valued functor on the commutative `A`-algebras may be restricted to any chosen domain
of algebras, `AdequateFunctor.restrictDomain`. For a general functor this throws information
away; for an **adequate** one it throws nothing away, provided the domain contains the
`A`-algebras of finite type — because an adequate functor is determined there by the joining
argument of [Stacks, Tag 06UU], `Stacks.Adequate.exists_preimage_of_finiteType`.

Consequently the restriction functor, composed with the inclusion of the adequate module-valued
functors, is exact and **reflects isomorphisms**.

## Main results

* `AdequateFunctor.isIso_of_isIso_restriction` — **a morphism of adequate module-valued functors
  which is an isomorphism over every algebra of the domain is an isomorphism.**
* `AdequateFunctor.reflectsIsomorphisms_adequateι_comp_restriction` — the same statement as a
  property of the functor on the abelian category of adequate functors.
* `AdequateFunctor.preservesFiniteLimits_restriction`,
  `AdequateFunctor.preservesFiniteColimits_restriction` — restriction is exact, kernels and
  cokernels of module-valued functors being computed algebra by algebra.
* `AdequateFunctor.preservesFiniteLimits_adequateι`,
  `AdequateFunctor.preservesFiniteColimits_adequateι` — so is the inclusion of the adequate
  functors, adequacy being closed under kernels and cokernels.
* `AdequateFunctor.preservesHomology_adequateι`,
  `AdequateFunctor.preservesHomology_adequateι_comp_restriction` — the inclusion, and the
  inclusion followed by restriction, preserve homology.

## References

* [Stacks Project, Tag 06UU](https://stacks.math.columbia.edu/tag/06UU)
* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

universe u u₁ v₁

namespace AdequateFunctor

section Reflection

variable {A : Type u} [CommRing A] {D : Type u₁} [Category.{v₁} D]
  (ι : D ⥤ CommAlgCat.{u} A)

/-- The components of a restricted morphism of module-valued functors are components of the
original, at the algebras of the domain. -/
public theorem pushforward₀_map_app
    {F G : ModuleValuedFunctor.{u, u} A} (φ : F ⟶ G) (X : D) :
    ((PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{u} A)).map φ).app
        (op (op X)) =
      φ.app (op (op (ι.obj X))) := rfl

/-- Exactness at `G` of `F ⟶ G ⟶ H` over the algebras of the domain propagates to every
`A`-algebra, for adequate `G` and `H`, provided the domain contains every finite-type algebra. -/
private theorem exists_preimage_of_domain
    (hft : ∀ C : CommAlgCat.{u} A, Algebra.FiniteType A ↥C → ∃ X : D, ι.obj X = C)
    {F G H : ModuleValuedFunctor.{u, u} A}
    (hG : IsAdequate (𝟭 _) G) (hH : IsAdequate (𝟭 _) H) (α : F ⟶ G) (β : G ⟶ H)
    (h : ∀ (X : D) (w : G.obj (op (op (ι.obj X)))), β.app (op (op (ι.obj X))) w = 0 →
      ∃ v : F.obj (op (op (ι.obj X))), α.app (op (op (ι.obj X))) v = w)
    (R : CommAlgCat.{u} A) (y : G.obj (op (op R))) (hy : β.app (op (op R)) y = 0) :
    ∃ x : F.obj (op (op R)), α.app (op (op R)) x = y :=
  Stacks.Adequate.exists_preimage_of_finiteType R hG hH α β
    (fun C hC w hw => by
      obtain ⟨X, rfl⟩ := hft C hC
      exact h X w hw) y hy

/-- **A morphism of adequate module-valued functors which is an isomorphism over every algebra
of the domain is an isomorphism**, provided the domain contains every `A`-algebra of finite
type. -/
public theorem isIso_of_isIso_restriction
    (hft : ∀ C : CommAlgCat.{u} A, Algebra.FiniteType A ↥C → ∃ X : D, ι.obj X = C)
    {F G : ModuleValuedFunctor.{u, u} A}
    (hF : IsAdequate (𝟭 _) F) (hG : IsAdequate (𝟭 _) G) (φ : F ⟶ G)
    (hφ : IsIso ((PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{u} A)).map φ)) :
    IsIso φ := by
  have hdom : ∀ X : D, Function.Bijective (φ.app (op (op (ι.obj X)))) := by
    intro X
    have h : IsIso (((PresheafOfModules.pushforward₀ ι.op
        (algebraRingDiagram.{u} A)).map φ).app (op (op X))) :=
      inferInstanceAs (IsIso ((PresheafOfModules.evaluation
        (algebraRingDiagramOn.{u} ι) (op (op X))).map
          ((PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{u} A)).map φ)))
    rw [pushforward₀_map_app ι φ X] at h
    exact (ConcreteCategory.isIso_iff_bijective (φ.app (op (op (ι.obj X))))).mp h
  have hzero : IsAdequate (𝟭 (CommAlgCat.{u} A))
      (0 : ModuleValuedFunctor.{u, u} A) :=
    isAdequate_of_isZero (𝟭 _) (isZero_zero _)
  have hinj : ∀ (R : CommAlgCat.{u} A) (w : F.obj (op (op R))),
      φ.app (op (op R)) w = 0 → w = 0 := by
    intro R w hw
    obtain ⟨v, hv⟩ := exists_preimage_of_domain ι hft
      (F := (0 : ModuleValuedFunctor.{u, u} A)) hF hG 0 φ
      (fun X w' hw' => ⟨0, by simp [(hdom X).1 (hw'.trans (map_zero _).symm)]⟩) R w hw
    simpa using hv.symm
  have hsurj : ∀ (R : CommAlgCat.{u} A) (y : G.obj (op (op R))),
      ∃ x : F.obj (op (op R)), φ.app (op (op R)) x = y := fun R y =>
    exists_preimage_of_domain ι hft
      (H := (0 : ModuleValuedFunctor.{u, u} A)) hG hzero φ 0
      (fun X w' _ => (hdom X).2 w') R y (by simp)
  refine (PresheafOfModules.jointlyFaithful_evaluation.jointlyReflectsIsomorphisms.isIso_iff
    φ).mpr fun Y =>
    (ConcreteCategory.isIso_iff_bijective
      ((PresheafOfModules.evaluation (algebraRingDiagram.{u} A) Y).map φ)).mpr
        ⟨fun a b hab => sub_eq_zero.mp (hinj _ (a - b)
          ((map_sub (φ.app Y).hom a b).trans (sub_eq_zero.mpr hab))), hsurj Y.unop.unop⟩

/-! ### Exactness of the two functors -/

/-- Restriction of module-valued functors from all `A`-algebras to the domain `ι`. -/
private abbrev restriction :
    ModuleValuedFunctor.{u, u} A ⥤ ModuleValuedFunctorOn.{u} ι :=
  PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{u} A)

/-- Restriction to a domain of algebras preserves limits of any shape that abelian groups
admit. -/
private theorem preservesLimitsOfShape_restriction (J : Type) [SmallCategory J]
    [HasLimitsOfShape J AddCommGrpCat.{u}] :
    PreservesLimitsOfShape J (restriction ι) where
  preservesLimit {E} := ⟨fun {c} hc =>
    ⟨PresheafOfModules.evaluationJointlyReflectsLimits (E ⋙ restriction ι)
      ((restriction ι).mapCone c) fun X =>
        (show IsLimit ((restriction ι ⋙
            PresheafOfModules.evaluation (algebraRingDiagramOn.{u} ι) X).mapCone c) from
          isLimitOfPreserves (PresheafOfModules.evaluation (algebraRingDiagram.{u} A)
            (ι.op.op.obj X)) hc).ofIsoLimit (Functor.mapConeMapCone c).symm⟩⟩

/-- Restriction to a domain of algebras is left exact. -/
public theorem preservesFiniteLimits_restriction :
    PreservesFiniteLimits
      (PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{u} A) :
        ModuleValuedFunctor.{u, u} A ⥤ ModuleValuedFunctorOn.{u} ι) :=
  ⟨fun J _ _ => preservesLimitsOfShape_restriction ι J⟩

/-- Restriction to a domain of algebras is right exact. -/
public theorem preservesFiniteColimits_restriction :
    PreservesFiniteColimits
      (PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{u} A) :
        ModuleValuedFunctor.{u, u} A ⥤ ModuleValuedFunctorOn.{u} ι) :=
  ⟨fun J _ _ => pushforward₀_preservesColimitsOfShape.{u, u} ι.op
    (algebraRingDiagram.{u} A) J⟩

/-- The inclusion of the adequate module-valued functors is left exact. -/
public theorem preservesFiniteLimits_adequateι :
    PreservesFiniteLimits (adequate.{u, u, u} A).ι :=
  have := (adequate.{u, u, u} A).preservesKernels_ι
  Functor.preservesFiniteLimits_of_preservesKernels _

set_option synthInstance.maxHeartbeats 200000 in
-- instance synthesis for finite-colimit preservation of the adequate inclusion functor
/-- The inclusion of the adequate module-valued functors is right exact. -/
public theorem preservesFiniteColimits_adequateι :
    PreservesFiniteColimits (adequate.{u, u, u} A).ι :=
  have := (adequate.{u, u, u} A).preservesCokernels_ι
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- The inclusion of the adequate module-valued functors preserves homology. -/
public theorem preservesHomology_adequateι :
    (adequate.{u, u, u} A).ι.PreservesHomology :=
  let := preservesFiniteLimits_adequateι.{u} (A := A)
  let := preservesFiniteColimits_adequateι.{u} (A := A)
  { preservesKernels _ := inferInstance
    preservesCokernels _ := inferInstance }

/-- The inclusion of the adequate module-valued functors followed by restriction to a domain of
algebras preserves homology. -/
public theorem preservesHomology_adequateι_comp_restriction :
    ((adequate.{u, u, u} A).ι ⋙
      PresheafOfModules.pushforward₀ ι.op
        (algebraRingDiagram.{u} A)).PreservesHomology :=
  let := preservesFiniteLimits_adequateι.{u} (A := A)
  let := preservesFiniteColimits_adequateι.{u} (A := A)
  let := preservesFiniteLimits_restriction.{u} ι
  let := preservesFiniteColimits_restriction.{u} ι
  let : PreservesFiniteLimits ((adequate.{u, u, u} A).ι ⋙
      PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{u} A)) :=
    comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits ((adequate.{u, u, u} A).ι ⋙
      PresheafOfModules.pushforward₀ ι.op (algebraRingDiagram.{u} A)) :=
    comp_preservesFiniteColimits _ _
  { preservesKernels _ := inferInstance
    preservesCokernels _ := inferInstance }

/-- The inclusion of the adequate module-valued functors followed by restriction to a domain of
algebras containing every `A`-algebra of finite type reflects isomorphisms. -/
public theorem reflectsIsomorphisms_adequateι_comp_restriction
    (hft : ∀ C : CommAlgCat.{u} A, Algebra.FiniteType A ↥C → ∃ X : D, ι.obj X = C) :
    ((adequate.{u, u, u} A).ι ⋙
      PresheafOfModules.pushforward₀ ι.op
        (algebraRingDiagram.{u} A)).ReflectsIsomorphisms := by
  let : (adequate.{u, u, u} A).ι.ReflectsIsomorphisms :=
    (adequate.{u, u, u} A).fullyFaithfulι.reflectsIsomorphisms
  refine ⟨fun {X Y} f hf => ?_⟩
  have : IsIso ((adequate.{u, u, u} A).ι.map f) :=
    isIso_of_isIso_restriction ι hft X.property Y.property _ hf
  exact isIso_of_reflects_iso f (adequate.{u, u, u} A).ι

end Reflection

end AdequateFunctor

end
