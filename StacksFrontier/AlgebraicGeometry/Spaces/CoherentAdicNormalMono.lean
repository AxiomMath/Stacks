module

public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicCokernel

/-!
# Levelwise injective morphisms of coherent adic systems are kernels

Let `F` be an algebraic space over a scheme `S` and let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its
small étale ringed site.  A morphism of the category `Coh(F, 𝓘)` of coherent adic systems which
is injective at every level is the kernel of the projection onto its cokernel.

## Main definitions

* `AlgebraicGeometry.Space.normalMonoOfMonoApp` — a levelwise injective morphism of coherent
  adic systems, presented as a kernel.

## Main results

* `AlgebraicGeometry.Space.mono_of_mono_app` — a levelwise injective morphism of coherent adic
  systems is a monomorphism of `Coh(F, 𝓘)`.
* `AlgebraicGeometry.Space.exists_lift_of_mono_app` — the lifting property of a levelwise
  injective morphism against its own cokernel.
* `AlgebraicGeometry.Space.isNormalMonoCategory_of_mono_app` — if every monomorphism of
  `Coh(F, 𝓘)` is injective level by level, then every monomorphism of `Coh(F, 𝓘)` is a kernel.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

section NormalMono

variable {E E' : CoherentAdicSystems B S hS F hF 𝓘} (f : E ⟶ E')

/-- A morphism of coherent adic systems which is injective at every level is a
monomorphism. -/
theorem mono_of_mono_app (h : ∀ n : ℕᵒᵖ, Mono (f.hom.app n)) : Mono f :=
  (ObjectProperty.ι _).mono_of_mono_map (NatTrans.mono_of_mono_app f.hom)

/-- **The lifting property of a levelwise injective morphism of coherent adic systems against
its own cokernel.**  A morphism into the target which becomes zero in the cokernel factors
through `f`. -/
theorem exists_lift_of_mono_app (h : ∀ n : ℕᵒᵖ, Mono (f.hom.app n))
    {K : CoherentAdicSystems B S hS F hF 𝓘} (k : K ⟶ E')
    (hk : k ≫ coherentAdicCokernelπ B S hS F hF 𝓘 f = 0) :
    ∃ l : K ⟶ E, l ≫ f = k := by
  have hk' : ∀ n : ℕᵒᵖ, k.hom.app n ≫ (cokernel.π f.hom).app n = 0 := fun n =>
    congrArg (fun t : K ⟶ coherentAdicCokernel B S hS F hF 𝓘 f => t.hom.app n) hk
  have hkn : ∀ n : ℕᵒᵖ, k.hom.app n ≫ cokernel.π (f.hom.app n) = 0 := by
    intro n
    rw [← app_comp_cokernelObjIso_hom B S hS F hF f.hom n, ← Category.assoc, hk' n, zero_comp]
  refine ⟨ObjectProperty.homMk
    { app := fun n => Abelian.monoLift (f.hom.app n) (k.hom.app n) (hkn n)
      naturality := fun m n g => ?_ }, ?_⟩
  · refine (cancel_mono (f.hom.app n)).mp ?_
    rw [Category.assoc, Abelian.monoLift_comp, Category.assoc, f.hom.naturality,
      ← Category.assoc, Abelian.monoLift_comp, k.hom.naturality]
  · refine ObjectProperty.hom_ext (IsCoherentAdicSystem B S hS F hF 𝓘) (NatTrans.ext ?_)
    funext n
    exact Abelian.monoLift_comp (f.hom.app n) (k.hom.app n) (hkn n)

/-- **A levelwise injective morphism of coherent adic systems is a kernel**, namely the kernel
of the projection onto its levelwise cokernel. -/
@[instance_reducible]
def normalMonoOfMonoApp (h : ∀ n : ℕᵒᵖ, Mono (f.hom.app n)) : NormalMono f where
  Z := coherentAdicCokernel B S hS F hF 𝓘 f
  g := coherentAdicCokernelπ B S hS F hF 𝓘 f
  w := comp_coherentAdicCokernelπ B S hS F hF 𝓘 f
  isLimit :=
    haveI : Mono f := mono_of_mono_app B S hS F hF 𝓘 f h
    KernelFork.IsLimit.ofι' _ _ fun {_} c hc =>
      ⟨(exists_lift_of_mono_app B S hS F hF 𝓘 f h c hc).choose,
        (exists_lift_of_mono_app B S hS F hF 𝓘 f h c hc).choose_spec⟩

end NormalMono

/-- **If every monomorphism of `Coh(F, 𝓘)` is injective level by level, then every monomorphism
of `Coh(F, 𝓘)` is a kernel.** -/
theorem isNormalMonoCategory_of_mono_app
    (h : ∀ {E E' : CoherentAdicSystems B S hS F hF 𝓘} (f : E ⟶ E'), Mono f →
      ∀ n : ℕᵒᵖ, Mono (f.hom.app n)) :
    IsNormalMonoCategory (CoherentAdicSystems B S hS F hF 𝓘) where
  normalMonoOfMono f _ := ⟨normalMonoOfMonoApp B S hS F hF 𝓘 f (h f inferInstance)⟩

end AlgebraicGeometry.Space

end
