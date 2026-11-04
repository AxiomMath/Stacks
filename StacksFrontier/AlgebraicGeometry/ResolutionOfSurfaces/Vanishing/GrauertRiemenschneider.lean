module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.Reduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.Basic
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Grauert-Riemenschneider vanishing for a normal surface singularity

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `(A, 𝔪, κ)` and a modification `f : X ⟶ S = Spec(A)` — let `X` be normal and let `A` be
Nagata with a dualizing complex `ω_A^•`. Writing `ω_X` for the dualizing module of `X`
([Stacks, Tag 0B4R]), [Stacks, Tag 0AXD] asserts `R¹f_*ω_X = 0`.

## Main definitions

* `AlgebraicGeometry.firstCohomologySheafAsBaseModule` is `H¹(X, ℱ)` for a sheaf of modules `ℱ`
  on `X`, regarded as a module over the base ring of a morphism `X ⟶ Spec A`.

## Main results

* `IsLocalRing.subsingleton_of_forall_linearMap_residueField_eq_zero`: a finite module over a
  local ring carrying no nonzero linear map to the residue field is zero.
* `AlgebraicGeometry.firstCohomologySheafAsBaseModule_unit`: at the structure sheaf the
  definition above is `AlgebraicGeometry.firstCohomologyAsBaseModule`.
* `AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_dualizingModule`:
  [Stacks, Tag 0AXD], the Grauert-Riemenschneider vanishing.

## What is granted, and what is not

The conclusion is read over the affine base: for a quasi-compact quasi-separated morphism to
`Spec(A)` and a quasi-coherent module, `R¹f_*ℱ` is the quasi-coherent module on `Spec(A)`
attached to the `A`-module `H¹(X, ℱ)` ([Stacks, Tag 01XJ]), so the vanishing of `R¹f_*ω_X` is
the vanishing of `H¹(X, ω_X)` as an `A`-module. That is also the spelling in which the first
cohomology of a modification already occurs in this library, as
`AlgebraicGeometry.firstCohomologyAsBaseModule` for the structure sheaf.

Two inputs of the source's proof are hypotheses, and both are named in the tag rider.

**Finiteness of `H¹(X, ω_X)` over `A`**, the hypothesis `hfin`. The source uses it in the
sentence *if the proposition is false, then we can find a nonzero map `R¹f_*ω_X → κ`*: a module
admits a nonzero map to the residue field of a local ring as soon as it is finite and nonzero,
and `H¹(X, ω_X)` is finite because `ω_X` is coherent and `f` is proper ([Stacks, Tag 02O5]).

**The duality step**, the hypothesis `hvanish`. The source dualizes a nonzero
`α : Rf_*ω_X^• → κ[1]` by `RHom_A(-, ω_A^•)` into a nonzero `β : κ[-1] → Rf_*𝒪_X`, which is
zero by [Stacks, Tag 0AXC]. The two computations making the dualization work are
`RHom_A(κ[1], ω_A^•) = κ[-1]`, because `ω_A^•` is normalized ([Stacks, Tag 0A7M]), and
`RHom_A(Rf_*ω_X^•, ω_A^•) = Rf_*RHom_{𝒪_X}(ω_X^•, ω_X^•) = Rf_*𝒪_X`, because
`ω_X^• = f^!ω_A^•` is a dualizing complex on `X` ([Stacks, Tags 0GEW, 0AA3]); and `α` is
obtained from a map `R¹f_*ω_X → κ` because `ω_X^• = ω_X[2]`, which holds since a Noetherian
normal two-dimensional scheme is Cohen-Macaulay ([Stacks, Tags 0B3D, 0AWT, 0AWI]). None of
`Rf_*`, `f^!` or `RHom_A(-, ω_A^•)` is available at this point in the library, so the outcome
of that step is carried instead: `hvanish` says every `A`-linear map `H¹(X, ω_X) → κ` is zero.

What is proved is the passage from those two to the conclusion, which is Nakayama's lemma: a
finite module over a local ring with no nonzero linear map to the residue field vanishes. The
source's remaining hypotheses — that `A` is Nagata and carries a dualizing complex, and that
`ω_X` is a dualizing module — are kept, as they enter the source's proof only through the
duality step.

`ω_X` is the dualizing module of `X` in the sense of [Stacks, Tag 0B4R], a coherent module some
shift of which is a dualizing complex. The source's further convention, that `ω_X` is
*normalized* with respect to `ω_A` — that `ω_X[2]` is `f^!` of the normalization of `ω_A^•` — is
not expressible without `f^!`, and it too is used by the source only inside the duality step, so
it is subsumed in `hvanish` and is not a separate hypothesis. Without it the conclusion would be
false for a general dualizing module, since the dualizing modules on `X` differ by tensoring
with an invertible module.

## Implementation notes

`firstCohomologySheafAsBaseModule` is `AlgebraicGeometry.firstCohomologyAsBaseModule` with the
structure sheaf replaced by an arbitrary sheaf of modules: cohomology is the first right derived
functor of global sections on sheaves of modules, and its natural module structure over
`Γ(X, 𝒪_X)` is restricted along the canonical map `A ⟶ Γ(X, 𝒪_X)` induced by `X ⟶ Spec A`.

The Nakayama step is run through the reduction `κ ⊗_A M`, for which Mathlib already has
`IsLocalRing.subsingleton_tensorProduct`: a `κ`-linear functional on `κ ⊗_A M` restricts along
`m ↦ 1 ⊗ m` to an `A`-linear map `M → κ`, and the elements `c ⊗ m = c • (1 ⊗ m)` span, so the
hypothesis kills every functional and a vector space with no nonzero functional is zero.

Local Noetherianness of `X`, which is what makes `Stacks.Duality.IsDualizingModule` available on
it, is an instance hypothesis rather than an instance of the vanishing situation, as it is in
`AlgebraicGeometry.RationalSingularitySituation.bijective_trace`; a client discharges it with
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian V.f`, the morphism being proper.

## References

* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0B3D](https://stacks.math.columbia.edu/tag/0B3D)
* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace IsLocalRing

/-- A finite module over a local ring admitting no nonzero linear map to the residue field is
zero.

This is Nakayama's lemma: the reduction `κ ⊗_A M` is a `κ`-vector space whose functionals
restrict to `A`-linear maps `M → κ` along `m ↦ 1 ⊗ m`, so it has no nonzero functional and
therefore vanishes, and a finite module whose reduction vanishes is zero. -/
@[ega "IV 2.5.5.4" "more general"]
theorem subsingleton_of_forall_linearMap_residueField_eq_zero (A : Type u) [CommRing A]
    [IsLocalRing A] (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (h : ∀ φ : M →ₗ[A] ResidueField A, φ = 0) : Subsingleton M := by
  rw [← IsLocalRing.subsingleton_tensorProduct (R := A) (M := M)]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  refine (Module.forall_dual_apply_eq_zero_iff (ResidueField A) x).mp fun φ => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c m =>
      have hsmul : (c ⊗ₜ[A] m : TensorProduct A (ResidueField A) M) = c • (1 ⊗ₜ[A] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have h0 : φ (1 ⊗ₜ[A] m) = 0 :=
        LinearMap.congr_fun
          (h ((φ.restrictScalars A).comp (TensorProduct.mk A (ResidueField A) M 1))) m
      rw [hsmul, map_smul, h0, smul_zero]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

end IsLocalRing

namespace AlgebraicGeometry

/-- The first cohomology of a sheaf of modules on `X`, regarded as an `A`-module via the
morphism `X ⟶ Spec A`. -/
def firstCohomologySheafAsBaseModule {A : Type u} [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) (ℱ : X.Modules) : ModuleCat.{u} A :=
  letI : (SheafOfModules.evaluation X.ringCatSheaf (.op ⊤)).Additive := {}
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
    (((SheafOfModules.evaluation X.ringCatSheaf (.op ⊤)).rightDerived 1).obj ℱ)

/-- At the structure sheaf the construction above is
`AlgebraicGeometry.firstCohomologyAsBaseModule`. -/
theorem firstCohomologySheafAsBaseModule_unit {A : Type u} [CommRing A] (X : Scheme.{u})
    (f : X ⟶ Spec (.of A)) :
    firstCohomologySheafAsBaseModule X f (SheafOfModules.unit X.ringCatSheaf) =
      firstCohomologyAsBaseModule X f :=
  rfl

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-- **Stacks Project, Tag 0AXD** (Grauert-Riemenschneider). In the vanishing situation of
[Stacks, Tag 0AX8] with `X` normal and `A` Nagata carrying a dualizing complex `ω_A^•`, the
first cohomology of the dualizing module `ω_X` of `X` vanishes; over the affine base
`S = Spec(A)` this is `R¹f_*ω_X = 0`.

The two hypotheses carried from the source's proof are `hfin`, the finiteness of `H¹(X, ω_X)`
over `A`, which comes from coherence of the higher direct images under the proper morphism `f`
([Stacks, Tag 02O5]) and is what lets a nonzero module be detected by a map to `κ`; and
`hvanish`, the outcome of the source's duality step, in which a nonzero `R¹f_*ω_X → κ` is
dualized by `RHom_A(-, ω_A^•)` into a nonzero `κ[-1] → Rf_*𝒪_X` and contradicts
[Stacks, Tag 0AXC]. The normalization of `ω_X` with respect to `ω_A` is used by the source only
inside that step and is subsumed in `hvanish`. -/
@[stacks 0AXD "the conclusion R^1 f_* omega_X = 0 read over the affine base S = Spec(A) as \
the vanishing of H^1(X, omega_X) as an A-module (Tag 01XJ), granted two inputs of the \
source's proof as named hypotheses: hfin, the finiteness of H^1(X, omega_X) over A, which is \
coherence of the higher direct image of a coherent module under a proper morphism (Tag 02O5) \
and is used by the source where it produces a nonzero map R^1 f_* omega_X -> kappa; and \
hvanish, the source's duality step, in which RHom_A(-, omega_A^bullet) carries a nonzero \
alpha : Rf_* omega_X^bullet -> kappa[1] to a nonzero beta : kappa[-1] -> Rf_* O_X and \
contradicts Tag 0AXC, using RHom_A(kappa[1], omega_A^bullet) = kappa[-1] for a normalized \
omega_A^bullet (Tag 0A7M), RHom_A(Rf_* omega_X^bullet, omega_A^bullet) = Rf_* O_X (Tags 0GEW, \
0AA3) and omega_X^bullet = omega_X[2] (Tags 0B3D, 0AWT, 0AWI), carried as the vanishing of \
every A-linear map H^1(X, omega_X) -> kappa, which also subsumes the source's normalization of \
omega_X with respect to omega_A (Tag 0B4R), not expressible without f^!; what is proved is the \
passage from those two to the conclusion, by Nakayama"]
theorem isZero_firstCohomology_dualizingModule [IsNormal V.X] [IsLocallyNoetherian V.X]
    (hnag : IsNagataRing V.A)
    (ωA : DerivedCategory (ModuleCat.{u} V.A)) (hωA : Dualizing.IsDualizingComplex ωA)
    (ω : V.X.Modules) (hω : Stacks.Duality.IsDualizingModule ω)
    (hfin : Module.Finite V.A (firstCohomologySheafAsBaseModule V.X V.f ω))
    (hvanish : ∀ φ : firstCohomologySheafAsBaseModule V.X V.f ω →ₗ[V.A]
      IsLocalRing.ResidueField V.A, φ = 0) :
    IsZero (firstCohomologySheafAsBaseModule V.X V.f ω) := by
  -- `A` Nagata with a dualizing complex, and `ω` dualizing, are the source's hypotheses; they
  -- enter its proof only through the duality step, which is `hvanish`.
  have : IsNagataRing V.A := hnag
  have : Dualizing.IsDualizingComplex ωA := hωA
  have : Stacks.Duality.IsDualizingModule ω := hω
  -- Finiteness is what lets a nonzero module be detected by a map to the residue field.
  have := hfin
  have : Subsingleton (firstCohomologySheafAsBaseModule V.X V.f ω) :=
    IsLocalRing.subsingleton_of_forall_linearMap_residueField_eq_zero V.A _ hvanish
  exact ModuleCat.isZero_of_subsingleton _

end VanishingSituation

end AlgebraicGeometry

end
