module

public import StacksFrontier.Topology.Sheaves.Cohomology.SquareZeroExtensionBoundaryDerivation
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DerivedBoundaryCocycle

/-!
# The boundary map of a square-zero extension of sheaves of rings: Stacks 0B8S

Let `X` be a topological space and let `π : O' ⟶ O` be a surjection of sheaves of commutative
rings whose kernel `I` has square zero.  Then `M = H¹(X, I)` is a module over `R = H⁰(X, O)`, and
the boundary map `∂ : R → M` associated to the short exact sequence `0 → I → O' → O → 0` is a
derivation.

`StacksFrontier.Topology.Sheaves.Cohomology.SquareZeroExtensionBoundaryDerivation` constructs the
`R`-module structure on `M` and proves that the boundary map, in the Čech description of
Stacks 02AP, is a derivation.  This file supplies the two remaining identifications the source
makes: that `0 → I → O' → O → 0` is a short exact sequence of abelian sheaves, with `I` the
kernel of `π`, and that the Čech boundary map is the connecting morphism `H⁰(X, O) → H¹(X, I)` of
the long exact cohomology sequence, where `H¹` is the first right derived functor of `Γ(X, -)`.

## Main definitions

* `Stacks.Cohomology.SquareZeroBoundary.addSheaf`: the abelian sheaf underlying a sheaf of
  commutative rings.
* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.ofSurjective`: the kernel of a
  surjection of sheaves of commutative rings with square-zero kernel, as a square-zero kernel.
* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.connecting`: the connecting morphism
  `H⁰(X, O) → H¹(X, I)` of the long exact cohomology sequence of `0 → I → O' → O → 0`.

## Main results

* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.shortExact`: `0 → I → O' → O → 0` is a
  short exact sequence of abelian sheaves.
* `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.boundary_eq_connecting`: the Čech
  boundary map is the connecting morphism of derived-functor cohomology.
* `…SquareZeroKernel.exists_derivation_eq_connecting_of_surjective`: **Stacks 0B8S**.

## Implementation notes

The surjectivity of `π` is its local surjectivity for the topology of open covers, which is
what being an epimorphism of sheaves means.  The square-zero hypothesis says that the product of
two sections of `O'` killed by `π` vanishes.  The connecting morphism is the one the long exact
homology sequence of `D⁺` attaches to the distinguished triangle of `RΓ(X, -)` (Stacks 05TE),
transported to the right derived functors computed by injective resolutions; its comparison with
the Čech description is `Stacks.Cohomology.CechOne.rightDerivedPlusδ_toRightDerivedZero`, and the
two use the same sign convention (the Čech coboundary of the local lifts).

## References

* [Stacks Project, Tag 0B8S](https://stacks.math.columbia.edu/tag/0B8S)
* [Stacks Project, Tag 02AP](https://stacks.math.columbia.edu/tag/02AP)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CechCochains
open Stacks.Cohomology.CechOne Stacks.Cohomology.CechBoundary

universe u

namespace Stacks.Cohomology.SquareZeroBoundary

variable {X : TopCat.{u}}

open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.HigherDirectImagePresheaf (derivedPlusToStandard)

/-- The sheaf of abelian groups underlying a sheaf of commutative rings. -/
noncomputable def addSheaf (F : TopCat.Sheaf CommRingCat.{u} X) : AbelianSheaf X :=
  ⟨addPresheaf.{u, u} F.presheaf,
    Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ RingCat AddCommGrpCat)
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) F.property)⟩

namespace SquareZeroKernel

variable {O' O : TopCat.Sheaf CommRingCat.{u} X} {I : TopCat.Sheaf AddCommGrpCat.{u} X}

/-- The short complex `0 → I → O' → O → 0` of abelian sheaves attached to a square-zero kernel
of a morphism of sheaves of commutative rings. -/
noncomputable def shortComplex (E : SquareZeroKernel.{u, u} O'.presheaf O.presheaf I) :
    ShortComplex (AbelianSheaf X) :=
  ShortComplex.mk (X₁ := I) (X₂ := addSheaf O') (X₃ := addSheaf O)
    (ObjectProperty.homMk E.ι) (ObjectProperty.homMk (addMap E.π)) (by
      ext V x
      exact E.π_ι V.unop x)

/-- **The sequence `0 → I → O' → O → 0` is short exact** in abelian sheaves: `I → O'` is
injective on sections, its image on sections is the kernel of `O' → O`, and `O' → O` is locally
surjective. -/
theorem shortExact (E : SquareZeroKernel.{u, u} O'.presheaf O.presheaf I) :
    E.shortComplex.ShortExact := by
  have : ∀ V : (Opens X)ᵒᵖ, Mono (E.ι.app V) := fun V =>
    (AddCommGrpCat.mono_iff_injective _).2 (E.ι_injective V.unop)
  have hmono : Mono (E.shortComplex.map (sheafToPresheaf _ _)).f :=
    NatTrans.mono_of_mono_app E.ι
  have hP : (E.shortComplex.map (sheafToPresheaf _ _)).Exact := by
    apply ShortComplex.exact_iff_isZero_homology _ |>.mpr
    apply (IsZero.iff_id_eq_zero _).mpr
    apply NatTrans.ext
    funext V
    have hV : (E.shortComplex.map (sheafToPresheaf _ _) |>.map
        ((evaluation _ _).obj V)).Exact :=
      (ShortComplex.ab_exact_iff _).2 fun b hb => E.exists_of_π_eq_zero V.unop b hb
    exact ((((ShortComplex.exact_iff_isZero_homology _).mp hV).of_iso
      ((E.shortComplex.map (sheafToPresheaf _ _)).mapHomologyIso
        ((evaluation _ _).obj V)).symm)).eq_of_src _ _
  have : Sheaf.IsLocallySurjective E.shortComplex.g := E.π_locallySurjective
  exact
    { exact := E.shortComplex.exact_of_f_is_kernel (isLimitOfReflects (sheafToPresheaf _ _)
        ((KernelFork.isLimitMapConeEquiv (KernelFork.ofι E.shortComplex.f E.shortComplex.zero)
          (sheafToPresheaf _ _)).symm hP.fIsKernel))
      mono_f := (sheafToPresheaf _ _).mono_of_mono_map hmono
      epi_g := Sheaf.epi_of_isLocallySurjective _ }

/-- The morphism of abelian sheaves underlying a morphism of sheaves of commutative rings. -/
noncomputable def addSheafMap {F G : TopCat.Sheaf CommRingCat.{u} X} (φ : F ⟶ G) :
    addSheaf F ⟶ addSheaf G :=
  ObjectProperty.homMk (addMap.{u, u} φ.hom)

/-- **The kernel of a surjection of sheaves of commutative rings with square-zero kernel.**
Given a locally surjective morphism `π : O' ⟶ O` of sheaves of commutative rings such that the
product of two sections of `O'` killed by `π` vanishes, the kernel of `π` in abelian sheaves is a
square-zero kernel of `π`. -/
noncomputable def ofSurjective (π : O' ⟶ O)
    (hπ : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) π.hom)
    (hsq : ∀ (V : Opens X) (b b' : ToType (O'.presheaf.obj (op V))),
      π.hom.app (op V) b = 0 → π.hom.app (op V) b' = 0 → b * b' = 0) :
    SquareZeroKernel.{u, u} O'.presheaf O.presheaf (kernel (addSheafMap π)) :=
  have hk (V : Opens X) := (KernelFork.isLimitMapConeEquiv _
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation _ _).obj (op V))) (isLimitOfPreserves _ (kernelIsKernel (addSheafMap π)))
  have hπι (V : Opens X) (x : ToType ((kernel (addSheafMap π)).obj.obj (op V))) :
      π.hom.app (op V) (asRing ((kernel.ι (addSheafMap π)).hom.app (op V) x)) = 0 := by
    have h := congrArg (fun φ => φ.hom.app (op V) x) (kernel.condition (addSheafMap π))
    exact h
  { π := π.hom
    ι := (kernel.ι (addSheafMap π)).hom
    ι_injective V := (AddCommGrpCat.mono_iff_injective _).1 (mono_of_isLimit_fork (hk V))
    π_ι := hπι
    exists_of_π_eq_zero V b hb :=
      (ShortComplex.ab_exact_iff _).1 (ShortComplex.exact_of_f_is_kernel
        (ShortComplex.mk ((kernel.ι (addSheafMap π)).hom.app (op V))
          ((addSheafMap π).hom.app (op V))
          (by
            rw [← NatTrans.comp_app]
            exact congrArg (fun φ => φ.hom.app (op V)) (kernel.condition (addSheafMap π)))) (hk V))
        b hb
    π_locallySurjective := ⟨fun s => hπ.imageSieve_mem s⟩
    ι_mul_ι V x y := hsq V _ _ (hπι V x) (hπι V y) }

attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus

/-- **The connecting morphism `H⁰(X, O) → H¹(X, I)`** of the long exact cohomology sequence of
`0 → I → O' → O → 0`: a global section of `O`, read in `R⁰Γ(X, O)`, is sent by the connecting
morphism of the right derived functors of `Γ(X, -)` (the one of Stacks 05TE, attached to the
distinguished triangle of `RΓ(X, -)`) to `R¹Γ(X, I) = H¹(X, I)`. -/
noncomputable def connecting (E : SquareZeroKernel.{u, u} O'.presheaf O.presheaf I)
    (f : ToType (O.presheaf.obj (op (⊤ : Opens X)))) : cohomologyOne.{u, u} I :=
  letI := HasDerivedCategory.standard (AbelianSheaf X)
  letI := HasDerivedCategory.standard AddCommGrpCat.{u}
  (derivedPlusToStandard (sectionsFunctor X ⊤) 1).hom.app E.shortComplex.X₁
    (CechDelta.rightDerivedPlusδ (sectionsFunctor X ⊤) E.shortExact 0
      ((derivedPlusToStandard (sectionsFunctor X ⊤) 0).inv.app E.shortComplex.X₃
        ((sectionsFunctor X ⊤).toRightDerivedZero.app E.shortComplex.X₃ f)))

/-- **The boundary map of the Čech description is the connecting morphism of derived-functor
cohomology** (Stacks 02AP): both send a global section of `O` to the class of the Čech cocycle
of differences of its local lifts. -/
theorem boundary_eq_connecting (E : SquareZeroKernel.{u, u} O'.presheaf O.presheaf I)
    (f : ToType (O.presheaf.obj (op (⊤ : Opens X)))) : E.boundary f = E.connecting f := by
  rw [boundary, connecting]
  exact (Stacks.Cohomology.CechOne.rightDerivedPlusδ_toRightDerivedZero E.shortComplex
    E.shortExact f (E.boundaryCover f) (E.boundaryCover_iSup f) (E.liftCochain f)
    (E.π_liftCochain f) (E.boundaryCocycle f) fun j => congrFun (E.push_boundaryCocycle f) j).symm

/-- **Stacks 0B8S**, for a square-zero kernel `I` of a surjection `O' → O` of sheaves of
commutative rings: `M = H¹(X, I)` is a module over `R = H⁰(X, O)` (through the `O`-module
structure of `I`, `Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.moduleCohomology`), and
the connecting morphism `∂ : R → M` of the long exact cohomology sequence of
`0 → I → O' → O → 0` is a derivation. -/
@[stacks 0B8S "the connecting morphism of `0 → I → O' → O → 0` is a derivation"]
theorem exists_derivation_eq_connecting (E : SquareZeroKernel.{u, u} O'.presheaf O.presheaf I) :
    letI := E.moduleCohomology
    ∃ D : Derivation ℤ (ToType (O.presheaf.obj (op (⊤ : Opens X)))) (cohomologyOne.{u, u} I),
      ⇑D = E.connecting :=
  ⟨E.boundaryDerivation, funext E.boundary_eq_connecting⟩

/-- **Stacks 0B8S.**  Let `X` be a topological space and let `π : O' ⟶ O` be a surjection of
sheaves of commutative rings whose kernel `I` has square zero.  Then `M = H¹(X, I)` is a module
over `R = H⁰(X, O)`, and the boundary map `∂ : R → M` associated to the short exact sequence
`0 → I → O' → O → 0` is a derivation.

Here `I` is the kernel of `π` in abelian sheaves, the surjectivity of `π` is its local
surjectivity (equivalently, `π` is an epimorphism of sheaves), `H¹` is the first right derived
functor of `Γ(X, -)`, the `R`-module structure on `M` is induced by the `O`-module structure of
`I` (`Stacks.Cohomology.SquareZeroBoundary.SquareZeroKernel.smulCohomology_def`), and `∂` is the
connecting morphism of the long exact cohomology sequence. -/
@[stacks 0B8S "the boundary map of a square-zero extension of sheaves of rings is a derivation"]
theorem exists_derivation_eq_connecting_of_surjective (π : O' ⟶ O)
    (hπ : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) π.hom)
    (hsq : ∀ (V : Opens X) (b b' : ToType (O'.presheaf.obj (op V))),
      π.hom.app (op V) b = 0 → π.hom.app (op V) b' = 0 → b * b' = 0) :
    letI := (ofSurjective π hπ hsq).moduleCohomology
    ∃ D : Derivation ℤ (ToType (O.presheaf.obj (op (⊤ : Opens X))))
        (cohomologyOne.{u, u} (kernel (addSheafMap π))),
      ⇑D = (ofSurjective π hπ hsq).connecting :=
  (ofSurjective π hπ hsq).exists_derivation_eq_connecting

end SquareZeroKernel

end Stacks.Cohomology.SquareZeroBoundary

end
