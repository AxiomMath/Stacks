module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.StandardCoverCofinality
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulDerivedSystem
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.TruncationTower
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AlternatingCechComputesDerivedSections
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulCechCohomologyOnUnion

/-!
# The alternating Čech complex computes cohomology over a union of basic opens

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`, read as an open subscheme of `X`.  The
opens `D(fᵢ) ∩ U = D(fᵢ)` cover `U`, and every intersection of finitely many of them is a basic
open of `X` contained in `U`, hence an affine open of `U`.  For a complex `ℱ^•` of quasi-coherent
`𝒪_U`-modules the comparison map

`Tot(Č_alt(𝒰, ℱ^•)) ⟶ RΓ(U, ℱ^•)`

of Tag 08C1 is therefore an isomorphism in `D(Ab)`, by the acyclic-basis criterion of Tag 08C2
applied to the basis of affine opens of `U`.

## Main definitions

* `Koszul.DerivedSystem.unionScheme` is `U` as a scheme, `Koszul.DerivedSystem.unionSpace` its
  underlying space, and `Koszul.DerivedSystem.unionSpaceCover` the covering of `U` by the `D(fᵢ)`,
  indexed by a copy of `Fin r` in the universe of the ring.

## Main results

* `Koszul.DerivedSystem.iSup_unionSpaceCover`: the family covers `U`.
* `Koszul.DerivedSystem.isAffineOpen_iInf_unionSpaceCover`: the intersections occurring in the Čech
  complex of that covering are affine opens of `U`.
* `Koszul.DerivedSystem.isIso_alternatingCechToDerivedComparison`: **the abelian form of
  Tag 08D2**, that the comparison map of Tag 08C1 for the covering `𝒰` is an isomorphism in
  `D(Ab)` on every complex of quasi-coherent `𝒪_U`-modules.

## Implementation notes

The index type of the covering is `ULift (Fin r)` in the universe of the ring, because the
comparison map of Tag 08C1 is stated for a family of opens indexed by a type in the universe of
the space; a finite sequence `f₁, …, f_r` is an ordered `r`-tuple, so the index type is `Fin r`
before that lift.

Tag 08C2 asks for the vanishing, in positive degrees and over every member of the basis, of the
cohomology of the terms of the complex, of the cokernels of its differentials, and of its
cohomology sheaves.  All three are quasi-coherent as soon as the terms are: the quasi-coherent
modules on a scheme are closed under kernels and cokernels, and a cohomology sheaf is a cokernel
of a map into a kernel.  The vanishing itself is Tag 01XB, in the shape
`AlgebraicGeometry.isZero_rightDerived_evaluation_of_isAffineOpen`.

The affineness of the intersections is the affineness of a basic open of an affine scheme,
transported across the open immersion `U ⟶ X`: an open of `U` is affine exactly when its image
in `X` is, and the image of the preimage of an open contained in `U` is that open again.

## References

* [Stacks Project, Tag 08D2](https://stacks.math.columbia.edu/tag/08D2)
* [Stacks Project, Tag 08C1](https://stacks.math.columbia.edu/tag/08C1)
* [Stacks Project, Tag 08C2](https://stacks.math.columbia.edu/tag/08C2)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules

universe u

namespace Koszul.DerivedSystem

attribute [local instance] HasDerivedCategory.standard

variable {A : CommRingCat.{u}} {r : ℕ}

/-! ### The open subscheme `U` and its covering by the basic opens -/

/-- The open `U = D(f₁) ∪ ⋯ ∪ D(f_r)`, read as an open subscheme of `Spec A`. -/
public abbrev unionScheme (f : Fin r → A) : Scheme.{u} := (unionOfBasicOpens f).toScheme

/-- The underlying topological space of the open subscheme `U`, read as an open subspace of
the space of `Spec A`. -/
public abbrev unionSpace (f : Fin r → A) : TopCat.{u} := Usp (unionOfBasicOpens f)

/-- The structure sheaf of `U`, as the restriction of the structure sheaf of `Spec A`. -/
public abbrev unionRingSheaf (f : Fin r → A) :
    Sheaf (Opens.grothendieckTopology (unionSpace f)) RingCat.{u} :=
  resRing (unionOfBasicOpens f) (Spec A).ringCatSheaf

/-- The covering `𝒰 : U = ⋃ᵢ D(fᵢ)`, as a family of opens of `U` indexed by a copy of `Fin r`
in the universe of the ring. -/
public abbrev unionSpaceCover (f : Fin r → A) : ULift.{u} (Fin r) → Opens (unionSpace f) :=
  fun i ↦ (Opens.map (Opens.inclusion' (unionOfBasicOpens f))).obj (basicOpens f i.down)

/-- **The basic opens cover `U`.** -/
public theorem iSup_unionSpaceCover (f : Fin r → A) :
    (⊤ : Opens (unionSpace f)) = iSup (unionSpaceCover f) := by
  refine le_antisymm (fun x _ ↦ ?_) le_top
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2
  exact Opens.mem_iSup.mpr ⟨⟨i⟩, hi⟩

/-- The intersections occurring in the Čech complex of `𝒰` are the preimages of the
corresponding intersections of basic opens of `Spec A`. -/
public theorem iInf_unionSpaceCover (f : Fin r → A) {p : ℕ}
    (s : Fin (p + 1) → ULift.{u} (Fin r)) :
    (⨅ k, unionSpaceCover f (s k)) =
      (Opens.map (Opens.inclusion' (unionOfBasicOpens f))).obj
        (⨅ k, basicOpens f (s k).down) := by
  apply Opens.ext
  simp only [Opens.coe_iInf, Opens.map_coe]
  exact (Set.preimage_iInter).symm

/-- **The intersections occurring in the Čech complex of `𝒰` are affine opens of `U`.** -/
public theorem isAffineOpen_iInf_unionSpaceCover (f : Fin r → A) {p : ℕ}
    (s : Fin (p + 1) → ULift.{u} (Fin r)) :
    IsAffineOpen (X := unionScheme f) (⨅ k, unionSpaceCover f (s k)) := by
  have hle : (⨅ k, basicOpens f (s k).down) ≤ unionOfBasicOpens f :=
    le_trans (iInf_le _ 0) (le_iSup (basicOpens f) (s 0).down)
  have h : (⨅ k, unionSpaceCover f (s k) : (unionScheme f).Opens) =
      (unionOfBasicOpens f).ι ⁻¹ᵁ (⨅ k, basicOpens f (s k).down) := iInf_unionSpaceCover f s
  refine ((unionOfBasicOpens f).ι.isAffineOpen_iff_of_isOpenImmersion).mp ?_
  rw [h, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hle]
  exact isAffineOpen_iInf_basicOpens f s

/-! ### Quasi-coherence of the cokernels and of the cohomology sheaves -/

/-- The cohomology sheaves of a complex of quasi-coherent modules on a scheme are
quasi-coherent: the quasi-coherent modules are closed under kernels and cokernels, and a
cohomology sheaf is a cokernel of a map into a kernel. -/
public theorem isQuasicoherent_homology {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) (q : ℤ) : (K.homology q).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isColimit_cokernelCofork
    (K.homologyIsCokernel ((ComplexShape.up ℤ).prev q) q rfl) (hK _)
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isLimit_kernelFork
      (K.cyclesIsKernel q ((ComplexShape.up ℤ).next q) rfl) (hK q) (hK _))

/-- The cokernels of the differentials of a complex of quasi-coherent modules are
quasi-coherent. -/
public theorem isQuasicoherent_cokernel_d {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) (q : ℤ) :
    (cokernel (K.d (q - 1) q)).IsQuasicoherent := by
  have := hK (q - 1)
  have := hK q
  infer_instance

/-! ### The comparison map is an isomorphism -/

/-- **Stacks Project, Tag 08D2, in `D(Ab)`.**  In Situation 08CZ, the comparison map
`Tot(Č_alt(𝒰, ℱ^•)) ⟶ RΓ(U, ℱ^•)` of Tag 08C1 for the covering `𝒰` of `U` by the basic opens
`D(fᵢ)` is an isomorphism in `D(Ab)` for every complex `ℱ^•` of quasi-coherent
`𝒪_U`-modules. -/
@[stacks 08D2 "the comparison map is an isomorphism, in D(Ab)"]
public theorem isIso_alternatingCechToDerivedComparison (f : Fin r → A)
    (K : CochainComplex (SheafOfModules.{u} (unionRingSheaf f)) ℤ)
    (hK : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    IsIso ((Stacks.Cech.alternatingCechToDerivedComparison (unionSpace f)
      (unionRingSheaf f) (unionSpaceCover f) (iSup_unionSpaceCover f)).app K) := by
  refine Stacks.Cech.isIso_alternatingCechToDerivedComparison_of_acyclicBasis
    (unionSpace f) (unionRingSheaf f) (unionSpaceCover f) (iSup_unionSpaceCover f) K
    (unionScheme f).affineOpens (unionScheme f).isBasis_affineOpens
    (fun p s ↦ isAffineOpen_iInf_unionSpaceCover f s) (fun W hW q p hp ↦ ?_)
    (fun W hW q p hp ↦ ?_) (fun W hW q p hp ↦ ?_) <;>
  · have := hK q
    have := @isQuasicoherent_cokernel_d (unionScheme f) K hK q
    have := @isQuasicoherent_homology (unionScheme f) K hK q
    exact @isZero_rightDerived_evaluation_of_isAffineOpen (unionScheme f) _ ‹_› W hW p hp

end Koszul.DerivedSystem

end
