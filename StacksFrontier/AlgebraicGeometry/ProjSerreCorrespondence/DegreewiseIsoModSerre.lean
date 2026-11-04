module

public import StacksFrontier.AlgebraicGeometry.ProjSerreCorrespondence.SerreClass
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degreewise bijectivity in the divisible degrees is invertibility modulo the irrelevant modules

Let `A` be a graded ring which is Noetherian as a ring and let `d` be a positive integer. A
finitely generated graded `A`-module is irrelevant for `d` exactly when it vanishes in all large
degrees divisible by `d`
(`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isIrrelevant_iff_gradeEventuallyZero`), so a
morphism of `Mod^fg_A` which is bijective on the homogeneous piece of every large degree
divisible by `d` has irrelevant kernel and cokernel: it is an isomorphism modulo the irrelevant
modules, hence becomes an isomorphism in the quotient category
`Mod^fg_A / Mod^fg_{A, irrelevant}`.

This is the bridge between the degreewise assertions (5) and (6) of Stacks 0B5R — the first
bijective in all large degrees, the second in every degree divisible by `d` — and
`CategoryTheory.ObjectProperty.isoModSerre`, which is stated at the kernel and the cokernel.

## Main results

* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.gradeEventuallyZero_kerObj` and
  `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.gradeEventuallyZero_cokerObj`: the kernel and
  the cokernel of a degreewise bijective map vanish in the degrees where it is bijective.
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.isoModSerre_of_eventually_bijective_grade`:
  **a morphism of `Mod^fg_A` bijective in all large degrees divisible by `d` is an isomorphism
  modulo the irrelevant modules.**
* `Stacks.AlgebraicGeometry.ProjSerreCorrespondence.toIrrelevantQuotientIsoOfBijectiveGrade`: the
  isomorphism it becomes in the quotient category.

## Implementation notes

The kernel and cokernel of `Mod^fg_A` are compared with the explicit ones of
`Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat` — `kerObj`, the homogeneous
submodule of elements killed by the map, and `cokerObj`, the quotient by the homogeneous image —
through the inclusion of the full subcategory, which preserves finite limits and colimits because
the finitely generated modules are a weak Serre class. Irrelevance is then read off the gradings
of those two, which are `Stacks.GradedModule.subGrade` and `Stacks.GradedModule.quotGrade`: a
homogeneous element of the kernel of a degree whose piece the map is injective on is zero, and a
homogeneous class in the cokernel of a degree whose piece the map is onto is zero.

The hypotheses are stated elementwise — injectivity as "a homogeneous element of that degree
killed by the map is zero" and surjectivity as "a homogeneous element of the target of that degree
is in the image" — rather than as the bijectivity of a restriction, because that is the form in
which the two assertions of Stacks 0B5R are applied and it needs no restriction map to be named.
Surjectivity is onto the homogeneous piece from the whole source, which is what the cokernel sees
and is weaker than degreewise surjectivity.

The degrees are indexed as `n * d` for a natural number `n`, which is the indexing
`Stacks.AlgebraicGeometry.ProjSerreCorrespondence.GradeEventuallyZero` uses.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0BXE](https://stacks.math.columbia.edu/tag/0BXE)
* [Stacks Project, Tag 0BXF](https://stacks.math.columbia.edu/tag/0BXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DirectSum
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality.GradedModuleCat

namespace Stacks.AlgebraicGeometry.ProjSerreCorrespondence

universe u v w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] {d : ℕ}

/-! ### The kernel and the cokernel of a degreewise bijective map -/

/-- **The kernel of a map which is injective on the homogeneous pieces of all large degrees
divisible by `d` vanishes in those degrees.** A homogeneous element of the kernel of such a degree
is a homogeneous element of the source killed by the map. -/
@[ega "II 2.7.2" "Forward direction"]
public theorem gradeEventuallyZero_kerObj {M N : GradedModuleCat.{u, v, w} 𝒮} (f : M ⟶ N)
    {N₀ : ℕ} (hinj : ∀ n : ℕ, N₀ ≤ n → ∀ x ∈ M.grade ((n : ℤ) * d),
      f.toLinearMap x = 0 → x = 0) :
    GradeEventuallyZero 𝒮 d (kerObj f) := by
  refine ⟨N₀, fun n hn => eq_bot_iff.2 fun x hx => AddSubgroup.mem_bot.2 ?_⟩
  obtain ⟨xv, hxker⟩ := x
  have hxg : xv ∈ M.grade ((n : ℤ) * d) := hx
  exact Subtype.ext (hinj n hn xv hxg (LinearMap.mem_ker.1 hxker))

/-- **The cokernel of a map whose image contains the homogeneous pieces of all large degrees
divisible by `d` vanishes in those degrees.** A homogeneous class of such a degree is the class of
a homogeneous element of the target, and that element is in the image. -/
public theorem gradeEventuallyZero_cokerObj {M N : GradedModuleCat.{u, v, w} 𝒮} (f : M ⟶ N)
    {N₀ : ℕ} (hsurj : ∀ n : ℕ, N₀ ≤ n → ∀ y ∈ N.grade ((n : ℤ) * d),
      ∃ x, f.toLinearMap x = y) :
    GradeEventuallyZero 𝒮 d (cokerObj f) := by
  refine ⟨N₀, fun n hn => eq_bot_iff.2 fun z hz => AddSubgroup.mem_bot.2 ?_⟩
  obtain ⟨y, hy, rfl⟩ := (Stacks.GradedModule.mem_quotGrade N.grade _).1 hz
  obtain ⟨x, hx⟩ := hsurj n hn y hy
  exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, hx⟩

/-- A graded module isomorphic to one vanishing in all large degrees divisible by `d` is
irrelevant. -/
private theorem isIrrelevant_of_iso_of_gradeEventuallyZero {P Q : GradedModuleCat.{u, v, w} 𝒮}
    (e : P ≅ Q) (h : GradeEventuallyZero 𝒮 d Q) : IsIrrelevant 𝒮 d P :=
  isIrrelevant_of_injective 𝒮 e.hom ((GradedModuleCat.mono_iff_injective e.hom).1 inferInstance)
    (isIrrelevant_of_gradeEventuallyZero 𝒮 h)

/-! ### Irrelevance of the kernel and the cokernel in `Mod^fg_A` -/

section Finite

variable [IsNoetherianRing S]

/-- **The kernel of a morphism of `Mod^fg_A` has `kerObj` of the underlying map for its underlying
graded module.** The inclusion of the finitely generated modules preserves finite limits, being
the inclusion of a weak Serre class, and `kerObj` is a kernel in all graded modules. -/
public def kerObjIso {X Y : FiniteGradedModules.{u, v, w} 𝒮} (f : X ⟶ Y) :
    (kernel f).obj ≅ kerObj f.hom :=
  haveI := ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass
    (C := GradedModuleCat.{u, v, w} 𝒮) (fun M => Module.Finite S M.carrier)
  PreservesKernel.iso (ObjectProperty.ι (C := GradedModuleCat.{u, v, w} 𝒮)
      (fun M => Module.Finite S M.carrier)) f ≪≫
    IsLimit.conePointUniqueUpToIso (kernelIsKernel f.hom) (kernelForkIsLimit f.hom)

/-- **The cokernel of a morphism of `Mod^fg_A` has `cokerObj` of the underlying map for its
underlying graded module.** -/
public def cokerObjIso {X Y : FiniteGradedModules.{u, v, w} 𝒮} (f : X ⟶ Y) :
    (cokernel f).obj ≅ cokerObj f.hom :=
  haveI := ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass
    (C := GradedModuleCat.{u, v, w} 𝒮) (fun M => Module.Finite S M.carrier)
  PreservesCokernel.iso (ObjectProperty.ι (C := GradedModuleCat.{u, v, w} 𝒮)
      (fun M => Module.Finite S M.carrier)) f ≪≫
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f.hom)
      (cokernelCoforkIsColimit f.hom)

/-- **The kernel of a morphism of `Mod^fg_A` injective on the homogeneous pieces of all large
degrees divisible by `d` is irrelevant.** -/
public theorem irrelevantModules_kernel
    {X Y : FiniteGradedModules.{u, v, w} 𝒮} (f : X ⟶ Y) {N₀ : ℕ}
    (hinj : ∀ n : ℕ, N₀ ≤ n → ∀ x ∈ X.obj.grade ((n : ℤ) * d),
      f.hom.toLinearMap x = 0 → x = 0) :
    irrelevantModules.{u, v, w} 𝒮 d (kernel f) :=
  isIrrelevant_of_iso_of_gradeEventuallyZero 𝒮 (kerObjIso 𝒮 f)
    (gradeEventuallyZero_kerObj 𝒮 f.hom hinj)

/-- **The cokernel of a morphism of `Mod^fg_A` whose image contains the homogeneous pieces of all
large degrees divisible by `d` is irrelevant.** -/
public theorem irrelevantModules_cokernel
    {X Y : FiniteGradedModules.{u, v, w} 𝒮} (f : X ⟶ Y) {N₀ : ℕ}
    (hsurj : ∀ n : ℕ, N₀ ≤ n → ∀ y ∈ Y.obj.grade ((n : ℤ) * d),
      ∃ x, f.hom.toLinearMap x = y) :
    irrelevantModules.{u, v, w} 𝒮 d (cokernel f) :=
  isIrrelevant_of_iso_of_gradeEventuallyZero 𝒮 (cokerObjIso 𝒮 f)
    (gradeEventuallyZero_cokerObj 𝒮 f.hom hsurj)

/-! ### The criterion -/

/-- **A morphism of `Mod^fg_A` which is bijective on the homogeneous piece of every large degree
divisible by `d` is an isomorphism modulo the irrelevant modules.** Both its kernel and its
cokernel vanish in those degrees, so both are irrelevant. -/
public theorem isoModSerre_of_eventually_bijective_grade (hd : 0 < d)
    {X Y : FiniteGradedModules.{u, v, w} 𝒮} (f : X ⟶ Y) {N₀ : ℕ}
    (hinj : ∀ n : ℕ, N₀ ≤ n → ∀ x ∈ X.obj.grade ((n : ℤ) * d),
      f.hom.toLinearMap x = 0 → x = 0)
    (hsurj : ∀ n : ℕ, N₀ ≤ n → ∀ y ∈ Y.obj.grade ((n : ℤ) * d),
      ∃ x, f.hom.toLinearMap x = y) :
    haveI := isSerreClass_irrelevantModules.{u, v, w} 𝒮 hd
    (ObjectProperty.isoModSerre (irrelevantModules.{u, v, w} 𝒮 d)) f :=
  have := isSerreClass_irrelevantModules.{u, v, w} 𝒮 hd
  ⟨irrelevantModules_kernel 𝒮 f hinj, irrelevantModules_cokernel 𝒮 f hsurj⟩

/-- **The isomorphism in `Mod^fg_A / Mod^fg_{A, irrelevant}` induced by a morphism which is
bijective on the homogeneous piece of every large degree divisible by `d`.** The quotient functor
inverts the isomorphisms modulo the irrelevant modules by construction. -/
public def toIrrelevantQuotientIsoOfBijectiveGrade (hd : 0 < d)
    {X Y : FiniteGradedModules.{u, v, w} 𝒮} (f : X ⟶ Y) {N₀ : ℕ}
    (hinj : ∀ n : ℕ, N₀ ≤ n → ∀ x ∈ X.obj.grade ((n : ℤ) * d),
      f.hom.toLinearMap x = 0 → x = 0)
    (hsurj : ∀ n : ℕ, N₀ ≤ n → ∀ y ∈ Y.obj.grade ((n : ℤ) * d),
      ∃ x, f.hom.toLinearMap x = y) :
    (toIrrelevantQuotient.{u, v, w} 𝒮 hd).obj X ≅ (toIrrelevantQuotient.{u, v, w} 𝒮 hd).obj Y :=
  haveI := isSerreClass_irrelevantModules.{u, v, w} 𝒮 hd
  haveI := Localization.inverts (toIrrelevantQuotient.{u, v, w} 𝒮 hd)
    (ObjectProperty.isoModSerre (irrelevantModules.{u, v, w} 𝒮 d)) f
    (isoModSerre_of_eventually_bijective_grade 𝒮 hd f hinj hsurj)
  asIso ((toIrrelevantQuotient.{u, v, w} 𝒮 hd).map f)

end Finite

end Stacks.AlgebraicGeometry.ProjSerreCorrespondence

end
