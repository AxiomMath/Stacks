module

public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectKGroupRing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.SecondAdamsOperator

/-!
# The second Adams operator on `K₀(D_perf(𝒪_X))` when `2` is invertible on `X`

Let `X` be a scheme on which `2` is invertible, i.e. `2` is a unit of `Γ(X, 𝒪_X)`. For a perfect
object `L` of `D(𝒪_X)` the group `{±1}` acts on `L ⊗^L L` by switching the factors, and
[Stacks, Tag 0FEK] sets

`ψ²(L) = [(L ⊗^L L)^+] - [(L ⊗^L L)^-]`,

`(-)^+` and `(-)^-` denoting the invariants and the anti-invariants. This file defines `ψ²` as
an additive endomorphism of `K₀(D_perf(𝒪_X))` and proves that it is well defined.

## Main definitions

* `AlgebraicGeometry.secondAdamsPerfect`: `ψ² : K₀(D_perf(𝒪_X)) ⟶ K₀(D_perf(𝒪_X))`, for any
  model of the derived category.
* `AlgebraicGeometry.perfectKZeroSecondAdams`: the same on `AlgebraicGeometry.PerfectKZero X`,
  the group `K₀(X)` of [Stacks, Tag 0FDG].

## Main results

* `AlgebraicGeometry.exists_switchSplittings_perfect`: the invariants and the anti-invariants of
  the switch on `L ⊗^L L` exist, and are perfect whichever splittings are taken.
* `AlgebraicGeometry.secondAdamsPerfect_cls`: **`ψ²([L]) = [(L ⊗^L L)^+] - [(L ⊗^L L)^-]`**, for
  any choice of the invariants and the anti-invariants.
* `AlgebraicGeometry.secondAdamsPerfect_distinguished`: **well-definedness**: the value is
  additive along distinguished triangles of `D_perf(𝒪_X)`, whatever invariants and
  anti-invariants are chosen at the three vertices.

## Implementation notes

**The derived tensor product and the switch.** `L ⊗^L L` is the tensor product of the symmetric
monoidal structure `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` of [Stacks, Tag 0FPT]
on `D(𝒪_X)`, whose tensor product is, on K-flat complexes, the image of the total tensor product,
and whose commutativity constraint is the Koszul symmetry; the switch is that constraint at
`(L, L)`.

**What `(-)^+` and `(-)^-` are.** Since `2` is invertible, `(𝟙 + σ)/2` and `(𝟙 - σ)/2` are
complementary idempotents of `L ⊗^L L`, and the invariants and the anti-invariants are the objects
splitting them, `Stacks.SecondAdamsPerfect.IdempotentSplitting`. Splittings exist
(`exists_switchSplittings_perfect`): writing `L` as the image of a K-flat complex `K`, they are cut
out of `Tot(K ⊗ K)` by the kernels of `𝟙 ∓ σ`. Any two splittings of one idempotent have isomorphic
objects, so the classes do not depend on the choice.

**Well-definedness.** This is `Stacks.SecondAdamsPerfect.secondAdamsValue_distinguished`, an
argument as for [Stacks, Tag 0FEJ] from the exactness of taking invariants: a distinguished
triangle is the image of the degreewise split short exact sequence `0 → K₁ → Cone(g) → K₀[1] → 0`
attached to a map `g` of K-flat complexes, taking invariants of complexes is exact, and the
three-step filtration of the tensor square of the middle term has as graded pieces the tensor
squares of the outer terms and a middle piece on which the switch exchanges two summands, so that
its invariants and anti-invariants have equal classes.

**The hypothesis that `2` is invertible on `X`** is read as `IsUnit (2 : Γ(X, ⊤))`; it makes `2`
a unit in every ring of sections, hence invertible on every `𝒪_X`-module
(`SheafOfModules.isIso_two_smul_id_of_isUnit`) and on `D(𝒪_X)`.

**The model of the derived category** is arbitrary in `secondAdamsPerfect`; `PerfectKZero X` is
defined with the standard model, and `perfectKZeroSecondAdams` is `secondAdamsPerfect` there.

## References

* [Stacks Project, Tag 0FEK](https://stacks.math.columbia.edu/tag/0FEK)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FDG](https://stacks.math.columbia.edu/tag/0FDG)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open Stacks.SheafOfModules.DerivedMonoidal Stacks.SecondAdamsPerfect
open Stacks.Cohomology.PerfectComplexes (IsPerfect)

universe d u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- If `2` is a unit of `Γ(X, 𝒪_X)`, it is a unit in every ring of sections of `𝒪_X`. -/
theorem isUnit_two_presheaf_obj (h2 : IsUnit (2 : Γ(X, ⊤))) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    IsUnit (2 : X.toRingedSpace.sheaf.val.obj U) := by
  have h := h2.map (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op).hom
  rwa [map_ofNat] at h

section Model

variable [HasDerivedCategory.{d} (Mod X.toRingedSpace.sheaf)]

/-- `D_perf(𝒪_X)`: the perfect objects of `D(𝒪_X)`, read at the spelling
`Stacks.SheafOfModules.DerivedMonoidal.DerivedModules` of `D(𝒪_X)` on which its symmetric
monoidal structure of [Stacks, Tag 0FPT] is defined. -/
local notation "𝒟ₚ" => ObjectProperty.FullSubcategory
  (fun K : DerivedModules X.toRingedSpace.sheaf => IsPerfect (X := X.toRingedSpace) K)

/-- The perfect objects of `D(𝒪_X)` form a triangulated subcategory (Tag 08CR), read at the
spelling `Stacks.SheafOfModules.DerivedMonoidal.DerivedModules` of `D(𝒪_X)` on which its
symmetric monoidal structure is defined. -/
instance isTriangulated_isPerfect_derivedModules :
    (show ObjectProperty (DerivedModules X.toRingedSpace.sheaf) from
      fun K => IsPerfect (X := X.toRingedSpace) K).IsTriangulated :=
  Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect X.toRingedSpace

/-- The perfect objects of `D(𝒪_X)` are closed under isomorphism, read at the spelling
`Stacks.SheafOfModules.DerivedMonoidal.DerivedModules` of `D(𝒪_X)`. -/
instance isClosedUnderIsomorphisms_isPerfect_derivedModules :
    (show ObjectProperty (DerivedModules X.toRingedSpace.sheaf) from
      fun K => IsPerfect (X := X.toRingedSpace) K).IsClosedUnderIsomorphisms :=
  Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect

/-- The first summand of a perfect biproduct is perfect. -/
theorem isPerfect_of_biprod_fst (K L : DerivedModules X.toRingedSpace.sheaf)
    (h : IsPerfect (X := X.toRingedSpace) (K ⊞ L : DerivedModules X.toRingedSpace.sheaf)) :
    IsPerfect (X := X.toRingedSpace) K :=
  (Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod K L h).1

/-- The derived tensor product of two perfect objects is perfect, for the tensor product of the
symmetric monoidal structure of [Stacks, Tag 0FPT]. -/
theorem isPerfect_tensorObj :
    letI := derivedMonoidal X.toRingedSpace.sheaf
    ∀ K L : DerivedModules X.toRingedSpace.sheaf, IsPerfect (X := X.toRingedSpace) K →
      IsPerfect (X := X.toRingedSpace) L →
        IsPerfect (X := X.toRingedSpace) (K ⊗ L : DerivedModules X.toRingedSpace.sheaf) :=
  fun K L hK hL =>
    (ObjectProperty.prop_of_iso
      (show ObjectProperty (DerivedModules X.toRingedSpace.sheaf) from
        fun K => IsPerfect (X := X.toRingedSpace) K)
      (RingedSpace.derivedTensorObjIso X.toRingedSpace
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.toRingedSpace.sheaf) K L)
      (RingedSpace.isPerfect_derivedTensorProduct X.toRingedSpace
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.toRingedSpace.sheaf)
        K L hK hL))

/-- The second Adams operator `ψ²` on `K₀(D_perf(𝒪_X))`, for a scheme `X` on which `2` is
invertible: the additive endomorphism sending the class of a perfect object `L` to
`[(L ⊗^L L)^+] - [(L ⊗^L L)^-]` (`secondAdamsPerfect_cls`). -/
@[stacks 0FEK "the second Adams operator ψ² on K₀(D_perf(𝒪_X)), for any model of D(𝒪_X), as an \
  additive endomorphism; its value on classes is `secondAdamsPerfect_cls`, and its \
  well-definedness (additivity along distinguished triangles) is \
  `secondAdamsPerfect_distinguished`"]
def secondAdamsPerfect (h2 : IsUnit (2 : Γ(X, ⊤))) :
    K0 𝒟ₚ →+ K0 𝒟ₚ :=
  secondAdamsOperator X.toRingedSpace.sheaf
    (fun K : DerivedModules X.toRingedSpace.sheaf => IsPerfect (X := X.toRingedSpace) K)
    (isUnit_two_presheaf_obj X h2) (isPerfect_of_biprod_fst X) (isPerfect_tensorObj X)

/-- For a perfect object `L` of `D(𝒪_X)`, with `2` invertible on `X`, the idempotents `(𝟙 + σ)/2`
and `(𝟙 - σ)/2` of the switch `σ` of `L ⊗^L L` split, and the objects splitting them — the
invariants `(L ⊗^L L)^+` and the anti-invariants `(L ⊗^L L)^-` — are perfect, whichever splittings
are taken. -/
@[stacks 0FEK "the invariants (L ⊗^L L)^+ and the anti-invariants (L ⊗^L L)^- of the switch on \
  the derived tensor square of a perfect object exist, and are perfect for every choice"]
theorem exists_switchSplittings_perfect (h2 : IsUnit (2 : Γ(X, ⊤))) (L : 𝒟ₚ) :
    letI := derivedMonoidal X.toRingedSpace.sheaf
    letI := derivedSymmetric X.toRingedSpace.sheaf
    haveI := isIso_two_smul_id X.toRingedSpace.sheaf (isUnit_two_presheaf_obj X h2)
    Nonempty (IdempotentSplitting
        (invariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ _))) ∧
      Nonempty (IdempotentSplitting
        (antiInvariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ _))) ∧
      (∀ s : IdempotentSplitting
        (invariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ _)),
          IsPerfect (X := X.toRingedSpace) s.obj) ∧
      (∀ s : IdempotentSplitting
        (antiInvariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ _)),
          IsPerfect (X := X.toRingedSpace) s.obj) :=
  exists_switchSplittings X.toRingedSpace.sheaf
    (fun K : DerivedModules X.toRingedSpace.sheaf => IsPerfect (X := X.toRingedSpace) K)
    (isUnit_two_presheaf_obj X h2)
    (isPerfect_of_biprod_fst X) (isPerfect_tensorObj X) L

/-- For a scheme `X` on which `2` is invertible and a perfect object `L` of `D(𝒪_X)`, the second
Adams operator sends the class of `L` to the class of the invariants minus the class of the
anti-invariants of the switch on `L ⊗^L L`, for any choice of the two (which exist and are perfect
by `exists_switchSplittings_perfect`). -/
@[stacks 0FEK "ψ²([L]) = [(L ⊗^L L)^+] - [(L ⊗^L L)^-] for every perfect L and every choice of \
  the invariants and the anti-invariants of the switch"]
theorem secondAdamsPerfect_cls (h2 : IsUnit (2 : Γ(X, ⊤))) (L : 𝒟ₚ) :
    letI := derivedMonoidal X.toRingedSpace.sheaf
    letI := derivedSymmetric X.toRingedSpace.sheaf
    haveI := isIso_two_smul_id X.toRingedSpace.sheaf (isUnit_two_presheaf_obj X h2)
    ∀ (sp : IdempotentSplitting
        (invariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ _)))
      (sm : IdempotentSplitting
        (antiInvariantIdempotent ((β_ L.obj L.obj).hom : L.obj ⊗ L.obj ⟶ _)))
      (hp : IsPerfect (X := X.toRingedSpace) sp.obj) (hm : IsPerfect (X := X.toRingedSpace) sm.obj),
      secondAdamsPerfect X h2 (K0.cls L) = K0.cls (⟨sp.obj, hp⟩ : 𝒟ₚ) -
        K0.cls (⟨sm.obj, hm⟩ : 𝒟ₚ) :=
  secondAdamsOperator_cls X.toRingedSpace.sheaf
    (fun K : DerivedModules X.toRingedSpace.sheaf => IsPerfect (X := X.toRingedSpace) K)
    (isUnit_two_presheaf_obj X h2)
    (isPerfect_of_biprod_fst X) (isPerfect_tensorObj X) L

/-- For a distinguished triangle `L₁ ⟶ L₂ ⟶ L₃ ⟶ L₁[1]` of `D_perf(𝒪_X)`, `2` being invertible on
`X`, and for any choices `sᵢ^±` of the invariants and the anti-invariants of the switch on
`Lᵢ ⊗^L Lᵢ`,

`[s₂^+] - [s₂^-] = ([s₁^+] - [s₁^-]) + ([s₃^+] - [s₃^-])`

in `K₀(D_perf(𝒪_X))`. -/
@[stacks 0FEK "well-definedness on K₀: [(L ⊗^L L)^+] - [(L ⊗^L L)^-] is additive along \
  distinguished triangles of D_perf(𝒪_X), for every choice of invariants and anti-invariants"]
theorem secondAdamsPerfect_distinguished (h2 : IsUnit (2 : Γ(X, ⊤)))
    (T : Triangle 𝒟ₚ) (hT : T ∈ distTriang _) :
    letI := derivedMonoidal X.toRingedSpace.sheaf
    letI := derivedSymmetric X.toRingedSpace.sheaf
    haveI := isIso_two_smul_id X.toRingedSpace.sheaf (isUnit_two_presheaf_obj X h2)
    ∀ (sp₁ : IdempotentSplitting
        (invariantIdempotent ((β_ T.obj₁.obj T.obj₁.obj).hom : T.obj₁.obj ⊗ T.obj₁.obj ⟶ _)))
      (sm₁ : IdempotentSplitting
        (antiInvariantIdempotent ((β_ T.obj₁.obj T.obj₁.obj).hom : T.obj₁.obj ⊗ T.obj₁.obj ⟶ _)))
      (sp₂ : IdempotentSplitting
        (invariantIdempotent ((β_ T.obj₂.obj T.obj₂.obj).hom : T.obj₂.obj ⊗ T.obj₂.obj ⟶ _)))
      (sm₂ : IdempotentSplitting
        (antiInvariantIdempotent ((β_ T.obj₂.obj T.obj₂.obj).hom : T.obj₂.obj ⊗ T.obj₂.obj ⟶ _)))
      (sp₃ : IdempotentSplitting
        (invariantIdempotent ((β_ T.obj₃.obj T.obj₃.obj).hom : T.obj₃.obj ⊗ T.obj₃.obj ⟶ _)))
      (sm₃ : IdempotentSplitting
        (antiInvariantIdempotent ((β_ T.obj₃.obj T.obj₃.obj).hom : T.obj₃.obj ⊗ T.obj₃.obj ⟶ _)))
      (hp₁ : IsPerfect (X := X.toRingedSpace) sp₁.obj)
      (hm₁ : IsPerfect (X := X.toRingedSpace) sm₁.obj)
      (hp₂ : IsPerfect (X := X.toRingedSpace) sp₂.obj)
      (hm₂ : IsPerfect (X := X.toRingedSpace) sm₂.obj)
      (hp₃ : IsPerfect (X := X.toRingedSpace) sp₃.obj)
      (hm₃ : IsPerfect (X := X.toRingedSpace) sm₃.obj),
      K0.cls (⟨sp₂.obj, hp₂⟩ : 𝒟ₚ) -
          K0.cls (⟨sm₂.obj, hm₂⟩ : 𝒟ₚ) =
        (K0.cls (⟨sp₁.obj, hp₁⟩ : 𝒟ₚ) -
          K0.cls (⟨sm₁.obj, hm₁⟩ : 𝒟ₚ)) +
        (K0.cls (⟨sp₃.obj, hp₃⟩ : 𝒟ₚ) -
          K0.cls (⟨sm₃.obj, hm₃⟩ : 𝒟ₚ)) :=
  secondAdams_distinguished X.toRingedSpace.sheaf
    (fun K : DerivedModules X.toRingedSpace.sheaf => IsPerfect (X := X.toRingedSpace) K)
    (isUnit_two_presheaf_obj X h2)
    (isPerfect_of_biprod_fst X) (isPerfect_tensorObj X) T hT

end Model

/-- The second Adams operator on the group `AlgebraicGeometry.PerfectKZero X = K₀(D_perf(𝒪_X))`
of [Stacks, Tag 0FDG]: `secondAdamsPerfect` at the standard model of the derived category. -/
@[stacks 0FEK "ψ² on K₀(X) = PerfectKZero X of Tag 0FDG: `secondAdamsPerfect` at the standard \
  model of D(𝒪_X) that PerfectKZero is defined with"]
def perfectKZeroSecondAdams (h2 : IsUnit (2 : Γ(X, ⊤))) : PerfectKZero X →+ PerfectKZero X :=
  @secondAdamsPerfect X (HasDerivedCategory.standard _) h2

end AlgebraicGeometry

end
