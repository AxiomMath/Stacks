module

public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP
public import StacksFrontier.Algebra.DifferentialGraded.NativeCover
public import StacksCore.Tactic.StacksAttribute

/-! # Covers by extensions of direct sums of shifts, bundled

Let `R` be a commutative ring, `(A, d)` a differential graded `R`-algebra and `M` a right
differential graded `A`-module. Tag 09KN produces a surjection `P ⟶ M` from a differential
graded `A`-module `P` which is surjective on cocycles in every degree and which is an extension
of one direct sum of shifts of `A` by another, the extension being an admissible short exact
sequence. This is the single step from which the property-(P) resolutions of Tag 09KP are built
by iteration.

This file states and proves that theorem in the bundled `DifferentialGradedAlgebra` /
`DifferentialGradedModule` interface of Stacks Tag 09JJ, which is what the rest of the chapter
consumes.

## Main results

* `DifferentialGradedModule.exists_cover`: every differential graded `A`-module `M` admits a
  surjection from a differential graded `A`-module `P` which is surjective on cocycles in every
  degree and sits in an admissible short exact sequence `P' ⟶ P ⟶ P''` with `P'` and `P''`
  isomorphic to direct sums of shifts of `A`.

## Implementation notes

No mathematics is redone here: the content is proved for the unbundled encoding
`Stacks.DifferentialGraded.DGAlgebra` / `Stacks.DifferentialGraded.DGModule` as
`DifferentialGraded.NativeCover.exists_native_cover` in
`StacksFrontier/Algebra/DifferentialGraded/NativeCover.lean`, and this file transports that theorem
across the conversions of the namespace `DifferentialGradedModule.Unbundled` of
`StacksFrontier/Algebra/DifferentialGraded/Module/PropertyP.lean`, exactly as
`DifferentialGradedModule.exists_propertyP_resolution` transports Tag 09KP.

Two conclusions are transported rather than inherited. The isomorphisms onto direct sums of
shifts become *bijective homomorphisms* onto `DifferentialGradedModule.directSumShifts`, because
the bundled encoding records no inverse datum; `Unbundled.iso_bijective` supplies the
bijectivity, and `directSumShifts A k` is by definition the bundling of the unbundled direct sum
of shifts, so the targets agree. The exactness `range i = ker p` is an equality of
`Aᵐᵒᵖ`-submodules on the unbundled side and of `R`-submodules on the bundled one, so it is
re-proved elementwise from the unbundled equality; the two memberships are the same condition.

The bundled encoding of Tag 09JJ is single-universe: the base ring, the algebra and every module
live in one universe `u`, and so do the cell index types `ι'`, `ι''`. The unbundled statement is
universe-polymorphic, and specialises to this.

## References

* [Stacks Project, Tag 09KN](https://stacks.math.columbia.edu/tag/09KN)
-/

@[expose] public noncomputable section

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R]

/-- **Stacks 09KN** in the bundled encoding. Let `(A, d)` be a differential graded algebra over
a commutative ring `R` and let `M` be a right differential graded `A`-module. Then there is a
right differential graded `A`-module `P` and a homomorphism `f : P ⟶ M` such that

1. `f` is surjective;
2. `f` is surjective on cocycles in every degree: every degree-`n` cocycle of `M` is the image
   of a degree-`n` cocycle of `P`; and
3. `P` is an extension of a direct sum of shifts of `A` by a direct sum of shifts of `A`, by an
   admissible short exact sequence `P' ⟶ P ⟶ P''` whose two ends `P'` and `P''` admit bijective
   homomorphisms onto `directSumShifts A k'` and `directSumShifts A k''` respectively.

This is `DifferentialGraded.NativeCover.exists_native_cover` transported to the bundled
encoding. -/
@[stacks 09KN]
theorem exists_cover (A : DifferentialGradedAlgebra R) (M : DifferentialGradedModule A) :
    ∃ (P : DifferentialGradedModule A) (f : P ⟶ M),
      Function.Surjective f.toFun ∧
      (∀ (n : ℤ) (y : M.M), y ∈ M.grading n → M.d y = 0 →
        ∃ x : P.M, x ∈ P.grading n ∧ P.d x = 0 ∧ f.toFun x = y) ∧
      ∃ (P' P'' : DifferentialGradedModule A) (i : P' ⟶ P) (p : P ⟶ P'')
        (ι' ι'' : Type u) (dec' : DecidableEq ι') (dec'' : DecidableEq ι'')
        (k' : ι' → ℤ) (k'' : ι'' → ℤ)
        (e' : P' ⟶ @directSumShifts _ _ A ι' dec' k')
        (e'' : P'' ⟶ @directSumShifts _ _ A ι'' dec'' k''),
        Function.Bijective e'.toFun ∧ Function.Bijective e''.toFun ∧
        IsAdmissibleShortExact i p := by
  obtain ⟨P, hP, f, hsurj, -, hcoc, P', P'', hP', hP'', i, p, ι', ι'', dec', dec'',
      k', k'', e', e'', hses⟩ :=
    DifferentialGraded.NativeCover.exists_native_cover (Unbundled.algebra A)
      (Unbundled.algebra_isLawful A)
      (Unbundled.module M) (Unbundled.module_isLawful M)
  let g : Hom (Unbundled.bundle hP) M :=
    { toFun := Unbundled.restrictR (N := Unbundled.module M) f.toFun
      map_smul := fun x a => f.toFun.map_smul (MulOpposite.op a) x
      map_grading := f.map_grading
      map_d := LinearMap.ext f.commute_d }
  refine ⟨Unbundled.bundle hP, g, hsurj, hcoc, Unbundled.bundle hP', Unbundled.bundle hP'',
    Unbundled.bundleHom hP' hP i, Unbundled.bundleHom hP hP'' p, ι', ι'', dec', dec'', k', k'',
    Unbundled.bundleHom hP' (@Unbundled.shiftSum_isLawful R _ A ι' dec' k') e'.toHom,
    Unbundled.bundleHom hP'' (@Unbundled.shiftSum_isLawful R _ A ι'' dec'' k'') e''.toHom,
    Unbundled.iso_bijective e', Unbundled.iso_bijective e'', ?_⟩
  obtain ⟨-, r, hr⟩ := hses.admissibleMono
  obtain ⟨-, s, hs⟩ := hses.admissibleEpi
  refine { injective := hses.injective
           surjective := hses.surjective
           exact := ?_
           admissibleMono := ⟨Unbundled.bundleGradedHom hP hP' r, hr⟩
           admissibleEpi := ⟨Unbundled.bundleGradedHom hP'' hP s, hs⟩ }
  have hex := SetLike.ext_iff.mp hses.exact
  ext x
  simpa only [LinearMap.mem_range, LinearMap.mem_ker, Unbundled.restrictR_apply] using hex x

end DifferentialGradedModule

end
