module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeSubalgebras
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage

/-!
# Finite type algebra sheaves on an algebraic space

Two facts about `AlgebraicGeometry.Space.AlgebraSheaf.IsFiniteType`, the property of an algebra
on the small étale site of an algebraic space that its structure-algebra map is of finite type on
every affine étale chart: that it is inherited by the target of a morphism whose sections are
surjective over the affine étale charts, and that the structure sheaf, read as an algebra over
itself, has it.

Together with `AlgebraicGeometry.Space.isQuasicoherent_unitAlgebra` the second makes
`AlgebraicGeometry.Space.unitAlgebra` a finite type quasi-coherent algebra, and
`AlgebraicGeometry.Space.unitAlgebraHom` is the canonical morphism from it to an arbitrary
algebra sheaf, which is the unique one by
`AlgebraicGeometry.Space.unitAlgebra_hom_right`.

## Main definitions

* `AlgebraicGeometry.Space.unitAlgebraHom` is the structure-algebra map of an algebra sheaf `A`
  read as a morphism `𝒪_Y ⟶ A` of algebra sheaves.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.IsFiniteType.of_surjective_app`: if the sections of
  `f : A ⟶ C` are surjective over every affine étale chart and `A` is of finite type, then so is
  `C`.  On a chart the structure-algebra map of `C` is the one of `A` followed by a surjection,
  so this is `RingHom.FiniteType.comp_surjective`.
* `AlgebraicGeometry.Space.isFiniteType_unitAlgebra`: `𝒪_Y` is of finite type as an
  `𝒪_Y`-algebra, its structure-algebra map being an identity on every chart.

## Implementation notes

`AlgebraicGeometry.Space.AlgebraSheaf.IsFiniteType.of_surjective_app` takes surjectivity of the
sections over the affine étale charts as an explicit hypothesis rather than deriving it from
local surjectivity of `f`, which is the shape the scheme case
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_of_isLocallySurjective` is stated
in.  The two differ by exactly one statement — that a locally surjective morphism of
quasi-coherent modules is surjective on the sections over an affine chart — and that statement is
available for the small étale site of an algebraic space, as
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`
(`StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent`), unconditionally and
by faithfully flat descent alone.

**The surjectivity needed here does not go through the uniform hypothesis `h03DW` or the
degree-one étale Čech vanishing of Stacks 03FJ.**  It is reached with no cohomology:
an epimorphism of sheaves of modules is locally surjective, the covering sieve on which a section
lifts contains a finite family of affine étale charts whose chart restrictions are jointly
faithfully flat, and membership in an image descends along a faithfully flat base change.  The
two base change comparisons that descent consumes are the two halves of
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, which quasi-coherence supplies through the
unconditional forward implication of Descent, Proposition 03DX(2),
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`.  What the Čech route
of `StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromCech` does not give is the
*literal* uniform form of Stacks 03DW, which asks cartesianness of the kernel of `q` alone and so
supplies neither half; that form, and not this file's surjectivity, is what remains open.

Surjectivity is nonetheless kept as an explicit hypothesis here, so that the one place where it
enters stays visible and so that this file does not import the descent module.

`AlgebraicGeometry.Space.unitAlgebraHom` is **not** a monomorphism in general — the
structure-algebra map of a quotient algebra is not injective — so it does not exhibit a subobject
of `A`, and neither it nor `AlgebraicGeometry.Space.isFiniteType_unitAlgebra` produces an object
of `AlgebraicGeometry.Space.FiniteTypeSubalgebra`.  That needs the *image* of
`unitAlgebraHom`, whose finite type is `IsFiniteType.of_surjective_app` applied to the
corestriction; for a quasi-coherent `A` the surjectivity that application needs is the
unconditional
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`.

## References

* [Stacks Project, Tag 082B](https://stacks.math.columbia.edu/tag/082B)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)

namespace AlgebraSheaf

variable {B S hS F hF}

/-- **Finite type passes to the target of a morphism which is surjective on the sections over the
affine étale charts.**  On such a chart the structure-algebra map of `C` is the structure-algebra
map of `A` followed by a surjection, so `RingHom.FiniteType.comp_surjective` applies. -/
theorem IsFiniteType.of_surjective_app {A C : AlgebraSheaf.{u, m} B S hS F hF} (f : A ⟶ C)
    (hf : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        Function.Surjective ((f.right.hom.app (.op U)).hom))
    (hA : A.IsFiniteType) : C.IsFiniteType := by
  intro U hU
  rw [← comp_algebraMap f (.op U)]
  exact (hA U hU).comp_surjective (hf U hU)

end AlgebraSheaf

/-! ### The structure sheaf as an algebra over itself -/

/-- The structure-algebra map of an algebra sheaf `A`, read as the canonical morphism of algebra
sheaves `𝒪_Y ⟶ A`.  It is the unique such morphism, by
`AlgebraicGeometry.Space.unitAlgebra_hom_right`. -/
def unitAlgebraHom (Y : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) :
    unitAlgebra B S hS Y ⟶ A :=
  ⟨A.hom, fun _ _ => rfl⟩

/-- The underlying morphism of sheaves of rings of `unitAlgebraHom` is the structure-algebra map
of `A`. -/
@[simp]
theorem unitAlgebraHom_right (Y : AlgebraicSpaces B S hS)
    (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) :
    (unitAlgebraHom B S hS Y A).right = A.hom :=
  rfl

/-- **`𝒪_Y` is of finite type as an `𝒪_Y`-algebra.**  Its structure-algebra map on every chart is
the identity ring map, which is of finite type. -/
theorem isFiniteType_unitAlgebra (Y : AlgebraicSpaces B S hS) :
    (unitAlgebra B S hS Y).IsFiniteType :=
  fun _ _ => RingHom.FiniteType.id _

end AlgebraicGeometry.Space

end
