module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.GradedPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedComapAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.GeneratingFamily

/-!
# The two pullbacks of a graded algebra sheaf, compared

Let `g : Z ⟶ Y` be a morphism of schemes with `Y` **affine** and let `𝓐` be a sheaf of graded
`𝒪_Y`-algebras with commutative homogeneous multiplication and quasi-coherent pieces. There are
two things one may call the pullback of `𝓐` along `g`:

* the **degreewise module pullback** `Stacks.Conormal.gradedPullback g 𝓐`, the graded algebra
  sheaf `n ↦ g^*(𝓐ₙ)`, whose ungraded realization is a sheaf of commutative `𝒪_Z`-algebras;
* the **algebra pullback** `(algebraPullback g).obj (⨁ₙ 𝓐ₙ)`, the pushout
  `g⁻¹(⨁ₙ 𝓐ₙ) ⊗_{g⁻¹𝒪_Y} 𝒪_Z` of sheaves of commutative rings, which is what a relative spectrum
  over `Z` consumes and what [Stacks, Tag 01LX] part (2) produces.

The implementation notes of
`StacksFrontier/AlgebraicGeometry/FormalFunctions/SpecReesRelativeSpec.lean` record that no
comparison between the two is in the library. This file produces one, in the direction and the
strength that [Stacks, Tag 01S8] needs to conclude that a relative spectrum is a closed
subscheme: a morphism of sheaves of commutative `𝒪_Z`-algebras

`ψ : (algebraPullback g).obj (⨁ₙ 𝓐ₙ) ⟶ ⨁ₙ g^*(𝓐ₙ)`

whose morphism of sheaves of rings is **locally surjective**.

## Why this is the datum the fibre-side instance of Tag 0897 needs

[Stacks, Tag 0D2M] applies part (2) of [Stacks, Tag 0897] on a fibre `X_y` of a proper morphism,
over the associated graded `Gr_𝔪(A) = ⨁ₙ 𝔪ⁿ/𝔪ⁿ⁺¹` of the maximal ideal of the local base. The
one hypothesis of
`Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_gradedModule` that is not
supplied by the graded data alone is a proper morphism from the relative spectrum
`X' = Spec_{X_y}(⨁ₙ 𝓑ₙ)` to the spectrum of a Noetherian ring; and the route to it is to exhibit
`X'` as a closed subscheme of `Spec(Gr_𝔪(A)) ×_{Spec κ(y)} X_y`, which is proper over
`Spec(Gr_𝔪(A))` as a base change of the proper `X_y ⟶ Spec κ(y)`. The identification of that
fibre product with `Spec_{X_y}((algebraPullback g).obj Gr~)` is
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`; the closed immersion is
`Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom` applied to a
locally surjective `ψ`. So `ψ` is the datum, and for `𝓑 = g^* Gr~` it is the one built here.

## Main definitions

* `Stacks.GradedComap.unitPieceComparison`: the unit of `g^* ⊣ g_*` read as a degreewise
  comparison `𝓐ₙ ⟶ g_*(g^* 𝓐ₙ)` in the sense of `Stacks.GradedComap.PieceComparison`. Its two
  laws are exactly the identification of the pulled-back multiplication and unit,
  `Stacks.Conormal.gradedPullback_mul_pullbackSection` and
  `Stacks.Conormal.gradedPullback_one_eval`; nothing is reproved.

## Main results

* `Stacks.GradedComap.mem_image_unitPieceComparison`: every homogeneous section of `g^*(𝓐ₙ)` over
  an affine open of `Z` is in the image of `ψ`.
* `Stacks.GradedComap.isLocallySurjective_unitPullbackHom`: **`ψ` is locally surjective.**

## Implementation notes

The generation argument is not a sheafification argument and uses nothing about `𝓐` beyond the
quasi-coherence of its pieces. Over a compatible pair of affine opens the sections of a
quasi-coherent module's pullback are the base change of its sections
(`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`), so they are **spanned** over
`Γ(Z, V)` by the pullbacks of the sections over the affine open downstairs
(`AlgebraicGeometry.span_pullbackSection_eq_top`); the base `Y` being affine, `⊤` serves as that
open. The homogeneous sections whose inclusion into the ungraded realization lies in the image of
`ψ` form a `Γ(Z, V)`-submodule — `Stacks.GradedComap.mem_image_ungradedIncl_zero`, `_add` and
`_smul` — and contain those generators by
`Stacks.GradedComap.mem_image_app_restrict`, so `Submodule.span_induction` closes it.

No `@[stacks]` attribute is attached: comparing the two pullbacks is a step inside the base change
of [Stacks, Tag 0897], not a numbered result of the source. In particular this is *not*
[Stacks, Tag 01LX], which is the identification of the base change with the relative spectrum of
the algebra pullback and is already registered on
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GradedComap

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  (𝓐 : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)

/-- **The unit of `g^* ⊣ g_*` as a degreewise comparison of `𝓐` with its degreewise pullback.**
Multiplicativity is `Stacks.Conormal.gradedPullback_mul_pullbackSection` and unitality is
`Stacks.Conormal.gradedPullback_one_eval`, read through
`Stacks.Conormal.pullbackSection_self`, which says that over the whole preimage of an open the
pullback of a section is the unit's value on it. -/
def unitPieceComparison : PieceComparison g 𝓐 (Stacks.Conormal.gradedPullback g 𝓐) where
  app n := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app (𝓐.piece n)
  map_mul i j V x y :=
    ((Stacks.Conormal.pullbackSection_self g (𝓐.piece (i + j)) V
          ((𝓐.mul i j).app (op V) x y)).symm.trans
        (Stacks.Conormal.gradedPullback_mul_pullbackSection g 𝓐 i j V x y).symm).trans
      (congrArg₂ (fun a b => ((Stacks.Conormal.gradedPullback g 𝓐).mul i j).app
          (op (g ⁻¹ᵁ V)) a b)
        (Stacks.Conormal.pullbackSection_self g (𝓐.piece i) V x)
        (Stacks.Conormal.pullbackSection_self g (𝓐.piece j) V y))
  map_one V :=
    ((Stacks.Conormal.gradedPullback_one_eval g 𝓐 V).trans
      (Stacks.Conormal.pullbackSection_self g (𝓐.piece 0) V (𝓐.one.eval (op V)))).symm

section Affine

variable (hA : ∀ (i j : ℤ) (W : (Opens ↥Y)ᵒᵖ) (a : (𝓐.piece i).val.obj W)
    (b : (𝓐.piece j).val.obj W), HEq ((𝓐.mul i j).app W a b) ((𝓐.mul j i).app W b a))
  [IsAffine Y] [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf Y 𝓐 hA)]

/-- **Every homogeneous section of `g^*(𝓐ₙ)` over an affine open of `Z` is in the image of
`ψ`.** Over the affine open `V` of `Z` and the affine open `⊤` of `Y` the sections of `g^*(𝓐ₙ)`
are spanned over `Γ(Z, V)` by the pullbacks of the global sections of `𝓐ₙ`
(`AlgebraicGeometry.span_pullbackSection_eq_top`), those generators are in the image
(`Stacks.GradedComap.mem_image_app_restrict`), and the sections whose inclusion is in the image
form a `Γ(Z, V)`-submodule. -/
theorem mem_image_unitPieceComparison (hqc : ∀ n : ℤ, (𝓐.piece n).IsQuasicoherent)
    {V : Z.Opens} (hV : IsAffineOpen V) (n : ℤ)
    (x : ((Stacks.Conormal.gradedPullback g 𝓐).piece n).val.obj (op V)) :
    (Stacks.Conormal.gradedPullback g 𝓐).ungradedIncl n x ∈
      image g 𝓐 (Stacks.Conormal.gradedPullback g 𝓐) (unitPieceComparison g 𝓐) hA
        (Stacks.Conormal.gradedPullback_mul_comm g 𝓐 hA) V := by
  have := hqc n
  have hVU : V ≤ g ⁻¹ᵁ (⊤ : Y.Opens) := le_top
  have hx : (show Γ((Scheme.Modules.pullback g).obj (𝓐.piece n), V) from x) ∈
      Submodule.span Γ(Z, V)
        (Set.range fun a : Γ(𝓐.piece n, (⊤ : Y.Opens)) =>
          pullbackSectionHom g (𝓐.piece n) ⊤ V hVU a) :=
    (span_pullbackSection_eq_top g (𝓐.piece n) (isAffineOpen_top Y) hV hVU).ge Submodule.mem_top
  refine Submodule.span_induction
    (p := fun (z : Γ((Scheme.Modules.pullback g).obj (𝓐.piece n), V)) _ =>
      (Stacks.Conormal.gradedPullback g 𝓐).ungradedIncl n z ∈
        image g 𝓐 (Stacks.Conormal.gradedPullback g 𝓐) (unitPieceComparison g 𝓐) hA
          (Stacks.Conormal.gradedPullback_mul_comm g 𝓐 hA) V)
    ?_ ?_ ?_ ?_ hx
  · rintro - ⟨a, rfl⟩
    exact mem_image_app_restrict g 𝓐 (Stacks.Conormal.gradedPullback g 𝓐)
      (unitPieceComparison g 𝓐) hA (Stacks.Conormal.gradedPullback_mul_comm g 𝓐 hA) hVU n a
  · exact mem_image_ungradedIncl_zero g 𝓐 (Stacks.Conormal.gradedPullback g 𝓐)
      (unitPieceComparison g 𝓐) hA (Stacks.Conormal.gradedPullback_mul_comm g 𝓐 hA) n V
  · intro y z _ _ hy hz
    exact mem_image_ungradedIncl_add g 𝓐 (Stacks.Conormal.gradedPullback g 𝓐)
      (unitPieceComparison g 𝓐) hA (Stacks.Conormal.gradedPullback_mul_comm g 𝓐 hA) n V hy hz
  · intro r y _ hy
    exact mem_image_ungradedIncl_smul g 𝓐 (Stacks.Conormal.gradedPullback g 𝓐)
      (unitPieceComparison g 𝓐) hA (Stacks.Conormal.gradedPullback_mul_comm g 𝓐 hA) n V
      (show Z.ringCatSheaf.obj.obj (op V) from r) hy

/-- **`ψ : (algebraPullback g).obj (⨁ₙ 𝓐ₙ) ⟶ ⨁ₙ g^*(𝓐ₙ) is locally surjective.** This is the
comparison of the two pullbacks of a graded algebra sheaf, in the strength
[Stacks, Tag 01S8] needs: by
`Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom` it exhibits
`Spec_Z(⨁ₙ g^*(𝓐ₙ))` as a closed subscheme of `Spec_Z((algebraPullback g).obj (⨁ₙ 𝓐ₙ))`, which
[Stacks, Tag 01LX] part (2) identifies with `Spec_Y(⨁ₙ 𝓐ₙ) ×_Y Z`. -/
theorem isLocallySurjective_unitPullbackHom (hqc : ∀ n : ℤ, (𝓐.piece n).IsQuasicoherent) :
    CategoryTheory.Sheaf.IsLocallySurjective
      (pullbackHom g 𝓐 (Stacks.Conormal.gradedPullback g 𝓐) (unitPieceComparison g 𝓐) hA
        (Stacks.Conormal.gradedPullback_mul_comm g 𝓐 hA)).right :=
  isLocallySurjective_pullbackHom g 𝓐 (Stacks.Conormal.gradedPullback g 𝓐)
    (unitPieceComparison g 𝓐) hA (Stacks.Conormal.gradedPullback_mul_comm g 𝓐 hA)
    fun hV n x => mem_image_unitPieceComparison g 𝓐 hA hqc hV n x

end Affine

end Stacks.GradedComap

end
