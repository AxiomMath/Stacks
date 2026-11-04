module

public import StacksFrontier.Cotangent.PolynomialResolution
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmallOfModules
public import StacksFrontier.RingTheory.Noetherian.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the cohomology of derived lower shriek

Let `A` be a Noetherian ring, let `A → B` be a finite type ring map and let `π`, `B̲` be as in
Tag 08PR: `C_{B/A}` is the site of polynomial `A`-algebras augmented to `B`, `B̲` is the constant
sheaf of rings `B` on it, and `π` is the morphism to the point. Tag 08PY says that if `ℱ` is a
`B̲`-module whose value `ℱ(P, α)` is a finite `B`-module for every augmentation whose `P` is a
finite type polynomial algebra, then every cohomology module of `Lπ_!(ℱ)` is a finite
`B`-module.

The proof is the source's: Tag 08PX supplies a resolution of `B` over `A` all of whose terms are
finite type polynomial algebras, the module half of Tag 08PS computes `L_nπ_!(ℱ)` as the homology
of the Moore complex of `ℱ(P_•, ε)`, every term of that complex is finite over `B` by hypothesis,
and `B` is Noetherian because it is of finite type over `A`.

## Main results

* `CommAlgCat.smallResolutionAlgebraAlgEquiv`: the algebra underlying the degree `m` term of the
  cosimplicial object of a bounded resolution, read in the small model of the restricted site, is
  the degree `m` term of the resolution.
* `CommAlgCat.finite_moduleLeftDerivedPointLowerShriek`: **Tag 08PY.**

## Implementation notes

**Which site, and what the cardinal bound is doing.** The identification of `Lπ_!` with the Moore
complex of `ℱ(P_•, ε)` is available at the small model of the footnote-restricted site and not at
the site of Tag 08PR itself, which is large; this is the restriction recorded in the first
implementation note of `StacksFrontier/Cotangent/ResolutionPointCriterionSmall.lean` and it is
inherited here. The footnote's cardinal bound is left as a parameter `κ`, as it is there, and the
only thing asked of it is that it be infinite: the resolution of Tag 08PX has finite type terms,
so each of them is a polynomial algebra on finitely many variables and lies in the site as soon
as `ℵ₀ ≤ κ`. The source's own choice `κ = #B` does not have this property when `B` is finite,
which is the same mismatch the standard resolution exhibits there.

**The hypothesis on `ℱ`.** The source quantifies over the augmentations `α : P = A[x_1, …, x_n] →
B`, that is over the objects of the site whose underlying algebra is of finite type over `A`;
`CommAlgCat.smallBoundedPolynomialAlgebra` names that algebra, and the hypothesis is stated for
every object of the site satisfying `Algebra.FiniteType`. No object is excluded and the
conclusion is asserted in every degree.

**Why the terms of the resolution are recognised as finite type.** The resolution of Tag 08PX
lives in `CommAlgCat.{u} A`; passing to the small model replaces each term by an isomorphic
polynomial augmentation chosen by `CommAlgCat.essSurj_smallBoundedPolynomialAugmentationι`, and
nothing pins down its set of variables. `CommAlgCat.smallResolutionAlgebraAlgEquiv` extracts the
`A`-algebra isomorphism from `CommAlgCat.smallResolutionCosimplicialObjectι`, the comparison of
the small model with the unrestricted site, and finiteness of type is transported along it.

## References

* [Stacks Project, Tag 08PY](https://stacks.math.columbia.edu/tag/08PY)
* [Stacks Project, Tag 08PX](https://stacks.math.columbia.edu/tag/08PX)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.ChaoticSite.ModuleValued

universe u

namespace CommAlgCat

/-- The homology of a complex of modules over a Noetherian ring is finite in a degree in which
the complex itself is finite: the cycles are a submodule of a finite module over a Noetherian
ring, and the homology is a quotient of the cycles. -/
private lemma finite_homology_of_finite_X {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) [Module.Finite R (K.X n)] :
    Module.Finite R (K.homology n) := by
  have : IsNoetherian R (K.X n) := isNoetherian_of_isNoetherianRing_of_finite R (K.X n)
  have : Module.Finite R (K.cycles n) :=
    .of_injective (K.iCycles n).hom ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact .of_surjective (K.homologyπ n).hom ((ModuleCat.epi_iff_surjective _).mp inferInstance)

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-- The polynomial `A`-algebra underlying an object of the small model of the restricted site
`C_{B/A}`. -/
abbrev smallBoundedPolynomialAlgebra (W : smallBoundedPolynomialSite A B κ) :
    CommAlgCat.{u} A :=
  ((smallBoundedPolynomialAugmentationι A B κ).obj W.unop).obj.left

section Resolution

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B) (κ : Cardinal.{u})
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- The algebra underlying the degree `m` term of the cosimplicial object of a bounded
resolution, read in the small model of the restricted site, is the degree `m` term of the
resolution: the small model is reached by an isomorphism of cosimplicial objects of the
unrestricted site. -/
def smallResolutionAlgebraAlgEquiv (m : ℕ) :
    (smallBoundedPolynomialAlgebra A B κ
        ((smallResolutionCosimplicialObject ε κ hPκ).obj ⦋m⦌) : Type u) ≃ₐ[A]
      (P.obj (op ⦋m⦌) : Type u) :=
  CommAlgCat.algEquivOfIso
    ((ObjectProperty.ι (IsPolynomialAlgebraOver A B) ⋙ Over.forget B).mapIso
      (((smallResolutionCosimplicialObjectι ε κ hPκ).app ⦋m⦌).unop.symm))

end Resolution

/-! ### Tag 08PY -/

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (B : CommAlgCat.{u} A)
  [Algebra.FiniteType A (B : Type u)]

/-- **Stacks 08PY.** Let `A` be a Noetherian ring, let `A → B` be a finite type ring map and let
`π`, `B̲` be as in Tag 08PR. If `ℱ` is a `B̲`-module such that `ℱ(P, α)` is a finite `B`-module
for every augmentation `α : P → B` whose `P` is of finite type over `A`, then every cohomology
module of `Lπ_!(ℱ)` is a finite `B`-module.

By Tag 08PX there is a resolution `ε : P_• ⟶ B` of `B` over `A` all of whose terms are
*finite type* polynomial algebras, and by the module half of Tag 08PS the sections at the point
of `L_nπ_!(ℱ)` are the degree `n` homology of the Moore complex of `ℱ(P_•, ε)`. Each term of that
complex is `ℱ` evaluated at a finite type polynomial augmentation, hence a finite `B`-module, and
`B` is Noetherian because it is of finite type over the Noetherian ring `A`; so each homology
module is a subquotient of a finite module over a Noetherian ring. -/
@[stacks 08PY "read at the small model of the footnote-restricted site, for the reason \
  recorded for Tag 08PS in \
  `StacksFrontier/Cotangent/ResolutionPointCriterionSmallOfModules.lean`; the cardinal bound `κ` \
  of the footnote is a parameter, required only to be infinite so that the finite type \
  resolution of Tag 08PX is an object of the site"]
theorem finite_moduleLeftDerivedPointLowerShriek (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0.{u} ≤ κ)
    (ℱ : Sheaf (GrothendieckTopology.trivial (smallBoundedPolynomialSite A B κ))
      (ModuleCat.{u} (B : Type u)))
    (hℱ : ∀ W : smallBoundedPolynomialSite A B κ,
      Algebra.FiniteType A (smallBoundedPolynomialAlgebra A B κ W : Type u) →
        Module.Finite (B : Type u) (ℱ.obj.obj (op W)))
    (n : ℕ) :
    Module.Finite (B : Type u)
      (((modulePointLowerShriek (smallBoundedPolynomialSite A B κ)
            (B : Type u)).leftDerived n ⋙
          Stacks.ChaoticSite.pointSections.{u, u + 1, u}
            (ModuleCat.{u} (B : Type u))).obj ℱ) := by
  classical
  have hBnoeth : IsNoetherianRing (B : Type u) :=
    Algebra.FiniteType.isNoetherianRing A (B : Type u)
  obtain ⟨P, ε, hpoly, hkan⟩ :=
    exists_trivialKanFibration_from_finiteType_polynomial_simplicialAlgebra
      (A := A) (B := (B : Type u))
  have hPκ : ∀ m : SimplexCategoryᵒᵖ, IsPolynomialAlgebraBelow A κ (P.obj m) := by
    intro m
    obtain ⟨j, rfl⟩ : ∃ j, m = op ⦋j⦌ := ⟨m.unop.len, by rw [SimplexCategory.mk_len]⟩
    obtain ⟨k, ⟨e⟩⟩ := hpoly j
    refine ⟨ULift.{u, 0} (Fin k), ?_,
      ⟨(MvPolynomial.renameEquiv A Equiv.ulift).trans e.symm⟩⟩
    rw [show Cardinal.mk (ULift.{u, 0} (Fin k)) = (k : Cardinal.{u}) by simp]
    exact Cardinal.natCast_le_aleph0.trans hκ
  have hX : Module.Finite (B : Type u)
      (((moduleCosimplicialMooreComplex
        (smallResolutionCosimplicialObject ε κ hPκ)).obj ℱ.obj).X n) := by
    obtain ⟨k, ⟨e⟩⟩ := hpoly n
    have : Algebra.FiniteType A (P.obj (op ⦋n⦌) : Type u) := .equiv inferInstance e.symm
    exact hℱ _ (.equiv this (smallResolutionAlgebraAlgEquiv ε κ hPκ n).symm)
  have hhom : Module.Finite (B : Type u)
      (((moduleCosimplicialMooreComplex
        (smallResolutionCosimplicialObject ε κ hPκ)).obj ℱ.obj).homology n) :=
    finite_homology_of_finite_X _ n
  exact hhom.equiv
    ((smallResolutionModuleLeftDerivedLowerShriekNatIso ε κ hPκ hkan n).app ℱ).symm.toLinearEquiv

end CommAlgCat

end
