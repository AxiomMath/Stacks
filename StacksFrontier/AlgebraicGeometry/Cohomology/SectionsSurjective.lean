module

public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections

/-!
# Sections are surjective where the first cohomology of the kernel vanishes

Let `0 ⟶ F ⟶ G ⟶ H ⟶ 0` be a short exact sequence of `𝒪_X`-modules on a scheme `X` and let `U`
be an open subscheme. The long exact sequence of the right derived functors of `Γ(U, -)` begins

`0 ⟶ Γ(U, F) ⟶ Γ(U, G) ⟶ Γ(U, H) ⟶ H¹(U, F) ⟶ ⋯`,

so `Γ(U, G) ⟶ Γ(U, H)` is surjective as soon as `H¹(U, F)` vanishes. This is the mechanism by
which a vanishing theorem on a curve makes functions extend from one infinitesimal thickening to
the next, as in [Stacks, Tag 0C2K].

Two inputs are combined. The long exact sequence in the *object* variable of a fixed additive
functor is `Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅`; it gives
the three-term window `R⁰Q G ⟶ R⁰Q H ⟶ R¹Q F`, whose last map lands in a zero object and
therefore vanishes, so the first is an epimorphism. The identification of `R⁰Q` with `Q` is
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, available because sections over an open are
left exact (`Stacks.Cohomology.preservesFiniteLimits_sectionsFunctor`).

## Main results

* `Stacks.Cohomology.epi_map_of_isZero_rightDerived_one` — for a left exact additive functor `Q`
  and a short exact sequence with `R¹Q X₁ = 0`, the map `Q X₂ ⟶ Q X₃` is an epimorphism.
* `Stacks.Cohomology.shortExact_map_of_isZero_rightDerived_one` — the same hypotheses make the
  whole image sequence short exact, left exactness supplying the other two thirds.
* `Stacks.Cohomology.surjective_sections_of_isZero_firstCohomology` — the same for sections of
  `𝒪_X`-modules over an open subscheme, read as surjectivity of a map of modules.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v v' u u'

namespace Stacks.Cohomology

/-! ### The categorical statement -/

variable {B : Type u} {D : Type u'} [Category.{v} B] [Category.{v'} D] [Abelian B] [Abelian D]
  [EnoughInjectives B] (Q : B ⥤ D) [Q.Additive] [PreservesFiniteLimits Q]

/-- **A left exact functor is right exact at a short exact sequence whose first term has
vanishing `R¹`.** For `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` short exact with `R¹Q X₁ = 0`, the map
`Q X₂ ⟶ Q X₃` is an epimorphism. -/
theorem epi_map_of_isZero_rightDerived_one {S : ShortComplex B} (hS : S.ShortExact)
    (h : IsZero ((Q.rightDerived 1).obj S.X₁)) : Epi (Q.map S.g) := by
  obtain ⟨δ, -, hex⟩ := RightDerivedDelta.exists_delta_exact_composableArrows₅ hS Q
  have he : Epi ((Q.rightDerived 0).map S.g) := ((hex 0).exact 1).epi_f (h.eq_of_tgt _ _)
  have hnat := Q.rightDerivedZeroIsoSelf.hom.naturality S.g
  have heq : Q.map S.g = inv (Q.rightDerivedZeroIsoSelf.hom.app S.X₂) ≫
      (Q.rightDerived 0).map S.g ≫ Q.rightDerivedZeroIsoSelf.hom.app S.X₃ := by
    rw [hnat, IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

/-- **A left exact functor carries a short exact sequence whose first term has vanishing `R¹` to a
short exact sequence.** Left exactness gives exactness of the image and monomorphy of its first
map (`CategoryTheory.Functor.preservesFiniteLimits_tfae`); the vanishing of `R¹Q X₁` gives
epimorphy of its second (`Stacks.Cohomology.epi_map_of_isZero_rightDerived_one`).

This is the mechanism by which a direct image, or any other left exact functor, keeps a
filtration sequence exact; the vanishing hypothesis is the only input beyond left exactness, and
nothing about the functor's provenance is used, so a direct image along a bare continuous map is
as admissible here as one along a morphism of schemes. -/
theorem shortExact_map_of_isZero_rightDerived_one {S : ShortComplex B} (hS : S.ShortExact)
    (h : IsZero ((Q.rightDerived 1).obj S.X₁)) : (S.map Q).ShortExact := by
  have htfae : ∀ T : ShortComplex B, T.ShortExact → (T.map Q).Exact ∧ Mono (Q.map T.f) :=
    ((Functor.preservesFiniteLimits_tfae Q).out 1 4).mpr ‹PreservesFiniteLimits Q›
  obtain ⟨hex, hmono⟩ := htfae S hS
  have hepi : Epi (Q.map S.g) := epi_map_of_isZero_rightDerived_one Q hS h
  have : Mono (S.map Q).f := hmono
  have : Epi (S.map Q).g := hepi
  exact ShortComplex.ShortExact.mk' hex inferInstance inferInstance

/-! ### Sections of modules on a scheme -/

/-- **Sections over an open are surjective where the first cohomology of the kernel vanishes.**
For a short exact sequence `0 ⟶ F ⟶ G ⟶ H ⟶ 0` of `𝒪_X`-modules with `H¹(U, F) = 0`, every
section of `H` over `U` lifts to a section of `G` over `U`. -/
theorem surjective_sections_of_isZero_firstCohomology (X : Scheme.{u}) (U : X.Opens)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : IsZero (((sectionsFunctor X U).rightDerived 1).obj S.X₁)) :
    Function.Surjective fun m : Γ(S.X₂, U) => S.g.app U m :=
  (ModuleCat.epi_iff_surjective _).1 (epi_map_of_isZero_rightDerived_one _ hS h)

end Stacks.Cohomology

end
