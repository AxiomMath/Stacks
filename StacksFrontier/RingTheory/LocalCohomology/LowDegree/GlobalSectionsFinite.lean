module

public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.Finiteness
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.GlobalSectionsChoice

/-!
# The module of global sections is an admissible choice of extension

Let `I` be a finitely generated ideal of a commutative ring `A`, let `U = Spec A \ V(I)` and let
`F` be a quasi-coherent module on `U` which is the restriction of `M̃` for some finite `A`-module
`M`.  If `H¹_{V(I)}(M)` is a finite `A`-module — one of the equivalent finiteness conditions of
clause (3) of [Stacks, Tag 0BK0] in degree zero — then the particular choice `N = Γ(U, F)` of
extension is itself admissible: `N` is a finite `A`-module whose associated sheaf restricts to
`F`, and it has no local cohomology with support in `V(I)` in degrees zero and one.

This is clause (4) of that tag.  The three statements it asserts about `N` are proved separately
in this subdirectory and are only combined here:

* finiteness of `N` is `Stacks.LocalCohomology.finite_complementGlobalSections_iff_finite_`
  `localCohomologyModule`, the degree-zero half of clause (3)'s equivalence of (b) and (c), read
  from right to left: the four-term sequence of clause (2) exhibits `Γ(U, F)` as an extension of
  `H¹_{V(I)}(M)` by a quotient of `M`;
* that `F` is the restriction of `Ñ` is
  `Stacks.LocalCohomology.iso_restrict_tilde_globalSectionsModule`, the counit of the
  tilde–Gamma adjunction on the affine scheme `Spec A` composed with the counit of the
  restriction–pushforward adjunction along the inclusion of `U`;
* the two vanishing statements are `Stacks.LocalCohomology.isZero_localCohomology_zero_`
  `globalSectionsModule` and `..._one_globalSectionsModule`, the degeneration of the four-term
  sequence at this choice of extension, where the restriction map `N ⟶ Γ(U, F)` is the identity
  and therefore both outer terms of the sequence vanish.

## Main results

* `Stacks.LocalCohomology.finite_iso_restrict_and_isZero_localCohomology_globalSectionsModule` —
  **[Stacks, Tag 0BK0] (4).**

## Implementation notes

Finite generation of `I` replaces the tag's hypothesis that `A` be Noetherian, which implies it
by `Ideal.fg_of_isNoetherianRing`, and quasi-coherence of `F` replaces the tag's coherence; both
are generalisations.  The hypothesis is clause (3)'s condition (c) in degree zero, finiteness of
`H¹_{V(I)}(M)`, stated for the extension `M` that clause (1) of the tag produces; the equivalence
of that condition with (a) and (b) is clause (3) and is registered elsewhere.

Local cohomology with support in `V(I)` is the coreflection model of [Stacks, Tag 0A6Q], as in
the four-term sequence of clause (2); no model of the derived category is pinned here, because
the model is part of the *value* of `Stacks.LocalCohomology.localCohomologyModule` and not of its
type.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- **[Stacks, Tag 0BK0] (4).** Let `I` be a finitely generated ideal of `A`, let
`U = Spec A \ V(I)`, let `F` be a quasi-coherent `𝒪_U`-module and let `M` be a finite `A`-module
with `F ≅ M̃|_U`.  If the equivalent conditions of clause (3) hold in degree zero, in the form
`H¹_{V(I)}(M)` finite, then `N = Γ(U, F)` is itself an admissible choice for `M`: it is a finite
`A`-module, `F` is the restriction of `Ñ` to `U`, and `H⁰_{V(I)}(N) = H¹_{V(I)}(N) = 0`.

Finiteness of `N` comes from the four-term sequence of clause (2), which presents `Γ(U, F)` as an
extension of `H¹_{V(I)}(M)` by a quotient of `M`.  The isomorphism `F ≅ Ñ|_U` is the counit of
the tilde–Gamma adjunction, and the two vanishing statements are the degeneration of the
four-term sequence at the extension `N`, whose restriction map `N ⟶ Γ(U, F)` is the identity. -/
@[stacks 0BK0 "(4)"]
theorem finite_iso_restrict_and_isZero_localCohomology_globalSectionsModule
    (F : (complementZeroLocus A I : Scheme).Modules) [F.IsQuasicoherent]
    (M : ModuleCat.{u} A) [Module.Finite A M] (e : F ≅ complementTilde A I M)
    (hfin : Module.Finite A (localCohomologyModule A I hI M 1)) :
    Module.Finite A (complementGlobalSections A I F) ∧
      Nonempty (F ≅ complementTilde A I (complementGlobalSections A I F)) ∧
      IsZero (localCohomologyModule A I hI (complementGlobalSections A I F) 0) ∧
      IsZero (localCohomologyModule A I hI (complementGlobalSections A I F) 1) :=
  ⟨(finite_complementGlobalSections_iff_finite_localCohomologyModule.{u, u} A I hI M F e).2 hfin,
    iso_restrict_tilde_globalSectionsModule A I hI F,
    isZero_localCohomology_zero_globalSectionsModule A I hI F,
    isZero_localCohomology_one_globalSectionsModule A I hI F⟩

end Stacks.LocalCohomology

end
