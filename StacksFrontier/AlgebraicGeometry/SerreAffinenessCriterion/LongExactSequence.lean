module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Discharge
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic

/-!
# The long exact cohomology sequence of a scheme, read off on `H⁰` and `H¹`

The repository's sheaf cohomology `Hgroup R U n F` (the `Hgroup` of [Stacks, Tag 01E3]) is the
`n`-th right derived functor of `Γ(U, -)`, and
`Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived`
(`StacksFrontier/AlgebraicGeometry/SectionsExact/Discharge.lean`) already exhibits it as the
positive-degree part of a cohomological δ-functor [Stacks, Tag 010Q] whose degree-zero part is
`Γ(U, -)`. In other words **the long exact cohomology sequence is available at this pin**, for an
arbitrary open of an arbitrary scheme.

This file extracts the two consequences of it that the affineness criteria use, specialised to a
scheme so that no instance argument is left for the caller to discharge:

* a short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` with `H¹(U, ℱ₁) = 0` has `Γ(U, ℱ₂) → Γ(U, ℱ₃)`
  surjective — exactness of `Γ(U, ℱ₂) → Γ(U, ℱ₃) → H¹(U, ℱ₁)`;
* `Hⁿ(U, ℱ₁) = 0` and `Hⁿ(U, ℱ₃) = 0` force `Hⁿ(U, ℱ₂) = 0` — exactness of
  `Hⁿ(U, ℱ₁) → Hⁿ(U, ℱ₂) → Hⁿ(U, ℱ₃)`.

Neither needs quasi-coherence, affineness, or any hypothesis on `X` or `U`.

## Main results

* `Stacks.SerreAffinenessCriterion.epi_secF_map_g_of_isZero_hgroup_one`
* `Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one`: the same read on elements.
* `Stacks.SerreAffinenessCriterion.isZero_hgroup_of_shortExact`

The file closes with an `example` re-deriving
`Stacks.SectionEpiAffine.epi_secF_map_of_isAffineOpen` from the first of these together with
[Stacks, Tag 01XB]. That theorem is proved there by the Čech element chase of [Stacks, Tag 01EU],
sharing no step with the derived-functor route, so the `example` is a machine-checked cross-check
on the strength of what is extracted here rather than a new statement.

## What this does and does not do for [Stacks, Tag 01YQ]

The module documentation of
`StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.Chevalley` names two
declarations as all that stands between the tag and a proof, and presents both as blocked on
cohomology. **The long exact sequence is not the blocked part**: each of the two is now one
application of `epi_secF_map_g_of_isZero_hgroup_one`, respectively of that together with
`isZero_hgroup_of_shortExact` for the filtration, away from its stated hypothesis. What is
genuinely absent is the *vanishing* those applications consume — `H¹(X, ℱ) = 0` on an `X` that is
not known to be affine, which in the source is the dévissage [Stacks, Tag 01YM] / [Stacks,
Tag 01YO], and which carries no attribute anywhere in this repository.

Two further remarks:

* With the vanishing available for *every* quasi-coherent module — which is what the dévissage of
  [Stacks, Tag 01YQ] supplies, and is the hypothesis of the second form [Stacks, Tag 01XG] of
  Serre's criterion rather than the first — the filtration of `ker(𝒪_X^{⊕n} → 𝒪_X)` by its
  intersections with the partial sums, which the source needs and which `Chevalley.lean` records
  as part of the remaining work, is **not needed at all**: the kernel of a map of quasi-coherent
  modules is quasi-coherent (`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`), so the
  hypothesis applies to it directly.
* The remaining obstacle in that step is then not cohomological but a book-keeping identification:
  `Γ(U, SheafOfModules.free I)` for a finite `I` as the direct sum of copies of `Γ(U, 𝒪_X)`, so
  that a lift of `1` along `𝒪_X^{⊕n} → 𝒪_X` can be read as a relation `∑ aᵢrᵢ = 1`. Mathlib has
  `SheafOfModules.free` and `SheafOfModules.freeHomEquiv` but, at this pin, no such computation of
  its sections.

## Implementation notes

**`[HasDerivedCategory _]` is a local instance and does not appear in any statement.** The
δ-functor of `Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives` is built through
the bounded-below derived category and therefore asks for `HasDerivedCategory` on both sides;
`HasDerivedCategory.standard` supplies it, and is deliberately not a global instance upstream
(it would compete with other models). Since `Hgroup` and `secF` mention no derived category, the
statements below are independent of the choice, and `attribute [local instance]` confines it to
this file.

**The identification of the δ-functor's parts with `Hgroup` is definitional.** For `D` the right
derived δ-functor of `Γ(U, -)` one has `D.functor n = (secF R U).rightDerived n` by `rfl`
(`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor`), and
`Hfunctor R U n` is a reducible abbreviation for the same functor, so `(D.functor n).obj F` *is*
`Hgroup R U n F`. No transport is needed in positive degrees. In degree zero the two differ —
`D.functor 0` is `R⁰Γ(U, -)` and not `Γ(U, -)` — and the comparison is the `isoZero` field of
`Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor`, i.e.
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, whose left-exactness side condition is
`Stacks.SectionsExact.preservesFiniteLimits_secF`. That is why the first result below is stated
about `secF` rather than about `Hgroup _ _ 0`: it is the form its consumers need.

**No `stacks` attribute is attached.** These are two readings of the exactness axioms of
[Stacks, Tag 010Q], which is already tagged on
`CategoryTheory.DeltaFunctor` (`StacksCore/CategoryTheory/Abelian/DeltaFunctor/Basic.lean`);
they are
not themselves numbered results of the source.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 01XF](https://stacks.math.columbia.edu/tag/01XF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.CohomologyVanishing

universe u

namespace Stacks.SerreAffinenessCriterion

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u}) (U : X.Opens) {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)}

/-- **The long exact cohomology sequence over an open `U` of a scheme, as data**: the right
derived δ-functor of `Γ(U, -)` on `𝒪_X`-modules. Its degree-`n + 1` part *is* `Hⁿ⁺¹(U, -)`, by
`rfl`; its degree-zero part is `R⁰Γ(U, -)`, compared to `Γ(U, -)` by the `isoZero` field of
`Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived`.

Kept as an `abbrev` rather than introduced by `set` inside a proof: a `let`-bound δ-functor makes
`(D.functor n).Additive` — hence `PreservesZeroMorphisms`, hence `ShortComplex.map` — impossible
to synthesize. -/
noncomputable abbrev cohomologyDeltaFunctor :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (secF X.ringCatSheaf U)

/-- **`Γ(U, -)` is surjective on the last term of a short exact sequence whose first term has
vanishing `H¹`.** This is exactness of `Γ(U, ℱ₂) → Γ(U, ℱ₃) → H¹(U, ℱ₁)` in the long exact
cohomology sequence: the connecting map is zero because its target is, so `Γ(U, ℱ₃)` is the image
of `Γ(U, ℱ₂)`.

No hypothesis on `X`, on `U`, or on the quasi-coherence of the sheaves. -/
theorem epi_secF_map_g_of_isZero_hgroup_one (hS : S.ShortExact)
    (h : IsZero (Hgroup X.ringCatSheaf U 1 S.X₁)) :
    Epi ((secF X.ringCatSheaf U).map S.g) := by
  have hD := Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived X.ringCatSheaf U
  have hδ : (cohomologyDeltaFunctor X U).δ hS 0 = 0 := h.eq_of_tgt _ _
  have hepi : Epi (((cohomologyDeltaFunctor X U).functor 0).map S.g) :=
    (ShortComplex.exact_iff_epi ((cohomologyDeltaFunctor X U).scδ₁ hS 0) hδ).1
      ((cohomologyDeltaFunctor X U).exact_δ₁ hS 0)
  have hnat := hD.isoZero.hom.naturality S.g
  have : IsIso (hD.isoZero.hom.app S.X₃) :=
    inferInstanceAs (IsIso (hD.isoZero.app S.X₃).hom)
  have hcomp : Epi (((cohomologyDeltaFunctor X U).functor 0).map S.g ≫
      hD.isoZero.hom.app S.X₃) := epi_comp _ _
  rw [hnat] at hcomp
  exact epi_of_epi (hD.isoZero.hom.app S.X₂) _

/-- **`epi_secF_map_g_of_isZero_hgroup_one` read on elements.** If `H¹(U, ℱ₁) = 0` then every
section of `ℱ₃` over `U` lifts to a section of `ℱ₂` over `U`. -/
theorem surjective_app_of_isZero_hgroup_one (hS : S.ShortExact)
    (h : IsZero (Hgroup X.ringCatSheaf U 1 S.X₁)) :
    Function.Surjective (S.g.val.app (op U)) :=
  (AddCommGrpCat.epi_iff_surjective _).1 (epi_secF_map_g_of_isZero_hgroup_one X U hS h)

/-- **Vanishing of `Hⁿ(U, -)` on the outer terms of a short exact sequence forces it in the
middle.** This is exactness of `Hⁿ(U, ℱ₁) → Hⁿ(U, ℱ₂) → Hⁿ(U, ℱ₃)`: the first map is zero because
its source is, so the second is a monomorphism, and a monomorphism into a zero object has zero
source.

This is the step that turns a filtration of a sheaf with `Hⁿ`-acyclic quotients into an
`Hⁿ`-acyclic sheaf. -/
theorem isZero_hgroup_of_shortExact (hS : S.ShortExact) (n : ℕ)
    (h₁ : IsZero (Hgroup X.ringCatSheaf U n S.X₁))
    (h₃ : IsZero (Hgroup X.ringCatSheaf U n S.X₃)) :
    IsZero (Hgroup X.ringCatSheaf U n S.X₂) := by
  have hadd : ((cohomologyDeltaFunctor X U).functor n).Additive :=
    CategoryTheory.DeltaFunctor.additive (cohomologyDeltaFunctor X U) n
  have hpz : ((cohomologyDeltaFunctor X U).functor n).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  have hf : ((cohomologyDeltaFunctor X U).functor n).map S.f = 0 := h₁.eq_of_src _ _
  have hmono : Mono (((cohomologyDeltaFunctor X U).functor n).map S.g) :=
    (ShortComplex.exact_iff_mono (S.map ((cohomologyDeltaFunctor X U).functor n)) hf).1
      ((cohomologyDeltaFunctor X U).exact_map hS n)
  have hg : ((cohomologyDeltaFunctor X U).functor n).map S.g = 0 := h₃.eq_of_tgt _ _
  have key : IsZero (((cohomologyDeltaFunctor X U).functor n).obj S.X₂) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    have h0 : 𝟙 (((cohomologyDeltaFunctor X U).functor n).obj S.X₂) ≫
        ((cohomologyDeltaFunctor X U).functor n).map S.g =
        0 ≫ ((cohomologyDeltaFunctor X U).functor n).map S.g := by
      rw [hg, comp_zero, zero_comp]
    exact (cancel_mono _).1 h0
  exact key

/-- **Cross-check against an independently proved theorem.**
`Stacks.SectionEpiAffine.epi_secF_map_of_isAffineOpen`
(in `StacksFrontier/AlgebraicGeometry/SectionEpiAffine/Basic.lean`) says that `Γ(U, -)` carries
an epimorphism of quasi-coherent modules to an epimorphism for `U` affine, and proves it by the
Čech element chase of [Stacks, Tag 01EU]. It is recovered here from
`epi_secF_map_g_of_isZero_hgroup_one` and the `H¹` half of [Stacks, Tag 01XB], by a route sharing
no step with that proof.

This is kept as an `example` rather than a theorem precisely because the statement is already
in the library: its purpose is to witness that the long exact sequence extracted above has
the strength
its own proof claims. -/
example {M N : X.Modules} (ψ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] [Epi ψ]
    (hU : IsAffineOpen U) : Epi ((secF X.ringCatSheaf U).map ψ) := by
  have hker : (kernel ψ).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel ψ
  have hS : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)).ShortExact :=
    { exact := ShortComplex.exact_kernel ψ }
  exact epi_secF_map_g_of_isZero_hgroup_one X U hS
    (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X (kernel ψ) U hU 1 one_pos)

end Stacks.SerreAffinenessCriterion

end
