module

public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.CoherentModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.CohomologyBoundedAbove
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08IK: pseudo-coherence on a Noetherian algebraic space is coherent cohomology

Let `S` be a scheme, let `F` be a Noetherian algebraic space over `S` and let `E` be an object
of `D_QCoh(𝒪_F)`. Stacks 08IK asserts, for every `m ∈ ℤ`, the equivalence of

1. `Hⁱ(E)` is coherent for `i ≥ m` and zero for `i ≫ 0`, and
2. `E` is `m`-pseudo-coherent,

and deduces that `E` is pseudo-coherent if and only if it is an object of `D⁻_Coh(𝒪_F)`.

This file proves the implication (1) ⇒ (2) and assembles the whole tag. The implication
(2) ⇒ (1) is the theorem
`Space.isCoherentOnSite_homology_and_isBoundedAbove_of_isPseudoCoherentFrom_of_isNoetherian`
in the namespace `AlgebraicGeometry`.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentFrom_of_isCoherentOnSite_homology_of_isBoundedAbove`:
  over a locally Noetherian algebraic space, an object of `D(𝒪_F)` which is bounded above and
  has coherent `Hⁱ` for `i ≥ m` is `m`-pseudo-coherent — the implication (1) ⇒ (2).
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_iff_of_isNoetherian`: the equivalence of (1) and
  (2) for an object of `D_QCoh(𝒪_F)` over a Noetherian algebraic space.
* `AlgebraicGeometry.Space.isPseudoCoherent_iff_of_isNoetherian`: the final statement, that such
  an object is pseudo-coherent exactly when it lies in `D⁻_Coh(𝒪_F)`.
* `AlgebraicGeometry.Space.isPseudoCoherentFrom_iff_and_isPseudoCoherent_iff_of_isNoetherian`:
  **Stacks 08IK**, the two together, for every `m`.

## How (1) ⇒ (2) is proved

The source reduces to the affine case étale locally and quotes the commutative algebra of
Stacks 064T / 066E there. Here the same content is run on the small étale site itself, in two
steps, each of which is the site form of a step of the scheme-level proof of Stacks 08E8.

*Each cohomology sheaf.* On a locally Noetherian algebraic space the structure sheaf is
coherent (`AlgebraicGeometry.Space.isCoherent_structureSheaf`, Stacks 07UB). On a ringed site
with coherent structure sheaf a coherent module placed in degree zero is `n`-pseudo-coherent for
every `n`: that is the syzygy induction
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_singleFunctor_zero_of_isCoherentOnSite`, the
sheaf form of "a finite module over a Noetherian ring has a resolution by finite free modules",
which is where 064T / 066E enter the source's argument. So `Hⁱ(E)`, placed in degree zero, is
`(m - i)`-pseudo-coherent for each `i ≥ m`.

*The truncation induction.* An object of `D(𝒪)` bounded above whose cohomology sheaves are so
is `m`-pseudo-coherent: that is the bounded above case of Stacks 09V8 on a ringed site,
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_homology_of_boundedAbove_general`, which
splits off the top cohomology degree with the canonical truncation triangle and applies
Stacks 08FV. The global bound it needs is exactly the vanishing clause of (1).

The implication (1) ⇒ (2) needs neither quasi-compactness nor quasi-separatedness of `F`, nor
the hypothesis `E ∈ D_QCoh(𝒪_F)`: only local Noetherianity, through the coherence of the
structure sheaf.

## References

* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 064T](https://stacks.math.columbia.edu/tag/064T)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 09V8](https://stacks.math.columbia.edu/tag/09V8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The implication (1) ⇒ (2) of Stacks 08IK.** Let `F` be a locally Noetherian algebraic
space over `S` and let `E` be an object of `D(𝒪_F)` whose cohomology vanishes in all
sufficiently large degrees and is coherent in every degree `i ≥ m`. Then `E` is
`m`-pseudo-coherent.

Each `Hⁱ(E)` with `i ≥ m`, placed in degree zero, is pseudo-coherent by the syzygy induction on
the small étale site, whose structure sheaf is coherent (Stacks 07UB); the truncation induction
(the bounded above case of Stacks 09V8) assembles them. -/
theorem isPseudoCoherentFrom_of_isCoherentOnSite_homology_of_isBoundedAbove
    (hN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) (m : ℤ)
    (hcoh : ∀ i : ℤ, m ≤ i → SheafOfModules.IsCoherentOnSite
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E))
    (hb : DerivedCategoryB.IsBoundedAbove E) :
    (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m := by
  have := Fact.mk hN
  obtain ⟨b, hb⟩ := hb
  exact RingedSite.isPseudoCoherentFrom_of_homology_of_boundedAbove_general _ E m b hb
    fun i hi =>
      RingedSite.isPseudoCoherentFrom_singleFunctor_zero_of_isCoherentOnSite.{u + 1, u, u} _
        (isCoherent_structureSheaf B S hS F hF).toIsCoherentOnSite _ (hcoh i hi) (m - i)

/-- **Stacks 08IK, the equivalence of (1) and (2).** Let `S` be a scheme, let `F` be a
Noetherian algebraic space over `S`, let `E` be an object of `D_QCoh(𝒪_F)` and let `m ∈ ℤ`.
Then `Hⁱ(E)` is coherent for `i ≥ m` and zero for `i ≫ 0` if and only if `E` is
`m`-pseudo-coherent.

The hypothesis `E ∈ D_QCoh(𝒪_F)` is the condition, `DerivedCategoryB.derivedCategoryB` of the
quasi-coherence predicate, whose full subcategory is
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` (Stacks 071X). -/
theorem isPseudoCoherentFrom_iff_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ F)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) E)
    (m : ℤ) :
    ((∀ i : ℤ, m ≤ i → SheafOfModules.IsCoherentOnSite
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E)) ∧
      DerivedCategoryB.IsBoundedAbove E) ↔
      (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m :=
  ⟨fun h => isPseudoCoherentFrom_of_isCoherentOnSite_homology_of_isBoundedAbove B S hS F hF
      hFN.2.2 E m h.1 h.2,
    fun h => isCoherentOnSite_homology_and_isBoundedAbove_of_isPseudoCoherentFrom_of_isNoetherian
      B S hS F hF hZ hFN E m h hE⟩

/-- **Stacks 08IK, the final statement.** Let `S` be a scheme, let `F` be a Noetherian algebraic
space over `S` and let `E` be an object of `D_QCoh(𝒪_F)`. Then `E` is pseudo-coherent if and
only if it is an object of `D⁻_Coh(𝒪_F)`: its cohomology vanishes in all sufficiently large
degrees and is coherent in every degree.

Pseudo-coherence is `m`-pseudo-coherence for every `m` witnessed by one representing complex;
that one complex serves for all `m` once some does for each is Stacks 08FU (2),
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_iso_general`. -/
theorem isPseudoCoherent_iff_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ F)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (_hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) E) :
    (smallEtaleRingedSite B S hS F hF).IsPseudoCoherent E ↔
      (DerivedCategoryB.IsBoundedAbove E ∧
        ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E)) := by
  refine ⟨isCoherentOnSite_homology_and_isBoundedAbove_of_isPseudoCoherent_of_isNoetherian
    B S hS F hF hZ hFN E, fun ⟨hb, hcoh⟩ => ?_⟩
  have h : ∀ m : ℤ, (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m := fun m =>
    isPseudoCoherentFrom_of_isCoherentOnSite_homology_of_isBoundedAbove B S hS F hF hFN.2.2 E m
      (fun i _ => hcoh i) hb
  obtain ⟨P, _, ⟨e⟩⟩ := h 0
  exact ⟨P, fun n => RingedSite.isPseudoCoherentComplexFrom_of_iso_general _ E n (h n) P e, ⟨e⟩⟩

/-- **Stacks 08IK.** Let `S` be a scheme, let `F` be a Noetherian algebraic space over `S` and
let `E` be an object of `D_QCoh(𝒪_F)`. For every `m ∈ ℤ` the following are equivalent:

1. `Hⁱ(E)` is coherent for `i ≥ m` and zero for `i ≫ 0`, and
2. `E` is `m`-pseudo-coherent.

In particular, `E` is pseudo-coherent if and only if `E` is an object of `D⁻_Coh(𝒪_F)`, that
is, its cohomology vanishes in all sufficiently large degrees and is coherent in every degree.

The first conjunct is `AlgebraicGeometry.Space.isPseudoCoherentFrom_iff_of_isNoetherian` and the
second `AlgebraicGeometry.Space.isPseudoCoherent_iff_of_isNoetherian`. Noetherianity of `F` is
Stacks 03EA: quasi-compact, quasi-separated and locally Noetherian. `D_QCoh(𝒪_F)` is the
condition whose full subcategory is `AlgebraicGeometry.Space.QuasicoherentDerivedCategory`
(Stacks 071X). -/
@[stacks 08IK]
theorem isPseudoCoherentFrom_iff_and_isPseudoCoherent_iff_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) (hFN : IsNoetherian B S hS hZ F)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) E) :
    (∀ m : ℤ,
      ((∀ i : ℤ, m ≤ i → SheafOfModules.IsCoherentOnSite
          ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E)) ∧
        DerivedCategoryB.IsBoundedAbove E) ↔
        (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E m) ∧
      ((smallEtaleRingedSite B S hS F hF).IsPseudoCoherent E ↔
        (DerivedCategoryB.IsBoundedAbove E ∧
          ∀ i : ℤ, SheafOfModules.IsCoherentOnSite
            ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E))) :=
  ⟨isPseudoCoherentFrom_iff_of_isNoetherian B S hS F hF hZ hFN E hE,
    isPseudoCoherent_iff_of_isNoetherian B S hS F hF hZ hFN E hE⟩

end AlgebraicGeometry.Space

end
