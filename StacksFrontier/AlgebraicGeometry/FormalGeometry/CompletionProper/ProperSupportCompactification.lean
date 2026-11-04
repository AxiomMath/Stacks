module

public import StacksFrontier.AlgebraicGeometry.Blowup.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportAnnihilation
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Basic
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective
public import StacksCore.Tactic.StacksAttribute

/-!
# The proper compactification behind the hypothesis `hSupp` of Stacks 088E

`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/ProperSupportAnnihilation.lean`
reduces the hypothesis `hSupp` of
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver` to the single properness
statement

  `IsProper ((Stacks.Algebraization.systemAnnihilatorIdeal 𝓖).subschemeι ≫ f)`,

for `f : X ⟶ Spec A` separated, locally of finite type and quasi-compact over a Noetherian
`I`-adically complete `A`, and records why that statement is not reachable from support and
annihilator bookkeeping: the sectionwise annihilator intersection is not quasi-coherent, properness
is not local on the source, and a decreasing chain of ideal sheaves with common proper support can
have infimum `⊥`. This file carries the three steps the source's proof uses instead, and reduces
the properness statement to the step they do not cover.

## The geometry the source uses

Completeness of `A` enters the proof of [Stacks, Tag 088E] in exactly one place: `I` lies in the
Jacobson radical of `A`, so *every nonempty closed subset of `Spec A` meets `V(I)`*. Applied over
a base morphism that is universally closed, that turns a statement about the closed fibre into a
statement about the whole space: a closed subset which does not escape an open subset *over
`V(I)`* does not escape it at all. The ambient must be universally closed over `A` for this —
`Spec ℚ_p ⟶ Spec ℤ_p` is separated of finite type, has proper (empty) closed fibre and is not
proper — which is why the source compactifies before using completeness.

The compactification is produced by Chow's lemma. For `f` separated, locally of finite type and
quasi-compact over a Noetherian base, `AlgebraicGeometry.hasDenseChowModification` gives a proper
surjective `π : Y ⟶ X` together with a *quasi-compact immersion* of `Y` into a projective space
over the base, i.e. H-quasi-projectivity of `π ≫ f`; and [Stacks, Tag 01WA],
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective`, factors that
into an open immersion `j : Y ⟶ Y'` followed by an H-projective `p : Y' ⟶ Spec A`. Both inputs are
unconditional, so the compactification below carries no hypothesis.

## Main results

* `Stacks.Algebraization.nonempty_inter_zeroLocus_of_isAdicComplete` — **the completeness step**:
  over an `I`-adically complete ring every nonempty closed subset of the prime spectrum meets
  `V(I)`.
* `Stacks.Algebraization.subset_of_mem_zeroLocus_imp_mem` — **support does not escape**: a closed
  subset of a scheme universally closed over `Spec A` which lies in an open subset at every point
  above `V(I)` lies in it everywhere.
* `Stacks.Algebraization.supp_subset_of_mem_zeroLocus_imp_mem` — the same for the support of a
  sheaf of modules, which is the shape the source applies it in.
* `Stacks.Algebraization.exists_isOpenImmersion_isProjectiveMorphism_denseChowModification` —
  **Chow's lemma with a projective compactification.** Unconditional.
* `AlgebraicGeometry.exists_closeds_image_isProperOver` — **the image of a proper closed subset in
  a separated ambient is closed and proper over the base**, which is what makes the direct image
  along `j` of a coherent sheaf with proper support coherent again.
* `Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_properCompactification` — the
  reduction: the properness statement behind `hSupp` follows from the same statement granted a
  proper surjective modification with a projective compactification, which the Chow step above
  supplies.

## What remains

The binder `hComp` of the last theorem is the step this file does not carry: transporting a
coherent adic system on `X` to the compactification `Y'`, algebraizing it there by the projective
case of Grothendieck existence —
`Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds`, which holds
outright — and descending the resulting annihilator along the proper surjection `π`. The two
geometric inputs that transport consumes are proved here: the support of the algebraization on `Y'`
does not escape `j(Y)` (`supp_subset_of_mem_zeroLocus_imp_mem`, since its intersection with the
closed fibre is the support of the first term of the system, which lives on `Y`), and the support
of the system on `Y` has closed image in `Y'`, proper over the base
(`AlgebraicGeometry.exists_closeds_image_isProperOver`). What is left is the transport of the
systems themselves, which is the comparison of [Stacks, Tag 088B] and the descent of
[Stacks, Tag 02O5], and is not a support statement.

## References

* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 01WA](https://stacks.math.columbia.edu/tag/01WA)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0CYN](https://stacks.math.columbia.edu/tag/0CYN)
* [Stacks Project, Tag 0CYQ](https://stacks.math.columbia.edu/tag/0CYQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-! ### The completeness step -/

/-- **Over an `I`-adically complete ring every nonempty closed subset of the prime spectrum meets
`V(I)`.** Completeness enters through `IsAdicComplete.le_jacobson_bot`: the ideal `I` lies in the
Jacobson radical, hence in every maximal ideal, and a nonempty closed subset
`Z = V(vanishingIdeal Z)` has `vanishingIdeal Z ≠ ⊤`, so it contains a maximal ideal.

This is the one place completeness of the base is used in the proof of [Stacks, Tag 088E]. -/
@[ega "I 1.1.15" "special case", ega "IV 18.5.7" "special case", sga "3 X 3.7" "more general"]
public theorem nonempty_inter_zeroLocus_of_isAdicComplete (A : Type u) [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] {Z : Set (PrimeSpectrum A)} (hZc : IsClosed Z) (hZ : Z.Nonempty) :
    (Z ∩ PrimeSpectrum.zeroLocus (I : Set A)).Nonempty := by
  obtain ⟨z, hz⟩ := hZ
  have hZeq : Z = PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set A) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]
  have hJne : PrimeSpectrum.vanishingIdeal Z ≠ ⊤ := by
    intro htop
    rw [PrimeSpectrum.vanishingIdeal_eq_top_iff] at htop
    exact absurd hz (htop ▸ Set.notMem_empty z)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hJne
  have := hm
  refine ⟨⟨m, hm.isPrime⟩, ?_, ?_⟩
  · rw [hZeq]
    exact hJm
  · refine (IsAdicComplete.le_jacobson_bot I).trans ?_
    rw [Ideal.jacobson_bot]
    exact Ring.jacobson_le_of_isMaximal m

/-! ### Support does not escape over a universally closed base -/

/-- **A closed subset of a scheme universally closed over `Spec A` which lies in an open subset
over `V(I)` lies in it everywhere.** Let `p : Y ⟶ Spec A` be universally closed, `A` complete
with respect to `I`, let `T ⊆ Y` be closed and `U ⊆ Y` open, and suppose every point of `T` lying
over `V(I)` is in `U`. Then `T ⊆ U`.

The complement `T \ U` is closed, so its image in `Spec A` is closed; if it were nonempty that
image would meet `V(I)` by
`Stacks.Algebraization.nonempty_inter_zeroLocus_of_isAdicComplete`, producing a point of `T` over
`V(I)` outside `U`.

Universal closedness of `p` is essential and not implied by separatedness and finite type:
`Spec ℚ_p ⟶ Spec ℤ_p` has empty closed fibre, so the hypothesis holds vacuously for every `T` and
`U = ⊥`, and the conclusion fails. This is why the proof of [Stacks, Tag 088E] passes to a
projective compactification before using completeness of `A`. -/
@[ega "III 5.2.6" "partial"]
public theorem subset_of_mem_zeroLocus_imp_mem (A : Type u) [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [UniversallyClosed p]
    {T : Set Y} (hT : IsClosed T) {U : Set Y} (hU : IsOpen U)
    (h : ∀ y ∈ T, p y ∈ PrimeSpectrum.zeroLocus (I : Set A) → y ∈ U) :
    T ⊆ U := by
  by_contra hTU
  obtain ⟨y₀, hy₀T, hy₀U⟩ := Set.not_subset.1 hTU
  have hCclosed : IsClosed (T \ U) := hT.sdiff hU
  have himg : IsClosed (p '' (T \ U)) := p.isClosedMap _ hCclosed
  obtain ⟨s, hsimg, hsI⟩ :=
    nonempty_inter_zeroLocus_of_isAdicComplete A I himg ⟨p y₀, y₀, ⟨hy₀T, hy₀U⟩, rfl⟩
  obtain ⟨y, ⟨hyT, hyU⟩, hys⟩ := hsimg
  exact hyU (h y hyT (hys ▸ hsI))

/-- **The support of a sheaf of modules does not escape over a universally closed base.** The
previous theorem at `T = ` the support, which is closed. This is the shape the proof of
[Stacks, Tag 088E] uses it in: on a projective compactification `Y'` of `Y`, the support of the
algebraization of a system living on `Y` meets the closed fibre inside `Y`, hence lies in `Y`
entirely. -/
public theorem supp_subset_of_mem_zeroLocus_imp_mem (A : Type u) [CommRing A] (I : Ideal A)
    [IsAdicComplete I A] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [UniversallyClosed p]
    (F : Y.Modules) [F.IsFiniteType] {U : Set Y} (hU : IsOpen U)
    (h : ∀ y ∈ _root_.SheafOfModules.supp F,
      p y ∈ PrimeSpectrum.zeroLocus (I : Set A) → y ∈ U) :
    _root_.SheafOfModules.supp F ⊆ U :=
  subset_of_mem_zeroLocus_imp_mem A I p (_root_.SheafOfModules.isClosed_supp F) hU h

end Stacks.Algebraization

/-! ### The image of a proper closed subset in a separated ambient -/

namespace AlgebraicGeometry

/-- The reduced subscheme on a closed subset proper over `S` has proper composite to `S`. -/
private theorem isProper_subschemeι_vanishingIdeal_comp_comp {Y Y' S : Scheme.{u}} (j : Y ⟶ Y')
    (p : Y' ⟶ S) [LocallyOfFiniteType p] [LocallyOfFiniteType (j ≫ p)] (W : Closeds Y)
    (hW : IsProperOver (j ≫ p) W) :
    IsProper (((Scheme.IdealSheafData.vanishingIdeal W).subschemeι ≫ j) ≫ p) := by
  have : IsProper ((Scheme.IdealSheafData.vanishingIdeal W).subschemeι ≫ (j ≫ p)) := hW
  rwa [Category.assoc]

/-- **The image of a closed subset proper over the base, under a morphism to a scheme separated
over the base, is closed and proper over the base.** Let `j : Y ⟶ Y'` be any morphism over `S`
with `p : Y' ⟶ S` separated, and let `W ⊆ Y` be a closed subset proper over `S`. Then `j '' W` is
closed in `Y'` and proper over `S`.

The reduced subscheme on `W` is proper over `S`, so its morphism to `Y'` is universally closed by
`AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated`, and
`AlgebraicGeometry.isProperOver_closedImage` ([Stacks, Tag 0CYQ]) applies to it.

Applied to an open immersion `j`, this is the geometric reason the direct image along `j` of a
coherent sheaf whose support is proper over the base is again coherent: the sheaf is the direct
image from a closed subscheme of `Y` whose image in `Y'` is closed, so the composite to `Y'` is a
closed immersion. -/
@[ega "II 5.4.10" "more general", ega "III 5.2.6" "more general", sga "4 XVII 6.1.1" "Clause (i)"]
public theorem exists_closeds_image_isProperOver {Y Y' S : Scheme.{u}} (j : Y ⟶ Y') (p : Y' ⟶ S)
    [IsSeparated p] [LocallyOfFiniteType p] [LocallyOfFiniteType (j ≫ p)]
    (W : Closeds Y) (hW : IsProperOver (j ≫ p) W) :
    ∃ W' : Closeds Y', (W' : Set Y') = j '' (W : Set Y) ∧ IsProperOver p W' := by
  set V := Scheme.IdealSheafData.vanishingIdeal W with hV
  set q : V.subscheme ⟶ Y' := V.subschemeι ≫ j with hq
  have hqp : IsProper (q ≫ p) := isProper_subschemeι_vanishingIdeal_comp_comp j p W hW
  have : UniversallyClosed q := UniversallyClosed.of_comp_of_isSeparated q p
  have htop : IsProperOver (q ≫ p) (⊤ : Closeds V.subscheme) := by
    show IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (⊤ : Closeds V.subscheme)).subschemeι ≫ (q ≫ p))
    infer_instance
  refine ⟨q.closedImage ⊤, ?_, isProperOver_closedImage q p ⊤ htop⟩
  show q '' Set.univ = j '' (W : Set Y)
  rw [Set.image_univ]
  have hrange : Set.range q.base = j.base '' Set.range V.subschemeι.base := by
    rw [hq]
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp] using
      (Set.range_comp j.base V.subschemeι.base)
  rw [hrange, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- **The reduced subscheme on a closed subset proper over the base is a closed subscheme of any
ambient separated over the base.** Let `j : Y ⟶ Y'` be an immersion over `S` with `p : Y' ⟶ S`
separated and let `W ⊆ Y` be a closed subset proper over `S`. Then the composite
`W ⟶ Y ⟶ Y'` is a *closed* immersion.

This is the form in which the proof of [Stacks, Tag 088E] makes the direct image along `j` of a
coherent sheaf with proper support coherent again. A coherent sheaf on `Y` annihilated by the
vanishing ideal sheaf of `W` is the direct image of a coherent sheaf on the reduced subscheme on
`W`; since that subscheme sits in `Y'` as a closed subscheme, its direct image to `Y'` is
coherent, and `j_*` of the original sheaf is that direct image. For an open immersion `j` this is
the only way the conclusion can hold — `j_*` does not preserve coherence in general, and the
hypothesis that is doing the work is properness of `W` over the base, not any property of `j`.

The composite is an immersion because immersions compose, and it is universally closed because
its composite with the separated `p` is proper; a preimmersion with closed range is a closed
immersion. -/
@[ega "III 5.2.6" "more general"]
public theorem isClosedImmersion_subschemeι_vanishingIdeal_comp {Y Y' S : Scheme.{u}} (j : Y ⟶ Y')
    [IsImmersion j] (p : Y' ⟶ S) [IsSeparated p] [LocallyOfFiniteType p]
    [LocallyOfFiniteType (j ≫ p)] (W : Closeds Y) (hW : IsProperOver (j ≫ p) W) :
    IsClosedImmersion ((Scheme.IdealSheafData.vanishingIdeal W).subschemeι ≫ j) := by
  set V := Scheme.IdealSheafData.vanishingIdeal W with hV
  set q : V.subscheme ⟶ Y' := V.subschemeι ≫ j with hq
  have hqp : IsProper (q ≫ p) := isProper_subschemeι_vanishingIdeal_comp_comp j p W hW
  have : UniversallyClosed q := UniversallyClosed.of_comp_of_isSeparated q p
  have : IsImmersion q := by rw [hq]; infer_instance
  exact IsClosedImmersion.of_isPreimmersion q q.isClosedMap.isClosed_range

end AlgebraicGeometry

/-! ### Chow's lemma with a projective compactification -/

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions

/-- **Chow's lemma with a projective compactification.** Let `S` be Noetherian and let
`f : X ⟶ S` be separated, locally of finite type and quasi-compact. Then there are a scheme `Y`,
a proper surjective `π : Y ⟶ X` which is an isomorphism over a dense open `U ⊆ X`, a scheme `Y'`,
an open immersion `j : Y ⟶ Y'` and an H-projective `p : Y' ⟶ S` with `j ≫ p = π ≫ f`.

Everything here is unconditional. `AlgebraicGeometry.hasDenseChowModification`
([Stacks, Tag 0200]) produces `π` together with an immersion `i : Y ⟶ ℙⁿ_S` over `S`; that
immersion is quasi-compact because `π ≫ f = i ≫ (ℙⁿ_S ↘ S)` is and `ℙⁿ_S` is separated over `S`
([Stacks, Tag 03GI]), so `π ≫ f` is H-quasi-projective, and
`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective`
([Stacks, Tag 01WA]) factors it through the scheme-theoretic image of `i`.

Note that `f` is not assumed proper: that is exactly the situation of [Stacks, Tag 088E], and it
is why a compactification is needed at all — for proper `f` the modification of
`AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification` is already projective over
the base and `Y' = Y` will do. -/
@[ega "II 5.6.1" "partial",
  ega "III 5.3.5" "Chow modification",
  sga "4 XVII 7.0.6" "Noetherian base"]
public theorem exists_isOpenImmersion_isProjectiveMorphism_denseChowModification
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    ∃ (Y Y' : Scheme.{u}) (π : Y ⟶ X) (j : Y ⟶ Y') (p : Y' ⟶ S) (U : X.Opens),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧
        AlgebraicGeometry.IsProjectiveMorphism p ∧ j ≫ p = π ≫ f ∧
          Dense (U : Set X) ∧ IsIso (π ∣_ U) := by
  obtain ⟨n, Y, π, i, U, hπ, hsurj, himm, hcomm, hU, hiso⟩ := hasDenseChowModification f
  have : IsProper π := hπ
  have : IsImmersion i := himm
  have : QuasiCompact (i ≫ (ProjectiveSpace n S ↘ S)) := by
    rw [← hcomm]; infer_instance
  have hqc : QuasiCompact i :=
    Stacks.QuasiProjectiveCompactification.quasiCompact_of_comp_isSeparated i
      (ProjectiveSpace n S ↘ S) inferInstance inferInstance
  obtain ⟨Y', j, p, hj, hp, hjp⟩ :=
    AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective
      (f := π ≫ f) ⟨n, i, himm, hqc, hcomm.symm⟩
  exact ⟨Y, Y', π, j, p, U, hπ, hsurj, hj, hp, hjp, hU, hiso⟩

/-- **Chow's lemma with a projective compactification across which support cannot escape.** The
previous theorem together with `Stacks.Algebraization.supp_subset_of_mem_zeroLocus_imp_mem`: over a
Noetherian `I`-adically complete `A` and for `f : X ⟶ Spec A` separated, locally of finite type and
quasi-compact, there is a proper surjective modification `π : Y ⟶ X`, an open immersion
`j : Y ⟶ Y'` and an H-projective `p : Y' ⟶ Spec A` over `f`, such that the support of *every*
sheaf of modules of finite type on `Y'` which lies in `j(Y)` over `V(I)` lies in `j(Y)` entirely.

This is the shape in which the proof of [Stacks, Tag 088E] uses the compactification. The
algebraization on `Y'` of a system living on `Y` — which the projective case of Grothendieck
existence provides,
`Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds` — has first
term the system's own first term, so its support meets the closed fibre inside `j(Y)`; the clause
below then says its whole support is inside `j(Y)`, which is what lets it be restricted back to
`Y`. H-projectivity of `p` is what makes `p` universally closed. -/
@[sga "4 XVII 7.0.6" "Affine Noetherian base"]
public theorem exists_denseChowModification_supp_subset_range
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (Y Y' : Scheme.{u}) (π : Y ⟶ X) (j : Y ⟶ Y') (p : Y' ⟶ Spec (.of A)) (U : X.Opens),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧
        AlgebraicGeometry.IsProjectiveMorphism p ∧ j ≫ p = π ≫ f ∧
          Dense (U : Set X) ∧ IsIso (π ∣_ U) ∧
            ∀ F : Y'.Modules, F.IsFiniteType →
              (∀ y ∈ _root_.SheafOfModules.supp F,
                  p y ∈ PrimeSpectrum.zeroLocus (I : Set A) → y ∈ Set.range j.base) →
                _root_.SheafOfModules.supp F ⊆ Set.range j.base := by
  obtain ⟨Y, Y', π, j, p, U, hπ, hsurj, hj, hp, hjp, hU, hiso⟩ :=
    exists_isOpenImmersion_isProjectiveMorphism_denseChowModification f
  refine ⟨Y, Y', π, j, p, U, hπ, hsurj, hj, hp, hjp, hU, hiso, fun F hF h => ?_⟩
  have := hj
  have := hF
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  exact supp_subset_of_mem_zeroLocus_imp_mem A I p F j.isOpenEmbedding.isOpen_range h

/-! ### The reduction of the properness statement behind `hSupp` -/

/-- **The properness statement behind `hSupp`, reduced to the compactified situation.** Let `A` be
Noetherian and complete with respect to `I` and let `f : X ⟶ Spec A` be separated, locally of
finite type and quasi-compact. Suppose that for *some* proper surjective modification `π : Y ⟶ X`
admitting an open immersion `j : Y ⟶ Y'` into a scheme `Y'` H-projective over `Spec A` with
`j ≫ p = π ≫ f`, every coherent `𝓘`-adic system on `X` whose first term has support proper over
`A` is annihilated by the ideal sheaf of a closed subscheme of `X` proper over `A`. Then the
closed subscheme cut out by `Stacks.Algebraization.systemAnnihilatorIdeal` is proper over `A` for
every such system — which is, by
`Stacks.Algebraization.hSupp_of_isProper_systemAnnihilatorIdeal`, exactly the hypothesis `hSupp`
of `Stacks.Algebraization.isEquivalence_completionFunctorProperOver`.

The content of the reduction is that the compactification exists: it is supplied by
`Stacks.Algebraization.exists_isOpenImmersion_isProjectiveMorphism_denseChowModification`, which
is unconditional, so the binder `hComp` may be used with the Chow data of the given `f` already
in hand. Converting the existential it produces into properness of the canonical ideal sheaf is
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_iff`, which shows the existential
carries no content.

See the module docstring for what `hComp` still requires and for the two geometric inputs to it
which this file proves. -/
public theorem isProper_systemAnnihilatorIdeal_of_properCompactification
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hComp : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ (Y Y' : Scheme.{u}) (π : Y ⟶ X) (j : Y ⟶ Y') (p : Y' ⟶ Spec (.of A)),
        IsProper π → Surjective π → IsOpenImmersion j →
          AlgebraicGeometry.IsProjectiveMorphism p → j ≫ p = π ≫ f →
            ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
              HasProperSupport f (𝓖.obj.obj (op 0)) →
                ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
                  IsSystemAnnihilatedBy J 𝓖.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓖.obj.obj (op 0)) →
        IsProper ((systemAnnihilatorIdeal 𝓖).subschemeι ≫ f) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨Y, Y', π, j, p, U, hπ, hsurj, hj, hp, hjp, -, -⟩ :=
    exists_isOpenImmersion_isProjectiveMorphism_denseChowModification f
  exact fun 𝓖 h => (exists_isProper_isSystemAnnihilatedBy_iff f 𝓖).1
    (hComp Y Y' π j p hπ hsurj hj hp hjp 𝓖 h)

end Stacks.Algebraization

end
