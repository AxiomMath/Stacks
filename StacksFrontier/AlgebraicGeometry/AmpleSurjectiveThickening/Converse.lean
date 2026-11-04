module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleClosedImmersion.Converse
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ClauseThree.GenericStalkInput
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Ample
public import StacksFrontier.AlgebraicGeometry.NilpotentThickeningLift.Lift
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.InvertibleTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample

/-!
# Stacks Tag 09MS

Let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a homeomorphism of
underlying topological spaces, and let `L` be an invertible `𝒪_X`-module. Then `i^* L` is ample
on `Z` if and only if `L` is ample on `X` ([Stacks, Tag 09MS]).

A closed immersion inducing a homeomorphism is a closed immersion which is surjective on points,
and conversely, so the statement is written with `Surjective i`.

## Main results

* `Stacks.AmpleSurjectiveThickening.exists_finite_affine_generator_cover`: a quasi-compact scheme
  is covered by finitely many affine opens on each of which `L` has a generator.
* `Stacks.AmpleSurjectiveThickening.isAmple_of_isAmple_modulePullback_of_surjective`: ampleness of
  `i^* L` gives ampleness of `L`.
* `Stacks.AmpleSurjectiveThickening.isAmple_modulePullback_iff_isAmple`: the biconditional of
  [Stacks, Tag 09MS].

## The route

Let `x ∈ X`, let `U_{j₀}` be an affine open around `x` of a finite cover by affine opens `U_j`
trivializing `L`, and let `z` be the point of `Z` over `x`. Ampleness of `i^* L` gives a section
`t` of some `(i^* L)^{⊗ n}` with `z ∈ Z_t ⊆ i⁻¹(U_{j₀})` and `Z_t` affine ([Stacks, Tag 01Q3]). A
power of `t` lifts to a section `s` of a tensor power of `L` with `i⁻¹(X_s) = Z_t`
(`Stacks.NilpotentThickeningLift.exists_sections_preimage_nonvanishingOpen_eq`), and `X_s` is
affine by [Stacks, Tag 01YQ].

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

universe u

namespace Stacks.AmpleSurjectiveThickening

variable {Z X : Scheme.{u}}

/-- **A quasi-compact scheme is covered by finitely many affine opens trivializing an invertible
module.** -/
theorem exists_finite_affine_generator_cover [CompactSpace X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens) (_ : ∀ j, IsAffineOpen (U j))
      (_ : ∀ x, ∃ j, x ∈ U j), Nonempty (∀ j, GeneratorSections X.toRingedSpace L (U j)) := by
  have hL := isInvertible_of_tensorInvertible L
  have key : ∀ x : X, ∃ (A : X.Opens) (_ : IsAffineOpen A) (_ : x ∈ A),
      Nonempty (GeneratorSections X.toRingedSpace L A) := by
    intro x
    obtain ⟨W, hxW, a, ha⟩ := exists_bijective_smul_of_isInvertible (X := X.toRingedSpace) L x
    obtain ⟨A, hA, hxA, hAW⟩ := exists_isAffineOpen_mem_and_subset (X := X) hxW
    exact ⟨A, hA, hxA, ⟨generatorRestrict L (fun y hy => hAW hy) ⟨a, ha⟩⟩⟩
  choose A hA hxA hg using key
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (A x : Set X))
    (fun x => (A x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxA x⟩)
  refine ⟨s, inferInstance, fun j => A j.1, fun j => hA j.1, fun x => ?_,
    ⟨fun j => (hg j.1).some⟩⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨y, hy⟩, hxy⟩

variable (i : Z ⟶ X) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The implication `i^* L` ample `⟹` `L` ample of [Stacks, Tag 09MS].** For a closed immersion
`i : Z ⟶ X` surjective on points onto a locally Noetherian scheme, ampleness of `i^* L` gives
ampleness of `L`. -/
theorem isAmple_of_isAmple_modulePullback_of_surjective [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X]
    (h : Stacks.Ample.IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L)) :
    Stacks.Ample.IsAmple X L := by
  have hX : CompactSpace X :=
    Stacks.AmpleClosedImmersion.compactSpace_of_surjective i inferInstance h.compactSpace
  set M := (modulePullback i.toLRSHom.toShHom).obj L
  refine (Stacks.AmpleBridge.isAmple_iff_isAmple X L).mpr ⟨hX, fun x => ?_⟩
  obtain ⟨J, hJ, U, hU, hcov, ⟨g⟩⟩ := exists_finite_affine_generator_cover L
  obtain ⟨j₀, hj₀⟩ := hcov x
  obtain ⟨z, rfl⟩ := i.surjective x
  obtain ⟨n, hn, t, haff, hzt, htU⟩ :=
    Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple Z M h z (i ⁻¹ᵁ U j₀) hj₀
  let e : AlgebraicGeometry.Scheme.Modules.tensorPowerModules M (n : ℤ) ≅
      Stacks.Ample.tensorPowModule Z M (n : ℤ) :=
    Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso Z M (n : ℤ)
  set t' := (Stacks.NonvanishingSpelling.sectionsEquiv Z
    (AlgebraicGeometry.Scheme.Modules.tensorPowerModules M (n : ℤ))).symm (e.symm.hom.app ⊤ t)
  have key : Stacks.SheafOfModules.nonvanishingOpen (X := Z.toRingedSpace) _ t' =
      Stacks.AmpleTheory.powNonvanishingOpen Z M n t :=
    TopologicalSpace.Opens.ext
      ((Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq Z _ _).trans
        (Stacks.Ample.nonvanishingLocus_congr e.symm t))
  obtain ⟨D, hD, s, hs⟩ :=
    Stacks.NilpotentThickeningLift.exists_sections_preimage_nonvanishingOpen_eq
      i L i.surjective U hU hcov g j₀ n hn t' (key.le.trans htU)
  refine ⟨D, hD, s, ?_, ?_⟩
  · refine Scheme.Hom.mem_preimage i |>.mp ?_
    rw [hs, key]; exact hzt
  · refine Stacks.AmpleClosedImmersion.isAffineOpen_of_isAffineOpen_preimage i
      (Stacks.AmpleClosedImmersion.affineOfSurjectiveClosedImmersion_of_chevalley
        fun _ _ j hfin hsurj hB hA => by
          have := hfin
          have := hsurj
          have := hB
          have := hA
          exact Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective j) _ ?_
    rw [hs, key]; exact haff

/-- **[Stacks, Tag 09MS].** Let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a
homeomorphism of underlying topological spaces — that is, a closed immersion surjective on points
— and let `L` be an invertible `𝒪_X`-module. Then `i^* L` is ample on `Z` if and only if `L` is
ample on `X`. -/
theorem isAmple_modulePullback_iff_isAmple [IsClosedImmersion i] [Surjective i] [IsNoetherian X] :
    Stacks.Ample.IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔
      Stacks.Ample.IsAmple X L :=
  ⟨isAmple_of_isAmple_modulePullback_of_surjective i L,
    Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion i L⟩

end Stacks.AmpleSurjectiveThickening
