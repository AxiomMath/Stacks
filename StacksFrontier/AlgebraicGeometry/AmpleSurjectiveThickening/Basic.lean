module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.AmpleClosedImmersion.Converse
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ClauseThree.GenericStalkInput
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Ample
public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Converse

/-!
# Stacks Tag 09MS

Let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a homeomorphism of
underlying topological spaces, and let `L` be an invertible `𝒪_X`-module. [Stacks, Tag 09MS]
asserts

> `i^* L` is ample on `Z`, if and only if `L` is ample on `X`.

A closed immersion inducing a homeomorphism is a **surjective** closed immersion, and conversely,
so the intermediate statements here are written with `Surjective i`.

## Main results

* `Stacks.AmpleSurjectiveThickening.isAmple_modulePullback_iff_isAmple_of_isHomeomorph`:
  **[Stacks, Tag 09MS]**, with the source's hypothesis that `i` induces a homeomorphism of
  underlying spaces. The converse implication is
  `Stacks.AmpleSurjectiveThickening.isAmple_of_isAmple_modulePullback_of_surjective`
  (`StacksFrontier/AlgebraicGeometry/AmpleSurjectiveThickening/Converse.lean`).
* `Stacks.AmpleSurjectiveThickening.affineOfSurjectiveClosedImmersion`:
  `Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion`, from [Stacks, Tag 01YQ].
* `Stacks.AmpleSurjectiveThickening.isAmple_modulePullback`: `L` ample `⟹` `i^* L` ample.
* `Stacks.AmpleSurjectiveThickening.isAffineOpen_of_isAffineOpen_preimage`: an open of `X` whose
  inverse image is affine is affine.
* `Stacks.AmpleSurjectiveThickening.isAmple_of_isAmple_modulePullback` and
  `isAmple_modulePullback_iff`: the converse, and the biconditional, through
  `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`.
* `Stacks.AmpleSurjectiveThickening.surjective_pullbackGlobalSection_of_isZero_h1`: a global
  section of `i^* M` is the pullback of one of `M` when `H¹(X, 𝓘 ⊗ M) = 0`.
* `Stacks.AmpleSurjectiveThickening.sectionsLiftAfterPower_of_isZero_h1`:
  `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` from the vanishing of
  `H¹(X, 𝓘 ⊗ L^{⊗ m})` in arbitrarily high degrees `m`, and its consequences
  `isAmple_of_isAmple_modulePullback_of_isZero_h1` and `isAmple_modulePullback_iff_of_isZero_h1`.

## The route

[Stacks, Tag 01YQ] — a Noetherian scheme receiving a finite surjective morphism from an affine
scheme is affine — is
`Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective`, and
`Stacks.AmpleClosedImmersion.affineOfSurjectiveClosedImmersion_of_chevalley` turns it into
`Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion`.

The vanishing of `H¹(X, 𝓘 ⊗ L^{⊗ m})` makes `Γ(X, L^{⊗ m}) ⟶ Γ(Z, (i^* L)^{⊗ m})` surjective
through the long exact sequence of `0 → 𝓘 ⊗ L^{⊗ m} → L^{⊗ m} → i_* (i^* L)^{⊗ m} → 0`
(`Stacks.Cohomology.AmpleH1.epi_globalSections_map_unit_app`), and a section lifting `t` has
`i^{-1}(X_{t'}) = Z_t` by [Stacks, Tag 0H78].

## Which ampleness predicate

`Stacks.Ample.IsAmple`, the [Stacks, Tag 01PS] predicate of
`Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion` and
`Stacks.AmpleClosedImmersion.isAmple_modulePullback_iff`. It agrees with
`AlgebraicGeometry.Scheme.Modules.IsAmple` by `Stacks.AmpleBridge.isAmple_iff_isAmple`. The module
`i^* L` is written as `(modulePullback i.toLRSHom.toShHom).obj L`.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01YQ](https://stacks.math.columbia.edu/tag/01YQ)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmpleSurjectiveThickening

/-- **A locally Noetherian scheme receiving a surjective closed immersion from an affine scheme is
affine.** This is [Stacks, Tag 01YQ]
(`Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective`) through
`Stacks.AmpleClosedImmersion.affineOfSurjectiveClosedImmersion_of_chevalley`: a closed immersion
is finite, and quasi-compactness of the target follows from surjectivity. -/
theorem affineOfSurjectiveClosedImmersion :
    Stacks.AmpleClosedImmersion.AffineOfSurjectiveClosedImmersion.{u} :=
  Stacks.AmpleClosedImmersion.affineOfSurjectiveClosedImmersion_of_chevalley
    fun _ _ j hfin hsurj hB hA => by
      have := hfin
      have := hsurj
      have := hB
      have := hA
      exact Stacks.AlgebraicGeometry.Tag01YQClauseThree.isAffine_of_isFinite_surjective j

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **`L` ample `⟹` `i^* L` ample.** For a closed immersion `i : Z ⟶ X` of Noetherian schemes
inducing a homeomorphism of underlying spaces, ampleness of an invertible `𝒪_X`-module `L` gives
ampleness of `i^* L` ([Stacks, Tag 0892]). The proof is
`Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion`. -/
@[stacks 09MS "the implication `L` ample ⟹ `i^* L` ample"]
theorem isAmple_modulePullback [IsClosedImmersion i] [Surjective i] [IsNoetherian X]
    (hL : IsAmple X L) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) :=
  Stacks.AmpleClosedImmersion.isAmple_modulePullback_of_surjective_isClosedImmersion i L hL

/-- **An open of `X` whose inverse image is affine is affine**, for a surjective closed immersion
onto a locally Noetherian scheme:
`Stacks.AmpleClosedImmersion.isAffineOpen_of_isAffineOpen_preimage` applied to
`Stacks.AmpleSurjectiveThickening.affineOfSurjectiveClosedImmersion`. -/
theorem isAffineOpen_of_isAffineOpen_preimage [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen (i ⁻¹ᵁ U)) :
    IsAffineOpen U :=
  Stacks.AmpleClosedImmersion.isAffineOpen_of_isAffineOpen_preimage i
    affineOfSurjectiveClosedImmersion U hU

/-- **`i^* L` ample `⟹` `L` ample, through `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`.**
For a surjective closed immersion onto a locally Noetherian scheme. -/
theorem isAmple_of_isAmple_modulePullback [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X]
    (hlift : Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L)
    (h : IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L)) :
    IsAmple X L :=
  Stacks.AmpleClosedImmersion.isAmple_of_isAmple_modulePullback i L
    affineOfSurjectiveClosedImmersion hlift h

/-- **`i^* L` ample `⟺` `L` ample, through `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower`.**
This is `Stacks.AmpleClosedImmersion.isAmple_modulePullback_iff` with its first input supplied by
`Stacks.AmpleSurjectiveThickening.affineOfSurjectiveClosedImmersion`. -/
theorem isAmple_modulePullback_iff [IsClosedImmersion i] [Surjective i] [IsNoetherian X]
    (hlift : Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔ IsAmple X L :=
  Stacks.AmpleClosedImmersion.isAmple_modulePullback_iff i L
    affineOfSurjectiveClosedImmersion hlift

/-! ### The cohomological lift, from the vanishing of the obstruction group -/

/-- **Global sections lift across a closed immersion when the obstruction group vanishes.** Let
`i : Z ⟶ X` be a closed immersion with ideal sheaf `𝓘` and let `M` be an invertible
`𝒪_X`-module with `H¹(X, 𝓘 ⊗ M) = 0`. Then every global section of `i^* M` is the pullback of a
global section of `M`.

The map is `Stacks.NonvanishingPullback.pullbackGlobalSection`, the image of a section under the
unit of `i^* ⊣ i_*`; `Stacks.Cohomology.AmpleH1.epi_globalSections_map_unit_app` asserts that
unit is carried to an epimorphism by global sections, which on elements is this surjectivity. -/
theorem surjective_pullbackGlobalSection_of_isZero_h1 [IsClosedImmersion i] (M : X.Modules)
    [IsInvertibleModule X M]
    (hvan : Limits.IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived
      1).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj (M))))) :
    Function.Surjective (Stacks.NonvanishingPullback.pullbackGlobalSection i M) := by
  have h := Stacks.Cohomology.AmpleH1.epi_globalSections_map_unit_app i M hvan
  rw [ModuleCat.epi_iff_surjective] at h
  exact h

/-- **A nonvanishing locus on `Z` is pulled back from one on `X` in a degree where the
obstruction group vanishes.** If `H¹(X, 𝓘 ⊗ L^{⊗ m}) = 0` then for every global section `t` of
`(i^* L)^{⊗ m}` there is a global section `t'` of `L^{⊗ m}` with `Z_t = i^{-1}(X_{t'})`.

The section `t'` is one whose pullback is `t` read through `i^* (L^{⊗ m}) ≅ (i^* L)^{⊗ m}`, and
the loci then agree by [Stacks, Tag 0H78]. -/
theorem exists_preimage_powNonvanishingOpen_eq_of_isZero_h1 [IsClosedImmersion i] (m : ℕ)
    (hvan : Limits.IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived
      1).obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
          ((tensorPowModule X L (m : ℤ)))))))
    (t : Γ(tensorPowModule Z (Stacks.AmpleLocallyClosed.pullbackModule i L) (m : ℤ), ⊤)) :
    ∃ t' : Γ(tensorPowModule X L (m : ℤ), ⊤),
      i ⁻¹ᵁ powNonvanishingOpen X L m t' =
        powNonvanishingOpen Z (Stacks.AmpleLocallyClosed.pullbackModule i L) m t := by
  obtain ⟨s, hs⟩ := surjective_pullbackGlobalSection_of_isZero_h1 i _ hvan
    (Scheme.Modules.Hom.app
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso i L m).symm.hom ⊤ t)
  refine ⟨s, TopologicalSpace.Opens.ext ?_⟩
  calc ((i ⁻¹ᵁ powNonvanishingOpen X L m s : Z.Opens) : Set Z)
      = i.base ⁻¹' Stacks.Ample.nonvanishingLocus (tensorPowModule X L (m : ℤ)) s := rfl
    _ = Stacks.Ample.nonvanishingLocus ((modulePullback i.toLRSHom.toShHom).obj
          (tensorPowModule X L (m : ℤ)))
          (Stacks.NonvanishingPullback.pullbackGlobalSection i
            (tensorPowModule X L (m : ℤ)) s) :=
        Stacks.NonvanishingPullback.preimage_nonvanishingLocus i _ s
    _ = Stacks.Ample.nonvanishingLocus ((modulePullback i.toLRSHom.toShHom).obj
          (tensorPowModule X L (m : ℤ)))
          (Scheme.Modules.Hom.app
            (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso i L m).symm.hom ⊤ t) := by
        rw [hs]
    _ = Stacks.Ample.nonvanishingLocus
          (tensorPowModule Z (Stacks.AmpleLocallyClosed.pullbackModule i L) (m : ℤ)) t :=
        Stacks.Ample.nonvanishingLocus_congr
          (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso i L m).symm t
    _ = _ := rfl

/-- **`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` from the vanishing of
`H¹(X, 𝓘 ⊗ L^{⊗ m})`.** It holds for a closed immersion `i` with ideal sheaf `𝓘` and an
invertible `L` as soon as every degree `n ≥ 1` has a multiple `m` with
`H¹(X, 𝓘 ⊗ L^{⊗ m}) = 0`: a section of degree `n` is replaced by a power of degree `m`, which has
the same nonvanishing locus, and in degree `m` the lift is
`Stacks.AmpleSurjectiveThickening.exists_preimage_powNonvanishingOpen_eq_of_isZero_h1`. -/
theorem sectionsLiftAfterPower_of_isZero_h1 [IsClosedImmersion i]
    (hvan : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ n ∣ m ∧
      Limits.IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
            ((tensorPowModule X L (m : ℤ))))))) :
    Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L := by
  intro n hn t _
  obtain ⟨m, hm, hdvd, hz⟩ := hvan n hn
  obtain ⟨t₁, ht₁⟩ := Stacks.Ample.exists_tensorPow_nonvanishingLocus_eq_of_dvd
    (Stacks.AmpleLocallyClosed.pullbackModule i L) hm hdvd t
  obtain ⟨t', ht'⟩ := exists_preimage_powNonvanishingOpen_eq_of_isZero_h1 i L m hz t₁
  exact ⟨m, hm, t', ht'.trans (TopologicalSpace.Opens.ext ht₁)⟩

/-- **`i^* L` ample `⟹` `L` ample when `H¹(X, 𝓘 ⊗ L^{⊗ m})` vanishes in arbitrarily high
degrees `m`**, for a surjective closed immersion `i : Z ⟶ X` onto a locally Noetherian scheme,
with ideal sheaf `𝓘`. -/
theorem isAmple_of_isAmple_modulePullback_of_isZero_h1 [IsClosedImmersion i] [Surjective i]
    [IsLocallyNoetherian X]
    (hvan : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ n ∣ m ∧
      Limits.IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
            ((tensorPowModule X L (m : ℤ)))))))
    (h : IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L)) :
    IsAmple X L :=
  isAmple_of_isAmple_modulePullback i L (sectionsLiftAfterPower_of_isZero_h1 i L hvan) h

/-- **`i^* L` ample `⟺` `L` ample when `H¹(X, 𝓘 ⊗ L^{⊗ m})` vanishes in arbitrarily high
degrees `m`.** -/
theorem isAmple_modulePullback_iff_of_isZero_h1 [IsClosedImmersion i] [Surjective i]
    [IsNoetherian X]
    (hvan : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ n ∣ m ∧
      Limits.IsZero (((AlgebraicGeometry.moduleGlobalSections X).rightDerived 1).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))).obj
            ((tensorPowModule X L (m : ℤ))))))) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔ IsAmple X L :=
  isAmple_modulePullback_iff i L (sectionsLiftAfterPower_of_isZero_h1 i L hvan)

/-- **[Stacks, Tag 09MS].** Let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a
homeomorphism of underlying topological spaces, and let `L` be an invertible `𝒪_X`-module. Then
`i^* L` is ample on `Z` if and only if `L` is ample on `X`. Noetherianness of `Z` follows from that
of `X`, since `i` is a closed immersion, and is not assumed. -/
@[stacks 09MS]
theorem isAmple_modulePullback_iff_isAmple_of_isHomeomorph [IsClosedImmersion i] [IsNoetherian X]
    (hi : IsHomeomorph i.base) :
    IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L) ↔ IsAmple X L :=
  have : Surjective i := ⟨hi.surjective⟩
  isAmple_modulePullback_iff_isAmple i L

end Stacks.AmpleSurjectiveThickening

end
