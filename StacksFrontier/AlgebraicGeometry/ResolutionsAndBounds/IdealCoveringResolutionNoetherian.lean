module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.GlobalSections
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ExternalTensorResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealPowTensorPower

/-!
# A finite affine covering cut out by ideals which are finite locally free quotients

The Noetherian case of the substantial direction of [Stacks, Tag 0F89].  Let `X` be a Noetherian
scheme equipped with

1. a finite affine open covering `X = U 0 ∪ ⋯ ∪ U (m - 1)`,
2. quasi-coherent sheaves of ideals `I j` with `X ∖ V(I j) = U j`, and
3. for each `j` a finite locally free `𝒪_X`-module `𝓔 j` and an epimorphism `𝓔 j ⟶ I j`.

Then `X` has the resolution property.

Given a coherent `𝒪_X`-module `𝓕`, it is generated over each `U j` by finitely many sections
`s`, and each such section is the image of the unit section of `(I j)ⁿ` under a morphism
`(I j)ⁿ ⟶ 𝓕` ([Stacks, Tag 01YB]).  A power of `I j` is a quotient of a tensor power of `𝓔 j`
(`AlgebraicGeometry.exists_isFiniteLocallyFree_epi_idealPow_of_epi`), so each pair (member of the
covering, generator over it) contributes a morphism to `𝓕` out of a finite locally free module.
Taking the biproduct over the finitely many pairs turns those morphisms into a single one, and it
is surjective because its image contains, near every point, a set of generators.

## Main results

* `AlgebraicGeometry.exists_factor_isFiniteLocallyFree_fin` and
  `AlgebraicGeometry.exists_factor_isFiniteLocallyFree_sigma`: finitely many morphisms into a
  module from finite locally free modules factor through a single finite locally free module.
* `AlgebraicGeometry.exists_isFiniteLocallyFree_epi_hom_app_oneSection_of_epi`: one member of the
  covering and one section over it — a section of `𝓕` over `X ∖ V(I)` is the image of the unit
  section under a morphism `Iⁿ ⟶ 𝓕` with `n` positive, and `Iⁿ` is a quotient of a finite locally
  free module.
* `AlgebraicGeometry.exists_isFiniteLocallyFree_hom_app_eq_smul_restrict_of_epi`: for a section
  `s` of `𝓕` over `X ∖ V(I)`, a morphism `φ : 𝓟 ⟶ 𝓕` out of a finite locally free module such that
  every multiple of `s` is, near each point, the image under `φ` of a section of `𝓟`.
* `AlgebraicGeometry.hasResolutionProperty_of_epi_idealPow_of_isNoetherian`: the Noetherian
  case of the substantial direction of [Stacks, Tag 0F89].

## Implementation notes

**Why the exponent is forced to be positive.** [Stacks, Tag 01YB] produces some exponent `n`,
possibly zero, and `I⁰` is the whole structure sheaf, onto which `𝓔` need not surject.  The
exponent is therefore raised by one before hypothesis (3) is used: the inclusion
`I^{n+1} ⟶ Iⁿ` carries the unit section to the unit section
(`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowMap_app_oneSection`), so the morphism to
`𝓕` survives the change and nothing about the section is lost.

**The vanishing locus.** Hypothesis (2) is stated as an equality of opens
`(I j).support.compl = U j` rather than as an equality of sets, because that open is the one over
which the unit section of a power of `I j` is defined.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Collecting finitely many finite locally free modules -/

/-- **Finitely many morphisms into `𝓕` out of finite locally free modules factor through a
single finite locally free module**, for a family indexed by `Fin k`: the biproduct of the `k`
modules. -/
theorem exists_factor_isFiniteLocallyFree_fin (F : X.Modules) :
    ∀ (k : ℕ) (P : Fin k → X.Modules),
      (∀ l, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (P l)) →
      ∀ φ : (l : Fin k) → (P l ⟶ F),
      ∃ (Q : X.Modules) (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) Q)
        (θ : Q ⟶ F), ∀ l, ∃ ι : P l ⟶ Q, ι ≫ θ = φ l := by
  intro k
  induction k with
  | zero => exact fun P _ φ ↦ ⟨0, isFiniteLocallyFree_zero X, 0, fun l ↦ l.elim0⟩
  | succ k ih =>
    intro P hP φ
    obtain ⟨Q'', hQ'', θ'', hfac⟩ := ih (fun j ↦ P j.succ) (fun j ↦ hP _) fun j ↦ φ j.succ
    have hQ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (P 0 ⊞ Q'' : X.Modules) :=
      have := hP 0
      have := hQ''
      SheafOfModules.isFiniteLocallyFree_biprod _ _
    refine ⟨P 0 ⊞ Q'', hQ, biprod.fst ≫ φ 0 + biprod.snd ≫ θ'', ?_⟩
    refine Fin.cases ⟨biprod.inl, by simp⟩ fun j ↦ ?_
    obtain ⟨ι₀, hι₀⟩ := hfac j
    exact ⟨ι₀ ≫ biprod.inr, by simp [hι₀]⟩

/-- **Finitely many morphisms into `𝓕` out of finite locally free modules factor through a
single finite locally free module**, for a family indexed by a dependent pair of `Fin`s. -/
theorem exists_factor_isFiniteLocallyFree_sigma (F : X.Modules) {m : ℕ} (k : Fin m → ℕ)
    (P : (j : Fin m) → Fin (k j) → X.Modules)
    (hP : ∀ j l, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (P j l))
    (φ : (j : Fin m) → (l : Fin (k j)) → (P j l ⟶ F)) :
    ∃ (Q : X.Modules) (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) Q)
      (θ : Q ⟶ F), ∀ j l, ∃ ι : P j l ⟶ Q, ι ≫ θ = φ j l := by
  choose Qj hQj θj hfacj using fun j : Fin m ↦
    exists_factor_isFiniteLocallyFree_fin F (k j) (P j) (hP j) (φ j)
  obtain ⟨Q, hQ, θ, hfac⟩ := exists_factor_isFiniteLocallyFree_fin F m Qj hQj θj
  refine ⟨Q, hQ, θ, fun j l ↦ ?_⟩
  obtain ⟨ι, hι⟩ := hfacj j l
  obtain ⟨κ, hκ⟩ := hfac j
  exact ⟨ι ≫ κ, by rw [Category.assoc, hκ, hι]⟩

/-! ### One member of the covering and one section over it -/

/-- **One piece of the substantial direction of [Stacks, Tag 0F89].** Let `X` be Noetherian, let
`I` be a quasi-coherent sheaf of ideals which is the quotient of a finite locally free module,
and let `𝓕` be quasi-coherent.  Every section `s` of `𝓕` over the open complement of `V(I)` is
the image of the unit section of `Iⁿ` under a morphism `Iⁿ ⟶ 𝓕`, for an `n` for which `Iⁿ` is a
quotient of a finite locally free module. -/
theorem exists_isFiniteLocallyFree_epi_hom_app_oneSection_of_epi [IsNoetherian X]
    (I : X.IdealSheafData) {E : X.Modules}
    (hE : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
    {e : E ⟶ idealPow I 1} (he : Epi e) (F : X.Modules) [F.IsQuasicoherent]
    (s : Γ(F, (I.support.compl : X.Opens))) :
    ∃ (n : ℕ) (P : X.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P)
      (ε : P ⟶ idealPow I n) (_ : Epi ε) (ψ : idealPow I n ⟶ F),
      ψ.app (I.support.compl : X.Opens) (oneSection I n) = s := by
  obtain ⟨n, ψ, hψ⟩ := exists_hom_idealPow_app_oneSection_eq_of_isQuasicoherent I F s
  obtain ⟨P, hP, ε, hε⟩ :=
    exists_isFiniteLocallyFree_epi_idealPow_of_epi I hE he (n := n + 1) (Nat.succ_ne_zero n)
  refine ⟨n + 1, P, hP, ε, hε, idealPowMap I (Nat.le_succ n) ≫ ψ, ?_⟩
  rw [Scheme.Modules.Hom.comp_app]
  change ψ.app (I.support.compl : X.Opens)
    ((idealPowMap I (Nat.le_succ n)).app (I.support.compl : X.Opens) (oneSection I (n + 1))) = s
  rw [idealPowMap_app_oneSection, hψ]

/-- **One piece of the substantial direction of [Stacks, Tag 0F89].** For a section `s` of `𝓕`
over an open identified with the complement of `V(I)` there are a finite locally free module `𝓟`
and a morphism `φ : 𝓟 ⟶ 𝓕` such that every multiple `c · s`, restricted to a neighbourhood of a
given point, is the image under `φ` of a section of `𝓟`.

The passage to a neighbourhood is necessary: `φ` is the composite of an epimorphism `𝓟 ⟶ Iⁿ`
with a morphism `Iⁿ ⟶ 𝓕`, and an epimorphism of sheaves has preimages of sections only
locally. -/
theorem exists_isFiniteLocallyFree_hom_app_eq_smul_restrict_of_epi [IsNoetherian X]
    (I : X.IdealSheafData) {E : X.Modules}
    (hE : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
    {e : E ⟶ idealPow I 1} (he : Epi e) (F : X.Modules) [F.IsQuasicoherent]
    {W₀ : X.Opens} (hW₀ : (I.support.compl : X.Opens) = W₀) (s : Γ(F, W₀)) :
    ∃ (P : X.Modules) (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P)
      (φ : P ⟶ F),
      ∀ (W' : X.Opens) (hW' : W' ≤ W₀) (c : Γ(X, W')) (p : X), p ∈ W' →
        ∃ (W'' : X.Opens) (h : W'' ≤ W'), p ∈ W'' ∧ ∃ u : Γ(P, W''),
          φ.app W'' u =
            F.presheaf.map (homOfLE h).op (c • F.presheaf.map (homOfLE hW').op s) := by
  subst hW₀
  obtain ⟨n, P, hP, ε, hε, ψ, hψ⟩ :=
    exists_isFiniteLocallyFree_epi_hom_app_oneSection_of_epi I hE he F s
  refine ⟨P, hP, ε ≫ ψ, fun W' hW' c p hp ↦ ?_⟩
  obtain ⟨W'', h, hpW'', u, hu⟩ := exists_app_eq_of_epi ε hε W'
    (c • (idealPow I n).presheaf.map (homOfLE hW').op (oneSection I n)) p hp
  refine ⟨W'', h, hpW'', u, ?_⟩
  have h1 : (ε ≫ ψ).app W'' u = ψ.app W'' (ε.app W'' u) := rfl
  rw [h1, hu, app_map_homOfLE ψ h]
  refine congrArg (fun y ↦ (F.presheaf.map (homOfLE h).op) y) ?_
  rw [Scheme.Modules.Hom.app_smul, app_map_homOfLE ψ hW', hψ]

/-! ### The Noetherian case -/

/-- **The Noetherian case of the substantial direction of [Stacks, Tag 0F89].** Let `X` be a
Noetherian scheme with a finite affine open covering `U`, let `I j` be quasi-coherent sheaves of
ideals whose vanishing loci are the complements of the `U j`, and suppose each `I j` is the
quotient of a finite locally free `𝒪_X`-module.  Then `X` has the resolution property. -/
theorem hasResolutionProperty_of_epi_idealPow_of_isNoetherian [IsNoetherian X] {m : ℕ}
    (U : Fin m → X.Opens) (I : Fin m → X.IdealSheafData)
    (hU : ∀ j, IsAffineOpen (U j)) (hcov : ⨆ j, U j = ⊤)
    (hsupp : ∀ j, ((I j).support.compl : X.Opens) = U j)
    (E : Fin m → X.Modules)
    (hE : ∀ j, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E j))
    (e : ∀ j, E j ⟶ idealPow (I j) 1) (he : ∀ j, Epi (e j)) :
    HasResolutionProperty X := by
  classical
  refine ⟨fun F _ _ ↦ ?_⟩
  have : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType F
  choose k s hs using fun j : Fin m ↦
    exists_fin_sections_generating_of_isCoherent F ⟨U j, hU j⟩
  choose Pm hPm φ hφ using fun (j : Fin m) (l : Fin (k j)) ↦
    exists_isFiniteLocallyFree_hom_app_eq_smul_restrict_of_epi (I j) (hE j) (he j) F
      (hsupp j) (s j l)
  obtain ⟨Q, hQ, θ, hfac⟩ := exists_factor_isFiniteLocallyFree_sigma F k Pm hPm φ
  choose ι hι using hfac
  refine ⟨Q, hQ, θ, epi_of_exists_app_eq θ fun W t p hp ↦ ?_⟩
  obtain ⟨j, hpj⟩ := Opens.mem_iSup.mp (hcov ▸ trivial : p ∈ ⨆ j, U j)
  obtain ⟨W₂, h₂, h₃, hpW₂, c, hc⟩ :=
    hs j (show W ⊓ U j ≤ U j from inf_le_right)
      (F.presheaf.map (homOfLE (inf_le_left : W ⊓ U j ≤ W)).op t) p ⟨hp, hpj⟩
  choose Wl hWl hpWl u hu using fun l ↦ hφ j l W₂ h₃ (c l) p hpW₂
  obtain ⟨Wc, hpWc, hWcW₂, hWcl⟩ := exists_opens_mem_le_of_fin Wl hpWl W₂ hpW₂
  refine ⟨Wc, hWcW₂.trans (h₂.trans inf_le_left), hpWc,
    ∑ l, (ι j l).app Wc ((Pm j l).presheaf.map (homOfLE (hWcl l)).op (u l)), ?_⟩
  refine Eq.trans (map_sum (θ.app Wc).hom _ Finset.univ) ?_
  have hterm : ∀ l : Fin (k j),
      θ.app Wc ((ι j l).app Wc ((Pm j l).presheaf.map (homOfLE (hWcl l)).op (u l)))
        = F.presheaf.map (homOfLE hWcW₂).op
            (c l • F.presheaf.map (homOfLE h₃).op (s j l)) := by
    intro l
    have h4 : θ.app Wc ((ι j l).app Wc
          ((Pm j l).presheaf.map (homOfLE (hWcl l)).op (u l)))
        = (φ j l).app Wc ((Pm j l).presheaf.map (homOfLE (hWcl l)).op (u l)) :=
      congrArg (fun χ ↦ Scheme.Modules.Hom.app χ Wc
        ((Pm j l).presheaf.map (homOfLE (hWcl l)).op (u l))) (hι j l)
    rw [h4, app_map_homOfLE (φ j l) (hWcl l), hu l, map_homOfLE_map_homOfLE]
  rw [Finset.sum_congr rfl fun l _ ↦ hterm l, ← map_sum (F.presheaf.map (homOfLE hWcW₂).op).hom,
    ← hc, map_homOfLE_map_homOfLE, map_homOfLE_map_homOfLE]

end AlgebraicGeometry

end

end
