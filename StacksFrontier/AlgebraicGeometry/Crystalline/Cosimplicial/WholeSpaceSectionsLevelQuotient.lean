module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRestrictionSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceKernelClause
public import StacksFrontier.RingTheory.AdicCompletion.TowerLevelQuotient

/-!
# The sections of a crystal over a level are the quotient `M(n) / p^{N+e} M(n)`

Let `ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` and let

`M(n) = lim_e Γ((X, T(n)_e, δ(n)), ℱ)`

be the module of the cosimplicial degree `n` of [Stacks, Proposition 60.20.1, Tag 07JN]. The
reduction `M(n) ⟶ Γ(T(n)_e, ℱ)` identifies the sections over the level `e` with
`M(n) / p^{N+e} M(n)`, for the uniform shift `N = Crystalline.uniformLevel` at which the levels of
that system are cut out.

## Implementation notes

Item (07JB), `p`-adic completeness of `M(n)`
(`...SmallSite.isPAdicallyComplete_wholeSpaceLevelScalars_sections`), does not give this
identification: it is proved from the annihilation of the levels alone, with no hypothesis on the
restriction maps of the system. The identification also uses the crystal property of
[Stacks, Proposition 60.21.3, Tag 07LG], `...SmallSite.IsCrystalLevelQuotient`: the restriction
`M(n)_{e+1} ⟶ M(n)_e` is surjective with kernel `p^{N+e} M(n)_{e+1}`. Surjectivity is
`...SmallSite.surjective_wholeSpaceSystem_level_map` under hypotheses (1) and (2) of
[Stacks, Tag 07JN], and the kernel clause is `...SmallSite.crysRestrict_eq_zero_iff_exists_nsmul`,
which is what the source's footnote at [Stacks, Lemma 60.19.3, Tag 07LF] says the crystal
condition buys. The passage from the levelwise statement to the statement about the limit is
`Crystalline.PAdicCompletion.towerLevelEquiv`, where precompleteness of `M(n)`, the other half of
item (07JB), is consumed.

## Main definitions

* `wholeSpaceSectionsValHom` — the reduction `M(n) ⟶ Γ(T(n)_e, ℱ)` as a `D̂(n)`-linear map, the
  target carrying the scalars of `...SmallSite.levelSectionsScalars`.
* `wholeSpaceSectionsLevelEquiv` — the identification `M(n) / p^{N+e} M(n) ≅ Γ(T(n)_e, ℱ)`.

## Main results

* `surjective_wholeSpaceSectionsVal` — the limit surjects onto every level.
* `nsmul_pow_wholeSpaceSectionsLevel_eq_zero` — `p^{N+e}` annihilates the level `e`.
* `exists_nsmul_of_levelRestrict_eq_zero` — the kernel clause of the crystal property, on the
  sections of `ℱ` rather than on the universe-lifted abelian sheaf.
* `mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero` — the level `N+e` of the `p`-adic
  filtration of `M(n)` is the kernel of the reduction to the level `e`.

## What is and is not proved

**No `@[stacks …]` attribute is placed and no tag is proved here.**  The hypotheses are the
source's own: Situation [Stacks, Tag 07MD] with `X` and `S` affine and `p` nilpotent, a crystal in
quasi-coherent `𝒪_{X/S}`-modules — which supplies both quasi-coherence and the crystal condition —
and hypothesis (2) of [Stacks, Tag 07JN], surjectivity of the closed-immersion comparison maps,
which is carried because nothing in the tree derives it.

## References

* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Simplicial

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp] (Fc : QuasiCoherentCrystal S)

/-! ### The reduction to a level as a `D̂(n)`-linear map -/

/-- **The sections of `ℱ` over the level `e` of the cosimplicial degree `n`, as a module over the
degree `n` of the completed cosimplicial envelope `D̂(*)`**, by restriction of scalars along
`...SmallSite.levelSectionsScalars`.  This is the scalar action
`...SmallSite.wholeSpaceSectionsVal_smul` reads the action on `M(n)` through, so it is the one
that makes the reduction linear. -/
local instance moduleWholeSpaceLevelSections (n : SimplexCategory) (e : ℕ) :
    Module ((wholeSpaceEnvelopeRing hp).obj n : Type u)
      (Fc.obj.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e))) :=
  Module.compHom _ (levelSectionsScalars hp n e)

/-- **The reduction `M(n) ⟶ Γ(T(n)_e, ℱ)` to a level, as a `D̂(n)`-linear map.**  Additivity is
`...SmallSite.wholeSpaceSectionsVal_add` and linearity is
`...SmallSite.wholeSpaceSectionsVal_smul`, the scalars of the target being the ones restricted
along `...SmallSite.levelSectionsScalars`. -/
def wholeSpaceSectionsValHom (n : SimplexCategory) (e : ℕ) :
    wholeSpaceSections hp Fc n →ₗ[((wholeSpaceEnvelopeRing hp).obj n : Type u)]
      Fc.obj.val.obj (op (((wholeSpaceSystem S hp).obj (op n)).obj e)) where
  toFun m := wholeSpaceSectionsVal hp Fc m e
  map_add' x y := wholeSpaceSectionsVal_add hp Fc x y e
  map_smul' r m := wholeSpaceSectionsVal_smul hp Fc r m e

/-- The reduction `wholeSpaceSectionsValHom` sends `m` to its component at the level `e`. -/
@[simp] theorem wholeSpaceSectionsValHom_apply (n : SimplexCategory) (e : ℕ)
    (m : wholeSpaceSections hp Fc n) :
    wholeSpaceSectionsValHom hp Fc n e m = wholeSpaceSectionsVal hp Fc m e := rfl

/-! ### The four tower hypotheses -/

/-- **A section of `M(n)` dying at a level dies at every lower level**, the component at the lower
level being the restriction of the one at the higher. -/
theorem wholeSpaceSectionsVal_eq_zero_of_le (n : SimplexCategory) {a b : ℕ} (hab : a ≤ b)
    (m : wholeSpaceSections hp Fc n) (h : wholeSpaceSectionsVal hp Fc m b = 0) :
    wholeSpaceSectionsVal hp Fc m a = 0 := by
  rw [← wholeSpaceSectionsVal_restrict hp Fc m (homOfLE hab), h, map_zero]
  rfl

/-- **The restriction maps of the tower of sections of a quasi-coherent crystal are
surjective**, on the sections of the sheaf of modules rather than on the universe-lifted abelian
sheaf.  This is `...SmallSite.surjective_wholeSpaceSystem_level_map` read through `ULift`. -/
theorem surjective_levelRestrict_wholeSpaceSections
    (hM : IsSurjectiveComparison Fc.obj.val) (n e : ℕ) :
    Function.Surjective (Fc.obj.val.map
      (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op) := by
  intro y
  obtain ⟨x, hx⟩ := surjective_wholeSpaceSystem_level_map hp Fc.obj
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite Fc.obj Fc.property.1) hM n e (ULift.up y)
  exact ⟨x.down, congrArg ULift.down hx⟩

/-- **The limit `M(n)` surjects onto the sections over every level.**  The lifts above the level
are chosen one at a time and the levels below it are reached by restriction, which is
`...exists_levelSectionsLimit_val_eq`; the one-step surjectivity it needs is
`surjective_levelRestrict_wholeSpaceSections`. -/
theorem surjective_wholeSpaceSectionsVal (hM : IsSurjectiveComparison Fc.obj.val) (n e : ℕ) :
    Function.Surjective fun m : wholeSpaceSections hp Fc ⦋n⦌ ↦
      wholeSpaceSectionsVal hp Fc m e := by
  intro s
  obtain ⟨m, hm⟩ := exists_levelSectionsLimit_val_eq
    (T := (wholeSpaceSystem S hp).obj (op ⦋n⦌)) (F := Fc)
    (surjective_levelRestrict_wholeSpaceSections hp Fc hM n) e s
  exact ⟨wholeSpaceSectionsMk hp Fc m.val m.property,
    (wholeSpaceSectionsVal_mk hp Fc m.val m.property e).trans hm⟩

/-- **`p^{N+e}` annihilates the sections over the level `e`**, as an `ℕ`-multiple.  This is
`...SmallSite.pow_smul_eq_zero_wholeSpaceLevelSections`, in which the scalar is the ring element
`p^{N+e}` of `D(n)`; the two agree because that element is the image of the integer. -/
theorem nsmul_pow_wholeSpaceSectionsLevel_eq_zero (n e : ℕ)
    (z : Fc.obj.val.obj (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e))) :
    (S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) • z = 0 := by
  have h : ∀ w : (wholeSpaceLevelScalars hp n).levelSections Fc e,
      ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
        ((wholeSpaceSystemEnvelope hp n).ring : Type u)) • w = 0 := by
    intro w
    rw [Nat.cast_pow]
    exact pow_smul_eq_zero_wholeSpaceLevelSections hp n e Fc w
  exact (Nat.cast_smul_eq_nsmul ((wholeSpaceSystemEnvelope hp n).ring : Type u)
    (S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))
    (show (wholeSpaceLevelScalars hp n).levelSections Fc e from z)).symm.trans (h z)

/-- **The kernel clause of the crystal property, on the sections of `ℱ`.**

A section over the level `e + 1` restricting to zero over the level `e` is `p^{N+e}` times a
section.  This is `...SmallSite.crysRestrict_eq_zero_iff_exists_nsmul` at the level drop, whose
two ring-theoretic inputs are `...SmallSite.surjective_levelRestrict_structureSheaf` and
`...SmallSite.levelRestrict_structureSheaf_eq_zero_iff_dvd`, and whose affineness inputs are
`...SmallSite.isAffine_target_wholeSpaceSystem`.  The crystal condition is the source's own and is
what the footnote at [Stacks, Lemma 60.19.3, Tag 07LF] says cannot be dispensed with. -/
theorem exists_nsmul_of_levelRestrict_eq_zero (n e : ℕ)
    (y : Fc.obj.val.obj (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1))))
    (h : Fc.obj.val.map (levelDrop hp n e).op y = 0) :
    ∃ z, y = (S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) • z := by
  have := isAffine_target_wholeSpaceSystem hp n (e + 1)
  have := isAffine_target_wholeSpaceSystem hp n e
  exact (crysRestrict_eq_zero_iff_exists_nsmul Fc.obj (levelDrop hp n e)
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite Fc.obj Fc.property.1) Fc.property.2
    (surjective_levelRestrict_structureSheaf hp n e) (wholeSpaceLevelExponent hp e)
    (levelRestrict_structureSheaf_eq_zero_iff_dvd hp n e) y).1 h

/-- **The crystal property in the form `Crystalline.PAdicCompletion.towerLevelEquiv` asks for**:
a section of `M(n)` dying at the level `e` has its component at the level `e + 1` equal to
`p^{N+e}` times the component of a section of `M(n)`.  The two inputs are the kernel clause
`exists_nsmul_of_levelRestrict_eq_zero` and the surjectivity
`surjective_wholeSpaceSectionsVal`. -/
theorem exists_wholeSpaceSectionsVal_eq_nsmul (hM : IsSurjectiveComparison Fc.obj.val) (n e : ℕ)
    (m : wholeSpaceSections hp Fc ⦋n⦌) (h : wholeSpaceSectionsVal hp Fc m e = 0) :
    ∃ u : wholeSpaceSections hp Fc ⦋n⦌,
      wholeSpaceSectionsVal hp Fc m (e + 1) =
        (S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) •
          wholeSpaceSectionsVal hp Fc u (e + 1) := by
  have hres : Fc.obj.val.map (levelDrop hp n e).op
      (wholeSpaceSectionsVal hp Fc m (e + 1)) = 0 :=
    (wholeSpaceSectionsVal_restrict hp Fc m (homOfLE (Nat.le_succ e))).trans h
  obtain ⟨z, hz⟩ := exists_nsmul_of_levelRestrict_eq_zero hp Fc n e _ hres
  obtain ⟨u, hu⟩ := surjective_wholeSpaceSectionsVal hp Fc hM n (e + 1) z
  exact ⟨u, hz.trans (congrArg _ hu.symm)⟩

/-! ### The identification of the level with the quotient -/

/-- **The level `N + e` of the `p`-adic filtration of `M(n)` is the kernel of the reduction to the
level `e` of the tower of sections.**

This is `Crystalline.PAdicCompletion.mem_pow_smul_top_iff_towerLevel_eq_zero` at the reduction
`...SmallSite.wholeSpaceSectionsValHom`, with its five hypotheses discharged:
`wholeSpaceSectionsVal_eq_zero_of_le`, `exists_wholeSpaceSectionsVal_eq_nsmul`,
`nsmul_pow_wholeSpaceSectionsLevel_eq_zero`, `...SmallSite.wholeSpaceSectionsVal_injective`, and
precompleteness from item (07JB). -/
theorem mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero
    (hM : IsSurjectiveComparison Fc.obj.val) (n e : ℕ) (x : wholeSpaceSections hp Fc ⦋n⦌) :
    x ∈ (DividedPowers.pAdicIdeal
          (A := ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) S.p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) •
      (⊤ : Submodule ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)
        (wholeSpaceSections hp Fc ⦋n⦌))) ↔ wholeSpaceSectionsVal hp Fc x e = 0 :=
  PAdicCompletion.mem_pow_smul_top_iff_towerLevel_eq_zero S.p
    (wholeSpaceSectionsValHom hp Fc ⦋n⦌)
    (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (fun hab z hz ↦ wholeSpaceSectionsVal_eq_zero_of_le hp Fc ⦋n⦌ hab z hz)
    (fun a z hz ↦ exists_wholeSpaceSectionsVal_eq_nsmul hp Fc hM n a z hz)
    (fun a z ↦ nsmul_pow_wholeSpaceSectionsLevel_eq_zero hp Fc n a z)
    (fun _ hz ↦ wholeSpaceSectionsVal_injective hp Fc fun a ↦
      (hz a).trans (map_zero (wholeSpaceSectionsValHom hp Fc ⦋n⦌ a)).symm)
    e x

/-- **The sections of a quasi-coherent crystal over the level `e` of the cosimplicial degree `n`
are `M(n) / p^{N+e} M(n)`**, as a `D̂(n)`-linear equivalence. -/
def wholeSpaceSectionsLevelEquiv (hM : IsSurjectiveComparison Fc.obj.val) (n e : ℕ) :
    (wholeSpaceSections hp Fc ⦋n⦌ ⧸
        (DividedPowers.pAdicIdeal
              (A := ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) S.p ^
            (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) •
          (⊤ : Submodule ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)
            (wholeSpaceSections hp Fc ⦋n⦌)))) ≃ₗ[((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)]
      Fc.obj.val.obj (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e)) :=
  PAdicCompletion.towerLevelEquiv S.p (wholeSpaceSectionsValHom hp Fc ⦋n⦌)
    (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (fun hab z hz ↦ wholeSpaceSectionsVal_eq_zero_of_le hp Fc ⦋n⦌ hab z hz)
    (fun a z hz ↦ exists_wholeSpaceSectionsVal_eq_nsmul hp Fc hM n a z hz)
    (fun a z ↦ nsmul_pow_wholeSpaceSectionsLevel_eq_zero hp Fc n a z)
    (fun _ hz ↦ wholeSpaceSectionsVal_injective hp Fc fun a ↦
      (hz a).trans (map_zero (wholeSpaceSectionsValHom hp Fc ⦋n⦌ a)).symm)
    (fun a ↦ surjective_wholeSpaceSectionsVal hp Fc hM n a) e

/-- The class of `x` in `M(n) / p^{N+e} M(n)` is sent by `wholeSpaceSectionsLevelEquiv` to the
component of `x` at the level `e`. -/
@[simp] theorem wholeSpaceSectionsLevelEquiv_mk (hM : IsSurjectiveComparison Fc.obj.val)
    (n e : ℕ) (x : wholeSpaceSections hp Fc ⦋n⦌) :
    wholeSpaceSectionsLevelEquiv hp Fc hM n e (Submodule.Quotient.mk x) =
      wholeSpaceSectionsVal hp Fc x e := rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

end
