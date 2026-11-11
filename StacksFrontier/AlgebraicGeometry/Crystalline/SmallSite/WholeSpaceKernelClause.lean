module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineBaseChangeSmall
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceLevelDropRing
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemAffine

/-!
# `hker`: the kernel clause of [Stacks, Tag 07LG] for a general quasi-coherent crystal

The distinguishing hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG] over the cosimplicial
system `(X, T(n)_e, δ(n))` of [Stacks, Proposition 60.20.1, Tag 07JN] is
`...SmallSite.IsCrystalLevelQuotient`, and its two clauses are surjectivity of the restriction
map `M(n)_{e+1} ⟶ M(n)_e` and the description of its kernel as `p^{N+e} M(n)_{e+1}`.  The first
is `...SmallSite.surjective_levelMap_wholeSpaceSystem`.  The second — the hypothesis `hker` of
`...SmallSite.computes07LG_of_doubleComplex` and of
`...SmallSite.computes07LG_of_doubleComplexSmall` — was proved only at the coefficient sheaf
`𝒪_{X/S}`, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrystalLevelQuotientStructure.lean`, where
the levels are the quotient rings `D(n)/(p)^{N+e}` outright.

**This module proves it for an arbitrary quasi-coherent crystal.**  Three inputs come together:

* the sections of a crystal over an object of `Cris(X/S)` with affine ambient scheme are the base
  change of its sections along a morphism of the site —
  `...SmallSite.crysRestrict_eq_zero_iff_exists_nsmul`;
* the objects of the system have affine ambient scheme —
  `...SmallSite.isAffine_target_wholeSpaceSystem`;
* the restriction map of `𝒪_{X/S}` along a level drop is surjective with kernel `(p^{N+e})` —
  `...SmallSite.surjective_levelRestrict_structureSheaf` and
  `...SmallSite.levelRestrict_structureSheaf_eq_zero_iff_dvd`.

This is exactly the source's footnote at [Stacks, Lemma 60.19.3, Tag 07LF]: "we don't know that
`M(n)_e = M(n)_{e+1}/p^e M(n)_{e+1}`.  If `ℱ` is a crystal then this does hold."

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `levelMap_abelianSheaf_eq_zero_iff_crysRestrict` — the restriction map of the abelian sheaf
  along a level drop is the restriction map of the sheaf of modules, inside the universe lift.
* `levelMap_abelianSheaf_eq_zero_iff_of_isSheafCrystal` — **the kernel clause for a locally
  quasi-coherent crystal**, in the spelling `...SmallSite.IsCrystalLevelQuotient` asks for.
* `isCrystalLevelQuotient_wholeSpaceSystem_of_isSheafCrystal` — **the whole crystal property for
  a locally quasi-coherent crystal with surjective closed-immersion comparison maps.**
* `hker_of_h07IT` — **the hypothesis `hker` of `...SmallSite.computes07LG_of_doubleComplexSmall`,
  discharged**, from that theorem's own hypothesis `h07IT` ([Stacks, Lemma 60.14.2, Tag 07IT]) and
  nothing else.

## What is and is not proved

**No tag attribute is placed in this module.**  [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamDerivedPlusIso` of
`SmallSite/CrystalDeRhamDerived07LG.lean`.  The hypothesis list of
`...SmallSite.computes07LG_of_doubleComplexSmall` is `K`, `hcolumns`, `rowTarget`, `rowComparison`,
`hrows`, `hrow0`, `hcolumn0`, `hker`; what falls here is `hker`, for every quasi-coherent
coefficient sheaf.  The others are untouched.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.14.2, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp] (F : SheafOfModules.{u} (structureSheaf S))

/-- **The restriction map of the underlying abelian sheaf along a level drop is the restriction
map of the sheaf of modules, inside the universe lift.**  `...SmallSite.abelianSheaf` is the
underlying abelian sheaf composed with `AddCommGrpCat.uliftFunctor`, so its restriction maps are
those of the sheaf of modules applied inside `ULift`. -/
theorem levelMap_abelianSheaf_eq_zero_iff_crysRestrict (n e : ℕ)
    (x : (abelianSheaf F).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))) :
    levelMap (wholeSpaceSystem S hp) (abelianSheaf F).obj n e x = 0 ↔
      crysRestrict F (levelDrop hp n e) x.down = 0 :=
  ⟨fun h ↦ congrArg ULift.down h, fun h ↦ ULift.ext h⟩

/-- **A section of the underlying abelian sheaf is `m` times a section exactly when its component
is**, the `ℕ`-action of `...SmallSite.abelianSheaf` being that of the sheaf of modules applied
inside `ULift`. -/
theorem exists_nsmul_abelianSheaf_iff (n e m : ℕ)
    (x : (abelianSheaf F).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))) :
    (∃ y, x = m • y) ↔ ∃ y, x.down = m • y :=
  ⟨fun ⟨y, hy⟩ ↦ ⟨y.down, congrArg ULift.down hy⟩,
    fun ⟨y, hy⟩ ↦ ⟨ULift.up y, ULift.ext hy⟩⟩

/-- **The kernel clause of the crystal property of [Stacks, Proposition 60.21.3, Tag 07LG], for a
locally quasi-coherent crystal on `Cris(X/S)`.**

A section of `ℱ` over the level `(n, e + 1)` of [Stacks, Tag 07JN] restricts to zero over the
level `(n, e)` exactly when it is `p^{N + e}` times a section over `(n, e + 1)`.

The level drop `T(n)_e ⟶ T(n)_{e+1}` has affine ambient schemes on both sides, and its
restriction map on the sections of `𝒪_{X/S}` is surjective with kernel the principal ideal
`(p^{N+e})`; so `...SmallSite.crysRestrict_eq_zero_iff_exists_nsmul` applies.  **The crystal
hypothesis is what the source's footnote at [Stacks, Lemma 60.19.3, Tag 07LF] says cannot be
dispensed with**; local quasi-coherence is hypothesis (1) of [Stacks, Tag 07JN]. -/
theorem levelMap_abelianSheaf_eq_zero_iff_of_isSheafCrystal
    (hF : IsLocallyQuasiCoherent F) (hcrys : IsSheafCrystal F) (n e : ℕ)
    (x : (abelianSheaf F).obj.obj
      (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))) :
    levelMap (wholeSpaceSystem S hp) (abelianSheaf F).obj n e x = 0 ↔
      ∃ y, x = S.p ^ wholeSpaceLevelExponent hp e • y := by
  have := isAffine_target_wholeSpaceSystem hp n (e + 1)
  have := isAffine_target_wholeSpaceSystem hp n e
  rw [levelMap_abelianSheaf_eq_zero_iff_crysRestrict hp F n e x,
    crysRestrict_eq_zero_iff_exists_nsmul F (levelDrop hp n e) hF hcrys
      (surjective_levelRestrict_structureSheaf hp n e) (wholeSpaceLevelExponent hp e)
      (levelRestrict_structureSheaf_eq_zero_iff_dvd hp n e) x.down]
  exact (exists_nsmul_abelianSheaf_iff hp F n e (S.p ^ wholeSpaceLevelExponent hp e) x).symm

/-- **The crystal property of [Stacks, Proposition 60.21.3, Tag 07LG] for a locally quasi-coherent
crystal on `Cris(X/S)`**, under hypotheses (1) and (2) of [Stacks, Tag 07JN] and the crystal
condition.

The surjectivity clause is `...SmallSite.surjective_levelMap_wholeSpaceSystem`, which is what
`hF` and `hM` are for; the kernel clause is
`levelMap_abelianSheaf_eq_zero_iff_of_isSheafCrystal`, which is what `hcrys` is for.

**This is not [Stacks, Tag 07LG]** and no tag attribute is placed: the property is one hypothesis
of that proposition. -/
theorem isCrystalLevelQuotient_wholeSpaceSystem_of_isSheafCrystal
    (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (hcrys : IsSheafCrystal F) :
    IsCrystalLevelQuotient (wholeSpaceSystem S hp) (abelianSheaf F).obj
      (wholeSpaceLevelExponent hp) :=
  isCrystalLevelQuotient_wholeSpaceSystem_of_ker hp F hF hM
    (fun n e x ↦ levelMap_abelianSheaf_eq_zero_iff_of_isSheafCrystal hp F hF hcrys n e x)

/-- **The hypothesis `hker` of `...SmallSite.computes07LG_of_doubleComplexSmall`, discharged for
every quasi-coherent coefficient sheaf.**

Its statement is the binder of that theorem verbatim; the only input is that theorem's own
hypothesis `h07IT`, which is [Stacks, Lemma 60.14.2, Tag 07IT] — quasi-coherent sheaves of
modules on `Cris(X/S)` are crystals.  Local quasi-coherence comes from quasi-coherence by
`...SmallSite.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`.

Compared with `...SmallSite.levelMap_abelianSheaf_unit_eq_zero_iff`, which is the same clause at
the single coefficient sheaf `𝒪_{X/S}` and carries no hypothesis at all, this covers every
quasi-coherent `ℱ` and costs `h07IT`. -/
theorem hker_of_h07IT
    (h07IT : ∀ G : SheafOfModules.{u} (structureSheaf S),
      G.IsQuasicoherentOnSite → IsSheafCrystal G) :
    ∀ (G : SheafOfModules.{u} (structureSheaf S)) (_hG : G.IsQuasicoherentOnSite) (n e : ℕ)
      (x : (abelianSheaf G).obj.obj
        (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))),
      levelMap (wholeSpaceSystem S hp) (abelianSheaf G).obj n e x = 0 →
        ∃ y, x = S.p ^ wholeSpaceLevelExponent hp e • y :=
  fun G hG n e x ↦ (levelMap_abelianSheaf_eq_zero_iff_of_isSheafCrystal hp G
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite G hG) (h07IT G hG) n e x).1

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
