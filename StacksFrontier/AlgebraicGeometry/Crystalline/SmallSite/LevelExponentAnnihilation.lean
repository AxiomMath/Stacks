module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalLevelQuotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsCosimplicialModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemLevelRings

/-!
# `p^{N + e}` annihilates the sections over the level `e` of the system of [Stacks, Tag 07JN]

The levels of `Crystalline.GlobalCrystallineSituation.SmallSite.wholeSpaceSystem` are
`T(n)_e = Spec(D(n)/(p)^{N + e})` for the uniform shift `N = Crystalline.uniformLevel`, by
`...SmallSite.wholeSpaceSystemLevelRingEquiv`.  So `p^{N + e}` is zero in the section ring of the
level `(n, e)`, and therefore annihilates the sections over that level of **every** sheaf of
`𝒪_{X/S}`-modules.

That statement is needed in two places.

* The module documentation of
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelLimitPAdicComplete.lean` records, of its result
  (07JB) for a shifted tower, that what is *not* done there is "the verification that `p^{N+e}`
  annihilates `Γ(T_e, ℱ)`", which it calls "the statement that the level `e` of the system is cut
  out by `(p)^{N+e}`".  That is `nsmul_pow_p_wholeSpaceSystem_eq_zero` below.
* It is **one of the two implications of the kernel clause of the crystal property**, the
  distinguishing hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG].  That clause,
  `...SmallSite.IsCrystalLevelQuotient`'s second half, is

  `levelMap … x = 0 ↔ ∃ y, x = p^{N + e} • y`,

  and the direction `←` needs nothing but the annihilation: a `p^{N + e}`-multiple restricts to a
  `p^{N + e}`-multiple of a section over the level `e`, and `p^{N + e}` is zero there.  The
  direction `→` is the crystal property proper — the source's footnote at
  [Stacks, Lemma 60.19.3, Tag 07LF] says that under the hypotheses of [Stacks, Tag 07JN] alone
  "we don't know that `M(n)_e = M(n)_{e+1}/p^e M(n)_{e+1}`.  If `ℱ` is a crystal then this does
  hold" — and nothing here proves it.

So what this module buys for [Stacks, Tag 07LG] is that the hypothesis `hker` of
`...SmallSite.computes07LG_of_doubleComplex` becomes the **implication** rather than the
equivalence: `isCrystalLevelQuotient_wholeSpaceSystem_of_ker_le` takes only
`levelMap … x = 0 → ∃ y, x = p^{N + e} • y`.  As a hypothesis it is weaker than the equivalence,
whose other direction is `levelMap_nsmul_pow_p_eq_zero`.

## The exponent

The exponent is `wholeSpaceLevelExponent hp e = N + e` and **not** `e`.  This is the shift that
already made the tower lemma `Stacks.AdicCompletion.InverseLimit.invLimit_isAdicComplete`
([Stacks, Tag 0G1Q]) unusable for this system — at `e = 0` its hypothesis reads `M_0 = 0` — and
forced `Crystalline.isPAdicallyComplete_invLimit_of_shift` to be proved outright.  Every statement
below is phrased with `...SmallSite.wholeSpaceLevelExponent` for that reason.

## Main results

* `DividedPowers.cast_pow_pAdicIdeal_pow_eq_zero` — `p^k = 0` in `R/(p)^k`.
* `...SmallSite.pow_cast_p_wholeSpaceSystem_eq_zero` — `p^{N + e} = 0` in the section *ring* of the
  level `(n, e)` of the system of [Stacks, Tag 07JN].
* `...SmallSite.nsmul_pow_p_wholeSpaceSystem_eq_zero` — **`p^{N + e}` annihilates the sections of
  every sheaf of `𝒪_{X/S}`-modules over the level `(n, e)`**, and
  `...SmallSite.nsmul_pow_p_abelianSheaf_wholeSpaceSystem_eq_zero` the same for the underlying
  abelian sheaf at the coefficient universe `u + 1`.
* `...SmallSite.pow_p_smul_levelSections_eq_zero` — the same annihilation read over `D(n)`, that is
  for the `...SmallSite.levelSectionsModule` structure the sections carry.  This is the shape
  `Crystalline.pAdicIdeal_pow_smul_top_eq_bot_iff` consumes, and hence the input
  `Crystalline.isPAdicallyComplete_invLimit_of_shift` wants for (07JB).
* `...SmallSite.levelMap_nsmul_pow_p_eq_zero` — a `p^{N + e}`-multiple is in the kernel of the
  level restriction `M(n)_{e + 1} ⟶ M(n)_e`; the easy half of the kernel clause.
* `...SmallSite.isCrystalLevelQuotient_wholeSpaceSystem_of_ker_le` — **the crystal property from
  the kernel inclusion alone**, the improvement of
  `...SmallSite.isCrystalLevelQuotient_wholeSpaceSystem_of_ker`.

## What is and is not proved

**No tag attribute is placed in this module.**  [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`.  Nothing below proves the crystal property:
`isCrystalLevelQuotient_wholeSpaceSystem_of_ker_le` carries the inclusion
`ker ⊆ p^{N + e} M(n)_{e + 1}` as a hypothesis, which is the whole of the source's footnote.  The
reverse inclusion is proved, by `levelMap_nsmul_pow_p_eq_zero`.

## References

* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace DividedPowers

/-- **`p^k` is zero in `R/(p)^k`.**  The `p`-adic ideal is principal, so its `k`-th power is
generated by `p^k`, which is therefore in it. -/
theorem cast_pow_pAdicIdeal_pow_eq_zero {R : Type*} [CommRing R] (m k : ℕ) :
    ((m : R ⧸ pAdicIdeal (A := R) m ^ k)) ^ k = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (pAdicIdeal (A := R) m ^ k)) m, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem, pAdicIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

end DividedPowers

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-- **`p^{N + e}` is zero in the section ring of the level `(n, e)` of the system of
[Stacks, Tag 07JN].**

That ring is `D(n)/(p)^{N + e}` by `...SmallSite.wholeSpaceSystemLevelRingEquiv`, with
`N + e = ...SmallSite.wholeSpaceLevelExponent hp e`, and `p^{N + e}` is zero in such a quotient by
`DividedPowers.cast_pow_pAdicIdeal_pow_eq_zero`. -/
theorem pow_cast_p_wholeSpaceSystem_eq_zero (n e : ℕ) :
    ((S.p : ((structureSheaf S).val.obj
        (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e)) : Type u))) ^
      wholeSpaceLevelExponent hp e = 0 := by
  refine (wholeSpaceSystemLevelRingEquiv hp n e).injective ?_
  rw [map_pow, map_natCast, map_zero]
  exact DividedPowers.cast_pow_pAdicIdeal_pow_eq_zero _ _

/-- **`p^{N + e}` annihilates the sections of a sheaf of `𝒪_{X/S}`-modules over the level `(n, e)`
of the system of [Stacks, Tag 07JN]**, for every sheaf of modules and with no hypothesis on it:
the `ℕ`-action on the sections is the action of the section ring through the cast, and `p^{N + e}`
is zero in that ring by `pow_cast_p_wholeSpaceSystem_eq_zero`.

This is the verification that the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelLimitPAdicComplete.lean` lists as not done there for
its result (07JB): that the level `e` of the system is cut out by `(p)^{N + e}`. -/
theorem nsmul_pow_p_wholeSpaceSystem_eq_zero (F : SheafOfModules.{u} (structureSheaf S)) (n e : ℕ)
    (s : (F.val.obj (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e)) : Type u)) :
    S.p ^ wholeSpaceLevelExponent hp e • s = 0 := by
  rw [← Nat.cast_smul_eq_nsmul ((structureSheaf S).val.obj
    (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e)) : Type u), Nat.cast_pow,
    pow_cast_p_wholeSpaceSystem_eq_zero hp n e, zero_smul]

/-- **`p^{N + e}` annihilates the sections over the level `(n, e)` read over `D(n)`.**

The sections carry a `D(n)`-module structure, `...SmallSite.levelSectionsModule`, by restriction of
scalars along the quotient `D(n) ⟶ D(n)/(p)^{N + e} = Γ(T(n)_e, 𝒪)`; `p^{N + e}` goes to zero
there, so it acts as zero.

This is the spelling `Crystalline.pAdicIdeal_pow_smul_top_eq_bot_iff` of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelLimitPAdicComplete.lean` takes, and through it the
annihilation hypothesis of `Crystalline.isPAdicallyComplete_invLimit_of_shift`, that module's
result (07JB) for a tower cut out at a shifted exponent.  Its module documentation lists this
verification as not done there. -/
theorem pow_p_smul_levelSections_eq_zero (F : SheafOfModules.{u} (structureSheaf S)) (n e : ℕ)
    (x : (F.val.obj (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e)) : Type u)) :
    ((S.p : ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) ^ wholeSpaceLevelExponent hp e) •
      x = 0 := by
  rw [levelSectionsModule_smul, map_pow, map_natCast, pow_cast_p_wholeSpaceSystem_eq_zero,
    zero_smul]

/-- **`p^{N + e}` annihilates the sections over the level `(n, e)` of the abelian sheaf underlying
a sheaf of `𝒪_{X/S}`-modules**, at the coefficient universe `u + 1` in which the cohomology of
`Cris(X/S)` is computed.  This is `nsmul_pow_p_wholeSpaceSystem_eq_zero` read inside the universe
lift, the `ℕ`-action of `...SmallSite.abelianSheaf` being that of the sheaf of modules applied
componentwise. -/
theorem nsmul_pow_p_abelianSheaf_wholeSpaceSystem_eq_zero
    (F : SheafOfModules.{u} (structureSheaf S)) (n e : ℕ)
    (x : (abelianSheaf F).val.obj (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e))) :
    S.p ^ wholeSpaceLevelExponent hp e • x = 0 :=
  ULift.ext _ _ (nsmul_pow_p_wholeSpaceSystem_eq_zero hp F n e x.down)

/-- **The easy half of the kernel clause of the crystal property**: a `p^{N + e}`-multiple is in
the kernel of the level restriction `M(n)_{e + 1} ⟶ M(n)_e` of [Stacks, Tag 07JN].

The restriction map is additive, so it carries `p^{N + e} • y` to `p^{N + e}` times a section over
the level `e`, and `p^{N + e}` annihilates those by
`nsmul_pow_p_abelianSheaf_wholeSpaceSystem_eq_zero`.  This holds for every sheaf of modules and
needs neither local quasi-coherence, nor surjectivity of the closed-immersion comparison maps, nor
the crystal condition.

The converse inclusion is the crystal property proper and is **not** proved anywhere in this
library; see the module documentation. -/
theorem levelMap_nsmul_pow_p_eq_zero (F : SheafOfModules.{u} (structureSheaf S)) (n e : ℕ)
    (y : (abelianSheaf F).val.obj
      (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))) :
    levelMap (wholeSpaceSystem S hp) (abelianSheaf F).val n e
        (S.p ^ wholeSpaceLevelExponent hp e • y) = 0 := by
  rw [map_nsmul, nsmul_pow_p_abelianSheaf_wholeSpaceSystem_eq_zero]

/-- **The crystal property of [Stacks, Tag 07LG] from the kernel *inclusion* alone.**

`...SmallSite.isCrystalLevelQuotient_wholeSpaceSystem_of_ker` reduces
`...SmallSite.IsCrystalLevelQuotient` for the system of [Stacks, Tag 07JN] to the equivalence
`levelMap … x = 0 ↔ ∃ y, x = p^{N + e} • y`.  Only the forward implication is content: the reverse
one is `levelMap_nsmul_pow_p_eq_zero`, proved above for every sheaf of modules.  So the crystal
property costs exactly

`ker(M(n)_{e + 1} ⟶ M(n)_e) ⊆ p^{N + e} M(n)_{e + 1}`

on top of the two hypotheses of [Stacks, Tag 07JN], and that inclusion is the whole of the
source's footnote at [Stacks, Lemma 60.19.3, Tag 07LF].

`hF` and `hM` are those two hypotheses and are **not removable**: the surjectivity clause of the
conclusion is `...SmallSite.surjective_wholeSpaceSystem_level_map`, which runs on them. -/
theorem isCrystalLevelQuotient_wholeSpaceSystem_of_ker_le
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (hker : ∀ (n e : ℕ)
      (x : (abelianSheaf F).val.obj
        (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))),
      levelMap (wholeSpaceSystem S hp) (abelianSheaf F).val n e x = 0 →
        ∃ y, x = S.p ^ wholeSpaceLevelExponent hp e • y) :
    IsCrystalLevelQuotient (wholeSpaceSystem S hp) (abelianSheaf F).val
      (wholeSpaceLevelExponent hp) :=
  isCrystalLevelQuotient_wholeSpaceSystem_of_ker hp F hF hM fun n e x =>
    ⟨hker n e x, fun ⟨y, hy⟩ => hy ▸ levelMap_nsmul_pow_p_eq_zero hp F n e y⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
