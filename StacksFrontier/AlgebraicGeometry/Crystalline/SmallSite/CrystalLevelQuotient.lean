module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRestrictionSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceEnvelope

/-!
# The crystal property `M(n)_e = M(n)_{e+1} / p^e M(n)_{e+1}`

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine and `p` nilpotent
on `Γ(X, 𝒪_X)`, and write `M(n)_e = Γ((X, T(n)_e, δ(n)), ℱ)` for the sections of a coefficient
sheaf over the levels of the cosimplicial system of thickenings of
[Stacks, Proposition 60.20.1, Tag 07JN], as `...SmallSite.levelCosimplicialSections` does.

This module states the property

`M(n)_e = M(n)_{e+1} / p^e M(n)_{e+1}`,

which is **the hypothesis that distinguishes [Stacks, Proposition 60.21.3, Tag 07LG] from
[Stacks, Lemma 60.19.3, Tag 07LF]**.  The source's proof of [Stacks, Tag 07LF] carries a footnote
saying that under the hypotheses of [Stacks, Tag 07JN] alone "we don't know that
`M(n)_e = M(n)_{e+1}/p^e M(n)_{e+1}`.  If `ℱ` is a crystal then this does hold", and that is
exactly why [Stacks, Tag 07LF] has to argue through a limit of acyclic complexes while
[Stacks, Tag 07LG] may work with the `p`-adic completion directly: the property is what makes
`lim_e (M(n)_e ⊗_{D(n)} Ω^i_{D(n)})` the `p`-adic completion of `M(n) ⊗_{D(n)} Ω^i_{D(n)}`.

Until now this library had the property **only as prose**, in the module documentation of
`SmallSite/WholeSpaceEnvelope.lean`, `SmallSite/TensorSheafVanishing.lean` and
`SmallSite/LevelLimitAcyclicity.lean`, each quoting the footnote and each saying the completed
route "is the reduction to aim at for [Stacks, Tag 07LG]".  What was *proved* was the strictly
weaker **surjectivity** of `M(n)_{e+1} → M(n)_e`
(`...SmallSite.surjective_wholeSpaceSystem_level_map`), which is all [Stacks, Tag 07LF] needs and
which holds under the hypotheses of [Stacks, Tag 07JN].  The two are different statements, and the
difference is the whole distance between the two tags.

## How the property is spelled

`...SmallSite.IsCrystalLevelQuotient` asks, of every `n` and `e`, two things of the restriction
map `M(n)_{e+1} → M(n)_e`:

* that it is surjective — the first half, already proved for the system of [Stacks, Tag 07JN] and
  the abelian sheaf of a coefficient sheaf satisfying that proposition's two hypotheses;
* that its kernel is exactly `p^{ℓ(e)} M(n)_{e+1}` — the second half, which is what the crystal
  property adds and which this library does not derive from anything.

The exponent is carried as a function `ℓ : ℕ → ℕ` rather than being `e` on the nose, because the
levels this library's system is built from are not the source's: `...SmallSite.wholeSpaceSystem`
in bidegree `(n, e)` is `D(n) / (p)^{N + e}` for `N = Crystalline.uniformLevel`, that uniform shift
being what makes every level a `p`-adic level of every `D(n)` at once.  So the property for the
library's system is `...IsCrystalLevelQuotient _ _ (fun e ↦ Crystalline.uniformLevel _ + e)`, and
writing `ℓ` makes the shift visible instead of silently wrong.

The kernel clause is stated as the equality of the kernel with the set of `p^{ℓ(e)}`-multiples,
which is the source's equality of `M(n)_e` with the quotient read through the surjection; the two
clauses together are packaged as the isomorphism
`...SmallSite.crystalLevelQuotientEquiv`.

## Main definitions

* `...SmallSite.IsCrystalLevelQuotient` — **the crystal property**, the distinguishing hypothesis
  of [Stacks, Tag 07LG].
* `...SmallSite.crystalLevelQuotientEquiv` — it packaged as
  `M(n)_{e+1} / p^{ℓ(e)} M(n)_{e+1} ≅ M(n)_e`.

## Main results

* `...SmallSite.surjective_level_map_of_isCrystalLevelQuotient` — the first clause, read off.
* `...SmallSite.mem_ker_level_map_iff_of_isCrystalLevelQuotient` and
  `...SmallSite.ker_level_map_of_isCrystalLevelQuotient` — the second clause as a statement about
  the kernel of the restriction map.
* `...SmallSite.isCrystalLevelQuotient_iff_of_surjective` — **what the crystal property adds over
  what is proved**: given the surjectivity that [Stacks, Tag 07JN]'s hypotheses already supply,
  the property is equivalent to the kernel clause alone.  This is the precise measure of the gap
  between [Stacks, Tag 07LF] and [Stacks, Tag 07LG] in this library.

No tag attribute is placed: this is a hypothesis of [Stacks, Tag 07LG], not a tag of its own, and
nothing here proves it.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- **The restriction map `M(n)_{e+1} → M(n)_e`** of a cosimplicial system of thickenings, as an
additive map of the groups of sections. -/
public def levelMap (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (n e : ℕ) :
    G.obj (op ((T.obj (op ⦋n⦌)).obj (e + 1))) →+ G.obj (op ((T.obj (op ⦋n⦌)).obj e)) :=
  ConcreteCategory.hom (G.map ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op)

/-- **The crystal property `M(n)_e = M(n)_{e+1} / p^{ℓ(e)} M(n)_{e+1}`.**

This is the hypothesis of [Stacks, Proposition 60.21.3, Tag 07LG] that [Stacks, Lemma 60.19.3,
Tag 07LF] does not have, and the only reason the completed route is valid for the first and not
the second.  It says of the restriction map `M(n)_{e+1} → M(n)_e` that it is surjective *and* that
its kernel is exactly the subgroup of `p^{ℓ(e)}`-multiples; together those two say that
`M(n)_e` is the quotient the source names.

`ℓ` is the exponent of `p` cutting out the level `e`, carried as a parameter because the levels of
`...SmallSite.wholeSpaceSystem` are `D(n) / (p)^{N + e}` for the uniform shift
`N = Crystalline.uniformLevel`, not `D(n) / (p)^e`.  See the module documentation.

**Surjectivity alone is strictly weaker and is what the library already proves**, in
`...SmallSite.surjective_wholeSpaceSystem_level_map`; see
`...SmallSite.isCrystalLevelQuotient_iff_of_surjective`. -/
public def IsCrystalLevelQuotient (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
    (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (ℓ : ℕ → ℕ) : Prop :=
  ∀ n e : ℕ, Function.Surjective (levelMap T G n e) ∧
    ∀ x : G.obj (op ((T.obj (op ⦋n⦌)).obj (e + 1))),
      levelMap T G n e x = 0 ↔ ∃ y, x = S.p ^ ℓ e • y

variable {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
  {G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} {ℓ : ℕ → ℕ}

/-- The first clause of the crystal property: the restriction maps are surjective. -/
public theorem surjective_level_map_of_isCrystalLevelQuotient
    (h : IsCrystalLevelQuotient T G ℓ) (n e : ℕ) : Function.Surjective (levelMap T G n e) :=
  (h n e).1

/-- The second clause of the crystal property, read on the kernel: an element of `M(n)_{e+1}`
restricts to zero in `M(n)_e` exactly when it is `p^{ℓ(e)}` times something. -/
public theorem mem_ker_level_map_iff_of_isCrystalLevelQuotient
    (h : IsCrystalLevelQuotient T G ℓ) (n e : ℕ)
    (x : G.obj (op ((T.obj (op ⦋n⦌)).obj (e + 1)))) :
    x ∈ (levelMap T G n e).ker ↔ ∃ y, x = S.p ^ ℓ e • y :=
  (h n e).2 x

/-- The second clause of the crystal property, as an equality of subgroups: the kernel of the
restriction map is `p^{ℓ(e)} M(n)_{e+1}`. -/
public theorem ker_level_map_of_isCrystalLevelQuotient
    (h : IsCrystalLevelQuotient T G ℓ) (n e : ℕ) :
    ((levelMap T G n e).ker : Set (G.obj (op ((T.obj (op ⦋n⦌)).obj (e + 1))))) =
      Set.range fun y : G.obj (op ((T.obj (op ⦋n⦌)).obj (e + 1))) => S.p ^ ℓ e • y := by
  ext x
  rw [Set.mem_range]
  refine ((h n e).2 x).trans ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

/-- **The crystal property packaged as the isomorphism the source writes**:
`M(n)_e = M(n)_{e+1} / p^{ℓ(e)} M(n)_{e+1}`.  The quotient is taken by the kernel of the
restriction map, which
`...SmallSite.ker_level_map_of_isCrystalLevelQuotient` identifies with the subgroup of
`p^{ℓ(e)}`-multiples; the isomorphism itself is the surjectivity clause. -/
public def crystalLevelQuotientEquiv (h : IsCrystalLevelQuotient T G ℓ) (n e : ℕ) :
    (G.obj (op ((T.obj (op ⦋n⦌)).obj (e + 1))) ⧸ (levelMap T G n e).ker) ≃+
      G.obj (op ((T.obj (op ⦋n⦌)).obj e)) :=
  QuotientAddGroup.quotientKerEquivOfSurjective (levelMap T G n e) (h n e).1

/-- **Exactly what the crystal property adds to what the library proves.**

The surjectivity of the restriction maps is available for the system of [Stacks, Tag 07JN] under
that proposition's own hypotheses, by
`...SmallSite.surjective_wholeSpaceSystem_level_map`.  Given it, the crystal property is
equivalent to the kernel clause alone.  So the gap between [Stacks, Tag 07LF] and
[Stacks, Tag 07LG] in this library is precisely the statement that the kernel of
`M(n)_{e+1} → M(n)_e` is `p^{ℓ(e)} M(n)_{e+1}`, and nothing else. -/
public theorem isCrystalLevelQuotient_iff_of_surjective
    (hsurj : ∀ n e : ℕ, Function.Surjective (levelMap T G n e)) :
    IsCrystalLevelQuotient T G ℓ ↔
      ∀ (n e : ℕ) (x : G.obj (op ((T.obj (op ⦋n⦌)).obj (e + 1)))),
        levelMap T G n e x = 0 ↔ ∃ y, x = S.p ^ ℓ e • y :=
  ⟨fun h n e => (h n e).2, fun h n e => ⟨hsurj n e, h n e⟩⟩

/-! ### The property for the system of [Stacks, Tag 07JN] -/

section WholeSpace

variable [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]

/-- **The exponent of `p` cutting out the level `e` of `...SmallSite.wholeSpaceSystem`.**  It is
`N + e` for the uniform shift `N = Crystalline.uniformLevel`, not `e`: the level `e` member of the
system is `D(n) / (p)^{N + e}`, by
`...SmallSite.wholeSpaceSystem_obj_obj`. -/
public def wholeSpaceLevelExponent (e : ℕ) : ℕ :=
  _root_.Crystalline.uniformLevel (affineSituation S hp) + e

/-- **The surjectivity half of the crystal property, for the system of [Stacks, Tag 07JN] and the
abelian sheaf of a coefficient sheaf satisfying that proposition's two hypotheses.**

This is `...SmallSite.surjective_wholeSpaceSystem_level_map` in the spelling
`...SmallSite.IsCrystalLevelQuotient` asks for.  It is everything the library has towards the
crystal property; the kernel clause is not derived from these hypotheses and, by the source's
footnote, is not expected to follow from them. -/
public theorem surjective_levelMap_wholeSpaceSystem
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val) (n e : ℕ) :
    Function.Surjective (levelMap (wholeSpaceSystem S hp) (abelianSheaf F).obj n e) :=
  surjective_wholeSpaceSystem_level_map hp F hF hM n e

/-- **The crystal property for the system of [Stacks, Tag 07JN] reduces to its kernel clause.**

The surjectivity clause is discharged by
`...SmallSite.surjective_levelMap_wholeSpaceSystem` from the two hypotheses of
[Stacks, Tag 07JN], so what remains of the distinguishing hypothesis of [Stacks, Tag 07LG] is
exactly: the kernel of `M(n)_{e+1} → M(n)_e` is `p^{N+e} M(n)_{e+1}`. -/
public theorem isCrystalLevelQuotient_wholeSpaceSystem_of_ker
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsLocallyQuasiCoherent F)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (hker : ∀ (n e : ℕ)
      (x : (abelianSheaf F).obj.obj
        (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj (e + 1)))),
      levelMap (wholeSpaceSystem S hp) (abelianSheaf F).obj n e x = 0 ↔
        ∃ y, x = S.p ^ wholeSpaceLevelExponent hp e • y) :
    IsCrystalLevelQuotient (wholeSpaceSystem S hp) (abelianSheaf F).obj
      (wholeSpaceLevelExponent hp) :=
  (isCrystalLevelQuotient_iff_of_surjective
    (surjective_levelMap_wholeSpaceSystem hp F hF hM)).2 hker

end WholeSpace

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
