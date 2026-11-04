module

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.LinearEmbedding
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.VeryAmple
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ChartTwistOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 01VT: the two relative very ampleness conditions, and all six at once

`StacksFrontier/AlgebraicGeometry/AmpleRelativeFiniteType/Basic.lean` proves four of the six
equivalent conditions of [Stacks, Tag 01VT] — (1), (2), (5) and (6) — unconditionally. The two it
omits, (3) and (4), assert relative very ampleness of `L ^⊗ d`, and the sole obstruction to them
was the module half of [Stacks, Tag 01OE]: that the isomorphism `ℙⁿ_S ≅ 𝐏(𝒪_S^{n+1})` carries one
hyperplane sheaf to the other. That comparison, named
`Stacks.SymGraded.HasFreeBundleTwistOne`, **is a theorem over an affine base**
(`Stacks.SymGraded.hasFreeBundleTwistOne`, in
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/ChartTwistOne.lean`), and Tag 01VT
hypothesises an affine base. This file supplies (3) and (4) from it and assembles the six-term
equivalence **with no named input**.

The passage is the source's own "as `ℙⁿ_S` is a projective bundle over `S`". An immersion
`i : X ⟶ ℙⁿ_S` over `S` with `L ^⊗ d ≅ i ^* 𝒪(1)` becomes the immersion
`i ≫ (projectiveBundleIsoProjectiveSpace n).inv` into `𝐏(𝒪_S^{n+1})` over `S`, and the
comparison of hyperplane sheaves turns the pinning isomorphism into one with
`𝒪_{𝐏(𝒪_S^{n+1})}(1)`, which is [Stacks, Tag 01VM] verbatim.

## Main results

* `Stacks.AmpleRelativeFiniteType.isRelativelyVeryAmple_of_hasImmersionTwistOver`: **the source's
  (5) at a single degree implies its (3) at that degree**, on the module half of Tag 01OE.
* `Stacks.AmpleRelativeFiniteType.isRelativelyAmple_of_exists_isRelativelyVeryAmple`:
  **(3) ⟹ (2), unconditionally** — [Stacks, Tag 01VN] followed by the relative half of
  [Stacks, Tag 01PT].
* `Stacks.AmpleRelativeFiniteType.tfae_six`: **[Stacks, Tag 01VT], all six conditions, with no
  named input.**
* `Stacks.AmpleRelativeFiniteType.isAmple_iff_exists_isRelativelyVeryAmple` and
  `isAmple_iff_eventually_isRelativelyVeryAmple`: the two equivalences with (1) read off the
  list.
* `Stacks.AmpleRelativeFiniteType.tfae_six_pos`: **the same six, with the source's own immersion
  clauses** — `∃ n ≥ 1` rather than `∃ n : ℕ` for the dimension of the projective space.

## The route

The cycle is (1) ⟹ (6) ⟹ (4) ⟹ (3) ⟹ (2) ⟹ (1), with (5) attached to (1) in both directions.
Every edge but (6) ⟹ (4) comes from `Stacks.AmpleRelativeFiniteType.tfae` or is unconditional:

* (1) ⟹ (6), (1) ⟺ (5) and (2) ⟹ (1) are read off the four-term list, so they carry
  [Stacks, Tag 01VS] and both halves of [Stacks, Tag 01VK] with them;
* (6) ⟹ (4) is the projective-bundle passage above, at each sufficiently large degree, and is the
  only step that consumes `Stacks.SymGraded.HasFreeBundleTwistOne`, which the affine base
  supplies as a theorem;
* (4) ⟹ (3) is instantiating the degree bound at itself;
* (3) ⟹ (2) is [Stacks, Tag 01VN] — relatively very ample implies relatively ample, available
  with no premise beyond quasi-compactness — and then the relative half of [Stacks, Tag 01PT],
  which descends relative ampleness from a positive tensor power.

## Implementation notes

**The comparison is needed at every `n`, not at one.** The degree of the projective space is
existentially quantified inside `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`, so
`Stacks.AmpleRelativeFiniteType.isRelativelyVeryAmple_of_hasImmersionTwistOver` — which is
stated at an arbitrary base and therefore still carries the comparison as a hypothesis — asks
for `∀ m, Stacks.SymGraded.HasFreeBundleTwistOne S m`. Over the affine base of Tag 01VT every
instance is `Stacks.SymGraded.hasFreeBundleTwistOne`, so `tfae_six` has no hypothesis.

**`Stacks.AmpleRelativeFiniteType.tfae_six` carries the keyed Tag 01VT attribute**, as do the
two equivalences with (1) read off it; the four-term
`Stacks.AmpleRelativeFiniteType.tfae` keeps the attribute it already carried, its note saying
which four of the six it states.

**Conditions (5) and (6) of `tfae_six` are taken with no lower bound on `n`**, exactly as in the
four-term list: `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver` writes `∃ n : ℕ` where
the source writes `∃ n ≥ 1`. The two are equivalent —
`Stacks.AmpleProjectiveImmersion.hasImmersionTwistOverPos_iff`, by the linear embedding
`ℙⁿ_S ↪ ℙᴺ_S` — and `Stacks.AmpleRelativeFiniteType.tfae_six_pos` is the list with the source's
clauses written out.

## References

* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01PT](https://stacks.math.columbia.edu/tag/01PT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Ample
open Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.AmpleRelativeFiniteType

variable {X S : Scheme.{u}}

/-! ### The projective-bundle passage: the source's (5) gives its (3) -/

/-- **An immersion into `ℙⁿ_S` over `S` pinning `M` to `𝒪(1)` makes `M` very ample relative to
`f`**, given the module half of [Stacks, Tag 01OE] at the degree the immersion produces.

This is the source's "as `ℙⁿ_S` is a projective bundle over `S`". Composing with the inverse of
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace` turns the immersion into one into
`𝐏(𝒪_S^{n+1}) = Proj_S(Sym(𝒪_S^{n+1}))`, still over `S` because the isomorphism is one over `S`;
`Stacks.SymGraded.nonempty_pullback_projectiveSpaceTwistingSheaf_iso_twistOne` turns the pinning
isomorphism into one with the glued degree-one twist. -/
theorem isRelativelyVeryAmple_of_hasImmersionTwistOver
    (hbundle : ∀ m : ℕ, Stacks.SymGraded.HasFreeBundleTwistOne S m) (f : X ⟶ S) (M : X.Modules)
    [IsInvertibleModule X M] (hM : HasImmersionTwistOver f M) :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f M := by
  obtain ⟨m, i, him, hover, ⟨e⟩⟩ := hM
  obtain ⟨t⟩ :=
    Stacks.SymGraded.nonempty_pullback_projectiveSpaceTwistingSheaf_iso_twistOne (X := S) m
      (hbundle m)
  set j := (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := S) m).inv with hj
  have hji : j ≫ (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := S) m).hom = 𝟙 _ :=
    Iso.inv_hom_id _
  -- `𝒪(1)` on `ℙⁿ_S` is the inverse image of the bundle's degree-one twist along `j`.
  have eInv : (Scheme.Modules.pullback j).obj
      (Stacks.Tag01VMVeryAmple.twistOne
        (Stacks.SymGraded.freeModule (Stacks.SymGraded.coordIndex.{u} m))) ≅
      projectiveSpaceTwistingSheaf m S :=
    (Scheme.Modules.pullback j).mapIso t.symm ≪≫
      (Scheme.Modules.pullbackComp j
        (Stacks.SymGraded.projectiveBundleIsoProjectiveSpace (X := S) m).hom).app _ ≪≫
      (Scheme.Modules.pullbackCongr hji).app _ ≪≫ (Scheme.Modules.pullbackId _).app _
  refine Stacks.Tag01VMVeryAmple.isRelativelyVeryAmple_of_immersion f M
    (Stacks.SymGraded.freeModule (Stacks.SymGraded.coordIndex.{u} m)) (i ≫ j) ?_ ?_ ?_
  · have : IsImmersion i := him
    infer_instance
  · have hfst : j ≫ (Stacks.SymGraded.freeProjectiveBundle (X := S) m).toBase =
        Limits.pullback.fst (Limits.terminal.from S)
          (Limits.terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} m)) := by
      rw [← Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst (X := S) m, hj,
        Iso.inv_hom_id_assoc]
    rw [Category.assoc, hfst]
    exact hover
  · exact e ≪≫ (Scheme.Modules.pullback i).mapIso eInv.symm ≪≫
      (Scheme.Modules.pullbackComp i j).app _

/-! ### The unconditional edge: (3) implies (2) -/

/-- **(3) ⟹ (2) of [Stacks, Tag 01VT], unconditionally**: if some positive tensor power of `L` is
very ample relative to a quasi-compact `f`, then `L` is ample relative to `f`.

[Stacks, Tag 01VN] (`Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple`) makes that
power ample relative to `f`, and the relative half of [Stacks, Tag 01PT]
(`Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule`) descends
relative ampleness to `L` itself. -/
@[ega "II 4.5.10" "more general", ega "II 4.6.2" "more general"]
theorem isRelativelyAmple_of_exists_isRelativelyVeryAmple (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d : ℕ, 1 ≤ d ∧
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨d, hd, hva⟩ := h
  exact Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule f L d hd
    (Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple f _ hf hva)

/-! ### [Stacks, Tag 01VT], all six conditions -/

/-- **[Stacks, Tag 01VT], all six conditions, with no named input.** For
`f : X ⟶ S` of finite type with `S` affine and `L` an invertible `𝒪_X`-module, the following are
equivalent:

1. `L` is ample on `X`;
2. `L` is ample relative to `f`;
3. `L ^⊗ d` is very ample relative to `f`, for some `d ≥ 1`;
4. `L ^⊗ d` is very ample relative to `f`, for every sufficiently large `d`;
5. `L ^⊗ d` is `𝒪(1)` pulled back along an immersion `X ⟶ ℙⁿ_S` over `S`, for some `d ≥ 1`;
6. the same, for every sufficiently large `d`.

The cycle is (1) ⟹ (6) ⟹ (4) ⟹ (3) ⟹ (2) ⟹ (1), with (5) attached to (1) in both directions.
Only (6) ⟹ (4) uses the module half of [Stacks, Tag 01OE], which over an affine base is
`Stacks.SymGraded.hasFreeBundleTwistOne`; see the module documentation for the rest.

Conditions (5) and (6) are taken with no lower bound on `n`, as in
`Stacks.AmpleRelativeFiniteType.tfae`. -/
@[stacks 01VT "all six conditions, with no named input: ampleness, `f`-ampleness, relative \
  very ampleness of some and of every sufficiently high tensor power, and the two immersion \
  clauses; the immersion clauses are taken with no lower bound on the dimension `n` of the \
  projective space, where the source writes `n ≥ 1` — the two agree by \
  `Stacks.AmpleProjectiveImmersion.hasImmersionTwistOverPos_iff`, and \
  `Stacks.AmpleRelativeFiniteType.tfae_six_pos` is the list with the source's clauses"]
theorem tfae_six [IsAffine S]
    (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    List.TFAE [
      IsAmple X L,
      Stacks.RelativeAmple.IsRelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧
        Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ)),
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOver f (tensorPowModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOver f (tensorPowModule X L (d : ℤ))] := by
  have hbundle : ∀ m : ℕ, Stacks.SymGraded.HasFreeBundleTwistOne S m := fun m =>
    Stacks.SymGraded.hasFreeBundleTwistOne S m
  tfae_have 1 → 6 := fun h => ((tfae f L).out 1 4).mp h
  tfae_have 6 → 4 := by
    rintro ⟨d₀, hd₀, h⟩
    exact ⟨d₀, hd₀, fun d hd =>
      isRelativelyVeryAmple_of_hasImmersionTwistOver hbundle f _ (h d hd)⟩
  tfae_have 4 → 3 := by
    rintro ⟨d₀, hd₀, h⟩
    exact ⟨d₀, hd₀, h d₀ le_rfl⟩
  tfae_have 3 → 2 := fun h =>
    isRelativelyAmple_of_exists_isRelativelyVeryAmple f L ‹QuasiCompact f› h
  tfae_have 2 → 1 := fun h => ((tfae f L).out 2 1).mp h
  tfae_have 1 → 5 := fun h => ((tfae f L).out 1 3).mp h
  tfae_have 5 → 1 := fun h => ((tfae f L).out 3 1).mp h
  tfae_finish

/-- **The equivalence of (1) and (3) of [Stacks, Tag 01VT]**: `L` is ample exactly when some
tensor power `L ^⊗ d` with `d ≥ 1` is very ample relative to `f`. -/
@[stacks 01VT "the equivalence of conditions (1) and (3): ampleness and relative very ampleness \
  of some positive tensor power"]
theorem isAmple_iff_exists_isRelativelyVeryAmple [IsAffine S] (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsAmple X L ↔ ∃ d : ℕ, 1 ≤ d ∧
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ)) :=
  (tfae_six f L).out 1 3

/-- **The equivalence of (1) and (4) of [Stacks, Tag 01VT]**: `L` is ample exactly when every
sufficiently high tensor power of `L` is very ample relative to `f`. -/
@[stacks 01VT "the equivalence of conditions (1) and (4): ampleness and relative very ampleness \
  of every sufficiently high tensor power", ega "II 4.5.10" "more general"]
theorem isAmple_iff_eventually_isRelativelyVeryAmple [IsAffine S] (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsAmple X L ↔ ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ)) :=
  (tfae_six f L).out 1 4

/-! ### The immersion clauses with the source's lower bound on the dimension -/

/-- **[Stacks, Tag 01VT], all six conditions, with the source's own immersion clauses.** The
immersion clauses (5) and (6) are
`Stacks.AmpleProjectiveImmersion.HasImmersionTwistOverPos`, which writes `∃ n ≥ 1` as the source
does, rather than `Stacks.AmpleProjectiveImmersion.HasImmersionTwistOver`'s `∃ n : ℕ`.

The two agree — `Stacks.AmpleProjectiveImmersion.hasImmersionTwistOverPos_iff` — because an
immersion into `ℙⁿ_S` composed with the linear embedding `ℙⁿ_S ↪ ℙᴺ_S` is an immersion into
`ℙᴺ_S` carrying the same hyperplane sheaf, so a witness at `n` gives one at `max n 1`. This is
therefore `Stacks.AmpleRelativeFiniteType.tfae_six` with two clauses rewritten, and the tag's
six conditions hold verbatim. -/
@[stacks 01VT "all six conditions verbatim and with no named input: ampleness, `f`-ampleness, \
  relative very ampleness of some and of every sufficiently high tensor power, and the two \
  immersion clauses with the source's lower bound `n ≥ 1` on the dimension of the projective \
  space"]
theorem tfae_six_pos [IsAffine S] (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    List.TFAE [
      IsAmple X L,
      Stacks.RelativeAmple.IsRelativelyAmple f L,
      ∃ d : ℕ, 1 ≤ d ∧
        Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f (tensorPowModule X L (d : ℤ)),
      ∃ d : ℕ, 1 ≤ d ∧ HasImmersionTwistOverPos f (tensorPowModule X L (d : ℤ)),
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        HasImmersionTwistOverPos f (tensorPowModule X L (d : ℤ))] := by
  simp only [← hasImmersionTwistOverPos_iff]
  exact tfae_six f L

end Stacks.AmpleRelativeFiniteType

end
