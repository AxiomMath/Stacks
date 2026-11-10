module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Devissage
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure

/-!
# The dévissage filtration of a coherent module, at the length it actually has

[Stacks, Tag 01YF] says that a coherent module `F` on a Noetherian scheme carries a *finite*
filtration

`0 = F₀ ⊆ F₁ ⊆ … ⊆ F_m = F`

by coherent submodules whose `m` successive quotients are direct images of ideal sheaves on
integral closed subschemes. Everything the source asserts about a quotient is asserted about the
`m` quotients that exist, and for `F = 0` the source takes `m = 0` and asserts nothing at all.

`Stacks.AlgebraicGeometry.CoherentDevissage.HasIdealDevissage` quantifies that last assertion over
**all** of `ℕ` rather than over the `n` steps of the filtration it has just produced. That is
not a harmless over-approximation: it demands an integral closed subscheme of `X` for every
natural number, so on a scheme whose underlying space is empty — where no integral closed
subscheme exists, an integral scheme being irreducible and hence nonempty — it holds for no
module whatever, not even the zero module. `Spec` of the zero ring is a Noetherian scheme of
that kind, so

`∀ (X : Scheme) (_ : IsNoetherian X) (F : X.Modules), F.IsCoherent → HasIdealDevissage F`

is **false**, and no proof of [Stacks, Tag 01YF] can discharge it. This file records that as a
theorem, replaces the predicate by the one the source states, and re-proves the dévissage engine
and its 01YG corollary against the replacement, so that a proof of 01YF — in the shape of
the tagged statement, a chain of subobjects indexed by `Fin (n + 1)` — plugs in with nothing left
over.

The bound `i < n` is what the induction consumes, and the other clauses are bounded to match:
the chain is walked from `G 0` to `G n`, so only the monomorphisms, the coherence of the terms
and the coherence of the quotients below `n` are ever used. Nothing is weakened by bounding
them, and `HasIdealDevissage F → HasIdealFiltration F` below is the one-line witness that the
replacement is implied by the old predicate wherever the old one holds.

## Main definitions

* `Stacks.AlgebraicGeometry.CoherentDevissage.HasIdealFiltration`: the conclusion of
  [Stacks, Tag 01YF] for one module, with each clause quantified over the steps of the
  filtration rather than over all of `ℕ`.

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissage.not_hasIdealDevissage_of_isEmpty`: on a scheme with
  empty underlying space `HasIdealDevissage` holds for no module.
* `Stacks.AlgebraicGeometry.CoherentDevissage.not_forall_isNoetherian_hasIdealDevissage`:
  consequently [Stacks, Tag 01YF], read as `HasIdealDevissage`, is false.
* `Stacks.AlgebraicGeometry.CoherentDevissage.hasIdealFiltration_terminal`: the zero module
  satisfies the replacement on every scheme, which is the case the source handles with `m = 0`.
* `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_hasIdealFiltration` and
  `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealFiltration`: the dévissage
  engine and [Stacks, Tag 01YG], conditional on the replacement instead.
* `Stacks.AlgebraicGeometry.CoherentDevissage.hasIdealFiltration_of_chain`: the same predicate
  from a chain that does not carry the coherence of its successive quotients, which is derivable.
* `Stacks.AlgebraicGeometry.CoherentDevissage.hasIdealFiltration_of_subobjectFiltration`: the
  conclusion of [Stacks, Tag 01YF] exactly as the tagged statement has it — a monotone chain of
  subobjects of `F` indexed by `Fin (n + 1)`, from `⊥` to `⊤`, with coherent terms and with each
  successive quotient a direct image of a nonzero coherent ideal sheaf — yields
  `HasIdealFiltration F`.

## Implementation notes

**No tag is attached to anything here.** [Stacks, Tag 01YF] is not proved: the replacement
predicate is a statement *about* a module, and the existence of a filtration satisfying it is
exactly what is still missing.

**The coherence of the successive quotients is derivable, and a correction.** The
implementation notes of `Devissage.lean` say that `HasIdealDevissage` must carry
`(cokernel (f i)).IsCoherent` as data because it "would follow from coherence of `G i` and
`G (i + 1)`" through the two-out-of-three property of coherence, "which this repository does
not have either". That is **not** the case: `Stacks.AlgebraicGeometry.ProperMapping`'s
`isCoherent_cokernel` ([Stacks, Tag 01BY] (3), cokernels) states exactly that, for the root
coherence predicate, with no hypothesis beyond coherence of the two modules. It is what
`hasIdealFiltration_of_chain` uses, so a filtration need not come with the coherence of its
quotients; the clause is kept in the predicate only so that the repair stays a one-clause
change from `HasIdealDevissage`. In particular the bridge from the tag's chain of subobjects
asks for **nothing** beyond the tag's own conclusion — not even local Noetherianness.

**`_root_.SheafOfModules.IsCoherent` is written out throughout.** Coherence is declared twice on
this branch; `HasIdealDevissage` and the engine of `Devissage.lean` are stated against the root
constant, and inside the `Stacks.` namespace an unqualified spelling can resolve to
`Stacks.SheafOfModules.IsCoherent` once that declaration is in the import closure — which it is
here, through `ProperMapping.CoherenceClosure`. Leaving it unqualified would state a different
predicate from the one being repaired.

**The chain is `ℕ`-indexed with a cut-off.** This follows `HasIdealDevissage`, so that the
induction is the plain `Nat.rec` with no index arithmetic, and so that the two predicates are
comparable clause by clause. The bridge truncates the tag's `Fin (n + 1)` index by `min · n`;
the resulting equalities of subobjects are not syntactic, so the comparison of the two
cokernels goes through `cokernel_ofLE_congr`, which substitutes the subobjects and then relies
on proof irrelevance for the two inequality witnesses.

## References

* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

variable {X : Scheme.{u}}

/-! ### The predicate the source states -/

/-- **The conclusion of [Stacks, Tag 01YF] for a single module.** `HasIdealFiltration F` says
that `F` carries a filtration of some finite length `n` by coherent submodules, starting at a
zero module and ending at `F`, each of whose `n` successive quotients is isomorphic to the
direct image along a closed immersion `Z ⟶ X`, with `Z` integral, of a quasi-coherent ideal of
`𝒪_Z`.

This is `Stacks.AlgebraicGeometry.CoherentDevissage.HasIdealDevissage` with every clause quantified
over the steps of the filtration instead of over all of `ℕ`. The difference is not cosmetic:
see `not_hasIdealDevissage_of_isEmpty`. -/
def HasIdealFiltration (F : X.Modules) : Prop :=
  ∃ (n : ℕ) (G : ℕ → X.Modules) (f : ∀ i, G i ⟶ G (i + 1)),
    (∀ i < n, Mono (f i)) ∧ IsZero (G 0) ∧
      (∀ i ≤ n, _root_.SheafOfModules.IsCoherent (G i)) ∧
      (∀ i < n, _root_.SheafOfModules.IsCoherent (cokernel (f i))) ∧
      Nonempty (G n ≅ F) ∧
      ∀ i < n, ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (_ : IsClosedImmersion ι) (_ : IsIntegral Z)
        (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
        I.toSheafOfModules.IsQuasicoherent ∧
          Nonempty (cokernel (f i) ≅
            (Scheme.Modules.pushforward ι).obj I.toSheafOfModules)

/-- The replacement is implied by the predicate it replaces: bounding the quantifiers only
discards assertions. -/
theorem hasIdealFiltration_of_hasIdealDevissage {F : X.Modules} (h : HasIdealDevissage F) :
    HasIdealFiltration F := by
  obtain ⟨n, G, f, hmono, hzeroG, hcoh, hcoker, he, hquot⟩ := h
  exact ⟨n, G, f, fun i _ => hmono i, hzeroG, fun i _ => hcoh i, fun i _ => hcoker i, he,
    fun i _ => hquot i⟩

/-- **A dévissage filtration from a chain that does not carry the coherence of its quotients.**
That coherence follows from the coherence of the two adjacent terms by [Stacks, Tag 01BY] (3),
so it need not be supplied. -/
theorem hasIdealFiltration_of_chain {F : X.Modules}
    (n : ℕ) (G : ℕ → X.Modules) (f : ∀ i, G i ⟶ G (i + 1))
    (hmono : ∀ i < n, Mono (f i)) (hzeroG : IsZero (G 0))
    (hcoh : ∀ i ≤ n, _root_.SheafOfModules.IsCoherent (G i))
    (he : Nonempty (G n ≅ F))
    (hquot : ∀ i < n, ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (_ : IsClosedImmersion ι)
      (_ : IsIntegral Z) (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent ∧
        Nonempty (cokernel (f i) ≅
          (Scheme.Modules.pushforward ι).obj I.toSheafOfModules)) :
    HasIdealFiltration F :=
  ⟨n, G, f, hmono, hzeroG, hcoh,
    fun i hi => ProperMapping.isCoherent_cokernel (hcoh i (by omega)) (hcoh (i + 1) (by omega))
      (f i),
    he, hquot⟩

/-! ### Why the replacement is necessary -/

/-- **On a scheme with empty underlying space no module has a dévissage in the sense of
`HasIdealDevissage`.** The predicate asks for an integral closed subscheme `Z ⟶ X` for every
natural number, and an integral scheme is irreducible, hence nonempty, so there is no such `Z`
at all. -/
theorem not_hasIdealDevissage_of_isEmpty [IsEmpty X] (F : X.Modules) :
    ¬ HasIdealDevissage F := by
  rintro ⟨n, G, f, -, -, -, -, -, hquot⟩
  obtain ⟨Z, ι, -, hZ, -, -, -⟩ := hquot 0
  have := hZ
  exact IsEmpty.false (ι.base (Nonempty.some inferInstance))

/-- The same statement in the form [Stacks, Tag 01YF] would have to supply. -/
theorem not_forall_hasIdealDevissage_of_isEmpty [IsEmpty X] :
    ¬ ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → HasIdealDevissage F :=
  fun h => not_hasIdealDevissage_of_isEmpty (⊤_ X.Modules) (h _ isCoherent_terminal)

/-- **[Stacks, Tag 01YF], read as `HasIdealDevissage`, is false.** `Spec` of the zero ring is a
Noetherian scheme with empty underlying space, so it carries a coherent module — the zero module
— for which the predicate fails. The source asserts nothing about a quotient in this case: it
takes the filtration to have length `0`. -/
theorem not_forall_isNoetherian_hasIdealDevissage :
    ¬ ∀ (X : Scheme.{u}) (_ : IsNoetherian X) (F : X.Modules),
        _root_.SheafOfModules.IsCoherent F → HasIdealDevissage F :=
  fun h => not_forall_hasIdealDevissage_of_isEmpty
    (X := Spec (CommRingCat.of PUnit.{u + 1})) (h _ inferInstance)

/-- A zero module has a filtration of length `0`, on every scheme. This is the case the source
handles with `m = 0`, and the one `HasIdealDevissage` cannot express. -/
theorem hasIdealFiltration_of_isZero {F : X.Modules} (h : IsZero F) : HasIdealFiltration F :=
  ⟨0, fun _ => F, fun _ => 𝟙 F, fun i hi => absurd hi (Nat.not_lt_zero i), h,
    fun _ _ => isCoherent_of_isZero h,
    fun i hi => absurd hi (Nat.not_lt_zero i), ⟨Iso.refl F⟩,
    fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- The zero module satisfies the replacement on every scheme, including the ones on which
`HasIdealDevissage` is unsatisfiable. -/
theorem hasIdealFiltration_terminal (X : Scheme.{u}) :
    HasIdealFiltration (⊤_ X.Modules) :=
  hasIdealFiltration_of_isZero isZero_terminal

/-! ### The dévissage engine at the replacement -/

variable (P : X.Modules → Prop)

/-- **The dévissage induction, run only over the steps the filtration has.** This is
`Stacks.AlgebraicGeometry.CoherentDevissage.property_of_monoChain` with each hypothesis asked for
only below the cut-off `n`, which is all the induction reads. -/
theorem property_of_monoChain_lt (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ → P S.X₁ → P S.X₃ → P S.X₂)
    {n : ℕ} (G : ℕ → X.Modules) (f : ∀ i, G i ⟶ G (i + 1))
    (hmono : ∀ i < n, Mono (f i)) (hzeroG : IsZero (G 0))
    (hcoh : ∀ i ≤ n, _root_.SheafOfModules.IsCoherent (G i))
    (hcoker : ∀ i < n, _root_.SheafOfModules.IsCoherent (cokernel (f i)))
    (hP : ∀ i < n, P (cokernel (f i))) :
    ∀ m ≤ n, P (G m) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact property_of_iso P hzero hext (isZero_terminal.iso hzeroG) isCoherent_terminal hzero
  | succ i ih =>
    intro hm
    exact hext (ShortComplex.mk (f i) (cokernel.π (f i)) (cokernel.condition (f i)))
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (f i))
        mono_f := hmono i (by omega)
        epi_g := inferInstance }
      (hcoh i (by omega)) (hcoh (i + 1) hm) (hcoker i (by omega)) (ih (by omega))
      (hP i (by omega))

/-- **[Stacks, Tag 01YG] for a module that has a dévissage filtration.** The three hypotheses of
01YG give `P F` for every `F` carrying a filtration as in `HasIdealFiltration`. -/
theorem property_of_hasIdealFiltration (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (F : X.Modules) (hF : HasIdealFiltration F) : P F := by
  obtain ⟨n, G, f, hmono, hzeroG, hcoh, hcoker, ⟨e⟩, hquot⟩ := hF
  have hP : ∀ i < n, P (cokernel (f i)) := by
    intro i hi
    obtain ⟨Z, ι, hι, hZ, I, hI, ⟨eq⟩⟩ := hquot i hi
    exact property_of_iso P hzero hext eq.symm
      (@isCoherent_of_iso _ _ _ _ _ eq.symm (hcoker i hi)) (hideal ι I hI)
  exact property_of_iso P hzero hext e (hcoh n le_rfl)
    (property_of_monoChain_lt P hzero hext G f hmono hzeroG hcoh hcoker hP n le_rfl)

/-- **[Stacks, Tag 01YG], conditional on [Stacks, Tag 01YF].** A property of modules that holds
on the zero module, is stable under extensions of coherent modules, and holds on the direct
image of every quasi-coherent ideal on every integral closed subscheme, holds on every coherent
module — provided every coherent module has a dévissage filtration.

This is
`Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealDevissage` with a hypothesis
that a proof of [Stacks, Tag 01YF] can actually deliver; the hypothesis of that version is
false, by `not_forall_isNoetherian_hasIdealDevissage`. -/
theorem property_of_forall_hasIdealFiltration
    (hfil : ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → HasIdealFiltration F)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      _root_.SheafOfModules.IsCoherent S.X₁ → _root_.SheafOfModules.IsCoherent S.X₂ →
      _root_.SheafOfModules.IsCoherent S.X₃ → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, _root_.SheafOfModules.IsCoherent F → P F :=
  fun F hF => property_of_hasIdealFiltration P hzero hext hideal F (hfil F hF)

/-! ### From a chain of subobjects, as in the statement of Tag 01YF -/

/-- Equal subobjects have the same quotient. The two witnesses of the inequality are proofs, so
once the subobjects are identified the two comparison maps are the same term. -/
theorem cokernel_ofLE_congr {C : Type*} [Category C] [Abelian C] {B : C}
    {V W V' W' : Subobject B} (hV : V = V') (hW : W = W') (h : V ≤ W) (h' : V' ≤ W') :
    Nonempty (cokernel (Subobject.ofLE V W h) ≅ cokernel (Subobject.ofLE V' W' h')) := by
  subst hV
  subst hW
  exact ⟨Iso.refl _⟩

/-- **The conclusion of Tag 01YF gives `HasIdealFiltration`.** A monotone chain
`G : Fin (n + 1) → Subobject F` from `⊥` to `⊤` with coherent terms, each of whose `n`
successive quotients is a direct image of a nonzero coherent ideal sheaf on an integral closed
subscheme, is a dévissage filtration of `F`.

So a proof of [Stacks, Tag 01YF], stated as a chain of subobjects, feeds
`property_of_forall_hasIdealFiltration` with nothing left to supply: the hypotheses below are
exactly that statement's conclusion, and the coherence of the quotients, which that statement
does not include, is derived from the coherence of the terms. -/
theorem hasIdealFiltration_of_subobjectFiltration {F : X.Modules}
    (n : ℕ) (G : Fin (n + 1) → Subobject F) (hG : Monotone G)
    (hbot : G 0 = ⊥) (htop : G (Fin.last n) = ⊤)
    (hcoh : ∀ j : Fin (n + 1), _root_.SheafOfModules.IsCoherent (G j : X.Modules))
    (hquot : ∀ j : Fin n, ∃ (Z : Scheme.{u}) (i : Z ⟶ X) (_ : IsClosedImmersion i)
      (_ : IsIntegral Z) (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      _root_.SheafOfModules.IsCoherent I.toSheafOfModules ∧ ¬ IsZero I.toSheafOfModules ∧
        Nonempty (cokernel (Subobject.ofLE (G j.castSucc) (G j.succ) (hG j.castSucc_le_succ)) ≅
          (Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    HasIdealFiltration F := by
  -- Truncate the index at `n`, so that the chain is defined on all of `ℕ`.
  set g : ℕ → Subobject F := fun i => G ⟨min i n, Nat.lt_succ_of_le (min_le_right i n)⟩
  have hstep : ∀ i, g i ≤ g (i + 1) := by
    intro i
    exact hG (by simp only [Fin.mk_le_mk]; omega)
  -- The truncation `g i` is `G j` whenever `j` is the index `min i n`.
  have hg : ∀ (i : ℕ) (j : Fin (n + 1)), (j : ℕ) = min i n → g i = G j :=
    fun i j h => congrArg G (Fin.ext h.symm)
  -- The quotients below the cut-off, transported from the tag's spelling.
  have hq : ∀ i < n, ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (_ : IsClosedImmersion ι)
      (_ : IsIntegral Z) (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent ∧
        Nonempty (cokernel (Subobject.ofLE (g i) (g (i + 1)) (hstep i)) ≅
          (Scheme.Modules.pushforward ι).obj I.toSheafOfModules) := by
    intro i hi
    obtain ⟨Z, ι, hι, hZ, I, hIcoh, -, ⟨e⟩⟩ := hquot ⟨i, hi⟩
    obtain ⟨c⟩ := cokernel_ofLE_congr (hg i _ (by simp [hi.le])) (hg _ _ (by simp; omega))
      (hstep i)
      (hG (Fin.castSucc_le_succ ⟨i, hi⟩))
    exact ⟨Z, ι, hι, hZ, I, @_root_.isQuasicoherent_of_isCoherent _ _ _ _ hIcoh, ⟨c.trans e⟩⟩
  refine hasIdealFiltration_of_chain n (fun i => (g i : X.Modules))
    (fun i => Subobject.ofLE (g i) (g (i + 1)) (hstep i)) (fun i _ => inferInstance) ?_
    (fun i _ => hcoh _) ?_ hq
  · -- The filtration starts at a zero module, because it starts at `⊥`.
    have h0 : g 0 = ⊥ := (hg 0 0 (by simp)).trans hbot
    change IsZero (Subobject.underlying.obj (g 0))
    rw [h0]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
  · -- The filtration ends at `F`, because it ends at `⊤`.
    have hn : g n = ⊤ := (hg n (Fin.last n) (by simp)).trans htop
    have : IsIso (g n).arrow := (Subobject.isIso_arrow_iff_eq_top (g n)).2 hn
    exact ⟨asIso (g n).arrow⟩

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
