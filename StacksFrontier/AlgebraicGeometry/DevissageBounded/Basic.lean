module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Devissage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs

/-!
# Bounded dévissage filtrations of coherent modules

[Stacks, Tag 01YG] and [Stacks, Tag 01YH] both work by taking a coherent module apart along a
finite filtration whose successive quotients are direct images of quasi-coherent ideal sheaves
on integral closed subschemes. The filtration itself is [Stacks, Tag 01YF], which this
repository does not have.

The library's dévissage file already carries the consumer side of 01YG: the induction along a
filtration, and 01YG itself conditional on an explicit hypothesis `hdev` naming 01YF
(`Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealDevissage`). This file does
three things that file does not.

**1. A filtration predicate that is satisfiable.** The library's `HasIdealDevissage` quantifies the
"quotient is `i_*I`" requirement over *all* of `ℕ`, not over the indices below the cut-off `n`.
Past the cut-off the quotient is the zero module, and the zero module is `i_*0` only once an
integral closed subscheme `i : Z ⟶ X` exists — which needs `X` to have a point, since
`AlgebraicGeometry.IsIntegral` carries `Nonempty`. So `HasIdealDevissage F` is **false for every
module on a scheme with no points**, and `property_of_forall_hasIdealDevissage` — the existing
route to 01YG — cannot be instantiated over such a scheme, even though 01YG itself holds there
by `property_of_iso` alone. That negative is `not_hasIdealDevissage_of_isEmpty` below. The
repair is to bound every index condition by the cut-off, which is what the source's finite
filtration `0 = F_0 ⊂ … ⊂ F_m = F` actually says.

**2. A quotient class as a parameter.** `HasDevissageWith Q F` is the bounded filtration with
every successive quotient in the class `Q`. Taking `Q` to be "isomorphic to the direct image of
a quasi-coherent ideal on an integral closed subscheme" gives the shape 01YG and 01YF speak
about; taking `Q` to be the property `P` under study gives the shape the last paragraph of the
proof of [Stacks, Tag 01YH] uses.

**3. The two-out-of-three hypothesis of 01YH is strictly stronger than the hypotheses of
01YG.** Tag 01YH assumes that in a short exact sequence of coherent modules, any two of the
three terms having `P` forces the third. From that plus `P` on a *single* coherent module,
`P` on the zero module follows — apply the two-out-of-three condition to `0 → G → G → 0 → 0`.
So 01YH's `hzero` need not be assumed, and the whole 01YG engine becomes available inside
01YH's proof. That is `property_terminal_of_twoOutOfThree`.

No `@[stacks]` attribute is attached to anything here: 01YF, 01YG and 01YH all remain open, and
the statements below are either conditional on a filtration or are transport lemmas.

## Main definitions

* `Stacks.AlgebraicGeometry.DevissageBounded.IsIdealPushforward`: the quotient class appearing in
  [Stacks, Tag 01YF] — isomorphic to the direct image of a quasi-coherent ideal sheaf on an
  integral closed subscheme.
* `Stacks.AlgebraicGeometry.DevissageBounded.HasDevissageWith`: a finite filtration by coherent
  submodules, starting at a zero module, whose successive quotients lie in a given class.
* `Stacks.AlgebraicGeometry.DevissageBounded.HasIdealDevissageLt`: the conclusion of
  [Stacks, Tag 01YF] for one module, with every index condition bounded by the cut-off.

## Main results

* `Stacks.AlgebraicGeometry.DevissageBounded.not_hasIdealDevissage_of_isEmpty`: the
  unbounded predicate fails for every module on a scheme with no points.
* `Stacks.AlgebraicGeometry.DevissageBounded.hasIdealDevissageLt_of_isZero`: the bounded
  predicate holds for every zero module, on every scheme.
* `Stacks.AlgebraicGeometry.DevissageBounded.hasIdealDevissageLt_of_hasIdealDevissage`: the
  bounded predicate is weaker, so the conditional 01YG below is stronger than the unbounded one.
* `Stacks.AlgebraicGeometry.DevissageBounded.property_of_monoChain_le`: the dévissage induction
  with all hypotheses bounded by the cut-off.
* `Stacks.AlgebraicGeometry.DevissageBounded.property_of_hasDevissageWith`: a property holding on
  the zero module, stable under extensions of coherent modules, and holding on the quotient
  class, holds on anything the class filters.
* `Stacks.AlgebraicGeometry.DevissageBounded.property_of_forall_hasIdealDevissageLt`:
  **[Stacks, Tag 01YG], conditional on [Stacks, Tag 01YF]** in its bounded form.
* `Stacks.AlgebraicGeometry.DevissageBounded.property_terminal_of_twoOutOfThree`: 01YH's
  two-out-of-three hypothesis plus `P` on one coherent module gives `P` on the zero module.
* `Stacks.AlgebraicGeometry.DevissageBounded.property_of_irreducible_support_of_devissage`:
  **[Stacks, Tag 01YH], conditional on a filtration with `P`-quotients.**

## Implementation notes

The filtration is carried as a sequence `G : ℕ → X.Modules` with monomorphisms
`f i : G i ⟶ G (i + 1)` and a cut-off `n`, exactly as in `HasIdealDevissage`, so that
the two predicates are comparable term by term and the induction is the plain `Nat.rec`. The only
change is that `Mono (f i)`, coherence of `G i` and of `cokernel (f i)`, and membership of
`cokernel (f i)` in the quotient class are required for `i < n` (resp. `i ≤ n`) rather than for
every `i`. Nothing past the cut-off is constrained, so a filtration can be padded with
identities, which is how `hasIdealDevissageLt_of_isZero` produces one on any scheme.

The successive short exact sequence is built from the constructor as
`ShortComplex.mk (f i) (cokernel.π (f i)) (cokernel.condition (f i))`, for the reason recorded in
the implementation notes of the library's dévissage file: its three terms are syntactically `G i`,
`G (i + 1)` and `cokernel (f i)`, so the extension hypothesis applies with no transport.

In `property_terminal_of_twoOutOfThree` the sequence `G → G → 0` is exact at its middle term
because its second map is `0` and its first is epi, which is `ShortComplex.exact_iff_epi`;
`ShortComplex.exact_iff_mono` does not apply, since the first map is `𝟙 G` and not `0`.

`Set.range` of the underlying map of a closed immersion, which [Stacks, Tag 01YH] uses to say
that an integral closed subscheme is strictly smaller than `Z₀`, is not needed here: the
hypothesis `hproper` of that tag enters only through the filtration hypothesis `hdev`, which is
why `property_of_irreducible_support_of_devissage` assumes neither it nor the closedness and
irreducibility of `Z₀`. Stating the reduction without them makes visible that the whole
geometric content of 01YH sits in `hdev`.

## References

* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules
open Stacks.AlgebraicGeometry.CoherentDevissage

universe u

namespace Stacks.AlgebraicGeometry.DevissageBounded

variable {X : Scheme.{u}}

/-! ### The unbounded predicate is unsatisfiable without points -/

/-- **The unbounded `HasIdealDevissage` is false for every module on a scheme with no points.** Its
quotient condition is imposed at every index, including the indices past the cut-off where the
quotient is zero, and meeting it anywhere produces an integral closed subscheme of `X`, whose
underlying space is nonempty and maps to `X`.

Consequently `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealDevissage`
  cannot
be applied over a scheme without points — its hypothesis `hdev` is unprovable there — although
[Stacks, Tag 01YG] does hold over such a scheme, since every module on it is a zero module and
`property_of_iso` already covers that case. The bounded predicate below does not have this
defect; see `hasIdealDevissageLt_of_isZero`. -/
theorem not_hasIdealDevissage_of_isEmpty (hX : IsEmpty X) (F : X.Modules) :
    ¬ HasIdealDevissage F := by
  rintro ⟨n, G, f, -, -, -, -, -, hquot⟩
  obtain ⟨Z, ι, hι, hZ, I, -, -⟩ := hquot 0
  exact hX.elim (ι (Classical.choice hZ.nonempty))

/-! ### Bounded dévissage filtrations -/

/-- The class of modules appearing as a successive quotient in [Stacks, Tag 01YF]: those
isomorphic to the direct image of a quasi-coherent ideal sheaf on an integral closed subscheme
of `X`. -/
def IsIdealPushforward (M : X.Modules) : Prop :=
  ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (_ : IsClosedImmersion ι) (_ : IsIntegral Z)
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
    I.toSheafOfModules.IsQuasicoherent ∧
      Nonempty (M ≅ (Scheme.Modules.pushforward ι).obj I.toSheafOfModules)

/-- A finite filtration of `F` by coherent submodules, starting at a zero module, whose
successive quotients all lie in the class `Q`.

The filtration is `G 0 ↪ G 1 ↪ … ↪ G n ≅ F` with `G 0` a zero module. Every condition is bounded
by the cut-off `n`: nothing is required of `G i` or `f i` for `i` beyond it, so a filtration may
be padded with identity maps. This is the shape of the finite filtration
`0 = F_0 ⊂ F_1 ⊂ … ⊂ F_m = F` that [Stacks, Tag 01YF] produces. -/
def HasDevissageWith (Q : X.Modules → Prop) (F : X.Modules) : Prop :=
  ∃ (n : ℕ) (G : ℕ → X.Modules) (f : ∀ i, G i ⟶ G (i + 1)),
    (∀ i, i < n → Mono (f i)) ∧ IsZero (G 0) ∧ (∀ i, i ≤ n → (G i).IsCoherent) ∧
      (∀ i, i < n → (cokernel (f i)).IsCoherent) ∧ Nonempty (G n ≅ F) ∧
      ∀ i, i < n → Q (cokernel (f i))

/-- **The conclusion of [Stacks, Tag 01YF] for a single module.** `F` carries a finite filtration
by coherent submodules, starting at a zero module, each of whose successive quotients is the
direct image of a quasi-coherent ideal sheaf on an integral closed subscheme.

This is the bounded repair of `HasIdealDevissage`; see
`not_hasIdealDevissage_of_isEmpty` for why the bound is needed and
`hasIdealDevissageLt_of_hasIdealDevissage` for the comparison. -/
abbrev HasIdealDevissageLt (F : X.Modules) : Prop :=
  HasDevissageWith IsIdealPushforward F

/-- Padding with identities: a zero module carries the empty filtration, on any scheme. This is
the case the unbounded `HasIdealDevissage` gets wrong when `X` has no points. -/
theorem hasIdealDevissageLt_of_isZero {F : X.Modules} (hF : IsZero F) :
    HasIdealDevissageLt F :=
  ⟨0, fun _ => F, fun _ => 𝟙 F, by omega, hF,
    fun _ _ => isCoherent_of_isZero hF, by omega, ⟨Iso.refl F⟩, by omega⟩

/-- The bounded predicate is weaker than the unbounded one, so the conditional
[Stacks, Tag 01YG] proved below is stronger than
`Stacks.AlgebraicGeometry.CoherentDevissage.property_of_forall_hasIdealDevissage`. -/
theorem hasIdealDevissageLt_of_hasIdealDevissage {F : X.Modules}
    (hF : HasIdealDevissage F) : HasIdealDevissageLt F := by
  obtain ⟨n, G, f, hmono, hzeroG, hcoh, hcoker, he, hquot⟩ := hF
  refine ⟨n, G, f, fun i _ => hmono i, hzeroG, fun i _ => hcoh i,
    fun i _ => hcoker i, he, fun i _ => ?_⟩
  obtain ⟨Z, ι, hι, hZ, I, hI, he'⟩ := hquot i
  exact ⟨Z, ι, hι, hZ, I, hI, he'⟩

/-! ### The dévissage induction, bounded -/

variable (P : X.Modules → Prop)

/-- **The dévissage induction with bounded hypotheses.** If `P` holds on the zero module, is
stable under extensions of coherent modules, and holds on every successive quotient
`cokernel (f i)` for `i` below the cut-off, then it holds on every term `G i` of the filtration
up to the cut-off.

This is `Stacks.AlgebraicGeometry.CoherentDevissage.property_of_monoChain` with every hypothesis
restricted to the indices the filtration actually uses. -/
theorem property_of_monoChain_le (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (n : ℕ) (G : ℕ → X.Modules) (f : ∀ i, G i ⟶ G (i + 1))
    (hmono : ∀ i, i < n → Mono (f i)) (hzeroG : IsZero (G 0))
    (hcoh : ∀ i, i ≤ n → (G i).IsCoherent)
    (hcoker : ∀ i, i < n → (cokernel (f i)).IsCoherent)
    (hP : ∀ i, i < n → P (cokernel (f i))) :
    ∀ i, i ≤ n → P (G i) := by
  intro i
  induction i with
  | zero =>
    intro _
    exact property_of_iso P hzero hext (isZero_terminal.iso hzeroG) isCoherent_terminal hzero
  | succ i ih =>
    intro hi
    exact hext (ShortComplex.mk (f i) (cokernel.π (f i)) (cokernel.condition (f i)))
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (f i))
        mono_f := hmono i hi
        epi_g := inferInstance }
      (hcoh i (Nat.le_of_lt hi)) (hcoh (i + 1) hi) (hcoker i hi)
      (ih (Nat.le_of_lt hi)) (hP i hi)

/-- **A property transported along a bounded dévissage filtration.** If `P` holds on the zero
module, is stable under extensions of coherent modules, and holds on every coherent module in the
class `Q`, then it holds on every module that `Q` filters. -/
theorem property_of_hasDevissageWith (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    {Q : X.Modules → Prop} (hQ : ∀ M : X.Modules, Q M → M.IsCoherent → P M)
    (F : X.Modules) (hF : HasDevissageWith Q F) : P F := by
  obtain ⟨n, G, f, hmono, hzeroG, hcoh, hcoker, ⟨e⟩, hquot⟩ := hF
  exact property_of_iso P hzero hext e (hcoh n le_rfl)
    (property_of_monoChain_le P hzero hext n G f hmono hzeroG hcoh hcoker
      (fun i hi => hQ _ (hquot i hi) (hcoker i hi)) n le_rfl)

/-- A property closed under isomorphism and holding on ideal pushforwards holds on every module
of the class `IsIdealPushforward`. -/
private theorem property_of_isIdealPushforward (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    {M : X.Modules} (hM : IsIdealPushforward M) (hc : M.IsCoherent) : P M := by
  obtain ⟨Z, ι, hι, hZ, I, hI, ⟨e⟩⟩ := hM
  have := hc
  exact property_of_iso P hzero hext e.symm (isCoherent_of_iso e.symm) (hideal ι I hI)

/-- **[Stacks, Tag 01YG], conditional on [Stacks, Tag 01YF].** A property of modules that holds on
the zero module, is stable under extensions of coherent modules, and holds on the direct image of
every quasi-coherent ideal sheaf on every integral closed subscheme, holds on every coherent
module — provided every coherent module carries a bounded dévissage filtration.

The hypothesis `hdev` is [Stacks, Tag 01YF] and is not proved anywhere in this repository. Unlike
the hypothesis of `property_of_forall_hasIdealDevissage`, it is satisfiable on every scheme; see
`not_hasIdealDevissage_of_isEmpty` and `hasIdealDevissageLt_of_isZero`. The `[IsNoetherian X]` of
Tag 01YG is used by the source only to obtain `hdev`, so it is not assumed here. -/
theorem property_of_forall_hasIdealDevissageLt
    (hdev : ∀ F : X.Modules, F.IsCoherent → HasIdealDevissageLt F)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F := by
  exact fun F hF => property_of_hasDevissageWith P hzero hext
    (fun _ => property_of_isIdealPushforward P hzero hext hideal) F (hdev F hF)

/-! ### An extension-closed form of the dévissage hypothesis -/

/-- **Dévissability by ideal pushforwards, as the smallest extension-closed class.** A coherent
module is ideal-dévissable when it is zero, or the direct image of a quasi-coherent ideal sheaf
on an integral closed subscheme, or an extension of two ideal-dévissable coherent modules.

This is the form in which a prover of [Stacks, Tag 01YF] should state its conclusion. The
source's proof is a Noetherian induction on the support, and its two reduction steps each end by
splicing two filtrations of the pieces of a short exact sequence into one filtration of the whole
— the step the source performs in the words "splicing them yields one for `F`". Against the
filtration predicate `HasDevissageWith` that splicing is a genuine obligation, requiring
preimages of subobjects along the epimorphism and a comparison of their cokernels. Against this
predicate it is the constructor `ext`, so the Noetherian induction needs only the geometry.

`isIdealDevissable_of_hasIdealDevissageLt` shows this is implied by — hence no stronger than —
the filtration form, and `property_of_forall_isIdealDevissable` shows it is already enough to
conclude [Stacks, Tag 01YG]. -/
inductive IsIdealDevissable : X.Modules → Prop
  /-- A zero coherent module is ideal-dévissable. -/
  | zero {F : X.Modules} (hF : IsZero F) (hc : F.IsCoherent) : IsIdealDevissable F
  /-- The direct image of a quasi-coherent ideal sheaf on an integral closed subscheme is
  ideal-dévissable. -/
  | ideal {F : X.Modules} (hF : IsIdealPushforward F) (hc : F.IsCoherent) :
      IsIdealDevissable F
  /-- An extension of ideal-dévissable coherent modules is ideal-dévissable. -/
  | ext (S : ShortComplex X.Modules) (hS : S.ShortExact)
      (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent)
      (hd₁ : IsIdealDevissable S.X₁) (hd₃ : IsIdealDevissable S.X₃) :
      IsIdealDevissable S.X₂

/-- An ideal-dévissable module is coherent. -/
theorem IsIdealDevissable.isCoherent {F : X.Modules} (hF : IsIdealDevissable F) :
    F.IsCoherent := by
  induction hF with
  | zero _ hc => exact hc
  | ideal _ hc => exact hc
  | ext _ _ _ h₂ _ _ _ => exact h₂

/-- The zero module is ideal-dévissable on every scheme, with no point needed. Contrast
`not_hasIdealDevissage_of_isEmpty`. -/
theorem isIdealDevissable_terminal : IsIdealDevissable (⊤_ X.Modules) :=
  .zero isZero_terminal isCoherent_terminal

/-- A bounded dévissage filtration by ideal pushforwards makes a coherent module
ideal-dévissable, so the hypothesis of `property_of_forall_isIdealDevissable` is no stronger than
the hypothesis of `property_of_forall_hasIdealDevissageLt`. -/
theorem isIdealDevissable_of_hasIdealDevissageLt {F : X.Modules}
    (hF : HasIdealDevissageLt F) : IsIdealDevissable F :=
  property_of_hasDevissageWith IsIdealDevissable isIdealDevissable_terminal
    (fun S hS h₁ h₂ h₃ hd₁ hd₃ => .ext S hS h₁ h₂ h₃ hd₁ hd₃)
    (fun _ hQ hc => .ideal hQ hc) F hF

/-- **A property transported along ideal-dévissability.** This is the recursor of
`IsIdealDevissable` read as the dévissage principle. -/
theorem property_of_isIdealDevissable (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    {F : X.Modules} (hF : IsIdealDevissable F) : P F := by
  induction hF with
  | zero h _ =>
    exact property_of_iso P hzero hext (isZero_terminal.iso h) isCoherent_terminal hzero
  | ideal h hc => exact property_of_isIdealPushforward P hzero hext hideal h hc
  | ext S hS h₁ h₂ h₃ _ _ ih₁ ih₃ => exact hext S hS h₁ h₂ h₃ ih₁ ih₃

/-- **[Stacks, Tag 01YG], conditional on the extension-closed form of [Stacks, Tag 01YF].** This
is the weakest of the three conditional forms of 01YG in this repository: its hypothesis is
implied by that of `property_of_forall_hasIdealDevissageLt`, which is in turn implied by that of
the original `property_of_forall_hasIdealDevissage`. -/
theorem property_of_forall_isIdealDevissable
    (hdev : ∀ F : X.Modules, F.IsCoherent → IsIdealDevissable F)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  fun F hF => property_of_isIdealDevissable P hzero hext hideal (hdev F hF)

/-! ### The two-out-of-three hypothesis of [Stacks, Tag 01YH] -/

/-- **Two-out-of-three plus one example gives the zero module.** Tag 01YH assumes that in a
short exact sequence of coherent modules any two of the three terms having `P` forces the third.
Applied to `0 → G → G → 0 → 0`, with `G` the coherent module of that tag's hypothesis (3), this
yields `P` on the zero module, so Tag 01YG's `hzero` is redundant in the presence of Tag 01YH's
hypotheses rather than an extra assumption. -/
theorem property_terminal_of_twoOutOfThree
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (G : X.Modules) (hG : G.IsCoherent) (hPG : P G) : P (⊤_ X.Modules) := by
  have := hG
  refine (hexact (ShortComplex.mk (𝟙 G) (0 : G ⟶ ⊤_ X.Modules) (by simp))
    (ShortComplex.ShortExact.mk' ((ShortComplex.exact_iff_epi _ rfl).2 inferInstance)
      inferInstance (isZero_terminal.epi _))
    hG hG isCoherent_terminal).1 ⟨hPG, hPG⟩

/-- Tag 01YH's two-out-of-three hypothesis contains Tag 01YG's extension hypothesis, as its
second clause. -/
theorem ext_of_twoOutOfThree
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁))) :
    ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂ :=
  fun S hS h₁ h₂ h₃ hP₁ hP₃ => (hexact S hS h₁ h₂ h₃).2.1 ⟨hP₁, hP₃⟩

/-- **[Stacks, Tag 01YH], conditional on a filtration with `P`-quotients.** Tag 01YH's
two-out-of-three hypothesis, together with a single coherent module satisfying `P`, gives `P` on
every coherent module supported in `Z₀` that is filtered by modules satisfying `P`.

This is the last paragraph of the source's proof. The geometric hypotheses of the tag — that
`Z₀` is closed and irreducible with generic point `ξ`, that `P` holds on ideal pushforwards from
integral closed subschemes strictly inside `Z₀`, and the generic length-one condition — are used
by the source only to produce `hdev`, so none of them appears here. What remains open is exactly
`hdev`, whose proof needs [Stacks, Tag 01YF] and [Stacks, Tag 01YE], neither of which exists in
this repository. -/
theorem property_of_irreducible_support_of_devissage
    (Z₀ : Set X)
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (G : X.Modules) (hG : G.IsCoherent) (hPG : P G)
    (hdev : ∀ F : X.Modules, F.IsCoherent → SheafOfModules.supp F ⊆ Z₀ →
      HasDevissageWith P F) :
    ∀ F : X.Modules, F.IsCoherent → SheafOfModules.supp F ⊆ Z₀ → P F :=
  fun F hF hsupp =>
    property_of_hasDevissageWith P
      (property_terminal_of_twoOutOfThree P hexact G hG hPG)
      (ext_of_twoOutOfThree P hexact) (fun _ h _ => h) F (hdev F hF hsupp)

end Stacks.AlgebraicGeometry.DevissageBounded

end

end
