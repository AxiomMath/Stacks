module

public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Basic

/-!
# Dévissage of coherent modules supported on an irreducible closed subset

[Stacks, Tag 01YH] is the relative form of [Stacks, Tag 01YG]: a property `P` of coherent
modules on a Noetherian scheme `X` holds for every coherent module supported inside a closed
irreducible `Z₀` as soon as

1. in a short exact sequence of coherent modules, any two of the three terms having `P` forces
   the third (two-out-of-three, strictly stronger than 01YG's stability under extensions),
2. `P` holds for `i_* I` whenever `i : Z ⟶ X` is a closed immersion with `Z` integral,
   `Set.range i.base` **strictly** inside `Z₀`, and `I ⊆ 𝒪_Z` quasi-coherent, and
3. there is one coherent `G` with support exactly `Z₀`, generic stalk killed by `𝔪_ξ` and of
   length one over `𝒪_{X,ξ}`, satisfying `P`.

The source's proof has two halves. The first is the Noetherian induction on the support, run
*relative to* `Z₀`; it is proved here, for an arbitrary `P`, from the two steps of
[Stacks, Tag 01YF] taken as hypotheses. The second shows that `P` holds for `i_* I` when
`Set.range i.base` is **all** of `Z₀`; it uses (3) through [Stacks, Tag 01YE] and enters here as
the hypothesis `htop` (see the implementation notes).

The absolute Noetherian induction of `StacksFrontier/AlgebraicGeometry/DevissageNoetherian/Basic.lean`
reduces [Stacks, Tag 01YF] to `Stacks.AlgebraicGeometry.DevissageNoetherian.HasSupportSplitting`
([Stacks, Tag 01YD]) and `Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage`.
Its quotient class `Stacks.AlgebraicGeometry.DevissageBounded.IsIdealPushforward` puts **no
constraint on where the integral closed subscheme sits**, whereas hypothesis (2) of 01YH is
available only for subschemes inside `Z₀`. So the class is relativized here to
`IsIdealPushforwardIn`, the irreducible step to `HasIrreducibleDevissageIn`, and the induction is
re-run carrying the containment. By `hasIrreducibleDevissage_of_hasIrreducibleDevissageIn` the
relativized step implies the absolute one.

The relativization matches the source: the integral closed subscheme that step 4 of the proof of
[Stacks, Tag 01YF] produces is the *reduced induced structure on the support of the module*, so
its range is the support, which the induction keeps inside `Z₀`.

## Main definitions

* `Stacks.AlgebraicGeometry.ConfinedDevissage.IsIdealPushforwardIn`: the direct image of a
  quasi-coherent ideal sheaf on an integral closed subscheme **whose range lies in a given set**.
* `Stacks.AlgebraicGeometry.ConfinedDevissage.HasIrreducibleDevissageIn`: the irreducible step of
  [Stacks, Tag 01YF] with the subschemes confined to the support of the module.

## Main results

* `Stacks.AlgebraicGeometry.ConfinedDevissage.hasDevissageWith_mono`: a dévissage filtration
  survives weakening of its quotient class.
* the relativized irreducible step implies the absolute one:
  `Stacks.AlgebraicGeometry.ConfinedDevissage.hasIrreducibleDevissage_of_hasIrreducibleDevissageIn`
* `Stacks.AlgebraicGeometry.ConfinedDevissage.property_of_supp_subset`: **the relativized
  Noetherian induction.** For any set `W`, a property that holds on the zero module, is stable
  under extensions of coherent modules, and holds on the direct image of every quasi-coherent
  ideal sheaf on every integral closed subscheme *with range inside `W`*, holds on every coherent
  module supported inside `W`.
* `Stacks.AlgebraicGeometry.ConfinedDevissage.property_of_supp_ssubset`: **the first paragraph of
  the proof of [Stacks, Tag 01YH]**: hypothesis (2) alone gives `P` on every coherent module
  whose support is strictly smaller than `Z₀`.
* `Stacks.AlgebraicGeometry.ConfinedDevissage.property_of_irreducible_support_of_topIdeals`:
  **[Stacks, Tag 01YH], conditional on the two steps of [Stacks, Tag 01YF] and on the
  top-stratum ideals.** The conclusion of 01YH from its hypotheses together with `htop`, the
  second half of the source's proof.
* `Stacks.AlgebraicGeometry.ConfinedDevissage.property_sub_of_twoOutOfThree`: the two-out-of-three
  hypothesis read backwards — `P` on a module and on the cokernel of a monomorphism out of it
  gives `P` on the sub.
* `Stacks.AlgebraicGeometry.ConfinedDevissage.property_pushforward_of_mono_of_supp_ssubset`: **the
  step the source takes with [Stacks, Tag 01YE]**, once the multiplicity is known to be one: a
  monomorphism `i_* I ⟶ G` whose cokernel is supported strictly inside `Z₀` transfers `P` from
  `G` to `i_* I`.
* `Stacks.AlgebraicGeometry.ConfinedDevissage.supp_eq_empty_of_isZero`: a zero module has empty
  support — the converse of
  `Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty`.
* `Stacks.AlgebraicGeometry.ConfinedDevissage.notMem_supp_of_supp_restrict_eq_empty`,
  `Stacks.AlgebraicGeometry.ConfinedDevissage.isZero_restrict_cokernel` and
  `Stacks.AlgebraicGeometry.ConfinedDevissage.notMem_supp_cokernel_of_isIso_restrict`: a morphism
  that restricts to an isomorphism on an open set has a cokernel whose support misses that open
  set.
* `Stacks.AlgebraicGeometry.ConfinedDevissage.supp_cokernel_ssubset_of_isIso_restrict` and
  `Stacks.AlgebraicGeometry.ConfinedDevissage.property_pushforward_of_mono_of_isIso_restrict`: the
  previous step with its hypothesis in the shape [Stacks, Tag 01YE] delivers — an open
  neighbourhood of the generic point on which the inclusion is invertible, rather than a
  statement about the support of the cokernel.

## Implementation notes

**The hypothesis `htop`.** `htop` asks for `P ((i : Z ⟶ X)_* I)` for `Z` integral,
`I ⊆ 𝒪_Z` quasi-coherent and `Set.range i.base = Z₀`. The source obtains it in three steps:

* [Stacks, Tag 01YE] applied to the module `G` of hypothesis (3). It produces `r : ℕ`, a
  coherent ideal `I` on the reduced induced structure of `Z₀`, and a monomorphism
  `i_* (I^{⊕ r}) ⟶ G` that is an isomorphism on a neighbourhood of `ξ`.
* `r = 1`, which is where the length-one condition of hypothesis (3) is used. The generic stalk
  of `i_* (I^{⊕ r})` has length `r` over `𝒪_{X,ξ}` and that of `G` has length `1`, and the two
  agree because the monomorphism is an isomorphism near `ξ`.
* the intersection argument that passes from the single ideal `I` so produced to an arbitrary
  nonzero quasi-coherent ideal `I'`, via `I'' = I ∩ I'` and the two short exact sequences with
  quotients of strictly smaller support. Besides exactness of `i_*` on quasi-coherent
  submodules of the unit, this uses that a **nonzero** quasi-coherent ideal sheaf on an integral
  scheme has full support — i.e. that its stalk at the generic point is the whole residue field
  — which makes the two quotients strictly smaller.

`property_pushforward_of_mono_of_supp_ssubset` and
`property_pushforward_of_mono_of_isIso_restrict` carry out the transfer of `P` from `G` to
`i_* I` once the first two steps have produced a monomorphism with multiplicity one.

**Why the relativized induction is phrased with an arbitrary set `W`.** Neither closedness nor
irreducibility of `W` is used: the induction decreases the support, which is closed because the
module is coherent, and `W` only ever appears in containments. Taking `W = Z₀` gives the
conclusion of 01YH; taking `W = SheafOfModules.supp F` gives `property_of_supp_ssubset`, where
hypothesis (2) supplies the ideals because a subscheme inside a set strictly inside `Z₀` is
strictly inside `Z₀`. Stating the induction once with `W` free lets both uses share it.

The induction itself is the one in
`Stacks.AlgebraicGeometry.DevissageNoetherian.isIdealDevissable_of_isCoherent`, run with `P`
directly in place of the inductive predicate `IsIdealDevissable`: the extra containment
`SheafOfModules.supp M ⊆ W` is carried through the recursion, and it is discharged at each of
the three branches from the fact that every piece the two steps produce has support inside the
support of the module being taken apart.

**The dichotomy that uses hypothesis (2).** A subscheme with range inside `Z₀` has range
either equal to `Z₀` or strictly inside it, so `hproper` and `htop` between them cover every
subscheme the induction meets. This is why
`property_of_irreducible_support_of_topIdeals` needs neither `IsClosed Z₀` nor
`IsIrreducible Z₀` nor the generic point `ξ`: the source uses the irreducibility of `Z₀` only
inside the two halves that are hypotheses here — to know that a closed subset of `Z₀` missing
`ξ` is strictly smaller, and to form the reduced induced structure on `Z₀`.

## References

* [Stacks Project, Tag 01YD](https://stacks.math.columbia.edu/tag/01YD)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.DevissageBounded
open Stacks.AlgebraicGeometry.DevissageNoetherian

universe u

namespace Stacks.AlgebraicGeometry.ConfinedDevissage

variable {X : Scheme.{u}}

/-! ### Weakening the quotient class of a dévissage filtration -/

/-- A bounded dévissage filtration with quotients in `Q` is one with quotients in any larger
class `Q'`. The filtration data is unchanged; only the last conjunct is weakened. -/
theorem hasDevissageWith_mono {Q Q' : X.Modules → Prop} (h : ∀ M : X.Modules, Q M → Q' M)
    {F : X.Modules} (hF : HasDevissageWith Q F) : HasDevissageWith Q' F := by
  obtain ⟨n, G, f, hmono, hzeroG, hcoh, hcoker, he, hquot⟩ := hF
  exact ⟨n, G, f, hmono, hzeroG, hcoh, hcoker, he, fun i hi => h _ (hquot i hi)⟩

/-! ### The quotient class of [Stacks, Tag 01YF], confined to a subset -/

/-- The quotient class of [Stacks, Tag 01YF] **with the subscheme confined to `W`**: modules
isomorphic to the direct image of a quasi-coherent ideal sheaf on an integral closed subscheme
of `X` whose range lies in `W`.

The absolute class `Stacks.AlgebraicGeometry.DevissageBounded.IsIdealPushforward` is this one
with `W = Set.univ` in effect; the containment is what [Stacks, Tag 01YH] needs and what the
absolute class discards. -/
def IsIdealPushforwardIn (W : Set X) (M : X.Modules) : Prop :=
  ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (_ : IsClosedImmersion ι) (_ : IsIntegral Z)
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
    I.toSheafOfModules.IsQuasicoherent ∧ Set.range ι.base ⊆ W ∧
      Nonempty (M ≅ (Scheme.Modules.pushforward ι).obj I.toSheafOfModules)

/-- Forgetting the containment recovers the absolute class. -/
theorem isIdealPushforward_of_isIdealPushforwardIn {W : Set X} {M : X.Modules}
    (h : IsIdealPushforwardIn W M) : IsIdealPushforward M := by
  obtain ⟨Z, ι, hι, hZ, I, hI, -, he⟩ := h
  exact ⟨Z, ι, hι, hZ, I, hI, he⟩

/-- The confined class grows with the confining set. -/
theorem isIdealPushforwardIn_mono {W W' : Set X} (hW : W ⊆ W') {M : X.Modules}
    (h : IsIdealPushforwardIn W M) : IsIdealPushforwardIn W' M := by
  obtain ⟨Z, ι, hι, hZ, I, hI, hr, he⟩ := h
  exact ⟨Z, ι, hι, hZ, I, hI, hr.trans hW, he⟩

/-- **The irreducible step of [Stacks, Tag 01YF], relativized.** A coherent module with
irreducible support carries a bounded dévissage filtration each of whose successive quotients is
either the direct image of a quasi-coherent ideal sheaf on an integral closed subscheme **whose
range lies in the support of the module**, or supported strictly inside that support.

This is `Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage` with the
containment the source's construction actually delivers: step 4 of the proof of
[Stacks, Tag 01YF] takes the subscheme to be the reduced induced structure on the support, whose
range is the support. -/
def HasIrreducibleDevissageIn (X : Scheme.{u}) : Prop :=
  ∀ F : X.Modules, F.IsCoherent → IsIrreducible (SheafOfModules.supp F) →
    HasDevissageWith
      (fun M => IsIdealPushforwardIn (SheafOfModules.supp F) M ∨
        SheafOfModules.supp M ⊂ SheafOfModules.supp F) F

/-- The relativized irreducible step implies the absolute one,
`Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage`. -/
theorem hasIrreducibleDevissage_of_hasIrreducibleDevissageIn
    (h : HasIrreducibleDevissageIn X) : HasIrreducibleDevissage X := by
  intro F hF hirr
  refine hasDevissageWith_mono (fun M hM => ?_) (h F hF hirr)
  exact hM.imp isIdealPushforward_of_isIdealPushforwardIn id

/-! ### Support and restriction to an open set -/

/-- **A zero module has empty support.** This is the converse of
`Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty`. Every section of a zero
module vanishes, because the identity morphism is the zero morphism and hence so is the identity
of each module of sections, and every element of a stalk is the germ of a section. -/
theorem supp_eq_empty_of_isZero (M : X.Modules) (h : IsZero M) :
    SheafOfModules.supp M = ∅ := by
  have hid : (𝟙 M : M ⟶ M) = 0 := (IsZero.iff_id_eq_zero M).mp h
  have hsec : ∀ (V : X.Opens) (s : Γ(M, V)), s = 0 := by
    intro V s
    have happ := congrArg (fun φ : M ⟶ M => Scheme.Modules.Hom.app φ V) hid
    simp only [Scheme.Modules.Hom.id_app, Scheme.Modules.Hom.zero_app] at happ
    have hzs := congrArg (fun f : Γ(M, V) ⟶ Γ(M, V) => f.hom s) happ
    simpa using hzs
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha⟩
  obtain ⟨V, hzV, s, hs⟩ := M.presheaf.exists_germ_eq a
  exact ha (by rw [← hs, hsec V s]; exact map_zero _)

/-- **A point of an open set on which a module restricts to something with empty support is
outside the support of the module.** The comparison is
`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`, which identifies the stalk of the
restriction at a point of the open set with the stalk of the module at its image. That
comparison is only an isomorphism of abelian groups, which is exactly the generality
`SheafOfModules.supp` needs, since the support is defined by existence of a nonzero element of
the stalk of the underlying additive presheaf. -/
theorem notMem_supp_of_supp_restrict_eq_empty (C : X.Modules) (U : X.Opens)
    (h : SheafOfModules.supp ((Scheme.Modules.restrictFunctor U.ι).obj C) = ∅)
    (x : X) (hx : x ∈ U) : x ∉ SheafOfModules.supp C := by
  let y : U.toScheme := ⟨x, hx⟩
  let e := (Scheme.Modules.restrictStalkNatIso U.ι y).app C
  rintro ⟨a, ha⟩
  let a' : (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (U.ι y)).obj C := a
  have ha' : a' ≠ 0 := ha
  have key : (ConcreteCategory.hom e.hom) ((ConcreteCategory.hom e.inv) a') = a' := by
    rw [← ConcreteCategory.comp_apply, e.inv_hom_id, ConcreteCategory.id_apply]
  have hb : (ConcreteCategory.hom e.inv) a' ≠ 0 := fun hz => ha' (by rw [← key, hz, map_zero])
  have hmem : y ∈ SheafOfModules.supp ((Scheme.Modules.restrictFunctor U.ι).obj C) :=
    ⟨(ConcreteCategory.hom e.inv) a', hb⟩
  simp [h] at hmem

/-- **The restriction of a cokernel to an open set on which the map is an isomorphism is zero.**
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is a left adjoint, by
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, so it preserves cokernels; an
isomorphism is epi, so its cokernel is zero.

The `PreservesColimitsOfSize` instance has to be produced by hand and at explicit universes:
instance search does not find it, and leaving the universes to elaboration fails to infer
them. -/
theorem isZero_restrict_cokernel {A B : X.Modules} (φ : A ⟶ B) (U : X.Opens)
    (hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj (cokernel φ)) := by
  have hpc : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor U.ι) :=
    (Scheme.Modules.restrictAdjunction U.ι).leftAdjoint_preservesColimits
  have hep : Epi ((Scheme.Modules.restrictFunctor U.ι).map φ) := inferInstance
  exact IsZero.of_iso (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor U.ι).map φ))
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor U.ι) φ)

/-- A point of an open set on which a morphism restricts to an isomorphism is outside the
support of the cokernel. -/
theorem notMem_supp_cokernel_of_isIso_restrict {A B : X.Modules} (φ : A ⟶ B) (U : X.Opens)
    (hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) (x : X) (hx : x ∈ U) :
    x ∉ SheafOfModules.supp (cokernel φ) :=
  notMem_supp_of_supp_restrict_eq_empty _ U
    (supp_eq_empty_of_isZero _ (isZero_restrict_cokernel φ U hiso)) x hx

/-- **The cokernel of a generically invertible morphism is supported strictly inside `Z₀`.** If a
morphism restricts to an isomorphism on a neighbourhood of a point `ξ` of `Z₀`, and the cokernel
is supported inside `Z₀`, then that support is strictly smaller, because it misses `ξ`.

This is the shape in which [Stacks, Tag 01YE] delivers its conclusion — a neighbourhood of the
generic point on which the inclusion is invertible — turned into the hypothesis
`property_of_supp_ssubset` consumes. No irreducibility is used: only that `ξ` lies in `Z₀` and
not in the support. -/
theorem supp_cokernel_ssubset_of_isIso_restrict {A B : X.Modules} (φ : A ⟶ B) {Z₀ : Set X}
    (U : X.Opens) (hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ))
    (ξ : X) (hξU : ξ ∈ U) (hξ : ξ ∈ Z₀)
    (hsub : SheafOfModules.supp (cokernel φ) ⊆ Z₀) :
    SheafOfModules.supp (cokernel φ) ⊂ Z₀ :=
  lt_of_le_of_ne hsub fun hEq =>
    notMem_supp_cokernel_of_isIso_restrict φ U hiso ξ hξU (hEq.symm.subset hξ)

/-! ### The relativized Noetherian induction -/

/-- A monomorphism followed by its cokernel projection is a short exact sequence. -/
private theorem shortExact_mk_cokernel_π {A B : X.Modules} (φ : A ⟶ B) [Mono φ] :
    (ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel φ)

variable (P : X.Modules → Prop)

/-- **The Noetherian induction of [Stacks, Tag 01YF], relative to a subset `W`.** A property of
modules that holds on the zero module, is stable under extensions of coherent modules, and holds
on the direct image of every quasi-coherent ideal sheaf on every integral closed subscheme whose
range lies in `W`, holds on every coherent module supported inside `W`.

Neither closedness nor irreducibility of `W` is needed; `W` enters only through containments.
With `W = Set.univ` this is
`Stacks.AlgebraicGeometry.DevissageNoetherian.property_of_devissageSteps`, which is
[Stacks, Tag 01YG] conditional on the same two steps.

The hypotheses `hsplit` and `hirr` are [Stacks, Tag 01YD] and the irreducible step of
[Stacks, Tag 01YF]. `hsplit` holds for every Noetherian scheme, by
`Stacks.AlgebraicGeometry.IdealPowerSmul.hasSupportSplitting`; see also
`StacksFrontier/AlgebraicGeometry/ConfinedDevissage/KilledSupport.lean`, where both `hsplit` and
`hirr` are discharged. -/
theorem property_of_supp_subset [IsNoetherian X]
    (hsplit : HasSupportSplitting X) (hirr : HasIrreducibleDevissageIn X)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    {W : Set X}
    (hideal : ∀ (Z : Scheme.{u}) (ι : Z ⟶ X), IsClosedImmersion ι → IsIntegral Z →
      Set.range ι.base ⊆ W →
      ∀ I : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
        I.toSheafOfModules.IsQuasicoherent →
        P ((Scheme.Modules.pushforward ι).obj I.toSheafOfModules))
    (F : X.Modules) (hF : F.IsCoherent) (hsupp : SheafOfModules.supp F ⊆ W) : P F := by
  have hclosed := forall_isClosed_supp X
  have hvanish := forall_isZero_of_supp_eq_empty X
  suffices H : ∀ Z : Closeds X, ∀ M : X.Modules, M.IsCoherent →
      SheafOfModules.supp M ⊆ (Z : Set X) → SheafOfModules.supp M ⊆ W → P M from
    H ⟨_, hclosed F hF⟩ F hF subset_rfl hsupp
  intro Z
  induction Z using WellFoundedLT.induction with
  | _ Z IH =>
    intro M hM hsub hsubW
    -- Either the support is strictly smaller than `Z`, and the induction hypothesis applies at
    -- once, or it is all of `Z`.
    by_cases hlt : (⟨SheafOfModules.supp M, hclosed M hM⟩ : Closeds X) < Z
    · exact IH _ hlt M hM subset_rfl hsubW
    have hZ : (Z : Set X) = SheafOfModules.supp M :=
      congrArg _ (eq_of_le_of_not_lt (SetLike.coe_subset_coe.mp hsub) hlt).symm
    -- The induction hypothesis at every closed set strictly inside the support. The containment
    -- in `W` is inherited, which is the whole cost of the relativization.
    have IH' : ∀ N : X.Modules, N.IsCoherent →
        SheafOfModules.supp N ⊂ SheafOfModules.supp M → P N := by
      intro N hN hlt'
      exact IH ⟨SheafOfModules.supp N, hclosed N hN⟩
        (SetLike.coe_ssubset_coe.mp (hZ ▸ hlt')) N hN subset_rfl (hlt'.subset.trans hsubW)
    by_cases hne : (SheafOfModules.supp M).Nonempty
    swap
    · exact property_of_iso P hzero hext
        (isZero_terminal.iso (hvanish M (Set.not_nonempty_iff_eq_empty.mp hne)))
        isCoherent_terminal hzero
    by_cases hpre : IsPreirreducible (SheafOfModules.supp M)
    · refine property_of_hasDevissageWith P hzero hext ?_ M (hirr M hM ⟨hne, hpre⟩)
      rintro N (hN | hN) hNc
      · obtain ⟨Y, ι, hι, hY, I, hI, hr, ⟨e⟩⟩ := hN
        have hPI := hideal Y ι hι hY (hr.trans hsubW) I hI
        have := hNc
        exact property_of_iso P hzero hext e.symm (isCoherent_of_iso e.symm) hPI
      · exact IH' N hNc hN
    -- The support is reducible: it is covered by two closed sets, neither containing it.
    rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
    simp only [not_forall, not_or] at hpre
    obtain ⟨z₁, z₂, hz₁, hz₂, hcov, hn₁, hn₂⟩ := hpre
    obtain ⟨W₁, W₂, hW₁, hW₂, hWcov, hWlt₁, hWlt₂⟩ :
        ∃ W₁ W₂ : Set X, IsClosed W₁ ∧ IsClosed W₂ ∧ SheafOfModules.supp M = W₁ ∪ W₂ ∧
          W₁ ⊂ SheafOfModules.supp M ∧ W₂ ⊂ SheafOfModules.supp M := by
      refine ⟨SheafOfModules.supp M ∩ z₁, SheafOfModules.supp M ∩ z₂,
        (hclosed M hM).inter hz₁, (hclosed M hM).inter hz₂, Set.Subset.antisymm ?_ ?_,
        ⟨Set.inter_subset_left, fun h => ?_⟩, ⟨Set.inter_subset_left, fun h => ?_⟩⟩
      · intro x hx
        rcases hcov hx with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro x (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      · exact hn₁ fun x hx => ((h hx).2)
      · exact hn₂ fun x hx => ((h hx).2)
    obtain ⟨K, ι, hmono, hK, hcoker, hKsupp, hQsupp⟩ := hsplit M hM W₁ W₂ hW₁ hW₂ hWcov
    have := hmono
    exact hext _ (shortExact_mk_cokernel_π ι) hK hM hcoker
      (IH' K hK (lt_of_le_of_lt hKsupp hWlt₁))
      (IH' _ hcoker (lt_of_le_of_lt hQsupp hWlt₂))

/-! ### The first paragraph of the proof of [Stacks, Tag 01YH] -/

/-- **A coherent module whose support is strictly smaller than `Z₀` satisfies `P`.** This is the
first paragraph of the source's proof: hypothesis (2) of 01YH — `P` on ideal direct images
from integral closed subschemes *strictly* inside `Z₀` — already covers every subscheme the
relativized induction meets when the support is strictly inside `Z₀`, because a subscheme whose
range lies in a set strictly inside `Z₀` has range strictly inside `Z₀`.

The hypothesis `hproper` is hypothesis (2) of [Stacks, Tag 01YH] verbatim. In
`property_of_irreducible_support_of_topIdeals`, `hzero` is supplied from the two-out-of-three
hypothesis and the module `G` by
`Stacks.AlgebraicGeometry.DevissageBounded.property_terminal_of_twoOutOfThree`. -/
theorem property_of_supp_ssubset [IsNoetherian X]
    (hsplit : HasSupportSplitting X) (hirr : HasIrreducibleDevissageIn X)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    {Z₀ : Set X}
    (hproper : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base ⊂ Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (F : X.Modules) (hF : F.IsCoherent) (hsupp : SheafOfModules.supp F ⊂ Z₀) : P F :=
  property_of_supp_subset P hsplit hirr hzero hext
    (W := SheafOfModules.supp F)
    (fun Y ι hι hY hr I hI => @hproper Y ι hι hY (lt_of_le_of_lt hr hsupp) I hI)
    F hF subset_rfl

/-! ### [Stacks, Tag 01YH], conditional on the top-stratum ideals -/

/-- **[Stacks, Tag 01YH], conditional on the two steps of [Stacks, Tag 01YF] and on the
top-stratum ideals.** The conclusion of 01YH — `P` on every coherent module supported inside
`Z₀` — follows from its two-out-of-three hypothesis `hexact`, its hypothesis `hproper` on
subschemes strictly inside `Z₀`, a single coherent module `G` satisfying `P` (the only part of
hypothesis (3) used here), and `htop`: `P` on the direct image of every quasi-coherent ideal
sheaf on every integral closed subscheme whose range is **all** of `Z₀`.

`hexact`, `hproper` and `G` are as in the statement of 01YH; the added hypotheses are `hsplit`,
`hirr` and `htop`. Neither `IsClosed Z₀` nor `IsIrreducible Z₀` nor a generic point is
required: the source uses the irreducibility of `Z₀` only inside the three added hypotheses.

The length-one condition and the annihilation condition of hypothesis (3) are used only in the
proof of `htop`, and are therefore absent here. -/
theorem property_of_irreducible_support_of_topIdeals [IsNoetherian X]
    (hsplit : HasSupportSplitting X) (hirr : HasIrreducibleDevissageIn X)
    {Z₀ : Set X}
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hproper : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base ⊂ Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (htop : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base = Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (G : X.Modules) (hG : G.IsCoherent) (hPG : P G) :
    ∀ F : X.Modules, F.IsCoherent → SheafOfModules.supp F ⊆ Z₀ → P F := by
  refine fun F hF hsupp =>
    property_of_supp_subset P hsplit hirr
      (property_terminal_of_twoOutOfThree P hexact G hG hPG)
      (ext_of_twoOutOfThree P hexact) (W := Z₀) (fun Y ι hι hY hr I hI => ?_) F hF hsupp
  -- A subscheme with range inside `Z₀` has range either equal to `Z₀` or strictly inside it.
  rcases eq_or_lt_of_le hr with h | h
  · exact @htop Y ι hι hY h I hI
  · exact @hproper Y ι hι hY h I hI

/-! ### The step [Stacks, Tag 01YE] feeds, once the multiplicity is one -/

/-- **Two-out-of-three read backwards.** `P` on `B` and on the cokernel of a monomorphism
`φ : A ⟶ B` gives `P` on `A`. This is the third clause of hypothesis (1) of [Stacks, Tag 01YH],
applied to the short exact sequence `0 → A → B → cokernel φ → 0`; the weaker extension
hypothesis of [Stacks, Tag 01YG] does not give it.

The short complex is built from the constructor so that its three terms are syntactically `A`,
`B` and `cokernel φ`, as in the implementation notes of
`StacksFrontier/AlgebraicGeometry/CoherentDevissage/Devissage.lean`. -/
theorem property_sub_of_twoOutOfThree
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    {A B : X.Modules} (φ : A ⟶ B) (hφ : Mono φ)
    (hA : A.IsCoherent) (hB : B.IsCoherent) (hC : (cokernel φ).IsCoherent)
    (hPB : P B) (hPC : P (cokernel φ)) : P A :=
  have := hφ
  (hexact _ (shortExact_mk_cokernel_π φ) hA hB hC).2.2 ⟨hPB, hPC⟩

/-- **The step the source takes with [Stacks, Tag 01YE], assembled.** Suppose the module `G`
of hypothesis (3) of [Stacks, Tag 01YH] receives a monomorphism from the direct image of a
quasi-coherent ideal sheaf on an integral closed subscheme, with cokernel supported strictly
inside `Z₀` — which is what [Stacks, Tag 01YE] provides once the multiplicity `r` is known to be
`1`, since the monomorphism is then an isomorphism near the generic point. Then `P` holds for
that direct image.

The cokernel's `P` comes from `property_of_supp_ssubset`, so hypothesis (2) is the only
geometric input; the transfer itself is `property_sub_of_twoOutOfThree`. -/
theorem property_pushforward_of_mono_of_supp_ssubset [IsNoetherian X]
    (hsplit : HasSupportSplitting X) (hirr : HasIrreducibleDevissageIn X)
    {Z₀ : Set X}
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hproper : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base ⊂ Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (G : X.Modules) (hG : G.IsCoherent) (hPG : P G)
    {Z : Scheme.{u}} (i : Z ⟶ X)
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hIcoh : ((Scheme.Modules.pushforward i).obj I.toSheafOfModules).IsCoherent)
    (φ : (Scheme.Modules.pushforward i).obj I.toSheafOfModules ⟶ G) (hφ : Mono φ)
    (hcoh : (cokernel φ).IsCoherent)
    (hsupp : SheafOfModules.supp (cokernel φ) ⊂ Z₀) :
    P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) :=
  property_sub_of_twoOutOfThree P hexact φ hφ hIcoh hG hcoh hPG
    (property_of_supp_ssubset P hsplit hirr
      (property_terminal_of_twoOutOfThree P hexact G hG hPG)
      (ext_of_twoOutOfThree P hexact) hproper _ hcoh hsupp)

/-- **The same step, with the hypothesis in the shape [Stacks, Tag 01YE] produces it.**
[Stacks, Tag 01YE] gives the monomorphism together with an open `U` containing the generic point
on which it becomes an isomorphism, not a statement about the support of the cokernel. This
version takes that data and does the conversion itself, by
`supp_cokernel_ssubset_of_isIso_restrict`.

The containment `hsub` follows from the support of `G` being `Z₀`, since the support of a
quotient is contained in the support of the module
(`Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_cokernel_subset`). Without multiplicity
one, the source of the monomorphism is the direct image of a *finite coproduct* of copies of
`I`, filtered by its factors in
`Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_pushforward_coproduct_const`;
two-out-of-three does not descend `P` from the coproduct to a single factor. -/
theorem property_pushforward_of_mono_of_isIso_restrict [IsNoetherian X]
    (hsplit : HasSupportSplitting X) (hirr : HasIrreducibleDevissageIn X)
    {Z₀ : Set X}
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hproper : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base ⊂ Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (G : X.Modules) (hG : G.IsCoherent) (hPG : P G)
    {Z : Scheme.{u}} (i : Z ⟶ X)
    (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hIcoh : ((Scheme.Modules.pushforward i).obj I.toSheafOfModules).IsCoherent)
    (φ : (Scheme.Modules.pushforward i).obj I.toSheafOfModules ⟶ G) (hφ : Mono φ)
    (hcoh : (cokernel φ).IsCoherent)
    (ξ : X) (hξ : ξ ∈ Z₀) (U : X.Opens) (hξU : ξ ∈ U)
    (hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ))
    (hsub : SheafOfModules.supp (cokernel φ) ⊆ Z₀) :
    P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) :=
  property_pushforward_of_mono_of_supp_ssubset P hsplit hirr hexact hproper G hG hPG i I hIcoh
    φ hφ hcoh (supp_cokernel_ssubset_of_isIso_restrict φ U hiso ξ hξU hξ hsub)

end Stacks.AlgebraicGeometry.ConfinedDevissage

end

end
