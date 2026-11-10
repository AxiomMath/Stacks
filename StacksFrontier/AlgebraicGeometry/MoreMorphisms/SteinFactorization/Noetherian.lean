module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.RelativeSpectrum
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stein factorization over a locally Noetherian base

Let `S` be a locally Noetherian scheme and let `f : X ⟶ S` be proper.  [Stacks, Tag 03H0]
asserts that `f` factors as `X --f'--> S' --π--> S` with

1. `f'` proper with geometrically connected fibres,
2. `π` **finite**,
3. `f'_* 𝒪_X = 𝒪_{S'}`,
4. `S' = Spec_S(f_* 𝒪_X)`, and
5. `S'` the normalization of `S` in `X`.

The intermediate scheme is produced, not assumed:  it is the normalization
`AlgebraicGeometry.Scheme.Hom.normalization` of `S` in `X`, with `f' = f.toNormalization` and
`π = f.fromNormalization`.

Each clause is a theorem of its own below, stated at the hypotheses of this tag — `S` locally
Noetherian and `f` proper — and registered on it.  Clauses (5),
(1) (properness) , (3) and (4) are the corresponding clauses of the general [Stacks, Tag 03H2],
which holds for an arbitrary base, so their proofs here are one application each.

What this module adds to the general factorization of [Stacks, Tag 03H2] is clause (2), the
upgrade of integrality of `π` to **finiteness**, which is where the local Noetherianness of `S`
enters.  It is proved here unconditionally from [Stacks, Tag 02O5]: the direct image
`f_* 𝒪_X` of the structure sheaf is a coherent `𝒪_S`-module, so its sections over an affine open
`U` of `S` form a finite `Γ(S, U)`-module, so `Γ(S, U) ⟶ Γ(X, f ⁻¹ᵁ U)` is a finite ring map;
and that map factors as `Γ(S, U) ⟶ Γ(S', π ⁻¹ᵁ U) ⟶ Γ(X, f ⁻¹ᵁ U)` with the second map an
isomorphism, by [Stacks, Tag 03GY], so the first map is finite too.

## Main results

* `Stacks.SteinFactorization.finite_app_of_isProper`: for `f` proper onto a locally Noetherian
  base, `Γ(S, U) ⟶ Γ(X, f ⁻¹ᵁ U)` is a finite ring map for every affine open `U` of `S`.
* `Stacks.SteinFactorization.isFinite_fromNormalization`: **clause (2)**, unconditionally.
* `Stacks.SteinFactorization.toNormalization_fromNormalization_of_isLocallyNoetherian`: the
  factorization together with **clause (5)**, unconditionally.
* `Stacks.SteinFactorization.isProper_toNormalization_of_isLocallyNoetherian`: the properness
  conjunct of **clause (1)**, unconditionally.
* `Stacks.SteinFactorization.isIso_c_toNormalization_of_isLocallyNoetherian`: **clause (3)**,
  unconditionally.
* `Stacks.SteinFactorization.overIsoPushforwardSpectrum_of_isLocallyNoetherian` and
  `toNormalization_overIsoPushforwardSpectrum_hom_left_of_isLocallyNoetherian`: **clause (4)**,
  unconditionally.
* `Stacks.SteinFactorization.geometricallyConnected_toNormalization`: the connectedness
  conjunct of **clause (1)**, unconditionally.  It is
  `Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper`, clause (1) of
  the general [Stacks, Tag 03H2], read at the stronger hypotheses of this tag.
* `Stacks.SteinFactorization.eq_zero_or_one_of_clopenSplitting`: why the input used here
  is Tag 0G7X and *not* the stronger clopen-splitting statement — that
  statement is **false**, and this is a machine-checked consequence of it that exhibits the
  failure.
* `Stacks.SteinFactorization.IsSteinFactorization`: the five clauses of the tag, as a structure
  on a factorization `f = f' ≫ π`.
* `Stacks.SteinFactorization.exists_isSteinFactorization`: **the tag**, unconditionally.

## Implementation notes

**No carried hypothesis.**  Every clause of this tag, including the connectedness conjunct of
clause (1), is proved outright.  That conjunct rests on [Stacks, Tag 0G7X], in exactly the form
the tag has — an idempotent of
`Γ(X_s, 𝒪_{X_s})` is the restriction of a section of `𝒪_X` over `f ⁻¹ᵁ U` for some open
neighbourhood `U` of `s`, `Stacks.AlgebraicGeometry.Fibres.ExtendsOverNeighbourhood`, quantified
over all proper morphisms.  Tag 0G7X is
`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`.

**Why not the clopen-splitting hypothesis.**  A tempting alternative input is the *geometric*
statement `hsplit` of
`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isIdempotentElem_of_isProper`:  for
every proper `g : Y ⟶ T`, every `t : T` and every idempotent `c ∈ Γ(Y_t, 𝒪_{Y_t})`, an open
neighbourhood `U` of `t` together with two *disjoint* opens `V₁, V₂` covering `g ⁻¹ᵁ U` and
cutting the fibre in the nonvanishing locus of `c`.  That statement is strictly stronger than
Tag 0G7X — it asks the lift to be an *idempotent* section, not merely a section — and it is
**false**.  `Stacks.SteinFactorization.eq_zero_or_one_of_clopenSplitting` derives from it that
every fibre of every proper morphism whose source is (pre)irreducible has only the trivial
idempotents in its ring of global functions;  but `Spec ℤ[i] ⟶ Spec ℤ` is finite, hence proper,
its source is irreducible, and its fibre over the prime `(5)` is `Spec(𝔽₅ × 𝔽₅)`, whose global
functions contain a nontrivial idempotent.  (The disjointness forces one of `V₁, V₂` to be empty
on an irreducible source, and then the trace on the fibre is `⊥` or the whole fibre.)  So any
theorem carrying `hsplit` is vacuous, and the proof uses instead the tag that the source
actually quotes.

**No circularity with [Stacks, Tag 03H2].**  In this library clause (1) of Tag 03H2 is itself
derived from Tag 0G7X, and the source's proof of Tag 03H2 quotes Tag 0G7X;  so Tag 03H2 is *not*
used here.  The connectedness argument below goes through the untagged generic reduction
`Stacks.AlgebraicGeometry.geometricallyConnected_fiberToSpecResidueField_of_etaleNeighborhood`
(Tag 03GZ plus degree-zero flat base change) and Tag 0G7X, both of which sit strictly below
Tag 03H2 in the dependency order.

**Where Tag 0G7X comes from.**  The source obtains it from the theorem on formal functions
([Stacks, Tag 02OD], through [Stacks, Tag 02OC]).  That whole chain is formalized:
[Stacks, Tag 02O5] and [Stacks, Tag 02O6] are proved and 02O5 is what clause (2) below is proved
from;  `0897(1) → 02O8 → 02OA → 02OB → 02OC` is joined in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/FormalFunctionsFrom02O8.lean`, with
[Stacks, Tag 02O8] itself unconditional;  the stalk form of 02OD at `p = 0` for the structure
sheaf is `Stacks.FormalFunctions.isFormalFunctionsStalk_of_isProper`, reached by identifying the
infinitesimal neighbourhoods of the fibre with the ideal-power subschemes of
`X ×_Y Spec 𝒪_{Y,y}` (`StacksFrontier/AlgebraicGeometry/FormalFunctions/InfinitesimalBaseIdeal.lean`
and `StacksFrontier/AlgebraicGeometry/FormalFunctions/InfinitesimalBaseIdealSections.lean`) and by
degree-zero flat base change along
`Spec 𝒪_{Y,y} ⟶ Y`
(`StacksFrontier/AlgebraicGeometry/FormalFunctions/StalkBaseChangeComparison.lean`);
and the general case follows from the
locally Noetherian one by the [Stacks, Tag 0A0P] limit argument of
`StacksFrontier/AlgebraicGeometry/Fibres/IdempotentExtensionApproximation.lean`.

**Where the hypotheses are consumed.**  Properness of `f` is consumed four times over: it gives
`UniversallyClosed f` and `QuasiSeparated f`, which is what makes the normalization factor `f`
at all ([Stacks, Tag 03GY]) and what makes `Γ(S', π ⁻¹ᵁ U) ⟶ Γ(X, f ⁻¹ᵁ U)` an isomorphism; it
gives `LocallyOfFiniteType f`, hence `IsLocallyNoetherian X`, hence coherence of `𝒪_X`; and it
is the hypothesis of [Stacks, Tag 02O5].  Local Noetherianness of `S` is consumed in
[Stacks, Tag 02O5] and in passing from `LocallyOfFiniteType f` to `IsLocallyNoetherian X`;  it is
used nowhere else, which is exactly why the remaining clauses hold over an arbitrary base.

## References

* [Stacks Project, Tag 03H0](https://stacks.math.columbia.edu/tag/03H0)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 03GY](https://stacks.math.columbia.edu/tag/03GY)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 035H](https://stacks.math.columbia.edu/tag/035H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeSpec (canonicalMorphism pushforwardSpectrum)

universe u

namespace Stacks.SteinFactorization

variable {X S : Scheme.{u}}

/-! ### Clause (2): the second factor is finite -/

section Finite

variable (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f]

/-- **The direct image of the structure sheaf along a proper morphism to a locally Noetherian
scheme is coherent.**  This is [Stacks, Tag 02O5] applied to `𝒪_X`, which is coherent because
`X` is locally Noetherian, being of finite type over a locally Noetherian scheme. -/
@[ega "II 7.3.12" "F = O_X",
  ega "III 4.3.1",
  ega "III 4.8.6" "special case",
  ega "III 6.2.5" "special case",
  ega "III 6.7.9" "special case"]
public theorem isCoherent_pushforward_structureSheaf :
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).IsCoherent :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward f _

/-- **For `f` proper onto a locally Noetherian base, `Γ(S, U) ⟶ Γ(X, f ⁻¹ᵁ U)` is a finite ring
map for every affine open `U` of `S`.**  The sections of `f_* 𝒪_X` over `U` *are*
`Γ(X, f ⁻¹ᵁ U)`, with the `Γ(S, U)`-module structure induced by `f.app U`, and they form a finite
module because `f_* 𝒪_X` is coherent, hence quasi-coherent of finite type. -/
public theorem finite_app_of_isProper (U : S.Opens) (hU : IsAffineOpen U) :
    (f.app U).hom.Finite := by
  have := isCoherent_pushforward_structureSheaf f
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
  have := hqc
  have := hft
  exact AlgebraicGeometry.moduleFinite_sections_on_affine
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) U hU

/-- **A ring map whose composite with an isomorphism is finite is itself finite.**  Peeling the
isomorphism off on the right is what turns finiteness of `Γ(S, U) ⟶ Γ(X, f ⁻¹ᵁ U)` into
finiteness of the first factor `Γ(S, U) ⟶ Γ(S', π ⁻¹ᵁ U)`. -/
private theorem finite_of_comp_isIso {R T₁ T₂ : CommRingCat.{u}} (a : R ⟶ T₁) (b : T₁ ⟶ T₂)
    [IsIso b] (hab : (a ≫ b).hom.Finite) : a.hom.Finite := by
  have ha : a = (a ≫ b) ≫ inv b := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [ha, CommRingCat.hom_comp]
  exact RingHom.Finite.comp
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).surjective) hab

/-- **Restricted sections transport along an equality of morphisms.**  The codomain of
`AlgebraicGeometry.Scheme.Hom.appLE g U V` is the open `V` as given, not a preimage along `g`;  so,
unlike for `AlgebraicGeometry.Scheme.Hom.app`, an equality `g = h` of morphisms can be pushed
through it without ever having to identify two spellings of one open subset. -/
private theorem appLE_congr_hom {X Z : Scheme.{u}} {g h : X ⟶ Z} (e : g = h) {U : Z.Opens}
    {V : X.Opens} {hV : V ≤ g ⁻¹ᵁ U} : g.appLE U V hV = h.appLE U V (e ▸ hV) := by
  subst e; rfl

/-- **Stacks Project, Tag 03H0, clause (2).**  For a proper morphism `f : X ⟶ S` onto a locally
Noetherian scheme, the second factor `π : S' ⟶ S` of the Stein factorization — the structure
morphism of the normalization of `S` in `X` — is **finite**.  **No hypothesis.**

This is the one clause of Tag 03H0 that is not already a clause of the general Tag 03H2, where
`π` is only asserted to be integral, and it is where local Noetherianness of `S` is used.  The
proof is the source's: `f_* 𝒪_X` is coherent by [Stacks, Tag 02O5], so `Γ(S, U) ⟶ Γ(X, f ⁻¹ᵁ U)`
is finite for `U ⊆ S` affine open (`Stacks.SteinFactorization.finite_app_of_isProper`); that map
is `Γ(S, U) ⟶ Γ(S', π ⁻¹ᵁ U) ⟶ Γ(X, f ⁻¹ᵁ U)` and the second map is an isomorphism by
[Stacks, Tag 03GY] (`Stacks.SteinFactorization.isIso_app_toNormalization`), so the first is
finite;  and `π` is affine, being integral. -/
@[stacks 03H0 "clause (2): the second factor of the Stein factorization of a proper morphism
over a locally Noetherian base is finite.  Proved from [Stacks, Tag 02O5]
(`AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`), with no carried
hypothesis", ega "III 7.8.10" "partial", sga "1 X 1.2" "Y′ is finite over Y"]
public theorem isFinite_fromNormalization : IsFinite f.fromNormalization := by
  rw [isFinite_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  have hopen : f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U = f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, toNormalization_fromNormalization f]
  have hiso :
      IsIso (f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U) hopen.ge) := by
    have h0 : IsIso (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)) :=
      isIso_app_toNormalization f hU
    rw [Scheme.Hom.app_eq_appLE] at h0
    exact (Scheme.Hom.appLE_congr _ le_rfl rfl hopen fun g ↦ IsIso g).mp h0
  have hfac : f.fromNormalization.app U ≫
      f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U) hopen.ge = f.app U := by
    rw [Scheme.Hom.app_eq_appLE f.fromNormalization, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (toNormalization_fromNormalization f), Scheme.Hom.appLE_eq_app]
  have hfin : (f.fromNormalization.app U ≫
      f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U) hopen.ge).hom.Finite := by
    rw [hfac]
    exact finite_app_of_isProper f U hU
  exact finite_of_comp_isIso _ _ hfin

end Finite

/-! ### Clause (1): the first factor has geometrically connected fibres -/

/-- The nonvanishing loci of an idempotent and of its complement are disjoint, because the
product of the two sections is zero. -/
private theorem basicOpen_inf_basicOpen_one_sub {Y : Scheme.{u}} {V : Y.Opens} {c : Γ(Y, V)}
    (hc : IsIdempotentElem c) : Y.basicOpen c ⊓ Y.basicOpen (1 - c) = ⊥ := by
  have hmul : c * (1 - c) = 0 := by rw [mul_sub, mul_one, hc, sub_self]
  rw [← Scheme.basicOpen_mul, hmul, Scheme.basicOpen_zero]

/-- **The clopen-splitting statement is false, and this is why the hypothesis carried below is
[Stacks, Tag 0G7X] itself.**  Suppose that for every proper `g : Y ⟶ T`, every `t : T` and every
idempotent `c ∈ Γ(Y_t, 𝒪_{Y_t})` there were an open neighbourhood `U` of `t` and two *disjoint*
opens `V₁, V₂ ⊆ Y` covering `g ⁻¹ᵁ U`, with `V₁` meeting the fibre exactly in the nonvanishing
locus of `c`.  Then every fibre of every proper morphism with (pre)irreducible source would have
only the trivial idempotents in its ring of global functions.

That is absurd:  `Spec ℤ[i] ⟶ Spec ℤ` is finite, hence proper, its source is irreducible, and
its fibre over the prime `(5)` is `Spec(𝔽₅[x]/(x²+1)) = Spec(𝔽₅ × 𝔽₅)`, whose ring of global
functions has a nontrivial idempotent.  The same happens for any ramified double cover of a
curve, or for any finite morphism to a non-Henselian local base that splits in the closed fibre
without splitting globally.

The reason is visible in the proof:  on an irreducible source two disjoint opens cannot both be
nonempty, so one of `V₁, V₂` is empty.  If `V₁ = ⊥` the trace on the fibre is empty, and an
idempotent with empty nonvanishing locus is `0`.  If `V₂ = ⊥` then `V₁ = g ⁻¹ᵁ U`, whose trace on
the fibre is everything, so the nonvanishing locus of `1 - c` is empty and `c = 1`.

Tag 0G7X asks for strictly less:  that the idempotent be the restriction of *some* section over
`g ⁻¹ᵁ U`, not of an idempotent one.  In the example `(1,0) ∈ 𝔽₅ × 𝔽₅` is indeed the restriction
of a section of `𝒪_{Spec ℤ[i]}`, since `ℤ[i] ⟶ 𝔽₅ × 𝔽₅` is surjective;  what fails is only the
idempotency of the lift. -/
public theorem eq_zero_or_one_of_clopenSplitting
    (hsplit : ∀ {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] (t : T) (c : Γ(g.fiber t, ⊤)),
      IsIdempotentElem c → ∃ (U : T.Opens) (_ : t ∈ U) (V₁ V₂ : Y.Opens), V₁ ≤ g ⁻¹ᵁ U ∧
        V₂ ≤ g ⁻¹ᵁ U ∧ g ⁻¹ᵁ U ≤ V₁ ⊔ V₂ ∧ V₁ ⊓ V₂ = ⊥ ∧
          g.fiberι t ⁻¹ᵁ V₁ = (g.fiber t).basicOpen c)
    {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] [PreirreducibleSpace Y] (t : T)
    {c : Γ(g.fiber t, ⊤)} (hc : IsIdempotentElem c) : c = 0 ∨ c = 1 := by
  obtain ⟨U, hU, V₁, V₂, hle₁, hle₂, hcover, hdisj, htrace⟩ := hsplit g t c hc
  have hne : ∀ V : Y.Opens, V ≠ ⊥ → ((V : Set Y)).Nonempty := by
    intro V hV
    rw [Set.nonempty_iff_ne_empty]
    simpa using hV
  have hbot : V₁ = ⊥ ∨ V₂ = ⊥ := by
    by_contra hcon
    rw [not_or] at hcon
    have hinter := (PreirreducibleSpace.isPreirreducible_univ (X := Y))
      (V₁ : Set Y) (V₂ : Set Y) V₁.isOpen V₂.isOpen
      (by simpa using hne V₁ hcon.1) (by simpa using hne V₂ hcon.2)
    have hempty : (V₁ : Set Y) ∩ (V₂ : Set Y) = ∅ := by
      have : ((V₁ ⊓ V₂ : Y.Opens) : Set Y) = ((⊥ : Y.Opens) : Set Y) := by rw [hdisj]
      simpa using this
    simp [hempty] at hinter
  obtain h | h := hbot
  · refine Or.inl
      (Stacks.AlgebraicGeometry.ProperGeomConnected.eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot
        hc ?_)
    rw [← htrace, h]
    ext x
    simp
  · have hV₁ : V₁ = g ⁻¹ᵁ U := le_antisymm hle₁ (by simpa [h] using hcover)
    have htop : g.fiberι t ⁻¹ᵁ V₁ = ⊤ := by
      rw [hV₁]
      exact Stacks.AlgebraicGeometry.Fibres.fiberι_preimage_preimage_eq_top g hU
    have hcompl : (g.fiber t).basicOpen (1 - c) = ⊥ := by
      have hd := basicOpen_inf_basicOpen_one_sub hc
      rw [← htrace, htop, top_inf_eq] at hd
      exact hd
    have hzero : (1 : Γ(g.fiber t, ⊤)) - c = 0 :=
      Stacks.AlgebraicGeometry.ProperGeomConnected.eq_zero_of_isIdempotentElem_of_basicOpen_eq_bot
        hc.one_sub hcompl
    exact Or.inr (sub_eq_zero.mp hzero).symm

/-- **The clopen-splitting statement forces every nonempty fibre of every proper morphism with
(pre)irreducible source to be connected**, which is the sharpest form of its falsity:  a
ramified double cover of a curve, or `Spec ℤ[i] ⟶ Spec ℤ` at the prime `(5)`, is proper with
irreducible source and has a fibre with two points.

The fibre is proper over the residue field `κ(t)`, so connectedness is equivalent to triviality
of the idempotents of its ring of global functions
(`Stacks.AlgebraicGeometry.ProperGeomConnected.connectedSpace_of_isProper_of_isIdempotentElem`),
and `Stacks.SteinFactorization.eq_zero_or_one_of_clopenSplitting` supplies that. -/
public theorem connectedSpace_fiber_of_clopenSplitting
    (hsplit : ∀ {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] (t : T) (c : Γ(g.fiber t, ⊤)),
      IsIdempotentElem c → ∃ (U : T.Opens) (_ : t ∈ U) (V₁ V₂ : Y.Opens), V₁ ≤ g ⁻¹ᵁ U ∧
        V₂ ≤ g ⁻¹ᵁ U ∧ g ⁻¹ᵁ U ≤ V₁ ⊔ V₂ ∧ V₁ ⊓ V₂ = ⊥ ∧
          g.fiberι t ⁻¹ᵁ V₁ = (g.fiber t).basicOpen c)
    {Y T : Scheme.{u}} (g : Y ⟶ T) [IsProper g] [PreirreducibleSpace Y] (t : T)
    [Nonempty (g.fiber t)] : ConnectedSpace (g.fiber t) := by
  have : IsProper (g.fiberToSpecResidueField t) :=
    inferInstanceAs (IsProper (pullback.snd g (T.fromSpecResidueField t)))
  have hne : Nonempty ((⊤ : (g.fiber t).Opens)) := ⟨⟨Classical.arbitrary _, trivial⟩⟩
  have hnt : Nontrivial Γ(g.fiber t, ⊤) := Scheme.component_nontrivial _ ⊤
  exact Stacks.AlgebraicGeometry.ProperGeomConnected.connectedSpace_of_isProper_of_isIdempotentElem
    (L := T.residueField t) (g.fiberToSpecResidueField t)
    fun e he ↦ eq_zero_or_one_of_clopenSplitting hsplit g t he

/-- **Stacks Project, Tag 03H0, clause (1), the geometric connectedness conjunct.**  For `f`
proper onto a locally Noetherian scheme `S`, the first factor `f' : X ⟶ S'` of the Stein
factorization — `S'` the normalization of `S` in `X` and `f' = f.toNormalization` — has
geometrically connected fibres.

Unconditional, at the hypotheses of the tag.  It is the reading of
`Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper`, clause (1) of the
general [Stacks, Tag 03H2], at the stronger hypotheses of this tag;  the local Noetherianness of
`S` is not used.

The properness conjunct of the same clause is
`Stacks.SteinFactorization.isProper_toNormalization_of_isLocallyNoetherian` below. -/
@[stacks 03H0 "clause (1), the geometric connectedness conjunct: the first factor of the Stein \
  factorization of a proper morphism onto a locally Noetherian base has geometrically connected \
  fibres. The properness conjunct of the same clause is \
  isProper_toNormalization_of_isLocallyNoetherian", ega "III 4.3.4" "special case"]
public theorem geometricallyConnected_toNormalization (f : X ⟶ S) [IsLocallyNoetherian S]
    [IsProper f] : GeometricallyConnected f.toNormalization :=
  geometricallyConnected_toNormalization_of_isProper f

/-! ### Clauses (5), (1) (properness), (3) and (4) at the hypotheses of Tag 03H0 -/

section RemainingClauses

variable (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f]

omit [IsLocallyNoetherian S] in
/-- **Stacks Project, Tag 03H0: the factorization, together with clause (5).**  A proper morphism
`f : X ⟶ S` onto a locally Noetherian scheme factors as `X --f'--> S' --π--> S` *through the
normalization of `S` in `X`* ([Stacks, Tag 035H],
`AlgebraicGeometry.Scheme.Hom.normalization`), with `f' = f.toNormalization` and
`π = f.fromNormalization`.  That the intermediate scheme of the factorization is the
normalization of `S` in `X` is clause (5), and since the intermediate scheme produced here *is*
`f.normalization` the whole content of that clause is the displayed equation.

Local Noetherianness is not needed: this is the general factorization of [Stacks, Tag 03H2],
which holds for any proper morphism, specialized to the hypotheses of Tag 03H0. -/
@[stacks 03H0 "the factorization itself together with clause (5): f factors as
X --f'--> S' --π--> S with S' the normalization of S in X (Stacks 035H), f' = f.toNormalization
and π = f.fromNormalization.  No carried hypothesis"]
public theorem toNormalization_fromNormalization_of_isLocallyNoetherian :
    f.toNormalization ≫ f.fromNormalization = f :=
  toNormalization_fromNormalization f

omit [IsLocallyNoetherian S] in
/-- **Stacks Project, Tag 03H0, clause (1), properness half.**  The first factor
`f' : X ⟶ S'` of the Stein factorization of a proper morphism onto a locally Noetherian scheme is
proper.  Local Noetherianness is not needed: `f'` is universally closed because `f` is, and
separated and locally of finite type by cancellation along `π`, which is the general
[Stacks, Tag 03H2] specialized to the hypotheses of Tag 03H0. -/
@[stacks 03H0 "clause (1), the properness half: the first factor of the Stein factorization is
proper.  No carried hypothesis"]
public theorem isProper_toNormalization_of_isLocallyNoetherian : IsProper f.toNormalization :=
  isProper_toNormalization f

omit [IsLocallyNoetherian S] in
/-- **Stacks Project, Tag 03H0, clause (3).**  `f'_* 𝒪_X = 𝒪_{S'}` for the first factor of the
Stein factorization of a proper morphism onto a locally Noetherian scheme:  the canonical map
`𝒪_{S'} ⟶ f'_* 𝒪_X` is an isomorphism.  Local Noetherianness is not needed; this is
[Stacks, Tag 03H2] clause (3), which holds for any proper morphism, specialized to the hypotheses
of Tag 03H0. -/
@[stacks 03H0 "clause (3): f'_* 𝒪_X = 𝒪_{S'}, i.e. the canonical map 𝒪_{S'} ⟶ f'_* 𝒪_X is an
isomorphism.  No carried hypothesis"]
public theorem isIso_c_toNormalization_of_isLocallyNoetherian : IsIso f.toNormalization.c :=
  isIso_c_toNormalization_of_isProper f

/-- **Stacks Project, Tag 03H0, clause (4).**  The intermediate scheme `S'` of the Stein
factorization of a proper morphism onto a locally Noetherian scheme is the relative spectrum
`Spec_S(f_* 𝒪_X)`, as a scheme over `S`.  Being an isomorphism in `CategoryTheory.Over S` is what
makes this an identification of *factorizations*:  it says that `π` is carried to the structure
morphism of the relative spectrum.  Local Noetherianness is not needed; this is
[Stacks, Tag 03H2] clause (4) specialized to the hypotheses of Tag 03H0. -/
@[stacks 03H0 "clause (4): S' = Spec_S(f_* 𝒪_X), as an isomorphism in Over S, so that π is
carried to the structure morphism of the relative spectrum.  No carried hypothesis",
  ega "III 7.8.10" "partial", sga "1 X 1.2" "Y′ ≅ Spec f_*O_X over Y", sga "6 XII 2.5" "partial"]
public noncomputable def overIsoPushforwardSpectrum_of_isLocallyNoetherian :
    Over.mk f.fromNormalization ≅ Over.mk (pushforwardSpectrum f).toBase :=
  overIsoPushforwardSpectrum_of_isProper f

omit [IsLocallyNoetherian S] in
/-- **Stacks Project, Tag 03H0, clause (4), continued.**  The identification of clause (4) carries
the first factor `f'` to the canonical morphism `X ⟶ Spec_S(f_* 𝒪_X)` of [Stacks, Tag 01LY];  this
is what makes clause (4) an identification of the factorization `f = f' ≫ π` with the
factorization of `f` through its relative spectrum. -/
@[stacks 03H0 "clause (4), continued: the identification of clause (4) carries f' to the canonical
morphism X ⟶ Spec_S(f_* 𝒪_X) of Stacks 01LY.  No carried hypothesis",
  sga "1 X 1.2" "Under Y′ ≅ Spec f_*O_X"]
public theorem toNormalization_overIsoPushforwardSpectrum_hom_left_of_isLocallyNoetherian :
    f.toNormalization ≫ (overIsoPushforwardSpectrum_of_isLocallyNoetherian f).hom.left =
      canonicalMorphism f :=
  toNormalization_overIsoPushforwardSpectrum_hom_left_of_isProper f

end RemainingClauses

/-! ### The five clauses together -/

/-- **The five clauses of [Stacks, Tag 03H0].**  `IsSteinFactorization f f' π` says that
`f = f' ≫ π` is a Stein factorization of `f`:  `f'` is proper with geometrically connected
fibres, `π` is finite, `f'_* 𝒪_X = 𝒪_{S'}`, the target of `f'` is the relative spectrum
`Spec_S(f_* 𝒪_X)` of the pushed-forward structure sheaf over `S` in a way carrying `f'` to the
canonical morphism of [Stacks, Tag 01LY], and it is the normalization of `S` in `X`
([Stacks, Tag 035H]) over `S` in a way carrying `f'` to the canonical map to the normalization.

The two identifications are stated as isomorphisms in `CategoryTheory.Over S`, which is what
makes them identifications of *factorizations* rather than of bare schemes:  being an
isomorphism over `S` says that `π` is carried to the structure morphism of the relative spectrum
respectively to the structure morphism of the normalization, and the accompanying equation says
that `f'` is carried to the canonical morphism respectively to `f.toNormalization`. -/
public structure IsSteinFactorization {X S S' : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (f' : X ⟶ S') (π : S' ⟶ S) where
  /-- The two factors compose to `f`. -/
  comp : f' ≫ π = f
  /-- Clause (1), first half: the first factor is proper. -/
  isProper : IsProper f'
  /-- Clause (1), second half: the first factor has geometrically connected fibres. -/
  geometricallyConnected : GeometricallyConnected f'
  /-- Clause (2): the second factor is finite. -/
  isFinite : IsFinite π
  /-- Clause (3): `f'_* 𝒪_X = 𝒪_{S'}`, i.e. the canonical map `𝒪_{S'} ⟶ f'_* 𝒪_X` is an
  isomorphism. -/
  structureSheaf : IsIso f'.c
  /-- Clause (4): `S' = Spec_S(f_* 𝒪_X)`, as a scheme over `S`. -/
  relativeSpectrum : Over.mk π ≅ Over.mk (pushforwardSpectrum f).toBase
  /-- Clause (4), continued: that identification carries `f'` to the canonical morphism
  `X ⟶ Spec_S(f_* 𝒪_X)` of [Stacks, Tag 01LY]. -/
  relativeSpectrum_hom_left : f' ≫ relativeSpectrum.hom.left = canonicalMorphism f
  /-- Clause (5): `S'` is the normalization of `S` in `X`, as a scheme over `S`. -/
  normalization : Over.mk π ≅ Over.mk f.fromNormalization
  /-- Clause (5), continued: that identification carries `f'` to the canonical map from `X` to
  the normalization of `S` in `X`. -/
  normalization_hom_left : f' ≫ normalization.hom.left = f.toNormalization

/-- **Stacks Project, Tag 03H0 (Stein factorization, Noetherian case).**  Let `S` be a locally
Noetherian scheme and let `f : X ⟶ S` be proper.  Then `f` factors as `X --f'--> S' --π--> S`
with all five properties of the tag:  `f'` proper with geometrically connected fibres, `π`
finite, `f'_* 𝒪_X = 𝒪_{S'}`, `S' = Spec_S(f_* 𝒪_X)`, and `S'` the normalization of `S` in `X`.

The witnesses are the ones the source names:  `S'` is the normalization of `S` in `X`, `f'` is
`f.toNormalization` and `π` is `f.fromNormalization`.

Unconditional.  Each of the five clauses is a theorem of its own above;  the last of them to be
proved was the connectedness conjunct of clause (1),
`Stacks.SteinFactorization.geometricallyConnected_toNormalization`, which rests on
[Stacks, Tag 0G7X] at a locally Noetherian base and through it on the theorem on formal
functions. -/
@[stacks 03H0,
  ega "II 8.11.8" "(ii), special case",
  ega "III 4.3.1",
  ega "III 7.8.10" "more general", sga "1 IX 6.6" "partial", sga "1 X 1.2"]
public theorem exists_isSteinFactorization
    (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f] :
    ∃ (S' : Scheme.{u}) (f' : X ⟶ S') (π : S' ⟶ S), Nonempty (IsSteinFactorization f f' π) :=
  ⟨f.normalization, f.toNormalization, f.fromNormalization,
    ⟨{ comp := toNormalization_fromNormalization f
       isProper := isProper_toNormalization f
       geometricallyConnected := geometricallyConnected_toNormalization f
       isFinite := isFinite_fromNormalization f
       structureSheaf := isIso_c_toNormalization_of_isProper f
       relativeSpectrum := overIsoPushforwardSpectrum_of_isProper f
       relativeSpectrum_hom_left :=
         toNormalization_overIsoPushforwardSpectrum_hom_left_of_isProper f
       normalization := Iso.refl _
       normalization_hom_left := Category.comp_id _ }⟩⟩

end Stacks.SteinFactorization

end
