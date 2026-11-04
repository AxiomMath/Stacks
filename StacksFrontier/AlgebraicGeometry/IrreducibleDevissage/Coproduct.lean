module

public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Graded
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks

/-!
# The direct image of a finite coproduct of copies of an ideal sheaf, filtered by its factors

Step 4 of the proof of [Stacks, Tag 01YF] is [Stacks, Tag 01YE]: a coherent module `Q`
annihilated by the ideal sheaf of an irreducible closed set `Z` receives a monomorphism from
`i_*(I ^ {⊕ r})`, the direct image along a closed immersion `i` from an integral scheme of a
finite coproduct of copies of one quasi-coherent ideal sheaf `I`, and the monomorphism is
invertible near the generic point of `Z`. Turning that one short exact sequence into the bounded
dévissage filtration
`Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealDevissage` demands a filtration of
`i_*(I ^ {⊕ r})` whose successive quotients are each `i_* I`.

The implementation notes of
`StacksFrontier/AlgebraicGeometry/IrreducibleDevissage/Basic.lean` record that filtration as
absent from this repository and from Mathlib at this pin, and those of
`StacksFrontier/AlgebraicGeometry/ConfinedDevissage/Basic.lean` name its absence as the reason the
multiplicity `r` had to be assumed to be `1`. **This file proves it**, so step 4 is reduced to
the single short exact sequence and nothing about filtrations.

## Main definitions

* `Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealCoproductSub`: step 4 of the proof
  of [Stacks, Tag 01YF] **as the one short exact sequence [Stacks, Tag 01YE] constructs** — a
  coherent quasi-coherent module annihilated by the ideal sheaf of an irreducible closed set `Z`
  receives a monomorphism from the direct image of a finite coproduct of copies of a
  quasi-coherent ideal sheaf on an integral closed subscheme, with cokernel supported strictly
  inside `Z`.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealCoproductSubIn`: the same with the
  subscheme confined to `Z`, which is what [Stacks, Tag 01YH] consumes.

## Main results

* `Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_biproduct_const`: **a finite
  biproduct of copies of a coherent module in a class `Q` carries a bounded dévissage filtration
  with quotients in `Q`** — the filtration by the factors.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.pushforwardCoproductConstIso`: the direct image
  of a finite coproduct of copies of a module is the biproduct of the copies of its direct
  image.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_pushforward_coproduct_const`:
  **the direct image of a finite coproduct of copies of a module is filtered by its factors.**
* `hasKilledIdealDevissage_of_hasKilledIdealCoproductSub` and
  `hasKilledIdealDevissageIn_of_hasKilledIdealCoproductSubIn`: **step 4 from the single short
  exact sequence**, absolute and confined.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_subset_of_epi` and
  `supp_cokernel_subset`: **the support of a quotient is contained in the support of the
  module**, which the implementation notes of
  `StacksFrontier/AlgebraicGeometry/ConfinedDevissage/Basic.lean` record as absent.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.property_of_hasKilledIdealCoproductSub`: the
  statement of Tag 01YG verbatim with `HasKilledIdealCoproductSub X` as its one added hypothesis.

## Implementation notes

**The filtration is over an arbitrary finite index type, not over `Fin r`.** Mathlib has no
decomposition `⨁_{Fin (n + 1)} N ≅ N ⊞ ⨁_{Fin n} N`, but it does have
`CategoryTheory.Limits.cokernelBiproductιIso`, which identifies the cokernel of the inclusion of
one factor with the biproduct over the complement of that index. Inducting on `Fintype.card` of
the index type therefore needs nothing new, and `Fin r` is the case
`Fintype.card (Fin r) = r`.

**`HasFiniteBiproducts` on the modules of a scheme is supplied here.** The category is abelian,
so it has finite products, and `CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts`
converts; that conversion is deliberately not an instance in Mathlib, so instance search does
not find `HasBiproduct` for any family at all. It is supplied as a `local instance`, which is
why the public statements of this file speak of the coproduct `∐` — whose instances are native —
and the biproduct `⨁` appears only in the auxiliary lemmas.

**The exchange `i_*(I ^ {⊕ r}) ≅ (i_* I) ^ {⊕ r}` needs nothing about `i`.**
`AlgebraicGeometry.Scheme.Modules.pushforward` is an additive functor, and an additive functor
preserves finite biproducts, so no affineness, closedness or quasi-coherence hypothesis enters.
In particular `StacksFrontier/AlgebraicGeometry/PushforwardColimits/Basic.lean` — whose
`isIso_coproductComparison_pushforward` is the quasi-coherent, affine-morphism form of the same
exchange — is not needed, and would have
required the index type to be reindexed into `Type u`.

**What the reduction does and does not remove, and it is not lossless.** The standing hypothesis
`HasKilledIdealDevissage` asks for a whole filtration; `HasKilledIdealCoproductSub` asks only for
the short exact sequence. The filtration content between them is proved here. But the new
hypothesis is **not** a consequence of Tag 01YE alone, in two respects, both of which are stated
on `HasKilledIdealCoproductSub` itself: it asks for coherence of `i_* I`, and it asks for the
support of the cokernel rather than an open on which the monomorphism is invertible. The second
is now one named implication away: `supp_cokernel_ssubset_of_isIso_restrict_of_supp_subset`
performs the whole conversion given `SheafOfModules.supp Q ⊆ Z`, and the only thing missing is
that annihilation of `Q` by the ideal sheaf of `Z` — which is what `HasKilledIdealDevissage`
supplies — forces that containment. In the other direction the new hypothesis is weaker than
01YE's, which asks only that the stalk at the generic point be killed by the maximal ideal.

**No `stacks` attribute is attached.** Tag 01YG carries a single unlabelled assertion, and every
theorem below either carries `HasKilledIdealCoproductSub X`, which the tag does not have, or is
a fragment. 01YE, 01YF, 01YG and 01YH all remain open.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Opposite
open AlgebraicGeometry.CoherentAbelian
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.DevissageBounded

universe u

namespace Stacks.AlgebraicGeometry.IrreducibleDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The category of modules on a scheme is abelian, hence has finite products, hence finite
biproducts; the last implication is not an instance in Mathlib, so it is supplied here. -/
public theorem hasFiniteBiproducts_modules (W : Scheme.{u}) :
    HasFiniteBiproducts W.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] hasFiniteBiproducts_modules

/-! ### One module as a one-step filtration -/

/-- **A coherent module in the class carries the one-step filtration `0 ↪ N`.** -/
theorem hasDevissageWith_single {Q : X.Modules → Prop}
    (hQ : ∀ {M N : X.Modules}, (M ≅ N) → Q M → Q N)
    {N : X.Modules} (hN : N.IsCoherent) (hQN : Q N) : HasDevissageWith Q N :=
  have hz : IsZero (⊤_ X.Modules) := isZero_terminal
  have _hmono : Mono (0 : (⊤_ X.Modules) ⟶ N) := ⟨fun g h _ => hz.eq_of_tgt g h⟩
  have he : cokernel (0 : (⊤_ X.Modules) ⟶ N) ≅ N := cokernelZeroIsoTarget
  hasDevissageWith_snoc hQ (0 : (⊤_ X.Modules) ⟶ N) hN (isCoherent_of_iso' he hN)
    (hQ he.symm hQN) (hasDevissageWith_of_isZero hz)

/-! ### Finite biproducts of copies of one module -/

/-- A biproduct indexed by an empty type is a zero module. -/
theorem isZero_biproduct_const_of_isEmpty (N : X.Modules) (J : Type) [Finite J] [IsEmpty J] :
    IsZero (⨁ fun _ : J => N) :=
  (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun j => isEmptyElim j)

/-- The short exact sequence `N ⟶ ⨁_J N ⟶ ⨁_{J ∖ {j}} N` splitting off one factor of a
biproduct of copies of `N`. -/
theorem shortExact_biproduct_ι (N : X.Modules) (J : Type) [Finite J] (j : J) :
    (ShortComplex.mk (biproduct.ι (fun _ : J => N) j)
      (cokernel.π (biproduct.ι (fun _ : J => N) j)) (cokernel.condition _)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := inferInstanceAs (Mono (biproduct.ι (fun _ : J => N) j))
  epi_g := inferInstanceAs (Epi (cokernel.π (biproduct.ι (fun _ : J => N) j)))

/-- Induction on the cardinality of the index type of a biproduct of copies of `N`: a property
that holds for zero modules, is transported along isomorphisms, and passes from the cokernel of
one factor's inclusion to the whole biproduct, holds for every finite biproduct of copies of `N`. -/
private theorem biproduct_const_induction (N : X.Modules) (P : X.Modules → Prop)
    (hzero : ∀ {M : X.Modules}, IsZero M → P M)
    (hiso : ∀ {M M' : X.Modules}, (M ≅ M') → P M' → P M)
    (hstep : ∀ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (j : J),
      P (cokernel (biproduct.ι (fun _ : J => N) j)) → P (⨁ fun _ : J => N)) :
    ∀ (n : ℕ) (J : Type) (_ : Fintype J) (_ : DecidableEq J), Fintype.card J = n →
      P (⨁ fun _ : J => N) := by
  intro n
  induction n with
  | zero =>
    intro J hJ _ hcard
    have : IsEmpty J := Fintype.card_eq_zero_iff.mp hcard
    exact hzero (isZero_biproduct_const_of_isEmpty N J)
  | succ m IH =>
    intro J hJ hde hcard
    obtain ⟨j⟩ : Nonempty J := Fintype.card_pos_iff.mp (by omega)
    have hsubcard : Fintype.card {k : J // k ≠ j} = m := by
      simp [Fintype.card_subtype_compl, hcard]
    exact hstep J hJ hde j (hiso (cokernelBiproductιIso (fun _ : J => N) j)
      (IH {k : J // k ≠ j} inferInstance inferInstance hsubcard))

/-- **A finite biproduct of copies of a coherent module is coherent.** -/
theorem isCoherent_biproduct_const (N : X.Modules) (hN : N.IsCoherent) :
    ∀ (n : ℕ) (J : Type) (_ : Fintype J) (_ : DecidableEq J), Fintype.card J = n →
      (⨁ fun _ : J => N).IsCoherent :=
  biproduct_const_induction N (fun M => M.IsCoherent) isCoherent_of_isZero
    (fun e => isCoherent_of_iso' e) fun J _ _ j hck =>
      isCoherent_X₂_of_shortExact (shortExact_biproduct_ι N J j) hN hck

/-- **A finite biproduct of copies of a coherent module in the class `Q` carries a bounded
dévissage filtration with quotients in `Q`** — the filtration by the factors. -/
theorem hasDevissageWith_biproduct_const {Q : X.Modules → Prop}
    (hQ : ∀ {M N : X.Modules}, (M ≅ N) → Q M → Q N)
    (N : X.Modules) (hN : N.IsCoherent) (hQN : Q N) :
    ∀ (n : ℕ) (J : Type) (_ : Fintype J) (_ : DecidableEq J), Fintype.card J = n →
      HasDevissageWith Q (⨁ fun _ : J => N) :=
  biproduct_const_induction N (HasDevissageWith Q) hasDevissageWith_of_isZero
    (fun e => hasDevissageWith_of_iso e.symm) fun J hJ hde j hC =>
      hasDevissageWith_trans' hQ (biproduct.ι (fun _ : J => N) j)
        (isCoherent_biproduct_const N hN _ J hJ hde rfl) (hasDevissageWith_single hQ hN hQN) hC

/-! ### Direct images of finite coproducts -/

/-- **The direct image of a finite coproduct of copies of a module is the biproduct of the
copies of its direct image.** `AlgebraicGeometry.Scheme.Modules.pushforward` is an additive
functor, and an additive functor preserves finite biproducts. -/
def pushforwardCoproductConstIso {W : Scheme.{u}} (i : W ⟶ X) (M : W.Modules) (r : ℕ) :
    (Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => M) ≅
      ⨁ fun _ : Fin r => (Scheme.Modules.pushforward i).obj M :=
  (Scheme.Modules.pushforward i).mapIso (biproduct.isoCoproduct _).symm ≪≫
    Functor.mapBiproduct _ _

/-- **The direct image of a finite coproduct of copies of a module is coherent** as soon as the
direct image of that module is. -/
theorem isCoherent_pushforward_coproduct_const {W : Scheme.{u}} (i : W ⟶ X) (M : W.Modules)
    (hM : ((Scheme.Modules.pushforward i).obj M).IsCoherent) (r : ℕ) :
    ((Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => M)).IsCoherent :=
  isCoherent_of_iso' (pushforwardCoproductConstIso i M r)
    (isCoherent_biproduct_const _ hM r (Fin r) inferInstance inferInstance (Fintype.card_fin r))

/-- **The direct image of a finite coproduct of copies of a quasi-coherent ideal sheaf on an
integral closed subscheme is filtered by its factors.**

This is the statement the implementation notes of
`StacksFrontier/AlgebraicGeometry/IrreducibleDevissage/Basic.lean` record as absent from this
repository and from Mathlib at this pin, and which the implementation notes of
`StacksFrontier/AlgebraicGeometry/ConfinedDevissage/Basic.lean` name as the reason the multiplicity
`r` of [Stacks, Tag 01YE] had to be assumed to be `1`. Each successive quotient is `i_* I` itself,
so each lies in `Stacks.AlgebraicGeometry.DevissageBounded.IsIdealPushforward`; the filtration is
the one by the `r` factors, transported along `pushforwardCoproductConstIso`.

Only coherence of `i_* I` is assumed. It is *not* available in this repository: the direct image
of a coherent module along a proper morphism is coherent only conditionally here
(`Stacks.AlgebraicGeometry.ProperCoherentImage.isCoherent_pushforward_of_isProper` carries the
unproved hypothesis `HigherDirectImageIsCoherentOverAffineBase`, which is [Stacks, Tag 02O5] and
itself depends on this dévissage), so it is carried as a hypothesis exactly as
`Stacks.AlgebraicGeometry.ConfinedDevissage.property_pushforward_of_mono_of_supp_ssubset` carries
it. -/
theorem hasDevissageWith_pushforward_coproduct_const {Q : X.Modules → Prop}
    (hQ : ∀ {M N : X.Modules}, (M ≅ N) → Q M → Q N)
    {W : Scheme.{u}} (i : W ⟶ X) (M : W.Modules)
    (hMc : ((Scheme.Modules.pushforward i).obj M).IsCoherent)
    (hQM : Q ((Scheme.Modules.pushforward i).obj M)) (r : ℕ) :
    HasDevissageWith Q ((Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => M)) :=
  hasDevissageWith_of_iso (pushforwardCoproductConstIso i M r).symm
    (hasDevissageWith_biproduct_const hQ _ hMc hQM r (Fin r) inferInstance inferInstance
      (Fintype.card_fin r))

/-- The direct image of a quasi-coherent ideal sheaf on an integral closed subscheme lies in the
class `Stacks.AlgebraicGeometry.DevissageBounded.IsIdealPushforward` — by definition, with the
identity isomorphism. -/
theorem isIdealPushforward_pushforward {W : Scheme.{u}} (i : W ⟶ X) (hi : IsClosedImmersion i)
    (hW : IsIntegral W) (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hIq : I.toSheafOfModules.IsQuasicoherent) :
    IsIdealPushforward ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) :=
  ⟨W, i, hi, hW, I, hIq, ⟨Iso.refl _⟩⟩

/-- The direct image of a quasi-coherent ideal sheaf on an integral closed subscheme whose range
lies in `S` lies in the confined class
`Stacks.AlgebraicGeometry.ConfinedDevissage.IsIdealPushforwardIn S`. -/
theorem isIdealPushforwardIn_pushforward {S : Set X} {W : Scheme.{u}} (i : W ⟶ X)
    (hi : IsClosedImmersion i) (hW : IsIntegral W)
    (I : (SheafOfModules.unit W.ringCatSheaf).Submodule)
    (hIq : I.toSheafOfModules.IsQuasicoherent) (hr : Set.range i.base ⊆ S) :
    ConfinedDevissage.IsIdealPushforwardIn S
      ((Scheme.Modules.pushforward i).obj I.toSheafOfModules) :=
  ⟨W, i, hi, hW, I, hIq, hr, ⟨Iso.refl _⟩⟩

/-! ### The support of a quotient -/

/-- **The support of a quotient is contained in the support of the module.** An epimorphism of
sheaves of modules is surjective on every stalk, so a nonzero element of the stalk of the target
lifts to one of the stalk of the source.

The implementation notes of `StacksFrontier/AlgebraicGeometry/ConfinedDevissage/Basic.lean` record
this as a statement the repository does not have. It does not — but the input it needs,
`AlgebraicGeometry.epi_iff_stalk_surjective`
(`StacksFrontier/AlgebraicGeometry/Cohomology/GlobalGeneration/Stalks.lean:211`), is already in
the library. The one hazard is the documented one: `Epi` in the `SheafOfModules` spelling of the
category is not found by instance search from `Epi` in the `X.Modules` spelling, so it is bound
explicitly. -/
theorem supp_subset_of_epi {B C : X.Modules} (π : B ⟶ C) (hπ : Epi π) :
    SheafOfModules.supp C ⊆ SheafOfModules.supp B := by
  have hπ' : Epi (C := SheafOfModules.{u} X.ringCatSheaf) π := hπ
  have hsurj := (AlgebraicGeometry.epi_iff_stalk_surjective X.ringCatSheaf π).mp hπ'
  intro x hx
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hsurj x a
  refine ⟨b, fun hbz => ha ?_⟩
  rw [← hb, hbz]
  exact map_zero _

/-- **The support of a cokernel is contained in the support of the target.** -/
theorem supp_cokernel_subset {A B : X.Modules} (φ : A ⟶ B) :
    SheafOfModules.supp (cokernel φ) ⊆ SheafOfModules.supp B :=
  supp_subset_of_epi (cokernel.π φ) (inferInstanceAs (Epi (cokernel.π φ)))

/-- **The cokernel of a generically invertible morphism into a module supported in `Z` is
supported strictly inside `Z`.** This is the conversion
`Stacks.AlgebraicGeometry.ConfinedDevissage.supp_cokernel_ssubset_of_isIso_restrict` performs, with
the containment it leaves as a hypothesis now discharged by `supp_cokernel_subset`: all that is
needed of the cokernel is that the target is supported in `Z`.

It is the shape [Stacks, Tag 01YE] delivers its conclusion — an open on which the monomorphism
is invertible — turned into the support condition `HasKilledIdealCoproductSub` asks for. What
still separates the two is only that `HasKilledIdealDevissage` gives annihilation of `Q` by the
ideal sheaf of `Z` and not `SheafOfModules.supp Q ⊆ Z`; that implication is the one piece of this
conversion the repository still lacks. -/
theorem supp_cokernel_ssubset_of_isIso_restrict_of_supp_subset {A B : X.Modules} (φ : A ⟶ B)
    {Z₀ : Set X} (U : X.Opens)
    (hiso : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ))
    (ξ : X) (hξU : ξ ∈ U) (hξ : ξ ∈ Z₀) (hB : SheafOfModules.supp B ⊆ Z₀) :
    SheafOfModules.supp (cokernel φ) ⊂ Z₀ :=
  ConfinedDevissage.supp_cokernel_ssubset_of_isIso_restrict φ U hiso ξ hξU hξ
    ((supp_cokernel_subset φ).trans hB)

/-! ### Step 4 with the multiplicity restored -/

/-- **Step 4 of the proof of [Stacks, Tag 01YF], in the shape [Stacks, Tag 01YE] produces it.**
A coherent quasi-coherent module `Q` annihilated by the ideal sheaf of an irreducible closed set
`Z` receives a monomorphism from the direct image, along a closed immersion from an integral
scheme, of a finite coproduct of copies of one quasi-coherent ideal sheaf, with cokernel
supported strictly inside `Z`.

Compared with `Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealDevissage`, which it
implies, this asks for the one short exact sequence [Stacks, Tag 01YE] constructs and nothing
about filtrations: the multiplicity `r` is arbitrary, the filtration by the `r` factors being
supplied by `hasDevissageWith_pushforward_coproduct_const`.

Two differences from Tag 01YE's conclusion, both recorded honestly because this is a reduction
and not a proof.

* It is **weaker** in its hypothesis on `Q`: 01YE asks only that the stalk of `Q` at the generic
  point be killed by the maximal ideal, whereas this asks for annihilation by the ideal sheaf
  over every affine open — the condition `HasKilledIdealDevissage` already carries. Sheaf-level
  annihilation implies the stalk condition, so 01YE's conclusion is available at every `Q` this
  predicate quantifies over.
* It is **stronger** in two respects. First, it asks for coherence of `i_* I` rather than of
  `i_*(I ^ {⊕ r})`; see `hasDevissageWith_pushforward_coproduct_const` for why that is carried
  as a hypothesis here. Second, it asks for the support of the cokernel to be strictly inside
  `Z`, where 01YE delivers an open `U` containing the generic point on which the monomorphism is
  invertible; `supp_cokernel_ssubset_of_isIso_restrict_of_supp_subset` makes that conversion in
  full given `SheafOfModules.supp Q ⊆ Z`, so what is missing is exactly the implication from
  annihilation of `Q` by the ideal sheaf of `Z` to that containment.

So **the reduction below is not lossless**: `HasKilledIdealCoproductSub` is not a consequence of
Tag 01YE alone. What it removes from the standing hypothesis is exactly the filtration content,
which is now proved. -/
def HasKilledIdealCoproductSub (X : Scheme.{u}) : Prop :=
  ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    ∀ Q : X.Modules, Q.IsQuasicoherent → Q.IsCoherent →
      (∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
          (⊤ : Submodule Γ(X, U.1) Γ(Q, U.1)) = ⊥) →
      ∃ (W : Scheme.{u}) (i : W ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral W) (r : ℕ)
        (I : (SheafOfModules.unit W.ringCatSheaf).Submodule),
        I.toSheafOfModules.IsQuasicoherent ∧
          ((Scheme.Modules.pushforward i).obj I.toSheafOfModules).IsCoherent ∧
          ∃ φ : (Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ Q,
            Mono φ ∧ SheafOfModules.supp (cokernel φ) ⊂ (Z : Set X)

/-- **Step 4 of the proof of [Stacks, Tag 01YF] from the single short exact sequence
[Stacks, Tag 01YE] constructs.** The sub `i_*(I ^ {⊕ r})` is filtered by its `r` factors, each
an ideal pushforward; the quotient has support strictly inside `Z`, so it is a one-step
filtration on its own; splicing the two gives the dévissage of `Q`.

This discharges, unconditionally, the part of
`Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealDevissage` that is about
filtrations — in particular the arbitrariness of the multiplicity `r`, which
`StacksFrontier/AlgebraicGeometry/ConfinedDevissage/Basic.lean` records as forcing `r = 1`. -/
theorem hasKilledIdealDevissage_of_hasKilledIdealCoproductSub
    (h : HasKilledIdealCoproductSub X) : HasKilledIdealDevissage X := by
  intro Z hZirr Q hQq hQc hkill
  obtain ⟨W, i, hi, hW, r, I, hIq, hIc, φ, hmono, hsupp⟩ := h Z hZirr Q hQq hQc hkill
  have hAc : ((Scheme.Modules.pushforward i).obj
      (∐ fun _ : Fin r => I.toSheafOfModules)).IsCoherent :=
    isCoherent_pushforward_coproduct_const i I.toSheafOfModules hIc r
  have hCc : (cokernel φ).IsCoherent := isCoherent_cokernel' φ hAc hQc
  refine hasDevissageWith_trans' isIdealPushforward_or_supp_ssubset_of_iso' φ hQc ?_ ?_
  · exact hasDevissageWith_pushforward_coproduct_const isIdealPushforward_or_supp_ssubset_of_iso'
      i I.toSheafOfModules hIc
      (Or.inl (isIdealPushforward_pushforward i hi hW I hIq)) r
  · exact hasDevissageWith_single isIdealPushforward_or_supp_ssubset_of_iso' hCc (Or.inr hsupp)

/-- **Step 4 of the proof of [Stacks, Tag 01YF], confined to `Z`, in the shape
[Stacks, Tag 01YE] produces it.** `HasKilledIdealCoproductSub` with the containment the source's
construction actually delivers — step 4 takes the subscheme to be the reduced induced structure
on `Z`, whose range is `Z` — and it is what [Stacks, Tag 01YH] consumes, through
`Stacks.AlgebraicGeometry.ConfinedDevissage.HasIrreducibleDevissageIn`.

The caveats recorded on `HasKilledIdealCoproductSub` apply verbatim here. -/
def HasKilledIdealCoproductSubIn (X : Scheme.{u}) : Prop :=
  ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    ∀ Q : X.Modules, Q.IsQuasicoherent → Q.IsCoherent →
      (∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
          (⊤ : Submodule Γ(X, U.1) Γ(Q, U.1)) = ⊥) →
      ∃ (W : Scheme.{u}) (i : W ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral W) (r : ℕ)
        (I : (SheafOfModules.unit W.ringCatSheaf).Submodule),
        I.toSheafOfModules.IsQuasicoherent ∧
          Set.range i.base ⊆ (Z : Set X) ∧
          ((Scheme.Modules.pushforward i).obj I.toSheafOfModules).IsCoherent ∧
          ∃ φ : (Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ Q,
            Mono φ ∧ SheafOfModules.supp (cokernel φ) ⊂ (Z : Set X)

/-- **Step 4 of the proof of [Stacks, Tag 01YF], confined, from the single short exact sequence
[Stacks, Tag 01YE] constructs.** The confined counterpart of
`hasKilledIdealDevissage_of_hasKilledIdealCoproductSub`; the filtration by the `r` factors is
the same one, the class being the only difference. -/
theorem hasKilledIdealDevissageIn_of_hasKilledIdealCoproductSubIn
    (h : HasKilledIdealCoproductSubIn X) : HasKilledIdealDevissageIn X := by
  intro Z hZirr Q hQq hQc hkill
  obtain ⟨W, i, hi, hW, r, I, hIq, hrange, hIc, φ, hmono, hsupp⟩ := h Z hZirr Q hQq hQc hkill
  have hAc : ((Scheme.Modules.pushforward i).obj
      (∐ fun _ : Fin r => I.toSheafOfModules)).IsCoherent :=
    isCoherent_pushforward_coproduct_const i I.toSheafOfModules hIc r
  have hCc : (cokernel φ).IsCoherent := isCoherent_cokernel' φ hAc hQc
  refine hasDevissageWith_trans' isIdealPushforwardIn_or_supp_ssubset_of_iso φ hQc ?_ ?_
  · exact hasDevissageWith_pushforward_coproduct_const
      isIdealPushforwardIn_or_supp_ssubset_of_iso i I.toSheafOfModules hIc
      (Or.inl (isIdealPushforwardIn_pushforward i hi hW I hIq hrange)) r
  · exact hasDevissageWith_single isIdealPushforwardIn_or_supp_ssubset_of_iso hCc (Or.inr hsupp)

/-- **[Stacks, Tag 01YG] on the single short exact sequence of [Stacks, Tag 01YE].** A property
of modules on a Noetherian scheme that holds on the zero module, is stable under extensions of
coherent modules, and holds on the direct image of every quasi-coherent ideal sheaf on every
integral closed subscheme, holds on every coherent module.

This is the statement of Tag 01YG verbatim with the single added hypothesis
`HasKilledIdealCoproductSub X`, which replaces the `HasKilledIdealDevissage X` of
`Stacks.AlgebraicGeometry.IrreducibleDevissage.property_of_hasKilledIdealDevissage`. -/
theorem property_of_hasKilledIdealCoproductSub (X : Scheme.{u}) [IsNoetherian X]
    (h : HasKilledIdealCoproductSub X)
    (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  property_of_hasKilledIdealDevissage X
    (hasKilledIdealDevissage_of_hasKilledIdealCoproductSub h) P hzero hext hideal

end Stacks.AlgebraicGeometry.IrreducibleDevissage

end
